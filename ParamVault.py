# -*- coding: utf-8 -*-
"""
ParamVault - Python 3.12
功能：
- 即時監控 .par（watchdog；未安裝時可選輪詢）
- 新增/修改/取代/刪除事件記錄
- 保存變更前版本（以掃描快照快取內容，事件觸發時備份）
- 變更後版本備份
- PAR 文字差異比較（統一 diff）
- GUI 通知與事件清單
- Windows 開機自動啟動捷徑（可選）
輸出：ParamVault.log（全部事件）、ParamVault_參數變更.log（只含「修改」，變更項目不截斷）
介面：左側導覽（監控總覽／事件紀錄／設定）＋右側內容頁
"""
from __future__ import annotations
import difflib
import hashlib
import os
import queue
import shutil
import subprocess
import sys
import threading
import time
from datetime import datetime, date, timedelta
from pathlib import Path
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

APP_TITLE = "ParamVault"
ICON_FILE = "backup-records-icon.ico"
LOGO_FILE = "backup-records-icon-48.png"
DEFAULT_INTERVAL = 5.0        # 網路磁碟機建議 5 秒以上
DELETE_CONFIRM_CYCLES = 2     # 連續幾輪都找不到才算「刪除」（避免網路瞬斷／先刪後寫的取代被誤判）
FULL_VERIFY_EVERY = 60        # 每 N 輪強制完整重讀內容（抓「大小與修改時間都沒變」的取代）
DISK_REFRESH_SEC = 30         # 備份空間更新週期
HOME_EVENT_LIMIT = 30         # 監控總覽只顯示最近 N 筆事件

# ---- 深色主題 ----
BG = "#050d1c"        # 視窗底色
SIDEBAR = "#07142b"   # 左側導覽
PANEL = "#0a1a33"     # 卡片底色
PANEL2 = "#102a4c"    # 輸入框／按鈕／表頭
BORDER = "#17325a"
FG = "#e6f0ff"
MUTED = "#7f93b5"
ACCENT = "#12b3ff"
CYAN = ACCENT
GREEN = "#39e08f"
AMBER = "#ffc83d"
RED = "#ff5d6c"
NAV_ACTIVE = "#0f2a4d"
FONT_UI = ("Microsoft JhengHei UI", 10)
FONT_UI_B = ("Microsoft JhengHei UI", 10, "bold")
FONT_SMALL = ("Microsoft JhengHei UI", 9)
FONT_TITLE = ("Microsoft JhengHei UI", 18, "bold")
FONT_CARD_T = ("Microsoft JhengHei UI", 12, "bold")
FONT_BIG = ("Microsoft JhengHei UI", 18, "bold")
FONT_ICON = ("Segoe UI Symbol", 15)
FONT_MONO = ("Consolas", 10)
ACTION_STYLE = {   # 事件 -> (tag, 圖示)
    "開始": ("start", "●"),
    "新增": ("new", "▲"),
    "修改/取代": ("mod", "◆"),
    "刪除": ("del", "✕"),
}
FILTERS = {"全部事件": None, "新增": "new", "修改/取代": "mod", "刪除": "del"}
PERIODS = ("今日", "近 7 天", "全部")
KIND_BY_LOG = {"新增": "new", "修改/取代": "mod", "刪除": "del", "監控開始": "other"}


def resource_path(name: str) -> str:
    """PyInstaller 打包後從暫存目錄取資源，未打包時從程式所在目錄取。"""
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, name)


def apply_icon(root):
    if os.name != "nt":
        return
    try:  # 讓工作列顯示本程式自己的圖示，而不是 python 的
        import ctypes
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("ParamVault.App")
    except Exception:
        pass
    try:  # default=True：之後開的子視窗（差異視窗）也會套用
        root.iconbitmap(default=resource_path(ICON_FILE))
    except tk.TclError:
        pass


def is_network_path(path: str) -> bool:
    """UNC 路徑或對應成磁碟機代號的網路磁碟機。"""
    if os.name != "nt":
        return False
    if path.startswith("\\\\"):
        return True
    drive = os.path.splitdrive(path)[0]
    if not drive:
        return False
    try:
        import ctypes
        return ctypes.windll.kernel32.GetDriveTypeW(drive + "\\") == 4  # DRIVE_REMOTE
    except Exception:
        return False


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def scan(folder: str, previous: dict, force_full: bool = False):
    """
    掃描 .par，回傳 {路徑: ((大小, 修改時間ns), 內容bytes)}；資料夾無法存取時回傳 None。
    - 大小與修改時間沒變就沿用快取，不重讀內容（網路磁碟機省流量）。
    - 讀取失敗／檔案還在寫入中／子資料夾暫時讀不到：保留舊版本，絕不因此判成「刪除」。
    """
    if not os.path.isdir(folder):
        return None
    result, failed_dirs = {}, []

    def onerror(err):
        if getattr(err, "filename", None):
            failed_dirs.append(os.path.normcase(str(err.filename)))

    for dirpath, _dirs, files in os.walk(folder, onerror=onerror):
        for name in files:
            if not name.lower().endswith(".par"):
                continue
            path = os.path.join(dirpath, name)
            old = previous.get(path)
            try:
                st = os.stat(path)
                sig = (st.st_size, st.st_mtime_ns)
                if old and old[0] == sig and not force_full:
                    result[path] = old
                    continue
                with open(path, "rb") as f:
                    data = f.read()
                st2 = os.stat(path)
                if (st2.st_size, st2.st_mtime_ns) != sig:   # 讀的當下還在被寫入，下一輪再看
                    if old:
                        result[path] = old
                    continue
                result[path] = (sig, data)
            except OSError:
                if old:
                    result[path] = old
    for path, val in previous.items():
        if path in result:
            continue
        npath = os.path.normcase(path)
        if any(npath.startswith(d.rstrip("\\/") + os.sep) for d in failed_dirs):
            result[path] = val
    return result


def decode_text(data: bytes) -> str:
    for encoding in ("utf-8-sig", "utf-8", "cp950", "big5", "utf-16"):
        try:
            return data.decode(encoding)
        except UnicodeDecodeError:
            continue
    return data.decode("utf-8", errors="replace")


def parse_par_items(text: str):
    """把 INI 風格的 PAR 文字解析成 [((區段, 參數, 第幾次出現), 值), ...]（保留原順序）。"""
    items, section, seen = [], "", {}
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith((";", "#")):
            continue
        if line.startswith("[") and line.endswith("]"):
            section = line[1:-1].strip()
            continue
        if "=" not in line:
            continue
        key, value = (x.strip() for x in line.split("=", 1))
        n = seen[(section, key)] = seen.get((section, key), 0) + 1
        items.append(((section, key, n), value))
    return items


_FMT_CACHE = {}


def _read_text_any(path):
    raw = Path(path).read_bytes()
    for enc in ("utf-8-sig", "cp950"):
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            pass
    return raw.decode("utf-8", "replace")


class ParamFormat:
    """InspectParamFormat.ini：區段（邏輯）與參數的中文名稱對照。"""
    def __init__(self, text: str):
        self.sec_names = {}    # 區段 key -> 中文（例：Discolor_White_OT_R -> 外部異色R(白霧)）
        self.params = {}       # (類型, 區段) -> {參數 key: 中文}
        self.type_names = {}   # 類型代碼 -> 中文（例：100 -> 金屬檢測）
        cur = None
        for raw in text.splitlines():
            line = raw.strip()
            if not line:
                continue
            if line.startswith("[") and line.endswith("]"):
                head = line[1:-1]
                if head.startswith(".\\"):
                    cur = ("names", None)
                elif head != "ParamType" and "\\" in head:
                    typ, sec = head.split("\\", 1)
                    cur = ("params", (typ, sec))
                    self.params.setdefault((typ, sec), {})
                elif head == "ParamType":
                    cur = ("types", None)
                else:
                    cur = None
                continue
            if cur is None or "=" not in line:
                continue
            key, value = (x.strip() for x in line.split("=", 1))
            if cur[0] == "types":
                self.type_names[key] = value.split("|")[-1].strip()
            elif cur[0] == "names":
                self.sec_names.setdefault(key, value.strip("【】"))
            else:
                parts = [p.strip() for p in value.split("|")]
                idx = 3 if parts[0] == "Boolean_Type" else 5
                if len(parts) > idx and parts[idx]:
                    self.params[cur[1]][key] = parts[idx]

    def section_name(self, sec):
        return self.sec_names.get(sec, sec)

    def type_name(self, typ):
        return self.type_names.get(typ)

    def param_name(self, file_no, sec, key, typ=None):
        if typ is None and file_no is not None:
            typ = str(file_no // 100 * 100 if file_no >= 100 else file_no // 10 * 10)
        if typ is not None:
            hit = self.params.get((str(typ), sec), {}).get(key)
            if hit:
                return hit
        for (_t, s), d in self.params.items():     # 找不到類型時，用區段名稱全面搜尋
            if s == sec and key in d:
                return d[key]
        return None


_FMT_BY_HASH = {}   # 內容相同的 ini（各料號通常一樣）只解析、保存一份


class FormatChain:
    """先用程式內建的對照表；內建查不到（例如新版軟體多出的參數）才去讀 .par 旁的 InspectParamFormat.ini。"""
    def __init__(self, builtin, par_path):
        self.builtin, self.par_path, self._disk = builtin, par_path, False

    def _disk_fmt(self):
        if self._disk is False:
            self._disk = load_param_format(self.par_path)
        return self._disk

    def type_name(self, typ):
        hit = self.builtin.type_name(typ)
        if hit is None and self._disk_fmt():
            hit = self._disk.type_name(typ)
        return hit

    def section_name(self, sec):
        if sec in self.builtin.sec_names:
            return self.builtin.sec_names[sec]
        d = self._disk_fmt()
        return d.section_name(sec) if d else sec

    def param_name(self, file_no, sec, key, typ=None):
        hit = self.builtin.param_name(file_no, sec, key, typ)
        if hit is None:
            d = self._disk_fmt()
            hit = d.param_name(file_no, sec, key, typ) if d else None
        return hit


_BUILTIN_FMT = None


def get_builtin_format():
    global _BUILTIN_FMT
    if _BUILTIN_FMT is None:
        import base64, zlib
        text = zlib.decompress(base64.b64decode("".join(_INI_BLOB))).decode("utf-8")
        _BUILTIN_FMT = ParamFormat(text)
    return _BUILTIN_FMT


def load_param_format(par_path):
    """從 .par 所在資料夾往上找（最多 3 層）名為 InspectParamFormat.ini 的檔案。
    只認這個檔名，其他 ini 一律忽略；以修改時間快取，內容相同者共用同一份解析結果。"""
    p = Path(par_path)
    for d in (p.parent, p.parent.parent, p.parent.parent.parent):
        ini = d / "InspectParamFormat.ini"
        try:
            mtime = ini.stat().st_mtime
        except OSError:
            continue
        hit = _FMT_CACHE.get(str(ini))
        if hit and hit[0] == mtime:
            return hit[1]
        try:
            raw = ini.read_bytes()
            key = hashlib.sha256(raw).hexdigest()
            fmt = _FMT_BY_HASH.get(key)
            if fmt is None:
                fmt = _FMT_BY_HASH[key] = ParamFormat(_decode_ini(raw))
        except Exception:
            return None
        _FMT_CACHE[str(ini)] = (mtime, fmt)
        return fmt
    return None


def _decode_ini(raw):
    for enc in ("utf-8-sig", "cp950"):
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            pass
    return raw.decode("utf-8", "replace")


def file_number(par_path):
    try:
        return int(Path(par_path).stem.rsplit("_", 1)[1])
    except (IndexError, ValueError):
        return None


SIDE_NAMES = {"sidea": "正面", "sideb": "背面"}


def par_context(par_path, items, fmt):
    """由 .par 的 [Info] 與所在資料夾，組出「面別_類型_群組」，例：正面_金屬檢測_BigFinger。"""
    folder = Path(par_path).parent.name
    side = SIDE_NAMES.get(folder.lower(), folder)
    info = {k[1]: v for k, v in items if k[0] == "Info"}
    typ = info.get("Type")
    tname = (fmt.type_name(typ) if fmt and typ else None) or (f"Type{typ}" if typ else "")
    group = info.get("Name") or Path(par_path).stem
    return "_".join(x for x in (side, tname, group) if x), typ


def summarize_changes(old: bytes, new: bytes, limit: int | None = 12, fmt=None, file_no=None, par_path=None):
    """回傳參數層級的變更摘要，例如
    '正面_金屬檢測_BigFinger_點異色B(白霧)_淡大亮型色差門檻 50 > 60'；無法解析時回傳 None。"""
    try:
        a, b = parse_par_items(decode_text(old)), parse_par_items(decode_text(new))
    except Exception:
        return None
    da, db = dict(a), dict(b)
    prefix, typ = (par_context(par_path, b or a, fmt) if par_path else ("", None))

    def label(k):
        sec, key = k[0], k[1]
        if sec == "Info":                          # 群組名稱／顏色的變更
            return "_".join(x for x in (prefix, {"Name": "群組名稱", "Color": "顏色"}.get(key, key)) if x)
        pname = (fmt.param_name(file_no, sec, key, typ) if fmt else None) or key
        pname = pname.replace(".", "")            # 淡大.亮型色差門檻 → 淡大亮型色差門檻
        sname = (fmt.section_name(sec) if fmt else sec) if sec else ""
        if sname and sname == pname and key.startswith("b"):
            pname = "開關"                          # 區段名與參數名相同（如 Golden異色）
        return "_".join(x for x in (prefix, sname if sname != pname else "", pname) if x)

    parts = []
    for k, v in a:
        if k not in db:
            parts.append((k, f"{label(k)} 刪除（原值 {v}）"))
        elif db[k] != v:
            parts.append((k, f"{label(k)} {v} > {db[k]}"))
    for k, v in b:
        if k not in da:
            parts.append((k, f"{label(k)} 新增 {v}"))
    if not parts:
        return None
    order = {k: i for i, (k, _) in enumerate(b)}
    parts.sort(key=lambda p: order.get(p[0], 10 ** 6))
    text = "; ".join(txt for _, txt in parts[:limit])
    if limit is not None and len(parts) > limit:
        text += f"; …共 {len(parts)} 項"
    return text


class Toggle(tk.Canvas):
    """設定頁用的開關（綁定 BooleanVar）。"""
    def __init__(self, parent, variable, bg=PANEL):
        super().__init__(parent, width=46, height=24, bg=bg, highlightthickness=0, cursor="hand2")
        self.var = variable
        self.bind("<Button-1>", lambda e: self.var.set(not self.var.get()))
        self.var.trace_add("write", lambda *a: self._draw())
        self._draw()

    def _draw(self):
        self.delete("all")
        on = bool(self.var.get())
        col = ACCENT if on else "#27406b"
        self.create_oval(1, 1, 23, 23, fill=col, outline=col)
        self.create_oval(23, 1, 45, 23, fill=col, outline=col)
        self.create_rectangle(12, 1, 34, 23, fill=col, outline=col)
        cx = 34 if on else 12
        self.create_oval(cx - 9, 3, cx + 9, 21, fill="#ffffff", outline="#ffffff")


class ParMonitor:
    def __init__(self, root):
        self.root = root
        self.root.title(APP_TITLE)
        self.root.geometry("1200x780")
        self.root.minsize(1100, 700)
        apply_icon(self.root)
        self.events = queue.Queue()
        self.stop_event = threading.Event()
        self.wake_event = threading.Event()
        self.offline = False
        self.worker = None
        self.observer = None
        self.previous = {}
        self.folder = None
        self.backup = None
        self.log_path = None
        self.param_log_path = None
        self.last_sync = None      # 最後一次成功掃描的時間（worker 寫、UI 讀）
        self.disk = None           # (total, used, free) bytes（worker 寫、UI 讀）
        self._disk_shown = None
        self.ever_started = False
        self.folder_var = tk.StringVar()
        self.backup_var = tk.StringVar()
        self.interval_var = tk.StringVar(value=str(DEFAULT_INTERVAL))
        self.autostart_var = tk.BooleanVar(value=False)
        self.notify_var = tk.BooleanVar(value=True)
        self.status_var = tk.StringVar(value="待機中")
        self.sub_var = tk.StringVar(value="尚未開始")
        self.mode_var = tk.StringVar(value="模式：--")
        self.clock_var = tk.StringVar(value="")
        self.today_var = tk.StringVar(value="0")
        self.delta_var = tk.StringVar(value="— 較昨日")
        self.disk_var = tk.StringVar(value="-- GB")
        self.disk_sub_var = tk.StringVar(value="尚未取得")
        self.sync_var = tk.StringVar(value="--")
        self.sync_sub_var = tk.StringVar(value="尚未同步")
        self.home_count_var = tk.StringVar(value="共 0 筆事件")
        self.ev_count_var = tk.StringVar(value="共 0 筆事件")
        self.folder_show_var = tk.StringVar(value="監控資料夾：尚未設定")
        self.backup_show_var = tk.StringVar(value="備份資料夾：尚未設定")
        self.cfg_note_var = tk.StringVar(value="資料夾與輪詢間隔會在按下「開始監控」時套用。")
        self.filter_var = tk.StringVar(value="全部事件")
        self.period_var = tk.StringVar(value=PERIODS[0])
        self.activity_vars = {k: tk.StringVar(value="0") for k in ("new", "mod", "del", "other")}
        self.rows = []             # 全部事件（iid, 時間, 事件, 檔名, 備註, tag）
        self.day_counts = {}       # {"YYYY-MM-DD": {new, mod, del, other}}
        self._eid = 0
        self._diff_cache = {}
        self._cfg_widgets = []
        self.nav = {}
        self.t0 = None
        self.phase = 0
        self._style()
        self._ui()
        self.folder_var.trace_add("write", lambda *a: self._refresh_paths())
        self.backup_var.trace_add("write", lambda *a: self._refresh_paths())
        self.root.after(100, self._dark_titlebar)
        self.root.after(300, self._tick)
        self.root.after(100, self._poll_ui)
        self.root.protocol("WM_DELETE_WINDOW", self.close)

    # ------------------------------------------------------------------ 外觀
    def _style(self):
        st = ttk.Style()
        try: st.theme_use("clam")
        except tk.TclError: pass
        self.root.configure(bg=BG)
        self.root.option_add("*TCombobox*Listbox.background", PANEL2)
        self.root.option_add("*TCombobox*Listbox.foreground", FG)
        self.root.option_add("*TCombobox*Listbox.selectBackground", ACCENT)
        self.root.option_add("*TCombobox*Listbox.selectForeground", "#001820")
        self.root.option_add("*TCombobox*Listbox.font", FONT_UI)
        st.configure(".", background=BG, foreground=FG, fieldbackground=PANEL, bordercolor=BORDER,
                     lightcolor=BORDER, darkcolor=BORDER, troughcolor=PANEL, font=FONT_UI,
                     focuscolor=BG, selectbackground="#17406b", selectforeground="#ffffff")
        st.configure("TFrame", background=BG)
        st.configure("TEntry", fieldbackground=PANEL2, foreground=FG, insertcolor=ACCENT,
                     bordercolor=BORDER, padding=7, font=FONT_UI)
        st.map("TEntry", bordercolor=[("focus", ACCENT)], lightcolor=[("focus", ACCENT)],
               darkcolor=[("focus", ACCENT)], fieldbackground=[("disabled", PANEL)],
               foreground=[("disabled", MUTED)])
        st.configure("TSpinbox", fieldbackground=PANEL2, foreground=FG, insertcolor=ACCENT,
                     bordercolor=BORDER, arrowcolor=ACCENT, background=PANEL2, padding=6, font=FONT_UI)
        st.map("TSpinbox", bordercolor=[("focus", ACCENT)], fieldbackground=[("disabled", PANEL)],
               foreground=[("disabled", MUTED)])
        st.configure("TCombobox", fieldbackground=PANEL2, background=PANEL2, foreground=FG,
                     arrowcolor=ACCENT, bordercolor=BORDER, lightcolor=BORDER, darkcolor=BORDER, padding=5)
        st.map("TCombobox", fieldbackground=[("readonly", PANEL2)], foreground=[("readonly", FG)],
               selectbackground=[("readonly", PANEL2)], selectforeground=[("readonly", FG)],
               bordercolor=[("focus", ACCENT)])
        st.configure("TButton", background=PANEL2, foreground=FG, bordercolor=BORDER, padding=(16, 8),
                     focusthickness=0, font=FONT_UI)
        st.map("TButton", background=[("active", "#17406b"), ("disabled", PANEL)],
               foreground=[("disabled", "#44587c")], bordercolor=[("active", ACCENT), ("disabled", BORDER)])
        st.configure("Accent.TButton", background=ACCENT, foreground="#00131c", bordercolor=ACCENT,
                     font=FONT_UI_B, padding=(18, 9))
        st.map("Accent.TButton", background=[("active", "#5cd0ff"), ("disabled", "#0f3a52")],
               foreground=[("disabled", "#3c6a85")], bordercolor=[("disabled", "#0f3a52")])
        st.configure("Danger.TButton", background="#2a1220", foreground=RED, bordercolor=RED,
                     font=FONT_UI_B, padding=(18, 9))
        st.map("Danger.TButton", background=[("active", "#3d1a2d"), ("disabled", PANEL)],
               foreground=[("disabled", "#5a3a48")], bordercolor=[("disabled", BORDER)])
        st.configure("Treeview", background=PANEL, fieldbackground=PANEL, foreground=FG, rowheight=30,
                     borderwidth=0, font=FONT_UI)
        st.map("Treeview", background=[("selected", "#17406b")], foreground=[("selected", "#ffffff")])
        st.configure("Treeview.Heading", background=PANEL2, foreground=FG, relief="flat",
                     font=FONT_UI_B, padding=(8, 7))
        st.map("Treeview.Heading", background=[("active", "#17406b")])
        st.configure("Vertical.TScrollbar", background=PANEL2, troughcolor=PANEL, bordercolor=PANEL,
                     arrowcolor=ACCENT, lightcolor=PANEL2, darkcolor=PANEL2, arrowsize=14)
        st.map("Vertical.TScrollbar", background=[("active", "#17406b")])

    def _dark_titlebar(self):
        # Windows 10/11：標題列改深色
        if os.name != "nt": return
        try:
            import ctypes
            self.root.update_idletasks()
            hwnd = ctypes.windll.user32.GetParent(self.root.winfo_id())
            val = ctypes.c_int(1)
            for attr in (20, 19):
                if ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(val), ctypes.sizeof(val)) == 0:
                    break
        except Exception:
            pass

    def _card(self, parent):
        return tk.Frame(parent, bg=PANEL, highlightbackground=BORDER, highlightthickness=1, bd=0)

    @staticmethod
    def _short(text, n=64):
        return text if len(text) <= n else "…" + text[-(n - 1):]

    # ------------------------------------------------------------------ 版面骨架
    def _ui(self):
        self.root.columnconfigure(1, weight=1)
        self.root.rowconfigure(0, weight=1)
        self._build_sidebar()

        main = tk.Frame(self.root, bg=BG)
        main.grid(row=0, column=1, sticky="nsew", padx=22, pady=(14, 18))
        main.columnconfigure(0, weight=1)
        main.rowconfigure(2, weight=1)

        # --- 頂部標題列 ---
        head = tk.Frame(main, bg=BG)
        head.grid(row=0, column=0, sticky="ew")
        pill = tk.Frame(head, bg=PANEL, highlightbackground=BORDER, highlightthickness=1)
        pill.pack(side="right")
        self.led = tk.Canvas(pill, width=14, height=14, bg=PANEL, highlightthickness=0)
        self.led.pack(side="left", padx=(14, 6), pady=10)
        self.led_dot = self.led.create_oval(2, 2, 12, 12, fill=MUTED, outline=MUTED)
        tk.Label(pill, textvariable=self.status_var, bg=PANEL, fg=FG, font=FONT_UI_B, width=12,
                 anchor="w").pack(side="left", padx=(0, 14))
        tk.Label(head, text=APP_TITLE, bg=BG, fg=FG, font=FONT_TITLE).pack(side="left")
        tk.Frame(head, bg=BORDER, width=1, height=22).pack(side="left", padx=14)
        tk.Label(head, text="監控資料夾中的變更，自動備份 .par 檔案", bg=BG, fg=MUTED,
                 font=FONT_SMALL).pack(side="left")
        tk.Frame(main, bg=BORDER, height=1).grid(row=1, column=0, sticky="ew", pady=(12, 14))

        # --- 頁面容器 ---
        host = tk.Frame(main, bg=BG)
        host.grid(row=2, column=0, sticky="nsew")
        host.columnconfigure(0, weight=1)
        host.rowconfigure(0, weight=1)
        self.pages = {
            "home": self._build_home(host),
            "events": self._build_events(host),
            "settings": self._build_settings(host),
        }
        for page in self.pages.values():
            page.grid(row=0, column=0, sticky="nsew")
        self.show_page("home")
        self._refresh_paths()
        self._refresh_counts()

    def _build_sidebar(self):
        side = tk.Frame(self.root, bg=SIDEBAR, width=220)
        side.grid(row=0, column=0, sticky="ns")
        side.pack_propagate(False)
        tk.Frame(self.root, bg=BORDER, width=1).grid(row=0, column=0, sticky="nse")
        try:
            self._logo = tk.PhotoImage(file=resource_path(LOGO_FILE))
            tk.Label(side, image=self._logo, bg=SIDEBAR).pack(pady=(26, 8))
        except Exception:
            c = tk.Canvas(side, width=56, height=56, bg=SIDEBAR, highlightthickness=0)
            c.create_oval(3, 3, 53, 53, outline=ACCENT, width=3)
            c.create_text(28, 28, text="P", fill=ACCENT, font=("Consolas", 22, "bold"))
            c.pack(pady=(26, 8))
        tk.Label(side, text=APP_TITLE, bg=SIDEBAR, fg=FG, font=("Microsoft JhengHei UI", 13, "bold")).pack()
        tk.Label(side, text="即時監控 · 自動備份 · 守護資料", bg=SIDEBAR, fg=MUTED,
                 font=("Microsoft JhengHei UI", 8)).pack(pady=(4, 26))
        self._nav_item(side, "home", "⌂", "監控總覽")
        self._nav_item(side, "events", "☰", "事件紀錄")
        self._nav_item(side, "settings", "⚙", "設定")
        tk.Label(side, textvariable=self.clock_var, bg=SIDEBAR, fg=MUTED, font=FONT_MONO).pack(side="bottom", pady=16)

    def _nav_item(self, parent, key, icon, text):
        f = tk.Frame(parent, bg=SIDEBAR, cursor="hand2", highlightthickness=1, highlightbackground=SIDEBAR)
        f.pack(fill="x", padx=12, pady=3)
        i = tk.Label(f, text=icon, bg=SIDEBAR, fg=ACCENT, font=FONT_ICON, width=2)
        i.pack(side="left", padx=(12, 4), pady=9)
        t = tk.Label(f, text=text, bg=SIDEBAR, fg=FG, font=FONT_UI)
        t.pack(side="left")
        for w in (f, i, t):
            w.bind("<Button-1>", lambda e, k=key: self.show_page(k))
        self.nav[key] = (f, i, t)

    def show_page(self, key):
        self.pages[key].tkraise()
        for k, (f, i, t) in self.nav.items():
            on = (k == key)
            bg = NAV_ACTIVE if on else SIDEBAR
            f.configure(bg=bg, highlightbackground=ACCENT if on else SIDEBAR)
            i.configure(bg=bg)
            t.configure(bg=bg)

    # ------------------------------------------------------------------ 頁面：監控總覽
    def _build_home(self, host):
        page = tk.Frame(host, bg=BG)
        page.columnconfigure(0, weight=1)
        page.rowconfigure(2, weight=1)

        # 控制列：按鈕先 pack 到右側，保證「停止監控」一定完整顯示，路徑文字被擠時才縮短
        bar = self._card(page)
        bar.grid(row=0, column=0, sticky="ew")
        inner = tk.Frame(bar, bg=PANEL)
        inner.pack(fill="x", padx=18, pady=14)
        self.stop_btn = ttk.Button(inner, text="■  停止監控", style="Danger.TButton", width=13,
                                   command=self.stop, state="disabled")
        self.stop_btn.pack(side="right")
        self.start_btn = ttk.Button(inner, text="▶  開始監控", style="Accent.TButton", width=13,
                                    command=self.start)
        self.start_btn.pack(side="right", padx=(0, 10))
        info = tk.Frame(inner, bg=PANEL)
        info.pack(side="left", fill="x", expand=True)
        for var, fg in ((self.folder_show_var, FG), (self.backup_show_var, FG), (self.mode_var, MUTED)):
            tk.Label(info, textvariable=var, bg=PANEL, fg=fg, font=FONT_SMALL, anchor="w").pack(fill="x")
        link = tk.Label(info, text="⚙ 前往設定變更路徑與間隔", bg=PANEL, fg=ACCENT, font=FONT_SMALL,
                        cursor="hand2", anchor="w")
        link.pack(fill="x", pady=(2, 0))
        link.bind("<Button-1>", lambda e: self.show_page("settings"))

        # 統計卡片
        stats = tk.Frame(page, bg=BG)
        stats.grid(row=1, column=0, sticky="ew", pady=(14, 0))
        for i in range(4):
            stats.columnconfigure(i, weight=1)
        self._stat_card(stats, 0, "◉", "監控狀態", self.status_var, self.sub_var)
        self._stat_card(stats, 1, "▤", "今日事件", self.today_var, self.delta_var)
        disk = self._stat_card(stats, 2, "▣", "備份空間（可用）", self.disk_var, self.disk_sub_var, ring=True)
        self._stat_card(stats, 3, "◷", "最後同步", self.sync_var, self.sync_sub_var)

        # 下半：最近事件 + 活動摘要
        low = tk.Frame(page, bg=BG)
        low.grid(row=2, column=0, sticky="nsew", pady=(14, 0))
        low.columnconfigure(0, weight=1)
        low.columnconfigure(1, weight=0, minsize=250)
        low.rowconfigure(0, weight=1)

        log = self._card(low)
        log.grid(row=0, column=0, sticky="nsew", padx=(0, 14))
        log.columnconfigure(0, weight=1)
        log.rowconfigure(1, weight=1)
        top = tk.Frame(log, bg=PANEL)
        top.grid(row=0, column=0, sticky="ew", padx=16, pady=(14, 8))
        tk.Label(top, text="☰", bg=PANEL, fg=ACCENT, font=FONT_ICON).pack(side="left")
        tk.Label(top, text="最近事件", bg=PANEL, fg=FG, font=FONT_CARD_T).pack(side="left", padx=(8, 6))
        tk.Label(top, text="（雙擊事件可查看差異）", bg=PANEL, fg=MUTED, font=FONT_SMALL).pack(side="left")
        more = tk.Label(top, text="查看全部 ›", bg=PANEL, fg=ACCENT, font=FONT_SMALL, cursor="hand2")
        more.pack(side="right")
        more.bind("<Button-1>", lambda e: self.show_page("events"))
        tk.Label(top, textvariable=self.home_count_var, bg=PANEL, fg=MUTED, font=FONT_SMALL).pack(side="right", padx=14)
        wrap, self.home_tree = self._make_tree(log, 8)
        wrap.grid(row=1, column=0, sticky="nsew", padx=16, pady=(0, 14))

        act = self._card(low)
        act.grid(row=0, column=1, sticky="nsew")
        top = tk.Frame(act, bg=PANEL)
        top.pack(fill="x", padx=16, pady=(14, 8))
        tk.Label(top, text="▮▮", bg=PANEL, fg=ACCENT, font=("Segoe UI Symbol", 11)).pack(side="left")
        tk.Label(top, text="活動摘要", bg=PANEL, fg=FG, font=FONT_CARD_T).pack(side="left", padx=(8, 0))
        cb = ttk.Combobox(top, textvariable=self.period_var, values=PERIODS, state="readonly", width=7)
        cb.pack(side="right")
        cb.bind("<<ComboboxSelected>>", lambda e: self._refresh_counts())
        for key, icon, label, color in (("new", "▲", "新增", GREEN), ("mod", "◆", "修改/取代", AMBER),
                                        ("del", "✕", "刪除", RED), ("other", "●", "其他", MUTED)):
            row = tk.Frame(act, bg=PANEL)
            row.pack(fill="x", padx=16, pady=9)
            tk.Label(row, text=icon, bg=PANEL, fg=color, font=FONT_UI_B, width=2).pack(side="left")
            tk.Label(row, text=label, bg=PANEL, fg=FG, font=FONT_UI).pack(side="left", padx=(4, 0))
            tk.Label(row, textvariable=self.activity_vars[key], bg=PANEL, fg=FG,
                     font=("Microsoft JhengHei UI", 12, "bold")).pack(side="right")
        return page

    def _stat_card(self, parent, col, icon, caption, var, subvar, ring=False):
        card = self._card(parent)
        card.grid(row=0, column=col, sticky="nsew", padx=(0 if col == 0 else 12, 0))
        inner = tk.Frame(card, bg=PANEL)
        inner.pack(fill="both", expand=True, padx=14, pady=14)
        tk.Label(inner, text=icon, bg=PANEL, fg=ACCENT, font=("Segoe UI Symbol", 20)).pack(side="left", padx=(0, 10))
        if ring:
            self.ring = tk.Canvas(inner, width=54, height=54, bg=PANEL, highlightthickness=0)
            self.ring.pack(side="right", padx=(6, 0))
            self._draw_ring(None)
        box = tk.Frame(inner, bg=PANEL)
        box.pack(side="left", fill="x", expand=True)
        tk.Label(box, text=caption, bg=PANEL, fg=MUTED, font=FONT_SMALL, anchor="w").pack(fill="x")
        tk.Label(box, textvariable=var, bg=PANEL, fg=FG, font=FONT_BIG, anchor="w").pack(fill="x")
        tk.Label(box, textvariable=subvar, bg=PANEL, fg=MUTED, font=FONT_SMALL, anchor="w").pack(fill="x")
        return card

    def _draw_ring(self, pct):
        c = self.ring
        c.delete("all")
        c.create_oval(6, 6, 48, 48, outline="#16325c", width=6)
        if pct is not None:
            color = RED if pct >= 90 else AMBER if pct >= 75 else ACCENT
            c.create_arc(6, 6, 48, 48, start=90, extent=-min(359.9, max(1.0, pct * 3.6)),
                         style="arc", outline=color, width=6)
        c.create_text(27, 27, text="--" if pct is None else f"{pct:.0f}%", fill=MUTED, font=("Consolas", 9))

    def _make_tree(self, parent, height):
        wrap = tk.Frame(parent, bg=PANEL)
        wrap.columnconfigure(0, weight=1)
        wrap.rowconfigure(0, weight=1)
        tree = ttk.Treeview(wrap, columns=("time", "action", "file", "details"), show="headings",
                            height=height, selectmode="browse")
        for col, title, width, stretch in (("time", "時間", 150, False), ("action", "事件", 105, False),
                                           ("file", "PAR 檔案", 150, False), ("details", "備註", 200, True)):
            tree.heading(col, text=title, anchor="w")
            tree.column(col, width=width, minwidth=70, anchor="w", stretch=stretch)
        tree.grid(row=0, column=0, sticky="nsew")
        ys = ttk.Scrollbar(wrap, orient="vertical", command=tree.yview)
        ys.grid(row=0, column=1, sticky="ns")
        tree.configure(yscrollcommand=ys.set)
        for tag, color in (("start", ACCENT), ("new", GREEN), ("mod", AMBER), ("del", RED)):
            tree.tag_configure(tag, foreground=color)
        tree.bind("<Double-1>", self.show_diff)
        return wrap, tree

    # ------------------------------------------------------------------ 頁面：事件紀錄
    def _build_events(self, host):
        page = tk.Frame(host, bg=BG)
        page.columnconfigure(0, weight=1)
        page.rowconfigure(0, weight=1)
        card = self._card(page)
        card.grid(row=0, column=0, sticky="nsew")
        card.columnconfigure(0, weight=1)
        card.rowconfigure(1, weight=1)
        top = tk.Frame(card, bg=PANEL)
        top.grid(row=0, column=0, sticky="ew", padx=18, pady=(16, 10))
        tk.Label(top, text="☰", bg=PANEL, fg=ACCENT, font=FONT_ICON).pack(side="left")
        tk.Label(top, text="事件紀錄", bg=PANEL, fg=FG, font=FONT_CARD_T).pack(side="left", padx=(8, 6))
        tk.Label(top, text="（雙擊事件可查看差異）", bg=PANEL, fg=MUTED, font=FONT_SMALL).pack(side="left")
        cb = ttk.Combobox(top, textvariable=self.filter_var, values=list(FILTERS), state="readonly", width=10)
        cb.pack(side="right")
        cb.bind("<<ComboboxSelected>>", lambda e: self._refill_events())
        tk.Label(top, textvariable=self.ev_count_var, bg=PANEL, fg=MUTED, font=FONT_SMALL).pack(side="right", padx=14)
        wrap, self.ev_tree = self._make_tree(card, 18)
        wrap.grid(row=1, column=0, sticky="nsew", padx=18, pady=(0, 16))
        return page

    # ------------------------------------------------------------------ 頁面：設定
    def _build_settings(self, host):
        page = tk.Frame(host, bg=BG)
        page.columnconfigure(0, weight=1)

        # --- 區塊 1：資料夾 ---
        body = self._section(page, 0, "▤", "資料夾", "指定要監控的來源，以及存放備份的位置")
        self._path_row(body, 0, "監控資料夾",
                       "可選擇網路磁碟機或輸入 \\\\主機\\分享；含子資料夾；只監控 .par",
                       self.folder_var, self.pick_folder)
        self._path_row(body, 1, "備份資料夾",
                       "存放變更前的舊檔、Log 與參數變更紀錄（不可位於監控資料夾內）",
                       self.backup_var, self.pick_backup)
        btns = tk.Frame(body, bg=PANEL)
        btns.grid(row=2, column=0, sticky="w", pady=(4, 0))
        ttk.Button(btns, text="開啟備份資料夾", command=self.open_backup).pack(side="left")
        ttk.Button(btns, text="開啟 Log", command=self.open_log).pack(side="left", padx=10)
        ttk.Button(btns, text="開啟參數變更紀錄", command=self.open_param_log).pack(side="left")

        # --- 區塊 2：監控選項（開關式列表） ---
        body = self._section(page, 1, "⚙", "監控選項", "調整偵測頻率與提醒方式")
        body.columnconfigure(0, weight=1)
        def make_spin(parent):
            sp = ttk.Spinbox(parent, from_=0.5, to=3600, increment=0.5, textvariable=self.interval_var,
                             width=7, justify="center")
            self._cfg_widgets.append(sp)
            return sp
        self._option_row(body, 0, "輪詢間隔（秒）", "網路磁碟機建議 5 秒以上；最小 0.5 秒", make_spin)
        self._option_row(body, 2, "變更時跳通知", "偵測到新增／修改／刪除時，在狀態列提示",
                         lambda p: Toggle(p, self.notify_var))
        self._option_row(body, 4, "加入 Windows 開機啟動", "於「開始監控」時建立啟動資料夾捷徑",
                         lambda p: Toggle(p, self.autostart_var))

        tk.Label(page, textvariable=self.cfg_note_var, bg=BG, fg=MUTED, font=FONT_SMALL,
                 anchor="w").grid(row=2, column=0, sticky="w", pady=(2, 0))
        return page

    def _section(self, page, row, icon, title, desc):
        card = self._card(page)
        card.grid(row=row, column=0, sticky="ew", pady=(0, 14))
        card.columnconfigure(0, weight=1)
        top = tk.Frame(card, bg=PANEL)
        top.grid(row=0, column=0, sticky="ew", padx=20, pady=(16, 0))
        tk.Label(top, text=icon, bg=PANEL, fg=ACCENT, font=FONT_ICON).pack(side="left")
        tk.Label(top, text=title, bg=PANEL, fg=FG, font=FONT_CARD_T).pack(side="left", padx=(8, 10))
        tk.Label(top, text=desc, bg=PANEL, fg=MUTED, font=FONT_SMALL).pack(side="left")
        tk.Frame(card, bg=BORDER, height=1).grid(row=1, column=0, sticky="ew", padx=20, pady=(12, 12))
        body = tk.Frame(card, bg=PANEL)
        body.grid(row=2, column=0, sticky="ew", padx=20, pady=(0, 16))
        body.columnconfigure(0, weight=1)
        return body

    def _path_row(self, body, row, title, hint, var, cmd):
        f = tk.Frame(body, bg=PANEL)
        f.grid(row=row, column=0, sticky="ew", pady=(0, 12))
        f.columnconfigure(0, weight=1)
        tk.Label(f, text=title, bg=PANEL, fg=FG, font=FONT_UI_B, anchor="w").grid(row=0, column=0, columnspan=2, sticky="w")
        tk.Label(f, text=hint, bg=PANEL, fg=MUTED, font=FONT_SMALL, anchor="w").grid(row=1, column=0, columnspan=2, sticky="w", pady=(2, 6))
        ent = ttk.Entry(f, textvariable=var)
        ent.grid(row=2, column=0, sticky="ew", padx=(0, 10))
        btn = ttk.Button(f, text="選擇…", command=cmd)
        btn.grid(row=2, column=1)
        self._cfg_widgets += [ent, btn]

    def _option_row(self, body, row, title, desc, make):
        f = tk.Frame(body, bg=PANEL)
        f.grid(row=row, column=0, sticky="ew", pady=8)
        f.columnconfigure(0, weight=1)
        tk.Label(f, text=title, bg=PANEL, fg=FG, font=FONT_UI_B, anchor="w").grid(row=0, column=0, sticky="w")
        tk.Label(f, text=desc, bg=PANEL, fg=MUTED, font=FONT_SMALL, anchor="w").grid(row=1, column=0, sticky="w")
        make(f).grid(row=0, column=1, rowspan=2, sticky="e", padx=(12, 0))
        if row < 4:
            tk.Frame(body, bg=BORDER, height=1).grid(row=row + 1, column=0, sticky="ew")

    # ------------------------------------------------------------------ 狀態與統計
    def _refresh_paths(self):
        f, b = self.folder_var.get().strip(), self.backup_var.get().strip()
        self.folder_show_var.set("監控資料夾：" + (self._short(f) if f else "尚未設定"))
        self.backup_show_var.set("備份資料夾：" + (self._short(b) if b else "尚未設定"))

    def _idle_status(self):
        if self.worker and self.worker.is_alive() and not self.stop_event.is_set():
            return "離線" if self.offline else "監控中"
        return "待機中"

    def _bump(self, day, kind):
        d = self.day_counts.setdefault(day, {"new": 0, "mod": 0, "del": 0, "other": 0})
        d[kind] += 1

    def _day_total(self, day):
        d = self.day_counts.get(day)
        return (d["new"] + d["mod"] + d["del"]) if d else 0

    def _refresh_counts(self):
        today = date.today()
        t, y = self._day_total(today.isoformat()), self._day_total((today - timedelta(days=1)).isoformat())
        self.today_var.set(str(t))
        diff = t - y
        self.delta_var.set("— 較昨日" if diff == 0 else f"{'▲ +' if diff > 0 else '▼ −'}{abs(diff)} 較昨日")
        period = self.period_var.get()
        if period == "今日":
            days = {today.isoformat()}
        elif period == "近 7 天":
            days = {(today - timedelta(days=i)).isoformat() for i in range(7)}
        else:
            days = set(self.day_counts)
        for key, var in self.activity_vars.items():
            var.set(str(sum(self.day_counts[d][key] for d in days if d in self.day_counts)))

    def _tick(self):
        # 每 0.5 秒：時鐘、運行時間、狀態燈呼吸、最後同步、備份空間
        self.phase = (self.phase + 1) % 2
        self.clock_var.set(datetime.now().strftime("%Y-%m-%d  %H:%M:%S"))
        running = bool(self.worker and self.worker.is_alive() and not self.stop_event.is_set())
        if running and self.t0:
            sec = int(time.time() - self.t0)
            self.sub_var.set(f"已運行 {sec // 3600:02d}:{sec % 3600 // 60:02d}:{sec % 60:02d} · {len(self.previous)} 個檔案")
            if self.offline:
                color = AMBER if self.phase else "#6b4a1c"
            else:
                color = GREEN if self.phase else "#12894f"
        else:
            self.sub_var.set("已停止" if self.ever_started else "尚未開始")
            color = MUTED
        self.led.itemconfigure(self.led_dot, fill=color, outline=color)
        ls = self.last_sync
        if ls:
            ago = int(time.time() - ls)
            self.sync_var.set(datetime.fromtimestamp(ls).strftime("%H:%M:%S"))
            self.sync_sub_var.set("剛剛" if ago < 2 else f"{ago} 秒前" if ago < 120 else f"{ago // 60} 分鐘前")
        disk = self.disk
        if disk and disk != self._disk_shown:
            self._disk_shown = disk
            total, used, free = disk
            pct = used * 100 / total if total else 0
            self.disk_var.set(f"{free / 1024 ** 3:,.1f} GB")
            self.disk_sub_var.set(f"共 {total / 1024 ** 3:,.0f} GB · 已用 {pct:.0f}%")
            self._draw_ring(pct)
        self.root.after(500, self._tick)

    # ------------------------------------------------------------------ 事件列表
    def _record_event(self, action, name, detail, path=None, old=None, new=None, t=None):
        tag, icon = ACTION_STYLE.get(action, ("start", "●"))
        self._eid += 1
        iid = str(self._eid)
        row = (iid, t or datetime.now().strftime("%Y-%m-%d %H:%M:%S"), f"{icon} {action}", name, detail, tag)
        self.rows.append(row)
        self._diff_cache[iid] = (path, old, new)
        self._bump(date.today().isoformat(), tag if tag in ("new", "mod", "del") else "other")
        self._insert_row(self.home_tree, row, limit=HOME_EVENT_LIMIT)
        if self._filter_match(row):
            self._insert_row(self.ev_tree, row)
        self.home_count_var.set(f"共 {len(self.rows)} 筆事件")
        self.ev_count_var.set(f"共 {len(self.ev_tree.get_children())} 筆事件")
        self._refresh_counts()

    def _insert_row(self, tree, row, limit=None):
        iid, t, action, name, detail, tag = row
        tree.insert("", "end", iid=iid, values=(t, action, name, detail), tags=(tag,))
        tree.see(iid)
        if limit:
            kids = tree.get_children()
            if len(kids) > limit:
                tree.delete(kids[0])

    def _filter_match(self, row):
        want = FILTERS.get(self.filter_var.get())
        return want is None or row[5] == want

    def _refill_events(self):
        self.ev_tree.delete(*self.ev_tree.get_children())
        for row in self.rows:
            if self._filter_match(row):
                self.ev_tree.insert("", "end", iid=row[0], values=row[1:5], tags=(row[5],))
        kids = self.ev_tree.get_children()
        self.ev_count_var.set(f"共 {len(kids)} 筆事件")
        if kids:
            self.ev_tree.see(kids[-1])

    def _load_history(self):
        """從既有 Log 還原每日事件數（供「較昨日」與活動摘要使用）。"""
        self.day_counts = {}
        try:
            with self.log_path.open(encoding="utf-8") as f:
                for line in f:
                    if len(line) < 30 or not line.startswith("["):
                        continue
                    kind = KIND_BY_LOG.get(line[line.find("] ") + 2:].split(" | ", 1)[0])
                    if kind:
                        self._bump(line[1:11], kind)
        except OSError:
            pass

    def pick_folder(self):
        p = filedialog.askdirectory(title="選擇監控資料夾")
        if p: self.folder_var.set(p)

    def pick_backup(self):
        p = filedialog.askdirectory(title="選擇備份資料夾")
        if p: self.backup_var.set(p)

    def start(self):
        folder_text = self.folder_var.get().strip()
        backup_text = self.backup_var.get().strip()
        folder = os.path.normpath(os.path.abspath(folder_text)) if folder_text else ""
        if not folder or not os.path.isdir(folder):
            self.show_page("settings"); messagebox.showerror("設定錯誤", "請選擇有效的監控資料夾。"); return
        if not backup_text:
            self.show_page("settings"); messagebox.showerror("設定錯誤", "請選擇備份資料夾。"); return
        try:
            interval = float(self.interval_var.get())
            if interval < 0.5: raise ValueError
        except ValueError:
            self.show_page("settings"); messagebox.showerror("設定錯誤", "輪詢間隔需為 0.5 秒以上。"); return
        backup = Path(os.path.normpath(os.path.abspath(backup_text)))
        if self._inside(str(backup), folder):
            self.show_page("settings"); messagebox.showerror("設定錯誤", "備份資料夾不可位於監控資料夾內。"); return
        try: backup.mkdir(parents=True, exist_ok=True)
        except OSError as e:
            self.show_page("settings"); messagebox.showerror("設定錯誤", f"無法建立備份資料夾：{e}"); return

        self.folder, self.backup = folder, backup
        self.log_path = backup / "ParamVault.log"
        self.param_log_path = backup / "ParamVault_參數變更.log"
        old_log = backup / "PAR_monitor.log"          # 沿用舊版 Log（改名保留歷史）
        if old_log.exists() and not self.log_path.exists():
            try: old_log.replace(self.log_path)
            except OSError: self.log_path = old_log
        self.previous = scan(folder, {}) or {}
        self._load_history()
        self.last_sync, self.disk, self._disk_shown = time.time(), None, None
        self.ever_started = True
        self.offline = False
        self.stop_event.clear()
        self.wake_event.clear()
        self._log(f"監控開始 | folder={folder} | backup={backup} | 網路路徑={is_network_path(folder)} | 初始檔案數={len(self.previous)}")
        self._record_event("開始", "-", f"初始掃描 {len(self.previous)} 個 PAR")
        self._start_watchdog()
        net = is_network_path(folder)
        self.mode_var.set(f"模式：{'網路磁碟機 · 輪詢' if net else '本機 · 即時事件 + 輪詢'} · 每 {interval:g} 秒")
        self.t0 = time.time()
        self.worker = threading.Thread(target=self._poll_loop, args=(interval,), daemon=True)
        self.worker.start()
        self.start_btn.configure(state="disabled")
        self.stop_btn.configure(state="normal")
        self.status_var.set("監控中")
        self._set_cfg_enabled(False)
        if self.autostart_var.get():
            try:
                self.install_autostart()
                self._log("已設定 Windows 開機啟動捷徑")
            except Exception as e:
                self._log(f"開機啟動設定失敗 | {e}")

    @staticmethod
    def _inside(child: str, parent: str) -> bool:
        """child 是否等於或位於 parent 內（同時比對原路徑與解析後路徑，涵蓋磁碟機代號 vs UNC）。"""
        def norm(x): return os.path.normcase(os.path.normpath(x)).rstrip("\\/")
        pairs = [(child, parent)]
        try: pairs.append((str(Path(child).resolve()), str(Path(parent).resolve())))
        except OSError: pass
        return any(norm(c) == norm(p) or norm(c).startswith(norm(p) + os.sep) for c, p in pairs)

    def _start_watchdog(self):
        if is_network_path(self.folder):
            # SMB 網路磁碟機不保證送出檔案變更通知，直接以輪詢為準
            self.observer = None
            self._log("監控目標為網路磁碟機：不使用 watchdog，改用輪詢")
            return
        try:
            from watchdog.observers import Observer
            from watchdog.events import FileSystemEventHandler
            app = self
            class Handler(FileSystemEventHandler):
                def on_any_event(self, event):
                    if event.is_directory: return
                    src = getattr(event, "src_path", "")
                    dest = getattr(event, "dest_path", "")
                    if src.lower().endswith(".par") or dest.lower().endswith(".par"):
                        app.wake_event.set()
            self.observer = Observer()
            self.observer.schedule(Handler(), str(self.folder), recursive=True)
            self.observer.start()
            self._log("即時事件監控已啟動（watchdog）")
        except ImportError:
            self.observer = None
            self._log("未安裝 watchdog，使用輪詢監控；可執行 pip install watchdog")
        except Exception as e:
            self.observer = None
            self._log(f"即時監控啟動失敗，改用輪詢 | {e}")

    def _poll_loop(self, interval):
        cycle, missing, last_disk = 0, {}, 0.0
        while not self.stop_event.is_set():
            cycle += 1
            current = scan(self.folder, self.previous, force_full=(cycle % FULL_VERIFY_EVERY == 0))
            if current is None:
                if not self.offline:
                    self.offline = True
                    self._log("監控資料夾無法存取（網路磁碟機可能中斷），暫停比對，等待恢復")
                    self.events.put(("state", "offline"))
            else:
                if self.offline:
                    self.offline = False
                    self._log("監控資料夾已恢復存取，繼續比對")
                    self.events.put(("state", "online"))
                old_keys, new_keys = set(self.previous), set(current)
                for path in sorted(new_keys - old_keys):
                    self._change("新增", path, None, current[path][1])
                for path in sorted(old_keys & new_keys):
                    missing.pop(path, None)
                    old_data, new_data = self.previous[path][1], current[path][1]
                    if old_data != new_data:
                        self._change("修改/取代", path, old_data, new_data)
                for path in sorted(old_keys - new_keys):
                    missing[path] = missing.get(path, 0) + 1
                    if missing[path] >= DELETE_CONFIRM_CYCLES:
                        missing.pop(path)
                        self._change("刪除", path, self.previous[path][1], None)
                    else:
                        current[path] = self.previous[path]   # 先保留，下一輪仍找不到才算刪除
                self.previous = current
                self.last_sync = time.time()
            if time.time() - last_disk >= DISK_REFRESH_SEC:
                last_disk = time.time()
                try:
                    u = shutil.disk_usage(str(self.backup))
                    self.disk = (u.total, u.used, u.free)
                except OSError:
                    pass
            self.wake_event.wait(interval)
            self.wake_event.clear()
        self.events.put(("status", "已停止"))

    def _change(self, action, path, old, new):
        src = Path(path)
        rel = self._relative(src)
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
        # 只備份「變更前的舊檔」（內容取自掃描快取）；變更後版本與差異檔不再存檔。
        if old is not None:
            self._save_bytes(old, rel, f"BEFORE_{stamp}")
        if old is not None and new is not None:
            detail = summarize_changes(old, new, fmt=FormatChain(get_builtin_format(), src), file_no=file_number(src), par_path=src)
            if detail is None:   # 非參數格式或只有空白／換行差異 → 退回雜湊與大小
                detail = f"內容已變更（無參數差異） before={sha256_bytes(old)[:12]}({len(old)}B) after={sha256_bytes(new)[:12]}({len(new)}B)"
        elif new is not None:
            detail = f"新檔案（{len(new)}B）"
        else:
            detail = f"檔案已刪除（原 {len(old)}B）" if old is not None else "檔案已刪除"
        parsed = old is not None and new is not None and not detail.startswith("內容已變更")
        msg = f"{action} | {detail}" if parsed else f"{action} | file={path} | {detail}"
        self._log(msg)
        if old is not None and new is not None:      # 參數紀錄檔：只放「修改」，改多少列多少（不截斷）
            full = summarize_changes(old, new, limit=None, fmt=FormatChain(get_builtin_format(), src),
                                     file_no=file_number(src), par_path=src) if parsed else None
            self._log_param(f"{action} | {full}" if full else msg)
        self.events.put(("event", (datetime.now().strftime("%Y-%m-%d %H:%M:%S"), action, src.name, detail, path, old, new)))
        if self.notify_var.get():
            self.events.put(("notify", f"{action}: {src.name}"))

    def _relative(self, path):
        try: return Path(os.path.relpath(str(path), self.folder))
        except ValueError: return Path(path.name)

    def _save_bytes(self, data, rel, prefix):
        dest_dir = self.backup / "versions" / rel.parent
        dest_dir.mkdir(parents=True, exist_ok=True)
        dest = dest_dir / f"{rel.stem}_{prefix}{rel.suffix}"
        dest.write_bytes(data)
        return dest

    def _log(self, message):
        line = f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f')}] {message}\n"
        try:
            with self.log_path.open("a", encoding="utf-8") as f: f.write(line)
        except Exception: pass

    def _log_param(self, message):
        line = f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f')}] {message}\n"
        try:
            with self.param_log_path.open("a", encoding="utf-8") as f: f.write(line)
        except Exception: pass

    def _set_cfg_enabled(self, enabled):
        for w in self._cfg_widgets:
            try: w.configure(state="normal" if enabled else "disabled")
            except tk.TclError: pass
        self.cfg_note_var.set("資料夾與輪詢間隔會在按下「開始監控」時套用。" if enabled
                              else "監控中：資料夾與輪詢間隔已鎖定，停止監控後才能修改。")

    def _poll_ui(self):
        try:
            while True:
                kind, payload = self.events.get_nowait()
                if kind == "event":
                    t, action, name, detail, path, old, new = payload
                    self._record_event(action, name, detail, path, old, new, t)
                elif kind == "notify":
                    self.status_var.set("有變更：" + payload)
                    self.root.after(2200, lambda: self.status_var.set(self._idle_status())
                                    if self.status_var.get().startswith("有變更") else None)
                elif kind == "status":
                    self.status_var.set("待機中")
                    self.start_btn.configure(state="normal")
                    self.stop_btn.configure(state="disabled")
                    self._set_cfg_enabled(True)
                elif kind == "state":
                    self.status_var.set(self._idle_status())
        except queue.Empty:
            pass
        self.root.after(120, self._poll_ui)

    def show_diff(self, event=None):
        tree = event.widget if event is not None and isinstance(event.widget, ttk.Treeview) else self.ev_tree
        selected = tree.selection()
        if not selected: return
        data = self._diff_cache.get(selected[0])
        if not data: return
        path, old, new = data
        if old is None or new is None:
            messagebox.showinfo("差異", "新增、刪除或開始事件沒有前後兩份內容可比較。"); return
        win = tk.Toplevel(self.root)
        win.title(f"差異 - {Path(path).name}")
        win.geometry("940x600")
        win.configure(bg=BG)
        head = tk.Label(win, text=f"◆ DIFF  {Path(path).name}", bg=BG, fg=CYAN, font=("Consolas", 12, "bold"), anchor="w")
        head.pack(fill="x", padx=14, pady=(12, 6))
        frame = tk.Frame(win, bg=BORDER, padx=1, pady=1)
        frame.pack(fill="both", expand=True, padx=14, pady=(0, 14))
        text = tk.Text(frame, wrap="none", bg=PANEL, fg=FG, insertbackground=CYAN, font=FONT_MONO,
                       relief="flat", borderwidth=0, padx=10, pady=8, selectbackground="#17406b")
        ys = ttk.Scrollbar(frame, orient="vertical", command=text.yview)
        xs = ttk.Scrollbar(frame, orient="horizontal", command=text.xview)
        text.configure(yscrollcommand=ys.set, xscrollcommand=xs.set)
        ys.pack(side="right", fill="y"); xs.pack(side="bottom", fill="x")
        text.pack(fill="both", expand=True)
        text.tag_configure("add", foreground=GREEN, background="#0c2a22")
        text.tag_configure("rem", foreground=RED, background="#2e1220")
        text.tag_configure("hunk", foreground=CYAN)
        text.tag_configure("hdr", foreground=AMBER)
        lines = list(difflib.unified_diff(decode_text(old).splitlines(), decode_text(new).splitlines(),
            fromfile="修改前", tofile="修改後", lineterm=""))
        if not lines:
            text.insert("1.0", "無文字差異")
        for ln in lines:
            if ln.startswith(("+++", "---")): tag = "hdr"
            elif ln.startswith("@@"): tag = "hunk"
            elif ln.startswith("+"): tag = "add"
            elif ln.startswith("-"): tag = "rem"
            else: tag = ""
            text.insert("end", ln + "\n", tag)
        text.configure(state="disabled")

    def stop(self):
        self.stop_event.set()
        self.wake_event.set()
        if self.observer:
            try: self.observer.stop(); self.observer.join(timeout=2)
            except Exception: pass
            self.observer = None
        self.status_var.set("停止中…")
        self.stop_btn.configure(state="disabled")

    def open_backup(self):
        if self.backup and self.backup.exists(): self._open_path(self.backup)
        else: messagebox.showinfo("提示", "請先開始監控。")

    def open_param_log(self):
        if self.param_log_path and self.param_log_path.exists(): self._open_path(self.param_log_path)
        else: messagebox.showinfo("提示", "尚未產生參數變更紀錄。")

    def open_log(self):
        if self.log_path and self.log_path.exists(): self._open_path(self.log_path)
        else: messagebox.showinfo("提示", "尚未產生 Log。")

    @staticmethod
    def _open_path(path):
        try:
            if os.name == "nt": os.startfile(str(path))
            elif sys.platform == "darwin": subprocess.Popen(["open", str(path)])
            else: subprocess.Popen(["xdg-open", str(path)])
        except Exception as e: messagebox.showerror("開啟失敗", str(e))

    def install_autostart(self):
        if os.name != "nt": raise RuntimeError("此功能只支援 Windows")
        startup = Path(os.environ.get("APPDATA", "")) / "Microsoft/Windows/Start Menu/Programs/Startup"
        startup.mkdir(parents=True, exist_ok=True)
        target = startup / "ParamVault.bat"
        exe = Path(sys.executable)
        if getattr(sys, "frozen", False):
            command = f'"{exe}"'
        else:
            command = f'"{exe}" "{Path(__file__).resolve()}"'
        target.write_text("@echo off\r\nstart \"\" " + command + "\r\n", encoding="utf-8")
        return target

    def close(self):
        self.stop_event.set()
        self.wake_event.set()
        if self.observer:
            try: self.observer.stop(); self.observer.join(timeout=1)
            except Exception: pass
        self.root.destroy()

# ---- 內建 InspectParamFormat.ini 對照表（zlib+base64；InspectParamFormat.ini 與 Z04 內容相同，Q11 少 3 個外形檢測參數） ----
_INI_BLOB = (
    "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"
    "kQ52NnYaS/X/AdlOkfE="
)


if __name__ == "__main__":
    root = tk.Tk()
    app = ParMonitor(root)
    root.mainloop()
