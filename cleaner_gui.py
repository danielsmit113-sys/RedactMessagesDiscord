#!/usr/bin/env python3
"""
Discord self-message cleaner - GUI (advanced)
=============================================

Tkinter front end for editing and/or deleting your own Discord messages,
with filters, run modes, a searchable channel picker, pause/resume and a
live activity log.

Only touches messages authored by the account whose token you provide.

WARNING
-------
Automating a *user* account ("self-botting") is against Discord's Terms of
Service and can get your account banned. Use at your own risk.

Run:  python cleaner_gui.py
Needs: pip install requests   (tkinter ships with Python on Windows)
"""

import json
import os
import queue
import re
import sys
import threading
import time
from datetime import datetime, timezone
from urllib.parse import quote

import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk

try:
    import requests
except ImportError:
    sys.exit('The "requests" package is required. Run:  pip install requests')

API = "https://discord.com/api/v10"
HERE = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(HERE, "config.json")
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) self-cleaner/1.0"
DISCORD_EPOCH = 1420070400000

# --- palette (mirrors the REDACT website tokens) ---------------------------
VOID     = "#0E1014"   # window background
PANEL    = "#16191F"   # raised panels
PANEL_2  = "#1B1F26"   # rows / inset wells
LINE     = "#262B34"
LINE_HOT = "#333A45"
TEXT     = "#DEE3E9"
MUTED    = "#7D8694"
MUTED_DIM = "#5A626E"
FIELD    = "#0D1014"   # entry / log wells

CYAN      = "#4FD1E0"  # SAFE accent
AMBER     = "#F0A93B"  # ARMED accent
CYAN_INK  = "#06232A"  # ink on cyan
AMBER_INK = "#2A1B02"  # ink on amber
DANGER    = "#F0564A"
OK        = "#5FC77E"

# aliases so existing references keep resolving
BG    = VOID
SAFE  = CYAN
ARMED = AMBER

FONT_UI   = ("Segoe UI", 9)
FONT_UI_B = ("Segoe UI", 9, "bold")
FONT_BAN  = ("Segoe UI Semibold", 12)
FONT_MONO = ("Consolas", 9)
FONT_EY   = ("Segoe UI", 8, "bold")   # eyebrow / panel titles
# color emoji: Segoe UI Emoji (Win), Apple Color Emoji (mac), Noto (Linux).
# tk picks the first that exists; the rest are graceful fallbacks.
EMOJI_FAMILY = "Segoe UI Emoji"
FONT_EMOJI    = (EMOJI_FAMILY, 18)
FONT_EMOJI_SM = (EMOJI_FAMILY, 15)

MODES = ["Edit, then delete", "Delete only", "Edit only"]
RTARGETS = ["All messages", "Only from user ID", "Most recent N"]
RASSIGN = ["Same emoji each time", "Cycle through list", "Random from list"]

# Per-route rate-limit floors (seconds), from Discord's documented limits:
#   delete message  = 5 / 1s per channel  -> ~0.25s edge; floor 0.30s for headroom
#   reactions       = 1 / 0.25s per channel -> floor 0.30s (300ms is the norm)
#   edit message    = 5 / 5s per channel  -> 1 per second; floor 1.00s
# These are minimums the UI will not let you go below, and also the defaults.
FLOOR_EDIT   = 1.0
FLOOR_DELETE = 0.3
FLOOR_REACT  = 0.3
FLOOR_MSG    = 0.0   # gap between messages has no per-route limit of its own
FLOOR_READ   = 0.3   # paging reads share the 50/s global; keep a small floor
FLOOR_SEARCH = 2.0   # watch-mode poll interval floor (avoid hammering the API)

CUSTOM_EMOJI = re.compile(r"^<a?:([A-Za-z0-9_]+):(\d+)>$")


def _blend(c1, c2, t):
    """Linear blend between two #rrggbb colors; t in 0..1."""
    t = max(0.0, min(1.0, t))
    a = tuple(int(c1[i:i + 2], 16) for i in (1, 3, 5))
    b = tuple(int(c2[i:i + 2], 16) for i in (1, 3, 5))
    m = tuple(round(a[i] + (b[i] - a[i]) * t) for i in range(3))
    return "#%02X%02X%02X" % m


def encode_emoji(e):
    """Return the API path segment for a reaction emoji.

    Unicode emoji are percent-encoded. Custom emoji written as <:name:id>
    or <a:name:id> become name:id (Discord's required form).
    """
    e = e.strip()
    m = CUSTOM_EMOJI.match(e)
    if m:
        return quote(f"{m.group(1)}:{m.group(2)}", safe="")
    return quote(e, safe="")


def snowflake_for(dt):
    """Lowest snowflake id at a given UTC datetime (for the `before` cursor)."""
    ms = int(dt.timestamp() * 1000)
    return str(max(0, (ms - DISCORD_EPOCH)) << 22)


class Cleaner:
    def __init__(self, root):
        self.root = root
        self.q = queue.Queue()
        self.stop_flag = threading.Event()
        self.pause_flag = threading.Event()
        self.worker = None
        self.items = []          # {id, kind, label, checked}
        self._selcount = None

        self.scanned = self.matched = self.done = self.failed = 0

        root.title("Discord message cleaner")
        root.geometry("1040x860")
        root.minsize(900, 760)
        root.configure(bg=BG)

        self._vars()
        self._style()
        self._delay_cache = {}
        self._floor_vars = getattr(self, "_floor_vars", {})
        self._build()
        self._refresh_delay_cache()
        self._load_config()
        self._refresh_banner()
        self._running = False
        self.root.after(100, self._pump)
        self.root.after(200, self._pulse)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    # -- state ------------------------------------------------------------
    def _vars(self):
        self.v_token    = tk.StringVar()
        self.v_user     = tk.StringVar()
        self.v_edit     = tk.StringVar(value=".")
        self.v_mode     = tk.StringVar(value=MODES[0])
        self.v_dry      = tk.BooleanVar(value=True)
        self.v_edelay   = tk.DoubleVar(value=FLOOR_EDIT)
        self.v_ddelay   = tk.DoubleVar(value=FLOOR_DELETE)
        self.v_rdelay   = tk.DoubleVar(value=FLOOR_READ)
        self.v_manual   = tk.StringVar()
        self.v_manual_name = tk.StringVar()
        self.v_search   = tk.StringVar()
        self.v_contains = tk.StringVar()
        self.v_regex    = tk.BooleanVar(value=False)
        self.v_noattach = tk.BooleanVar(value=False)
        self.v_after    = tk.StringVar()
        self.v_before   = tk.StringVar()
        self.v_selcount = tk.StringVar(value="0 selected")
        self.v_stats    = tk.StringVar(
            value="Scanned 0   Matched 0   Done 0   Failed 0")
        self.v_banner   = tk.StringVar()
        self.v_search.trace_add("write", lambda *_: self._redraw())

        # --- React tab ---
        self.v_rchan    = tk.StringVar()                 # channel id
        self.v_rtarget  = tk.StringVar(value=RTARGETS[0])
        self.v_ruser    = tk.StringVar()                 # target author id
        self.v_rcount   = tk.IntVar(value=50)            # recent N
        self.v_remoji   = tk.StringVar()                 # emoji input
        self.v_rassign  = tk.StringVar(value=RASSIGN[0])
        self.v_r_react_delay = tk.DoubleVar(value=FLOOR_REACT)  # cooldown / reaction
        self.v_r_msg_delay   = tk.DoubleVar(value=FLOOR_MSG)    # cooldown / message
        self.v_rdry     = tk.BooleanVar(value=True)
        self.v_prescan  = tk.BooleanVar(value=True)
        self.v_rwatch   = tk.BooleanVar(value=False)     # keep watching for new
        self.v_rsearch  = tk.DoubleVar(value=5.0)        # poll interval (s)
        self.emojis     = []                             # list[str]
        self.active_tab = "clean"
        self.v_selcount_e = tk.StringVar(value="0 emoji")

    def _style(self):
        # pick a color-emoji font that actually exists on this OS
        global FONT_EMOJI, FONT_EMOJI_SM
        try:
            from tkinter import font as tkfont
            fams = set(tkfont.families(self.root))
            for cand in ("Segoe UI Emoji", "Apple Color Emoji",
                         "Noto Color Emoji", "Noto Emoji", "Twemoji",
                         "Segoe UI Symbol"):
                if cand in fams:
                    FONT_EMOJI = (cand, 18)
                    FONT_EMOJI_SM = (cand, 15)
                    break
        except Exception:
            pass
        st = ttk.Style()
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        st.configure("Treeview", background=PANEL, fieldbackground=PANEL,
                     foreground=TEXT, bordercolor=LINE, borderwidth=0,
                     rowheight=24, font=FONT_MONO)
        st.map("Treeview", background=[("selected", PANEL_2)],
               foreground=[("selected", TEXT)])
        st.configure("Treeview.Heading", background=FIELD, foreground=MUTED_DIM,
                     borderwidth=0, font=FONT_EY)
        st.map("Treeview.Heading", background=[("active", FIELD)])
        st.configure("Redact.Horizontal.TProgressbar", background=SAFE,
                     troughcolor=FIELD, borderwidth=0, thickness=6)
        st.configure("TCombobox", fieldbackground=FIELD, background=LINE,
                     foreground=TEXT, arrowcolor=MUTED, bordercolor=LINE,
                     selectbackground=FIELD, selectforeground=TEXT)
        st.map("TCombobox", fieldbackground=[("readonly", FIELD)],
               foreground=[("readonly", TEXT)])
        st.configure("Redact.TNotebook", background=VOID, borderwidth=0,
                     tabmargins=[0, 0, 0, 6])
        st.configure("Redact.TNotebook.Tab", background=VOID, foreground=MUTED,
                     borderwidth=0, padding=[16, 8], font=FONT_UI_B)
        st.map("Redact.TNotebook.Tab",
               background=[("selected", PANEL), ("active", PANEL_2)],
               foreground=[("selected", TEXT), ("active", TEXT)])
        st.configure("Redact.Vertical.TScrollbar", background=PANEL_2,
                     troughcolor=VOID, borderwidth=0, arrowcolor=MUTED)
        self._ttk = st
        # widgets whose colour follows the SAFE/ARMED accent
        self._accentables = []   # (widget, role) role in {"bg","fg","hl"}

    def _track(self, widget, role):
        self._accentables.append((widget, role))
        return widget

    def _is_armed(self):
        if getattr(self, "active_tab", "clean") == "react":
            return not self.v_rdry.get()
        return self.v_dry is not None and not self.v_dry.get()

    def _recolor_accent(self):
        armed = self._is_armed()
        acc = ARMED if armed else SAFE
        ink = AMBER_INK if armed else CYAN_INK
        for w, role in self._accentables:
            try:
                if role == "fg":
                    w.configure(fg=acc)
                elif role == "hl":
                    w.configure(highlightcolor=acc)
                elif role == "bg":
                    w.configure(bg=acc)
                elif role == "fill":
                    w.configure(bg=acc, fg=ink, activebackground=acc,
                                activeforeground=ink, highlightbackground=acc)
            except tk.TclError:
                pass
        try:
            self._ttk.configure("Redact.Horizontal.TProgressbar", background=acc)
        except tk.TclError:
            pass

    # -- widget helpers ---------------------------------------------------
    def _btn(self, parent, text, cmd, fg=TEXT, bold=False, accent=False,
             fill=False):
        if fill:
            b = tk.Button(parent, text=text, command=cmd, bg=SAFE, fg=CYAN_INK,
                          font=("Segoe UI Semibold", 10), relief="flat",
                          activebackground=SAFE, activeforeground=CYAN_INK,
                          cursor="hand2", padx=16, pady=9, borderwidth=0,
                          highlightthickness=1, highlightbackground=SAFE,
                          disabledforeground=CYAN_INK)
            self._track(b, "fill")
            return b
        b = tk.Button(parent, text=text, command=cmd, bg=PANEL_2, fg=fg,
                      font=FONT_UI_B if bold else FONT_UI, relief="flat",
                      activebackground=LINE_HOT, activeforeground=TEXT,
                      cursor="hand2", padx=13, pady=6, borderwidth=0,
                      highlightthickness=1, highlightbackground=LINE,
                      disabledforeground=MUTED_DIM)
        if accent:
            self._track(b, "fg")
        return b

    def _entry(self, parent, var, show=None, width=None):
        e = tk.Entry(parent, textvariable=var, bg=FIELD, fg=TEXT,
                     insertbackground=TEXT, relief="flat", font=FONT_MONO,
                     show=show or "", width=width or 20,
                     highlightthickness=1, highlightbackground=LINE,
                     highlightcolor=SAFE)
        return self._track(e, "hl")

    def _lbl(self, parent, text, fg=MUTED, font=FONT_UI, bg=PANEL):
        return tk.Label(parent, text=text, bg=bg, fg=fg, font=font)

    def _chk(self, parent, text, var, cmd=None):
        return tk.Checkbutton(parent, text=text, variable=var, command=cmd,
                              bg=PANEL, fg=TEXT, selectcolor=FIELD,
                              activebackground=PANEL, activeforeground=TEXT,
                              font=FONT_UI, anchor="w", highlightthickness=0,
                              cursor="hand2")

    def _panel(self, parent, title):
        outer = tk.Frame(parent, bg=PANEL, highlightthickness=1,
                         highlightbackground=LINE)
        head = tk.Frame(outer, bg=PANEL)
        head.pack(anchor="w", fill="x", padx=13, pady=(10, 0))
        tk.Frame(head, bg=SAFE, width=8, height=8).pack(side="left", pady=1)
        self._track(head.winfo_children()[-1], "bg")
        self._lbl(head, "  " + title.upper(), fg=MUTED_DIM,
                  font=FONT_EY).pack(side="left")
        inner = tk.Frame(outer, bg=PANEL)
        inner.pack(fill="both", expand=True, padx=13, pady=(7, 12))
        return outer, inner

    def _scroll_area(self, parent):
        """A borderless vertical scroll region; returns the inner frame."""
        canvas = tk.Canvas(parent, bg=BG, highlightthickness=0, borderwidth=0)
        sb = ttk.Scrollbar(parent, orient="vertical", command=canvas.yview,
                           style="Redact.Vertical.TScrollbar")
        inner = tk.Frame(canvas, bg=BG)
        win = canvas.create_window((0, 0), window=inner, anchor="nw")
        canvas.configure(yscrollcommand=sb.set)
        canvas.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

        def _resize(_=None):
            canvas.itemconfigure(win, width=canvas.winfo_width())
            canvas.configure(scrollregion=canvas.bbox("all"))
        inner.bind("<Configure>", _resize)
        canvas.bind("<Configure>", _resize)

        def _wheel(ev):
            step = -1 if (ev.delta > 0 or ev.num == 4) else 1
            canvas.yview_scroll(step, "units")
            return "break"
        canvas.bind("<Enter>", lambda e: canvas.bind_all("<MouseWheel>", _wheel))
        canvas.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))
        inner.bind("<Enter>", lambda e: canvas.bind_all("<MouseWheel>", _wheel))
        inner.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))
        canvas.bind("<Button-4>", _wheel)
        canvas.bind("<Button-5>", _wheel)
        return inner

    def _scroll_panel(self, parent, title):
        """Like _panel, but the content area scrolls if it overflows."""
        outer = tk.Frame(parent, bg=PANEL, highlightthickness=1,
                         highlightbackground=LINE)
        head = tk.Frame(outer, bg=PANEL)
        head.pack(anchor="w", fill="x", padx=13, pady=(10, 4))
        tk.Frame(head, bg=SAFE, width=8, height=8).pack(side="left", pady=1)
        self._track(head.winfo_children()[-1], "bg")
        self._lbl(head, "  " + title.upper(), fg=MUTED_DIM,
                  font=FONT_EY).pack(side="left")

        holder = tk.Frame(outer, bg=PANEL)
        holder.pack(fill="both", expand=True, padx=(13, 4), pady=(0, 10))
        canvas = tk.Canvas(holder, bg=PANEL, highlightthickness=0, borderwidth=0)
        sb = ttk.Scrollbar(holder, orient="vertical", command=canvas.yview,
                           style="Redact.Vertical.TScrollbar")
        inner = tk.Frame(canvas, bg=PANEL)
        win = canvas.create_window((0, 0), window=inner, anchor="nw")
        canvas.configure(yscrollcommand=sb.set)
        canvas.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

        def _resize(_=None):
            canvas.itemconfigure(win, width=canvas.winfo_width())
            canvas.configure(scrollregion=canvas.bbox("all"))
        inner.bind("<Configure>", _resize)
        canvas.bind("<Configure>", _resize)

        # mousewheel only while the pointer is over this canvas
        def _wheel(ev):
            step = -1 if (ev.delta > 0 or ev.num == 4) else 1
            canvas.yview_scroll(step, "units")
            return "break"
        for w in (canvas, inner):
            w.bind("<Enter>", lambda e, c=canvas: c.bind_all(
                "<MouseWheel>", _wheel))
            w.bind("<Leave>", lambda e, c=canvas: c.unbind_all("<MouseWheel>"))
            w.bind("<Button-4>", _wheel)
            w.bind("<Button-5>", _wheel)
        return outer, inner

    def _spin(self, parent, var, floor=0.3):
        if not hasattr(self, "_floors"):
            self._floors = {}
        if not hasattr(self, "_floor_vars"):
            self._floor_vars = {}
        self._floors[str(var)] = floor
        self._floor_vars[str(var)] = (var, floor)
        sb = tk.Spinbox(parent, from_=floor, to=30.0, increment=0.1,
                        textvariable=var, width=6, bg=FIELD, fg=TEXT,
                        font=FONT_MONO, relief="flat", buttonbackground=PANEL_2,
                        insertbackground=TEXT, highlightthickness=1,
                        highlightbackground=LINE, readonlybackground=FIELD)
        # clamp up to the floor whenever the value is committed or focus leaves
        def clamp(*_):
            try:
                if float(var.get()) < floor:
                    var.set(floor)
            except (tk.TclError, ValueError):
                var.set(floor)
        sb.configure(command=clamp)
        sb.bind("<FocusOut>", clamp)
        sb.bind("<Return>", clamp)
        return sb

    def _floor_of(self, var):
        return getattr(self, "_floors", {}).get(str(var), 0.0)

    # -- layout -----------------------------------------------------------
    def _build(self):
        self.root.rowconfigure(2, weight=3)   # body
        self.root.rowconfigure(4, weight=2)   # activity  <-- always visible
        self.root.columnconfigure(0, weight=1)

        # brand header (mirrors the website nav)
        head = tk.Frame(self.root, bg=VOID)
        head.grid(row=0, column=0, sticky="ew", padx=14, pady=(12, 4))
        mark = tk.Frame(head, bg=VOID, highlightthickness=1,
                        highlightbackground=SAFE, width=22, height=22)
        mark.pack_propagate(False)
        mark.pack(side="left")
        self._track(mark, "hl")
        bar = tk.Frame(mark, bg=SAFE, width=9, height=2)
        bar.place(relx=.5, rely=.5, anchor="center")
        self._track(bar, "bg")
        tk.Label(head, text="  REDACT", bg=VOID, fg=TEXT,
                 font=("Segoe UI Semibold", 13)).pack(side="left")
        tk.Label(head, text="overwrite \u00b7 then erase", bg=VOID, fg=MUTED_DIM,
                 font=("Segoe UI", 9)).pack(side="left", padx=(10, 0))
        tk.Label(head, text="local \u00b7 your account only", bg=VOID,
                 fg=MUTED_DIM, font=FONT_MONO).pack(side="right")

        self.banner = tk.Label(self.root, textvariable=self.v_banner,
                               font=FONT_BAN, bg=SAFE, fg=CYAN_INK, pady=11)
        self.banner.grid(row=1, column=0, sticky="ew")

        body = tk.Frame(self.root, bg=BG)
        body.grid(row=2, column=0, sticky="nsew", padx=14, pady=(12, 8))
        body.columnconfigure(0, weight=1)
        body.rowconfigure(1, weight=1)

        # shared account panel, above the tabs
        self._build_account(body)

        # tabbed area
        nb = ttk.Notebook(body, style="Redact.TNotebook")
        nb.grid(row=1, column=0, sticky="nsew")
        self.nb = nb

        clean = tk.Frame(nb, bg=BG)
        clean.columnconfigure(0, weight=3, uniform="c")
        clean.columnconfigure(1, weight=2, uniform="c")
        clean.rowconfigure(0, weight=1)
        nb.add(clean, text="  Clean messages  ")

        react = tk.Frame(nb, bg=BG)
        react.columnconfigure(0, weight=1)
        react.rowconfigure(0, weight=1)
        nb.add(react, text="  React to messages  ")

        self._build_targets(clean)
        self._build_right(clean)
        self._build_react(react)
        self._build_actionbar()
        self._build_activity()

        nb.bind("<<NotebookTabChanged>>", self._on_tab)

    def _build_account(self, body):
        acc_o, acc = self._panel(body, "Account")
        acc_o.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        acc.columnconfigure(1, weight=1)
        self._lbl(acc, "Token").grid(row=0, column=0, sticky="w", padx=(0, 8))
        self.e_token = self._entry(acc, self.v_token, show="\u2022")
        self.e_token.grid(row=0, column=1, sticky="ew")
        self.b_eye = self._btn(acc, "Show", self._toggle_token)
        self.b_eye.grid(row=0, column=2, padx=(8, 0))
        self._lbl(acc, "User ID").grid(row=1, column=0, sticky="w",
                                       padx=(0, 8), pady=(8, 0))
        self._entry(acc, self.v_user).grid(row=1, column=1, sticky="ew",
                                           pady=(8, 0))
        self.b_load = self._btn(acc, "Load my channels", self._start_load,
                                fg=SAFE, bold=True, accent=True)
        self.b_load.grid(row=1, column=2, padx=(8, 0), pady=(8, 0))

    def _build_targets(self, body):
        tg_o, tg = self._panel(body, "Targets to clean")
        tg_o.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        tg.rowconfigure(2, weight=1)
        tg.columnconfigure(0, weight=1)

        top = tk.Frame(tg, bg=PANEL)
        top.grid(row=0, column=0, sticky="ew", pady=(0, 6))
        self._lbl(top, "Filter").pack(side="left", padx=(0, 8))
        self._entry(top, self.v_search).pack(side="left", fill="x", expand=True)

        bar = tk.Frame(tg, bg=PANEL)
        bar.grid(row=1, column=0, sticky="ew", pady=(0, 7))
        self._btn(bar, "Select all", lambda: self._mark(True)).pack(side="left")
        self._btn(bar, "Clear all", lambda: self._mark(False)).pack(side="left",
                                                                    padx=6)
        self._btn(bar, "Import IDs\u2026", self._import_ids).pack(side="left")
        tk.Label(bar, textvariable=self.v_selcount, bg=PANEL, fg=MUTED,
                 font=FONT_UI).pack(side="right")

        wrap = tk.Frame(tg, bg=PANEL)
        wrap.grid(row=2, column=0, sticky="nsew")
        self.tree = ttk.Treeview(wrap, columns=("on", "kind", "label"),
                                 show="headings", selectmode="none")
        self.tree.heading("on", text="")
        self.tree.heading("kind", text="Type")
        self.tree.heading("label", text="Channel / conversation")
        self.tree.column("on", width=34, anchor="center", stretch=False)
        self.tree.column("kind", width=64, anchor="w", stretch=False)
        self.tree.column("label", width=300, anchor="w")
        sb = ttk.Scrollbar(wrap, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.bind("<Button-1>", self._on_click)
        self.tree.tag_configure("on", foreground=TEXT)
        self.tree.tag_configure("off", foreground=MUTED)

        add = tk.Frame(tg, bg=PANEL)
        add.grid(row=3, column=0, sticky="ew", pady=(7, 0))
        add.columnconfigure(1, weight=2)
        add.columnconfigure(3, weight=3)
        self._lbl(add, "Add ID").grid(row=0, column=0, padx=(0, 6))
        self._entry(add, self.v_manual).grid(row=0, column=1, sticky="ew")
        self._lbl(add, "name").grid(row=0, column=2, padx=(8, 6))
        ne = self._entry(add, self.v_manual_name)
        ne.grid(row=0, column=3, sticky="ew")
        ne.bind("<Return>", lambda *_: self._add_manual())
        self._btn(add, "Add", self._add_manual).grid(row=0, column=4,
                                                     padx=(8, 0))
        self._lbl(add, "double-click a row to rename it", fg=MUTED_DIM,
                  font=("Segoe UI", 8)).grid(row=1, column=0, columnspan=5,
                                             sticky="w", pady=(4, 0))
        self.tree.bind("<Double-Button-1>", self._rename_row)

    def _build_right(self, body):
        holder = tk.Frame(body, bg=BG)
        holder.grid(row=0, column=1, sticky="nsew")
        right = self._scroll_area(holder)
        right.columnconfigure(0, weight=1)

        # options
        op_o, op = self._panel(right, "Options")
        op_o.grid(row=0, column=0, sticky="ew")
        op.columnconfigure(1, weight=1)
        self._lbl(op, "Mode").grid(row=0, column=0, sticky="w")
        cb = ttk.Combobox(op, textvariable=self.v_mode, values=MODES,
                          state="readonly", font=FONT_UI, width=16)
        cb.grid(row=0, column=1, sticky="e")
        cb.bind("<<ComboboxSelected>>", lambda *_: self._refresh_banner())
        self._lbl(op, "Replace text with").grid(row=1, column=0, sticky="w",
                                                pady=(7, 0))
        self._entry(op, self.v_edit, width=10).grid(row=1, column=1, sticky="e",
                                                    pady=(7, 0))
        for i, (name, var, floor) in enumerate(
                [("Pause after edit", self.v_edelay, FLOOR_EDIT),
                 ("Pause after delete", self.v_ddelay, FLOOR_DELETE),
                 ("Pause between pages", self.v_rdelay, FLOOR_READ)], start=2):
            self._lbl(op, f"{name}  (min {floor:g}s)").grid(
                row=i, column=0, sticky="w", pady=(7, 0))
            self._spin(op, var, floor=floor).grid(row=i, column=1, sticky="e",
                                                  pady=(7, 0))
        self._chk(op, "Dry run \u2014 only list what matches", self.v_dry,
                  self._refresh_banner).grid(row=5, column=0, columnspan=2,
                                             sticky="w", pady=(10, 0))

        # filters
        fl_o, fl = self._panel(right, "Filters (optional)")
        fl_o.grid(row=1, column=0, sticky="ew", pady=(10, 0))
        fl.columnconfigure(1, weight=1)
        self._lbl(fl, "Contains").grid(row=0, column=0, sticky="w")
        self._entry(fl, self.v_contains, width=14).grid(row=0, column=1,
                                                        sticky="ew", padx=(8, 0))
        self._chk(fl, "Treat as regular expression", self.v_regex).grid(
            row=1, column=0, columnspan=2, sticky="w", pady=(4, 0))
        self._chk(fl, "Skip messages that have attachments",
                  self.v_noattach).grid(row=2, column=0, columnspan=2,
                                        sticky="w")
        self._lbl(fl, "After date").grid(row=3, column=0, sticky="w", pady=(6, 0))
        self._entry(fl, self.v_after, width=14).grid(row=3, column=1, sticky="ew",
                                                     padx=(8, 0), pady=(6, 0))
        self._lbl(fl, "Before date").grid(row=4, column=0, sticky="w")
        self._entry(fl, self.v_before, width=14).grid(row=4, column=1,
                                                      sticky="ew", padx=(8, 0))
        self._lbl(fl, "dates as YYYY-MM-DD", fg=MUTED,
                  font=("Segoe UI", 8)).grid(row=5, column=0, columnspan=2,
                                             sticky="w", pady=(3, 0))

    # -- react tab --------------------------------------------------------
    def _build_react(self, tab):
        tab.columnconfigure(0, weight=3, uniform="rc")
        tab.columnconfigure(1, weight=2, uniform="rc")
        tab.rowconfigure(0, weight=1)

        # left: emoji list
        em_o, em = self._panel(tab, "Emoji pool")
        em_o.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        em.rowconfigure(2, weight=1)
        em.columnconfigure(0, weight=1)

        add = tk.Frame(em, bg=PANEL)
        add.grid(row=0, column=0, sticky="ew", pady=(0, 6))
        self._lbl(add, "Add").pack(side="left", padx=(0, 8))
        e = self._entry(add, self.v_remoji)
        e.pack(side="left", fill="x", expand=True)
        e.bind("<Return>", lambda *_: self._emoji_add())
        self._btn(add, "Add", self._emoji_add).pack(side="left", padx=(8, 0))

        quickbar = tk.Frame(em, bg=PANEL)
        quickbar.grid(row=1, column=0, sticky="ew", pady=(0, 7))
        self._lbl(quickbar, "quick").pack(side="left", padx=(0, 6))
        for q in ("\U0001F990", "\U0001F921", "\U0001F480", "\U0001F44D",
                  "\U0001F525", "\U0001F440"):
            b = tk.Button(quickbar, text=q, command=lambda x=q: self._emoji_add(x),
                          bg=PANEL_2, fg=TEXT, relief="flat", cursor="hand2",
                          font=FONT_EMOJI_SM, width=2, pady=1, borderwidth=0,
                          activebackground=LINE_HOT, highlightthickness=1,
                          highlightbackground=LINE)
            b.pack(side="left", padx=2)

        # emoji chips render on a canvas so we can size them big, colour
        # them, and animate additions/removals.
        wrap = tk.Frame(em, bg=PANEL)
        wrap.grid(row=2, column=0, sticky="nsew")
        self.emoji_canvas = tk.Canvas(wrap, bg=FIELD, highlightthickness=1,
                                      highlightbackground=LINE, borderwidth=0)
        ecsb = ttk.Scrollbar(wrap, orient="vertical",
                             command=self.emoji_canvas.yview,
                             style="Redact.Vertical.TScrollbar")
        self.emoji_canvas.configure(yscrollcommand=ecsb.set)
        self.emoji_canvas.pack(side="left", fill="both", expand=True)
        ecsb.pack(side="right", fill="y")
        self.emoji_holder = tk.Frame(self.emoji_canvas, bg=FIELD)
        self._emoji_win = self.emoji_canvas.create_window(
            (0, 0), window=self.emoji_holder, anchor="nw")
        self.emoji_canvas.bind(
            "<Configure>",
            lambda e: self.emoji_canvas.itemconfigure(self._emoji_win,
                                                      width=e.width))
        self.emoji_holder.bind(
            "<Configure>",
            lambda e: self.emoji_canvas.configure(
                scrollregion=self.emoji_canvas.bbox("all")))
        self._emoji_selected = None
        self._emoji_widgets = {}   # emoji -> chip frame

        rm = tk.Frame(em, bg=PANEL)
        rm.grid(row=3, column=0, sticky="ew", pady=(7, 0))
        self._btn(rm, "Remove selected", self._emoji_remove).pack(side="left")
        self._btn(rm, "Clear", self._emoji_clear).pack(side="left", padx=6)
        tk.Label(rm, textvariable=self.v_selcount_e, bg=PANEL, fg=MUTED,
                 font=FONT_UI).pack(side="right")

        # right: targeting + cooldowns (scrolls if it overflows)
        rt_o, rt = self._scroll_panel(tab, "Where & how")
        rt_o.grid(row=0, column=1, sticky="nsew")
        rt.columnconfigure(1, weight=1)

        self._lbl(rt, "Channel ID").grid(row=0, column=0, sticky="w")
        self._entry(rt, self.v_rchan, width=16).grid(row=0, column=1,
                                                     sticky="ew", padx=(8, 0))
        self._lbl(rt, "React to").grid(row=1, column=0, sticky="w", pady=(9, 0))
        cb = ttk.Combobox(rt, textvariable=self.v_rtarget, values=RTARGETS,
                          state="readonly", font=FONT_UI, width=16)
        cb.grid(row=1, column=1, sticky="e", pady=(9, 0))
        cb.bind("<<ComboboxSelected>>", lambda *_: self._react_target_ui())

        # conditional row (user id / N) lives in its own frame
        self.react_cond = tk.Frame(rt, bg=PANEL)
        self.react_cond.grid(row=2, column=0, columnspan=2, sticky="ew",
                             pady=(7, 0))
        self.react_cond.columnconfigure(1, weight=1)
        self._lbl(rt, "Emoji order").grid(row=3, column=0, sticky="w",
                                          pady=(9, 0))
        ca = ttk.Combobox(rt, textvariable=self.v_rassign, values=RASSIGN,
                          state="readonly", font=FONT_UI, width=16)
        ca.grid(row=3, column=1, sticky="e", pady=(9, 0))

        self._lbl(rt, f"Cooldown / reaction  (min {FLOOR_REACT:g}s)").grid(
            row=4, column=0, sticky="w", pady=(9, 0))
        self._spin(rt, self.v_r_react_delay, floor=FLOOR_REACT).grid(
            row=4, column=1, sticky="e", pady=(9, 0))
        self._lbl(rt, "Cooldown / message").grid(row=5, column=0, sticky="w",
                                                 pady=(7, 0))
        self._spin(rt, self.v_r_msg_delay, floor=FLOOR_MSG).grid(
            row=5, column=1, sticky="e", pady=(7, 0))
        self._chk(rt, "Dry run \u2014 only list what it would react to",
                  self.v_rdry, self._refresh_state).grid(
            row=6, column=0, columnspan=2, sticky="w", pady=(12, 0))
        self._chk(rt, "Fast pre-scan \u2014 find existing reactions, then skip "
                      "them", self.v_prescan).grid(
            row=7, column=0, columnspan=2, sticky="w", pady=(2, 0))
        self._chk(rt, "Keep watching \u2014 react to new messages as they arrive",
                  self.v_rwatch, self._refresh_state).grid(
            row=8, column=0, columnspan=2, sticky="w", pady=(2, 0))
        self._lbl(rt, f"Search delay  (min {FLOOR_SEARCH:g}s)").grid(
            row=9, column=0, sticky="w", pady=(6, 0))
        self._spin(rt, self.v_rsearch, floor=FLOOR_SEARCH).grid(
            row=9, column=1, sticky="e", pady=(6, 0))
        self._lbl(rt, "Reacts as you. Custom emoji: paste <:name:id>.",
                  fg=MUTED_DIM, font=("Segoe UI", 8)).grid(
            row=10, column=0, columnspan=2, sticky="w", pady=(9, 0))

        self._react_target_ui()

    def _react_target_ui(self):
        for w in self.react_cond.winfo_children():
            w.destroy()
        mode = self.v_rtarget.get()
        if mode == "Only from user ID":
            self._lbl(self.react_cond, "Author ID").grid(row=0, column=0,
                                                         sticky="w")
            self._entry(self.react_cond, self.v_ruser, width=16).grid(
                row=0, column=1, sticky="ew", padx=(8, 0))
        elif mode == "Most recent N":
            self._lbl(self.react_cond, "How many").grid(row=0, column=0,
                                                       sticky="w")
            tk.Spinbox(self.react_cond, from_=1, to=100000, increment=10,
                       textvariable=self.v_rcount, width=8, bg=FIELD, fg=TEXT,
                       font=FONT_MONO, relief="flat", buttonbackground=PANEL_2,
                       insertbackground=TEXT, highlightthickness=1,
                       highlightbackground=LINE).grid(row=0, column=1,
                                                      sticky="e", padx=(8, 0))

    def _emoji_add(self, val=None):
        e = (val if val is not None else self.v_remoji.get()).strip()
        if not e:
            return
        if e in self.emojis:
            if val is None:
                self.v_remoji.set("")
            # flash the existing chip so the user sees why nothing happened
            self._emoji_flash(e)
            return
        self.emojis.append(e)
        self._emoji_add_chip(e)
        if val is None:
            self.v_remoji.set("")
        self._emoji_count()

    def _emoji_add_chip(self, e):
        chip = tk.Frame(self.emoji_holder, bg=PANEL_2, highlightthickness=1,
                        highlightbackground=LINE, cursor="hand2")
        m = CUSTOM_EMOJI.match(e)
        label = (":" + m.group(1) + ":") if m else e
        fnt = FONT_UI if m else FONT_EMOJI
        lab = tk.Label(chip, text=label, bg=PANEL_2, fg=TEXT, font=fnt,
                       padx=9, pady=4)
        lab.pack()
        for w in (chip, lab):
            w.bind("<Button-1>", lambda ev, x=e: self._emoji_select(x))
        self._emoji_widgets[e] = (chip, lab)
        self._emoji_reflow()
        self._emoji_pop(lab)

    def _emoji_reflow(self):
        cols = 6
        for i, e in enumerate(self.emojis):
            pair = self._emoji_widgets.get(e)
            if pair:
                pair[0].grid(row=i // cols, column=i % cols, padx=4, pady=4,
                             sticky="w")
        self.emoji_holder.update_idletasks()

    def _emoji_select(self, e):
        self._emoji_selected = e
        for k, (chip, lab) in self._emoji_widgets.items():
            on = (k == e)
            chip.configure(highlightbackground=SAFE if on else LINE,
                           bg=PANEL if on else PANEL_2)
            lab.configure(bg=PANEL if on else PANEL_2)

    def _emoji_pop(self, lab, step=0):
        # colour flash = reliable cross-platform "pop" on add
        seq = [SAFE, "#7FE0EC", "#B7ECF2", TEXT]
        if step >= len(seq):
            return
        try:
            lab.configure(fg=seq[step])
        except tk.TclError:
            return
        self.root.after(70, lambda: self._emoji_pop(lab, step + 1))

    def _emoji_flash(self, e, n=0):
        pair = self._emoji_widgets.get(e)
        if not pair or n > 5:
            if pair:
                pair[0].configure(highlightbackground=LINE)
            return
        pair[0].configure(highlightbackground=AMBER if n % 2 == 0 else LINE)
        self.root.after(90, lambda: self._emoji_flash(e, n + 1))

    def _emoji_remove(self):
        e = self._emoji_selected
        if e is None:
            e = self.emojis[-1] if self.emojis else None
            if e is None:
                return
        pair = self._emoji_widgets.pop(e, None)
        if pair:
            pair[0].destroy()
        if e in self.emojis:
            self.emojis.remove(e)
        self._emoji_selected = None
        self._emoji_reflow()
        self._emoji_count()

    def _emoji_clear(self):
        for chip, _lab in self._emoji_widgets.values():
            chip.destroy()
        self._emoji_widgets = {}
        self.emojis = []
        self._emoji_selected = None
        self._emoji_count()

    def _emoji_count(self):
        self.v_selcount_e.set(f"{len(self.emojis)} emoji")

    def _on_tab(self, *_):
        try:
            idx = self.nb.index(self.nb.select())
        except tk.TclError:
            idx = 0
        self.active_tab = "react" if idx == 1 else "clean"
        self._refresh_state()

    def _refresh_state(self):
        """Update banner + Start button for whichever tab is active."""
        if self.active_tab == "react":
            watch = self.v_rwatch.get()
            if self.v_rdry.get():
                self.v_banner.set("SAFE  \u00b7  DRY RUN \u2014 lists the "
                                  "reactions it would add, changes nothing")
                self.banner.configure(bg=SAFE, fg=CYAN_INK)
                self.b_start.configure(text="Preview reactions")
            else:
                self.v_banner.set(
                    ("ARMED  \u00b7  watching \u2014 will react to new messages "
                     "as they arrive" if watch else
                     "ARMED  \u00b7  will add reactions as you to the messages "
                     "you chose"))
                self.banner.configure(bg=ARMED, fg=AMBER_INK)
                self.b_start.configure(
                    text="Start watching" if watch else "Start reacting")
            if hasattr(self, "_accentables"):
                self._recolor_accent()
        else:
            self._refresh_banner()

    def _build_actionbar(self):
        """Full-width run controls — always visible, never clipped."""
        outer = tk.Frame(self.root, bg=PANEL, highlightthickness=1,
                         highlightbackground=LINE)
        outer.grid(row=3, column=0, sticky="ew", padx=14, pady=(0, 8))
        row = tk.Frame(outer, bg=PANEL)
        row.pack(fill="x", padx=13, pady=11)

        self.b_start = self._btn(row, "Start dry run", self._start_active,
                                 fill=True)
        self.b_start.pack(side="left")
        self.b_pause = self._btn(row, "Pause", self._toggle_pause)
        self.b_pause.pack(side="left", padx=(8, 0))
        self.b_pause.configure(state="disabled")
        self.b_stop = self._btn(row, "Stop", self._stop, fg=DANGER, bold=True)
        self.b_stop.pack(side="left", padx=(8, 0))
        self.b_stop.configure(state="disabled")

        self.live_dot = tk.Label(row, text="", bg=PANEL, fg=SAFE,
                                  font=FONT_MONO, width=10, anchor="w")
        self.live_dot.pack(side="left", padx=(14, 0))

        self._btn(row, "Save settings", self._save_config).pack(side="right")
        tk.Label(row, textvariable=self.v_stats, bg=PANEL, fg=TEXT,
                 font=FONT_MONO).pack(side="right", padx=(0, 16))

        barwrap = tk.Frame(outer, bg=PANEL)
        barwrap.pack(fill="x", padx=13, pady=(0, 11))
        self.bar = ttk.Progressbar(barwrap, mode="indeterminate",
                                   style="Redact.Horizontal.TProgressbar")
        self.bar.pack(fill="x")

    def _build_activity(self):
        lg_o, lg = self._panel(self.root, "Activity")
        lg_o.grid(row=4, column=0, sticky="nsew", padx=14, pady=(0, 14))
        lg.rowconfigure(1, weight=1)
        lg.columnconfigure(0, weight=1)
        tb = tk.Frame(lg, bg=PANEL)
        tb.grid(row=0, column=0, sticky="ew", pady=(0, 6))
        self._btn(tb, "Clear", self._clear_log).pack(side="left")
        self._btn(tb, "Save log\u2026", self._save_log).pack(side="left", padx=6)
        wrap = tk.Frame(lg, bg=PANEL)
        wrap.grid(row=1, column=0, sticky="nsew")
        self.log = tk.Text(wrap, height=8, bg=FIELD, fg=TEXT, font=FONT_MONO,
                           relief="flat", wrap="none", insertbackground=TEXT,
                           padx=10, pady=8,
                           highlightthickness=1, highlightbackground=LINE)
        lsb = ttk.Scrollbar(wrap, orient="vertical", command=self.log.yview)
        self.log.configure(yscrollcommand=lsb.set, state="disabled")
        self.log.pack(side="left", fill="both", expand=True)
        lsb.pack(side="right", fill="y")
        for tag, col in (("info", TEXT), ("muted", MUTED), ("ok", OK),
                         ("warn", ARMED), ("err", DANGER), ("safe", SAFE)):
            self.log.tag_configure(tag, foreground=col)
        self._log("Fill in your token, then load your channels.", "muted")

    # -- small UI actions -------------------------------------------------
    def _toggle_token(self):
        hidden = self.e_token.cget("show") != ""
        self.e_token.configure(show="" if hidden else "\u2022")
        self.b_eye.configure(text="Hide" if hidden else "Show")

    def _refresh_banner(self):
        mode = self.v_mode.get()
        verb = {"Edit, then delete": "edit and delete",
                "Delete only": "delete",
                "Edit only": "edit"}.get(mode, "change")
        if self.v_dry.get():
            self.v_banner.set(f"SAFE  \u00b7  DRY RUN \u2014 nothing will be "
                              f"changed  (mode: {verb})")
            self.banner.configure(bg=SAFE, fg=CYAN_INK)
            self.b_start.configure(text="Start dry run")
        else:
            self.v_banner.set(f"ARMED  \u00b7  will {verb} your messages "
                              f"\u2014 cannot be undone")
            self.banner.configure(bg=ARMED, fg=AMBER_INK)
            self.b_start.configure(text=f"Start ({verb})")
        if hasattr(self, "_accentables"):
            self._recolor_accent()

    def _log(self, msg, tag="info"):
        self.log.configure(state="normal")
        self.log.insert("end", msg + "\n", tag)
        self.log.see("end")
        self.log.configure(state="disabled")

    def _clear_log(self):
        self.log.configure(state="normal")
        self.log.delete("1.0", "end")
        self.log.configure(state="disabled")

    def _save_log(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".txt", filetypes=[("Text", "*.txt")],
            initialfile="cleaner_log.txt")
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(self.log.get("1.0", "end"))
            self._log(f"Saved log to {path}", "ok")
        except Exception as e:
            self._log(f"Could not save log: {e}", "err")

    def _stats(self):
        self.v_stats.set(f"Scanned {self.scanned}   Matched {self.matched}"
                         f"   Done {self.done}   Failed {self.failed}")

    # -- target list ------------------------------------------------------
    def _visible(self):
        q = self.v_search.get().strip().lower()
        out = []
        for i, it in enumerate(self.items):
            if not q or q in it["label"].lower() or q in it["id"]:
                out.append(i)
        return out

    def _redraw(self):
        self.tree.delete(*self.tree.get_children())
        for i in self._visible():
            it = self.items[i]
            self.tree.insert("", "end", iid=str(i),
                             values=("\u2713" if it["checked"] else "",
                                     it["kind"], it["label"]),
                             tags=("on" if it["checked"] else "off",))
        self.v_selcount.set(f"{len(self._selected())} selected")

    def _on_click(self, event):
        row = self.tree.identify_row(event.y)
        if not row:
            return
        idx = int(row)
        self.items[idx]["checked"] = not self.items[idx]["checked"]
        self._redraw()

    def _mark(self, state):
        for i in self._visible():
            self.items[i]["checked"] = state
        self._redraw()

    def _add_item(self, cid, kind, label, checked=False):
        cid = str(cid).strip()
        if not cid or any(x["id"] == cid for x in self.items):
            return False
        self.items.append({"id": cid, "kind": kind,
                           "label": label, "checked": checked})
        return True

    def _add_manual(self):
        cid = self.v_manual.get().strip()
        if not cid.isdigit():
            messagebox.showwarning(
                "Not an ID",
                "A channel ID is all digits. With Developer Mode on, "
                "right-click a channel \u2192 Copy Channel ID.")
            return
        name = self.v_manual_name.get().strip() or "added by hand"
        if self._add_item(cid, "manual", name, checked=True):
            self.v_manual.set("")
            self.v_manual_name.set("")
            self._redraw()
        else:
            messagebox.showinfo("Already listed", "That ID is already here.")

    def _rename_row(self, event):
        row = self.tree.identify_row(event.y)
        if not row:
            return "break"
        idx = int(row)
        it = self.items[idx]
        current = "" if it["label"] in ("from config", "added by hand") \
            else it["label"]
        new = simpledialog.askstring(
            "Rename", f"Name for {it['kind']} {it['id']}:",
            initialvalue=current, parent=self.root)
        if new is not None:
            it["label"] = new.strip() or it["label"]
            self._redraw()
        return "break"

    def _selected(self):
        return [it for it in self.items if it["checked"]]

    # -- mass import ------------------------------------------------------
    @staticmethod
    def _parse_import(text):
        """Parse pasted IDs. Accepts one per line; optional name after the
        id separated by comma, tab, pipe, '=' or whitespace. Also pulls the
        id out of a channel URL. Returns list of (id, name-or-None)."""
        out, seen = [], set()
        for raw in text.splitlines():
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            # channel URL -> last long number
            url = re.search(r"/channels/(?:@me|\d+)/(\d{15,25})", line)
            if url:
                cid, name = url.group(1), ""
            else:
                m = re.match(r"^\s*(\d{15,25})\s*(?:[,\t|=]\s*|\s+)?(.*)$", line)
                if not m:
                    continue
                cid, name = m.group(1), (m.group(2) or "").strip()
            if cid in seen:
                continue
            seen.add(cid)
            out.append((cid, name or None))
        return out

    def _import_ids(self):
        win = tk.Toplevel(self.root)
        win.title("Import channel / DM IDs")
        win.configure(bg=VOID)
        win.geometry("460x420")
        win.transient(self.root)
        tk.Label(win, text="Paste IDs \u2014 one per line. Optional name after "
                           "the ID:", bg=VOID, fg=TEXT, font=FONT_UI,
                 anchor="w", justify="left").pack(fill="x", padx=14, pady=(14, 2))
        tk.Label(win, text="123456789012345678\n123456789012345678, Main chat\n"
                           "https://discord.com/channels/@me/1234567890",
                 bg=VOID, fg=MUTED_DIM, font=FONT_MONO, anchor="w",
                 justify="left").pack(fill="x", padx=14, pady=(0, 8))
        txt = tk.Text(win, height=12, bg=FIELD, fg=TEXT, font=FONT_MONO,
                      relief="flat", insertbackground=TEXT, wrap="word",
                      highlightthickness=1, highlightbackground=LINE)
        txt.pack(fill="both", expand=True, padx=14)
        txt.focus_set()
        row = tk.Frame(win, bg=VOID)
        row.pack(fill="x", padx=14, pady=12)
        auto = tk.BooleanVar(value=True)
        self._chk(row, "Auto-fetch names from Discord for un-named IDs",
                  auto).pack(side="left")

        def do_import():
            pairs = self._parse_import(txt.get("1.0", "end"))
            win.destroy()
            if not pairs:
                messagebox.showinfo("Nothing to import",
                                    "No valid IDs found in that text.")
                return
            added, dupes, need = 0, 0, []
            for cid, name in pairs:
                if any(x["id"] == cid for x in self.items):
                    dupes += 1
                    continue
                label = name or "importing\u2026"
                if self._add_item(cid, "channel", label, checked=True):
                    added += 1
                    if not name:
                        need.append(cid)
            self._redraw()
            self._log(f"Imported {added} ID(s)"
                      + (f", {dupes} already listed" if dupes else "") + ".",
                      "ok")
            if need and auto.get() and self.v_token.get().strip():
                self._fetch_names(need)
            elif need and not self.v_token.get().strip():
                self._log("Paste your token to auto-fetch names for imported "
                          "IDs.", "warn")

        btns = tk.Frame(win, bg=VOID)
        btns.pack(fill="x", padx=14, pady=(0, 14))
        self._btn(btns, "Import", do_import, fill=True).pack(side="left")
        self._btn(btns, "Cancel", win.destroy).pack(side="left", padx=(8, 0))

    def _fetch_names(self, ids):
        """Resolve real channel/DM names in the background."""
        if getattr(self, "_naming", False):
            return
        self._naming = True
        self._log(f"Fetching names for {len(ids)} channel(s)\u2026", "safe")
        threading.Thread(target=self._name_worker, args=(list(ids),),
                         daemon=True).start()

    def _name_worker(self, ids):
        try:
            s = self._session()
            for cid in ids:
                if self.stop_flag.is_set():
                    break
                r = self._req(s, "GET", f"{API}/channels/{cid}")
                name, kind = None, "channel"
                if r is not None and r.status_code == 200:
                    ch = r.json()
                    ctype = ch.get("type")
                    if ctype in (1, 3):   # DM / group DM
                        kind = "dm"
                        who = ", ".join(x.get("username", "?")
                                        for x in ch.get("recipients", []))
                        name = who or ch.get("name") or "DM"
                    else:
                        gid = ch.get("guild_id")
                        cname = ch.get("name") or "channel"
                        name = f"#{cname}"
                        if gid:
                            gr = self._req(s, "GET", f"{API}/guilds/{gid}")
                            if gr is not None and gr.status_code == 200:
                                name = f"{gr.json().get('name','')} \u2014 #{cname}"
                    self.q.put(("rename", cid, name, kind))
                elif r is not None and r.status_code in (403, 404):
                    self.q.put(("rename", cid, "(no access)", "channel"))
                time.sleep(self._cd(self.v_rdelay))
        finally:
            self.q.put(("naming_done",))

    # -- filters ----------------------------------------------------------
    def _parse_date(self, s):
        s = (s or "").strip()
        if not s:
            return None
        return datetime.strptime(s, "%Y-%m-%d").replace(tzinfo=timezone.utc)

    def _compile_filters(self):
        """Validate filter inputs; return a spec dict. Raises ValueError."""
        contains = self.v_contains.get().strip()
        rx = None
        if contains and self.v_regex.get():
            try:
                rx = re.compile(contains, re.IGNORECASE)
            except re.error as e:
                raise ValueError(f"Bad regular expression: {e}")
        try:
            after = self._parse_date(self.v_after.get())
        except ValueError:
            raise ValueError("After date must look like 2024-01-31.")
        try:
            before = self._parse_date(self.v_before.get())
        except ValueError:
            raise ValueError("Before date must look like 2024-01-31.")
        if after and before and after > before:
            raise ValueError("After date is later than before date.")
        return {"contains": contains, "regex": rx,
                "no_attach": bool(self.v_noattach.get()),
                "after": after, "before": before}

    def _match(self, m, spec):
        if spec["no_attach"] and m.get("attachments"):
            return False
        text = m.get("content") or ""
        if spec["contains"]:
            if spec["regex"] is not None:
                if not spec["regex"].search(text):
                    return False
            elif spec["contains"].lower() not in text.lower():
                return False
        if spec["after"] or spec["before"]:
            ts = m.get("timestamp")
            if not ts:
                return False
            try:
                when = datetime.fromisoformat(ts)
            except ValueError:
                return False
            if spec["after"] and when < spec["after"]:
                return False
            if spec["before"] and when >= spec["before"]:
                return False
        return True

    # -- config -----------------------------------------------------------
    def _load_config(self):
        if not os.path.exists(CONFIG_PATH):
            return
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                cfg = json.load(f)
        except Exception as e:
            self._log(f"Could not read config.json: {e}", "err")
            return
        for key, var in (("token", self.v_token), ("user_id", self.v_user),
                         ("edit_text", self.v_edit)):
            val = str(cfg.get(key, "") or "")
            if val and not val.startswith("PASTE_"):
                var.set(val)
        for key, var, floor in (("edit_delay", self.v_edelay, FLOOR_EDIT),
                                 ("delete_delay", self.v_ddelay, FLOOR_DELETE),
                                 ("read_delay", self.v_rdelay, FLOOR_READ)):
            try:
                var.set(max(floor, float(cfg.get(key, var.get()))))
            except (TypeError, ValueError):
                var.set(floor)
        self.v_dry.set(bool(cfg.get("dry_run", True)))
        if cfg.get("mode") in MODES:
            self.v_mode.set(cfg["mode"])
        names = cfg.get("names") or {}
        n = 0
        for cid in cfg.get("channel_ids", []):
            cid = str(cid)
            if cid.isdigit() and cid[:6] not in ("111111", "222222"):
                n += self._add_item(cid, "channel",
                                    names.get(cid, "from config"), True)
        for cid in cfg.get("dm_ids", []):
            cid = str(cid)
            if cid.isdigit() and cid[:6] != "333333":
                n += self._add_item(cid, "dm",
                                    names.get(cid, "from config"), True)
        self._redraw()
        if n:
            self._log(f"Loaded {n} saved target(s) from config.json.", "muted")

        rc = cfg.get("react") or {}
        if isinstance(rc, dict):
            self.v_rchan.set(str(rc.get("channel_id", "")))
            self.v_ruser.set(str(rc.get("author_id", "")))
            if rc.get("target") in RTARGETS:
                self.v_rtarget.set(rc["target"])
            if rc.get("assign") in RASSIGN:
                self.v_rassign.set(rc["assign"])
            try:
                self.v_rcount.set(int(rc.get("recent_n", 50)))
            except (TypeError, ValueError):
                pass
            for k, var, floor in (("react_delay", self.v_r_react_delay,
                                   FLOOR_REACT),
                                  ("msg_delay", self.v_r_msg_delay, FLOOR_MSG),
                                  ("search_delay", self.v_rsearch,
                                   FLOOR_SEARCH)):
                try:
                    var.set(max(floor, float(rc.get(k, var.get()))))
                except (TypeError, ValueError):
                    var.set(floor)
            self.v_rwatch.set(bool(rc.get("watch", False)))
            for emo in rc.get("emojis", []):
                if isinstance(emo, str):
                    self._emoji_add(emo)

    def _save_config(self):
        cfg = {
            "token": self.v_token.get().strip(),
            "user_id": self.v_user.get().strip(),
            "edit_text": self.v_edit.get(),
            "mode": self.v_mode.get(),
            "dry_run": bool(self.v_dry.get()),
            "edit_delay": round(self._cd(self.v_edelay), 2),
            "delete_delay": round(self._cd(self.v_ddelay), 2),
            "read_delay": round(self._cd(self.v_rdelay), 2),
            "channel_ids": [it["id"] for it in self._selected()
                            if it["kind"] != "dm"],
            "dm_ids": [it["id"] for it in self._selected()
                       if it["kind"] == "dm"],
            "names": {it["id"]: it["label"] for it in self.items
                      if it.get("label") and it["label"] != "from config"},
            "react": {
                "channel_id": self.v_rchan.get().strip(),
                "emojis": list(self.emojis),
                "target": self.v_rtarget.get(),
                "author_id": self.v_ruser.get().strip(),
                "recent_n": int(self.v_rcount.get()) if str(
                    self.v_rcount.get()).isdigit() else 50,
                "assign": self.v_rassign.get(),
                "react_delay": round(self._live_delay("react"), 2),
                "msg_delay": round(self._live_delay("message"), 2),
                "watch": bool(self.v_rwatch.get()),
                "search_delay": round(self._cd(self.v_rsearch), 2),
            },
        }
        try:
            with open(CONFIG_PATH, "w", encoding="utf-8") as f:
                json.dump(cfg, f, indent=2)
            self._log("Saved settings to config.json.", "ok")
        except Exception as e:
            self._log(f"Could not save config.json: {e}", "err")

    # -- threading plumbing -----------------------------------------------
    def _session(self):
        s = requests.Session()
        s.headers.update({"Authorization": self.v_token.get().strip(),
                          "Content-Type": "application/json", "User-Agent": UA})
        return s

    def _wait_if_paused(self):
        while self.pause_flag.is_set() and not self.stop_flag.is_set():
            time.sleep(0.2)

    def _req(self, s, method, url, **kw):
        for _ in range(6):
            if self.stop_flag.is_set():
                return None
            self._wait_if_paused()
            try:
                r = s.request(method, url, timeout=30, **kw)
            except requests.RequestException as e:
                self.q.put(("log", f"  network error: {e}", "err"))
                time.sleep(3)
                continue
            if r.status_code == 429:
                try:
                    wait = float(r.json().get("retry_after", 1.0)) + 0.5
                except Exception:
                    wait = 1.5
                self.q.put(("log", f"  rate limited, waiting {wait:.1f}s", "warn"))
                time.sleep(wait)
                continue
            return r
        return None

    def _live_dot(self, i):
        """Animated marquee shown while a job runs (paused shows a hold)."""
        if not getattr(self, "_running", False):
            if hasattr(self, "live_dot"):
                self.live_dot.configure(text="")
            return
        if self.pause_flag.is_set():
            self.live_dot.configure(text="\u2016 paused", fg=AMBER)
        else:
            frames = ["\u2809", "\u2819", "\u2838", "\u2830",
                      "\u2820", "\u2804", "\u2806", "\u2807"]
            acc = ARMED if self._is_armed() else SAFE
            self.live_dot.configure(text=frames[i % len(frames)] + " working",
                                    fg=acc)
        self.root.after(110, lambda: self._live_dot(i + 1))

    def _pulse(self, i=0):
        """Gently breathe the banner background while armed."""
        try:
            armed = self._is_armed()
        except Exception:
            armed = False
        if armed:
            import math
            t = (math.sin(i / 6.0) + 1) / 2          # 0..1
            self.banner.configure(bg=_blend(ARMED, "#F7C56B", t * 0.55))
        self.root.after(90, lambda: self._pulse(i + 1))

    def _busy(self, on):
        state = "disabled" if on else "normal"
        for w in (self.b_start, self.b_load):
            w.configure(state=state)
        self.b_stop.configure(state="normal" if on else "disabled")
        self.b_pause.configure(state="normal" if on else "disabled")
        self._running = on
        if on:
            self.bar.start(12)
            self._live_dot(0)
        else:
            self.bar.stop()
            if hasattr(self, "live_dot"):
                self.live_dot.configure(text="")
            self.pause_flag.clear()
            self.b_pause.configure(text="Pause")

    def _refresh_delay_cache(self):
        """Main-thread snapshot of delay vars into plain floats (thread-safe
        for the worker to read). Keeps live edits applying mid-run."""
        for k, (var, floor) in getattr(self, "_floor_vars", {}).items():
            try:
                self._delay_cache[k] = max(floor, float(var.get()))
            except (tk.TclError, ValueError):
                self._delay_cache[k] = floor

    def _pump(self):
        self._refresh_delay_cache()
        try:
            while True:
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "log":
                    self._log(msg[1], msg[2] if len(msg) > 2 else "info")
                elif kind == "stats":
                    (self.scanned, self.matched,
                     self.done, self.failed) = msg[1:5]
                    self._stats()
                elif kind == "targets":
                    self._apply_loaded(msg[1], msg[2])
                elif kind == "user":
                    if not self.v_user.get().strip():
                        self.v_user.set(msg[1])
                elif kind == "rename":
                    _, cid, name, knd = msg
                    for it in self.items:
                        if it["id"] == cid:
                            it["label"] = name
                            if knd:
                                it["kind"] = knd
                            break
                    self._redraw()
                elif kind == "naming_done":
                    self._naming = False
                    self._log("Finished fetching names.", "ok")
                elif kind == "done":
                    self._busy(False)
                    self.worker = None
        except queue.Empty:
            pass
        self.root.after(100, self._pump)

    def _apply_loaded(self, dms, chans):
        keep = {it["id"]: it["checked"] for it in self.items}
        self.items = []
        for cid, label in dms:
            self._add_item(cid, "dm", label, keep.get(cid, False))
        for cid, label in chans:
            self._add_item(cid, "channel", label, keep.get(cid, False))
        for cid, checked in keep.items():
            self._add_item(cid, "manual", "from config", checked)
        self._redraw()

    # -- load channels ----------------------------------------------------
    def _start_load(self):
        if self.worker:
            return
        if not self.v_token.get().strip():
            messagebox.showwarning("No token", "Paste your token first.")
            return
        self.stop_flag.clear()
        self._busy(True)
        self._log("Asking Discord what you have access to...", "safe")
        self.worker = threading.Thread(target=self._load_worker, daemon=True)
        self.worker.start()

    def _load_worker(self):
        try:
            s = self._session()
            me = self._req(s, "GET", f"{API}/users/@me")
            if me is None:
                self.q.put(("log", "Could not reach Discord.", "err"))
                return
            if me.status_code == 401:
                self.q.put(("log", "401 Unauthorized \u2014 token is wrong or "
                                   "expired. Grab a fresh one.", "err"))
                return
            if me.status_code != 200:
                self.q.put(("log", f"HTTP {me.status_code} from /users/@me", "err"))
                return
            me = me.json()
            self.q.put(("user", str(me.get("id"))))
            self.q.put(("log", f"Signed in as {me.get('username')} "
                               f"({me.get('id')})", "ok"))
            dms = []
            r = self._req(s, "GET", f"{API}/users/@me/channels")
            if r is not None and r.status_code == 200:
                for ch in r.json():
                    who = ", ".join(x.get("username", "?")
                                    for x in ch.get("recipients", []))
                    who = who or ch.get("name") or "unknown"
                    dms.append((str(ch["id"]),
                                ("group: " if ch.get("type") == 3 else "") + who))
                self.q.put(("log", f"Found {len(dms)} open DM channel(s).", "info"))
            else:
                self.q.put(("log", "Could not list DMs.", "warn"))
            chans = []
            time.sleep(0.6)
            g = self._req(s, "GET", f"{API}/users/@me/guilds")
            if g is not None and g.status_code == 200:
                guilds = g.json()
                for gu in guilds:
                    if self.stop_flag.is_set():
                        break
                    time.sleep(0.6)
                    cr = self._req(s, "GET", f'{API}/guilds/{gu["id"]}/channels')
                    if cr is None or cr.status_code != 200:
                        continue
                    for c in cr.json():
                        if c.get("type") in (0, 5):
                            chans.append((str(c["id"]),
                                          f'{gu.get("name")} \u2014 #{c.get("name")}'))
                self.q.put(("log", f"Found {len(chans)} text channel(s) across "
                                   f"{len(guilds)} server(s).", "info"))
            else:
                self.q.put(("log", "Could not list servers.", "warn"))
            self.q.put(("targets", dms, chans))
            self.q.put(("log", "Tick the ones you want, set filters, then run.",
                        "safe"))
        finally:
            self.q.put(("done",))

    # -- clean ------------------------------------------------------------
    def _start_active(self):
        if self.active_tab == "react":
            self._start_react()
        else:
            self._start_clean()

    def _start_clean(self):
        if self.worker:
            return
        token = self.v_token.get().strip()
        user = self.v_user.get().strip()
        targets = self._selected()
        if not token:
            messagebox.showwarning("No token", "Paste your token first.")
            return
        if not user.isdigit():
            messagebox.showwarning(
                "No user ID",
                "Your user ID is needed so only your own messages are touched.\n"
                'Click "Load my channels" to fill it in.')
            return
        if not targets:
            messagebox.showwarning("Nothing ticked",
                                   "Tick at least one channel or DM.")
            return
        try:
            spec = self._compile_filters()
        except ValueError as e:
            messagebox.showwarning("Check filters", str(e))
            return

        mode = self.v_mode.get()
        if not self.v_dry.get():
            verb = {"Edit, then delete": "edit and permanently delete",
                    "Delete only": "permanently delete",
                    "Edit only": "edit"}[mode]
            if not messagebox.askyesno(
                    "Run for real?",
                    f"This will {verb} your matching messages in "
                    f"{len(targets)} channel/DM(s).\n\nContinue?",
                    icon="warning", default="no"):
                return
            typed = simpledialog.askstring("Confirm", "Type RUN to confirm:",
                                           parent=self.root)
            if (typed or "").strip() != "RUN":
                self._log("Cancelled \u2014 confirmation did not match.", "muted")
                return

        self.scanned = self.matched = self.done = self.failed = 0
        self._stats()
        self.stop_flag.clear()
        self.pause_flag.clear()
        self._busy(True)
        self._save_config()
        args = (token, user, self.v_edit.get(), mode, bool(self.v_dry.get()),
                float(self.v_edelay.get()), float(self.v_ddelay.get()),
                float(self.v_rdelay.get()), spec,
                [(it["id"], it["label"]) for it in targets])
        self.worker = threading.Thread(target=self._clean_worker, args=args,
                                       daemon=True)
        self.worker.start()

    def _clean_worker(self, token, user_id, edit_text, mode, dry,
                      edelay, ddelay, rdelay, spec, targets):
        scanned = matched = done = failed = 0
        do_edit = mode in ("Edit, then delete", "Edit only")
        do_delete = mode in ("Edit, then delete", "Delete only")
        before_seed = snowflake_for(spec["before"]) if spec.get("before") else None
        try:
            s = self._session()
            self.q.put(("log", "-" * 60, "muted"))
            self.q.put(("log",
                        ("Dry run \u2014 listing matches only."
                         if dry else f"Live run \u2014 {mode.lower()}."),
                        "safe" if dry else "warn"))

            for cid, label in targets:
                if self.stop_flag.is_set():
                    break
                self.q.put(("log", f"\n{label}  ({cid})", "info"))
                before = before_seed
                stop_channel = False

                while not self.stop_flag.is_set() and not stop_channel:
                    params = {"limit": 100}
                    if before:
                        params["before"] = before
                    r = self._req(s, "GET", f"{API}/channels/{cid}/messages",
                                  params=params)
                    if r is None:
                        break
                    if r.status_code == 401:
                        self.q.put(("log", "401 Unauthorized \u2014 token "
                                           "expired. Stopping.", "err"))
                        return
                    if r.status_code in (403, 404):
                        self.q.put(("log", f"  no access (HTTP {r.status_code}) "
                                           f"\u2014 skipping", "warn"))
                        break
                    if r.status_code != 200:
                        self.q.put(("log", f"  HTTP {r.status_code} \u2014 "
                                           f"skipping", "warn"))
                        break
                    msgs = r.json()
                    if not msgs:
                        break

                    for m in msgs:
                        if self.stop_flag.is_set():
                            break
                        if m.get("author", {}).get("id") != user_id:
                            continue
                        if m.get("type", 0) not in (0, 19):
                            continue
                        scanned += 1
                        # after-date short-circuit: pages go newest -> oldest
                        if spec.get("after"):
                            ts = m.get("timestamp")
                            try:
                                if ts and datetime.fromisoformat(ts) < spec["after"]:
                                    stop_channel = True
                                    self.q.put(("stats", scanned, matched,
                                                done, failed))
                                    break
                            except ValueError:
                                pass
                        if not self._match(m, spec):
                            self.q.put(("stats", scanned, matched, done, failed))
                            continue
                        matched += 1
                        mid = m["id"]
                        prev = (m.get("content") or "<no text>") \
                            .replace("\n", " ")[:42]

                        if dry:
                            self.q.put(("log", f"  match {mid}  {prev}", "muted"))
                            self.q.put(("stats", scanned, matched, done, failed))
                            continue

                        ok = True
                        if do_edit:
                            er = self._req(s, "PATCH",
                                           f"{API}/channels/{cid}/messages/{mid}",
                                           data=json.dumps({"content": edit_text}))
                            if er is None or er.status_code not in (200, 201):
                                code = er.status_code if er is not None else "net"
                                self.q.put(("log", f"  edit failed {mid} ({code})",
                                            "warn"))
                                if not do_delete:
                                    ok = False
                            time.sleep(self._cd(self.v_edelay))
                            if self.stop_flag.is_set():
                                break
                        if do_delete:
                            dr = self._req(s, "DELETE",
                                           f"{API}/channels/{cid}/messages/{mid}")
                            if dr is not None and dr.status_code in (200, 204):
                                self.q.put(("log", f"  deleted {mid}  {prev}", "ok"))
                            else:
                                ok = False
                                code = dr.status_code if dr is not None else "net"
                                self.q.put(("log", f"  delete failed {mid} "
                                                   f"({code})", "err"))
                            time.sleep(self._cd(self.v_ddelay))
                        elif do_edit and ok:
                            self.q.put(("log", f"  edited {mid}  {prev}", "ok"))

                        if ok:
                            done += 1
                        else:
                            failed += 1
                        self.q.put(("stats", scanned, matched, done, failed))

                    before = msgs[-1]["id"]
                    if len(msgs) < 100:
                        break
                    time.sleep(self._cd(self.v_rdelay))

            self.q.put(("stats", scanned, matched, done, failed))
            self.q.put(("log", "-" * 60, "muted"))
            if self.stop_flag.is_set():
                self.q.put(("log", f"Stopped. Scanned {scanned}, matched "
                                   f"{matched}, done {done}, failed {failed}.",
                            "warn"))
            elif dry:
                self.q.put(("log", f"Dry run complete. {matched} of {scanned} "
                                   f"message(s) match your filters. Untick dry "
                                   f"run to act on them.", "safe"))
            else:
                self.q.put(("log", f"Finished. Done {done} of {matched} matched "
                                   f"({failed} failed).", "ok"))
        finally:
            self.q.put(("done",))

    # -- react ------------------------------------------------------------
    def _start_react(self):
        if self.worker:
            return
        token = self.v_token.get().strip()
        chan = self.v_rchan.get().strip()
        if not token:
            messagebox.showwarning("No token", "Paste your token first.")
            return
        if not chan.isdigit():
            messagebox.showwarning("Channel ID",
                                   "Enter a numeric channel ID to react in.")
            return
        if not self.emojis:
            messagebox.showwarning("No emoji",
                                   "Add at least one emoji to the pool.")
            return
        target = self.v_rtarget.get()
        author = self.v_ruser.get().strip()
        if target == "Only from user ID" and not author.isdigit():
            messagebox.showwarning("Author ID",
                                   "Enter the numeric user ID to react to.")
            return
        try:
            limit = int(self.v_rcount.get()) if target == "Most recent N" else 0
        except (tk.TclError, ValueError):
            limit = 0

        watch = bool(self.v_rwatch.get())
        dry = bool(self.v_rdry.get()) and not watch   # watch is always live

        if watch and target != "Only from user ID":
            if not messagebox.askyesno(
                    "Watch everyone?",
                    "Watch mode will react to EVERY new message in the channel, "
                    "not just one person. That's very noticeable.\n\nTo watch a "
                    "single user, set \u2018React to\u2192 Only from user ID\u2019."
                    "\n\nContinue anyway?",
                    icon="warning", default="no"):
                return

        if not dry:
            n = len(self.emojis)
            who = f"user {author}" if target == "Only from user ID" else \
                "matching messages"
            msg = (f"Watch channel {chan} and react to {who} with {n} emoji "
                   f"as they post, until you press Stop.\n\nContinue?"
                   if watch else
                   f"This will add {n} emoji as reactions to the matching "
                   f"messages in channel {chan}, as your account.\n\nContinue?")
            if not messagebox.askyesno("React for real?", msg,
                                       icon="warning", default="no"):
                return

        self.scanned = self.matched = self.done = self.failed = 0
        self._stats()
        self.stop_flag.clear()
        self.pause_flag.clear()
        self._busy(True)
        self._save_config()
        args = (token, chan, list(self.emojis), self.v_rassign.get(),
                target, author, limit,
                self.v_user.get().strip(),
                dry, bool(self.v_prescan.get()), watch)
        self.worker = threading.Thread(target=self._react_worker, args=args,
                                       daemon=True)
        self.worker.start()

    def _cd(self, var):
        """Delay value for a spinbox var, from the main-thread cache (never
        below floor). Safe to call from the worker thread."""
        return self._delay_cache.get(str(var), self._floor_of(var))

    def _i_reacted(self, message, emoji):
        """True if my account already reacted to this message with `emoji`.

        Uses the reactions array Discord embeds in each message. Unicode
        emoji match on name; custom emoji (<:name:id>) match on id.
        """
        m = CUSTOM_EMOJI.match(emoji.strip())
        want_id = m.group(2) if m else None
        want_name = emoji.strip() if not m else m.group(1)
        for rc in message.get("reactions", []) or []:
            if not rc.get("me"):
                continue
            emo = rc.get("emoji", {}) or {}
            if want_id is not None:
                if str(emo.get("id")) == want_id:
                    return True
            else:
                if emo.get("id") in (None, "") and emo.get("name") == want_name:
                    return True
        return False

    def _live_delay(self, which):
        """Cooldown from the main-thread cache; never below floor. Thread-safe."""
        var = self.v_r_react_delay if which == "react" else self.v_r_msg_delay
        return self._cd(var)

    def _react_worker(self, token, cid, emojis, assign, target, author,
                      limit, me_id, dry, prescan=True, watch=False):
        import random
        C = {"scanned": 0, "matched": 0, "done": 0, "failed": 0,
             "skipped": 0, "cursor": 0}
        skip_ids = set()

        def wanted(m):
            if m.get("type", 0) not in (0, 19):
                return False
            if target == "Only from user ID" and \
                    m.get("author", {}).get("id") != author:
                return False
            return True

        def act(m):
            """React to one already-filtered message (or list it, if dry)."""
            mid = m["id"]
            C["scanned"] += 1
            if mid in skip_ids:
                C["skipped"] += 1
                return
            if assign == "Random from list":
                chosen = [random.choice(emojis)]
            elif assign == "Cycle through list":
                chosen = [emojis[C["cursor"] % len(emojis)]]
                C["cursor"] += 1
            else:
                chosen = list(emojis)
            C["matched"] += 1
            prev = (m.get("content") or "<no text>").replace("\n", " ")[:34]

            if dry:
                already = [e for e in chosen if self._i_reacted(m, e)]
                todo = [e for e in chosen if e not in already]
                if not todo:
                    C["skipped"] += 1
                    self.q.put(("log", f"  already reacted, skip  {mid}", "muted"))
                else:
                    note = "  (some already present)" if already else ""
                    self.q.put(("log", f"  would react {' '.join(todo)}  {mid}  "
                                       f"{prev}{note}", "muted"))
                self.q.put(("stats", C["scanned"], C["matched"], C["done"],
                            C["failed"]))
                return

            okone, did_any = True, False
            for emo in chosen:
                if self.stop_flag.is_set():
                    break
                if self._i_reacted(m, emo):
                    self.q.put(("log", f"  skip {emo} {mid} (already reacted)",
                                "muted"))
                    continue
                seg = encode_emoji(emo)
                rr = self._req(s, "PUT", f"{API}/channels/{cid}/messages/{mid}"
                                         f"/reactions/{seg}/@me")
                if rr is not None and rr.status_code in (200, 204):
                    did_any = True
                    self.q.put(("log", f"  {emo}  {mid}  {prev}", "ok"))
                else:
                    okone = False
                    code = rr.status_code if rr is not None else "net"
                    self.q.put(("log", f"  fail {emo} {mid} ({code})", "err"))
                time.sleep(self._live_delay("react"))
            if not did_any and okone:
                C["skipped"] += 1
            elif okone:
                C["done"] += 1
            else:
                C["failed"] += 1
            self.q.put(("stats", C["scanned"], C["matched"], C["done"],
                        C["failed"]))
            time.sleep(self._live_delay("message"))

        def wait_search():
            end = time.time() + max(FLOOR_SEARCH, self._cd(self.v_rsearch))
            while time.time() < end and not self.stop_flag.is_set():
                self._wait_if_paused()
                time.sleep(0.2)

        try:
            s = self._session()
            self.q.put(("log", "-" * 60, "muted"))
            self.q.put(("log",
                        ("Dry run \u2014 listing reactions only." if dry else
                         ("Watch mode \u2014 reacting to new messages." if watch
                          else "Live run \u2014 adding reactions.")),
                        "safe" if dry else "warn"))
            who = f"user {author}" if target == "Only from user ID" else "all"
            self.q.put(("log", f"channel {cid}  \u00b7  {len(emojis)} emoji  "
                               f"\u00b7  {assign.lower()}  \u00b7  {who}", "info"))

            # Phase 1: fast pre-scan (live only) to record already-reacted msgs.
            if not dry and prescan:
                self.q.put(("log", "pre-scan: checking existing reactions...",
                            "safe"))
                pre_seen = pre_hit = 0
                pbefore = None
                while not self.stop_flag.is_set():
                    pparams = {"limit": 100}
                    if pbefore:
                        pparams["before"] = pbefore
                    pr = self._req(s, "GET", f"{API}/channels/{cid}/messages",
                                   params=pparams)
                    if pr is None or pr.status_code != 200:
                        break
                    pmsgs = pr.json()
                    if not pmsgs:
                        break
                    for m in pmsgs:
                        if not wanted(m):
                            continue
                        pre_seen += 1
                        if any(self._i_reacted(m, e) for e in emojis):
                            skip_ids.add(m["id"])
                            pre_hit += 1
                        if limit and pre_seen >= limit:
                            break
                    pbefore = pmsgs[-1]["id"]
                    if len(pmsgs) < 100 or (limit and pre_seen >= limit):
                        break
                    time.sleep(self._cd(self.v_rdelay))
                self.q.put(("log", f"pre-scan done: {pre_hit} of {pre_seen} "
                                   f"already reacted \u2014 will skip those.",
                            "safe"))

            # Phase 2: history pass (newest -> oldest), react/list matches.
            newest_id = None
            before = None
            reached = False
            while not self.stop_flag.is_set() and not reached:
                params = {"limit": 100}
                if before:
                    params["before"] = before
                r = self._req(s, "GET", f"{API}/channels/{cid}/messages",
                              params=params)
                if r is None:
                    break
                if r.status_code == 401:
                    self.q.put(("log", "401 Unauthorized \u2014 token expired.",
                                "err"))
                    return
                if r.status_code in (403, 404):
                    self.q.put(("log", f"  no access (HTTP {r.status_code}).",
                                "warn"))
                    break
                if r.status_code != 200:
                    self.q.put(("log", f"  HTTP {r.status_code}.", "warn"))
                    break
                msgs = r.json()
                if not msgs:
                    break
                if newest_id is None:
                    newest_id = msgs[0]["id"]     # remember channel's newest
                for m in msgs:
                    if self.stop_flag.is_set():
                        break
                    if not wanted(m):
                        continue
                    act(m)
                    if limit and C["matched"] >= limit:
                        reached = True
                        break
                before = msgs[-1]["id"]
                if len(msgs) < 100:
                    break

            # Phase 3: watch loop — poll for messages newer than newest_id.
            if watch and not dry and not self.stop_flag.is_set():
                self.q.put(("log", f"watching for new messages "
                                   f"(every {max(FLOOR_SEARCH, self._cd(self.v_rsearch)):g}s)"
                                   f" \u2014 press Stop to end.", "safe"))
                if newest_id is None:
                    newest_id = "0"
                while not self.stop_flag.is_set():
                    wait_search()
                    if self.stop_flag.is_set():
                        break
                    r = self._req(s, "GET", f"{API}/channels/{cid}/messages",
                                  params={"after": newest_id, "limit": 100})
                    if r is None:
                        continue
                    if r.status_code == 401:
                        self.q.put(("log", "401 \u2014 token expired. Stopping.",
                                    "err"))
                        break
                    if r.status_code in (403, 404):
                        self.q.put(("log", f"lost access (HTTP {r.status_code}). "
                                           f"Stopping.", "warn"))
                        break
                    if r.status_code != 200:
                        continue
                    fresh = r.json()
                    if not fresh:
                        continue
                    # returned newest-first; process oldest-first
                    for m in sorted(fresh, key=lambda x: int(x["id"])):
                        if self.stop_flag.is_set():
                            break
                        newest_id = str(max(int(newest_id), int(m["id"])))
                        if wanted(m):
                            act(m)

            self.q.put(("stats", C["scanned"], C["matched"], C["done"],
                        C["failed"]))
            self.q.put(("log", "-" * 60, "muted"))
            if self.stop_flag.is_set():
                self.q.put(("log", f"Stopped. Matched {C['matched']}, reacted "
                                   f"{C['done']}, skipped {C['skipped']}, "
                                   f"failed {C['failed']}.", "warn"))
            elif dry:
                self.q.put(("log", f"Dry run complete. {C['matched']} matched, "
                                   f"{C['skipped']} already reacted. Untick dry "
                                   f"run to go.", "safe"))
            else:
                self.q.put(("log", f"Finished. Reacted to {C['done']} of "
                                   f"{C['matched']} ({C['skipped']} already done, "
                                   f"{C['failed']} failed).", "ok"))
        finally:
            self.q.put(("done",))

    # -- lifecycle --------------------------------------------------------
    def _toggle_pause(self):
        if not self.worker:
            return
        if self.pause_flag.is_set():
            self.pause_flag.clear()
            self.b_pause.configure(text="Pause")
            self._log("Resumed.", "muted")
        else:
            self.pause_flag.set()
            self.b_pause.configure(text="Resume")
            self._log("Paused \u2014 will hold after the current step.", "warn")

    def _stop(self):
        if self.worker:
            self.stop_flag.set()
            self.pause_flag.clear()
            self._log("Stopping after the current message...", "warn")

    def _on_close(self):
        if self.worker:
            if not messagebox.askyesno("Still running",
                                       "A run is in progress. Quit anyway?"):
                return
            self.stop_flag.set()
        self.root.destroy()


def main():
    root = tk.Tk()
    Cleaner(root)
    root.mainloop()


if __name__ == "__main__":
    main()
