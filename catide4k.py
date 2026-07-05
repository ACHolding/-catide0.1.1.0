#!/usr/bin/env python3
"""
CatIDE 0.1 — a Cursor-3-style "AI agents OS" IDE powered by LM Studio.

Single file. Stdlib only (tkinter). Python 3.10 – 3.14.
Cross-platform: macOS, Linux, Windows, BSD, Android, Unix.

Cursor-style features:
  * Activity bar + sidebar (Explorer file tree, workspace Search)
  * Tabbed editor with line numbers, syntax highlighting, current-line glow
  * Integrated pty TERMINAL (real shell), AI AGENT terminal, OUTPUT, PROBLEMS
  * Multiple parallel AI agent sessions (tabs) with Agent / Ask / Plan modes
  * Agent tools: list_dir, read_file, write_file, edit_file, delete_file,
    grep_search, run_terminal — with checkpoints + Keep All / Undo All review
  * Cursor Tab: AI ghost-text autocomplete (Tab accepts, Esc dismisses)
  * @file mentions in chat, .cursorrules / AGENTS.md workspace rules
  * Cmd+K inline edit, Cmd+Shift+P command palette, Cmd+I focus agent
  * Status bar with model, git branch, Ln/Col, language, build info
LM Studio must be serving its OpenAI-compatible API (default localhost:1234).
"""

import difflib
import hashlib
import json
import keyword
import os
import platform as platform_mod
import queue
import re
import shlex
import shutil
import subprocess
import sys
import threading
import time
import tkinter as tk
import urllib.error
import urllib.request
from urllib.parse import unquote, urlparse
from tkinter import filedialog, font as tkfont, messagebox, ttk

try:
    import fcntl
    import pty
    import struct
    import termios
    HAS_PTY = True
except ImportError:          # Windows / platforms without pty
    HAS_PTY = False

IS_MAC = sys.platform == "darwin"
MOD = "Command" if IS_MAC else "Control"
MOD_LABEL = "⌘" if IS_MAC else "Ctrl+"


# =============================================================================
# Platform + shell autodetection (mac / windows / linux / bsd / android / unix)
# =============================================================================
def detect_platform():
    p = sys.platform
    if "ANDROID_ROOT" in os.environ or "ANDROID_DATA" in os.environ:
        return "android"
    if p == "darwin":
        return "mac"
    if p.startswith("win") or p == "cygwin":
        return "windows"
    if p.startswith("linux"):
        return "linux"
    if p.startswith(("freebsd", "openbsd", "netbsd", "dragonfly")) or "bsd" in p:
        return "bsd"
    return "unix"


PLATFORM = detect_platform()


def detect_shell():
    """Autodetect the user's shell. Returns (argv list, display name)."""
    if PLATFORM == "windows":
        ps = shutil.which("pwsh") or shutil.which("powershell")
        if ps:
            return [ps, "-NoLogo", "-NoExit"], os.path.basename(ps).split(".")[0]
        cmd = os.environ.get("COMSPEC") or shutil.which("cmd") or "cmd.exe"
        return [cmd], "cmd"
    sh = os.environ.get("SHELL", "")
    if not sh or not os.path.isfile(sh):
        for cand in ("/bin/zsh", "/bin/bash", "/usr/local/bin/bash",
                     "/usr/bin/fish", "/bin/sh", "/system/bin/sh"):
            if os.path.isfile(cand):
                sh = cand
                break
        else:
            sh = shutil.which("sh") or "sh"
    name = os.path.basename(sh)
    argv = [sh]
    if name in ("zsh", "bash", "fish") and PLATFORM != "android":
        argv.append("-l")
    return argv, name


SHELL_ARGV, SHELL_NAME = detect_shell()


def shell_command(cmd):
    """Wrap a command for subprocess.run(shell=True) on this OS."""
    if PLATFORM == "windows" and SHELL_NAME in ("powershell", "pwsh"):
        return f"& {cmd}"
    return cmd


def run_file_command(path):
    """Build a shell one-liner to execute the given file (paths always quoted)."""
    path = os.path.normpath(path)
    q = shlex.quote(path)
    if path.lower().endswith((".py", ".pyw")):
        return f"{shlex.quote(sys.executable)} {q}"
    return q

# =============================================================================
# On-disk persistence (agents, transcripts, checkpoints, settings, logs)
# =============================================================================
CONFIG_DIR = os.path.join(os.path.expanduser("~"), ".catide")
SESS_DIR = os.path.join(CONFIG_DIR, "agents")
LOG_DIR = os.path.join(CONFIG_DIR, "logs")
SETTINGS_PATH = os.path.join(CONFIG_DIR, "settings.json")


def normalize_path(path, base=None):
    """Normalize filesystem paths and file:// URIs (Cursor / VS Code style)."""
    if path is None:
        return ""
    p = str(path).strip().strip('"').strip("'")
    if not p:
        return ""
    if p.lower().startswith("file:"):
        u = urlparse(p)
        p = unquote(u.path or "")
        if (PLATFORM == "windows" and len(p) >= 3
                and p[0] == "/" and p[2] == ":"):
            p = p[1:]
    else:
        p = unquote(p)
    p = p.replace("\\", os.sep)
    p = os.path.expanduser(p)
    if base and not os.path.isabs(p):
        p = os.path.join(base, p)
    p = os.path.normpath(p)
    if os.path.isabs(p):
        p = os.path.abspath(p)
    elif base:
        p = os.path.abspath(os.path.join(base, p))
    if PLATFORM == "windows":
        p = os.path.normcase(p)
    return p


def squash_path(path):
    """Collapse whitespace for fuzzy path compare (macOS volume names)."""
    return re.sub(r"\s+", "", str(path))


def paths_equal(a, b):
    """True when two paths refer to the same file (symlink-safe, space-tolerant)."""
    if not a or not b:
        return a == b
    try:
        a = os.path.realpath(normalize_path(a))
        b = os.path.realpath(normalize_path(b))
    except OSError:
        a = normalize_path(a)
        b = normalize_path(b)
    if PLATFORM == "windows":
        return os.path.normcase(a) == os.path.normcase(b)
    if a == b:
        return True
    return squash_path(a) == squash_path(b)


def norm_workspace(path):
    """Stable workspace key for hashing / session files."""
    p = normalize_path(path)
    if not p:
        return p
    try:
        return os.path.realpath(p)
    except OSError:
        return p


def _script_dir():
    return norm_workspace(os.path.dirname(os.path.abspath(sys.argv[0])))


def sanitize_model_path(raw, workspace=None):
    """Clean corrupted model paths (embedded volume URLs, duplicate roots)."""
    if raw is None:
        return ""
    p = str(raw).strip().strip('"').strip("'")
    if not p:
        return p
    if p.lower().startswith("file:"):
        return p
    p = p.replace("\\", os.sep)

    # Embedded /Volumes/... in the middle: project/Volumes/1TB/.../file
    if not p.startswith("/Volumes") and "/Volumes/" in p:
        head, _, tail = p.partition("/Volumes/")
        vol_tail = tail.split("/", 1)[-1] if "/" in tail else tail
        vol_parts = []
        for x in vol_tail.split(os.sep):
            if not x:
                continue
            xl = x.lower().replace(" ", "")
            if re.match(r"^\d+tb$", xl):
                continue
            if xl.startswith(":") or "stuff" in xl or "coding" in xl:
                continue
            vol_parts.append(x)
        if workspace:
            base = os.path.basename(norm_workspace(workspace).rstrip(os.sep))
            while vol_parts and vol_parts[0] == base:
                vol_parts.pop(0)
        tail_rel = os.sep.join(vol_parts)
        head = head.rstrip(os.sep)
        p = f"{head}{os.sep}{tail_rel}" if head else tail_rel

    # Repeated workspace folder in path: foo/Proj/foo/bar → bar (after last base)
    if workspace:
        base = os.path.basename(norm_workspace(workspace).rstrip(os.sep))
        if base:
            parts = p.split(os.sep)
            last = -1
            for i, part in enumerate(parts):
                if part == base:
                    last = i
            if last >= 0:
                rest = os.sep.join(parts[last + 1:])
                if rest:
                    p = rest

    return p


def resolve_startup_workspace():
    """Autodetect workspace: prefer script folder over saved parent directory."""
    script_dir = _script_dir()
    saved = None
    try:
        with open(SETTINGS_PATH, "r", encoding="utf-8") as f:
            saved = json.load(f).get("workspace")
        if saved:
            saved = norm_workspace(normalize_path(saved))
    except (OSError, json.JSONDecodeError):
        pass

    if saved and os.path.isdir(saved):
        # Saved parent folder (e.g. :Coding~) → use script dir (CatIDE0.1)
        if script_dir != saved and script_dir.startswith(saved + os.sep):
            if os.path.isdir(script_dir):
                return script_dir
        return saved

    if os.path.isdir(script_dir):
        return script_dir
    return norm_workspace(os.getcwd())


def workspace_agent_dir(workspace):
    """Cursor-style project-local agent storage."""
    d = os.path.join(norm_workspace(workspace), ".catide", "agents")
    try:
        os.makedirs(d, exist_ok=True)
    except OSError:
        pass
    return d


def ensure_dirs():
    for d in (CONFIG_DIR, SESS_DIR, LOG_DIR):
        try:
            os.makedirs(d, exist_ok=True)
        except OSError:
            pass


ensure_dirs()

# =============================================================================
# Build / version info (Cursor-3 compat layer shown in About + status bar)
# =============================================================================
APP_NAME = "CatIDE"
APP_VERSION = "0.1"
BUILD_INFO = """Version: 3.9.16
VS Code Extension API: 1.105.1
Commit: 042b3c1a4c53f2c3808067f519fbfc67b72cad80
Date: 2026-06-27T06:41:01.941Z
Layout: editor
Build Type: Stable
Release Track: Default
Electron: 40.10.3
Chromium: 144.0.7559.236
Node.js: 24.15.0
V8: 14.4.258.32-electron.0
xterm.js: 6.1.0-beta.256
OS: Darwin arm64 25.5.0"""

# =============================================================================
# Theme — Cursor 3 dark, blue hue
# =============================================================================
BG          = "#0a0e1a"   # window chrome
ACTIVITY_BG = "#070b14"   # activity bar (far left)
SIDEBAR_BG  = "#0b101f"   # explorer / search sidebar
EDITOR_BG   = "#0d1220"   # editor surface
PANEL_BG    = "#0a0f1c"   # bottom panel
TAB_BG      = "#0b101f"   # inactive tab
TAB_ACTIVE  = "#0d1220"   # active tab
INPUT_BG    = "#080c16"   # inputs / terminal
STATUS_BG   = "#0d47a1"   # status bar (cursor blue)

FG          = "#7aa7e8"   # primary blue text
FG_BRIGHT   = "#b8d4ff"   # bright text
FG_DIM      = "#3b5b8f"   # dim blue
FG_FAINT    = "#24406b"   # faintest (line numbers, hints)
ACCENT      = "#2f81f7"   # cursor-blue accent
SEL_BG      = "#1a3a6b"   # selection
CURLINE     = "#101830"   # current line highlight
BTN_BG      = "#000000"   # buttons = black
BTN_FG      = "#6fa8ff"
BTN_HOVER   = "#0d1b3d"
ERR_RED     = "#ff6b7a"
OK_GREEN    = "#4dd0a1"
WARN_YEL    = "#e5c07b"

SYNTAX = {
    "kw":      "#6f9fff",
    "builtin": "#4dd0e1",
    "string":  "#8ab4ff",
    "comment": "#33507d",
    "number":  "#40c4ff",
    "deco":    "#448aff",
    "defname": "#b8d4ff",
}

ANSI_RE = re.compile(
    r"\x1b\[[0-9;?]*[a-zA-Z]"      # CSI sequences
    r"|\x1b\][^\x07\x1b]*(?:\x07|\x1b\\)"  # OSC sequences
    r"|\x1b[=>NOc]"                # misc
    r"|\x1b\([AB012]"              # charset
)
ANSI_SGR_RE = re.compile(r"\x1b\[([0-9;]*)m")
TERM_COLORS = {
    30: "#33507d", 31: ERR_RED, 32: OK_GREEN, 33: WARN_YEL,
    34: ACCENT, 35: "#c792ea", 36: "#4dd0e1", 37: FG_BRIGHT,
    90: "#5c7a99", 91: "#ff8a95", 92: "#69e0b0", 93: "#f0d87a",
    94: "#6fa8ff", 95: "#d8a6ff", 96: "#6ee8f0", 97: "#e8f0ff",
}
SKIP_TREE = frozenset({
    ".git", ".catide", "__pycache__", "node_modules", ".DS_Store",
    ".venv", "venv", ".idea", ".vscode",
})

LM_STUDIO_BASE = "http://localhost:1234/v1"


def mono_font(size=13):
    wanted = ("SF Mono", "Menlo", "JetBrains Mono", "Fira Code", "Consolas",
              "Cascadia Code", "Courier New")
    avail = set(tkfont.families())
    for name in wanted:
        if name in avail:
            return tkfont.Font(family=name, size=size)
    return tkfont.Font(family="Courier", size=size)


def ui_font(size=12, weight="normal"):
    if PLATFORM == "mac":
        fam = "SF Pro Text"
    elif PLATFORM == "windows":
        fam = "Segoe UI"
    else:
        fam = "Helvetica"
    if fam not in tkfont.families():
        fam = "Helvetica"
    return (fam, size, weight)


# =============================================================================
# LM Studio client (OpenAI-compatible, streaming, stdlib only)
# =============================================================================
class LMStudio:
    def __init__(self, base=LM_STUDIO_BASE):
        self.base = base

    def list_models(self):
        with urllib.request.urlopen(self.base + "/models", timeout=5) as r:
            data = json.loads(r.read().decode("utf-8"))
        return [m["id"] for m in data.get("data", [])]

    def stream_chat(self, messages, model, on_token, stop_flag,
                    temperature=0.7, max_tokens=None):
        """Blocking generator-style call; returns the full reply text.
        Raises on network errors."""
        body = {
            "model": model, "messages": messages,
            "temperature": temperature, "stream": True,
        }
        if max_tokens:
            body["max_tokens"] = max_tokens
        payload = json.dumps(body).encode("utf-8")
        req = urllib.request.Request(
            self.base + "/chat/completions", data=payload,
            headers={"Content-Type": "application/json"})
        full = []
        with urllib.request.urlopen(req, timeout=600) as resp:
            for raw in resp:
                if stop_flag.is_set():
                    break
                line = raw.decode("utf-8", "replace").strip()
                if not line.startswith("data:"):
                    continue
                chunk = line[5:].strip()
                if chunk == "[DONE]":
                    break
                try:
                    delta = json.loads(chunk)["choices"][0]["delta"]
                except (json.JSONDecodeError, KeyError, IndexError):
                    continue
                tok = delta.get("content")
                if tok:
                    full.append(tok)
                    on_token(tok)
        return "".join(full)


# =============================================================================
# Agent prompts + tool protocol
# =============================================================================
TOOL_SPEC = """You can use tools to read and WRITE files in the workspace.

FORMAT A — simple tools (list_dir, read_file, delete_file, grep, run_terminal):
Reply with ONLY this fence:
```tool
{"tool": "read_file", "path": "src/main.py"}
```

FORMAT B — write_file (REQUIRED for any file with code):
Use TWO fences back-to-back. First the path, then the raw file content:
```tool
{"tool": "write_file", "path": "relative/path.py"}
```
```write
paste the ENTIRE file content here — no JSON escaping needed
```

FORMAT C — edit_file (small targeted change):
```tool
{"tool": "edit_file", "path": "file.py", "old": "exact text to find once", "new": "replacement"}
```

Available tools:
  {"tool": "list_dir",     "path": "."}
  {"tool": "read_file",    "path": "relative/path"}
  {"tool": "write_file",   "path": "relative/path"}  + ```write block (Format B)
  {"tool": "edit_file",    "path": "path", "old": "...", "new": "..."}
  {"tool": "delete_file",  "path": "relative/path"}
  {"tool": "grep_search",  "pattern": "regex", "path": "."}
  {"tool": "run_terminal", "command": "shell command"}

Rules:
  * ONE tool call per message — nothing else in that message.
  * ALWAYS use Format B (two fences) for write_file — never put code inside JSON.
  * Paths are relative to the workspace root (file:// URLs also accepted).
  * write_file creates parent directories automatically (src/nested/file.py works).
  * read_file on a missing file returns an error — use write_file to create it first.
  * After each call you receive [TOOL RESULT]. When done, reply normally (no tool)."""

MODE_PROMPTS = {
    "Agent": (
        "You are CatIDE Agent — a Cursor-style autonomous coding agent. "
        "CatIDE autodetects the workspace, OS, shell, Python version, git branch, "
        "open files, cursor line, text selection, project rules, and mentioned files. "
        "You ACT immediately: read, write, edit, delete, grep, and run terminal commands. "
        "Never ask for permission. Use tools to change files — every write_file saves "
        "to disk instantly with exact whitespace. Use relative paths from workspace root. "
        "Quote shell paths that contain spaces. Keep going until the task is done.\n\n"
        + TOOL_SPEC
    ),
    "Ask": (
        "You are CatIDE Ask mode — a read-only AI assistant inside CatIDE 0.1. "
        "Answer questions about the user's code clearly and concisely. "
        "Use fenced code blocks for code. You cannot modify files."
    ),
    "Plan": (
        "You are CatIDE Plan mode inside CatIDE 0.1. Produce a clear, "
        "step-by-step implementation plan for the user's request: numbered "
        "steps, files to touch, and risks. Do NOT write full implementations."
    ),
}

TOOL_FENCE_RE = re.compile(
    r"```(?:tool|json|write|file)?\s*\n(.*?)```", re.S | re.I)
MENTION_RE = re.compile(r"@([^\s@`]+)")
FILE_REF_RE = re.compile(r"(?:[\w./~-]+/)*[\w.-]+\.\w+")
LANG_MAP = {
    ".py": "Python", ".pyw": "Python", ".pyi": "Python",
    ".js": "JavaScript", ".jsx": "JavaScript", ".ts": "TypeScript",
    ".tsx": "TypeScript", ".json": "JSON", ".md": "Markdown",
    ".html": "HTML", ".css": "CSS", ".scss": "SCSS",
    ".c": "C", ".h": "C", ".cpp": "C++", ".cc": "C++",
    ".rs": "Rust", ".go": "Go", ".java": "Java", ".kt": "Kotlin",
    ".swift": "Swift", ".rb": "Ruby", ".php": "PHP",
    ".sh": "Shell", ".zsh": "Shell", ".bash": "Shell",
    ".yaml": "YAML", ".yml": "YAML", ".toml": "TOML",
    ".xml": "XML", ".sql": "SQL", ".r": "R",
}
MAX_AGENT_STEPS = 20
RULE_FILES = (".cursorrules", "AGENTS.md", "CLAUDE.md")


def preserve_file_content(text):
    """Keep exact whitespace; only normalize CRLF line endings."""
    if text is None:
        return ""
    if not isinstance(text, str):
        text = str(text)
    return text.replace("\r\n", "\n").replace("\r", "\n")


def read_file_exact(path):
    """Read a text file preserving exact on-disk whitespace."""
    with open(path, "r", encoding="utf-8", errors="replace", newline="") as f:
        return f.read()


def parse_tool_call(reply):
    """Extract a tool call from model output — tolerant of local LLM formats."""
    if not reply or not reply.strip():
        return None, "empty reply"

    blocks = TOOL_FENCE_RE.findall(reply)

    # Standalone ```write block: first line is path, rest is content
    for raw in blocks:
        text = raw.strip()
        if text.startswith("{"):
            continue
        lines = text.split("\n", 1)
        first = lines[0].strip()
        m = re.match(
            r'^(?:path:\s*)?["\']?([^"\'\s`]+\.\w+)["\']?\s*$', first, re.I)
        if m and len(lines) > 1:
            return {"tool": "write_file", "path": m.group(1),
                    "content": preserve_file_content(lines[1])}, None

    if not blocks:
        for m in re.finditer(r'\{[^{}]*"tool"\s*:\s*"[^"]+"', reply):
            start = m.start()
            depth = 0
            for i in range(start, len(reply)):
                if reply[i] == "{":
                    depth += 1
                elif reply[i] == "}":
                    depth -= 1
                    if depth == 0:
                        try:
                            return json.loads(reply[start:i + 1]), None
                        except json.JSONDecodeError:
                            break
        return None, "no tool fence — use ```tool {...}``` or Format B for writes"

    for i, raw in enumerate(blocks):
        text = raw.strip()
        if not text.startswith("{"):
            continue
        call = _parse_tool_json(text)
        if not call:
            continue
        tool = call.get("tool", "")
        if tool == "write_file" and not call.get("content"):
            for j in range(i + 1, len(blocks)):
                body = blocks[j]
                if body.strip().startswith("{"):
                    continue
                call["content"] = preserve_file_content(body)
                return call, None
            # path-only header — don't return yet; may pair with later block
            continue
        return call, None

    for raw in blocks:
        text = raw.strip()
        if not text.startswith("{"):
            continue
        call = _parse_tool_json(text)
        if call:
            return call, None

    return None, "no valid tool JSON in fences"


def _parse_tool_json(text):
    """Parse tool JSON; recover tool+path from broken JSON."""
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        tm = re.search(r'"tool"\s*:\s*"(\w+)"', text)
        pm = re.search(r'"(?:path|file|filename)"\s*:\s*"([^"]+)"', text)
        if not (tm and pm):
            return None
        call = {"tool": tm.group(1), "path": pm.group(1)}
        if call["tool"] == "write_file":
            cm = re.search(r'"content"\s*:\s*"(.*)"\s*\}', text, re.S)
            if cm:
                call["content"] = cm.group(1).encode().decode("unicode_escape")
        return call


def detect_language(path):
    ext = os.path.splitext(str(path or ""))[1].lower()
    return LANG_MAP.get(ext, ext.lstrip(".") or "Plain Text")


def env_context():
    return (
        f"OS: {PLATFORM} ({platform_mod.system()} {platform_mod.release()} "
        f"{platform_mod.machine()}) · shell: {SHELL_NAME} "
        f"({shutil.which(SHELL_ARGV[0]) or SHELL_ARGV[0]}) · "
        f"python: {sys.version.split()[0]}. "
        f"Use run_terminal commands appropriate for this OS and shell."
    )


def startup_workspace():
    return resolve_startup_workspace()


class AgentSession:
    """One AI agent conversation (Cursor-style parallel agent).
    Persisted to disk under ~/.catide/agents/ as JSON."""
    _next_id = 1

    def __init__(self, name=None, workspace=""):
        self.id = AgentSession._next_id
        AgentSession._next_id += 1
        self.name = name or f"Agent {self.id}"
        self.workspace = norm_workspace(workspace) if workspace else ""
        self.history = []
        self.streaming = False
        self.stop_flag = threading.Event()
        self.last_reply = ""
        self.checkpoints = {}       # path -> original content (None = created)
        self.transcript = ""        # rendered chat text (for restore)
        self.log = None             # tk.Text, attached by the UI
        self.tab_btn = None

    # -- persistence ---------------------------------------------------------
    def _ws_hash(self):
        return hashlib.sha1(self.workspace.encode("utf-8")).hexdigest()[:10]

    def _basename(self):
        return f"agent-{self._ws_hash()}-{self.id}.json"

    def _save_paths(self):
        """Global + workspace-local paths (Cursor-style project persistence)."""
        paths = [os.path.join(SESS_DIR, self._basename())]
        if self.workspace:
            paths.append(os.path.join(workspace_agent_dir(self.workspace),
                                      self._basename()))
        return paths

    def _file(self):
        return self._save_paths()[0]

    def _log_file(self):
        return os.path.join(LOG_DIR, f"agent-{self._ws_hash()}-{self.id}.log")

    @staticmethod
    def _ck_to_rel(workspace, checkpoints):
        out = {}
        for k, v in checkpoints.items():
            try:
                out[os.path.relpath(k, workspace)] = v
            except ValueError:
                out[k] = v
        return out

    @staticmethod
    def _ck_to_abs(workspace, checkpoints):
        out = {}
        for k, v in checkpoints.items():
            out[k if os.path.isabs(k) else os.path.normpath(
                os.path.join(workspace, k))] = v
        return out

    def save(self):
        data = {
            "id": self.id,
            "name": self.name,
            "workspace": self.workspace,
            "history": self.history,
            "last_reply": self.last_reply,
            "checkpoints": self._ck_to_rel(self.workspace, self.checkpoints),
            "transcript": self.transcript[-40000:],
            "platform": PLATFORM,
            "shell": SHELL_NAME,
            "updated": time.time(),
        }
        payload = json.dumps(data, ensure_ascii=False, indent=1)
        for dest in self._save_paths():
            try:
                os.makedirs(os.path.dirname(dest), exist_ok=True)
                tmp = dest + ".tmp"
                with open(tmp, "w", encoding="utf-8") as f:
                    f.write(payload)
                os.replace(tmp, dest)
            except OSError:
                pass

    def delete_from_disk(self):
        for dest in self._save_paths():
            try:
                os.remove(dest)
            except OSError:
                pass
        try:
            os.remove(self._log_file())
        except OSError:
            pass

    @classmethod
    def load_all(cls, workspace):
        """Restore saved sessions — workspace .catide/agents first, then global."""
        workspace = norm_workspace(workspace)
        ws = hashlib.sha1(workspace.encode("utf-8")).hexdigest()[:10]
        seen = {}
        search_dirs = []
        wdir = workspace_agent_dir(workspace)
        if os.path.isdir(wdir):
            search_dirs.append(wdir)
        if os.path.isdir(SESS_DIR) and SESS_DIR not in search_dirs:
            search_dirs.append(SESS_DIR)
        for sdir in search_dirs:
            try:
                names = sorted(os.listdir(sdir))
            except OSError:
                continue
            for fn in names:
                if not (fn.startswith(f"agent-{ws}-") and fn.endswith(".json")):
                    continue
                try:
                    with open(os.path.join(sdir, fn), "r",
                              encoding="utf-8") as f:
                        data = json.load(f)
                except (OSError, json.JSONDecodeError):
                    continue
                sid = data.get("id", 0)
                if sid in seen:
                    continue
                sess = cls.__new__(cls)
                sess.id = sid
                sess.name = data.get("name", f"Agent {sess.id}")
                sess.workspace = workspace
                sess.history = data.get("history", [])
                sess.streaming = False
                sess.stop_flag = threading.Event()
                sess.last_reply = data.get("last_reply", "")
                sess.checkpoints = cls._ck_to_abs(
                    workspace, data.get("checkpoints", {}))
                sess.transcript = data.get("transcript", "")
                sess.log = None
                sess.tab_btn = None
                cls._next_id = max(cls._next_id, sess.id + 1)
                seen[sid] = sess
        out = sorted(seen.values(), key=lambda s: s.id)
        return out


# =============================================================================
# Editor widget
# =============================================================================
class Editor(tk.Frame):
    def __init__(self, master, app, path=None):
        super().__init__(master, bg=EDITOR_BG)
        self.app = app
        self.path = path
        self.mono = mono_font(13)

        self.linenos = tk.Text(
            self, width=5, padx=8, takefocus=0, bd=0, bg=EDITOR_BG,
            fg=FG_FAINT, font=self.mono, state="disabled",
            highlightthickness=0, cursor="arrow")
        self.linenos.pack(side="left", fill="y")

        self.text = tk.Text(
            self, wrap="none", undo=True, bd=0, padx=10, pady=8,
            bg=EDITOR_BG, fg=FG, insertbackground=FG_BRIGHT,
            insertwidth=2, selectbackground=SEL_BG,
            selectforeground=FG_BRIGHT, font=self.mono,
            highlightthickness=0, tabs=(self.mono.measure("    "),))
        self.text.pack(side="left", fill="both", expand=True)

        ysb = tk.Scrollbar(self, orient="vertical", command=self._yscroll,
                           troughcolor=EDITOR_BG, bg=SIDEBAR_BG, bd=0,
                           activebackground=FG_DIM, highlightthickness=0,
                           relief="flat", width=10)
        ysb.pack(side="right", fill="y")
        self.text.configure(
            yscrollcommand=lambda a, b: (ysb.set(a, b), self._sync()))

        self.text.tag_configure("curline", background=CURLINE)
        for tag, color in SYNTAX.items():
            self.text.tag_configure(tag, foreground=color)
        self.text.tag_configure("ghost", foreground=FG_FAINT)
        self.text.tag_raise("sel")

        # Cursor Tab ghost-text state
        self.ghost_active = False
        self._ghost_after = None
        self._ghost_gen = 0
        self._ghost_pos = None

        self.text.bind("<KeyRelease>", self._on_change)
        self.text.bind("<KeyPress>", self._ghost_keypress, add=True)
        self.text.bind("<ButtonRelease-1>",
                       lambda e: (self.dismiss_ghost(), self._cursor_moved()))
        self.text.bind("<Return>", self._auto_indent)
        self.text.bind("<Tab>", self._soft_tab)
        self.text.bind("<Escape>", lambda e: self.dismiss_ghost())
        self.text.bind("<<Modified>>", self._on_modified)
        self._sync()

    # scrolling / gutters ------------------------------------------------
    def _yscroll(self, *args):
        self.text.yview(*args)
        self._sync()

    def _sync(self):
        lines = int(self.text.index("end-1c").split(".")[0])
        self.linenos.configure(state="normal")
        self.linenos.delete("1.0", "end")
        self.linenos.insert("1.0", "\n".join(str(i) for i in range(1, lines + 1)))
        self.linenos.configure(state="disabled")
        self.linenos.yview_moveto(self.text.yview()[0])

    # editing helpers ------------------------------------------------------
    def _auto_indent(self, _e):
        self.dismiss_ghost()
        line = self.text.get("insert linestart", "insert")
        indent = re.match(r"[ \t]*", line).group(0)
        if line.rstrip().endswith(":"):
            indent += "    "
        self.text.insert("insert", "\n" + indent)
        self.after_idle(self._on_change)
        return "break"

    def _soft_tab(self, _e):
        if self.ghost_active:
            self.accept_ghost()
        else:
            self.text.insert("insert", "    ")
        return "break"

    def _on_modified(self, _e):
        if self.text.edit_modified():
            self.app.mark_dirty(self)

    def _on_change(self, _e=None):
        self._sync()
        self.highlight()
        self._cursor_moved()
        if _e is not None and not self.ghost_active:
            self._schedule_ghost()

    # -- Cursor Tab: ghost-text autocomplete --------------------------------
    _MODIFIER_KEYS = frozenset((
        "Tab", "Shift_L", "Shift_R", "Control_L", "Control_R", "Alt_L",
        "Alt_R", "Meta_L", "Meta_R", "Super_L", "Super_R", "Caps_Lock"))

    def _ghost_keypress(self, ev):
        if self.ghost_active and ev.keysym not in self._MODIFIER_KEYS:
            self.dismiss_ghost()

    def _schedule_ghost(self):
        if self._ghost_after:
            self.after_cancel(self._ghost_after)
        self._ghost_after = self.after(700, self._request_ghost)

    def _request_ghost(self):
        self._ghost_after = None
        if self.ghost_active or self.text.tag_ranges("sel"):
            return
        if self.text.get("insert", "insert lineend").strip():
            return  # only complete at end of line
        self._ghost_gen += 1
        self._ghost_pos = self.text.index("insert")
        prefix = self.text.get("insert-60l linestart", "insert")
        suffix = self.text.get("insert", "insert+20l lineend")
        self.app.request_completion(self, self._ghost_gen, prefix, suffix)

    def show_ghost(self, gen, completion):
        if (gen != self._ghost_gen or self.ghost_active or not completion
                or self.text.index("insert") != self._ghost_pos):
            return
        completion = completion[:400]
        pos = self.text.index("insert")
        self.text.mark_set("ghost_start", pos)
        self.text.mark_gravity("ghost_start", "left")
        self.text.insert(pos, completion, "ghost")
        self.text.mark_set("ghost_end", f"{pos}+{len(completion)}c")
        self.text.mark_set("insert", pos)
        self.ghost_active = True

    def dismiss_ghost(self):
        if not self.ghost_active:
            return
        self.ghost_active = False
        try:
            self.text.delete("ghost_start", "ghost_end")
        except tk.TclError:
            pass

    def accept_ghost(self):
        self.ghost_active = False
        self.text.tag_remove("ghost", "ghost_start", "ghost_end")
        self.text.mark_set("insert", "ghost_end")
        self._on_change()

    def _cursor_moved(self):
        self.text.tag_remove("curline", "1.0", "end")
        self.text.tag_add("curline", "insert linestart", "insert lineend+1c")
        ln, col = self.text.index("insert").split(".")
        self.app.set_cursor_pos(int(ln), int(col) + 1)
        self.app._update_ctx_chip()

    # syntax highlighting -----------------------------------------------------
    _patterns = [
        ("string",  re.compile(
            r"('''.*?'''|\"\"\".*?\"\"\"|'[^'\n]*'|\"[^\"\n]*\")", re.S)),
        ("comment", re.compile(r"#[^\n]*")),
        ("deco",    re.compile(r"@\w[\w.]*")),
        ("number",  re.compile(r"\b\d+(\.\d+)?\b")),
        ("defname", re.compile(r"(?<=\bdef\s)\w+|(?<=\bclass\s)\w+")),
        ("kw",      re.compile(r"\b(" + "|".join(keyword.kwlist) + r")\b")),
        ("builtin", re.compile(
            r"\b(print|len|range|str|int|float|list|dict|set|tuple|open|type"
            r"|super|self|cls|isinstance|enumerate|zip|map|filter|sum|min|max"
            r"|abs|repr|input|sorted|any|all|True|False|None)\b")),
    ]

    def highlight(self):
        if self.path and not self.path.endswith((".py", ".pyw")):
            return
        src = self.text.get("1.0", "end-1c")
        if len(src) > 200_000:
            return
        for tag in SYNTAX:
            self.text.tag_remove(tag, "1.0", "end")
        for tag, pat in self._patterns:
            for m in pat.finditer(src):
                self.text.tag_add(tag, f"1.0+{m.start()}c", f"1.0+{m.end()}c")

    # content API ------------------------------------------------------------------
    def get(self):
        self.dismiss_ghost()
        return self.text.get("1.0", "end-1c")

    def set(self, content):
        self.text.delete("1.0", "end")
        self.text.insert("1.0", content)
        self.text.edit_modified(False)
        self.app.unmark_dirty(self)
        self._on_change()

    def goto(self, line):
        self.text.mark_set("insert", f"{line}.0")
        self.text.see(f"{line}.0")
        self.text.focus_set()
        self._cursor_moved()


# =============================================================================
# Integrated pty terminal (xterm-style)
# =============================================================================
class PtyTerminal(tk.Frame):
    """Cursor-style integrated pty terminal (xterm-like, color, workspace cwd)."""

    def __init__(self, master, cwd=None):
        super().__init__(master, bg=INPUT_BG)
        self.mono = mono_font(12)
        self.text = tk.Text(
            self, bg=INPUT_BG, fg=FG, bd=0, padx=10, pady=6,
            insertbackground=FG_BRIGHT, insertwidth=2, font=self.mono,
            selectbackground=SEL_BG, selectforeground=FG_BRIGHT,
            highlightthickness=0, wrap="char")
        self.text.pack(fill="both", expand=True)
        for code, color in TERM_COLORS.items():
            self.text.tag_configure(f"t{code}", foreground=color)
        self.text.tag_configure("tbold", font=ui_font(12, "bold"))
        self.text.bind("<Key>", self._key)
        self.text.bind("<<Paste>>", self._paste)
        self.text.bind("<Button-2>", lambda e: "break")
        self.text.bind("<Control-c>", lambda e: self._send_raw("\x03") or "break")
        self.text.bind("<Control-v>", self._paste)
        self.text.bind("<Control-l>", lambda e: self._clear_screen() or "break")
        if IS_MAC:
            self.text.bind("<Command-k>", lambda e: self._clear_screen() or "break")

        self.master_fd = None
        self.proc = None
        self.q = queue.Queue()
        self._pending_cr = False
        self._sgr = [FG]
        self.cwd = cwd or os.path.expanduser("~")
        self._alive = False

        try:
            self._spawn()
            self.after(40, self._poll)
            self.bind("<Configure>", self._resize)
        except OSError as e:
            self.text.insert("end",
                             f"pty unavailable ({e}) — use PipeTerminal.\n")
            self.text.configure(state="disabled")

    def _send_raw(self, seq):
        if self._alive and self.master_fd is not None:
            try:
                os.write(self.master_fd, seq.encode("utf-8"))
            except OSError:
                pass

    def _clear_screen(self):
        self.text.delete("1.0", "end")
        self._send_raw("\x0c")  # ^L

    def _spawn(self):
        env = os.environ.copy()
        env["TERM"] = "xterm-256color"
        env["CATIDE"] = APP_VERSION
        env["CATIDE_PLATFORM"] = PLATFORM
        self.master_fd, slave = pty.openpty()
        popen_kw = dict(
            stdin=slave, stdout=slave, stderr=slave,
            cwd=self.cwd, env=env, close_fds=True)
        if hasattr(os, "setsid") and PLATFORM not in ("windows", "android"):
            popen_kw["preexec_fn"] = os.setsid
        self.proc = subprocess.Popen(SHELL_ARGV, **popen_kw)
        os.close(slave)
        self._alive = True
        threading.Thread(target=self._reader, daemon=True).start()

    def _reader(self):
        while True:
            try:
                data = os.read(self.master_fd, 4096)
            except OSError:
                break
            if not data:
                break
            self.q.put(data.decode("utf-8", "replace"))
        self.q.put(None)

    def _poll(self):
        try:
            while True:
                item = self.q.get_nowait()
                if item is None:
                    self._write_plain("\n[process exited]\n")
                    return
                self._write(item)
        except queue.Empty:
            pass
        self.after(40, self._poll)

    def _sgr_tag(self):
        code = self._sgr[-1] if self._sgr else FG
        if isinstance(code, int):
            return f"t{code}"
        return None

    def _apply_sgr(self, spec):
        if not spec:
            self._sgr = [FG]
            return
        codes = [int(c) if c.isdigit() else 0 for c in spec.split(";") if c]
        if not codes:
            self._sgr = [FG]
            return
        i = 0
        while i < len(codes):
            c = codes[i]
            if c == 0:
                self._sgr = [FG]
            elif c == 1:
                self._sgr.append("bold")
            elif 30 <= c <= 37 or 90 <= c <= 97:
                self._sgr = [c]
            elif c == 39:
                self._sgr = [FG]
            i += 1

    def _write(self, data):
        parts = ANSI_SGR_RE.split(data)
        for i, part in enumerate(parts):
            if i % 2 == 1:
                self._apply_sgr(part)
                continue
            self._write_plain(ANSI_RE.sub("", part))

    def _write_plain(self, txt):
        tag = self._sgr_tag()
        bold = "bold" in self._sgr
        tags = tuple(t for t in (tag, "tbold" if bold else None) if t)
        buf = []

        def flush():
            if buf:
                if self._pending_cr:
                    self.text.delete("end-1c linestart", "end-1c lineend")
                    self._pending_cr = False
                chunk = "".join(buf)
                if tags:
                    self.text.insert("end", chunk, tags)
                else:
                    self.text.insert("end", chunk)
                buf.clear()

        for ch in txt:
            if ch == "\r":
                flush()
                self._pending_cr = True
            elif ch == "\n":
                flush()
                self._pending_cr = False
                self.text.insert("end", "\n")
            elif ch == "\x08":
                flush()
                try:
                    self.text.delete("end-2c", "end-1c")
                except tk.TclError:
                    pass
            elif ch == "\x07":
                continue
            else:
                buf.append(ch)
        flush()
        if int(self.text.index("end-1c").split(".")[0]) > 4000:
            self.text.delete("1.0", "500.0")
        self.text.see("end")

    _SPECIAL = {
        "Return": "\r", "BackSpace": "\x7f", "Tab": "\t", "Escape": "\x1b",
        "Up": "\x1b[A", "Down": "\x1b[B", "Right": "\x1b[C", "Left": "\x1b[D",
        "Home": "\x1b[H", "End": "\x1b[F", "Delete": "\x1b[3~",
    }

    def _key(self, ev):
        if not self._alive or self.master_fd is None:
            return "break"
        seq = self._SPECIAL.get(ev.keysym, ev.char)
        if seq:
            self._send_raw(seq)
        return "break"

    def _paste(self, _e):
        try:
            data = self.clipboard_get()
        except tk.TclError:
            return "break"
        self._send_raw(data)
        return "break"

    def _resize(self, _e):
        if self.master_fd is None:
            return
        try:
            cols = max(20, self.text.winfo_width() // self.mono.measure("M"))
            rows = max(5, self.text.winfo_height() //
                       self.mono.metrics("linespace"))
            fcntl.ioctl(self.master_fd, termios.TIOCSWINSZ,
                        struct.pack("HHHH", rows, cols, 0, 0))
        except OSError:
            pass

    def send(self, command):
        if self._alive and self.master_fd is not None:
            self._send_raw(command + "\n")

    def destroy(self):
        try:
            if self.proc:
                self.proc.terminate()
            if self.master_fd is not None:
                os.close(self.master_fd)
        except OSError:
            pass
        super().destroy()


class PipeTerminal(tk.Frame):
    """Cursor-style shell for platforms without pty — read-only output + input line."""

    def __init__(self, master, cwd=None):
        super().__init__(master, bg=INPUT_BG)
        self.mono = mono_font(12)
        self.cwd = cwd or os.path.expanduser("~")
        self.q = queue.Queue()
        self.proc = None

        self.out = tk.Text(
            self, bg=INPUT_BG, fg=FG, bd=0, padx=10, pady=6,
            insertbackground=FG_BRIGHT, font=self.mono,
            selectbackground=SEL_BG, selectforeground=FG_BRIGHT,
            highlightthickness=0, wrap="char", state="disabled")
        self.out.pack(fill="both", expand=True)

        row = tk.Frame(self, bg=PANEL_BG)
        row.pack(fill="x")
        self.prompt_lbl = tk.Label(
            row, text=f"{SHELL_NAME} ›", bg=PANEL_BG, fg=FG_DIM,
            font=mono_font(11), padx=8, pady=4)
        self.prompt_lbl.pack(side="left")
        self.input = tk.Entry(
            row, bg=INPUT_BG, fg=FG_BRIGHT, bd=0,
            insertbackground=FG_BRIGHT, font=self.mono,
            highlightthickness=1, highlightbackground=FG_FAINT,
            highlightcolor=ACCENT)
        self.input.pack(side="left", fill="x", expand=True, padx=(0, 8), pady=4)
        self.input.bind("<Return>", self._enter)
        self.input.bind("<Up>", self._hist_up)
        self.input.bind("<Down>", self._hist_down)
        self._history = []
        self._hist_idx = -1

        self._spawn()
        self.after(60, self._poll)

    def _spawn(self):
        env = os.environ.copy()
        env["CATIDE"] = APP_VERSION
        env["CATIDE_PLATFORM"] = PLATFORM
        creation = 0
        if PLATFORM == "windows":
            creation = getattr(subprocess, "CREATE_NO_WINDOW", 0)
        try:
            self.proc = subprocess.Popen(
                SHELL_ARGV, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, cwd=self.cwd, env=env,
                text=True, bufsize=1, creationflags=creation)
        except OSError as e:
            self._append(f"couldn't start {SHELL_NAME}: {e}\n")
            return
        self._append(f"CatIDE · {PLATFORM} · {SHELL_NAME} · {self.cwd}\n")
        threading.Thread(target=self._reader, daemon=True).start()

    def _reader(self):
        if not self.proc or not self.proc.stdout:
            self.q.put(None)
            return
        for line in self.proc.stdout:
            self.q.put(line)
        self.q.put(None)

    def _poll(self):
        try:
            while True:
                item = self.q.get_nowait()
                if item is None:
                    self._append("\n[process exited]\n")
                    return
                self._append(ANSI_RE.sub("", item))
        except queue.Empty:
            pass
        self.after(60, self._poll)

    def _append(self, s):
        self.out.configure(state="normal")
        self.out.insert("end", s)
        if int(self.out.index("end-1c").split(".")[0]) > 4000:
            self.out.delete("1.0", "500.0")
        self.out.see("end")
        self.out.configure(state="disabled")

    def _enter(self, _e):
        cmd = self.input.get().strip()
        self.input.delete(0, "end")
        if cmd:
            self._history.append(cmd)
            self._hist_idx = len(self._history)
            self._append(f"{SHELL_NAME} › {cmd}\n")
            self.send(cmd)
        return "break"

    def _hist_up(self, _e):
        if not self._history:
            return "break"
        self._hist_idx = max(0, self._hist_idx - 1)
        self.input.delete(0, "end")
        self.input.insert(0, self._history[self._hist_idx])
        return "break"

    def _hist_down(self, _e):
        if not self._history:
            return "break"
        self._hist_idx = min(len(self._history), self._hist_idx + 1)
        self.input.delete(0, "end")
        if self._hist_idx < len(self._history):
            self.input.insert(0, self._history[self._hist_idx])
        return "break"

    def focus_input(self):
        self.input.focus_set()

    def send(self, command):
        if self.proc and self.proc.stdin:
            try:
                self.proc.stdin.write(command + "\n")
                self.proc.stdin.flush()
            except OSError:
                pass

    def destroy(self):
        try:
            if self.proc:
                self.proc.kill()
        except OSError:
            pass
        super().destroy()


def make_terminal(master, cwd=None):
    """Autodetect the best terminal backend for this OS."""
    if HAS_PTY and PLATFORM not in ("windows",):
        try:
            term = PtyTerminal(master, cwd=cwd)
            if getattr(term, "_alive", False):
                return term
            term.destroy()
        except (OSError, AttributeError):
            pass
    return PipeTerminal(master, cwd=cwd)


# =============================================================================
# Main application
# =============================================================================
class CatIDE(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"{APP_NAME} {APP_VERSION} — AI Agents OS")
        self.geometry("1500x920")
        self.minsize(1000, 620)
        self.configure(bg=BG)

        self.lm = LMStudio()
        self.model_var = tk.StringVar(value="connecting…")
        self.models = []
        self.workspace = startup_workspace()
        self.ui_queue = queue.Queue()
        self.mode = tk.StringVar(value="Agent")
        self.sessions = []
        self.active_session = None
        self.completion_busy = False
        self.tab_enabled = tk.BooleanVar(value=True)
        self.git_branch = ""
        self._lm_warned = False
        self.settings = self._load_settings()
        self.rules_text = self._load_rules()

        self.tabs = {}          # path/key -> {"editor":..,"tabframe":..,"label":..}
        self.active_key = None
        self.terminals = []
        self.active_term = None

        self._style_ttk()
        self._build_menu()
        self._build_ui()
        self._bind_keys()
        self.protocol("WM_DELETE_WINDOW", self._quit_app)
        self.model_var.trace_add("write", lambda *_: self._save_settings())
        self.after(60, self._pump)
        self.after(5000, self._autosave_tick)
        threading.Thread(target=self._detect_models, daemon=True).start()
        threading.Thread(target=self._detect_git, daemon=True).start()
        self.after(30000, self._retry_lm_studio)
        self._open_welcome()
        self.populate_tree(self.workspace)
        self._restore_open_files()
        self._update_ctx_chip()

    # -- settings persistence ------------------------------------------------
    def _load_settings(self):
        try:
            with open(SETTINGS_PATH, "r", encoding="utf-8") as f:
                s = json.load(f)
        except (OSError, json.JSONDecodeError):
            s = {}
        ws = resolve_startup_workspace()
        if ws and os.path.isdir(ws):
            self.workspace = ws
        if "geometry" in s:
            try:
                self.geometry(s["geometry"])
            except tk.TclError:
                pass
        self.tab_enabled.set(bool(s.get("tab_autocomplete", True)))
        self.mode.set(s.get("mode", "Agent"))
        return s

    def _save_settings(self):
        s = {
            "workspace": self.workspace,
            "geometry": self.geometry(),
            "tab_autocomplete": self.tab_enabled.get(),
            "mode": self.mode.get(),
            "model": self.model_var.get(),
            "open_files": [k for k in self.tabs if os.path.sep in k],
        }
        try:
            tmp = SETTINGS_PATH + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(s, f, indent=1)
            os.replace(tmp, SETTINGS_PATH)
        except OSError:
            pass

    def _restore_open_files(self):
        for raw in self.settings.get("open_files", []):
            try:
                clean = sanitize_model_path(raw, self.workspace)
                path = self._canon_path(self._safe_path(clean))
            except (ValueError, OSError):
                continue
            if os.path.isfile(path) and self._in_workspace(path):
                self.open_path(path)

    def _autosave_tick(self):
        for s in self.sessions:
            if s.streaming or s.transcript:
                s.save()
        self.after(5000, self._autosave_tick)

    def _load_rules(self):
        """Read .cursorrules / AGENTS.md style workspace rules."""
        chunks = []
        for name in RULE_FILES:
            p = os.path.join(self.workspace, name)
            if os.path.isfile(p):
                try:
                    with open(p, "r", encoding="utf-8", errors="ignore") as f:
                        chunks.append(f.read()[:4000])
                except OSError:
                    pass
        rules_dir = os.path.join(self.workspace, ".cursor", "rules")
        if os.path.isdir(rules_dir):
            for fn in sorted(os.listdir(rules_dir)):
                if fn.endswith((".md", ".mdc")):
                    try:
                        with open(os.path.join(rules_dir, fn), "r",
                                  encoding="utf-8", errors="ignore") as f:
                            chunks.append(f.read()[:2000])
                    except OSError:
                        pass
        return "\n\n".join(chunks)

    def _detect_git(self):
        try:
            p = subprocess.run(
                ["git", "-C", self.workspace, "rev-parse", "--abbrev-ref",
                 "HEAD"], capture_output=True, text=True, timeout=5)
            branch = p.stdout.strip() if p.returncode == 0 else ""
        except (OSError, subprocess.TimeoutExpired):
            branch = ""
        self.ui_queue.put(("git", branch))

    # ------------------------------------------------------------------ ttk style
    def _style_ttk(self):
        st = ttk.Style(self)
        st.theme_use("clam")
        st.configure("Cat.Treeview", background=SIDEBAR_BG,
                     fieldbackground=SIDEBAR_BG, foreground=FG,
                     bordercolor=SIDEBAR_BG, borderwidth=0,
                     font=ui_font(11), rowheight=24)
        st.map("Cat.Treeview",
               background=[("selected", SEL_BG)],
               foreground=[("selected", FG_BRIGHT)])
        st.configure("Cat.Treeview.Heading", background=SIDEBAR_BG,
                     foreground=FG_DIM, borderwidth=0)
        st.layout("Cat.Treeview", [("Treeview.treearea", {"sticky": "nswe"})])

    # ------------------------------------------------------------------- helpers
    def _btn(self, parent, label, cmd, size=11, pad=(10, 4)):
        b = tk.Button(parent, text=label, command=cmd, bg=BTN_BG, fg=BTN_FG,
                      activebackground=BTN_HOVER, activeforeground=FG_BRIGHT,
                      bd=0, padx=pad[0], pady=pad[1], font=ui_font(size, "bold"),
                      cursor="hand2", highlightthickness=0, relief="flat")
        b.bind("<Enter>", lambda e: b.configure(bg=BTN_HOVER))
        b.bind("<Leave>", lambda e: b.configure(bg=BTN_BG))
        return b

    # --------------------------------------------------------------------- menu
    def _build_menu(self):
        m = tk.Menu(self)
        filem = tk.Menu(m, tearoff=0)
        filem.add_command(label="New File", accelerator=f"{MOD_LABEL}N",
                          command=self.new_file)
        filem.add_command(label="Open File…", accelerator=f"{MOD_LABEL}O",
                          command=self.open_file_dialog)
        filem.add_command(label="Open Folder…", command=self.open_folder_dialog)
        filem.add_separator()
        filem.add_command(label="Save", accelerator=f"{MOD_LABEL}S",
                          command=self.save_file)
        filem.add_command(label="Save As…", command=self.save_file_as)
        m.add_cascade(label="File", menu=filem)

        viewm = tk.Menu(m, tearoff=0)
        viewm.add_command(label="Command Palette…",
                          accelerator=f"{MOD_LABEL}⇧P",
                          command=self.command_palette)
        viewm.add_command(label="Toggle Sidebar", accelerator=f"{MOD_LABEL}B",
                          command=self.toggle_sidebar)
        viewm.add_command(label="Toggle Panel", accelerator=f"{MOD_LABEL}J",
                          command=self.toggle_panel)
        viewm.add_command(label="Toggle AI Pane", command=self.toggle_ai)
        m.add_cascade(label="View", menu=viewm)

        termm = tk.Menu(m, tearoff=0)
        termm.add_command(label="New Terminal", command=self.new_terminal)
        termm.add_command(label="Run Active File", accelerator=f"{MOD_LABEL}R",
                          command=self.run_file)
        m.add_cascade(label="Terminal", menu=termm)

        helpm = tk.Menu(m, tearoff=0)
        helpm.add_command(label=f"About {APP_NAME}", command=self.show_about)
        m.add_cascade(label="Help", menu=helpm)
        self.configure(menu=m)

    # ----------------------------------------------------------------------- UI
    def _build_ui(self):
        body = tk.Frame(self, bg=BG)
        body.pack(fill="both", expand=True)

        # activity bar -------------------------------------------------------
        act = tk.Frame(body, bg=ACTIVITY_BG, width=48)
        act.pack(side="left", fill="y")
        act.pack_propagate(False)
        self._act_buttons = {}
        for icon, key, tip in (("📁", "explorer", "Explorer"),
                               ("🔍", "search", "Search"),
                               ("🤖", "agents", "AI Agents"),
                               ("🖥", "terminal", "Terminal")):
            b = tk.Button(act, text=icon, bd=0, bg=ACTIVITY_BG, fg=FG_DIM,
                          activebackground=ACTIVITY_BG, activeforeground=ACCENT,
                          font=("Helvetica", 17), cursor="hand2",
                          highlightthickness=0,
                          command=lambda k=key: self._activity(k))
            b.pack(pady=(14 if not self._act_buttons else 6, 0))
            self._act_buttons[key] = b
        tk.Label(act, text="🐱", bg=ACTIVITY_BG, fg=FG_DIM,
                 font=("Helvetica", 16)).pack(side="bottom", pady=12)

        # main horizontal paned: sidebar | center | AI ------------------------
        self.hpane = tk.PanedWindow(body, orient="horizontal", bg=BG,
                                    sashwidth=4, bd=0, sashrelief="flat",
                                    opaqueresize=True)
        self.hpane.pack(side="left", fill="both", expand=True)

        self._build_sidebar()
        self._build_center()
        self._build_ai_pane()

        self.hpane.add(self.sidebar, minsize=170, width=250)
        self.hpane.add(self.center, minsize=420, stretch="always")
        self.hpane.add(self.ai_pane, minsize=300, width=430)

        self._build_status()
        self._activity("explorer")

    # sidebar ------------------------------------------------------------------
    def _build_sidebar(self):
        self.sidebar = tk.Frame(self.hpane, bg=SIDEBAR_BG)

        # EXPLORER view
        self.explorer_view = tk.Frame(self.sidebar, bg=SIDEBAR_BG)
        head = tk.Frame(self.explorer_view, bg=SIDEBAR_BG)
        head.pack(fill="x")
        self.explorer_label = tk.Label(
            head, text="EXPLORER", bg=SIDEBAR_BG, fg=FG_DIM,
            font=ui_font(10, "bold"), anchor="w", padx=12, pady=8)
        self.explorer_label.pack(side="left")
        self._btn(head, "⟳", lambda: self.populate_tree(self.workspace),
                  size=10, pad=(6, 2)).pack(side="right", padx=6)

        self.tree = ttk.Treeview(self.explorer_view, style="Cat.Treeview",
                                 show="tree", selectmode="browse")
        self.tree.pack(fill="both", expand=True, padx=4, pady=(0, 6))
        self.tree.bind("<<TreeviewOpen>>", self._tree_open)
        self.tree.bind("<Double-1>", self._tree_activate)

        # SEARCH view
        self.search_view = tk.Frame(self.sidebar, bg=SIDEBAR_BG)
        tk.Label(self.search_view, text="SEARCH", bg=SIDEBAR_BG, fg=FG_DIM,
                 font=ui_font(10, "bold"), anchor="w", padx=12, pady=8
                 ).pack(fill="x")
        self.search_entry = tk.Entry(
            self.search_view, bg=INPUT_BG, fg=FG_BRIGHT, bd=0,
            insertbackground=FG_BRIGHT, font=ui_font(12),
            highlightthickness=1, highlightbackground=FG_FAINT,
            highlightcolor=ACCENT)
        self.search_entry.pack(fill="x", padx=10, ipady=5)
        self.search_entry.bind("<Return>", lambda e: self.run_search())
        self.search_results = tk.Listbox(
            self.search_view, bg=SIDEBAR_BG, fg=FG, bd=0,
            selectbackground=SEL_BG, selectforeground=FG_BRIGHT,
            font=ui_font(10), highlightthickness=0, activestyle="none")
        self.search_results.pack(fill="both", expand=True, padx=6, pady=8)
        self.search_results.bind("<Double-1>", self._search_open)
        self._search_hits = []

    def _activity(self, key):
        for k, b in self._act_buttons.items():
            b.configure(fg=ACCENT if k == key else FG_DIM)
        if key == "agents":
            self.ai_input.focus_set()
            return
        if key == "terminal":
            self.show_panel_tab("TERMINAL")
            if self.active_term:
                if hasattr(self.active_term, "focus_input"):
                    self.active_term.focus_input()
                elif hasattr(self.active_term, "text"):
                    self.active_term.text.focus_set()
            return
        self.explorer_view.pack_forget()
        self.search_view.pack_forget()
        if key == "explorer":
            self.explorer_view.pack(fill="both", expand=True)
        elif key == "search":
            self.search_view.pack(fill="both", expand=True)
            self.search_entry.focus_set()

    # center: tabs + editor + bottom panel -----------------------------------------
    def _build_center(self):
        self.center = tk.Frame(self.hpane, bg=BG)
        self.vpane = tk.PanedWindow(self.center, orient="vertical", bg=BG,
                                    sashwidth=4, bd=0, sashrelief="flat")
        self.vpane.pack(fill="both", expand=True)

        editor_zone = tk.Frame(self.vpane, bg=EDITOR_BG)
        self.tabbar = tk.Frame(editor_zone, bg=TAB_BG, height=34)
        self.tabbar.pack(fill="x")
        self.tabbar.pack_propagate(False)
        self.editor_holder = tk.Frame(editor_zone, bg=EDITOR_BG)
        self.editor_holder.pack(fill="both", expand=True)
        self.vpane.add(editor_zone, stretch="always", minsize=220)

        # bottom panel -------------------------------------------------------
        self.panel = tk.Frame(self.vpane, bg=PANEL_BG)
        self.vpane.add(self.panel, height=240, minsize=100)

        ptabs = tk.Frame(self.panel, bg=PANEL_BG)
        ptabs.pack(fill="x")
        self._panel_tab_btns = {}
        for name in ("TERMINAL", "AI AGENT", "OUTPUT", "PROBLEMS"):
            b = tk.Button(ptabs, text=name, bd=0, bg=PANEL_BG, fg=FG_DIM,
                          activebackground=PANEL_BG, activeforeground=FG_BRIGHT,
                          font=ui_font(10, "bold"), cursor="hand2", padx=12,
                          pady=6, highlightthickness=0,
                          command=lambda n=name: self.show_panel_tab(n))
            b.pack(side="left")
            self._panel_tab_btns[name] = b
        self._btn(ptabs, f"＋ {SHELL_NAME}", self.new_terminal, size=10,
                  pad=(8, 2)).pack(side="right", padx=8, pady=3)
        self.term_selector = tk.Frame(ptabs, bg=PANEL_BG)
        self.term_selector.pack(side="right")

        self.panel_stack = tk.Frame(self.panel, bg=PANEL_BG)
        self.panel_stack.pack(fill="both", expand=True)

        # TERMINAL page
        self.term_page = tk.Frame(self.panel_stack, bg=INPUT_BG)

        # AI AGENT terminal page (read-only log of agent tool activity)
        self.agent_term = tk.Text(
            self.panel_stack, bg=INPUT_BG, fg=FG, bd=0, padx=10, pady=6,
            font=mono_font(12), state="disabled", wrap="word",
            highlightthickness=0)
        self.agent_term.tag_configure("cmd", foreground=FG_BRIGHT)
        self.agent_term.tag_configure("ok", foreground=OK_GREEN)
        self.agent_term.tag_configure("err", foreground=ERR_RED)
        self.agent_term.tag_configure("dim", foreground=FG_DIM)

        # OUTPUT page
        self.output = tk.Text(
            self.panel_stack, bg=INPUT_BG, fg=FG, bd=0, padx=10, pady=6,
            font=mono_font(12), state="disabled", highlightthickness=0)

        # PROBLEMS page
        self.problems = tk.Listbox(
            self.panel_stack, bg=INPUT_BG, fg=WARN_YEL, bd=0,
            selectbackground=SEL_BG, font=mono_font(11),
            highlightthickness=0, activestyle="none")

        self._panel_pages = {
            "TERMINAL": self.term_page, "AI AGENT": self.agent_term,
            "OUTPUT": self.output, "PROBLEMS": self.problems,
        }
        self.new_terminal()
        self.show_panel_tab("TERMINAL")

    def show_panel_tab(self, name):
        for n, page in self._panel_pages.items():
            page.pack_forget()
            self._panel_tab_btns[n].configure(fg=FG_DIM)
        self._panel_pages[name].pack(fill="both", expand=True)
        self._panel_tab_btns[name].configure(fg=FG_BRIGHT)

    # terminals ---------------------------------------------------------------------
    def _term_cwd_label(self):
        try:
            rel = os.path.relpath(self.workspace, os.path.expanduser("~"))
            if not rel.startswith(".."):
                return f"~/{rel}"
        except ValueError:
            pass
        return os.path.basename(self.workspace) or self.workspace

    def new_terminal(self):
        holder = tk.Frame(self.term_page, bg=INPUT_BG)
        header = tk.Frame(holder, bg=PANEL_BG, height=26)
        header.pack(fill="x")
        header.pack_propagate(False)
        cwd_lbl = tk.Label(
            header, text=self._term_cwd_label(), bg=PANEL_BG, fg=FG_DIM,
            font=ui_font(10), anchor="w", padx=10)
        cwd_lbl.pack(side="left", fill="x", expand=True)
        self._btn(header, "Clear", lambda t=None: self._clear_term(holder),
                  size=9, pad=(6, 2)).pack(side="right", padx=2, pady=2)

        term = make_terminal(holder, cwd=self.workspace)
        term.pack(fill="both", expand=True)
        term._holder = holder
        term._cwd_label = cwd_lbl
        self.terminals.append(term)
        idx = len(self.terminals)

        tab = tk.Frame(self.term_selector, bg=PANEL_BG)
        tab.pack(side="left", padx=2)
        b = tk.Button(tab, text=f"{SHELL_NAME} {idx}", bd=0,
                      bg=PANEL_BG, fg=FG_DIM, font=ui_font(10),
                      activebackground=PANEL_BG, activeforeground=FG_BRIGHT,
                      cursor="hand2", highlightthickness=0,
                      command=lambda t=term: self._select_term(t))
        b.pack(side="left")
        x = tk.Button(tab, text="×", bd=0, bg=PANEL_BG, fg=FG_FAINT,
                      activebackground=PANEL_BG, activeforeground=ERR_RED,
                      font=ui_font(9), padx=4, cursor="hand2",
                      highlightthickness=0,
                      command=lambda t=term: self.close_terminal(t))
        x.pack(side="left")
        term._selector_btn = b
        term._selector_tab = tab
        holder._term = term
        term._last_cd = self._canon_path(self.workspace)
        self._select_term(term)

    def _clear_term(self, holder):
        term = getattr(holder, "_term", None)
        if term is None:
            return
        if hasattr(term, "_clear_screen"):
            term._clear_screen()
        elif hasattr(term, "out"):
            term.out.configure(state="normal")
            term.out.delete("1.0", "end")
            term.out.configure(state="disabled")

    def close_terminal(self, term):
        if term not in self.terminals:
            return
        if hasattr(term, "_selector_tab"):
            term._selector_tab.destroy()
        if hasattr(term, "_holder"):
            term._holder.destroy()
        else:
            term.destroy()
        self.terminals.remove(term)
        if self.terminals:
            self._select_term(self.terminals[-1])
        else:
            self.active_term = None
            self.new_terminal()

    def _cd_terminals(self):
        label = self._term_cwd_label()
        cwd = self._canon_path(self.workspace)
        q = shlex.quote(cwd)
        for term in self.terminals:
            term.cwd = cwd
            if hasattr(term, "_cwd_label"):
                term._cwd_label.configure(text=label)
            alive = getattr(term, "_alive", False) or (
                term.proc and term.proc.poll() is None)
            if not alive:
                continue
            if paths_equal(getattr(term, "_last_cd", ""), cwd):
                continue
            # builtin cd -- handles spaces/colons in volume paths (macOS)
            term.send(f"builtin cd -- {q}")
            term._last_cd = cwd

    def _select_term(self, term):
        for t in self.terminals:
            if hasattr(t, "_holder"):
                t._holder.pack_forget()
            else:
                t.pack_forget()
            if hasattr(t, "_selector_btn"):
                t._selector_btn.configure(fg=FG_DIM)
        if hasattr(term, "_holder"):
            term._holder.pack(fill="both", expand=True)
        else:
            term.pack(fill="both", expand=True)
        if hasattr(term, "_selector_btn"):
            term._selector_btn.configure(fg=ACCENT)
        self.active_term = term
        self.show_panel_tab("TERMINAL")
        if hasattr(term, "focus_input"):
            term.focus_input()
        elif hasattr(term, "text"):
            term.text.focus_set()

    # AI pane ----------------------------------------------------------------------
    def _build_ai_pane(self):
        self.ai_pane = tk.Frame(self.hpane, bg=SIDEBAR_BG)

        head = tk.Frame(self.ai_pane, bg=SIDEBAR_BG)
        head.pack(fill="x", padx=10, pady=(10, 4))
        tk.Label(head, text="✦ AI Agents", bg=SIDEBAR_BG, fg=FG_BRIGHT,
                 font=ui_font(13, "bold")).pack(side="left")
        self._btn(head, "＋ Agent", self.new_session, size=10).pack(
            side="right", padx=2)
        self._btn(head, "Apply ⤶", self.apply_code, size=10).pack(
            side="right", padx=2)

        # session tabs (parallel agents)
        self.session_bar = tk.Frame(self.ai_pane, bg=SIDEBAR_BG)
        self.session_bar.pack(fill="x", padx=10, pady=(0, 4))

        # mode tabs
        modes = tk.Frame(self.ai_pane, bg=SIDEBAR_BG)
        modes.pack(fill="x", padx=10)
        self._mode_btns = {}
        for name in ("Agent", "Ask", "Plan"):
            b = tk.Button(modes, text=name, bd=0, bg=BTN_BG, fg=FG_DIM,
                          activebackground=BTN_HOVER,
                          activeforeground=FG_BRIGHT, font=ui_font(11, "bold"),
                          padx=14, pady=4, cursor="hand2",
                          highlightthickness=0,
                          command=lambda n=name: self.set_mode(n))
            b.pack(side="left", padx=(0, 4))
            self._mode_btns[name] = b

        # model picker
        row = tk.Frame(self.ai_pane, bg=SIDEBAR_BG)
        row.pack(fill="x", padx=10, pady=6)
        tk.Label(row, text="model", bg=SIDEBAR_BG, fg=FG_FAINT,
                 font=ui_font(10)).pack(side="left")
        self.model_menu = tk.OptionMenu(row, self.model_var, "connecting…")
        self.model_menu.configure(bg=BTN_BG, fg=BTN_FG, bd=0,
                                  activebackground=BTN_HOVER,
                                  activeforeground=FG_BRIGHT,
                                  font=ui_font(10), highlightthickness=0,
                                  indicatoron=False, padx=10, pady=3,
                                  cursor="hand2")
        self.model_menu["menu"].configure(bg=BTN_BG, fg=FG,
                                          activebackground=SEL_BG,
                                          activeforeground=FG_BRIGHT, bd=0)
        self.model_menu.pack(side="left", padx=6)

        # chat logs stack (one Text per session)
        self.chat_stack = tk.Frame(self.ai_pane, bg=EDITOR_BG)
        self.chat_stack.pack(fill="both", expand=True, padx=10, pady=(2, 6))

        # review bar (checkpoints: Keep All / Undo All)
        self.review_bar = tk.Frame(self.ai_pane, bg=BTN_HOVER)
        self.review_label = tk.Label(self.review_bar, text="", bg=BTN_HOVER,
                                     fg=FG_BRIGHT, font=ui_font(10, "bold"),
                                     padx=8)
        self.review_label.pack(side="left")
        self._btn(self.review_bar, "Undo All", self.undo_all_changes,
                  size=10).pack(side="right", padx=(2, 6), pady=3)
        self._btn(self.review_bar, "Keep All", self.keep_all_changes,
                  size=10).pack(side="right", padx=2, pady=3)
        self._btn(self.review_bar, "Review Diff", self.review_changes,
                  size=10).pack(side="right", padx=2, pady=3)

        # context chip + input
        foot = tk.Frame(self.ai_pane, bg=SIDEBAR_BG)
        foot.pack(fill="x", padx=10, pady=(0, 10))
        self.ai_foot = foot
        chipline = tk.Frame(foot, bg=SIDEBAR_BG)
        chipline.pack(fill="x")
        self.ctx_chip = tk.Label(chipline, text="@ auto", bg=BTN_BG,
                                 fg=FG_DIM, font=ui_font(10), padx=8, pady=2)
        self.ctx_chip.pack(side="left")
        self.include_code = tk.BooleanVar(value=True)
        tk.Label(chipline, text="Cursor-style autodetect",
                 bg=SIDEBAR_BG, fg=FG_FAINT, font=ui_font(9)
                 ).pack(side="right")

        box = tk.Frame(foot, bg=SIDEBAR_BG)
        box.pack(fill="x", pady=(6, 0))
        self.ai_input = tk.Text(
            box, height=3, bg=INPUT_BG, fg=FG_BRIGHT, bd=0, padx=10, pady=8,
            wrap="word", font=ui_font(12), insertbackground=FG_BRIGHT,
            highlightthickness=1, highlightbackground=FG_FAINT,
            highlightcolor=ACCENT)
        self.ai_input.pack(side="left", fill="both", expand=True)
        self.ai_input.bind("<Return>", self._ai_return)
        self.ai_input.bind("<Shift-Return>", lambda e: None)
        self.send_btn = self._btn(box, "▶", self.send_chat, size=13,
                                  pad=(12, 8))
        self.send_btn.pack(side="right", fill="y", padx=(6, 0))

        self.set_mode(self.mode.get())
        # restore saved agent sessions from disk, else start fresh
        restored = AgentSession.load_all(self.workspace)
        if restored:
            for s in restored:
                self._attach_session(s, select=False)
            self.select_session(self.sessions[-1])
            self._chat_write(
                f"✦ restored {len(restored)} agent session"
                f"{'s' if len(restored) != 1 else ''} from "
                f"{workspace_agent_dir(self.workspace)}\n", "tool")
        else:
            self.new_session()
            self._chat_write(
                "✦ CatIDE Agents ready. Agent mode can read/write/"
                "edit files, grep, and run terminal commands. Run "
                "several agents in parallel with ＋ Agent. "
                f"{MOD_LABEL}I focus · {MOD_LABEL}K inline edit · "
                f"Tab accepts ghost completions. Sessions autosave to "
                f"{workspace_agent_dir(self.workspace)} and {SESS_DIR}.\n",
                "tool")

    # session management (parallel agents) ---------------------------------
    def new_session(self):
        sess = AgentSession(workspace=self.workspace)
        self._attach_session(sess)
        sess.save()
        self.set_status(f"new agent · saved to {workspace_agent_dir(self.workspace)}")
        return sess

    def _attach_session(self, sess, select=True):
        log = tk.Text(self.chat_stack, bg=EDITOR_BG, fg=FG, bd=0, padx=12,
                      pady=10, wrap="word", font=ui_font(12),
                      state="disabled", highlightthickness=0)
        log.tag_configure("you", foreground=FG_BRIGHT,
                          font=ui_font(12, "bold"))
        log.tag_configure("cat", foreground="#4dd0e1",
                          font=ui_font(12, "bold"))
        log.tag_configure("tool", foreground=FG_DIM,
                          font=ui_font(11, "italic"))
        log.tag_configure("err", foreground=ERR_RED)
        log.tag_configure("code", foreground=FG_BRIGHT, font=mono_font(11))
        sess.log = log

        holder = tk.Frame(self.session_bar, bg=SIDEBAR_BG)
        holder.pack(side="left", padx=(0, 4))
        btn = tk.Button(holder, text=sess.name, bd=0, bg=BTN_BG, fg=FG_DIM,
                        activebackground=BTN_HOVER, activeforeground=FG_BRIGHT,
                        font=ui_font(10, "bold"), padx=10, pady=3,
                        cursor="hand2", highlightthickness=0,
                        command=lambda s=sess: self.select_session(s))
        btn.pack(side="left")
        x = tk.Button(holder, text="✕", bd=0, bg=BTN_BG, fg=FG_FAINT,
                      activebackground=BTN_HOVER, activeforeground=ERR_RED,
                      font=ui_font(9), padx=4, cursor="hand2",
                      highlightthickness=0,
                      command=lambda s=sess: self.close_session(s))
        x.pack(side="left")
        sess.tab_btn = btn
        sess._holder = holder

        # restore transcript from disk into the log widget
        if sess.transcript:
            log.configure(state="normal")
            log.insert("end", sess.transcript)
            log.configure(state="disabled")

        self.sessions.append(sess)
        if select:
            self.select_session(sess)
        return sess

    def _reload_agent_sessions(self):
        """Swap agent tabs to match the current workspace (disk-backed)."""
        for s in list(self.sessions):
            s.stop_flag.set()
            s.save()
            s._holder.destroy()
            s.log.destroy()
        self.sessions.clear()
        self.active_session = None
        restored = AgentSession.load_all(self.workspace)
        if restored:
            for s in restored:
                self._attach_session(s, select=False)
            self.select_session(self.sessions[-1])
            self._chat_write(
                f"✦ loaded {len(restored)} agent session"
                f"{'s' if len(restored) != 1 else ''} for this workspace "
                f"({workspace_agent_dir(self.workspace)})\n", "tool")
        else:
            self.new_session()
            self._chat_write(
                f"✦ new agent for workspace · autosave → "
                f"{workspace_agent_dir(self.workspace)}\n",
                "tool")

    def select_session(self, sess):
        self.active_session = sess
        for s in self.sessions:
            s.log.pack_forget()
            s.tab_btn.configure(fg=FG_DIM, bg=BTN_BG)
        sess.log.pack(fill="both", expand=True)
        sess.tab_btn.configure(fg=ACCENT, bg=BTN_HOVER)
        self._update_review_bar()
        self._update_send_btn()

    def close_session(self, sess):
        if len(self.sessions) <= 1:
            self.clear_chat()
            return
        sess.stop_flag.set()
        sess.delete_from_disk()
        self.sessions.remove(sess)
        sess._holder.destroy()
        sess.log.destroy()
        if self.active_session is sess:
            self.select_session(self.sessions[-1])

    def _session_by_id(self, sid):
        for s in self.sessions:
            if s.id == sid:
                return s
        return None

    def _update_send_btn(self):
        if self.active_session and self.active_session.streaming:
            self.send_btn.configure(text="■")
        else:
            self.send_btn.configure(text="▶")

    def _session_spinner(self):
        for s in self.sessions:
            base = s.name
            s.tab_btn.configure(text=("⟳ " + base) if s.streaming else base)

    def set_mode(self, name):
        self.mode.set(name)
        for n, b in self._mode_btns.items():
            b.configure(fg=ACCENT if n == name else FG_DIM,
                        bg=BTN_HOVER if n == name else BTN_BG)
        self._save_settings()

    # status bar -------------------------------------------------------------------
    def _build_status(self):
        sb = tk.Frame(self, bg=STATUS_BG, height=24)
        sb.pack(fill="x", side="bottom")
        sb.pack_propagate(False)

        def cell(text, side="left"):
            lab = tk.Label(sb, text=text, bg=STATUS_BG, fg="#dce9ff",
                           font=ui_font(10), padx=10)
            lab.pack(side=side)
            return lab

        cell(f"⚡ {APP_NAME} {APP_VERSION}")
        self.status_git = cell("")
        self.status_msg = cell("ready to vibe ✦")
        self.status_model = cell("model: —", "right")
        self.status_tab = cell(
            f"Tab: {'on' if self.tab_enabled.get() else 'off'}", "right")
        self.status_tab.configure(cursor="hand2")
        self.status_tab.bind("<Button-1>", lambda e: self._toggle_tab())
        cell(f"{PLATFORM} · {SHELL_NAME}{' · pty' if HAS_PTY else ''}",
             "right")
        cell("UTF-8", "right")
        cell("Python", "right")
        self.status_pos = cell("Ln 1, Col 1", "right")

    def _toggle_tab(self):
        self.tab_enabled.set(not self.tab_enabled.get())
        self.status_tab.configure(
            text=f"Tab: {'on' if self.tab_enabled.get() else 'off'}")
        self._save_settings()

    # ------------------------------------------------------------------- keybinds
    def _bind_keys(self):
        self.bind(f"<{MOD}-s>", lambda e: self.save_file())
        self.bind(f"<{MOD}-o>", lambda e: self.open_file_dialog())
        self.bind(f"<{MOD}-n>", lambda e: self.new_file())
        self.bind(f"<{MOD}-r>", lambda e: self.run_file())
        self.bind(f"<{MOD}-w>", lambda e: self.close_active_tab())
        self.bind(f"<{MOD}-b>", lambda e: self.toggle_sidebar())
        self.bind(f"<{MOD}-j>", lambda e: self.toggle_panel())
        self.bind(f"<{MOD}-i>", lambda e: self.ai_input.focus_set())
        self.bind(f"<{MOD}-k>", lambda e: self.inline_edit())
        self.bind(f"<{MOD}-Shift-p>", lambda e: self.command_palette())
        self.bind(f"<{MOD}-P>", lambda e: self.command_palette())

    def _ai_return(self, _e):
        self.send_chat()
        return "break"

    # =========================================================================
    # File explorer (Cursor 3: flat workspace root — no duplicate folder node)
    # =========================================================================
    def _canon_path(self, path, base=None):
        """Canonical absolute path for tabs, tree nodes, and comparisons."""
        if not path:
            return path
        p = normalize_path(path, base=base or self.workspace)
        if not os.path.isabs(p):
            p = normalize_path(p, base=self.workspace)
        try:
            return os.path.realpath(p)
        except OSError:
            return norm_workspace(p)

    def _in_workspace(self, full, root=None):
        root = self._canon_path(root or self.workspace)
        try:
            full = self._canon_path(full)
        except (OSError, ValueError):
            return False
        if PLATFORM == "windows":
            rl, rf = root.lower(), full.lower()
            return rf == rl or rf.startswith(rl + os.sep.lower())
        if full == root or full.startswith(root + os.sep):
            return True
        sr, sf = squash_path(root), squash_path(full)
        return sf == sr or sf.startswith(sr + os.sep)

    def _strip_workspace_prefix(self, rel, root):
        """Remove duplicated workspace folder name from model paths."""
        rel = rel.replace("\\", os.sep).lstrip(os.sep)
        base = os.path.basename(root.rstrip(os.sep))
        if not base:
            return rel
        parts = rel.split(os.sep)
        while parts and parts[0] == base:
            parts.pop(0)
        return os.sep.join(parts) if parts else ""

    def _ensure_parent_dirs(self, path):
        """Create all parent directories for a file path (Cursor-style)."""
        p = normalize_path(path, base=self.workspace)
        if not os.path.isabs(p):
            p = os.path.abspath(os.path.join(self.workspace, p))
        parent = os.path.dirname(p)
        if parent and parent != p:
            os.makedirs(parent, exist_ok=True)
        return p

    def _find_workspace_match(self, rel, root):
        """Find an existing file in workspace matching a relative path."""
        rel = rel.replace("\\", os.sep).lstrip(os.sep)
        if not rel:
            return None
        direct = os.path.join(root, rel)
        if os.path.exists(direct):
            return direct
        target = rel.lower()
        bn = os.path.basename(rel).lower()
        best = None
        best_len = 10 ** 9
        try:
            for dirpath, dirnames, filenames in os.walk(root):
                dirnames[:] = [d for d in dirnames if d not in SKIP_TREE]
                if dirpath.replace(root, "").count(os.sep) > 5:
                    dirnames.clear()
                    continue
                for fn in filenames:
                    full = os.path.join(dirpath, fn)
                    try:
                        r = os.path.relpath(full, root)
                    except ValueError:
                        continue
                    rl = r.lower()
                    if rl == target or rl.endswith(os.sep + target):
                        return full
                    if fn.lower() == bn and len(r) < best_len:
                        best = full
                        best_len = len(r)
        except OSError:
            pass
        return best

    def _safe_path(self, rel):
        """Resolve any model/user path to an absolute path inside the workspace."""
        root = self._canon_path(self.workspace)
        raw = sanitize_model_path(rel, self.workspace)
        raw = str(raw).strip().strip('"').strip("'")
        if not raw or raw in (".", "./"):
            return root

        clean = raw.replace("\\", os.sep)
        if any(p == ".." for p in re.split(r"[/\\]", clean)):
            raise ValueError("path escapes workspace")

        candidates = []

        def add(*paths):
            for p in paths:
                if p and p not in candidates:
                    candidates.append(p)

        add(normalize_path(raw, base=root))
        if raw.lower().startswith("file:"):
            add(normalize_path(raw))
        elif os.path.isabs(raw) or (len(raw) > 1 and raw[1] == ":"):
            add(normalize_path(raw))

        rel_clean = self._strip_workspace_prefix(clean, root)
        if rel_clean:
            add(os.path.join(root, rel_clean))
            match = self._find_workspace_match(rel_clean, root)
            if match:
                add(match)

        # Leading-slash paths (/catide4k.py, /:Coding~/CatIDE0.1/…) → workspace-relative
        if clean.startswith(("/", "\\")):
            tail = self._strip_workspace_prefix(clean.lstrip("/\\"), root)
            if tail:
                add(os.path.join(root, tail))
                match = self._find_workspace_match(tail, root)
                if match:
                    add(match)
            bn = os.path.basename(tail or clean)
            if bn:
                add(os.path.join(root, bn))
            # overlap with workspace suffix (:Coding~/CatIDE0.1/…)
            for part in (tail or clean).split("/"):
                if part and root.endswith(part):
                    rest = (tail or clean).split(part, 1)[-1].lstrip("/")
                    if rest:
                        add(os.path.join(root, self._strip_workspace_prefix(
                            rest, root) or rest))
                    elif part == os.path.basename(root):
                        add(root)

        # No leading slash: volume fragment or folder name
        if not os.path.isabs(clean) and not clean.lower().startswith("file:"):
            stripped = self._strip_workspace_prefix(clean, root)
            if stripped:
                add(os.path.join(root, stripped))
                match = self._find_workspace_match(stripped, root)
                if match:
                    add(match)
            if clean.startswith(":") or clean.startswith("~"):
                add(os.path.join(root, os.path.basename(clean)))

        bn = os.path.basename(clean)
        if bn and bn not in (".", "..", clean):
            add(os.path.join(root, bn))

        # macOS volume paths with missing spaces
        if " " in root or " " in raw:
            add(normalize_path(raw.replace(" ", ""), base=root.replace(" ", "")))
            if os.path.isabs(raw.replace(" ", "")):
                add(normalize_path(raw.replace(" ", "")))

        seen = set()
        in_ws = []
        for c in candidates:
            try:
                full = self._canon_path(c)
            except (OSError, ValueError):
                continue
            if full in seen:
                continue
            seen.add(full)
            if self._in_workspace(full, root):
                in_ws.append(full)

        if not in_ws:
            raise ValueError(
                f"path escapes workspace — use a path relative to "
                f"{os.path.basename(root) or root}, e.g. catide4k.py")

        existing = [p for p in in_ws if os.path.exists(p)]
        if existing:
            existing.sort(key=lambda p: (
                0 if os.path.isfile(p) else 1, len(p)))
            return existing[0]
        in_ws.sort(key=len)
        return in_ws[0]

    def _write_file_exact(self, path, content):
        """Atomic disk write — exact whitespace, fsync, creates parent dirs."""
        path = self._ensure_parent_dirs(path)
        content = preserve_file_content(content)
        tmp = f"{path}.catide.{os.getpid()}.tmp"
        try:
            with open(tmp, "w", encoding="utf-8", newline="") as f:
                f.write(content)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp, path)
        except OSError as e:
            try:
                if os.path.exists(tmp):
                    os.remove(tmp)
            except OSError:
                pass
            raise OSError(
                f"could not write {path}: {e}") from e
        return path

    def _sync_editor_from_disk(self, path):
        """Reload open tab from disk so editor matches exact on-disk bytes."""
        path = self._canon_path(path)
        if path not in self.tabs:
            return
        try:
            disk = read_file_exact(path)
        except OSError:
            return
        ed = self.tabs[path]["editor"]
        ed.set(disk)
        ed.text.edit_modified(False)
        t = self.tabs[path]
        t["label"].configure(text=t["title"])

    def _tool_path(self, call):
        """Extract path string from tool call (resolution happens in _safe_path)."""
        p = (call.get("path") or call.get("file") or call.get("filename")
             or call.get("filepath") or "")
        if not p:
            raise KeyError("missing path in tool call")
        return sanitize_model_path(str(p).strip(), self.workspace)

    def populate_tree(self, root_path):
        root_path = norm_workspace(root_path)
        self.workspace = root_path
        label = os.path.basename(root_path) or root_path
        self.explorer_label.configure(text=label.upper())
        self.tree.delete(*self.tree.get_children())
        self._fill_node("", root_path)

    def _fill_node(self, node, path):
        path = self._canon_path(path)
        for child in self.tree.get_children(node):
            self.tree.delete(child)
        try:
            entries = sorted(
                os.listdir(path),
                key=lambda n: (not os.path.isdir(os.path.join(path, n)),
                               n.lower()))
        except OSError:
            return
        for name in entries:
            if name in SKIP_TREE:
                continue
            full = self._canon_path(os.path.join(path, name))
            if os.path.isdir(full):
                n = self.tree.insert(node, "end", text=" 📁 " + name,
                                     values=(full,))
                self.tree.insert(n, "end", text="…", values=("",))
            else:
                icon = "🐍" if name.endswith(".py") else "📄"
                self.tree.insert(node, "end", text=f" {icon} {name}",
                                 values=(full,))

    def _tree_open(self, _e):
        node = self.tree.focus()
        vals = self.tree.item(node, "values")
        if not (vals and vals[0] and os.path.isdir(vals[0])):
            return
        children = self.tree.get_children(node)
        if children and self.tree.item(children[0], "text") != "…":
            return
        self._fill_node(node, vals[0])

    def _find_tree_child(self, node, path):
        for child in self.tree.get_children(node):
            vals = self.tree.item(child, "values")
            if vals and vals[0] and paths_equal(vals[0], path):
                return child
        return None

    def _sync_tree_file(self, path):
        """Add or refresh one file in the explorer without rebuilding the tree."""
        if not path or not self.workspace:
            return
        path = self._canon_path(path)
        try:
            rel = os.path.relpath(path, self._canon_path(self.workspace))
        except ValueError:
            return
        if rel.startswith(".."):
            return
        parts = rel.split(os.sep)
        node = ""
        cur = self._canon_path(self.workspace)
        for part in parts[:-1]:
            cur = self._canon_path(os.path.join(cur, part))
            found = self._find_tree_child(node, cur)
            if found is None:
                found = self.tree.insert(
                    node, "end", text=" 📁 " + part, values=(cur,), open=True)
                self.tree.insert(found, "end", text="…", values=("",))
            else:
                kids = self.tree.get_children(found)
                if not kids or self.tree.item(kids[0], "text") == "…":
                    if not kids:
                        self.tree.insert(found, "end", text="…", values=("",))
                self.tree.item(found, open=True)
            node = found
        if os.path.isfile(path):
            name = os.path.basename(path)
            icon = "🐍" if name.endswith(".py") else "📄"
            if self._find_tree_child(node, path):
                return
            self.tree.insert(node, "end", text=f" {icon} {name}",
                             values=(path,))

    def _tree_activate(self, _e):
        node = self.tree.focus()
        vals = self.tree.item(node, "values")
        if vals and vals[0] and os.path.isfile(vals[0]):
            self.open_path(vals[0])

    # =========================================================================
    # Search
    # =========================================================================
    def run_search(self):
        needle = self.search_entry.get().strip()
        if not needle:
            return
        self.search_results.delete(0, "end")
        self._search_hits = []
        self.search_results.insert("end", "searching…")
        threading.Thread(target=self._search_worker, args=(needle,),
                         daemon=True).start()

    def _search_worker(self, needle):
        hits = []
        for dirpath, dirnames, filenames in os.walk(self.workspace):
            dirnames[:] = [d for d in dirnames if d not in SKIP_TREE]
            for fn in filenames:
                full = os.path.join(dirpath, fn)
                try:
                    if os.path.getsize(full) > 300_000:
                        continue
                    with open(full, "r", encoding="utf-8",
                              errors="ignore") as f:
                        for i, line in enumerate(f, 1):
                            if needle.lower() in line.lower():
                                hits.append((full, i, line.strip()[:90]))
                                if len(hits) >= 400:
                                    raise StopIteration
                except (OSError, StopIteration):
                    if hits and len(hits) >= 400:
                        break
        self.ui_queue.put(("search_done", hits))

    def _search_open(self, _e):
        sel = self.search_results.curselection()
        if not sel or sel[0] >= len(self._search_hits):
            return
        path, line, _ = self._search_hits[sel[0]]
        self.open_path(path)
        ed = self.tabs[self.active_key]["editor"]
        ed.goto(line)

    # =========================================================================
    # Tabs / editors
    # =========================================================================
    def _open_welcome(self):
        key = "__welcome__"
        ed = self._add_tab(key, "Welcome")
        ed.set(
            f"# {APP_NAME} {APP_VERSION} — AI Agents OS  🐱💙\n"
            "# A Cursor-3-style vibe coding IDE, powered by LM Studio.\n"
            "#\n"
            f"#   {MOD_LABEL}I   focus AI agent      {MOD_LABEL}K   inline AI edit\n"
            f"#   {MOD_LABEL}R   run file in terminal {MOD_LABEL}⇧P  command palette\n"
            f"#   {MOD_LABEL}B   toggle sidebar       {MOD_LABEL}J   toggle panel\n"
            "#   Tab  accept ghost completion (Cursor Tab)  Esc dismiss\n"
            "#\n"
            "# Agents can read/write/edit/delete files, grep, and run terminal\n"
            "# commands — every change is checkpointed: Keep All / Undo All /\n"
            "# Review Diff. Run parallel agents with ＋ Agent. Mention files\n"
            "# in chat with @path. Rules load from .cursorrules / AGENTS.md.\n"
            "# Start LM Studio's local server and load a model to begin.\n\n"
            "def vibe():\n"
            '    print("hello from CatIDE — let\'s ship")\n\n'
            "vibe()\n")
        ed.text.edit_modified(False)

    def _add_tab(self, key, title):
        if key in self.tabs:
            self._activate_tab(key)
            return self.tabs[key]["editor"]
        ed = Editor(self.editor_holder, self,
                    path=key if os.path.sep in key else None)
        tabf = tk.Frame(self.tabbar, bg=TAB_BG)
        tabf.pack(side="left")
        lab = tk.Label(tabf, text=title, bg=TAB_BG, fg=FG_DIM,
                       font=ui_font(11), padx=12, pady=7, cursor="hand2")
        lab.pack(side="left")
        x = tk.Label(tabf, text="✕", bg=TAB_BG, fg=FG_FAINT,
                     font=ui_font(10), padx=6, cursor="hand2")
        x.pack(side="left")
        lab.bind("<Button-1>", lambda e, k=key: self._activate_tab(k))
        x.bind("<Button-1>", lambda e, k=key: self._close_tab(k))
        self.tabs[key] = {"editor": ed, "tabframe": tabf, "label": lab,
                          "title": title}
        self._activate_tab(key)
        return ed

    def _activate_tab(self, key):
        for k, t in self.tabs.items():
            t["editor"].pack_forget()
            t["tabframe"].configure(bg=TAB_BG)
            t["label"].configure(bg=TAB_BG, fg=FG_DIM)
        t = self.tabs[key]
        t["editor"].pack(fill="both", expand=True)
        t["tabframe"].configure(bg=TAB_ACTIVE)
        t["label"].configure(bg=TAB_ACTIVE, fg=FG_BRIGHT)
        self.active_key = key
        path = key if os.path.sep in key else None
        self._update_ctx_chip()
        t["editor"].text.focus_set()

    def _close_tab(self, key):
        t = self.tabs.pop(key, None)
        if not t:
            return
        t["editor"].destroy()
        t["tabframe"].destroy()
        if self.active_key == key:
            self.active_key = None
            if self.tabs:
                self._activate_tab(next(reversed(self.tabs)))

    def close_active_tab(self):
        if self.active_key:
            self._close_tab(self.active_key)

    def mark_dirty(self, editor):
        for k, t in self.tabs.items():
            if t["editor"] is editor and not t["label"].cget("text"
                                                             ).startswith("●"):
                t["label"].configure(text="● " + t["title"])

    def unmark_dirty(self, editor):
        for k, t in self.tabs.items():
            if t["editor"] is editor:
                t["label"].configure(text=t["title"])

    def _active_editor(self):
        if self.active_key and self.active_key in self.tabs:
            return self.tabs[self.active_key]["editor"]
        return None

    # file operations ------------------------------------------------------------
    def new_file(self):
        n = 1
        while f"__untitled{n}__" in self.tabs:
            n += 1
        self._add_tab(f"__untitled{n}__", f"Untitled-{n}")

    def open_file_dialog(self):
        path = filedialog.askopenfilename(initialdir=self.workspace)
        if path:
            self.open_path(path)

    def open_folder_dialog(self):
        path = filedialog.askdirectory(initialdir=self.workspace)
        if path:
            path = norm_workspace(path)
            self.populate_tree(path)
            self.rules_text = self._load_rules()
            threading.Thread(target=self._detect_git, daemon=True).start()
            self._reload_agent_sessions()
            self._cd_terminals()
            self.log_output(f"workspace: {path}\n")
            self._update_ctx_chip()
            self._save_settings()

    def open_path(self, path):
        path = self._canon_path(path)
        if path in self.tabs:
            self._activate_tab(path)
            return
        try:
            with open(path, "r", encoding="utf-8", errors="replace", newline="") as f:
                content = f.read()
        except OSError as e:
            messagebox.showerror(APP_NAME, f"Couldn't open file:\n{e}")
            return
        ed = self._add_tab(path, os.path.basename(path))
        ed.path = path
        ed.set(content)

    def save_file(self):
        ed = self._active_editor()
        if ed is None:
            return
        if not ed.path:
            return self.save_file_as()
        path = self._canon_path(ed.path)
        try:
            self._write_file_exact(path, ed.get())
        except OSError as e:
            messagebox.showerror(APP_NAME, f"Couldn't save:\n{e}")
            return
        ed.path = path
        ed.text.edit_modified(False)
        t = self.tabs[self.active_key]
        t["label"].configure(text=t["title"])
        self.set_status(f"saved {os.path.basename(path)}")
        self.check_problems(path)
        self._sync_tree_file(path)

    def save_file_as(self):
        ed = self._active_editor()
        if ed is None:
            return
        path = filedialog.asksaveasfilename(
            initialdir=self.workspace, defaultextension=".py")
        if not path:
            return
        path = self._canon_path(path)
        content = ed.get()
        try:
            self._write_file_exact(path, content)
        except OSError as e:
            messagebox.showerror(APP_NAME, f"Couldn't save:\n{e}")
            return
        self._close_tab(self.active_key)
        self.open_path(path)
        self._sync_tree_file(path)

    # run / problems --------------------------------------------------------------
    def run_file(self):
        ed = self._active_editor()
        if ed is None:
            return
        if not ed.path:
            self.save_file()
            ed = self._active_editor()
            if ed is None or not ed.path:
                return
        else:
            self.save_file()
        cmd = run_file_command(ed.path)
        if self.active_term:
            self.show_panel_tab("TERMINAL")
            self.active_term.send(cmd)
        else:
            threading.Thread(target=self._run_fallback, args=(cmd,),
                             daemon=True).start()

    def _run_fallback(self, cmd):
        try:
            p = subprocess.run(
                shell_command(cmd), shell=True, capture_output=True,
                text=True, timeout=60, cwd=self.workspace)
            out = p.stdout + p.stderr + f"\n[exit {p.returncode}]\n"
        except subprocess.TimeoutExpired:
            out = "[timed out]\n"
        self.ui_queue.put(("output", out))

    def check_problems(self, path):
        if not path.endswith(".py"):
            return
        threading.Thread(target=self._problems_worker, args=(path,),
                         daemon=True).start()

    def _problems_worker(self, path):
        p = subprocess.run([sys.executable, "-m", "py_compile", path],
                           capture_output=True, text=True)
        errs = [l for l in p.stderr.splitlines() if l.strip()]
        self.ui_queue.put(("problems", (path, errs)))

    # =========================================================================
    # AI chat + agent loop
    # =========================================================================
    def _detect_models(self):
        try:
            self.models = self.lm.list_models()
        except Exception:
            self.models = []
        self.ui_queue.put(("models", self.models))

    def _retry_lm_studio(self):
        if not self.models:
            threading.Thread(target=self._detect_models, daemon=True).start()
        self.after(30000, self._retry_lm_studio)

    # -- Cursor-style agent autodetection ------------------------------------
    def _update_ctx_chip(self):
        ctx = self._editor_context()
        model = self.model_var.get()
        parts = []
        if ctx:
            parts.append(f"@{ctx['rel']}")
            parts.append(ctx["lang"])
            parts.append(f"L{ctx['line']}")
            if ctx.get("selection"):
                parts.append("sel")
        else:
            parts.append("@ auto")
        if self.git_branch:
            parts.append(f"⎇{self.git_branch}")
        if model and model != "connecting…":
            parts.append(model[:18])
        self.ctx_chip.configure(text=" · ".join(parts))

    def _editor_context(self):
        ed = self._active_editor()
        if ed is None:
            return None
        path = ed.path if ed.path and os.path.sep in str(ed.path) else None
        rel = "untitled"
        if path:
            try:
                rel = os.path.relpath(
                    self._canon_path(path),
                    self._canon_path(self.workspace))
            except ValueError:
                rel = os.path.basename(path)
        idx = ed.text.index("insert")
        line, col = idx.split(".")
        selection = None
        try:
            if ed.text.tag_ranges("sel"):
                selection = ed.text.get("sel.first", "sel.last")
        except tk.TclError:
            pass
        return {
            "rel": rel, "path": path,
            "lang": detect_language(path or ""),
            "line": int(line), "col": int(col) + 1,
            "selection": selection,
            "content": ed.get(),
        }

    def _snapshot_workspace(self, max_entries=40):
        lines = []
        try:
            for name in sorted(os.listdir(self.workspace))[:max_entries]:
                if name in SKIP_TREE:
                    continue
                full = os.path.join(self.workspace, name)
                if os.path.isdir(full):
                    lines.append(f"  {name}/")
                else:
                    lines.append(f"  {name}")
        except OSError:
            return "(unreadable)"
        return "\n".join(lines) or "(empty)"

    def _autodetect_prompt_files(self, prompt):
        """Find workspace files referenced in the user's message."""
        hits = []
        seen = set()
        for ref in FILE_REF_RE.findall(prompt):
            try:
                full = self._safe_path(ref)
                if os.path.isfile(full):
                    rel = os.path.relpath(full, self._canon_path(self.workspace))
                    if rel not in seen:
                        seen.add(rel)
                        hits.append(rel)
            except ValueError:
                pass
        prompt_lower = prompt.lower()
        try:
            for dirpath, dirnames, filenames in os.walk(self.workspace):
                dirnames[:] = [d for d in dirnames if d not in SKIP_TREE]
                if dirpath.replace(self.workspace, "").count(os.sep) > 3:
                    dirnames.clear()
                    continue
                for fn in filenames:
                    if len(hits) >= 8:
                        return hits
                    if fn.lower() in prompt_lower and fn not in seen:
                        try:
                            rel = os.path.relpath(
                                os.path.join(dirpath, fn),
                                self._canon_path(self.workspace))
                            seen.add(rel)
                            hits.append(rel)
                        except ValueError:
                            pass
        except OSError:
            pass
        return hits

    def _full_env_context(self):
        ws = self._canon_path(self.workspace)
        parts = [
            env_context(),
            f"workspace: {ws}",
            f"workspace name: {os.path.basename(ws) or ws}",
        ]
        if self.git_branch:
            parts.append(f"git branch: {self.git_branch}")
        model = self.model_var.get()
        if model and model != "connecting…":
            parts.append(f"LM Studio model: {model}")
        open_tabs = [os.path.basename(k) for k in self.tabs
                     if os.path.sep in str(k)]
        if open_tabs:
            parts.append(f"open tabs: {', '.join(open_tabs)}")
        return "\n".join(parts)

    def _build_agent_system(self, mode):
        system = MODE_PROMPTS[mode]
        system += f"\n\n[Autodetected environment]\n{self._full_env_context()}"
        if self.rules_text:
            system += f"\n\n[Autodetected workspace rules]\n{self.rules_text}"
        return system

    def _attach_file_content(self, rel, user_msg):
        try:
            full = self._safe_path(rel)
        except ValueError:
            return user_msg
        if not os.path.isfile(full):
            return user_msg
        try:
            body = read_file_exact(full)[:12000]
        except OSError:
            return user_msg
        return (user_msg + f"\n\n[file: {rel}]\n```\n{body}\n```")

    def _build_agent_user_msg(self, prompt, mode):
        """Assemble user message with all autodetected context (Cursor-style)."""
        mention_targets = []
        parts = [f"[workspace: {self._canon_path(self.workspace)}]"]
        parts.append(f"[project tree]\n{self._snapshot_workspace()}")
        if self.git_branch:
            parts.append(f"[git: {self.git_branch}]")

        ctx = self._editor_context()
        active_file = None
        auto_attach = mode == "Agent" or self.include_code.get()

        if ctx:
            active_file = ctx["rel"] if ctx["rel"] != "untitled" else None
            parts.append(
                f"[active file: {ctx['rel']} · {ctx['lang']} · "
                f"line {ctx['line']}, col {ctx['col']}]")
            if ctx.get("selection"):
                parts.append(f"[selection]\n```\n{ctx['selection'][:6000]}\n```")
            if auto_attach and ctx["content"].strip():
                if active_file:
                    mention_targets.append(active_file)
                parts.append(f"[active file content]\n```\n{ctx['content']}\n```")

        open_tabs = [os.path.basename(k) for k in self.tabs
                     if os.path.sep in str(k)]
        if open_tabs:
            parts.append(f"[open tabs: {', '.join(open_tabs)}]")

        user_msg = "\n\n".join(parts)

        for name in MENTION_RE.findall(prompt)[:8]:
            clean = name.replace("\\", os.sep)
            if clean.lower().startswith("file:"):
                clean = normalize_path(clean)
            try:
                rel = os.path.relpath(
                    self._safe_path(clean),
                    self._canon_path(self.workspace))
            except ValueError:
                rel = clean
            if rel not in mention_targets:
                mention_targets.append(rel)
            user_msg = self._attach_file_content(rel, user_msg)
            try:
                if os.path.isdir(self._safe_path(clean)):
                    user_msg += f"\n\n[mentioned folder: {name}]"
            except ValueError:
                pass

        for rel in self._autodetect_prompt_files(prompt):
            if rel not in mention_targets:
                mention_targets.append(rel)
                user_msg = self._attach_file_content(rel, user_msg)

        if mode == "Agent" and active_file and active_file not in mention_targets:
            mention_targets.append(active_file)

        user_msg += f"\n\n[request]\n{prompt}"
        return user_msg, active_file, list(dict.fromkeys(mention_targets))

    def send_chat(self):
        sess = self.active_session
        if sess is None:
            return
        if sess.streaming:
            sess.stop_flag.set()
            return
        prompt = self.ai_input.get("1.0", "end-1c").strip()
        if not prompt:
            return
        self.ai_input.delete("1.0", "end")
        mode = self.mode.get()
        system = self._build_agent_system(mode)
        if not sess.history:
            sess.history = [{"role": "system", "content": system}]
        else:
            sess.history[0] = {"role": "system", "content": system}

        user_msg, active_file, mention_targets = self._build_agent_user_msg(
            prompt, mode)
        sess.history.append({"role": "user", "content": user_msg})

        self._chat_write("\nyou ▸ ", "you", sess)
        self._chat_write(prompt + "\n", None, sess)
        sess.streaming = True
        sess.stop_flag.clear()
        self._update_send_btn()
        self._session_spinner()
        self._update_ctx_chip()
        self.set_status(f"{sess.name}: {mode} · autodetect on")
        sess.save()

        threading.Thread(target=self._agent_worker,
                         args=(sess, mode, active_file, mention_targets),
                         daemon=True).start()

    def _agent_worker(self, sess, mode, active_file=None, mention_targets=None):
        model = self.model_var.get()
        sid = sess.id
        targets = set(mention_targets or [])
        try:
            for _step in range(MAX_AGENT_STEPS):
                self.ui_queue.put(("chat_head", sid))
                reply = self.lm.stream_chat(
                    sess.history, model,
                    lambda t: self.ui_queue.put(("token", (sid, t))),
                    sess.stop_flag)
                if reply or not sess.stop_flag.is_set():
                    sess.history.append(
                        {"role": "assistant", "content": reply})
                self.ui_queue.put(("reply_done", sid))
                if mode != "Agent" or sess.stop_flag.is_set():
                    break
                call, perr = parse_tool_call(reply)
                if not call:
                    # fallback: only save when path is explicit or @mentioned
                    saved = self._try_save_code_blocks(
                        reply, sess, active_file, targets)
                    if saved:
                        result = f"OK, auto-saved {saved}"
                        self.ui_queue.put(
                            ("chat_note", (sid, f"\n💾 saved {saved} to disk\n")))
                        sess.history.append(
                            {"role": "user",
                             "content": f"[TOOL RESULT]\n{result}"})
                        sess.save()
                        continue
                    if perr:
                        self._agent_log(f"[{sess.name}] ⚠ {perr}\n", "err", sess)
                        self.ui_queue.put(("chat_note", (sid, f"\n⚠ {perr}\n")))
                    break
                try:
                    result = self._exec_tool(call, sess)
                except Exception as e:  # noqa: BLE001
                    result = f"ERROR: {e}"
                sess.history.append(
                    {"role": "user",
                     "content": f"[TOOL RESULT]\n{result[:8000]}"})
                sess.save()
            self.ui_queue.put(("done", sid))
        except urllib.error.URLError as e:
            self.ui_queue.put(("error", (sid,
                f"Can't reach LM Studio at {LM_STUDIO_BASE}. Start the local "
                f"server (Developer tab) and load a model.\n{e}")))
        except Exception as e:  # noqa: BLE001
            self.ui_queue.put(("error", (sid, str(e))))

    # tools -------------------------------------------------------------------------
    def _active_editor_path(self):
        ed = self._active_editor()
        if ed and ed.path:
            try:
                return os.path.relpath(
                    self._canon_path(ed.path),
                    self._canon_path(self.workspace))
            except ValueError:
                return os.path.basename(ed.path)
        return None

    def _extract_saveable_block(self, reply, active_file=None,
                                targets=None, explicit_only=False):
        """Return (path, code). explicit_only=True avoids blind active-file writes."""
        targets = set(targets or [])
        blocks = re.findall(r"```([^\n]*)\n(.*?)```", reply, re.S)
        for lang_hint, body in reversed(blocks):
            hint = lang_hint.strip()
            if hint.lower() in ("tool", "json", "write"):
                continue
            code = preserve_file_content(body)
            path = None
            explicit = False
            m = re.match(r"^\d+:\d+:(.+)$", hint)
            if m:
                path = m.group(1).strip()
                explicit = True
            if not path:
                for p in hint.split():
                    if "." in p:
                        path = p.replace("\\", os.sep)
                        explicit = True
                        break
            if not path:
                gp = self._guess_path_from_body(code, None)
                if gp:
                    path = gp
                    explicit = True
            if not path and not explicit_only:
                path = active_file
            if not path:
                continue
            path = path.replace("\\", os.sep)
            if path.lower().startswith("file:"):
                try:
                    path = os.path.relpath(
                        self._safe_path(path),
                        self._canon_path(self.workspace))
                except ValueError:
                    continue
            if explicit_only and not explicit:
                norm_targets = {t.replace("\\", os.sep) for t in targets}
                if path not in norm_targets:
                    continue
            return path, code
        return None, None

    def _try_save_code_blocks(self, reply, sess, active_file=None,
                              targets=None):
        """Fallback: save code fences only when path is explicit or @mentioned."""
        path, code = self._extract_saveable_block(
            reply, active_file, targets, explicit_only=True)
        if not path or not code:
            return None
        try:
            r = self._exec_tool(
                {"tool": "write_file", "path": path, "content": code}, sess)
            if r.startswith("OK"):
                return path
        except (OSError, KeyError, ValueError):
            pass
        return None

    def _guess_path_from_body(self, body, active_file=None):
        """Guess filename from first-line comment like '# file: x.py'."""
        first = body.split("\n", 1)[0].strip()
        for pat in (r"^#\s*file:\s*(\S+)", r"^//\s*file:\s*(\S+)",
                    r"^#\s*(\S+\.\w+)\s*$"):
            m = re.match(pat, first, re.I)
            if m:
                return m.group(1)
        return active_file

    def _checkpoint(self, sess, path):
        """Remember a file's pre-change content once per session run."""
        if path in sess.checkpoints:
            return
        if os.path.isfile(path):
            try:
                with open(path, "r", encoding="utf-8", errors="replace") as f:
                    sess.checkpoints[path] = f.read()
            except OSError:
                sess.checkpoints[path] = None
        else:
            sess.checkpoints[path] = None
        self.ui_queue.put(("review", sess.id))
        sess.save()

    def _exec_tool(self, call, sess):
        tool = call.get("tool", "?")

        def alog(text, tag="dim"):
            self._agent_log(text, tag, sess)

        try:
            if tool == "list_dir":
                path = self._safe_path(call.get("path", "."))
                rel = os.path.relpath(path, self._canon_path(self.workspace))
                if not os.path.isdir(path):
                    alog(f"[{sess.name}] $ ls {rel} — not found\n", "err")
                    return (f"ERROR: directory not found: {rel} — "
                            "write_file creates parent dirs automatically")
                names = sorted(os.listdir(path))
                alog(f"[{sess.name}] $ ls {rel}", "cmd")
                out = "\n".join(
                    n + ("/" if os.path.isdir(os.path.join(path, n)) else "")
                    for n in names) or "(empty)"
                alog(out + "\n", "dim")
                return out
            if tool == "read_file":
                path = self._safe_path(self._tool_path(call))
                rel = os.path.relpath(path, self._canon_path(self.workspace))
                if not os.path.isfile(path):
                    alog(f"[{sess.name}] $ read {rel} — not found\n", "err")
                    return (f"ERROR: file not found: {rel} — "
                            "use write_file to create it (dirs created auto)")
                with open(path, "r", encoding="utf-8", errors="replace",
                          newline="") as f:
                    content = f.read()
                alog(f"[{sess.name}] $ read {rel} "
                     f"({len(content)} chars)\n", "cmd")
                return content[:20000]
            if tool == "write_file":
                path = self._safe_path(self._tool_path(call))
                if os.path.isdir(path):
                    return ("ERROR: path is a directory — use a file path "
                            "like 'src/main.py'")
                if "content" not in call:
                    return ("ERROR: write_file missing content — use Format B: "
                            "```tool {\"tool\":\"write_file\",\"path\":\"...\"}``` "
                            "then ```write\\n<file content>```")
                content = preserve_file_content(call["content"])
                path = self._ensure_parent_dirs(path)
                self._checkpoint(sess, path)
                self._write_file_exact(path, content)
                path = self._canon_path(path)
                rel = os.path.relpath(path, self._canon_path(self.workspace))
                alog(f"[{sess.name}] $ write {rel} ({len(content)} chars)", "cmd")
                alog(f"  ✓ saved → {path}\n", "ok")
                self.ui_queue.put(("refresh_file", path))
                self.ui_queue.put(("open_file", path))
                self._sync_tree_file(path)
                sess.save()
                return f"OK, wrote {rel} ({len(content)} chars) — exact bytes on disk"
            if tool == "edit_file":
                path = self._safe_path(self._tool_path(call))
                rel = os.path.relpath(path, self._canon_path(self.workspace))
                if not os.path.isfile(path):
                    alog(f"[{sess.name}] $ edit {rel} — not found\n", "err")
                    return (f"ERROR: file not found: {rel} — "
                            "use write_file to create it first")
                with open(path, "r", encoding="utf-8", errors="replace",
                          newline="") as f:
                    content = f.read()
                old = call.get("old", "")
                new = call.get("new", "")
                n = content.count(old) if old else 0
                if n == 0:
                    alog(f"[{sess.name}] $ edit {rel} "
                         "— old text not found\n", "err")
                    return "ERROR: 'old' text not found in file"
                if n > 1:
                    alog(f"[{sess.name}] $ edit {rel} "
                         f"— old text matches {n}×\n", "err")
                    return (f"ERROR: 'old' text matches {n} times; "
                            "provide more context")
                self._checkpoint(sess, path)
                new_content = preserve_file_content(
                    content.replace(old, new, 1))
                self._write_file_exact(path, new_content)
                alog(f"[{sess.name}] $ edit {rel}", "cmd")
                alog("  ✓ edited\n", "ok")
                self.ui_queue.put(("refresh_file", path))
                sess.save()
                return f"OK, edited {rel}"
            if tool == "delete_file":
                path = self._safe_path(self._tool_path(call))
                rel = os.path.relpath(path, self._canon_path(self.workspace))
                if not os.path.isfile(path):
                    alog(f"[{sess.name}] $ rm {rel} — not found\n", "err")
                    return f"ERROR: file not found: {rel}"
                self._checkpoint(sess, path)
                os.remove(path)
                alog(f"[{sess.name}] $ rm {rel}", "cmd")
                alog("  ✓ deleted\n", "ok")
                self.ui_queue.put(("refresh_file", path))
                sess.save()
                return f"OK, deleted {rel}"
            if tool == "grep_search":
                pattern = call.get("pattern", "")
                rx = re.compile(pattern)
                base = self._safe_path(call.get("path", "."))
                rel = os.path.relpath(base, self._canon_path(self.workspace))
                alog(f"[{sess.name}] $ grep {pattern!r} in {rel}", "cmd")
                hits = []
                files = []
                if os.path.isfile(base):
                    files = [base]
                elif os.path.isdir(base):
                    for dirpath, dirnames, filenames in os.walk(base):
                        dirnames[:] = [d for d in dirnames
                                       if d not in SKIP_TREE]
                        for fn in filenames:
                            files.append(os.path.join(dirpath, fn))
                else:
                    alog(f"  path not found: {rel}\n", "err")
                    return (f"ERROR: path not found: {rel} — "
                            "use write_file to create files first")
                for full in files:
                    try:
                        if os.path.getsize(full) > 300_000:
                            continue
                        with open(full, "r", encoding="utf-8",
                                  errors="ignore") as f:
                            for i, line in enumerate(f, 1):
                                if rx.search(line):
                                    r = os.path.relpath(full, self.workspace)
                                    hits.append(
                                        f"{r}:{i}: {line.strip()[:120]}")
                                    if len(hits) >= 60:
                                        break
                    except OSError:
                        continue
                    if len(hits) >= 60:
                        break
                out = "\n".join(hits) or "(no matches)"
                alog(f"{len(hits)} matches\n", "dim")
                return out
            if tool == "run_terminal":
                cmd = call.get("command", "").strip()
                if not cmd:
                    return "ERROR: empty command"
                alog(f"[{sess.name}] $ {cmd}", "cmd")
                # Run in workspace via shell with proper cwd (not the UI pty)
                p = subprocess.run(
                    shell_command(cmd), shell=True, capture_output=True,
                    text=True, timeout=90, cwd=self._canon_path(self.workspace))
                out = (p.stdout + p.stderr).strip() or "(no output)"
                alog(out + f"\n[exit {p.returncode}]\n",
                     "dim" if p.returncode == 0 else "err")
                return f"exit {p.returncode}\n{out}"
            return f"ERROR: unknown tool '{tool}'"
        except subprocess.TimeoutExpired:
            alog("[timed out after 90s]\n", "err")
            return "ERROR: command timed out"
        except re.error as e:
            return f"ERROR: bad regex ({e})"
        except (OSError, KeyError, ValueError) as e:
            msg = str(e)
            if isinstance(e, FileNotFoundError) or "No such file" in msg:
                msg = (f"file or directory not found — use write_file to "
                       f"create files (parent dirs created automatically)")
            alog(f"  ✗ {msg}\n", "err")
            return f"ERROR: {msg}"

    def _agent_log(self, text, tag="dim", sess=None):
        line = text + ("" if text.endswith("\n") else "\n")
        self.ui_queue.put(("agent_term", (line, tag)))
        paths = [os.path.join(LOG_DIR, "agent.log")]
        if sess:
            paths.insert(0, sess._log_file())
        for path in paths:
            try:
                with open(path, "a", encoding="utf-8") as f:
                    f.write(line)
            except OSError:
                pass

    # chat helpers -----------------------------------------------------------------
    def clear_chat(self):
        sess = self.active_session
        if sess is None:
            return
        sess.stop_flag.set()
        sess.history = []
        sess.checkpoints = {}
        sess.transcript = ""
        sess.last_reply = ""
        sess.log.configure(state="normal")
        sess.log.delete("1.0", "end")
        sess.log.configure(state="disabled")
        sess.save()
        self._update_review_bar()
        self.set_status("new chat")

    def apply_code(self):
        """Accept last AI code block — write to disk (Cursor-style)."""
        sess = self.active_session
        reply = sess.last_reply if sess else ""
        path, code = self._extract_saveable_block(
            reply, self._active_editor_path(), explicit_only=False)
        if not code:
            self.set_status("no code block in last reply")
            return
        if not path:
            self.set_status("no file path — open a file or name it in the block")
            return
        if sess:
            result = self._exec_tool(
                {"tool": "write_file", "path": path, "content": code}, sess)
        else:
            try:
                full = self._safe_path(path)
                self._write_file_exact(full, code)
                self._sync_tree_file(full)
                if full in self.tabs:
                    self._sync_editor_from_disk(full)
                else:
                    self.open_path(full)
                result = f"OK, wrote {path}"
            except (OSError, ValueError, KeyError) as e:
                result = f"ERROR: {e}"
        if result.startswith("OK"):
            self.set_status(f"saved {path} ✓")
        else:
            self.set_status(result[:120])

    def _chat_write(self, text, tag=None, sess=None):
        sess = sess or self.active_session
        if sess is None:
            return
        sess.transcript += text
        sess.log.configure(state="normal")
        sess.log.insert("end", text, tag)
        sess.log.see("end")
        sess.log.configure(state="disabled")

    # =========================================================================
    # Checkpoint review (Keep All / Undo All / diff)
    # =========================================================================
    def _update_review_bar(self):
        sess = self.active_session
        n = len(sess.checkpoints) if sess else 0
        if n:
            self.review_label.configure(
                text=f"✦ {n} file{'s' if n != 1 else ''} changed")
            self.review_bar.pack(fill="x", padx=10, pady=(0, 4),
                                 before=self.ai_foot)
        else:
            self.review_bar.pack_forget()

    def keep_all_changes(self):
        sess = self.active_session
        if sess:
            sess.checkpoints.clear()
            sess.save()
        self._update_review_bar()
        self.set_status("changes kept ✓")

    def undo_all_changes(self):
        sess = self.active_session
        if not sess:
            return
        for path, original in sess.checkpoints.items():
            try:
                if original is None:
                    if os.path.isfile(path):
                        os.remove(path)
                else:
                    with open(path, "w", encoding="utf-8") as f:
                        f.write(original)
                self.ui_queue.put(("refresh_file", path))
            except OSError:
                pass
        sess.checkpoints.clear()
        sess.save()
        self._update_review_bar()
        self.set_status("changes reverted ↩")

    def review_changes(self):
        sess = self.active_session
        if not sess or not sess.checkpoints:
            return
        top = tk.Toplevel(self)
        top.title("Review Changes")
        top.configure(bg=BG)
        top.geometry("820x560")
        tk.Label(top, text="✦ Agent changes — review diff", bg=BG,
                 fg=FG_BRIGHT, font=ui_font(13, "bold"), anchor="w",
                 padx=12, pady=8).pack(fill="x")
        txt = tk.Text(top, bg=EDITOR_BG, fg=FG, bd=0, padx=12, pady=8,
                      font=mono_font(11), wrap="none", highlightthickness=0)
        txt.pack(fill="both", expand=True, padx=10)
        txt.tag_configure("add", foreground=OK_GREEN)
        txt.tag_configure("del", foreground=ERR_RED)
        txt.tag_configure("hdr", foreground=ACCENT,
                          font=mono_font(11))
        for path, original in sess.checkpoints.items():
            rel = os.path.relpath(path, self.workspace)
            try:
                with open(path, "r", encoding="utf-8", errors="replace") as f:
                    current = f.read()
            except OSError:
                current = ""
            old_lines = (original or "").splitlines(keepends=True)
            new_lines = current.splitlines(keepends=True)
            label = "created" if original is None else "modified"
            if not os.path.isfile(path):
                label = "deleted"
            txt.insert("end", f"\n═══ {rel}  ({label}) ═══\n", "hdr")
            for line in difflib.unified_diff(old_lines, new_lines,
                                             lineterm=""):
                if line.startswith("+") and not line.startswith("+++"):
                    txt.insert("end", line.rstrip("\n") + "\n", "add")
                elif line.startswith("-") and not line.startswith("---"):
                    txt.insert("end", line.rstrip("\n") + "\n", "del")
                elif line.startswith("@@"):
                    txt.insert("end", line.rstrip("\n") + "\n", "hdr")
                else:
                    txt.insert("end", line.rstrip("\n") + "\n")
        txt.configure(state="disabled")
        btns = tk.Frame(top, bg=BG)
        btns.pack(fill="x", padx=10, pady=8)
        self._btn(btns, "Keep All ✓",
                  lambda: (self.keep_all_changes(), top.destroy())
                  ).pack(side="right", padx=4)
        self._btn(btns, "Undo All ↩",
                  lambda: (self.undo_all_changes(), top.destroy())
                  ).pack(side="right", padx=4)

    # =========================================================================
    # Cursor Tab completion backend
    # =========================================================================
    def request_completion(self, editor, gen, prefix, suffix):
        if (not self.tab_enabled.get() or not self.models
                or self.completion_busy):
            return
        self.completion_busy = True
        threading.Thread(target=self._completion_worker,
                         args=(editor, gen, prefix, suffix),
                         daemon=True).start()

    def _completion_worker(self, editor, gen, prefix, suffix):
        msgs = [
            {"role": "system", "content":
                "You are a code autocomplete engine inside an IDE. Continue "
                "the code exactly at <CURSOR>. Reply with ONLY the raw text "
                "to insert — no markdown fences, no commentary, no repeating "
                "existing code. Maximum 3 lines."},
            {"role": "user", "content": prefix + "<CURSOR>" + suffix},
        ]
        try:
            reply = self.lm.stream_chat(
                msgs, self.model_var.get(), lambda t: None,
                threading.Event(), temperature=0.2, max_tokens=80)
        except Exception:  # noqa: BLE001 -- completions fail silently
            reply = ""
        finally:
            self.completion_busy = False
        reply = re.sub(r"^```[\w]*\n?|\n?```$", "", reply.strip("\n"))
        reply = reply.rstrip()
        if reply:
            self.ui_queue.put(("ghost", (editor, gen, reply)))

    # =========================================================================
    # Cmd+K inline edit
    # =========================================================================
    def inline_edit(self):
        ed = self._active_editor()
        if ed is None:
            return
        top = tk.Toplevel(self)
        top.overrideredirect(True)
        top.configure(bg=ACCENT)
        x = ed.winfo_rootx() + 60
        y = ed.winfo_rooty() + 16
        top.geometry(f"560x44+{x}+{y}")
        inner = tk.Frame(top, bg=INPUT_BG)
        inner.pack(fill="both", expand=True, padx=1, pady=1)
        tk.Label(inner, text="✦", bg=INPUT_BG, fg=ACCENT,
                 font=ui_font(13)).pack(side="left", padx=(10, 4))
        ent = tk.Entry(inner, bg=INPUT_BG, fg=FG_BRIGHT, bd=0,
                       insertbackground=FG_BRIGHT, font=ui_font(12),
                       highlightthickness=0)
        ent.pack(side="left", fill="both", expand=True, ipady=8)
        ent.insert(0, "")
        ent.focus_set()
        tk.Label(inner, text="⏎ edit  esc cancel", bg=INPUT_BG, fg=FG_FAINT,
                 font=ui_font(9)).pack(side="right", padx=10)

        def cancel(_e=None):
            top.destroy()

        def submit(_e=None):
            instruction = ent.get().strip()
            top.destroy()
            if instruction:
                self._inline_worker_start(ed, instruction)

        ent.bind("<Return>", submit)
        ent.bind("<Escape>", cancel)
        top.grab_set()

    def _inline_worker_start(self, ed, instruction):
        try:
            sel = ed.text.get("sel.first", "sel.last")
            sel_range = (ed.text.index("sel.first"), ed.text.index("sel.last"))
        except tk.TclError:
            sel = ed.get()
            sel_range = None
        self.set_status("✦ generating inline edit…")
        threading.Thread(target=self._inline_worker,
                         args=(ed, instruction, sel, sel_range),
                         daemon=True).start()

    def _inline_worker(self, ed, instruction, code, sel_range):
        msgs = [
            {"role": "system", "content":
                "You are an inline code editor. Rewrite the given code per "
                "the instruction. Reply with ONLY the replacement code — no "
                "explanations, no markdown fences."},
            {"role": "user", "content":
                f"Instruction: {instruction}\n\nCode:\n{code}"},
        ]
        flag = threading.Event()
        try:
            reply = self.lm.stream_chat(msgs, self.model_var.get(),
                                        lambda t: None, flag, temperature=0.3)
        except Exception as e:  # noqa: BLE001
            self.ui_queue.put(("status", f"inline edit failed: {e}"))
            return
        reply = re.sub(r"^```[\w]*\n|```$", "", reply.strip(), flags=re.M)
        self.ui_queue.put(("inline_result", (ed, sel_range, reply)))

    # =========================================================================
    # Command palette
    # =========================================================================
    def command_palette(self):
        cmds = [
            ("New File", self.new_file),
            ("Open File…", self.open_file_dialog),
            ("Open Folder…", self.open_folder_dialog),
            ("Save", self.save_file),
            ("Save As…", self.save_file_as),
            ("Run Active File", self.run_file),
            ("New Terminal", self.new_terminal),
            ("Toggle Sidebar", self.toggle_sidebar),
            ("Toggle Panel", self.toggle_panel),
            ("Toggle AI Pane", self.toggle_ai),
            ("New AI Chat", self.clear_chat),
            ("New Agent Session", self.new_session),
            ("AI: Agent Mode", lambda: self.set_mode("Agent")),
            ("AI: Ask Mode", lambda: self.set_mode("Ask")),
            ("AI: Plan Mode", lambda: self.set_mode("Plan")),
            ("AI: Review Changes (Diff)", self.review_changes),
            ("AI: Keep All Changes", self.keep_all_changes),
            ("AI: Undo All Changes", self.undo_all_changes),
            ("AI: Toggle Tab Autocomplete", self._toggle_tab),
            ("About CatIDE", self.show_about),
        ]
        top = tk.Toplevel(self)
        top.overrideredirect(True)
        top.configure(bg=ACCENT)
        w = 520
        x = self.winfo_rootx() + (self.winfo_width() - w) // 2
        y = self.winfo_rooty() + 80
        top.geometry(f"{w}x320+{x}+{y}")
        inner = tk.Frame(top, bg=SIDEBAR_BG)
        inner.pack(fill="both", expand=True, padx=1, pady=1)
        ent = tk.Entry(inner, bg=INPUT_BG, fg=FG_BRIGHT, bd=0,
                       insertbackground=FG_BRIGHT, font=ui_font(13),
                       highlightthickness=0)
        ent.pack(fill="x", padx=8, pady=8, ipady=7)
        lb = tk.Listbox(inner, bg=SIDEBAR_BG, fg=FG, bd=0,
                        selectbackground=SEL_BG, selectforeground=FG_BRIGHT,
                        font=ui_font(12), highlightthickness=0,
                        activestyle="none")
        lb.pack(fill="both", expand=True, padx=8, pady=(0, 8))

        state = {"filtered": cmds}

        def refresh(_e=None):
            q = ent.get().lower()
            state["filtered"] = [c for c in cmds if q in c[0].lower()]
            lb.delete(0, "end")
            for name, _ in state["filtered"]:
                lb.insert("end", "  " + name)
            if state["filtered"]:
                lb.selection_set(0)

        def run(_e=None):
            sel = lb.curselection()
            idx = sel[0] if sel else 0
            top.destroy()
            if state["filtered"]:
                state["filtered"][idx][1]()

        def move(delta):
            sel = lb.curselection()
            idx = (sel[0] if sel else 0) + delta
            idx = max(0, min(lb.size() - 1, idx))
            lb.selection_clear(0, "end")
            lb.selection_set(idx)
            lb.see(idx)
            return "break"

        ent.bind("<KeyRelease>", refresh)
        ent.bind("<Return>", run)
        ent.bind("<Escape>", lambda e: top.destroy())
        ent.bind("<Down>", lambda e: move(1))
        ent.bind("<Up>", lambda e: move(-1))
        lb.bind("<Double-1>", run)
        top.grab_set()
        refresh()
        ent.focus_set()

    # =========================================================================
    # Toggles / misc
    # =========================================================================
    def toggle_sidebar(self):
        if str(self.sidebar) in map(str, self.hpane.panes()):
            self.hpane.forget(self.sidebar)
        else:
            self.hpane.add(self.sidebar, before=self.center, minsize=170,
                           width=250)

    def toggle_panel(self):
        if str(self.panel) in map(str, self.vpane.panes()):
            self.vpane.forget(self.panel)
        else:
            self.vpane.add(self.panel, height=240, minsize=100)

    def toggle_ai(self):
        if str(self.ai_pane) in map(str, self.hpane.panes()):
            self.hpane.forget(self.ai_pane)
        else:
            self.hpane.add(self.ai_pane, minsize=300, width=430)

    def show_about(self):
        messagebox.showinfo(
            f"About {APP_NAME}",
            f"{APP_NAME} {APP_VERSION} — AI Agents OS\n"
            "A Cursor-3-style vibe coding IDE powered by LM Studio.\n\n"
            f"Platform: {PLATFORM} · shell: {SHELL_NAME}\n"
            f"Agents: {workspace_agent_dir(self.workspace)}\n"
            f"Global: {CONFIG_DIR}\n\n"
            f"Compat layer:\n{BUILD_INFO}\n\n"
            f"Python: {sys.version.split()[0]}\n"
            f"LM Studio API: {LM_STUDIO_BASE}")

    def _quit_app(self):
        for sess in self.sessions:
            sess.stop_flag.set()
            sess.save()
        self._save_settings()
        for t in self.terminals:
            try:
                if t.proc:
                    t.proc.kill()
            except OSError:
                pass
        self.destroy()
        os._exit(0)

    def log_output(self, text):
        self.output.configure(state="normal")
        self.output.insert("end", text)
        self.output.see("end")
        self.output.configure(state="disabled")

    def set_status(self, text):
        self.status_msg.configure(text=text)

    def set_cursor_pos(self, ln, col):
        self.status_pos.configure(text=f"Ln {ln}, Col {col}")

    # =========================================================================
    # UI queue pump (all worker → UI updates flow through here)
    # =========================================================================
    def _pump(self):
        try:
            while True:
                kind, payload = self.ui_queue.get_nowait()
                if kind == "token":
                    sid, tok = payload
                    sess = self._session_by_id(sid)
                    if sess:
                        sess.last_reply += tok
                        self._chat_write(tok, None, sess)
                elif kind == "chat_head":
                    sess = self._session_by_id(payload)
                    if sess:
                        sess.last_reply = ""
                        self._chat_write("\ncat ▸ ", "cat", sess)
                elif kind == "reply_done":
                    sess = self._session_by_id(payload)
                    if sess:
                        self._chat_write("\n", None, sess)
                        sess.save()
                elif kind == "chat_note":
                    sid, note = payload
                    sess = self._session_by_id(sid)
                    if sess:
                        self._chat_write(note, "ok", sess)
                elif kind == "done":
                    sess = self._session_by_id(payload)
                    if sess:
                        sess.streaming = False
                        sess.save()
                    self._session_spinner()
                    self._update_send_btn()
                    self.set_status("ready to vibe ✦")
                elif kind == "error":
                    sid, msg = payload
                    sess = self._session_by_id(sid)
                    if sess:
                        self._chat_write("\n⚠ " + msg + "\n", "err", sess)
                        sess.streaming = False
                        sess.save()
                    self._session_spinner()
                    self._update_send_btn()
                    self.set_status("LM Studio error")
                elif kind == "ghost":
                    editor, gen, completion = payload
                    if editor.winfo_exists():
                        editor.show_ghost(gen, completion)
                elif kind == "git":
                    self.git_branch = payload
                    self.status_git.configure(
                        text=f"⎇ {payload}" if payload else "")
                    self._update_ctx_chip()
                elif kind == "review":
                    sess = self._session_by_id(payload)
                    if sess is self.active_session:
                        self._update_review_bar()
                elif kind == "status":
                    self.set_status(payload)
                elif kind == "models":
                    self._apply_models(payload)
                elif kind == "output":
                    self.show_panel_tab("OUTPUT")
                    self.log_output(payload)
                elif kind == "agent_term":
                    text, tag = payload
                    self.agent_term.configure(state="normal")
                    self.agent_term.insert("end", text, tag)
                    self.agent_term.see("end")
                    self.agent_term.configure(state="disabled")
                    self.show_panel_tab("AI AGENT")
                elif kind == "problems":
                    path, errs = payload
                    self.problems.delete(0, "end")
                    if errs:
                        for e in errs:
                            self.problems.insert("end", " ⚠ " + e)
                        self.show_panel_tab("PROBLEMS")
                    else:
                        self.problems.insert(
                            "end", f" ✓ {os.path.basename(path)} — no problems")
                elif kind == "refresh_file":
                    path = self._canon_path(payload)
                    if path in self.tabs:
                        self._sync_editor_from_disk(path)
                    if os.path.isfile(path):
                        self._sync_tree_file(path)
                    elif not os.path.exists(path):
                        self.populate_tree(self.workspace)
                elif kind == "open_file":
                    path = self._canon_path(payload)
                    if os.path.isfile(path):
                        self.open_path(path)
                elif kind == "search_done":
                    self._search_hits = payload
                    self.search_results.delete(0, "end")
                    for path, line, snippet in payload:
                        rel = os.path.relpath(path, self.workspace)
                        self.search_results.insert(
                            "end", f" {rel}:{line}  {snippet}")
                    if not payload:
                        self.search_results.insert("end", " no results")
                elif kind == "inline_result":
                    ed, sel_range, new_code = payload
                    if sel_range:
                        ed.text.delete(*sel_range)
                        ed.text.insert(sel_range[0], new_code)
                    else:
                        ed.set(new_code)
                    ed._on_change()
                    self.set_status("✦ inline edit applied")
        except queue.Empty:
            pass
        self.after(60, self._pump)

    def _apply_models(self, models):
        menu = self.model_menu["menu"]
        menu.delete(0, "end")
        saved = self.settings.get("model", "")
        if models:
            for mid in models:
                menu.add_command(
                    label=mid, command=lambda m=mid: self.model_var.set(m))
            pick = saved if saved in models else models[0]
            self.model_var.set(pick)
            self.status_model.configure(text=f"model: {pick}")
        else:
            self.model_var.set(saved or "local-model")
            self.status_model.configure(text="LM Studio offline")
            if not self._lm_warned:
                self._lm_warned = True
                self._chat_write(
                    "⚠ LM Studio not reachable — start its local server "
                    "(Developer tab) and load a model, then it auto-connects "
                    "on the next message.\n", "err")


if __name__ == "__main__":
    app = CatIDE()
    app.mainloop()
