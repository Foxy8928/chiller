"""
Music DL 2.0 - ダウンローダー + 音楽プレーヤー
YouTube / SoundCloud / Bandcamp / ニコニコ / Vimeo / X など yt-dlp が対応するサイトからダウンロードし、
そのままアプリ内で聴けます。ライブラリ / アルバム / アーティストページ / プレイリスト /
同期歌詞(LRC) / ビジュアライザー / 設定(yt-dlp更新・Denoインストール) 付き。
(Spotify / Apple Music / Amazon Music などDRM保護のサービスは非対応です)

必要: Python 3.9+ / FFmpeg  (Pythonライブラリは初回起動時に自動インストール)
"""
import base64
import hashlib
import io
import json
import math
import os
import platform
import queue
import random
import re
import shutil
import subprocess
import sys
import threading
import time
import tkinter as tk
import tkinter.font as tkfont
import urllib.parse
import urllib.request
import webbrowser
import zipfile
from bisect import bisect_right
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from tkinter import filedialog, messagebox, ttk


# ───────────────────────── 依存ライブラリの自動導入 ─────────────────────────
def ensure_deps():
    missing = []
    for mod, pkg in (("customtkinter", "customtkinter"), ("yt_dlp", "yt-dlp[default]"), ("mutagen", "mutagen"),
                     ("PIL", "Pillow"), ("numpy", "numpy"), ("sounddevice", "sounddevice")):
        try:
            __import__(mod)
        except ImportError:
            missing.append(pkg)
        except Exception:
            pass  # sounddeviceはPortAudioが無いとOSError。プレーヤー機能だけ無効にして続行する
    if missing:
        print(f"初回セットアップ: {', '.join(missing)} をインストールします...")
        try:
            subprocess.check_call([sys.executable, "-m", "pip", "install", "-U", *missing])
        except Exception as e:
            print(f"自動インストールに失敗しました: {e}")
            print(f"手動で実行してください: pip install -U {' '.join(missing)}")
            try:
                input("Enterで終了")
            except Exception:
                pass
            sys.exit(1)


ensure_deps()

import customtkinter as ctk  # noqa: E402
import mutagen  # noqa: E402
import numpy as np  # noqa: E402
import yt_dlp  # noqa: E402
from mutagen.flac import FLAC, Picture  # noqa: E402
from mutagen.id3 import ID3  # noqa: E402
from mutagen.mp4 import MP4  # noqa: E402
from PIL import Image, ImageDraw, ImageEnhance, ImageFilter, ImageOps, ImageTk  # noqa: E402

try:
    import sounddevice as sd  # noqa: E402
except Exception:  # PortAudio未導入など
    sd = None

APP_NAME = "Music DL"
APP_VER = "2.0"
APP_DIR = Path.home() / ".music_dl"
BIN_DIR = APP_DIR / "bin"
LYRICS_DIR = APP_DIR / "lyrics"
ART_DIR = APP_DIR / "artists"
LIB_FILE = APP_DIR / "library.json"
USER_FILE = APP_DIR / "userdata.json"
SETTINGS_FILE = Path.home() / ".music_dl_settings.json"
for _d in (BIN_DIR, LYRICS_DIR, ART_DIR):
    try:
        _d.mkdir(parents=True, exist_ok=True)
    except Exception:
        pass
ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
SEARCH_RE = re.compile(r"^\w+search\d*:")
NOWIN = getattr(subprocess, "CREATE_NO_WINDOW", 0)
UA = "Mozilla/5.0 (compatible; MusicDL/2.0)"
FONT_FAMILY = "Yu Gothic UI" if os.name == "nt" else "Helvetica"

# ───────────────────────── テーマ ─────────────────────────
THEMES = {
    "バイオレット": ("#7c5cff", "#6a49f0"),
    "ブルー": ("#3b82f6", "#2f6fdc"),
    "グリーン": ("#22c55e", "#1aa34a"),
    "ピンク": ("#ec4899", "#d33a87"),
    "オレンジ": ("#f97316", "#dc6410"),
}
BG = "#0d0f14"
SIDEBAR = "#0a0c11"
CARD = "#161a23"
CARD_2 = "#1d2230"
HOVER = "#272d3f"
ACCENT, ACCENT_H = THEMES["バイオレット"]
TEXT = "#e8eaf2"
MUTED = "#8b91a7"
OK = "#4ade80"
WARN = "#fbbf24"
ERR = "#f87171"


def apply_theme(name):
    global ACCENT, ACCENT_H
    ACCENT, ACCENT_H = THEMES.get(name, THEMES["バイオレット"])


def F(size=13, weight="normal"):
    return ctk.CTkFont(family=FONT_FAMILY, size=size, weight=weight)


AUDIO_FORMATS = {"M4A": "m4a", "MP3": "mp3", "FLAC": "flac", "OPUS": "opus", "WAV": "wav"}
LOSSLESS = {"flac", "wav"}
AUDIO_QUALITIES = ["128k", "192k", "256k", "320k"]
VIDEO_QUALITIES = ["480p", "720p", "1080p", "最高画質"]
BROWSERS = ["使わない", "chrome", "edge", "firefox", "brave", "opera"]
RATE_LIMITS = ["無制限", "500K", "1M", "2M", "5M", "10M"]
AUDIO_EXTS = {".m4a", ".mp3", ".flac", ".opus", ".ogg", ".wav", ".aac", ".wma"}
TAG_JUNK = re.compile(r"\.f\d+\.|\.part$|\.temp\.|\.ytdl$", re.I)
SITES_HINT = "YouTube · SoundCloud · Bandcamp · ニコニコ · Vimeo · X · TikTok など1000+サイト / 検索ワードもOK"


# ───────────────────────── ユーティリティ ─────────────────────────
class Cancelled(yt_dlp.utils.DownloadCancelled):
    """キャンセル用。DownloadCancelledを継承しないと ignoreerrors=True で握りつぶされてしまう"""


def fmt_size(n):
    if not n:
        return "-- B"
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024:
            return f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} TB"


def fmt_eta(s):
    if s is None:
        return "--:--"
    s = max(0, int(s))
    h, r = divmod(s, 3600)
    return f"{h}:{r // 60:02d}:{r % 60:02d}" if h else f"{r // 60:02d}:{r % 60:02d}"


def fmt_dur(s):
    if not s:
        return ""
    s = int(s)
    h, r = divmod(s, 3600)
    m, sec = divmod(r, 60)
    return f"{h}:{m:02d}:{sec:02d}" if h else f"{m}:{sec:02d}"


def fmt_total(s):
    s = int(s or 0)
    h, r = divmod(s, 3600)
    if h:
        return f"{h}時間{r // 60}分"
    return f"{r // 60}分" if r >= 60 else f"{r}秒"


def fmt_views(n):
    if not n:
        return ""
    if n >= 1e8:
        return f"{n / 1e8:.1f}億回"
    if n >= 1e4:
        return f"{n / 1e4:.1f}万回"
    return f"{int(n)}回"


def find_ffmpeg():
    """PATH → スクリプト横 → ./ffmpeg/bin → winget の順に探す。見つかったらフォルダパス(PATHにある場合はNone)を返す"""
    if shutil.which("ffmpeg"):
        return True, None
    bases = []
    try:
        bases.append(Path(__file__).resolve().parent)
    except NameError:
        pass
    if getattr(sys, "frozen", False):
        bases.append(Path(sys.executable).resolve().parent)
    bases.append(Path.cwd())
    exe_name = "ffmpeg.exe" if os.name == "nt" else "ffmpeg"
    for base in bases:
        for cand in (base, base / "ffmpeg", base / "ffmpeg" / "bin", base / "bin"):
            if (cand / exe_name).exists():
                return True, str(cand)
    la = os.environ.get("LOCALAPPDATA")
    if la:
        cand = Path(la) / "Microsoft" / "WinGet" / "Links"
        if (cand / exe_name).exists():
            return True, str(cand)
    return False, None


def ffmpeg_exe():
    _, d = find_ffmpeg()
    return str(Path(d) / ("ffmpeg.exe" if os.name == "nt" else "ffmpeg")) if d else "ffmpeg"


def normalize_input(text):
    """URLならそのまま、URLでなければYouTube検索(上位1件)にする"""
    text = text.strip().strip("'\"")
    if not text:
        return None
    if re.match(r"^[A-Za-z][A-Za-z0-9+.-]*://", text) or SEARCH_RE.match(text):
        return text
    if text.startswith("www.") or re.match(r"^[\w-]+(\.[\w-]+)+/", text):
        return "https://" + text
    return f"ytsearch1:{text}"


def split_items(text):
    """入力欄/クリップボードの文字列を1件ずつに分ける(1行にURLがスペース区切りで複数あれば分割)"""
    items = []
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        if re.search(r"https?://", line) and " " in line:
            items += [x for x in line.split() if x]
        else:
            items.append(line)
    return items


def load_settings():
    try:
        d = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def save_settings(d):
    try:
        SETTINGS_FILE.write_text(json.dumps(d, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception:
        pass


def http_get(url, timeout=10, headers=None):
    h = {"User-Agent": UA}
    h.update(headers or {})
    with urllib.request.urlopen(urllib.request.Request(url, headers=h), timeout=timeout) as r:
        return r.read()


def http_json(url, timeout=10):
    return json.loads(http_get(url, timeout).decode("utf-8"))


def parse_rate(s):
    m = re.match(r"^(\d+(?:\.\d+)?)\s*([KkMm]?)$", (s or "").strip())
    if not m:
        return None
    return int(float(m.group(1)) * {"": 1, "k": 1024, "m": 1024 * 1024}[m.group(2).lower()])


def ver_tuple(v):
    return tuple(int(x) for x in re.findall(r"\d+", v or "")) or (0,)


def dir_info(path):
    n = size = 0
    try:
        for p in Path(path).glob("*"):
            if p.is_file():
                n += 1
                size += p.stat().st_size
    except Exception:
        pass
    return n, size


def open_path(p):
    try:
        if os.name == "nt":
            os.startfile(str(p))  # type: ignore[attr-defined]
        elif sys.platform == "darwin":
            subprocess.Popen(["open", str(p)])
        else:
            subprocess.Popen(["xdg-open", str(p)])
    except Exception:
        pass


def reveal_file(p):
    try:
        if os.name == "nt":
            subprocess.Popen(["explorer", "/select,", str(p)])
        elif sys.platform == "darwin":
            subprocess.Popen(["open", "-R", str(p)])
        else:
            subprocess.Popen(["xdg-open", str(Path(p).parent)])
    except Exception:
        pass


# ───────────────────────── ツール管理 (yt-dlp / Deno / FFmpeg) ─────────────────────────
def ytdlp_version():
    try:
        return yt_dlp.version.__version__
    except Exception:
        return "?"


def latest_ytdlp_version():
    return http_json("https://pypi.org/pypi/yt-dlp/json", 10)["info"]["version"]


def deno_exe_name():
    return "deno.exe" if os.name == "nt" else "deno"


def deno_asset():
    arm = platform.machine().lower() in ("arm64", "aarch64")
    if os.name == "nt":
        return "deno-aarch64-pc-windows-msvc.zip" if arm else "deno-x86_64-pc-windows-msvc.zip"
    if sys.platform == "darwin":
        return "deno-aarch64-apple-darwin.zip" if arm else "deno-x86_64-apple-darwin.zip"
    return "deno-aarch64-unknown-linux-gnu.zip" if arm else "deno-x86_64-unknown-linux-gnu.zip"


def deno_path():
    local = BIN_DIR / deno_exe_name()
    if local.exists():
        return str(local)
    return shutil.which("deno")


def activate_deno_path():
    """アプリ内にインストールしたDenoをこのプロセスのPATHへ追加(yt-dlpが自動検出できるように)"""
    if (BIN_DIR / deno_exe_name()).exists() and str(BIN_DIR) not in os.environ.get("PATH", ""):
        os.environ["PATH"] = str(BIN_DIR) + os.pathsep + os.environ.get("PATH", "")


def tool_version(path, args=("--version",)):
    try:
        p = subprocess.run([path, *args], capture_output=True, text=True, timeout=20, creationflags=NOWIN)
        return (p.stdout or p.stderr).strip().splitlines()[0]
    except Exception:
        return ""


def install_deno(on_progress):
    """GitHub公式リリースからDenoを取得して ~/.music_dl/bin に展開する"""
    asset = deno_asset()
    url = f"https://github.com/denoland/deno/releases/latest/download/{asset}"
    BIN_DIR.mkdir(parents=True, exist_ok=True)
    tmp = BIN_DIR / asset
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=30) as r, open(tmp, "wb") as f:
        total = int(r.headers.get("Content-Length") or 0)
        done = 0
        while True:
            chunk = r.read(65536)
            if not chunk:
                break
            f.write(chunk)
            done += len(chunk)
            on_progress(done, total)
    name = deno_exe_name()
    with zipfile.ZipFile(tmp) as z:
        z.extract(name, BIN_DIR)
    tmp.unlink(missing_ok=True)
    exe = BIN_DIR / name
    os.chmod(exe, 0o755)
    activate_deno_path()
    return str(exe)


def run_stream(cmd, on_line):
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                         encoding="utf-8", errors="replace", creationflags=NOWIN)
    for line in p.stdout:
        line = line.rstrip()
        if line:
            on_line(line)
    return p.wait()


def ydl_common(cfg):
    """ダウンロード/試聴で共通のyt-dlpオプション (プロキシ・Cookie・JSランタイム)"""
    o = {}
    if cfg.get("proxy"):
        o["proxy"] = cfg["proxy"]
    dp = deno_path()
    if dp:
        o["js_runtimes"] = {"deno": {"path": dp}}
    if cfg.get("remote_components"):
        o["remote_components"] = ["ejs:github"]
    b = cfg.get("browser", "使わない")
    if b and b != "使わない":
        o["cookiesfrombrowser"] = (b,)
    return o


# ───────────────────────── ライブラリ (タグ・カバー) ─────────────────────────
def clean_artist(a):
    return re.sub(r"\s*-\s*Topic$", "", (a or "").strip())


def read_tags(path):
    p = Path(path)
    st = p.stat()
    d = {"path": str(p), "title": p.stem, "artist": "", "album": "", "albumartist": "", "dur": 0.0,
         "track": 0, "year": "", "mtime": st.st_mtime, "size": st.st_size}
    try:
        f = mutagen.File(str(p), easy=True)
        if f is not None:
            d["dur"] = float(getattr(f.info, "length", 0) or 0)
            tg = f.tags or {}

            def g(k):
                try:
                    v = tg.get(k)
                except Exception:
                    v = None
                return str(v[0]).strip() if v else ""

            d["title"] = g("title") or d["title"]
            d["artist"] = g("artist")
            d["albumartist"] = g("albumartist")
            d["album"] = g("album")
            m = re.match(r"\d+", g("tracknumber"))
            d["track"] = int(m.group()) if m else 0
            d["year"] = g("date")[:4]
    except Exception:
        pass
    d["artist"] = clean_artist(d["artist"] or d["albumartist"])
    if not d["artist"]:
        d["artist"] = p.parent.name if p.parent.name not in ("Music", "") else "不明なアーティスト"
    d["albumartist"] = clean_artist(d["albumartist"])
    return d


def extract_cover_bytes(path):
    p = Path(path)
    ext = p.suffix.lower()
    try:
        if ext == ".mp3":
            tags = ID3(str(p))
            for k in tags.keys():
                if k.startswith("APIC"):
                    return tags[k].data
        elif ext in (".m4a", ".mp4", ".aac"):
            covr = (MP4(str(p)).tags or {}).get("covr")
            if covr:
                return bytes(covr[0])
        elif ext == ".flac":
            pics = FLAC(str(p)).pictures
            if pics:
                return pics[0].data
        elif ext in (".opus", ".ogg"):
            f = mutagen.File(str(p))
            mbp = (f.tags or {}).get("metadata_block_picture") if f else None
            if mbp:
                return Picture(base64.b64decode(mbp[0])).data
    except Exception:
        pass
    for name in ("cover.jpg", "folder.jpg", "cover.png", "folder.png", "front.jpg"):
        c = p.parent / name
        if c.exists():
            try:
                return c.read_bytes()
            except Exception:
                pass
    return None


class Library:
    def __init__(self):
        self.tracks, self.by_path = [], {}
        self.artists, self.albums = {}, {}
        self._cache = {}
        try:
            raw = json.loads(LIB_FILE.read_text(encoding="utf-8"))
            if isinstance(raw, dict):
                self._cache = raw
        except Exception:
            pass

    def cached_tracks(self):
        return [t for p, t in self._cache.items() if os.path.exists(p)]

    def scan(self, dirs):
        """バックグラウンドで実行。変更の無いファイルはキャッシュを再利用"""
        found = {}
        for base in dirs:
            for root, _, files in os.walk(base):
                for fn in files:
                    if os.path.splitext(fn)[1].lower() not in AUDIO_EXTS or TAG_JUNK.search(fn):
                        continue
                    fp = os.path.join(root, fn)
                    try:
                        st = os.stat(fp)
                    except OSError:
                        continue
                    c = self._cache.get(fp)
                    if c and abs(c.get("mtime", 0) - st.st_mtime) < 1 and c.get("size") == st.st_size:
                        found[fp] = c
                    else:
                        found[fp] = read_tags(fp)
        self._cache = found
        try:
            LIB_FILE.write_text(json.dumps(found, ensure_ascii=False), encoding="utf-8")
        except Exception:
            pass
        return list(found.values())

    def set_tracks(self, tracks):
        self.tracks = sorted(tracks, key=lambda t: (t["artist"].casefold(), (t["album"] or "").casefold(),
                                                    t["track"] or 999, t["title"].casefold()))
        self.by_path = {t["path"]: t for t in self.tracks}
        self.artists, self.albums = {}, {}
        for t in self.tracks:
            self.artists.setdefault(t["artist"], []).append(t)
            key = (t["albumartist"] or t["artist"], t["album"] or "シングル")
            self.albums.setdefault(key, []).append(t)

    def total_duration(self, tracks=None):
        return sum(t.get("dur") or 0 for t in (tracks if tracks is not None else self.tracks))


class UserData:
    """お気に入り・プレイリスト・再生回数・履歴"""

    def __init__(self):
        self.d = {"favorites": [], "playlists": {}, "plays": {}, "recent": []}
        try:
            raw = json.loads(USER_FILE.read_text(encoding="utf-8"))
            if isinstance(raw, dict):
                self.d.update(raw)
        except Exception:
            pass
        self.fav = set(self.d["favorites"])

    def save(self):
        self.d["favorites"] = sorted(self.fav)
        try:
            USER_FILE.write_text(json.dumps(self.d, ensure_ascii=False), encoding="utf-8")
        except Exception:
            pass

    def is_fav(self, path):
        return path in self.fav

    def toggle_fav(self, path):
        if path in self.fav:
            self.fav.discard(path)
        else:
            self.fav.add(path)
        self.save()
        return path in self.fav

    @property
    def playlists(self):
        return self.d["playlists"]

    def create_playlist(self, name):
        name = name.strip()
        if name and name not in self.playlists:
            self.playlists[name] = []
            self.save()
            return True
        return False

    def add_to_playlist(self, name, paths):
        pl = self.playlists.setdefault(name, [])
        n = 0
        for p in paths:
            if p not in pl:
                pl.append(p)
                n += 1
        self.save()
        return n

    def remove_from_playlist(self, name, paths):
        self.playlists[name] = [p for p in self.playlists.get(name, []) if p not in set(paths)]
        self.save()

    def rename_playlist(self, old, new):
        new = new.strip()
        if new and new != old and new not in self.playlists and old in self.playlists:
            self.playlists[new] = self.playlists.pop(old)
            self.save()
            return True
        return False

    def delete_playlist(self, name):
        self.playlists.pop(name, None)
        self.save()

    def record_play(self, path):
        self.d["plays"][path] = self.d["plays"].get(path, 0) + 1
        rec = [p for p in self.d["recent"] if p != path]
        rec.insert(0, path)
        self.d["recent"] = rec[:60]
        self.save()

    def plays(self, path):
        return self.d["plays"].get(path, 0)


def make_placeholder(size, seed):
    h = int(hashlib.md5((seed or "?").encode("utf-8")).hexdigest()[:6], 16)
    c1 = (60 + h % 90, 50 + (h >> 8) % 80, 110 + (h >> 16) % 120)
    img = ImageOps.colorize(Image.linear_gradient("L").resize((size, size)), black=c1, white=(20, 22, 34))
    d = ImageDraw.Draw(img)
    s = size
    col = (255, 255, 255)
    d.ellipse([s * .30, s * .56, s * .50, s * .72], fill=col)
    d.rectangle([s * .47, s * .26, s * .51, s * .64], fill=col)
    d.polygon([(s * .51, s * .26), (s * .68, s * .34), (s * .68, s * .42), (s * .51, s * .35)], fill=col)
    return img


def round_image(img, radius_ratio=0.07):
    w, h = img.size
    big = Image.new("L", (w * 3, h * 3), 0)
    ImageDraw.Draw(big).rounded_rectangle([0, 0, w * 3 - 1, h * 3 - 1], radius=int(w * 3 * radius_ratio), fill=255)
    out = img.convert("RGBA")
    out.putalpha(big.resize((w, h), Image.LANCZOS))
    return out


class Covers:
    def __init__(self):
        self.cache = {}

    def key(self, t, size):
        return (t["path"], size)

    def cached(self, t, size):
        return self.cache.get(self.key(t, size), 0)  # 0=未取得 / None=無し

    def get(self, t, size):
        k = self.key(t, size)
        if k in self.cache:
            return self.cache[k]
        img = None
        try:
            data = http_get(t["thumb"], 8) if t.get("remote") and t.get("thumb") else \
                (None if t.get("remote") else extract_cover_bytes(t["path"]))
            if data:
                img = ImageOps.fit(Image.open(io.BytesIO(data)).convert("RGB"), (size, size), Image.LANCZOS)
        except Exception:
            img = None
        if len(self.cache) > 800:
            self.cache.clear()
        self.cache[k] = img
        return img

    def get_any(self, tracks, size, tries=4):
        for t in tracks[:tries]:
            im = self.get(t, size)
            if im is not None:
                return im
        return None


DEEZER_LOCK = threading.Lock()


def fetch_artist_image(name, size=300):
    """Deezer公開API(キー不要)からアーティスト画像を取得してキャッシュ"""
    f = ART_DIR / (hashlib.md5(name.encode("utf-8")).hexdigest() + ".jpg")
    try:
        if f.exists():
            if f.stat().st_size == 0:
                return None
            return ImageOps.fit(Image.open(f).convert("RGB"), (size, size), Image.LANCZOS)
        with DEEZER_LOCK:
            time.sleep(0.12)  # 公開APIの制限(約10回/秒)を超えないように
            j = http_json("https://api.deezer.com/search/artist?limit=3&q=" + urllib.parse.quote(name), 10)
        if not isinstance(j.get("data"), list):
            return None  # エラー応答(レート制限など)は結果をキャッシュしない
        for d in j["data"]:
            if (d.get("name") or "").casefold() == name.casefold() and d.get("picture_xl"):
                data = http_get(d["picture_xl"], 10)
                f.write_bytes(data)
                return ImageOps.fit(Image.open(io.BytesIO(data)).convert("RGB"), (size, size), Image.LANCZOS)
        f.write_bytes(b"")  # 見つからなかった(次回から問い合わせない)
    except Exception:
        pass
    return None


# ───────────────────────── 歌詞 (LRC / LRCLIB) ─────────────────────────
LRC_TS = re.compile(r"\[(\d+):(\d+(?:\.\d+)?)\]")
TITLE_NOISE = re.compile(r"[\(\[（【「『][^\)\]）】」』]*(official|mv|music video|lyric|audio|video|hd|4k|公式|歌ってみた|"
                         r"フル|full|ミュージックビデオ|オフィシャル)[^\)\]）】」』]*[\)\]）】」』]", re.I)


def clean_title(t):
    c = re.sub(r"\s+", " ", TITLE_NOISE.sub("", t or "")).strip()
    return c or t


def parse_lrc(text):
    out = []
    for line in (text or "").splitlines():
        stamps = LRC_TS.findall(line)
        if not stamps:
            continue
        body = re.sub(r"<\d+:\d+(?:\.\d+)?>", "", LRC_TS.sub("", line)).strip()
        for mm, ss in stamps:
            out.append((int(mm) * 60 + float(ss), body))
    out.sort(key=lambda x: x[0])
    return out


def pack_lyrics(txt):
    synced = parse_lrc(txt)
    if synced:
        return {"synced": synced, "plain": None}
    txt = (txt or "").strip()
    return {"synced": None, "plain": txt} if txt else None


def read_embedded_lyrics(path):
    try:
        f = mutagen.File(path)
        if f is None or not f.tags:
            return None
        tg = f.tags
        if isinstance(tg, ID3):
            us = tg.getall("USLT")
            if us:
                return str(us[0].text)
        for k in ("\xa9lyr", "lyrics", "unsyncedlyrics", "LYRICS"):
            v = tg.get(k)
            if v:
                return str(v[0])
    except Exception:
        pass
    return None


def fetch_lrclib(t):
    title, artist = clean_title(t.get("title", "")), clean_artist(t.get("artist", ""))
    q = {"track_name": title, "artist_name": artist}
    if t.get("album"):
        q["album_name"] = t["album"]
    if t.get("dur"):
        q["duration"] = int(round(t["dur"]))
    j = None
    try:
        j = http_json("https://lrclib.net/api/get?" + urllib.parse.urlencode(q), 10)
    except Exception:
        pass
    if not j:
        try:
            lst = http_json("https://lrclib.net/api/search?" + urllib.parse.urlencode({"q": f"{artist} {title}".strip()}), 10)
            if lst:
                j = next((x for x in lst if x.get("syncedLyrics")), lst[0])
        except Exception:
            pass
    if not j:
        return None
    return j.get("syncedLyrics") or j.get("plainLyrics")


def load_lyrics(t, online):
    p = t["path"]
    if not t.get("remote"):
        side = Path(p).with_suffix(".lrc")
        if side.exists():
            try:
                return pack_lyrics(side.read_text(encoding="utf-8", errors="replace"))
            except Exception:
                pass
    h = hashlib.md5(p.encode("utf-8")).hexdigest()
    for ext in (".lrc", ".txt"):
        f = LYRICS_DIR / (h + ext)
        if f.exists():
            return pack_lyrics(f.read_text(encoding="utf-8", errors="replace"))
    if not t.get("remote"):
        emb = read_embedded_lyrics(p)
        if emb:
            return pack_lyrics(emb)
    if online:
        txt = fetch_lrclib(t)
        if txt:
            ext = ".lrc" if parse_lrc(txt) else ".txt"
            try:
                (LYRICS_DIR / (h + ext)).write_text(txt, encoding="utf-8")
            except Exception:
                pass
            return pack_lyrics(txt)
    return None


# ───────────────────────── オーディオエンジン (ffmpegデコード + sounddevice出力) ─────────────────────────
class Session:
    def __init__(self, proc, start, source, headers, duration):
        self.proc, self.start, self.source, self.headers, self.duration = proc, start, source, headers, duration
        self.q = queue.Queue(maxsize=80)
        self.buf = bytearray()
        self.frames = 0
        self.eof = False
        self.finished = False
        self.dead = False


class AudioEngine:
    SR = 44100
    N = 2048

    def __init__(self):
        self.available = sd is not None
        self.sess = None
        self.stream = None
        self.paused = False
        self.volume = 0.8
        self.device = None
        self.error = ""
        self.ring = np.zeros(4096, dtype=np.float32)
        self.ri = 0
        self.win = np.hanning(self.N).astype(np.float32)
        self._edges = {}

    @property
    def gain(self):
        return self.volume * self.volume  # 体感に合うよう2乗カーブ

    def _ensure_stream(self):
        if not self.available:
            self.error = "sounddevice が使えません (PortAudio未導入)"
            return False
        if self.stream is not None:
            return True
        try:
            self.stream = sd.RawOutputStream(samplerate=self.SR, channels=2, dtype="int16",
                                             device=self.device, callback=self._cb)
            self.stream.start()
            return True
        except Exception as e:
            self.error = f"オーディオ出力を開けません: {e}"
            self.stream = None
            return False

    def set_device(self, device):
        self.device = device
        if self.stream is not None:
            try:
                self.stream.close()
            except Exception:
                pass
            self.stream = None
            self._ensure_stream()

    def _push_viz(self, arr):
        m = (arr[0::2].astype(np.float32) + arr[1::2].astype(np.float32)) * (0.5 / 32768.0)
        k, r, i = len(m), self.ring, self.ri
        if k >= len(r):
            r[:] = m[-len(r):]
            i = 0
        else:
            end = i + k
            if end <= len(r):
                r[i:end] = m
            else:
                split = len(r) - i
                r[i:] = m[:split]
                r[:k - split] = m[split:]
            i = end % len(r)
        self.ri = i

    def _cb(self, outdata, frames, tinfo, status):
        need = frames * 4
        s = self.sess
        if s is None or self.paused:
            outdata[:] = bytes(need)
            return
        buf = s.buf
        while len(buf) < need:
            try:
                buf += s.q.get_nowait()
            except queue.Empty:
                break
        n = min(need, len(buf))
        raw = bytes(buf[:n])
        del buf[:n]
        if n < need:
            raw += bytes(need - n)
            if n == 0 and s.eof and s.q.empty():
                s.finished = True
        arr = np.frombuffer(raw, dtype=np.int16)
        self._push_viz(arr)
        g = self.gain
        if g < 0.999:
            raw = (arr.astype(np.float32) * g).astype(np.int16).tobytes()
        outdata[:] = raw
        s.frames += n // 4

    def _reader(self, s):
        out = s.proc.stdout
        try:
            while not s.dead:
                data = out.read(16384)
                if not data:
                    break
                while not s.dead:
                    try:
                        s.q.put(data, timeout=0.2)
                        break
                    except queue.Full:
                        pass
        except Exception:
            pass
        s.eof = True

    def play(self, source, start=0.0, headers=None, duration=0.0):
        self.stop()
        if not self._ensure_stream():
            return False
        cmd = [ffmpeg_exe(), "-v", "error", "-nostdin"]
        if str(source).startswith("http"):
            cmd += ["-user_agent", UA]
            hdr = "".join(f"{k}: {v}\r\n" for k, v in (headers or {}).items() if k.lower() != "user-agent")
            if hdr:
                cmd += ["-headers", hdr]
            cmd += ["-reconnect", "1", "-reconnect_streamed", "1", "-reconnect_delay_max", "5"]
        if start > 0.05:
            cmd += ["-ss", f"{start:.3f}"]
        cmd += ["-i", str(source), "-vn", "-sn", "-f", "s16le", "-acodec", "pcm_s16le",
                "-ac", "2", "-ar", str(self.SR), "-"]
        try:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                    stdin=subprocess.DEVNULL, creationflags=NOWIN)
        except Exception as e:
            self.error = f"ffmpegを起動できません: {e}"
            return False
        s = Session(proc, start, source, headers, duration)
        threading.Thread(target=self._reader, args=(s,), daemon=True).start()
        self.paused = False
        self.sess = s
        return True

    def stop(self):
        s, self.sess = self.sess, None
        if s:
            s.dead = True
            try:
                s.proc.kill()
            except Exception:
                pass
            threading.Thread(target=s.proc.wait, daemon=True).start()

    def close(self):
        self.stop()
        if self.stream is not None:
            try:
                self.stream.close()
            except Exception:
                pass
            self.stream = None

    def seek(self, t):
        s = self.sess
        if s:
            self.play(s.source, max(0.0, t), s.headers, s.duration)

    def position(self):
        s = self.sess
        return (s.start + s.frames / self.SR) if s else 0.0

    def finished(self):
        s = self.sess
        return bool(s and s.finished)

    def spectrum(self, n=48):
        N = self.N
        r = np.concatenate((self.ring[self.ri:], self.ring[:self.ri]))[-N:]
        spec = np.abs(np.fft.rfft(r * self.win)) / (N / 4)
        e = self._edges.get(n)
        if e is None:
            e = np.clip((np.geomspace(40, 15000, n + 1) / (self.SR / N)).astype(int), 1, N // 2 - 1)
            for i in range(1, len(e)):
                e[i] = max(e[i], e[i - 1] + 1)
            self._edges[n] = e
        out = np.fromiter((spec[e[i]:e[i + 1]].max() for i in range(n)), dtype=np.float32, count=n)
        db = 20 * np.log10(out + 1e-7) + np.linspace(0, 16, n)
        return np.clip((db + 78) / 56, 0, 1)

    @staticmethod
    def output_devices():
        if sd is None:
            return []
        try:
            return [d["name"] for d in sd.query_devices() if d.get("max_output_channels", 0) > 0]
        except Exception:
            return []
class QLogger:
    KEEP = ("Destination", "Merging", "Downloading playlist", "Downloading item", "Adding thumbnail", "Extracting audio",
            "has already been downloaded")

    def __init__(self, q):
        self.q = q

    def debug(self, msg):
        msg = ANSI_RE.sub("", msg)
        if msg.startswith("[debug]"):
            return
        if any(k in msg for k in self.KEEP):
            self.q.put(("log", msg, "info"))

    def info(self, msg):
        self.debug(msg)

    def warning(self, msg):
        self.q.put(("log", ANSI_RE.sub("", msg), "warn"))

    def error(self, msg):
        msg = ANSI_RE.sub("", msg)
        self.q.put(("log", msg, "err"))
        low = msg.lower()
        if re.search(r"sign in|\b403\b|\bbot\b", low):
            self.q.put((
                "log",
                "ヒント: 設定 > ツール で yt-dlp更新 / Denoインストール、またはCookie取得ブラウザを選ぶと直ることが多いです。",
                "warn",
            ))
        elif "cookie" in low and ("database" in low or "decrypt" in low or "copy" in low):
            self.q.put(("log", "ヒント: ブラウザを完全に閉じてからやり直すか、別のブラウザを選んでください。", "warn"))
        elif "javascript runtime" in low or "n challenge" in low or re.search(r"\bdeno\b", low):
            self.q.put(("log", "ヒント: YouTubeにはJavaScriptランタイム(Deno)が必要です。設定 > ツール でDenoをインストールし、yt-dlpも更新してください。", "warn"))
        elif "ffmpeg" in low or "ffprobe" in low:
            self.q.put(("log", "ヒント: FFmpegをインストールしてください (Windows: winget install ffmpeg)", "warn"))


class Downloader(threading.Thread):
    def __init__(self, urls, cfg, q, cancel):
        super().__init__(daemon=True)
        self.urls, self.cfg, self.q, self.cancel = urls, cfg, q, cancel

    # --- yt-dlpオプション構築 ---
    def build_opts(self, target=""):
        c = self.cfg
        outdir = Path(c["outdir"])
        _, ffdir = find_ffmpeg()
        opts = {
            "windowsfilenames": True,
            "socket_timeout": 20,
            "retries": int(c.get("retries", 5)),
            "fragment_retries": int(c.get("retries", 5)),
            "concurrent_fragment_downloads": int(c.get("concurrency", 4)),
            "ignoreerrors": True,
            "noplaylist": not c["playlist"],
            "quiet": True,
            "noprogress": True,
            "logger": QLogger(self.q),
            "progress_hooks": [self.on_progress],
            "postprocessor_hooks": [self.on_pp],
        }
        if ffdir:
            opts["ffmpeg_location"] = ffdir
        opts.update(ydl_common(c))
        rate = parse_rate(c.get("ratelimit", ""))
        if rate:
            opts["ratelimit"] = rate

        group = c["group"]
        # 検索ワード指定(ytsearch1:...)は「検索結果の1件目」なので、連番や検索語名のフォルダは付けない
        is_search = bool(SEARCH_RE.match(target))
        idx = "" if is_search else "%(playlist_index&{} - |)s"
        album = "%(uploader,channel|Unknown)s" if is_search else "%(playlist_title,uploader,channel|Unknown)s"

        if c["kind"] == "audio":
            codec = AUDIO_FORMATS[c["format"]]
            folder = outdir / "Music"
            tmpl = (folder / album / f"{idx}%(title)s.%(ext)s") if group \
                else (folder / f"{idx}%(title)s.%(ext)s")
            pp = [{"key": "FFmpegExtractAudio", "preferredcodec": codec}]
            if codec not in LOSSLESS:
                pp[0]["preferredquality"] = c["quality"].replace("k", "")
            opts["format"] = "bestaudio[ext=m4a]/bestaudio/best" if codec == "m4a" else "bestaudio/best"
            opts["outtmpl"] = str(tmpl)
            if c["embed"] and codec != "wav":
                opts["writethumbnail"] = True
                pp += [
                    {"key": "FFmpegThumbnailsConvertor", "format": "jpg", "when": "before_dl"},
                    {"key": "FFmpegMetadata", "add_metadata": True},
                    {"key": "EmbedThumbnail", "already_have_thumbnail": False},
                ]
            else:
                pp.append({"key": "FFmpegMetadata", "add_metadata": True})
            opts["postprocessors"] = pp
        else:
            folder = outdir / "Video"
            opts["outtmpl"] = str(folder / f"{idx}%(title)s.%(ext)s")
            # H.264 + AAC のMP4を優先 (スマホ/ウォークマン等で再生しやすい)。再エンコードしないので速い
            sort = ["vcodec:h264", "acodec:aac", "ext:mp4:m4a"]
            if c["quality"] != "最高画質":
                sort.insert(0, f"res:{c['quality'].replace('p', '')}")
            else:
                sort.insert(0, "res")
            opts["format"] = "bv*+ba/b"
            opts["format_sort"] = sort
            opts["merge_output_format"] = "mp4"
            opts["postprocessors"] = [{"key": "FFmpegMetadata", "add_metadata": True}]
            if c["embed"]:
                opts["writethumbnail"] = True
                opts["postprocessors"] = [
                    {"key": "FFmpegThumbnailsConvertor", "format": "jpg", "when": "before_dl"},
                    {"key": "FFmpegMetadata", "add_metadata": True},
                    {"key": "EmbedThumbnail", "already_have_thumbnail": False},
                ]
        return opts

    # --- フック ---
    def on_progress(self, d):
        if self.cancel.is_set():
            raise Cancelled()
        info = d.get("info_dict") or {}
        idx, n = info.get("playlist_index"), info.get("n_entries")
        prefix = f"[{idx}/{n}] " if idx and n else ""
        title = f"{prefix}{info.get('title', '')}"
        st = d.get("status")
        if st == "downloading":
            total = d.get("total_bytes") or d.get("total_bytes_estimate")
            done = d.get("downloaded_bytes") or 0
            frac = (done / total) if total else 0
            stats = f"{frac * 100:5.1f}%   ·   {fmt_size(d.get('speed'))}/s   ·   残り {fmt_eta(d.get('eta'))}"
            self.q.put(("progress", frac, title, stats))
        elif st == "finished":
            self.q.put(("progress", 1.0, title, "ダウンロード完了（後処理中…）"))

    def on_pp(self, d):
        if self.cancel.is_set():
            raise Cancelled()
        if d.get("status") == "started":
            self.q.put(("status", f"処理中: {d.get('postprocessor', '')}"))

    # --- 実行 ---
    def run(self):
        ok = fail = 0
        n = len(self.urls)
        cancelled = False
        try:
            for i, raw in enumerate(self.urls, 1):
                if self.cancel.is_set():
                    cancelled = True
                    break
                target = normalize_input(raw)
                if not target:
                    continue
                self.q.put(("overall", i, n))
                self.q.put(("log", f"▶ ({i}/{n}) {raw}", "head"))
                try:
                    with yt_dlp.YoutubeDL(self.build_opts(target)) as ydl:
                        ret = ydl.download([target])
                    if ret == 0:
                        ok += 1
                        self.q.put(("log", "✔ 完了", "ok"))
                    else:
                        fail += 1
                        self.q.put(("log", "✖ 一部または全部の取得に失敗しました", "err"))
                except yt_dlp.utils.DownloadCancelled:  # Cancelled を含む
                    cancelled = True
                    self.q.put(("log", "■ キャンセルしました", "warn"))
                    break
                except Exception as e:
                    fail += 1
                    self.q.put(("log", f"✖ エラー: {e}", "err"))
        except Exception as e:
            self.q.put(("log", f"✖ 予期しないエラー: {e}", "err"))
        finally:
            # 何があってもUIを「実行中」のままにしない
            self.q.put(("done", ok, fail, cancelled))


# ───────────────────────── オンライン検索 ─────────────────────────
SEARCH_KEYS = {"YouTube": "ytsearch", "SoundCloud": "scsearch", "ニコニコ": "nicosearch"}
SEARCH_SOURCES = ["YouTube", "SoundCloud", "ニコニコ", "すべて"]


class _Silent:
    def debug(self, msg):
        pass

    info = warning = error = debug


def search_result(e, label):
    if not e:
        return None
    url = e.get("webpage_url") or e.get("url")
    if not url or not str(url).startswith("http"):
        if label == "YouTube" and e.get("id"):
            url = f"https://www.youtube.com/watch?v={e['id']}"
        else:
            return None
    thumb = None
    cands = [t for t in (e.get("thumbnails") or []) if t.get("url")]
    if cands:
        good = [t for t in cands if 120 <= (t.get("width") or 0) <= 500]
        thumb = (good or cands)[0]["url"]
    thumb = thumb or e.get("thumbnail")
    if not thumb and "youtube.com/watch" in url and e.get("id"):
        thumb = f"https://i.ytimg.com/vi/{e['id']}/mqdefault.jpg"
    return {"url": url, "title": e.get("title") or url, "dur": e.get("duration"),
            "uploader": clean_artist(e.get("uploader") or e.get("channel") or ""),
            "views": e.get("view_count"), "thumb": thumb, "src": label}


def online_search(text, labels, n, cfg):
    """サイトごとに並列検索して、結果を交互に混ぜて返す"""
    out = {}

    def one(label):
        o = {"quiet": True, "no_warnings": True, "extract_flat": True, "skip_download": True,
             "ignoreerrors": True, "socket_timeout": 12, "logger": _Silent()}
        o.update(ydl_common(cfg))
        try:
            with yt_dlp.YoutubeDL(o) as ydl:
                info = ydl.extract_info(f"{SEARCH_KEYS[label]}{n}:{text}", download=False)
            out[label] = [r for r in (search_result(e, label) for e in (info or {}).get("entries") or []) if r]
        except Exception:
            out[label] = []

    ths = [threading.Thread(target=one, args=(s,), daemon=True) for s in labels]
    for t in ths:
        t.start()
    for t in ths:
        t.join(25)
    lists = [out.get(s, []) for s in labels]
    merged, seen = [], set()
    for i in range(max((len(x) for x in lists), default=0)):
        for lst in lists:
            if i < len(lst) and lst[i]["url"] not in seen:
                seen.add(lst[i]["url"])
                merged.append(lst[i])
    return merged


def remote_track(r):
    """検索結果(dict)をプレーヤー用のトラックに変換"""
    return {"path": r["url"], "title": r["title"], "artist": r.get("uploader") or "", "album": "", "albumartist": "",
            "dur": r.get("dur") or 0, "track": 0, "year": "", "mtime": 0, "remote": True, "thumb": r.get("thumb"),
            "src": r.get("src", ""), "views": r.get("views")}


# ───────────────────────── 共通ウィジェット ─────────────────────────
def is_inside(widget, w):
    while w is not None:
        if w is widget:
            return True
        w = getattr(w, "master", None)
    return False


def forward_wheel(widget, e):
    """内側のウィジェット上のホイール操作を、外側のスクロール領域へ渡す"""
    w = widget
    while w is not None:
        c = getattr(w, "_parent_canvas", None)
        if c is not None:
            d = -1 if (getattr(e, "num", 0) == 4 or getattr(e, "delta", 0) > 0) else 1
            c.yview_scroll(d * 3, "units")
            return "break"
        w = getattr(w, "master", None)
    return None


def icon_btn(parent, text, command, size=18, width=38, color=TEXT, hover=HOVER, **kw):
    return ctk.CTkButton(parent, text=text, width=width, height=width, corner_radius=width // 2, fg_color="transparent",
                         hover_color=hover, text_color=color, font=F(size, "bold"), command=command, **kw)


class Sidebar(ctk.CTkFrame):
    ITEMS = [("search", "⌕", "検索"), ("home", "⌂", "ホーム"), ("songs", "♪", "曲"), ("albums", "◉", "アルバム"),
             ("artists", "☺", "アーティスト"), ("playlists", "≡", "プレイリスト"),
             ("download", "↓", "ダウンロード"), ("settings", "⚙", "設定")]

    def __init__(self, master, app):
        super().__init__(master, width=224, fg_color=SIDEBAR, corner_radius=0)
        self.app = app
        self.grid_propagate(False)
        logo = ctk.CTkFrame(self, fg_color="transparent")
        logo.pack(fill="x", padx=20, pady=(24, 22))
        ctk.CTkLabel(logo, text="♪", width=36, height=36, corner_radius=12, fg_color=ACCENT, text_color="white",
                     font=F(20, "bold")).pack(side="left")
        ctk.CTkLabel(logo, text=APP_NAME, font=F(19, "bold"), text_color=TEXT).pack(side="left", padx=12)
        self.btns = {}
        for key, icon, text in self.ITEMS:
            if key == "download":
                ctk.CTkFrame(self, height=1, fg_color=CARD_2).pack(fill="x", padx=22, pady=10)
            b = ctk.CTkButton(self, text=f"  {icon}   {text}", anchor="w", height=42, corner_radius=12,
                              fg_color="transparent", hover_color=CARD_2, text_color=MUTED, font=F(14, "bold"),
                              command=lambda k=key: app.show(k))
            b.pack(fill="x", padx=12, pady=2)
            self.btns[key] = b
        self.badge = ctk.CTkLabel(self, text="", font=F(11), text_color=MUTED, justify="left")
        self.badge.pack(side="bottom", anchor="w", padx=22, pady=18)

    def highlight(self, key):
        for k, b in self.btns.items():
            b.configure(fg_color=CARD_2 if k == key else "transparent", text_color=TEXT if k == key else MUTED)

    def set_stats(self, text):
        self.badge.configure(text=text)

    def mark_update(self, on):
        self.btns["settings"].configure(text="  ⚙   設定" + ("  ●" if on else ""))


class PlayerBar(ctk.CTkFrame):
    def __init__(self, master, app):
        super().__init__(master, height=96, fg_color=SIDEBAR, corner_radius=0)
        self.app = app
        self.seeking = False
        self.grid_propagate(False)
        self.grid_columnconfigure(0, weight=1, uniform="b")
        self.grid_columnconfigure(1, weight=2, uniform="b")
        self.grid_columnconfigure(2, weight=1, uniform="b")
        self.grid_rowconfigure(0, weight=1)

        # 左: ジャケット/タイトル
        left = ctk.CTkFrame(self, fg_color="transparent")
        left.grid(row=0, column=0, sticky="nsew", padx=(18, 8), pady=10)
        self.cover = ctk.CTkLabel(left, text="", width=64, height=64, image=app.placeholder_img(64, "-", False, 0.12))
        self.cover.pack(side="left")
        info = ctk.CTkFrame(left, fg_color="transparent")
        info.pack(side="left", padx=12, fill="x", expand=True)
        self.title = ctk.CTkLabel(info, text="再生していません", font=F(14, "bold"), text_color=TEXT, anchor="w")
        self.title.pack(anchor="w", fill="x")
        self.artist = ctk.CTkLabel(info, text="", font=F(12), text_color=MUTED, anchor="w", cursor="hand2")
        self.artist.pack(anchor="w", fill="x")
        self.artist.bind("<Button-1>", lambda e: app.open_current_artist())
        self.fav = icon_btn(left, "♡", app.toggle_fav_current, size=18, width=34)
        self.fav.pack(side="left")
        for w in (self.cover, self.title):
            w.bind("<Button-1>", lambda e: app.show("now"))
            w.configure(cursor="hand2")

        # 中央: 操作 + シーク
        mid = ctk.CTkFrame(self, fg_color="transparent")
        mid.grid(row=0, column=1, sticky="nsew", pady=8)
        mid.grid_columnconfigure(0, weight=1)
        ctrl = ctk.CTkFrame(mid, fg_color="transparent")
        ctrl.grid(row=0, column=0)
        self.b_shuf = icon_btn(ctrl, "⇄", app.toggle_shuffle, size=17)
        self.b_prev = icon_btn(ctrl, "⏮", app.prev, size=17)
        self.b_play = ctk.CTkButton(ctrl, text="▶", width=46, height=46, corner_radius=23, fg_color="white",
                                    hover_color="#d7d9e4", text_color="#111", font=F(18, "bold"), command=app.toggle_play)
        self.b_next = icon_btn(ctrl, "⏭", app.next, size=17)
        self.b_rep = icon_btn(ctrl, "↻", app.cycle_repeat, size=17)
        for b in (self.b_shuf, self.b_prev, self.b_play, self.b_next, self.b_rep):
            b.pack(side="left", padx=5)
        seek = ctk.CTkFrame(mid, fg_color="transparent")
        seek.grid(row=1, column=0, sticky="ew", padx=10)
        seek.grid_columnconfigure(1, weight=1)
        self.t_cur = ctk.CTkLabel(seek, text="0:00", width=44, font=F(11), text_color=MUTED)
        self.t_cur.grid(row=0, column=0)
        self.slider = ctk.CTkSlider(seek, from_=0, to=1, height=14, progress_color=ACCENT, button_color="white",
                                    button_hover_color="white", fg_color=CARD_2, command=self._on_slide)
        self.slider.set(0)
        self.slider.grid(row=0, column=1, sticky="ew", padx=6)
        self.slider.bind("<ButtonPress-1>", self._press, add="+")
        self.slider.bind("<ButtonRelease-1>", self._release, add="+")
        self.t_end = ctk.CTkLabel(seek, text="0:00", width=44, font=F(11), text_color=MUTED)
        self.t_end.grid(row=0, column=2)

        # 右: キュー/歌詞/音量
        right = ctk.CTkFrame(self, fg_color="transparent")
        right.grid(row=0, column=2, sticky="nse", padx=(8, 18))
        self.b_dl = icon_btn(right, "↓", app.download_current, size=17, color=ACCENT)
        self.b_lyr = icon_btn(right, "歌", lambda: app.show("now", mode="lyrics"), size=14)
        self.b_q = icon_btn(right, "≡", lambda: app.show("now", mode="queue"), size=18)
        self.b_lyr.pack(side="left", padx=2)
        self.b_q.pack(side="left", padx=2)
        self.b_vol = icon_btn(right, "♬", app.toggle_mute, size=15, width=32)
        self.b_vol.pack(side="left", padx=(8, 0))
        self.vol = ctk.CTkSlider(right, from_=0, to=1, width=100, height=14, progress_color=ACCENT, button_color="white",
                                 button_hover_color="white", fg_color=CARD_2, command=app.set_volume)
        self.vol.set(app.engine.volume)
        self.vol.pack(side="left", padx=(2, 0))

    def _on_slide(self, v):
        if self.seeking and self.app.cur_dur():
            self.t_cur.configure(text=fmt_dur(v * self.app.cur_dur()) or "0:00")

    def _press(self, e):
        self.seeking = True

    def _release(self, e):
        self.seeking = False
        self.app.seek_frac(self.slider.get())

    def set_track(self, t):
        if t and t.get("remote"):
            self.b_dl.pack(side="left", padx=2, before=self.b_lyr)
        else:
            self.b_dl.pack_forget()
        if not t:
            self.title.configure(text="再生していません")
            self.artist.configure(text="")
            self.fav.configure(text="♡", text_color=TEXT)
            return
        self.title.configure(text=t["title"])
        self.artist.configure(text=t["artist"])
        self.set_fav(not t.get("remote") and self.app.user.is_fav(t["path"]))

    def set_fav(self, on):
        self.fav.configure(text="♥" if on else "♡", text_color=ACCENT if on else TEXT)

    def set_playing(self, playing):
        self.b_play.configure(text="⏸" if playing else "▶")

    def set_progress(self, pos, dur):
        if not self.seeking:
            self.slider.set(min(1, pos / dur) if dur else 0)
            self.t_cur.configure(text=fmt_dur(pos) or "0:00")
        self.t_end.configure(text=fmt_dur(dur) or "0:00")

    def set_modes(self, shuffle, repeat):
        self.b_shuf.configure(text_color=ACCENT if shuffle else TEXT)
        self.b_rep.configure(text="↻¹" if repeat == "one" else "↻", text_color=ACCENT if repeat != "off" else TEXT)


class TrackTable(ctk.CTkFrame):
    COLS = {"idx": ("#", 54, "center"), "title": ("タイトル", 340, "w"), "artist": ("アーティスト", 190, "w"),
            "album": ("アルバム", 190, "w"), "time": ("時間", 70, "e")}

    def __init__(self, master, app, cols=("idx", "title", "artist", "album", "time"), flat=False,
                 empty_text="曲がありません", removable=False):
        super().__init__(master, fg_color=CARD, corner_radius=16)
        self.app, self.cols, self.flat, self.removable = app, cols, flat, removable
        self.src, self.tracks = [], []
        self.sort_col, self.sort_rev = None, False
        self.playing_iid = None
        self.paths = {}
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(0, weight=1)
        self.tree = ttk.Treeview(self, columns=cols, show="headings", style="Music.Treeview", selectmode="extended")
        for c in cols:
            name, w, anchor = self.COLS[c]
            self.tree.heading(c, text=name, anchor="w" if anchor == "w" else anchor,
                              command=lambda c=c: self._sort(c))
            self.tree.column(c, width=w, minwidth=40, anchor=anchor, stretch=c in ("title", "artist", "album"))
        self.tree.tag_configure("playing", foreground=ACCENT)
        self.tree.grid(row=0, column=0, sticky="nsew", padx=(10, 0), pady=10)
        if not flat:
            sb = ctk.CTkScrollbar(self, command=self.tree.yview, fg_color="transparent")
            self.tree.configure(yscrollcommand=sb.set)
            sb.grid(row=0, column=1, sticky="ns", pady=10, padx=(2, 4))
        else:
            for ev in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                self.tree.bind(ev, lambda e: forward_wheel(self.tree, e))
        self.empty = ctk.CTkLabel(self, text=empty_text, font=F(13), text_color=MUTED)
        self.tree.bind("<Double-1>", self._activate)
        self.tree.bind("<Return>", self._activate)
        self.tree.bind("<Button-3>", self._menu)
        self.tree.bind("<Button-2>", self._menu)
        if removable:
            self.tree.bind("<Delete>", lambda e: self._remove())

    # --- データ ---
    def set_tracks(self, tracks):
        self.src = list(tracks)
        self.sort_col = None
        self.tracks = list(self.src)
        self._fill()

    def _sort(self, col):
        if col == "idx":
            self.tracks, self.sort_col = list(self.src), None
        else:
            self.sort_rev = (not self.sort_rev) if self.sort_col == col else False
            self.sort_col = col
            key = {"title": lambda t: t["title"].casefold(), "artist": lambda t: t["artist"].casefold(),
                   "album": lambda t: (t.get("album") or "").casefold(), "time": lambda t: t.get("dur") or 0}[col]
            self.tracks = sorted(self.src, key=key, reverse=self.sort_rev)
        self._fill()

    def _row_values(self, i, t, cur):
        fav = (not t.get("remote")) and self.app.user.is_fav(t["path"])
        vals = {"idx": "▶" if t["path"] == cur else str(i + 1),
                "title": ("♥ " if fav else "") + t["title"], "artist": t["artist"],
                "album": t.get("album") or "", "time": fmt_dur(t.get("dur"))}
        return [vals[c] for c in self.cols]

    def _fill(self):
        self.tree.delete(*self.tree.get_children())
        cur = self.app.current_path()
        self.paths = {}
        self.playing_iid = None
        for i, t in enumerate(self.tracks):
            playing = t["path"] == cur
            if playing and self.playing_iid is None:
                self.playing_iid = str(i)
            self.paths.setdefault(t["path"], str(i))
            self.tree.insert("", "end", iid=str(i), values=self._row_values(i, t, cur),
                             tags=("playing",) if playing else ())
        if self.flat:
            self.tree.configure(height=max(1, len(self.tracks)))
        if self.tracks:
            self.empty.place_forget()
        else:
            self.empty.place(relx=0.5, rely=0.5, anchor="center")

    def refresh_playing(self):
        cur = self.app.current_path()
        for iid in (self.playing_iid, self.paths.get(cur)):
            if iid is not None and self.tree.exists(iid):
                t = self.tracks[int(iid)]
                playing = t["path"] == cur
                self.tree.item(iid, values=self._row_values(int(iid), t, cur), tags=("playing",) if playing else ())
        self.playing_iid = self.paths.get(cur)

    def refresh_all(self):
        self._fill()

    # --- 操作 ---
    def selected(self):
        return [self.tracks[int(i)] for i in self.tree.selection() if i.isdigit() and int(i) < len(self.tracks)]

    def _activate(self, e=None):
        sel = self.tree.selection()
        if not sel:
            return
        if e is not None and getattr(e, "type", None) is not None and str(e.type) == "4":
            if self.tree.identify_region(e.x, e.y) != "cell":
                return
        self.app.play_list(self.tracks, int(sel[0]))

    def _remove(self):
        sel = self.selected()
        if sel and self.removable and callable(getattr(self, "on_remove", None)):
            self.on_remove(sel)

    def _menu(self, e):
        iid = self.tree.identify_row(e.y)
        if iid and iid not in self.tree.selection():
            self.tree.selection_set(iid)
        sel = self.selected()
        if not sel:
            return
        a, t0 = self.app, sel[0]
        m = tk.Menu(self, tearoff=0, bg=CARD_2, fg=TEXT, activebackground=ACCENT, activeforeground="white",
                    bd=0, relief="flat", font=(FONT_FAMILY, 10))
        m.add_command(label="▶  再生", command=lambda: a.play_list(self.tracks, self.tracks.index(t0)))
        m.add_command(label="次に再生", command=lambda: a.play_next(sel))
        m.add_command(label="キューに追加", command=lambda: a.add_queue(sel))
        if not t0.get("remote"):
            m.add_separator()
            m.add_command(label=("♡  お気に入りから外す" if a.user.is_fav(t0["path"]) else "♥  お気に入りに追加"),
                          command=lambda: a.toggle_fav(sel))
            pm = tk.Menu(m, tearoff=0, bg=CARD_2, fg=TEXT, activebackground=ACCENT, activeforeground="white",
                         bd=0, font=(FONT_FAMILY, 10))
            for name in a.user.playlists:
                pm.add_command(label=name, command=lambda n=name: a.add_to_playlist(n, sel))
            if a.user.playlists:
                pm.add_separator()
            pm.add_command(label="＋ 新しいプレイリスト…", command=lambda: a.new_playlist_dialog(sel))
            m.add_cascade(label="プレイリストに追加", menu=pm)
            m.add_separator()
            m.add_command(label="アーティストページへ", command=lambda: a.open_artist(t0["artist"]))
            m.add_command(label="アルバムページへ", command=lambda: a.open_album((t0["albumartist"] or t0["artist"],
                                                                         t0["album"] or "シングル")))
            m.add_command(label="歌詞を表示", command=lambda: (a.play_list(self.tracks, self.tracks.index(t0)),
                                                         a.show("now", mode="lyrics")))
            m.add_command(label="ファイルの場所を開く", command=lambda: reveal_file(t0["path"]))
        if self.removable:
            m.add_separator()
            m.add_command(label="この一覧から削除", command=self._remove)
        try:
            m.tk_popup(e.x_root, e.y_root)
        finally:
            m.grab_release()


def rrect(cv, x1, y1, x2, y2, r, **kw):
    pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2, x2 - r, y2, x1 + r, y2,
           x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
    return cv.create_polygon(pts, smooth=True, **kw)


class CardCanvas(tk.Frame):
    """アルバム/アーティスト等のカード一覧。1枚のCanvasに『見えている分だけ』描画するので、何百件あっても軽い。
    items: dict(kind='card'|'header'|'note', title, sub, tracks, command, circle, artist, text)"""
    CARD_W, IMG, PAD = 184, 156, 20
    CARD_H = 156 + 66

    def __init__(self, master, app, autoheight=False):
        super().__init__(master, bg=BG, bd=0, highlightthickness=0)
        self.app, self.autoheight = app, autoheight
        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(0, weight=1)
        self.cv = tk.Canvas(self, bg=BG, highlightthickness=0, bd=0, yscrollincrement=44)
        self.cv.grid(row=0, column=0, sticky="nsew")
        if not autoheight:
            self.sb = ctk.CTkScrollbar(self, command=self._sb, fg_color="transparent")
            self.sb.grid(row=0, column=1, sticky="ns", padx=(0, 4))
            self.cv.configure(yscrollcommand=self.sb.set)
        self.items, self.pos, self.live, self.photo = [], [], {}, {}
        self.total_h, self.width, self.hover, self.gen, self._job = 0, 0, None, 0, None
        self.f_t = tkfont.Font(root=self, family=FONT_FAMILY, size=-14, weight="bold")
        self.f_s = tkfont.Font(root=self, family=FONT_FAMILY, size=-12)
        self.f_h = tkfont.Font(root=self, family=FONT_FAMILY, size=-21, weight="bold")
        self._fit_cache = {}
        self.cv.bind("<Configure>", self._on_cfg)
        for ev in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.cv.bind(ev, self._wheel)
        self.cv.bind("<Button-1>", self._click)
        self.cv.bind("<Motion>", self._motion)
        self.cv.bind("<Leave>", lambda e: self._set_hover(None))

    # --- レイアウト ---
    def set_items(self, items):
        self.items = items
        self.gen += 1
        self.cv.delete("all")
        self.live, self.photo, self.hover = {}, {}, None
        self.cv.update_idletasks()
        self._layout()
        self.cv.yview_moveto(0)
        self._visible()

    def _layout(self):
        W = max(300, self.cv.winfo_width())
        self.width = W
        cols = max(1, (W - 2 * self.PAD) // self.CARD_W)
        y, col, self.pos = 8, 0, []
        for it in self.items:
            k = it.get("kind", "card")
            if k != "card":
                if col:
                    y += self.CARD_H
                    col = 0
                h = 54 if k == "header" else 40
                self.pos.append((self.PAD, y, W - 2 * self.PAD, h))
                y += h
                continue
            self.pos.append((self.PAD + col * self.CARD_W, y, self.CARD_W, self.CARD_H))
            col += 1
            if col >= cols:
                col, y = 0, y + self.CARD_H
        if col:
            y += self.CARD_H
        self.total_h = y + 12
        if self.autoheight:
            self.cv.configure(height=self.total_h)
        self.cv.configure(scrollregion=(0, 0, W, self.total_h))

    def _on_cfg(self, e):
        if abs(e.width - self.width) > 4:
            if self._job:
                self.after_cancel(self._job)
            self._job = self.after(70, self._relayout)
        else:
            self._visible()

    def _relayout(self):
        self._job = None
        for i in list(self.live):
            self._drop(i)
        self.gen += 1
        self._layout()
        self._visible()

    # --- 描画(見えている分だけ) ---
    def _visible(self):
        if not self.items:
            return
        if self.autoheight:
            lo, hi = -1, 10 ** 9
        else:
            top = self.cv.canvasy(0)
            lo, hi = top - 320, top + self.cv.winfo_height() + 320
        want = {i for i, (x, y, w, h) in enumerate(self.pos) if y + h >= lo and y <= hi}
        for i in [i for i in self.live if i not in want]:
            self._drop(i)
        for i in sorted(want):
            if i not in self.live:
                self._draw(i)

    def _drop(self, i):
        for cid in self.live.pop(i, []):
            self.cv.delete(cid)
        self.photo.pop(i, None)

    def _fit(self, text, font, maxw):
        k = (text, id(font), maxw)
        if k in self._fit_cache:
            return self._fit_cache[k]
        out = text
        if font.measure(text) > maxw:
            lo, hi = 0, len(text)
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if font.measure(text[:mid] + "…") <= maxw:
                    lo = mid
                else:
                    hi = mid - 1
            out = text[:lo] + "…"
        if len(self._fit_cache) > 4000:
            self._fit_cache.clear()
        self._fit_cache[k] = out
        return out

    def _draw(self, i):
        it, cv = self.items[i], self.cv
        x, y, w, h = self.pos[i]
        tag, ids = f"c{i}", []
        k = it.get("kind", "card")
        if k == "header":
            ids.append(cv.create_text(x, y + h - 12, anchor="sw", text=it["text"], fill=TEXT, font=self.f_h, tags=(tag, "hdr")))
        elif k == "note":
            ids.append(cv.create_text(x, y + 8, anchor="nw", text=it["text"], fill=MUTED, font=self.f_s, tags=(tag, "hdr")))
        else:
            circle, s = bool(it.get("circle")), self.IMG
            bw = w - 10
            ids.append(rrect(cv, x, y, x + bw, y + h - 6, 14, fill=BG, outline="", tags=(tag, "bg")))
            ph = self.app.tk_placeholder(s, it["title"], circle)
            img = cv.create_image(x + (bw - s) // 2, y + 8, anchor="nw", image=ph, tags=(tag,))
            self.photo[i] = ph
            ids.append(img)
            self.live[i] = ids  # ジャケットが即時に取れる場合に備えて、先に登録しておく
            tx, anc = (x + bw // 2, "center") if circle else (x + 12, "w")
            ids.append(cv.create_text(tx, y + s + 24, anchor=anc, text=self._fit(it["title"], self.f_t, bw - 24),
                                      fill=TEXT, font=self.f_t, tags=(tag,)))
            ids.append(cv.create_text(tx, y + s + 46, anchor=anc, text=self._fit(it.get("sub", ""), self.f_s, bw - 24),
                                      fill=MUTED, font=self.f_s, tags=(tag,)))
            gen = self.gen
            self.app.cover_pil(it.get("tracks") or [], s, it.get("artist"),
                               lambda im, i=i, img=img, gen=gen, circle=circle: self._set_cover(i, gen, img, im, circle))
        self.live[i] = ids

    def _set_cover(self, i, gen, img, im, circle):
        if gen != self.gen or i not in self.live or im is None:
            return
        try:
            ph = self.app.tk_cover(im, self.IMG, circle)
            self.cv.itemconfig(img, image=ph)
            self.photo[i] = ph
        except Exception:
            pass

    # --- 操作 ---
    def _idx_at_current(self):
        ids = self.cv.find_withtag("current")
        if not ids:
            return None
        for t in self.cv.gettags(ids[0]):
            if t[0] == "c" and t[1:].isdigit():
                return int(t[1:])
        return None

    def _is_card(self, i):
        return i is not None and i < len(self.items) and self.items[i].get("kind", "card") == "card"

    def _set_hover(self, i):
        if i == self.hover:
            return
        for idx, col in ((self.hover, BG), (i, CARD)):
            if idx in self.live:
                for cid in self.live[idx]:
                    if "bg" in self.cv.gettags(cid):
                        self.cv.itemconfig(cid, fill=col)
        self.hover = i
        self.cv.configure(cursor="hand2" if i is not None else "")

    def _motion(self, e):
        i = self._idx_at_current()
        self._set_hover(i if self._is_card(i) else None)

    def _click(self, e):
        i = self._idx_at_current()
        if self._is_card(i) and self.items[i].get("command"):
            self.items[i]["command"]()

    def _wheel(self, e):
        if self.autoheight:
            return forward_wheel(self, e)
        d = -1 if (getattr(e, "num", 0) == 4 or getattr(e, "delta", 0) > 0) else 1
        self.cv.yview_scroll(d * 3, "units")
        self._visible()

    def _sb(self, *a):
        self.cv.yview(*a)
        self._visible()


# ───────────────────────── ページ: ライブラリ系 ─────────────────────────
class _EntryGetter:
    def __init__(self, entry):
        self.entry = entry

    def get(self):
        return self.entry.get()


def page_title(parent, text, sub=""):
    f = ctk.CTkFrame(parent, fg_color="transparent")
    ctk.CTkLabel(f, text=text, font=F(28, "bold"), text_color=TEXT).pack(side="left")
    if sub:
        ctk.CTkLabel(f, text=sub, font=F(13), text_color=MUTED).pack(side="left", padx=14, pady=(10, 0))
    return f


def pill_btn(parent, text, command, primary=False, width=None, **kw):
    return ctk.CTkButton(parent, text=text, command=command, height=38, corner_radius=19,
                         width=width or 110, font=F(13, "bold"),
                         fg_color=ACCENT if primary else CARD_2, hover_color=ACCENT_H if primary else HOVER,
                         text_color="white" if primary else TEXT, **kw)


class EmptyLibrary(ctk.CTkFrame):
    def __init__(self, master, app):
        super().__init__(master, fg_color=CARD, corner_radius=20)
        ctk.CTkLabel(self, text="♪", font=F(46, "bold"), text_color=ACCENT).pack(pady=(34, 0))
        ctk.CTkLabel(self, text="ライブラリはまだ空です", font=F(20, "bold"), text_color=TEXT).pack(pady=(4, 6))
        ctk.CTkLabel(self, text="検索して聴くか、曲をダウンロード/音楽フォルダを追加すると、ここに並びます。",
                     font=F(13), text_color=MUTED).pack()
        row = ctk.CTkFrame(self, fg_color="transparent")
        row.pack(pady=24)
        pill_btn(row, "⌕ 検索して聴く", lambda: app.show("search"), primary=True, width=150).pack(side="left", padx=6)
        pill_btn(row, "↓ ダウンロード", lambda: app.show("download"), width=150).pack(side="left", padx=6)
        pill_btn(row, "フォルダを追加…", app.add_library_folder, width=150).pack(side="left", padx=6)


class HomePage(ctk.CTkFrame):
    def __init__(self, master, app):
        super().__init__(master, fg_color=BG, corner_radius=0)
        self.app = app
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)
        self.head = ctk.CTkFrame(self, fg_color="transparent")
        self.head.grid(row=0, column=0, sticky="ew")
        self.canvas = CardCanvas(self, app)
        self.canvas.grid(row=1, column=0, sticky="nsew", padx=(12, 0), pady=(6, 0))

    def on_show(self, **kw):
        for w in self.head.winfo_children():
            w.destroy()
        a, lib = self.app, self.app.lib
        h = time.localtime().tm_hour
        greet = "おはようございます" if 5 <= h < 11 else "こんにちは" if 11 <= h < 18 else "こんばんは"
        page_title(self.head, greet).pack(anchor="w", padx=32, pady=(18, 4))
        if not lib.tracks:
            EmptyLibrary(self.head, a).pack(fill="x", padx=32, pady=14)
            self.canvas.set_items([])
            return
        chips = ctk.CTkFrame(self.head, fg_color="transparent")
        chips.pack(anchor="w", padx=32, pady=(0, 4))
        for text in (f"{len(lib.tracks)} 曲", f"{len(lib.albums)} アルバム", f"{len(lib.artists)} アーティスト",
                     fmt_total(lib.total_duration())):
            ctk.CTkLabel(chips, text=text, font=F(12, "bold"), text_color=MUTED, fg_color=CARD, corner_radius=14,
                         height=28, width=70).pack(side="left", padx=(0, 8))
        acts = ctk.CTkFrame(self.head, fg_color="transparent")
        acts.pack(anchor="w", padx=32, pady=(8, 2))
        pill_btn(acts, "▶ すべてシャッフル", lambda: a.play_list(lib.tracks, 0, shuffle=True), primary=True, width=170).pack(side="left")
        pill_btn(acts, "オンラインで探す", lambda: a.show("search"), width=150).pack(side="left", padx=8)
        recent = [lib.by_path[p] for p in a.user.d["recent"] if p in lib.by_path][:12]
        top = sorted([t for t in lib.tracks if a.user.plays(t["path"])], key=lambda t: -a.user.plays(t["path"]))[:12]
        added = sorted(lib.tracks, key=lambda t: -t["mtime"])[:12]
        favs = [lib.by_path[p] for p in sorted(a.user.fav) if p in lib.by_path][:12]
        items = []
        for title, tracks in (("最近再生した曲", recent), ("よく聴く曲", top), ("お気に入り", favs), ("最近追加した曲", added)):
            if tracks:
                items.append({"kind": "header", "text": title})
                items += [{"title": t["title"], "sub": t["artist"], "tracks": [t],
                           "command": lambda pool=tracks, i=i: a.play_list(pool, i)} for i, t in enumerate(tracks)]
        self.canvas.set_items(items)


class SongsPage(ctk.CTkFrame):
    FILTERS = ["すべて", "お気に入り", "最近再生", "よく聴く"]

    def __init__(self, master, app):
        super().__init__(master, fg_color=BG, corner_radius=0)
        self.app = app
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(2, weight=1)
        page_title(self, "曲").grid(row=0, column=0, sticky="w", padx=32, pady=(28, 6))
        bar = ctk.CTkFrame(self, fg_color="transparent")
        bar.grid(row=1, column=0, sticky="ew", padx=32, pady=(4, 10))
        self.entry = ctk.CTkEntry(bar, width=300, height=38, corner_radius=19, fg_color=CARD,
                                  border_width=0, placeholder_text="曲・アーティスト・アルバムを検索", font=F(13))
        self.entry.pack(side="left")
        self.entry.bind("<KeyRelease>", lambda e: self._apply())
        self.q = _EntryGetter(self.entry)
        self.flt = ctk.CTkSegmentedButton(bar, values=self.FILTERS, command=lambda v: self._apply(), height=34,
                                          fg_color=CARD, selected_color=ACCENT, selected_hover_color=ACCENT_H,
                                          unselected_color=CARD, unselected_hover_color=CARD_2, font=F(12, "bold"))
        self.flt.set("すべて")
        self.flt.pack(side="left", padx=12)
        pill_btn(bar, "▶ 再生", lambda: self._play(False), primary=True, width=90).pack(side="right")
        pill_btn(bar, "⇄ シャッフル", lambda: self._play(True), width=120).pack(side="right", padx=8)
        self.table = TrackTable(self, app)
        self.table.grid(row=2, column=0, sticky="nsew", padx=32, pady=(0, 18))
        self.shown = []

    def on_show(self, **kw):
        self._apply()

    def _apply(self):
        a, lib = self.app, self.app.lib
        q = self.q.get().strip().casefold()
        f = self.flt.get()
        if f == "お気に入り":
            tracks = [t for t in lib.tracks if a.user.is_fav(t["path"])]
        elif f == "最近再生":
            tracks = [lib.by_path[p] for p in a.user.d["recent"] if p in lib.by_path]
        elif f == "よく聴く":
            tracks = sorted([t for t in lib.tracks if a.user.plays(t["path"])], key=lambda t: -a.user.plays(t["path"]))
        else:
            tracks = list(lib.tracks)
        if q:
            tracks = [t for t in tracks if q in (t["title"] + " " + t["artist"] + " " + (t.get("album") or "")).casefold()]
        self.shown = tracks
        self.table.empty.configure(text="該当する曲がありません" if lib.tracks else "ライブラリが空です。ダウンロードするか、設定でフォルダを追加してください")
        self.table.set_tracks(tracks)

    def _play(self, shuffle):
        if self.shown:
            self.app.play_list(self.shown, 0, shuffle=shuffle)


class AlbumsPage(ctk.CTkFrame):
    def __init__(self, master, app):
        super().__init__(master, fg_color=BG, corner_radius=0)
        self.app = app
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(2, weight=1)
        page_title(self, "アルバム").grid(row=0, column=0, sticky="w", padx=32, pady=(28, 6))
        e = ctk.CTkEntry(self, width=300, height=38, corner_radius=19, fg_color=CARD, border_width=0,
                         placeholder_text="アルバム・アーティストを検索", font=F(13))
        e.grid(row=1, column=0, sticky="w", padx=32, pady=(4, 8))
        e.bind("<KeyRelease>", lambda ev: self._apply())
        self.q = _EntryGetter(e)
        self.grid_ = CardCanvas(self, app)
        self.grid_.grid(row=2, column=0, sticky="nsew", padx=22, pady=(0, 10))

    def on_show(self, **kw):
        self._apply()

    def _apply(self):
        a, q = self.app, self.q.get().strip().casefold()
        items = []
        for key in sorted(a.lib.albums, key=lambda k: (k[0].casefold(), k[1].casefold())):
            if q and q not in (key[0] + " " + key[1]).casefold():
                continue
            ts = a.lib.albums[key]
            items.append({"title": key[1], "sub": f"{key[0]} · {len(ts)}曲", "tracks": ts,
                          "command": lambda k=key: a.open_album(k)})
        self.grid_.set_items(items)


class ArtistsPage(ctk.CTkFrame):
    def __init__(self, master, app):
        super().__init__(master, fg_color=BG, corner_radius=0)
        self.app = app
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(2, weight=1)
        page_title(self, "アーティスト").grid(row=0, column=0, sticky="w", padx=32, pady=(28, 6))
        e = ctk.CTkEntry(self, width=300, height=38, corner_radius=19, fg_color=CARD, border_width=0,
                         placeholder_text="アーティストを検索", font=F(13))
        e.grid(row=1, column=0, sticky="w", padx=32, pady=(4, 8))
        e.bind("<KeyRelease>", lambda ev: self._apply())
        self.q = _EntryGetter(e)
        self.grid_ = CardCanvas(self, app)
        self.grid_.grid(row=2, column=0, sticky="nsew", padx=22, pady=(0, 10))

    def on_show(self, **kw):
        self._apply()

    def _apply(self):
        a, q = self.app, self.q.get().strip().casefold()
        items = []
        for name in sorted(a.lib.artists, key=str.casefold):
            if q and q not in name.casefold():
                continue
            ts = a.lib.artists[name]
            items.append({"title": name, "sub": f"{len(ts)}曲", "tracks": ts, "circle": True, "artist": name,
                          "command": lambda n=name: a.open_artist(n)})
        self.grid_.set_items(items)


class PlaylistsPage(ctk.CTkFrame):
    def __init__(self, master, app):
        super().__init__(master, fg_color=BG, corner_radius=0)
        self.app = app
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)
        top = ctk.CTkFrame(self, fg_color="transparent")
        top.grid(row=0, column=0, sticky="ew", padx=32, pady=(28, 8))
        page_title(top, "プレイリスト").pack(side="left")
        pill_btn(top, "＋ 新規作成", lambda: app.new_playlist_dialog(None), primary=True, width=130).pack(side="right")
        self.grid_ = CardCanvas(self, app)
        self.grid_.grid(row=1, column=0, sticky="nsew", padx=22, pady=(0, 10))

    def on_show(self, **kw):
        a = self.app
        items = []
        favs = [a.lib.by_path[p] for p in sorted(a.user.fav) if p in a.lib.by_path]
        items.append({"title": "お気に入り", "sub": f"{len(favs)}曲", "tracks": favs,
                      "command": lambda: a.show("detail", kind="favorites")})
        for name, paths in a.user.playlists.items():
            ts = [a.lib.by_path[p] for p in paths if p in a.lib.by_path]
            items.append({"title": name, "sub": f"{len(ts)}曲", "tracks": ts,
                          "command": lambda n=name: a.show("detail", kind="playlist", key=n)})
        self.grid_.set_items(items)


class DetailPage(ctk.CTkScrollableFrame):
    """アルバム / アーティスト / プレイリスト / お気に入り の詳細"""

    def __init__(self, master, app):
        super().__init__(master, fg_color=BG, corner_radius=0)
        self.app = app
        self.grid_columnconfigure(0, weight=1)
        self.tables = []

    def refresh_playing(self):
        for t in self.tables:
            try:
                t.refresh_playing()
            except Exception:
                pass

    def on_show(self, kind="album", key=None, **kw):
        for w in self.winfo_children():
            w.destroy()
        self.tables = []
        a, lib = self.app, self.app.lib
        self.kind, self.key = kind, key
        if kind == "album":
            tracks = sorted(lib.albums.get(key, []), key=lambda t: (t["track"] or 999, t["title"].casefold()))
            title, kicker = key[1], "アルバム"
            meta = f"{key[0]} · {len(tracks)}曲 · {fmt_total(lib.total_duration(tracks))}" + \
                   (f" · {tracks[0]['year']}" if tracks and tracks[0]["year"] else "")
            circle, artist = False, None
        elif kind == "artist":
            tracks = list(lib.artists.get(key, []))
            albums = {(t["albumartist"] or t["artist"], t["album"] or "シングル") for t in tracks}
            plays = sum(a.user.plays(t["path"]) for t in tracks)
            title, kicker = key, "アーティスト"
            meta = f"{len(tracks)}曲 · {len(albums)}アルバム · {fmt_total(lib.total_duration(tracks))}" + \
                   (f" · 再生 {plays}回" if plays else "")
            circle, artist = True, key
        elif kind == "favorites":
            tracks = [lib.by_path[p] for p in sorted(a.user.fav) if p in lib.by_path]
            title, kicker, circle, artist = "お気に入り", "プレイリスト", False, None
            meta = f"{len(tracks)}曲 · {fmt_total(lib.total_duration(tracks))}"
        else:
            tracks = [lib.by_path[p] for p in a.user.playlists.get(key, []) if p in lib.by_path]
            title, kicker, circle, artist = key, "プレイリスト", False, None
            meta = f"{len(tracks)}曲 · {fmt_total(lib.total_duration(tracks))}"
        self.tracks = tracks

        head = ctk.CTkFrame(self, fg_color="transparent")
        head.grid(row=0, column=0, sticky="ew", padx=32, pady=(24, 10))
        pill_btn(head, "← 戻る", a.back, width=80).grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 14))
        size = 200
        img = ctk.CTkLabel(head, text="", width=size, height=size, image=a.placeholder_img(size, title, circle))
        img.grid(row=1, column=0, rowspan=2, sticky="nw")
        a.load_cover(img, tracks, size, circle, artist)
        info = ctk.CTkFrame(head, fg_color="transparent")
        info.grid(row=1, column=1, sticky="nsw", padx=26)
        ctk.CTkLabel(info, text=kicker, font=F(12, "bold"), text_color=ACCENT).pack(anchor="w", pady=(28, 0))
        ctk.CTkLabel(info, text=title, font=F(34, "bold"), text_color=TEXT, anchor="w", justify="left",
                     wraplength=620).pack(anchor="w")
        ctk.CTkLabel(info, text=meta, font=F(13), text_color=MUTED).pack(anchor="w", pady=(2, 12))
        btns = ctk.CTkFrame(info, fg_color="transparent")
        btns.pack(anchor="w")
        pill_btn(btns, "▶ 再生", lambda: a.play_list(tracks, 0) if tracks else None, primary=True, width=110).pack(side="left")
        pill_btn(btns, "⇄ シャッフル", lambda: a.play_list(tracks, 0, shuffle=True) if tracks else None, width=130).pack(side="left", padx=8)
        pill_btn(btns, "キューに追加", lambda: a.add_queue(tracks), width=120).pack(side="left")
        if kind == "artist":
            pill_btn(btns, "オンラインで探す", lambda: a.open_search(key), width=140).pack(side="left", padx=8)
        if kind == "playlist":
            pill_btn(btns, "名前変更", lambda: a.rename_playlist_dialog(key), width=100).pack(side="left", padx=8)
            pill_btn(btns, "削除", lambda: a.delete_playlist_dialog(key), width=80).pack(side="left")
        r = 1
        if kind == "artist":
            top = sorted(tracks, key=lambda t: (-a.user.plays(t["path"]), t["title"].casefold()))[:5]
            r = self._section("人気の曲", top, tracks, r, cols=("idx", "title", "album", "time"))
            albums = {}
            for t in tracks:
                albums.setdefault((t["albumartist"] or t["artist"], t["album"] or "シングル"), []).append(t)
            if albums:
                ctk.CTkLabel(self, text="アルバム", font=F(18, "bold"), text_color=TEXT).grid(row=r, column=0, sticky="w", padx=32, pady=(20, 4))
                cc = CardCanvas(self, a, autoheight=True)
                cc.grid(row=r + 1, column=0, sticky="ew", padx=24)
                cc.set_items([{"title": k[1], "sub": f"{len(ts)}曲", "tracks": ts, "command": lambda k=k: a.open_album(k)}
                              for k, ts in sorted(albums.items(), key=lambda kv: kv[0][1].casefold())])
                r += 2
            self._section("すべての曲", tracks, tracks, r)
        else:
            self._section(None, tracks, tracks, r, cols=("idx", "title", "artist", "album", "time") if kind != "album"
                          else ("idx", "title", "artist", "time"), removable=(kind in ("playlist", "favorites")))

    def _section(self, title, shown, queue_tracks, r, cols=("idx", "title", "artist", "album", "time"), removable=False):
        if title:
            ctk.CTkLabel(self, text=title, font=F(18, "bold"), text_color=TEXT).grid(row=r, column=0, sticky="w", padx=32, pady=(20, 4))
            r += 1
        tbl = TrackTable(self, self.app, cols=cols, flat=True, removable=removable,
                         empty_text="曲がありません" if self.kind != "playlist" else "曲を追加するには、曲を右クリック → プレイリストに追加")
        tbl.grid(row=r, column=0, sticky="ew", padx=32, pady=(6, 24))
        tbl.set_tracks(shown)
        tbl.tree.unbind("<Double-1>")
        tbl.tree.unbind("<Return>")
        tbl.tree.bind("<Double-1>", lambda e, t=tbl, q=queue_tracks: self._play_row(t, q, e))
        tbl.tree.bind("<Return>", lambda e, t=tbl, q=queue_tracks: self._play_row(t, q, None))
        if removable:
            tbl.on_remove = self._remove
        self.tables.append(tbl)
        return r + 1

    def _play_row(self, tbl, queue_tracks, e):
        sel = tbl.tree.selection()
        if not sel:
            return
        if e is not None and tbl.tree.identify_region(e.x, e.y) != "cell":
            return
        t = tbl.tracks[int(sel[0])]
        try:
            idx = queue_tracks.index(t)
        except ValueError:
            queue_tracks, idx = tbl.tracks, int(sel[0])
        self.app.play_list(queue_tracks, idx)

    def _remove(self, sel):
        paths = [t["path"] for t in sel]
        if self.kind == "playlist":
            self.app.user.remove_from_playlist(self.key, paths)
        elif self.kind == "favorites":
            for p in paths:
                self.app.user.fav.discard(p)
            self.app.user.save()
        self.on_show(kind=self.kind, key=self.key)


# ───────────────────────── ページ: 再生中 (歌詞 + ビジュアライザー) ─────────────────────────
def mix_color(c1, c2, f):
    return "#%02x%02x%02x" % tuple(int(c1[i] * f + c2[i] * (1 - f)) for i in range(3))


class NowPlayingPage(ctk.CTkFrame):
    BG_RGB = (20, 21, 30)

    def __init__(self, master, app):
        super().__init__(master, fg_color=BG, corner_radius=0)
        self.app = app
        self.cv = tk.Canvas(self, bg=BG, highlightthickness=0, bd=0)
        self.cv.pack(fill="both", expand=True)
        self.mode = "lyrics"
        self.cover = None
        self.tint = (124, 92, 255)
        self.photos = {}
        self.times, self.lines, self.cum, self.heights = [], [], [], []
        self.lyr_state = "none"  # none / loading / ok
        self.scroll = 0.0
        self.user_off, self.user_t, self.qscroll = 0.0, 0.0, 0
        self.bars = np.zeros(48)
        self.size = (0, 0)
        self.dirty = True
        self.visible = False
        self.f_ly = tkfont.Font(root=self, family=FONT_FAMILY, size=-27, weight="bold")
        self.f_title = tkfont.Font(root=self, family=FONT_FAMILY, size=-24, weight="bold")
        self.f_sub = tkfont.Font(root=self, family=FONT_FAMILY, size=-16)
        self.f_q = tkfont.Font(root=self, family=FONT_FAMILY, size=-17, weight="bold")
        self.f_q2 = tkfont.Font(root=self, family=FONT_FAMILY, size=-13)
        self.seg = ctk.CTkSegmentedButton(self.cv, values=["歌詞", "キュー"], command=self._seg, height=32,
                                          fg_color=CARD, selected_color=ACCENT, selected_hover_color=ACCENT_H,
                                          unselected_color=CARD, unselected_hover_color=CARD_2, font=F(12, "bold"))
        self.seg.set("歌詞")
        self.fs = ctk.CTkButton(self.cv, text="⛶", width=36, height=32, corner_radius=10, fg_color=CARD,
                                hover_color=CARD_2, text_color=TEXT, font=F(16), command=app.toggle_fullscreen)
        self.lyr_btn = ctk.CTkButton(self.cv, text="オンラインで歌詞を探す", height=36, corner_radius=18,
                                     fg_color=ACCENT, hover_color=ACCENT_H, font=F(13, "bold"),
                                     command=lambda: app.fetch_lyrics_online())
        self.w_seg = self.cv.create_window(0, 0, window=self.seg, anchor="ne")
        self.w_fs = self.cv.create_window(0, 0, window=self.fs, anchor="ne")
        self.cv.bind("<Configure>", self._on_resize)
        for ev in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.cv.bind(ev, self._wheel)
        self.cv.bind("<Button-1>", self._click)

    # --- 外部から ---
    def on_show(self, mode=None, **kw):
        self.visible = True
        if mode:
            self.mode = mode
            self.seg.set("歌詞" if mode == "lyrics" else "キュー")
        self.redraw_static()

    def on_hide(self):
        self.visible = False

    def track_changed(self):
        t = self.app.cur
        self.cover = None
        self.scroll, self.user_off = 0.0, 0.0
        self.set_lyrics(None, "loading" if t else "none")
        if t:
            def done(img, t=t):
                if self.app.cur is t:
                    self.cover = img
                    if img is not None:
                        c = img.resize((1, 1), Image.BILINEAR).getpixel((0, 0))
                        m = max(c) or 1
                        k = 210 / m if m < 210 else 1
                        self.tint = tuple(min(255, int(x * k)) for x in c)
                    else:
                        self.tint = (124, 92, 255)
                    self.dirty = True
                    if self.visible:
                        self.redraw_static()
            self.app.run_bg(lambda: self.app.covers.get(t, 640), done)
        if self.visible:
            self.redraw_static()
        else:
            self.dirty = True

    def set_lyrics(self, lyr, state=None):
        if lyr and lyr.get("synced"):
            self.times = [x[0] for x in lyr["synced"]]
            self.lines = [x[1] or "♪" for x in lyr["synced"]]
            self.lyr_state = "ok"
        elif lyr and lyr.get("plain"):
            self.times = []
            self.lines = [x if x.strip() else "" for x in lyr["plain"].splitlines()]
            self.lyr_state = "ok"
        else:
            self.times, self.lines = [], []
            self.lyr_state = state or "none"
        self._calc_heights()
        self.dirty = True
        if self.visible:
            self.redraw_static()

    # --- レイアウト ---
    def _calc_heights(self):
        lh = self.f_ly.metrics("linespace")
        maxw = max(200, self.size[0] - self._rx() - 60) if self.size[0] else 500
        self.heights, self.cum, acc = [], [], 0
        for ln in self.lines:
            n = max(1, math.ceil(self.f_ly.measure(ln or " ") / maxw))
            h = n * lh + 22
            self.cum.append(acc)
            self.heights.append(h)
            acc += h

    def _lw(self):
        return int(min(self.size[0] * 0.40, 440))

    def _rx(self):
        return 56 + self._lw() + 60

    def _on_resize(self, e):
        if (e.width, e.height) != self.size:
            self.size = (e.width, e.height)
            self.cv.coords(self.w_seg, e.width - 70, 20)
            self.cv.coords(self.w_fs, e.width - 20, 20)
            self._calc_heights()
            self.dirty = True
            if self.visible:
                self.redraw_static()

    def redraw_static(self):
        cv, a = self.cv, self.app
        W, H = self.size
        if W < 100 or H < 100:
            return
        self.dirty = False
        cv.delete("static")
        cv.delete("dyn")
        t = a.cur
        if t is None:
            cv.create_text(W // 2, H // 2, text="再生中の曲はありません\nライブラリから曲を選んでください",
                           fill=MUTED, font=self.f_sub, justify="center", tags="static")
            return
        # 背景: ジャケットをぼかして暗くする
        if self.cover is not None:
            small = ImageOps.fit(self.cover, (max(8, W // 8), max(8, H // 8)), Image.BILINEAR).filter(ImageFilter.GaussianBlur(5))
            bg = ImageEnhance.Brightness(small.resize((W, H), Image.BILINEAR)).enhance(0.38)
            self.photos["bg"] = ImageTk.PhotoImage(bg)
            cv.create_image(0, 0, anchor="nw", image=self.photos["bg"], tags="static")
        lw = self._lw()
        cs = int(max(120, min(lw - 10, H * 0.44, 380)))
        x0 = 56
        y0 = max(70, int((H - cs - 170) / 2))
        self.geo = (x0, y0, cs)
        if self.cover is not None:
            img = round_image(self.cover.resize((cs, cs), Image.LANCZOS), 0.05)
        else:
            img = round_image(make_placeholder(cs, t["title"]), 0.05)
        self.photos["cover"] = ImageTk.PhotoImage(img)
        cv.create_image(x0, y0, anchor="nw", image=self.photos["cover"], tags="static")
        cv.create_text(x0, y0 + cs + 26, anchor="nw", text=t["title"], fill="white", font=self.f_title,
                       width=cs + 20, tags="static")
        th = self.f_title.metrics("linespace") * min(2, max(1, math.ceil(self.f_title.measure(t["title"]) / (cs + 20))))
        cv.create_text(x0, y0 + cs + 30 + th, anchor="nw", text=t["artist"], fill="#c4c8d8", font=self.f_sub,
                       width=cs + 20, tags="static")
        self.viz_geo = (x0, y0 + cs + 40 + th + self.f_sub.metrics("linespace"), cs)
        if self.mode == "lyrics" and self.lyr_state in ("none", "loading"):
            rx = self._rx()
            msg = "歌詞を検索しています…" if self.lyr_state == "loading" else "歌詞が見つかりません"
            cv.create_text(rx, H // 2 - 30, anchor="w", text=msg, fill="#c4c8d8", font=self.f_ly, tags="static")
            if self.lyr_state == "none":
                cv.create_window(rx, H // 2 + 20, window=self.lyr_btn, anchor="w", tags="static")
        cv.tag_lower("static")

    # --- 毎フレーム ---
    def tick(self, pos, playing):
        if self.dirty:
            self.redraw_static()
        cv, a = self.cv, self.app
        W, H = self.size
        if W < 100 or a.cur is None:
            return
        cv.delete("dyn")
        rx = self._rx()
        rw = max(200, W - rx - 60)
        if self.mode == "queue":
            self._draw_queue(rx, rw, H)
        elif self.lyr_state == "ok":
            self._draw_lyrics(pos, rx, rw, H)
        if a.cfg.get("viz", True) and hasattr(self, "viz_geo"):
            vx, vy, vw = self.viz_geo
            n = len(self.bars)
            raw = a.engine.spectrum(n) if playing else np.zeros(n)
            self.bars = np.maximum(raw, self.bars * 0.84)
            maxh = 58
            bw = vw / n
            col = "#%02x%02x%02x" % self.tint
            for i in range(n):
                h = 3 + float(self.bars[i]) * maxh
                cv.create_rectangle(vx + i * bw + 1, vy + maxh - h, vx + (i + 1) * bw - 1, vy + maxh,
                                    fill=col, width=0, tags="dyn")

    def _draw_lyrics(self, pos, rx, rw, H):
        cv = self.cv
        n = len(self.lines)
        if not n:
            return
        synced = bool(self.times)
        idx = (bisect_right(self.times, pos + 0.2) - 1) if synced else -1
        if synced:
            target = (self.cum[idx] + self.heights[idx] / 2) if idx >= 0 else 0
        else:
            target = H * 0.42
        self.scroll += (target - self.scroll) * 0.16
        if time.time() - self.user_t > 2.5:
            self.user_off *= 0.9
        base = H * 0.42 - self.scroll - self.user_off
        bg = self.BG_RGB
        for i in range(n):
            y = base + self.cum[i]
            if y + self.heights[i] < 50 or y > H:
                continue
            if synced:
                d = abs(i - idx)
                col = "#ffffff" if d == 0 else mix_color((255, 255, 255), bg, (0.5, 0.36, 0.27, 0.2)[min(d, 4) - 1 if d else 0] if d < 5 else 0.18)
            else:
                col = "#e6e8f0"
            if self.lines[i]:
                cv.create_text(rx, y, anchor="nw", text=self.lines[i], fill=col, font=self.f_ly, width=rw,
                               tags=("dyn", f"ly{i}"))

    def _draw_queue(self, rx, rw, H):
        cv, a = self.cv, self.app
        cv.create_text(rx, 64, anchor="nw", text="再生キュー", fill="white", font=self.f_title, tags="dyn")
        q = a.queue
        start = max(0, min(a.pos - 1 + self.qscroll, max(0, len(q) - 1)))
        y = 112
        for i in range(start, len(q)):
            if y > H - 40:
                break
            t = q[i]
            cur = i == a.pos
            cv.create_rectangle(rx - 12, y - 6, rx + rw, y + 50, fill=("#2a2f45" if cur else ""), width=0, tags=("dyn", f"q{i}"))
            cv.create_text(rx, y, anchor="nw", text=("▶ " if cur else "") + t["title"], fill=(ACCENT if cur else "white"),
                           font=self.f_q, width=rw - 20, tags=("dyn", f"q{i}"))
            cv.create_text(rx, y + 24, anchor="nw", text=t["artist"], fill="#9aa0b8", font=self.f_q2, tags=("dyn", f"q{i}"))
            y += 62

    # --- 操作 ---
    def _seg(self, v):
        self.mode = "lyrics" if v == "歌詞" else "queue"
        self.qscroll = 0
        self.redraw_static()

    def _wheel(self, e):
        d = -1 if (getattr(e, "num", 0) == 4 or getattr(e, "delta", 0) > 0) else 1
        if self.mode == "queue":
            self.qscroll = max(-self.app.pos + 1, self.qscroll + d)
        else:
            self.user_off += d * 70
            self.user_t = time.time()

    def _click(self, e):
        for item in reversed(self.cv.find_overlapping(e.x - 1, e.y - 1, e.x + 1, e.y + 1)):
            for tg in self.cv.gettags(item):
                if tg.startswith("ly") and tg[2:].isdigit() and self.times:
                    self.app.seek_to(self.times[int(tg[2:])])
                    return
                if tg.startswith("q") and tg[1:].isdigit():
                    self.app.jump_to(int(tg[1:]))
                    return


# ───────────────────────── ページ: ダウンロード ─────────────────────────
class DownloadPage(ctk.CTkScrollableFrame):
    def __init__(self, master, app):
        super().__init__(master, fg_color=BG, corner_radius=0)
        self.app = app
        self.cfg = app.cfg
        self.worker = None
        self.busy = False
        self.grid_columnconfigure(0, weight=1)
        self._build()
        self._on_kind_change(self.kind.get())

    def card(self, parent=None):
        return ctk.CTkFrame(parent or self, fg_color=CARD, corner_radius=18)

    def _build(self):
        head = ctk.CTkFrame(self, fg_color="transparent")
        head.grid(row=0, column=0, sticky="ew", padx=28, pady=(24, 4))
        ctk.CTkLabel(head, text="ダウンロード", font=F(28, "bold"), text_color=TEXT).pack(anchor="w")
        ctk.CTkLabel(head, text=SITES_HINT, font=F(12), text_color=MUTED).pack(anchor="w", pady=(2, 0))

        # Deno未導入のお知らせ(必要なときだけ表示)
        self.banner = ctk.CTkFrame(self, fg_color="#2a2236", corner_radius=14)
        ctk.CTkLabel(self.banner, text="YouTubeのダウンロードにはDeno(JavaScriptランタイム)が必要になりました。",
                     font=F(12), text_color=WARN).pack(side="left", padx=16, pady=10)
        ctk.CTkButton(self.banner, text="設定で導入する", width=120, height=30, corner_radius=15, fg_color=ACCENT,
                      hover_color=ACCENT_H, font=F(12, "bold"),
                      command=lambda: self.app.show("settings")).pack(side="right", padx=12)

        c1 = self.card()
        c1.grid(row=2, column=0, sticky="ew", padx=28, pady=8)
        c1.grid_columnconfigure(0, weight=1)
        top = ctk.CTkFrame(c1, fg_color="transparent")
        top.grid(row=0, column=0, sticky="ew", padx=18, pady=(14, 6))
        top.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(top, text="URL / 検索ワード（1行に1件・複数OK）", font=F(13, "bold"),
                     text_color=TEXT).grid(row=0, column=0, sticky="w")
        ctk.CTkButton(top, text="貼り付け", width=80, height=28, corner_radius=14, fg_color=CARD_2, hover_color=HOVER,
                      font=F(12), command=self._paste).grid(row=0, column=1, padx=(0, 6))
        ctk.CTkButton(top, text="クリア", width=70, height=28, corner_radius=14, fg_color=CARD_2, hover_color=HOVER,
                      font=F(12), command=lambda: self.urls.delete("1.0", "end")).grid(row=0, column=2, padx=(0, 6))
        ctk.CTkButton(top, text="🔍 検索", width=90, height=28, corner_radius=14, fg_color=ACCENT, hover_color=ACCENT_H,
                      font=F(12, "bold"), command=self.app.open_search).grid(row=0, column=3)
        self.urls = ctk.CTkTextbox(c1, height=110, corner_radius=12, fg_color=CARD_2, text_color=TEXT, font=F(13),
                                   border_width=0)
        self.urls.grid(row=1, column=0, sticky="ew", padx=18, pady=(0, 16))

        c2 = self.card()
        c2.grid(row=3, column=0, sticky="ew", padx=28, pady=8)
        c2.grid_columnconfigure((0, 1), weight=1, uniform="o")
        left = ctk.CTkFrame(c2, fg_color="transparent")
        left.grid(row=0, column=0, sticky="nsew", padx=(18, 9), pady=14)
        ctk.CTkLabel(left, text="種類", font=F(12), text_color=MUTED).pack(anchor="w")
        seg = dict(selected_color=ACCENT, selected_hover_color=ACCENT_H, unselected_color=CARD_2,
                   unselected_hover_color=HOVER, fg_color=CARD_2, corner_radius=12)
        self.kind = ctk.CTkSegmentedButton(left, values=["音声", "動画"], command=self._on_kind_change,
                                           font=F(13, "bold"), **seg)
        self.kind.pack(fill="x", pady=(4, 10))
        self.kind.set("動画" if self.cfg.get("kind") == "video" else "音声")
        ctk.CTkLabel(left, text="形式", font=F(12), text_color=MUTED).pack(anchor="w")
        self.fmt = ctk.CTkSegmentedButton(left, values=list(AUDIO_FORMATS), font=F(12), command=self._on_fmt_change, **seg)
        self.fmt.pack(fill="x", pady=(4, 10))
        self.fmt.set(self.cfg.get("format", "M4A") if self.cfg.get("format") in AUDIO_FORMATS else "M4A")
        self._last_audio_fmt = self.fmt.get()
        ctk.CTkLabel(left, text="音質 / 画質", font=F(12), text_color=MUTED).pack(anchor="w")
        menu = dict(fg_color=CARD_2, button_color=CARD_2, button_hover_color=HOVER, dropdown_fg_color=CARD_2,
                    corner_radius=12, font=F(13))
        self.quality = ctk.CTkOptionMenu(left, values=AUDIO_QUALITIES, **menu)
        self.quality.pack(fill="x", pady=(4, 0))

        right = ctk.CTkFrame(c2, fg_color="transparent")
        right.grid(row=0, column=1, sticky="nsew", padx=(9, 18), pady=14)
        self.v_playlist = ctk.BooleanVar(value=self.cfg.get("playlist", True))
        self.v_embed = ctk.BooleanVar(value=self.cfg.get("embed", True))
        self.v_group = ctk.BooleanVar(value=self.cfg.get("group", True))
        for text, var in (("プレイリスト全体を取得", self.v_playlist), ("サムネイル・タグを埋め込む", self.v_embed),
                          ("プレイリスト/投稿者ごとにフォルダ分け（音声）", self.v_group)):
            ctk.CTkSwitch(right, text=text, variable=var, font=F(13), text_color=TEXT, progress_color=ACCENT,
                          button_color="#ffffff").pack(anchor="w", pady=5)
        ctk.CTkLabel(right, text="ログイン必要/403のとき Cookie取得元", font=F(12), text_color=MUTED).pack(anchor="w", pady=(8, 0))
        self.browser = ctk.CTkOptionMenu(right, values=BROWSERS, command=lambda v: self.app.set_cfg("browser", v), **menu)
        self.browser.pack(fill="x", pady=(4, 0))
        self.browser.set(self.cfg.get("browser", "使わない"))

        c3 = self.card()
        c3.grid(row=4, column=0, sticky="ew", padx=28, pady=8)
        c3.grid_columnconfigure(1, weight=1)
        ctk.CTkLabel(c3, text="保存先", font=F(12), text_color=MUTED).grid(row=0, column=0, padx=(18, 8), pady=(14, 6))
        self.outdir = ctk.CTkEntry(c3, height=34, corner_radius=12, fg_color=CARD_2, border_width=0, text_color=TEXT, font=F(12))
        self.outdir.grid(row=0, column=1, sticky="ew", pady=(14, 6))
        self.outdir.insert(0, self.cfg.get("outdir", str(Path.home() / "Downloads" / "MusicDL")))
        self.outdir.bind("<FocusOut>", lambda e: self.app.set_outdir(self.outdir.get().strip(), from_dl=True))
        ctk.CTkButton(c3, text="選択", width=70, height=34, corner_radius=12, fg_color=CARD_2, hover_color=HOVER,
                      font=F(12), command=self.app.choose_outdir).grid(row=0, column=2, padx=6, pady=(14, 6))
        ctk.CTkButton(c3, text="開く", width=70, height=34, corner_radius=12, fg_color=CARD_2, hover_color=HOVER,
                      font=F(12), command=self._open_dir).grid(row=0, column=3, padx=(0, 18), pady=(14, 6))
        btns = ctk.CTkFrame(c3, fg_color="transparent")
        btns.grid(row=1, column=0, columnspan=4, sticky="ew", padx=18, pady=(6, 10))
        btns.grid_columnconfigure(0, weight=1)
        self.start_btn = ctk.CTkButton(btns, text="ダウンロード開始", height=46, corner_radius=14, fg_color=ACCENT,
                                       hover_color=ACCENT_H, font=F(15, "bold"), command=self._start)
        self.start_btn.grid(row=0, column=0, sticky="ew")
        self.cancel_btn = ctk.CTkButton(btns, text="キャンセル", width=110, height=46, corner_radius=14, fg_color="#3a2230",
                                        hover_color="#51304a", text_color=ERR, font=F(13, "bold"), state="disabled",
                                        command=self._cancel)
        self.cancel_btn.grid(row=0, column=1, padx=(8, 0))
        ctk.CTkButton(btns, text="ツール設定", width=110, height=46, corner_radius=14, fg_color=CARD_2, hover_color=HOVER,
                      font=F(13), command=lambda: self.app.show("settings")).grid(row=0, column=2, padx=(8, 0))
        self.title_lbl = ctk.CTkLabel(c3, text="待機中", font=F(13, "bold"), text_color=TEXT, anchor="w")
        self.title_lbl.grid(row=2, column=0, columnspan=4, sticky="ew", padx=20)
        self.bar = ctk.CTkProgressBar(c3, height=10, corner_radius=5, fg_color=CARD_2, progress_color=ACCENT)
        self.bar.grid(row=3, column=0, columnspan=4, sticky="ew", padx=18, pady=(6, 4))
        self.bar.set(0)
        self.stats_lbl = ctk.CTkLabel(c3, text=" ", font=F(12), text_color=MUTED, anchor="w")
        self.stats_lbl.grid(row=4, column=0, columnspan=4, sticky="ew", padx=20, pady=(0, 14))

        c4 = self.card()
        c4.grid(row=5, column=0, sticky="ew", padx=28, pady=(8, 24))
        c4.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(c4, text="ログ", font=F(13, "bold"), text_color=TEXT).grid(row=0, column=0, sticky="w", padx=18, pady=(12, 4))
        self.log = ctk.CTkTextbox(c4, height=230, corner_radius=12, fg_color=CARD_2, text_color=MUTED,
                                  font=ctk.CTkFont(family="Consolas" if os.name == "nt" else "Courier", size=12),
                                  border_width=0, wrap="word")
        self.log.grid(row=1, column=0, sticky="ew", padx=18, pady=(0, 16))
        for tag, color in (("ok", OK), ("warn", WARN), ("err", ERR), ("head", TEXT), ("info", MUTED)):
            self.log._textbox.tag_config(tag, foreground=color)
        self.log.configure(state="disabled")

    def on_show(self, **kw):
        self.refresh_banner()

    def refresh_banner(self):
        if self.app.deno_missing:
            self.banner.grid(row=1, column=0, sticky="ew", padx=28, pady=(6, 4))
        else:
            self.banner.grid_remove()

    def set_outdir(self, path):
        self.outdir.delete(0, "end")
        self.outdir.insert(0, path)

    # --- 動作 ---
    def _on_kind_change(self, value):
        if value == "音声":
            self.fmt.configure(values=list(AUDIO_FORMATS), state="normal")
            if self.fmt.get() not in AUDIO_FORMATS:
                self.fmt.set(self._last_audio_fmt)
        else:
            self.fmt.configure(values=["MP4"], state="disabled")
            self.fmt.set("MP4")
        self._refresh_quality()

    def _on_fmt_change(self, value):
        if value in AUDIO_FORMATS:
            self._last_audio_fmt = value
        self._refresh_quality()

    def _refresh_quality(self):
        if self.kind.get() == "動画":
            vals, default = VIDEO_QUALITIES, self.cfg.get("vquality", "720p")
        elif AUDIO_FORMATS.get(self.fmt.get()) in LOSSLESS:
            vals, default = ["ロスレス"], "ロスレス"
        else:
            vals, default = AUDIO_QUALITIES, self.cfg.get("aquality", "192k")
        self.quality.configure(values=vals, state="disabled" if vals == ["ロスレス"] else "normal")
        self.quality.set(default if default in vals else vals[0])

    def _paste(self):
        try:
            lines = split_items(self.clipboard_get())
        except Exception:
            return
        self.add_to_queue(lines)

    def add_to_queue(self, urls, start=False):
        """入力欄(キュー)にURLを追加。重複は除外。start=Trueなら続けてダウンロード開始"""
        existing = set(self._collect_urls())
        new = []
        for u in urls:
            if u not in existing:
                existing.add(u)
                new.append(u)
        if new:
            cur = self.urls.get("1.0", "end-1c")
            prefix = "\n" if cur and not cur.endswith("\n") else ""
            self.urls.insert("end-1c", prefix + "\n".join(new) + "\n")
        self._log(f"キューに {len(new)} 件追加しました" + (f"（重複 {len(urls) - len(new)} 件は除外）" if len(new) < len(urls) else ""), "info")
        if start:
            if self.busy or (self.worker and self.worker.is_alive()):
                self._log("ダウンロード実行中です。終了後に「ダウンロード開始」を押してください。", "warn")
            else:
                self._start()

    def _open_dir(self):
        path = self.outdir.get().strip()
        if not path:
            self._log("保存先を指定してください。", "warn")
            return
        try:
            Path(path).mkdir(parents=True, exist_ok=True)
            open_path(path)
        except Exception as e:
            self._log(f"フォルダを開けませんでした: {e}", "err")

    def _collect_urls(self):
        return split_items(self.urls.get("1.0", "end"))

    def snapshot_cfg(self):
        a = self.app.cfg
        return {
            "kind": "audio" if self.kind.get() == "音声" else "video", "format": self.fmt.get(),
            "quality": self.quality.get(), "outdir": self.outdir.get().strip(),
            "playlist": self.v_playlist.get(), "embed": self.v_embed.get(), "group": self.v_group.get(),
            "browser": self.browser.get(), "concurrency": a.get("concurrency", 4), "retries": a.get("retries", 5),
            "ratelimit": "" if a.get("ratelimit", "無制限") == "無制限" else a.get("ratelimit", ""),
            "proxy": a.get("proxy", ""), "remote_components": a.get("remote_components", False),
        }

    def _start(self):
        if self.busy or (self.worker and self.worker.is_alive()):
            return
        items = self._collect_urls()
        if not items:
            messagebox.showinfo(APP_NAME, "URLか検索ワードを入力してください。")
            return
        has_ff, _ = find_ffmpeg()
        if not has_ff:
            messagebox.showerror(APP_NAME, "FFmpegが見つかりません。\n設定 > ツール からインストールするか、このファイルと同じフォルダに ffmpeg.exe を置いてください。")
            return
        outdir = self.outdir.get().strip()
        if not outdir:
            messagebox.showinfo(APP_NAME, "保存先を指定してください。")
            return
        try:
            os.makedirs(outdir, exist_ok=True)
        except Exception as e:
            messagebox.showerror(APP_NAME, f"保存先を作成できません:\n{e}")
            return
        cfg = self.snapshot_cfg()
        self.save_state()
        self.app.cancel.clear()
        self.bar.set(0)
        self.title_lbl.configure(text="準備中…")
        self.stats_lbl.configure(text=" ")
        self.start_btn.configure(state="disabled", text="ダウンロード中…")
        self.cancel_btn.configure(state="normal")
        self.busy = True
        self.worker = Downloader(items, cfg, self.app.q, self.app.cancel)
        self.worker.start()

    def _cancel(self):
        self.app.cancel.set()
        self.cancel_btn.configure(state="disabled")
        self.title_lbl.configure(text="キャンセル中…")

    def save_state(self):
        d = self.app.cfg
        d.update({"kind": "audio" if self.kind.get() == "音声" else "video", "outdir": self.outdir.get().strip(),
                  "playlist": self.v_playlist.get(), "embed": self.v_embed.get(), "group": self.v_group.get(),
                  "browser": self.browser.get()})
        if self.kind.get() == "音声":
            d["format"] = self.fmt.get()
            if self.quality.get() in AUDIO_QUALITIES:
                d["aquality"] = self.quality.get()
        else:
            d["vquality"] = self.quality.get()
        save_settings(d)

    def _log(self, text, level="info"):
        self.log.configure(state="normal")
        self.log._textbox.insert("end", text + "\n", level)
        self.log.configure(state="disabled")
        self.log.see("end")

    def handle(self, m):
        kind = m[0]
        if kind == "log":
            self._log(m[1], m[2])
        elif kind == "progress":
            self.bar.set(max(0.0, min(1.0, m[1])))
            self.title_lbl.configure(text=m[2] or "ダウンロード中")
            self.stats_lbl.configure(text=m[3])
        elif kind == "status":
            self.stats_lbl.configure(text=m[1])
        elif kind == "overall":
            self.title_lbl.configure(text=f"({m[1]}/{m[2]}) 取得中…")
        elif kind == "done":
            ok, fail, cancelled = m[1], m[2], m[3]
            self.busy = False
            self.start_btn.configure(state="normal", text="ダウンロード開始")
            self.cancel_btn.configure(state="disabled")
            if cancelled:
                self.title_lbl.configure(text="キャンセルしました")
            else:
                self.bar.set(1 if fail == 0 else self.bar.get())
                self.title_lbl.configure(text=f"完了: 成功 {ok} / 失敗 {fail}")
            self.stats_lbl.configure(text=" ")
            self._log(f"— 終了: 成功 {ok} / 失敗 {fail} —", "ok" if fail == 0 and not cancelled else "warn")
            if ok and self.app.cfg.get("auto_scan", True):
                self.app.rescan_library()


# ───────────────────────── ページ: 設定 ─────────────────────────
class SettingsPage(ctk.CTkScrollableFrame):
    STARTUP = {"検索": "search", "ホーム": "home", "曲": "songs", "アルバム": "albums", "アーティスト": "artists", "ダウンロード": "download"}

    def __init__(self, master, app):
        super().__init__(master, fg_color=BG, corner_radius=0)
        self.app = app
        self.grid_columnconfigure(0, weight=1)
        self.r = 0
        self.restart_btn = None
        self.latest = None
        page_title(self, "設定").grid(row=self.r, column=0, sticky="w", padx=32, pady=(28, 4))
        self.r += 1
        self._build()

    # --- 部品 ---
    def ui(self, fn):
        self.app.q.put(("call", fn))

    def section(self, title, sub=""):
        card = ctk.CTkFrame(self, fg_color=CARD, corner_radius=18)
        card.grid(row=self.r, column=0, sticky="ew", padx=32, pady=8)
        card.grid_columnconfigure(0, weight=1)
        self.r += 1
        ctk.CTkLabel(card, text=title, font=F(16, "bold"), text_color=TEXT).grid(row=0, column=0, sticky="w", padx=22, pady=(16, 0 if sub else 6))
        card._n = 1
        if sub:
            ctk.CTkLabel(card, text=sub, font=F(12), text_color=MUTED, justify="left", wraplength=760).grid(row=1, column=0, sticky="w", padx=22, pady=(0, 6))
            card._n = 2
        return card

    def row(self, card, title, desc, maker):
        f = ctk.CTkFrame(card, fg_color="transparent")
        f.grid(row=card._n, column=0, sticky="ew", padx=22, pady=7)
        f.grid_columnconfigure(0, weight=1)
        card._n += 1
        t = ctk.CTkFrame(f, fg_color="transparent")
        t.grid(row=0, column=0, sticky="w")
        ctk.CTkLabel(t, text=title, font=F(13, "bold"), text_color=TEXT, anchor="w").pack(anchor="w")
        if desc:
            ctk.CTkLabel(t, text=desc, font=F(11), text_color=MUTED, anchor="w", justify="left", wraplength=470).pack(anchor="w")
        w = maker(f)
        w.grid(row=0, column=1, sticky="e", padx=(12, 0))
        return w

    def pad(self, card):
        ctk.CTkFrame(card, height=8, fg_color="transparent").grid(row=card._n, column=0)
        card._n += 1

    def switch(self, key, default=True, after=None):
        def mk(p):
            v = ctk.BooleanVar(value=self.app.cfg.get(key, default))

            def cmd():
                self.app.set_cfg(key, v.get())
                if after:
                    after(v.get())
            return ctk.CTkSwitch(p, text="", variable=v, width=46, progress_color=ACCENT, button_color="#ffffff", command=cmd)
        return mk

    def option(self, key, values, default, cast=str, width=150, after=None):
        def mk(p):
            def cmd(v):
                self.app.set_cfg(key, cast(v) if cast is not str else v)
                if after:
                    after(v)
            m = ctk.CTkOptionMenu(p, values=values, width=width, fg_color=CARD_2, button_color=CARD_2,
                                  button_hover_color=HOVER, dropdown_fg_color=CARD_2, corner_radius=12, font=F(12),
                                  command=cmd)
            cur = self.app.cfg.get(key, default)
            m.set(str(cur) if str(cur) in values else str(default))
            return m
        return mk

    def btn(self, text, command, width=120, primary=False):
        def mk(p):
            return ctk.CTkButton(p, text=text, width=width, height=34, corner_radius=17, font=F(12, "bold"),
                                 fg_color=ACCENT if primary else CARD_2, hover_color=ACCENT_H if primary else HOVER,
                                 command=command)
        return mk

    def label(self, text="", color=MUTED):
        def mk(p):
            lb = ctk.CTkLabel(p, text=text, font=F(12), text_color=color, anchor="e", justify="right")
            self._tmp = lb
            return lb
        return mk

    # --- 画面 ---
    def _build(self):
        a = self.app
        # 一般
        c = self.section("一般")
        self.out_entry = None

        def mk_out(p):
            fr = ctk.CTkFrame(p, fg_color="transparent")
            self.out_lbl = ctk.CTkLabel(fr, text=a.cfg.get("outdir", ""), font=F(11), text_color=MUTED, anchor="e", wraplength=330)
            self.out_lbl.pack(side="left", padx=(0, 8))
            ctk.CTkButton(fr, text="変更", width=70, height=32, corner_radius=16, fg_color=CARD_2, hover_color=HOVER,
                          font=F(12, "bold"), command=a.choose_outdir).pack(side="left")
            return fr
        self.row(c, "保存先フォルダ", "ダウンロードした音声は「保存先/Music」に入り、ライブラリに自動で表示されます", mk_out)
        self.lib_box = ctk.CTkFrame(c, fg_color="transparent")
        self.lib_box.grid(row=c._n, column=0, sticky="ew", padx=22, pady=(4, 0))
        c._n += 1
        self._draw_lib_list()
        self.row(c, "起動時に開くページ", "", self.option("startup", list(self.STARTUP), "検索", width=150))
        self.row(c, "起動時にライブラリを更新", "フォルダの変更をスキャンして反映します", self.switch("scan_on_start", True))
        self.row(c, "ダウンロード完了後にライブラリを更新", "", self.switch("auto_scan", True))
        self.pad(c)

        self._steps = [self._b2, self._b3, self._b4, self._b5]
        self.after(10, self._next_step)

    def _next_step(self):
        if self._steps:
            self._steps.pop(0)()
            self.after(12, self._next_step)

    def _b2(self):
        a = self.app
        c = self.section("外観 / プレーヤー")
        self.row(c, "アクセントカラー", "再起動すると全体に反映されます", self.option("accent", list(THEMES), "バイオレット", after=lambda v: self._need_restart()))
        self.row(c, "ビジュアライザー", "再生中ページに音に合わせたバーを表示します", self.switch("viz", True))
        devs = ["既定"] + AudioEngine.output_devices()
        self.row(c, "出力デバイス", "音が出るスピーカー/ヘッドホン", self.option("device", devs, "既定", width=260, after=self._set_device))
        self.row(c, "歌詞をオンラインで取得 (LRCLIB)", "曲名・アーティスト名・長さを lrclib.net へ送って同期歌詞を探します。.lrcファイルや埋め込み歌詞が優先されます", self.switch("lyrics_online", True))
        self.row(c, "アーティスト画像をオンラインで取得 (Deezer)", "アーティスト名を api.deezer.com へ送って画像を探します", self.switch("artist_online", True))
        self.pad(c)


    def _b3(self):
        a = self.app
        c = self.section("ダウンロード")
        self.row(c, "同時ダウンロード(分割)数", "多いほど速い場合があります", self.option("concurrency", ["1", "2", "4", "8", "16"], "4", cast=int, width=100))
        self.row(c, "速度制限", "回線を使い切りたくないときに", self.option("ratelimit", RATE_LIMITS, "無制限", width=110))
        self.row(c, "リトライ回数", "", self.option("retries", ["3", "5", "10"], "5", cast=int, width=100))
        self.row(c, "Cookieを取得するブラウザ", "ログイン必要/403のとき", self.option("browser", BROWSERS, "使わない", width=130, after=lambda v: a.dl.browser.set(v) if a.dl_ready else None))

        def mk_proxy(p):
            e = ctk.CTkEntry(p, width=260, height=32, corner_radius=12, fg_color=CARD_2, border_width=0,
                             placeholder_text="例: http://127.0.0.1:8080", font=F(12))
            e.insert(0, a.cfg.get("proxy", ""))
            e.bind("<FocusOut>", lambda ev: a.set_cfg("proxy", e.get().strip()))
            e.bind("<Return>", lambda ev: a.set_cfg("proxy", e.get().strip()))
            return e
        self.row(c, "プロキシ", "空欄なら使いません", mk_proxy)
        self.row(c, "リモートコンポーネントを許可", "YouTube用の解析スクリプトをGitHubから取得します。通常は不要(yt-dlp[default]に同梱)。オフ推奨", self.switch("remote_components", False))
        self.pad(c)


    def _b4(self):
        a = self.app
        c = self.section("ツール", "YouTubeのダウンロード/試聴には、最新のyt-dlpとDeno(JavaScriptランタイム)が必要です。ここからワンクリックで導入・更新できます。")
        self.row(c, "yt-dlp", "", self.label(f"バージョン {ytdlp_version()}"))
        self.lbl_ytdlp = self._tmp
        self.row(c, "yt-dlp の更新", "安定版(PyPI) / ナイトリー版を pip で更新します", lambda p: self._pair(p, [("最新を確認", self.check_latest, False), ("安定版に更新", lambda: self.update_ytdlp(False), True), ("ナイトリー", lambda: self.update_ytdlp(True), False)]))
        self.row(c, "Deno", "", self.label("確認中…"))
        self.lbl_deno = self._tmp
        self.row(c, "Deno の導入", "公式GitHubから取得し、アプリ専用フォルダ(~/.music_dl/bin)に置きます。システムは変更しません", lambda p: self._pair(p, [("インストール / 更新", self.install_deno, True), ("削除", self.remove_deno, False)]))
        self.deno_bar = ctk.CTkProgressBar(c, height=8, corner_radius=4, fg_color=CARD_2, progress_color=ACCENT)
        self.deno_bar.set(0)
        self.deno_bar.grid(row=c._n, column=0, sticky="ew", padx=22, pady=(0, 4))
        self.deno_bar.grid_remove()
        c._n += 1
        self.row(c, "FFmpeg", "", self.label("確認中…"))
        self.lbl_ff = self._tmp
        self.row(c, "FFmpeg の導入", "Windowsは winget、macOSは Homebrew で導入します (Linuxはパッケージマネージャで)", lambda p: self._pair(p, [("インストール", self.install_ffmpeg, False)]))
        self.tool_log = ctk.CTkTextbox(c, height=140, corner_radius=12, fg_color=CARD_2, text_color=MUTED, border_width=0,
                                       font=ctk.CTkFont(family="Consolas" if os.name == "nt" else "Courier", size=11), wrap="word")
        self.tool_log.grid(row=c._n, column=0, sticky="ew", padx=22, pady=(6, 4))
        self.tool_log.configure(state="disabled")
        c._n += 1
        self.tool_foot = ctk.CTkFrame(c, fg_color="transparent", height=1)
        self.tool_foot.grid(row=c._n, column=0, sticky="ew", padx=22, pady=(0, 14))
        c._n += 1
        self.row(c, "更新を自動で確認", "起動時にyt-dlpの新バージョンを確認し、サイドバーに●を表示します", self.switch("check_updates", True))
        self.pad(c)


    def _b5(self):
        a = self.app
        c = self.section("データ / キャッシュ")
        self.cache_lbls = {}
        for key, title, path, desc in (("lyr", "歌詞キャッシュ", LYRICS_DIR, "取得済みの歌詞(.lrc/.txt)"),
                                       ("art", "アーティスト画像キャッシュ", ART_DIR, "Deezerから取得した画像")):
            self.row(c, title, desc, lambda p, key=key, path=path: self._cache_row(p, key, path))
        self.row(c, "ライブラリ索引", "曲のタグ情報キャッシュ。再構築するとフォルダを再スキャンします", self.btn("再スキャン", a.rescan_library, 120))
        self.row(c, "データフォルダ", str(APP_DIR), self.btn("開く", lambda: open_path(APP_DIR), 90))
        self.row(c, "すべての設定を初期化", "お気に入り/プレイリストは消えません。再起動します", self.btn("初期化", self.reset_all, 90))
        self.pad(c)

        c = self.section("このアプリについて")
        self.row(c, f"{APP_NAME} {APP_VER}", "yt-dlp + FFmpeg で取得 / アプリ内プレーヤー。DRM保護の配信サービス(Spotify等)には対応していません", self.label(f"yt-dlp {ytdlp_version()}"))
        self.built = True
        self.refresh_tools()
        self._refresh_cache_labels()

    def _pair(self, parent, specs):
        fr = ctk.CTkFrame(parent, fg_color="transparent")
        for text, cmd, primary in specs:
            ctk.CTkButton(fr, text=text, command=cmd, height=34, corner_radius=17, font=F(12, "bold"),
                          width=max(90, 22 + len(text) * 13), fg_color=ACCENT if primary else CARD_2,
                          hover_color=ACCENT_H if primary else HOVER).pack(side="left", padx=3)
        return fr

    def _cache_row(self, parent, key, path):
        fr = ctk.CTkFrame(parent, fg_color="transparent")
        lb = ctk.CTkLabel(fr, text="", font=F(12), text_color=MUTED)
        lb.pack(side="left", padx=8)
        self.cache_lbls[key] = (lb, path)
        ctk.CTkButton(fr, text="削除", width=70, height=32, corner_radius=16, fg_color=CARD_2, hover_color=HOVER,
                      font=F(12, "bold"), command=lambda: self._clear_cache(path)).pack(side="left")
        return fr

    def _refresh_cache_labels(self):
        for lb, path in self.cache_lbls.values():
            n, size = dir_info(path)
            lb.configure(text=f"{n}件 / {fmt_size(size)}")

    def _clear_cache(self, path):
        for p in Path(path).glob("*"):
            try:
                p.unlink()
            except Exception:
                pass
        self._refresh_cache_labels()

    def on_show(self, **kw):
        if getattr(self, "built", False):
            self._refresh_cache_labels()
            self.refresh_tools()
        self.out_lbl.configure(text=self.app.cfg.get("outdir", ""))
        self._draw_lib_list()

    # --- ライブラリフォルダ ---
    def _draw_lib_list(self):
        for w in self.lib_box.winfo_children():
            w.destroy()
        a = self.app
        head = ctk.CTkFrame(self.lib_box, fg_color="transparent")
        head.pack(fill="x")
        ctk.CTkLabel(head, text="ライブラリに含めるフォルダ", font=F(13, "bold"), text_color=TEXT).pack(side="left")
        ctk.CTkButton(head, text="＋ 追加", width=80, height=30, corner_radius=15, fg_color=CARD_2, hover_color=HOVER,
                      font=F(12, "bold"), command=a.add_library_folder).pack(side="right")
        ctk.CTkLabel(self.lib_box, text=str(Path(a.cfg.get("outdir", "")) / "Music") + "  (既定)", font=F(11),
                     text_color=MUTED, anchor="w").pack(fill="x", pady=(2, 0))
        for p in a.cfg.get("library_extra", []):
            ctk.CTkButton(self.lib_box, text=f"✕  {p}", anchor="w", height=26, corner_radius=8, fg_color="transparent",
                          hover_color=CARD_2, text_color=MUTED, font=F(11),
                          command=lambda p=p: a.remove_library_folder(p)).pack(fill="x")

    def _need_restart(self):
        if self.restart_btn is None:
            self.restart_btn = ctk.CTkButton(self.tool_foot, text="今すぐ再起動して反映", height=34, corner_radius=17,
                                             fg_color=ACCENT, hover_color=ACCENT_H, font=F(12, "bold"), command=self.app.restart)
        self.restart_btn.pack(anchor="w")

    def _set_device(self, name):
        self.app.engine.set_device(None if name == "既定" else name)

    # --- ツール ---
    def log(self, text):
        self.tool_log.configure(state="normal")
        self.tool_log.insert("end", text + "\n")
        self.tool_log.configure(state="disabled")
        self.tool_log.see("end")

    def refresh_tools(self):
        def work():
            dp = deno_path()
            dv = tool_version(dp) if dp else ""
            ff, ffdir = find_ffmpeg()
            fv = tool_version(ffmpeg_exe(), ("-version",)) if ff else ""
            return dp, dv, ff, fv

        def done(res):
            if not res:
                return
            dp, dv, ff, fv = res
            self.lbl_deno.configure(text=(f"{dv.split(' (')[0]}  ✔" if dv else "導入済み ✔") if dp else "未導入 (YouTubeに必要)",
                                    text_color=OK if dp else WARN)
            self.lbl_ff.configure(text=(fv.split(' Copyright')[0][:48] + "  ✔") if ff else "未導入", text_color=OK if ff else ERR)
            self.app.deno_missing = not dp
            if self.app.dl_ready:
                self.app.dl.refresh_banner()
        self.app.run_bg(work, done)

    def check_latest(self):
        self.lbl_ytdlp.configure(text=f"バージョン {ytdlp_version()} / 確認中…", text_color=MUTED)

        def work():
            return latest_ytdlp_version()

        def done(v):
            cur = ytdlp_version()
            if not v:
                self.lbl_ytdlp.configure(text=f"バージョン {cur} / 最新版を確認できませんでした", text_color=WARN)
                return
            newer = ver_tuple(v) > ver_tuple(cur)
            self.lbl_ytdlp.configure(text=f"バージョン {cur} / " + (f"新しい版 {v} があります" if newer else "最新です ✔"),
                                     text_color=WARN if newer else OK)
            self.app.sidebar.mark_update(newer)
        self.app.run_bg(work, done)

    def update_ytdlp(self, nightly=False):
        self.log(f"yt-dlp を{'ナイトリー版へ' if nightly else '安定版へ'}更新します…")
        cmd = [sys.executable, "-m", "pip", "install", "-U", "--no-input"] + (["--pre"] if nightly else []) + ["yt-dlp[default]"]

        def work():
            try:
                rc = run_stream(cmd, lambda ln: self.ui(lambda ln=ln: self.log(ln)))
            except Exception as e:
                self.ui(lambda e=e: self.log(f"失敗: {e}"))
                return -1
            return rc

        def done(rc):
            if rc == 0:
                self.log("✔ 更新しました。再起動すると反映されます。")
                self._need_restart()
                self.app.sidebar.mark_update(False)
            else:
                self.log("✖ 更新に失敗しました。ログを確認してください。")
        self.app.run_bg(work, done)

    def install_deno(self):
        self.deno_bar.grid()
        self.deno_bar.set(0)
        self.log("Deno をダウンロードしています…")

        def prog(done, total):
            if total:
                self.ui(lambda: self.deno_bar.set(done / total))

        def work():
            try:
                return install_deno(prog)
            except Exception as e:
                return f"ERR:{e}"

        def done(res):
            self.deno_bar.grid_remove()
            if res and not str(res).startswith("ERR:"):
                self.log(f"✔ Deno を導入しました: {res}")
            else:
                self.log(f"✖ Deno の導入に失敗しました: {str(res)[4:] if res else ''}")
            self.refresh_tools()
        self.app.run_bg(work, done)

    def remove_deno(self):
        p = BIN_DIR / deno_exe_name()
        try:
            p.unlink()
            self.log("アプリ内のDenoを削除しました。")
        except FileNotFoundError:
            self.log("アプリ内にDenoはありません。(システムのDenoはそのままです)")
        except Exception as e:
            self.log(f"削除に失敗: {e}")
        self.refresh_tools()

    def install_ffmpeg(self):
        if os.name == "nt":
            cmd = ["winget", "install", "--id", "Gyan.FFmpeg", "-e", "--accept-source-agreements", "--accept-package-agreements"]
        elif sys.platform == "darwin" and shutil.which("brew"):
            cmd = ["brew", "install", "ffmpeg"]
        else:
            self.log("お使いの環境ではパッケージマネージャで導入してください。例: sudo apt install ffmpeg")
            return
        self.log("FFmpeg を導入します…(数分かかることがあります)")

        def work():
            try:
                return run_stream(cmd, lambda ln: self.ui(lambda ln=ln: self.log(ln)))
            except Exception as e:
                self.ui(lambda e=e: self.log(f"失敗: {e}"))
                return -1

        def done(rc):
            self.log("✔ 完了。アプリを再起動すると認識されます。" if rc == 0 else "✖ 失敗しました。")
            if rc == 0:
                self._need_restart()
            self.refresh_tools()
        self.app.run_bg(work, done)

    def reset_all(self):
        if messagebox.askyesno(APP_NAME, "設定を初期化して再起動しますか？\n(お気に入り・プレイリスト・ダウンロード済みの曲は消えません)"):
            try:
                SETTINGS_FILE.unlink()
            except Exception:
                pass
            self.app.cfg = {}
            self.app.restart(save=False)


# ───────────────────────── ページ: 検索 (ライブラリ + オンライン → そのまま再生) ─────────────────────────
class SearchPage(ctk.CTkFrame):
    def __init__(self, master, app):
        super().__init__(master, fg_color=BG, corner_radius=0)
        self.app = app
        self.rows, self.token, self.query = [], 0, ""
        self.thumbs = {}
        self.ph = ImageTk.PhotoImage(Image.new("RGB", (96, 54), (29, 34, 48)))
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(2, weight=1)

        head = ctk.CTkFrame(self, fg_color="transparent")
        head.grid(row=0, column=0, sticky="ew", padx=32, pady=(14, 4))
        page_title(head, "検索").pack(side="left")
        self.status = ctk.CTkLabel(head, text="", font=F(13), text_color=MUTED)
        self.status.pack(side="left", padx=14, pady=(10, 0))

        bar = ctk.CTkFrame(self, fg_color="transparent")
        bar.grid(row=1, column=0, sticky="ew", padx=32, pady=(2, 10))
        self.src = ctk.CTkSegmentedButton(bar, values=SEARCH_SOURCES, command=self._src_changed, height=34, fg_color=CARD,
                                          selected_color=ACCENT, selected_hover_color=ACCENT_H, unselected_color=CARD,
                                          unselected_hover_color=CARD_2, font=F(12, "bold"))
        self.src.set(app.cfg.get("search_src", "YouTube") if app.cfg.get("search_src") in SEARCH_SOURCES else "YouTube")
        self.src.pack(side="left")
        self.short_v = ctk.BooleanVar(value=app.cfg.get("search_short", True))
        ctk.CTkSwitch(bar, text="10分以下の曲だけ", variable=self.short_v, font=F(12), text_color=TEXT, progress_color=ACCENT,
                      button_color="#ffffff", command=self._short_changed).pack(side="left", padx=18)
        pill_btn(bar, "↓ ダウンロード", self.download_selected, width=130).pack(side="right")
        pill_btn(bar, "▶ すべて再生", self.play_all, primary=True, width=120).pack(side="right", padx=8)

        wrap = ctk.CTkFrame(self, fg_color=CARD, corner_radius=16)
        wrap.grid(row=2, column=0, sticky="nsew", padx=32, pady=(0, 18))
        wrap.grid_columnconfigure(0, weight=1)
        wrap.grid_rowconfigure(0, weight=1)
        self.tree = ttk.Treeview(wrap, columns=("by", "dur", "views", "src"), show="tree headings",
                                 style="Search.Treeview", selectmode="extended")
        for col, text, w, anc in (("#0", "タイトル", 520, "w"), ("by", "チャンネル / アーティスト", 200, "w"),
                                  ("dur", "時間", 70, "e"), ("views", "再生数", 90, "e"), ("src", "サイト", 90, "w")):
            self.tree.heading(col, text=text, anchor=anc)
            self.tree.column(col, width=w, minwidth=50, anchor=anc, stretch=col in ("#0", "by"))
        self.tree.tag_configure("playing", foreground=ACCENT)
        sb = ctk.CTkScrollbar(wrap, command=self.tree.yview, fg_color="transparent")
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.grid(row=0, column=0, sticky="nsew", padx=(10, 0), pady=10)
        sb.grid(row=0, column=1, sticky="ns", pady=10, padx=(2, 4))
        self.tree.bind("<Double-1>", self._activate)
        self.tree.bind("<Return>", self._activate)
        self.tree.bind("<Button-3>", self._menu)
        self.tree.bind("<Button-2>", self._menu)

        self.empty = ctk.CTkFrame(wrap, fg_color="transparent")
        self.empty_lbl = ctk.CTkLabel(self.empty, text="", font=F(15), text_color=MUTED, justify="center")
        self.empty_lbl.pack()
        self.chips = ctk.CTkFrame(self.empty, fg_color="transparent")
        self.chips.pack(pady=14)

    # --- 表示 ---
    def on_show(self, q=None, **kw):
        if q and (q != self.query or not self.rows):
            self.run(q)
        elif not self.rows:
            self._empty("曲名・アーティスト名を上の検索欄に入力して Enter\n(YouTubeのURLを貼ると、そのまま再生できます)")

    def _empty(self, text, chips=True):
        self.empty_lbl.configure(text=text)
        for w in self.chips.winfo_children():
            w.destroy()
        if chips:
            for h in self.app.cfg.get("history", [])[:8]:
                ctk.CTkButton(self.chips, text=h, height=30, corner_radius=15, fg_color=CARD_2, hover_color=HOVER,
                              font=F(12), command=lambda h=h: self.app.search(h)).pack(side="left", padx=4)
        self.empty.place(relx=0.5, rely=0.4, anchor="center")

    def _src_changed(self, v):
        self.app.set_cfg("search_src", v)
        if self.query:
            self.run(self.query)

    def _short_changed(self):
        self.app.set_cfg("search_short", self.short_v.get())
        if self.query:
            self.run(self.query)

    def run(self, query):
        q = query.strip()
        if not q:
            return
        a = self.app
        self.query = q
        self.token += 1
        tok = self.token
        a.add_history(q)
        self.status.configure(text="検索中…")
        local = a.search_local(q, 8)
        self._fill(local, [])
        if not local:
            self._empty("検索中…", chips=False)
        labels = SEARCH_SOURCES[:3] if self.src.get() == "すべて" else [self.src.get()]
        n = 14 if len(labels) > 1 else 28
        short = self.short_v.get()

        def done(res):
            if tok != self.token:
                return
            remote = [r for r in (res or []) if not short or not r.get("dur") or r["dur"] <= 600]
            self._fill(local, remote)
            total = len(local) + len(remote)
            self.status.configure(text=f"{total}件" if total else "")
            if not total:
                self._empty("見つかりませんでした。\nサイトを変えるか、設定 > ツール で yt-dlp / Deno を更新してください。", chips=False)
        a.run_bg(lambda: online_search(q, labels, n, a.cfg), done)

    def _fill(self, local, remote):
        self.tree.delete(*self.tree.get_children())
        self.thumbs = {}
        self.rows = list(local) + [remote_track(r) for r in remote]
        cur = self.app.current_path()
        for i, t in enumerate(self.rows):
            is_local = not t.get("remote")
            self.tree.insert("", "end", iid=str(i), text="  " + t["title"], image=self.ph,
                             values=(t["artist"], fmt_dur(t.get("dur")), fmt_views(t.get("views")) if not is_local else "",
                                     "ライブラリ" if is_local else t.get("src", "")),
                             tags=("playing",) if t["path"] == cur else ())
        if self.rows:
            self.empty.place_forget()
        tok = self.token
        for i, t in enumerate(self.rows):
            self._load_thumb(tok, i, t)

    def _load_thumb(self, tok, i, t):
        if t.get("remote") and not t.get("thumb"):
            return

        def work():
            im = self.app.covers.get(t, 108)
            return ImageOps.fit(im, (96, 54), Image.LANCZOS) if im is not None else None

        def done(im, iid=str(i)):
            if tok != self.token or im is None or not self.tree.exists(iid):
                return
            ph = ImageTk.PhotoImage(round_image(im, 0.1))
            self.thumbs[iid] = ph
            self.tree.item(iid, image=ph)
        if t.get("remote"):
            def work_r():
                im = Image.open(io.BytesIO(http_get(t["thumb"], 8))).convert("RGB")
                return ImageOps.fit(im, (96, 54), Image.LANCZOS)
            self.app.run_bg(work_r, done)
        else:
            self.app.run_bg(work, done)

    def refresh_playing(self):
        cur = self.app.current_path()
        for i, t in enumerate(self.rows):
            iid = str(i)
            if self.tree.exists(iid):
                self.tree.item(iid, tags=("playing",) if t["path"] == cur else ())

    # --- 操作 ---
    def selected(self):
        return [self.rows[int(i)] for i in self.tree.selection() if i.isdigit() and int(i) < len(self.rows)]

    def _activate(self, e=None):
        sel = self.tree.selection()
        if not sel:
            return
        if e is not None and str(getattr(e, "type", "")) == "4" and self.tree.identify_region(e.x, e.y) not in ("tree", "cell"):
            return
        self.app.play_list(self.rows, int(sel[0]))

    def play_all(self):
        if self.rows:
            self.app.play_list(self.rows, 0)

    def download_selected(self):
        sel = [t for t in self.selected() if t.get("remote")] or [t for t in self.rows if t.get("remote")]
        self.app.download_remote(sel)

    def _menu(self, e):
        iid = self.tree.identify_row(e.y)
        if iid and iid not in self.tree.selection():
            self.tree.selection_set(iid)
        sel = self.selected()
        if not sel:
            return
        a, t0 = self.app, sel[0]
        m = tk.Menu(self, tearoff=0, bg=CARD_2, fg=TEXT, activebackground=ACCENT, activeforeground="white",
                    bd=0, relief="flat", font=(FONT_FAMILY, 10))
        m.add_command(label="▶  再生", command=lambda: a.play_list(self.rows, self.rows.index(t0)))
        m.add_command(label="次に再生", command=lambda: a.play_next(sel))
        m.add_command(label="キューに追加", command=lambda: a.add_queue(sel))
        if t0.get("remote"):
            m.add_separator()
            m.add_command(label="↓  ダウンロード(選択した曲)", command=lambda: a.download_remote([t for t in sel if t.get("remote")]))
            m.add_command(label="ブラウザで開く", command=lambda: webbrowser.open(t0["path"]))
            if t0["artist"]:
                m.add_command(label=f"「{t0['artist']}」の曲を検索", command=lambda: a.search(t0["artist"]))
        else:
            m.add_command(label="アーティストページへ", command=lambda: a.open_artist(t0["artist"]))
        try:
            m.tk_popup(e.x_root, e.y_root)
        finally:
            m.grab_release()


# ───────────────────────── 試聴(ストリーミング)の解決 ─────────────────────────
def resolve_stream(url, cfg):
    o = {"quiet": True, "no_warnings": True, "noplaylist": True, "format": "bestaudio/best",
         "socket_timeout": 15, "logger": _Silent()}
    o.update(ydl_common(cfg))
    try:
        with yt_dlp.YoutubeDL(o) as ydl:
            info = ydl.extract_info(url, download=False)
        if info and info.get("entries"):
            info = next((e for e in info["entries"] if e), None)
        if not info or not info.get("url"):
            return ("err", "再生用URLを取得できませんでした")
        meta = {"title": info.get("title"), "uploader": info.get("uploader") or info.get("channel"),
                "thumbnail": info.get("thumbnail")}
        return ("ok", info["url"], info.get("http_headers"), info.get("duration"), meta)
    except Exception as e:
        return ("err", str(e)[:200])


# ───────────────────────── アプリ本体 ─────────────────────────
class App(ctk.CTk):
    NAV_OF = {"album": "albums", "artist": "artists", "playlist": "playlists", "favorites": "playlists"}

    def __init__(self):
        self.cfg = load_settings()
        self.cfg.setdefault("outdir", str(Path.home() / "Downloads" / "MusicDL"))
        apply_theme(self.cfg.get("accent", "バイオレット"))
        ctk.set_appearance_mode("dark")
        ctk.set_default_color_theme("blue")
        super().__init__()
        self.font = FONT_FAMILY
        self.title(APP_NAME)
        self.geometry(self.cfg.get("geometry", "1320x840"))
        self.minsize(1040, 700)
        self.configure(fg_color=BG)
        activate_deno_path()

        self.q = queue.Queue()
        self.cancel = threading.Event()
        self.pool = ThreadPoolExecutor(max_workers=8)
        self.user, self.lib, self.covers, self.engine = UserData(), Library(), Covers(), AudioEngine()
        self.engine.volume = float(self.cfg.get("volume", 0.8))
        dev = self.cfg.get("device", "既定")
        self.engine.device = None if dev in ("既定", None) else dev

        self.queue, self.orig, self.pos = [], [], -1
        self.cur = None
        self.shuffle = bool(self.cfg.get("shuffle", False))
        self.repeat = self.cfg.get("repeat", "off")
        self.lyrics, self.lyr_state = None, "none"
        self.play_token, self.counted, self.fail_count = 0, False, 0
        self.loading = False
        self.deno_missing = False
        self.dl_ready = False
        self.pages, self.page_name, self.page_kw, self.nav_hist = {}, None, {}, []
        self._ph, self._ctk = {}, {}
        self._scanning = False
        self._toast_id = 0
        self._prev_vol = 0.8

        self._setup_styles()
        self._build()
        self._pump_id = self.after(60, self._pump)
        self._tick_id = self.after(100, self._tick)
        self.protocol("WM_DELETE_WINDOW", self._close)
        self._bind_keys()

        self.bar.set_modes(self.shuffle, self.repeat)
        self.lib.set_tracks(self.lib.cached_tracks())
        self._library_changed(refresh=False)
        if self.cfg.get("scan_on_start", True) or not self.lib.tracks:
            self.rescan_library()
        self.show(SettingsPage.STARTUP.get(self.cfg.get("startup", "検索"), "search"), push=False)
        self._startup_checks()

    # --- 共通 ---
    def card(self, parent):
        return ctk.CTkFrame(parent, fg_color=CARD, corner_radius=18)

    def set_cfg(self, key, value):
        self.cfg[key] = value
        save_settings(self.cfg)

    def run_bg(self, work, done=None):
        def task():
            try:
                res = work()
            except Exception:
                res = None
            if done:
                self.q.put(("call", lambda: done(res)))
        try:
            self.pool.submit(task)
        except RuntimeError:
            pass

    def toast(self, text, ms=2600):
        self._toast_id += 1
        i = self._toast_id
        self.toast_lbl.configure(text=text)
        self.toast_lbl.place(relx=0.5, rely=1.0, y=-116, anchor="s")
        self.toast_lbl.lift()
        self.after(ms, lambda: self.toast_lbl.place_forget() if i == self._toast_id else None)

    def _setup_styles(self):
        st = ttk.Style(self)
        try:
            st.theme_use("clam")
        except Exception:
            pass
        st.configure("Music.Treeview", background=CARD, fieldbackground=CARD, foreground=TEXT, rowheight=40,
                     borderwidth=0, relief="flat", font=(FONT_FAMILY, 11))
        st.map("Music.Treeview", background=[("selected", HOVER)], foreground=[("selected", "#ffffff")])
        st.configure("Music.Treeview.Heading", background=CARD, foreground=MUTED, relief="flat", borderwidth=0,
                     font=(FONT_FAMILY, 10, "bold"), padding=(6, 6))
        st.map("Music.Treeview.Heading", background=[("active", CARD_2)])
        st.layout("Music.Treeview", [("Treeview.treearea", {"sticky": "nswe"})])
        st.configure("Search.Treeview", background=CARD, fieldbackground=CARD, foreground=TEXT, rowheight=64,
                     borderwidth=0, relief="flat", font=(FONT_FAMILY, 11))
        st.map("Search.Treeview", background=[("selected", HOVER)], foreground=[("selected", "#ffffff")])
        st.configure("Search.Treeview.Heading", background=CARD, foreground=MUTED, relief="flat", borderwidth=0,
                     font=(FONT_FAMILY, 10, "bold"), padding=(6, 6))
        st.map("Search.Treeview.Heading", background=[("active", CARD_2)])
        st.layout("Search.Treeview", [("Treeview.treearea", {"sticky": "nswe"})])

    def _build(self):
        self.grid_columnconfigure(1, weight=1)
        self.grid_rowconfigure(0, weight=1)
        self.sidebar = Sidebar(self, self)
        self.sidebar.grid(row=0, column=0, sticky="ns")
        self.content = ctk.CTkFrame(self, fg_color=BG, corner_radius=0)
        self.content.grid(row=0, column=1, sticky="nsew")
        self.content.grid_columnconfigure(0, weight=1)
        self.content.grid_rowconfigure(1, weight=1)
        top = ctk.CTkFrame(self.content, fg_color=BG, height=66, corner_radius=0)
        top.grid(row=0, column=0, sticky="ew")
        top.grid_columnconfigure(1, weight=1)
        ctk.CTkButton(top, text="‹", width=42, height=42, corner_radius=21, fg_color=CARD, hover_color=CARD_2,
                      text_color=TEXT, font=F(22, "bold"), command=self.back).grid(row=0, column=0, padx=(24, 12), pady=12)
        self.search_entry = ctk.CTkEntry(top, height=44, corner_radius=22, fg_color=CARD, border_width=0, font=F(14),
                                         placeholder_text="曲名・アーティスト名・URL を入力して Enter  (Ctrl+K)")
        self.search_entry.grid(row=0, column=1, sticky="ew", padx=(0, 28), pady=11)
        self.search_entry.bind("<Return>", lambda e: self.search(self.search_entry.get()))
        self.bar = PlayerBar(self, self)
        self.bar.grid(row=1, column=0, columnspan=2, sticky="ew")
        self.toast_lbl = ctk.CTkLabel(self, text="", fg_color=CARD_2, corner_radius=16, text_color=TEXT,
                                      font=F(12, "bold"), height=34)
        self.dl = DownloadPage(self.content, self)
        self.pages["download"] = self.dl
        self.dl_ready = True
        self.dl._log("準備OK。URLか検索ワードを入力してください。" if find_ffmpeg()[0] else
                     "FFmpegが見つかりません。設定 > ツール から導入できます。", "info" if find_ffmpeg()[0] else "err")

    def _bind_keys(self):
        def guard(fn):
            def h(e):
                w = self.focus_get()
                if isinstance(w, (tk.Entry, tk.Text, ttk.Entry)):
                    return
                fn()
            return h
        self.bind_all("<space>", guard(self.toggle_play))
        self.bind_all("<Left>", guard(lambda: self.seek_to(max(0, self.engine.position() - 5))))
        self.bind_all("<Right>", guard(lambda: self.seek_to(self.engine.position() + 5)))
        self.bind_all("<Control-Left>", lambda e: self.prev())
        self.bind_all("<Control-Right>", lambda e: self.next())
        self.bind_all("<F11>", lambda e: self.toggle_fullscreen())
        self.bind_all("<Control-k>", lambda e: (self.search_entry._entry.focus_set(), "break")[1])
        self.bind_all("<slash>", guard(lambda: self.search_entry._entry.focus_set()))
        self.bind_all("<Escape>", lambda e: self.attributes("-fullscreen", False))

    def toggle_fullscreen(self):
        self.attributes("-fullscreen", not bool(self.attributes("-fullscreen")))

    # --- ナビゲーション ---
    def get_page(self, name):
        if name in self.pages:
            return self.pages[name]
        make = {"search": SearchPage, "home": HomePage, "songs": SongsPage, "albums": AlbumsPage, "artists": ArtistsPage,
                "playlists": PlaylistsPage, "detail": DetailPage, "now": NowPlayingPage, "settings": SettingsPage}[name]
        p = make(self.content, self)
        self.pages[name] = p
        if name == "now":
            p.track_changed()
            p.set_lyrics(self.lyrics, self.lyr_state)
        return p

    def show(self, name, push=True, **kw):
        page = self.get_page(name)
        old = self.pages.get(self.page_name)
        if push and self.page_name:
            self.nav_hist = (self.nav_hist + [(self.page_name, self.page_kw)])[-30:]
        if old is not None and old is not page:
            if hasattr(old, "on_hide"):
                old.on_hide()
            old.grid_remove()
        self.page_name, self.page_kw = name, kw
        page.grid(row=1, column=0, sticky="nsew")
        if hasattr(page, "on_show"):
            page.on_show(**kw)
        nav = self.NAV_OF.get(kw.get("kind"), "") if name == "detail" else name
        self.sidebar.highlight(nav)

    def back(self):
        if self.nav_hist:
            name, kw = self.nav_hist.pop()
            self.show(name, push=False, **kw)
        else:
            self.show("home", push=False)

    def open_artist(self, name):
        self.show("detail", kind="artist", key=name)

    def open_album(self, key):
        self.show("detail", kind="album", key=key)

    def open_current_artist(self):
        if self.cur and not self.cur.get("remote"):
            self.open_artist(self.cur["artist"])

    def open_search(self, query=None):
        if query:
            self.search(query)
        else:
            self.show("search")
            try:
                self.search_entry._entry.focus_set()
            except Exception:
                pass

    def search(self, text):
        text = (text or "").strip()
        if not text:
            return
        if re.match(r"^https?://", text):
            self.open_url(text)
            return
        self.search_entry.delete(0, "end")
        self.search_entry.insert(0, text)
        self.show("search", q=text)

    def open_url(self, url):
        t = remote_track({"url": url, "title": url, "uploader": "", "dur": 0})
        self.search_entry.delete(0, "end")
        self.play_list([t], 0, shuffle=False)

    def search_local(self, q, n=8):
        ql = q.casefold()
        return [t for t in self.lib.tracks if ql in (t["title"] + " " + t["artist"] + " " + (t.get("album") or "")).casefold()][:n]

    def add_history(self, q):
        h = [x for x in self.cfg.get("history", []) if x != q]
        self.set_cfg("history", ([q] + h)[:12])

    def download_remote(self, tracks):
        urls = [t["path"] for t in tracks if t.get("remote")]
        if not urls:
            self.toast("ダウンロードできる曲がありません")
            return
        self.dl.add_to_queue(urls, start=True)
        self.toast(f"{len(urls)}件をダウンロードに追加しました" + ("(実行中のため、終わったら『開始』を押してください)" if self.dl.busy else ""))

    def download_current(self):
        if self.cur and self.cur.get("remote"):
            self.download_remote([self.cur])

    def add_to_queue(self, urls, start=False):
        self.dl.add_to_queue(urls, start=start)

    # --- 画像 ---
    def placeholder_img(self, size, seed, circle=False, ratio=0.07):
        k = (size, seed, circle, ratio)
        if k not in self._ph:
            im = round_image(make_placeholder(size, seed), 0.5 if circle else ratio)
            self._ph[k] = ctk.CTkImage(light_image=im, dark_image=im, size=(size, size))
        return self._ph[k]

    def ctk_img(self, pil, size, circle=False, ratio=0.07):
        k = (id(pil), size, circle, ratio)
        if k not in self._ctk:
            im = round_image(pil, 0.5 if circle else ratio)
            self._ctk[k] = (pil, ctk.CTkImage(light_image=im, dark_image=im, size=(size, size)))
        return self._ctk[k][1]

    def tk_placeholder(self, size, seed, circle=False):
        k = ("tk", size, seed, circle)
        if k not in self._ph:
            self._ph[k] = ImageTk.PhotoImage(round_image(make_placeholder(size, seed), 0.5 if circle else 0.07))
        return self._ph[k]

    def tk_cover(self, pil, size, circle=False):
        return ImageTk.PhotoImage(round_image(pil, 0.5 if circle else 0.07))

    def cover_pil(self, tracks, size, artist, cb):
        """ジャケット(またはアーティスト画像)を取得してcb(PIL or None)。キャッシュにあれば即時"""
        online_artist = bool(artist) and self.cfg.get("artist_online", True)
        if not online_artist and tracks:
            for t in tracks[:4]:
                c = self.covers.cached(t, size)
                if isinstance(c, Image.Image):
                    cb(c)
                    return
            if all(self.covers.cached(t, size) is None for t in tracks[:4]):
                return

        def work():
            im = fetch_artist_image(artist, size) if online_artist else None
            return im if im is not None else self.covers.get_any(tracks, size)
        self.run_bg(work, cb)

    def load_cover(self, label, tracks, size, circle=False, artist=None, ratio=0.07, disp=None):
        """size=取得する画像の解像度 / disp=画面上の表示サイズ(省略時はsizeと同じ)"""
        if not tracks:
            return
        disp = disp or size
        online_artist = bool(artist) and self.cfg.get("artist_online", True)
        if not online_artist:
            for t in tracks[:4]:
                c = self.covers.cached(t, size)
                if isinstance(c, Image.Image):
                    label.configure(image=self.ctk_img(c, disp, circle, ratio))
                    return

        def work():
            im = fetch_artist_image(artist, size) if online_artist else None
            return im if im is not None else self.covers.get_any(tracks, size)

        def done(im):
            try:
                if im is not None and label.winfo_exists():
                    label.configure(image=self.ctk_img(im, disp, circle, ratio))
            except Exception:
                pass
        self.run_bg(work, done)

    # --- ライブラリ ---
    def library_dirs(self):
        dirs = [str(Path(self.cfg.get("outdir", str(Path.home() / "Downloads" / "MusicDL"))) / "Music")]
        dirs += self.cfg.get("library_extra", [])
        return [d for d in dirs if os.path.isdir(d)]

    def rescan_library(self):
        if self._scanning:
            return
        self._scanning = True
        dirs = self.library_dirs()
        self.sidebar.set_stats("ライブラリを読み込み中…")

        def done(tracks):
            self._scanning = False
            if tracks is not None:
                self.lib.set_tracks(tracks)
            self._library_changed()
        self.run_bg(lambda: self.lib.scan(dirs), done)

    def _library_changed(self, refresh=True):
        n = len(self.lib.tracks)
        self.sidebar.set_stats(f"ライブラリ {n}曲\n{len(self.lib.artists)}アーティスト" if n else "ライブラリは空です")
        if refresh and self.page_name in ("home", "songs", "albums", "artists", "playlists", "detail"):
            p = self.pages.get(self.page_name)
            if p is not None:
                try:
                    p.on_show(**self.page_kw)
                except Exception:
                    pass

    def add_library_folder(self):
        d = filedialog.askdirectory(title="音楽フォルダを選択")
        if d:
            extra = self.cfg.get("library_extra", [])
            if d not in extra:
                self.set_cfg("library_extra", extra + [d])
            self._settings_refresh()
            self.rescan_library()

    def remove_library_folder(self, d):
        self.set_cfg("library_extra", [x for x in self.cfg.get("library_extra", []) if x != d])
        self._settings_refresh()
        self.rescan_library()

    def _settings_refresh(self):
        p = self.pages.get("settings")
        if p is not None:
            p._draw_lib_list()

    def choose_outdir(self):
        d = filedialog.askdirectory(initialdir=self.cfg.get("outdir") or str(Path.home()))
        if d:
            self.set_outdir(d)

    def set_outdir(self, path, from_dl=False):
        if not path or path == self.cfg.get("outdir"):
            return
        self.set_cfg("outdir", path)
        if not from_dl:
            self.dl.set_outdir(path)
        p = self.pages.get("settings")
        if p is not None:
            p.out_lbl.configure(text=path)
            p._draw_lib_list()
        self.rescan_library()

    # --- 再生制御 ---
    def current_path(self):
        return self.cur["path"] if self.cur else None

    def cur_dur(self):
        if not self.cur:
            return 0
        s = self.engine.sess
        return self.cur.get("dur") or (s.duration if s else 0) or 0

    def play_list(self, tracks, index=0, shuffle=None):
        tracks = list(tracks)
        if not tracks:
            return
        if shuffle is not None:
            self.shuffle = bool(shuffle)
        self.orig = list(tracks)
        if self.shuffle:
            if shuffle:
                index = random.randrange(len(tracks))
            first = tracks[index]
            rest = tracks[:index] + tracks[index + 1:]
            random.shuffle(rest)
            self.queue, self.pos = [first] + rest, 0
        else:
            self.queue, self.pos = tracks, index
        self.bar.set_modes(self.shuffle, self.repeat)
        self._start_pos()

    def _start_pos(self, start=0.0):
        if 0 <= self.pos < len(self.queue):
            self._start_track(self.queue[self.pos], start)

    def _start_track(self, t, start=0.0):
        self.play_token += 1
        token = self.play_token
        self.cur, self.counted, self.lyrics = t, False, None
        self.bar.set_track(t)
        self.bar.set_progress(0, t.get("dur") or 0)
        self.bar.cover.configure(image=self.placeholder_img(64, t["title"], False, 0.12))
        self.load_cover(self.bar.cover, [t], 128, False, None, 0.12, disp=64)
        self.title(f"▶ {t['title']} — {t['artist']}")
        self.loading = False
        if "now" in self.pages:
            self.pages["now"].track_changed()
        self._refresh_tables()
        self._load_lyrics(t, token)
        if t.get("remote"):
            self.engine.stop()
            self.loading = True
            cached = t.get("_res")
            if cached and time.time() - cached[0] < 1500:
                self.after(5, lambda: self._remote_ready(cached[1], token, t))
            else:
                self.toast("読み込み中…", 1800)
                self.run_bg(lambda: resolve_stream(t["path"], self.cfg), lambda res: self._remote_ready(res, token, t))
        else:
            if not self.engine.play(t["path"], start, duration=t.get("dur") or 0):
                self.toast(self.engine.error or "再生できません")
        self.bar.set_playing(self.engine.sess is not None or self.loading)
        self._prefetch_next()

    def _prefetch_next(self):
        """次の曲(オンライン)の再生URLを先に解決しておく → 曲間がほぼ待たずにつながる"""
        n = self.pos + 1
        if self.repeat == "one" or n >= len(self.queue):
            return
        t = self.queue[n]
        if not t.get("remote") or t.get("_res") or t.get("_pf"):
            return
        t["_pf"] = True

        def done(res):
            t["_pf"] = False
            if res and res[0] == "ok":
                t["_res"] = (time.time(), res)
        self.run_bg(lambda: resolve_stream(t["path"], self.cfg), done)

    def _remote_ready(self, res, token, t):
        if token != self.play_token:
            return
        self.loading = False
        if not res or res[0] != "ok":
            self.toast("試聴できませんでした: " + (res[1] if res else "不明なエラー"), 4500)
            self.bar.set_playing(False)
            self.fail_count += 1
            if self.fail_count < 3 and self.pos + 1 < len(self.queue):
                self.after(900, lambda: self.next(auto=True) if token == self.play_token else None)
            else:
                self.fail_count = 0
            return
        self.fail_count = 0
        _, url, headers, dur, meta = res
        if dur:
            t["dur"] = dur
        if t["title"] == t["path"] and meta.get("title"):  # URL直接入力: 取得できたタイトル等を反映
            t["title"] = meta["title"]
            t["artist"] = clean_artist(meta.get("uploader") or "")
            t["thumb"] = meta.get("thumbnail")
            self.bar.set_track(t)
            self.load_cover(self.bar.cover, [t], 128, False, None, 0.12, disp=64)
            self.title(f"▶ {t['title']} — {t['artist']}")
            if "now" in self.pages:
                self.pages["now"].track_changed()
            self._load_lyrics(t, token)
        if not self.engine.play(url, 0.0, headers=headers, duration=dur or 0):
            self.toast(self.engine.error or "再生できません")
        self.bar.set_playing(self.engine.sess is not None)

    def _load_lyrics(self, t, token, force_online=False):
        online = force_online or self.cfg.get("lyrics_online", True)
        self.lyr_state = "loading"

        def done(res):
            if token != self.play_token:
                return
            self.lyrics, self.lyr_state = res, ("ok" if res else "none")
            if "now" in self.pages:
                self.pages["now"].set_lyrics(res, self.lyr_state)
            if force_online and not res:
                self.toast("歌詞が見つかりませんでした")
        self.run_bg(lambda: load_lyrics(t, online), done)

    def fetch_lyrics_online(self):
        if self.cur:
            if "now" in self.pages:
                self.pages["now"].set_lyrics(None, "loading")
            self._load_lyrics(self.cur, self.play_token, force_online=True)

    def toggle_play(self):
        if self.cur is None:
            if self.lib.tracks:
                self.play_list(self.lib.tracks, 0)
            return
        if self.loading:
            return
        if self.engine.sess is None:
            self._start_pos()
            return
        self.engine.paused = not self.engine.paused
        self.bar.set_playing(not self.engine.paused)

    def next(self, auto=False):
        if not self.queue:
            return
        if auto and self.repeat == "one":
            self._start_pos()
            return
        if self.pos + 1 < len(self.queue):
            self.pos += 1
            self._start_pos()
        elif self.repeat == "all" or not auto:
            if self.shuffle and len(self.queue) > 1:
                rest = self.queue[1:]
                random.shuffle(rest)
                self.queue = [self.queue[0]] + rest
            self.pos = 0
            self._start_pos()
        else:
            self.engine.stop()
            self.bar.set_playing(False)
            self.bar.set_progress(0, self.cur_dur())

    def prev(self):
        if not self.queue:
            return
        if self.engine.position() > 3 or self.pos <= 0:
            self._start_pos()
        else:
            self.pos -= 1
            self._start_pos()

    def jump_to(self, i):
        if 0 <= i < len(self.queue):
            self.pos = i
            self._start_pos()

    def seek_frac(self, f):
        d = self.cur_dur()
        if d:
            self.seek_to(f * d)

    def seek_to(self, sec):
        if self.engine.sess is not None:
            d = self.cur_dur()
            self.engine.seek(min(max(0, sec), d - 0.5 if d else sec))
            self.bar.set_playing(True)

    def set_volume(self, v):
        self.engine.volume = float(v)
        self.cfg["volume"] = float(v)
        self.bar.b_vol.configure(text="♬" if v > 0 else "✕")

    def toggle_mute(self):
        if self.engine.volume > 0:
            self._prev_vol = self.engine.volume
            self.bar.vol.set(0)
            self.set_volume(0)
        else:
            self.bar.vol.set(self._prev_vol)
            self.set_volume(self._prev_vol)

    def toggle_shuffle(self):
        self.shuffle = not self.shuffle
        if self.queue and 0 <= self.pos < len(self.queue):
            cur = self.queue[self.pos]
            if self.shuffle:
                rest = self.queue[:self.pos] + self.queue[self.pos + 1:]
                random.shuffle(rest)
                self.queue, self.pos = [cur] + rest, 0
            else:
                self.queue = list(self.orig)
                self.pos = next((i for i, t in enumerate(self.queue) if t is cur), 0)
        self.bar.set_modes(self.shuffle, self.repeat)

    def cycle_repeat(self):
        self.repeat = {"off": "all", "all": "one", "one": "off"}[self.repeat]
        self.bar.set_modes(self.shuffle, self.repeat)

    def play_next(self, tracks):
        if not self.queue:
            self.play_list(tracks, 0)
            return
        for i, t in enumerate(tracks):
            self.queue.insert(self.pos + 1 + i, t)
        self.orig += list(tracks)
        self.toast(f"次に再生: {len(tracks)}曲")

    def add_queue(self, tracks):
        if not self.queue:
            self.play_list(tracks, 0)
            return
        self.queue += list(tracks)
        self.orig += list(tracks)
        self.toast(f"キューに {len(tracks)}曲 追加しました")

    # --- お気に入り・プレイリスト ---
    def toggle_fav(self, tracks):
        tracks = [t for t in tracks if not t.get("remote")]
        if not tracks:
            return
        want = not self.user.is_fav(tracks[0]["path"])
        for t in tracks:
            if self.user.is_fav(t["path"]) != want:
                self.user.toggle_fav(t["path"])
        self._refresh_tables(full=True)
        if self.cur:
            self.bar.set_fav(not self.cur.get("remote") and self.user.is_fav(self.cur["path"]))
        self.toast("お気に入りに追加しました" if want else "お気に入りから外しました")

    def toggle_fav_current(self):
        if self.cur and not self.cur.get("remote"):
            self.toggle_fav([self.cur])

    def add_to_playlist(self, name, tracks):
        n = self.user.add_to_playlist(name, [t["path"] for t in tracks])
        self.toast(f"「{name}」に {n}曲 追加しました")

    def new_playlist_dialog(self, tracks=None):
        name = ctk.CTkInputDialog(text="新しいプレイリスト名", title=APP_NAME).get_input()
        if name and name.strip():
            if self.user.create_playlist(name):
                if tracks:
                    self.add_to_playlist(name.strip(), tracks)
                else:
                    self.toast(f"プレイリスト「{name.strip()}」を作成しました")
                if self.page_name == "playlists":
                    self.pages["playlists"].on_show()
            else:
                self.toast("同じ名前のプレイリストがあります")

    def rename_playlist_dialog(self, old):
        new = ctk.CTkInputDialog(text="新しい名前", title=APP_NAME).get_input()
        if new and self.user.rename_playlist(old, new):
            self.show("detail", push=False, kind="playlist", key=new.strip())

    def delete_playlist_dialog(self, name):
        if messagebox.askyesno(APP_NAME, f"プレイリスト「{name}」を削除しますか？\n(曲のファイルは消えません)"):
            self.user.delete_playlist(name)
            self.show("playlists", push=False)

    def _refresh_tables(self, full=False):
        for p in self.pages.values():
            tbs = ([p.table] if hasattr(p, "table") else []) + list(getattr(p, "tables", []))
            for tb in tbs:
                try:
                    tb.refresh_all() if full else tb.refresh_playing()
                except Exception:
                    pass
            if not tbs and hasattr(p, "refresh_playing"):
                try:
                    p.refresh_playing()
                except Exception:
                    pass

    # --- 定期処理 ---
    def _pump(self):
        try:
            while True:
                m = self.q.get_nowait()
                if m[0] == "call":
                    try:
                        m[1]()
                    except Exception:
                        pass
                else:
                    self.dl.handle(m)
        except queue.Empty:
            pass
        self._pump_id = self.after(60, self._pump)

    def _tick(self):
        try:
            self._tick_inner()
        except Exception:
            pass
        self._tick_id = self.after(33 if self.page_name == "now" else 90, self._tick)

    def _tick_inner(self):
        if self.cur is None:
            return
        e = self.engine
        s = e.sess
        pos = e.position() if s else 0.0
        dur = self.cur_dur()
        if s:
            self.bar.set_progress(pos, dur)
        if s and not self.counted and pos >= min(30, (dur or 60) / 2):
            self.counted = True
            if not self.cur.get("remote"):
                self.user.record_play(self.cur["path"])
        if e.finished():
            failed = s.frames < e.SR * 0.5 and not self.cur.get("remote")
            if failed:
                self.fail_count += 1
                self.toast(f"再生できませんでした: {self.cur['title']}")
                if self.fail_count >= 3:
                    self.fail_count = 0
                    e.stop()
                    self.bar.set_playing(False)
                    return
            else:
                self.fail_count = 0
            self.next(auto=True)
            return
        if self.page_name == "now":
            self.pages["now"].tick(pos, s is not None and not e.paused)

    def _startup_checks(self):
        self.run_bg(deno_path, lambda p: self._set_deno(p))
        if self.cfg.get("check_updates", True):
            def done(v):
                if v and ver_tuple(v) > ver_tuple(ytdlp_version()):
                    self.sidebar.mark_update(True)
                    self.dl._log(f"yt-dlp の新しいバージョン {v} があります。設定 > ツール から更新できます。", "warn")
            self.run_bg(latest_ytdlp_version, done)

    def _set_deno(self, p):
        self.deno_missing = not p
        self.dl.refresh_banner()

    # --- 終了 ---
    def _save_state(self):
        try:
            self.cfg["geometry"] = self.geometry().split("+")[0]
        except Exception:
            pass
        self.cfg.update({"volume": self.engine.volume if self.engine.volume > 0 else self._prev_vol,
                         "shuffle": self.shuffle, "repeat": self.repeat})
        self.dl.save_state()

    def restart(self, save=True):
        if save:
            self._save_state()
        args = sys.argv[1:] if getattr(sys, "frozen", False) else sys.argv
        try:
            subprocess.Popen([sys.executable] + args)
        except Exception:
            return
        self._close(save=False)

    def _close(self, save=True):
        if save:
            self._save_state()
        self.cancel.set()
        self.engine.close()
        for i in (self._pump_id, self._tick_id):
            try:
                self.after_cancel(i)
            except Exception:
                pass
        try:
            self.pool.shutdown(wait=False, cancel_futures=True)
        except Exception:
            pass
        self.destroy()


if __name__ == "__main__":
    App().mainloop()
