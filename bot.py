"""
Тега: Telegram-бот для поиска музыки (всё в одном файле).

Как запустить:
  1) pip install python-telegram-bot httpx python-dotenv
  2) рядом с этим файлом создай файл .env и впиши в него одну строку:
         BOT_TOKEN=токен_от_BotFather
     (по желанию добавь ещё  ADMIN_IDS=твой_telegram_id  для команды /stats)
  3) python bot.py

Нужен Python 3.10 или новее.
"""

from __future__ import annotations

import asyncio
import html
import json
import logging
import logging.handlers
import math
import os
import random
import re
import secrets
import sqlite3
import tempfile
import threading
import time
from collections import OrderedDict
from dataclasses import asdict, dataclass, field, fields
from pathlib import Path
from typing import Any, Callable, Generic, Hashable, Sequence, TypeVar

import httpx
from dotenv import load_dotenv
from telegram import (
    BotCommand,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InlineQueryResultAudio,
    InputFile,
    Message,
    Update,
)
from telegram.constants import ChatAction, ParseMode
from telegram.error import BadRequest
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    InlineQueryHandler,
    MessageHandler,
    filters,
)

__version__ = "2.0.0"

log = logging.getLogger("tega")


######################################################################
# Ошибки
######################################################################
class HttpError(Exception):
    """Сетевая ошибка или плохой HTTP-статус."""

    def __init__(self, message: str, status: int | None = None) -> None:
        super().__init__(message)
        self.status = status


class ProviderError(Exception):
    """Музыкальный сервис (iTunes / Deezer) не смог ответить."""


######################################################################
# Модели
######################################################################
SOURCE_NAMES = {"itunes": "Apple Music", "deezer": "Deezer"}


@dataclass(frozen=True)
class Track:
    source: str  # "itunes" | "deezer"
    track_id: str
    title: str
    artist: str
    album: str = ""
    duration_s: int = 0
    preview_url: str = ""
    cover_url: str | None = None
    link: str | None = None
    artist_id: str | None = None

    @property
    def key(self) -> str:
        """Короткий ключ для callback_data (лимит Telegram — 64 байта)."""
        return f"{self.source[0]}:{self.track_id}"

    @property
    def source_name(self) -> str:
        return SOURCE_NAMES.get(self.source, self.source)

    @property
    def full_title(self) -> str:
        return f"{self.artist} — {self.title}"

    @property
    def duration_text(self) -> str:
        if self.duration_s <= 0:
            return ""
        minutes, seconds = divmod(self.duration_s, 60)
        return f"{minutes}:{seconds:02d}"

    def to_dict(self) -> dict:
        """Для хранения в базе. Ссылку на превью не сохраняем: она протухает."""
        data = asdict(self)
        data.pop("preview_url", None)
        return data

    @classmethod
    def from_dict(cls, data: dict) -> "Track":
        allowed = {f.name for f in fields(cls)}
        return cls(**{k: v for k, v in data.items() if k in allowed})


@dataclass
class TrackList:
    """Список треков, который листается кнопками."""

    kind: str  # search | chart | artist | similar | voice | favorites
    arg: str
    tracks: list[Track] = field(default_factory=list)


######################################################################
# Кеш и антиспам
######################################################################
K = TypeVar("K", bound=Hashable)
V = TypeVar("V")


class TTLCache(Generic[K, V]):
    def __init__(self, ttl: float, max_size: int = 1000) -> None:
        self.ttl = ttl
        self.max_size = max_size
        self._data: OrderedDict[K, tuple[float, V]] = OrderedDict()

    def get(self, key: K) -> V | None:
        item = self._data.get(key)
        if item is None:
            return None
        expires_at, value = item
        if expires_at < time.monotonic():
            self._data.pop(key, None)
            return None
        self._data.move_to_end(key)
        return value

    def set(self, key: K, value: V) -> None:
        self._data[key] = (time.monotonic() + self.ttl, value)
        self._data.move_to_end(key)
        while len(self._data) > self.max_size:
            self._data.popitem(last=False)

    def __len__(self) -> int:
        return len(self._data)

    def clear(self) -> None:
        self._data.clear()
class Throttle:
    def __init__(self, cooldown: float) -> None:
        self.cooldown = cooldown
        self._last: dict[tuple[int, str], float] = {}

    def allow(self, user_id: int, bucket: str = "default", cooldown: float | None = None) -> bool:
        wait = self.cooldown if cooldown is None else cooldown
        now = time.monotonic()
        key = (user_id, bucket)
        last = self._last.get(key)
        if last is not None and now - last < wait:
            return False
        self._last[key] = now
        if len(self._last) > 20_000:
            self._cleanup(now)
        return True

    def _cleanup(self, now: float) -> None:
        stale = [k for k, ts in self._last.items() if now - ts > 3600]
        for k in stale:
            del self._last[k]


######################################################################
# Настройки
######################################################################
def _env_int(name: str, default: int) -> int:
    raw = os.getenv(name, "").strip()
    try:
        return int(raw) if raw else default
    except ValueError:
        raise SystemExit(f"Переменная {name} должна быть числом, а там: {raw!r}")


def _env_float(name: str, default: float) -> float:
    raw = os.getenv(name, "").strip()
    try:
        return float(raw) if raw else default
    except ValueError:
        raise SystemExit(f"Переменная {name} должна быть числом, а там: {raw!r}")


def _env_bool(name: str, default: bool = False) -> bool:
    raw = os.getenv(name, "").strip().lower()
    if not raw:
        return default
    return raw in {"1", "true", "yes", "on", "да"}


def _env_ids(name: str) -> frozenset[int]:
    ids = set()
    for part in os.getenv(name, "").replace(";", ",").split(","):
        part = part.strip()
        if part.isdigit():
            ids.add(int(part))
    return frozenset(ids)


@dataclass(frozen=True)
class Config:
    bot_token: str
    admin_ids: frozenset[int]
    db_path: Path
    page_size: int
    max_results: int
    cache_ttl: int
    cooldown: float
    default_lang: str
    itunes_country: str
    http_timeout: float
    enable_shazam: bool
    log_level: str
    log_file: Path | None


def load_config() -> Config:
    load_dotenv()

    token = os.getenv("BOT_TOKEN", "").strip()
    if not token:
        raise SystemExit(
            "Не найден BOT_TOKEN. Создай файл .env рядом с main.py "
            "и добавь строку: BOT_TOKEN=токен_от_BotFather"
        )

    default_lang = os.getenv("DEFAULT_LANG", "ru").strip().lower()
    if default_lang not in {"ru", "en"}:
        default_lang = "ru"

    log_file_raw = os.getenv("LOG_FILE", "tega.log").strip()

    return Config(
        bot_token=token,
        admin_ids=_env_ids("ADMIN_IDS"),
        db_path=Path(os.getenv("DB_PATH", "tega.db")),
        page_size=max(3, min(_env_int("PAGE_SIZE", 5), 10)),
        max_results=max(5, min(_env_int("MAX_RESULTS", 20), 50)),
        cache_ttl=max(60, _env_int("CACHE_TTL", 600)),
        cooldown=max(0.0, _env_float("COOLDOWN_SECONDS", 1.2)),
        default_lang=default_lang,
        itunes_country=os.getenv("ITUNES_COUNTRY", "US").strip().upper() or "US",
        http_timeout=_env_float("HTTP_TIMEOUT", 15.0),
        enable_shazam=_env_bool("ENABLE_SHAZAM", False),
        log_level=os.getenv("LOG_LEVEL", "INFO").strip().upper(),
        log_file=Path(log_file_raw) if log_file_raw else None,
    )


######################################################################
# HTTP-клиент
######################################################################
RETRY_STATUSES = {429, 500, 502, 503, 504}


class HttpClient:
    def __init__(self, timeout: float = 15.0, retries: int = 2, user_agent: str = "TegaBot/2.0") -> None:
        self.timeout = timeout
        self.retries = retries
        self.user_agent = user_agent
        self._client: httpx.AsyncClient | None = None

    async def start(self) -> None:
        self._client = httpx.AsyncClient(
            timeout=self.timeout,
            follow_redirects=True,
            headers={"User-Agent": self.user_agent},
            limits=httpx.Limits(max_connections=50, max_keepalive_connections=20),
        )

    async def close(self) -> None:
        if self._client is not None:
            await self._client.aclose()
            self._client = None

    async def _request(self, url: str, params: dict[str, Any] | None) -> httpx.Response:
        if self._client is None:
            raise RuntimeError("HttpClient не запущен: вызови start()")

        last_error: HttpError | None = None
        for attempt in range(self.retries + 1):
            try:
                response = await self._client.get(url, params=params)
            except httpx.TransportError as exc:
                last_error = HttpError(f"{type(exc).__name__}: {exc}")
            else:
                if response.status_code in RETRY_STATUSES:
                    last_error = HttpError(f"HTTP {response.status_code}", response.status_code)
                elif response.status_code >= 400:
                    raise HttpError(f"HTTP {response.status_code}", response.status_code)
                else:
                    return response

            if attempt < self.retries:
                delay = 0.5 * (2**attempt)
                log.debug("Повтор запроса %s через %.1f c (%s)", url, delay, last_error)
                await asyncio.sleep(delay)

        raise last_error or HttpError("Неизвестная ошибка сети")

    async def get_json(self, url: str, params: dict[str, Any] | None = None) -> Any:
        response = await self._request(url, params)
        try:
            return response.json()
        except ValueError as exc:
            raise HttpError(f"Некорректный JSON от {url}") from exc

    async def get_bytes(self, url: str, max_bytes: int = 10_000_000) -> bytes:
        response = await self._request(url, None)
        if len(response.content) > max_bytes:
            raise HttpError("Файл слишком большой")
        return response.content


######################################################################
# База данных
######################################################################
SCHEMA = """
CREATE TABLE IF NOT EXISTS users (
    user_id    INTEGER PRIMARY KEY,
    username   TEXT,
    first_name TEXT,
    lang       TEXT NOT NULL,
    source     TEXT NOT NULL DEFAULT 'both',
    created_at INTEGER NOT NULL,
    last_seen  INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS favorites (
    user_id   INTEGER NOT NULL,
    track_key TEXT NOT NULL,
    data      TEXT NOT NULL,
    added_at  INTEGER NOT NULL,
    PRIMARY KEY (user_id, track_key)
);

CREATE TABLE IF NOT EXISTS history (
    id      INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id INTEGER NOT NULL,
    query   TEXT NOT NULL,
    ts      INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_history_user ON history (user_id, id DESC);

CREATE TABLE IF NOT EXISTS plays (
    id        INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id   INTEGER NOT NULL,
    track_key TEXT NOT NULL,
    title     TEXT NOT NULL,
    artist    TEXT NOT NULL,
    ts        INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_plays_key ON plays (track_key);
"""

HISTORY_KEEP = 50


class Database:
    def __init__(self, path: Path | str) -> None:
        self.path = str(path)
        self._conn: sqlite3.Connection | None = None
        self._lock = threading.Lock()

    # ── низкоуровневые помощники ──────────────────────────────

    async def _run(self, fn: Callable[[sqlite3.Connection], Any]) -> Any:
        def runner() -> Any:
            with self._lock:
                if self._conn is None:
                    raise RuntimeError("База не подключена: вызови connect()")
                return fn(self._conn)

        return await asyncio.to_thread(runner)

    async def connect(self) -> None:
        def open_db() -> None:
            self._conn = sqlite3.connect(self.path, check_same_thread=False)
            self._conn.row_factory = sqlite3.Row
            self._conn.execute("PRAGMA journal_mode=WAL")
            self._conn.execute("PRAGMA foreign_keys=ON")
            self._conn.executescript(SCHEMA)
            self._conn.commit()

        await asyncio.to_thread(open_db)

    async def close(self) -> None:
        def close_db() -> None:
            with self._lock:
                if self._conn is not None:
                    self._conn.close()
                    self._conn = None

        await asyncio.to_thread(close_db)

    async def _execute(self, sql: str, params: tuple = ()) -> int:
        def op(conn: sqlite3.Connection) -> int:
            cur = conn.execute(sql, params)
            conn.commit()
            return cur.rowcount

        return await self._run(op)

    async def _fetchone(self, sql: str, params: tuple = ()) -> dict | None:
        def op(conn: sqlite3.Connection) -> dict | None:
            row = conn.execute(sql, params).fetchone()
            return dict(row) if row else None

        return await self._run(op)

    async def _fetchall(self, sql: str, params: tuple = ()) -> list[dict]:
        def op(conn: sqlite3.Connection) -> list[dict]:
            return [dict(r) for r in conn.execute(sql, params).fetchall()]

        return await self._run(op)

    # ── пользователи ──────────────────────────────────────────

    async def upsert_user(self, user_id: int, username: str | None, first_name: str | None, lang: str) -> dict:
        now = int(time.time())

        def op(conn: sqlite3.Connection) -> dict:
            conn.execute(
                """
                INSERT INTO users (user_id, username, first_name, lang, source, created_at, last_seen)
                VALUES (?, ?, ?, ?, 'both', ?, ?)
                ON CONFLICT(user_id) DO UPDATE SET
                    username = excluded.username,
                    first_name = excluded.first_name,
                    last_seen = excluded.last_seen
                """,
                (user_id, username, first_name, lang, now, now),
            )
            conn.commit()
            return dict(conn.execute("SELECT * FROM users WHERE user_id = ?", (user_id,)).fetchone())

        return await self._run(op)

    async def get_user(self, user_id: int) -> dict | None:
        return await self._fetchone("SELECT * FROM users WHERE user_id = ?", (user_id,))

    async def set_lang(self, user_id: int, lang: str) -> None:
        await self._execute("UPDATE users SET lang = ? WHERE user_id = ?", (lang, user_id))

    async def set_source(self, user_id: int, source: str) -> None:
        await self._execute("UPDATE users SET source = ? WHERE user_id = ?", (source, user_id))

    # ── избранное ─────────────────────────────────────────────

    async def add_favorite(self, user_id: int, track: Track) -> None:
        await self._execute(
            "INSERT OR REPLACE INTO favorites (user_id, track_key, data, added_at) VALUES (?, ?, ?, ?)",
            (user_id, track.key, json.dumps(track.to_dict(), ensure_ascii=False), int(time.time())),
        )

    async def remove_favorite(self, user_id: int, track_key: str) -> bool:
        removed = await self._execute(
            "DELETE FROM favorites WHERE user_id = ? AND track_key = ?", (user_id, track_key)
        )
        return removed > 0

    async def is_favorite(self, user_id: int, track_key: str) -> bool:
        row = await self._fetchone(
            "SELECT 1 AS x FROM favorites WHERE user_id = ? AND track_key = ?", (user_id, track_key)
        )
        return row is not None

    async def list_favorites(self, user_id: int, limit: int = 200) -> list[Track]:
        rows = await self._fetchall(
            "SELECT data FROM favorites WHERE user_id = ? ORDER BY added_at DESC LIMIT ?",
            (user_id, limit),
        )
        return [Track.from_dict(json.loads(r["data"])) for r in rows]

    async def count_favorites(self, user_id: int) -> int:
        row = await self._fetchone("SELECT COUNT(*) AS n FROM favorites WHERE user_id = ?", (user_id,))
        return int(row["n"]) if row else 0

    # ── история поиска ────────────────────────────────────────

    async def add_history(self, user_id: int, query: str) -> None:
        now = int(time.time())

        def op(conn: sqlite3.Connection) -> None:
            # Тот же запрос подряд не дублируем
            last = conn.execute(
                "SELECT id, query FROM history WHERE user_id = ? ORDER BY id DESC LIMIT 1", (user_id,)
            ).fetchone()
            if last and last["query"].lower() == query.lower():
                conn.execute("UPDATE history SET ts = ? WHERE id = ?", (now, last["id"]))
            else:
                conn.execute(
                    "INSERT INTO history (user_id, query, ts) VALUES (?, ?, ?)", (user_id, query, now)
                )
                conn.execute(
                    """
                    DELETE FROM history WHERE user_id = ? AND id NOT IN (
                        SELECT id FROM history WHERE user_id = ? ORDER BY id DESC LIMIT ?
                    )
                    """,
                    (user_id, user_id, HISTORY_KEEP),
                )
            conn.commit()

        await self._run(op)

    async def get_history(self, user_id: int, limit: int = 10) -> list[dict]:
        return await self._fetchall(
            "SELECT id, query FROM history WHERE user_id = ? ORDER BY id DESC LIMIT ?", (user_id, limit)
        )

    async def get_history_item(self, user_id: int, item_id: int) -> str | None:
        row = await self._fetchone(
            "SELECT query FROM history WHERE user_id = ? AND id = ?", (user_id, item_id)
        )
        return row["query"] if row else None

    async def clear_history(self, user_id: int) -> int:
        return await self._execute("DELETE FROM history WHERE user_id = ?", (user_id,))

    # ── прослушивания и статистика ────────────────────────────

    async def log_play(self, user_id: int, track: Track) -> None:
        await self._execute(
            "INSERT INTO plays (user_id, track_key, title, artist, ts) VALUES (?, ?, ?, ?, ?)",
            (user_id, track.key, track.title, track.artist, int(time.time())),
        )

    async def stats(self) -> dict:
        day_ago = int(time.time()) - 86400

        def op(conn: sqlite3.Connection) -> dict:
            def one(sql: str, params: tuple = ()) -> int:
                return int(conn.execute(sql, params).fetchone()[0])

            top = conn.execute(
                """
                SELECT artist, title, COUNT(*) AS n FROM plays
                GROUP BY track_key ORDER BY n DESC, MAX(ts) DESC LIMIT 5
                """
            ).fetchall()
            return {
                "users": one("SELECT COUNT(*) FROM users"),
                "new_24h": one("SELECT COUNT(*) FROM users WHERE created_at >= ?", (day_ago,)),
                "active_24h": one("SELECT COUNT(*) FROM users WHERE last_seen >= ?", (day_ago,)),
                "searches": one("SELECT COUNT(*) FROM history"),
                "plays": one("SELECT COUNT(*) FROM plays"),
                "plays_24h": one("SELECT COUNT(*) FROM plays WHERE ts >= ?", (day_ago,)),
                "favorites": one("SELECT COUNT(*) FROM favorites"),
                "top": [dict(r) for r in top],
            }

        return await self._run(op)


######################################################################
# Тексты (русский / английский)
######################################################################
SUPPORTED = ("ru", "en")

STRINGS: dict[str, dict[str, str]] = {
    "ru": {
        "start": (
            "Привет, {name}! Я <b>Тега</b> 🎵\n\n"
            "Напиши название песни или «исполнитель — название», и я покажу варианты. "
            "Выбери нужный, и я пришлю превью с обложкой и ссылкой, где послушать целиком.\n\n"
            "Что ещё умею:\n"
            "🔥 /top — чарты по жанрам\n"
            "🎲 /random — случайный трек\n"
            "❤️ /favorites — твоё избранное\n"
            "🕘 /history — история поиска\n"
            "⚙️ /settings — язык и источники\n\n"
            "Подробнее: /help"
        ),
        "help": (
            "<b>Как пользоваться</b>\n\n"
            "• Просто напиши название песни или исполнителя.\n"
            "• Под превью есть кнопки: ❤️ в избранное, ссылка на полный трек, "
            "🎤 другие песни исполнителя и 🔁 похожие треки.\n"
            "• В любом чате можно набрать <code>@{bot} запрос</code>, "
            "чтобы быстро отправить превью (если включён inline-режим).\n"
            "• Отправь голосовое или аудио, и я попробую узнать песню "
            "(если функция включена владельцем бота).\n\n"
            "<b>Команды</b>\n"
            "/search — поиск (можно и без команды)\n"
            "/top — чарты по жанрам\n"
            "/random — случайный трек из чарта\n"
            "/favorites — избранное\n"
            "/history — последние запросы\n"
            "/settings — язык и источники музыки\n\n"
            "ℹ️ Превью длится 30 секунд — это ограничение самих сервисов. "
            "Полную версию можно послушать по кнопке со ссылкой."
        ),
        "ask_query": "Напиши, что искать: <code>/search название песни</code>",
        "nothing_found": "Ничего не нашёл 😕 Попробуй написать иначе, например «исполнитель — название».",
        "unavailable": "Музыкальные сервисы сейчас не отвечают 😔 Попробуй чуть позже.",
        "slow_down": "Не так быстро 🙂 Подожди секунду.",
        "generic_error": "Что-то пошло не так 😔 Попробуй ещё раз.",
        "list_search": "🔎 Результаты по запросу «{arg}»",
        "list_chart": "🔥 Чарт: {arg}",
        "list_artist": "🎤 Песни исполнителя {arg}",
        "list_similar": "🔁 Похоже на {arg}",
        "list_voice": "🎧 Распознано: {arg}",
        "list_favorites": "❤️ Твоё избранное",
        "list_page": "Страница {page}/{pages} · треков: {total}",
        "expired": "Список устарел, отправь запрос ещё раз.",
        "track_not_found": "Не удалось найти этот трек, попробуй другой.",
        "preview_failed": "Не получилось загрузить превью 😕 Попробуй другой трек.",
        "caption_preview": "Превью 30 сек · {source}",
        "btn_fav_add": "🤍 В избранное",
        "btn_fav_remove": "❤️ Убрать из избранного",
        "btn_full": "▶️ Слушать полностью ({source})",
        "btn_artist": "🎤 Ещё от исполнителя",
        "btn_similar": "🔁 Похожие",
        "fav_added": "Добавлено в избранное ❤️",
        "fav_removed": "Убрано из избранного",
        "fav_empty": "В избранном пока пусто. Нажми 🤍 под любым превью, чтобы сохранить трек.",
        "history_title": "🕘 Последние запросы. Нажми, чтобы повторить:",
        "history_empty": "История пока пустая.",
        "history_cleared": "История очищена 🧹",
        "btn_clear_history": "🗑 Очистить историю",
        "top_title": "🔥 Выбери жанр чарта:",
        "btn_global_chart": "🌍 Общий чарт",
        "chart_global": "общий",
        "chart_failed": "Не удалось загрузить чарт 😔",
        "random_intro": "🎲 Случайный трек из чарта:",
        "settings_title": (
            "⚙️ <b>Настройки</b>\n\n"
            "Язык: <b>{lang}</b>\n"
            "Источник музыки: <b>{source}</b>"
        ),
        "settings_saved": "Сохранено ✅",
        "src_both": "Все сервисы",
        "src_itunes": "Apple Music",
        "src_deezer": "Deezer",
        "voice_disabled": "Распознавание песен сейчас выключено. Напиши название текстом 🙂",
        "voice_listening": "🎧 Слушаю…",
        "voice_not_recognized": "Не получилось узнать песню 😕 Попробуй запись подлиннее и почище.",
        "voice_too_long": "Запись слишком длинная. Пришли отрывок до 5 минут.",
        "admin_only": "Эта команда только для администраторов.",
        "stats_text": (
            "📊 <b>Статистика</b>\n\n"
            "👥 Пользователей: <b>{users}</b> (новых за сутки: {new_24h}, активных за сутки: {active_24h})\n"
            "🔎 Поисков: <b>{searches}</b>\n"
            "▶️ Прослушиваний: <b>{plays}</b> (за сутки: {plays_24h})\n"
            "❤️ В избранном: <b>{favorites}</b>\n\n"
            "<b>Топ-5 треков</b>\n{top}"
        ),
        "stats_no_top": "Пока нет данных.",
    },
    "en": {
        "start": (
            "Hi, {name}! I'm <b>Tega</b> 🎵\n\n"
            "Send me a song title or \"artist — title\" and I'll show you the matches. "
            "Pick one and I'll send a preview with cover art and a link to listen to the full track.\n\n"
            "What else I can do:\n"
            "🔥 /top — charts by genre\n"
            "🎲 /random — random track\n"
            "❤️ /favorites — your favorites\n"
            "🕘 /history — search history\n"
            "⚙️ /settings — language and sources\n\n"
            "More: /help"
        ),
        "help": (
            "<b>How to use</b>\n\n"
            "• Just type a song or artist name.\n"
            "• Under each preview: ❤️ add to favorites, link to the full track, "
            "🎤 more from the artist and 🔁 similar tracks.\n"
            "• In any chat type <code>@{bot} query</code> "
            "to quickly share a preview (if inline mode is enabled).\n"
            "• Send a voice message or audio and I'll try to recognize the song "
            "(if the bot owner enabled this).\n\n"
            "<b>Commands</b>\n"
            "/search — search (works without the command too)\n"
            "/top — charts by genre\n"
            "/random — random track from the chart\n"
            "/favorites — favorites\n"
            "/history — recent searches\n"
            "/settings — language and music sources\n\n"
            "ℹ️ Previews are 30 seconds long — that's a limit set by the services themselves. "
            "Use the link button to listen to the full version."
        ),
        "ask_query": "Tell me what to search for: <code>/search song title</code>",
        "nothing_found": "Nothing found 😕 Try rephrasing, e.g. \"artist — title\".",
        "unavailable": "The music services aren't responding right now 😔 Please try again later.",
        "slow_down": "Not so fast 🙂 Wait a second.",
        "generic_error": "Something went wrong 😔 Please try again.",
        "list_search": "🔎 Results for \"{arg}\"",
        "list_chart": "🔥 Chart: {arg}",
        "list_artist": "🎤 Songs by {arg}",
        "list_similar": "🔁 Similar to {arg}",
        "list_voice": "🎧 Recognized: {arg}",
        "list_favorites": "❤️ Your favorites",
        "list_page": "Page {page}/{pages} · tracks: {total}",
        "expired": "This list has expired, please search again.",
        "track_not_found": "Couldn't find that track, try another one.",
        "preview_failed": "Couldn't load the preview 😕 Try another track.",
        "caption_preview": "30 sec preview · {source}",
        "btn_fav_add": "🤍 Add to favorites",
        "btn_fav_remove": "❤️ Remove from favorites",
        "btn_full": "▶️ Listen in full ({source})",
        "btn_artist": "🎤 More by artist",
        "btn_similar": "🔁 Similar",
        "fav_added": "Added to favorites ❤️",
        "fav_removed": "Removed from favorites",
        "fav_empty": "No favorites yet. Tap 🤍 under any preview to save a track.",
        "history_title": "🕘 Recent searches. Tap to repeat:",
        "history_empty": "Your history is empty.",
        "history_cleared": "History cleared 🧹",
        "btn_clear_history": "🗑 Clear history",
        "top_title": "🔥 Pick a chart genre:",
        "btn_global_chart": "🌍 Global chart",
        "chart_global": "global",
        "chart_failed": "Couldn't load the chart 😔",
        "random_intro": "🎲 Random track from the chart:",
        "settings_title": (
            "⚙️ <b>Settings</b>\n\n"
            "Language: <b>{lang}</b>\n"
            "Music source: <b>{source}</b>"
        ),
        "settings_saved": "Saved ✅",
        "src_both": "All services",
        "src_itunes": "Apple Music",
        "src_deezer": "Deezer",
        "voice_disabled": "Song recognition is turned off right now. Type the title instead 🙂",
        "voice_listening": "🎧 Listening…",
        "voice_not_recognized": "Couldn't recognize the song 😕 Try a longer, cleaner recording.",
        "voice_too_long": "The recording is too long. Send a clip under 5 minutes.",
        "admin_only": "This command is for administrators only.",
        "stats_text": (
            "📊 <b>Statistics</b>\n\n"
            "👥 Users: <b>{users}</b> (new in 24h: {new_24h}, active in 24h: {active_24h})\n"
            "🔎 Searches: <b>{searches}</b>\n"
            "▶️ Plays: <b>{plays}</b> (24h: {plays_24h})\n"
            "❤️ Favorites: <b>{favorites}</b>\n\n"
            "<b>Top 5 tracks</b>\n{top}"
        ),
        "stats_no_top": "No data yet.",
    },
}

LANG_LABELS = {"ru": "Русский", "en": "English"}


def normalize_lang(code: str | None, default: str = "ru") -> str:
    """Определяет язык интерфейса по language_code из Telegram."""
    if not code:
        return default
    code = code.lower()
    if code.startswith("ru"):
        return "ru"
    if code.startswith("en"):
        return "en"
    return default


def t(lang: str, key: str, **kwargs: object) -> str:
    table = STRINGS.get(lang) or STRINGS["ru"]
    text = table.get(key) or STRINGS["ru"].get(key) or key
    return text.format(**kwargs) if kwargs else text


######################################################################
# Музыкальные сервисы: Apple Music (iTunes)
######################################################################
ITUNES_BASE = "https://itunes.apple.com"


class ItunesProvider:
    name = "itunes"

    def __init__(self, http: "HttpClient", country: str = "US") -> None:
        self.http = http
        self.country = country

    @staticmethod
    def parse(item: dict[str, Any]) -> Track | None:
        if item.get("wrapperType") != "track" or not item.get("previewUrl") or not item.get("trackId"):
            return None
        cover = (item.get("artworkUrl100") or "").replace("100x100bb", "300x300bb")
        artist_id = item.get("artistId")
        return Track(
            source="itunes",
            track_id=str(item["trackId"]),
            title=item.get("trackName") or "Без названия",
            artist=item.get("artistName") or "Неизвестный исполнитель",
            album=item.get("collectionName") or "",
            duration_s=int(item.get("trackTimeMillis") or 0) // 1000,
            preview_url=item["previewUrl"],
            cover_url=cover or None,
            link=item.get("trackViewUrl"),
            artist_id=str(artist_id) if artist_id else None,
        )

    async def _results(self, path: str, params: dict[str, Any]) -> list[dict[str, Any]]:
        try:
            data = await self.http.get_json(f"{ITUNES_BASE}{path}", {**params, "country": self.country})
        except Exception as exc:
            raise ProviderError(f"iTunes: {exc}") from exc
        if not isinstance(data, dict):
            raise ProviderError("iTunes: неожиданный формат ответа")
        return data.get("results", [])

    async def search(self, query: str, limit: int) -> list[Track]:
        items = await self._results(
            "/search", {"term": query, "media": "music", "entity": "song", "limit": limit}
        )
        return [t for t in map(self.parse, items) if t]

    async def lookup(self, track_id: str) -> Track | None:
        items = await self._results("/lookup", {"id": track_id})
        for item in items:
            track = self.parse(item)
            if track:
                return track
        return None

    async def artist_songs(self, artist_id: str, limit: int) -> list[Track]:
        # Первый элемент ответа — сам исполнитель, дальше его песни
        items = await self._results("/lookup", {"id": artist_id, "entity": "song", "limit": limit})
        return [t for t in map(self.parse, items) if t]


######################################################################
# Музыкальные сервисы: Deezer
######################################################################
DEEZER_BASE = "https://api.deezer.com"


class DeezerProvider:
    name = "deezer"

    def __init__(self, http: "HttpClient") -> None:
        self.http = http

    @staticmethod
    def parse(item: dict[str, Any]) -> Track | None:
        preview = item.get("preview")
        if not preview or not item.get("id"):
            return None
        artist = item.get("artist") or {}
        album = item.get("album") or {}
        cover = album.get("cover_medium") or album.get("cover_big") or album.get("cover")
        return Track(
            source="deezer",
            track_id=str(item["id"]),
            title=item.get("title") or "Без названия",
            artist=artist.get("name") or "Неизвестный исполнитель",
            album=album.get("title") or "",
            duration_s=int(item.get("duration") or 0),
            preview_url=preview,
            cover_url=cover or None,
            link=item.get("link"),
            artist_id=str(artist["id"]) if artist.get("id") else None,
        )

    async def _get(self, path: str, params: dict[str, Any] | None = None) -> Any:
        try:
            data = await self.http.get_json(f"{DEEZER_BASE}{path}", params)
        except Exception as exc:
            raise ProviderError(f"Deezer: {exc}") from exc
        # Deezer возвращает ошибки с кодом 200 и полем "error"
        if isinstance(data, dict) and "error" in data:
            raise ProviderError(f"Deezer: {data['error']}")
        return data

    def _tracks(self, data: Any) -> list[Track]:
        items = data.get("data", []) if isinstance(data, dict) else []
        return [t for t in map(self.parse, items) if t]

    async def search(self, query: str, limit: int) -> list[Track]:
        return self._tracks(await self._get("/search", {"q": query, "limit": limit}))

    async def get_track(self, track_id: str) -> Track | None:
        data = await self._get(f"/track/{track_id}")
        return self.parse(data) if isinstance(data, dict) else None

    async def chart(self, genre_id: int = 0, limit: int = 50) -> list[Track]:
        return self._tracks(await self._get(f"/chart/{genre_id}/tracks", {"limit": limit}))

    async def genres(self) -> list[tuple[int, str]]:
        data = await self._get("/genre")
        items = data.get("data", []) if isinstance(data, dict) else []
        return [(int(g["id"]), g["name"]) for g in items if g.get("id") and g.get("name")]

    async def search_artist(self, name: str) -> str | None:
        data = await self._get("/search/artist", {"q": name, "limit": 1})
        items = data.get("data", []) if isinstance(data, dict) else []
        return str(items[0]["id"]) if items else None

    async def artist_top(self, artist_id: str, limit: int) -> list[Track]:
        return self._tracks(await self._get(f"/artist/{artist_id}/top", {"limit": limit}))

    async def artist_radio(self, artist_id: str, limit: int) -> list[Track]:
        return self._tracks(await self._get(f"/artist/{artist_id}/radio", {"limit": limit}))


######################################################################
# Музыкальные сервисы: объединение, кеш, дубли
######################################################################
_BRACKETS = re.compile(r"[\(\[].*?[\)\]]")
_NON_WORD = re.compile(r"[\W_]+", re.UNICODE)


def _norm(text: str) -> str:
    cleaned = _NON_WORD.sub("", _BRACKETS.sub("", text.lower()))
    return cleaned or text.lower()


def dedupe_key(track: Track) -> tuple[str, str]:
    return _norm(track.artist), _norm(track.title)


def merge_results(lists: Sequence[Sequence[Track]], limit: int) -> list[Track]:
    """Чередуем результаты сервисов (1-й из А, 1-й из Б, 2-й из А…) и убираем повторы."""
    merged: list[Track] = []
    seen: set[tuple[str, str]] = set()
    longest = max((len(lst) for lst in lists), default=0)
    for i in range(longest):
        for lst in lists:
            if i < len(lst):
                track = lst[i]
                key = dedupe_key(track)
                if key not in seen:
                    seen.add(key)
                    merged.append(track)
    return merged[:limit]


class MusicService:
    def __init__(self, itunes: Any, deezer: Any, cache_ttl: int = 600, max_results: int = 20) -> None:
        self.itunes = itunes
        self.deezer = deezer
        self.max_results = max_results
        # Превью-ссылки живут недолго, поэтому треки держим в кеше ограниченное время
        self._searches: TTLCache[tuple[str, str], list[Track]] = TTLCache(cache_ttl, 500)
        self._tracks: TTLCache[str, Track] = TTLCache(cache_ttl, 5000)
        self._lists: TTLCache[str, TrackList] = TTLCache(3600, 2000)
        self._charts: TTLCache[int, list[Track]] = TTLCache(900, 50)
        self._genres: TTLCache[str, list[tuple[int, str]]] = TTLCache(86400, 2)

    # ── треки и списки ────────────────────────────────────────

    def remember(self, tracks: Sequence[Track]) -> None:
        for track in tracks:
            self._tracks.set(track.key, track)

    def store_list(self, kind: str, arg: str, tracks: Sequence[Track]) -> str:
        token = secrets.token_urlsafe(5)
        self._lists.set(token, TrackList(kind=kind, arg=arg, tracks=list(tracks)))
        return token

    def get_list(self, token: str) -> TrackList | None:
        return self._lists.get(token)

    async def resolve(self, key: str, *, fresh: bool = False) -> Track | None:
        """Находит трек по короткому ключу ('d:123' / 'i:456')."""
        if not fresh:
            cached = self._tracks.get(key)
            if cached:
                return cached
        source, _, track_id = key.partition(":")
        if source == "d":
            track = await self.deezer.get_track(track_id)
        elif source == "i":
            track = await self.itunes.lookup(track_id)
        else:
            return None
        if track:
            self._tracks.set(track.key, track)
        return track

    # ── поиск ─────────────────────────────────────────────────

    async def search(self, query: str, source: str = "both") -> list[Track]:
        query = query.strip()
        cache_key = (query.lower(), source)
        cached = self._searches.get(cache_key)
        if cached is not None:
            return cached

        jobs = []
        if source in ("both", "itunes"):
            jobs.append(self.itunes.search(query, self.max_results))
        if source in ("both", "deezer"):
            jobs.append(self.deezer.search(query, self.max_results))

        results = await asyncio.gather(*jobs, return_exceptions=True)
        good = [r for r in results if not isinstance(r, BaseException)]
        for r in results:
            if isinstance(r, BaseException):
                log.warning("Источник не ответил на поиск: %s", r)
        if not good:
            raise ProviderError("Все источники недоступны")

        tracks = merge_results(good, self.max_results)
        self.remember(tracks)
        if len(good) == len(jobs):  # частичный результат не кешируем
            self._searches.set(cache_key, tracks)
        return tracks

    # ── чарты ─────────────────────────────────────────────────

    async def chart(self, genre_id: int = 0) -> list[Track]:
        cached = self._charts.get(genre_id)
        if cached is not None:
            return cached
        tracks = await self.deezer.chart(genre_id, 50)
        self.remember(tracks)
        if tracks:
            self._charts.set(genre_id, tracks)
        return tracks

    async def genres(self) -> list[tuple[int, str]]:
        cached = self._genres.get("all")
        if cached is not None:
            return cached
        genres = [(gid, name) for gid, name in await self.deezer.genres() if gid != 0]
        if genres:
            self._genres.set("all", genres)
        return genres

    # ── по исполнителю и «похожие» ────────────────────────────

    async def more_by_artist(self, track: Track) -> list[Track]:
        if not track.artist_id:
            return []
        if track.source == "deezer":
            tracks = await self.deezer.artist_top(track.artist_id, self.max_results)
        else:
            tracks = await self.itunes.artist_songs(track.artist_id, self.max_results)
        self.remember(tracks)
        return tracks

    async def similar(self, track: Track) -> list[Track]:
        artist_id = track.artist_id if track.source == "deezer" else None
        if artist_id is None:
            artist_id = await self.deezer.search_artist(track.artist)
        if not artist_id:
            return []
        tracks = await self.deezer.artist_radio(artist_id, self.max_results + 5)
        own = dedupe_key(track)
        tracks = [t for t in tracks if dedupe_key(t) != own]
        tracks = merge_results([tracks], self.max_results)
        self.remember(tracks)
        return tracks


######################################################################
# Интерфейс: кнопки и оформление
######################################################################
SOURCES = ("both", "itunes", "deezer")
MAX_BUTTON_TEXT = 58


def esc(text: str) -> str:
    return html.escape(text or "", quote=False)


def _clip(text: str, limit: int = MAX_BUTTON_TEXT) -> str:
    return text if len(text) <= limit else text[: limit - 1] + "…"


def track_label(track: Track) -> str:
    label = f"🎵 {track.full_title}"
    duration = track.duration_text
    if duration:
        label += f" · {duration}"
    return _clip(label)


def track_list_keyboard(
    tracks: Sequence[Track], page: int, pages: int, nav_prefix: str
) -> InlineKeyboardMarkup:
    rows = [[InlineKeyboardButton(track_label(tr), callback_data=f"p:{tr.key}")] for tr in tracks]
    if pages > 1:
        rows.append(
            [
                InlineKeyboardButton("◀️", callback_data=f"{nav_prefix}:{(page - 1) % pages}"),
                InlineKeyboardButton(f"{page + 1}/{pages}", callback_data="noop"),
                InlineKeyboardButton("▶️", callback_data=f"{nav_prefix}:{(page + 1) % pages}"),
            ]
        )
    return InlineKeyboardMarkup(rows)


def render_track_list(
    tlist: TrackList, page: int, lang: str, nav_prefix: str, page_size: int
) -> tuple[str, InlineKeyboardMarkup]:
    total = len(tlist.tracks)
    pages = max(1, math.ceil(total / page_size))
    page = min(max(page, 0), pages - 1)
    chunk = tlist.tracks[page * page_size : (page + 1) * page_size]

    header = t(lang, f"list_{tlist.kind}", arg=esc(tlist.arg))
    footer = t(lang, "list_page", page=page + 1, pages=pages, total=total)
    text = f"{header}\n<i>{footer}</i>"
    return text, track_list_keyboard(chunk, page, pages, nav_prefix)


def player_keyboard(track: Track, is_fav: bool, lang: str) -> InlineKeyboardMarkup:
    fav_text = t(lang, "btn_fav_remove" if is_fav else "btn_fav_add")
    rows = [[InlineKeyboardButton(fav_text, callback_data=f"fv:{track.key}")]]
    if track.link:
        rows.append(
            [InlineKeyboardButton(t(lang, "btn_full", source=track.source_name), url=track.link)]
        )
    rows.append(
        [
            InlineKeyboardButton(t(lang, "btn_artist"), callback_data=f"a:{track.key}"),
            InlineKeyboardButton(t(lang, "btn_similar"), callback_data=f"sm:{track.key}"),
        ]
    )
    return InlineKeyboardMarkup(rows)


def genres_keyboard(genres: Sequence[tuple[int, str]], lang: str) -> InlineKeyboardMarkup:
    rows = [[InlineKeyboardButton(t(lang, "btn_global_chart"), callback_data="c:0")]]
    row: list[InlineKeyboardButton] = []
    for genre_id, name in genres[:30]:
        row.append(InlineKeyboardButton(_clip(name, 24), callback_data=f"c:{genre_id}"))
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    return InlineKeyboardMarkup(rows)


def settings_keyboard(lang: str, source: str) -> InlineKeyboardMarkup:
    mark = lambda active: "✅ " if active else ""  # noqa: E731
    lang_row = [
        InlineKeyboardButton(f"{mark(code == lang)}{LANG_LABELS[code]}", callback_data=f"set:lang:{code}")
        for code in SUPPORTED
    ]
    source_row = [
        InlineKeyboardButton(f"{mark(src == source)}{t(lang, f'src_{src}')}", callback_data=f"set:src:{src}")
        for src in SOURCES
    ]
    return InlineKeyboardMarkup([lang_row, source_row[:1], source_row[1:]])


def history_keyboard(rows: Sequence[dict], lang: str) -> InlineKeyboardMarkup:
    buttons = [
        [InlineKeyboardButton(_clip(f"🔎 {row['query']}"), callback_data=f"h:{row['id']}")] for row in rows
    ]
    buttons.append([InlineKeyboardButton(t(lang, "btn_clear_history"), callback_data="hc")])
    return InlineKeyboardMarkup(buttons)


def track_caption(track: Track, lang: str) -> str:
    lines = [f"<b>{esc(track.title)}</b>", esc(track.artist)]
    if track.album:
        lines.append(f"💿 {esc(track.album)}")
    lines.append("")
    lines.append(f"<i>{esc(t(lang, 'caption_preview', source=track.source_name))}</i>")
    return "\n".join(lines)[:1000]


######################################################################
# Общие зависимости
######################################################################
@dataclass
class Deps:
    cfg: Config
    db: Database
    http: HttpClient
    music: MusicService
    throttle: Throttle
    shazam: Any | None = None


@dataclass
class UserCtx:
    user_id: int
    lang: str
    source: str


def get_deps(context: ContextTypes.DEFAULT_TYPE) -> Deps:
    return context.application.bot_data["deps"]


async def get_user_ctx(update: Update, context: ContextTypes.DEFAULT_TYPE) -> UserCtx:
    """Записывает пользователя в базу (если нового) и возвращает его настройки."""
    deps = get_deps(context)
    user = update.effective_user
    detected = normalize_lang(user.language_code, deps.cfg.default_lang)
    row = await deps.db.upsert_user(user.id, user.username, user.first_name, detected)
    return UserCtx(user_id=user.id, lang=row["lang"], source=row["source"])


######################################################################
# Обработчики: /start, /help, /settings
######################################################################
async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    name = esc(update.effective_user.first_name or "друг")
    await update.message.reply_text(t(uc.lang, "start", name=name), parse_mode=ParseMode.HTML)


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    await update.message.reply_text(
        t(uc.lang, "help", bot=context.bot.username or "bot"),
        parse_mode=ParseMode.HTML,
    )


def _settings_text(lang: str, source: str) -> str:
    return t(lang, "settings_title", lang=LANG_LABELS[lang], source=t(lang, f"src_{source}"))


async def cmd_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    await update.message.reply_text(
        _settings_text(uc.lang, uc.source),
        parse_mode=ParseMode.HTML,
        reply_markup=settings_keyboard(uc.lang, uc.source),
    )


async def cb_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    uc = await get_user_ctx(update, context)
    deps = get_deps(context)

    _, kind, value = query.data.split(":", 2)
    lang, source = uc.lang, uc.source
    if kind == "lang" and value in SUPPORTED:
        lang = value
        await deps.db.set_lang(uc.user_id, lang)
    elif kind == "src" and value in SOURCES:
        source = value
        await deps.db.set_source(uc.user_id, source)
    else:
        await query.answer()
        return

    await query.answer(t(lang, "settings_saved"))
    try:
        await query.edit_message_text(
            _settings_text(lang, source),
            parse_mode=ParseMode.HTML,
            reply_markup=settings_keyboard(lang, source),
        )
    except BadRequest as exc:
        if "not modified" not in str(exc).lower():
            raise


async def cb_noop(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.callback_query.answer()


def register_common(app: Application) -> None:
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("help", cmd_help))
    app.add_handler(CommandHandler(["settings", "lang"], cmd_settings))
    app.add_handler(CallbackQueryHandler(cb_settings, pattern=r"^set:(lang|src):\w+$"))
    app.add_handler(CallbackQueryHandler(cb_noop, pattern=r"^noop$"))


######################################################################
# Обработчики: поиск и история
######################################################################
MAX_QUERY_LEN = 200


async def run_search(
    message: Message, context: ContextTypes.DEFAULT_TYPE, uc: UserCtx, query: str, *, save_history: bool = True
) -> None:
    deps = get_deps(context)
    await message.chat.send_action(ChatAction.TYPING)

    try:
        tracks = await deps.music.search(query, uc.source)
    except ProviderError:
        await message.reply_text(t(uc.lang, "unavailable"))
        return

    if not tracks:
        await message.reply_text(t(uc.lang, "nothing_found"))
        return

    if save_history:
        await deps.db.add_history(uc.user_id, query)

    token = deps.music.store_list("search", query, tracks)
    text, keyboard = render_track_list(
        deps.music.get_list(token), 0, uc.lang, f"l:{token}", deps.cfg.page_size
    )
    await message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=keyboard)


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    deps = get_deps(context)
    query = (update.message.text or "").strip()[:MAX_QUERY_LEN]
    if not query:
        return
    if not deps.throttle.allow(uc.user_id, "search"):
        await update.message.reply_text(t(uc.lang, "slow_down"))
        return
    await run_search(update.message, context, uc, query)


async def cmd_search(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    query = " ".join(context.args or []).strip()[:MAX_QUERY_LEN]
    if not query:
        await update.message.reply_text(t(uc.lang, "ask_query"), parse_mode=ParseMode.HTML)
        return
    if not get_deps(context).throttle.allow(uc.user_id, "search"):
        await update.message.reply_text(t(uc.lang, "slow_down"))
        return
    await run_search(update.message, context, uc, query)


async def cb_list_nav(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Листание страниц: callback_data = l:<токен списка>:<страница>."""
    query = update.callback_query
    uc = await get_user_ctx(update, context)
    deps = get_deps(context)

    _, token, page_raw = query.data.split(":")
    tlist = deps.music.get_list(token)
    if tlist is None:
        await query.answer(t(uc.lang, "expired"), show_alert=True)
        return

    await query.answer()
    text, keyboard = render_track_list(tlist, int(page_raw), uc.lang, f"l:{token}", deps.cfg.page_size)
    try:
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=keyboard)
    except BadRequest as exc:
        if "not modified" not in str(exc).lower():
            raise


async def cmd_history(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    rows = await get_deps(context).db.get_history(uc.user_id, 10)
    if not rows:
        await update.message.reply_text(t(uc.lang, "history_empty"))
        return
    await update.message.reply_text(t(uc.lang, "history_title"), reply_markup=history_keyboard(rows, uc.lang))


async def cb_history_item(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    uc = await get_user_ctx(update, context)
    deps = get_deps(context)

    if not deps.throttle.allow(uc.user_id, "search"):
        await query.answer(t(uc.lang, "slow_down"))
        return
    await query.answer()

    text = await deps.db.get_history_item(uc.user_id, int(query.data.split(":")[1]))
    if text:
        await run_search(query.message, context, uc, text)


async def cb_history_clear(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    uc = await get_user_ctx(update, context)
    await get_deps(context).db.clear_history(uc.user_id)
    await query.answer(t(uc.lang, "history_cleared"))
    await query.edit_message_text(t(uc.lang, "history_empty"))


def register_search(app: Application) -> None:
    app.add_handler(CommandHandler("search", cmd_search))
    app.add_handler(CommandHandler("history", cmd_history))
    app.add_handler(CallbackQueryHandler(cb_list_nav, pattern=r"^l:[\w-]+:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_history_item, pattern=r"^h:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_history_clear, pattern=r"^hc$"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))


######################################################################
# Обработчики: плеер, избранное-кнопка, /random
######################################################################
MAX_AUDIO_BYTES = 8_000_000
MAX_THUMB_BYTES = 190_000  # Telegram принимает обложки до 200 КБ
_BAD_FILENAME_CHARS = re.compile(r'[\\/:*?"<>|]+')


def safe_filename(name: str) -> str:
    return _BAD_FILENAME_CHARS.sub(" ", name).strip()[:100] or "track"


async def _fetch_preview(context: ContextTypes.DEFAULT_TYPE, track: Track) -> tuple[bytes | None, Track]:
    """Скачивает превью. Если ссылка протухла, берёт свежую и пробует ещё раз."""
    deps = get_deps(context)
    for attempt in range(2):
        try:
            return await deps.http.get_bytes(track.preview_url, MAX_AUDIO_BYTES), track
        except HttpError as exc:
            log.info("Превью %s не скачалось (попытка %d): %s", track.key, attempt + 1, exc)
            if attempt == 1:
                break
            try:
                fresh = await deps.music.resolve(track.key, fresh=True)
            except ProviderError:
                break
            if fresh is None:
                break
            track = fresh
    return None, track


async def _fetch_cover(context: ContextTypes.DEFAULT_TYPE, track: Track) -> bytes | None:
    if not track.cover_url:
        return None
    try:
        data = await get_deps(context).http.get_bytes(track.cover_url, MAX_THUMB_BYTES)
    except HttpError:
        return None
    return data


async def deliver_track(message: Message, context: ContextTypes.DEFAULT_TYPE, uc: UserCtx, track: Track) -> None:
    deps = get_deps(context)
    await message.chat.send_action(ChatAction.UPLOAD_VOICE)

    audio, track = await _fetch_preview(context, track)
    if audio is None:
        await message.reply_text(t(uc.lang, "preview_failed"))
        return

    thumb = await _fetch_cover(context, track)
    is_fav = await deps.db.is_favorite(uc.user_id, track.key)
    extension = "m4a" if ".m4a" in track.preview_url else "mp3"

    await message.reply_audio(
        audio=InputFile(audio, filename=f"{safe_filename(track.full_title)}.{extension}"),
        title=track.title,
        performer=track.artist,
        duration=30,
        thumbnail=thumb,
        caption=track_caption(track, uc.lang),
        parse_mode=ParseMode.HTML,
        reply_markup=player_keyboard(track, is_fav, uc.lang),
    )
    await deps.db.log_play(uc.user_id, track)


async def _resolve_or_report(
    update: Update, context: ContextTypes.DEFAULT_TYPE, uc: UserCtx, key: str
) -> Track | None:
    try:
        track = await get_deps(context).music.resolve(key)
    except ProviderError:
        track = None
    if track is None:
        await update.callback_query.message.reply_text(t(uc.lang, "track_not_found"))
    return track


async def cb_play(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    uc = await get_user_ctx(update, context)

    if not get_deps(context).throttle.allow(uc.user_id, "play", cooldown=1.0):
        await query.answer(t(uc.lang, "slow_down"))
        return
    await query.answer()

    track = await _resolve_or_report(update, context, uc, query.data[2:])
    if track:
        await deliver_track(query.message, context, uc, track)


async def cb_toggle_favorite(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    uc = await get_user_ctx(update, context)
    deps = get_deps(context)
    key = query.data[3:]

    try:
        track = await deps.music.resolve(key)
    except ProviderError:
        track = None
    if track is None:
        await query.answer(t(uc.lang, "track_not_found"), show_alert=True)
        return

    if await deps.db.is_favorite(uc.user_id, key):
        await deps.db.remove_favorite(uc.user_id, key)
        now_fav, note = False, t(uc.lang, "fav_removed")
    else:
        await deps.db.add_favorite(uc.user_id, track)
        now_fav, note = True, t(uc.lang, "fav_added")

    await query.answer(note)
    await query.edit_message_reply_markup(reply_markup=player_keyboard(track, now_fav, uc.lang))


async def _send_track_list(
    update: Update, context: ContextTypes.DEFAULT_TYPE, uc: UserCtx, kind: str, track: Track
) -> None:
    deps = get_deps(context)
    query = update.callback_query
    if not deps.throttle.allow(uc.user_id, "search"):
        await query.answer(t(uc.lang, "slow_down"))
        return
    await query.answer()

    try:
        if kind == "artist":
            tracks = await deps.music.more_by_artist(track)
        else:
            tracks = await deps.music.similar(track)
    except ProviderError:
        await query.message.reply_text(t(uc.lang, "unavailable"))
        return

    if not tracks:
        await query.message.reply_text(t(uc.lang, "nothing_found"))
        return

    arg = track.artist if kind == "artist" else track.full_title
    token = deps.music.store_list(kind, arg, tracks)
    text, keyboard = render_track_list(
        deps.music.get_list(token), 0, uc.lang, f"l:{token}", deps.cfg.page_size
    )
    await query.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=keyboard)


async def cb_more_by_artist(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    track = await _resolve_or_report(update, context, uc, update.callback_query.data[2:])
    if track:
        await _send_track_list(update, context, uc, "artist", track)


async def cb_similar(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    track = await _resolve_or_report(update, context, uc, update.callback_query.data[3:])
    if track:
        await _send_track_list(update, context, uc, "similar", track)


async def cmd_random(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    deps = get_deps(context)
    if not deps.throttle.allow(uc.user_id, "play", cooldown=1.5):
        await update.message.reply_text(t(uc.lang, "slow_down"))
        return
    try:
        tracks = await deps.music.chart(0)
    except ProviderError:
        tracks = []
    if not tracks:
        await update.message.reply_text(t(uc.lang, "unavailable"))
        return
    await update.message.reply_text(t(uc.lang, "random_intro"))
    await deliver_track(update.message, context, uc, random.choice(tracks))


def register_player(app: Application) -> None:
    app.add_handler(CommandHandler("random", cmd_random))
    app.add_handler(CallbackQueryHandler(cb_play, pattern=r"^p:[di]:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_toggle_favorite, pattern=r"^fv:[di]:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_more_by_artist, pattern=r"^a:[di]:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_similar, pattern=r"^sm:[di]:\d+$"))


######################################################################
# Обработчики: избранное
######################################################################
async def _load(context: ContextTypes.DEFAULT_TYPE, user_id: int) -> TrackList:
    deps = get_deps(context)
    tracks = await deps.db.list_favorites(user_id)
    deps.music.remember(tracks)
    return TrackList(kind="favorites", arg="", tracks=tracks)


async def cmd_favorites(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    tlist = await _load(context, uc.user_id)
    if not tlist.tracks:
        await update.message.reply_text(t(uc.lang, "fav_empty"))
        return
    text, keyboard = render_track_list(tlist, 0, uc.lang, "fav", get_deps(context).cfg.page_size)
    await update.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=keyboard)


async def cb_favorites_nav(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    uc = await get_user_ctx(update, context)
    await query.answer()

    tlist = await _load(context, uc.user_id)
    if not tlist.tracks:
        await query.edit_message_text(t(uc.lang, "fav_empty"))
        return
    page = int(query.data.split(":")[1])
    text, keyboard = render_track_list(tlist, page, uc.lang, "fav", get_deps(context).cfg.page_size)
    try:
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=keyboard)
    except BadRequest as exc:
        if "not modified" not in str(exc).lower():
            raise


def register_favorites(app: Application) -> None:
    app.add_handler(CommandHandler(["favorites", "fav"], cmd_favorites))
    app.add_handler(CallbackQueryHandler(cb_favorites_nav, pattern=r"^fav:\d+$"))


######################################################################
# Обработчики: чарты
######################################################################
async def cmd_top(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    try:
        genres = await get_deps(context).music.genres()
    except ProviderError:
        genres = []
    # Даже если список жанров не загрузился, общий чарт всё равно доступен
    await update.message.reply_text(t(uc.lang, "top_title"), reply_markup=genres_keyboard(genres, uc.lang))


async def cb_chart(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    uc = await get_user_ctx(update, context)
    deps = get_deps(context)

    if not deps.throttle.allow(uc.user_id, "search"):
        await query.answer(t(uc.lang, "slow_down"))
        return
    await query.answer()
    await query.message.chat.send_action(ChatAction.TYPING)

    genre_id = int(query.data.split(":")[1])
    try:
        tracks = await deps.music.chart(genre_id)
        genre_names = dict(await deps.music.genres())
    except ProviderError:
        await query.message.reply_text(t(uc.lang, "chart_failed"))
        return

    if not tracks:
        await query.message.reply_text(t(uc.lang, "chart_failed"))
        return

    name = genre_names.get(genre_id) or t(uc.lang, "chart_global")
    token = deps.music.store_list("chart", name, tracks)
    text, keyboard = render_track_list(
        deps.music.get_list(token), 0, uc.lang, f"l:{token}", deps.cfg.page_size
    )
    await query.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=keyboard)


def register_charts(app: Application) -> None:
    app.add_handler(CommandHandler("top", cmd_top))
    app.add_handler(CallbackQueryHandler(cb_chart, pattern=r"^c:\d+$"))


######################################################################
# Обработчики: inline-режим
######################################################################
MAX_INLINE_RESULTS = 20


async def on_inline_query(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    inline = update.inline_query
    text = (inline.query or "").strip()[:200]
    deps = get_deps(context)

    try:
        if text:
            tracks = await deps.music.search(text, "deezer")
        else:
            tracks = await deps.music.chart(0)  # пустой запрос — показываем популярное
    except ProviderError:
        await inline.answer([], cache_time=5)
        return

    results = [
        InlineQueryResultAudio(
            id=track.key,
            audio_url=track.preview_url,
            title=track.title,
            performer=track.artist,
            audio_duration=30,
        )
        for track in tracks
        if track.source == "deezer" and track.preview_url
    ][:MAX_INLINE_RESULTS]

    await inline.answer(results, cache_time=30, is_personal=False)


def register_inline(app: Application) -> None:
    app.add_handler(InlineQueryHandler(on_inline_query))


######################################################################
# Обработчики: распознавание песен
######################################################################
MAX_DURATION_S = 300


async def _recognize(shazam, path: str) -> dict:
    # В разных версиях shazamio метод называется по-разному
    method = getattr(shazam, "recognize", None) or getattr(shazam, "recognize_song")
    return await method(path)


async def on_audio_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    deps = get_deps(context)
    message = update.message

    if deps.shazam is None:
        await message.reply_text(t(uc.lang, "voice_disabled"))
        return

    media = message.voice or message.audio or message.video_note
    if media.duration and media.duration > MAX_DURATION_S:
        await message.reply_text(t(uc.lang, "voice_too_long"))
        return
    if not deps.throttle.allow(uc.user_id, "voice", cooldown=5.0):
        await message.reply_text(t(uc.lang, "slow_down"))
        return

    status = await message.reply_text(t(uc.lang, "voice_listening"))

    try:
        tg_file = await media.get_file()
        suffix = Path(tg_file.file_path or "").suffix or ".ogg"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / f"clip{suffix}"
            await tg_file.download_to_drive(path)
            result = await _recognize(deps.shazam, str(path))
    except Exception:
        log.exception("Не удалось распознать запись")
        await status.edit_text(t(uc.lang, "voice_not_recognized"))
        return

    info = (result or {}).get("track")
    if not info or not info.get("title"):
        await status.edit_text(t(uc.lang, "voice_not_recognized"))
        return

    title, artist = info["title"], info.get("subtitle", "")
    label = f"{artist} — {title}" if artist else title

    try:
        tracks = await deps.music.search(f"{artist} {title}".strip(), uc.source)
    except ProviderError:
        tracks = []
    if not tracks:
        await status.edit_text(f"🎧 {label}")
        return

    token = deps.music.store_list("voice", label, tracks)
    text, keyboard = render_track_list(
        deps.music.get_list(token), 0, uc.lang, f"l:{token}", deps.cfg.page_size
    )
    await status.edit_text(text, parse_mode=ParseMode.HTML, reply_markup=keyboard)


def register_voice(app: Application) -> None:
    app.add_handler(
        MessageHandler(filters.VOICE | filters.AUDIO | filters.VIDEO_NOTE, on_audio_message)
    )


######################################################################
# Обработчики: админка
######################################################################
async def cmd_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uc = await get_user_ctx(update, context)
    deps = get_deps(context)

    if uc.user_id not in deps.cfg.admin_ids:
        await update.message.reply_text(t(uc.lang, "admin_only"))
        return

    stats = await deps.db.stats()
    if stats["top"]:
        top = "\n".join(
            f"{i}. {esc(row['artist'])} — {esc(row['title'])} ({row['n']})"
            for i, row in enumerate(stats["top"], start=1)
        )
    else:
        top = t(uc.lang, "stats_no_top")

    await update.message.reply_text(
        t(uc.lang, "stats_text", **{k: v for k, v in stats.items() if k != "top"}, top=top),
        parse_mode=ParseMode.HTML,
    )


def register_admin(app: Application) -> None:
    app.add_handler(CommandHandler("stats", cmd_stats))


######################################################################
# Запуск бота
######################################################################
COMMANDS = ["search", "top", "random", "favorites", "history", "settings", "help"]
COMMAND_DESCRIPTIONS = {
    "ru": {
        "search": "Найти песню",
        "top": "Чарты по жанрам",
        "random": "Случайный трек",
        "favorites": "Избранное",
        "history": "История поиска",
        "settings": "Язык и источники",
        "help": "Помощь",
    },
    "en": {
        "search": "Find a song",
        "top": "Charts by genre",
        "random": "Random track",
        "favorites": "Favorites",
        "history": "Search history",
        "settings": "Language and sources",
        "help": "Help",
    },
}


def register_all(app: Application) -> None:
    # Порядок важен: сначала команды и кнопки, текстовый поиск — последним
    for fn in (
        register_common,
        register_favorites,
        register_charts,
        register_player,
        register_voice,
        register_inline,
        register_admin,
        register_search,
    ):
        fn(app)


def setup_logging(cfg: Config) -> None:
    handlers: list[logging.Handler] = [logging.StreamHandler()]
    if cfg.log_file:
        handlers.append(
            logging.handlers.RotatingFileHandler(
                cfg.log_file, maxBytes=2_000_000, backupCount=3, encoding="utf-8"
            )
        )
    logging.basicConfig(
        level=getattr(logging, cfg.log_level, logging.INFO),
        format="%(asctime)s | %(levelname)-7s | %(name)s | %(message)s",
        handlers=handlers,
        force=True,
    )
    # httpx на уровне INFO печатает каждый запрос вместе с токеном бота — не нужно
    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.getLogger("httpcore").setLevel(logging.WARNING)


def load_shazam(cfg: Config):
    if not cfg.enable_shazam:
        return None
    try:
        from shazamio import Shazam
    except ImportError:
        log.warning("ENABLE_SHAZAM=1, но пакет shazamio не установлен: pip install shazamio")
        return None
    log.info("Распознавание песен включено")
    return Shazam()


async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    log.error("Необработанная ошибка", exc_info=context.error)
    if isinstance(update, Update) and update.effective_chat:
        lang = update.effective_user.language_code if update.effective_user else None
        try:
            await context.bot.send_message(
                update.effective_chat.id, t("en" if (lang or "").startswith("en") else "ru", "generic_error")
            )
        except Exception:
            pass


def build_post_init(cfg: Config):
    async def post_init(app: Application) -> None:
        http = HttpClient(timeout=cfg.http_timeout)
        await http.start()
        db = Database(cfg.db_path)
        await db.connect()

        music = MusicService(
            ItunesProvider(http, cfg.itunes_country),
            DeezerProvider(http),
            cache_ttl=cfg.cache_ttl,
            max_results=cfg.max_results,
        )
        app.bot_data["deps"] = Deps(
            cfg=cfg,
            db=db,
            http=http,
            music=music,
            throttle=Throttle(cfg.cooldown),
            shazam=load_shazam(cfg),
        )

        # Меню команд в Telegram: на русском по умолчанию и на английском
        await app.bot.set_my_commands(
            [BotCommand(c, COMMAND_DESCRIPTIONS["ru"][c]) for c in COMMANDS]
        )
        await app.bot.set_my_commands(
            [BotCommand(c, COMMAND_DESCRIPTIONS["en"][c]) for c in COMMANDS], language_code="en"
        )
        log.info("Тега %s запущена как @%s", __version__, app.bot.username)

    return post_init


async def post_shutdown(app: Application) -> None:
    deps: Deps | None = app.bot_data.get("deps")
    if deps:
        await deps.http.close()
        await deps.db.close()
    log.info("Тега остановлена")


def main() -> None:
    cfg = load_config()
    setup_logging(cfg)

    app = (
        Application.builder()
        .token(cfg.bot_token)
        .post_init(build_post_init(cfg))
        .post_shutdown(post_shutdown)
        .concurrent_updates(True)
        .build()
    )
    register_all(app)
    app.add_error_handler(on_error)
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


if __name__ == "__main__":
    main()