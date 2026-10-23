import base64
import calendar
import datetime
import hashlib
import html
import logging
import math
import os
import re
import secrets
import sqlite3
import threading
import warnings
import time
import xml.etree.ElementTree as ET
import unicodedata
from contextlib import contextmanager
from urllib.parse import urlparse

import requests
from dotenv import load_dotenv

load_dotenv()

from telegram import (
    BotCommand,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    ReplyKeyboardRemove,
    MenuButtonCommands,
    Update,
)
from telegram.ext import (
    ApplicationBuilder,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    ConversationHandler,
    MessageHandler,
    TypeHandler,
    filters,
)

# ============================================================
# LOGGING
# ============================================================
# httpx/httpcore loggano l'URL completo delle richieste, che per Telegram
# contiene il token del bot: li silenziamo. Non logghiamo mai eccezioni
# complete di requests/httpx (anche loro includono l'URL), solo il tipo.
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(name)s: %(message)s",
)
for _noisy in ("httpx", "httpcore", "telegram", "urllib3"):
    logging.getLogger(_noisy).setLevel(logging.WARNING)
log = logging.getLogger("flipbot")

# ============================================================
# CONFIG
# ============================================================
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "")
BOT_STANDBY = os.getenv("BOT_STANDBY", "").strip().lower() in {"1", "true", "yes", "on"}
EBAY_CLIENT_ID = os.getenv("EBAY_CLIENT_ID", "").strip().strip("\"'").strip()
EBAY_CLIENT_SECRET = os.getenv("EBAY_CLIENT_SECRET", "").strip().strip("\"'").strip()

# Un solo abbonamento: 5 € per carta monitorata per mese.
PRICE_PER_CARD_MONTH_EUR = 5
PLAN_LABEL = {"FREE": "Nessun abbonamento", "CUSTOM": "🎴 Monitoraggio", "ADMIN": "👑 ADMIN", "PREMIUM": "🎴 Monitoraggio", "VIP": "🎴 Monitoraggio"}
MAX_USER_CARDS = 100
MAX_SUBSCRIPTION_MONTHS = 12

# Unico link PayPal configurato nel file .env: PAYPAL_LINK.
def _paypal_base_url(raw: str) -> str:
    raw = (raw or "").strip()
    if not raw:
        return ""
    try:
        p = urlparse(raw)
    except ValueError:
        return ""
    host = (p.hostname or "").lower().rstrip(".")
    if p.scheme != "https" or host not in {"paypal.me", "www.paypal.me"} or p.query or p.fragment:
        return ""
    parts = [x for x in p.path.split("/") if x]
    if not parts or len(parts[0]) > 80 or not re.fullmatch(r"[A-Za-z0-9._-]+", parts[0]):
        return ""
    return f"https://{host}/{parts[0]}"

PAYPAL_LINK = _paypal_base_url(os.getenv("PAYPAL_LINK", ""))

# Dati per pagamento tramite bonifico istantaneo.
BANK_ACCOUNT_HOLDER = os.getenv("BANK_ACCOUNT_HOLDER", "").strip()
BANK_IBAN = os.getenv("BANK_IBAN", "").strip().replace(" ", "")
BANK_CAUSALE = os.getenv("BANK_CAUSALE", "").strip()
BANK_TRANSFER_AVAILABLE = bool(BANK_ACCOUNT_HOLDER and BANK_IBAN and BANK_CAUSALE)

ADMIN_CHAT_ID = os.getenv("ADMIN_CHAT_ID", "").strip()
if not re.fullmatch(r"\d{1,20}", ADMIN_CHAT_ID):
    ADMIN_CHAT_ID = ""

SUPPORT_USERNAME = os.getenv("SUPPORT_USERNAME", "").strip().lstrip("@")
if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]{4,31}", SUPPORT_USERNAME):
    SUPPORT_USERNAME = ""
SUPPORT_URL = (
    f"https://t.me/{SUPPORT_USERNAME}"
    if SUPPORT_USERNAME
    else (f"tg://user?id={ADMIN_CHAT_ID}" if ADMIN_CHAT_ID else "")
)

EBAY_CARD_CATEGORY_ID = "183454"
DB_PATH = os.getenv("BOT_DB_PATH", "bot_database.db")
ACTIVE_STATUS = "ACTIVE"

MAX_CARD_NAME_LEN = 100
MAX_CARD_NUMBER_LEN = 30
MAX_SET_NAME_LEN = 100
MAX_LANGUAGE_LEN = 5
MAX_TELEGRAM_TEXT_LEN = 4096
MAX_BUDGET_INPUT_LEN = 32
MAX_NUMERIC_INPUT_LEN = 12
MAX_USERNAME_LEN = 32
MAX_FIRST_NAME_LEN = 64
MAX_TARGET_PRICE = 100000.0
POKEMON_NAMES_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "pokemon_names.txt")
POKEMON_NAMES_SOURCE_URL = "https://raw.githubusercontent.com/sindresorhus/pokemon/refs/heads/main/data/en.json"
MAX_TITLE_LEN = 120
MIN_SECONDS_BETWEEN_UPDATES = 0.7
PAYMENT_REQUEST_COOLDOWN = 3600
PAYMENT_REQUEST_RETENTION_DAYS = 30
RENEW_WINDOW_DAYS = 7
ALERT_CLAIM_STALE_SECONDS = 300

ADD_CARD_NAME, ADD_CARD_NUMBER, ADD_CARD_SET, ADD_CARD_LANGUAGE, ADD_CARD_TARGET, ADD_CARD_CONFIRM, EDIT_CARD_PRICE = range(7)
ADMIN_EDIT_SELECT, ADMIN_EDIT_FIELD, ADMIN_EDIT_VALUE = range(7, 10)
SUB_CARDS, SUB_MONTHS = range(6, 8)
PRIVATE = filters.ChatType.PRIVATE

# eBay: tetto assoluto noto e tetto operativo con margine di sicurezza.
ABSOLUTE_DAILY_LIMIT = 4800
OPERATING_DAILY_LIMIT = min(4500, ABSOLUTE_DAILY_LIMIT)
EBAY_TOKEN_TTL = 5400

# Stato runtime dello scanner.
CURRENT_DAILY_CALLS = 0
_LAST_SEEN = {}
LAST_SCAN_BY_CHAT = {}
SCANNER_WAKE = threading.Event()
PROCESS_LOCK_HANDLE = None


def acquire_process_lock():
    """Impedisce due istanze contemporanee dello stesso bot/scanner."""
    global PROCESS_LOCK_HANDLE
    lock_path = DB_PATH + ".lock"
    handle = open(lock_path, "a+b")
    try:
        if os.name == "nt":
            import msvcrt
            handle.seek(0)
            if not handle.read(1):
                handle.seek(0)
                handle.write(b"0")
                handle.flush()
            handle.seek(0)
            msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
        else:
            import fcntl
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except (OSError, BlockingIOError):
        handle.close()
        raise RuntimeError("Un'altra istanza di POKEBOT è già in esecuzione con questo database.")
    PROCESS_LOCK_HANDLE = handle

# Promemoria.
REMINDER_DAYS = 3
NOTICE_CHECK_INTERVAL = 600

BOT_DESCRIPTION = (
    "🎴 POKEBOT\n\n"
    "Ti è mai capitato di trovare una carta a un prezzo ottimo quando ormai era troppo tardi? 👀\n\n"
    "POKEBOT monitora eBay.it 24/7 e cerca continuamente le carte che ti interessano. "
    "Imposti la carta e il budget massimo: quando trova un'inserzione entro il tuo budget, "
    "ti invia un avviso con prezzo, eventuale spedizione, foto e link. 🚨\n\n"
    "Un solo abbonamento: 5 € al mese per ogni carta monitorata."
)
BOT_SHORT_DESCRIPTION = (
    "🔎 POKEBOT monitora eBay.it e ti avvisa quando trova carte Pokémon entro il tuo budget."
)
# ============================================================
# TEMA POKÉMON
# ============================================================
BTN_ADD = "🎴 Aggiungi carta"
BTN_CARDS = "📕 Pokédex"
BTN_ACCOUNT = "🎒 Account"
BTN_HELP = "❓ Guida"

# Pulsanti delle vecchie tastiere fisse: ora rimosse, ma i client che le hanno
# ancora in cache continuano a funzionare (la risposta toglie la tastiera).
# Account include anche i vecchi pulsanti «Abbonamento», così non restano sezioni duplicate.
LEGACY_BUTTONS = {
    BTN_ADD: ["➕ Aggiungi carta"],
    BTN_CARDS: ["📋 Le mie carte"],
    BTN_ACCOUNT: ["🎒 Account", "ℹ️ Il mio account", "🏅 Abbonamento", "💳 Abbonamento"],
    BTN_HELP: ["❓ Come funziona"],
}
ALL_MENU_TEXTS = [t for b, old in LEGACY_BUTTONS.items() for t in [b, *old]]
MENU_FILTER = filters.Text(ALL_MENU_TEXTS)

DIV = "━━━━━━━━━━━━━━━━━━"



def esc(value) -> str:
    return html.escape(str(value), quote=True)


def is_admin_chat(chat_id) -> bool:
    return bool(ADMIN_CHAT_ID and str(chat_id) == ADMIN_CHAT_ID)


def plan_label(plan: str) -> str:
    return PLAN_LABEL.get(plan, plan)


def _slot_bar(used: int, total: int) -> str:
    """Visualizza i posti acquistati/usati per le carte monitorate."""
    if total <= 0:
        return ""
    used = max(0, min(int(used), int(total)))
    icons = ["🟢"] * used + ["⚪"] * (total - used)
    rows = ["".join(icons[i:i + 10]) for i in range(0, total, 10)]
    return "\n".join(rows)


def budget_bar(total: float, target: float, width: int = 10) -> str:
    ratio = 0.0 if target <= 0 else max(0.0, min(total / target, 1.0))
    filled = round(ratio * width)
    return "▰" * filled + "▱" * (width - filled) + f" {ratio * 100:.0f}%"


def fmt_date(iso_value) -> str:
    dt = _parse_iso(iso_value)
    return dt.strftime("%d/%m/%Y") if dt else "n/d"


def days_left(iso_value) -> int:
    dt = _parse_iso(iso_value)
    if not dt:
        return 0
    delta = dt - datetime.datetime.now(datetime.timezone.utc)
    return max(0, math.ceil(delta.total_seconds() / 86400))


def fmt_ago(ts) -> str:
    """'2 minuti fa' a partire da un timestamp time.time(); '' se sconosciuto."""
    if not ts:
        return ""
    sec = max(0, int(time.time() - ts))
    if sec < 60:
        return "pochi secondi fa"
    minutes = sec // 60
    if minutes < 60:
        return "1 minuto fa" if minutes == 1 else f"{minutes} minuti fa"
    hours = minutes // 60
    if hours < 48:
        return "1 ora fa" if hours == 1 else f"{hours} ore fa"
    return f"{hours // 24} giorni fa"


def monitor_line(chat_id: str, used: int) -> str:
    """Mostra quanto è recente l'ultimo controllo riuscito per la chat."""
    if used <= 0:
        return "📡 Monitoraggio: <i>aggiungi una carta per iniziare</i>"
    ago = fmt_ago(LAST_SCAN_BY_CHAT.get(str(chat_id)))
    if not ago:
        return "📡 Ultimo controllo: <i>in corso…</i>"
    return f"📡 Ultimo controllo: <b>{ago}</b>"


def parse_budget(raw: str):
    """Budget massimo in euro da testo ('350' o '350,50'); None se non valido."""
    raw = normalize_user_text(raw, MAX_BUDGET_INPUT_LEN)
    if raw is None:
        return None
    raw = raw.replace(",", ".")
    if re.fullmatch(r"\d{1,6}(?:\.\d{1,2})?", raw):
        value = float(raw)
        if math.isfinite(value) and 0 < value <= MAX_TARGET_PRICE:
            return value
    return None


# ============================================================
# DATABASE
# ============================================================


def wake_scanner(reason: str = "evento"):
    """Risveglia lo scanner prima dell'intervallo calcolato per ricalcolare la coda."""
    log.debug("Wake scanner: %s", clean_text(reason)[:120])
    SCANNER_WAKE.set()


def add_months(dt: datetime.datetime, months: int) -> datetime.datetime:
    """Nel listino POKEBOT un mese commerciale vale 30 giorni esatti."""
    if not isinstance(months, int) or months < 0:
        raise ValueError("months non valido")
    return dt + datetime.timedelta(days=30 * months)


def custom_price_cents(card_count: int, months: int) -> int:
    if not isinstance(card_count, int) or not 1 <= card_count <= MAX_USER_CARDS:
        raise ValueError("Numero carte non valido")
    if not isinstance(months, int) or not 1 <= months <= MAX_SUBSCRIPTION_MONTHS:
        raise ValueError("Numero mesi non valido")
    return PRICE_PER_CARD_MONTH_EUR * 100 * card_count * months


@contextmanager
def db():
    """Connessione SQLite breve e thread-safe."""
    conn = sqlite3.connect(DB_PATH, timeout=30, check_same_thread=False)
    try:
        conn.execute("PRAGMA busy_timeout = 30000")
        conn.execute("PRAGMA journal_mode = WAL")
        conn.execute("PRAGMA synchronous = NORMAL")
        conn.execute("PRAGMA foreign_keys = ON")
        yield conn
        conn.commit()
    except Exception:
        try:
            conn.rollback()
        except Exception:
            pass
        raise
    finally:
        conn.close()


def init_db():
    """Crea/aggiorna le tabelle preservando i dati esistenti."""
    with db() as conn:
        cur = conn.cursor()

        cur.execute("""
            CREATE TABLE IF NOT EXISTS users (
                chat_id TEXT PRIMARY KEY,
                plan TEXT NOT NULL DEFAULT 'FREE',
                subscription_status TEXT NOT NULL DEFAULT 'INACTIVE',
                subscription_start TEXT,
                subscription_end TEXT,
                card_limit INTEGER NOT NULL DEFAULT 0,
                reminder_3d_for TEXT,
                expired_notice_for TEXT
            )
        """)
        user_columns = {row[1] for row in cur.execute("PRAGMA table_info(users)").fetchall()}
        user_migrations = [
            ("subscription_status", "ALTER TABLE users ADD COLUMN subscription_status TEXT NOT NULL DEFAULT 'INACTIVE'"),
            ("subscription_start", "ALTER TABLE users ADD COLUMN subscription_start TEXT"),
            ("subscription_end", "ALTER TABLE users ADD COLUMN subscription_end TEXT"),
            ("card_limit", "ALTER TABLE users ADD COLUMN card_limit INTEGER NOT NULL DEFAULT 0"),
            ("reminder_3d_for", "ALTER TABLE users ADD COLUMN reminder_3d_for TEXT"),
            ("expired_notice_for", "ALTER TABLE users ADD COLUMN expired_notice_for TEXT"),
        ]
        for name, sql in user_migrations:
            if name not in user_columns:
                cur.execute(sql)

        cur.execute("""
            CREATE TABLE IF NOT EXISTS cards (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                chat_id TEXT NOT NULL,
                card_name TEXT NOT NULL,
                card_number TEXT,
                set_name TEXT,
                language TEXT,
                keywords TEXT,
                market_price REAL NOT NULL DEFAULT 0,
                min_margin_pct REAL NOT NULL DEFAULT 0,
                max_target_price REAL,
                monitoring_enabled INTEGER NOT NULL DEFAULT 1 CHECK (monitoring_enabled IN (0, 1)),
                FOREIGN KEY (chat_id) REFERENCES users(chat_id)
            )
        """)
        card_columns = {row[1] for row in cur.execute("PRAGMA table_info(cards)").fetchall()}
        remove_existing_admin_cards = "monitoring_enabled" not in card_columns
        card_migrations = [
            ("card_number", "ALTER TABLE cards ADD COLUMN card_number TEXT"),
            ("set_name", "ALTER TABLE cards ADD COLUMN set_name TEXT"),
            ("language", "ALTER TABLE cards ADD COLUMN language TEXT"),
            ("subscription_package_id", "ALTER TABLE cards ADD COLUMN subscription_package_id INTEGER"),
            ("monitoring_enabled", "ALTER TABLE cards ADD COLUMN monitoring_enabled INTEGER NOT NULL DEFAULT 1 CHECK (monitoring_enabled IN (0, 1))"),
        ]
        for name, sql in card_migrations:
            if name not in card_columns:
                cur.execute(sql)
        if remove_existing_admin_cards and ADMIN_CHAT_ID:
            removed = cur.execute(
                "DELETE FROM cards WHERE chat_id = ?",
                (ADMIN_CHAT_ID,),
            ).rowcount
            if removed:
                log.info("Migrazione admin: rimosse dal Pokédex %s carte admin esistenti.", removed)
        card_columns = {row[1] for row in cur.execute("PRAGMA table_info(cards)").fetchall()}
        if "max_target_price" not in card_columns:
            cur.execute("ALTER TABLE cards ADD COLUMN max_target_price REAL")
            cur.execute(
                "UPDATE cards SET max_target_price = market_price * (1 - min_margin_pct) "
                "WHERE max_target_price IS NULL"
            )

        cur.execute("""
            CREATE TABLE IF NOT EXISTS alerted_listings (
                chat_id TEXT NOT NULL,
                card_id INTEGER NOT NULL,
                item_id TEXT NOT NULL,
                last_alerted_price REAL NOT NULL,
                alerted_at TEXT NOT NULL,
                claim_token TEXT,
                claim_at REAL,
                delivered INTEGER NOT NULL DEFAULT 1,
                PRIMARY KEY (chat_id, card_id, item_id),
                FOREIGN KEY (chat_id) REFERENCES users(chat_id),
                FOREIGN KEY (card_id) REFERENCES cards(id) ON DELETE CASCADE
            )
        """)
        alerted_columns = {row[1] for row in cur.execute("PRAGMA table_info(alerted_listings)").fetchall()}
        for name, sql in [
            ("claim_token", "ALTER TABLE alerted_listings ADD COLUMN claim_token TEXT"),
            ("claim_at", "ALTER TABLE alerted_listings ADD COLUMN claim_at REAL"),
            ("delivered", "ALTER TABLE alerted_listings ADD COLUMN delivered INTEGER NOT NULL DEFAULT 1"),
        ]:
            if name not in alerted_columns:
                cur.execute(sql)

        cur.execute("""
            CREATE TABLE IF NOT EXISTS daily_api_usage (
                usage_date TEXT PRIMARY KEY,
                calls INTEGER NOT NULL DEFAULT 0
            )
        """)

        cur.execute("""
            CREATE TABLE IF NOT EXISTS payment_requests (
                chat_id TEXT PRIMARY KEY,
                package_key TEXT NOT NULL DEFAULT 'CUSTOM',
                username TEXT NOT NULL DEFAULT '-',
                renewal INTEGER NOT NULL DEFAULT 0,
                created_at REAL NOT NULL,
                request_token TEXT,
                card_count INTEGER,
                months INTEGER,
                amount_cents INTEGER,
                payment_method TEXT NOT NULL DEFAULT 'unspecified',
                status TEXT NOT NULL DEFAULT 'PENDING',
                processed_at REAL
            )
        """)
        payment_columns = {row[1] for row in cur.execute("PRAGMA table_info(payment_requests)").fetchall()}
        migrations = [
            ("request_token", "ALTER TABLE payment_requests ADD COLUMN request_token TEXT"),
            ("card_count", "ALTER TABLE payment_requests ADD COLUMN card_count INTEGER"),
            ("months", "ALTER TABLE payment_requests ADD COLUMN months INTEGER"),
            ("amount_cents", "ALTER TABLE payment_requests ADD COLUMN amount_cents INTEGER"),
            ("payment_method", "ALTER TABLE payment_requests ADD COLUMN payment_method TEXT NOT NULL DEFAULT 'unspecified'"),
            ("status", "ALTER TABLE payment_requests ADD COLUMN status TEXT NOT NULL DEFAULT 'PENDING'"),
            ("processed_at", "ALTER TABLE payment_requests ADD COLUMN processed_at REAL"),
        ]
        for name, sql in migrations:
            if name not in payment_columns:
                cur.execute(sql)
        cur.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_payment_request_token ON payment_requests(request_token)")
        cur.execute(
            "UPDATE payment_requests SET status = 'REJECTED', processed_at = ? "
            "WHERE status = 'PENDING' AND (request_token IS NULL OR card_count IS NULL OR months IS NULL)",
            (time.time(),),
        )

        cur.execute("""
            CREATE TABLE IF NOT EXISTS bot_state (
                state_key TEXT PRIMARY KEY,
                state_value TEXT NOT NULL
            )
        """)

        cur.execute("""
            CREATE TABLE IF NOT EXISTS subscription_packages (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                source_key TEXT NOT NULL UNIQUE,
                chat_id TEXT NOT NULL,
                card_count INTEGER NOT NULL CHECK (card_count > 0),
                subscription_start TEXT NOT NULL,
                subscription_end TEXT NOT NULL,
                status TEXT NOT NULL CHECK (status IN ('ACTIVE', 'EXPIRED', 'CANCELED')),
                reminder_3d_for TEXT,
                expired_notice_for TEXT,
                created_at REAL NOT NULL,
                FOREIGN KEY (chat_id) REFERENCES users(chat_id)
            )
        """)
        cur.execute("""
            CREATE INDEX IF NOT EXISTS idx_subscription_packages_chat_status_end
            ON subscription_packages(chat_id, status, subscription_end)
        """)

        # Migrazione trasparente dal vecchio Premium/VIP al nuovo abbonamento a consumo.
        cur.execute("""
            UPDATE users
            SET card_limit = CASE
                WHEN plan = 'PREMIUM' AND card_limit = 0 THEN 5
                WHEN plan = 'VIP' AND card_limit = 0 THEN 20
                ELSE card_limit
            END
            WHERE plan IN ('PREMIUM', 'VIP')
        """)
        cur.execute("UPDATE users SET plan = 'CUSTOM' WHERE plan IN ('PREMIUM', 'VIP')")

        # Preserve existing entitlements as legacy packages. Historical renewal
        # rows were overwritten, so the migration keeps the currently stored end.
        migration_now = datetime.datetime.now(datetime.timezone.utc)
        legacy_subscriptions = cur.execute("""
            SELECT chat_id, subscription_status, subscription_start,
                   subscription_end, card_limit
            FROM users
            WHERE plan = 'CUSTOM' AND card_limit > 0
              AND subscription_start IS NOT NULL AND subscription_end IS NOT NULL
              AND NOT EXISTS (
                  SELECT 1 FROM subscription_packages packages
                  WHERE packages.chat_id = users.chat_id
              )
        """).fetchall()
        for chat_id, status, start_raw, end_raw, card_limit in legacy_subscriptions:
            start = _parse_iso(start_raw)
            end = _parse_iso(end_raw)
            if not start or not end:
                continue
            renewal = cur.execute("""
                SELECT request_token, card_count, months
                FROM payment_requests
                WHERE chat_id = ? AND status = 'APPROVED' AND renewal = 1
                ORDER BY processed_at DESC LIMIT 1
            """, (str(chat_id),)).fetchone()
            previous_end = None
            if renewal and renewal[1] and renewal[2]:
                candidate = end - datetime.timedelta(days=30 * int(renewal[2]))
                if start < candidate < end:
                    previous_end = candidate

            if previous_end:
                previous_status = 'ACTIVE' if status == ACTIVE_STATUS and previous_end > migration_now else 'EXPIRED'
                renewal_status = 'ACTIVE' if status == ACTIVE_STATUS and end > migration_now else 'EXPIRED'
                package_rows = [
                    (f"legacy-base:{chat_id}", max(1, int(card_limit)), start, previous_end, previous_status),
                    (f"legacy-renewal:{chat_id}:{renewal[0]}", int(renewal[1]), previous_end, end, renewal_status),
                ]
            else:
                package_status = 'ACTIVE' if status == ACTIVE_STATUS and end > migration_now else 'EXPIRED'
                package_rows = [
                    (f"legacy:{chat_id}", max(1, int(card_limit)), start, end, package_status),
                ]
            for source_key, package_cards, package_start, package_end, package_status in package_rows:
                cur.execute("""
                    INSERT OR IGNORE INTO subscription_packages
                        (source_key, chat_id, card_count, subscription_start,
                         subscription_end, status, created_at)
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                """, (
                    source_key, str(chat_id), package_cards,
                    package_start.isoformat(), package_end.isoformat(), package_status, time.time(),
                ))

        # Attach saved cards to the legacy entitlements they consume. New cards
        # are attached to a package when inserted, so expiry disables the right cards.
        for (chat_id,) in cur.execute("SELECT DISTINCT chat_id FROM cards WHERE subscription_package_id IS NULL").fetchall():
            packages = cur.execute("""
                SELECT id, card_count FROM subscription_packages
                WHERE chat_id = ? ORDER BY subscription_start, id
            """, (str(chat_id),)).fetchall()
            cards = cur.execute("SELECT id FROM cards WHERE chat_id = ? ORDER BY id", (str(chat_id),)).fetchall()
            card_index = 0
            for package_id, card_count in packages:
                for card_row in cards[card_index:card_index + int(card_count)]:
                    cur.execute("UPDATE cards SET subscription_package_id = ? WHERE id = ?", (package_id, card_row[0]))
                card_index += int(card_count)

        # I vecchi cursori non servono più: lo scanner lavora per cicli completi dinamici.
        cur.execute("DELETE FROM bot_state WHERE state_key = 'scan_cursor'")

        cutoff_usage = (
            datetime.datetime.now(datetime.timezone.utc).date() - datetime.timedelta(days=7)
        ).isoformat()
        cur.execute("DELETE FROM daily_api_usage WHERE usage_date < ?", (cutoff_usage,))
        payment_cutoff = time.time() - PAYMENT_REQUEST_RETENTION_DAYS * 86400
        cur.execute(
            "DELETE FROM payment_requests WHERE created_at < ? AND status <> 'PENDING'",
            (payment_cutoff,),
        )

    try:
        os.chmod(DB_PATH, 0o600)
    except OSError:
        pass
    log.info("Database inizializzato: %s", os.path.abspath(DB_PATH))


def db_get_user(chat_id):
    with db() as conn:
        row = conn.execute("""
            SELECT chat_id, plan, subscription_status,
                   subscription_start, subscription_end, card_limit
            FROM users WHERE chat_id = ?
        """, (str(chat_id),)).fetchone()
        if not row:
            return None
        summary = _refresh_subscription_summary_on_conn(conn, str(chat_id))
    return {
        "chat_id": row[0], "plan": "ADMIN" if is_admin_chat(row[0]) else row[1],
        "subscription_status": summary["subscription_status"],
        "subscription_start": summary["subscription_start"],
        "subscription_end": summary["subscription_end"],
        "card_limit": summary["card_limit"],
        "subscription_packages": summary["subscription_packages"],
    }


def db_ensure_user(chat_id):
    with db() as conn:
        conn.execute("""
            INSERT OR IGNORE INTO users (chat_id, plan, subscription_status, card_limit)
            VALUES (?, 'FREE', 'INACTIVE', 0)
        """, (str(chat_id),))


def _parse_iso(value):
    if not value:
        return None
    try:
        dt = datetime.datetime.fromisoformat(value)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=datetime.timezone.utc)
        return dt
    except (TypeError, ValueError):
        return None


def _move_cards_to_scheduled_renewal_on_conn(conn, chat_id, now_raw):
    """Carry card assignments across a legacy renewal that starts at expiry."""
    conn.execute("""
        UPDATE cards SET subscription_package_id = (
            SELECT successor.id
            FROM subscription_packages expired
            JOIN subscription_packages successor
              ON successor.chat_id = expired.chat_id
             AND successor.status = 'ACTIVE'
             AND successor.subscription_start = expired.subscription_end
             AND successor.subscription_start <= ?
             AND successor.subscription_end > ?
            WHERE expired.id = cards.subscription_package_id
            ORDER BY successor.subscription_start, successor.id
            LIMIT 1
        )
        WHERE cards.chat_id = ? AND cards.subscription_package_id IN (
            SELECT id FROM subscription_packages
            WHERE chat_id = ? AND status = 'ACTIVE' AND subscription_end <= ?
        )
    """, (now_raw, now_raw, str(chat_id), str(chat_id), now_raw))


def _refresh_subscription_summary_on_conn(conn, chat_id, now=None):
    """Derive legacy user fields from the packages that are currently valid."""
    chat_id = str(chat_id)
    now = now or datetime.datetime.now(datetime.timezone.utc)
    now_raw = now.isoformat()
    _move_cards_to_scheduled_renewal_on_conn(conn, chat_id, now_raw)
    conn.execute("""
        UPDATE subscription_packages SET status = 'EXPIRED'
        WHERE chat_id = ? AND status = 'ACTIVE' AND subscription_end <= ?
    """, (chat_id, now_raw))
    rows = conn.execute("""
        SELECT card_count, subscription_start, subscription_end
        FROM subscription_packages
        WHERE chat_id = ? AND status = 'ACTIVE' AND subscription_end > ?
        ORDER BY subscription_start, subscription_end
    """, (chat_id, now_raw)).fetchall()
    if rows:
        active_rows = [row for row in rows if row[1] <= now_raw]
        card_limit = sum(int(row[0]) for row in active_rows)
        start = min(row[1] for row in rows)
        end = max(row[2] for row in rows)
        status = ACTIVE_STATUS if active_rows else 'INACTIVE'
        conn.execute("""
            UPDATE users SET plan = 'CUSTOM', subscription_status = ?,
                subscription_start = ?, subscription_end = ?, card_limit = ?
            WHERE chat_id = ? AND plan <> 'ADMIN'
        """, (status, start, end, card_limit, chat_id))
        packages = [
            {"card_count": int(row[0]), "subscription_start": row[1], "subscription_end": row[2]}
            for row in rows
        ]
        return {
            "subscription_status": status, "subscription_start": start,
            "subscription_end": end, "card_limit": card_limit,
            "subscription_packages": packages,
        }

    last = conn.execute("""
        SELECT MIN(subscription_start), MAX(subscription_end)
        FROM subscription_packages WHERE chat_id = ?
    """, (chat_id,)).fetchone()
    has_packages = conn.execute(
        "SELECT 1 FROM subscription_packages WHERE chat_id = ? LIMIT 1", (chat_id,)
    ).fetchone() is not None
    expired = conn.execute(
        "SELECT 1 FROM subscription_packages WHERE chat_id = ? AND status = 'EXPIRED' LIMIT 1",
        (chat_id,),
    ).fetchone() is not None
    status = 'EXPIRED' if expired else 'INACTIVE'
    start, end = (last[0], last[1]) if has_packages else (None, None)
    conn.execute("""
        UPDATE users SET subscription_status = ?, subscription_start = ?,
            subscription_end = ?, card_limit = 0
        WHERE chat_id = ? AND plan <> 'ADMIN'
    """, (status, start, end, chat_id))
    return {
        "subscription_status": status, "subscription_start": start,
        "subscription_end": end, "card_limit": 0, "subscription_packages": [],
    }


def db_get_active_subscription_packages(chat_id):
    now_raw = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with db() as conn:
        _move_cards_to_scheduled_renewal_on_conn(conn, str(chat_id), now_raw)
        conn.execute("""
            UPDATE subscription_packages SET status = 'EXPIRED'
            WHERE chat_id = ? AND status = 'ACTIVE' AND subscription_end <= ?
        """, (str(chat_id), now_raw))
        rows = conn.execute("""
            SELECT card_count, subscription_start, subscription_end
            FROM subscription_packages
        WHERE chat_id = ? AND status = 'ACTIVE'
          AND subscription_start <= ? AND subscription_end > ?
        ORDER BY subscription_end
        """, (str(chat_id), now_raw, now_raw)).fetchall()
    return [
        {"card_count": int(row[0]), "subscription_start": row[1], "subscription_end": row[2]}
        for row in rows
    ]


def _max_reserved_subscription_capacity_on_conn(conn, chat_id, now=None, proposed=None):
    now = now or datetime.datetime.now(datetime.timezone.utc)
    rows = conn.execute("""
        SELECT card_count, subscription_start, subscription_end
        FROM subscription_packages
        WHERE chat_id = ? AND status = 'ACTIVE' AND subscription_end > ?
    """, (str(chat_id), now.isoformat())).fetchall()
    events = []
    for count, start_raw, end_raw in rows:
        start, end = _parse_iso(start_raw), _parse_iso(end_raw)
        if not start or not end or end <= now:
            continue
        start = max(start, now)
        events.append((start, 1, int(count)))
        events.append((end, 0, -int(count)))
    if proposed:
        count, start, end = proposed
        events.append((max(start, now), 1, int(count)))
        events.append((end, 0, -int(count)))
    current = peak = 0
    for _, _, delta in sorted(events, key=lambda event: (event[0], event[1])):
        current += delta
        peak = max(peak, current)
    return peak


def db_subscription_is_active(user):
    """Admin always active; regular users need at least one valid package."""
    if not user:
        return False
    if is_admin_chat(user["chat_id"]):
        return True
    current = db_get_user(user["chat_id"])
    return bool(current and int(current["card_limit"]) > 0)


def _activate_custom_subscription_on_conn(conn, chat_id, card_count, months):
    if not (1 <= int(card_count) <= MAX_USER_CARDS):
        raise ValueError("Numero carte non valido")
    if not (1 <= int(months) <= MAX_SUBSCRIPTION_MONTHS):
        raise ValueError("Numero mesi non valido")

    chat_id = str(chat_id)
    if conn.execute("SELECT 1 FROM users WHERE chat_id = ?", (chat_id,)).fetchone() is None:
        raise ValueError("Utente non trovato")

    now = datetime.datetime.now(datetime.timezone.utc)
    current_cards = int(conn.execute(
        "SELECT COUNT(*) FROM cards WHERE chat_id = ?", (chat_id,)
    ).fetchone()[0])
    summary = _refresh_subscription_summary_on_conn(conn, chat_id, now)
    current_limit = int(summary["card_limit"])
    if current_limit > 0:
        now_raw = now.isoformat()
        used_slots = int(conn.execute("""
            SELECT COUNT(*) FROM cards c
            JOIN subscription_packages p ON p.id = c.subscription_package_id
            WHERE c.chat_id = ? AND p.status = 'ACTIVE'
              AND p.subscription_start <= ? AND p.subscription_end > ?
        """, (chat_id, now_raw, now_raw)).fetchone()[0])
        if used_slots < current_limit:
            raise ValueError("L'utente ha ancora slot liberi: deve usarli tutti prima di aggiungere un pacchetto.")
    new_limit = current_limit + int(card_count)
    end = add_months(now, int(months))
    reserved_peak = _max_reserved_subscription_capacity_on_conn(
        conn, chat_id, now, proposed=(int(card_count), now, end)
    )
    if reserved_peak > MAX_USER_CARDS:
        raise ValueError(f"Il pacchetto supererebbe il limite massimo di {MAX_USER_CARDS} carte monitorate.")
    if current_cards > new_limit:
        missing = current_cards - current_limit
        raise ValueError(f"L'utente ha {current_cards} carte salvate: il pacchetto deve coprirne almeno altre {missing}.")

    start = now
    cur = conn.execute("""
        INSERT INTO subscription_packages
            (source_key, chat_id, card_count, subscription_start, subscription_end,
             status, reminder_3d_for, expired_notice_for, created_at)
        VALUES (?, ?, ?, ?, ?, 'ACTIVE', NULL, NULL, ?)
    """, (
        f"purchase:{secrets.token_hex(12)}", chat_id, int(card_count),
        start.isoformat(), end.isoformat(), time.time(),
    ))
    package_id = cur.lastrowid
    # Previously saved cards whose old packages expired can be covered again by
    # this purchase before the user adds more cards.
    unassigned = conn.execute("""
        SELECT id FROM cards WHERE chat_id = ? AND subscription_package_id IS NULL
        ORDER BY id LIMIT ?
    """, (chat_id, int(card_count))).fetchall()
    for (card_id,) in unassigned:
        conn.execute("UPDATE cards SET subscription_package_id = ? WHERE id = ?", (package_id, card_id))
    _refresh_subscription_summary_on_conn(conn, chat_id, now)
    return end


def db_activate_subscription(chat_id, card_count, months):
    """Adds one independently expiring card package."""
    with db() as conn:
        end = _activate_custom_subscription_on_conn(conn, chat_id, card_count, months)
        conn.execute("""
            UPDATE payment_requests
            SET status = 'REJECTED', processed_at = ?
            WHERE chat_id = ? AND status = 'PENDING'
        """, (time.time(), str(chat_id)))
    wake_scanner("abbonamento attivato")
    log.info("Abbonamento attivato: chat=%s carte=%s mesi=%s scadenza=%s",
             chat_id, card_count, months, end.isoformat())
    return end


def db_deactivate_subscription(chat_id):
    with db() as conn:
        conn.execute("""
            UPDATE subscription_packages SET status = 'CANCELED'
            WHERE chat_id = ? AND status = 'ACTIVE'
        """, (str(chat_id),))
        conn.execute("UPDATE cards SET subscription_package_id = NULL WHERE chat_id = ?", (str(chat_id),))
        conn.execute("""
            UPDATE subscription_packages
            SET expired_notice_for = subscription_end
            WHERE chat_id = ? AND status = 'EXPIRED'
        """, (str(chat_id),))
        conn.execute("""
            UPDATE users
            SET plan = 'CUSTOM', subscription_status = 'INACTIVE', card_limit = 0
            WHERE chat_id = ?
        """, (str(chat_id),))
        conn.execute("""
            UPDATE payment_requests
            SET status = 'REJECTED', processed_at = ?
            WHERE chat_id = ? AND status = 'PENDING'
        """, (time.time(), str(chat_id)))
    wake_scanner("abbonamento disattivato")


def db_get_user_cards(chat_id):
    now = datetime.datetime.now(datetime.timezone.utc)
    with db() as conn:
        rows = conn.execute("""
            SELECT c.id, c.card_name, c.card_number, c.set_name, c.language, c.keywords,
                   c.market_price, c.min_margin_pct, c.max_target_price,
                   p.subscription_start, p.subscription_end, c.monitoring_enabled
            FROM cards c LEFT JOIN subscription_packages p ON p.id = c.subscription_package_id
            WHERE c.chat_id = ? ORDER BY c.id
        """, (str(chat_id),)).fetchall()
    cards = []
    for r in rows:
        start, end = _parse_iso(r[9]), _parse_iso(r[10])
        covered = bool(end and end > now and (not start or start <= now))
        monitoring_enabled = bool(r[11])
        if is_admin_chat(chat_id):
            coverage = "Monitoraggio illimitato" if monitoring_enabled else "Monitoraggio in pausa"
            covered = monitoring_enabled
        elif not monitoring_enabled:
            coverage = "Monitoraggio in pausa"
            covered = False
        elif start and start > now and end:
            coverage = f"Coperta dal {fmt_date(r[9])} al {fmt_date(r[10])}"
        elif covered:
            coverage = f"Coperta fino al {fmt_date(r[10])}"
        elif end:
            coverage = "Pacchetto scaduto"
        else:
            coverage = "Non coperta da un pacchetto"
        cards.append({
            "id": r[0], "name": r[1], "card_number": r[2] or "",
            "set_name": r[3] or "", "language": r[4] or "", "keywords": r[5] or r[1],
            "market_price_eur": r[6], "min_margin_pct": r[7],
            "max_target_price_eur": r[8] if r[8] is not None else r[6] * (1 - r[7]),
            "coverage_text": coverage, "is_monitored": covered,
            "monitoring_enabled": monitoring_enabled,
        })
    return cards


def db_get_monitored_user_cards(chat_id, now=None):
    now = now or datetime.datetime.now(datetime.timezone.utc)
    with db() as conn:
        if is_admin_chat(chat_id):
            rows = conn.execute("""
                SELECT id, card_name, card_number, set_name, language, keywords,
                       market_price, min_margin_pct, max_target_price
                FROM cards
                WHERE chat_id = ? AND monitoring_enabled = 1
                ORDER BY id
            """, (str(chat_id),)).fetchall()
        else:
            rows = conn.execute("""
                SELECT c.id, c.card_name, c.card_number, c.set_name, c.language, c.keywords,
                       c.market_price, c.min_margin_pct, c.max_target_price
                FROM cards c JOIN subscription_packages p ON p.id = c.subscription_package_id
                WHERE c.chat_id = ? AND c.monitoring_enabled = 1 AND p.status = 'ACTIVE'
                  AND p.subscription_start <= ? AND p.subscription_end > ?
                ORDER BY c.id
            """, (str(chat_id), now.isoformat(), now.isoformat())).fetchall()
    return [
        {
            "id": r[0], "name": r[1], "card_number": r[2] or "",
            "set_name": r[3] or "", "language": r[4] or "", "keywords": r[5] or r[1],
            "market_price_eur": r[6], "min_margin_pct": r[7],
            "max_target_price_eur": r[8] if r[8] is not None else r[6] * (1 - r[7]),
        }
        for r in rows
    ]


def db_set_card_monitoring(chat_id, card_id, enabled):
    """Admin can pause/resume its own cards without deleting their saved data."""
    if not is_admin_chat(chat_id):
        return False
    try:
        card_id = int(card_id)
    except (TypeError, ValueError):
        return False
    if card_id <= 0:
        return False
    with db() as conn:
        cur = conn.execute(
            "UPDATE cards SET monitoring_enabled = ? WHERE id = ? AND chat_id = ?",
            (1 if enabled else 0, card_id, str(chat_id)),
        )
    if cur.rowcount == 1:
        wake_scanner("monitoraggio admin aggiornato")
        return True
    return False


def db_delete_card(chat_id, card_id):
    """Admin can permanently remove a card from its own Pokédex."""
    if not is_admin_chat(chat_id):
        return False
    try:
        card_id = int(card_id)
    except (TypeError, ValueError):
        return False
    if card_id <= 0:
        return False
    with db() as conn:
        cur = conn.execute(
            "DELETE FROM cards WHERE id = ? AND chat_id = ?",
            (card_id, str(chat_id)),
        )
    if cur.rowcount == 1:
        wake_scanner("carta admin eliminata")
        return True
    return False


def _can_buy_another_package(chat_id):
    user = db_get_user(chat_id)
    active_slots = int(user.get("card_limit") or 0) if user and db_subscription_is_active(user) else 0
    if active_slots <= 0:
        return True
    now_raw = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with db() as conn:
        used_slots = conn.execute("""
            SELECT COUNT(*) FROM cards c
            JOIN subscription_packages p ON p.id = c.subscription_package_id
            WHERE c.chat_id = ? AND p.status = 'ACTIVE'
              AND p.subscription_start <= ? AND p.subscription_end > ?
        """, (str(chat_id), now_raw, now_raw)).fetchone()[0]
    return int(used_slots) >= active_slots


def db_add_card(chat_id, card_name, card_number, set_name, language, target_price, max_cards=None):
    """Inserimento atomico con validazione server-side e race protection."""
    safe_name = parse_card_name(card_name)
    safe_number = parse_card_number(card_number)
    safe_set = parse_set_name(set_name)
    safe_language = parse_language(language or "", allow_empty=True)
    try:
        safe_target = float(target_price)
    except (TypeError, ValueError):
        safe_target = float("nan")
    identity_input = " ".join(str(x or "") for x in (card_name, card_number, set_name, language) if str(x or "").strip())
    if _non_pokemon_reason(identity_input):
        raise ValueError("Carta non Pokémon TCG")
    if safe_name is None or safe_number is None or safe_set is None or safe_language is None:
        raise ValueError("Dati carta non validi")
    identity_raw = " ".join(x for x in (safe_name, safe_number, safe_set, safe_language or "") if x)
    blocked_reason = _non_pokemon_reason(identity_raw)
    if blocked_reason or not _card_contains_known_pokemon(safe_name):
        raise ValueError("Carta non Pokémon TCG")
    if not math.isfinite(safe_target) or not 0 < safe_target <= MAX_TARGET_PRICE:
        raise ValueError("Budget non valido")
    if max_cards is not None and (not isinstance(max_cards, int) or not 0 <= max_cards <= MAX_USER_CARDS):
        raise ValueError("Limite carte non valido")

    parts = [safe_name, safe_set, safe_number]
    if safe_language:
        parts.append(safe_language)
    keywords = " ".join(x for x in parts if x)
    with db() as conn:
        identity = tuple(re.sub(r"\s+", " ", str(value or "").strip()).casefold()
                         for value in (safe_name, safe_number, safe_set, safe_language or ""))
        for existing in conn.execute("""
            SELECT card_name, card_number, set_name, language
            FROM cards WHERE chat_id = ?
        """, (str(chat_id),)).fetchall():
            existing_identity = tuple(
                re.sub(r"\s+", " ", str(value or "").strip()).casefold() for value in existing
            )
            if existing_identity == identity:
                raise ValueError("Questa carta è già nel tuo Pokédex.")
        package_id = None
        if max_cards is not None:
            now_iso = datetime.datetime.now(datetime.timezone.utc).isoformat()
            used_active = conn.execute("""
                SELECT COUNT(*) FROM cards c JOIN subscription_packages p
                  ON p.id = c.subscription_package_id
                WHERE c.chat_id = ? AND p.status = 'ACTIVE'
                  AND p.subscription_start <= ? AND p.subscription_end > ?
            """, (str(chat_id), now_iso, now_iso)).fetchone()[0]
            if int(used_active) >= int(max_cards):
                return False
            candidates = conn.execute("""
                SELECT p.id, p.card_count,
                       (SELECT COUNT(*) FROM cards c WHERE c.subscription_package_id = p.id)
                FROM subscription_packages p
                WHERE p.chat_id = ? AND p.status = 'ACTIVE'
                  AND p.subscription_start <= ? AND p.subscription_end > ?
                ORDER BY p.created_at DESC, p.id DESC
            """, (str(chat_id), now_iso, now_iso)).fetchall()
            package_id = next((r[0] for r in candidates if int(r[2]) < int(r[1])), None)
            if package_id is None:
                return False
        if max_cards is None:
            cur = conn.execute("""
                INSERT INTO cards
                    (chat_id, card_name, card_number, set_name, language, keywords, subscription_package_id,
                     market_price, min_margin_pct, max_target_price)
                VALUES (?, ?, ?, ?, ?, ?, NULL, 0.0, 0.0, ?)
            """, (str(chat_id), safe_name, safe_number, safe_set, safe_language or None, keywords, safe_target))
            added = cur.rowcount == 1
        else:
            cur = conn.execute("""
                INSERT INTO cards
                    (chat_id, card_name, card_number, set_name, language, keywords, subscription_package_id,
                     market_price, min_margin_pct, max_target_price)
                SELECT ?, ?, ?, ?, ?, ?, ?, 0.0, 0.0, ?
                WHERE (SELECT COUNT(*) FROM cards c
                    JOIN subscription_packages p ON p.id = c.subscription_package_id
                    WHERE c.chat_id = ? AND p.status = 'ACTIVE'
                      AND p.subscription_start <= ? AND p.subscription_end > ?) < ?
            """, (
                str(chat_id), safe_name, safe_number, safe_set, safe_language or None, keywords,
                package_id, safe_target, str(chat_id), now_iso, now_iso, int(max_cards)
            ))
            added = cur.rowcount == 1
    if added:
        wake_scanner("nuova carta")
        log.info(
            "Carta aggiunta: chat=%s nome_len=%s numero_len=%s set_len=%s lingua=%s budget=%.2f",
            chat_id, len(safe_name), len(safe_number), len(safe_set), safe_language or "-", safe_target
        )
    return added


def db_get_all_users_data():
    with db() as conn:
        rows = conn.execute("SELECT chat_id FROM users").fetchall()
    result = {}
    for (chat_id,) in rows:
        user = db_get_user(chat_id)
        if not db_subscription_is_active(user):
            continue
        cards = db_get_monitored_user_cards(user["chat_id"])
        if is_admin_chat(user["chat_id"]):
            user["plan"] = "ADMIN"
            user["target_cards"] = cards
        else:
            user["target_cards"] = cards[:max(0, user["card_limit"])]
        result[user["chat_id"]] = user
    return result


def db_get_state(key: str, default=None):
    with db() as conn:
        row = conn.execute("SELECT state_value FROM bot_state WHERE state_key = ?", (key,)).fetchone()
    return row[0] if row else default


def db_set_state(key: str, value: str):
    with db() as conn:
        conn.execute("""
            INSERT INTO bot_state (state_key, state_value) VALUES (?, ?)
            ON CONFLICT(state_key) DO UPDATE SET state_value = excluded.state_value
        """, (key, str(value)))


def db_get_daily_api_calls():
    today = datetime.datetime.now(datetime.timezone.utc).date().isoformat()
    with db() as conn:
        row = conn.execute("SELECT calls FROM daily_api_usage WHERE usage_date = ?", (today,)).fetchone()
    return int(row[0]) if row else 0


def db_increment_daily_api_calls():
    today = datetime.datetime.now(datetime.timezone.utc).date().isoformat()
    with db() as conn:
        conn.execute("""
            INSERT INTO daily_api_usage (usage_date, calls) VALUES (?, 1)
            ON CONFLICT(usage_date) DO UPDATE SET calls = calls + 1
        """, (today,))
        row = conn.execute("SELECT calls FROM daily_api_usage WHERE usage_date = ?", (today,)).fetchone()
    return int(row[0])


def db_get_pending_payment(chat_id):
    with db() as conn:
        row = conn.execute("""
            SELECT chat_id, username, renewal, created_at, request_token,
                   card_count, months, amount_cents, payment_method, status
            FROM payment_requests
            WHERE chat_id = ? AND status = 'PENDING'
        """, (str(chat_id),)).fetchone()
    return _payment_row_to_dict(row) if row else None


def _payment_row_to_dict(row):
    return {
        "chat_id": row[0], "username": row[1], "renewal": bool(row[2]),
        "created_at": float(row[3]), "request_token": row[4],
        "card_count": int(row[5] or 0), "months": int(row[6] or 0),
        "amount_cents": int(row[7] or 0), "payment_method": row[8], "status": row[9],
    }


def db_save_pending_payment(chat_id, card_count, months, username, renewal, payment_method="unspecified"):
    try:
        card_count = int(card_count)
        months = int(months)
    except (TypeError, ValueError):
        raise ValueError("Parametri pagamento non validi")
    if not (1 <= card_count <= MAX_USER_CARDS and 1 <= months <= MAX_SUBSCRIPTION_MONTHS):
        raise ValueError("Parametri pagamento non validi")
    username = safe_telegram_username(username)
    if payment_method not in {"unspecified", "paypal", "bank_transfer"}:
        payment_method = "unspecified"
    amount_cents = custom_price_cents(card_count, months)
    token = secrets.token_hex(8)
    now = time.time()
    with db() as conn:
        conn.execute("BEGIN IMMEDIATE")
        existing = conn.execute(
            "SELECT created_at FROM payment_requests WHERE chat_id = ? AND status = 'PENDING'",
            (str(chat_id),)
        ).fetchone()
        if existing and now - float(existing[0]) < PAYMENT_REQUEST_COOLDOWN:
            return None
        conn.execute("""
            INSERT INTO payment_requests
                (chat_id, package_key, username, renewal, created_at, request_token,
                 card_count, months, amount_cents, payment_method, status, processed_at)
            VALUES (?, 'CUSTOM', ?, ?, ?, ?, ?, ?, ?, ?, 'PENDING', NULL)
            ON CONFLICT(chat_id) DO UPDATE SET
                package_key = 'CUSTOM', username = excluded.username, renewal = excluded.renewal,
                created_at = excluded.created_at, request_token = excluded.request_token,
                card_count = excluded.card_count, months = excluded.months,
                amount_cents = excluded.amount_cents, payment_method = excluded.payment_method,
                status = 'PENDING', processed_at = NULL
        """, (
            str(chat_id), username[:64] or "-", 1 if renewal else 0, now, token,
            int(card_count), int(months), amount_cents, payment_method,
        ))
    log.info("Richiesta pagamento creata: chat=%s carte=%s mesi=%s importo=%.2f",
             chat_id, card_count, months, amount_cents / 100)
    return token


def db_get_pending_payment_by_token(token):
    if not re.fullmatch(r"[0-9a-f]{16}", token or ""):
        return None
    with db() as conn:
        row = conn.execute("""
            SELECT chat_id, username, renewal, created_at, request_token,
                   card_count, months, amount_cents, payment_method, status
            FROM payment_requests
            WHERE request_token = ?
        """, (token,)).fetchone()
    return _payment_row_to_dict(row) if row else None


def db_get_pending_payments(limit=20):
    with db() as conn:
        rows = conn.execute("""
            SELECT chat_id, username, renewal, created_at, request_token,
                   card_count, months, amount_cents, payment_method, status
            FROM payment_requests
            WHERE status = 'PENDING'
            ORDER BY created_at DESC LIMIT ?
        """, (max(1, min(int(limit), 100)),)).fetchall()
    return [_payment_row_to_dict(r) for r in rows]


def db_approve_payment_request(token):
    """Approva atomicamente una richiesta: un doppio click non può attivarla due volte."""
    if not re.fullmatch(r"[0-9a-f]{16}", token or ""):
        return {"ok": False, "reason": "invalid_token"}
    with db() as conn:
        conn.execute("BEGIN IMMEDIATE")
        row = conn.execute("""
            SELECT chat_id, renewal, card_count, months, amount_cents, payment_method,
                   username, created_at
            FROM payment_requests
            WHERE request_token = ? AND status = 'PENDING'
        """, (token,)).fetchone()
        if not row:
            return {"ok": False, "reason": "not_pending"}

        target, renewal, card_count, months, amount_cents, payment_method, username, created_at = row
        current = conn.execute(
            "SELECT plan, subscription_status, subscription_end FROM users WHERE chat_id = ?",
            (str(target),),
        ).fetchone()
        now = datetime.datetime.now(datetime.timezone.utc)
        current_end = _parse_iso(current[2]) if current else None
        already_active = bool(current and current[0] == 'CUSTOM' and current[1] == ACTIVE_STATUS and current_end and current_end > now)
        if already_active and not bool(renewal):
            return {"ok": False, "reason": "already_active", "chat_id": target}
        try:
            end = _activate_custom_subscription_on_conn(conn, target, int(card_count), int(months))
        except ValueError as e:
            return {"ok": False, "reason": "validation", "message": str(e), "chat_id": target}

        changed = conn.execute("""
            UPDATE payment_requests
            SET status = 'APPROVED', processed_at = ?
            WHERE request_token = ? AND status = 'PENDING'
        """, (time.time(), token)).rowcount
        if changed != 1:
            return {"ok": False, "reason": "race"}

    wake_scanner("pagamento approvato")
    return {
        "ok": True, "chat_id": target, "card_count": int(card_count), "months": int(months),
        "amount_cents": int(amount_cents), "payment_method": payment_method,
        "username": username, "renewal": bool(renewal), "end": end,
    }


def db_reject_payment_request(token):
    if not re.fullmatch(r"[0-9a-f]{16}", token or ""):
        return None
    with db() as conn:
        row = conn.execute("""
            SELECT chat_id, card_count, months, amount_cents
            FROM payment_requests
            WHERE request_token = ? AND status = 'PENDING'
        """, (token,)).fetchone()
        if not row:
            return None
        changed = conn.execute("""
            UPDATE payment_requests
            SET status = 'REJECTED', processed_at = ?
            WHERE request_token = ? AND status = 'PENDING'
        """, (time.time(), token)).rowcount
        if changed != 1:
            return None
    return {
        "chat_id": row[0], "card_count": int(row[1] or 0),
        "months": int(row[2] or 0), "amount_cents": int(row[3] or 0),
    }


def db_get_card(chat_id, card_id):
    with db() as conn:
        row = conn.execute("""
            SELECT id, card_name, card_number, set_name, language, max_target_price
            FROM cards WHERE id = ? AND chat_id = ?
        """, (int(card_id), str(chat_id))).fetchone()
    if not row:
        return None
    return {
        "id": row[0], "name": row[1], "card_number": row[2] or "",
        "set_name": row[3] or "", "language": row[4] or "",
        "max_target_price_eur": row[5]
    }


def db_update_card_price(chat_id, card_id, new_price):
    try:
        price = float(new_price)
        card_id = int(card_id)
    except (TypeError, ValueError):
        return False
    if not math.isfinite(price) or not 0 < price <= MAX_TARGET_PRICE or card_id <= 0:
        return False
    with db() as conn:
        cur = conn.execute("""
            UPDATE cards SET max_target_price = ?
            WHERE id = ? AND chat_id = ?
        """, (price, card_id, str(chat_id)))
    return cur.rowcount == 1


def db_update_card_field(chat_id, card_id, field, raw_value):
    validators = {
        "name": parse_card_name,
        "number": parse_card_number,
        "set": parse_set_name,
        "language": lambda value: parse_language(value, allow_empty=True),
        "price": parse_budget,
    }
    if field not in validators:
        raise ValueError("Campo non modificabile")
    value = validators[field](raw_value)
    if value is None:
        messages = {
            "name": "Nome carta non valido o Pokémon non riconosciuto.",
            "number": "Numero carta non valido.",
            "set": "Nome set non valido.",
            "language": "Lingua non valida: usa 2-5 lettere o lascia vuoto.",
            "price": f"Prezzo non valido: inserisci un importo da 0,01 a {MAX_TARGET_PRICE:.0f} euro.",
        }
        raise ValueError(messages[field])

    card = db_get_card(chat_id, card_id)
    if not card:
        raise ValueError("Carta non trovata")
    if field == "price":
        if not db_update_card_price(chat_id, card_id, value):
            raise ValueError("Impossibile aggiornare il prezzo")
        wake_scanner("budget carta aggiornato")
        return value

    updated = dict(card)
    updated[{"name": "name", "number": "card_number", "set": "set_name", "language": "language"}[field]] = value
    identity = tuple(re.sub(r"\s+", " ", str(updated.get(key) or "").strip()).casefold()
                     for key in ("name", "card_number", "set_name", "language"))
    with db() as conn:
        rows = conn.execute("""
            SELECT id, card_name, card_number, set_name, language
            FROM cards WHERE chat_id = ? AND id <> ?
        """, (str(chat_id), int(card_id))).fetchall()
        for row in rows:
            existing = tuple(re.sub(r"\s+", " ", str(value or "").strip()).casefold() for value in row[1:])
            if existing == identity:
                raise ValueError("Questa modifica duplicherebbe un'altra carta nel Pokédex.")
        keywords = " ".join(
            str(updated.get(key) or "").strip()
            for key in ("name", "set_name", "card_number", "language")
            if str(updated.get(key) or "").strip()
        )
        column = {"name": "card_name", "number": "card_number", "set": "set_name", "language": "language"}[field]
        stored = (value or None) if field == "language" else value
        conn.execute(
            f"UPDATE cards SET {column} = ?, keywords = ? WHERE id = ? AND chat_id = ?",
            (stored, keywords, int(card_id), str(chat_id)),
        )
    wake_scanner("dati carta modificati dall'admin")
    return value


def db_should_alert_listing(chat_id, card_id, item_id, price):
    with db() as conn:
        row = conn.execute("""
            SELECT last_alerted_price FROM alerted_listings
            WHERE chat_id = ? AND card_id = ? AND item_id = ?
        """, (str(chat_id), int(card_id), str(item_id))).fetchone()
    if row is None:
        return True
    return float(price) < float(row[0]) - 0.005


def db_claim_listing_alert(chat_id, card_id, item_id, price):
    """Claim atomically an alert slot so overlapping scanner workers cannot duplicate it."""
    token = secrets.token_hex(8)
    now = time.time()
    price = float(price)
    with db() as conn:
        conn.execute("BEGIN IMMEDIATE")
        row = conn.execute("""
            SELECT last_alerted_price, claim_at, delivered
            FROM alerted_listings
            WHERE chat_id = ? AND card_id = ? AND item_id = ?
        """, (str(chat_id), int(card_id), str(item_id))).fetchone()

        if row is None:
            conn.execute("""
                INSERT INTO alerted_listings
                    (chat_id, card_id, item_id, last_alerted_price, alerted_at, claim_token, claim_at, delivered)
                VALUES (?, ?, ?, ?, ?, ?, ?, 0)
            """, (str(chat_id), int(card_id), str(item_id), price, datetime.datetime.now(datetime.timezone.utc).isoformat(), token, now))
            return token

        last_price, claim_at, delivered = float(row[0]), row[1], int(row[2] or 1)

        # Another worker is already trying this listing: do not duplicate the alert.
        if not delivered and claim_at and now - float(claim_at) < ALERT_CLAIM_STALE_SECONDS:
            return None

        # Delivered listings alert only for a meaningful new lower price.
        # Stale undelivered claims may be retried at the same/lower price.
        if delivered:
            if price >= last_price - 0.005:
                return None
        elif price > last_price + 0.005:
            return None

        conn.execute("""
            UPDATE alerted_listings
            SET last_alerted_price = ?, alerted_at = ?, claim_token = ?, claim_at = ?, delivered = 0
            WHERE chat_id = ? AND card_id = ? AND item_id = ?
        """, (price, datetime.datetime.now(datetime.timezone.utc).isoformat(), token, now, str(chat_id), int(card_id), str(item_id)))
    return token


def db_finalize_listing_alert(chat_id, card_id, item_id, price, claim_token):
    if not re.fullmatch(r"[0-9a-f]{16}", claim_token or ""):
        return False
    with db() as conn:
        changed = conn.execute("""
            UPDATE alerted_listings
            SET delivered = 1, claim_token = NULL, claim_at = NULL,
                last_alerted_price = ?, alerted_at = ?
            WHERE chat_id = ? AND card_id = ? AND item_id = ? AND claim_token = ? AND delivered = 0
        """, (float(price), datetime.datetime.now(datetime.timezone.utc).isoformat(), str(chat_id), int(card_id), str(item_id), claim_token)).rowcount
    return changed == 1


def db_mark_listing_alerted(chat_id, card_id, item_id, price):
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with db() as conn:
        conn.execute("""
            INSERT INTO alerted_listings
                (chat_id, card_id, item_id, last_alerted_price, alerted_at, claim_token, claim_at, delivered)
            VALUES (?, ?, ?, ?, ?, NULL, NULL, 1)
            ON CONFLICT(chat_id, card_id, item_id) DO UPDATE SET
                last_alerted_price = excluded.last_alerted_price,
                alerted_at = excluded.alerted_at,
                claim_token = NULL, claim_at = NULL, delivered = 1
        """, (str(chat_id), int(card_id), str(item_id), float(price), now))


def db_prune_alerted(days=60):
    cutoff = (
        datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=days)
    ).isoformat()
    with db() as conn:
        conn.execute("DELETE FROM alerted_listings WHERE alerted_at < ?", (cutoff,))


def db_expire_overdue():
    now = datetime.datetime.now(datetime.timezone.utc)
    now_raw = now.isoformat()
    with db() as conn:
        chats = [r[0] for r in conn.execute("""
            SELECT DISTINCT chat_id FROM subscription_packages
            WHERE status = 'ACTIVE' AND subscription_end <= ?
        """, (now_raw,)).fetchall()]
        for chat_id in chats:
            _move_cards_to_scheduled_renewal_on_conn(conn, str(chat_id), now_raw)
        expired = conn.execute("""
            UPDATE subscription_packages SET status = 'EXPIRED'
            WHERE status = 'ACTIVE' AND subscription_end <= ?
        """, (now_raw,)).rowcount
        for chat_id in chats:
            _refresh_subscription_summary_on_conn(conn, chat_id, now)
    if expired:
        wake_scanner("packages expired")
    return expired


def db_users_to_remind():
    now = datetime.datetime.now(datetime.timezone.utc)
    limit = now + datetime.timedelta(days=REMINDER_DAYS)
    with db() as conn:
        rows = conn.execute("""
            SELECT chat_id, subscription_end
            FROM subscription_packages
            WHERE status = 'ACTIVE' AND subscription_end > ? AND subscription_end <= ?
              AND subscription_start <= ?
              AND (reminder_3d_for IS NULL OR reminder_3d_for <> subscription_end)
            GROUP BY chat_id, subscription_end
            ORDER BY subscription_end
        """, (now.isoformat(), limit.isoformat(), now.isoformat())).fetchall()
    return [
        {"chat_id": chat_id, "end_raw": end_raw, "end": _parse_iso(end_raw)}
        for chat_id, end_raw in rows
    ]


def db_mark_reminded(chat_id, end_raw):
    with db() as conn:
        conn.execute("""
            UPDATE subscription_packages SET reminder_3d_for = ?
            WHERE chat_id = ? AND subscription_end = ? AND status = 'ACTIVE'
        """, (end_raw, str(chat_id), end_raw))


def db_users_to_notify_expired():
    now = datetime.datetime.now(datetime.timezone.utc)
    since = now - datetime.timedelta(days=REMINDER_DAYS)
    with db() as conn:
        rows = conn.execute("""
            SELECT chat_id, subscription_end, SUM(card_count)
            FROM subscription_packages
            WHERE status = 'EXPIRED' AND subscription_end >= ? AND subscription_end <= ?
              AND (expired_notice_for IS NULL OR expired_notice_for <> subscription_end)
            GROUP BY chat_id, subscription_end
            ORDER BY subscription_end
        """, (since.isoformat(), now.isoformat())).fetchall()
    return [
        {"chat_id": chat_id, "end_raw": end_raw, "card_count": int(card_count), "end": _parse_iso(end_raw)}
        for chat_id, end_raw, card_count in rows
    ]


def db_mark_expired_notified(chat_id, end_raw):
    with db() as conn:
        conn.execute("""
            UPDATE subscription_packages SET expired_notice_for = ?
            WHERE chat_id = ? AND subscription_end = ? AND status = 'EXPIRED'
        """, (end_raw, str(chat_id), end_raw))


# ============================================================
# HELPER SICUREZZA
# ============================================================
FORBIDDEN_UNICODE_CATEGORIES = {"Cc", "Cf", "Cs", "Co"}


def normalize_user_text(value: str, max_len: int, allow_empty: bool = False):
    """Normalizza input testuale e rifiuta controlli/invisibili/surrogati.

    Non esegue né interpreta mai il contenuto come codice: il testo viene solo
    validato prima di entrare nella logica applicativa o nel DB.
    """
    if not isinstance(value, str):
        return None
    if len(value) > MAX_TELEGRAM_TEXT_LEN or len(value) > max_len:
        return None
    value = unicodedata.normalize("NFKC", value)
    chars = []
    for ch in value:
        cat = unicodedata.category(ch)
        if cat in FORBIDDEN_UNICODE_CATEGORIES:
            return None
        if ch in "\r\n\t":
            chars.append(" ")
        else:
            chars.append(ch)
    value = " ".join("".join(chars).split())
    if len(value) > max_len:
        return None
    if not allow_empty and not value:
        return None
    return value


def safe_telegram_username(value: str) -> str:
    """Valida il solo username Telegram mostrato all'ADMIN."""
    value = str(value or "").strip()
    if not value:
        return "-"
    if len(value) > MAX_USERNAME_LEN or not re.fullmatch(r"[A-Za-z0-9_]{5,32}", value):
        return "-"
    return value


def safe_first_name(value: str) -> str:
    """Nome visualizzato in Telegram: normalizzato e limitato."""
    value = normalize_user_text(str(value or ""), MAX_FIRST_NAME_LEN)
    return value or "Collezionista"


def is_safe_callback_data(value: str) -> bool:
    """Whitelist per callback_data generati esclusivamente dal bot."""
    if not isinstance(value, str) or len(value.encode("utf-8")) > 64:
        return False
    return re.fullmatch(r"[A-Za-z0-9:_-]+", value) is not None


async def security_gate(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Filtro globale: valida solo input realmente inviati dall'utente.

    Un callback_query contiene anche il messaggio originale del bot in
    ``effective_message``. Quel testo NON e' input dell'utente e non deve
    essere sottoposto al filtro testo (altrimenti pulsanti come Guida, ADMIN
    o Salta possono essere bloccati). I callback vengono validati separatamente
    tramite whitelist.
    """
    if not update:
        return

    # Messaggi realmente inviati/modificati dall'utente. Non usare
    # effective_message qui: nei callback Telegram restituisce il messaggio
    # che contiene il pulsante, quindi testo generato dal bot.
    message = getattr(update, "message", None) or getattr(update, "edited_message", None)
    if message is not None and getattr(message, "text", None) is not None:
        raw = message.text
        if not isinstance(raw, str) or len(raw) > MAX_TELEGRAM_TEXT_LEN:
            log.warning(
                "Input testo rifiutato: lunghezza non valida chat=%s",
                getattr(getattr(update, "effective_chat", None), "id", None),
            )
            try:
                await message.reply_text(
                    "❌ Messaggio non valido o troppo lungo. Inserisci solo i dati richiesti."
                )
            except Exception:
                pass
            raise ApplicationHandlerStop

        if any(unicodedata.category(ch) in FORBIDDEN_UNICODE_CATEGORIES for ch in raw):
            log.warning(
                "Input testo rifiutato: caratteri di controllo/invisibili chat=%s",
                getattr(getattr(update, "effective_chat", None), "id", None),
            )
            try:
                await message.reply_text(
                    "❌ Sono presenti caratteri non consentiti. Riprova usando solo testo normale."
                )
            except Exception:
                pass
            raise ApplicationHandlerStop

    query = getattr(update, "callback_query", None)
    if query is not None and not is_safe_callback_data(query.data or ""):
        log.warning("Callback sospetta rifiutata: user=%s", getattr(query.from_user, "id", None))
        try:
            await query.answer("Operazione non valida.", show_alert=True)
        except Exception:
            pass
        raise ApplicationHandlerStop


def is_admin(update: Update) -> bool:
    """Admin = ID utente uguale ad ADMIN_CHAT_ID, in chat privata."""
    if not ADMIN_CHAT_ID:
        return False
    user = update.effective_user
    chat = update.effective_chat
    return bool(
        user and chat
        and chat.type == "private"
        and str(user.id) == ADMIN_CHAT_ID
    )


def clean_text(value: str) -> str:
    """Compatibilità interna: normalizza testo senza accettare controlli."""
    return normalize_user_text(value, MAX_TELEGRAM_TEXT_LEN, allow_empty=True) or ""


def is_ebay_url(url: str) -> bool:
    try:
        p = urlparse(url)
    except ValueError:
        return False
    host = (p.hostname or "").lower().rstrip(".")
    return p.scheme == "https" and host in {"ebay.it", "www.ebay.it"}


def is_ebay_image_url(url: str) -> bool:
    try:
        p = urlparse(url)
    except ValueError:
        return False
    host = (p.hostname or "").lower()
    return p.scheme == "https" and re.fullmatch(r"(?:[a-z0-9-]+\.)*ebayimg\.com", host) is not None


async def rate_limit(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    if chat is None:
        return
    now = time.monotonic()
    last = _LAST_SEEN.get(chat.id, 0.0)
    if now - last < MIN_SECONDS_BETWEEN_UPDATES:
        raise ApplicationHandlerStop
    _LAST_SEEN[chat.id] = now
    if len(_LAST_SEEN) > 10000:
        cutoff = now - 60
        for k in [k for k, v in _LAST_SEEN.items() if v < cutoff]:
            _LAST_SEEN.pop(k, None)


# ============================================================
# TASTIERE
# ============================================================
def header(emoji: str, title: str) -> str:
    """Intestazione standard di ogni schermata."""
    return f"{emoji} <b>{title}</b>\n{DIV}\n\n"


def tip(text: str) -> str:
    """Riquadro «consiglio» (citazione evidenziata di Telegram)."""
    return f"<blockquote>💡 {text}</blockquote>"


def fmt_days(n: int) -> str:
    return "1 giorno" if n == 1 else f"{n} giorni"


def support_row(label="💬 Contatta il supporto"):
    """Riga con il pulsante verso il supporto, se il contatto è configurato."""
    return [InlineKeyboardButton(label, url=SUPPORT_URL)] if SUPPORT_URL else None




def fmt_eur(value) -> str:
    amount = float(value)
    return f"€{amount:,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")


def price_for_selection(card_count: int, months: int) -> float:
    return custom_price_cents(card_count, months) / 100


def paypal_payment_url(amount_cents: int):
    """Costruisce un PayPal.Me con l'importo dell'abbonamento in EUR, se configurato."""
    if not PAYPAL_LINK:
        return None
    try:
        p = urlparse(PAYPAL_LINK)
    except ValueError:
        return None
    host = (p.hostname or "").lower().rstrip(".")
    if p.scheme != "https" or host not in {"paypal.me", "www.paypal.me"}:
        return PAYPAL_LINK if not p.username and not p.password else None
    parts = [x for x in p.path.split("/") if x]
    if len(parts) != 1:
        return None
    amount = amount_cents / 100
    return f"https://{host}/{parts[0]}/{amount:.2f}EUR"


def subscription_keyboard():
    rows = [[InlineKeyboardButton("💳 Configura monitoraggio", callback_data="sub:start")]]
    if BANK_TRANSFER_AVAILABLE:
        rows.append([InlineKeyboardButton("🏦 Come pagare con bonifico", callback_data="bank:info")])
    rows.append([
        InlineKeyboardButton("💳 Come si paga?", callback_data="help:pay"),
        InlineKeyboardButton("📖 Guida", callback_data="help:home"),
    ])
    return InlineKeyboardMarkup(rows)


def subscription_cards_keyboard():
    counts = [1, 3, 5, 10, 20, 50]
    rows = []
    for i in range(0, len(counts), 3):
        rows.append([
            InlineKeyboardButton(f"{n} carte", callback_data=f"sub:cards:{n}")
            for n in counts[i:i + 3]
        ])
    rows.append([InlineKeyboardButton("✏️ Numero personalizzato", callback_data="sub:cards:custom")])
    rows.append([InlineKeyboardButton("⬅️ Indietro", callback_data="sub:back")])
    return InlineKeyboardMarkup(rows)


def subscription_months_keyboard():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("1 mese", callback_data="sub:months:1"),
         InlineKeyboardButton("3 mesi", callback_data="sub:months:3")],
        [InlineKeyboardButton("6 mesi", callback_data="sub:months:6"),
         InlineKeyboardButton("12 mesi", callback_data="sub:months:12")],
        [InlineKeyboardButton("✏️ Altra durata", callback_data="sub:months:custom")],
        [InlineKeyboardButton("⬅️ Numero carte", callback_data="sub:edit")],
    ])


def subscription_summary_keyboard(card_count: int, months: int):
    amount_cents = custom_price_cents(card_count, months)
    rows = []
    pp = paypal_payment_url(amount_cents)
    if pp:
        rows.append([InlineKeyboardButton(f"💳 Paga {fmt_eur(amount_cents/100)} con PayPal", url=pp)])
    elif PAYPAL_LINK:
        rows.append([InlineKeyboardButton("💳 Apri PayPal", url=PAYPAL_LINK)])
    if BANK_TRANSFER_AVAILABLE:
        rows.append([InlineKeyboardButton("🏦 Paga con bonifico", callback_data=f"sub:bank:{card_count}:{months}")])
    rows.append([InlineKeyboardButton("✅ Ho pagato", callback_data=f"sub:paid:{card_count}:{months}")])
    rows.append([InlineKeyboardButton("✏️ Modifica", callback_data="sub:edit")])
    rows.append([
        InlineKeyboardButton("💳 Come si paga?", callback_data="help:pay"),
        InlineKeyboardButton("📖 Guida", callback_data="help:home"),
    ])
    return InlineKeyboardMarkup(rows)


def bank_transfer_text(card_count=None, months=None) -> str:
    if not BANK_TRANSFER_AVAILABLE:
        return header("🏦", "BONIFICO ISTANTANEO") + "Il pagamento tramite bonifico non è ancora configurato."
    text = header("🏦", "BONIFICO ISTANTANEO")
    if card_count and months:
        amount = price_for_selection(card_count, months)
        text += (
            f"🎴 <b>{card_count}</b> carte monitorate\n"
            f"⏳ <b>{months}</b> {('mese' if months == 1 else 'mesi')}\n"
            f"💰 Totale: <b>{fmt_eur(amount)}</b>\n\n"
        )
    text += (
        f"👤 <b>Intestatario</b>\n<code>{esc(BANK_ACCOUNT_HOLDER)}</code>\n\n"
        f"🏦 <b>IBAN</b>\n<code>{esc(BANK_IBAN)}</code>\n\n"
        f"📝 <b>Causale</b>\n<code>{esc(BANK_CAUSALE)}</code>\n\n"
        "Dopo il bonifico premi <b>✅ Ho pagato</b>. L'ADMIN verificherà l'accredito prima dell'attivazione."
    )
    return text


def bank_transfer_keyboard(card_count=None, months=None):
    rows = []
    if card_count and months:
        rows.append([InlineKeyboardButton("✅ Ho pagato", callback_data=f"sub:paid:{card_count}:{months}")])
        rows.append([InlineKeyboardButton("⬅️ Torna al riepilogo", callback_data=f"sub:summary:{card_count}:{months}")])
    else:
        rows.append([InlineKeyboardButton("⬅️ Abbonamento", callback_data="sub:start")])
    return InlineKeyboardMarkup(rows)


def main_menu_keyboard():
    return ReplyKeyboardRemove()


def pricing_block() -> str:
    return (
        "<b>Monitoraggio a pacchetti</b>\n"
        f"{PRICE_PER_CARD_MONTH_EUR} \u20ac al mese per ogni carta monitorata\n\n"
        "Scegli quante carte aggiungere e per quanti mesi: ogni pacchetto ha la propria scadenza.\n"
        "Gli acquisti successivi aggiungono slot senza prolungare quelli gia attivi."
    )


def subscription_card(user, used: int, limit: int | None, chat_id=None) -> str:
    if limit is None:
        capacity = f"Carte monitorate: <b>{used}</b> - illimitate"
    else:
        monitored = min(used, int(limit))
        capacity = (
            f"Carte monitorate: <b>{monitored}/{limit}</b>\n"
            f"{_slot_bar(monitored, limit)}"
        )
    packages = user.get("subscription_packages") or []
    if packages:
        now = datetime.datetime.now(datetime.timezone.utc)
        package_lines = []
        for p in packages[:8]:
            start = _parse_iso(p["subscription_start"])
            starts = f"dal {fmt_date(p['subscription_start'])}, " if start and start > now else ""
            plural = "carta" if p["card_count"] == 1 else "carte"
            package_lines.append(
                f"- {starts}{p['card_count']} {plural} fino al <b>{fmt_date(p['subscription_end'])}</b>"
            )
        if len(packages) > 8:
            package_lines.append(f"- altri {len(packages) - 8} pacchetti attivi")
        expiry = "<b>Pacchetti e scadenze</b>\n" + "\n".join(package_lines)
    else:
        expiry = "Nessun pacchetto attivo"
    return (
        "Monitoraggio eBay: <b>attivo</b>\n"
        + expiry + "\n\n"
        + capacity
        + (f"\n\n{monitor_line(chat_id, min(used, limit) if limit is not None else used)}" if chat_id is not None else "")
    )


def pokedex_button():
    return InlineKeyboardMarkup([[InlineKeyboardButton("📕 Apri il Pokédex", callback_data="go:cards")]])


def _new_package_card_bounds(chat_id):
    user = db_get_user(chat_id)
    active_slots = int(user.get("card_limit") or 0) if db_subscription_is_active(user) else 0
    stored_cards = len(db_get_user_cards(chat_id))
    with db() as conn:
        reserved_peak = _max_reserved_subscription_capacity_on_conn(conn, chat_id)
    minimum = max(1, stored_cards - active_slots)
    maximum = max(0, MAX_USER_CARDS - reserved_peak)
    return minimum, maximum, active_slots


def subscription_prompt_text(card_count=None):
    extra = ""
    if card_count:
        extra = f"\nHai scelto <b>{card_count} carte aggiuntive</b>. Ora scegli per quanti mesi.\n"
    return (
        header("💳", "CONFIGURA IL MONITORAGGIO")
        + pricing_block() + "\n\n"
        + ("Quante carte vuoi aggiungere al monitoraggio?\n" if not card_count else extra)
    )


def _package_purchase_block_text():
    return (
        header("🧩", "USA GLI SLOT DISPONIBILI")
        + "Hai ancora slot liberi nel pacchetto attivo. Aggiungi prima carte fino a occupare tutti gli slot; "
          "potrai acquistare un altro pacchetto quando saranno pieni."
    )


async def subscription_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    db_ensure_user(chat_id)
    if is_admin_chat(chat_id):
        await update.effective_message.reply_text(
            header("\U0001F451", "ACCOUNT ADMIN") + "Il tuo account e illimitato: non devi acquistare un abbonamento.",
            parse_mode="HTML",
        )
        return ConversationHandler.END
    user = db_get_user(chat_id)
    active = db_subscription_is_active(user)
    current_cards = len(db_get_monitored_user_cards(chat_id))
    context.user_data.pop("subscription_cards", None)
    if active and not _can_buy_another_package(chat_id):
        await update.effective_message.reply_text(_package_purchase_block_text(), parse_mode="HTML")
        return ConversationHandler.END
    intro = subscription_prompt_text()
    if active:
        intro = (
            header("\U0001F4B3", "PACCHETTI DI MONITORAGGIO")
            + subscription_card(user, current_cards, user["card_limit"], chat_id)
            + "\n\nQuando avrai occupato tutti gli slot, potrai acquistare un nuovo pacchetto con la propria scadenza."
        )
    await update.effective_message.reply_text(
        intro, parse_mode="HTML", reply_markup=subscription_cards_keyboard()
    )
    return SUB_CARDS


async def subscription_start_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    if query.message is None or query.message.chat.type != "private":
        return ConversationHandler.END
    chat_id = str(query.from_user.id)
    db_ensure_user(chat_id)
    if is_admin_chat(chat_id):
        await query.message.reply_text(
            header("\U0001F451", "ACCOUNT ADMIN") + "Il tuo account e illimitato.", parse_mode="HTML"
        )
        return ConversationHandler.END
    user = db_get_user(chat_id)
    active = db_subscription_is_active(user)
    current_cards = len(db_get_monitored_user_cards(chat_id))
    context.user_data.pop("subscription_cards", None)
    if active and not _can_buy_another_package(chat_id):
        await query.message.reply_text(_package_purchase_block_text(), parse_mode="HTML")
        return ConversationHandler.END
    intro = subscription_prompt_text()
    if active:
        intro = (
            header("\U0001F4B3", "PACCHETTI DI MONITORAGGIO")
            + subscription_card(user, current_cards, user["card_limit"], chat_id)
            + "\n\nQuando avrai occupato tutti gli slot, potrai acquistare un nuovo pacchetto con la propria scadenza."
        )
    await query.message.reply_text(intro, parse_mode="HTML", reply_markup=subscription_cards_keyboard())
    return SUB_CARDS


async def subscription_card_choice(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query.message is None or query.message.chat.type != "private":
        await query.answer()
        return ConversationHandler.END
    m = re.fullmatch(r"sub:cards:(custom|\d{1,3})", query.data or "")
    if not m:
        await query.answer()
        return SUB_CARDS
    if m.group(1) == "custom":
        await query.answer()
        await query.message.reply_text(
            header("🎴", "NUMERO DI CARTE")
            + f"Scrivi un numero da <b>1 a {MAX_USER_CARDS}</b>.\n"
              "Esempio: <code>7</code>", parse_mode="HTML"
        )
        return SUB_CARDS
    card_count = int(m.group(1))
    if not 1 <= card_count <= MAX_USER_CARDS:
        await query.answer("Numero di carte non valido.", show_alert=True)
        return SUB_CARDS
    if not _can_buy_another_package(str(query.from_user.id)):
        await query.answer("Prima usa tutti gli slot del pacchetto attivo.", show_alert=True)
        return ConversationHandler.END
    minimum, maximum, active_slots = _new_package_card_bounds(str(query.from_user.id))
    if card_count < minimum or card_count > maximum:
        await query.answer(
            f"Questo pacchetto deve aggiungere da {minimum} a {maximum} carte.", show_alert=True
        )
        return SUB_CARDS
    context.user_data["subscription_cards"] = card_count
    await query.answer()
    await query.message.reply_text(
        subscription_prompt_text(card_count), parse_mode="HTML", reply_markup=subscription_months_keyboard()
    )
    return SUB_MONTHS


async def subscription_card_text_step(update: Update, context: ContextTypes.DEFAULT_TYPE):
    card_count = parse_count(update.effective_message.text or "", MAX_USER_CARDS)
    if card_count is None:
        await update.effective_message.reply_text(
            f"❌ Scrivi un numero da 1 a {MAX_USER_CARDS}.", parse_mode="HTML"
        )
        return SUB_CARDS
    if not _can_buy_another_package(str(update.effective_chat.id)):
        await update.effective_message.reply_text(_package_purchase_block_text(), parse_mode="HTML")
        return ConversationHandler.END
    minimum, maximum, active_slots = _new_package_card_bounds(str(update.effective_chat.id))
    if card_count < minimum or card_count > maximum:
        await update.effective_message.reply_text(
            f"Scegli un pacchetto da {minimum} a {maximum} carte aggiuntive.", parse_mode="HTML"
        )
        return SUB_CARDS
    context.user_data["subscription_cards"] = card_count
    await update.effective_message.reply_text(
        subscription_prompt_text(card_count), parse_mode="HTML", reply_markup=subscription_months_keyboard()
    )
    return SUB_MONTHS


async def subscription_show_summary(target_message, card_count: int, months: int):
    amount = price_for_selection(card_count, months)
    text = (
        header("🧾", "RIEPILOGO")
        + f"🎴 Carte monitorate: <b>{card_count}</b>\n"
          f"⏳ Durata: <b>{months} {'mese' if months == 1 else 'mesi'}</b>\n"
          f"💶 Prezzo: <b>{PRICE_PER_CARD_MONTH_EUR} € / carta / mese</b>\n\n"
          f"💰 <b>TOTALE: {fmt_eur(amount)}</b>\n\n"
        + ("💳 <b>PayPal</b>: usa il pulsante qui sotto per aprire direttamente il pagamento.\n\n" if PAYPAL_LINK else "")
        + tip("Dopo il pagamento premi <b>✅ Ho pagato</b>. L'attivazione avviene solo dopo la verifica manuale dell'ADMIN.")
    )
    await target_message.reply_text(text, parse_mode="HTML", reply_markup=subscription_summary_keyboard(card_count, months))



async def create_payment_request(update: Update, context: ContextTypes.DEFAULT_TYPE, card_count: int, months: int):
    query = update.callback_query
    user_id = str(query.from_user.id)
    chat_id = str(query.message.chat.id if query.message else user_id)
    if chat_id != user_id or not (1 <= card_count <= MAX_USER_CARDS and 1 <= months <= MAX_SUBSCRIPTION_MONTHS):
        await query.answer("Selezione non valida.", show_alert=True)
        return SUB_MONTHS
    if not _can_buy_another_package(user_id):
        await query.answer("Prima usa tutti gli slot del pacchetto attivo.", show_alert=True)
        return ConversationHandler.END
    if not ADMIN_CHAT_ID:
        await query.answer("📵 Verifica pagamenti momentaneamente non disponibile.", show_alert=True)
        return SUB_MONTHS

    db_ensure_user(user_id)
    minimum, maximum, active_slots = _new_package_card_bounds(user_id)
    if card_count < minimum or card_count > maximum:
        await query.answer(
            f"Questo pacchetto deve aggiungere da {minimum} a {maximum} carte.", show_alert=True
        )
        return SUB_MONTHS
    active = active_slots > 0

    pending = db_get_pending_payment(user_id)
    now = time.time()
    if pending and now - pending["created_at"] < PAYMENT_REQUEST_COOLDOWN:
        await query.answer("⏳ Hai già una richiesta in verifica. Attendi l'esito dell'ADMIN.", show_alert=True)
        return ConversationHandler.END

    username = safe_telegram_username(query.from_user.username)
    renewal = active
    amount_cents = custom_price_cents(card_count, months)
    token = db_save_pending_payment(user_id, card_count, months, username, renewal)
    if not token:
        await query.answer("⏳ Hai già una richiesta in verifica. Attendi l'esito dell'ADMIN.", show_alert=True)
        return ConversationHandler.END
    try:
        await context.bot.send_message(
            chat_id=int(ADMIN_CHAT_ID),
            text=(
                "💳 RICHIESTA VERIFICA PAGAMENTO\n"
                "━━━━━━━━━━━━━━━━━━\n\n"
                f"🎴 Carte: <b>{card_count}</b>\n"
                f"⏳ Durata: <b>{months} {'mese' if months == 1 else 'mesi'}</b>\n"
                f"💰 Totale: <b>{fmt_eur(amount_cents / 100)}</b>\n"
                f"🆔 chat_id: <code>{esc(user_id)}</code>\n"
                f"👤 username: @{esc(username)}\n"
                f"🔄 {'PACCHETTO AGGIUNTIVO' if renewal else 'NUOVA ATTIVAZIONE'}\n\n"
                "⚠️ Verifica il pagamento prima di approvare."
            ),
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("✅ Approva", callback_data=f"approve:{token}"),
                InlineKeyboardButton("❌ Rifiuta", callback_data=f"reject:{token}"),
            ]]),
        )
    except Exception as e:
        # La richiesta non deve restare bloccata se la notifica ADMIN fallisce.
        db_reject_payment_request(token)
        log.warning("Notifica pagamento ad ADMIN fallita: tipo=%s", type(e).__name__)
        await query.answer("⚠️ Non sono riuscito ad avvisare l'ADMIN. Riprova.", show_alert=True)
        return SUB_MONTHS

    context.user_data.pop("subscription_cards", None)
    await query.answer("✅ Richiesta inviata!")
    await query.message.reply_text(
        header("🔍", "PAGAMENTO IN VERIFICA")
        + "Ho avvisato l'ADMIN: sta verificando il pagamento.\n\n"
          f"🎴 Carte: <b>{card_count}</b>\n"
          f"⏳ Durata: <b>{months} {'mese' if months == 1 else 'mesi'}</b>\n"
          f"💰 Totale: <b>{fmt_eur(amount_cents / 100)}</b>\n\n"
        + tip("Non serve ripremere il pulsante. Riceverai una conferma quando il pagamento sarà verificato."),
        parse_mode="HTML",
    )
    log.info("Pagamento notificato all'ADMIN: chat=%s carte=%s mesi=%s", user_id, card_count, months)
    return ConversationHandler.END


async def subscription_month_choice(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query.message is None or query.message.chat.type != "private":
        await query.answer()
        return ConversationHandler.END
    data = query.data or ""
    if data == "sub:edit":
        await query.answer()
        await query.message.reply_text(subscription_prompt_text(), parse_mode="HTML", reply_markup=subscription_cards_keyboard())
        return SUB_CARDS
    if not _can_buy_another_package(str(query.from_user.id)):
        await query.answer("Prima usa tutti gli slot del pacchetto attivo.", show_alert=True)
        return ConversationHandler.END
    m = re.fullmatch(r"sub:months:(custom|\d{1,2})", data)
    if not m:
        m2 = re.fullmatch(r"sub:(summary|bank|paid):(\d{1,3}):(\d{1,2})", data)
        if m2:
            action, cards_raw, months_raw = m2.groups()
            card_count, months = int(cards_raw), int(months_raw)
            if not (1 <= card_count <= MAX_USER_CARDS and 1 <= months <= MAX_SUBSCRIPTION_MONTHS):
                await query.answer("Selezione non valida.", show_alert=True)
                return SUB_MONTHS
            if action == "summary":
                await query.answer()
                await query.message.reply_text(subscription_prompt_text(card_count), parse_mode="HTML", reply_markup=subscription_months_keyboard())
                return SUB_MONTHS
            if action == "bank":
                if not BANK_TRANSFER_AVAILABLE:
                    await query.answer("Bonifico non disponibile.", show_alert=True)
                    return SUB_MONTHS
                await query.answer()
                await query.message.reply_text(bank_transfer_text(card_count, months), parse_mode="HTML", reply_markup=bank_transfer_keyboard(card_count, months))
                return SUB_MONTHS
            if action == "paid":
                return await create_payment_request(update, context, card_count, months)
        await query.answer()
        return SUB_MONTHS
    if m.group(1) == "custom":
        await query.answer()
        await query.message.reply_text(
            header("⏳", "DURATA")
            + f"Scrivi un numero da <b>1 a {MAX_SUBSCRIPTION_MONTHS}</b>.\n"
              "Esempio: <code>4</code>", parse_mode="HTML"
        )
        return SUB_MONTHS
    months = int(m.group(1))
    card_count = int(context.user_data.get("subscription_cards") or 0)
    if not 1 <= months <= MAX_SUBSCRIPTION_MONTHS or not 1 <= card_count <= MAX_USER_CARDS:
        await query.answer("Selezione non valida.", show_alert=True)
        return SUB_CARDS
    await query.answer()
    await subscription_show_summary(query.message, card_count, months)
    return SUB_MONTHS


async def subscription_month_text_step(update: Update, context: ContextTypes.DEFAULT_TYPE):
    months = parse_months(update.effective_message.text or "")
    if months is None:
        await update.effective_message.reply_text(f"❌ Scrivi un numero da 1 a {MAX_SUBSCRIPTION_MONTHS}.")
        return SUB_MONTHS
    card_count = int(context.user_data.get("subscription_cards") or 0)
    if not (1 <= months <= MAX_SUBSCRIPTION_MONTHS and 1 <= card_count <= MAX_USER_CARDS):
        await update.effective_message.reply_text("⌛ Selezione non valida. Riparti da /abbonamento.")
        return ConversationHandler.END
    await subscription_show_summary(update.effective_message, card_count, months)
    return SUB_MONTHS


def help_back_subscription_keyboard():
    return InlineKeyboardMarkup([[InlineKeyboardButton("💳 Configura monitoraggio", callback_data="sub:start")],
                                 [InlineKeyboardButton("⬅️ Indice", callback_data="help:home")]])

# ============================================================
# GUIDA INTERATTIVA
# ============================================================
def help_index_keyboard():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📡 Come funziona", callback_data="help:how"),
         InlineKeyboardButton("🎴 Prezzi", callback_data="help:plans")],
        [InlineKeyboardButton("💳 Pagamento", callback_data="help:pay"),
         InlineKeyboardButton("🛠️ Problemi?", callback_data="help:faq")],
    ])


def help_back_keyboard(show_account=False):
    row = [InlineKeyboardButton("⬅️ Indice", callback_data="help:home")]
    if show_account:
        row.append(InlineKeyboardButton("🎒 Account", callback_data="go:sub"))
    return InlineKeyboardMarkup([row])


def help_page(topic: str):
    if topic == "home":
        return (
            header("📖", "GUIDA POKEBOT")
            + "Benvenuto, Collezionista.\n"
              "Qui trovi tutto quello che serve per iniziare.\n\n"
              "👇 <b>Scegli un argomento:</b>",
            help_index_keyboard(),
        )
    if topic == "how":
        return (
            header("📡", "COME FUNZIONA")
            + "<b>1️⃣ Scegli quante carte vuoi monitorare</b>\n"
              f"Paghi {PRICE_PER_CARD_MONTH_EUR} € al mese per ogni carta.\n\n"
              "<b>2️⃣ Scegli la durata dell'abbonamento</b>\n"
              "Indica per quanti mesi vuoi mantenere attivo il servizio: il totale viene calcolato automaticamente.\n\n"
              "<b>3️⃣ Inserisci le carte che vuoi cercare</b>\n"
              "Ti chiediamo nome della carta, numero e set. La lingua è facoltativa e puoi indicarla con un semplice acronimo come ITA, ENG o JAP. Infine imposti il tuo budget massimo.\n\n"
              "<b>4️⃣ Lascia fare a POKEBOT</b>\n"
              "Il monitoraggio eBay viene effettuato serenamente al posto tuo, <b>24 ore su 24, 7 giorni su 7</b>.\n\n"
              "<b>5️⃣ Ricevi un avviso quando c'è un'opportunità</b>\n"
              "Quando viene individuata un'inserzione che rientra nel tuo budget, ricevi un avviso con le informazioni utili per valutarla e il link per aprirla su eBay.\n\n"
              "<b>🚫 Sicurezza della ricerca</b>\n"
              "Le inserzioni che contengono le parole <code>fake</code> o <code>proxy</code> vengono escluse.",
            help_back_keyboard(),
        )
    if topic == "plans":
        return (
            header("🎴", "PREZZO E ABBONAMENTO")
            + f"<b>{PRICE_PER_CARD_MONTH_EUR} € / carta / mese</b>\n\n"
              "Non ci sono piani separati: scegli liberamente il numero di carte e la durata dell'abbonamento.\n\n"
              "Esempi:\n"
              "▫️ 1 carta × 1 mese = 5 €\n"
              "▫️ 3 carte × 3 mesi = 45 €\n"
              "▫️ 10 carte × 6 mesi = 300 €\n\n"
            + tip("Le carte restano nel tuo Pokédex anche quando l'abbonamento scade; il Monitoraggio si ferma finché non riattivi il servizio."),
            help_back_subscription_keyboard(),
        )
    if topic == "pay":
        bank_line = (
            "🏦 <b>Bonifico istantaneo</b>\nDisponibile come alternativa a PayPal.\n\n"
            if BANK_TRANSFER_AVAILABLE else
            "🏦 <b>Bonifico istantaneo</b>\nMetodo non ancora configurato.\n\n"
        )
        return (
            header("💳", "COME SI PAGA")
            + "💳 <b>PayPal</b>\n"
              "Scegli il numero di carte e i mesi: il bot calcola il totale e prepara il pagamento.\n\n"
            + bank_line
            + "✅ <b>Dopo il pagamento</b>\n"
              "Premi <b>Ho pagato</b>. L'ADMIN verifica manualmente il pagamento e solo dopo attiva il servizio.\n\n"
            + tip("Nessun pagamento viene dato per verificato automaticamente."),
            InlineKeyboardMarkup((
                ([[InlineKeyboardButton("💳 Apri PayPal", url=PAYPAL_LINK)]] if PAYPAL_LINK else [])
                + ([[InlineKeyboardButton("🏦 Dati bonifico", callback_data="bank:info")]] if BANK_TRANSFER_AVAILABLE else [])
                + [[InlineKeyboardButton("💳 Configura monitoraggio", callback_data="sub:start")],
                   [InlineKeyboardButton("⬅️ Indice", callback_data="help:home")]]
            )),
        )
    if topic == "faq":
        support = [support_row("💬 Contatta il supporto")] if SUPPORT_URL else []
        return (
            header("🛠️", "PROBLEMI?")
            + "<b>📡 Non ricevo avvisi</b>\n"
              "Controlla che il Monitoraggio sia attivo e che il budget sia abbastanza alto rispetto alle inserzioni che stai cercando.\n\n"
              "<b>🎴 La ricerca trova risultati strani</b>\n"
              "Usa un nome carta preciso e aggiungi numero, set e lingua quando li conosci. Questi dati aiutano la ricerca, ma non sono obbligatori nel titolo dell'inserzione.\n\n"
              "<b>💰 Prezzi in GBP, USD o altre valute</b>\n"
              "Non vengono esclusi per la valuta: POKEBOT converte il prezzo dell'inserzione in euro per confrontarlo con il tuo budget.\n\n"
              "<b>🚚 Spedizione</b>\n"
              "La spedizione viene mostrata nell'avviso quando disponibile, ma <b>non viene conteggiata nel budget</b>.\n\n"
              "<b>🚫 Inserzioni fake o proxy</b>\n"
              "Le inserzioni in cui compaiono le parole <code>fake</code> o <code>proxy</code> vengono escluse.\n\n"
              "<b>🔔 Bot bloccato</b>\n"
              "Se blocchi il bot, Telegram non può consegnare gli avvisi."
              + ("\n\n<b>💬 Serve aiuto?</b>\nContatta direttamente il supporto." if SUPPORT_URL else ""),
            InlineKeyboardMarkup(
                support
                + [[InlineKeyboardButton("⬅️ Indice", callback_data="help:home")]]
            ),
        )
    return None


# ============================================================
# COMANDI UTENTE
# ============================================================
async def start_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    db_ensure_user(chat_id)
    user = db_get_user(chat_id)
    active = db_subscription_is_active(user)
    user = db_get_user(chat_id)
    first = esc(safe_first_name(update.effective_user.first_name if update.effective_user else "Collezionista"))
    title = "🔴⚪ <b>POKEBOT</b> ⚪🔴\n" + DIV + "\n\n"

    if is_admin_chat(chat_id):
        admin_cards = db_get_user_cards(chat_id)
        monitored_count = sum(1 for card in admin_cards if card["is_monitored"])
        await update.effective_message.reply_text(
            title + f"Bentornato, <b>{first}</b>! 👑\n\n"
            "🔐 <b>ACCOUNT ADMIN</b>\n"
            f"📡 Monitoraggio eBay: <b>{'attivo' if monitored_count else 'in pausa'}</b>\n"
            f"🎴 Carte in monitoraggio: <b>{monitored_count}</b> · nel Pokédex: <b>{len(admin_cards)}</b>\n"
            "⏳ Scadenza: <b>nessuna</b>\n\n"
            + tip("Tutto il bot è gestibile direttamente da Telegram."),
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("👑 Pannello ADMIN", callback_data="admin:home")]]),
        )
        return

    if active:
        limit = user["card_limit"]
        used = len(db_get_monitored_user_cards(chat_id))
        renew = (
            min((days_left(p["subscription_end"]) for p in user.get("subscription_packages", [])), default=999) <= RENEW_WINDOW_DAYS
            and _can_buy_another_package(chat_id)
        )
        footer = (
            tip("Un pacchetto scade presto: puoi aggiungerne un altro con carte e durata desiderate.")
            if renew else
            tip("Il monitoraggio è attivo. Usa /aggiungi per inserire una nuova carta.")
        )
        await update.effective_message.reply_text(
            title + f"Bentornato, <b>{first}</b>! 👋\n\n"
            + subscription_card(user, used, limit, chat_id)
            + "\n\n" + footer,
            parse_mode="HTML", reply_markup=subscription_keyboard() if renew else main_menu_keyboard()
        )
        return

    await update.effective_message.reply_text(
        title + f"Ciao <b>{first}</b>, Collezionista! 👋\n\n"
        "POKEBOT monitora eBay.it e ti avvisa quando trova un'inserzione Pokémon TCG entro il tuo budget.\n\n"
        + pricing_block() + "\n\n"
        + tip("Configura il numero di carte e la durata: il totale viene calcolato automaticamente."),
        parse_mode="HTML", reply_markup=subscription_keyboard(),
    )
    await update.effective_message.reply_text(
        "☰ Per tutti i comandi tocca il pulsante <b>Menu</b> accanto alla tastiera.",
        parse_mode="HTML", reply_markup=main_menu_keyboard(),
    )


async def menu_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text, keyboard = help_page("home")
    await update.effective_message.reply_text(text, parse_mode="HTML", reply_markup=keyboard)


async def status_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    db_ensure_user(chat_id)
    user = db_get_user(chat_id)
    active = db_subscription_is_active(user)
    user = db_get_user(chat_id)
    first = esc(safe_first_name(update.effective_user.first_name if update.effective_user else "Collezionista"))

    if is_admin_chat(chat_id):
        admin_cards = db_get_user_cards(chat_id)
        monitored_count = sum(1 for card in admin_cards if card["is_monitored"])
        await update.effective_message.reply_text(
            header("👑", "ACCOUNT ADMIN")
            + f"👤 Collezionista: <b>{first}</b>\n"
              f"🆔 ID: <code>{esc(chat_id)}</code>\n\n"
              f"📡 Monitoraggio eBay: <b>{'attivo' if monitored_count else 'in pausa'}</b>\n"
              f"🎴 Carte in monitoraggio: <b>{monitored_count}</b> · nel Pokédex: <b>{len(admin_cards)}</b>\n"
              "⏳ Scadenza: <b>nessuna</b>",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("👑 Pannello ADMIN", callback_data="admin:home")]]),
        )
        return

    identity = f"👤 Collezionista: <b>{first}</b>\n🆔 ID: <code>{esc(chat_id)}</code>\n"
    if not active:
        await update.effective_message.reply_text(
            header("🎒", "IL MIO ACCOUNT") + identity
            + "🎴 Abbonamento: <b>non attivo</b>\n"
              "📡 Monitoraggio eBay: <b>fermo</b> 🔒\n\n"
            + pricing_block() + "\n\n"
            + tip("Configura il monitoraggio quando vuoi."),
            parse_mode="HTML", reply_markup=subscription_keyboard()
        )
        return

    used = len(db_get_monitored_user_cards(chat_id))
    limit = user["card_limit"]
    left = min((days_left(p["subscription_end"]) for p in user.get("subscription_packages", [])), default=days_left(user["subscription_end"]))
    if left <= RENEW_WINDOW_DAYS:
        note = tip(f"Scade tra <b>{fmt_days(left)}</b>. Potrai acquistare un nuovo pacchetto dopo aver occupato tutti gli slot disponibili.")
    else:
        note = tip("Quando avrai occupato tutti gli slot, potrai acquistare un nuovo pacchetto con una scadenza indipendente.")
    markup = subscription_keyboard()
    await update.effective_message.reply_text(
        header("🎒", "IL MIO ACCOUNT") + identity
        + subscription_card(user, used, limit, chat_id) + "\n\n"
        + f"💶 Prezzo di riferimento: <b>{PRICE_PER_CARD_MONTH_EUR} € / carta / mese</b>\n\n"
        + note,
        parse_mode="HTML", reply_markup=markup
    )


POKEDEX_PAGE_SIZE = 10
POKEDEX_SAFE_TEXT_LEN = 3600


def _pokedex_card_block(index: int, card: dict) -> str:
    """Blocco compatto di una carta, con dati già escapati per Telegram HTML."""
    lines = [
        f"<b>#{index:03d}</b>  🎴 {esc(card.get('name', ''))}",
        f"┗ 🔢 {esc(card.get('card_number', ''))} · 📦 {esc(card.get('set_name', ''))}",
    ]
    if card.get("language"):
        lines.append(f"┗ 🌐 {esc(card['language'])}")
    lines.append(f"┗ 🎯 Budget max <b>{fmt_eur(card.get('max_target_price_eur', 0))}</b>")
    if card.get("coverage_text"):
        lines.append(f"┗ 📡 {esc(card['coverage_text'])}")
    return "\n".join(lines)


def _pokedex_pages(cards, active: bool, limit, chat_id: str):
    """Costruisce pagine <=10 carte, riducendole automaticamente se il testo si avvicina al limite Telegram."""
    if not cards:
        return []

    shown = str(len(cards))
    monitored = sum(1 for card in cards if card.get("is_monitored"))
    footer = []
    if limit:
        footer.append(_slot_bar(monitored, limit))
    if active:
        footer.append(monitor_line(chat_id, monitored))
        if is_admin_chat(chat_id):
            footer.append(tip("Usa ⏸ Pausa o ▶️ Riprendi sotto ogni carta. Le carte in pausa restano nel Pokédex."))
        else:
            footer.append(tip("Tocca ✏️ per cambiare il budget. La carta resta nel Pokédex."))
    else:
        footer.append(tip("Monitoraggio eBay non attivo. Riattiva l'abbonamento per riprendere gli avvisi."))
    footer_text = "\n\n".join(footer)

    pages = []
    i = 0
    while i < len(cards):
        chunk = cards[i:i + POKEDEX_PAGE_SIZE]
        # Se 10 carte sono troppo lunghe, riduci progressivamente la pagina.
        while len(chunk) > 1:
            body = "\n\n".join(_pokedex_card_block(i + j + 1, c) for j, c in enumerate(chunk))
            preview = header("📕", f"POKÉDEX · {shown} carte").rstrip("\n") + "\n\n" + body + "\n\n" + footer_text
            if len(preview) <= POKEDEX_SAFE_TEXT_LEN:
                break
            chunk = chunk[:-1]
        pages.append((i, chunk))
        i += len(chunk)

    return pages


def _pokedex_render(cards, page: int, chat_id: str, active: bool, limit):
    pages = _pokedex_pages(cards, active, limit, chat_id)
    if not pages:
        return None, None
    page = max(0, min(page, len(pages) - 1))
    start, chunk = pages[page]
    shown = str(len(cards))
    monitored = sum(1 for card in cards if card.get("is_monitored"))
    lines = [header("📕", f"POKÉDEX · {shown} carte").rstrip("\n"), ""]
    lines.extend(_pokedex_card_block(start + j + 1, c) for j, c in enumerate(chunk))
    footer = []
    if limit:
        footer.append(_slot_bar(monitored, limit))
    if active:
        footer.append(monitor_line(chat_id, monitored))
        if is_admin_chat(chat_id):
            footer.append(tip("Usa ⏸ Pausa o ▶️ Riprendi sotto ogni carta. Le carte in pausa restano nel Pokédex."))
        else:
            footer.append(tip("Tocca ✏️ per cambiare il budget. La carta resta nel Pokédex."))
    else:
        footer.append(tip("Monitoraggio eBay non attivo. Riattiva l'abbonamento per riprendere gli avvisi."))
    lines.extend(["", "\n\n".join(footer)])
    text = "\n\n".join(lines)
    if len(text) > MAX_TELEGRAM_TEXT_LEN:
        raise RuntimeError("Pokédex oltre il limite Telegram")
    return text, pages


async def my_cards_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    db_ensure_user(chat_id)
    user = db_get_user(chat_id)
    active = db_subscription_is_active(user)
    user = db_get_user(chat_id)
    cards = db_get_user_cards(chat_id)
    limit = None if is_admin_chat(chat_id) else (user["card_limit"] if active else 0)

    if not cards:
        await update.effective_message.reply_text(
            header("📕", "POKÉDEX")
            + "Il tuo Pokédex è ancora vuoto.\n\n"
            + tip("Usa /aggiungi per registrare la prima carta."),
            parse_mode="HTML", reply_markup=main_menu_keyboard()
        )
        return

    text, pages = _pokedex_render(cards, 0, chat_id, active, limit)
    await update.effective_message.reply_text(
        text, parse_mode="HTML", reply_markup=pokedex_keyboard(pages, 0, chat_id)
    )


async def _edit_admin_pokedex(query, page=0):
    chat_id = ADMIN_CHAT_ID
    cards = db_get_user_cards(chat_id)
    if not cards:
        await query.edit_message_text(
            header("📕", "POKÉDEX") + "Il tuo Pokédex è ancora vuoto.\n\n"
            + tip("Usa /aggiungi per registrare la prima carta."),
            parse_mode="HTML", reply_markup=main_menu_keyboard(),
        )
        return
    text, pages = _pokedex_render(cards, page, chat_id, True, None)
    await query.edit_message_text(
        text, parse_mode="HTML", reply_markup=pokedex_keyboard(pages, page, chat_id)
    )


# ============================================================
# VALIDAZIONE DATI CARTA
# ============================================================
_POKEMON_NAME_CACHE = None
_POKEMON_NAME_LOCK = threading.Lock()

def _norm_pokemon_name(value: str) -> str:
    value = unicodedata.normalize("NFKD", str(value or ""))
    value = "".join(ch for ch in value if not unicodedata.combining(ch))
    value = value.casefold().replace("♀", "f").replace("♂", "m")
    value = re.sub(r"[^a-z0-9]+", " ", value)
    return " ".join(value.split())

def ensure_pokemon_names_file():
    """Garantisce una lista locale completa: 1.025 specie, senza liste parziali."""
    path = POKEMON_NAMES_FILE
    try:
        if os.path.isfile(path):
            with open(path, "r", encoding="utf-8") as fh:
                count = sum(1 for line in fh if line.strip() and not line.lstrip().startswith("#"))
            if count == 1025:
                return True
    except OSError:
        pass
    try:
        response = requests.get(POKEMON_NAMES_SOURCE_URL, timeout=15, headers={"Accept": "application/json"})
        response.raise_for_status()
        data = response.json()
        if not isinstance(data, list) or len(data) != 1025 or len({str(x).strip() for x in data}) != 1025:
            raise ValueError("lista Pokémon incompleta o duplicata")
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8", newline="\n") as fh:
            fh.write("# Pokémon species list: 1.025 specie Gen I-IX\n")
            for name in data:
                safe = normalize_user_text(str(name), 100)
                if not safe:
                    raise ValueError("nome Pokémon non valido")
                fh.write(safe + "\n")
        os.replace(tmp, path)
        log.info("Lista Pokémon locale aggiornata: %s (1025 specie)", path)
        return True
    except Exception as e:
        log.error("Impossibile creare la lista Pokémon locale: tipo=%s", type(e).__name__)
        try:
            if os.path.exists(path + ".tmp"):
                os.remove(path + ".tmp")
        except OSError:
            pass
        return False


def _load_pokemon_names():
    global _POKEMON_NAME_CACHE
    if _POKEMON_NAME_CACHE is not None:
        return _POKEMON_NAME_CACHE
    with _POKEMON_NAME_LOCK:
        if _POKEMON_NAME_CACHE is not None:
            return _POKEMON_NAME_CACHE
        try:
            with open(POKEMON_NAMES_FILE, "r", encoding="utf-8") as fh:
                names = []
                for line in fh:
                    name = normalize_user_text(line.strip(), 100, allow_empty=True)
                    if name:
                        names.append(name)
        except OSError:
            log.error("File lista Pokémon mancante: %s", POKEMON_NAMES_FILE)
            _POKEMON_NAME_CACHE = set()
            return _POKEMON_NAME_CACHE
        _POKEMON_NAME_CACHE = {_norm_pokemon_name(n) for n in names if _norm_pokemon_name(n)}
        log.info("Lista Pokémon caricata: %s nomi", len(_POKEMON_NAME_CACHE))
        return _POKEMON_NAME_CACHE

def _card_contains_known_pokemon(card_name: str) -> bool:
    normalized = _norm_pokemon_name(card_name)
    if not normalized:
        return False
    # I nomi delle carte possono contenere Mega, ex, GX, V, VMAX, ecc.: cerchiamo
    # una specie canonica come token/sottostringa, senza richiedere il titolo esatto.
    names = _load_pokemon_names()
    if not names:
        return False
    padded = f" {normalized} "
    for name in sorted(names, key=len, reverse=True):
        if f" {name} " in padded:
            return True
    return False

def parse_card_name(raw: str):
    value = normalize_user_text(raw or "", MAX_CARD_NAME_LEN)
    if value is None:
        return None
    if _contains_non_pokemon_tcg_term(value):
        return None
    if not _card_contains_known_pokemon(value):
        return None
    return value


def parse_card_number(raw: str):
    value = normalize_user_text(raw or "", MAX_CARD_NUMBER_LEN)
    if value is None:
        return None
    value = re.sub(r"\s*/\s*", "/", value)
    if _contains_non_pokemon_tcg_term(value):
        return None
    if len(value) > MAX_CARD_NUMBER_LEN:
        return None
    if not re.fullmatch(r"[A-Za-z0-9]+(?:[ /-][A-Za-z0-9]+){0,5}", value):
        return None
    return value


def parse_set_name(raw: str):
    value = normalize_user_text(raw or "", MAX_SET_NAME_LEN)
    if value is None:
        return None
    if _contains_non_pokemon_tcg_term(value):
        return None
    return value


def parse_language(raw: str, allow_empty=False):
    value = normalize_user_text(raw or "", MAX_LANGUAGE_LEN, allow_empty=allow_empty)
    if value is None:
        return None
    value = value.upper()
    if allow_empty and value in {"", "-", "NO", "NONE", "NESSUNA"}:
        return ""
    if not re.fullmatch(r"[A-Z]{2,5}", value):
        return None
    return value


def parse_count(raw: str, maximum: int):
    value = normalize_user_text(raw or "", MAX_NUMERIC_INPUT_LEN)
    if value is None or not re.fullmatch(r"\d{1,3}", value):
        return None
    number = int(value)
    return number if 1 <= number <= maximum else None


def parse_months(raw: str):
    value = normalize_user_text(raw or "", 2)
    if value is None or not re.fullmatch(r"\d{1,2}", value):
        return None
    number = int(value)
    return number if 1 <= number <= MAX_SUBSCRIPTION_MONTHS else None


def card_identity(card):
    """Identità compatta della carta per messaggi Telegram."""
    parts = [card.get("name", ""), card.get("card_number", ""), card.get("set_name", "")]
    if card.get("language"):
        parts.append(card["language"])
    return " · ".join(esc(x) for x in parts if x)


def card_identity_raw(card):
    parts = [card.get("name", ""), card.get("card_number", ""), card.get("set_name", "")]
    if card.get("language"):
        parts.append(card["language"])
    return " · ".join(str(x) for x in parts if x)


# ============================================================
# AGGIUNTA CARTA (procedura guidata)
# ============================================================
async def add_card_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.pop("edit_card_id", None)
    for key in ("new_card_name", "new_card_number", "new_card_set", "new_card_language", "new_card_target", "editing_card_field"):
        context.user_data.pop(key, None)

    chat_id = str(update.effective_chat.id)
    db_ensure_user(chat_id)
    user = db_get_user(chat_id)
    if not db_subscription_is_active(user):
        await update.effective_message.reply_text(
            header("🔒", "MONITORAGGIO EBAY NON ATTIVO")
            + "Per monitorare carte serve un abbonamento attivo.\n\n"
            + pricing_block() + "\n\n"
            + tip("Configura il numero di carte e la durata dal pulsante qui sotto."),
            parse_mode="HTML", reply_markup=subscription_keyboard()
        )
        return ConversationHandler.END

    max_cards = None if is_admin_chat(chat_id) else user["card_limit"]
    current_cards = db_get_monitored_user_cards(chat_id)
    if max_cards is not None and len(current_cards) >= max_cards:
        await update.effective_message.reply_text(
            header("🚫", "LIMITE RAGGIUNTO")
            + f"Stai monitorando <b>{len(current_cards)}</b> carte su <b>{max_cards}</b> acquistate.\n\n"
            + tip("Per aggiungerne altre, prima usa tutti gli slot del pacchetto attivo; poi potrai acquistarne uno nuovo."),
            parse_mode="HTML", reply_markup=subscription_keyboard()
        )
        return ConversationHandler.END

    await update.effective_message.reply_text(
        header("🎴", "NUOVA CARTA · 1/5")
        + "<b>Nome della carta</b>\n"
          "È il nome scritto nella parte alta della carta. <b>Obbligatorio.</b>\n\n"
          "Esempio: <code>Mega Charizard ex</code>\n\n"
          "Scrivi solo il nome della carta.\n"
          "Usa /annulla per uscire.",
        parse_mode="HTML",
    )
    return ADD_CARD_NAME


async def add_card_name_step(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw_name = update.effective_message.text or ""
    if _non_pokemon_reason(raw_name):
        await update.effective_message.reply_text(
            "❌ <b>Carta non riconosciuta come Pokémon TCG</b>\n"
            "POKEBOT monitora esclusivamente carte Pokémon TCG.",
            parse_mode="HTML",
        )
        return ADD_CARD_NAME
    name = parse_card_name(raw_name)
    if not name:
        await update.effective_message.reply_text(
            "❌ <b>Carta non valida</b>\n"
            "Inserisci il nome di una carta del <b>Pokémon TCG</b>, ad esempio <code>Mega Charizard ex</code>."
            "\n\nPOKEBOT è dedicato esclusivamente alle carte Pokémon.",
            parse_mode="HTML",
        )
        return ADD_CARD_NAME

    context.user_data["new_card_name"] = name
    if context.user_data.pop("editing_card_field", None) == "name":
        await _show_card_confirmation(update.effective_message, context)
        return ADD_CARD_CONFIRM
    await update.effective_message.reply_text(
        header("🔢", "NUOVA CARTA · 2/5")
        + f"🎴 <b>{esc(name)}</b>\n\n"
          "<b>Numero della carta</b>\n"
          "Di solito si trova in basso a destra. <b>Obbligatorio.</b>\n\n"
          "Esempi: <code>125/131</code> · <code>125</code> · <code>TG05/TG30</code>\n\n"
          "Scrivi il numero esattamente come compare sulla carta.",
        parse_mode="HTML",
    )
    return ADD_CARD_NUMBER


async def add_card_number_step(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw_number = update.effective_message.text or ""
    if _non_pokemon_reason(raw_number):
        await update.effective_message.reply_text(
            "❌ <b>Numero non riconosciuto</b>\n"
            "Il codice inserito corrisponde a un altro gioco di carte.",
            parse_mode="HTML",
        )
        return ADD_CARD_NUMBER
    number = parse_card_number(raw_number)
    if not number:
        await update.effective_message.reply_text(
            "❌ <b>Numero non valido</b>\n"
            "Inserisci un numero carta come <code>125/131</code>, <code>125</code> o <code>TG05/TG30</code>.",
            parse_mode="HTML",
        )
        return ADD_CARD_NUMBER

    context.user_data["new_card_number"] = number
    if context.user_data.pop("editing_card_field", None) == "number":
        await _show_card_confirmation(update.effective_message, context)
        return ADD_CARD_CONFIRM
    await update.effective_message.reply_text(
        header("📦", "NUOVA CARTA · 3/5")
        + f"🎴 <b>{esc(context.user_data['new_card_name'])}</b> · <b>{esc(number)}</b>\n\n"
          "<b>Nome del set</b>\n"
          "Inserisci il nome del set a cui appartiene la carta. <b>Obbligatorio.</b>\n\n"
          "Esempio: <code>Phantasmal Flames</code> oppure <code>Set Base</code>",
        parse_mode="HTML",
    )
    return ADD_CARD_SET


async def add_card_set_step(update: Update, context: ContextTypes.DEFAULT_TYPE):
    raw_set = update.effective_message.text or ""
    if _non_pokemon_reason(raw_set):
        await update.effective_message.reply_text(
            "❌ <b>Set non riconosciuto come Pokémon TCG</b>\n"
            "Inserisci il nome del set Pokémon della carta.",
            parse_mode="HTML",
        )
        return ADD_CARD_SET
    set_name = parse_set_name(raw_set)
    if not set_name:
        await update.effective_message.reply_text(
            "❌ <b>Set non valido</b>\n"
            "Inserisci il nome del set Pokémon, ad esempio <code>Phantasmal Flames</code>.",
            parse_mode="HTML",
        )
        return ADD_CARD_SET

    context.user_data["new_card_set"] = set_name
    if context.user_data.pop("editing_card_field", None) == "set":
        await _show_card_confirmation(update.effective_message, context)
        return ADD_CARD_CONFIRM
    await update.effective_message.reply_text(
        header("🌐", "NUOVA CARTA · 4/5")
        + f"🎴 <b>{esc(context.user_data['new_card_name'])}</b> · {esc(context.user_data['new_card_number'])}\n"
          f"📦 <b>{esc(set_name)}</b>\n\n"
          "<b>Lingua</b> <i>(opzionale)</i>\n"
          "Consigliato usare solo l'acronimo: <code>ITA</code>, <code>ENG</code>, <code>JAP</code>, ecc.\n\n"
          "Puoi anche premere <b>Salta</b>.",
        parse_mode="HTML",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⏭️ Salta", callback_data="add:lang:skip")]]),
    )
    return ADD_CARD_LANGUAGE


async def add_card_language_skip(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    context.user_data["new_card_language"] = ""
    if context.user_data.pop("editing_card_field", None) == "language":
        await _show_card_confirmation(query.message, context)
        return ADD_CARD_CONFIRM
    await query.message.reply_text(
        header("🎯", "NUOVA CARTA · 5/5")
        + "<b>Qual è il tuo budget massimo?</b>\n"
          "Il tuo budget è espresso in euro. Se l'inserzione è in GBP, USD o un'altra valuta, POKEBOT la considera convertendone il prezzo in euro. La spedizione può essere mostrata nell'avviso, ma non viene conteggiata nel budget.\n\n"
          "Scrivi il tuo budget massimo in euro:\n"
          "<code>350</code> oppure <code>350,50</code>",
        parse_mode="HTML",
    )
    return ADD_CARD_TARGET


async def add_card_language_step(update: Update, context: ContextTypes.DEFAULT_TYPE):
    language = parse_language(update.effective_message.text or "", allow_empty=True)
    if language is None:
        await update.effective_message.reply_text(
            "❌ <b>Lingua non valida</b>\n"
            "Usa solo l'acronimo in lettere, ad esempio <code>ITA</code>, <code>ENG</code> o <code>JAP</code>, oppure premi <b>Salta</b>.",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⏭️ Salta", callback_data="add:lang:skip")]]),
        )
        return ADD_CARD_LANGUAGE

    context.user_data["new_card_language"] = language
    if context.user_data.pop("editing_card_field", None) == "language":
        await _show_card_confirmation(update.effective_message, context)
        return ADD_CARD_CONFIRM
    await update.effective_message.reply_text(
        header("🎯", "NUOVA CARTA · 5/5")
        + f"🎴 <b>{esc(context.user_data['new_card_name'])}</b> · {esc(context.user_data['new_card_number'])}\n"
          f"📦 <b>{esc(context.user_data['new_card_set'])}</b> · {esc(language) if language else '<i>lingua non specificata</i>'}\n\n"
          "<b>Qual è il tuo budget massimo?</b>\n"
          "Il tuo budget è espresso in euro. Se l'inserzione è in GBP, USD o un'altra valuta, POKEBOT la considera convertendone il prezzo in euro. La spedizione può essere mostrata nell'avviso, ma non viene conteggiata nel budget.\n\n"
          "Scrivi il tuo budget massimo in euro:\n"
          "<code>350</code> oppure <code>350,50</code>",
        parse_mode="HTML",
    )
    return ADD_CARD_TARGET


async def _show_card_confirmation(target_message, context):
    name = context.user_data.get("new_card_name", "")
    number = context.user_data.get("new_card_number", "")
    set_name = context.user_data.get("new_card_set", "")
    language = context.user_data.get("new_card_language", "") or ""
    budget = context.user_data.get("new_card_target")
    if not name or not number or not set_name or budget is None:
        return False
    text = (
        header("🧾", "CONFERMA CARTA")
        + "Controlla attentamente i dati prima di aggiungerla al Pokédex.\n\n"
          f"🎴 <b>Carta:</b> {esc(name)}\n"
          f"🔢 <b>Numero:</b> {esc(number)}\n"
          f"📦 <b>Set:</b> {esc(set_name)}\n"
          f"🌐 <b>Lingua:</b> {esc(language) if language else '<i>non specificata</i>'}\n"
          f"🎯 <b>Budget massimo:</b> {fmt_eur(budget)}\n\n"
          "Se qualcosa è sbagliato, modifica solo quel campo. Nessuno slot viene consumato finché non premi <b>Conferma aggiunta</b>."
    )
    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("🎴 Conferma aggiunta", callback_data="add:confirm")],
        [InlineKeyboardButton("✏️ Nome", callback_data="add:edit:name"), InlineKeyboardButton("✏️ Numero", callback_data="add:edit:number")],
        [InlineKeyboardButton("✏️ Set", callback_data="add:edit:set"), InlineKeyboardButton("✏️ Lingua", callback_data="add:edit:language")],
        [InlineKeyboardButton("✏️ Budget", callback_data="add:edit:budget")],
        [InlineKeyboardButton("❌ Annulla", callback_data="add:cancel")],
    ])
    await target_message.reply_text(text, parse_mode="HTML", reply_markup=keyboard)
    return True


async def add_card_confirm_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query.message is None or query.message.chat.type != "private":
        await query.answer(); return ConversationHandler.END
    action = query.data or ""
    if action == "add:cancel":
        await query.answer()
        return await cancel_add_card(update, context)
    if action.startswith("add:edit:"):
        field = action.split(":")[-1]
        prompts = {
            "name": (ADD_CARD_NAME, "🎴", "NUOVO NOME", "Inserisci il nome corretto della carta."),
            "number": (ADD_CARD_NUMBER, "🔢", "NUOVO NUMERO", "Inserisci il numero corretto della carta."),
            "set": (ADD_CARD_SET, "📦", "NUOVO SET", "Inserisci il nome corretto del set."),
            "language": (ADD_CARD_LANGUAGE, "🌐", "NUOVA LINGUA", "Inserisci l'acronimo, ad esempio ITA, ENG o JAP, oppure premi Salta."),
            "budget": (ADD_CARD_TARGET, "🎯", "NUOVO BUDGET", "Inserisci il nuovo budget massimo in euro."),
        }
        if field not in prompts:
            await query.answer("Operazione non valida.", show_alert=True); return ADD_CARD_CONFIRM
        state, emoji, title, prompt = prompts[field]
        context.user_data["editing_card_field"] = field
        await query.answer()
        markup = InlineKeyboardMarkup([[InlineKeyboardButton("⏭️ Salta", callback_data="add:lang:skip")]]) if field == "language" else None
        await query.message.reply_text(header(emoji, title) + prompt, parse_mode="HTML", reply_markup=markup)
        return state
    if action == "add:confirm":
        chat_id = str(query.from_user.id)
        user = db_get_user(chat_id)
        if not db_subscription_is_active(user):
            await query.answer("Abbonamento non attivo.", show_alert=True)
            return ConversationHandler.END
        max_cards = None if is_admin_chat(chat_id) else int(user.get("card_limit") or 0)
        used = len(db_get_monitored_user_cards(chat_id))
        if max_cards is not None and used >= max_cards:
            await query.answer("Hai esaurito gli slot acquistati.", show_alert=True)
            return ConversationHandler.END
        try:
            added = db_add_card(chat_id, context.user_data.get("new_card_name"), context.user_data.get("new_card_number"), context.user_data.get("new_card_set"), context.user_data.get("new_card_language", ""), context.user_data.get("new_card_target"), max_cards)
        except ValueError as exc:
            await query.answer(str(exc)[:180], show_alert=True)
            return ADD_CARD_CONFIRM
        if not added:
            await query.answer("Slot esauriti: aggiorna prima l'abbonamento.", show_alert=True)
            return ConversationHandler.END
        name = context.user_data.get("new_card_name")
        number = context.user_data.get("new_card_number")
        set_name = context.user_data.get("new_card_set")
        language = context.user_data.get("new_card_language", "")
        budget = context.user_data.get("new_card_target")
        for key in ("new_card_name", "new_card_number", "new_card_set", "new_card_language", "new_card_target"):
            context.user_data.pop(key, None)
        await query.answer("Carta aggiunta ✅")
        used += 1
        capacity = "🎴 Carte monitorate: <b>illimitate</b>" if max_cards is None else f"🎴 Carte monitorate: <b>{used}/{max_cards}</b>\n{_slot_bar(used, max_cards)}"
        await query.message.reply_text(header("🎉", "CARTA AGGIUNTA") + f"🎴 <b>{esc(name)}</b>\n🔢 Numero: <b>{esc(number)}</b>\n📦 Set: <b>{esc(set_name)}</b>\n🌐 Lingua: <b>{esc(language) if language else 'non specificata'}</b>\n🎯 Budget massimo: <b>{fmt_eur(budget)}</b>\n\n" + capacity + "\n\n" + tip("Il Monitoraggio eBay è già attivo."), parse_mode="HTML", reply_markup=pokedex_button())
        return ConversationHandler.END
    await query.answer("Operazione non valida.", show_alert=True)
    return ADD_CARD_CONFIRM


async def add_card_target_step(update: Update, context: ContextTypes.DEFAULT_TYPE):
    target_price = parse_budget(update.effective_message.text or "")
    if target_price is None:
        await update.effective_message.reply_text(
            "🤔 <b>Budget non valido</b>\n"
            f"Scrivi solo un numero positivo (massimo {MAX_TARGET_PRICE:.0f}), ad esempio <code>350,50</code>.",
            parse_mode="HTML"
        )
        return ADD_CARD_TARGET

    chat_id = str(update.effective_chat.id)
    user = db_get_user(chat_id)
    if not db_subscription_is_active(user):
        for key in ("new_card_name", "new_card_number", "new_card_set", "new_card_language", "new_card_target"):
            context.user_data.pop(key, None)
        await update.effective_message.reply_text(header("🔒", "MONITORAGGIO EBAY NON ATTIVO") + "Il tuo abbonamento è scaduto mentre aggiungevi la carta.", parse_mode="HTML")
        return ConversationHandler.END
    max_cards = None if is_admin_chat(chat_id) else int(user.get("card_limit") or 0)
    if max_cards is not None and len(db_get_monitored_user_cards(chat_id)) >= max_cards:
        await update.effective_message.reply_text("🚫 Hai raggiunto il limite di carte acquistato.\nAumenta prima il numero di carte dal tuo abbonamento.", parse_mode="HTML", reply_markup=subscription_keyboard())
        return ConversationHandler.END
    context.user_data["new_card_target"] = target_price
    if not await _show_card_confirmation(update.effective_message, context):
        await update.effective_message.reply_text("⌛ <b>Sessione scaduta</b>\nRiparti da /aggiungi.", parse_mode="HTML")
        return ConversationHandler.END
    return ADD_CARD_CONFIRM

async def cancel_add_card(update: Update, context: ContextTypes.DEFAULT_TYPE):
    for key in ("new_card_name", "new_card_number", "new_card_set", "new_card_language"):
        context.user_data.pop(key, None)
    context.user_data.pop("subscription_cards", None)
    was_edit = context.user_data.pop("edit_card_id", None) is not None
    if was_edit:
        text = "↩️ <b>Modifica annullata</b>\nIl budget non è stato cambiato."
    else:
        text = ("🌿 <b>Aggiunta annullata</b>\n"
                "Nessun problema: puoi riprovare quando vuoi!")
    await update.effective_message.reply_text(
        text, parse_mode="HTML", reply_markup=main_menu_keyboard(),
    )
    return ConversationHandler.END


def pokedex_keyboard(pages, page=0, chat_id=None):
    """Pulsanti di modifica per la pagina corrente + navigazione pagine."""
    rows, row = [], []
    total_pages = len(pages)
    page = max(0, min(int(page), max(0, total_pages - 1)))
    start, chunk = pages[page] if pages else (0, [])
    for j, c in enumerate(chunk):
        index = start + j + 1
        row.append(InlineKeyboardButton(f"✏️ #{index:03d}", callback_data=f"edit:{c['id']}"))
        if len(row) == 2:
            rows.append(row)
            row = []
        if chat_id and is_admin_chat(chat_id):
            enabled = bool(c.get("monitoring_enabled", True))
            label = "⏸ Pausa" if enabled else "▶️ Riprendi"
            next_state = 0 if enabled else 1
            rows.append([
                InlineKeyboardButton(
                    f"{label} #{index:03d}",
                    callback_data=f"admin:cardmon:{c['id']}:{next_state}:{page}",
                ),
                InlineKeyboardButton(
                    f"🗑 Elimina #{index:03d}",
                    callback_data=f"admin:carddel:ask:{c['id']}:{page}",
                ),
            ])
    if row:
        rows.append(row)

    if total_pages > 1:
        nav = []
        if page > 0:
            nav.append(InlineKeyboardButton("◀️", callback_data=f"pdx:{page - 1}"))
        nav.append(InlineKeyboardButton(f"{page + 1}/{total_pages}", callback_data="pdx:noop"))
        if page < total_pages - 1:
            nav.append(InlineKeyboardButton("▶️", callback_data=f"pdx:{page + 1}"))
        rows.append(nav)
    return InlineKeyboardMarkup(rows)


async def edit_card_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Tocco su ✏️: chiede il nuovo budget (la carta NON è modificabile)."""
    query = update.callback_query
    if query.message is None or query.message.chat.type != "private":
        await query.answer()
        return ConversationHandler.END

    m = re.fullmatch(r"edit:(\d{1,12})", query.data or "")
    if not m:
        await query.answer()
        return ConversationHandler.END

    chat_id = str(update.effective_chat.id)
    card = db_get_card(chat_id, int(m.group(1)))  # controlla che la carta sia sua
    if not card:
        await query.answer("Carta non trovata.", show_alert=True)
        return ConversationHandler.END

    context.user_data.pop("new_card_name", None)
    context.user_data["edit_card_id"] = card["id"]
    await query.answer()
    await query.message.reply_text(
        header("✏️", "MODIFICA BUDGET")
        + f"🎴 <b>{card_identity(card)}</b>\n"
          f"🎯 Budget attuale: <b>€{card['max_target_price_eur']:.2f}</b>\n\n"
          "<b>Qual è il nuovo budget massimo?</b>\n"
          "Scrivi il tuo budget massimo in euro:\n"
          "<code>350</code> oppure <code>350,50</code>\n\n"
        + tip("Puoi cambiare solo il budget: la carta resta nel tuo Pokédex. "
              "Scrivi /annulla per tornare indietro."),
        parse_mode="HTML",
    )
    return EDIT_CARD_PRICE


async def edit_card_price_step(update: Update, context: ContextTypes.DEFAULT_TYPE):
    price = parse_budget(update.effective_message.text or "")
    if price is None:
        await update.effective_message.reply_text(
            "🤔 <b>Budget non valido</b>\n"
            f"Scrivi solo un numero positivo (massimo {MAX_TARGET_PRICE:.0f}), ad esempio:\n"
            "<code>350</code> oppure <code>350,50</code>",
            parse_mode="HTML",
        )
        return EDIT_CARD_PRICE

    chat_id = str(update.effective_chat.id)
    card_id = context.user_data.pop("edit_card_id", None)
    card = db_get_card(chat_id, card_id) if card_id else None
    if not card or not db_update_card_price(chat_id, card["id"], price):
        await update.effective_message.reply_text(
            "⌛ <b>Sessione scaduta</b>\nApri il Pokédex con /carte e riprova.",
            parse_mode="HTML",
        )
        return ConversationHandler.END

    await update.effective_message.reply_text(
        header("✅", "BUDGET AGGIORNATO")
        + f"🎴 <b>{esc(card['name'])}</b>\n"
          f"💰 Prima: €{card['max_target_price_eur']:.2f}  →  Ora: <b>€{price:.2f}</b>\n\n"
        + tip("Il Monitoraggio eBay usa già il nuovo budget."),
        parse_mode="HTML",
        reply_markup=pokedex_button(),
    )
    return ConversationHandler.END



async def support_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Contatto diretto per problemi o domande."""
    chat_id = str(update.effective_chat.id)

    if not SUPPORT_URL:
        await update.effective_message.reply_text(
            header("💬", "SUPPORTO")
            + "Il contatto per l'assistenza non è configurato.\n\n"
              "Prova più tardi oppure contatta l'amministratore del bot.",
            parse_mode="HTML",
        )
        return

    await update.effective_message.reply_text(
        header("💬", "SUPPORTO")
        + "Hai un problema o una domanda? <b>Scrivimi direttamente</b>: "
          "ti rispondo appena posso.\n\n"
          "<b>Per risolvere più in fretta, indica:</b>\n"
          "▫️ cosa stavi facendo\n"
          f"▫️ il tuo ID: <code>{esc(chat_id)}</code>\n"
          "▫️ uno screenshot, se puoi\n\n"
        + tip("Diffida di chi ti scrive in privato dicendo di essere dell'assistenza: "
              "i pagamenti si fanno solo dai pulsanti del bot."),
        parse_mode="HTML",
        reply_markup=InlineKeyboardMarkup([support_row("💬 Scrivi al supporto")]),
    )


# ============================================================
# ADMIN
# ============================================================
def admin_keyboard():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("💳 Pagamenti", callback_data="admin:payments"),
         InlineKeyboardButton("👥 Utenti", callback_data="admin:users")],
        [InlineKeyboardButton("📊 Statistiche", callback_data="admin:stats")],
    ])


async def admin_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update):
        return
    await update.effective_message.reply_text(
        header("👑", "PANNELLO ADMIN")
        + "Gestione essenziale di pagamenti, utenti e monitoraggio.\n\n"
        + tip("Il numero di carte attive determina automaticamente la frequenza dello scanner."),
        parse_mode="HTML", reply_markup=admin_keyboard()
    )


async def admin_user_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update):
        return
    args = context.args or []
    target = str(args[0]).strip() if len(args) == 1 else ""
    if len(target) > 20 or not re.fullmatch(r"\d{1,20}", target):
        await update.effective_message.reply_text("Uso: /utente <chat_id>")
        return
    await send_admin_user_card(update, context, target)


async def send_admin_user_card(update_or_query, context, chat_id):
    user = db_get_user(chat_id)
    cards = db_get_user_cards(chat_id)
    if not user:
        status, limit, end = "non registrato", 0, "—"
    else:
        active = db_subscription_is_active(user)
        status = "attivo" if active else "non attivo"
        limit = "illimitate" if is_admin_chat(chat_id) else user["card_limit"]
        if is_admin_chat(chat_id):
            end = "nessuna"
        elif user.get("subscription_packages"):
            now = datetime.datetime.now(datetime.timezone.utc)
            end = "\n".join(
                (f"dal {fmt_date(p['subscription_start'])}, " if (_parse_iso(p["subscription_start"]) or now) > now else "")
                + f"{p['card_count']} carte fino al {fmt_date(p['subscription_end'])}"
                for p in user["subscription_packages"]
            )
        else:
            end = "nessuna (abbonamento non attivo)"
    text = (
        header("👤", "UTENTE")
        + f"🆔 ID: <code>{esc(chat_id)}</code>\n"
          f"📡 Monitoraggio: <b>{status}</b>\n"
          f"🎴 Carte salvate: <b>{len(cards)}</b>\n"
          f"🎴 Limite acquistato: <b>{limit}</b>\n"
          f"⏳ Pacchetti / scadenze: <b>{esc(end)}</b>\n"
          f"💶 Prezzo: <b>{PRICE_PER_CARD_MONTH_EUR} € / carta / mese</b>"
    )
    rows = []
    if not is_admin_chat(chat_id):
        rows.append([InlineKeyboardButton("⚙️ Attiva pacchetto", callback_data=f"admin:configure:{chat_id}")])
        if cards:
            rows.append([InlineKeyboardButton("✏️ Modifica carte", callback_data=f"admin:editcards:{chat_id}")])
        if user and user["subscription_status"] == ACTIVE_STATUS:
            rows.append([InlineKeyboardButton("🔒 Disattiva", callback_data=f"admin:deactivate:{chat_id}")])
    rows.append([InlineKeyboardButton("⬅️ Admin", callback_data="admin:home")])
    markup = InlineKeyboardMarkup(rows)
    if hasattr(update_or_query, "callback_query") and update_or_query.callback_query:
        q = update_or_query.callback_query
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=markup)
        except Exception as e:
            log.debug("Admin user card edit: %s", type(e).__name__)
            await q.message.reply_text(text, parse_mode="HTML", reply_markup=markup)
    else:
        await update_or_query.effective_message.reply_text(text, parse_mode="HTML", reply_markup=markup)


def admin_card_count_keyboard(target):
    counts = [1, 3, 5, 10, 20, 50, 100]
    rows = []
    for i in range(0, len(counts), 3):
        rows.append([
            InlineKeyboardButton(f"{n} carte", callback_data=f"admin:setc:{target}:{n}")
            for n in counts[i:i + 3]
        ])
    rows.append([InlineKeyboardButton("⬅️ Utente", callback_data=f"admin:user:{target}")])
    return InlineKeyboardMarkup(rows)


def admin_month_keyboard(target, card_count):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("1 mese", callback_data=f"admin:setm:{target}:{card_count}:1"),
         InlineKeyboardButton("3 mesi", callback_data=f"admin:setm:{target}:{card_count}:3")],
        [InlineKeyboardButton("6 mesi", callback_data=f"admin:setm:{target}:{card_count}:6"),
         InlineKeyboardButton("12 mesi", callback_data=f"admin:setm:{target}:{card_count}:12")],
        [InlineKeyboardButton("⬅️ Numero carte", callback_data=f"admin:configure:{target}")],
    ])


ADMIN_CARD_FIELDS = {
    "name": ("Nome", "name"), "number": ("Numero", "card_number"),
    "set": ("Set", "set_name"), "language": ("Lingua", "language"),
    "price": ("Prezzo massimo (€)", "max_target_price_eur"),
}


def _admin_edit_card_keyboard(target, card):
    rows = [[InlineKeyboardButton(label, callback_data=f"admin:editfield:{target}:{card['id']}:{key}")]
            for key, (label, _) in ADMIN_CARD_FIELDS.items()]
    rows.append([InlineKeyboardButton("⬅️ Elenco carte", callback_data=f"admin:editcards:{target}")])
    rows.append([InlineKeyboardButton("Fine", callback_data=f"admin:editdone:{target}")])
    return InlineKeyboardMarkup(rows)


def _admin_edit_card_text(target, card):
    return (header("✏️", "MODIFICA CARTA")
            + f"Utente: <code>{esc(target)}</code>\n"
            + f"Carta: <b>{esc(card['name'])}</b>\n"
            + f"Numero: <b>{esc(card['card_number'] or '—')}</b>\n"
            + f"Set: <b>{esc(card['set_name'] or '—')}</b>\n"
            + f"Lingua: <b>{esc(card['language'] or '—')}</b>\n"
            + f"Prezzo massimo: <b>{esc(card['max_target_price_eur'])} €</b>\n\nSeleziona il dato da correggere.")


async def admin_edit_cards_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update):
        await update.callback_query.answer("Non autorizzato.", show_alert=True)
        return ConversationHandler.END
    target = re.fullmatch(r"admin:editcards:(\d{1,20})", update.callback_query.data).group(1)
    if target == ADMIN_CHAT_ID:
        await update.callback_query.answer("Non puoi modificare le carte admin.", show_alert=True)
        return ConversationHandler.END
    context.user_data["admin_edit_target"] = target
    cards = db_get_user_cards(target)
    if not cards:
        await update.callback_query.answer("L'utente non ha carte salvate.", show_alert=True)
        return ConversationHandler.END
    keyboard = [[InlineKeyboardButton(f"{c['name']} · {c['card_number'] or 'senza numero'}", callback_data=f"admin:editcard:{target}:{c['id']}")] for c in cards]
    keyboard.append([InlineKeyboardButton("Fine", callback_data=f"admin:editdone:{target}")])
    await update.callback_query.answer()
    await update.callback_query.edit_message_text(header("✏️", "MODIFICA CARTE") + "Scegli la carta da correggere.", parse_mode="HTML", reply_markup=InlineKeyboardMarkup(keyboard))
    return ADMIN_EDIT_SELECT


async def admin_edit_card_select(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not is_admin(update):
        await q.answer("Non autorizzato.", show_alert=True)
        return ConversationHandler.END
    match = re.fullmatch(r"admin:editcard:(\d{1,20}):(\d{1,12})", q.data)
    target = context.user_data.get("admin_edit_target")
    if not match or match.group(1) != target:
        await q.answer("Selezione non valida.", show_alert=True)
        return ConversationHandler.END
    card = db_get_card(target, match.group(2))
    if not card:
        await q.answer("Carta non trovata.", show_alert=True)
        return ConversationHandler.END
    context.user_data["admin_edit_card_id"] = int(card["id"])
    await q.answer()
    await q.edit_message_text(_admin_edit_card_text(target, card), parse_mode="HTML", reply_markup=_admin_edit_card_keyboard(target, card))
    return ADMIN_EDIT_FIELD


async def admin_edit_field_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not is_admin(update):
        await q.answer("Non autorizzato.", show_alert=True)
        return ConversationHandler.END
    match = re.fullmatch(r"admin:editfield:(\d{1,20}):(\d{1,12}):(name|number|set|language|price)", q.data)
    target = context.user_data.get("admin_edit_target")
    card_id = context.user_data.get("admin_edit_card_id")
    if not match or match.group(1) != target or int(match.group(2)) != card_id:
        await q.answer("Selezione non valida.", show_alert=True)
        return ConversationHandler.END
    field = match.group(3)
    card = db_get_card(target, card_id)
    if not card:
        await q.answer("Carta non trovata.", show_alert=True)
        return ConversationHandler.END
    context.user_data["admin_edit_field"] = field
    prompts = {"name": "Invia il nome corretto della carta.", "number": "Invia il numero corretto.", "set": "Invia il nome corretto del set.", "language": "Invia la lingua (2-5 lettere); invia — per cancellarla.", "price": f"Invia il nuovo prezzo massimo (0,01–{MAX_TARGET_PRICE:.0f} €)."}
    await q.answer()
    await q.edit_message_text(prompts[field], reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("Annulla", callback_data=f"admin:editcard:{target}:{card_id}")]]))
    return ADMIN_EDIT_VALUE


async def admin_edit_value_step(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update):
        return ConversationHandler.END
    target = context.user_data.get("admin_edit_target")
    card_id = context.user_data.get("admin_edit_card_id")
    field = context.user_data.get("admin_edit_field")
    raw = update.effective_message.text or ""
    if field == "language" and raw.strip() in {"—", "-"}:
        raw = ""
    try:
        db_update_card_field(target, card_id, field, raw)
    except ValueError as exc:
        await update.effective_message.reply_text(f"{exc}\nRiprova oppure usa /annulla.")
        return ADMIN_EDIT_VALUE
    card = db_get_card(target, card_id)
    await update.effective_message.reply_text("Dato aggiornato ✅")
    await update.effective_message.reply_text(_admin_edit_card_text(target, card), parse_mode="HTML", reply_markup=_admin_edit_card_keyboard(target, card))
    return ADMIN_EDIT_FIELD


async def admin_edit_done(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not is_admin(update):
        await q.answer("Non autorizzato.", show_alert=True)
        return ConversationHandler.END
    target = re.fullmatch(r"admin:editdone:(\d{1,20})", q.data).group(1)
    if target != context.user_data.get("admin_edit_target"):
        await q.answer("Selezione non valida.", show_alert=True)
        return ConversationHandler.END
    context.user_data.pop("admin_edit_target", None)
    context.user_data.pop("admin_edit_card_id", None)
    context.user_data.pop("admin_edit_field", None)
    await q.answer()
    await send_admin_user_card(update, context, target)
    return ConversationHandler.END


async def admin_edit_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    for key in ("admin_edit_target", "admin_edit_card_id", "admin_edit_field"):
        context.user_data.pop(key, None)
    await update.effective_message.reply_text("Modifica annullata.")
    return ConversationHandler.END


def scanner_metrics():
    used = db_get_daily_api_calls()
    remaining = max(0, OPERATING_DAILY_LIMIT - used)
    tasks = [
        (chat_id, card)
        for chat_id, info in db_get_all_users_data().items()
        for card in info.get("target_cards", [])
    ]
    total_cards = len(tasks)
    now = datetime.datetime.now(datetime.timezone.utc)
    midnight = datetime.datetime.combine(
        now.date() + datetime.timedelta(days=1), datetime.time.min, tzinfo=datetime.timezone.utc
    )
    seconds_left = max(1.0, (midnight - now).total_seconds())
    if total_cards and remaining >= total_cards:
        cycles = max(1, remaining // total_cards)
        interval = seconds_left / cycles
    else:
        interval = None
    return total_cards, used, remaining, interval


def admin_stats_text():
    with db() as conn:
        total = conn.execute("SELECT COUNT(*) FROM users").fetchone()[0]
        active = conn.execute("SELECT COUNT(*) FROM users WHERE subscription_status='ACTIVE' AND plan='CUSTOM'").fetchone()[0]
        cards_total = conn.execute("SELECT COUNT(*) FROM cards").fetchone()[0]
        paid_capacity = conn.execute("SELECT COALESCE(SUM(card_limit),0) FROM users WHERE subscription_status='ACTIVE' AND plan='CUSTOM'").fetchone()[0]
        pending = conn.execute("SELECT COUNT(*) FROM payment_requests WHERE status='PENDING'").fetchone()[0]
    total_cards, used, remaining, interval = scanner_metrics()
    last_cycle = db_get_state("scanner_last_cycle_at")
    interval_text = "non disponibile" if interval is None else f"{interval:.0f} s"
    last_text = fmt_date(last_cycle) if last_cycle and _parse_iso(last_cycle) else ("nessuno" if not last_cycle else esc(last_cycle))
    return (
        header("📊", "STATISTICHE")
        + f"👥 Utenti registrati: <b>{total}</b>\n"
          f"🟢 Abbonamenti attivi: <b>{active}</b>\n"
          f"🎴 Carte attive nello scanner: <b>{total_cards}</b>\n"
          f"📦 Capacità acquistata: <b>{paid_capacity}</b> carte\n"
          f"💳 Pagamenti in attesa: <b>{pending}</b>\n\n"
          f"📡 Chiamate eBay oggi: <b>{used}/{OPERATING_DAILY_LIMIT}</b>\n"
          f"📉 Chiamate operative rimaste: <b>{remaining}</b>\n"
          f"⏱️ Intervallo stimato: <b>{interval_text}</b>\n"
          f"🔄 Ultimo ciclo: <b>{last_text}</b>"
    )


async def _notify_user_activation(context, chat_id, card_count, months, end, payment_verified=False, amount_cents=None):
    payment_line = (
        f"💶 Pagamento verificato: <b>{fmt_eur((amount_cents or custom_price_cents(card_count, months))/100)}</b>\n"
        if payment_verified else "🔧 Attivazione effettuata dall'ADMIN.\n"
    )
    try:
        await context.bot.send_message(
            chat_id=int(chat_id),
            text=(
                header("🎊", "ABBONAMENTO ATTIVO")
                + "Il pacchetto Monitoraggio eBay è stato attivato. ✅\n\n"
                  f"🎴 Carte acquistate: <b>{card_count}</b>\n"
                  f"⏳ Durata: <b>{months} {'mese' if months == 1 else 'mesi'}</b>\n"
                  + payment_line
                  + f"📡 Valido fino al <b>{end.strftime('%d/%m/%Y')}</b>\n\n"
                + tip("Puoi iniziare subito a registrare le carte dal menu." )
            ),
            parse_mode="HTML", reply_markup=main_menu_keyboard()
        )
    except Exception as e:
        log.warning("Notifica attivazione fallita: %s", type(e).__name__)


def pending_payments_text():
    pending = db_get_pending_payments(20)
    if not pending:
        return (
            header("💳", "PAGAMENTI") + "Nessun pagamento in attesa. ✅",
            InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Admin", callback_data="admin:home")]])
        )
    rows = []
    chunks = [header("💳", "PAGAMENTI IN ATTESA") + f"<b>{len(pending)}</b> richiesta/e.\n"]
    for item in pending:
        amount = item["amount_cents"] / 100
        duration = f"{item['months']} mese" if item["months"] == 1 else f"{item['months']} mesi"
        chunks.append(
            f"\n<b>{item['card_count']} carte · {duration} · {fmt_eur(amount)}</b>\n"
            f"🆔 <code>{esc(item['chat_id'])}</code>\n"
            f"👤 @{esc(item['username'])}\n"
            f"💳 Metodo dichiarato: <b>{esc(item['payment_method'])}</b>\n"
        )
        rows.append([
            InlineKeyboardButton("✅ Approva", callback_data=f"approve:{item['request_token']}"),
            InlineKeyboardButton("❌ Rifiuta", callback_data=f"reject:{item['request_token']}"),
        ])
    rows.append([InlineKeyboardButton("⬅️ Admin", callback_data="admin:home")])
    return "".join(chunks), InlineKeyboardMarkup(rows)

async def button_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = query.data or ""
    if query.message is None or query.message.chat.type != "private":
        await query.answer()
        return
    user_id = str(query.from_user.id)

    # ADMIN
    if data.startswith("admin:"):
        if not is_admin(update):
            await query.answer("🚫 Non autorizzato.", show_alert=True)
            return
        m = re.fullmatch(r"admin:cardmon:(\d{1,12}):([01]):(\d{1,3})", data)
        if m:
            chat_id = str(query.message.chat.id)
            if chat_id != ADMIN_CHAT_ID or str(query.from_user.id) != ADMIN_CHAT_ID:
                await query.answer("🚫 Azione disponibile solo nel Pokédex admin.", show_alert=True)
                return
            card_id, enabled, page = int(m.group(1)), bool(int(m.group(2))), int(m.group(3))
            if not db_set_card_monitoring(chat_id, card_id, enabled):
                await query.answer("Carta non trovata nel tuo Pokédex.", show_alert=True)
                return
            await query.answer("Monitoraggio ripreso ✅" if enabled else "Monitoraggio in pausa ⏸️")
            await _edit_admin_pokedex(query, page)
            return
        m = re.fullmatch(r"admin:carddel:ask:(\d{1,12}):(\d{1,3})", data)
        if m:
            chat_id = str(query.message.chat.id)
            card_id, page = int(m.group(1)), int(m.group(2))
            card = db_get_card(chat_id, card_id)
            if not card:
                await query.answer("Carta non trovata nel tuo Pokédex.", show_alert=True)
                return
            await query.answer()
            await query.edit_message_text(
                header("🗑️", "ELIMINA CARTA")
                + f"Vuoi eliminare <b>{esc(card['name'])}</b> dal tuo Pokédex?\n\n"
                + tip("L'eliminazione è definitiva e cancella anche gli avvisi salvati per questa carta."),
                parse_mode="HTML",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🗑 Elimina definitivamente", callback_data=f"admin:carddel:yes:{card_id}:{page}")],
                    [InlineKeyboardButton("↩️ Annulla", callback_data=f"admin:carddel:no:{page}")],
                ]),
            )
            return
        m = re.fullmatch(r"admin:carddel:yes:(\d{1,12}):(\d{1,3})", data)
        if m:
            chat_id = str(query.message.chat.id)
            card_id, page = int(m.group(1)), int(m.group(2))
            if not db_delete_card(chat_id, card_id):
                await query.answer("La carta non è stata trovata.", show_alert=True)
                return
            await query.answer("Carta eliminata.")
            await _edit_admin_pokedex(query, page)
            return
        m = re.fullmatch(r"admin:carddel:no:(\d{1,3})", data)
        if m:
            await query.answer("Eliminazione annullata.")
            await _edit_admin_pokedex(query, int(m.group(1)))
            return
        if data == "admin:home":
            await query.answer()
            await query.edit_message_text(header("👑", "PANNELLO ADMIN") + "Gestione essenziale di pagamenti, utenti e monitoraggio.", parse_mode="HTML", reply_markup=admin_keyboard())
            return
        if data == "admin:payments":
            await query.answer()
            text, markup = pending_payments_text()
            await query.edit_message_text(text, parse_mode="HTML", reply_markup=markup)
            return
        if data == "admin:stats":
            await query.answer()
            await query.edit_message_text(admin_stats_text(), parse_mode="HTML", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Admin", callback_data="admin:home")]]))
            return
        if data == "admin:users":
            await query.answer()
            with db() as conn:
                users = conn.execute(
                    "SELECT chat_id, subscription_status, card_limit FROM users WHERE chat_id != ? ORDER BY rowid DESC LIMIT 12",
                    (ADMIN_CHAT_ID,),
                ).fetchall()
            if not users:
                await query.edit_message_text(header("👥", "UTENTI") + "Nessun utente registrato.", parse_mode="HTML", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Admin", callback_data="admin:home")]]))
                return
            rows = []
            for uid, status, limit in users:
                rows.append([InlineKeyboardButton(f"{uid} · {status} · {limit} carte", callback_data=f"admin:user:{uid}")])
            rows.append([InlineKeyboardButton("💡 Cerca per ID", callback_data="admin:user_hint")])
            rows.append([InlineKeyboardButton("⬅️ Admin", callback_data="admin:home")])
            await query.edit_message_text(header("👥", "UTENTI") + "Seleziona un utente o usa <code>/utente ID</code>.", parse_mode="HTML", reply_markup=InlineKeyboardMarkup(rows))
            return
        if data == "admin:user_hint":
            await query.answer("Usa /utente ID per aprire la gestione di un utente.", show_alert=True)
            return
        m = re.fullmatch(r"admin:user:(\d{1,20})", data)
        if m:
            await query.answer()
            await send_admin_user_card(update, context, m.group(1))
            return
        m = re.fullmatch(r"admin:configure:(\d{1,20})", data)
        if m:
            target = m.group(1)
            if target == ADMIN_CHAT_ID:
                await query.answer("L'ADMIN è illimitato.", show_alert=True)
                return
            if not _can_buy_another_package(target):
                await query.answer(
                    "L'utente ha ancora slot liberi. Prima deve usarli tutti.", show_alert=True
                )
                return
            await query.answer()
            await query.edit_message_text(
                header("⚙️", "CONFIGURA UTENTE") + "Scegli il numero di carte da attivare.",
                parse_mode="HTML", reply_markup=admin_card_count_keyboard(target)
            )
            return
        m = re.fullmatch(r"admin:setc:(\d{1,20}):(\d{1,3})", data)
        if m:
            target, cards = m.group(1), int(m.group(2))
            if target == ADMIN_CHAT_ID or not 1 <= cards <= MAX_USER_CARDS:
                await query.answer("Dati non validi.", show_alert=True)
                return
            await query.answer()
            await query.edit_message_text(
                header("⚙️", "DURATA") + f"Attivazione manuale: <b>{cards} carte</b>.\nScegli la durata.",
                parse_mode="HTML", reply_markup=admin_month_keyboard(target, cards)
            )
            return
        m = re.fullmatch(r"admin:setm:(\d{1,20}):(\d{1,3}):(\d{1,2})", data)
        if m:
            target, cards, months = m.group(1), int(m.group(2)), int(m.group(3))
            if target == ADMIN_CHAT_ID or not (1 <= cards <= MAX_USER_CARDS and 1 <= months <= MAX_SUBSCRIPTION_MONTHS):
                await query.answer("Dati non validi.", show_alert=True)
                return
            if not _can_buy_another_package(target):
                await query.answer(
                    "L'utente ha ancora slot liberi. Prima deve usarli tutti.", show_alert=True
                )
                return
            try:
                end = db_activate_subscription(target, cards, months)
            except ValueError as e:
                await query.answer(str(e)[:180], show_alert=True)
                return
            log.info("ADMIN attivazione manuale: chat=%s carte=%s mesi=%s", target, cards, months)
            await query.answer("Attivato ✅")
            await _notify_user_activation(context, target, cards, months, end, payment_verified=False)
            await send_admin_user_card(update, context, target)
            return
        m = re.fullmatch(r"admin:deactivate:(\d{1,20})", data)
        if m:
            target = m.group(1)
            if target == ADMIN_CHAT_ID:
                await query.answer("L'ADMIN non può essere disattivato.", show_alert=True)
                return
            db_deactivate_subscription(target)
            log.info("ADMIN disattivazione: chat=%s", target)
            await query.answer("Disattivato ✅")
            await send_admin_user_card(update, context, target)
            return
        return

    # Guida
    if data.startswith("help:"):
        page = help_page(data.split(":", 1)[1])
        await query.answer()
        if page:
            text, keyboard = page
            try:
                await query.edit_message_text(text, parse_mode="HTML", reply_markup=keyboard)
            except Exception as e:
                log.debug("edit guida: %s", type(e).__name__)
        return

    # Navigazione Pokédex: il callback è valido solo nella chat privata che lo ha generato.
    if data == "pdx:noop":
        await query.answer(f"Pagina del Pokédex", show_alert=False)
        return
    m = re.fullmatch(r"pdx:(\d{1,3})", data)
    if m:
        if query.from_user is None or str(query.from_user.id) != str(query.message.chat.id):
            await query.answer("🚫 Non autorizzato.", show_alert=True)
            return
        chat_id = str(query.message.chat.id)
        try:
            page = int(m.group(1))
            db_ensure_user(chat_id)
            user = db_get_user(chat_id)
            active = db_subscription_is_active(user)
            user = db_get_user(chat_id)
            cards = db_get_user_cards(chat_id)
            limit = None if is_admin_chat(chat_id) else (user["card_limit"] if active else 0)
            if not cards:
                await query.answer("Il Pokédex è vuoto.", show_alert=True)
                return
            text, pages = _pokedex_render(cards, page, chat_id, active, limit)
            if text is None or pages is None:
                await query.answer("Pagina non disponibile.", show_alert=True)
                return
            await query.answer()
            await query.edit_message_text(
                text, parse_mode="HTML", reply_markup=pokedex_keyboard(pages, page, chat_id)
            )
        except Exception as e:
            log.warning("Navigazione Pokédex fallita: tipo=%s msg=%s", type(e).__name__, str(e)[:200])
            await query.answer("⚠️ Impossibile aprire questa pagina.", show_alert=True)
        return

    # Scorciatoie
    if data == "go:cards":
        await query.answer(); await my_cards_command(update, context); return
    if data == "go:sub":
        await query.answer(); await status_command(update, context); return
    if data == "bank:info":
        await query.answer()
        await query.message.reply_text(bank_transfer_text(), parse_mode="HTML", reply_markup=bank_transfer_keyboard())
        return

    m = re.fullmatch(r"sub:paid:(\d{1,3}):(\d{1,2})", data)
    if m:
        # Se il messaggio di pagamento è vecchio e la ConversationHandler non è più attiva,
        # manteniamo comunque il pulsante funzionante e ricreiamo la richiesta in sicurezza.
        cards, months = int(m.group(1)), int(m.group(2))
        if 1 <= cards <= MAX_USER_CARDS and 1 <= months <= MAX_SUBSCRIPTION_MONTHS:
            result_state = await create_payment_request(update, context, cards, months)
            return
        await query.answer("Selezione non valida.", show_alert=True)
        return

    # Compatibilità con vecchi messaggi dopo la migrazione.
    if data.startswith(("buy_plan:", "payment_plan:", "payment_done:", "payment_choose", "payment_back", "bank_plan:", "buy_package:")):
        await query.answer("Il sistema di abbonamento è stato aggiornato.", show_alert=True)
        await query.message.reply_text(pricing_block() + "\n\nConfigura ora il nuovo abbonamento.", parse_mode="HTML", reply_markup=subscription_keyboard())
        return

    # Azioni admin sui pagamenti: token casuale, singolo utilizzo.
    m = re.fullmatch(r"approve:([0-9a-f]{16})", data)
    if m:
        if not is_admin(update):
            await query.answer("🚫 Non autorizzato.", show_alert=True)
            return
        result = db_approve_payment_request(m.group(1))
        if not result.get("ok"):
            msg = result.get("message") or "Questa richiesta è già stata gestita o non è più valida."
            await query.answer(msg[:180], show_alert=True)
            return
        await query.answer("Approvato ✅")
        amount = result["amount_cents"] / 100
        await query.edit_message_text(
            f"✅ {result['card_count']} carte · {result['months']} {('mese' if result['months']==1 else 'mesi')} · {fmt_eur(amount)}\n"
            f"Pacchetto aggiunto per utente {result['chat_id']}, valido fino al {result['end'].strftime('%d/%m/%Y')}.",
            parse_mode="HTML"
        )
        await _notify_user_activation(
            context, result["chat_id"], result["card_count"], result["months"], result["end"],
            payment_verified=True, amount_cents=result["amount_cents"]
        )
        return

    m = re.fullmatch(r"reject:([0-9a-f]{16})", data)
    if m:
        if not is_admin(update):
            await query.answer("🚫 Non autorizzato.", show_alert=True)
            return
        result = db_reject_payment_request(m.group(1))
        if not result:
            await query.answer("Questa richiesta è già stata gestita o non esiste più.", show_alert=True)
            return
        await query.answer("Rifiutato")
        await query.edit_message_text(f"❌ Richiesta di {result['chat_id']} rifiutata.")
        try:
            await context.bot.send_message(
                chat_id=int(result["chat_id"]),
                text=header("❌", "PAGAMENTO NON VERIFICATO")
                + "Non siamo riusciti a verificare il pagamento.\n\n"
                + tip("Controlla il pagamento e riprova; l'attivazione avviene solo dopo la verifica dell'ADMIN."),
                parse_mode="HTML",
                reply_markup=InlineKeyboardMarkup([support_row()]) if SUPPORT_URL else None,
            )
        except Exception as e:
            log.warning("Notifica rifiuto fallita: %s", type(e).__name__)
        return

    await query.answer()


# ============================================================
# EBAY / ALERT
# ============================================================
def get_ebay_oauth_token():
    """Ottiene un token OAuth (client credentials). Non logga mai segreti."""
    if not EBAY_CLIENT_ID or not EBAY_CLIENT_SECRET:
        log.error("EBAY_CLIENT_ID / EBAY_CLIENT_SECRET non configurati.")
        return None

    if "-SBX-" in EBAY_CLIENT_ID.upper():
        log.warning("EBAY_CLIENT_ID sembra una chiave SANDBOX, ma il bot usa api.ebay.com "
                    "(Production): servono le chiavi Production.")

    credentials = base64.b64encode(
        f"{EBAY_CLIENT_ID}:{EBAY_CLIENT_SECRET}".encode()
    ).decode()

    try:
        response = requests.post(
            "https://api.ebay.com/identity/v1/oauth2/token",
            headers={
                "Content-Type": "application/x-www-form-urlencoded",
                "Authorization": f"Basic {credentials}",
            },
            data={
                "grant_type": "client_credentials",
                "scope": "https://api.ebay.com/oauth/api_scope",
            },
            timeout=20,
        )
        if response.status_code != 200:
            detail = ""
            try:
                body = response.json()
                detail = " | ".join(
                    str(body.get(k))[:200] for k in ("error", "error_description") if body.get(k)
                )
            except Exception:
                pass
            if response.status_code >= 500:
                log.error("Token eBay: HTTP %s (errore lato eBay, riprovo) %s",
                          response.status_code, detail)
            elif response.status_code in (400, 401):
                log.error("Token eBay: HTTP %s (credenziali/scope rifiutati: controlla "
                          "EBAY_CLIENT_ID/SECRET e che siano chiavi PRODUCTION) %s",
                          response.status_code, detail)
            else:
                log.error("Token eBay: HTTP %s %s", response.status_code, detail)
            return None
        return response.json().get("access_token")
    except Exception as e:
        log.error("Token eBay: errore %s", type(e).__name__)
        return None


def build_alert_text(card_name, listing_title, price, currency, shipping, shipping_currency, total,
                     target_price, condition, seller, feedback):
    """Costruisce il testo HTML dell'alert (tutto l'input esterno è escapato)."""
    saved = max(0.0, target_price - total)

    lines = [
        "🚨 <b>ATTENZIONE: CARTA SOTTO BUDGET!</b> 🚨",
        DIV,
        f"🎴 <b>{esc(card_name)}</b>",
        "",
        f"📄 {esc(listing_title[:MAX_TITLE_LEN])}",
    ]
    if condition:
        lines.append(f"🏷️ Condizione: <b>{esc(condition)}</b>")
    if seller:
        fb = f" · {esc(feedback)}% feedback" if feedback else ""
        lines.append(f"👤 Venditore: <b>{esc(seller)}</b>{fb}")

    lines += [
        "",
        f"💰 Prezzo: <b>{currency_symbol(currency)}{price:.2f}</b>",
        "🚚 Spedizione: " + (
            f"<b>{currency_symbol(shipping_currency)}{shipping:.2f}</b>"
            if shipping is not None and shipping_currency else "<i>non indicata</i>"
        ),
        f"💶 <b>Prezzo convertito in EUR per il budget: €{total:.2f}</b>",
        "",
        f"🎯 Il tuo budget: €{target_price:.2f}",
        f"<code>{budget_bar(total, target_price)}</code>",
        f"💸 Sotto budget di <b>€{saved:.2f}</b>",
        "",
        "⚠️ <i>Valuta l'acquisto prima che l'inserzione venga venduta.</i>",
    ]
    return "\n".join(lines)


def send_telegram_alert(target_chat_id, card_name, listing_title, price, currency, shipping,
                        shipping_currency, total, target_price, item_url, image_url=None,
                        condition=None, seller=None, feedback=None):
    """Invia l'alert con foto (se disponibile) e pulsante di acquisto.

    Ritorna True se consegnato (o destinatario irraggiungibile in modo
    permanente), False se va ritentato.
    """
    if not is_ebay_url(item_url):
        log.warning("Alert scartato: URL non eBay")
        return False

    text = build_alert_text(card_name, listing_title, price, currency, shipping, shipping_currency, total,
                            target_price, condition, seller, feedback)
    keyboard = {"inline_keyboard": [[{"text": "🛒 VEDI INSERZIONE SU EBAY", "url": item_url}]]}
    base = "https://api.telegram.org/bot" + TELEGRAM_BOT_TOKEN

    def _post(method, payload):
        try:
            return requests.post(f"{base}/{method}", json=payload, timeout=20)
        except requests.RequestException as e:
            # NON stampare e: l'eccezione contiene l'URL col token.
            log.warning("Invio Telegram fallito: %s", type(e).__name__)
            return None

    resp = None
    # Foto della carta: la caption ha limite 1024 caratteri.
    if image_url and is_ebay_image_url(image_url) and len(text) <= 1024:
        resp = _post("sendPhoto", {
            "chat_id": target_chat_id,
            "photo": image_url,
            "caption": text,
            "parse_mode": "HTML",
            "reply_markup": keyboard,
        })
        if resp is not None and resp.status_code == 200:
            return True
        # Foto non scaricabile da Telegram (400) → ripiego sul solo testo.

    resp = _post("sendMessage", {
        "chat_id": target_chat_id,
        "text": text,
        "parse_mode": "HTML",
        "reply_markup": keyboard,
    })

    if resp is None:
        return False
    if resp.status_code == 200:
        return True
    if resp.status_code == 403:
        log.info("Utente %s ha bloccato il bot, alert saltato.", target_chat_id)
        return True
    log.warning("Telegram sendMessage HTTP %s", resp.status_code)
    return False


# ============================================================
# VALUTE / FILTRI INSERZIONI
# ============================================================
# Il budget utente resta espresso in EUR. Se eBay restituisce una valuta diversa,
# convertiamo il prezzo in EUR usando il cambio giornaliero BCE, memorizzato in cache.
FX_CACHE = {"date": None, "rates": {"EUR": 1.0}, "loaded_at": {"EUR": time.time()}}
FX_LOCK = threading.Lock()
FX_CACHE_TTL = 24 * 60 * 60
BLOCKED_LISTING_TERMS = ("fake", "proxy")

# POKEBOT è dedicato esclusivamente al Pokémon TCG.
# Questi termini servono come seconda barriera client-side nel caso in cui
# un'inserzione sia pubblicata nella categoria CCG generica ma appartenga a un altro TCG.
NON_POKEMON_TCG_TERMS = (
    # Dragon Ball / Fusion World
    "dragon ball",
    "dragonball",
    "dragon ball super",
    "fusion world",
    "majin buu",
    "majinbuu",
    "kid buu",
    "goku",
    "gohan",
    "goten",
    "vegeta",
    "vegetto",
    "vegito",
    "gogeta",
    "frieza",
    "freezer",
    "broly",
    "piccolo",
    "trunks",
    "krillin",
    "yamcha",
    "tien",
    "beerus",
    "whis",
    "shenron",
    "zamasu",
    "jiren",
    "kefla",
    "caulifla",
    "kale",
    "bardock",
    "raditz",
    "cell",
    "dabura",
    "janemba",
    "cooler",
    "ginyu",
    "android 17",
    "android 18",
    "android 16",
    "android 21",
    "super saiyan",
    "saiyan",
    # Other major TCGs
    "one piece",
    "yu-gi-oh",
    "yugioh",
    "magic: the gathering",
    "magic the gathering",
    "digimon",
    "disney lorcana",
    "lorcana",
    "weiss schwarz",
    "flesh and blood",
    "cardfight!! vanguard",
    "battle spirits",
    "shadowverse",
    "final fantasy tcg",
    "gundam card game",
    "union arena",
    "star wars unlimited",
    "luffy",
    "zoro",
    "nami",
    "yugi",
)

# Pattern di codici tipici di giochi diversi dal Pokémon TCG.
# In particolare FBxx-xxx identifica Fusion World.
NON_POKEMON_TCG_PATTERNS = (
    re.compile(r"\bFB\d{2}[-/ ]\d{3}\b", re.IGNORECASE),
    re.compile(r"\bOP\d{2}[-/ ]\d{3}\b", re.IGNORECASE),
    re.compile(r"\bBT\d{2}[-/ ]\d{3}\b", re.IGNORECASE),
)


def _contains_non_pokemon_tcg_term(text):
    normalized = str(text or "").casefold()
    if not normalized:
        return False
    for term in NON_POKEMON_TCG_TERMS:
        pattern = r"(?<![\w])" + re.escape(term) + r"(?![\w])"
        if re.search(pattern, normalized):
            return True
    return any(pattern.search(str(text or "")) for pattern in NON_POKEMON_TCG_PATTERNS)


def _non_pokemon_reason(text):
    normalized = str(text or "").casefold()
    if not normalized:
        return None
    for term in NON_POKEMON_TCG_TERMS:
        pattern = r"(?<![\w])" + re.escape(term) + r"(?![\w])"
        if re.search(pattern, normalized):
            return term
    for pattern in NON_POKEMON_TCG_PATTERNS:
        match = pattern.search(str(text or ""))
        if match:
            return match.group(0).upper()
    return None


def _listing_text(item):
    parts = [
        str(item.get("title") or ""),
        str(item.get("shortDescription") or ""),
    ]
    for category in item.get("categories") or []:
        if isinstance(category, dict):
            parts.append(str(category.get("categoryName") or ""))
    for aspect in item.get("localizedAspects") or []:
        if isinstance(aspect, dict):
            parts.append(str(aspect.get("localizedAspectName") or ""))
            for value in aspect.get("localizedAspectValue") or []:
                parts.append(str(value or ""))
    return " ".join(p for p in parts if p).strip()


def _listing_game_is_pokemon(item):
    """Controllo permissivo dell'aspetto Game eBay.

    Non consideriamo più "Pokémon TCG" l'unico valore valido: eBay può restituire
    "Pokémon", "Pokémon TCG" oppure nessun aspetto. La decisione finale viene presa
    dai controlli locali sul testo dell'inserzione e sull'identità della carta.
    """
    for aspect in item.get("localizedAspects") or []:
        if not isinstance(aspect, dict):
            continue
        name = str(aspect.get("localizedAspectName") or "").strip().casefold()
        if name != "game":
            continue
        values = [str(v or "").strip().casefold() for v in (aspect.get("localizedAspectValue") or [])]
        if not values:
            return True
        return any(
            "pokemon" in v or "pokémon" in v
            for v in values
        )
    return True


def _listing_matches_requested_card(item, card):
    """Require the requested species and any provided set and card number."""
    requested_name = _norm_pokemon_name(card.get("name") or card.get("card_name"))
    raw_listing = _listing_text(item)
    listing_name = _norm_pokemon_name(raw_listing)
    if not requested_name or not listing_name:
        return False

    requested_padded = f" {requested_name} "
    listing_padded = f" {listing_name} "
    requested_species = [
        species for species in sorted(_load_pokemon_names(), key=len, reverse=True)
        if f" {species} " in requested_padded
    ]
    if not requested_species or not all(
        f" {species} " in listing_padded for species in requested_species
    ):
        return False

    requested_set = _norm_pokemon_name(card.get("set_name"))
    if requested_set:
        set_words = requested_set.split()
        set_variants = [set_words]
        if len(set_words) == 2 and set_words[0] == "set":
            set_variants.append(list(reversed(set_words)))
        if not any(
            re.search(
                r"(?<![a-z0-9])" + r"\s+".join(map(re.escape, words)) + r"(?![a-z0-9])",
                listing_name,
            )
            for words in set_variants
        ):
            return False

    requested_number = str(card.get("card_number") or "").strip()
    if requested_number:
        number_parts = re.findall(r"[A-Za-z0-9]+", requested_number)
        if not number_parts:
            return False
        number_pattern = (
            r"(?<![A-Za-z0-9])"
            + r"[\s./#-]*".join(map(re.escape, number_parts))
            + r"(?![A-Za-z0-9])"
        )
        if not re.search(number_pattern, raw_listing, re.IGNORECASE):
            return False

    return True


def _listing_has_blocked_terms(item):
    text = _listing_text(item).casefold()
    if not text:
        return False
    # Parole intere: evitiamo falsi positivi come "proximity" / "prefake".
    return any(re.search(r"(?<![\w])" + re.escape(term) + r"(?![\w])", text)
               for term in BLOCKED_LISTING_TERMS)


def _fetch_ecb_rate(currency):
    code = str(currency or "").upper()
    if not re.fullmatch(r"[A-Z]{3}", code) or code == "EUR":
        return 1.0 if code == "EUR" else None
    url = (
        f"https://data-api.ecb.europa.eu/service/data/EXR/D.{code}.EUR.SP00.A"
        f"?startPeriod={datetime.datetime.now(datetime.timezone.utc).date().isoformat()}"
    )
    try:
        response = requests.get(url, timeout=12, headers={"Accept": "text/xml"})
        response.raise_for_status()
        root = ET.fromstring(response.content)
    except Exception as e:
        log.warning("Cambio BCE non disponibile per %s: %s", code, type(e).__name__)
        return None

    for obs in root.iter():
        if obs.tag.endswith("Cube") and obs.attrib.get("currency", "").upper() == code:
            try:
                rate = float(obs.attrib.get("rate", ""))
            except (TypeError, ValueError):
                continue
            if math.isfinite(rate) and rate > 0:
                return rate
    return None


def get_fx_rate_to_eur(currency):
    code = str(currency or "").upper()
    if not re.fullmatch(r"[A-Z]{3}", code):
        return None
    if code == "EUR":
        return 1.0
    today = datetime.datetime.now(datetime.timezone.utc).date().isoformat()
    now = time.time()
    with FX_LOCK:
        cached = FX_CACHE.get("rates", {}).get(code)
        cached_date = FX_CACHE.get("date")
        cached_at = FX_CACHE.get("loaded_at", {}).get(code, 0)
        if cached is not None and cached_date == today and now - cached_at < FX_CACHE_TTL:
            return cached
    rate = _fetch_ecb_rate(code)
    if rate is None:
        return None
    with FX_LOCK:
        FX_CACHE["date"] = today
        FX_CACHE.setdefault("rates", {})[code] = rate
        FX_CACHE.setdefault("loaded_at", {})[code] = now
    return rate

def _price_to_eur(price_value, currency):
    try:
        value = float(price_value)
    except (TypeError, ValueError):
        return None
    if not math.isfinite(value) or value <= 0:
        return None
    code = str(currency or "").upper()
    rate = get_fx_rate_to_eur(code)
    if rate is None:
        return None
    converted = value / rate
    return converted if math.isfinite(converted) and converted > 0 else None


def currency_symbol(currency):
    return {
        "EUR": "€", "GBP": "£", "USD": "$", "JPY": "¥", "CAD": "C$",
        "AUD": "A$", "CHF": "CHF ", "SEK": "SEK ", "NOK": "NOK ",
        "DKK": "DKK ", "PLN": "PLN ",
    }.get(str(currency or "").upper(), str(currency or "").upper() + " ")


def _min_shipping_any_currency(item):
    """Restituisce il costo minimo di spedizione disponibile, senza usarlo nel budget."""
    options = item.get("shippingOptions") or []
    candidates = []
    for opt in options:
        cost = opt.get("shippingCost") or {}
        currency = str(cost.get("currency") or "").upper()
        try:
            value = float(cost.get("value", ""))
        except (TypeError, ValueError):
            continue
        if currency and re.fullmatch(r"[A-Z]{3}", currency) and math.isfinite(value) and value >= 0:
            candidates.append((value, currency))
    return min(candidates, key=lambda x: x[0]) if candidates else None


def _min_shipping_eur(item):
    """Costo di spedizione minimo in EUR, oppure None se non indicato."""
    costs = []
    for opt in item.get("shippingOptions") or []:
        cost = opt.get("shippingCost") or {}
        if cost.get("currency") != "EUR":
            continue
        try:
            value = float(cost.get("value", ""))
        except (TypeError, ValueError):
            continue
        if math.isfinite(value) and value >= 0:
            costs.append(value)
    return min(costs) if costs else None


def _item_image(item):
    img = (item.get("image") or {}).get("imageUrl")
    if not img:
        thumbs = item.get("thumbnailImages") or []
        if thumbs:
            img = (thumbs[0] or {}).get("imageUrl")
    return img


def search_ebay_deals(token, card, chat_id):
    """Cerca le inserzioni attive per la carta.

    La valuta non è un filtro: il prezzo viene convertito in EUR per confrontarlo con il budget.
    La spedizione viene mostrata ma NON entra nel budget.

    Ritorna "ok" se la ricerca è andata a buon fine, "auth_error" se il token non
    è più valido, "error" in tutti gli altri casi.
    """
    url = "https://api.ebay.com/buy/browse/v1/item_summary/search"
    headers = {
        "Authorization": f"Bearer {token}",
        "X-EBAY-C-MARKETPLACE-ID": "EBAY_IT",
    }
    # Include the number and set so eBay's AND-based search is more specific.
    raw_keywords = " ".join(
        str(value).strip()
        for value in (card.get("name") or card.get("card_name"), card.get("card_number"), card.get("set_name"))
        if str(value or "").strip()
    )
    if not raw_keywords:
        return "error"
    blocked_reason = _non_pokemon_reason(raw_keywords)
    if blocked_reason:
        log.info("Ricerca saltata: carta non Pokémon, card_id=%s reason=%s", card.get("id"), blocked_reason)
        return "non_pokemon"

    # Rafforziamo la ricerca anche sul termine Pokémon, oltre a categoria e aspetto eBay.
    search_query = raw_keywords if re.search(r"\bpok(?:e|é)mon\b", raw_keywords, re.IGNORECASE) else f"Pokémon {raw_keywords}"
    params = {
        "q": search_query,
        "category_ids": EBAY_CARD_CATEGORY_ID,
        "filter": "buyingOptions:{FIXED_PRICE}",
        "limit": 50,
        "sort": "price",
    }

    target_price = card.get("max_target_price_eur")
    if target_price is None or not math.isfinite(target_price) or target_price <= 0:
        return "error"

    try:
        response = requests.get(url, headers=headers, params=params, timeout=20)

        if response.status_code == 401:
            return "auth_error"
        if response.status_code != 200:
            log.warning("eBay search HTTP %s per carta id=%s", response.status_code, card.get("id"))
            return "error"

        data = response.json()

        items = data.get("itemSummaries") or []
        if not items:
            log.info("eBay: nessun risultato per carta_id=%s", card.get("id"))
        for item in items:
            title = item.get("title", "")
            item_url = item.get("itemWebUrl", "")
            item_id = item.get("itemId", "")
            price_info = item.get("price") or {}

            if not price_info or not item_id or not item_url:
                continue
            if _listing_has_blocked_terms(item):
                log.info("Inserzione scartata per termine bloccato: carta_id=%s item_id=%s",
                         card.get("id"), item_id)
                continue
            listing_reason = _non_pokemon_reason(_listing_text(item))
            if listing_reason:
                log.info("Inserzione scartata: TCG diverso dal Pokémon TCG, carta_id=%s item_id=%s reason=%s",
                         card.get("id"), item_id, listing_reason)
                continue
            if not _listing_game_is_pokemon(item):
                log.info("Inserzione scartata: Game eBay non Pokémon, carta_id=%s item_id=%s",
                         card.get("id"), item_id)
                continue
            if not _card_contains_known_pokemon(_listing_text(item)):
                log.info("Inserzione scartata: nessun Pokémon riconosciuto localmente, carta_id=%s item_id=%s",
                         card.get("id"), item_id)
                continue
            if not _listing_matches_requested_card(item, card):
                log.info("Inserzione scartata: identità carta non corrispondente, carta_id=%s item_id=%s",
                         card.get("id"), item_id)
                continue

            raw_currency = str(price_info.get("currency") or "").upper()
            try:
                price_val_native = float(price_info.get("value", 0.0))
            except (TypeError, ValueError):
                continue
            if not math.isfinite(price_val_native) or price_val_native <= 0:
                continue

            # Nessuna valuta viene esclusa. Se eBay fornisce già la conversione in EUR,
            # usiamo quella; altrimenti ricorriamo al cambio giornaliero BCE.
            price_val = None
            converted_value = price_info.get("convertedFromValue")
            converted_currency = str(price_info.get("convertedFromCurrency") or "").upper()
            if converted_currency == "EUR":
                try:
                    converted_value_num = float(converted_value)
                except (TypeError, ValueError):
                    converted_value_num = float("nan")
                if math.isfinite(converted_value_num) and converted_value_num > 0:
                    price_val = converted_value_num
            if price_val is None:
                price_val = _price_to_eur(price_val_native, raw_currency)
            if price_val is None:
                log.warning("Valuta non convertibile, alert saltato: carta_id=%s item_id=%s valuta=%s",
                            card.get("id"), item_id, raw_currency or "?")
                continue

            # La spedizione NON entra nel calcolo del budget. Viene mostrata soltanto nell'alert.
            shipping_info = _min_shipping_any_currency(item)
            shipping_value = shipping_info[0] if shipping_info else None
            shipping_currency = shipping_info[1] if shipping_info else None
            total = price_val

            if total > target_price:
                continue
            claim_token = db_claim_listing_alert(chat_id, card.get("id"), item_id, total)
            if not claim_token:
                continue

            seller_info = item.get("seller") or {}
            delivered = send_telegram_alert(
                chat_id, card_identity_raw(card), title,
                price_val_native, raw_currency or "EUR",
                shipping_value, shipping_currency, total, target_price, item_url,
                image_url=_item_image(item),
                condition=item.get("condition"),
                seller=seller_info.get("username"),
                feedback=seller_info.get("feedbackPercentage"),
            )
            if delivered:
                db_finalize_listing_alert(chat_id, card.get("id"), item_id, total, claim_token)

        return "ok"

    except Exception as e:
        log.warning("Errore scansione carta id=%s: %s", card.get("id"), type(e).__name__)
        return "error"


def send_telegram_text(chat_id, text, reply_markup=None) -> bool:
    """Messaggio semplice dal thread dello scanner.

    True = consegnato (o destinatario irraggiungibile in modo permanente),
    False = da ritentare. Non logga mai l'URL (contiene il token)."""
    payload = {"chat_id": chat_id, "text": text, "parse_mode": "HTML"}
    if reply_markup is not None:
        payload["reply_markup"] = reply_markup.to_dict()
    try:
        resp = requests.post(
            f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
            json=payload, timeout=20,
        )
    except requests.RequestException as e:
        log.warning("Invio Telegram fallito: %s", type(e).__name__)
        return False
    if resp.status_code == 200 or resp.status_code == 403:
        return True
    log.warning("Telegram sendMessage HTTP %s", resp.status_code)
    return False


def run_notice_checks():
    db_expire_overdue()
    for package in db_users_to_remind():
        left = days_left(package["end_raw"])
        text = (
            header("\U000023F0", "PACCHETTO IN SCADENZA")
            + f"Un pacchetto scade il <b>{fmt_date(package['end_raw'])}</b> (tra {fmt_days(left)}).\n\n"
              "Dopo la scadenza diminuiscono gli slot disponibili; le carte restano nel Pokedex.\n\n"
            + tip("Puoi aggiungere un pacchetto dal tuo Account.")
        )
        if send_telegram_text(package["chat_id"], text, subscription_keyboard()):
            db_mark_reminded(package["chat_id"], package["end_raw"])
    for package in db_users_to_notify_expired():
        user = db_get_user(package["chat_id"])
        still_active = db_subscription_is_active(user)
        n_cards = len(db_get_user_cards(package["chat_id"]))
        saved = f"Le tue <b>{n_cards}</b> carte restano nel Pokedex." if n_cards else "Il tuo Pokedex e vuoto."
        state = (
            "Gli altri pacchetti attivi continuano a coprire il monitoraggio.\n"
            if still_active else "Il monitoraggio eBay e fermo.\n"
        )
        text = (
            header("\U000023F3", "PACCHETTO SCADUTO")
            + f"Il pacchetto da {package['card_count']} carte e scaduto.\n"
            + state + saved + "\n\n"
            + tip("Puoi aggiungere un altro pacchetto dal tuo Account.")
        )
        if send_telegram_text(package["chat_id"], text, subscription_keyboard()):
            db_mark_expired_notified(package["chat_id"], package["end_raw"])


# ============================================================
# SCANNER (Monitoraggio eBay)
# ============================================================
def seconds_until_midnight(now=None):
    now = now or datetime.datetime.now(datetime.timezone.utc)
    midnight = datetime.datetime.combine(
        now.date() + datetime.timedelta(days=1), datetime.time.min, tzinfo=datetime.timezone.utc
    )
    return max(1.0, (midnight - now).total_seconds())


def _fair_overload_tasks(tasks, daily_date):
    """Quando non è matematicamente possibile controllare tutte le carte oggi,
    distribuisce il sottoinsieme in modo deterministico diverso ogni giorno."""
    seed = daily_date.isoformat().encode("utf-8")
    return sorted(
        tasks,
        key=lambda t: hashlib.sha256(seed + f"|{t[0]}|{t[1]['id']}".encode("utf-8")).digest()
    )


def calculate_next_scan_interval(total_cards, calls_remaining, seconds_remaining):
    """Intervallo start-to-start che spalma i cicli completi rimasti fino a mezzanotte."""
    if total_cards <= 0 or calls_remaining < total_cards or seconds_remaining <= 0:
        return None
    full_cycles = calls_remaining // total_cards
    if full_cycles <= 0:
        return None
    return seconds_remaining / full_cycles


def run_scanner_cycle(token, now=None):
    """Esegue un ciclo completo di tutte le carte attive e calcola il prossimo intervallo."""
    global CURRENT_DAILY_CALLS
    now = now or datetime.datetime.now(datetime.timezone.utc)
    CURRENT_DAILY_CALLS = db_get_daily_api_calls()
    calls_remaining = max(0, OPERATING_DAILY_LIMIT - CURRENT_DAILY_CALLS)

    users_data = db_get_all_users_data()
    tasks = [
        (chat_id, card)
        for chat_id, info in users_data.items()
        for card in info.get("target_cards", [])
    ]
    total_cards = len(tasks)
    if total_cards == 0:
        db_set_state("scanner_active_cards", "0")
        return {"status": "idle", "sleep": 30.0, "processed": 0, "total_cards": 0}

    if calls_remaining <= 0:
        sleep = seconds_until_midnight(now)
        log.warning("Budget eBay operativo esaurito: usate=%s limite=%s. Prossimo reset tra %.0fs",
                    CURRENT_DAILY_CALLS, OPERATING_DAILY_LIMIT, sleep)
        return {"status": "budget_exhausted", "sleep": sleep, "processed": 0, "total_cards": total_cards}

    cycle_id = secrets.token_hex(4)
    start_wall = time.time()
    daily = now.date()

    if total_cards <= calls_remaining:
        cycle_tasks = tasks
        overloaded = False
    else:
        cycle_tasks = _fair_overload_tasks(tasks, daily)[:calls_remaining]
        overloaded = True
        log.error(
            "CAPACITÀ SCANNER SUPERATA: carte_attive=%s chiamate_rimaste=%s. "
            "Oggi verranno controllate solo %s carte; il campionamento cambia ogni giorno.",
            total_cards, calls_remaining, len(cycle_tasks)
        )

    log.info(
        "Ciclo scanner %s: carte_attive=%s carte_nel_ciclo=%s chiamate_usate=%s/%s",
        cycle_id, total_cards, len(cycle_tasks), CURRENT_DAILY_CALLS, OPERATING_DAILY_LIMIT
    )
    processed = 0
    ok_count = 0
    auth_errors = 0
    errors = 0
    skipped_non_pokemon = 0

    for chat_id, card in cycle_tasks:
        # Se un nuovo utente/carta arriva durante il ciclo, non interrompiamo il ciclo
        # corrente: entrerà nel successivo. Questo evita cicli parziali incoerenti.
        result = search_ebay_deals(token, card, chat_id)
        CURRENT_DAILY_CALLS = db_increment_daily_api_calls()
        processed += 1
        if result == "ok":
            ok_count += 1
            LAST_SCAN_BY_CHAT[str(chat_id)] = time.time()
        elif result == "auth_error":
            auth_errors += 1
            log.warning("Ciclo scanner %s: token eBay rifiutato su carta id=%s", cycle_id, card.get("id"))
            # Il token verrà invalidato dal loop e rigenerato.
            break
        elif result == "non_pokemon":
            skipped_non_pokemon += 1
        else:
            errors += 1
        log.debug("Ciclo scanner %s: carta_id=%s risultato=%s calls=%s", cycle_id, card.get("id"), result, CURRENT_DAILY_CALLS)

    elapsed = time.time() - start_wall
    db_set_state("scanner_last_cycle_at", datetime.datetime.now(datetime.timezone.utc).isoformat())
    db_set_state("scanner_last_cycle_cards", str(processed))
    db_set_state("scanner_active_cards", str(total_cards))
    db_set_state("scanner_last_cycle_id", cycle_id)

    log.info(
        "Fine ciclo %s: processate=%s ok=%s skip_non_pokemon=%s errori=%s durata=%.1fs",
        cycle_id, processed, ok_count, skipped_non_pokemon, errors, elapsed
    )

    if auth_errors:
        return {"status": "auth_error", "sleep": 5.0, "processed": processed, "total_cards": total_cards, "elapsed": elapsed}

    if overloaded:
        # Non è possibile completare un ciclo globale: lasciamo il resto del budget per
        # il campionamento successivo e ricalcoliamo alla prossima wake/sosta breve.
        sleep = min(300.0, seconds_until_midnight(now))
        log.warning("Ciclo scanner %s parziale: %s/%s carte, prossimo controllo tra %.0fs",
                    cycle_id, processed, total_cards, sleep)
        return {"status": "overloaded", "sleep": max(5.0, sleep - elapsed), "processed": processed, "total_cards": total_cards, "elapsed": elapsed}

    remaining_after = max(0, OPERATING_DAILY_LIMIT - CURRENT_DAILY_CALLS)
    seconds_left = seconds_until_midnight(datetime.datetime.now(datetime.timezone.utc))
    ideal_interval = calculate_next_scan_interval(total_cards, remaining_after, seconds_left)
    if ideal_interval is None:
        sleep = seconds_left
    else:
        # ideal_interval è distanza tra gli inizi dei cicli; sottraiamo il tempo
        # già impiegato per mantenere costante la cadenza reale.
        sleep = max(2.0, ideal_interval - elapsed)

    db_set_state("scanner_next_interval_seconds", f"{ideal_interval:.3f}" if ideal_interval else "0")
    db_set_state("scanner_last_result", f"ok={ok_count},errors={errors},cards={processed}/{total_cards}")
    log.info(
        "Ciclo scanner %s completato: ok=%s errori=%s carte=%s/%s durata=%.1fs "
        "calls=%s/%s intervallo_successivo=%s",
        cycle_id, ok_count, errors, processed, total_cards, elapsed,
        CURRENT_DAILY_CALLS, OPERATING_DAILY_LIMIT,
        f"{ideal_interval:.1f}s" if ideal_interval else "fine_giornata"
    )
    return {"status": "ok", "sleep": sleep, "processed": processed, "total_cards": total_cards, "elapsed": elapsed, "interval": ideal_interval}


def run_scanner_loop():
    global CURRENT_DAILY_CALLS
    log.info(
        "Monitoraggio eBay avviato: limite operativo=%s/giorno, limite assoluto=%s/giorno",
        OPERATING_DAILY_LIMIT, ABSOLUTE_DAILY_LIMIT
    )
    token = None
    token_fetch_time = 0.0
    token_failures = 0
    last_notice_check = 0.0
    last_prune = 0.0

    while True:
        try:
            now = time.time()
            if now - last_notice_check > NOTICE_CHECK_INTERVAL:
                last_notice_check = now
                try:
                    run_notice_checks()
                except Exception as e:
                    log.warning("Controllo promemoria fallito: tipo=%s msg=%s", type(e).__name__, str(e)[:200])

            if now - last_prune > 86400:
                last_prune = now
                try:
                    db_prune_alerted(60)
                except Exception as e:
                    log.warning("Pulizia alert fallita: tipo=%s msg=%s", type(e).__name__, str(e)[:200])

            if not token or time.time() - token_fetch_time > EBAY_TOKEN_TTL:
                new_token = get_ebay_oauth_token()
                if new_token:
                    token = new_token
                    token_fetch_time = time.time()
                    token_failures = 0
                    log.info("Token eBay ottenuto/aggiornato")
                elif not token:
                    token_failures += 1
                    wait = min(60 * 2 ** (token_failures - 1), 900)
                    log.warning("Token eBay non disponibile: nuovo tentativo tra %ss", wait)
                    SCANNER_WAKE.wait(timeout=wait)
                    SCANNER_WAKE.clear()
                    continue

            result = run_scanner_cycle(token)
            if result["status"] == "auth_error":
                token = None
                token_fetch_time = 0.0
                continue

            sleep_seconds = max(2.0, float(result.get("sleep", 30)))
            SCANNER_WAKE.wait(timeout=sleep_seconds)
            SCANNER_WAKE.clear()
        except sqlite3.OperationalError as e:
            log.error("Errore SQLite nel ciclo scanner: tipo=%s msg=%s", type(e).__name__, str(e)[:300])
            # Se il DB è temporaneamente occupato (es. DB Browser), il busy_timeout
            # dovrebbe gestirlo; qui evitiamo che un errore inatteso blocchi il bot.
            SCANNER_WAKE.wait(timeout=10)
            SCANNER_WAKE.clear()
        except requests.RequestException as e:
            log.warning("Errore rete nel ciclo scanner: tipo=%s", type(e).__name__)
            SCANNER_WAKE.wait(timeout=15)
            SCANNER_WAKE.clear()
        except Exception as e:
            log.error("Errore nel ciclo scanner: tipo=%s msg=%s", type(e).__name__, str(e)[:300])
            SCANNER_WAKE.wait(timeout=30)
            SCANNER_WAKE.clear()

# ============================================================
# MAIN
# ============================================================
async def error_handler(update, context: ContextTypes.DEFAULT_TYPE):
    update_id = getattr(update, "update_id", None)
    user = getattr(update, "effective_user", None) if update else None
    user_id = getattr(user, "id", None)
    msg = str(context.error)[:300] if context.error else ""
    for secret in (TELEGRAM_BOT_TOKEN, EBAY_CLIENT_SECRET, EBAY_CLIENT_ID):
        if secret:
            msg = msg.replace(secret, "[REDACTED]")
    log.error(
        "Errore handler: tipo=%s msg=%s update=%s user=%s",
        type(context.error).__name__, msg, update_id, user_id
    )


async def post_init(application):
    try:
        await application.bot.set_my_commands([
            BotCommand("start", "🔴 Avvia il bot"),
            BotCommand("aggiungi", "🎴 Aggiungi una carta"),
            BotCommand("abbonamento", "💳 Configura monitoraggio"),
            BotCommand("carte", "📕 Il mio Pokédex"),
            BotCommand("account", "🎒 Il mio account"),
            BotCommand("guida", "❓ Guida"),
            BotCommand("supporto", "💬 Contatta il supporto"),
            BotCommand("annulla", "❌ Annulla l'operazione"),
        ])
        await application.bot.set_chat_menu_button(menu_button=MenuButtonCommands())
    except Exception as e:
        log.warning("set_my_commands fallito: tipo=%s msg=%s", type(e).__name__, str(e)[:200])

    for method, kwargs in (
        ("set_my_description", {"description": BOT_DESCRIPTION}),
        ("set_my_short_description", {"short_description": BOT_SHORT_DESCRIPTION}),
    ):
        try:
            await getattr(application.bot, method)(**kwargs)
        except Exception as e:
            log.warning("%s fallito: tipo=%s msg=%s", method, type(e).__name__, str(e)[:200])


def _menu_handler(button, callback):
    texts = [button, *LEGACY_BUTTONS[button]]
    return MessageHandler(PRIVATE & filters.Text(texts), callback)


if __name__ == "__main__":
    if not TELEGRAM_BOT_TOKEN and not BOT_STANDBY:
        raise RuntimeError("Variabile TELEGRAM_BOT_TOKEN non configurata.")
    if not ADMIN_CHAT_ID:
        log.warning("ADMIN_CHAT_ID non configurato o non valido: le funzioni admin sono disabilitate.")
    if not SUPPORT_URL:
        log.warning("Supporto non configurato: verificare SUPPORT_USERNAME o ADMIN_CHAT_ID.")
    if not PAYPAL_LINK:
        log.warning("PAYPAL_LINK non configurato: PayPal non sarà disponibile.")
    if not BANK_TRANSFER_AVAILABLE:
        log.info("Bonifico non configurato: verrà mostrato solo se i dati bancari sono presenti nel .env.")

    acquire_process_lock()
    if not ensure_pokemon_names_file():
        raise RuntimeError("Lista Pokémon non disponibile: impossibile avviare POKEBOT in modalità sicura.")
    init_db()
    CURRENT_DAILY_CALLS = db_get_daily_api_calls()
    log.info(
        "Configurazione scanner: chiamate oggi=%s/%s, prezzo=%s€/carta/mese, max self-service=%s carte",
        CURRENT_DAILY_CALLS, OPERATING_DAILY_LIMIT, PRICE_PER_CARD_MONTH_EUR, MAX_USER_CARDS
    )

    if BOT_STANDBY:
        log.info("Modalità standby attiva: Telegram e scanner sono disattivati.")
        while True:
            time.sleep(3600)

    scanner_thread = threading.Thread(target=run_scanner_loop, name="ebay-scanner", daemon=True)
    scanner_thread.start()

    app = ApplicationBuilder().token(TELEGRAM_BOT_TOKEN).post_init(post_init).build()
    app.add_handler(TypeHandler(Update, security_gate), group=-2)
    app.add_handler(TypeHandler(Update, rate_limit), group=-1)
    app.add_error_handler(error_handler)

    app.add_handler(CommandHandler("start", start_command, filters=PRIVATE))
    app.add_handler(CommandHandler(["account", "status", "abbonamento_old", "subscription"], status_command, filters=PRIVATE))
    app.add_handler(CommandHandler(["guida", "help"], menu_help, filters=PRIVATE))
    app.add_handler(CommandHandler("supporto", support_command, filters=PRIVATE))
    app.add_handler(CommandHandler("admin", admin_command, filters=PRIVATE))
    app.add_handler(CommandHandler("utente", admin_user_command, filters=PRIVATE))

    warnings.filterwarnings("ignore", message=".*per_message=False.*")

    add_card_conversation = ConversationHandler(
        entry_points=[
            CommandHandler(["aggiungi", "addcard"], add_card_command, filters=PRIVATE),
            _menu_handler(BTN_ADD, add_card_command),
            CallbackQueryHandler(edit_card_start, pattern=r"^edit:\d{1,12}$"),
        ],
        states={
            ADD_CARD_NAME: [MessageHandler(PRIVATE & filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, add_card_name_step)],
            ADD_CARD_NUMBER: [MessageHandler(PRIVATE & filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, add_card_number_step)],
            ADD_CARD_SET: [MessageHandler(PRIVATE & filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, add_card_set_step)],
            ADD_CARD_LANGUAGE: [
                CallbackQueryHandler(add_card_language_skip, pattern=r"^add:lang:skip$"),
                MessageHandler(PRIVATE & filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, add_card_language_step),
            ],
            ADD_CARD_TARGET: [MessageHandler(PRIVATE & filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, add_card_target_step)],
            ADD_CARD_CONFIRM: [
                CallbackQueryHandler(add_card_confirm_callback, pattern=r"^add:(?:confirm|cancel|edit:(?:name|number|set|language|budget))$")
            ],
            EDIT_CARD_PRICE: [MessageHandler(PRIVATE & filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, edit_card_price_step)],
        },
        fallbacks=[CommandHandler(["annulla", "cancel"], cancel_add_card, filters=PRIVATE)],
        allow_reentry=True,
    )
    app.add_handler(add_card_conversation)

    admin_card_edit_conversation = ConversationHandler(
        entry_points=[CallbackQueryHandler(admin_edit_cards_start, pattern=r"^admin:editcards:\d{1,20}$")],
        states={
            ADMIN_EDIT_SELECT: [
                CallbackQueryHandler(admin_edit_card_select, pattern=r"^admin:editcard:\d{1,20}:\d{1,12}$"),
                CallbackQueryHandler(admin_edit_done, pattern=r"^admin:editdone:\d{1,20}$"),
            ],
            ADMIN_EDIT_FIELD: [
                CallbackQueryHandler(admin_edit_field_start, pattern=r"^admin:editfield:\d{1,20}:\d{1,12}:(?:name|number|set|language|price)$"),
                CallbackQueryHandler(admin_edit_cards_start, pattern=r"^admin:editcards:\d{1,20}$"),
                CallbackQueryHandler(admin_edit_done, pattern=r"^admin:editdone:\d{1,20}$"),
            ],
            ADMIN_EDIT_VALUE: [
                MessageHandler(PRIVATE & filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, admin_edit_value_step),
                CallbackQueryHandler(admin_edit_card_select, pattern=r"^admin:editcard:\d{1,20}:\d{1,12}$"),
            ],
        },
        fallbacks=[CommandHandler(["annulla", "cancel"], admin_edit_cancel, filters=PRIVATE)],
        allow_reentry=True,
    )
    app.add_handler(admin_card_edit_conversation)

    subscription_conversation = ConversationHandler(
        entry_points=[
            CommandHandler("abbonamento", subscription_start, filters=PRIVATE),
            CallbackQueryHandler(subscription_start_callback, pattern=r"^sub:start$"),
        ],
        states={
            SUB_CARDS: [
                CallbackQueryHandler(subscription_card_choice, pattern=r"^sub:cards:(?:custom|\d{1,3})$"),
                MessageHandler(PRIVATE & filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, subscription_card_text_step),
            ],
            SUB_MONTHS: [
                CallbackQueryHandler(subscription_month_choice, pattern=r"^sub:(?:months:(?:custom|\d{1,2})|edit|summary:\d{1,3}:\d{1,2}|bank:\d{1,3}:\d{1,2}|paid:\d{1,3}:\d{1,2})$"),
                MessageHandler(PRIVATE & filters.TEXT & ~filters.COMMAND & ~MENU_FILTER, subscription_month_text_step),
            ],
        },
        fallbacks=[CommandHandler(["annulla", "cancel"], cancel_add_card, filters=PRIVATE)],
        allow_reentry=True,
    )
    app.add_handler(subscription_conversation)

    app.add_handler(_menu_handler(BTN_CARDS, my_cards_command))
    app.add_handler(_menu_handler(BTN_ACCOUNT, status_command))
    app.add_handler(_menu_handler(BTN_HELP, menu_help))
    app.add_handler(CommandHandler(["carte", "mycards"], my_cards_command, filters=PRIVATE))
    app.add_handler(CallbackQueryHandler(button_callback))

    log.info("POKEBOT avviato! In ascolto per nuovi comandi Telegram...")
    app.run_polling()
