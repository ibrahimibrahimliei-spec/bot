# -*- coding: utf-8 -*-
"""
Çox-fənnli Telegram Quiz Botu

Xüsusiyyətlər:
- Çox fənn (Mülki Müdafiə, ADİAK, ...)
- Mövzuya görə və ya ümumi sınaq
- Reklam yoxlaması (WebApp sendData ilə — manual keçid yoxdur)
- Səhv suallar rejimi (yanlış cavablandığın sualları təkrarlama)
- Yarımçıq testi davam etdir
- Favorit sualları ⭐
- Çətinlik statistikası (hansı sual ən çox səhv cavablanır)
- Admin: sual əlavə et / redaktə et / sil + bulk import (PDF/JSON)
- Qrup rejimi (qrupda yarış)
- Test sonunda nəticəni paylaş
- Hər yeni sual göstəriləndə əvvəlki mesaj silinir (qarışıqlıq olmasın)
"""
import json
import random
import logging
import sqlite3
import os
import io
import time
import re
import urllib.parse
from datetime import datetime, timedelta
from telegram import (
    Update, InlineKeyboardButton, InlineKeyboardMarkup, WebAppInfo,
    KeyboardButton, ReplyKeyboardMarkup, ReplyKeyboardRemove
)
from telegram.ext import (
    Updater, CommandHandler, CallbackQueryHandler,
    CallbackContext, MessageHandler, Filters, ConversationHandler
)

# ─── CONFIG ───────────────────────────────────────────────────────────────────

TOKEN = "8652179755:AAHIDbbPgfJg4PwMbEA_mpNtblcxZRpUyn0"
DATA_DIR = os.environ.get("DATA_DIR", ".")
os.makedirs(DATA_DIR, exist_ok=True)
DATA_FILE = os.path.join(DATA_DIR, "questions_data.json")
DB_FILE = os.path.join(DATA_DIR, "bot_data.db")

# İlk işə salımda repo-dakı default questions_data.json-u volume-ə kopyala
if not os.path.exists(DATA_FILE) and os.path.exists("questions_data.json"):
    import shutil
    shutil.copy("questions_data.json", DATA_FILE)
# ⚠️  Buraya öz Telegram ID-nizi yazın!
ADMIN_IDS = [1051646816]

# Bot username (paylaş linkləri üçün lazımdır; bot işə düşəndə avtomatik təyin olunur)
BOT_USERNAME = None

# ─── Monetag Ad Config ────────────────────────────────────────────────────────
# WebApp URL-lərinə #ctx=start və ya #ctx=cont fragmenti əlavə olunur ki,
# HTML hansı kontekstdə açıldığını biləsin və bota düzgün siqnal göndərsin.
AD_WEBAPP_REWARDED_URL     = "https://ibrahimibrahimliei-spec.github.io/bot/ad_rewarded.html"
AD_WEBAPP_INTERSTITIAL_URL = "https://ibrahimibrahimliei-spec.github.io/bot/ad_rewarded.html"
AD_EVERY_N_QUESTIONS = 5
AD_MIN_GAP_SECONDS = 30  # Eyni reklamın çox sıx göstərilməməsi üçün
AD_REQUIRED = True  # False edilərsə reklam izləmədən də başlamaq mümkün olur (debug üçün)

logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
log = logging.getLogger("quiz-bot")

# ─── DATA LOADING ─────────────────────────────────────────────────────────────

def load_data():
    with open(DATA_FILE, 'r', encoding='utf-8') as f:
        data = json.load(f)
    # Köhnə format dəstəyi
    if 'subjects' not in data:
        data = {
            "subjects": [{
                "id": "mm",
                "name": "Mülki Müdafiə",
                "emoji": "🛡",
                "topics": data.get('topics', []),
                "all_questions": data.get('all_questions', [])
            }]
        }
    # Hər suala unikal id təyin et (yox idisə) — DB-də referans üçün lazımdır
    next_id = 1
    seen_ids = set()
    for s in data['subjects']:
        for t in s.get('topics', []):
            for q in t.get('questions', []):
                if 'id' not in q or q['id'] in seen_ids:
                    q['id'] = next_id
                seen_ids.add(q['id'])
                next_id = max(next_id, q['id'] + 1)
        for q in s.get('all_questions', []):
            if 'id' not in q or q['id'] in seen_ids:
                q['id'] = next_id
            seen_ids.add(q['id'])
            next_id = max(next_id, q['id'] + 1)
    return data


def save_data():
    """JSON-u diskə yaz (admin yeni sual əlavə etdikdə)."""
    with open(DATA_FILE, 'w', encoding='utf-8') as f:
        json.dump(DATA, f, ensure_ascii=False, indent=2)
    # In-memory indexləri yenilə
    rebuild_question_index()


def rebuild_question_index():
    global QUESTIONS_BY_ID, SUBJECTS_BY_ID
    SUBJECTS_BY_ID = {s['id']: s for s in DATA['subjects']}
    QUESTIONS_BY_ID = {}
    for s in DATA['subjects']:
        for t in s.get('topics', []):
            for q in t.get('questions', []):
                QUESTIONS_BY_ID[q['id']] = (s['id'], q)
        for q in s.get('all_questions', []):
            if q['id'] not in QUESTIONS_BY_ID:
                QUESTIONS_BY_ID[q['id']] = (s['id'], q)


DATA = load_data()
SUBJECTS_BY_ID = {}
QUESTIONS_BY_ID = {}  # qid -> (subject_id, question_dict)
rebuild_question_index()


def get_subject(subject_id):
    return SUBJECTS_BY_ID.get(subject_id)


def subject_has_topics(subject):
    return any(len(t.get('questions', [])) > 0 for t in subject.get('topics', []))


def subject_all_questions(subject):
    if subject.get('all_questions'):
        return subject['all_questions']
    pool = []
    for t in subject.get('topics', []):
        pool.extend(t.get('questions', []))
    return pool


# Sessiyalar — istifadəçilər və qruplar üçün ayrı saxlanılır.
# Resume üçün periodic olaraq DB-yə də yaddaşa alınır.
user_sessions = {}     # chat_id -> {...}
group_sessions = {}    # chat_id (group) -> {...}
ad_signals = {}        # user_id -> {ctx, ts}  - WebApp sendData siqnalı buraya düşür
last_ad_shown = {}     # chat_id -> timestamp
range_pending = {}     # chat_id -> subject_id (istifadəçidən diapazon gözləyirik)
pdf_import_pending = {}  # user_id -> parse olunmuş suallar (fənn seçimini gözləyirik)


# ─── DATABASE ─────────────────────────────────────────────────────────────────

def get_conn():
    return sqlite3.connect(DB_FILE)


def init_db():
    conn = get_conn()
    c = conn.cursor()

    # İstifadəçilər
    c.execute('''
        CREATE TABLE IF NOT EXISTS users (
            user_id     INTEGER PRIMARY KEY,
            username    TEXT,
            full_name   TEXT,
            joined_at   TEXT,
            referrer_id INTEGER DEFAULT NULL
        )
    ''')

    # Statistika
    c.execute('''
        CREATE TABLE IF NOT EXISTS stats (
            user_id         INTEGER PRIMARY KEY,
            total_quizzes   INTEGER DEFAULT 0,
            total_correct   INTEGER DEFAULT 0,
            total_questions INTEGER DEFAULT 0,
            best_score_pct  INTEGER DEFAULT 0,
            last_played     TEXT
        )
    ''')

    # Quiz nəticələri
    c.execute('''
        CREATE TABLE IF NOT EXISTS quiz_results (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id     INTEGER,
            score       INTEGER,
            total       INTEGER,
            pct         INTEGER,
            mode        TEXT,
            topic_name  TEXT,
            played_at   TEXT
        )
    ''')

    # subject_id sütunu mövcud deyilsə əlavə et
    c.execute("PRAGMA table_info(quiz_results)")
    cols = [row[1] for row in c.fetchall()]
    if 'subject_id' not in cols:
        c.execute("ALTER TABLE quiz_results ADD COLUMN subject_id TEXT")

    # Referral
    c.execute('''
        CREATE TABLE IF NOT EXISTS referrals (
            referrer_id INTEGER,
            referred_id INTEGER PRIMARY KEY,
            created_at  TEXT
        )
    ''')

    # Hər istifadəçinin hər suala cavabı (səhv suallar rejimi + çətinlik üçün)
    c.execute('''
        CREATE TABLE IF NOT EXISTS user_question_log (
            user_id      INTEGER,
            question_id  INTEGER,
            subject_id   TEXT,
            is_correct   INTEGER,    -- 0 və ya 1
            answered_at  TEXT,
            PRIMARY KEY (user_id, question_id, answered_at)
        )
    ''')
    c.execute('CREATE INDEX IF NOT EXISTS idx_uql_user ON user_question_log(user_id)')
    c.execute('CREATE INDEX IF NOT EXISTS idx_uql_qid ON user_question_log(question_id)')

    # Yığılmış sual statistikası (çətinlik üçün — hər dəfə cavablananda update)
    c.execute('''
        CREATE TABLE IF NOT EXISTS question_stats (
            question_id  INTEGER PRIMARY KEY,
            subject_id   TEXT,
            times_shown  INTEGER DEFAULT 0,
            times_correct INTEGER DEFAULT 0
        )
    ''')

    # Favorit suallar
    c.execute('''
        CREATE TABLE IF NOT EXISTS favorites (
            user_id      INTEGER,
            question_id  INTEGER,
            added_at     TEXT,
            PRIMARY KEY (user_id, question_id)
        )
    ''')

    # Yarımçıq sessiyaları saxla (resume üçün)
    c.execute('''
        CREATE TABLE IF NOT EXISTS saved_sessions (
            user_id      INTEGER PRIMARY KEY,
            session_json TEXT,
            saved_at     TEXT
        )
    ''')

    # Sual problemləri (istifadəçi report etdikdə)
    c.execute('''
        CREATE TABLE IF NOT EXISTS question_reports (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id      INTEGER,
            question_id  INTEGER,
            note         TEXT,
            reported_at  TEXT,
            resolved     INTEGER DEFAULT 0
        )
    ''')

    conn.commit()
    conn.close()


def register_user(user_id, username, full_name, referrer_id=None):
    conn = get_conn()
    c = conn.cursor()
    c.execute('SELECT user_id FROM users WHERE user_id=?', (user_id,))
    exists = c.fetchone()
    if not exists:
        c.execute(
            'INSERT INTO users (user_id, username, full_name, joined_at, referrer_id) VALUES (?,?,?,?,?)',
            (user_id, username, full_name, datetime.now().isoformat(), referrer_id)
        )
        c.execute(
            'INSERT INTO stats (user_id, total_quizzes, total_correct, total_questions, best_score_pct, last_played) VALUES (?,0,0,0,0,?)',
            (user_id, datetime.now().isoformat())
        )
        if referrer_id:
            c.execute('SELECT user_id FROM users WHERE user_id=?', (referrer_id,))
            if c.fetchone():
                c.execute(
                    'INSERT OR IGNORE INTO referrals (referrer_id, referred_id, created_at) VALUES (?,?,?)',
                    (referrer_id, user_id, datetime.now().isoformat())
                )
        conn.commit()
    conn.close()
    return not exists


def save_quiz_result(user_id, score, total, pct, mode, topic_name, subject_id):
    conn = get_conn()
    c = conn.cursor()
    c.execute(
        'INSERT INTO quiz_results (user_id, score, total, pct, mode, topic_name, played_at, subject_id) VALUES (?,?,?,?,?,?,?,?)',
        (user_id, score, total, pct, mode, topic_name, datetime.now().isoformat(), subject_id)
    )
    c.execute('''
        UPDATE stats SET
            total_quizzes   = total_quizzes + 1,
            total_correct   = total_correct + ?,
            total_questions = total_questions + ?,
            best_score_pct  = MAX(best_score_pct, ?),
            last_played     = ?
        WHERE user_id = ?
    ''', (score, total, pct, datetime.now().isoformat(), user_id))
    conn.commit()
    conn.close()


def log_answer(user_id, question_id, subject_id, is_correct):
    """Hər cavabı log et + sualın çətinlik statistikasını güncəllə."""
    conn = get_conn()
    c = conn.cursor()
    c.execute(
        'INSERT OR IGNORE INTO user_question_log (user_id, question_id, subject_id, is_correct, answered_at) VALUES (?,?,?,?,?)',
        (user_id, question_id, subject_id, 1 if is_correct else 0, datetime.now().isoformat())
    )
    # question_stats: yoxdursa əlavə et, varsa update et
    c.execute('''
        INSERT INTO question_stats (question_id, subject_id, times_shown, times_correct)
        VALUES (?, ?, 1, ?)
        ON CONFLICT(question_id) DO UPDATE SET
            times_shown   = times_shown + 1,
            times_correct = times_correct + ?
    ''', (question_id, subject_id, 1 if is_correct else 0, 1 if is_correct else 0))
    conn.commit()
    conn.close()


def get_user_stats(user_id):
    conn = get_conn()
    c = conn.cursor()
    c.execute('SELECT * FROM users WHERE user_id=?', (user_id,))
    user = c.fetchone()
    c.execute('SELECT * FROM stats WHERE user_id=?', (user_id,))
    stats = c.fetchone()
    c.execute('SELECT COUNT(*) FROM referrals WHERE referrer_id=?', (user_id,))
    ref_count = c.fetchone()[0]
    conn.close()
    return user, stats, ref_count


def get_leaderboard(limit=10, subject_id=None):
    conn = get_conn()
    c = conn.cursor()
    if subject_id:
        # Fənn üzrə liderboard: yalnız o fənnin nəticələrindən hesabla
        c.execute('''
            SELECT u.full_name, u.username,
                   MAX(q.pct) as best_pct,
                   COUNT(q.id) as quizzes,
                   SUM(q.score) as total_correct,
                   SUM(q.total) as total_q
            FROM quiz_results q
            JOIN users u ON q.user_id = u.user_id
            WHERE q.subject_id = ?
            GROUP BY q.user_id
            ORDER BY best_pct DESC, total_correct DESC
            LIMIT ?
        ''', (subject_id, limit))
    else:
        c.execute('''
            SELECT u.full_name, u.username, s.best_score_pct, s.total_quizzes, s.total_correct, s.total_questions
            FROM stats s
            JOIN users u ON s.user_id = u.user_id
            WHERE s.total_quizzes > 0
            ORDER BY s.best_score_pct DESC, s.total_correct DESC
            LIMIT ?
        ''', (limit,))
    rows = c.fetchall()
    conn.close()
    return rows


def get_all_user_ids():
    conn = get_conn()
    c = conn.cursor()
    c.execute('SELECT user_id FROM users')
    rows = [r[0] for r in c.fetchall()]
    conn.close()
    return rows


# ─── Səhv suallar ─────────────────────────────────────────────────────────────

def get_wrong_questions(user_id, subject_id=None, limit=50):
    """İstifadəçinin son cavabı SƏHV olan suallarını qaytarır."""
    conn = get_conn()
    c = conn.cursor()
    # Hər sual üçün sonuncu cavabı al; əgər sonuncu cavab səhvdirsə daxil et
    sql = '''
        SELECT question_id FROM (
            SELECT question_id, is_correct,
                   ROW_NUMBER() OVER (PARTITION BY question_id ORDER BY answered_at DESC) as rn
            FROM user_question_log
            WHERE user_id = ? {subject_filter}
        ) WHERE rn = 1 AND is_correct = 0
        LIMIT ?
    '''
    if subject_id:
        sql = sql.format(subject_filter="AND subject_id = ?")
        c.execute(sql, (user_id, subject_id, limit))
    else:
        sql = sql.format(subject_filter="")
        c.execute(sql, (user_id, limit))
    qids = [r[0] for r in c.fetchall()]
    conn.close()
    questions = []
    for qid in qids:
        if qid in QUESTIONS_BY_ID:
            sid, q = QUESTIONS_BY_ID[qid]
            questions.append(q)
    return questions


def count_wrong_questions(user_id, subject_id=None):
    return len(get_wrong_questions(user_id, subject_id, limit=10000))


# ─── Favoritlər ───────────────────────────────────────────────────────────────

def add_favorite(user_id, question_id):
    conn = get_conn()
    c = conn.cursor()
    c.execute('INSERT OR IGNORE INTO favorites (user_id, question_id, added_at) VALUES (?,?,?)',
              (user_id, question_id, datetime.now().isoformat()))
    conn.commit()
    conn.close()


def remove_favorite(user_id, question_id):
    conn = get_conn()
    c = conn.cursor()
    c.execute('DELETE FROM favorites WHERE user_id=? AND question_id=?', (user_id, question_id))
    conn.commit()
    conn.close()


def is_favorite(user_id, question_id):
    conn = get_conn()
    c = conn.cursor()
    c.execute('SELECT 1 FROM favorites WHERE user_id=? AND question_id=?', (user_id, question_id))
    r = c.fetchone()
    conn.close()
    return bool(r)


def get_favorites(user_id, subject_id=None):
    conn = get_conn()
    c = conn.cursor()
    if subject_id:
        c.execute('SELECT question_id FROM favorites WHERE user_id=? ORDER BY added_at DESC', (user_id,))
    else:
        c.execute('SELECT question_id FROM favorites WHERE user_id=? ORDER BY added_at DESC', (user_id,))
    qids = [r[0] for r in c.fetchall()]
    conn.close()
    questions = []
    for qid in qids:
        if qid in QUESTIONS_BY_ID:
            sid, q = QUESTIONS_BY_ID[qid]
            if subject_id and sid != subject_id:
                continue
            questions.append(q)
    return questions


def count_favorites(user_id, subject_id=None):
    return len(get_favorites(user_id, subject_id))


# ─── Çətinlik statistikası ────────────────────────────────────────────────────

def get_hardest_questions(subject_id=None, limit=10, min_shown=5):
    """Ən çətin suallar — düzgün cavab faizi ən aşağı olanlar."""
    conn = get_conn()
    c = conn.cursor()
    if subject_id:
        c.execute('''
            SELECT question_id, times_shown, times_correct,
                   CAST(times_correct AS REAL) / times_shown as pct
            FROM question_stats
            WHERE times_shown >= ? AND subject_id = ?
            ORDER BY pct ASC, times_shown DESC
            LIMIT ?
        ''', (min_shown, subject_id, limit))
    else:
        c.execute('''
            SELECT question_id, times_shown, times_correct,
                   CAST(times_correct AS REAL) / times_shown as pct
            FROM question_stats
            WHERE times_shown >= ?
            ORDER BY pct ASC, times_shown DESC
            LIMIT ?
        ''', (min_shown, limit))
    rows = c.fetchall()
    conn.close()
    return rows


def get_question_difficulty(question_id):
    """Sualın düzgün cavab faizini qaytarır (None - kifayət qədər data yoxdur)."""
    conn = get_conn()
    c = conn.cursor()
    c.execute('SELECT times_shown, times_correct FROM question_stats WHERE question_id=?', (question_id,))
    r = c.fetchone()
    conn.close()
    if not r or r[0] < 3:
        return None
    return round(100 * r[1] / r[0])


# ─── Resume — yarımçıq sessiyaları saxla / yüklə ─────────────────────────────

def save_session_to_db(user_id, session):
    """Sessiyanı serializə edib DB-də saxla."""
    if not session or not session.get('questions'):
        return
    # questions list-ində "id" istifadə olunur — referans olaraq saxlamaq kifayətdir
    payload = {
        'question_ids': [q.get('id') for q in session['questions']],
        'current': session.get('current', 0),
        'score': session.get('score', 0),
        'wrong': session.get('wrong', 0),
        'mode': session.get('mode'),
        'subject_id': session.get('subject_id'),
        'subject_name': session.get('subject_name'),
        'topic_name': session.get('topic_name'),
    }
    conn = get_conn()
    c = conn.cursor()
    c.execute('INSERT OR REPLACE INTO saved_sessions (user_id, session_json, saved_at) VALUES (?,?,?)',
              (user_id, json.dumps(payload, ensure_ascii=False), datetime.now().isoformat()))
    conn.commit()
    conn.close()


def load_saved_session(user_id):
    conn = get_conn()
    c = conn.cursor()
    c.execute('SELECT session_json FROM saved_sessions WHERE user_id=?', (user_id,))
    r = c.fetchone()
    conn.close()
    if not r:
        return None
    try:
        payload = json.loads(r[0])
        # ID-lərdən sual obyektlərini bərpa et
        questions = []
        for qid in payload['question_ids']:
            if qid in QUESTIONS_BY_ID:
                questions.append(QUESTIONS_BY_ID[qid][1])
        if not questions:
            return None
        return {
            'questions': questions,
            'current': payload.get('current', 0),
            'score': payload.get('score', 0),
            'wrong': payload.get('wrong', 0),
            'mode': payload.get('mode'),
            'subject_id': payload.get('subject_id'),
            'subject_name': payload.get('subject_name'),
            'topic_name': payload.get('topic_name'),
            'user_id': user_id,
        }
    except Exception as e:
        log.warning(f"Saved session parse failed for {user_id}: {e}")
        return None


def clear_saved_session(user_id):
    conn = get_conn()
    c = conn.cursor()
    c.execute('DELETE FROM saved_sessions WHERE user_id=?', (user_id,))
    conn.commit()
    conn.close()


# ─── Reklam göstər (WebApp sendData ilə yoxlanılır) ──────────────────────────
#
# WebApp HTML reklam tamamlananda tg.sendData(JSON) çağırır. Bu, bot tərəfdə
# MessageHandler(Filters.status_update.web_app_data) ilə tutulur və ad_signals
# dict-inə yazılır. Bot davam etmək üçün BU SİQNALI gözləyir — manual düymə
# silinib, beləliklə kimsə reklam izləmədən keçə bilməz.

def show_rewarded_ad(chat_id, context: CallbackContext, after_ad_callback: str):
    """Start sonrası reklam — ana menyuya keçidi açır."""
    if not AD_REQUIRED:
        # Debug rejimi: birbaşa keç
        if after_ad_callback == "ad_done_start":
            show_subject_menu(chat_id, context)
        elif after_ad_callback == "ad_done_continue":
            send_next_question(chat_id, context)
        return

    url = f"{AD_WEBAPP_REWARDED_URL}#ctx=start"
    # ⚠️ VACİB: sendData() yalnız ReplyKeyboardMarkup-dakı KeyboardButton-dan
    # işləyir, InlineKeyboardButton-dan YOX. Bu Telegram limitidir.
    keyboard = ReplyKeyboardMarkup(
        [[KeyboardButton(text="📢 Reklamı izlə (Testə başla)", web_app=WebAppInfo(url=url))]],
        resize_keyboard=True,
        one_time_keyboard=True
    )
    msg = context.bot.send_message(
        chat_id=chat_id,
        text=(
            "🎯 *Testə başlamaq üçün qısa reklam izləyin*\n\n"
            "Aşağıdakı düyməyə basın → Reklamı izləyin → Avtomatik bota qayıdacaqsınız."
        ),
        parse_mode='Markdown',
        reply_markup=keyboard
    )
    if chat_id not in user_sessions:
        user_sessions[chat_id] = {}
    user_sessions[chat_id]['_ad_msg_id'] = msg.message_id


def show_interstitial_ad(chat_id, context: CallbackContext):
    """Test arası reklam — növbəti suala keçidi açır."""
    if not AD_REQUIRED:
        send_next_question(chat_id, context)
        return

    now = time.time()
    last = last_ad_shown.get(chat_id, 0)
    if now - last < AD_MIN_GAP_SECONDS:
        send_next_question(chat_id, context)
        return

    url = f"{AD_WEBAPP_REWARDED_URL}#ctx=cont"
    keyboard = ReplyKeyboardMarkup(
        [[KeyboardButton(text="⏱ Reklamı izlə (Davam et)", web_app=WebAppInfo(url=url))]],
        resize_keyboard=True,
        one_time_keyboard=True
    )
    msg = context.bot.send_message(
        chat_id=chat_id,
        text=(
            "📢 *Qısa fasilə*\n\n"
            "Növbəti suala keçmək üçün reklamı izləyin."
        ),
        parse_mode='Markdown',
        reply_markup=keyboard
    )
    if chat_id not in user_sessions:
        user_sessions[chat_id] = {}
    user_sessions[chat_id]['_ad_msg_id'] = msg.message_id
    last_ad_shown[chat_id] = now


def web_app_data_handler(update: Update, context: CallbackContext):
    """WebApp-dən gələn sendData() siqnalını qəbul et."""
    if not update.effective_message or not update.effective_message.web_app_data:
        return
    user = update.effective_user
    chat_id = update.effective_chat.id
    raw = update.effective_message.web_app_data.data

    try:
        payload = json.loads(raw)
    except Exception:
        log.warning(f"WebApp data parse failed: {raw[:100]}")
        return

    if payload.get('type') != 'ad_done':
        return

    ctx_kind = payload.get('ctx', 'start')
    log.info(f"Ad signal received: user={user.id} ctx={ctx_kind} reason={payload.get('reason')}")

    # Reklam mesajını sil
    sess = user_sessions.get(chat_id, {})
    ad_msg_id = sess.get('_ad_msg_id')
    if ad_msg_id:
        try:
            context.bot.delete_message(chat_id=chat_id, message_id=ad_msg_id)
        except Exception:
            pass
        sess.pop('_ad_msg_id', None)

    # WebApp data mesajının özünü də sil
    try:
        update.effective_message.delete()
    except Exception:
        pass

    # Reply keyboard-u gizlət (görünməz dummy mesaj göndərib dərhal sil)
    try:
        dummy = context.bot.send_message(
            chat_id=chat_id,
            text="✅",
            reply_markup=ReplyKeyboardRemove()
        )
        try:
            context.bot.delete_message(chat_id=chat_id, message_id=dummy.message_id)
        except Exception:
            pass
    except Exception:
        pass

    if ctx_kind == 'cont':
        send_next_question(chat_id, context)
    else:
        show_subject_menu(chat_id, context)


# ─── Mesaj idarəçiliyi (köhnə sual mesajını sil) ─────────────────────────────
#
# Yeni sual göstəriləndə əvvəlki sual mesajını silirik ki, ekranda qarışıqlıq
# olmasın. Sessiyaya '_q_msg_id' yazırıq və hər yeni sualdan əvvəl onu silirik.

def delete_prev_question_msg(chat_id, context):
    sess = user_sessions.get(chat_id)
    if not sess:
        return
    prev = sess.get('_q_msg_id')
    if prev:
        try:
            context.bot.delete_message(chat_id=chat_id, message_id=prev)
        except Exception:
            pass
        sess['_q_msg_id'] = None


# ─── /start ───────────────────────────────────────────────────────────────────

def start(update: Update, context: CallbackContext):
    user = update.message.from_user
    chat_id = update.message.chat_id

    referrer_id = None
    if context.args:
        try:
            arg = context.args[0]
            if arg.startswith("ref_"):
                referrer_id = int(arg.split("_")[1])
                if referrer_id == user.id:
                    referrer_id = None
        except (ValueError, IndexError):
            pass

    full_name = (user.first_name or "") + (" " + user.last_name if user.last_name else "")
    is_new = register_user(user.id, user.username or "", full_name.strip(), referrer_id)

    if is_new and referrer_id:
        try:
            context.bot.send_message(
                chat_id=referrer_id,
                text=(
                    f"🎉 *Təbriklər!*\n\n"
                    f"*{full_name}* sizin dəvətinizlə bota qoşuldu! 👥\n"
                    f"Referral sayınız artdı. /profile ilə yoxlaya bilərsiniz."
                ),
                parse_mode='Markdown'
            )
        except Exception:
            pass

    # Yarımçıq sessiya varsa, davam etmək təklif et
    saved = load_saved_session(user.id)
    if saved and saved.get('current', 0) < len(saved.get('questions', [])):
        offer_resume(chat_id, context, user.id, saved)
        return

    show_rewarded_ad(chat_id, context, after_ad_callback="ad_done_start")


def offer_resume(chat_id, context, user_id, saved):
    remaining = len(saved['questions']) - saved.get('current', 0)
    text = (
        f"⏸ *Yarımçıq testin var!*\n\n"
        f"📖 {saved.get('topic_name', 'Sınaq')}\n"
        f"✅ Düz: {saved.get('score', 0)}  ❌ Səhv: {saved.get('wrong', 0)}\n"
        f"📝 Qalan: {remaining} sual\n\n"
        f"Davam etmək istəyirsən?"
    )
    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("▶️ Davam et",     callback_data="resume_yes"),
         InlineKeyboardButton("🗑 Yox, sil",      callback_data="resume_no")]
    ])
    context.bot.send_message(chat_id=chat_id, text=text, parse_mode='Markdown', reply_markup=keyboard)


# ─── Ana menyu (fənn seçimi) ─────────────────────────────────────────────────

def show_subject_menu(chat_id, context: CallbackContext, edit_query=None):
    keyboard = []
    for s in DATA['subjects']:
        if s.get('hidden'):  # Gizli fənnlər istifadəçilərə göstərilmir
            continue
        total_q = len(subject_all_questions(s))
        label = f"{s.get('emoji', '📘')} {s['name']}"
        if len(label) > 45:
            label = label[:42] + "…"
        btn_text = f"{label} ({total_q} sual)" if total_q else f"{label} (boş)"
        keyboard.append([InlineKeyboardButton(btn_text, callback_data=f"subj_{s['id']}")])

    keyboard.append([
        InlineKeyboardButton("⭐ Favoritlərim",    callback_data="menu_favs"),
        InlineKeyboardButton("📝 Səhv suallarım",  callback_data="menu_wrong"),
    ])
    keyboard.append([
        InlineKeyboardButton("📊 Liderboard", callback_data="menu_leaderboard"),
        InlineKeyboardButton("👤 Profilim",   callback_data="menu_profile"),
    ])
    keyboard.append([InlineKeyboardButton("📢 Dost dəvət et", callback_data="menu_referral")])

    text = "🎓 *Test Botu*\n\n" + ("Fənni seçin:" if len(DATA['subjects']) > 1 else "Hazırsansa, başlayaq:")

    if edit_query is not None:
        try:
            edit_query.edit_message_text(text=text, parse_mode='Markdown',
                                          reply_markup=InlineKeyboardMarkup(keyboard))
            return
        except Exception:
            pass
    context.bot.send_message(chat_id=chat_id, text=text, parse_mode='Markdown',
                             reply_markup=InlineKeyboardMarkup(keyboard))


# ─── Fənn üzrə alt menyu (mövzu / ümumi / paylaş və s.) ──────────────────────

def show_subject_mode_menu(query, context: CallbackContext, subject_id):
    subject = get_subject(subject_id)
    if not subject:
        query.edit_message_text("❌ Fənn tapılmadı.")
        return

    user_id = query.from_user.id
    total_q   = len(subject_all_questions(subject))
    has_topics = subject_has_topics(subject)
    fav_n   = count_favorites(user_id, subject_id)
    wrong_n = count_wrong_questions(user_id, subject_id)

    if total_q == 0:
        text = f"{subject.get('emoji', '📘')} *{subject['name']}*\n\n⚠️ Bu fənnə hələ sual əlavə olunmayıb."
        keyboard = [[InlineKeyboardButton("⬅️ Geri", callback_data="back_subjects")]]
        query.edit_message_text(text=text, parse_mode='Markdown',
                                reply_markup=InlineKeyboardMarkup(keyboard))
        return

    keyboard = []
    if has_topics:
        keyboard.append([InlineKeyboardButton("📚 Mövzuya görə sınaq",
                                               callback_data=f"topicmenu_{subject_id}")])
    keyboard.append([InlineKeyboardButton("🎲 Ümumi sınaq",
                                           callback_data=f"countmenu_{subject_id}")])

    extras = []
    if fav_n > 0:
        extras.append(InlineKeyboardButton(f"⭐ Favoritlər ({fav_n})",
                                           callback_data=f"startfavs_{subject_id}"))
    if wrong_n > 0:
        extras.append(InlineKeyboardButton(f"📝 Səhv suallar ({wrong_n})",
                                           callback_data=f"startwrong_{subject_id}"))
    if extras:
        keyboard.append(extras)

    keyboard.append([InlineKeyboardButton("⬅️ Geri (fənnlər)", callback_data="back_subjects")])

    text = (
        f"{subject.get('emoji', '📘')} *{subject['name']}*\n"
        f"📝 Toplam sual: *{total_q}*\n\n"
        f"Sınaq növünü seçin:"
    )
    query.edit_message_text(text=text, parse_mode='Markdown',
                            reply_markup=InlineKeyboardMarkup(keyboard))


# ─── Mövzu menyusu ────────────────────────────────────────────────────────────

def show_topic_menu(query, context: CallbackContext, subject_id):
    subject = get_subject(subject_id)
    if not subject:
        query.edit_message_text("❌ Fənn tapılmadı.")
        return

    keyboard = []
    for i, topic in enumerate(subject.get('topics', [])):
        q_count = len(topic.get('questions', []))
        if q_count == 0:
            label = f"📖 Mövzu {topic['num']}: {topic['name'][:30]}… (boş)"
            cb = f"topicempty_{subject_id}_{i}"
        else:
            label = f"📖 Mövzu {topic['num']}: {topic['name'][:30]}… ({q_count})"
            cb = f"topic_{subject_id}_{i}"
        keyboard.append([InlineKeyboardButton(label, callback_data=cb)])
    keyboard.append([InlineKeyboardButton("⬅️ Geri", callback_data=f"subj_{subject_id}")])

    query.edit_message_text(
        text=f"{subject.get('emoji', '📘')} *{subject['name']}*\n\n📚 Mövzu seçin:",
        parse_mode='Markdown',
        reply_markup=InlineKeyboardMarkup(keyboard)
    )


# ─── Ümumi sınaq — sual sayı seçimi ──────────────────────────────────────────

def ask_question_count(query, context: CallbackContext, subject_id):
    subject = get_subject(subject_id)
    if not subject:
        return
    total_q = len(subject_all_questions(subject))
    if total_q == 0:
        query.edit_message_text(
            f"⚠️ Bu fənnə hələ sual əlavə olunmayıb.",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Geri", callback_data=f"subj_{subject_id}")]])
        )
        return

    standard_counts = [c for c in [5, 10, 20, 30, 50, 100] if c <= total_q]
    rows = []
    row = []
    for cnt in standard_counts:
        row.append(InlineKeyboardButton(str(cnt), callback_data=f"count_{subject_id}_{cnt}"))
        if len(row) == 3:
            rows.append(row)
            row = []
    row.append(InlineKeyboardButton(f"Hamısı ({total_q})", callback_data=f"count_{subject_id}_{total_q}"))
    rows.append(row)
    # Ardıcıl diapazon
    rows.append([InlineKeyboardButton("🎯 Ardıcıl diapazon (məs: 20-40)", callback_data=f"range_{subject_id}")])
    rows.append([InlineKeyboardButton("⬅️ Geri", callback_data=f"subj_{subject_id}")])

    query.edit_message_text(
        text=(
            f"{subject.get('emoji', '📘')} *{subject['name']}*\n"
            f"🎲 *Ümumi sınaq*\n\n"
            f"Neçə sual istəyirsiniz?\n"
            f"(və ya 🎯 ilə ardıcıl diapazon seçin)"
        ),
        parse_mode='Markdown',
        reply_markup=InlineKeyboardMarkup(rows)
    )


# ─── Quiz başlatma ────────────────────────────────────────────────────────────

def start_topic_quiz(query, context: CallbackContext, subject_id, topic_idx):
    chat_id = query.message.chat_id
    subject = get_subject(subject_id)
    if not subject:
        return
    topics = subject.get('topics', [])
    if topic_idx < 0 or topic_idx >= len(topics):
        return
    topic = topics[topic_idx]
    questions = list(topic.get('questions', []))
    if not questions:
        query.answer("⚠️ Bu mövzu boşdur.", show_alert=True)
        return
    random.shuffle(questions)
    user_sessions[chat_id] = {
        'questions': questions,
        'current': 0,
        'score': 0,
        'wrong': 0,
        'mode': 'topic',
        'subject_id': subject_id,
        'subject_name': subject['name'],
        'topic_name': f"{subject['name']} — Mövzu {topic['num']}: {topic['name']}",
        'user_id': query.from_user.id
    }
    try: query.message.delete()
    except: pass
    send_next_question(chat_id, context)


def start_general_quiz(query, context: CallbackContext, subject_id, count):
    chat_id = query.message.chat_id
    subject = get_subject(subject_id)
    if not subject:
        return
    pool = list(subject_all_questions(subject))
    if not pool:
        return
    random.shuffle(pool)
    count = max(1, min(count, len(pool)))
    questions = pool[:count]
    user_sessions[chat_id] = {
        'questions': questions,
        'current': 0,
        'score': 0,
        'wrong': 0,
        'mode': 'general',
        'subject_id': subject_id,
        'subject_name': subject['name'],
        'topic_name': f"{subject['name']} — Ümumi Sınaq",
        'user_id': query.from_user.id
    }
    try: query.message.delete()
    except: pass
    send_next_question(chat_id, context)


def start_range_quiz(chat_id, context, subject_id, start_id, end_id, user_id):
    """
    ID diapazonuna görə ardıcıl sınaq.
    start_id/end_id ADİAK üçün sualın nömrəsidir (1-703).
    Suallar ID sırasına görə ardıcıl verilir (qarışdırılmır).
    """
    subject = get_subject(subject_id)
    if not subject:
        return False
    pool = subject_all_questions(subject)
    if not pool:
        return False

    # ID sırasına görə sırala və diapazona uyğun olanları götür
    selected = sorted(
        [q for q in pool if start_id <= q.get('id', 0) <= end_id],
        key=lambda q: q.get('id', 0)
    )
    if not selected:
        return False

    user_sessions[chat_id] = {
        'questions': selected,
        'current': 0,
        'score': 0,
        'wrong': 0,
        'mode': 'range',
        'subject_id': subject_id,
        'subject_name': subject['name'],
        'topic_name': f"{subject['name']} — Suallar {start_id}-{end_id}",
        'user_id': user_id
    }
    send_next_question(chat_id, context)
    return True


def start_wrong_quiz(query, context, subject_id):
    """Səhv suallar rejimi."""
    chat_id = query.message.chat_id
    user_id = query.from_user.id
    questions = get_wrong_questions(user_id, subject_id, limit=100)
    if not questions:
        query.answer("✅ Heç səhv sualın yoxdur!", show_alert=True)
        return
    random.shuffle(questions)
    subject = get_subject(subject_id)
    user_sessions[chat_id] = {
        'questions': questions,
        'current': 0,
        'score': 0,
        'wrong': 0,
        'mode': 'wrong_review',
        'subject_id': subject_id,
        'subject_name': subject['name'] if subject else '',
        'topic_name': f"{subject['name'] if subject else ''} — Səhv suallar təkrarı",
        'user_id': user_id
    }
    try: query.message.delete()
    except: pass
    send_next_question(chat_id, context)


def start_favs_quiz(query, context, subject_id):
    """Favoritlər rejimi."""
    chat_id = query.message.chat_id
    user_id = query.from_user.id
    questions = get_favorites(user_id, subject_id)
    if not questions:
        query.answer("⭐ Heç favoritin yoxdur.", show_alert=True)
        return
    random.shuffle(questions)
    subject = get_subject(subject_id)
    user_sessions[chat_id] = {
        'questions': questions,
        'current': 0,
        'score': 0,
        'wrong': 0,
        'mode': 'favorites',
        'subject_id': subject_id,
        'subject_name': subject['name'] if subject else '',
        'topic_name': f"{subject['name'] if subject else ''} — Favoritlər",
        'user_id': user_id
    }
    try: query.message.delete()
    except: pass
    send_next_question(chat_id, context)


# ─── Sual göndərmə (əvvəlki mesaj silinir) ───────────────────────────────────

def send_next_question(chat_id, context: CallbackContext):
    session = user_sessions.get(chat_id)
    if not session:
        show_subject_menu(chat_id, context)
        return

    # Əvvəlki sual mesajını sil
    delete_prev_question_msg(chat_id, context)

    idx = session['current']
    total = len(session['questions'])
    if idx >= total:
        show_result(chat_id, context)
        return

    q = session['questions'][idx]
    answers = list(q['answers'])
    random.shuffle(answers)
    session['shuffled_answers'] = answers

    labels = ['🅰', '🅱', '🇨', '🇩', '🇪']
    keyboard = []
    for i, ans in enumerate(answers):
        label = labels[i] if i < len(labels) else f"{i+1}."
        short = ans[:40] + ('…' if len(ans) > 40 else '')
        keyboard.append([InlineKeyboardButton(f"{label} {short}", callback_data=f"ans_{i}")])

    progress   = f"❓ Sual {idx+1}/{total}"
    score_line = f"✅ {session['score']}  ❌ {session['wrong']}"
    options_text = "\n".join(
        f"{labels[i] if i < len(labels) else str(i+1)} {ans}"
        for i, ans in enumerate(answers)
    )

    # Çətinlik göstərici (varsa)
    diff = get_question_difficulty(q.get('id', -1))
    diff_text = ""
    if diff is not None:
        if diff < 40:   diff_text = f"  🔴 Çətin ({diff}%)"
        elif diff < 70: diff_text = f"  🟡 Orta ({diff}%)"
        else:           diff_text = f"  🟢 Asan ({diff}%)"

    text = (
        f"{progress}  |  {score_line}{diff_text}\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"*{q['q']}*\n\n"
        f"{options_text}"
    )
    msg = context.bot.send_message(
        chat_id=chat_id,
        text=text,
        parse_mode='Markdown',
        reply_markup=InlineKeyboardMarkup(keyboard)
    )
    session['_q_msg_id'] = msg.message_id

    # Hər 3 sualdan bir sessiyanı DB-yə yaz (resume üçün)
    if session.get('user_id') and (idx % 3 == 0):
        save_session_to_db(session['user_id'], session)


# ─── Cavab idarəsi ────────────────────────────────────────────────────────────

def handle_answer(query, context: CallbackContext):
    chat_id = query.message.chat_id
    session = user_sessions.get(chat_id)
    if not session:
        return

    idx = session['current']
    q = session['questions'][idx]
    chosen_idx = int(query.data.split("_")[1])
    answers = session.get('shuffled_answers', q['answers'])
    chosen  = answers[chosen_idx]
    correct = q['correct']
    qid = q.get('id')
    user_id = session.get('user_id', query.from_user.id)
    subject_id = session.get('subject_id')

    labels = ['🅰', '🅱', '🇨', '🇩', '🇪']
    is_correct = (chosen == correct)
    if is_correct:
        session['score'] += 1
        result_icon = "✅"
        result_text = "Düzgün cavab!"
    else:
        session['wrong'] += 1
        result_icon = "❌"
        result_text = f"Səhv cavab!\n✅ Düzgün: *{correct}*"

    # DB-də cavabı log et (səhv suallar + çətinlik üçün)
    if qid is not None:
        log_answer(user_id, qid, subject_id, is_correct)

    session['current'] += 1
    total     = len(session['questions'])
    remaining = total - session['current']
    last_question = session['current'] >= total

    # Naviqasiya düymələri
    nav_row = []
    if last_question:
        nav_row.append(InlineKeyboardButton("📊 Nəticə", callback_data="finish"))
    else:
        nav_row.append(InlineKeyboardButton(f"▶️ Növbəti ({remaining} qaldı)", callback_data="next"))

    # Favorit düyməsi
    if qid is not None:
        if is_favorite(user_id, qid):
            nav_row.append(InlineKeyboardButton("⭐ Favoritdən sil", callback_data=f"unfav_{qid}"))
        else:
            nav_row.append(InlineKeyboardButton("☆ Favorit əlavə et", callback_data=f"fav_{qid}"))

    # Report düyməsi (sualda problem varsa)
    if qid is not None:
        nav_row2 = [InlineKeyboardButton("🚩 Sualı şikayət et", callback_data=f"report_{qid}")]
    else:
        nav_row2 = []

    options_text = "\n".join(
        f"{labels[i] if i < len(labels) else str(i+1)} {ans}"
        for i, ans in enumerate(answers)
    )
    progress   = f"❓ Sual {idx+1}/{total}"
    score_line = f"✅ {session['score']}  ❌ {session['wrong']}"
    text = (
        f"{progress}  |  {score_line}\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"*{q['q']}*\n\n"
        f"{options_text}\n\n"
        f"{result_icon} *{result_text}*"
    )
    keyboard_rows = [nav_row]
    if nav_row2:
        keyboard_rows.append(nav_row2)
    query.edit_message_text(
        text=text,
        parse_mode='Markdown',
        reply_markup=InlineKeyboardMarkup(keyboard_rows)
    )


# ─── Nəticə ───────────────────────────────────────────────────────────────────

def show_result(chat_id, context: CallbackContext):
    delete_prev_question_msg(chat_id, context)

    session = user_sessions.get(chat_id, {})
    score       = session.get('score', 0)
    wrong       = session.get('wrong', 0)
    total       = len(session.get('questions', []))
    topic_name  = session.get('topic_name', '')
    mode        = session.get('mode', 'general')
    subject_id  = session.get('subject_id', '')
    user_id     = session.get('user_id', chat_id)

    pct = round(score / total * 100) if total > 0 else 0

    save_quiz_result(user_id, score, total, pct, mode, topic_name, subject_id)
    clear_saved_session(user_id)

    if pct >= 90:   grade = "🏆 Əla!"
    elif pct >= 75: grade = "👍 Yaxşı"
    elif pct >= 50: grade = "😐 Orta"
    else:           grade = "😞 Zəif"

    bar_filled = round(pct / 10)
    bar = "🟩" * bar_filled + "⬜" * (10 - bar_filled)

    rows = get_leaderboard(100)
    rank = next((i+1 for i, r in enumerate(rows) if r[2] <= pct), None)
    rank_text = f"\n🏅 Liderboard sıranız: *#{rank}*" if rank else ""

    text = (
        f"📊 *Sınaq Nəticəsi*\n"
        f"📖 {topic_name}\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"✅ Düzgün: *{score}*\n"
        f"❌ Səhv: *{wrong}*\n"
        f"📝 Cəmi: *{total}*\n\n"
        f"{bar}\n"
        f"Nəticə: *{pct}%* — {grade}"
        f"{rank_text}"
    )

    # Paylaş URL — Telegram share link
    share_text = (
        f"🎓 {topic_name}\n"
        f"📊 Nəticəm: {score}/{total} ({pct}%) — {grade}\n\n"
        f"Sən də sına!"
    )
    bot_link = f"https://t.me/{BOT_USERNAME}" if BOT_USERNAME else "https://t.me/"
    share_url = f"https://t.me/share/url?url={urllib.parse.quote(bot_link)}&text={urllib.parse.quote(share_text)}"

    buttons = []
    if subject_id:
        buttons.append(InlineKeyboardButton("🔄 Yenidən", callback_data=f"subj_{subject_id}"))
    buttons.append(InlineKeyboardButton("🏠 Ana menyu", callback_data="back_subjects"))

    keyboard = [
        buttons,
        [InlineKeyboardButton("📤 Paylaş", url=share_url),
         InlineKeyboardButton("📊 Liderboard", callback_data="menu_leaderboard")]
    ]

    context.bot.send_message(
        chat_id=chat_id,
        text=text,
        parse_mode='Markdown',
        reply_markup=InlineKeyboardMarkup(keyboard)
    )

    if chat_id in user_sessions:
        del user_sessions[chat_id]


# ─── Callback router ──────────────────────────────────────────────────────────

def callback_handler(update: Update, context: CallbackContext):
    query = update.callback_query
    query.answer()
    data = query.data
    chat_id = query.message.chat_id
    user = query.from_user

    full_name = (user.first_name or "") + (" " + user.last_name if user.last_name else "")
    register_user(user.id, user.username or "", full_name.strip())

    # Köhnə (artıq istifadə edilməyən) "ad_done_*" callback-ləri:
    # WebApp sendData ilə əvəzlənib, lakin debug rejimi üçün köməkçi qalır
    if data == "ad_done_start":
        try: query.message.delete()
        except: pass
        show_subject_menu(chat_id, context)
        return
    if data == "ad_done_continue":
        try: query.message.delete()
        except: pass
        send_next_question(chat_id, context)
        return

    # Resume idarəsi
    if data == "resume_yes":
        saved = load_saved_session(user.id)
        if not saved:
            try: query.message.delete()
            except: pass
            show_rewarded_ad(chat_id, context, "ad_done_start")
            return
        user_sessions[chat_id] = saved
        try: query.message.delete()
        except: pass
        send_next_question(chat_id, context)
        return
    if data == "resume_no":
        clear_saved_session(user.id)
        try: query.message.delete()
        except: pass
        show_rewarded_ad(chat_id, context, "ad_done_start")
        return

    if data == "back_subjects":
        try: query.message.delete()
        except: pass
        show_subject_menu(chat_id, context)
        return

    if data == "menu_leaderboard":
        show_leaderboard(query, context)
        return
    if data == "menu_profile":
        show_profile(query, context)
        return
    if data == "menu_referral":
        show_referral(query, context, user.id)
        return
    if data == "menu_favs":
        show_favorites_menu(query, context, user.id)
        return
    if data == "menu_wrong":
        show_wrong_menu(query, context, user.id)
        return

    # Liderboard fənn üzrə filter
    if data.startswith("lbsubj_"):
        sid = data[len("lbsubj_"):]
        show_leaderboard(query, context, subject_id=(None if sid == "all" else sid))
        return

    if data.startswith("subj_"):
        show_subject_mode_menu(query, context, data[len("subj_"):])
        return

    if data.startswith("topicmenu_"):
        show_topic_menu(query, context, data[len("topicmenu_"):])
        return

    if data.startswith("countmenu_"):
        ask_question_count(query, context, data[len("countmenu_"):])
        return

    if data.startswith("startwrong_"):
        start_wrong_quiz(query, context, data[len("startwrong_"):])
        return

    if data.startswith("startfavs_"):
        start_favs_quiz(query, context, data[len("startfavs_"):])
        return

    if data.startswith("topic_"):
        payload = data[len("topic_"):]
        rsplit = payload.rsplit("_", 1)
        if len(rsplit) != 2:
            return
        sid, idx_str = rsplit
        try:
            topic_idx = int(idx_str)
        except ValueError:
            return
        start_topic_quiz(query, context, sid, topic_idx)
        return

    if data.startswith("topicempty_"):
        query.answer("⚠️ Bu mövzu boşdur.", show_alert=True)
        return

    if data.startswith("range_"):
        sid = data[len("range_"):]
        subject = get_subject(sid)
        if not subject:
            return
        # Diapazon aralığını hesabla
        pool = subject_all_questions(subject)
        if not pool:
            return
        ids = [q.get('id', 0) for q in pool if q.get('id')]
        min_id = min(ids) if ids else 1
        max_id = max(ids) if ids else 1

        range_pending[chat_id] = sid
        try: query.message.delete()
        except: pass
        context.bot.send_message(
            chat_id=chat_id,
            text=(
                f"🎯 *Ardıcıl Diapazon*\n\n"
                f"Hansı sualdan hansı suala qədər işləmək istəyirsiniz?\n\n"
                f"Format: `başlanğıc-son`\n"
                f"Misal: `20-40` və ya `178-704`\n\n"
                f"Mövcud diapazon: *{min_id}–{max_id}*\n\n"
                f"_Ləğv: /cancel_"
            ),
            parse_mode='Markdown'
        )
        return

    if data.startswith("count_"):
        payload = data[len("count_"):]
        rsplit = payload.rsplit("_", 1)
        if len(rsplit) != 2:
            return
        sid, cnt_str = rsplit
        try:
            count = int(cnt_str)
        except ValueError:
            return
        start_general_quiz(query, context, sid, count)
        return

    if data.startswith("ans_"):
        handle_answer(query, context)
        return

    if data == "next":
        session = user_sessions.get(chat_id, {})
        current = session.get('current', 0)
        if current > 0 and current % AD_EVERY_N_QUESTIONS == 0:
            try: query.message.delete()
            except: pass
            show_interstitial_ad(chat_id, context)
        else:
            send_next_question(chat_id, context)
        return

    if data == "finish":
        show_result(chat_id, context)
        return

    # Favoritlər
    if data.startswith("fav_"):
        try:
            qid = int(data[len("fav_"):])
            add_favorite(user.id, qid)
            query.answer("⭐ Favoritlərə əlavə edildi", show_alert=False)
            # Düyməni yenilə (mesajı bütünlüklə yeniləməyə ehtiyac yoxdur, sadəcə bildiriş)
        except Exception:
            pass
        return
    if data.startswith("unfav_"):
        try:
            qid = int(data[len("unfav_"):])
            remove_favorite(user.id, qid)
            query.answer("☆ Favoritlərdən silindi", show_alert=False)
        except Exception:
            pass
        return

    # Sual şikayəti
    if data.startswith("report_"):
        try:
            qid = int(data[len("report_"):])
            conn = get_conn()
            c = conn.cursor()
            c.execute('INSERT INTO question_reports (user_id, question_id, reported_at) VALUES (?,?,?)',
                      (user.id, qid, datetime.now().isoformat()))
            conn.commit()
            conn.close()
            query.answer("🚩 Şikayətiniz qeydə alındı. Təşəkkürlər!", show_alert=True)
            # Adminlərə bildiriş
            for admin_id in ADMIN_IDS:
                try:
                    context.bot.send_message(
                        chat_id=admin_id,
                        text=f"🚩 Yeni şikayət\n👤 user_id: `{user.id}`\n❓ question_id: `{qid}`\n\n/qedit {qid}",
                        parse_mode='Markdown'
                    )
                except Exception:
                    pass
        except Exception:
            pass
        return

    # Qrup rejimi
    if data == "group_join":
        handle_group_join(query, context)
        return
    if data == "group_start":
        handle_group_start(query, context)
        return
    if data.startswith("gans_"):
        handle_group_answer(query, context)
        return
    if data == "group_next":
        handle_group_next_advance(chat_id, context)
        return
    if data == "group_finish":
        show_group_result(chat_id, context)
        return


# ─── Liderboard ──────────────────────────────────────────────────────────────

def show_leaderboard(query, context: CallbackContext, subject_id=None):
    rows = get_leaderboard(10, subject_id=subject_id)
    medals = ["🥇", "🥈", "🥉"] + ["🏅"] * 7

    title = "📊 *Ən Yaxşı Nəticələr — TOP 10*"
    if subject_id:
        s = get_subject(subject_id)
        if s:
            title = f"📊 *{s['name']} — TOP 10*"

    if not rows:
        text = f"{title}\n\nHələ heç kim test verməyib!"
    else:
        lines = [title, "━━━━━━━━━━━━━━━━━"]
        for i, (full_name, username, best_pct, total_quizzes, total_correct, total_q) in enumerate(rows):
            name = full_name if full_name else (f"@{username}" if username else "İstifadəçi")
            avg = round(total_correct / total_q * 100) if total_q and total_q > 0 else 0
            lines.append(
                f"{medals[i]} *{name}*\n"
                f"   🏆 {best_pct}%  |  📝 {total_quizzes} test  |  📈 Ort: {avg}%"
            )
        text = "\n".join(lines)

    # Filtr düymələri
    filter_row = [InlineKeyboardButton("🌐 Hamısı", callback_data="lbsubj_all")]
    for s in DATA['subjects']:
        filter_row.append(InlineKeyboardButton(s.get('emoji', '📘'), callback_data=f"lbsubj_{s['id']}"))

    keyboard = InlineKeyboardMarkup([
        filter_row,
        [InlineKeyboardButton("⬅️ Geri", callback_data="back_subjects")]
    ])
    query.edit_message_text(text=text, parse_mode='Markdown', reply_markup=keyboard)


# ─── Profil / Referral ───────────────────────────────────────────────────────

def show_profile(query, context: CallbackContext):
    user_id = query.from_user.id
    user, stats, ref_count = get_user_stats(user_id)
    if not user or not stats:
        query.edit_message_text("❌ Profil tapılmadı. /start yazın.")
        return

    full_name = user[2] or "İstifadəçi"
    username  = f"@{user[1]}" if user[1] else "—"
    joined    = user[3][:10] if user[3] else "—"

    total_quizzes   = stats[1]
    total_correct   = stats[2]
    total_questions = stats[3]
    best_pct        = stats[4]
    last_played     = stats[5][:10] if stats[5] else "—"
    avg_pct = round(total_correct / total_questions * 100) if total_questions > 0 else 0

    bar_filled = round(avg_pct / 10)
    bar = "🟩" * bar_filled + "⬜" * (10 - bar_filled)

    if avg_pct >= 90:   grade = "🏆 Əla"
    elif avg_pct >= 75: grade = "👍 Yaxşı"
    elif avg_pct >= 50: grade = "😐 Orta"
    elif avg_pct > 0:   grade = "😞 Zəif"
    else:               grade = "—"

    fav_n   = count_favorites(user_id)
    wrong_n = count_wrong_questions(user_id)

    text = (
        f"👤 *Profilim*\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"📛 Ad: *{full_name}*\n"
        f"🔗 İstifadəçi: {username}\n"
        f"📅 Qoşulma: {joined}\n\n"
        f"📊 *Statistika*\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"📝 Toplam test: *{total_quizzes}*\n"
        f"❓ Toplam sual: *{total_questions}*\n"
        f"✅ Düzgün: *{total_correct}*\n"
        f"🏆 Ən yaxşı nəticə: *{best_pct}%*\n"
        f"📈 Ortalama: *{avg_pct}%* — {grade}\n"
        f"🕐 Son test: {last_played}\n\n"
        f"⭐ Favoritlər: *{fav_n}*\n"
        f"📝 Səhv suallar: *{wrong_n}*\n\n"
        f"{bar}\n\n"
        f"👥 Dəvət etdiyim dostlar: *{ref_count}*"
    )

    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("📢 Dost dəvət et", callback_data="menu_referral")],
        [InlineKeyboardButton("⬅️ Geri", callback_data="back_subjects")]
    ])
    query.edit_message_text(text=text, parse_mode='Markdown', reply_markup=keyboard)


def show_referral(query, context: CallbackContext, user_id):
    bot_username = BOT_USERNAME or context.bot.username
    ref_link = f"https://t.me/{bot_username}?start=ref_{user_id}"
    _, _, ref_count = get_user_stats(user_id)

    text = (
        f"📢 *Dost Dəvət Et*\n"
        f"━━━━━━━━━━━━━━━━━\n\n"
        f"Aşağıdakı linki dostlarınızla paylaşın:\n\n"
        f"`{ref_link}`\n\n"
        f"👥 Dəvət etdiyiniz dostlar: *{ref_count}*"
    )
    share_url = f"https://t.me/share/url?url={urllib.parse.quote(ref_link)}&text={urllib.parse.quote('Bu test botu ilə hazırlaş!')}"

    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("📤 Linki paylaş", url=share_url)],
        [InlineKeyboardButton("⬅️ Geri", callback_data="back_subjects")]
    ])
    query.edit_message_text(text=text, parse_mode='Markdown', reply_markup=keyboard)


# ─── Favoritlər/Səhv suallar — fənn seçim alt-menyusu ───────────────────────

def show_favorites_menu(query, context, user_id):
    keyboard = []
    any_fav = False
    for s in DATA['subjects']:
        n = count_favorites(user_id, s['id'])
        if n > 0:
            any_fav = True
            keyboard.append([InlineKeyboardButton(
                f"{s.get('emoji', '📘')} {s['name'][:30]}… ({n})",
                callback_data=f"startfavs_{s['id']}"
            )])
    keyboard.append([InlineKeyboardButton("⬅️ Geri", callback_data="back_subjects")])
    text = ("⭐ *Favoritlərim*\n\n" + ("Fənni seçin:" if any_fav else "Hələ heç favoritin yoxdur."))
    query.edit_message_text(text=text, parse_mode='Markdown',
                            reply_markup=InlineKeyboardMarkup(keyboard))


def show_wrong_menu(query, context, user_id):
    keyboard = []
    any_wrong = False
    for s in DATA['subjects']:
        n = count_wrong_questions(user_id, s['id'])
        if n > 0:
            any_wrong = True
            keyboard.append([InlineKeyboardButton(
                f"{s.get('emoji', '📘')} {s['name'][:30]}… ({n})",
                callback_data=f"startwrong_{s['id']}"
            )])
    keyboard.append([InlineKeyboardButton("⬅️ Geri", callback_data="back_subjects")])
    text = ("📝 *Səhv suallarım*\n\n" + ("Fənni seçin (yalnız son cavabı SƏHV olan suallar):" if any_wrong else "Hələ səhv etdiyin sual yoxdur."))
    query.edit_message_text(text=text, parse_mode='Markdown',
                            reply_markup=InlineKeyboardMarkup(keyboard))


# ─── Komandlar ────────────────────────────────────────────────────────────────

def referral_command(update: Update, context: CallbackContext):
    user = update.message.from_user
    bot_username = BOT_USERNAME or context.bot.username
    ref_link = f"https://t.me/{bot_username}?start=ref_{user.id}"
    _, _, ref_count = get_user_stats(user.id)
    update.message.reply_text(
        f"📢 *Dost Dəvət Et*\n\nLinkiniz:\n`{ref_link}`\n\n👥 Dəvət edilən: *{ref_count}*",
        parse_mode='Markdown'
    )


def profile_command(update: Update, context: CallbackContext):
    user = update.message.from_user
    full_name = (user.first_name or "") + (" " + user.last_name if user.last_name else "")
    register_user(user.id, user.username or "", full_name.strip())
    user_data, stats, ref_count = get_user_stats(user.id)
    if not stats:
        update.message.reply_text("Hələ test verməmisiniz. /start yazın!")
        return
    total_quizzes, total_correct, total_questions, best_pct = stats[1], stats[2], stats[3], stats[4]
    avg_pct = round(total_correct / total_questions * 100) if total_questions > 0 else 0
    update.message.reply_text(
        f"👤 *Profilim*\n📝 Test: *{total_quizzes}*\n✅ *{total_correct}/{total_questions}*\n"
        f"🏆 Ən yaxşı: *{best_pct}%*\n📈 Ortalama: *{avg_pct}%*\n👥 Dəvət: *{ref_count}*",
        parse_mode='Markdown'
    )


def leaderboard_command(update: Update, context: CallbackContext):
    rows = get_leaderboard(10)
    medals = ["🥇", "🥈", "🥉"] + ["🏅"] * 7
    if not rows:
        update.message.reply_text("📊 Hələ heç kim test verməyib!")
        return
    lines = ["📊 *TOP 10*\n━━━━━━━━━━━━━━━━━"]
    for i, (full_name, username, best_pct, total_quizzes, total_correct, total_q) in enumerate(rows):
        name = full_name if full_name else (f"@{username}" if username else "İstifadəçi")
        lines.append(f"{medals[i]} *{name}* — {best_pct}%")
    update.message.reply_text("\n".join(lines), parse_mode='Markdown')


# ─── ADMIN: Sual idarəçiliyi ──────────────────────────────────────────────────
#
# /qadd <subject_id> | <topic_num_or_0> | sual? | A | B | C | D | E | düz_cavab
#   - subject_id: "mm" və ya "adiak" və s.
#   - topic_num: mövzu nömrəsi (1-7) və ya 0 (general)
#   - düz_cavab: A/B/C/D/E (hansı seçim düzgündür)
#
# /qedit <qid>  → düzəltmək üçün hazırkı versiyanı göstər + təlimat
#   /qsetcorrect <qid> <A|B|C|D|E>  - düzgün cavabı dəyiş
#   /qsetq <qid> | yeni sual mətni  - sual mətnini dəyiş
#   /qseta <qid> <A-E> | yeni cavab - bir cavab variantını dəyiş
#
# /qdel <qid>   → sualı sil
#
# /qsearch söz  → açar söz axtar
#
# /qimport     → JSON faylı yüklə (cavab olaraq cavab gözlənilir)
#
# /reports     → açıq şikayətləri göstər
#
# /qhardest [subject_id] → ən çətin sualları göstər

def admin_only(fn):
    def wrapper(update, context):
        if update.effective_user.id not in ADMIN_IDS:
            update.message.reply_text("❌ Bu əmr yalnız adminlər üçündür.")
            return
        return fn(update, context)
    return wrapper


def _next_qid():
    if not QUESTIONS_BY_ID:
        return 1
    return max(QUESTIONS_BY_ID.keys()) + 1


@admin_only
def qadd_command(update: Update, context: CallbackContext):
    """
    /qadd subject_id | topic_num | sual? | A | B | C | D | E | düz
    Misal: /qadd adiak | 0 | Test sualıdır? | bir | iki | üç | dörd | beş | A
    """
    if not context.args:
        update.message.reply_text(
            "ℹ️ İstifadə:\n"
            "`/qadd subject_id | topic_num | sual? | A | B | C | D | E | düz_cavab(A-E)`\n\n"
            "Misal:\n"
            "`/qadd adiak | 0 | Test sualıdır? | bir | iki | üç | dörd | beş | A`\n\n"
            "topic_num 0 olduqda sual `all_questions`-a əlavə olunur, əks halda həmin nömrəli mövzuya.",
            parse_mode='Markdown'
        )
        return
    raw = update.message.text.split(maxsplit=1)[1] if len(update.message.text.split(maxsplit=1)) > 1 else ""
    parts = [p.strip() for p in raw.split("|")]
    if len(parts) != 9:
        update.message.reply_text(f"❌ Format səhvdir. {len(parts)} hissə tapıldı, 9 lazımdır.")
        return
    sid, topic_str, qtext, a, b, c, d, e, correct_letter = parts
    sid = sid.lower()
    subj = get_subject(sid)
    if not subj:
        update.message.reply_text(f"❌ Fənn tapılmadı: `{sid}`", parse_mode='Markdown')
        return
    try:
        topic_num = int(topic_str)
    except ValueError:
        update.message.reply_text("❌ topic_num rəqəm olmalıdır.")
        return
    correct_letter = correct_letter.upper()
    if correct_letter not in ("A", "B", "C", "D", "E"):
        update.message.reply_text("❌ Düz cavab A/B/C/D/E olmalıdır.")
        return
    options = [a, b, c, d, e]
    correct = options[ord(correct_letter) - ord('A')]

    new_q = {
        "id": _next_qid(),
        "q": qtext,
        "answers": options,
        "correct": correct
    }

    if topic_num == 0:
        subj.setdefault('all_questions', []).append(new_q)
        location = f"{subj['name']} → Ümumi"
    else:
        topics = subj.get('topics', [])
        target = next((t for t in topics if t.get('num') == topic_num), None)
        if not target:
            update.message.reply_text(f"❌ Mövzu tapılmadı: {topic_num}")
            return
        target.setdefault('questions', []).append(new_q)
        location = f"{subj['name']} → Mövzu {topic_num}: {target['name']}"

    save_data()
    update.message.reply_text(
        f"✅ Sual əlavə edildi.\n"
        f"📍 {location}\n"
        f"🆔 ID: `{new_q['id']}`",
        parse_mode='Markdown'
    )


@admin_only
def qdel_command(update: Update, context: CallbackContext):
    if not context.args:
        update.message.reply_text("ℹ️ İstifadə: `/qdel <qid>`", parse_mode='Markdown')
        return
    try:
        qid = int(context.args[0])
    except ValueError:
        update.message.reply_text("❌ qid rəqəm olmalıdır.")
        return
    if qid not in QUESTIONS_BY_ID:
        update.message.reply_text("❌ Sual tapılmadı.")
        return
    sid, q = QUESTIONS_BY_ID[qid]
    subj = get_subject(sid)
    found = False
    for t in subj.get('topics', []):
        before = len(t['questions'])
        t['questions'] = [x for x in t['questions'] if x.get('id') != qid]
        if len(t['questions']) < before:
            found = True
    if subj.get('all_questions'):
        before = len(subj['all_questions'])
        subj['all_questions'] = [x for x in subj['all_questions'] if x.get('id') != qid]
        if len(subj['all_questions']) < before:
            found = True
    if found:
        save_data()
        update.message.reply_text(f"🗑 Sual `{qid}` silindi.", parse_mode='Markdown')
    else:
        update.message.reply_text("❌ Silinmə uğursuz oldu.")


@admin_only
def qedit_command(update: Update, context: CallbackContext):
    if not context.args:
        update.message.reply_text("ℹ️ `/qedit <qid>`", parse_mode='Markdown')
        return
    try:
        qid = int(context.args[0])
    except ValueError:
        return
    if qid not in QUESTIONS_BY_ID:
        update.message.reply_text("❌ Sual tapılmadı.")
        return
    sid, q = QUESTIONS_BY_ID[qid]
    subj = get_subject(sid)
    text = (
        f"📝 *Sual {qid}* — {subj['name']}\n\n"
        f"*Q:* {q['q']}\n\n"
    )
    letters = "ABCDE"
    for i, opt in enumerate(q['answers']):
        mark = "✅" if opt == q['correct'] else "  "
        text += f"{mark} {letters[i]}) {opt}\n"
    text += (
        f"\n*Redaktə əmrləri:*\n"
        f"`/qsetq {qid} | yeni sual`\n"
        f"`/qseta {qid} A | yeni cavab` (A-E)\n"
        f"`/qsetcorrect {qid} A` (A-E)\n"
        f"`/qdel {qid}` — sil\n"
    )
    update.message.reply_text(text, parse_mode='Markdown')


@admin_only
def qsetq_command(update: Update, context: CallbackContext):
    """/qsetq <qid> | yeni sual mətni"""
    raw = update.message.text.split(maxsplit=1)[1] if len(update.message.text.split(maxsplit=1)) > 1 else ""
    parts = [p.strip() for p in raw.split("|", 1)]
    if len(parts) != 2:
        update.message.reply_text("❌ Format: `/qsetq qid | yeni mətn`", parse_mode='Markdown')
        return
    try:
        qid = int(parts[0].strip())
    except ValueError:
        return
    if qid not in QUESTIONS_BY_ID:
        update.message.reply_text("❌ Sual tapılmadı.")
        return
    QUESTIONS_BY_ID[qid][1]['q'] = parts[1]
    save_data()
    update.message.reply_text(f"✅ Sual {qid} mətni yeniləndi.")


@admin_only
def qseta_command(update: Update, context: CallbackContext):
    """/qseta <qid> A | yeni cavab"""
    raw = update.message.text.split(maxsplit=1)[1] if len(update.message.text.split(maxsplit=1)) > 1 else ""
    # ilk hissə "qid letter", sonra "|", sonra mətn
    m = re.match(r"^\s*(\d+)\s+([A-Ea-e])\s*\|\s*(.*)$", raw)
    if not m:
        update.message.reply_text("❌ Format: `/qseta qid A | yeni cavab`", parse_mode='Markdown')
        return
    qid = int(m.group(1)); letter = m.group(2).upper(); new_text = m.group(3).strip()
    if qid not in QUESTIONS_BY_ID:
        update.message.reply_text("❌ Sual tapılmadı.")
        return
    idx = ord(letter) - ord('A')
    q = QUESTIONS_BY_ID[qid][1]
    if idx >= len(q['answers']):
        update.message.reply_text("❌ Cavab indeksi həddən çox.")
        return
    old = q['answers'][idx]
    q['answers'][idx] = new_text
    if q['correct'] == old:
        q['correct'] = new_text
    save_data()
    update.message.reply_text(f"✅ Sual {qid}, cavab {letter} yeniləndi.")


@admin_only
def qsetcorrect_command(update: Update, context: CallbackContext):
    """/qsetcorrect <qid> <A-E>"""
    if len(context.args) != 2:
        update.message.reply_text("❌ Format: `/qsetcorrect qid A`", parse_mode='Markdown')
        return
    try:
        qid = int(context.args[0])
    except ValueError:
        return
    letter = context.args[1].upper()
    if letter not in "ABCDE":
        update.message.reply_text("❌ Hərf A/B/C/D/E.")
        return
    if qid not in QUESTIONS_BY_ID:
        update.message.reply_text("❌ Sual tapılmadı.")
        return
    q = QUESTIONS_BY_ID[qid][1]
    idx = ord(letter) - ord('A')
    if idx >= len(q['answers']):
        return
    q['correct'] = q['answers'][idx]
    save_data()
    update.message.reply_text(f"✅ Sual {qid} üçün düzgün cavab → {letter}: {q['correct']}")


@admin_only
def qsearch_command(update: Update, context: CallbackContext):
    """/qsearch söz - sual mətnində axtar"""
    if not context.args:
        update.message.reply_text("ℹ️ `/qsearch söz`", parse_mode='Markdown')
        return
    needle = " ".join(context.args).lower()
    matches = []
    for qid, (sid, q) in QUESTIONS_BY_ID.items():
        if needle in q['q'].lower():
            matches.append((qid, sid, q['q']))
        if len(matches) >= 20:
            break
    if not matches:
        update.message.reply_text("❌ Tapılmadı.")
        return
    lines = [f"🔎 *{len(matches)} nəticə:*"]
    for qid, sid, qtext in matches:
        snippet = qtext[:80] + ("…" if len(qtext) > 80 else "")
        lines.append(f"`{qid}` [{sid}] {snippet}")
    update.message.reply_text("\n".join(lines), parse_mode='Markdown')


@admin_only
def reports_command(update: Update, context: CallbackContext):
    conn = get_conn()
    c = conn.cursor()
    c.execute('SELECT id, user_id, question_id, reported_at FROM question_reports WHERE resolved=0 ORDER BY id DESC LIMIT 20')
    rows = c.fetchall()
    conn.close()
    if not rows:
        update.message.reply_text("✅ Açıq şikayət yoxdur.")
        return
    lines = ["🚩 *Açıq şikayətlər:*"]
    for rid, uid, qid, ts in rows:
        lines.append(f"#{rid} — qid: `{qid}` (user `{uid}`) — {ts[:10]}\n   /qedit {qid}  /resolve {rid}")
    update.message.reply_text("\n".join(lines), parse_mode='Markdown')


@admin_only
def resolve_command(update: Update, context: CallbackContext):
    if not context.args:
        return
    try:
        rid = int(context.args[0])
    except ValueError:
        return
    conn = get_conn()
    c = conn.cursor()
    c.execute('UPDATE question_reports SET resolved=1 WHERE id=?', (rid,))
    conn.commit()
    conn.close()
    update.message.reply_text(f"✅ Şikayət #{rid} həll edildi.")


@admin_only
def qhardest_command(update: Update, context: CallbackContext):
    """/qhardest [subject_id]"""
    sid = context.args[0] if context.args else None
    rows = get_hardest_questions(subject_id=sid, limit=10, min_shown=3)
    if not rows:
        update.message.reply_text("Hələ kifayət qədər data yoxdur.")
        return
    lines = ["🔴 *Ən çətin 10 sual:*"]
    for qid, shown, correct, pct in rows:
        if qid in QUESTIONS_BY_ID:
            qtext = QUESTIONS_BY_ID[qid][1]['q']
            snippet = qtext[:60] + ("…" if len(qtext) > 60 else "")
            lines.append(f"`{qid}` ({round(pct*100)}% düz, {shown}x): {snippet}")
    update.message.reply_text("\n".join(lines), parse_mode='Markdown')


# ─── ADMIN: bulk import ───────────────────────────────────────────────────────
#
# Admin botu sənəd (JSON faylı) göndərir. Fayl belə formatda olmalıdır:
# {
#   "subject_id": "adiak",     // və ya "mm" — hansı fənnə əlavə etmək
#   "topic_num": 0,            // 0 = all_questions, başqa rəqəm = mövzu nömrəsi
#   "questions": [
#     {"q": "...", "answers": ["A","B","C","D","E"], "correct": "A"}
#   ]
# }
# Alternativ: PDF format (ADİAK PDF kimi). Bot PDF-i parse edir.

def document_handler(update: Update, context: CallbackContext):
    """Admin sənəd göndərdikdə bulk import üçün."""
    user = update.effective_user
    if user.id not in ADMIN_IDS:
        return  # Adi istifadəçilərdən sənədləri ignore edirik
    doc = update.message.document
    if not doc:
        return
    file_name = doc.file_name or ""
    file_obj = context.bot.get_file(doc.file_id)
    buf = io.BytesIO()
    file_obj.download(out=buf)
    buf.seek(0)
    raw = buf.read()

    if file_name.lower().endswith('.json'):
        try:
            payload = json.loads(raw.decode('utf-8'))
            n = bulk_import_json(payload)
            update.message.reply_text(f"✅ JSON-dan {n} sual əlavə edildi.")
        except Exception as e:
            update.message.reply_text(f"❌ JSON xətası: {e}")
        return

    if file_name.lower().endswith('.pdf'):
        try:
            questions = parse_pdf_questions(raw)
            if not questions:
                update.message.reply_text("❌ PDF-dən heç bir sual parse edilə bilmədi.")
                return
            # Parse olunmuş sualları müvəqqəti saxla, fənn seçimini gözlə
            pdf_import_pending[user.id] = questions
            keyboard = []
            for s in DATA['subjects']:
                keyboard.append([InlineKeyboardButton(
                    f"{s.get('emoji','📘')} {s['name']}",
                    callback_data=f"pdfimp_sub_{s['id']}"
                )])
            keyboard.append([InlineKeyboardButton("❌ Ləğv et", callback_data="pdfimp_cancel")])
            update.message.reply_text(
                f"✅ PDF-dən *{len(questions)}* sual parse edildi.\n\n"
                f"📚 Hansı fənnə əlavə edilsin?",
                parse_mode='Markdown',
                reply_markup=InlineKeyboardMarkup(keyboard)
            )
        except Exception as e:
            update.message.reply_text(f"❌ PDF xətası: {e}")
        return

    update.message.reply_text("❌ Dəstəklənməyən fayl tipi. JSON və ya PDF göndərin.")


def bulk_import_json(payload):
    """JSON payload-dan sualları aktual DATA-ya əlavə et.
    Dəstəklənən formatlar:
      1) {subject_id, topic_num, questions: [...]}  - klassik format
      2) [{subject_id, topic_num, questions: [...]}, ...]  - list of payloads
      3) [{q, answers, correct}, ...]  - sadəcə suallar (default fənnə gedir)
    `correct` ya tam mətn, ya A-E hərfi ola bilər.
    """
    # Format 2 və ya 3 — list halı
    if isinstance(payload, list):
        if not payload:
            return 0
        # Hər element subject_id keysi varsa - format 2
        if isinstance(payload[0], dict) and 'subject_id' in payload[0]:
            total = 0
            for item in payload:
                total += _import_one_payload(item)
            return total
        # Yoxsa format 3 — sual siyahısıdır
        return _import_one_payload({"subject_id": "adiak", "topic_num": 0, "questions": payload})

    # Format 1 — dict
    if isinstance(payload, dict):
        return _import_one_payload(payload)

    raise ValueError(f"Dəstəklənməyən JSON formatı: {type(payload).__name__}")


def _import_one_payload(payload):
    """Bir payload-u import edir."""
    sid = payload.get('subject_id')
    topic_num = payload.get('topic_num', 0)
    questions = payload.get('questions', [])
    subj = get_subject(sid)
    if not subj:
        raise ValueError(f"Fənn tapılmadı: {sid}")
    target_list = None
    if topic_num == 0:
        target_list = subj.setdefault('all_questions', [])
    else:
        target = next((t for t in subj.get('topics', []) if t.get('num') == topic_num), None)
        if not target:
            raise ValueError(f"Mövzu tapılmadı: {topic_num}")
        target_list = target.setdefault('questions', [])

    n = 0
    nxt = _next_qid()
    for q in questions:
        if not q.get('q') or not q.get('answers'):
            continue
        # `correct` A-E hərfi ola bilər — mətn olaraq çevir
        correct = q.get('correct')
        if isinstance(correct, str) and len(correct) == 1 and correct.upper() in "ABCDE":
            idx = ord(correct.upper()) - ord('A')
            if idx < len(q['answers']):
                correct = q['answers'][idx]
        if not correct or correct not in q['answers']:
            continue
        new_q = {
            "id": nxt,
            "q": q['q'],
            "answers": list(q['answers']),
            "correct": correct
        }
        target_list.append(new_q)
        nxt += 1
        n += 1
    save_data()
    return n


def parse_pdf_questions(raw_bytes):
    """PDF binary-dən sualları parse edir (• və √ markerli cavablar).
    Yalnız parse edir, import etmir. Sual siyahısı qaytarır."""
    try:
        from pypdf import PdfReader
    except ImportError:
        try:
            from PyPDF2 import PdfReader  # köhnə versiya fallback
        except ImportError:
            raise RuntimeError("pypdf kitabxanası yoxdur. requirements.txt-ə əlavə et: pypdf")

    import io as _io
    reader = PdfReader(_io.BytesIO(raw_bytes))
    text_parts = []
    for page in reader.pages:
        try:
            text_parts.append(page.extract_text() or "")
        except Exception as e:
            log.warning(f"PDF səhifə parse xətası: {e}")
    text = "\n".join(text_parts)
    return parse_adiak_text(text)


def bulk_import_pdf(raw_bytes, default_subject_id="adiak", default_topic_num=0):
    """PDF binary-dən parse edib birbaşa import edir (köhnə uyğunluq üçün)."""
    questions = parse_pdf_questions(raw_bytes)
    payload = {
        "subject_id": default_subject_id,
        "topic_num": default_topic_num,
        "questions": questions
    }
    return bulk_import_json(payload)


def parse_adiak_text(raw_text):
    """ADİAK PDF mətnindən sualları çıxart (• = səhv, √ = düz)."""
    raw_text = raw_text.replace("\f", "")
    lines = [l.rstrip() for l in raw_text.split("\n")]
    HEADER_RE = re.compile(r"Y\d+_Əyani_Yekun imtahan testinin sualları")
    NUM_RE = re.compile(r"^(\d+)\.(\s|$)")

    def cln(s): return s.replace("\xad", "").strip()

    def strip_marker(line):
        s = line.lstrip()
        if s.startswith("√"): return ("correct", s[1:].strip())
        if s.startswith("•"): return ("wrong", s[1:].strip())
        return (None, line.strip())

    questions = []
    state = "Q"
    q_lines = []
    answers = []

    def emit():
        if not q_lines and not answers:
            return
        # sual nömrəsini tap
        q_num = None
        num_idx = None
        num_match = None
        for i, l in enumerate(q_lines):
            m = NUM_RE.match(l)
            if m:
                q_num = int(m.group(1)); num_idx = i; num_match = m; break
        if q_num is None:
            cleaned = [cln(l) for l in q_lines if cln(l)]
            q_text = " ".join(cleaned)
        else:
            tail = q_lines[num_idx][num_match.end():].strip()
            before = [cln(l) for l in q_lines[:num_idx] if cln(l)]
            after  = [cln(l) for l in q_lines[num_idx+1:] if cln(l)]
            parts = before + ([tail] if tail else []) + after
            q_text = " ".join(parts)

        opts = [cln(t) for _, t in answers]
        correct = None
        for mk, t in answers:
            if mk == "correct":
                correct = cln(t)
                break
        if len(opts) == 5 and correct in opts:
            questions.append({"q": q_text, "answers": opts, "correct": correct})

    for line in lines:
        if HEADER_RE.search(line) or not line.strip():
            continue
        mk, txt = strip_marker(line)
        if mk:
            if state == "Q":
                answers.append((mk, txt)); state = "A"
            else:
                if len(answers) >= 5:
                    emit(); q_lines = []; answers = []
                    answers.append((mk, txt))
                else:
                    answers.append((mk, txt))
        else:
            if state == "A":
                if len(answers) >= 5:
                    emit(); q_lines = []; answers = []
                    state = "Q"; q_lines.append(line)
                else:
                    if answers:
                        answers[-1] = (answers[-1][0], (answers[-1][1] + " " + line.strip()).strip())
                    else:
                        q_lines.append(line)
            else:
                q_lines.append(line)
    if q_lines or answers:
        emit()
    return questions


# ─── ADMIN PANEL (inline düymələrlə) ──────────────────────────────────────────
#
# /admin — panelni açır
# Panel aşağıdakı funksiyaları təklif edir:
#   ➕ Sual əlavə et      - ConversationHandler wizard
#   ✏️ Sual redaktə et    - qid ilə axtarış + redaktə
#   🔍 Sual axtar         - açar söz
#   📥 Bulk import        - JSON/PDF göndər
#   🔴 Ən çətin suallar   - statistika
#   🚩 Şikayətlər         - açıq reports
#   📊 Statistika         - ümumi

# Wizard state-ləri
ADD_Q_TEXT, ADD_Q_OPTIONS, ADD_Q_CORRECT, ADD_Q_SUBJECT, ADD_Q_CONFIRM = range(5)
EDIT_Q_SEARCH, EDIT_Q_ACTION, EDIT_Q_NEW_VALUE = range(5, 8)

# Hər admin üçün müvəqqəti wizard data-sı
admin_wizard_data = {}  # user_id -> {step, question_text, options, correct, subject_id, ...}


@admin_only
def admin_command(update: Update, context: CallbackContext):
    """/admin əmri — əsas admin paneli aç."""
    show_admin_panel(update.effective_chat.id, context, user_id=update.effective_user.id)


def show_admin_panel(chat_id, context, user_id=None, edit_query=None):
    # Statistika qısa xülasəsi
    conn = get_conn()
    c = conn.cursor()
    c.execute('SELECT COUNT(*) FROM users'); total_users = c.fetchone()[0]
    c.execute('SELECT COUNT(*) FROM quiz_results'); total_quizzes = c.fetchone()[0]
    c.execute('SELECT COUNT(*) FROM question_reports WHERE resolved=0'); open_reports = c.fetchone()[0]
    conn.close()

    total_q = len(QUESTIONS_BY_ID)

    text = (
        f"⚙️ *Admin Panel*\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"👥 İstifadəçi: *{total_users}*\n"
        f"📝 Test: *{total_quizzes}*\n"
        f"❓ Sual: *{total_q}*\n"
        f"🚩 Şikayət (açıq): *{open_reports}*\n\n"
        f"Nə etmək istəyirsiniz?"
    )

    keyboard = [
        [InlineKeyboardButton("➕ Yeni sual əlavə et", callback_data="admin_add")],
        [InlineKeyboardButton("✏️ Sual redaktə et", callback_data="admin_edit"),
         InlineKeyboardButton("🔍 Sual axtar", callback_data="admin_search")],
        [InlineKeyboardButton("📥 Bulk import (fayl göndər)", callback_data="admin_bulk")],
        [InlineKeyboardButton("🔴 Ən çətin suallar", callback_data="admin_hardest"),
         InlineKeyboardButton("🚩 Şikayətlər", callback_data="admin_reports")],
        [InlineKeyboardButton("📊 Tam statistika", callback_data="admin_stats"),
         InlineKeyboardButton("📢 Bildiriş göndər", callback_data="admin_broadcast")],
        [InlineKeyboardButton("📚 Fənn/Mövzu idarəçiliyi", callback_data="admin_subjects")],
        [InlineKeyboardButton("❌ Bağla", callback_data="admin_close")]
    ]

    if edit_query:
        try:
            edit_query.edit_message_text(text=text, parse_mode='Markdown',
                                          reply_markup=InlineKeyboardMarkup(keyboard))
            return
        except Exception:
            pass
    context.bot.send_message(chat_id=chat_id, text=text, parse_mode='Markdown',
                             reply_markup=InlineKeyboardMarkup(keyboard))


# ─── Admin callback router ────────────────────────────────────────────────────

def admin_callback_handler(update: Update, context: CallbackContext):
    """Admin panel callback-lərini idarə edir."""
    query = update.callback_query
    query.answer()
    user_id = query.from_user.id
    chat_id = query.message.chat_id
    data = query.data

    if user_id not in ADMIN_IDS:
        query.answer("❌ Yalnız adminlər üçün.", show_alert=True)
        return

    if data == "admin_close":
        try: query.message.delete()
        except: pass
        return

    # PDF import: fənn seçimi
    if data == "pdfimp_cancel":
        pdf_import_pending.pop(user_id, None)
        try:
            query.edit_message_text("❌ PDF import ləğv edildi.")
        except: pass
        return

    if data.startswith("pdfimp_sub_"):
        sid = data[len("pdfimp_sub_"):]
        questions = pdf_import_pending.get(user_id)
        if not questions:
            try:
                query.edit_message_text("⚠️ Import məlumatı tapılmadı (vaxtı keçib). PDF-i yenidən göndərin.")
            except: pass
            return
        subj = get_subject(sid)
        if not subj:
            try:
                query.edit_message_text(f"❌ Fənn tapılmadı: {sid}")
            except: pass
            return
        try:
            n = _import_one_payload({
                "subject_id": sid,
                "topic_num": 0,
                "questions": questions
            })
            pdf_import_pending.pop(user_id, None)
            query.edit_message_text(
                f"✅ *{subj['name']}* fənninə {n} sual əlavə edildi.",
                parse_mode='Markdown'
            )
        except Exception as e:
            query.edit_message_text(f"❌ Import xətası: {e}")
        return

    if data == "admin_panel":
        show_admin_panel(chat_id, context, user_id=user_id, edit_query=query)
        return

    if data == "admin_add":
        # Wizard başlat
        admin_wizard_data[user_id] = {'step': 'q_text'}
        try: query.message.delete()
        except: pass
        context.bot.send_message(
            chat_id=chat_id,
            text=(
                "➕ *Yeni Sual Əlavə Et*\n\n"
                "1/4: Sual mətnini yazın.\n"
                "_Ləğv etmək üçün: /cancel_"
            ),
            parse_mode='Markdown'
        )
        return

    if data == "admin_edit":
        admin_wizard_data[user_id] = {'step': 'edit_search'}
        try: query.message.delete()
        except: pass
        context.bot.send_message(
            chat_id=chat_id,
            text=(
                "✏️ *Sual Redaktə Et*\n\n"
                "Sualın ID nömrəsini yazın (məs: `42`)\n"
                "yaxud suala məxsus açar söz yazın (məs: `natiq`).\n\n"
                "_Ləğv: /cancel_"
            ),
            parse_mode='Markdown'
        )
        return

    if data == "admin_search":
        admin_wizard_data[user_id] = {'step': 'search_keyword'}
        try: query.message.delete()
        except: pass
        context.bot.send_message(
            chat_id=chat_id,
            text="🔍 *Sual Axtar*\n\nAçar söz yazın:\n\n_Ləğv: /cancel_",
            parse_mode='Markdown'
        )
        return

    if data == "admin_bulk":
        try: query.message.delete()
        except: pass
        context.bot.send_message(
            chat_id=chat_id,
            text=(
                "📥 *Bulk Import*\n\n"
                "Bu söhbətə fayl göndərin:\n\n"
                "• *JSON* formatı:\n"
                "```\n"
                "{\n"
                '  "subject_id": "adiak",\n'
                '  "topic_num": 0,\n'
                '  "questions": [\n'
                '    {"q":"...","answers":["A","B","C","D","E"],"correct":"A"}\n'
                "  ]\n"
                "}\n"
                "```\n\n"
                "• *PDF* formatı: ADİAK-a bənzər layout (• və √ markerli)\n\n"
                "Fayl göndərdikdən sonra bot avtomatik import edir."
            ),
            parse_mode='Markdown',
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("⬅️ Geri", callback_data="admin_panel")]
            ])
        )
        return

    if data == "admin_hardest":
        rows = get_hardest_questions(limit=10, min_shown=3)
        if not rows:
            text = "🔴 *Ən çətin suallar*\n\nHələ kifayət qədər data yoxdur (ən azı 3 dəfə cavablanmış sual lazımdır)."
        else:
            lines = ["🔴 *Ən çətin 10 sual*\n━━━━━━━━━━━━━━━━━"]
            for qid, shown, correct, pct in rows:
                if qid in QUESTIONS_BY_ID:
                    qtext = QUESTIONS_BY_ID[qid][1]['q']
                    snippet = qtext[:55] + ("…" if len(qtext) > 55 else "")
                    lines.append(f"`#{qid}` — {round(pct*100)}% düz ({shown}x)\n   {snippet}")
            text = "\n\n".join(lines)
        query.edit_message_text(
            text=text, parse_mode='Markdown',
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Geri", callback_data="admin_panel")]])
        )
        return

    if data == "admin_reports":
        show_admin_reports(query, context)
        return

    if data.startswith("admin_resolve_"):
        try:
            rid = int(data[len("admin_resolve_"):])
            conn = get_conn()
            c = conn.cursor()
            c.execute('UPDATE question_reports SET resolved=1 WHERE id=?', (rid,))
            conn.commit()
            conn.close()
            query.answer(f"✅ Şikayət #{rid} həll edildi.", show_alert=False)
            show_admin_reports(query, context)
        except Exception as e:
            query.answer(f"❌ Xəta: {e}", show_alert=True)
        return

    if data == "admin_stats":
        show_admin_stats_inline(query, context)
        return

    if data == "admin_broadcast":
        admin_wizard_data[user_id] = {'step': 'broadcast_text'}
        try: query.message.delete()
        except: pass
        context.bot.send_message(
            chat_id=chat_id,
            text=(
                "📢 *Bildiriş Göndər*\n\n"
                "Bütün istifadəçilərə göndəriləcək mətni yazın.\n\n"
                "_Ləğv: /cancel_"
            ),
            parse_mode='Markdown'
        )
        return

    # ─── Fənn/Mövzu İdarəçiliyi ──────────────────────────────────────────────

    if data == "admin_subjects":
        show_subject_list(query, context)
        return

    if data == "admin_subj_new":
        admin_wizard_data[user_id] = {'step': 'subj_new_id'}
        query.edit_message_text(
            "📚 *Yeni Fənn Yarat*\n\n"
            "1/3: Fənn üçün qısa ID yazın (məs: `mm`, `adiak`, `tarix`)\n"
            "_Yalnız latın hərfləri və rəqəm, boşluqsuz_\n\n"
            "_Ləğv: /cancel_",
            parse_mode='Markdown'
        )
        return

    if data == "admin_subj_list":
        show_subject_list(query, context)
        return

    # Dublikat detektoru
    if data == "admin_dupcheck":
        run_duplicate_check(query, context)
        return

    if data.startswith("admin_subj_"):
        # Format: admin_subj_<action>_<sid>  OR  admin_subj_<action>_<sid>_<idx>
        # Strip prefix and parse manually
        rest = data[len("admin_subj_"):]  # e.g. "view_adiak" or "deltopic_adiak_2"
        underscore_pos = rest.find("_")
        if underscore_pos == -1:
            return
        action = rest[:underscore_pos]          # "view", "hide", "topics", "addtopic", "deltopic", "rntopic"
        after_action = rest[underscore_pos+1:]  # "adiak" or "adiak_2"

        # For deltopic/rntopic the last segment is the index
        if action in ("deltopic", "rntopic"):
            last_under = after_action.rfind("_")
            if last_under == -1:
                return
            sid = after_action[:last_under]
            try:
                tidx = int(after_action[last_under+1:])
            except ValueError:
                return
        else:
            sid = after_action
            tidx = None

        subj = get_subject(sid)

        if action == "view":
            if not subj:
                query.answer("Fənn tapılmadı", show_alert=True); return
            show_subject_detail(query, context, sid)
            return

        if action == "hide":
            if not subj:
                query.answer("Fənn tapılmadı", show_alert=True); return
            subj['hidden'] = not subj.get('hidden', False)
            save_data()
            state = "gizlədildi 🙈" if subj['hidden'] else "görünür edildi 👁"
            query.answer(f"Fənn {state}", show_alert=True)
            show_subject_detail(query, context, sid)
            return

        if action == "delconfirm":
            if not subj:
                query.answer("Fənn tapılmadı", show_alert=True); return
            q_count = len(subj.get('all_questions', [])) + sum(len(t.get('questions',[])) for t in subj.get('topics',[]))
            text = (
                f"🗑 <b>Fənni sil: {_he(subj['emoji'])} {_he(subj['name'])}</b>\n"
                f"━━━━━━━━━━━━━━━━━\n"
                f"⚠️ Bu əməliyyat GERİ ALINMAZ!\n\n"
                f"❓ {q_count} sual da silinəcək.\n\n"
                f"Əminsiniz?"
            )
            keyboard = [
                [InlineKeyboardButton("🗑 Bəli, sil!", callback_data=f"admin_subj_delyes_{sid}"),
                 InlineKeyboardButton("❌ Xeyr", callback_data=f"admin_subj_view_{sid}")]
            ]
            _send_or_edit(query, context, text, keyboard)
            return

        if action == "delyes":
            if not subj:
                query.answer("Fənn tapılmadı", show_alert=True); return
            DATA['subjects'] = [s for s in DATA['subjects'] if s['id'] != sid]
            save_data()
            query.answer(f"✅ Fənn silindi: {subj['name']}", show_alert=True)
            show_subject_list(query, context)
            return

        if action == "topics":
            if not subj:
                query.answer("Fənn tapılmadı", show_alert=True); return
            show_topic_list(query, context, sid)
            return

        if action == "addtopic":
            if not subj:
                query.answer("Fənn tapılmadı", show_alert=True); return
            admin_wizard_data[user_id] = {'step': 'topic_add_name', 'sid': sid}
            query.edit_message_text(
                f"➕ *Yeni Mövzu* — _{subj['name']}_\n\n"
                "Mövzunun adını yazın:\n\n_Ləğv: /cancel_",
                parse_mode='Markdown'
            )
            return

        if action == "deltopic":
            subj2 = get_subject(sid)
            if subj2 and tidx is not None and 0 <= tidx < len(subj2.get('topics', [])):
                t = subj2['topics'].pop(tidx)
                save_data()
                query.answer(f"Mövzu silindi: {t['name']}", show_alert=True)
                show_topic_list(query, context, sid)
            return

        if action == "rntopic":
            subj2 = get_subject(sid)
            if subj2 and tidx is not None:
                topic_name = subj2['topics'][tidx]['name'] if tidx < len(subj2.get('topics', [])) else "?"
                admin_wizard_data[user_id] = {'step': 'topic_rename', 'sid': sid, 'tidx': tidx}
                query.edit_message_text(
                    f"✏️ {topic_name} — yeni adı yazın:\n\nLəğv: /cancel",
                    parse_mode=None
                )
            return

        if action == "delete":
            # Silmə təsdiq ekranı
            subj2 = get_subject(sid)
            if not subj2:
                query.answer("Fənn tapılmadı", show_alert=True); return
            q_count = len(subj2.get('all_questions', []))
            t_count = len(subj2.get('topics', []))
            text = (
                f"⚠️ <b>Fənni silmək istədiyinizdən əminsiniz?</b>\n\n"
                f"{_he(subj2['emoji'])} <b>{_he(subj2['name'])}</b>\n"
                f"❓ {q_count} sual və {t_count} mövzu <b>tamamilə silinəcək!</b>\n\n"
                f"Bu əməliyyat geri alına bilməz."
            )
            keyboard = [
                [InlineKeyboardButton("✅ Bəli, sil", callback_data=f"admin_subj_delconfirm_{sid}"),
                 InlineKeyboardButton("❌ Xeyr, geri", callback_data=f"admin_subj_view_{sid}")]
            ]
            _send_or_edit(query, context, text, keyboard)
            return

        if action == "delconfirm":
            # Fənni sil
            before = len(DATA['subjects'])
            DATA['subjects'] = [s for s in DATA['subjects'] if s['id'] != sid]
            if len(DATA['subjects']) < before:
                save_data()
                query.answer("✅ Fənn silindi!", show_alert=True)
            else:
                query.answer("Fənn tapılmadı", show_alert=True)
            show_subject_list(query, context)
            return

        return


    # ─── Sual redaktə düymələri (admin_edit wizard içindən) ──────────────────
    if data.startswith("adminq_"):
        # adminq_<action>_<qid>
        parts = data.split("_", 2)
        if len(parts) != 3:
            return
        action = parts[1]
        try:
            qid = int(parts[2])
        except ValueError:
            return
        if qid not in QUESTIONS_BY_ID:
            query.answer("Sual tapılmadı.", show_alert=True)
            return

        if action == "show":
            show_question_edit_menu(query, context, qid)
            return

        if action == "del":
            # Təsdiq soruş
            q = QUESTIONS_BY_ID[qid][1]
            query.edit_message_text(
                text=f"🗑 *Silmə təsdiq*\n\nSual #{qid}:\n_{q['q'][:100]}…_\n\nSilmək istəyirsiniz?",
                parse_mode='Markdown',
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("✅ Bəli, sil", callback_data=f"adminq_delyes_{qid}"),
                     InlineKeyboardButton("❌ Ləğv", callback_data=f"adminq_show_{qid}")]
                ])
            )
            return

        if action == "delyes":
            sid, q = QUESTIONS_BY_ID[qid]
            subj = get_subject(sid)
            for t in subj.get('topics', []):
                t['questions'] = [x for x in t['questions'] if x.get('id') != qid]
            if subj.get('all_questions'):
                subj['all_questions'] = [x for x in subj['all_questions'] if x.get('id') != qid]
            save_data()
            query.edit_message_text(
                text=f"🗑 Sual #{qid} silindi.",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Admin panel", callback_data="admin_panel")]])
            )
            return

        if action == "editq":
            admin_wizard_data[user_id] = {'step': 'edit_q_text', 'qid': qid}
            context.bot.send_message(
                chat_id=chat_id,
                text=f"📝 Sual #{qid}-ün yeni mətnini yazın:\n\n_Ləğv: /cancel_",
                parse_mode='Markdown'
            )
            return

        if action in ("a", "b", "c", "d", "e"):
            # Cavab variantını redaktə et
            letter = action.upper()
            idx = ord(letter) - ord('A')
            q = QUESTIONS_BY_ID[qid][1]
            if idx >= len(q['answers']):
                return
            admin_wizard_data[user_id] = {'step': 'edit_answer', 'qid': qid, 'letter': letter, 'idx': idx}
            context.bot.send_message(
                chat_id=chat_id,
                text=(
                    f"📝 Sual #{qid}, cavab *{letter}*\n\n"
                    f"Köhnə: _{q['answers'][idx]}_\n\n"
                    f"Yeni mətni yazın:\n\n_Ləğv: /cancel_"
                ),
                parse_mode='Markdown'
            )
            return

        if action == "setcorrect":
            q = QUESTIONS_BY_ID[qid][1]
            keyboard = []
            letters = "ABCDE"
            for i, opt in enumerate(q['answers']):
                mark = "✅ " if opt == q['correct'] else ""
                keyboard.append([InlineKeyboardButton(
                    f"{mark}{letters[i]}) {opt[:40]}",
                    callback_data=f"adminq_setc{i}_{qid}"
                )])
            keyboard.append([InlineKeyboardButton("⬅️ Geri", callback_data=f"adminq_show_{qid}")])
            query.edit_message_text(
                text=f"✅ Düzgün cavabı seçin (sual #{qid}):",
                reply_markup=InlineKeyboardMarkup(keyboard)
            )
            return

        if action.startswith("setc"):
            try:
                idx = int(action[4:])
            except ValueError:
                return
            q = QUESTIONS_BY_ID[qid][1]
            if idx >= len(q['answers']):
                return
            q['correct'] = q['answers'][idx]
            save_data()
            query.answer("✅ Düzgün cavab dəyişdirildi.")
            show_question_edit_menu(query, context, qid)
            return

    # ─── Yeni sual wizard-dan fənn seçimi ───────────────────────────────────
    if data.startswith("addq_subj_"):
        sid = data[len("addq_subj_"):]
        subj = get_subject(sid)
        if not subj:
            query.answer("Fənn tapılmadı.", show_alert=True)
            return
        wiz = admin_wizard_data.get(user_id, {})
        wiz['subject_id'] = sid
        wiz['step'] = 'confirm'
        admin_wizard_data[user_id] = wiz
        show_add_q_confirm(query, context, user_id)
        return

    if data.startswith("addq_correct_"):
        try:
            idx = int(data[len("addq_correct_"):])
        except ValueError:
            return
        wiz = admin_wizard_data.get(user_id, {})
        if 'options' not in wiz or idx >= len(wiz['options']):
            return
        wiz['correct'] = wiz['options'][idx]
        wiz['step'] = 'choose_subject'
        admin_wizard_data[user_id] = wiz
        # Fənn seçimini göstər
        keyboard = []
        for s in DATA['subjects']:
            keyboard.append([InlineKeyboardButton(
                f"{s.get('emoji','📘')} {s['name']}",
                callback_data=f"addq_subj_{s['id']}"
            )])
        keyboard.append([InlineKeyboardButton("❌ Ləğv", callback_data="addq_cancel")])
        query.edit_message_text(
            text="4/4: Sual hansı fənnə aid olmalıdır?",
            reply_markup=InlineKeyboardMarkup(keyboard)
        )
        return

    if data == "addq_save":
        wiz = admin_wizard_data.get(user_id, {})
        try:
            new_q = {
                "id": _next_qid(),
                "q": wiz['q_text'],
                "answers": list(wiz['options']),
                "correct": wiz['correct']
            }
            subj = get_subject(wiz['subject_id'])
            subj.setdefault('all_questions', []).append(new_q)
            save_data()
            query.edit_message_text(
                text=f"✅ Sual əlavə edildi.\n🆔 ID: *{new_q['id']}*\n📚 Fənn: {subj['name']}",
                parse_mode='Markdown',
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Admin panel", callback_data="admin_panel")]])
            )
            admin_wizard_data.pop(user_id, None)
        except Exception as e:
            query.answer(f"❌ Xəta: {e}", show_alert=True)
        return

    if data == "addq_cancel":
        admin_wizard_data.pop(user_id, None)
        show_admin_panel(chat_id, context, user_id=user_id, edit_query=query)
        return



# ─── Fənn/Mövzu İdarəçiliyi Funksiyaları ─────────────────────────────────────

def _send_or_edit(query, context, text, keyboard):
    """Mesajı edit et, alınmasa reply et. HTML parse mode istifadə edir."""
    markup = InlineKeyboardMarkup(keyboard)
    try:
        query.edit_message_text(text=text, parse_mode='HTML',
                                reply_markup=markup)
    except Exception as e:
        log.warning(f"edit_message_text failed ({type(e).__name__}: {e}), falling back to reply_text")
        try:
            query.message.reply_text(text=text, parse_mode='HTML',
                                     reply_markup=markup)
        except Exception as e2:
            log.error(f"reply_text also failed: {e2}")


def _he(s):
    """HTML escape — fənn adlarında xüsusi simvol olsa da qırılmasın."""
    import html as _html_mod
    return _html_mod.escape(str(s))


def show_subject_list(query, context):
    """Bütün fənnlərin siyahısını göstər."""
    subjects = DATA.get('subjects', [])
    lines = ["📚 <b>Fənn İdarəçiliyi</b>\n━━━━━━━━━━━━━━━━━"]
    keyboard = []
    for s in subjects:
        hidden_mark = " 🙈" if s.get('hidden') else ""
        q_count = len(s.get('all_questions', []))
        t_count = len(s.get('topics', []))
        lines.append(
            f"{_he(s['emoji'])} <b>{_he(s['name'])}</b>{hidden_mark}\n"
            f"   ID: <code>{_he(s['id'])}</code> | {q_count} sual | {t_count} mövzu"
        )
        keyboard.append([InlineKeyboardButton(
            f"{s['emoji']} {s['name']}{hidden_mark}",
            callback_data=f"admin_subj_view_{s['id']}"
        )])

    keyboard.append([
        InlineKeyboardButton("➕ Yeni fənn yarat", callback_data="admin_subj_new"),
        InlineKeyboardButton("🔍 Dublikat", callback_data="admin_dupcheck")
    ])
    keyboard.append([InlineKeyboardButton("⬅️ Admin panel", callback_data="admin_panel")])

    _send_or_edit(query, context, "\n\n".join(lines), keyboard)


def show_subject_detail(query, context, sid):
    """Bir fənnin detallarını və mövzularını göstər."""
    subj = get_subject(sid)
    if not subj:
        query.answer("Fənn tapılmadı", show_alert=True)
        return

    hidden = subj.get('hidden', False)
    topics = subj.get('topics', [])
    q_count = len(subj.get('all_questions', []))
    t_total_q = sum(len(t.get('questions', [])) for t in topics)

    text = (
        f"{_he(subj['emoji'])} <b>{_he(subj['name'])}</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"🆔 ID: <code>{_he(subj['id'])}</code>\n"
        f"👁 Status: {'🙈 Gizli' if hidden else '✅ Görünür'}\n"
        f"❓ Sual sayı: <b>{q_count}</b>\n"
        f"📂 Mövzular: <b>{len(topics)}</b> ({t_total_q} sual)\n\n"
        f"Aşağıdan əməliyyat seçin:"
    )

    keyboard = []
    if topics:
        keyboard.append([InlineKeyboardButton(
            f"📋 Mövzulara bax/idarə et ({len(topics)})",
            callback_data=f"admin_subj_topics_{sid}"
        )])
    keyboard.append([
        InlineKeyboardButton("➕ Mövzu əlavə et", callback_data=f"admin_subj_addtopic_{sid}"),
        InlineKeyboardButton("🙈 Gizlət" if not hidden else "👁 Göstər",
                             callback_data=f"admin_subj_hide_{sid}")
    ])
    keyboard.append([
        InlineKeyboardButton("🗑 Fənni sil", callback_data=f"admin_subj_delconfirm_{sid}"),
    ])
    keyboard.append([InlineKeyboardButton("⬅️ Fənn siyahısı", callback_data="admin_subj_list")])

    _send_or_edit(query, context, text, keyboard)


def show_topic_list(query, context, sid):
    """Fənnin mövzularını idarəetmə düymələri ilə göstər."""
    subj = get_subject(sid)
    if not subj:
        query.answer("Fənn tapılmadı", show_alert=True)
        return

    topics = subj.get('topics', [])
    if not topics:
        query.answer("Bu fənndə heç mövzu yoxdur.", show_alert=True)
        show_subject_detail(query, context, sid)
        return

    lines = [f"📂 <b>{_he(subj['emoji'])} {_he(subj['name'])}</b> — Mövzular\n━━━━━━━━━━━━━━━━━"]
    keyboard = []
    for i, t in enumerate(topics):
        qc = len(t.get('questions', []))
        lines.append(f"{i+1}. {_he(t['name'])} — {qc} sual")
        keyboard.append([
            InlineKeyboardButton(f"✏️ {t['name'][:28]}", callback_data=f"admin_subj_rntopic_{sid}_{i}"),
            InlineKeyboardButton("🗑 Sil", callback_data=f"admin_subj_deltopic_{sid}_{i}")
        ])

    text = "\n".join(lines)
    keyboard.append([InlineKeyboardButton(f"⬅️ {subj['emoji']} {subj['name']}", callback_data=f"admin_subj_view_{sid}")])

    _send_or_edit(query, context, text, keyboard)


def run_duplicate_check(query, context):
    """Bütün suallar arasında dublikat tapır (token set uyğunluğu >= 85%)."""
    import re as _re
    all_qs = list(QUESTIONS_BY_ID.items())

    def normalize(s):
        return _re.sub(r'\s+', ' ', s.lower().strip())

    def similarity(a, b):
        sa = set(normalize(a).split())
        sb = set(normalize(b).split())
        if not sa or not sb:
            return 0
        return len(sa & sb) / max(len(sa), len(sb))

    duplicates = []
    checked = set()
    for i in range(len(all_qs)):
        qid_a, (sid_a, q_a) = all_qs[i]
        for j in range(i + 1, min(i + 200, len(all_qs))):
            qid_b, (sid_b, q_b) = all_qs[j]
            pair = (min(qid_a, qid_b), max(qid_a, qid_b))
            if pair in checked:
                continue
            checked.add(pair)
            sim = similarity(q_a['q'], q_b['q'])
            if sim >= 0.85:
                duplicates.append((sim, qid_a, q_a['q'], qid_b, q_b['q']))
            if len(duplicates) >= 15:
                break
        if len(duplicates) >= 15:
            break

    if not duplicates:
        text = "✅ <b>Dublikat Detektoru</b>\n\nHeç bir dublikat tapılmadı! (ilk 200 sual yoxlanıldı)"
    else:
        lines = [f"⚠️ <b>Dublikat Detektoru</b> — {len(duplicates)} cüt tapıldı\n━━━━━━━━━━━━━━━━━"]
        for sim, qa_id, qa_text, qb_id, qb_text in duplicates:
            lines.append(
                f"🔴 <b>{round(sim*100)}% uyğun</b>\n"
                f"  <code>#{qa_id}</code> {_he(qa_text[:50])}…\n"
                f"  <code>#{qb_id}</code> {_he(qb_text[:50])}…"
            )
        text = "\n\n".join(lines)

    keyboard = [[InlineKeyboardButton("⬅️ Fənn siyahısı", callback_data="admin_subj_list")]]
    _send_or_edit(query, context, text, keyboard)


def show_admin_reports(query, context):
    conn = get_conn()
    c = conn.cursor()
    c.execute('SELECT id, user_id, question_id, reported_at FROM question_reports WHERE resolved=0 ORDER BY id DESC LIMIT 10')
    rows = c.fetchall()
    conn.close()

    keyboard = []
    if not rows:
        text = "🚩 *Şikayətlər*\n\n✅ Açıq şikayət yoxdur."
    else:
        lines = ["🚩 *Açıq şikayətlər*\n━━━━━━━━━━━━━━━━━"]
        for rid, uid, qid, ts in rows:
            qtext = ""
            if qid in QUESTIONS_BY_ID:
                qtext = QUESTIONS_BY_ID[qid][1]['q'][:50] + "…"
            lines.append(f"`#{rid}` — sual `{qid}` — {ts[:10]}\n   _{qtext}_")
            keyboard.append([
                InlineKeyboardButton(f"✏️ #{qid} redaktə", callback_data=f"adminq_show_{qid}"),
                InlineKeyboardButton(f"✅ Həll #{rid}", callback_data=f"admin_resolve_{rid}")
            ])
        text = "\n\n".join(lines)
    keyboard.append([InlineKeyboardButton("⬅️ Admin panel", callback_data="admin_panel")])
    query.edit_message_text(text=text, parse_mode='Markdown', reply_markup=InlineKeyboardMarkup(keyboard))


def show_admin_stats_inline(query, context):
    conn = get_conn()
    c = conn.cursor()
    c.execute('SELECT COUNT(*) FROM users'); total_users = c.fetchone()[0]
    c.execute('SELECT COUNT(*) FROM quiz_results'); total_quizzes = c.fetchone()[0]
    c.execute('SELECT COUNT(*) FROM referrals'); total_refs = c.fetchone()[0]
    c.execute('SELECT AVG(pct) FROM quiz_results'); avg_pct = round(c.fetchone()[0] or 0)
    c.execute('SELECT subject_id, COUNT(*) FROM quiz_results GROUP BY subject_id'); per_subj = c.fetchall()
    c.execute('SELECT COUNT(*) FROM question_reports WHERE resolved=0'); open_reports = c.fetchone()[0]
    # Ən aktiv 5 istifadəçi
    c.execute('SELECT u.full_name, s.total_quizzes FROM stats s JOIN users u ON s.user_id=u.user_id ORDER BY s.total_quizzes DESC LIMIT 5')
    top_users = c.fetchall()
    conn.close()

    per_subj_text = ""
    if per_subj:
        per_subj_text = "\n📚 *Fənn üzrə:*\n"
        for sid, cnt in per_subj:
            s = get_subject(sid) if sid else None
            name = s['name'] if s else (sid or "köhnə")
            per_subj_text += f"   • {name[:30]}: {cnt}\n"

    top_text = ""
    if top_users:
        top_text = "\n🏆 *Ən aktiv:*\n"
        for name, cnt in top_users:
            top_text += f"   • {name[:25]} — {cnt} test\n"

    text = (
        f"📊 *Tam Statistika*\n━━━━━━━━━━━━━━━━━\n"
        f"👥 İstifadəçi: *{total_users}*\n"
        f"📝 Test: *{total_quizzes}*\n"
        f"📢 Referral: *{total_refs}*\n"
        f"📈 Ortalama: *{avg_pct}%*\n"
        f"🚩 Açıq şikayət: *{open_reports}*"
        f"{per_subj_text}"
        f"{top_text}"
    )
    query.edit_message_text(
        text=text, parse_mode='Markdown',
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Admin panel", callback_data="admin_panel")]])
    )


def show_question_edit_menu(query, context, qid):
    if qid not in QUESTIONS_BY_ID:
        query.answer("Sual tapılmadı.", show_alert=True)
        return
    sid, q = QUESTIONS_BY_ID[qid]
    subj = get_subject(sid)
    letters = "ABCDE"
    text = f"✏️ *Sual #{qid}* — {subj['name']}\n━━━━━━━━━━━━━━━━━\n\n*Q:* {q['q']}\n\n"
    for i, opt in enumerate(q['answers']):
        mark = "✅" if opt == q['correct'] else "  "
        text += f"{mark} *{letters[i]})* {opt}\n"

    # Çətinlik
    diff = get_question_difficulty(qid)
    if diff is not None:
        text += f"\n📊 Düz cavab: {diff}%\n"

    keyboard = [
        [InlineKeyboardButton("📝 Sual mətnini dəyiş", callback_data=f"adminq_editq_{qid}")],
        [InlineKeyboardButton("A", callback_data=f"adminq_a_{qid}"),
         InlineKeyboardButton("B", callback_data=f"adminq_b_{qid}"),
         InlineKeyboardButton("C", callback_data=f"adminq_c_{qid}"),
         InlineKeyboardButton("D", callback_data=f"adminq_d_{qid}"),
         InlineKeyboardButton("E", callback_data=f"adminq_e_{qid}")],
        [InlineKeyboardButton("✅ Düzgün cavabı dəyiş", callback_data=f"adminq_setcorrect_{qid}")],
        [InlineKeyboardButton("🗑 Sualı sil", callback_data=f"adminq_del_{qid}")],
        [InlineKeyboardButton("⬅️ Admin panel", callback_data="admin_panel")]
    ]
    try:
        query.edit_message_text(text=text, parse_mode='Markdown', reply_markup=InlineKeyboardMarkup(keyboard))
    except Exception:
        context.bot.send_message(chat_id=query.message.chat_id, text=text, parse_mode='Markdown',
                                 reply_markup=InlineKeyboardMarkup(keyboard))


def show_add_q_confirm(query, context, user_id):
    wiz = admin_wizard_data.get(user_id, {})
    letters = "ABCDE"
    subj = get_subject(wiz.get('subject_id', ''))
    text = "📝 *Yeni Sual — Təsdiq*\n━━━━━━━━━━━━━━━━━\n\n"
    text += f"📚 *Fənn:* {subj['name'] if subj else '?'}\n\n"
    text += f"*Q:* {wiz.get('q_text', '')}\n\n"
    for i, opt in enumerate(wiz.get('options', [])):
        mark = "✅" if opt == wiz.get('correct') else "  "
        text += f"{mark} *{letters[i]})* {opt}\n"
    text += "\nSaxlamaq istəyirsiniz?"

    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Saxla", callback_data="addq_save"),
         InlineKeyboardButton("❌ Ləğv", callback_data="addq_cancel")]
    ])
    try:
        query.edit_message_text(text=text, parse_mode='Markdown', reply_markup=keyboard)
    except Exception:
        context.bot.send_message(chat_id=query.message.chat_id, text=text,
                                  parse_mode='Markdown', reply_markup=keyboard)


# ─── Admin wizard mətn handler-i (əmr olmayan adi mətni tutur) ───────────────

def admin_text_handler(update: Update, context: CallbackContext):
    """Admin wizard aktivdirsə, gələn mətni uyğun addıma görə emal edir."""
    user = update.effective_user
    if user.id not in ADMIN_IDS:
        return False  # Adi istifadəçilərə toxunma
    wiz = admin_wizard_data.get(user.id)
    if not wiz:
        return False
    text = update.message.text or ""
    if text == "/cancel":
        admin_wizard_data.pop(user.id, None)
        update.message.reply_text("❌ Ləğv edildi.")
        show_admin_panel(update.effective_chat.id, context, user_id=user.id)
        return True

    step = wiz.get('step')

    # ── Yeni sual wizard ──
    if step == 'q_text':
        wiz['q_text'] = text.strip()
        wiz['step'] = 'options'
        wiz['options'] = []
        update.message.reply_text(
            "2/4: İndi *A* variantının mətnini yazın.\n\n_Ləğv: /cancel_",
            parse_mode='Markdown'
        )
        return True

    if step == 'options':
        wiz['options'].append(text.strip())
        if len(wiz['options']) < 5:
            letters = "ABCDE"
            next_letter = letters[len(wiz['options'])]
            update.message.reply_text(
                f"{len(wiz['options'])+1}/4 (variantlar): İndi *{next_letter}* variantının mətnini yazın.\n\n_Ləğv: /cancel_",
                parse_mode='Markdown'
            )
        else:
            # 5 variant toplandı — düzgün cavabı soruş
            wiz['step'] = 'correct'
            letters = "ABCDE"
            keyboard = []
            for i, opt in enumerate(wiz['options']):
                keyboard.append([InlineKeyboardButton(
                    f"{letters[i]}) {opt[:40]}",
                    callback_data=f"addq_correct_{i}"
                )])
            keyboard.append([InlineKeyboardButton("❌ Ləğv", callback_data="addq_cancel")])
            update.message.reply_text(
                "3/4: Düzgün cavabı seçin:",
                reply_markup=InlineKeyboardMarkup(keyboard)
            )
        return True

    # ── Redaktə wizard: qid və ya açar söz axtarışı ──
    if step == 'edit_search':
        # Rəqəm isə qid, əks halda axtarış
        s = text.strip()
        if s.isdigit():
            qid = int(s)
            if qid not in QUESTIONS_BY_ID:
                update.message.reply_text(f"❌ Sual #{qid} tapılmadı.")
                return True
            admin_wizard_data.pop(user.id, None)
            # Fake query obyekti yoxdur — mesaj göndərək
            ctx_msg = update.message
            # Menyunu yeni mesaj kimi göndər
            send_q_edit_menu_as_message(ctx_msg.chat_id, context, qid)
            return True
        else:
            # Axtarış
            needle = s.lower()
            matches = []
            for qid, (sid, q) in QUESTIONS_BY_ID.items():
                if needle in q['q'].lower():
                    matches.append((qid, q['q']))
                if len(matches) >= 15:
                    break
            if not matches:
                update.message.reply_text("❌ Tapılmadı. Başqa söz yazın və ya /cancel")
                return True
            lines = [f"🔎 *{len(matches)} nəticə:*"]
            keyboard = []
            for qid, qtext in matches:
                snippet = qtext[:60] + ("…" if len(qtext) > 60 else "")
                lines.append(f"`#{qid}` — {snippet}")
                keyboard.append([InlineKeyboardButton(f"✏️ #{qid} redaktə et", callback_data=f"adminq_show_{qid}")])
            keyboard.append([InlineKeyboardButton("❌ Ləğv", callback_data="admin_panel")])
            update.message.reply_text("\n\n".join(lines), parse_mode='Markdown',
                                       reply_markup=InlineKeyboardMarkup(keyboard))
            admin_wizard_data.pop(user.id, None)
            return True

    # ── Axtarış (yalnız siyahı) ──
    if step == 'search_keyword':
        needle = text.strip().lower()
        matches = []
        for qid, (sid, q) in QUESTIONS_BY_ID.items():
            if needle in q['q'].lower():
                matches.append((qid, q['q']))
            if len(matches) >= 20:
                break
        admin_wizard_data.pop(user.id, None)
        if not matches:
            update.message.reply_text("❌ Tapılmadı.")
            return True
        lines = [f"🔎 *{len(matches)} nəticə:*"]
        keyboard = []
        for qid, qtext in matches:
            snippet = qtext[:60] + ("…" if len(qtext) > 60 else "")
            lines.append(f"`#{qid}` — {snippet}")
            keyboard.append([InlineKeyboardButton(f"✏️ #{qid}", callback_data=f"adminq_show_{qid}")])
        keyboard.append([InlineKeyboardButton("⬅️ Panel", callback_data="admin_panel")])
        update.message.reply_text("\n\n".join(lines), parse_mode='Markdown',
                                   reply_markup=InlineKeyboardMarkup(keyboard))
        return True

    # ── Sual mətnini redaktə ──
    if step == 'edit_q_text':
        qid = wiz.get('qid')
        if qid in QUESTIONS_BY_ID:
            QUESTIONS_BY_ID[qid][1]['q'] = text.strip()
            save_data()
            update.message.reply_text(f"✅ Sual #{qid} mətni yeniləndi.")
            send_q_edit_menu_as_message(update.effective_chat.id, context, qid)
        admin_wizard_data.pop(user.id, None)
        return True

    # ── Cavab variantını redaktə ──
    if step == 'edit_answer':
        qid = wiz.get('qid'); idx = wiz.get('idx')
        if qid in QUESTIONS_BY_ID:
            q = QUESTIONS_BY_ID[qid][1]
            old = q['answers'][idx]
            q['answers'][idx] = text.strip()
            if q['correct'] == old:
                q['correct'] = text.strip()
            save_data()
            update.message.reply_text(f"✅ Sual #{qid}, cavab {wiz.get('letter')} yeniləndi.")
            send_q_edit_menu_as_message(update.effective_chat.id, context, qid)
        admin_wizard_data.pop(user.id, None)
        return True

    # ── Broadcast (bildiriş göndər) ──
    if step == 'broadcast_text':
        announcement = text.strip()
        admin_wizard_data.pop(user.id, None)
        all_users = get_all_user_ids()
        update.message.reply_text(f"📤 {len(all_users)} istifadəçiyə göndərilir...")
        success = 0; failed = 0
        for uid in all_users:
            try:
                context.bot.send_message(
                    chat_id=uid,
                    text=f"🆕 *Bildiriş!*\n\n📢 {announcement}",
                    parse_mode='Markdown'
                )
                success += 1
            except Exception:
                failed += 1
        update.message.reply_text(f"✅ Göndərildi: {success}\n❌ Uğursuz: {failed}")
        return True

    # ── Yeni Fənn wizard ──
    if step == 'subj_new_id':
        sid_new = text.strip().lower().replace(' ', '_')
        import re as _re2
        if not _re2.match(r'^[a-z0-9_]+$', sid_new):
            update.message.reply_text(
                "❌ ID yalnız latın hərfləri, rəqəm və alt xəttdən ibarət olmalıdır.\n"
                "Yenidən yazın və ya /cancel"
            )
            return True
        if sid_new in SUBJECTS_BY_ID:
            update.message.reply_text(
                f"❌ `{sid_new}` ID-li fənn artıq mövcuddur. Başqa ID seçin:\n\n_Ləğv: /cancel_",
                parse_mode='Markdown'
            )
            return True
        wiz['sid_new'] = sid_new
        wiz['step'] = 'subj_new_name'
        update.message.reply_text(
            f"2/3: ID qəbul edildi: `{sid_new}`\n\nİndi fənnin tam adını yazın:\n\n_Ləğv: /cancel_",
            parse_mode='Markdown'
        )
        return True

    if step == 'subj_new_name':
        wiz['name_new'] = text.strip()
        wiz['step'] = 'subj_new_emoji'
        update.message.reply_text(
            f"3/3: Ad: *{text.strip()}*\n\nFənn üçün emoji seçin (bir emoji yazın):\n\n_Ləğv: /cancel_",
            parse_mode='Markdown'
        )
        return True

    if step == 'subj_new_emoji':
        emoji_new = text.strip().split()[0] if text.strip() else '📚'
        sid_new = wiz.get('sid_new')
        name_new = wiz.get('name_new')
        # Yeni fənn yarat
        new_subj = {
            'id': sid_new,
            'name': name_new,
            'emoji': emoji_new,
            'topics': [],
            'all_questions': []
        }
        DATA['subjects'].append(new_subj)
        save_data()
        admin_wizard_data.pop(user.id, None)
        update.message.reply_text(
            f"✅ Fənn yaradıldı!\n\n{emoji_new} *{name_new}*\nID: `{sid_new}`\n\n"
            "İndi bu fənnə sual əlavə etmək üçün `/qadd` əmrindən və ya admin paneldəki "
            "Bulk Import-dan istifadə edə bilərsiniz.",
            parse_mode='Markdown'
        )
        show_admin_panel(update.effective_chat.id, context, user_id=user.id)
        return True

    # ── Mövzu əlavə et wizard ──
    if step == 'topic_add_name':
        sid = wiz.get('sid')
        subj = get_subject(sid)
        if not subj:
            admin_wizard_data.pop(user.id, None)
            update.message.reply_text("❌ Fənn tapılmadı.")
            return True
        topic_name = text.strip()
        # Eyni adlı mövzu var mı?
        existing_names = [t['name'].lower() for t in subj.get('topics', [])]
        if topic_name.lower() in existing_names:
            update.message.reply_text(
                f"⚠️ *{topic_name}* adlı mövzu artıq mövcuddur.\nBaşqa ad yazın və ya /cancel",
                parse_mode='Markdown'
            )
            return True
        subj.setdefault('topics', []).append({'name': topic_name, 'questions': []})
        save_data()
        admin_wizard_data.pop(user.id, None)
        update.message.reply_text(
            f"✅ Mövzu əlavə edildi: *{topic_name}*\n"
            f"Fənn: {subj['emoji']} {subj['name']}",
            parse_mode='Markdown'
        )
        show_admin_panel(update.effective_chat.id, context, user_id=user.id)
        return True

    # ── Mövzu adını dəyiş wizard ──
    if step == 'topic_rename':
        sid = wiz.get('sid')
        tidx = wiz.get('tidx')
        subj = get_subject(sid)
        if subj and tidx is not None and 0 <= tidx < len(subj.get('topics', [])):
            old_name = subj['topics'][tidx]['name']
            subj['topics'][tidx]['name'] = text.strip()
            save_data()
            admin_wizard_data.pop(user.id, None)
            update.message.reply_text(
                f"✅ Mövzu adı dəyişdirildi:\n*{old_name}* → *{text.strip()}*",
                parse_mode='Markdown'
            )
            show_admin_panel(update.effective_chat.id, context, user_id=user.id)
        else:
            admin_wizard_data.pop(user.id, None)
            update.message.reply_text("❌ Mövzu tapılmadı.")
        return True


    return False


def send_q_edit_menu_as_message(chat_id, context, qid):
    """show_question_edit_menu-nun mesaj versiyası (query olmayanda istifadə)."""
    if qid not in QUESTIONS_BY_ID:
        return
    sid, q = QUESTIONS_BY_ID[qid]
    subj = get_subject(sid)
    letters = "ABCDE"
    text = f"✏️ *Sual #{qid}* — {subj['name']}\n━━━━━━━━━━━━━━━━━\n\n*Q:* {q['q']}\n\n"
    for i, opt in enumerate(q['answers']):
        mark = "✅" if opt == q['correct'] else "  "
        text += f"{mark} *{letters[i]})* {opt}\n"
    diff = get_question_difficulty(qid)
    if diff is not None:
        text += f"\n📊 Düz cavab: {diff}%\n"

    keyboard = [
        [InlineKeyboardButton("📝 Sual mətni", callback_data=f"adminq_editq_{qid}")],
        [InlineKeyboardButton("A", callback_data=f"adminq_a_{qid}"),
         InlineKeyboardButton("B", callback_data=f"adminq_b_{qid}"),
         InlineKeyboardButton("C", callback_data=f"adminq_c_{qid}"),
         InlineKeyboardButton("D", callback_data=f"adminq_d_{qid}"),
         InlineKeyboardButton("E", callback_data=f"adminq_e_{qid}")],
        [InlineKeyboardButton("✅ Düzgün", callback_data=f"adminq_setcorrect_{qid}")],
        [InlineKeyboardButton("🗑 Sil", callback_data=f"adminq_del_{qid}")],
        [InlineKeyboardButton("⬅️ Admin panel", callback_data="admin_panel")]
    ]
    context.bot.send_message(chat_id=chat_id, text=text, parse_mode='Markdown',
                             reply_markup=InlineKeyboardMarkup(keyboard))


# ─── /newtest, /adminstats (mövcud) ───────────────────────────────────────────

@admin_only
def newtest_command(update: Update, context: CallbackContext):
    if not context.args:
        update.message.reply_text("ℹ️ `/newtest mətn`", parse_mode='Markdown')
        return
    announcement = " ".join(context.args)
    all_users = get_all_user_ids()
    success = 0; failed = 0
    keyboard = InlineKeyboardMarkup([[InlineKeyboardButton("🎯 Testi Başlat", callback_data="ad_done_start")]])
    update.message.reply_text(f"📤 {len(all_users)} istifadəçiyə göndərilir...")
    for uid in all_users:
        try:
            context.bot.send_message(
                chat_id=uid,
                text=f"🆕 *Yeni Test!*\n\n📢 {announcement}",
                parse_mode='Markdown',
                reply_markup=keyboard
            )
            success += 1
        except Exception:
            failed += 1
    update.message.reply_text(f"✅ {success}\n❌ {failed}")


@admin_only
def admin_stats_command(update: Update, context: CallbackContext):
    conn = get_conn()
    c = conn.cursor()
    c.execute('SELECT COUNT(*) FROM users'); total_users = c.fetchone()[0]
    c.execute('SELECT COUNT(*) FROM quiz_results'); total_quizzes = c.fetchone()[0]
    c.execute('SELECT COUNT(*) FROM referrals'); total_refs = c.fetchone()[0]
    c.execute('SELECT AVG(pct) FROM quiz_results'); avg_pct = round(c.fetchone()[0] or 0)
    c.execute('SELECT subject_id, COUNT(*) FROM quiz_results GROUP BY subject_id'); per_subj = c.fetchall()
    c.execute('SELECT COUNT(*) FROM question_reports WHERE resolved=0'); open_reports = c.fetchone()[0]
    conn.close()
    per_subj_text = ""
    if per_subj:
        per_subj_text = "\n\n📚 *Fənn üzrə test sayı:*\n"
        for sid, cnt in per_subj:
            s = get_subject(sid) if sid else None
            name = s['name'] if s else (sid or "köhnə")
            per_subj_text += f"   • {name}: {cnt}\n"
    update.message.reply_text(
        f"📊 *Bot Statistikası*\n━━━━━━━━━━━━━━━━━\n"
        f"👥 İstifadəçi: *{total_users}*\n"
        f"📝 Test: *{total_quizzes}*\n"
        f"📢 Referral: *{total_refs}*\n"
        f"📈 Ortalama: *{avg_pct}%*\n"
        f"🚩 Açıq şikayət: *{open_reports}*"
        f"{per_subj_text}",
        parse_mode='Markdown'
    )


# ─── QRUP REJİMİ ──────────────────────────────────────────────────────────────
#
# /quiz qrupda yazılır → qrupun adminləri sınaq başlada bilər.
# 1) Qrup üzvləri "✋ İştirak edirəm" düyməsinə basır (lobby).
# 2) Lobby başlatan "▶️ Başla" basır.
# 3) Hər sual qrupa göndərilir; iştirakçılar 30 saniyə içində cavab verir.
#    Hər iştirakçı üçün ilk cavab sayılır, dublikat ignore olunur.
# 4) Hər sual sonunda kim doğru/səhv cavablandı göstərilir + score table.
#
# Qrup sessiyası group_sessions[chat_id] saxlanılır.

def quiz_command(update: Update, context: CallbackContext):
    """Qrupda /quiz əmri — lobby aç."""
    chat = update.effective_chat
    if chat.type not in ("group", "supergroup"):
        update.message.reply_text(
            "ℹ️ Bu əmr yalnız qruplarda işləyir.\n"
            "Şəxsi sınaq üçün /start yazın."
        )
        return

    if chat.id in group_sessions and group_sessions[chat.id].get('active'):
        update.message.reply_text("⚠️ Qrupda artıq aktiv sınaq var. Gözləyin və ya /quizstop ilə dayandırın.")
        return

    # Default: ADİAK fənni, 10 sual. Daha sonra inline seçim əlavə oluna bilər.
    args = context.args
    subject_id = None
    count = 10
    if args:
        for a in args:
            if a.isdigit():
                count = max(3, min(int(a), 30))
            elif a in SUBJECTS_BY_ID:
                subject_id = a
    if not subject_id:
        # ən çox sualı olan fənni seç
        biggest = max(DATA['subjects'], key=lambda s: len(subject_all_questions(s)))
        subject_id = biggest['id']
    subj = get_subject(subject_id)
    if not subj or len(subject_all_questions(subj)) == 0:
        update.message.reply_text("❌ Bu fənnə suallar əlavə olunmayıb.")
        return

    pool = list(subject_all_questions(subj))
    random.shuffle(pool)
    questions = pool[:count]

    group_sessions[chat.id] = {
        'active': False,
        'questions': questions,
        'current': -1,  # lobby
        'subject_id': subject_id,
        'subject_name': subj['name'],
        'participants': {},   # user_id -> {name, score, wrong}
        'creator_id': update.effective_user.id,
        'answered_this_q': set(),
    }

    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("✋ İştirak edirəm", callback_data="group_join")],
        [InlineKeyboardButton("▶️ Başla (yalnız başladan)", callback_data="group_start")]
    ])
    context.bot.send_message(
        chat_id=chat.id,
        text=(
            f"🎮 *Qrup Sınağı — {subj.get('emoji', '📘')} {subj['name']}*\n\n"
            f"📝 {count} sual\n"
            f"👤 İştirak etmək üçün düyməyə basın.\n\n"
            f"Başlatmaq üçün: {update.effective_user.first_name} \"Başla\" düyməsinə basmalıdır."
        ),
        parse_mode='Markdown',
        reply_markup=keyboard
    )


def quizstop_command(update: Update, context: CallbackContext):
    chat = update.effective_chat
    if chat.id not in group_sessions:
        return
    sess = group_sessions[chat.id]
    if update.effective_user.id != sess.get('creator_id') and update.effective_user.id not in ADMIN_IDS:
        update.message.reply_text("Yalnız sınağı başladan dayandıra bilər.")
        return
    del group_sessions[chat.id]
    update.message.reply_text("⛔ Qrup sınağı dayandırıldı.")


def handle_group_join(query, context):
    chat_id = query.message.chat_id
    user = query.from_user
    sess = group_sessions.get(chat_id)
    if not sess:
        query.answer("Bu sınaq artıq aktual deyil.", show_alert=True)
        return
    if sess.get('active'):
        query.answer("Sınaq artıq başlayıb, qoşulmaq olmaz.", show_alert=True)
        return
    if user.id in sess['participants']:
        query.answer("Sən artıq qoşulmusan.")
        return
    sess['participants'][user.id] = {
        'name': user.first_name or user.username or "İstifadəçi",
        'score': 0,
        'wrong': 0
    }
    query.answer(f"✅ Qoşuldun, {user.first_name}!")
    # Lobby mesajını yenilə
    names = ", ".join(p['name'] for p in sess['participants'].values())
    try:
        query.edit_message_text(
            text=(
                f"🎮 *Qrup Sınağı — {sess['subject_name']}*\n\n"
                f"📝 {len(sess['questions'])} sual\n"
                f"👥 İştirakçılar ({len(sess['participants'])}): {names}\n\n"
                f"Başlatmaq üçün başladan \"Başla\" basmalıdır."
            ),
            parse_mode='Markdown',
            reply_markup=query.message.reply_markup
        )
    except Exception:
        pass


def handle_group_start(query, context):
    chat_id = query.message.chat_id
    user = query.from_user
    sess = group_sessions.get(chat_id)
    if not sess:
        query.answer("Sınaq tapılmadı.", show_alert=True)
        return
    if user.id != sess.get('creator_id'):
        query.answer("Yalnız sınağı başladan başlada bilər.", show_alert=True)
        return
    if not sess['participants']:
        query.answer("Heç kim qoşulmayıb.", show_alert=True)
        return
    sess['active'] = True
    sess['current'] = 0
    try: query.message.delete()
    except: pass
    send_group_next_question(chat_id, context)


def send_group_next_question(chat_id, context):
    sess = group_sessions.get(chat_id)
    if not sess:
        return
    idx = sess['current']
    total = len(sess['questions'])
    if idx >= total:
        show_group_result(chat_id, context)
        return

    q = sess['questions'][idx]
    answers = list(q['answers'])
    random.shuffle(answers)
    sess['shuffled'] = answers
    sess['answered_this_q'] = {}  # user_id -> chosen index

    labels = ['🅰', '🅱', '🇨', '🇩', '🇪']
    keyboard = []
    for i, ans in enumerate(answers):
        short = ans[:40] + ('…' if len(ans) > 40 else '')
        keyboard.append([InlineKeyboardButton(f"{labels[i]} {short}", callback_data=f"gans_{i}")])

    options_text = "\n".join(f"{labels[i]} {a}" for i, a in enumerate(answers))
    text = (
        f"🎮 *Qrup Sınağı — Sual {idx+1}/{total}*\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"*{q['q']}*\n\n"
        f"{options_text}\n\n"
        f"⏱ Hər kəs cavab verə bilər. Növbəti suala keçmək üçün \"⏭ Növbəti\" düyməsi."
    )
    keyboard.append([InlineKeyboardButton("⏭ Növbəti", callback_data="group_next")])
    msg = context.bot.send_message(
        chat_id=chat_id, text=text, parse_mode='Markdown',
        reply_markup=InlineKeyboardMarkup(keyboard)
    )
    sess['_q_msg_id'] = msg.message_id


def handle_group_answer(query, context):
    chat_id = query.message.chat_id
    user = query.from_user
    sess = group_sessions.get(chat_id)
    if not sess or not sess.get('active'):
        return
    if user.id not in sess['participants']:
        query.answer("Sən bu sınağa qoşulmamısan.", show_alert=True)
        return
    if user.id in sess.get('answered_this_q', {}):
        query.answer("Sən bu suala artıq cavab vermisən.")
        return
    chosen_idx = int(query.data.split("_")[1])
    answers = sess.get('shuffled', [])
    if chosen_idx >= len(answers):
        return
    chosen = answers[chosen_idx]
    q = sess['questions'][sess['current']]
    is_correct = (chosen == q['correct'])
    sess['answered_this_q'][user.id] = chosen_idx
    if is_correct:
        sess['participants'][user.id]['score'] += 1
        query.answer("✅ Düz!")
    else:
        sess['participants'][user.id]['wrong'] += 1
        query.answer("❌ Səhv.")


def show_group_result(chat_id, context):
    sess = group_sessions.get(chat_id)
    if not sess:
        return
    sorted_p = sorted(sess['participants'].values(), key=lambda x: -x['score'])
    medals = ["🥇", "🥈", "🥉"] + ["🏅"] * 20
    total = len(sess['questions'])

    lines = [f"🏁 *Qrup Sınağı Bitti*", f"📚 {sess['subject_name']}", "━━━━━━━━━━━━━━━━━"]
    for i, p in enumerate(sorted_p):
        pct = round(p['score'] / total * 100) if total > 0 else 0
        lines.append(f"{medals[i] if i < len(medals) else '•'} *{p['name']}* — {p['score']}/{total} ({pct}%)")

    context.bot.send_message(chat_id=chat_id, text="\n".join(lines), parse_mode='Markdown')
    if chat_id in group_sessions:
        del group_sessions[chat_id]


# Qrup sınağında "Növbəti" düyməsi üçün handle_group_next
def handle_group_next_advance(chat_id, context):
    sess = group_sessions.get(chat_id)
    if not sess:
        return
    sess['current'] += 1
    # Əvvəlki sual mesajını sil
    prev_id = sess.get('_q_msg_id')
    if prev_id:
        try:
            context.bot.delete_message(chat_id=chat_id, message_id=prev_id)
        except Exception:
            pass
    send_group_next_question(chat_id, context)


# ─── MAIN ─────────────────────────────────────────────────────────────────────

def main():
    global BOT_USERNAME
    init_db()
    updater = Updater(TOKEN, use_context=True)
    BOT_USERNAME = updater.bot.username
    log.info(f"Bot @{BOT_USERNAME} işə düşür...")

    dp = updater.dispatcher

    # İstifadəçi əmrləri
    dp.add_handler(CommandHandler("start",       start, pass_args=True))
    dp.add_handler(CommandHandler("profile",     profile_command))
    dp.add_handler(CommandHandler("leaderboard", leaderboard_command))
    dp.add_handler(CommandHandler("referral",    referral_command))

    # Qrup
    dp.add_handler(CommandHandler("quiz",     quiz_command, pass_args=True))
    dp.add_handler(CommandHandler("quizstop", quizstop_command))

    # Admin
    dp.add_handler(CommandHandler("admin",        admin_command))
    dp.add_handler(CommandHandler("newtest",      newtest_command))
    dp.add_handler(CommandHandler("adminstats",   admin_stats_command))
    dp.add_handler(CommandHandler("qadd",         qadd_command))
    dp.add_handler(CommandHandler("qedit",        qedit_command))
    dp.add_handler(CommandHandler("qdel",         qdel_command))
    dp.add_handler(CommandHandler("qsetq",        qsetq_command))
    dp.add_handler(CommandHandler("qseta",        qseta_command))
    dp.add_handler(CommandHandler("qsetcorrect",  qsetcorrect_command))
    dp.add_handler(CommandHandler("qsearch",      qsearch_command))
    dp.add_handler(CommandHandler("qhardest",     qhardest_command))
    dp.add_handler(CommandHandler("reports",      reports_command))
    dp.add_handler(CommandHandler("resolve",      resolve_command))

    # WebApp data (reklam tamamlandı siqnalı)
    dp.add_handler(MessageHandler(Filters.status_update.web_app_data, web_app_data_handler))

    # Sənəd (admin import üçün)
    dp.add_handler(MessageHandler(Filters.document, document_handler))

    # Mətn router: range diapazonu və admin wizard emal edir
    def _text_router(update, context):
        msg = update.effective_message
        if not msg or not msg.text:
            return
        text = msg.text.strip()
        chat_id = update.effective_chat.id
        user_id = update.effective_user.id

        # /cancel universal
        if text == "/cancel":
            if chat_id in range_pending:
                del range_pending[chat_id]
                msg.reply_text("❌ Diapazon ləğv edildi.")
                return
            if user_id in admin_wizard_data:
                admin_wizard_data.pop(user_id, None)
                msg.reply_text("❌ Ləğv edildi.")
                return
            msg.reply_text("ℹ️ Aktiv əməliyyat yoxdur.")
            return

        # 1) Adi istifadəçi: diapazon gözlənilirsə
        if chat_id in range_pending:
            sid = range_pending[chat_id]
            subject = get_subject(sid)
            # Format: "20-40" və ya "20 - 40"
            m = re.match(r"^\s*(\d+)\s*[-–—]\s*(\d+)\s*$", text)
            if not m:
                msg.reply_text(
                    "❌ Format səhvdir. Misal: `20-40`\n_Ləğv üçün /cancel_",
                    parse_mode='Markdown'
                )
                return
            start_id = int(m.group(1))
            end_id = int(m.group(2))
            if start_id > end_id:
                start_id, end_id = end_id, start_id
            if not subject:
                del range_pending[chat_id]
                msg.reply_text("❌ Fənn tapılmadı.")
                return
            pool = subject_all_questions(subject)
            count = sum(1 for q in pool if start_id <= q.get('id', 0) <= end_id)
            if count == 0:
                msg.reply_text(
                    f"❌ Bu diapazonda sual tapılmadı ({start_id}-{end_id}).\n"
                    "Başqa diapazon yazın və ya /cancel"
                )
                return
            del range_pending[chat_id]
            msg.reply_text(
                f"🎯 Sual *{start_id}* - *{end_id}* ({count} sual) başlayır...",
                parse_mode='Markdown'
            )
            start_range_quiz(chat_id, context, sid, start_id, end_id, user_id)
            return

        # 2) Admin wizard
        admin_text_handler(update, context)

    dp.add_handler(MessageHandler(Filters.text & ~Filters.command, _text_router))
    # /cancel əmri (slash ilə yazsalar da işləsin)
    def _cancel_cmd(update, context):
        chat_id = update.effective_chat.id
        user_id = update.effective_user.id
        if chat_id in range_pending:
            del range_pending[chat_id]
            update.message.reply_text("❌ Diapazon ləğv edildi.")
            return
        if user_id in admin_wizard_data:
            admin_wizard_data.pop(user_id, None)
            update.message.reply_text("❌ Ləğv edildi.")
            return
        update.message.reply_text("ℹ️ Aktiv əməliyyat yoxdur.")
    dp.add_handler(CommandHandler("cancel", _cancel_cmd))

    # Admin callback-ləri (pattern əsasında)
    dp.add_handler(CallbackQueryHandler(
        admin_callback_handler,
        pattern=r"^(admin_|adminq_|addq_|pdfimp_)"
    ))

    # Callback router (əsas)
    dp.add_handler(CallbackQueryHandler(callback_handler))

    updater.start_polling(allowed_updates=["message", "callback_query", "chat_member"])
    log.info("Bot işə düşdü.")
    updater.idle()


if __name__ == '__main__':
    main()
