# -*- PRO ANTIBAN -*-
"""
PRO ANTIBAN - Dashboard Server
Full Web Dashboard + Login Protection (no captcha) + Persistent sessions
+ Admin Panel (bulk add) + Access Token Generator
"""
import asyncio
import json
import os
import re
import time
import hmac
import random
import string
import hashlib
from typing import Dict, List, Any, Optional
from urllib.parse import unquote, parse_qs, urlsplit
from aiohttp import web, ClientSession, ClientTimeout
from aiohttp_session import setup as setup_session, get_session
from aiohttp_session.cookie_storage import EncryptedCookieStorage

# ==================== GLOBAL STATE ====================
class BotState:
    def __init__(self):
        self.accounts: Dict[str, Dict[str, Any]] = {}
        self.logs: List[Dict[str, Any]] = []
        self.max_logs = 200
        self.total_matches = 0
        self.total_gained_exp = 0
        self.start_time = time.time()
        self.account_workers: Dict[str, asyncio.Task] = {}
        self.refresh_callbacks: Dict[str, Any] = {}
        self.account_credentials: Dict[str, Dict[str, Any]] = {}
        # Blocklist of UIDs the admin deleted. Prevents a still-running worker
        # from re-registering the account into the live state a moment later.
        self.deleted_uids: set = set()

    def log(self, message: str, level: str = "info", uid: Optional[str] = None):
        entry = {
            "time": time.strftime("%H:%M:%S"),
            "level": level,
            "message": message,
            "uid": uid
        }
        self.logs.append(entry)
        if len(self.logs) > self.max_logs:
            self.logs.pop(0)

    def register_account(self, uid: str, nickname: str, region: str, level: int, exp: int, likes: int = 0):
        uid_str = str(uid)
        if uid_str in self.deleted_uids:
            return
        if uid_str not in self.accounts:
            self.accounts[uid_str] = {
                "uid": uid_str,
                "nickname": nickname or f"Player_{uid_str[:6]}",
                "region": region or "BD",
                "level": level or 1,
                "initial_exp": exp,
                "current_exp": exp,
                "gained_exp": 0,
                "likes": likes or 0,
                "status": "ONLINE",
                "matches_played": 0,
                "active_matches": 0,
                "last_match_time": None,
                "last_updated": time.strftime("%H:%M:%S"),
                "is_paused": False,
                "uptime_seconds": int(time.time()),
                "match_history": []
            }
        else:
            acc = self.accounts[uid_str]
            if nickname:
                acc["nickname"] = nickname
            if region:
                acc["region"] = region
            if level:
                acc["level"] = level
            acc["current_exp"] = exp
            acc["gained_exp"] = max(0, exp - acc["initial_exp"])
            acc["likes"] = likes
            acc["status"] = "ONLINE"
            acc["last_updated"] = time.strftime("%H:%M:%S")
        self.recalc_totals()

    def update_exp(self, uid: str, current_exp: int, level: Optional[int] = None):
        uid_str = str(uid)
        if uid_str in self.deleted_uids:
            return
        if uid_str in self.accounts:
            acc = self.accounts[uid_str]
            old_exp = acc["current_exp"]
            acc["current_exp"] = current_exp
            if level is not None and level > 0:
                acc["level"] = level
            acc["gained_exp"] = max(0, current_exp - acc["initial_exp"])
            acc["last_updated"] = time.strftime("%H:%M:%S")
            diff = current_exp - old_exp
            if diff > 0:
                self.log(f"{acc['nickname']} gained +{diff} EXP! Total: +{acc['gained_exp']}", "success", uid_str)
            self.recalc_totals()

    def update_status(self, uid: str, status: str, active_matches: Optional[int] = None):
        uid_str = str(uid)
        if uid_str in self.deleted_uids:
            return
        if uid_str in self.accounts:
            self.accounts[uid_str]["status"] = status
            if active_matches is not None:
                self.accounts[uid_str]["active_matches"] = active_matches
            self.accounts[uid_str]["last_updated"] = time.strftime("%H:%M:%S")

    def increment_match(self, uid: str):
        uid_str = str(uid)
        self.total_matches += 1
        if uid_str in self.deleted_uids:
            return
        if uid_str in self.accounts:
            acc = self.accounts[uid_str]
            acc["matches_played"] += 1
            acc["last_match_time"] = time.strftime("%H:%M:%S")
            acc["last_updated"] = time.strftime("%H:%M:%S")
            history = acc.get("match_history", [])
            history.append({
                "time": time.strftime("%H:%M:%S"),
                "msg": f"Match #{acc['matches_played']} completed"
            })
            if len(history) > 20:
                history.pop(0)
            acc["match_history"] = history
            self.log(f"{acc['nickname']} finished Match #{acc['matches_played']}", "info", uid_str)

    def recalc_totals(self):
        self.total_gained_exp = sum(acc.get("gained_exp", 0) for acc in self.accounts.values())

    def get_exp_per_hour(self) -> int:
        elapsed = max(1, time.time() - self.start_time)
        return int(self.total_gained_exp / (elapsed / 3600))

    def get_total_active_matches(self) -> int:
        return sum(acc.get("active_matches", 0) for acc in self.accounts.values())

bot_state = BotState()

# ==================== PATHS ====================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
TEMPLATES_DIR = os.path.join(BASE_DIR, "templates")
STATIC_DIR = os.path.join(TEMPLATES_DIR, "static")
LOGIN_PATH = os.path.join(TEMPLATES_DIR, "login.html")
ADMIN_PATH = os.path.join(TEMPLATES_DIR, "admin.html")
INDEX_PATH = os.path.join(TEMPLATES_DIR, "index.html")
ACCOUNTS_FILE = "accounts.json"
USERS_FILE = "users.json"
TOKEN_CACHE_FILE = "token_cache.json"
DEVICES_FILE = "devices.json"

# ==================== AUTH HELPERS ====================
# users.json can grow large (up to 50k logins), so cache it in memory and only
# re-read when the file actually changes (checked by mtime).
_users_cache: Dict[str, Any] = {"mtime": None, "data": {}}


def load_users():
    try:
        mtime = os.path.getmtime(USERS_FILE) if os.path.exists(USERS_FILE) else None
    except OSError:
        mtime = None
    if mtime is not None and _users_cache.get("mtime") == mtime:
        return _users_cache["data"]
    data = {}
    if mtime is not None:
        try:
            with open(USERS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            data = {}
    _users_cache["mtime"] = mtime
    _users_cache["data"] = data
    return data

def save_users(users):
    tmp = USERS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(users, f, indent=2)
    os.replace(tmp, USERS_FILE)
    # Invalidate the cache so the next read sees the change even if the file
    # mtime resolution is coarse.
    _users_cache["mtime"] = None
    _users_cache["data"] = users


def user_is_active(user: Dict[str, Any]) -> bool:
    """Admins never expire. Normal logins expire once their days run out."""
    if not user:
        return False
    if user.get('role') == 'admin':
        return True
    exp = user.get('expires_at') or 0
    try:
        exp = float(exp)
    except Exception:
        exp = 0
    if exp and time.time() > exp:
        return False
    return True


def days_left(user: Dict[str, Any]) -> int:
    """Remaining whole days for a login (0 = unlimited for admins)."""
    if user.get('role') == 'admin':
        return 0
    exp = user.get('expires_at') or 0
    try:
        exp = float(exp)
    except Exception:
        exp = 0
    if not exp:
        return 0
    return max(0, int((exp - time.time()) // 86400))


def count_accounts_by(owner: str) -> int:
    """How many game accounts someone has already deployed."""
    if not os.path.exists(ACCOUNTS_FILE):
        return 0
    try:
        with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception:
        return 0
    return sum(1 for a in data if a.get('added_by') == owner)


# ==================== BOT PROTECTION (no captcha) ====================
# A signed, stateless login token is handed out with the login page and
# required back on POST. A bot that hits /login directly (or posts without
# first loading the form) is rejected. Plus a hidden honeypot field and a
# per-IP rate limit. Nothing ugly is shown to real users.
WEB_SECRET = 'pro_antiban_web_secret_fixed_2026_do_not_change'
LOGIN_TOKEN_COOKIE = 'pro_login_tok'
LOGIN_TOKEN_TTL = 86400  # 24h

_login_attempts: Dict[str, List[float]] = {}
RATE_WINDOW = 60.0
RATE_MAX = 15


def _client_ip(request: web.Request) -> str:
    xff = request.headers.get('X-Forwarded-For')
    if xff:
        return xff.split(',')[0].strip()
    return request.remote or 'unknown'


def _rate_ok(ip: str) -> bool:
    now = time.time()
    hits = [t for t in _login_attempts.get(ip, []) if now - t < RATE_WINDOW]
    if len(hits) >= RATE_MAX:
        _login_attempts[ip] = hits
        return False
    hits.append(now)
    _login_attempts[ip] = hits
    return True


def issue_login_token() -> str:
    ts = str(int(time.time()))
    sig = hmac.new(WEB_SECRET.encode(), ts.encode(), hashlib.sha256).hexdigest()[:32]
    return f"{ts}.{sig}"


def login_token_state(token: Optional[str]) -> str:
    if not token or not isinstance(token, str) or token.count('.') != 1:
        return 'missing'
    ts, _, sig = token.partition('.')
    expected = hmac.new(WEB_SECRET.encode(), ts.encode(), hashlib.sha256).hexdigest()[:32]
    if not hmac.compare_digest(sig, expected):
        return 'bad'
    try:
        if time.time() - float(ts) > LOGIN_TOKEN_TTL:
            return 'expired'
    except Exception:
        return 'bad'
    return 'ok'


async def auth_required(request):
    session = await get_session(request)
    if not session.get("logged_in"):
        if request.path.startswith('/api/'):
            raise web.HTTPUnauthorized(
                text='{"status":"error","error":"unauthorized"}',
                content_type='application/json',
            )
        raise web.HTTPFound('/login')
    # Re-validate on EVERY request so an expired or deleted login loses access
    # immediately, even though its session cookie is still valid for 30 days.
    user = load_users().get(session.get("username"))
    if not user_is_active(user):
        session.clear()
        if request.path.startswith('/api/'):
            raise web.HTTPUnauthorized(
                text='{"status":"error","error":"expired"}',
                content_type='application/json',
            )
        raise web.HTTPFound('/login')
    return session

# ==================== HANDLERS ====================
async def handle_login_get(request: web.Request) -> web.Response:
    session = await get_session(request)
    if session.get("logged_in"):
        raise web.HTTPFound('/admin' if session.get('role') == 'admin' else '/')
    if os.path.exists(LOGIN_PATH):
        with open(LOGIN_PATH, "r", encoding="utf-8") as f:
            content = f.read()
    else:
        content = "<h1>login.html missing</h1>"
    resp = web.Response(text=content, content_type="text/html", charset="utf-8")
    # Hand the browser a fresh signed login token (invisible to the user).
    resp.set_cookie(
        LOGIN_TOKEN_COOKIE, issue_login_token(),
        max_age=LOGIN_TOKEN_TTL, httponly=True, samesite='Lax', path='/',
    )
    return resp

async def handle_login_post(request: web.Request) -> web.Response:
    try:
        if not _rate_ok(_client_ip(request)):
            return web.json_response(
                {"status": "error", "error": "Too many attempts. Please wait a minute and try again."},
                status=429,
            )
        data = await request.post()
        username = str(data.get('username', '')).strip()
        password = str(data.get('password', '')).strip()
        # Honeypot: real users never see or fill this hidden field.
        if str(data.get('website', '')).strip():
            return web.json_response({"status": "error", "error": "Verification failed"})
        # The signed login token must come back from a page we served.
        if login_token_state(request.cookies.get(LOGIN_TOKEN_COOKIE)) != 'ok':
            return web.json_response(
                {"status": "error", "error": "Verification failed - reload the page and try again"},
                status=403,
            )
        users = load_users()
        if username in users and users[username].get('password') == password:
            user = users[username]
            if not user_is_active(user):
                return web.json_response({
                    "status": "error",
                    "error": "This account has expired. Please contact the admin.",
                })
            session = await get_session(request)
            session['logged_in'] = True
            session['username'] = username
            session['role'] = user.get('role', 'user')
            resp = web.json_response({"status": "ok", "redirect": "/admin" if session['role'] == 'admin' else "/"})
            resp.set_cookie(
                LOGIN_TOKEN_COOKIE, issue_login_token(),
                max_age=LOGIN_TOKEN_TTL, httponly=True, samesite='Lax', path='/',
            )
            return resp
        return web.json_response({"status": "error", "error": "Invalid credentials"})
    except Exception as e:
        return web.json_response({"status": "error", "error": str(e)})

async def handle_logout(request: web.Request) -> web.Response:
    session = await get_session(request)
    session.clear()
    raise web.HTTPFound('/login')

async def handle_admin_get(request: web.Request) -> web.Response:
    session = await auth_required(request)
    if session.get('role') != 'admin':
        raise web.HTTPFound('/')
    if os.path.exists(ADMIN_PATH):
        with open(ADMIN_PATH, "r", encoding="utf-8") as f:
            content = f.read()
        return web.Response(text=content, content_type="text/html", charset="utf-8")
    return web.Response(text="<h1>admin.html missing</h1>", content_type="text/html")

async def handle_index(request: web.Request) -> web.Response:
    await auth_required(request)
    if os.path.exists(INDEX_PATH):
        with open(INDEX_PATH, "r", encoding="utf-8") as f:
            content = f.read()
        return web.Response(text=content, content_type="text/html", charset="utf-8")
    content = "<html><body><h1>index.html missing</h1></body></html>"
    return web.Response(text=content, content_type="text/html")

async def handle_get_stats(request: web.Request) -> web.Response:
    await auth_required(request)
    accounts_data = list(bot_state.accounts.values())
    accounts_data.sort(key=lambda x: x.get("gained_exp", 0), reverse=True)
    return web.json_response({
        "total_accounts": len(bot_state.accounts),
        "total_matches": bot_state.total_matches,
        "total_matches_started": bot_state.total_matches,
        "total_gained_exp": bot_state.total_gained_exp,
        "total_active_matches": bot_state.get_total_active_matches(),
        "exp_per_hour": bot_state.get_exp_per_hour(),
        "accounts": accounts_data,
        "logs": bot_state.logs[-60:],
        "uptime": int(time.time() - bot_state.start_time)
    })

async def handle_me(request: web.Request) -> web.Response:
    session = await auth_required(request)
    users = load_users()
    u = users.get(session['username'], {})
    return web.json_response({
        "username": session['username'],
        "role": u.get('role', session.get('role', 'user')),
        "days_left": days_left(u),
        "max_accounts": int(u.get('max_accounts', 0) or 0),
        "used_accounts": count_accounts_by(session['username']),
    })


async def handle_bulk_add(request: web.Request) -> web.Response:
    """Bulk-create WEBSITE LOGIN accounts (username/password) with a validity
    in days and a per-user deploy limit (how many game accounts they may add)."""
    session = await auth_required(request)
    if session.get('role') != 'admin':
        return web.json_response({"status": "error", "error": "Admin only"})
    try:
        data = await request.json()
        count = int(data.get('count', 0))
        days = int(data.get('days', 0)) or 0
        # per_user = how many game accounts each login may deploy ("places")
        per_user = int(data.get('per_user', 0)) or 0
        prefix = str(data.get('prefix', 'ACC')).strip() or 'ACC'
        users = load_users()
        admin = users.get(session['username'], {})
        max_bulk = int(admin.get('max_bulk_add', 50000))
        if count <= 0:
            return web.json_response({"status": "error", "error": "Invalid count"})
        if count > max_bulk:
            return web.json_response({"status": "error", "error": f"Max {max_bulk} accounts per bulk"})
        now = time.time()
        expires_at = (now + days * 86400) if days > 0 else 0
        created = []
        for _ in range(count):
            # Unique, easy-to-share username
            while True:
                uname = prefix + ''.join(random.choices(string.digits, k=7))
                if uname not in users:
                    break
            pwd = ''.join(random.choices(string.ascii_uppercase + string.digits, k=8))
            users[uname] = {
                "username": uname,
                "password": pwd,
                "role": "user",
                "days": days,
                "created_at": now,
                "expires_at": expires_at,
                "max_accounts": per_user,
                "added_by": session['username'],
            }
            created.append({
                "username": uname,
                "password": pwd,
                "days": days,
                "expires_at": expires_at,
                "max_accounts": per_user,
            })
        save_users(users)
        bot_state.log(
            f"Admin {session['username']} created {len(created)} login accounts ({days} days, limit {per_user})",
            "success",
        )
        return web.json_response({"status": "ok", "added": len(created), "accounts": created})
    except Exception as e:
        return web.json_response({"status": "error", "error": str(e)})


async def handle_list_users(request: web.Request) -> web.Response:
    """List website login accounts (admins excluded) for the admin panel."""
    session = await auth_required(request)
    if session.get('role') != 'admin':
        return web.json_response({"status": "error", "error": "Admin only"})
    users = load_users()
    out = []
    for name, u in users.items():
        if u.get('role') == 'admin':
            continue
        out.append({
            "username": name,
            "password": u.get('password', ''),
            "days": u.get('days', 0),
            "days_left": days_left(u),
            "expires_at": u.get('expires_at', 0),
            "max_accounts": u.get('max_accounts', 0),
            "used_accounts": count_accounts_by(name),
            "added_by": u.get('added_by', ''),
            "created_at": u.get('created_at', 0),
            "active": user_is_active(u),
        })
    out.sort(key=lambda x: x.get('created_at') or 0, reverse=True)
    return web.json_response(out)


async def handle_delete_user(request: web.Request) -> web.Response:
    session = await auth_required(request)
    if session.get('role') != 'admin':
        return web.json_response({"status": "error", "error": "Admin only"})
    try:
        data = await request.json()
        username = str(data.get('username', '')).strip()
        users = load_users()
        target = users.get(username)
        if not target:
            return web.json_response({"status": "error", "error": "User not found"})
        if target.get('role') == 'admin':
            return web.json_response({"status": "error", "error": "Cannot delete an admin"})
        del users[username]
        save_users(users)
        bot_state.log(f"Login account {username} removed by {session['username']}", "warning")
        return web.json_response({"status": "ok"})
    except Exception as e:
        return web.json_response({"status": "error", "error": str(e)})

async def handle_add_account(request: web.Request) -> web.Response:
    session = await auth_required(request)
    try:
        data = await request.json()
        existing = []
        if os.path.exists(ACCOUNTS_FILE):
            try:
                with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                    existing = json.load(f)
            except:
                existing = []
        owner = session['username']
        # Enforce the per-login deploy limit ("places"). Admins are unlimited.
        user = load_users().get(owner, {})
        if user.get('role') != 'admin':
            limit = int(user.get('max_accounts', 0) or 0)
            if limit > 0:
                # Replacing one you already own does not count as a new deploy.
                is_replace = False
                if "uid" in data and "password" in data:
                    is_replace = any(str(a.get("uid")) == str(data["uid"]).strip() and a.get('added_by') == owner for a in existing)
                elif "token" in data:
                    is_replace = any(a.get("token") == str(data["token"]).strip() and a.get('added_by') == owner for a in existing)
                if not is_replace and count_accounts_by(owner) >= limit:
                    return web.json_response({
                        "status": "error",
                        "error": f"Limit reached: your account may deploy up to {limit} accounts",
                    })
        if "uid" in data and "password" in data:
            uid = str(data["uid"]).strip()
            pwd = str(data["password"]).strip()
            if not uid or not pwd:
                return web.json_response({"status": "error", "error": "UID and Password required"})
            bot_state.deleted_uids.discard(uid)
            existing = [acc for acc in existing if str(acc.get("uid")) != uid]
            existing.append({"uid": uid, "password": pwd, "days": data.get('days', 0), "added_by": owner})
        elif "token" in data:
            token = str(data["token"]).strip()
            if not token:
                return web.json_response({"status": "error", "error": "Token required"})
            bot_state.deleted_uids.discard(token)
            existing = [acc for acc in existing if acc.get("token") != token]
            existing.append({"token": token, "days": data.get('days', 0), "added_by": owner})
        else:
            return web.json_response({"status": "error", "error": "Invalid payload"})
        with open(ACCOUNTS_FILE, "w", encoding="utf-8") as f:
            json.dump(existing, f, indent=2)
        bot_state.log(f"New account added: {data.get('uid') or 'Token'}", "success")
        if "on_account_added" in bot_state.refresh_callbacks:
            asyncio.create_task(bot_state.refresh_callbacks["on_account_added"](data))
        return web.json_response({"status": "ok"})
    except Exception as e:
        return web.json_response({"status": "error", "error": str(e)})

async def handle_delete_account(request: web.Request) -> web.Response:
    session = await auth_required(request)
    try:
        data = await request.json()
        uid = str(data.get("uid")).strip()
        # Mark as deleted FIRST so any in-flight worker callback is ignored.
        bot_state.deleted_uids.add(uid)
        # Clean accounts.json
        if os.path.exists(ACCOUNTS_FILE):
            with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                existing = json.load(f)
            existing = [acc for acc in existing if str(acc.get("uid")) != uid and str(acc.get("token", ""))[:30] != uid]
            with open(ACCOUNTS_FILE, "w", encoding="utf-8") as f:
                json.dump(existing, f, indent=2)
        # Clean token_cache
        if os.path.exists(TOKEN_CACHE_FILE):
            try:
                with open(TOKEN_CACHE_FILE, "r", encoding="utf-8") as f:
                    tc = json.load(f)
                tc.pop(uid, None)
                with open(TOKEN_CACHE_FILE, "w", encoding="utf-8") as f:
                    json.dump(tc, f, indent=2)
            except:
                pass
        # Clean devices
        if os.path.exists(DEVICES_FILE):
            try:
                with open(DEVICES_FILE, "r", encoding="utf-8") as f:
                    dc = json.load(f)
                dc.pop(uid, None)
                with open(DEVICES_FILE, "w", encoding="utf-8") as f:
                    json.dump(dc, f, indent=2)
            except:
                pass
        # Clean live state (also cover token-keyed workers stored under uid[:10])
        bot_state.accounts.pop(uid, None)
        for key in [uid, uid[:10], uid[:20]]:
            task = bot_state.account_workers.pop(key, None)
            if task is not None:
                try:
                    task.cancel()
                except Exception:
                    pass
        bot_state.log(f"Account {uid} removed by {session['username']}", "warning", uid)
        return web.json_response({"status": "ok"})
    except Exception as e:
        return web.json_response({"status": "error", "error": str(e)})

async def handle_refresh_account(request: web.Request) -> web.Response:
    await auth_required(request)
    try:
        data = await request.json()
        uid = str(data.get("uid")).strip()
        if "on_refresh_account" in bot_state.refresh_callbacks:
            asyncio.create_task(bot_state.refresh_callbacks["on_refresh_account"](uid))
        return web.json_response({"status": "ok"})
    except Exception as e:
        return web.json_response({"status": "error", "error": str(e)})

async def handle_pause_account(request: web.Request) -> web.Response:
    await auth_required(request)
    try:
        data = await request.json()
        uid = str(data.get("uid")).strip()
        if uid in bot_state.accounts:
            acc = bot_state.accounts[uid]
            acc["is_paused"] = not acc.get("is_paused", False)
            if acc["is_paused"]:
                acc["status"] = "PAUSED"
            else:
                acc["status"] = "ONLINE"
            return web.json_response({"status": "ok", "is_paused": acc["is_paused"]})
        return web.json_response({"status": "error", "error": "Account not found"})
    except Exception as e:
        return web.json_response({"status": "error", "error": str(e)})

async def handle_pause_all(request: web.Request) -> web.Response:
    await auth_required(request)
    try:
        all_paused = all(acc.get("is_paused", False) for acc in bot_state.accounts.values()) if bot_state.accounts else False
        new_state = not all_paused
        for acc in bot_state.accounts.values():
            acc["is_paused"] = new_state
            acc["status"] = "PAUSED" if new_state else "ONLINE"
        return web.json_response({"status": "ok", "all_paused": new_state})
    except Exception as e:
        return web.json_response({"status": "error", "error": str(e)})

async def handle_restart_account(request: web.Request) -> web.Response:
    await auth_required(request)
    try:
        data = await request.json()
        uid = str(data.get("uid")).strip()
        if uid in bot_state.account_workers:
            bot_state.account_workers[uid].cancel()
        return web.json_response({"status": "ok"})
    except Exception as e:
        return web.json_response({"status": "error", "error": str(e)})

async def handle_clear_logs(request: web.Request) -> web.Response:
    await auth_required(request)
    try:
        bot_state.logs.clear()
        return web.json_response({"status": "ok"})
    except Exception as e:
        return web.json_response({"status": "error", "error": str(e)})

async def handle_get_accounts_json(request: web.Request) -> web.Response:
    await auth_required(request)
    existing = []
    if os.path.exists(ACCOUNTS_FILE):
        try:
            with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                existing = json.load(f)
        except:
            existing = []
    return web.json_response(existing)

# ==================== TOKEN GENERATOR (EAT -> access token) ====================
# Garena's own support-callback endpoint answers a valid EAT with a 302 whose
# Location query carries access_token / account_id / nickname / region - the
# same thing the standalone generator sites do, but served from our own backend
# so tokens never leave this site.
_EAT_RE = re.compile(r"^[A-Za-z0-9._\-]{16,2000}$")


def extract_eat(raw: str) -> str:
    """Accept either the full callback URL or the bare ?eat= value."""
    raw = str(raw or "").strip().strip('"\'')
    if not raw:
        return ""
    if "eat=" in raw.lower():
        m = re.search(r"[?&/]eat=([^&#\s]+)", raw, re.IGNORECASE)
        if not m:
            m = re.search(r"eat=([^&#\s]+)", raw, re.IGNORECASE)
        if m:
            return unquote(m.group(1)).strip()
    return raw


async def handle_token_generate(request: web.Request) -> web.Response:
    await auth_required(request)
    try:
        data = await request.json()
    except Exception:
        return web.json_response({"status": "error", "error": "Invalid request"}, status=400)

    eat = extract_eat(data.get("token", ""))
    if not eat or not _EAT_RE.match(eat):
        return web.json_response({
            "status": "error",
            "error": "Not a valid EAT - paste the full callback URL or the ?eat= value",
        })

    location = ""
    try:
        timeout = ClientTimeout(total=20)
        headers = {
            "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                           "AppleWebKit/537.36 (KHTML, like Gecko) "
                           "Chrome/124.0.0.0 Safari/537.36"),
        }
        async with ClientSession(timeout=timeout, headers=headers) as session:
            async with session.get(
                "https://api-otrss.garena.com/support/callback/",
                params={"access_token": eat},
                allow_redirects=False,
            ) as resp:
                location = resp.headers.get("Location", "") or ""
    except Exception as e:
        bot_state.log(f"[TOKEN] Garena callback unreachable: {e}", "warning")
        return web.json_response({"status": "error", "error": f"Could not reach Garena: {e}"})

    if not location:
        return web.json_response({
            "status": "error",
            "error": "Conversion failed - the token is invalid or already expired",
        })

    q = parse_qs(urlsplit(location).query)
    first = lambda k: (q.get(k) or [""])[0]
    access_token = first("access_token")
    if not access_token:
        return web.json_response({
            "status": "error",
            "error": "Conversion failed - the token is invalid or already expired",
        })
    bot_state.log(
        f"[TOKEN] Generated access token for {first('nickname') or '?'}",
        "success",
    )
    return web.json_response({
        "status": "ok",
        "access_token": access_token,
        "account_id": first("account_id") or first("uid"),
        "nickname": first("nickname"),
        "region": first("region"),
    })


# ==================== SERVER START ====================
async def start_web_dashboard(host: str = "0.0.0.0", port: int = 20333):
    app = web.Application()
    # Session setup - fixed key + 30-day cookie so an admin stays logged in
    # even if the source/process restarts (cookie is verified client-side).
    secret_key = '5Rue2xdfS34BP3UjXUf3fWmH9cfvK2JKdideDm0xbi0='
    setup_session(app, EncryptedCookieStorage(
        secret_key, cookie_name='PRO_SESSION', max_age=30 * 24 * 3600,
    ))
    # Routes
    app.router.add_get("/", handle_index)
    app.router.add_get("/login", handle_login_get)
    app.router.add_post("/login", handle_login_post)
    app.router.add_get("/logout", handle_logout)
    app.router.add_get("/admin", handle_admin_get)
    app.router.add_get("/api/stats", handle_get_stats)
    app.router.add_get("/api/me", handle_me)
    app.router.add_post("/api/account/add", handle_add_account)
    app.router.add_post("/api/account/delete", handle_delete_account)
    app.router.add_post("/api/account/refresh", handle_refresh_account)
    app.router.add_post("/api/account/pause", handle_pause_account)
    app.router.add_post("/api/account/pause_all", handle_pause_all)
    app.router.add_post("/api/account/restart", handle_restart_account)
    app.router.add_post("/api/logs/clear", handle_clear_logs)
    app.router.add_post("/api/admin/bulk_add", handle_bulk_add)
    app.router.add_get("/api/admin/accounts", handle_get_accounts_json)
    app.router.add_get("/api/admin/users", handle_list_users)
    app.router.add_post("/api/admin/user_delete", handle_delete_user)
    app.router.add_post("/api/token/generate", handle_token_generate)
    if os.path.exists(STATIC_DIR):
        app.router.add_static("/static", STATIC_DIR)
        print(f"[+] Static folder: {STATIC_DIR}")
    else:
        os.makedirs(STATIC_DIR, exist_ok=True)
        print(f"[!] Created static folder: {STATIC_DIR}")
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, host, port)
    await site.start()
    print(f"[+] Web Dashboard: http://{host}:{port}")
    print(f"[+] Admin Login: proegy / adminproegy1")

if __name__ == "__main__":
    import sys
    async def main():
        await start_web_dashboard("0.0.0.0", 20333)
        await asyncio.Future()
    asyncio.run(main())
