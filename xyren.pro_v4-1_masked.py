import os
import time
import random
import io
import re
import uuid
import string
import threading
from datetime import datetime
import requests
from flask import Flask, request, jsonify
from PIL import Image, ImageDraw, ImageFont

app = Flask(__name__)

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
ZAPUPI_API_KEY = os.environ.get("ZAPUPI_API_KEY")
BOT_USERNAME = "@Xyren_upibot"
WINS_CHANNEL_ID = os.environ.get("WINS_CHANNEL_ID", "3555754688")
WITHDRAW_LOG_CHANNEL_ID = os.environ.get("WITHDRAW_LOG_CHANNEL_ID", "3975966539")
WINS_CHANNEL_USERNAME = "xyren_wins"

TELEGRAM_API_URL = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}"

ADMIN_USER_ID = 1822336097
admin_list = {ADMIN_USER_ID}

approved_groups = set()

user_balances = {}
user_currency = {}
user_usernames = {}
user_first_names = {}
username_to_id = {}
user_stats = {}
user_deposits = {}
user_withdrawals = {}
user_bet_logs = {}
deposit_history = []
withdrawal_history = []
banned_users = set()

active_games = {}
active_7up_games = {}
pending_game_setup = {}
open_pvp_challenges = {}
active_pvp_games = {}
active_bj_games = {}
post_match_actions = {}
button_owners = {}  # (chat_id, message_id) -> user_id who owns that message's buttons
NOT_YOUR_MESSAGE_TEXT = "This is not your message ❌"
pending_manual_txns = {}
turn_locks = {}

def get_turn_lock(lock_key):
    if lock_key not in turn_locks:
        turn_locks[lock_key] = threading.Lock()
    return turn_locks[lock_key]

def get_active_game_summary(user_id):
    if user_id in active_7up_games:
        g7 = active_7up_games[user_id]
        gid = g7.get("game_id")
        return f"7Up (`{gid}`)" if gid else "7Up"
    if user_id in globals().get("active_mines_games", {}):
        gid = active_mines_games[user_id].get("game_id")
        return f"Mines (`{gid}`)"
    if user_id in globals().get("active_tower_games", {}):
        gid = active_tower_games[user_id].get("game_id")
        return f"Tower (`{gid}`)"
    if user_id in active_bj_games:
        gbj = active_bj_games[user_id]
        gid = gbj.get("game_id")
        return f"Blackjack (`{gid}`)" if gid else "Blackjack"
    if user_id in active_games:
        ref = active_games[user_id]
        if isinstance(ref, str) and ref in active_pvp_games:
            pvm = active_pvp_games[ref]
            gid = pvm.get("game_id") or ref
            return f"PvP Match (`{gid}`)"
        if isinstance(ref, dict):
            gid = ref.get("game_id")
            emoji = ref.get("emoji", "🎮")
            return f"{emoji} Versus Match (`{gid}`)" if gid else f"{emoji} Versus Match"
        return "an active match"
    return None

def is_player_in_active_game(user_id):
    return get_active_game_summary(user_id) is not None

def schedule_pvb_turn_timeout(chat_id, user_id, game):
    token = uuid.uuid4().hex
    game["turn_token"] = token
    emoji = game["emoji"]
    gid = game.get("game_id")

    def on_warn():
        cur = active_games.get(user_id)
        if not isinstance(cur, dict) or cur is not game or cur.get("turn_token") != token:
            return
        if cur.get("step") not in ["selecting_turn", "waiting_user_first", "waiting_user_second"]:
            return
        player_tag = format_user_mention(user_id)
        rem_rolls = cur["rolls_per_round"] - len(cur["current_user_rolls"])
        if rem_rolls <= 0:
            return
        gid_part = f" (`{gid}`)" if gid else ""
        warn_msg = (
            f"⏳ *Turn Timeout Warning*{gid_part}\n\n"
            f"⚠️ {player_tag}, please send {emoji} (`x{rem_rolls}`) within the next *60 seconds*, "
            f"else the bot will roll for you!"
        )
        send_message(chat_id, warn_msg)

    def on_timeout():
        lock = get_turn_lock(f"pvb_{user_id}")
        with lock:
            cur = active_games.get(user_id)
            if not isinstance(cur, dict) or cur is not game or cur.get("turn_token") != token:
                return
            if cur.get("step") not in ["selecting_turn", "waiting_user_first", "waiting_user_second"]:
                return

            cur["turn_token"] = None
            player_tag = format_user_mention(user_id)
            rolls_needed = cur["rolls_per_round"]
            rem_rolls = rolls_needed - len(cur["current_user_rolls"])
            if rem_rolls <= 0:
                return

            if cur["step"] == "selecting_turn":
                cur["first_turn"] = "user"
                cur["step"] = "waiting_user_first"
                s_chat_id = cur.get("start_chat_id") or chat_id
                s_msg_id = cur.get("start_message_id")
                if s_msg_id:
                    remove_inline_keyboard(s_chat_id, s_msg_id)
                    cur["start_message_id"] = None

            gid_part = f" (`{gid}`)" if gid else ""
            send_message(
                chat_id,
                f"⏰ *Timeout*{gid_part} — {player_tag}, bot is throwing {emoji} (`x{rem_rolls}`) for you..."
            )

            auto_vals = roll_bot_series(chat_id, emoji, rem_rolls)
            cur["current_user_rolls"].extend(auto_vals)

            step = cur["step"]
            if step == "waiting_user_first":
                u_expr = "+".join(map(str, cur["current_user_rolls"]))
                send_message(
                    chat_id,
                    f"👤 {player_tag} Auto-Rolls ({emoji}): `{u_expr}` (*{sum(cur['current_user_rolls'])}*)\n\n🤖 Now bot is throwing..."
                )
                time.sleep(0.8)
                b_vals = roll_bot_series(chat_id, emoji, rolls_needed)
                cur["current_bot_rolls"] = b_vals
                resolve_round_and_match(chat_id, user_id, cur)
            elif step == "waiting_user_second":
                resolve_round_and_match(chat_id, user_id, cur)

    t_warn = threading.Timer(60.0, on_warn)
    t_warn.daemon = True
    t_warn.start()

    t_expire = threading.Timer(120.0, on_timeout)
    t_expire.daemon = True
    t_expire.start()

def schedule_pvp_turn_timeout(chat_id, match_id, pvm):
    token = uuid.uuid4().hex
    pvm["turn_token"] = token
    target_uid = pvm["turn"]
    emoji = pvm["emoji"]
    gid = pvm.get("game_id") or match_id

    def on_warn():
        cur = active_pvp_games.get(match_id)
        if cur is not pvm or cur.get("turn_token") != token or cur.get("turn") != target_uid:
            return
        is_p1 = (target_uid == cur["p1_id"])
        cur_rolls = cur["p1_rolls"] if is_p1 else cur["p2_rolls"]
        rem_rolls = cur["rolls_per_round"] - len(cur_rolls)
        if rem_rolls <= 0:
            return
        player_tag = format_user_mention(target_uid)
        warn_msg = (
            f"⏳ *Turn Timeout Warning* (`{gid}`)\n\n"
            f"⚠️ {player_tag}, throw {emoji} (`x{rem_rolls}`) within the next *60 seconds*, "
            f"else your game will forfeit!"
        )
        send_message(chat_id, warn_msg)

    def on_forfeit():
        global HOUSE_BALANCE
        lock = get_turn_lock(f"pvp_{match_id}")
        with lock:
            cur = active_pvp_games.get(match_id)
            if cur is not pvm or cur.get("turn_token") != token or cur.get("turn") != target_uid:
                return

            cur["turn_token"] = None
            p1 = cur["p1_id"]
            p2 = cur["p2_id"]
            loser_id = target_uid
            winner_id = p2 if loser_id == p1 else p1
            bet = cur["bet"]
            g_name = GAME_NAME_MAP.get(emoji, "Game")
            mode = cur["mode"]
            rw_label = cur["rw_label"]

            mult = float(GAME_MULTIPLIERS.get("pvp", 1.94))
            payout = bet * mult
            house_fee = max(0.0, (bet * 2) - payout)
            HOUSE_BALANCE += house_fee

            win_pnl = payout - bet
            user_balances[winner_id] = user_balances.get(winner_id, 0.0) + payout
            persist_user(winner_id)
            persist_user(loser_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            update_user_stats(winner_id, emoji, bet, win_pnl, True)
            update_user_stats(loser_id, emoji, bet, -bet, False)

            label = f"PvP {g_name} ({rw_label}/{mode})"
            record_user_bet(winner_id, label, bet, win_pnl, "WON (Forfeit)", game_id=gid)
            record_user_bet(loser_id, label, bet, -bet, "FORFEITED", game_id=gid)
            win_actor = format_win_actor(winner_id)
            mark_game_finished(
                gid,
                "forfeited",
                extra_meta={"winner_id": winner_id, "winner_label": win_actor, "forfeited_by": loser_id, "payout": payout}
            )
            log_win_to_channel(winner_id, emoji, f"PvP {g_name}", payout, fmt_mult(mult))

            loser_tag = format_user_mention(loser_id)
            winner_tag = format_user_mention(winner_id)
            forfeit_text = (
                f"⌛ *Match Forfeited!* (`{gid}` | {emoji} | `{rw_label}`)\n\n"
                f"🚫 {loser_tag} failed to throw within 2 minutes and forfeited the match.\n"
                f"🏆 *Winner:* {winner_tag}\n"
                f"🎁 *Payout:* *{format_money(payout, winner_id)}* (`{fmt_mult(mult)}`)"
            )
            send_message(chat_id, forfeit_text)

            active_pvp_games.pop(match_id, None)
            if active_games.get(p1) == match_id:
                active_games.pop(p1, None)
            if active_games.get(p2) == match_id:
                active_games.pop(p2, None)

    t_warn = threading.Timer(60.0, on_warn)
    t_warn.daemon = True
    t_warn.start()

    t_forfeit = threading.Timer(120.0, on_forfeit)
    t_forfeit.daemon = True
    t_forfeit.start()

def normalize_chat_id(raw_id):
    if raw_id is None:
        return None
    s = str(raw_id).strip()
    if s.lstrip("-").isdigit():
        return int(s)
    return raw_id

def is_group_approved(raw_chat_id):
    norm = normalize_chat_id(raw_chat_id)
    if norm in approved_groups:
        return True
    if str(norm) in {str(x) for x in approved_groups}:
        return True
    return False

def create_manual_txn_confirmation(initiator_id, prompt_chat_id, action_type, payload):
    token = uuid.uuid4().hex[:10]
    pending_manual_txns[token] = {
        "initiator_id": initiator_id,
        "prompt_chat_id": prompt_chat_id,
        "action_type": action_type,
        "payload": payload,
        "created_at": time.time(),
    }
    keyboard = {
        "inline_keyboard": [
            [
                {"text": "✅ Confirm", "callback_data": f"mtx_ok_{token}"},
                {"text": "❌ Cancel", "callback_data": f"mtx_no_{token}"},
            ]
        ]
    }
    return token, keyboard

def execute_manual_txn(entry):
    global HOUSE_BALANCE
    action_type = entry["action_type"]
    initiator_id = entry["initiator_id"]
    prompt_chat_id = entry["prompt_chat_id"]
    p = entry["payload"]

    if action_type == "sethb":
        val = float(p["val"])
        HOUSE_BALANCE = val
        save_config_value("house_balance", HOUSE_BALANCE)
        send_message(prompt_chat_id, f"✅ House Balance set to *{format_money(HOUSE_BALANCE, initiator_id)}*.")

    elif action_type == "deducthb":
        amt = float(p["amt"])
        HOUSE_BALANCE = max(0.0, HOUSE_BALANCE - amt)
        save_config_value("house_balance", HOUSE_BALANCE)
        send_message(
            prompt_chat_id,
            f"✅ Deducted *{format_money(amt, initiator_id)}* from House Balance.\n🏦 New House Balance: *{format_money(HOUSE_BALANCE, initiator_id)}*"
        )

    elif action_type == "addbalance":
        target_uid = int(p["target_uid"])
        amt_inr = float(p["amt_inr"])
        if target_uid not in user_balances:
            user_balances[target_uid] = 0.0
            user_currency[target_uid] = 'INR'
        user_balances[target_uid] += amt_inr
        persist_user(target_uid)
        send_message(
            prompt_chat_id,
            f"✅ Added *{format_money(amt_inr, target_uid)}* to `{target_uid}`.\n💰 New Balance: *{format_money(user_balances[target_uid], target_uid)}*"
        )
        send_message(target_uid, f"💰 *Admin credited your account!* +{format_money(amt_inr, target_uid)}")

    elif action_type == "deductbalance":
        target_uid = int(p["target_uid"])
        amt_inr = float(p["amt_inr"])
        cur_b = float(user_balances.get(target_uid, 0.0))
        user_balances[target_uid] = max(0.0, cur_b - amt_inr)
        persist_user(target_uid)
        send_message(
            prompt_chat_id,
            f"✅ Deducted *{format_money(amt_inr, target_uid)}* from `{target_uid}`.\n💰 New Balance: *{format_money(user_balances[target_uid], target_uid)}*"
        )
        send_message(target_uid, f"⚠️ *Admin deducted from your account.* -{format_money(amt_inr, target_uid)}")

    elif action_type == "tip":
        receiver_id = int(p["receiver_id"])
        amt_inr = float(p["amt_inr"])
        origin_chat_id = p.get("origin_chat_id", prompt_chat_id)
        current_bal = float(user_balances.get(initiator_id, 0.0))
        if current_bal < amt_inr:
            send_message(
                prompt_chat_id,
                f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, initiator_id)}*\n🎯 Required Tip: *{format_money(amt_inr, initiator_id)}*"
            )
            return
        if receiver_id not in user_balances:
            user_balances[receiver_id] = 0.0
            user_currency[receiver_id] = 'INR'
        user_balances[initiator_id] = current_bal - amt_inr
        user_balances[receiver_id] = float(user_balances.get(receiver_id, 0.0)) + amt_inr
        persist_user(initiator_id)
        persist_user(receiver_id)

        sender_label = display_sender_label(initiator_id)
        amt_for_receiver = format_money(amt_inr, receiver_id)
        amt_for_sender = format_money(amt_inr, initiator_id)
        send_message(receiver_id, f"{amt_for_receiver} tip recived from {sender_label}")
        if origin_chat_id != receiver_id:
            send_message(origin_chat_id, f"✅ Sent *{amt_for_sender}* tip to {display_sender_label(receiver_id)}!")
        if prompt_chat_id != origin_chat_id:
            send_message(prompt_chat_id, f"✅ Tip confirmed: *{amt_for_sender}* sent to {display_sender_label(receiver_id)}.")

game_id_registry = {}
deposit_states = {}
withdrawal_states = {}
admin_states = {}

HOUSE_BALANCE = 100000.0
MIN_BET = 10.0
MAX_BET = 1000.0
EXCHANGE_RATE = 98.0
MAINTENANCE_MODE = False
DEPOSIT_ENABLED = True
WITHDRAW_ENABLED = True
DM_GAMES_ENABLED = True
GROUP_LINK = None

DM_GAME_COMMANDS = ['/dice', '/dart', '/foot', '/basket', '/bowl', '/dr', '/bj', '/7up', '/mines', '/tower', '/limbo']

def is_dm_game_command(text):
    bot_name = re.escape(BOT_USERNAME.lstrip('@'))
    for cmd in DM_GAME_COMMANDS:
        if re.match(rf"^{re.escape(cmd)}(?:@{bot_name})?(?:\s|$)", text, re.IGNORECASE):
            return True
    return False

def build_dm_games_off_text():
    if GROUP_LINK:
        safe_link = GROUP_LINK.replace('_', '\\_').replace('*', '\\*').replace('`', '\\`').replace('[', '\\[')
        place = safe_link
    else:
        place = "our group"
    return f"❌ Games in DM are currently turned off.\n\nPlease play in {place}."

PAGE_SIZE = 5

GAME_MULTIPLIERS = {
    "dice": 1.94,
    "dart": 1.94,
    "foot": 1.94,
    "basket": 1.94,
    "bowl": 1.94,
    "pvp": 1.94,
    "bj": 2.0,
    "dr": 1.92,
    "dr_nums": {1: 5.56, 2: 2.88, 3: 1.92, 4: 1.44, 5: 1.15},
    "7up": {
        "up": 2.16,
        "down": 2.16,
        "odd": 1.9,
        "even": 1.9,
        "7": 5.16,
    },
}

EMOJI_TO_MULT_KEY = {
    "🎲": "dice",
    "🎯": "dart",
    "⚽": "foot",
    "🏀": "basket",
    "🎳": "bowl",
}

VALID_RW_MODES = {
    "1r1w": (1, 1),
    "2r1w": (2, 1),
    "3r1w": (3, 1),
    "1r2w": (1, 2),
    "2r2w": (2, 2),
    "3r2w": (3, 2),
    "1r3w": (1, 3),
    "2r3w": (2, 3),
    "3r3w": (3, 3),
}

GAME_NAME_MAP = {
    "🎲": "Dice",
    "🎯": "Dart",
    "⚽": "Football",
    "🏀": "Basketball",
    "🎳": "Bowling",
}

def normalize_7up_choice(raw_choice):
    if raw_choice is None:
        return None
    c = str(raw_choice).strip().lower()
    if c in ("up", "high"):
        return "up"
    if c in ("down", "low"):
        return "down"
    if c == "odd":
        return "odd"
    if c == "even":
        return "even"
    if c == "7":
        return "7"
    return None

def format_7up_choice_label(canonical_choice, is_win=True):
    if canonical_choice == "up":
        return "up / high (8–12)" if is_win else "up/ high (8–12)"
    if canonical_choice == "down":
        return "down / low (2–6)" if is_win else "down/ low (2–6)"
    if canonical_choice == "odd":
        return "odd"
    if canonical_choice == "even":
        return "even"
    if canonical_choice == "7":
        return "7"
    return str(canonical_choice)

def format_7up_outcome_tag(canonical_choice, total_val):
    if canonical_choice in ("up", "down"):
        return "up/high" if total_val >= 8 else ("down/low" if total_val <= 6 else "7")
    if canonical_choice in ("odd", "even"):
        return "even" if total_val % 2 == 0 else "odd"
    if canonical_choice == "7":
        if total_val == 7:
            return "7"
        return "up/high" if total_val >= 8 else "down/low"
    return "up/high" if total_val >= 8 else ("down/low" if total_val <= 6 else "7")

def evaluate_7up_outcome(canonical_choice, total_val):
    if canonical_choice == "up":
        return 8 <= total_val <= 12
    if canonical_choice == "down":
        return 2 <= total_val <= 6
    if canonical_choice == "odd":
        return (total_val % 2) == 1
    if canonical_choice == "even":
        return (total_val % 2) == 0
    if canonical_choice == "7":
        return total_val == 7
    return False

def get_7up_multiplier(canonical_choice):
    mult_map = GAME_MULTIPLIERS.get("7up") or {}
    defaults = {"up": 2.16, "down": 2.16, "odd": 1.9, "even": 1.9, "7": 5.16}
    return float(mult_map.get(canonical_choice, defaults.get(canonical_choice, 1.0)))

def run_7up_game(chat_id, user_id, bet_inr, canonical_choice, raw_choice_text=None, reply_to_message_id=None):
    global HOUSE_BALANCE
    gid = generate_game_id()
    current_bal = float(user_balances.get(user_id, 0.0))
    user_balances[user_id] = current_bal - bet_inr
    persist_user(user_id)

    active_7up_games[user_id] = {
        "game_id": gid,
        "chat_id": chat_id,
        "bet": bet_inr,
        "choice": canonical_choice,
        "raw_choice": raw_choice_text or canonical_choice,
    }

    try:
        register_game_record(
            gid,
            "seven_up",
            user_id,
            bet_inr,
            meta={"choice": canonical_choice, "raw_choice": raw_choice_text or canonical_choice},
            refund_on_cancel=True
        )
        choice_disp_hist = format_7up_choice_label(canonical_choice, is_win=True)
        mult = get_7up_multiplier(canonical_choice)
        res1 = send_animated_game(chat_id, "🎲", reply_to_message_id=reply_to_message_id)
        d1 = res1["result"]["dice"]["value"] if res1 and "result" in res1 else random.randint(1, 6)
        time.sleep(0.6)
        res2 = send_animated_game(chat_id, "🎲", reply_to_message_id=reply_to_message_id)
        d2 = res2["result"]["dice"]["value"] if res2 and "result" in res2 else random.randint(1, 6)
        time.sleep(0.8)

        total_val = d1 + d2
        is_win = evaluate_7up_outcome(canonical_choice, total_val)
        outcome_tag = format_7up_outcome_tag(canonical_choice, total_val)

        if is_win:
            win_amt = bet_inr * mult
            profit_inr = win_amt - bet_inr
            user_balances[user_id] = float(user_balances.get(user_id, 0.0)) + win_amt
            HOUSE_BALANCE -= profit_inr
            persist_user(user_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            update_user_stats(user_id, "7up", bet_inr, profit_inr, True)
            record_user_bet(user_id, f"7Up ({choice_disp_hist})", bet_inr, profit_inr, "WON", game_id=gid)
            mark_game_finished(
                gid,
                "completed",
                extra_meta={"outcome": "WON", "d1": d1, "d2": d2, "total": total_val, "pnl": profit_inr}
            )
            log_win_to_channel(user_id, "🎲", "7Up", win_amt, fmt_mult(mult))
            pick_label = format_7up_choice_label(canonical_choice, is_win=True)
            result_text = (
                f"📊 7UP GAME REPORT\n"
                f"━━━━━━━━━━━━━━━━\n"
                f"🔑 Round ID: {gid}\n"
                f"🎲 Dice Result: {d1} + {d2} = {total_val}\n"
                f"🎯 Selected: {pick_label}\n"
                f"🔥 Outcome: Win\n"
                f"💰 Payout: {format_money(win_amt, user_id)}\n"
                f"⚡ Multiplier: {fmt_mult(mult)}\n"
                f"━━━━━━━━━━━━━━━━"
            )
        else:
            profit_inr = -bet_inr
            HOUSE_BALANCE += bet_inr
            persist_user(user_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            update_user_stats(user_id, "7up", bet_inr, profit_inr, False)
            record_user_bet(user_id, f"7Up ({choice_disp_hist})", bet_inr, profit_inr, "LOST", game_id=gid)
            mark_game_finished(
                gid,
                "completed",
                extra_meta={"outcome": "LOST", "d1": d1, "d2": d2, "total": total_val, "pnl": profit_inr}
            )
            pick_label = format_7up_choice_label(canonical_choice, is_win=True)
            result_text = (
                f"📊 7UP GAME REPORT\n"
                f"━━━━━━━━━━━━━━━━\n"
                f"🔑 Round ID: {gid}\n"
                f"🎲 Dice Result: {d1} + {d2} = {total_val}\n"
                f"🎯 Selected: {pick_label}\n"
                f"🔥 Outcome: loss\n"
                f"💰 Payout: {format_money(0.0, user_id)}\n"
                f"⚡ Multiplier: {fmt_mult(mult)}\n"
                f"━━━━━━━━━━━━━━━━"
            )

        pm_7up_payload = {
            "kind": "7up",
            "owner_id": user_id,
            "bet": bet_inr,
            "choice_7up": canonical_choice,
        }
        send_message(chat_id, result_text, reply_markup=create_post_match_keyboard(user_id, pm_7up_payload))
    finally:
        active_7up_games.pop(user_id, None)

import json
import psycopg2
from psycopg2.extras import RealDictCursor

DATABASE_URL = os.environ.get("DATABASE_URL")

def get_db_connection():
    if not DATABASE_URL:
        return None
    return psycopg2.connect(DATABASE_URL)

def init_db():
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS users (
                        user_id BIGINT PRIMARY KEY,
                        balance DOUBLE PRECISION DEFAULT 0.0,
                        currency TEXT DEFAULT 'INR',
                        username TEXT,
                        first_name TEXT,
                        is_banned BOOLEAN DEFAULT FALSE,
                        is_admin BOOLEAN DEFAULT FALSE,
                        total_deposits DOUBLE PRECISION DEFAULT 0.0,
                        total_withdrawals DOUBLE PRECISION DEFAULT 0.0,
                        stats_json TEXT DEFAULT '{}'
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS bet_logs (
                        id SERIAL PRIMARY KEY,
                        user_id BIGINT,
                        game_id TEXT,
                        game_label TEXT,
                        bet_inr DOUBLE PRECISION,
                        pnl_inr DOUBLE PRECISION,
                        outcome_label TEXT,
                        created_at TEXT
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS deposits (
                        id SERIAL PRIMARY KEY,
                        user_id BIGINT,
                        amount DOUBLE PRECISION,
                        utr TEXT,
                        created_at TEXT
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS withdrawals (
                        id SERIAL PRIMARY KEY,
                        user_id BIGINT,
                        amount DOUBLE PRECISION,
                        upi TEXT,
                        created_at TEXT
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS approved_groups (
                        chat_id BIGINT PRIMARY KEY
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS bot_config (
                        key TEXT PRIMARY KEY,
                        value_json TEXT
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS game_records (
                        game_id TEXT PRIMARY KEY,
                        record_json TEXT
                    )
                """)
    except Exception as e:
        print(f"DB init error: {e}")
    finally:
        conn.close()

def save_config_value(key, val):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO bot_config (key, value_json) VALUES (%s, %s)
                    ON CONFLICT (key) DO UPDATE SET value_json = EXCLUDED.value_json
                    """,
                    (key, json.dumps(val))
                )
    except Exception as e:
        print(f"DB save_config error ({key}): {e}")
    finally:
        conn.close()

def persist_config_all():
    save_config_value("house_balance", HOUSE_BALANCE)
    save_config_value("min_bet", MIN_BET)
    save_config_value("max_bet", MAX_BET)
    save_config_value("exchange_rate", EXCHANGE_RATE)
    save_config_value("maintenance_mode", MAINTENANCE_MODE)
    save_config_value("deposit_enabled", DEPOSIT_ENABLED)
    save_config_value("withdraw_enabled", WITHDRAW_ENABLED)
    save_config_value("game_multipliers", GAME_MULTIPLIERS)
    save_config_value("dm_games_enabled", DM_GAMES_ENABLED)
    save_config_value("group_link", GROUP_LINK)

def persist_user(uid):
    if uid is None:
        return
    conn = get_db_connection()
    if not conn:
        return
    try:
        bal = float(user_balances.get(uid, 0.0))
        curr = user_currency.get(uid, "INR")
        uname = user_usernames.get(uid)
        fname = user_first_names.get(uid)
        is_banned = uid in banned_users
        is_adm = uid in admin_list
        tot_dep = float(user_deposits.get(uid, 0.0))
        tot_wd = float(user_withdrawals.get(uid, 0.0))
        st_json = json.dumps(user_stats.get(uid, {"games": 0, "wins": 0, "losses": 0, "total_pnl": 0.0, "biggest_win": 0.0, "game_counts": {}}))
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO users (user_id, balance, currency, username, first_name, is_banned, is_admin, total_deposits, total_withdrawals, stats_json)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                    ON CONFLICT (user_id) DO UPDATE SET
                        balance = EXCLUDED.balance,
                        currency = EXCLUDED.currency,
                        username = COALESCE(EXCLUDED.username, users.username),
                        first_name = COALESCE(EXCLUDED.first_name, users.first_name),
                        is_banned = EXCLUDED.is_banned,
                        is_admin = EXCLUDED.is_admin,
                        total_deposits = EXCLUDED.total_deposits,
                        total_withdrawals = EXCLUDED.total_withdrawals,
                        stats_json = EXCLUDED.stats_json
                    """,
                    (uid, bal, curr, uname, fname, is_banned, is_adm, tot_dep, tot_wd, st_json)
                )
    except Exception as e:
        print(f"DB persist_user error ({uid}): {e}")
    finally:
        conn.close()

def persist_bet_log(user_id, game_label, bet_inr, pnl_inr, outcome_label, game_id, ts):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO bet_logs (user_id, game_id, game_label, bet_inr, pnl_inr, outcome_label, created_at)
                    VALUES (%s, %s, %s, %s, %s, %s, %s)
                    """,
                    (user_id, game_id, game_label, float(bet_inr), float(pnl_inr), outcome_label, ts)
                )
    except Exception as e:
        print(f"DB persist_bet_log error: {e}")
    finally:
        conn.close()

def persist_deposit(user_id, amount, utr, ts):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    "INSERT INTO deposits (user_id, amount, utr, created_at) VALUES (%s, %s, %s, %s)",
                    (user_id, float(amount), utr, ts)
                )
    except Exception as e:
        print(f"DB persist_deposit error: {e}")
    finally:
        conn.close()

def persist_withdrawal(user_id, amount, upi, ts):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    "INSERT INTO withdrawals (user_id, amount, upi, created_at) VALUES (%s, %s, %s, %s)",
                    (user_id, float(amount), upi, ts)
                )
    except Exception as e:
        print(f"DB persist_withdrawal error: {e}")
    finally:
        conn.close()

def persist_approved_group(chat_id):
    norm_id = normalize_chat_id(chat_id)
    if norm_id is None:
        return
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    "INSERT INTO approved_groups (chat_id) VALUES (%s) ON CONFLICT (chat_id) DO NOTHING",
                    (int(norm_id),)
                )
    except Exception as e:
        print(f"DB persist_approved_group error: {e}")
    finally:
        conn.close()

def persist_game_record(game_id, record):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO game_records (game_id, record_json) VALUES (%s, %s)
                    ON CONFLICT (game_id) DO UPDATE SET record_json = EXCLUDED.record_json
                    """,
                    (game_id, json.dumps(record))
                )
    except Exception as e:
        print(f"DB persist_game_record error: {e}")
    finally:
        conn.close()

def load_all_from_db():
    global HOUSE_BALANCE, MIN_BET, MAX_BET, EXCHANGE_RATE, MAINTENANCE_MODE, DEPOSIT_ENABLED, WITHDRAW_ENABLED, DM_GAMES_ENABLED, GROUP_LINK
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn.cursor(cursor_factory=RealDictCursor) as cur:
            cur.execute("SELECT key, value_json FROM bot_config")
            for row in cur.fetchall():
                k = row["key"]
                v = json.loads(row["value_json"])
                if k == "house_balance":
                    HOUSE_BALANCE = float(v)
                elif k == "min_bet":
                    MIN_BET = float(v)
                elif k == "max_bet":
                    MAX_BET = float(v)
                elif k == "exchange_rate":
                    EXCHANGE_RATE = float(v)
                elif k == "maintenance_mode":
                    MAINTENANCE_MODE = bool(v)
                elif k == "deposit_enabled":
                    DEPOSIT_ENABLED = bool(v)
                elif k == "withdraw_enabled":
                    WITHDRAW_ENABLED = bool(v)
                elif k == "dm_games_enabled":
                    DM_GAMES_ENABLED = bool(v)
                elif k == "helper_bots":
                    HELPER_BOTS[:] = [x for x in (v or []) if isinstance(x, dict) and x.get("token")]
                elif k == "group_link":
                    GROUP_LINK = v if v else None
                elif k == "game_multipliers" and isinstance(v, dict):
                    for mk, mv in v.items():
                        if mk == "dr_nums" and isinstance(mv, dict):
                            GAME_MULTIPLIERS["dr_nums"].update({int(dk): float(dv) for dk, dv in mv.items()})
                        elif mk == "7up" and isinstance(mv, dict):
                            GAME_MULTIPLIERS["7up"].update({str(sk): float(sv) for sk, sv in mv.items()})
                        else:
                            GAME_MULTIPLIERS[mk] = float(mv)

            cur.execute("SELECT * FROM users")
            for r in cur.fetchall():
                uid = int(r["user_id"])
                user_balances[uid] = float(r["balance"] or 0.0)
                user_currency[uid] = r["currency"] or "INR"
                if r["username"]:
                    clean_u = r["username"].lstrip("@").lower()
                    user_usernames[uid] = clean_u
                    username_to_id[clean_u] = uid
                if r["first_name"]:
                    user_first_names[uid] = r["first_name"]
                if r["is_banned"]:
                    banned_users.add(uid)
                if r["is_admin"]:
                    admin_list.add(uid)
                user_deposits[uid] = float(r["total_deposits"] or 0.0)
                user_withdrawals[uid] = float(r["total_withdrawals"] or 0.0)
                if r["stats_json"]:
                    try:
                        parsed_st = json.loads(r["stats_json"])
                        if isinstance(parsed_st, dict):
                            user_stats[uid] = parsed_st
                    except Exception:
                        pass

            cur.execute("SELECT * FROM bet_logs ORDER BY id ASC")
            for r in cur.fetchall():
                uid = int(r["user_id"])
                user_bet_logs.setdefault(uid, []).append({
                    "game_id": r["game_id"],
                    "game": r["game_label"],
                    "bet": float(r["bet_inr"] or 0.0),
                    "pnl": float(r["pnl_inr"] or 0.0),
                    "outcome": r["outcome_label"],
                    "time": r["created_at"] or ""
                })

            cur.execute("SELECT * FROM deposits ORDER BY id ASC")
            for r in cur.fetchall():
                deposit_history.append({
                    "user": int(r["user_id"]),
                    "amount": float(r["amount"] or 0.0),
                    "utr": r["utr"] or "",
                    "time": r["created_at"] or ""
                })

            cur.execute("SELECT * FROM withdrawals ORDER BY id ASC")
            for r in cur.fetchall():
                withdrawal_history.append({
                    "user": int(r["user_id"]),
                    "amount": float(r["amount"] or 0.0),
                    "upi": r["upi"] or "",
                    "time": r["created_at"] or ""
                })

            cur.execute("SELECT chat_id FROM approved_groups")
            for r in cur.fetchall():
                if r and r.get("chat_id") is not None:
                    approved_groups.add(int(r["chat_id"]))

            cur.execute("SELECT game_id, record_json FROM game_records")
            for r in cur.fetchall():
                try:
                    game_id_registry[r["game_id"]] = json.loads(r["record_json"])
                except Exception:
                    pass
    except Exception as e:
        print(f"DB load_all error: {e}")
    finally:
        conn.close()


def fmt_mult(val):
    s = f"{float(val):.4f}".rstrip("0").rstrip(".")
    return f"{s}x"

def get_versus_multiplier(emoji):
    key = EMOJI_TO_MULT_KEY.get(emoji, "dice")
    return float(GAME_MULTIPLIERS.get(key, 1.94))

def normalize_channel_id(raw_id):
    if raw_id is None:
        return None
    s = str(raw_id).strip()
    if not s:
        return None
    if s.startswith("-100"):
        return int(s)
    if s.startswith("-"):
        num = s[1:]
        return int(f"-100{num}") if not num.startswith("100") else int(s)
    if s.isdigit():
        return int(f"-100{s}")
    return s

def mask_user_id_for_log(user_id):
    value = str(user_id)
    if len(value) <= 4:
        return "*" * len(value)
    return "*" * (len(value) - 4) + value[-4:]

def mask_upi_id_for_log(upi_id):
    value = str(upi_id or "").strip()
    local, separator, provider = value.partition("@")
    if separator:
        if len(local) <= 2:
            masked_local = (local[:1] + "*") if local else "**"
        else:
            masked_local = local[0] + "*" * (len(local) - 2) + local[-1]
        return f"{masked_local}@{provider}"
    return mask_user_id_for_log(value)

def format_user_mention(user_id):
    uname = user_usernames.get(user_id)
    if uname:
        return f"@{uname}"
    fname = user_first_names.get(user_id) or f"User {user_id}"
    safe_name = str(fname).replace("[", "").replace("]", "")
    return f"[{safe_name}](tg://user?id={user_id})"

def tag_player(user_id):
    """Clickable mention that tags the player (safe for Markdown)."""
    uname = user_usernames.get(user_id)
    if uname:
        return "@" + str(uname).replace("_", "\\_")
    fname = user_first_names.get(user_id) or "Player"
    safe_name = re.sub(r"[\[\]_*`()]", "", str(fname)).strip() or "Player"
    return f"[{safe_name}](tg://user?id={user_id})"

def format_win_actor(user_id):
    if user_id in user_usernames and user_usernames[user_id]:
        return f"@{user_usernames[user_id]}"
    if user_id in user_first_names and user_first_names[user_id]:
        return user_first_names[user_id]
    return f"User {user_id}"

def log_win_to_channel(user_id, game_emoji, game_title, won_inr, mult_text=None):
    target_channel = normalize_channel_id(WINS_CHANNEL_ID)
    actor = format_win_actor(user_id)
    amt_str = f"₹{won_inr:,.2f}"
    mult_part = f" `({mult_text})`" if mult_text else ""
    msg = f"{game_emoji} *{game_title}* · *{actor}* won *{amt_str}*{mult_part}"

    res = send_message(target_channel, msg) if target_channel else None
    if (not res or not res.get("ok")) and WINS_CHANNEL_USERNAME:
        send_message(f"@{WINS_CHANNEL_USERNAME}", msg)

def current_timestamp():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")

def generate_game_id():
    while True:
        mid = "".join(random.choices(string.ascii_uppercase + string.digits, k=7))
        tail = "".join(random.choices(string.digits, k=4))
        gid = f"XC-{mid}-{tail}"
        if gid not in game_id_registry:
            return gid

def register_game_record(game_id, kind, owner_id, bet_inr, meta=None, refund_on_cancel=True):
    record = {
        "game_id": game_id,
        "kind": kind,
        "owner_id": owner_id,
        "bet_inr": bet_inr,
        "refund_on_cancel": refund_on_cancel,
        "created_at": current_timestamp(),
        "status": "active",
        "meta": meta or {}
    }
    game_id_registry[game_id] = record
    persist_game_record(game_id, record)
    return record

def mark_game_finished(game_id, status="completed", extra_meta=None):
    if game_id and game_id in game_id_registry:
        game_id_registry[game_id]["status"] = status
        game_id_registry[game_id]["ended_at"] = current_timestamp()
        if extra_meta:
            game_id_registry[game_id]["meta"].update(extra_meta)
        persist_game_record(game_id, game_id_registry[game_id])

def record_user_bet(user_id, game_label, bet_inr, pnl_inr, outcome_label, game_id=None):
    if user_id not in user_bet_logs:
        user_bet_logs[user_id] = []
    ts = current_timestamp()
    user_bet_logs[user_id].append({
        "game_id": game_id,
        "game": game_label,
        "bet": bet_inr,
        "pnl": pnl_inr,
        "outcome": outcome_label,
        "time": ts
    })
    persist_bet_log(user_id, game_label, bet_inr, pnl_inr, outcome_label, game_id, ts)
    persist_user(user_id)

def resolve_user_identifier(raw_ident):
    if not raw_ident:
        return None
    cleaned = raw_ident.strip()
    if cleaned.lstrip("-").isdigit():
        return int(cleaned)
    uname = cleaned.lstrip("@").lower()
    return username_to_id.get(uname)

def register_user_identity(from_user):
    if not from_user:
        return None
    uid = from_user.get("id")
    if uid is None:
        return None
    if uid not in user_balances:
        user_balances[uid] = 0.0
        user_currency[uid] = 'INR'
    first_name = from_user.get("first_name")
    if first_name:
        user_first_names[uid] = first_name.strip()
    uname = from_user.get("username")
    if uname:
        clean_uname = uname.lstrip("@").lower()
        old_uname = user_usernames.get(uid)
        if old_uname and old_uname != clean_uname and username_to_id.get(old_uname) == uid:
            del username_to_id[old_uname]
        user_usernames[uid] = clean_uname
        username_to_id[clean_uname] = uid
    return uid

def display_sender_label(user_id):
    uname = user_usernames.get(user_id)
    if uname:
        return f"@{uname}"
    return f"`{user_id}`"

def game_style_keyboard():
    return {
        "inline_keyboard": [
            [
                {"text": "🔥 Crazy", "callback_data": "gs_style_crazy"},
                {"text": "⚡ Normal", "callback_data": "gs_style_normal"},
            ],
            [
                {"text": "❌ Cancel", "callback_data": "gs_cancel"},
            ],
        ]
    }

def rw_mode_keyboard():
    return {
        "inline_keyboard": [
            [
                {"text": "1r1w", "callback_data": "rw_pick_1r1w"},
                {"text": "2r1w", "callback_data": "rw_pick_2r1w"},
                {"text": "3r1w", "callback_data": "rw_pick_3r1w"},
            ],
            [
                {"text": "1r2w", "callback_data": "rw_pick_1r2w"},
                {"text": "2r2w", "callback_data": "rw_pick_2r2w"},
                {"text": "3r2w", "callback_data": "rw_pick_3r2w"},
            ],
            [
                {"text": "1r3w", "callback_data": "rw_pick_1r3w"},
                {"text": "2r3w", "callback_data": "rw_pick_2r3w"},
                {"text": "3r3w", "callback_data": "rw_pick_3r3w"},
            ],
            [
                {"text": "❌ Cancel", "callback_data": "gs_cancel"},
            ],
        ]
    }

def match_confirm_keyboard(chat_type="group"):
    if chat_type == "private":
        opponent_row = [
            {"text": "🤖 Against Bot", "callback_data": "mc_bot"},
        ]
    else:
        opponent_row = [
            {"text": "🤖 Against Bot", "callback_data": "mc_bot"},
            {"text": "👥 Against Player", "callback_data": "mc_player"},
        ]
    return {
        "inline_keyboard": [
            opponent_row,
            [
                {"text": "❌ Cancel", "callback_data": "gs_cancel"},
            ],
        ]
    }

def build_match_confirmation_text(user_id, emoji, bet_inr, mode, rw_label, game_id=None):
    mode_label = "CRAZY (Lowest Sum Wins)" if mode == "crazy" else "NORMAL (Highest Sum Wins)"
    g_name = GAME_NAME_MAP.get(emoji, "Game")
    gid_line = f"🆔 *Game ID:* `{game_id}`\n" if game_id else ""
    return (
        "📋 *Match Confirmation*\n\n"
        f"{gid_line}"
        f"🎮 *Game:* {g_name} ({emoji})\n"
        f"⚙️ *Mode:* *{mode_label}*\n"
        f"🏆 *RW Format:* `{rw_label}`\n"
        f"💰 *Bet Amount:* *{format_money(bet_inr, user_id)}*\n\n"
        "Choose how you want to play:"
    )

def start_versus_match(chat_id, message_id, user_id, emoji, bet_inr, mode, rw_label, game_id=None, trigger_msg_id=None):
    gid = game_id or generate_game_id()
    rolls_per_round, target_wins = VALID_RW_MODES[rw_label]
    user_balances[user_id] = user_balances.get(user_id, 0.0) - bet_inr
    persist_user(user_id)
    register_game_record(
        gid,
        "bot_versus",
        user_id,
        bet_inr,
        meta={"chat_id": chat_id, "emoji": emoji, "mode": mode, "rw_label": rw_label, "trigger_msg_id": trigger_msg_id},
        refund_on_cancel=True
    )
    mode_title = "🔥 CRAZY MODE (Lowest Sum Wins)" if mode == "crazy" else "⚡ NORMAL MODE (Highest Sum Wins)"
    player_tag = format_user_mention(user_id)
    keyboard = {
        "inline_keyboard": [
            [
                {"text": "🤖 Bot Roll First", "callback_data": "play_bot_first"}
            ]
        ]
    }
    text = (
        f"🎮 *Game Started* (`{gid}` | {emoji} | `{rw_label}` | {mode_title})\n"
        f"👤 Player: {player_tag}\n"
        f"🎯 First to *{target_wins}* round win(s) | *{rolls_per_round}* roll(s)/round\n"
        f"💰 Bet: {format_money(bet_inr, user_id)}\n\n{player_tag}, send {emoji} x{rolls_per_round}"
    )
    sent_msg_id = message_id
    if message_id:
        edit_message(chat_id, message_id, text, reply_markup=keyboard)
    else:
        res = send_message(chat_id, text, reply_markup=keyboard)
        if res and res.get("ok"):
            sent_msg_id = res["result"]["message_id"]
    remember_button_owner(chat_id, sent_msg_id, user_id)

    active_games[user_id] = {
        "game_id": gid,
        "bet": bet_inr,
        "emoji": emoji,
        "mode": mode,
        "rw_label": rw_label,
        "rolls_per_round": rolls_per_round,
        "target_wins": target_wins,
        "round_num": 1,
        "user_wins": 0,
        "bot_wins": 0,
        "current_user_rolls": [],
        "current_bot_rolls": [],
        "first_turn": None,
        "step": "selecting_turn",
        "start_chat_id": chat_id,
        "start_message_id": sent_msg_id,
        "trigger_msg_id": trigger_msg_id
    }
    schedule_pvb_turn_timeout(chat_id, user_id, active_games[user_id])

def roll_text(vals):
    """Single roll -> '4'; multiple rolls -> '3+4 = 7'."""
    total = sum(vals)
    if len(vals) <= 1:
        return f"{total}"
    return f"{'+'.join(map(str, vals))} = {total}"

def resolve_pvp_round_and_match(chat_id, match_id, pvm):
    with helper_voice(chat_id):
        return _resolve_pvp_round_and_match(chat_id, match_id, pvm)

def _resolve_pvp_round_and_match(chat_id, match_id, pvm):
    global HOUSE_BALANCE
    gid = pvm.get("game_id") or match_id
    emoji = pvm["emoji"]
    g_name = GAME_NAME_MAP.get(emoji, "Game")
    mode = pvm["mode"]
    rw_label = pvm["rw_label"]
    target_wins = pvm["target_wins"]
    bet = pvm["bet"]
    p1 = pvm["p1_id"]
    p2 = pvm["p2_id"]

    r1_vals = pvm["p1_rolls"]
    r2_vals = pvm["p2_rolls"]
    s1 = sum(r1_vals)
    s2 = sum(r2_vals)

    expr1 = "+".join(map(str, r1_vals))
    expr2 = "+".join(map(str, r2_vals))
    round_num = pvm["round_num"]
    mode_tag = "🔥 CRAZY" if mode == "crazy" else "⚡ NORMAL"

    round_winner = None
    if s1 == s2:
        r_status = "🤝 *Round Tied!* No point awarded."
    elif mode == "crazy":
        if s1 < s2:
            pvm["p1_wins"] += 1
            round_winner = p1
            r_status = f"✨ {tag_player(p1)} takes this round! (Lower sum wins)"
        else:
            pvm["p2_wins"] += 1
            round_winner = p2
            r_status = f"✨ {tag_player(p2)} takes this round! (Lower sum wins)"
    else:
        if s1 > s2:
            pvm["p1_wins"] += 1
            round_winner = p1
            r_status = f"✨ {tag_player(p1)} takes this round! (Higher sum wins)"
        else:
            pvm["p2_wins"] += 1
            round_winner = p2
            r_status = f"✨ {tag_player(p2)} takes this round! (Higher sum wins)"

    if pvm["p1_wins"] >= target_wins or pvm["p2_wins"] >= target_wins:
        winner_id = p1 if pvm["p1_wins"] >= target_wins else p2
        loser_id = p2 if winner_id == p1 else p1

        mult = float(GAME_MULTIPLIERS.get("pvp", 1.94))
        payout = bet * mult
        house_fee = max(0.0, (bet * 2) - payout)
        HOUSE_BALANCE += house_fee

        win_pnl = payout - bet
        user_balances[winner_id] = user_balances.get(winner_id, 0.0) + payout
        persist_user(winner_id)
        persist_user(loser_id)
        save_config_value("house_balance", HOUSE_BALANCE)
        update_user_stats(winner_id, emoji, bet, win_pnl, True)
        update_user_stats(loser_id, emoji, bet, -bet, False)

        label = f"PvP {g_name} ({rw_label}/{mode})"
        record_user_bet(winner_id, label, bet, win_pnl, "WON", game_id=gid)
        record_user_bet(loser_id, label, bet, -bet, "LOST", game_id=gid)
        win_actor = format_win_actor(winner_id)
        mark_game_finished(gid, "completed", extra_meta={"winner_id": winner_id, "winner_label": win_actor, "payout": payout})
        log_win_to_channel(winner_id, emoji, f"PvP {g_name}", payout, fmt_mult(mult))

        final_text = (
            f"⚔️ *Final Round Result*\n"
            f"━━━━━━━━━━━━━━━━\n"
            f"{emoji} {tag_player(p1)} — {roll_text(r1_vals)}{' ✅' if winner_id == p1 else ''}\n"
            f"{emoji} {tag_player(p2)} — {roll_text(r2_vals)}{' ✅' if winner_id == p2 else ''}\n"
            f"━━━━━━━━━━━━━━━━\n"
            f"🔥 Winner: {tag_player(winner_id)}\n"
            f"🏆 Score: {pvm['p1_wins']} : {pvm['p2_wins']} | First to {target_wins}\n"
            f"🆔 `{gid}`\n"
            f"💰 Final payout: {format_money(payout, winner_id)} ({fmt_mult(mult)})"
        )
        send_message(chat_id, final_text)

        active_pvp_games.pop(match_id, None)
        if active_games.get(p1) == match_id:
            active_games.pop(p1, None)
        if active_games.get(p2) == match_id:
            active_games.pop(p2, None)
        return

    if round_winner is None:
        winner_line = "🤝 Round Tied — no point"
    else:
        winner_line = f"🔥 Winner: {tag_player(round_winner)}"
    msg = (
        f"⚔️ *Round {round_num} Result*\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{emoji} {tag_player(p1)} — {roll_text(r1_vals)}{' ✅' if round_winner == p1 else ''}\n"
        f"{emoji} {tag_player(p2)} — {roll_text(r2_vals)}{' ✅' if round_winner == p2 else ''}\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{winner_line}\n"
        f"🏆 Score: {pvm['p1_wins']} : {pvm['p2_wins']} | First to {target_wins}\n"
        f"🆔 `{gid}`"
    )
    send_message(chat_id, msg)

    pvm["round_num"] += 1
    pvm["p1_rolls"] = []
    pvm["p2_rolls"] = []
    pvm["turn"] = p1
    send_message(
        chat_id,
        f"➡️ *Round {pvm['round_num']}* — {tag_player(p1)}, send `{emoji}` x{pvm['rolls_per_round']} in chat!"
    )
    schedule_pvp_turn_timeout(chat_id, match_id, pvm)

DECK_RANKS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
DECK_SUITS = ["♠", "♥", "♦", "♣"]

def draw_card():
    rank = random.choice(DECK_RANKS)
    suit = random.choice(DECK_SUITS)
    return f"{rank}{suit}"

def card_value(card):
    rank = card[:-1]
    if rank == "A":
        return 11
    if rank in ["K", "Q", "J", "10"]:
        return 10
    return int(rank)

def calculate_hand_total(cards):
    total = sum(card_value(c) for c in cards)
    aces = sum(1 for c in cards if c[:-1] == "A")
    while total > 21 and aces > 0:
        total -= 10
        aces -= 1
    return total

def format_cards(cards):
    return " ".join(f"`{c}`" for c in cards)

def bj_action_keyboard(can_double=True):
    row1 = [
        {"text": "🃏 Hit", "callback_data": "bj_hit"},
        {"text": "🛑 Stand", "callback_data": "bj_stand"}
    ]
    rows = [row1]
    if can_double:
        rows.append([{"text": "⚡ Double", "callback_data": "bj_double"}])
    return {"inline_keyboard": rows}

def format_money(amount_in_inr, user_id):
    curr = user_currency.get(user_id, 'INR')
    if curr == 'USDT':
        val = amount_in_inr / EXCHANGE_RATE
        return f"${val:.2f} USDT"
    else:
        return f"₹{amount_in_inr:.2f}"

def parse_user_amount(text_val, user_id):
    try:
        val = float(text_val)
        curr = user_currency.get(user_id, 'INR')
        if curr == 'USDT':
            return val * EXCHANGE_RATE
        return val
    except:
        return None


# =====================================================================
# 🤖 HELPER BOTS — up to 3 helper bots throw every emoji in groups and
# send the round / final round messages, so the main bot has less load.
# Admin manages them with /helper (token is saved in the DB, no file edits).
# Main bot throws only as an emergency backup (no helper could throw)
# and in player DMs (Telegram does not let helpers post in someone's DM).
# =====================================================================
import hashlib as _hb_hashlib
import hmac as _hb_hmac

MAX_HELPERS = 3
HELPER_BOTS = []            # [{"id", "username", "token", "enabled", "hook"}]
HELPER_THROW_WAIT = 4       # seconds to wait for a rate-limited helper before backup
_helper_lock = threading.Lock()
_helper_rr = [0]
_helper_cooldown = {}       # helper_id -> unix time it can be used again (Telegram 429)
_helper_chat_block = {}     # (helper_id, chat_id) -> unix time (helper not in that chat)
_helper_backup_note = {}    # chat_id -> last time admin was told main bot threw
_tg_ctx = threading.local() # per-request: which bot answers / which helper speaks

def _api_base():
    return getattr(_tg_ctx, "api", None) or TELEGRAM_API_URL

def tg_url(method):
    return f"{_api_base()}/{method}"

def helper_api(h):
    return f"https://api.telegram.org/bot{h['token']}"

def helper_ids():
    return {h.get("id") for h in HELPER_BOTS}

def save_helpers():
    save_config_value("helper_bots", HELPER_BOTS)

def helper_hook_secret(token):
    return _hb_hashlib.sha256(f"xyren-helper:{token}".encode()).hexdigest()

def _md_safe(t):
    return str(t).replace('_', '\\_').replace('*', '\\*').replace('`', '\\`').replace('[', '\\[')

def _helpers_for_chat(chat_id):
    """Enabled helpers usable in this chat, in round-robin order (spreads the load)."""
    now = time.time()
    with _helper_lock:
        live = [h for h in HELPER_BOTS if h.get("enabled") and _helper_chat_block.get((h.get("id"), chat_id), 0) <= now]
        if not live:
            return []
        start = _helper_rr[0] % len(live)
        _helper_rr[0] += 1
    return live[start:] + live[:start]

_HELPER_NOT_IN_CHAT = ("chat not found", "not a member", "kicked", "forbidden", "rights", "chat_send", "initiate", "blocked", "restricted")

def _helper_post(h, method, payload, timeout=5):
    try:
        data = requests.post(f"{helper_api(h)}/{method}", json=payload, timeout=timeout).json()
    except Exception as e:
        print(f"Helper @{h.get('username')} {method} error: {e}")
        return None
    if not data.get("ok"):
        code = data.get("error_code")
        desc = str(data.get("description", "")).lower()
        if code == 429:
            wait = (data.get("parameters") or {}).get("retry_after", 3)
            _helper_cooldown[h.get("id")] = time.time() + float(wait)
        elif code == 401:
            h["enabled"] = False
            save_helpers()
            try:
                requests.post(f"{TELEGRAM_API_URL}/sendMessage", json={"chat_id": ADMIN_USER_ID, "text": f"⚠️ Helper @{h.get('username')} token stopped working (revoked?). It is now OFF. Re-add it with /helper add <token>."}, timeout=5)
            except Exception:
                pass
        elif code in (400, 403) and any(k in desc for k in _HELPER_NOT_IN_CHAT):
            _helper_chat_block[(h.get("id"), payload.get("chat_id"))] = time.time() + 600
        print(f"Helper @{h.get('username')} {method} failed: {data.get('description')}")
    return data

def _main_throw(payload):
    try:
        return requests.post(f"{TELEGRAM_API_URL}/sendDice", json=payload, timeout=5).json()
    except Exception as e:
        print(f"Error sending game: {e}")
        return None

def _note_backup_throw(chat_id, why):
    now = time.time()
    if now - _helper_backup_note.get(chat_id, 0) < 600:
        return
    _helper_backup_note[chat_id] = now
    try:
        requests.post(
            f"{TELEGRAM_API_URL}/sendMessage",
            json={"chat_id": ADMIN_USER_ID, "text": f"⚠️ Main bot threw an emoji as backup in chat {chat_id} ({why}). Check /helper — add the helpers to that group or turn them on."},
            timeout=5,
        )
    except Exception:
        pass

class helper_voice:
    """Inside this block, messages to `chat_id` go out from a helper bot.
    If the helper can't send, the main bot sends it instead (no message is lost)."""
    def __init__(self, chat_id):
        self.chat_id = chat_id
    def __enter__(self):
        self.prev = (getattr(_tg_ctx, "voice", None), getattr(_tg_ctx, "voice_chat", None))
        pick = None
        if isinstance(self.chat_id, int) and self.chat_id < 0:
            now = time.time()
            for h in _helpers_for_chat(self.chat_id):
                if _helper_cooldown.get(h.get("id"), 0) <= now:
                    pick = h
                    break
        _tg_ctx.voice = pick
        _tg_ctx.voice_chat = self.chat_id if pick else None
        return self
    def __exit__(self, *exc):
        _tg_ctx.voice, _tg_ctx.voice_chat = self.prev
        return False

_EDIT_WRONG_BOT = ("can't be edited", "message to edit not found", "message_id_invalid", "message can't be")

def _tg_edit(method, payload, timeout=5):
    """Edit a message. If this bot didn't send it, try the other bots (main + helpers)."""
    bases = [_api_base(), TELEGRAM_API_URL] + [helper_api(h) for h in HELPER_BOTS]
    seen = set()
    data = None
    for base in bases:
        if base in seen:
            continue
        seen.add(base)
        body = dict(payload)
        try:
            data = requests.post(f"{base}/{method}", json=body, timeout=timeout).json()
            if not data.get("ok") and "parse" in str(data.get("description", "")).lower() and "parse_mode" in body:
                body.pop("parse_mode", None)
                data = requests.post(f"{base}/{method}", json=body, timeout=timeout).json()
        except Exception as e:
            print(f"Error {method}: {e}")
            return None
        if data.get("ok"):
            return data
        desc = str(data.get("description", "")).lower()
        if not any(k in desc for k in _EDIT_WRONG_BOT):
            return data
    return data

def _has_fair_link(text):
    url = os.environ.get("VERIFY_URL")
    return bool(url and text and url.rstrip("/") in text)

def send_message(chat_id, text, reply_markup=None, reply_to_message_id=None):
    payload = {"chat_id": chat_id, "text": text, "parse_mode": "Markdown"}
    if reply_markup:
        payload["reply_markup"] = reply_markup
    if reply_to_message_id:
        payload["reply_to_message_id"] = reply_to_message_id
        payload["allow_sending_without_reply"] = True
    if _has_fair_link(text):
        payload["link_preview_options"] = {"is_disabled": True}

    # Round / final round messages: sent by a helper bot.
    voice = getattr(_tg_ctx, "voice", None)
    if voice and voice.get("enabled") and getattr(_tg_ctx, "voice_chat", None) == chat_id and (not reply_markup or voice.get("hook")):
        body = dict(payload)
        data = _helper_post(voice, "sendMessage", body)
        if data and not data.get("ok") and "parse" in str(data.get("description", "")).lower():
            body.pop("parse_mode", None)
            data = _helper_post(voice, "sendMessage", body)
        if data and data.get("ok"):
            return data

    bases = [_api_base()]
    if bases[0] != TELEGRAM_API_URL:
        bases.append(TELEGRAM_API_URL)
    data = None
    for base in bases:
        body = dict(payload)
        try:
            data = requests.post(f"{base}/sendMessage", json=body, timeout=5).json()
            if not data.get("ok") and "parse" in str(data.get("description", "")).lower():
                body.pop("parse_mode", None)
                data = requests.post(f"{base}/sendMessage", json=body, timeout=5).json()
            if data.get("ok"):
                return data
        except Exception as e:
            print(f"Error sending message: {e}")
            data = None
    return data

def edit_message(chat_id, message_id, text, reply_markup=None):
    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "text": text,
        "parse_mode": "Markdown"
    }
    if reply_markup:
        payload["reply_markup"] = reply_markup
    else:
        payload["reply_markup"] = {"inline_keyboard": []}
    if _has_fair_link(text):
        payload["link_preview_options"] = {"is_disabled": True}
    data = _tg_edit("editMessageText", payload, timeout=5)
    if data is None:
        print("Error editing message")
    return data

def answer_callback(callback_query_id, text=""):
    url = tg_url("answerCallbackQuery")
    payload = {"callback_query_id": callback_query_id, "text": text}
    try:
        requests.post(url, json=payload, timeout=3)
    except Exception as e:
        print(f"Error answering callback: {e}")

def remove_inline_keyboard(chat_id, message_id):
    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "reply_markup": {"inline_keyboard": []}
    }
    _tg_edit("editMessageReplyMarkup", payload, timeout=3)

def set_inline_keyboard(chat_id, message_id, reply_markup):
    payload = {"chat_id": chat_id, "message_id": message_id, "reply_markup": reply_markup}
    _tg_edit("editMessageReplyMarkup", payload, timeout=3)

def send_photo(chat_id, photo_bio, caption=""):
    url = f"{TELEGRAM_API_URL}/sendPhoto"
    files = {'photo': ('game.png', photo_bio, 'image/png')}
    data = {'chat_id': chat_id, 'caption': caption, 'parse_mode': 'Markdown'}
    try:
        requests.post(url, files=files, data=data, timeout=10)
    except Exception as e:
        print(f"Error sending photo: {e}")

def generate_stats_image(user_id):
    stats = user_stats.get(user_id, {"games": 0, "wins": 0, "losses": 0, "total_pnl": 0.0, "biggest_win": 0.0, "game_counts": {}})
    total_games = stats["games"]
    wins = stats["wins"]
    losses = stats["losses"]
    win_rate = (wins / total_games * 100) if total_games > 0 else 0.0
    total_pnl = stats["total_pnl"]
    biggest_win = stats["biggest_win"]
    total_dep = user_deposits.get(user_id, 0.0)
    total_wd = user_withdrawals.get(user_id, 0.0)
    
    game_counts = stats.get("game_counts", {})
    most_played = max(game_counts, key=game_counts.get) if game_counts else "None"

    img = Image.new('RGB', (600, 480), color=(15, 15, 25))
    d = ImageDraw.Draw(img)
    
    d.rectangle([0, 0, 600, 75], fill=(30, 30, 50))
    d.text((25, 25), f"📊 {BOT_USERNAME} - PLAYER STATS", fill=(255, 215, 0))
    
    y = 100
    items = [
        ("Total Games Played:", f"{total_games}"),
        ("Total Deposits:", format_money(total_dep, user_id)),
        ("Total Withdrawals:", format_money(total_wd, user_id)),
        ("Most Played Game:", f"{str(most_played).upper()}"),
        ("Total PnL:", format_money(total_pnl, user_id)),
        ("Win Rate:", f"{win_rate:.1f}% ({wins}W / {losses}L)"),
        ("Biggest Lifetime Win:", format_money(biggest_win, user_id))
    ]
    
    for label, val in items:
        d.text((30, y), label, fill=(180, 180, 200))
        d.text((340, y), val, fill=(0, 255, 127) if "PnL" not in label or total_pnl >= 0 else (255, 69, 0))
        y += 42
        
    bio = io.BytesIO()
    img.save(bio, 'PNG')
    bio.seek(0)
    return bio

def update_user_stats(user_id, game_name, bet_inr, profit_inr, is_win):
    if user_id not in user_stats:
        user_stats[user_id] = {"games": 0, "wins": 0, "losses": 0, "total_pnl": 0.0, "total_wager": 0.0, "biggest_win": 0.0, "game_counts": {}}
    
    st = user_stats[user_id]
    st["games"] += 1
    st["total_wager"] = float(st.get("total_wager", 0.0)) + float(bet_inr)
    st["total_pnl"] += profit_inr
    
    if game_name not in st["game_counts"]:
        st["game_counts"][game_name] = 0
    st["game_counts"][game_name] += 1
    
    if is_win:
        st["wins"] += 1
        if profit_inr > st["biggest_win"]:
            st["biggest_win"] = profit_inr
    else:
        st["losses"] += 1
    persist_user(user_id)


def get_user_total_wager(uid):
    st = user_stats.get(uid) or {}
    if "total_wager" in st and st["total_wager"] is not None:
        return float(st["total_wager"])
    logs = user_bet_logs.get(uid) or []
    if logs:
        return sum(float(item.get("bet", 0.0)) for item in logs)
    return 0.0

def generate_top_wagerers_image(viewer_id=None):
    ranked = []
    candidate_ids = set(user_stats.keys()) | set(user_bet_logs.keys()) | set(user_balances.keys())
    for uid in candidate_ids:
        wager_inr = get_user_total_wager(uid)
        if wager_inr > 0:
            st = user_stats.get(uid) or {}
            games = int(st.get("games", len(user_bet_logs.get(uid) or [])))
            wins = int(st.get("wins", 0))
            win_rate = (wins / games * 100.0) if games > 0 else 0.0
            uname = user_usernames.get(uid)
            fname = user_first_names.get(uid)
            label = f"@{uname}" if uname else (fname[:16] if fname else f"User {uid}")
            ranked.append({
                "uid": uid,
                "label": label,
                "wager_inr": wager_inr,
                "games": games,
                "win_rate": win_rate
            })

    ranked.sort(key=lambda x: x["wager_inr"], reverse=True)
    top10 = ranked[:10]

    width, height = 740, 620
    img = Image.new("RGB", (width, height), color=(14, 17, 29))
    d = ImageDraw.Draw(img)

    d.rectangle([0, 0, width, 84], fill=(28, 34, 58))
    d.rectangle([0, 82, width, 86], fill=(255, 198, 41))
    d.text((28, 18), "🏆 TOP 10 WAGERERS LEADERBOARD", fill=(255, 215, 64))
    d.text((28, 48), f"{BOT_USERNAME}  •  Total Volume (All Time)", fill=(185, 198, 230))

    y_hdr = 100
    d.text((28, y_hdr), "RANK", fill=(140, 155, 190))
    d.text((115, y_hdr), "PLAYER", fill=(140, 155, 190))
    d.text((380, y_hdr), "WAGERED", fill=(140, 155, 190))
    d.text((565, y_hdr), "GAMES / WR", fill=(140, 155, 190))
    d.line([(24, 122), (width - 24, 122)], fill=(45, 55, 85), width=1)

    if not top10:
        d.text((28, 160), "No wagers recorded yet. Play a game to claim #1!", fill=(200, 210, 235))
    else:
        medals = {1: "🥇", 2: "🥈", 3: "🥉"}
        row_h = 46
        start_y = 132
        for idx, row in enumerate(top10, start=1):
            ry = start_y + (idx - 1) * row_h
            bg_col = (22, 28, 46) if idx % 2 == 1 else (17, 21, 36)
            if idx == 1:
                bg_col = (44, 36, 16)
            d.rounded_rectangle([22, ry, width - 22, ry + row_h - 4], radius=8, fill=bg_col)

            rank_txt = f"#{idx}"
            rank_col = (255, 215, 64) if idx == 1 else ((210, 218, 235) if idx <= 3 else (155, 170, 200))
            name_col = (255, 225, 105) if idx == 1 else (238, 242, 250)
            wager_col = (72, 245, 155) if idx <= 3 else (110, 215, 255)

            curr = user_currency.get(viewer_id, "INR") if viewer_id else "INR"
            if curr == "USDT" and EXCHANGE_RATE > 0:
                w_disp = f"${row['wager_inr'] / EXCHANGE_RATE:,.2f}"
            else:
                w_disp = f"₹{row['wager_inr']:,.2f}"

            d.text((28, ry + 13), rank_txt, fill=rank_col)
            d.text((115, ry + 13), str(row["label"])[:20], fill=name_col)
            d.text((380, ry + 13), w_disp, fill=wager_col)
            d.text((565, ry + 13), f"{row['games']}g • {row['win_rate']:.0f}%", fill=(175, 188, 215))

    d.text((28, height - 28), "Public Leaderboard  •  Updated live from player wagers", fill=(120, 132, 160))

    bio = io.BytesIO()
    img.save(bio, "PNG")
    bio.seek(0)
    return bio

def build_dr_result_message(gid, dice_val, arg, is_win, win_amt=0.0, multiplier=0.0, user_id=None):
    if arg in ["high", "low", "odd", "even"]:
        pick_label = arg.upper()
    else:
        nums = [int(n.strip()) for n in str(arg).split(",")]
        pick_label = " • ".join(str(n) for n in nums)

    if is_win:
        return (
            f"📊 PREDICTION REPORT\n"
            f"━━━━━━━━━━━━━━━━\n"
            f"🔑 Round ID: {gid}\n"
            f"🎲 Actual Result: {dice_val}\n"
            f"🎯 Selected Range: {pick_label}\n"
            f"🔥 Final Status: Win\n"
            f"💰 Payout: {format_money(win_amt, user_id)} ({fmt_mult(multiplier)})\n"
            f"━━━━━━━━━━━━━━━━"
        )
    return (
        f"📊 PREDICTION REPORT\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"🔑 Round ID: {gid}\n"
        f"🎲 Actual Roll: {dice_val}\n"
        f"🎯 Selected Range: {pick_label}\n"
        f"📉 Final Status: Lost\n"
        f"💰 Payout: {format_money(0.0, user_id)}\n"
        f"━━━━━━━━━━━━━━━━"
    )

def remember_button_owner(chat_id, sent_or_msg_id, user_id):
    """Remember which player owns the buttons on a message (accepts a send_message result or a message id)."""
    msg_id = sent_or_msg_id
    if isinstance(sent_or_msg_id, dict):
        msg_id = sent_or_msg_id.get("result", {}).get("message_id") if sent_or_msg_id.get("ok") else None
    if chat_id is None or not msg_id or user_id is None:
        return
    button_owners[(chat_id, msg_id)] = user_id
    if len(button_owners) > 5000:
        for k in list(button_owners.keys())[:1000]:
            button_owners.pop(k, None)

def find_button_owner(chat_id, message_id):
    """Who owns the buttons on this message? None if unknown."""
    owner = button_owners.get((chat_id, message_id))
    if owner is not None:
        return owner
    for uid, st in list(pending_game_setup.items()):
        if st and st.get("message_id") == message_id and st.get("chat_id") in (chat_id, None):
            return uid
    for uid, g in list(active_games.items()):
        if isinstance(g, dict) and g.get("start_message_id") == message_id and g.get("start_chat_id") in (chat_id, None):
            return uid
    for uid, bj in list(active_bj_games.items()):
        if bj and bj.get("message_id") == message_id and bj.get("chat_id") in (chat_id, None):
            return uid
    return None

def create_post_match_keyboard(user_id, payload):
    token = uuid.uuid4().hex[:10]
    post_match_actions[token] = payload
    last_bet = float(payload.get("bet", 0.0))
    double_bet = last_bet * 2.0

    again_label = "🔁 Bet Again"
    row1 = [{"text": again_label, "callback_data": f"pm_again_{token}"}]

    if double_bet <= MAX_BET:
        double_label = "⚡ Bet Double"
        row1.append({"text": double_label, "callback_data": f"pm_double_{token}"})

    return {"inline_keyboard": [row1]}

def execute_post_match_restart(chat_id, message_id, user_id, payload, multiplier_factor, callback_query_id):
    global HOUSE_BALANCE
    kind = payload.get("kind")
    last_bet = float(payload.get("bet", 0.0))
    next_bet = last_bet * multiplier_factor

    if next_bet <= 0:
        answer_callback(callback_query_id, "Invalid bet amount.")
        return

    if next_bet < MIN_BET or next_bet > MAX_BET:
        answer_callback(
            callback_query_id,
            f"Bet limit check failed! Allowed: {format_money(MIN_BET, user_id)} - {format_money(MAX_BET, user_id)}"
        )
        return

    active_summary = get_active_game_summary(user_id)
    if active_summary:
        answer_callback(callback_query_id, f"Finish your active {active_summary} game first!")
        return

    fresh_bal = float(user_balances.get(user_id, 0.0))
    if fresh_bal < next_bet:
        answer_callback(
            callback_query_id,
            f"Insufficient balance! Need {format_money(next_bet, user_id)}, have {format_money(fresh_bal, user_id)}"
        )
        return

    if payload.get("result_grid"):
        set_inline_keyboard(chat_id, message_id, {"inline_keyboard": payload["result_grid"]})
    else:
        remove_inline_keyboard(chat_id, message_id)

    if kind == "versus":
        gid = generate_game_id()
        start_versus_match(
            chat_id,
            None,
            user_id,
            payload["emoji"],
            next_bet,
            payload.get("mode") or "normal",
            payload.get("rw_label") or "1r1w",
            game_id=gid
        )
        answer_callback(callback_query_id, f"Started {format_money(next_bet, user_id)} match!")

    elif kind in ("mines", "tower", "limbo"):
        answer_callback(callback_query_id, f"Starting {kind.title()} ({format_money(next_bet, user_id)})!")
        restart_fair_game(chat_id, user_id, payload, next_bet)

    elif kind == "7up":
        choice_7up = normalize_7up_choice(payload.get("choice_7up")) or "up"
        answer_callback(callback_query_id, f"Rolling 7Up ({format_money(next_bet, user_id)})!")
        run_7up_game(chat_id, user_id, next_bet, choice_7up, raw_choice_text=payload.get("choice_7up"))

    elif kind == "bj":
        start_bj_game(chat_id, user_id, next_bet)
        answer_callback(callback_query_id, f"Blackjack started ({format_money(next_bet, user_id)})!")

    elif kind == "dr":
        arg = payload.get("dr_arg")
        gid = generate_game_id()
        user_balances[user_id] = fresh_bal - next_bet
        persist_user(user_id)
        register_game_record(gid, "prediction", user_id, next_bet, meta={"choice": arg}, refund_on_cancel=True)

        is_win = False
        multiplier = 0.0
        win_desc = ""
        if arg in ["high", "low", "odd", "even"]:
            res = send_animated_game(chat_id, "🎲")
            dice_val = res["result"]["dice"]["value"] if res and "result" in res else random.randint(1, 6)
            time.sleep(1)
            if arg == "high" and dice_val in [4, 5, 6]: is_win = True
            elif arg == "low" and dice_val in [1, 2, 3]: is_win = True
            elif arg == "odd" and dice_val in [1, 3, 5]: is_win = True
            elif arg == "even" and dice_val in [2, 4, 6]: is_win = True
            multiplier = float(GAME_MULTIPLIERS.get("dr", 1.92))
            win_desc = f"Prediction: {arg.upper()}"
        else:
            nums = [int(n.strip()) for n in str(arg).split(",")]
            res = send_animated_game(chat_id, "🎲")
            dice_val = res["result"]["dice"]["value"] if res and "result" in res else random.randint(1, 6)
            time.sleep(1)
            if dice_val in nums: is_win = True
            dr_num_map = GAME_MULTIPLIERS.get("dr_nums", {1: 5.56, 2: 2.88, 3: 1.92, 4: 1.44, 5: 1.15})
            multiplier = float(dr_num_map.get(len(nums), 1.0))
            win_desc = f"Numbers: {nums}"

        if is_win:
            win_amt = next_bet * multiplier
            profit_inr = win_amt - next_bet
            user_balances[user_id] = float(user_balances.get(user_id, 0.0)) + win_amt
            HOUSE_BALANCE -= profit_inr
            persist_user(user_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            update_user_stats(user_id, "prediction", next_bet, profit_inr, True)
            record_user_bet(user_id, f"Prediction ({win_desc})", next_bet, profit_inr, "WON", game_id=gid)
            mark_game_finished(gid, "completed", extra_meta={"outcome": "WON", "pnl": profit_inr})
            log_win_to_channel(user_id, "🔮", "Predict", win_amt, fmt_mult(multiplier))
            result_text = build_dr_result_message(gid, dice_val, arg, True, win_amt=win_amt, multiplier=multiplier, user_id=user_id)
        else:
            profit_inr = -next_bet
            HOUSE_BALANCE += next_bet
            persist_user(user_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            update_user_stats(user_id, "prediction", next_bet, profit_inr, False)
            record_user_bet(user_id, f"Prediction ({win_desc})", next_bet, profit_inr, "LOST", game_id=gid)
            mark_game_finished(gid, "completed", extra_meta={"outcome": "LOST", "pnl": profit_inr})
            result_text = build_dr_result_message(gid, dice_val, arg, False, user_id=user_id)

        pm_payload = {"kind": "dr", "owner_id": user_id, "bet": next_bet, "dr_arg": arg}
        send_message(chat_id, result_text, reply_markup=create_post_match_keyboard(user_id, pm_payload))
        answer_callback(callback_query_id, f"Predicted {arg} ({format_money(next_bet, user_id)})!")

def format_history_money(amount_in_inr, user_id):
    curr = user_currency.get(user_id, 'INR')
    if curr == 'USDT':
        val = amount_in_inr / EXCHANGE_RATE
        return f"${val:.2f}"
    return f"₹{amount_in_inr:.2f}"

def history_page_keyboard(target_uid, page, total_items):
    total_pages = max(1, (total_items + PAGE_SIZE - 1) // PAGE_SIZE)
    page = max(0, min(page, total_pages - 1))
    nav_row = []
    if page > 0:
        nav_row.append({"text": "⬅️", "callback_data": f"myhistpg_{target_uid}_{page - 1}"})
    if page + 1 < total_pages:
        nav_row.append({"text": "➡️", "callback_data": f"myhistpg_{target_uid}_{page + 1}"})
    return {"inline_keyboard": [nav_row]} if nav_row else None

def build_user_history_page(user_id, page=0):
    raw_logs = user_bet_logs.get(user_id, [])
    logs = list(reversed(raw_logs))
    total_items = len(logs)
    total_pages = max(1, (total_items + PAGE_SIZE - 1) // PAGE_SIZE)
    page = max(0, min(page, total_pages - 1))

    start_idx = page * PAGE_SIZE
    end_idx = start_idx + PAGE_SIZE
    page_items = logs[start_idx:end_idx]

    if not page_items:
        return "📜 *Bet History*\n\n_No bets found yet._\n\nPage 1/1", None

    lines = ["📜 *Your Bet History*", ""]
    for item in page_items:
        game_title = item.get("game", "Game")
        gid = item.get("game_id")
        id_part = f" `#{gid}`" if gid else ""
        bet_val = float(item.get("bet", 0.0))
        pnl_val = float(item.get("pnl", 0.0))
        outcome = str(item.get("outcome", "")).upper()
        if outcome == "PUSH":
            payout_val = bet_val
        elif pnl_val > 0:
            payout_val = bet_val + pnl_val
        else:
            payout_val = 0.0

        t_str = item.get("time", "")
        lines.append(f"🎲 *{game_title}*{id_part}")
        lines.append(f"⬆️ Bet *{format_history_money(bet_val, user_id)}*")
        lines.append(f"⬇️ Payout *{format_history_money(payout_val, user_id)}*")
        if t_str:
            lines.append(f"🕒 `{t_str}`")
        lines.append("")

    lines.append(f"Page {page + 1}/{total_pages}")
    return "\n".join(lines).strip(), history_page_keyboard(user_id, page, total_items)

def info_menu_keyboard(target_uid):
    return {
        "inline_keyboard": [
            [
                {"text": "📥 Deposits", "callback_data": f"infopg_{target_uid}_deposits_0"},
                {"text": "📤 Withdrawals", "callback_data": f"infopg_{target_uid}_withdrawals_0"},
                {"text": "🎲 Bets", "callback_data": f"infopg_{target_uid}_bets_0"},
            ]
        ]
    }

def info_page_keyboard(target_uid, section, page, total_items):
    total_pages = max(1, (total_items + PAGE_SIZE - 1) // PAGE_SIZE)
    page = max(0, min(page, total_pages - 1))
    nav_row = []
    if page > 0:
        nav_row.append({"text": "⬅️ Previous", "callback_data": f"infopg_{target_uid}_{section}_{page - 1}"})
    if page + 1 < total_pages:
        nav_row.append({"text": "➡️ Next", "callback_data": f"infopg_{target_uid}_{section}_{page + 1}"})

    switch_row = []
    for sec_key, sec_label in [("deposits", "📥 Deposits"), ("withdrawals", "📤 Withdrawals"), ("bets", "🎲 Bets")]:
        prefix = "• " if sec_key == section else ""
        switch_row.append({"text": f"{prefix}{sec_label}", "callback_data": f"infopg_{target_uid}_{sec_key}_0"})

    rows = []
    if nav_row:
        rows.append(nav_row)
    rows.append(switch_row)
    return {"inline_keyboard": rows}

def build_user_info_summary(target_uid):
    bal_str = format_money(user_balances.get(target_uid, 0.0), target_uid)
    curr = user_currency.get(target_uid, "INR")
    uname = user_usernames.get(target_uid)
    uname_str = f"@{uname}" if uname else "N/A"
    status_str = "🔴 BANNED" if target_uid in banned_users else "🟢 Active"

    u_deps = [d for d in deposit_history if d.get("user") == target_uid]
    u_wds = [w for w in withdrawal_history if w.get("user") == target_uid]
    u_bets = user_bet_logs.get(target_uid, [])

    dep_total = format_money(user_deposits.get(target_uid, 0.0), target_uid)
    wd_total = format_money(user_withdrawals.get(target_uid, 0.0), target_uid)

    lines = [
        "🪪 *User Lifetime Info*",
        f"• *User ID:* `{target_uid}`",
        f"• *Username:* {uname_str}",
        f"• *Status:* {status_str}",
        f"• *Currency:* *{curr}*",
        f"• *Current Balance:* *{bal_str}*",
        f"• *Lifetime Deposits:* *{dep_total}* (`{len(u_deps)}` txns)",
        f"• *Lifetime Withdrawals:* *{wd_total}* (`{len(u_wds)}` txns)",
        f"• *Lifetime Bets:* *{len(u_bets)}*",
        "",
        "Tap a section below to view lifetime history (5 per page):"
    ]
    return "\n".join(lines)

def build_user_info_section_page(target_uid, section, page):
    uname = user_usernames.get(target_uid)
    who_str = f"@{uname} (`{target_uid}`)" if uname else f"`{target_uid}`"

    if section == "deposits":
        records = [d for d in deposit_history if d.get("user") == target_uid]
        title = "📥 *Lifetime Deposits*"
    elif section == "withdrawals":
        records = [w for w in withdrawal_history if w.get("user") == target_uid]
        title = "📤 *Lifetime Withdrawals*"
    else:
        records = user_bet_logs.get(target_uid, [])
        title = "🎲 *Lifetime Bets*"

    total_items = len(records)
    total_pages = max(1, (total_items + PAGE_SIZE - 1) // PAGE_SIZE)
    page = max(0, min(page, total_pages - 1))

    start_idx = page * PAGE_SIZE
    end_idx = start_idx + PAGE_SIZE
    slice_items = records[start_idx:end_idx]

    lines = [
        f"{title} — {who_str}",
        f"📄 *Page {page + 1} / {total_pages}* (Total: *{total_items}*)",
        ""
    ]

    if not slice_items:
        lines.append("_No records found._")
    else:
        for idx, item in enumerate(slice_items, start=start_idx + 1):
            if section == "deposits":
                t_str = item.get("time", "N/A")
                utr_str = item.get("utr") or "N/A"
                lines.append(f"{idx}. `{t_str}` | *{format_money(item['amount'], target_uid)}* | UTR: `{utr_str}`")
            elif section == "withdrawals":
                t_str = item.get("time", "N/A")
                upi_str = item.get("upi") or "N/A"
                lines.append(f"{idx}. `{t_str}` | *{format_money(item['amount'], target_uid)}* | UPI: `{upi_str}`")
            else:
                gid_part = f"`{item['game_id']}` | " if item.get("game_id") else ""
                pnl_val = item.get("pnl", 0.0)
                sign = "+" if pnl_val > 0 else ""
                pnl_str = f"{sign}{format_money(pnl_val, target_uid)}"
                lines.append(
                    f"{idx}. {gid_part}*{item['game']}* | Bet: *{format_money(item['bet'], target_uid)}* | "
                    f"*{item['outcome']}* ({pnl_str}) | `{item.get('time', '')}`"
                )

    return "\n".join(lines), info_page_keyboard(target_uid, section, page, total_items)

def build_game_search_report(target_gid):
    gid = target_gid.strip().upper()
    rec = game_id_registry.get(gid)
    if not rec:
        return f"⚠️ No game found with ID `{gid}`."

    meta = rec.get("meta", {})
    kind_labels = {
        "bot_versus": "🤖 Bot Versus",
        "pvp_match": "⚔️ Player vs Player",
        "blackjack": "🃏 Blackjack",
        "prediction": "🔮 Dice Prediction",
        "seven_up": "🎲🎲 7Up",
        "mines": "💣 Mines",
        "tower": "🗼 Tower",
        "limbo": "🚀 Limbo",
    }
    kind_str = kind_labels.get(rec.get("kind"), rec.get("kind", "Game"))
    status_str = str(rec.get("status", "unknown")).upper()
    owner_id = rec.get("owner_id")
    bet_inr = rec.get("bet_inr", 0.0)

    lines = [
        "🔎 *Game ID Details*",
        f"• *Game ID:* `{gid}`",
        f"• *Type:* {kind_str}",
        f"• *Status:* *{status_str}*",
        f"• *Started By:* `{owner_id}`",
    ]

    if rec.get("kind") == "pvp_match":
        p1 = meta.get("p1_id")
        p2 = meta.get("p2_id")
        lines.append(f"• *Players:* P1 `{p1}` vs P2 `{p2}`")
        lines.append(f"• *Bet Each:* *{format_money(bet_inr, owner_id)}*")
        if status_str == "COMPLETED":
            if meta.get("winner_id"):
                w_lbl = f" ({meta['winner_label']})" if meta.get("winner_label") else ""
                lines.append(f"• *Winner:* `{meta['winner_id']}`{w_lbl}")
            else:
                lines.append("• *Winner:* _N/A_")
    elif rec.get("kind") == "bot_versus":
        lines.append(f"• *Bet Amount:* *{format_money(bet_inr, owner_id)}*")
        if status_str == "COMPLETED":
            w_id = meta.get("winner_id")
            w_lbl = meta.get("winner_label")
            if w_id is not None:
                lbl_part = f" ({w_lbl})" if w_lbl else ""
                lines.append(f"• *Winner:* `{w_id}`{lbl_part}")
            else:
                lines.append("• *Winner:* _N/A_")
    else:
        lines.append(f"• *Bet Amount:* *{format_money(bet_inr, owner_id)}*")
        if status_str == "COMPLETED" and meta.get("outcome"):
            lines.append(f"• *Outcome:* *{meta['outcome']}*")

    if meta.get("emoji"):
        g_name = GAME_NAME_MAP.get(meta["emoji"], "Game")
        lines.append(f"• *Game:* {g_name} ({meta['emoji']})")
    if meta.get("rw_label") or meta.get("mode"):
        lines.append(f"• *Format / Mode:* `{meta.get('rw_label', '-')}` / *{meta.get('mode', '-')}*")
    if meta.get("choice"):
        lines.append(f"• *Prediction:* *{str(meta['choice']).upper()}*")
    if meta.get("nums"):
        lines.append(f"• *Numbers:* `{meta['nums']}`")

    lines.append(f"• *Created At:* `{rec.get('created_at', 'N/A')}`")
    if rec.get("ended_at"):
        lines.append(f"• *Ended At:* `{rec.get('ended_at')}`")

    return "\n".join(lines)

def cancel_game_by_id(target_gid):
    gid = target_gid.strip().upper()
    rec = game_id_registry.get(gid)
    if not rec:
        return False, f"⚠️ Game ID `{gid}` not found."

    if rec.get("status") != "active":
        return False, f"⚠️ Game `{gid}` is already *{rec.get('status')}*."

    kind = rec.get("kind")
    owner_id = rec.get("owner_id")
    bet_inr = rec.get("bet_inr", 0.0)
    refund = rec.get("refund_on_cancel", True)

    if kind == "bot_versus":
        active_games.pop(owner_id, None)
        if refund and bet_inr > 0:
            user_balances[owner_id] = user_balances.get(owner_id, 0.0) + bet_inr
    elif kind == "pvp_match":
        match_id = rec.get("meta", {}).get("match_id")
        p1 = rec.get("meta", {}).get("p1_id")
        p2 = rec.get("meta", {}).get("p2_id")
        if match_id:
            active_pvp_games.pop(match_id, None)
        if p1 and active_games.get(p1) == match_id:
            active_games.pop(p1, None)
        if p2 and active_games.get(p2) == match_id:
            active_games.pop(p2, None)
        if refund and bet_inr > 0:
            if p1 is not None:
                user_balances[p1] = user_balances.get(p1, 0.0) + bet_inr
            if p2 is not None:
                user_balances[p2] = user_balances.get(p2, 0.0) + bet_inr
    elif kind == "blackjack":
        bj = active_bj_games.pop(owner_id, None)
        effective_bet = (bj or {}).get("bet", bet_inr)
        if refund and effective_bet > 0:
            user_balances[owner_id] = user_balances.get(owner_id, 0.0) + effective_bet
    elif kind == "seven_up":
        g7 = active_7up_games.pop(owner_id, None)
        effective_bet = (g7 or {}).get("bet", bet_inr)
        if refund and effective_bet > 0:
            user_balances[owner_id] = user_balances.get(owner_id, 0.0) + effective_bet
    elif kind == "prediction":
        if refund and bet_inr > 0:
            user_balances[owner_id] = user_balances.get(owner_id, 0.0) + bet_inr
    elif kind in ("mines", "tower"):
        store = active_mines_games if kind == "mines" else active_tower_games
        live = store.get(owner_id)
        if live and live.get("game_id") == gid and (live.get("revealed") or live.get("picks")):
            return False, f"⚠️ Game `{gid}` already has picks. Use the 💰 Cashout button instead."
        if live and live.get("game_id") == gid:
            store.pop(owner_id, None)
        if refund and bet_inr > 0:
            user_balances[owner_id] = user_balances.get(owner_id, 0.0) + bet_inr
            persist_user(owner_id)

    mark_game_finished(gid, "cancelled")
    refund_note = " Stake refunded." if refund and bet_inr > 0 else ""
    return True, f"🛑 Game `{gid}` has been *CANCELLED*.{refund_note}"

def finish_bj_game(chat_id, message_id, user_id, bj, outcome):
    global HOUSE_BALANCE
    gid = bj.get("game_id")
    p_cards = bj["player_cards"]
    d_cards = bj["dealer_cards"]
    p_tot = calculate_hand_total(p_cards)
    d_tot = calculate_hand_total(d_cards)
    bet = bj["bet"]
    mult = float(GAME_MULTIPLIERS.get("bj", 2.0))

    header = (
        f"🃏 *Blackjack Result* (`{gid}`)\n\n"
        f"👤 Your Hand: {format_cards(p_cards)} (*{p_tot}*)\n"
        f"🤖 Dealer Hand: {format_cards(d_cards)} (*{d_tot}*)\n"
        f"💰 Total Bet: {format_money(bet, user_id)}\n\n"
    )

    if outcome == "push":
        user_balances[user_id] = user_balances.get(user_id, 0.0) + bet
        persist_user(user_id)
        update_user_stats(user_id, "blackjack", bet, 0.0, False)
        record_user_bet(user_id, "Blackjack", bet, 0.0, "PUSH", game_id=gid)
        body = f"🤝 *Push (Tie)!* Bet refunded.\n💰 Balance: {format_money(user_balances[user_id], user_id)}"
    elif outcome == "win":
        win_amt = bet * mult
        profit_inr = win_amt - bet
        user_balances[user_id] = user_balances.get(user_id, 0.0) + win_amt
        HOUSE_BALANCE -= profit_inr
        persist_user(user_id)
        save_config_value("house_balance", HOUSE_BALANCE)
        update_user_stats(user_id, "blackjack", bet, profit_inr, True)
        record_user_bet(user_id, "Blackjack", bet, profit_inr, "WON", game_id=gid)
        log_win_to_channel(user_id, "🃏", "Blackjack", win_amt, fmt_mult(mult))
        body = f"🎉 *You WON {format_money(win_amt, user_id)}* (`{fmt_mult(mult)}`)! 🥳\n💰 Balance: {format_money(user_balances[user_id], user_id)}"
    else:
        profit_inr = -bet
        HOUSE_BALANCE += bet
        update_user_stats(user_id, "blackjack", bet, profit_inr, False)
        record_user_bet(user_id, "Blackjack", bet, profit_inr, "LOST", game_id=gid)
        reason_txt = "Bust! Over 21." if outcome == "bust" else "Dealer wins."
        body = f"😢 *You Lost!* {reason_txt}\n💰 Balance: {format_money(user_balances[user_id], user_id)}"

    mark_game_finished(gid, "completed", extra_meta={"outcome": outcome})
    if bj.get("seeds"):
        fair_reveal(bj["seeds"], user_id)
        body += bj_fair_footer(bj, reveal=True)
    pm_bj_payload = {"kind": "bj", "owner_id": user_id, "bet": bet}
    edit_message(chat_id, message_id, header + body, reply_markup=create_post_match_keyboard(user_id, pm_bj_payload))
    if user_id in active_bj_games:
        del active_bj_games[user_id]

def play_dealer_and_settle(chat_id, message_id, user_id, bj):
    p_tot = calculate_hand_total(bj["player_cards"])
    while calculate_hand_total(bj["dealer_cards"]) < 17:
        bj["dealer_cards"].append(bj_draw(bj))
    d_tot = calculate_hand_total(bj["dealer_cards"])

    if d_tot > 21 or p_tot > d_tot:
        finish_bj_game(chat_id, message_id, user_id, bj, "win")
    elif p_tot < d_tot:
        finish_bj_game(chat_id, message_id, user_id, bj, "lose")
    else:
        finish_bj_game(chat_id, message_id, user_id, bj, "push")

def send_animated_game(chat_id, emoji, reply_to_message_id=None):
    """Every emoji throw in a group is done by a helper bot (round-robin).
    Main bot throws only in a player's DM, or as emergency backup when no helper could."""
    payload = {"chat_id": chat_id, "emoji": emoji}
    if reply_to_message_id:
        payload["reply_to_message_id"] = reply_to_message_id
        payload["allow_sending_without_reply"] = True

    # Player DM: helpers can't post there, the main bot throws.
    if isinstance(chat_id, int) and chat_id > 0:
        return _main_throw(payload)

    deadline = time.time() + HELPER_THROW_WAIT
    while True:
        order = _helpers_for_chat(chat_id)
        if not order:
            break
        now = time.time()
        for h in order:
            if _helper_cooldown.get(h.get("id"), 0) > now:
                continue
            data = _helper_post(h, "sendDice", payload)
            if data and data.get("ok") and (data.get("result") or {}).get("dice"):
                return data
        left = deadline - time.time()
        if left <= 0:
            break
        soonest = min(max(0.3, _helper_cooldown.get(h.get("id"), 0) - time.time()) for h in order)
        if soonest > left:
            break
        time.sleep(soonest)

    # Emergency backup: no helper could throw here.
    why = "no helper is ON" if not any(h.get("enabled") for h in HELPER_BOTS) else "helpers failed or are not in this group"
    _note_backup_throw(chat_id, why)
    return _main_throw(payload)

def roll_bot_series(chat_id, emoji, rolls_count, reply_to_message_id=None):
    vals = []
    for idx in range(rolls_count):
        res = send_animated_game(chat_id, emoji, reply_to_message_id=reply_to_message_id if idx == 0 else None)
        v = res['result']['dice']['value'] if res and 'result' in res else random.randint(1, 6)
        vals.append(v)
        if rolls_count > 1:
            time.sleep(0.6)
    return vals

def create_zapupi_order(amount, chat_id):
    url = "https://pay.zapupi.com/api/create-order"
    order_id = "ORD" + str(int(time.time() * 1000))
    
    payload = {
        "zap_key": ZAPUPI_API_KEY,
        "order_id": order_id,
        "amount": str(amount),
        "remark": f"Deposit|{chat_id}",
        "webhook_url": "https://xyren-upi.onrender.com/zapupi-webhook"
    }
    
    headers = {"Content-Type": "application/json"}
    try:
        response = requests.post(url, json=payload, headers=headers, timeout=10)
        data = response.json()
        if data.get("status") == "success" and data.get("payment_url"):
            msg = (
                f"🔗 *Deposit Order Created!*\n\n"
                f"💰 Amount: *₹{amount}*\n"
                f"🧾 Order ID: `{order_id}`"
            )
            kb = {
                "inline_keyboard": [
                    [{"text": "💳 Deposit Now", "url": data.get("payment_url")}]
                ]
            }
            return msg, kb
        else:
            return f"❌ Failed: {data.get('message', 'Unknown error')}", None
    except Exception:
        return "⚠️ Failed to connect to payment gateway.", None

def build_pvb_round_text(user_id, emoji, u_vals, b_vals, round_winner, game, gid, round_num):
    """PvB round result. round_winner: 'user', 'bot' or None (tie)."""
    if round_winner == "user":
        winner_line = f"🔥 Winner: {tag_player(user_id)}"
    elif round_winner == "bot":
        winner_line = "🔥 Winner: Bot"
    else:
        winner_line = "🤝 Round Tied — no point"
    return (
        f"⚔️ *Round {round_num} Result*\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{emoji} {tag_player(user_id)} — {roll_text(u_vals)}{' ✅' if round_winner == 'user' else ''}\n"
        f"{emoji} Bot — {roll_text(b_vals)}{' ✅' if round_winner == 'bot' else ''}\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{winner_line}\n"
        f"🏆 Score: {game['user_wins']} : {game['bot_wins']} | First to {game['target_wins']}\n"
        f"🆔 `{gid}`"
    )

def build_pvb_final_text(user_id, emoji, u_vals, b_vals, user_won, game, gid, win_amt, mult):
    """PvB final result. Multiplier is read live, so /setmulti changes show here."""
    return (
        f"⚔️ *Final Round Result*\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{emoji} {tag_player(user_id)} — {roll_text(u_vals)}{' ✅' if user_won else ''}\n"
        f"{emoji} Bot — {roll_text(b_vals)}{'' if user_won else ' ✅'}\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"🔥 Winner: {tag_player(user_id) if user_won else 'Bot'}\n"
        f"🏆 Score: {game['user_wins']} : {game['bot_wins']} | First to {game['target_wins']}\n"
        f"🆔 `{gid}`\n"
        f"🏁 Winnings: {format_money(win_amt, user_id)} ({fmt_mult(mult)})"
    )

def resolve_round_and_match(chat_id, user_id, game):
    with helper_voice(chat_id):
        return _resolve_round_and_match(chat_id, user_id, game)

def _resolve_round_and_match(chat_id, user_id, game):
    global HOUSE_BALANCE
    gid = game.get("game_id")
    emoji = game["emoji"]
    g_name = GAME_NAME_MAP.get(emoji, "Game")
    mode = game["mode"]
    rw_label = game["rw_label"]
    target_wins = game["target_wins"]
    bet = game["bet"]
    
    u_vals = game["current_user_rolls"]
    b_vals = game["current_bot_rolls"]
    u_sum = sum(u_vals)
    b_sum = sum(b_vals)
    
    u_expr = "+".join(map(str, u_vals))
    b_expr = "+".join(map(str, b_vals))
    
    round_num = game["round_num"]
    mode_tag = "🔥 CRAZY" if mode == "crazy" else "⚡ NORMAL"
    
    round_winner = None
    if u_sum == b_sum:
        r_status = "🤝 *Round Tied!* No point awarded."
    elif mode == "crazy":
        if u_sum < b_sum:
            round_winner = "user"
            game["user_wins"] += 1
            r_status = "✨ *You took this round!* (Lower sum wins)"
        else:
            round_winner = "bot"
            game["bot_wins"] += 1
            r_status = "🤖 *Bot took this round!* (Lower sum wins)"
    else:
        if u_sum > b_sum:
            round_winner = "user"
            game["user_wins"] += 1
            r_status = "✨ *You took this round!* (Higher sum wins)"
        else:
            round_winner = "bot"
            game["bot_wins"] += 1
            r_status = "🤖 *Bot took this round!* (Higher sum wins)"

    if game["user_wins"] >= target_wins or game["bot_wins"] >= target_wins:
        user_won_match = game["user_wins"] >= target_wins
        label = f"Bot {g_name} ({rw_label}/{mode})"
        if user_won_match:
            mult = get_versus_multiplier(emoji)
            win_amt = bet * mult
            profit_inr = win_amt - bet
            user_balances[user_id] = user_balances.get(user_id, 0.0) + win_amt
            HOUSE_BALANCE -= profit_inr
            persist_user(user_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            update_user_stats(user_id, emoji, bet, profit_inr, True)
            record_user_bet(user_id, label, bet, profit_inr, "WON", game_id=gid)
            mark_game_finished(
                gid,
                "completed",
                extra_meta={
                    "outcome": "WON",
                    "winner_id": user_id,
                    "winner_label": format_win_actor(user_id),
                    "pnl": profit_inr
                }
            )
            log_win_to_channel(user_id, emoji, g_name, win_amt, fmt_mult(mult))
            final_text = build_pvb_final_text(user_id, emoji, u_vals, b_vals, True, game, gid, win_amt, mult)
        else:
            profit_inr = -bet
            HOUSE_BALANCE += bet
            update_user_stats(user_id, emoji, bet, profit_inr, False)
            record_user_bet(user_id, label, bet, profit_inr, "LOST", game_id=gid)
            mark_game_finished(
                gid,
                "completed",
                extra_meta={
                    "outcome": "LOST",
                    "winner_id": "Bot",
                    "winner_label": "Bot",
                    "pnl": profit_inr
                }
            )
            final_text = build_pvb_final_text(user_id, emoji, u_vals, b_vals, False, game, gid, 0.0, get_versus_multiplier(emoji))

        pm_vs_payload = {
            "kind": "versus",
            "owner_id": user_id,
            "bet": bet,
            "emoji": emoji,
            "mode": mode,
            "rw_label": rw_label
        }
        send_message(chat_id, final_text, reply_markup=create_post_match_keyboard(user_id, pm_vs_payload))
        if user_id in active_games:
            del active_games[user_id]
        return

    msg = build_pvb_round_text(user_id, emoji, u_vals, b_vals, round_winner, game, gid, round_num)
    send_message(chat_id, msg)

    game["round_num"] += 1
    game["current_user_rolls"] = []
    game["current_bot_rolls"] = []
    rolls_per_round = game["rolls_per_round"]
    
    if game["first_turn"] == "bot":
        game["step"] = "waiting_user_second"
        send_message(chat_id, f"🤖 *Round {game['round_num']}* — Bot is throwing `{emoji}` x{rolls_per_round}...")
        b_next = roll_bot_series(chat_id, emoji, rolls_per_round)
        game["current_bot_rolls"] = b_next
        b_next_expr = "+".join(map(str, b_next))
        send_message(chat_id, f"🤖 Bot Roll: `{b_next_expr}` (*{sum(b_next)}*)\n\n👉 *Now* {tag_player(user_id)}*'s turn! Send `{emoji}` x{rolls_per_round} in chat.*")
        schedule_pvb_turn_timeout(chat_id, user_id, game)
    else:
        game["step"] = "waiting_user_first"
        send_message(chat_id, f"👤 *Round {game['round_num']}* — Your turn! Send `{emoji}` x{rolls_per_round} in chat.")
        schedule_pvb_turn_timeout(chat_id, user_id, game)

# =====================================================================
# 🔐 PROVABLY FAIR GAMES: MINES · TOWER · LIMBO
# ---------------------------------------------------------------------
# result bytes = HMAC_SHA256(key=server_seed, msg=f"{client_seed}:{nonce}:{round}")
# every 4 bytes -> one float in [0, 1). Player sees sha256(server_seed)
# before betting. Every bet gets its own fresh server seed, revealed
# automatically when that game ends (so it can never predict another bet).
# =====================================================================
import hmac as _pf_hmac
import hashlib as _pf_hashlib
import secrets as _pf_secrets
import math as _pf_math
from urllib.parse import urlencode as _pf_urlencode

FAIR_HOUSE_EDGE = 0.08          # 8% house edge
FAIR_RTP = 1.0 - FAIR_HOUSE_EDGE
VERIFY_URL = os.environ.get("VERIFY_URL")  # optional: link to the online verify page

MINES_TILES = 25
MINES_DEFAULT = 3
LIMBO_MAX = 1000000.0
LIMBO_MIN_TARGET = 1.01
LIMBO_MAX_TARGET = 1000.0
TOWER_LEVELS = 9
TOWER_DIFFICULTIES = {
    "easy":   {"cols": 4, "bombs": 1},
    "medium": {"cols": 3, "bombs": 1},
    "hard":   {"cols": 2, "bombs": 1},
    "expert": {"cols": 3, "bombs": 2},
    "master": {"cols": 4, "bombs": 3},
}

fair_seeds = {}             # uid -> {"server_seed", "client_seed", "nonce"}
revealed_server_seeds = {}  # sha256(server_seed) -> server_seed
active_mines_games = {}     # uid -> game dict
active_tower_games = {}     # uid -> game dict


# ---------------- core math (same as the verify page) ----------------
def pf_sha256(text_val):
    return _pf_hashlib.sha256(text_val.encode()).hexdigest()

def pf_floats(server_seed, client_seed, nonce, count):
    out = []
    rnd = 0
    while len(out) < count:
        msg = f"{client_seed}:{nonce}:{rnd}".encode()
        digest = _pf_hmac.new(server_seed.encode(), msg, _pf_hashlib.sha256).digest()
        for i in range(0, 32, 4):
            if len(out) >= count:
                break
            f = 0.0
            for j in range(4):
                f += digest[i + j] / (256 ** (j + 1))
            out.append(f)
        rnd += 1
    return out

def pf_pick(floats, size, picks):
    pool = list(range(size))
    res = []
    for i in range(picks):
        idx = int(_pf_math.floor(floats[i] * len(pool)))
        res.append(pool.pop(idx))
    return res

def pf_floor2(x):
    return _pf_math.floor(x * 100) / 100

def pf_limbo_result(seeds):
    f = pf_floats(seeds["server_seed"], seeds["client_seed"], seeds["nonce"], 1)[0]
    if f == 0:
        return LIMBO_MAX
    return min(LIMBO_MAX, max(1.0, pf_floor2((1.0 / f) * FAIR_RTP)))

def pf_mines_layout(seeds, mines):
    floats = pf_floats(seeds["server_seed"], seeds["client_seed"], seeds["nonce"], mines)
    return pf_pick(floats, MINES_TILES, mines)

def pf_mines_multiplier(mines, safe_revealed):
    if safe_revealed <= 0:
        return 1.0
    fair = 1.0
    for i in range(safe_revealed):
        fair *= (MINES_TILES - i) / (MINES_TILES - mines - i)
    return pf_floor2(fair * FAIR_RTP)

def pf_tower_layout(seeds, difficulty):
    cfg = TOWER_DIFFICULTIES[difficulty]
    cols, bombs = cfg["cols"], cfg["bombs"]
    floats = pf_floats(seeds["server_seed"], seeds["client_seed"], seeds["nonce"], TOWER_LEVELS * bombs)
    levels = []
    for lvl in range(TOWER_LEVELS):
        levels.append(sorted(pf_pick(floats[lvl * bombs:(lvl + 1) * bombs], cols, bombs)))
    return levels

def pf_tower_multiplier(difficulty, levels_cleared):
    if levels_cleared <= 0:
        return 1.0
    cfg = TOWER_DIFFICULTIES[difficulty]
    return pf_floor2((cfg["cols"] / (cfg["cols"] - cfg["bombs"])) ** levels_cleared * FAIR_RTP)


# ---------------- seeds storage ----------------
def init_fair_db():
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS fair_seeds (
                        user_id BIGINT PRIMARY KEY,
                        server_seed TEXT,
                        client_seed TEXT,
                        nonce BIGINT DEFAULT 0
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS fair_revealed_seeds (
                        seed_hash TEXT PRIMARY KEY,
                        server_seed TEXT,
                        user_id BIGINT
                    )
                """)
    except Exception as e:
        print(f"DB init_fair error: {e}")
    finally:
        conn.close()

def load_fair_from_db():
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn.cursor(cursor_factory=RealDictCursor) as cur:
            cur.execute("SELECT user_id, server_seed, client_seed, nonce FROM fair_seeds")
            for r in cur.fetchall():
                fair_seeds[int(r["user_id"])] = {
                    "server_seed": r["server_seed"],
                    "client_seed": r["client_seed"],
                    "nonce": int(r["nonce"] or 0),
                }
            cur.execute("SELECT seed_hash, server_seed FROM fair_revealed_seeds")
            for r in cur.fetchall():
                revealed_server_seeds[r["seed_hash"]] = r["server_seed"]
    except Exception as e:
        print(f"DB load_fair error: {e}")
    finally:
        conn.close()

def persist_fair_seed(uid):
    st = fair_seeds.get(uid)
    conn = get_db_connection()
    if not conn or not st:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO fair_seeds (user_id, server_seed, client_seed, nonce) VALUES (%s, %s, %s, %s)
                    ON CONFLICT (user_id) DO UPDATE SET server_seed = EXCLUDED.server_seed,
                        client_seed = EXCLUDED.client_seed, nonce = EXCLUDED.nonce
                    """,
                    (uid, st["server_seed"], st["client_seed"], st["nonce"])
                )
    except Exception as e:
        print(f"DB persist_fair_seed error ({uid}): {e}")
    finally:
        conn.close()

def persist_revealed_seed(seed_hash, server_seed, uid):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    "INSERT INTO fair_revealed_seeds (seed_hash, server_seed, user_id) VALUES (%s, %s, %s) ON CONFLICT (seed_hash) DO NOTHING",
                    (seed_hash, server_seed, uid)
                )
    except Exception as e:
        print(f"DB persist_revealed_seed error: {e}")
    finally:
        conn.close()

def fair_get_state(uid):
    st = fair_seeds.get(uid)
    if not st:
        st = {"server_seed": _pf_secrets.token_hex(32), "client_seed": _pf_secrets.token_hex(10), "nonce": 0}
        fair_seeds[uid] = st
        persist_fair_seed(uid)
    return st

def fair_take_seeds(uid):
    """Seeds for the next bet. The server seed is used for this ONE bet only:
    a fresh one is prepared right away for the next bet, so revealing this
    seed after the game can never help predict another game."""
    st = fair_get_state(uid)
    seeds = {"server_seed": st["server_seed"], "client_seed": st["client_seed"], "nonce": st["nonce"]}
    st["nonce"] += 1
    st["server_seed"] = _pf_secrets.token_hex(32)
    persist_fair_seed(uid)
    return seeds

def fair_reveal(seeds, uid):
    """Game is over -> publish its server seed so anyone can verify it."""
    seed_hash = pf_sha256(seeds["server_seed"])
    if revealed_server_seeds.get(seed_hash) != seeds["server_seed"]:
        revealed_server_seeds[seed_hash] = seeds["server_seed"]
        persist_revealed_seed(seed_hash, seeds["server_seed"], uid)

def fair_meta(seeds):
    return {"server_seed_hash": pf_sha256(seeds["server_seed"]), "client_seed": seeds["client_seed"], "nonce": seeds["nonce"]}

def fair_rotate(uid, new_client_seed=None):
    st = fair_get_state(uid)
    old_seed = st["server_seed"]
    old_hash = pf_sha256(old_seed)
    revealed_server_seeds[old_hash] = old_seed
    persist_revealed_seed(old_hash, old_seed, uid)
    st["server_seed"] = _pf_secrets.token_hex(32)
    st["client_seed"] = new_client_seed or _pf_secrets.token_hex(10)
    st["nonce"] = 0
    persist_fair_seed(uid)
    return old_seed, old_hash

def fair_link(seeds, kind=None, gid=None, reveal=False, **extra):
    """Browser link that shows the fairness details of this bet (needs VERIFY_URL).
    reveal=True only after the game is over: adds the real server seed."""
    if not VERIFY_URL:
        return None
    params = {}
    if kind:
        params["game"] = kind
    if gid:
        params["id"] = gid
    params["hash"] = pf_sha256(seeds["server_seed"])
    params["client"] = seeds["client_seed"]
    params["nonce"] = seeds["nonce"]
    if reveal:
        params["server"] = seeds["server_seed"]
    for k, v in extra.items():
        if v is not None:
            params[k] = v
    return f"{VERIFY_URL.rstrip('/')}/?{_pf_urlencode(params)}"

def fair_footer(seeds, kind=None, gid=None, reveal=False, **extra):
    link = fair_link(seeds, kind, gid, reveal, **extra)
    if not link:
        return f"\n\n🔐 _Provably Fair_ · Nonce `{seeds['nonce']}` · /fair"
    return f"\n\n🔐 [Provably Fair]({link})"

def build_fair_text(uid):
    st = fair_get_state(uid)
    return (
        "🔐 *Provably Fair*\n\n"
        f"🔒 Next Server Seed (hashed):\n`{pf_sha256(st['server_seed'])}`\n\n"
        f"👤 Client Seed: `{st['client_seed']}`\n"
        f"🔢 Nonce (next bet): `{st['nonce']}`\n\n"
        "ℹ️ Every Mines, Tower, Limbo and Blackjack bet gets its own server seed. "
        "It is revealed automatically when the game ends — just tap *Provably Fair* on the result message.\n"
        "✏️ Set your own client seed: `/setseed yourtext`"
    )

def fair_keyboard():
    return {"inline_keyboard": [[{"text": "🔄 Change Seed (reveal)", "callback_data": "pf_rotate"}]]}

def clean_client_seed(raw):
    cleaned = re.sub(r"[^A-Za-z0-9\-]", "", raw or "")[:32]
    return cleaned or None

def has_open_fair_game(uid):
    return uid in active_mines_games or uid in active_tower_games or uid in active_bj_games


# ---------------- shared bet helpers ----------------
def fair_validate_bet(chat_id, user_id, bet_inr, example):
    if is_player_in_active_game(user_id):
        send_message(chat_id, f"⚠️ You already have an active game (*{get_active_game_summary(user_id)}*)! Finish it before starting a new game.")
        return False
    if bet_inr is None or bet_inr <= 0:
        send_message(chat_id, f"⚠️ Enter a valid bet amount. Example: `{example}`")
        return False
    if bet_inr < MIN_BET or bet_inr > MAX_BET:
        send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
        return False
    bal = float(user_balances.get(user_id, 0.0))
    if bal < bet_inr:
        send_message(chat_id, f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*")
        return False
    return True

def fair_settle(user_id, game_key, game_label, emoji, title, bet, mult, won, gid, outcome_meta):
    """won=True pays bet*mult. Returns (win_amt, profit)."""
    global HOUSE_BALANCE
    if won:
        win_amt = bet * mult
        profit = win_amt - bet
        user_balances[user_id] = float(user_balances.get(user_id, 0.0)) + win_amt
        HOUSE_BALANCE -= profit
        persist_user(user_id)
        save_config_value("house_balance", HOUSE_BALANCE)
        update_user_stats(user_id, game_key, bet, profit, profit > 0)
        record_user_bet(user_id, game_label, bet, profit, "WON", game_id=gid)
        if profit > 0:
            log_win_to_channel(user_id, emoji, title, win_amt, fmt_mult(mult))
    else:
        win_amt = 0.0
        profit = -bet
        HOUSE_BALANCE += bet
        save_config_value("house_balance", HOUSE_BALANCE)
        update_user_stats(user_id, game_key, bet, profit, False)
        record_user_bet(user_id, game_label, bet, profit, "LOST", game_id=gid)
    mark_game_finished(gid, "completed", extra_meta=dict(outcome_meta, outcome="WON" if won else "LOST", pnl=profit))
    return win_amt, profit


def signed_money(amount_in_inr, user_id):
    if amount_in_inr < 0:
        return "-" + format_money(-amount_in_inr, user_id)
    return format_money(amount_in_inr, user_id)

def fair_result_text(title, bet, mult, win_amt, user_id):
    return (
        f"{title}\n\n"
        f"Profit: *{signed_money(win_amt - bet, user_id)}*\n"
        f"Multiplier: *{fmt_mult(mult)}*\n"
        f"Bet: {format_money(bet, user_id)}\n"
        f"Payout: *{format_money(win_amt, user_id)}*"
    )


# ---------------- LIMBO ----------------
def run_limbo_game(chat_id, user_id, bet_inr, target, reply_to_message_id=None):
    if not fair_validate_bet(chat_id, user_id, bet_inr, "/limbo 50 2"):
        return
    gid = generate_game_id()
    user_balances[user_id] = float(user_balances.get(user_id, 0.0)) - bet_inr
    persist_user(user_id)
    seeds = fair_take_seeds(user_id)
    meta = dict(fair_meta(seeds), chat_id=chat_id, target=target)
    register_game_record(gid, "limbo", user_id, bet_inr, meta=meta, refund_on_cancel=False)

    result = pf_limbo_result(seeds)
    won = result >= target
    win_amt, _ = fair_settle(user_id, "limbo", f"Limbo ({target:.2f}x)", "🚀", "Limbo", bet_inr, target, won, gid, {"result": result})

    chance = min(100.0, FAIR_RTP / target * 100)
    fair_reveal(seeds, user_id)
    text_out = (
        f"🚀 *Limbo* (`{gid}`)\n\n"
        f"🎯 Target: *{target:.2f}x* (win chance {chance:.2f}%)\n"
        f"📈 Result: *{result:.2f}x* {'✅' if won else '❌'}\n"
        f"💰 Bet: {format_money(bet_inr, user_id)}"
    ) + fair_footer(seeds, "limbo", gid, reveal=True, target=f"{target:.2f}", result=f"{result:.2f}")
    payload = {"kind": "limbo", "owner_id": user_id, "bet": bet_inr, "target": target}
    sent = send_message(chat_id, text_out, reply_markup=create_post_match_keyboard(user_id, payload), reply_to_message_id=reply_to_message_id)
    remember_button_owner(chat_id, sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None, user_id)


# ---------------- MINES ----------------
def mines_keyboard(game):
    rows = []
    for r in range(5):
        row = []
        for c in range(5):
            idx = r * 5 + c
            if idx in game["revealed"]:
                row.append({"text": "💎", "callback_data": "mn_x"})
            else:
                row.append({"text": "🟦", "callback_data": f"mn_t_{idx}"})
        rows.append(row)
    picks = len(game["revealed"])
    ctrl = [{"text": "🎲 Random", "callback_data": "mn_rand"}]
    if picks > 0:
        mult = pf_mines_multiplier(game["mines"], picks)
        ctrl.append({"text": f"💰 Cashout {fmt_mult(mult)}", "callback_data": "mn_cash"})
    rows.append(ctrl)
    return {"inline_keyboard": rows}

def mines_status_text(game, user_id):
    picks = len(game["revealed"])
    cur = pf_mines_multiplier(game["mines"], picks)
    nxt = pf_mines_multiplier(game["mines"], picks + 1) if picks < MINES_TILES - game["mines"] else cur
    return (
        f"💣 *Mines* (`{game['game_id']}`)\n\n"
        f"💣 Mines: *{game['mines']}* | 💎 Found: *{picks}*\n"
        f"💰 Bet: {format_money(game['bet'], user_id)}\n"
        f"📈 Current: *{fmt_mult(cur)}* → Next: *{fmt_mult(nxt)}*\n\n"
        "Pick a tile:" + fair_footer(game["seeds"], "mines", game["game_id"], mines=game["mines"])
    )

def mines_final_grid(game, hit_idx=None):
    lines = []
    for r in range(5):
        cells = []
        for c in range(5):
            idx = r * 5 + c
            if idx == hit_idx:
                cells.append("💥")
            elif idx in game["layout"]:
                cells.append("💣")
            elif idx in game["revealed"]:
                cells.append("💎")
            else:
                cells.append("▫️")
        lines.append("".join(cells))
    return "\n".join(lines)

def start_mines_game(chat_id, user_id, bet_inr, mines, reply_to_message_id=None):
    if not fair_validate_bet(chat_id, user_id, bet_inr, "/mines 50 3"):
        return
    gid = generate_game_id()
    user_balances[user_id] = float(user_balances.get(user_id, 0.0)) - bet_inr
    persist_user(user_id)
    seeds = fair_take_seeds(user_id)
    register_game_record(gid, "mines", user_id, bet_inr, meta=dict(fair_meta(seeds), chat_id=chat_id, mines=mines), refund_on_cancel=True)
    game = {
        "game_id": gid, "chat_id": chat_id, "message_id": None, "bet": bet_inr,
        "mines": mines, "seeds": seeds, "layout": set(pf_mines_layout(seeds, mines)), "revealed": [],
    }
    active_mines_games[user_id] = game
    sent = send_message(chat_id, mines_status_text(game, user_id), reply_markup=mines_keyboard(game), reply_to_message_id=reply_to_message_id)
    msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
    game["message_id"] = msg_id
    remember_button_owner(chat_id, msg_id, user_id)

def mines_result_rows(game, hit_idx=None):
    """Final board as buttons: 💣 = mine, 💎 = safe, red = the mine you hit, green = your picks."""
    rows = []
    for r in range(5):
        row = []
        for c in range(5):
            idx = r * 5 + c
            btn = {"text": "💣" if idx in game["layout"] else "💎", "callback_data": "mn_done"}
            if idx == hit_idx:
                btn["style"] = "danger"
            elif idx in game["revealed"]:
                btn["style"] = "success"
            row.append(btn)
        rows.append(row)
    return rows

def finish_mines_game(user_id, game, won, hit_idx=None):
    active_mines_games.pop(user_id, None)
    picks = len(game["revealed"])
    mult = pf_mines_multiplier(game["mines"], picks) if won else 0.0
    win_amt, _ = fair_settle(user_id, "mines", f"Mines ({game['mines']}💣)", "💣", "Mines", game["bet"], mult, won,
                             game["game_id"], {"picks": picks, "revealed": list(game["revealed"])})
    fair_reveal(game["seeds"], user_id)
    text_out = fair_result_text("*Mines* 💣", game["bet"], mult, win_amt, user_id) + fair_footer(
        game["seeds"], "mines", game["game_id"], reveal=True, mines=game["mines"],
        picks=",".join(str(i) for i in game["revealed"]) or None,
        hit=hit_idx)
    grid = mines_result_rows(game, hit_idx)
    payload = {"kind": "mines", "owner_id": user_id, "bet": game["bet"], "mines": game["mines"], "result_grid": grid}
    post_kb = create_post_match_keyboard(user_id, payload)
    edit_message(game["chat_id"], game["message_id"], text_out,
                 reply_markup={"inline_keyboard": grid + post_kb["inline_keyboard"]})

def handle_mines_callback(user_id, chat_id, message_id, data):
    game = active_mines_games.get(user_id)
    if not game:
        if data != "mn_x":
            edit_message(chat_id, message_id, "⚠️ Mines session expired. Start a new game with `/mines <amount> <mines>`.")
        return
    if game.get("message_id") is None:
        game["message_id"] = message_id
    if data == "mn_x":
        return
    if data == "mn_cash":
        if game["revealed"]:
            finish_mines_game(user_id, game, True)
        return
    if data == "mn_rand":
        hidden = [i for i in range(MINES_TILES) if i not in game["revealed"]]
        idx = _pf_secrets.choice(hidden)
    else:
        try:
            idx = int(data.replace("mn_t_", "", 1))
        except ValueError:
            return
        if idx < 0 or idx >= MINES_TILES or idx in game["revealed"]:
            return
    if idx in game["layout"]:
        finish_mines_game(user_id, game, False, hit_idx=idx)
        return
    game["revealed"].append(idx)
    if len(game["revealed"]) >= MINES_TILES - game["mines"]:
        finish_mines_game(user_id, game, True)
        return
    edit_message(game["chat_id"], game["message_id"], mines_status_text(game, user_id), reply_markup=mines_keyboard(game))


# ---------------- TOWER ----------------
def tower_keyboard(game):
    cfg = TOWER_DIFFICULTIES[game["difficulty"]]
    level = len(game["picks"])
    rows = []
    for lvl in range(TOWER_LEVELS - 1, -1, -1):
        row = []
        for c in range(cfg["cols"]):
            if lvl < level:
                txt = "✅" if game["picks"][lvl] == c else "⬛"
                row.append({"text": txt, "callback_data": "tw_x"})
            elif lvl == level:
                row.append({"text": f"❓ {fmt_mult(pf_tower_multiplier(game['difficulty'], lvl + 1))}", "callback_data": f"tw_p_{c}"})
            else:
                row.append({"text": "⬛", "callback_data": "tw_x"})
        rows.append(row)
    ctrl = [{"text": "🎲 Random", "callback_data": "tw_rand"}]
    if level > 0:
        ctrl.append({"text": f"💰 Cashout {fmt_mult(pf_tower_multiplier(game['difficulty'], level))}", "callback_data": "tw_cash"})
    rows.append(ctrl)
    return {"inline_keyboard": rows}

def tower_status_text(game, user_id):
    level = len(game["picks"])
    cfg = TOWER_DIFFICULTIES[game["difficulty"]]
    return (
        f"🗼 *Tower* (`{game['game_id']}`)\n\n"
        f"⚙️ Mode: *{game['difficulty'].title()}* ({cfg['cols']} tiles, {cfg['bombs']} 💀 per row)\n"
        f"🪜 Level: *{level}/{TOWER_LEVELS}*\n"
        f"💰 Bet: {format_money(game['bet'], user_id)}\n"
        f"📈 Current: *{fmt_mult(pf_tower_multiplier(game['difficulty'], level))}*\n\n"
        "Climb! Pick a tile on the ❓ row:" + fair_footer(game["seeds"], "tower", game["game_id"], difficulty=game["difficulty"])
    )

def tower_final_grid(game, hit=None):
    cfg = TOWER_DIFFICULTIES[game["difficulty"]]
    lines = []
    for lvl in range(TOWER_LEVELS - 1, -1, -1):
        cells = []
        for c in range(cfg["cols"]):
            if hit == (lvl, c):
                cells.append("💥")
            elif c in game["layout"][lvl]:
                cells.append("💀")
            elif lvl < len(game["picks"]) and game["picks"][lvl] == c:
                cells.append("✅")
            else:
                cells.append("🟩")
        lines.append("".join(cells))
    return "\n".join(lines)

def start_tower_game(chat_id, user_id, bet_inr, difficulty, reply_to_message_id=None):
    if not fair_validate_bet(chat_id, user_id, bet_inr, "/tower 50 easy"):
        return
    gid = generate_game_id()
    user_balances[user_id] = float(user_balances.get(user_id, 0.0)) - bet_inr
    persist_user(user_id)
    seeds = fair_take_seeds(user_id)
    register_game_record(gid, "tower", user_id, bet_inr, meta=dict(fair_meta(seeds), chat_id=chat_id, difficulty=difficulty), refund_on_cancel=True)
    game = {
        "game_id": gid, "chat_id": chat_id, "message_id": None, "bet": bet_inr,
        "difficulty": difficulty, "seeds": seeds, "layout": pf_tower_layout(seeds, difficulty), "picks": [],
    }
    active_tower_games[user_id] = game
    sent = send_message(chat_id, tower_status_text(game, user_id), reply_markup=tower_keyboard(game), reply_to_message_id=reply_to_message_id)
    msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
    game["message_id"] = msg_id
    remember_button_owner(chat_id, msg_id, user_id)

def tower_result_rows(game, hit=None):
    """Final tower as buttons: 🐍 = skull tile, 🥚 = safe tile, red = the tile that was hit, green = your picks."""
    cfg = TOWER_DIFFICULTIES[game["difficulty"]]
    picks = game["picks"]
    rows = []
    for lvl in range(TOWER_LEVELS - 1, -1, -1):
        row = []
        for c in range(cfg["cols"]):
            btn = {"text": "🐍" if c in game["layout"][lvl] else "🥚", "callback_data": "tw_done"}
            if hit == (lvl, c):
                btn["style"] = "danger"
            elif lvl < len(picks) and picks[lvl] == c:
                btn["style"] = "success"
            row.append(btn)
        rows.append(row)
    return rows

def finish_tower_game(user_id, game, won, hit=None):
    active_tower_games.pop(user_id, None)
    level = len(game["picks"])
    mult = pf_tower_multiplier(game["difficulty"], level) if won else 0.0
    win_amt, _ = fair_settle(user_id, "tower", f"Tower ({game['difficulty'].title()})", "🗼", "Tower", game["bet"], mult, won,
                             game["game_id"], {"levels": level, "picks": list(game["picks"])})
    fair_reveal(game["seeds"], user_id)
    text_out = fair_result_text("*Tower* 🗼", game["bet"], mult, win_amt, user_id)
    text_out += fair_footer(game["seeds"], "tower", game["game_id"], reveal=True, difficulty=game["difficulty"],
                            picks=",".join(str(c) for c in game["picks"]) or None,
                            hit=hit[1] if hit else None)
    grid = tower_result_rows(game, hit)
    payload = {"kind": "tower", "owner_id": user_id, "bet": game["bet"], "difficulty": game["difficulty"], "result_grid": grid}
    post_kb = create_post_match_keyboard(user_id, payload)
    edit_message(game["chat_id"], game["message_id"], text_out,
                 reply_markup={"inline_keyboard": grid + post_kb["inline_keyboard"]})

def handle_tower_callback(user_id, chat_id, message_id, data):
    game = active_tower_games.get(user_id)
    if not game:
        if data != "tw_x":
            edit_message(chat_id, message_id, "⚠️ Tower session expired. Start a new game with `/tower <amount> <mode>`.")
        return
    if game.get("message_id") is None:
        game["message_id"] = message_id
    if data == "tw_x":
        return
    level = len(game["picks"])
    if data == "tw_cash":
        if level > 0:
            finish_tower_game(user_id, game, True)
        return
    cols = TOWER_DIFFICULTIES[game["difficulty"]]["cols"]
    if data == "tw_rand":
        col = _pf_secrets.randbelow(cols)
    else:
        try:
            col = int(data.replace("tw_p_", "", 1))
        except ValueError:
            return
        if col < 0 or col >= cols:
            return
    if col in game["layout"][level]:
        finish_tower_game(user_id, game, False, hit=(level, col))
        return
    game["picks"].append(col)
    if len(game["picks"]) >= TOWER_LEVELS:
        finish_tower_game(user_id, game, True)
        return
    edit_message(game["chat_id"], game["message_id"], tower_status_text(game, user_id), reply_markup=tower_keyboard(game))


# ---------------- VERIFY ----------------
def build_verify_text(gid):
    gid = gid.strip().upper()
    rec = game_id_registry.get(gid)
    if not rec or rec.get("kind") not in ("mines", "tower", "limbo"):
        return f"⚠️ No Mines / Tower / Limbo game found with ID `{gid}`."
    meta = rec.get("meta", {})
    seed_hash = meta.get("server_seed_hash")
    server_seed = revealed_server_seeds.get(seed_hash)
    head = (
        f"🔍 *Verify* `{gid}` ({rec['kind'].title()})\n\n"
        f"🔒 Server Seed Hash: `{seed_hash}`\n"
        f"👤 Client Seed: `{meta.get('client_seed')}`\n"
        f"🔢 Nonce: `{meta.get('nonce')}`\n"
    )
    if not server_seed:
        return head + "\n⏳ This game is still running. The server seed is revealed automatically when it ends."
    seeds = {"server_seed": server_seed, "client_seed": meta.get("client_seed"), "nonce": int(meta.get("nonce", 0))}
    head += f"🔓 Server Seed: `{server_seed}`\n✅ Hash matches: *{'YES' if pf_sha256(server_seed) == seed_hash else 'NO'}*\n\n"
    link_params = f"server={server_seed}&client={seeds['client_seed']}&nonce={seeds['nonce']}"
    if rec["kind"] == "limbo":
        res = pf_limbo_result(seeds)
        head += f"🚀 Limbo result: *{res:.2f}x* (target {float(meta.get('target', 0)):.2f}x)"
        link_params = f"game=limbo&{link_params}"
    elif rec["kind"] == "mines":
        m = int(meta.get("mines", MINES_DEFAULT))
        layout = sorted(t + 1 for t in pf_mines_layout(seeds, m))
        head += f"💣 Mine tiles (1-25, left→right, top→bottom): `{', '.join(map(str, layout))}`"
        link_params = f"game=mines&mines={m}&{link_params}"
    else:
        d = meta.get("difficulty", "easy")
        layout = pf_tower_layout(seeds, d)
        rows = " | ".join(f"L{i + 1}:{'/'.join(str(c + 1) for c in row)}" for i, row in enumerate(layout))
        head += f"💀 Skull tiles per level (bottom→top): `{rows}`"
        link_params = f"game=tower&difficulty={d}&{link_params}"
    if VERIFY_URL:
        head += f"\n\n🌐 Check online: {VERIFY_URL.rstrip('/')}/?{link_params}"
    return head


# ---------------- COMMAND + CALLBACK ROUTERS ----------------
FAIR_CMD_RE = rf"^/(mines|tower|limbo|fair|setseed|verify)(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)"

def handle_fair_command(chat_id, chat_type, user_id, text, message):
    m = re.match(FAIR_CMD_RE, text, re.IGNORECASE)
    cmd = m.group(1).lower()
    parts = text.split()
    reply_to = message.get("message_id") if chat_type in ["group", "supergroup"] else None

    if cmd == "fair":
        sent = send_message(chat_id, build_fair_text(user_id), reply_markup=fair_keyboard())
        remember_button_owner(chat_id, sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None, user_id)
        return

    if cmd == "setseed":
        new_seed = clean_client_seed(parts[1]) if len(parts) > 1 else None
        if not new_seed:
            send_message(chat_id, "⚠️ Usage: `/setseed yourtext` (letters, numbers, - only, max 32)")
            return
        if has_open_fair_game(user_id):
            send_message(chat_id, "⚠️ Finish your Mines / Tower / Blackjack game before changing seeds.")
            return
        old_seed, old_hash = fair_rotate(user_id, new_seed)
        send_message(chat_id, f"✅ Client seed set to `{new_seed}`.\n\n🔓 Previous server seed revealed:\n`{old_seed}`\n\n" + build_fair_text(user_id))
        return

    if cmd == "verify":
        if len(parts) < 2:
            send_message(chat_id, "⚠️ Usage: `/verify XC-XXXXXXX-XXXX`")
            return
        send_message(chat_id, build_verify_text(parts[1]))
        return

    bet_inr = parse_user_amount(parts[1], user_id) if len(parts) > 1 else parse_user_amount("10", user_id)

    if cmd == "limbo":
        try:
            target = float(parts[2].lower().rstrip("x")) if len(parts) > 2 else 2.0
        except ValueError:
            target = None
        if target is None or target < LIMBO_MIN_TARGET or target > LIMBO_MAX_TARGET:
            send_message(chat_id, f"⚠️ Target must be {LIMBO_MIN_TARGET:.2f}x – {LIMBO_MAX_TARGET:.0f}x. Example: `/limbo 50 2`")
            return
        run_limbo_game(chat_id, user_id, bet_inr, round(target, 2), reply_to_message_id=reply_to)
    elif cmd == "mines":
        try:
            mines = int(parts[2]) if len(parts) > 2 else MINES_DEFAULT
        except ValueError:
            mines = None
        if mines is None or mines < 1 or mines > 24:
            send_message(chat_id, "⚠️ Mines must be 1–24. Example: `/mines 50 3`")
            return
        start_mines_game(chat_id, user_id, bet_inr, mines, reply_to_message_id=reply_to)
    elif cmd == "tower":
        diff = parts[2].lower() if len(parts) > 2 else "easy"
        if diff not in TOWER_DIFFICULTIES:
            send_message(chat_id, "⚠️ Mode must be `easy`, `medium`, `hard`, `expert` or `master`. Example: `/tower 50 easy`")
            return
        start_tower_game(chat_id, user_id, bet_inr, diff, reply_to_message_id=reply_to)

def handle_fair_callback(chat_id, message_id, user_id, data):
    with get_turn_lock(f"fair_{user_id}"):
        if data in ("tw_done", "mn_done"):
            return
        if data.startswith("mn_"):
            handle_mines_callback(user_id, chat_id, message_id, data)
        elif data.startswith("tw_"):
            handle_tower_callback(user_id, chat_id, message_id, data)
        elif data == "pf_rotate":
            if has_open_fair_game(user_id):
                send_message(chat_id, "⚠️ Finish your Mines / Tower / Blackjack game before changing seeds.")
                return
            old_seed, _ = fair_rotate(user_id)
            edit_message(chat_id, message_id, f"🔓 *Previous server seed revealed:*\n`{old_seed}`\n\n" + build_fair_text(user_id), reply_markup=fair_keyboard())

def restart_fair_game(chat_id, user_id, payload, next_bet):
    kind = payload.get("kind")
    if kind == "limbo":
        run_limbo_game(chat_id, user_id, next_bet, float(payload.get("target", 2.0)))
    elif kind == "mines":
        start_mines_game(chat_id, user_id, next_bet, int(payload.get("mines", MINES_DEFAULT)))
    elif kind == "tower":
        start_tower_game(chat_id, user_id, next_bet, payload.get("difficulty", "easy"))
# ---------------- BLACKJACK (provably fair deck) ----------------
def pf_bj_cards(seeds, count):
    """Card i of the hand = float i of the bet: 0..51 -> rank (i % 13) + suit (i // 13).
    Deal order: you, you, dealer, dealer, then your hits, then the dealer's draws."""
    floats = pf_floats(seeds["server_seed"], seeds["client_seed"], seeds["nonce"], count)
    cards = []
    for f in floats:
        idx = int(_pf_math.floor(f * 52))
        cards.append(f"{DECK_RANKS[idx % 13]}{DECK_SUITS[idx // 13]}")
    return cards

def bj_draw(bj):
    seeds = bj.get("seeds")
    if not seeds:
        return draw_card()
    pos = bj.get("drawn", 0)
    bj["drawn"] = pos + 1
    return pf_bj_cards(seeds, pos + 1)[pos]

def bj_fair_footer(bj, reveal=False):
    seeds = bj.get("seeds")
    if not seeds:
        return ""
    extra = {}
    if reveal:
        extra = {"pc": len(bj["player_cards"]), "dc": len(bj["dealer_cards"])}
    return fair_footer(seeds, "bj", bj.get("game_id"), reveal=reveal, **extra)

def start_bj_game(chat_id, user_id, bet_inr):
    gid = generate_game_id()
    user_balances[user_id] = float(user_balances.get(user_id, 0.0)) - bet_inr
    persist_user(user_id)
    seeds = fair_take_seeds(user_id)
    register_game_record(gid, "blackjack", user_id, bet_inr, meta=dict(fair_meta(seeds), chat_id=chat_id), refund_on_cancel=True)
    bj = {
        "game_id": gid,
        "chat_id": chat_id,
        "message_id": None,
        "bet": bet_inr,
        "seeds": seeds,
        "drawn": 0,
        "player_cards": [],
        "dealer_cards": [],
        "doubled": False,
    }
    bj["player_cards"] = [bj_draw(bj), bj_draw(bj)]
    bj["dealer_cards"] = [bj_draw(bj), bj_draw(bj)]
    p_tot = calculate_hand_total(bj["player_cards"])
    can_double = float(user_balances.get(user_id, 0.0)) >= bet_inr
    table_msg = (
        f"🃏 *Blackjack Started!* (`{gid}`)\n\n"
        f"👤 Your Hand: {format_cards(bj['player_cards'])} (*{p_tot}*)\n"
        f"🤖 Dealer Shows: `{bj['dealer_cards'][0]}` `[?]`\n"
        f"💰 Bet: {format_money(bet_inr, user_id)}\n\n"
        f"Choose your move:" + bj_fair_footer(bj)
    )
    active_bj_games[user_id] = bj
    sent = send_message(chat_id, table_msg, reply_markup=bj_action_keyboard(can_double=can_double))
    msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
    bj["message_id"] = msg_id
    remember_button_owner(chat_id, msg_id, user_id)

# ===================== END PROVABLY FAIR GAMES =====================


@app.route('/')
def index():
    return f"{BOT_USERNAME} Casino Bot is Live!", 200

@app.route('/webhook', methods=['POST'])
def telegram_webhook():
    global HOUSE_BALANCE, MIN_BET, MAX_BET, EXCHANGE_RATE, MAINTENANCE_MODE, DEPOSIT_ENABLED, WITHDRAW_ENABLED, DM_GAMES_ENABLED, GROUP_LINK
    try:
        data = request.get_json()
        if not data:
            return jsonify({'status': 'error'}), 400
            
        if 'message' in data:
            message = data['message']
            chat_id = message['chat'].get('id')
            chat_type = message['chat'].get('type')
            user_id = message['from'].get('id')

            if message['from'].get('is_bot') and user_id in helper_ids():
                return jsonify({'status': 'ok'}), 200

            if 'reply_to_message' in message and message['reply_to_message'].get('from'):
                register_user_identity(message['reply_to_message']['from'])
            
            if chat_type in ['group', 'supergroup'] and not is_group_approved(chat_id) and user_id not in admin_list:
                if 'text' in message and message['text'].startswith('/myid'):
                    send_message(chat_id, f"📌 This Group Chat ID is: `{chat_id}`")
                return jsonify({'status': 'ok'}), 200

            if user_id in banned_users:
                send_message(chat_id, "⛔ Your account has been banned from using this bot.")
                return jsonify({'status': 'ok'}), 200
                
            if MAINTENANCE_MODE and user_id not in admin_list:
                send_message(chat_id, "🛠 *Bot is under Maintenance.* Please try again later.")
                return jsonify({'status': 'ok'}), 200
                
            register_user_identity(message.get('from'))
                
            if user_id in admin_list and user_id in admin_states and 'text' in message:
                state = admin_states[user_id]
                text = message['text'].strip()
                action = state['action']
                
                if action == 'add_bal':
                    try:
                        parts = text.split(' ')
                        t_user = resolve_user_identifier(parts[0])
                        if t_user is None:
                            raise ValueError()
                        amt = parse_user_amount(parts[1], t_user)
                        if amt is None or amt <= 0:
                            raise ValueError()
                        if t_user not in user_balances: user_balances[t_user] = 0.0
                        user_balances[t_user] += amt
                        persist_user(t_user)
                        send_message(chat_id, f"✅ Added {format_money(amt, t_user)} to user `{t_user}`.")
                        send_message(t_user, f"💰 *Admin credited your account!* +{format_money(amt, t_user)}")
                    except:
                        send_message(chat_id, "⚠️ Invalid format. Use: `<user_id/@username> <amount>`")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'deduct_bal':
                    try:
                        parts = text.split(' ')
                        t_user = resolve_user_identifier(parts[0])
                        if t_user is None:
                            raise ValueError()
                        amt = parse_user_amount(parts[1], t_user)
                        if amt is None or amt <= 0:
                            raise ValueError()
                        if t_user in user_balances:
                            user_balances[t_user] = max(0.0, user_balances[t_user] - amt)
                            persist_user(t_user)
                            send_message(chat_id, f"✅ Deducted {format_money(amt, t_user)} from user `{t_user}`.")
                            send_message(t_user, f"⚠️ *Admin deducted from your account.* -{format_money(amt, t_user)}")
                    except:
                        send_message(chat_id, "⚠️ Invalid format. Use: `<user_id/@username> <amount>`")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'user_stats':
                    try:
                        target_u = resolve_user_identifier(text)
                        if target_u is None:
                            raise ValueError()
                        bio = generate_stats_image(target_u)
                        send_photo(chat_id, bio, caption=f"📊 Stats for User `{target_u}`")
                    except:
                        send_message(chat_id, "⚠️ Invalid User ID or Username.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'ban_user':
                    try:
                        target_u = resolve_user_identifier(text)
                        if target_u is None:
                            raise ValueError()
                        banned_users.add(target_u)
                        persist_user(target_u)
                        send_message(chat_id, f"🚫 User `{target_u}` has been BANNED.")
                    except:
                        send_message(chat_id, "⚠️ Invalid User ID or Username.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'unban_user':
                    try:
                        target_u = resolve_user_identifier(text)
                        if target_u is None:
                            raise ValueError()
                        if target_u in banned_users: banned_users.remove(target_u)
                        persist_user(target_u)
                        send_message(chat_id, f"✅ User `{target_u}` has been UNBANNED.")
                    except:
                        send_message(chat_id, "⚠️ Invalid User ID or Username.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'grant_admin':
                    try:
                        target_u = resolve_user_identifier(text)
                        if target_u is None:
                            raise ValueError()
                        admin_list.add(target_u)
                        persist_user(target_u)
                        send_message(chat_id, f"👑 User `{target_u}` granted Admin rights.")
                    except:
                        send_message(chat_id, "⚠️ Invalid User ID or Username.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'revoke_admin':
                    try:
                        target_u = resolve_user_identifier(text)
                        if target_u is None:
                            raise ValueError()
                        if target_u != ADMIN_USER_ID and target_u in admin_list:
                            admin_list.remove(target_u)
                            send_message(chat_id, f"⛔ Admin rights revoked for `{target_u}`.")
                    except:
                        send_message(chat_id, "⚠️ Invalid User ID or Username.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'broadcast_all':
                    count = 0
                    for u in list(user_balances.keys()):
                        send_message(u, f"📢 *Announcement*\n\n{text}")
                        count += 1
                    send_message(chat_id, f"✅ Broadcast sent to {count} users.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'broadcast_private':
                    try:
                        parts = text.split(' ', 1)
                        target_u = resolve_user_identifier(parts[0])
                        if target_u is None:
                            raise ValueError()
                        msg = parts[1]
                        send_message(target_u, f"📢 *Admin Message*\n\n{msg}")
                        send_message(chat_id, f"✅ Private message sent to `{target_u}`.")
                    except:
                        send_message(chat_id, "⚠️ Format error. Use: `<user_id/@username> <message>`")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200

            if user_id in deposit_states and 'text' in message:
                text = message['text'].strip()
                if chat_type != 'private':
                    del deposit_states[user_id]
                    send_message(chat_id, "❌ Deposit can only be done in Bot's DM (Private Chat)!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                    return jsonify({'status': 'ok'}), 200

                if text.startswith('/'):  
                    del deposit_states[user_id]
                else:
                    del deposit_states[user_id]
                    if not DEPOSIT_ENABLED:
                        send_message(chat_id, "❌ Deposits are currently disabled by Admin.")
                        return jsonify({'status': 'ok'}), 200
                    amt_inr = parse_user_amount(text, user_id)
                    if amt_inr and amt_inr > 0:
                        send_message(chat_id, "⏳ Generating deposit link...")
                        res_text, pay_kb = create_zapupi_order(amt_inr, user_id)
                        send_message(chat_id, res_text, reply_markup=pay_kb)
                    else:
                        send_message(chat_id, "⚠️ Invalid amount. Use `/deposit <amount>` or `/deposit` again.")
                    return jsonify({'status': 'ok'}), 200

            if user_id in withdrawal_states and 'text' in message:
                state = withdrawal_states[user_id]
                text = message['text'].strip()
                if chat_type != 'private':
                    del withdrawal_states[user_id]
                    send_message(chat_id, "❌ Withdrawal can only be done in Bot's DM (Private Chat)!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                    return jsonify({'status': 'ok'}), 200

                if text.startswith('/'):
                    del withdrawal_states[user_id]
                else:
                    if state['step'] == 'waiting_amount':
                        if not WITHDRAW_ENABLED:
                            send_message(chat_id, "❌ Withdrawals are currently disabled by Admin.")
                            del withdrawal_states[user_id]
                            return jsonify({'status': 'ok'}), 200
                        amt_inr = parse_user_amount(text, user_id)
                        if not amt_inr or amt_inr <= 0:
                            send_message(chat_id, "⚠️ Invalid amount. Please enter a valid number:")
                            return jsonify({'status': 'ok'}), 200
                        if user_balances.get(user_id, 0.0) < amt_inr:
                            send_message(chat_id, f"❌ Insufficient balance! Your balance is {format_money(user_balances.get(user_id, 0.0), user_id)}.")
                            del withdrawal_states[user_id]
                            return jsonify({'status': 'ok'}), 200
                            
                        state['amount'] = amt_inr
                        state['step'] = 'waiting_upi'
                        send_message(chat_id, "🏦 *Please enter your UPI ID / Destination Address for payout:*")
                        return jsonify({'status': 'ok'}), 200
                        
                    elif state['step'] == 'waiting_upi':
                        state['upi_id'] = text
                        withdrawal_states[user_id]['step'] = 'confirming'
                        
                        amt_str = format_money(state['amount'], user_id)
                        summary = (
                            "📋 *Withdrawal Summary*\n\n"
                            f"💰 Amount: *{amt_str}*\n"
                            f"🏦 UPI ID: `{state['upi_id']}`\n\n"
                            "Please verify your details below:"
                        )
                        keyboard = {
                            "inline_keyboard": [
                                [
                                    {"text": "✅ Confirm Withdrawal", "callback_data": "wd_confirm"},
                                    {"text": "❌ Cancel", "callback_data": "wd_cancel"}
                                ]
                            ]
                        }
                        send_message(chat_id, summary, reply_markup=keyboard)
                        return jsonify({'status': 'ok'}), 200

            if user_id in admin_list and user_id in withdrawal_states and withdrawal_states[user_id].get('step') == 'waiting_reject_reason' and 'text' in message:
                reason = message['text'].strip()
                target_user = withdrawal_states[user_id]['target_user']
                amt_str = withdrawal_states[user_id]['amount_str']
                
                user_balances[target_user] = user_balances.get(target_user, 0.0) + withdrawal_states[user_id]['raw_amount']
                
                send_message(target_user, f"❌ *Withdrawal Request Rejected*\n\nAmount: {amt_str}\nReason: *{reason}*\n\nYour funds have been refunded to your wallet.")
                send_message(chat_id, f"✅ Rejection sent to user `{target_user}` with reason: _{reason}_")
                del withdrawal_states[user_id]
                return jsonify({'status': 'ok'}), 200

            if 'dice' in message and user_id in active_games:
                active_ref = active_games[user_id]
                user_dice = message['dice']

                if isinstance(active_ref, str) and active_ref in active_pvp_games:
                    with get_turn_lock(f"pvp_{active_ref}"):
                        pvm = active_pvp_games.get(active_ref)
                        if not pvm or pvm["chat_id"] != chat_id or pvm["turn"] != user_id:
                            return jsonify({'status': 'ok'}), 200
                        if user_dice.get('emoji') != pvm["emoji"]:
                            return jsonify({'status': 'ok'}), 200

                        pvm["turn_token"] = None
                        val = user_dice.get('value', 1)
                        needed = pvm["rolls_per_round"]
                        is_p1 = (user_id == pvm["p1_id"])
                        roll_list = pvm["p1_rolls"] if is_p1 else pvm["p2_rolls"]
                        roll_list.append(val)

                        rem = needed - len(roll_list)
                        if rem > 0:
                            send_message(chat_id, f"🎲 {tag_player(user_id)} Roll `{len(roll_list)}/{needed}`: *{val}* — Send `{rem}` more `{pvm['emoji']}`!")
                            schedule_pvp_turn_timeout(chat_id, active_ref, pvm)
                            return jsonify({'status': 'ok'}), 200

                        if is_p1:
                            expr = "+".join(map(str, roll_list))
                            send_message(chat_id, f"👤 {tag_player(pvm['p1_id'])} Rolls: `{expr}` (*{sum(roll_list)}*)\n\n👉 {tag_player(pvm['p2_id'])}, *your turn! Send* `{pvm['emoji']}` *x{needed}.*")
                            pvm["turn"] = pvm["p2_id"]
                            schedule_pvp_turn_timeout(chat_id, active_ref, pvm)
                        else:
                            resolve_pvp_round_and_match(chat_id, active_ref, pvm)
                        return jsonify({'status': 'ok'}), 200

                with get_turn_lock(f"pvb_{user_id}"):
                    game = active_games.get(user_id)
                    if not isinstance(game, dict):
                        return jsonify({'status': 'ok'}), 200
                    expected_emoji = game['emoji']
                    
                    if user_dice.get('emoji') == expected_emoji and game['step'] in ['selecting_turn', 'waiting_user_first', 'waiting_user_second']:
                        game["turn_token"] = None
                        if game['step'] == 'selecting_turn':
                            game['first_turn'] = 'user'
                            game['step'] = 'waiting_user_first'
                            s_chat_id = game.get('start_chat_id') or chat_id
                            s_msg_id = game.get('start_message_id')
                            if s_msg_id:
                                remove_inline_keyboard(s_chat_id, s_msg_id)
                                game['start_message_id'] = None
                        user_val = user_dice.get('value', 1)
                        rolls_needed = game['rolls_per_round']
                        game['current_user_rolls'].append(user_val)
                        
                        remaining = rolls_needed - len(game['current_user_rolls'])
                        if remaining > 0:
                            send_message(chat_id, f"🎲 Roll `{len(game['current_user_rolls'])}/{rolls_needed}`: *{user_val}* — Send `{remaining}` more `{expected_emoji}`!")
                            schedule_pvb_turn_timeout(chat_id, user_id, game)
                            return jsonify({'status': 'ok'}), 200
                            
                        step = game['step']
                        if step == 'waiting_user_first':
                            u_expr = "+".join(map(str, game['current_user_rolls']))
                            player_tag = format_user_mention(user_id)
                            user_roll_msg_id = message.get('message_id')
                            send_message(chat_id, f"👤 {player_tag} Rolls ({expected_emoji}): `{u_expr}` (*{sum(game['current_user_rolls'])}*)\n\n🤖 Now bot is throwing...")
                            time.sleep(0.8)
                            
                            b_vals = roll_bot_series(chat_id, expected_emoji, rolls_needed, reply_to_message_id=user_roll_msg_id)
                            game['current_bot_rolls'] = b_vals
                            
                            resolve_round_and_match(chat_id, user_id, game)
                            return jsonify({'status': 'ok'}), 200
                            
                        elif step == 'waiting_user_second':
                            resolve_round_and_match(chat_id, user_id, game)
                            return jsonify({'status': 'ok'}), 200

            if 'text' in message:
                text = message['text'].strip()

                if re.match(rf"^/helpers?(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        return jsonify({'status': 'ok'}), 200
                    handle_helper_command(chat_id, chat_type, text, message)
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/offgame(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    DM_GAMES_ENABLED = False
                    save_config_value("dm_games_enabled", DM_GAMES_ENABLED)
                    send_message(chat_id, "🔴 *Games in Bot DM are now OFF.*\nPlayers will be asked to play in the group.")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/ongame(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    DM_GAMES_ENABLED = True
                    save_config_value("dm_games_enabled", DM_GAMES_ENABLED)
                    send_message(chat_id, "🟢 *Games in Bot DM are now ON.*")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/setgc(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split(maxsplit=1)
                    if len(parts) < 2 or not parts[1].strip():
                        current = GROUP_LINK if GROUP_LINK else "Not set"
                        current = current.replace('_', '\\_')
                        send_message(chat_id, f"🔗 Current Group Link: {current}\nUsage: `/setgc @grouplink`")
                        return jsonify({'status': 'ok'}), 200
                    GROUP_LINK = parts[1].strip()
                    save_config_value("group_link", GROUP_LINK)
                    safe = GROUP_LINK.replace('_', '\\_')
                    send_message(chat_id, f"✅ Group link set to: {safe}")
                    return jsonify({'status': 'ok'}), 200

                if chat_type == 'private' and not DM_GAMES_ENABLED and is_dm_game_command(text):
                    send_message(chat_id, build_dm_games_off_text())
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/setrate(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, f"💱 Current Rate: *₹{EXCHANGE_RATE:.2f} / USDT*\nUsage: `/setrate <rate>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = float(parts[1])
                        if val <= 0:
                            raise ValueError()
                        EXCHANGE_RATE = val
                        save_config_value("exchange_rate", EXCHANGE_RATE)
                        send_message(chat_id, f"✅ Exchange rate updated to *₹{EXCHANGE_RATE:.2f} / USDT*.")
                    except ValueError:
                        send_message(chat_id, "⚠️ Enter a valid positive rate (e.g. `/setrate 98`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/sethb(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, f"🏦 Current House Balance: *{format_money(HOUSE_BALANCE, user_id)}*\nUsage: `/sethb <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = float(parts[1])
                        if val < 0:
                            raise ValueError()
                        _, kb = create_manual_txn_confirmation(user_id, chat_id, "sethb", {"val": val})
                        conf_txt = (
                            "⚠️ *Confirm Manual Transaction*\n\n"
                            "• *Action:* Set House Balance (`/sethb`)\n"
                            f"• *Current HB:* *{format_money(HOUSE_BALANCE, user_id)}*\n"
                            f"• *New HB:* *{format_money(val, user_id)}*"
                        )
                        send_message(chat_id, conf_txt, reply_markup=kb)
                    except ValueError:
                        send_message(chat_id, "⚠️ Enter a valid non-negative amount (e.g. `/sethb 150000`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/deducthb(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, f"🏦 Current House Balance: *{format_money(HOUSE_BALANCE, user_id)}*\nUsage: `/deducthb <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        amt = float(parts[1])
                        if amt <= 0:
                            raise ValueError()
                        new_hb = max(0.0, HOUSE_BALANCE - amt)
                        _, kb = create_manual_txn_confirmation(user_id, chat_id, "deducthb", {"amt": amt})
                        conf_txt = (
                            "⚠️ *Confirm Manual Transaction*\n\n"
                            "• *Action:* Deduct House Balance (`/deducthb`)\n"
                            f"• *Deduct Amount:* *{format_money(amt, user_id)}*\n"
                            f"• *Current HB:* *{format_money(HOUSE_BALANCE, user_id)}*\n"
                            f"• *HB After:* *{format_money(new_hb, user_id)}*"
                        )
                        send_message(chat_id, conf_txt, reply_markup=kb)
                    except ValueError:
                        send_message(chat_id, "⚠️ Enter a valid positive amount (e.g. `/deducthb 5000`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/minbet(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, f"🎯 Current Min Bet: *{format_money(MIN_BET, user_id)}*\nUsage: `/minbet <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = float(parts[1])
                        if val <= 0 or val > MAX_BET:
                            raise ValueError()
                        MIN_BET = val
                        send_message(chat_id, f"✅ Min Bet updated to *{format_money(MIN_BET, user_id)}*.")
                    except ValueError:
                        send_message(chat_id, f"⚠️ Enter a valid amount `> 0` and `<= MAX_BET` (`{MAX_BET}`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/maxbet(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, f"🎯 Current Max Bet: *{format_money(MAX_BET, user_id)}*\nUsage: `/maxbet <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = float(parts[1])
                        if val <= 0 or val < MIN_BET:
                            raise ValueError()
                        MAX_BET = val
                        send_message(chat_id, f"✅ Max Bet updated to *{format_money(MAX_BET, user_id)}*.")
                    except ValueError:
                        send_message(chat_id, f"⚠️ Enter a valid amount `>= MIN_BET` (`{MIN_BET}`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/addbalance(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 3:
                        send_message(chat_id, "⚠️ Usage: `/addbalance <user_id/@username> <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    target_uid = resolve_user_identifier(parts[1])
                    if target_uid is None:
                        send_message(chat_id, f"⚠️ User `{parts[1]}` not found.")
                        return jsonify({'status': 'ok'}), 200
                    amt_inr = parse_user_amount(parts[2], target_uid)
                    if amt_inr is None or amt_inr <= 0:
                        send_message(chat_id, "⚠️ Enter a valid positive amount.")
                        return jsonify({'status': 'ok'}), 200
                    cur_b = float(user_balances.get(target_uid, 0.0))
                    _, kb = create_manual_txn_confirmation(
                        user_id, chat_id, "addbalance", {"target_uid": target_uid, "amt_inr": amt_inr}
                    )
                    conf_txt = (
                        "⚠️ *Confirm Manual Transaction*\n\n"
                        "• *Action:* Add Balance (`/addbalance`)\n"
                        f"• *Target User:* `{target_uid}` ({display_sender_label(target_uid)})\n"
                        f"• *Amount:* *+{format_money(amt_inr, target_uid)}*\n"
                        f"• *Current Balance:* *{format_money(cur_b, target_uid)}*\n"
                        f"• *Balance After:* *{format_money(cur_b + amt_inr, target_uid)}*"
                    )
                    send_message(chat_id, conf_txt, reply_markup=kb)
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/deductbalance(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 3:
                        send_message(chat_id, "⚠️ Usage: `/deductbalance <user_id/@username> <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    target_uid = resolve_user_identifier(parts[1])
                    if target_uid is None:
                        send_message(chat_id, f"⚠️ User `{parts[1]}` not found.")
                        return jsonify({'status': 'ok'}), 200
                    amt_inr = parse_user_amount(parts[2], target_uid)
                    if amt_inr is None or amt_inr <= 0:
                        send_message(chat_id, "⚠️ Enter a valid positive amount.")
                        return jsonify({'status': 'ok'}), 200
                    cur_b = float(user_balances.get(target_uid, 0.0))
                    after_b = max(0.0, cur_b - amt_inr)
                    _, kb = create_manual_txn_confirmation(
                        user_id, chat_id, "deductbalance", {"target_uid": target_uid, "amt_inr": amt_inr}
                    )
                    conf_txt = (
                        "⚠️ *Confirm Manual Transaction*\n\n"
                        "• *Action:* Deduct Balance (`/deductbalance`)\n"
                        f"• *Target User:* `{target_uid}` ({display_sender_label(target_uid)})\n"
                        f"• *Deduct Amount:* *-{format_money(amt_inr, target_uid)}*\n"
                        f"• *Current Balance:* *{format_money(cur_b, target_uid)}*\n"
                        f"• *Balance After:* *{format_money(after_b, target_uid)}*"
                    )
                    send_message(chat_id, conf_txt, reply_markup=kb)
                    return jsonify({'status': 'ok'}), 200

                mult_cmd_map = {
                    "/setmultidice": "dice",
                    "/setmultidart": "dart",
                    "/setmultifoot": "foot",
                    "/setmultibasket": "basket",
                    "/setmultibowl": "bowl",
                    "/setmultiboel": "bowl",
                    "/setmultipvp": "pvp",
                    "/setmultibj": "bj",
                    "/setmultidr": "dr",
                }

                matched_mult_key = None
                for cmd_prefix, m_key in mult_cmd_map.items():
                    if re.match(rf"^{re.escape(cmd_prefix)}(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                        matched_mult_key = m_key
                        break

                if matched_mult_key:
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        cur_m = GAME_MULTIPLIERS.get(matched_mult_key)
                        send_message(chat_id, f"⚙️ Current `{matched_mult_key}` multiplier: *{fmt_mult(cur_m)}*\nUsage: `{parts[0]} <multiplier>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        new_val = float(parts[1])
                        if new_val <= 0 or new_val > 100:
                            raise ValueError()
                        GAME_MULTIPLIERS[matched_mult_key] = new_val
                        send_message(chat_id, f"✅ Updated `{matched_mult_key}` multiplier to *{fmt_mult(new_val)}*.")
                    except ValueError:
                        send_message(chat_id, "⚠️ Enter a valid positive multiplier (e.g. `1.94`, `1.9`, `2`).")
                    return jsonify({'status': 'ok'}), 200

                seven_up_mult_cmd_map = {
                    "/setmulti7upup": "up",
                    "/setmultihigh": "up",
                    "/setmulti7updown": "down",
                    "/setmultilow": "down",
                    "/setmulti7upodd": "odd",
                    "/setmulti7upeven": "even",
                    "/setmulti7up7": "7",
                }
                matched_7up_key = None
                for cmd_prefix, s_key in seven_up_mult_cmd_map.items():
                    if re.match(rf"^{re.escape(cmd_prefix)}(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                        matched_7up_key = s_key
                        break

                if matched_7up_key:
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        cur_m = get_7up_multiplier(matched_7up_key)
                        send_message(chat_id, f"⚙️ Current `7up` (`{matched_7up_key}`) multiplier: *{fmt_mult(cur_m)}*\nUsage: `{parts[0]} <multiplier>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        new_val = float(parts[1])
                        if new_val <= 0 or new_val > 100:
                            raise ValueError()
                        GAME_MULTIPLIERS.setdefault("7up", {})[matched_7up_key] = new_val
                        send_message(chat_id, f"✅ Updated `7up` (`{matched_7up_key}`) multiplier to *{fmt_mult(new_val)}*.")
                    except ValueError:
                        send_message(chat_id, "⚠️ Enter a valid positive multiplier (e.g. `2.16`, `1.9`, `5.16`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/setmultidrnum(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 3:
                        send_message(chat_id, "⚠️ Usage: `/setmultidrnum <1-5> <multiplier>` (e.g. `/setmultidrnum 3 1.92`)")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        cnt = int(parts[1])
                        new_val = float(parts[2])
                        if cnt not in [1, 2, 3, 4, 5] or new_val <= 0 or new_val > 100:
                            raise ValueError()
                        GAME_MULTIPLIERS["dr_nums"][cnt] = new_val
                        send_message(chat_id, f"✅ Updated `/dr` ({cnt} number(s)) multiplier to *{fmt_mult(new_val)}*.")
                    except ValueError:
                        send_message(chat_id, "⚠️ Invalid input. Count must be `1`–`5` and multiplier `> 0`.")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/mults(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    dr_nums_str = ", ".join(f"{k}n: {fmt_mult(v)}" for k, v in GAME_MULTIPLIERS["dr_nums"].items())
                    m7 = GAME_MULTIPLIERS.get("7up", {})
                    txt = (
                        "⚙️ *Active Game Multipliers*\n\n"
                        f"• Dice: *{fmt_mult(GAME_MULTIPLIERS['dice'])}*\n"
                        f"• Dart: *{fmt_mult(GAME_MULTIPLIERS['dart'])}*\n"
                        f"• Football: *{fmt_mult(GAME_MULTIPLIERS['foot'])}*\n"
                        f"• Basketball: *{fmt_mult(GAME_MULTIPLIERS['basket'])}*\n"
                        f"• Bowling: *{fmt_mult(GAME_MULTIPLIERS['bowl'])}*\n"
                        f"• PvP: *{fmt_mult(GAME_MULTIPLIERS['pvp'])}*\n"
                        f"• Blackjack: *{fmt_mult(GAME_MULTIPLIERS['bj'])}*\n"
                        f"• Predict (H/L/O/E): *{fmt_mult(GAME_MULTIPLIERS['dr'])}*\n"
                        f"• Predict Numbers: `{dr_nums_str}`\n"
                        f"• 7Up: `up/high: {fmt_mult(m7.get('up', 2.16))}, down/low: {fmt_mult(m7.get('down', 2.16))}, odd: {fmt_mult(m7.get('odd', 1.9))}, even: {fmt_mult(m7.get('even', 1.9))}, 7: {fmt_mult(m7.get('7', 5.16))}`"
                    )
                    send_message(chat_id, txt)
                    return jsonify({'status': 'ok'}), 200
                
                if re.match(r'^/approve(?:@\S+)?(?:\s+|$)', text, re.IGNORECASE):
                    if user_id in admin_list:
                        parts = text.split(' ')
                        if len(parts) > 1 and parts[1].strip('-').isdigit():
                            target_chat_id = int(parts[1])
                            approved_groups.add(target_chat_id)
                            persist_approved_group(target_chat_id)
                            send_message(chat_id, f"✅ Group `{target_chat_id}` has been successfully *APPROVED*!")
                        else:
                            send_message(chat_id, "⚠️ Invalid format. Use: `/approve <chat_id>`")
                    else:
                        pass  # normal users get no reply to admin commands
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/info(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, "⚠️ Usage: `/info <username/userid>`")
                        return jsonify({'status': 'ok'}), 200
                    target_uid = resolve_user_identifier(parts[1])
                    if target_uid is None:
                        send_message(chat_id, f"⚠️ User `{parts[1]}` not found.")
                        return jsonify({'status': 'ok'}), 200
                    send_message(chat_id, build_user_info_summary(target_uid), reply_markup=info_menu_keyboard(target_uid))
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/search(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, "⚠️ Usage: `/search XC-XXXXXXX-XXXX`")
                        return jsonify({'status': 'ok'}), 200
                    send_message(chat_id, build_game_search_report(parts[1]))
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/cancel(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, "⚠️ Usage: `/cancel XC-XXXXXXX-XXXX`")
                        return jsonify({'status': 'ok'}), 200
                    gid = parts[1].strip().upper()
                    rec = game_id_registry.get(gid)
                    if not rec:
                        send_message(chat_id, f"⚠️ Game ID `{gid}` not found.")
                        return jsonify({'status': 'ok'}), 200
                    involved = {rec.get("owner_id"), rec.get("meta", {}).get("p1_id"), rec.get("meta", {}).get("p2_id")}
                    if user_id not in admin_list and user_id not in involved:
                        send_message(chat_id, "⛔ You can only cancel your own active games.")
                        return jsonify({'status': 'ok'}), 200
                    _, status_msg = cancel_game_by_id(gid)
                    send_message(chat_id, status_msg)
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/tip(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    parts = text.split()
                    current_bal = user_balances.get(user_id, 0.0)
                    receiver_id = None
                    amt_inr = None

                    if 'reply_to_message' in message and message['reply_to_message'].get('from'):
                        reply_from = message['reply_to_message']['from']
                        if not reply_from.get('is_bot'):
                            receiver_id = register_user_identity(reply_from)
                        if len(parts) >= 2:
                            amt_inr = parse_user_amount(parts[1], user_id)
                    else:
                        if len(parts) >= 3:
                            amt_inr = parse_user_amount(parts[1], user_id)
                            target_uname = parts[2].lstrip("@").lower()
                            receiver_id = username_to_id.get(target_uname)
                        elif len(parts) == 2:
                            send_message(chat_id, "⚠️ Reply to a user's message with `/tip <amount>` or use `/tip <amount> <username>`.")
                            return jsonify({'status': 'ok'}), 200
                        else:
                            send_message(chat_id, "⚠️ Usage: `/tip <amount> <username>` or reply to a message with `/tip <amount>`.")
                            return jsonify({'status': 'ok'}), 200

                    if amt_inr is None or amt_inr <= 0:
                        send_message(chat_id, "⚠️ Enter a valid tip amount. Example: `/tip 50 @username`")
                        return jsonify({'status': 'ok'}), 200

                    if receiver_id is None:
                        send_message(chat_id, "⚠️ Recipient not found! Make sure they have interacted with the bot or reply directly to their message.")
                        return jsonify({'status': 'ok'}), 200

                    if receiver_id == user_id:
                        send_message(chat_id, "⚠️ You cannot tip yourself!")
                        return jsonify({'status': 'ok'}), 200

                    if current_bal < amt_inr:
                        send_message(
                            chat_id,
                            f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Tip: *{format_money(amt_inr, user_id)}*"
                        )
                        return jsonify({'status': 'ok'}), 200

                    _, kb = create_manual_txn_confirmation(
                        user_id,
                        chat_id,
                        "tip",
                        {"receiver_id": receiver_id, "amt_inr": amt_inr, "origin_chat_id": chat_id},
                    )
                    conf_txt = (
                        "⚠️ *Confirm Tip Transaction*\n\n"
                        "• *Action:* Send Tip (`/tip`)\n"
                        f"• *To:* {display_sender_label(receiver_id)} (`{receiver_id}`)\n"
                        f"• *Amount:* *{format_money(amt_inr, user_id)}*\n"
                        f"• *Your Balance:* *{format_money(current_bal, user_id)}*"
                    )
                    send_message(chat_id, conf_txt, reply_markup=kb)
                    return jsonify({'status': 'ok'}), 200

                if text == '/start':
                    help_text = (
                        f"🎰 *Welcome to {BOT_USERNAME} Casino!* 🎲\n\n"
                        "Commands:\n"
                        "- `/balance` or `/bal` - Check wallet balance\n"
                        "- `/hb` - Check House Balance\n"
                        "- `/currency` - Change currency (INR / USDT)\n"
                        "- `/stats` - View your visual stats card\n"
                        "- `/history` - View your bet history (5 per page)\n"
                        "- `/deposit` - Add money via ZapUPI (DM Only)\n"
                        "- `/withdraw` - Withdraw your winnings (DM Only)\n"
                        "- `/tip <amount> <username>` or reply `/tip <amount>` - Send tip\n"
                        "- `/cancel <game_id>` - Cancel an active game\n"
                        "- `/search <game_id>` - Search game info by ID\n\n"
                        "🃏 *Blackjack:* `/bj 50` (Hit / Stand / Double buttons)\n\n"
                        "🔐 *Provably Fair Games:*\n"
                        "• 💣 `/mines 50 3` → 5x5 board, 3 mines (1-24)\n"
                        "• 🗼 `/tower 50 easy` → easy / medium / hard / expert / master\n"
                        "• 🚀 `/limbo 50 2` → win if result ≥ your target\n"
                        "• `/fair` seeds · `/setseed <text>` · `/verify <game_id>`\n\n"
                        "🎮 *Versus Games (`/dice`, `/dart`, `/foot`, `/basket`, `/bowl`)*\n"
                        "• `/dice 50` → Opens menu\n"
                        "• `/dice 50 1r1w` → Auto `normal` mode + direct confirmation\n"
                        "• `/dice 50 1r1w crazy` → `crazy` mode + direct confirmation\n\n"
                        "🔮 *Prediction Game (`/dr`):*\n"
                        "- `/dr 50 high` or `/dr 50 2,4,6`\n\n"
                        "🎲🎲 *7Up Game (`/7up`):*\n"
                        "- `/7up 50 up` (`high`), `/7up 50 down` (`low`), `/7up 50 odd`, `/7up 50 even`, `/7up 50 7`"
                    )
                    send_message(chat_id, help_text)

                elif re.match(rf"^/top(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    bio = generate_top_wagerers_image(viewer_id=user_id)
                    send_photo(chat_id, bio, caption="🏆 *Top 10 Wagerers Leaderboard*")
                    return jsonify({'status': 'ok'}), 200

                elif re.match(rf"^/hb(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    send_message(chat_id, f"🏦 *House Balance:* *{format_money(HOUSE_BALANCE, user_id)}*")

                elif re.match(rf"^/(?:history|mybets)(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    hist_text, hist_kb = build_user_history_page(user_id, page=0)
                    send_message(chat_id, hist_text, reply_markup=hist_kb)
                    return jsonify({'status': 'ok'}), 200

                elif re.match(rf"^/7up(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    active_summary = get_active_game_summary(user_id)
                    if active_summary:
                        send_message(chat_id, f"⚠️ You are already playing *{active_summary}*! Finish it before starting another game.")
                        return jsonify({'status': 'ok'}), 200

                    tokens = text.split()[1:]
                    bet_inr = None
                    canonical_choice = None
                    raw_choice = None

                    for tok in tokens:
                        norm_c = normalize_7up_choice(tok)
                        if norm_c is not None and canonical_choice is None:
                            canonical_choice = norm_c
                            raw_choice = tok
                        elif bet_inr is None:
                            parsed = parse_user_amount(tok, user_id)
                            if parsed is not None:
                                bet_inr = parsed

                    if canonical_choice is None or bet_inr is None:
                        send_message(
                            chat_id,
                            "⚠️ Usage: `/7up <amount> <up/high | down/low | odd | even | 7>`\n"
                            "Example: `/7up 50 up` or `/7up 50 7`"
                        )
                        return jsonify({'status': 'ok'}), 200

                    current_bal = float(user_balances.get(user_id, 0.0))
                    if bet_inr <= 0:
                        send_message(chat_id, "⚠️ Enter a valid bet amount.")
                    elif bet_inr < MIN_BET or bet_inr > MAX_BET:
                        send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                    elif current_bal < bet_inr:
                        send_message(
                            chat_id,
                            f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                        )
                    else:
                        run_7up_game(
                            chat_id, user_id, bet_inr, canonical_choice, raw_choice_text=raw_choice,
                            reply_to_message_id=message.get('message_id') if chat_type in ['group', 'supergroup'] else None
                        )
                    return jsonify({'status': 'ok'}), 200

                elif re.match(FAIR_CMD_RE, text, re.IGNORECASE):
                    handle_fair_command(chat_id, chat_type, user_id, text, message)
                    return jsonify({'status': 'ok'}), 200

                elif re.match(rf"^/bj(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    active_summary = get_active_game_summary(user_id)
                    if active_summary:
                        send_message(chat_id, f"⚠️ You already have an active game (*{active_summary}*)! Finish it before starting a new game.")
                        return jsonify({'status': 'ok'}), 200

                    parts = text.split()
                    bet_inr = parse_user_amount(parts[1], user_id) if len(parts) > 1 else parse_user_amount("10", user_id)
                    current_bal = user_balances.get(user_id, 0.0)

                    if bet_inr is None or bet_inr <= 0:
                        send_message(chat_id, "⚠️ Enter a valid bet amount. Example: `/bj 50`")
                    elif bet_inr < MIN_BET or bet_inr > MAX_BET:
                        send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                    elif current_bal < bet_inr:
                        send_message(
                            chat_id,
                            f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                        )
                    else:
                        start_bj_game(chat_id, user_id, bet_inr)
                    return jsonify({'status': 'ok'}), 200
                    
                elif text in ['/balance', '/bal']:
                    if user_id in deposit_states: del deposit_states[user_id]
                    if user_id in withdrawal_states: del withdrawal_states[user_id]
                    
                    bal_str = format_money(user_balances.get(user_id, 0.0), user_id)
                    
                    if chat_type == 'private':
                        bal_keyboard = {
                            "inline_keyboard": [
                                [
                                    {"text": "💳 Deposit", "callback_data": "btn_deposit"},
                                    {"text": "💸 Withdraw", "callback_data": "btn_withdraw"}
                                ]
                            ]
                        }
                        send_message(chat_id, f"💰 *Your Wallet Balance:* {bal_str}", reply_markup=bal_keyboard)
                    else:
                        bal_keyboard = {
                            "inline_keyboard": [
                                [
                                    {"text": "📥 Manage Balance in DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}
                                ]
                            ]
                        }
                        send_message(chat_id, f"💰 *Your Wallet Balance:* {bal_str}\n\n_ℹ️ Deposit & Withdraw can only be done in Bot's DM!_", reply_markup=bal_keyboard)
                    
                elif text == '/currency':
                    keyboard = {
                        "inline_keyboard": [
                            [
                                {"text": "🇮🇳 INR (₹)", "callback_data": "curr_inr"},
                                {"text": "🇺🇸 USDT ($)", "callback_data": "curr_usdt"}
                            ]
                        ]
                    }
                    cur_sent = send_message(chat_id, f"🌐 *Select Your Preferred Currency:*\nCurrent: *{user_currency.get(user_id, 'INR')}*", reply_markup=keyboard)
                    remember_button_owner(chat_id, cur_sent, user_id)
                    
                elif text == '/stats':
                    send_message(chat_id, "📊 Generating your stats card...")
                    bio = generate_stats_image(user_id)
                    send_photo(chat_id, bio, caption=f"✨ *Stats for user `{user_id}`*")
                    
                elif text == '/deposit':
                    if chat_type != 'private':
                        send_message(chat_id, f"❌ Deposit command can only be used in Bot's DM (Private Chat)!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                        return jsonify({'status': 'ok'}), 200

                    if not DEPOSIT_ENABLED:
                        send_message(chat_id, "❌ Deposits are currently disabled by Admin.")
                        return jsonify({'status': 'ok'}), 200
                    deposit_states[user_id] = True
                    send_message(chat_id, "💳 *Please enter the amount you want to deposit (e.g. 200):*")
                    
                elif text.startswith('/deposit '):
                    if chat_type != 'private':
                        send_message(chat_id, f"❌ Deposit command can only be used in Bot's DM (Private Chat)!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                        return jsonify({'status': 'ok'}), 200

                    if not DEPOSIT_ENABLED:
                        send_message(chat_id, "❌ Deposits are currently disabled by Admin.")
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split(' ')
                    if len(parts) > 1 and parts[1].replace('.', '', 1).isdigit():
                        amt_inr = parse_user_amount(parts[1], user_id)
                        send_message(chat_id, "⏳ Generating deposit link...")
                        res_text, pay_kb = create_zapupi_order(amt_inr, user_id)
                        send_message(chat_id, res_text, reply_markup=pay_kb)
                    else:
                        send_message(chat_id, "⚠️ Use format: `/deposit 100`")

                elif text == '/withdraw':
                    if chat_type != 'private':
                        send_message(chat_id, f"❌ Withdrawal command can only be used in Bot's DM (Private Chat)!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                        return jsonify({'status': 'ok'}), 200

                    if not WITHDRAW_ENABLED:
                        send_message(chat_id, "❌ Withdrawals are currently disabled by Admin.")
                        return jsonify({'status': 'ok'}), 200
                    withdrawal_states[user_id] = {'step': 'waiting_amount'}
                    send_message(chat_id, "💸 *Withdrawal Flow*\n\nPlease enter the amount you want to withdraw:")
                    
                elif text in ['/panel', '/admin']:
                    if user_id in admin_list:
                        panel_text = (
                            "👑 *Owner & Admin Control Dashboard*\n\n"
                            f"🛠 *Maintenance:* {'🟢 OFF' if not MAINTENANCE_MODE else '🔴 ON'}\n"
                            f"💳 *Deposits:* {'🟢 Enabled' if DEPOSIT_ENABLED else '🔴 Disabled'}\n"
                            f"💸 *Withdrawals:* {'🟢 Enabled' if WITHDRAW_ENABLED else '🔴 Disabled'}\n"
                            f"🎮 *DM Games:* {'🟢 ON' if DM_GAMES_ENABLED else '🔴 OFF'}\n"
                            f"🤖 *Helper Bots:* {sum(1 for h in HELPER_BOTS if h.get('enabled'))}/{len(HELPER_BOTS)} ON (`/helper`)\n"
                            f"🏦 *House Balance:* ₹{HOUSE_BALANCE:,.2f}"
                        )
                        admin_keyboard = {
                            "inline_keyboard": [
                                [{"text": "➕ Add Balance", "callback_data": "adm_add_bal"}, {"text": "➖ Deduct Balance", "callback_data": "adm_deduct_bal"}],
                                [{"text": "📊 User Stats", "callback_data": "adm_user_stats"}, {"text": "👥 User List", "callback_data": "adm_users"}],
                                [{"text": "🚫 Ban User", "callback_data": "adm_ban"}, {"text": "✅ Unban User", "callback_data": "adm_unban"}],
                                [{"text": "📥 Last 50 Deposits", "callback_data": "adm_last_dep"}, {"text": "📤 Last 50 Withdraws", "callback_data": "adm_last_wd"}],
                                [{"text": "👑 Grant Admin", "callback_data": "adm_grant"}, {"text": "⛔ Revoke Admin", "callback_data": "adm_revoke"}],
                                [{"text": "📢 Broadcast All", "callback_data": "adm_bc_all"}, {"text": "💬 Broadcast Private", "callback_data": "adm_bc_priv"}],
                                [{"text": "🛠 Toggle Maintenance", "callback_data": "adm_toggle_maint"}],
                                [{"text": "💳 Toggle Deposit", "callback_data": "adm_toggle_dep"}, {"text": "💸 Toggle Withdraw", "callback_data": "adm_toggle_wd"}]
                            ]
                        }
                        send_message(chat_id, panel_text, reply_markup=admin_keyboard)
                    else:
                        pass  # normal users get no reply to admin commands
                        
                elif text.startswith('/dr '):
                    active_summary = get_active_game_summary(user_id)
                    if active_summary:
                        send_message(chat_id, f"⚠️ You are already playing *{active_summary}*! Finish it before starting another game.")
                        return jsonify({'status': 'ok'}), 200

                    parts = text.split(' ')
                    current_bal = user_balances.get(user_id, 0.0)
                    if len(parts) == 3 and parts[1].replace('.', '', 1).isdigit():
                        bet_inr = parse_user_amount(parts[1], user_id)
                        arg = parts[2].lower()
                        
                        if bet_inr is None or bet_inr <= 0:
                            send_message(chat_id, "⚠️ Enter a valid bet amount.")
                            return jsonify({'status': 'ok'}), 200
                        elif bet_inr < MIN_BET or bet_inr > MAX_BET:
                            send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                            return jsonify({'status': 'ok'}), 200
                        elif current_bal < bet_inr:
                            send_message(
                                chat_id,
                                f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                            )
                            return jsonify({'status': 'ok'}), 200
                            
                        is_win = False
                        multiplier = 0.0
                        win_desc = ""
                        
                        if arg in ['high', 'low', 'odd', 'even']:
                            gid = generate_game_id()
                            user_balances[user_id] = current_bal - bet_inr
                            register_game_record(gid, "prediction", user_id, bet_inr, meta={"choice": arg}, refund_on_cancel=True)
                            res = send_animated_game(chat_id, '🎲', reply_to_message_id=message.get('message_id') if chat_type in ['group', 'supergroup'] else None)
                            dice_val = res['result']['dice']['value'] if res and 'result' in res else random.randint(1, 6)
                            time.sleep(1)
                            
                            if arg == 'high' and dice_val in [4, 5, 6]: is_win = True
                            elif arg == 'low' and dice_val in [1, 2, 3]: is_win = True
                            elif arg == 'odd' and dice_val in [1, 3, 5]: is_win = True
                            elif arg == 'even' and dice_val in [2, 4, 6]: is_win = True
                            
                            multiplier = float(GAME_MULTIPLIERS.get("dr", 1.92))
                            win_desc = f"Prediction: {arg.upper()}"
                        else:
                            try:
                                nums = [int(n.strip()) for n in arg.split(',')]
                                if not all(1 <= n <= 6 for n in nums) or len(nums) > 5 or len(nums) != len(set(nums)):
                                    raise ValueError()
                                    
                                gid = generate_game_id()
                                user_balances[user_id] = current_bal - bet_inr
                                register_game_record(gid, "prediction", user_id, bet_inr, meta={"nums": nums}, refund_on_cancel=True)
                                res = send_animated_game(chat_id, '🎲', reply_to_message_id=message.get('message_id') if chat_type in ['group', 'supergroup'] else None)
                                dice_val = res['result']['dice']['value'] if res and 'result' in res else random.randint(1, 6)
                                time.sleep(1)
                                
                                if dice_val in nums: is_win = True
                                
                                count = len(nums)
                                dr_num_map = GAME_MULTIPLIERS.get("dr_nums", {1: 5.56, 2: 2.88, 3: 1.92, 4: 1.44, 5: 1.15})
                                multiplier = float(dr_num_map.get(count, 1.0))
                                win_desc = f"Numbers: {nums}"
                            except:
                                send_message(chat_id, "⚠️ Invalid format! Use `high`, `low`, `odd`, `even` or numbers like `2,4,6`.\nExample: `/dr 50 2,4,6`")
                                return jsonify({'status': 'ok'}), 200
                                
                        if is_win:
                            win_amt = bet_inr * multiplier
                            profit_inr = win_amt - bet_inr
                            user_balances[user_id] = user_balances.get(user_id, 0.0) + win_amt
                            HOUSE_BALANCE -= profit_inr
                            update_user_stats(user_id, "prediction", bet_inr, profit_inr, True)
                            record_user_bet(user_id, f"Prediction ({win_desc})", bet_inr, profit_inr, "WON", game_id=gid)
                            mark_game_finished(gid, "completed", extra_meta={"outcome": "WON", "pnl": profit_inr})
                            log_win_to_channel(user_id, "🔮", "Predict", win_amt, fmt_mult(multiplier))
                            result_text = build_dr_result_message(gid, dice_val, arg, True, win_amt=win_amt, multiplier=multiplier, user_id=user_id)
                        else:
                            profit_inr = -bet_inr
                            HOUSE_BALANCE += bet_inr
                            update_user_stats(user_id, "prediction", bet_inr, profit_inr, False)
                            record_user_bet(user_id, f"Prediction ({win_desc})", bet_inr, profit_inr, "LOST", game_id=gid)
                            mark_game_finished(gid, "completed", extra_meta={"outcome": "LOST", "pnl": profit_inr})
                            result_text = build_dr_result_message(gid, dice_val, arg, False, user_id=user_id)
                            
                        pm_dr_payload = {"kind": "dr", "owner_id": user_id, "bet": bet_inr, "dr_arg": arg}
                        send_message(chat_id, result_text, reply_markup=create_post_match_keyboard(user_id, pm_dr_payload))
                    else:
                        send_message(chat_id, "⚠️ Format error! Use: `/dr <amount> <choice>`\nExample: `/dr 50 high` or `/dr 50 1,3,5`")
                        
                else:
                    game_cmd_map = {
                        '/dice': '🎲',
                        '/dart': '🎯',
                        '/foot': '⚽',
                        '/basket': '🏀',
                        '/bowl': '🎳'
                    }
                    
                    triggered_game = None
                    for cmd, emoji in game_cmd_map.items():
                        if re.match(rf"^{re.escape(cmd)}(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                            triggered_game = emoji
                            break
                    
                    if triggered_game:
                        active_summary = get_active_game_summary(user_id)
                        if active_summary:
                            send_message(chat_id, f"⚠️ You are already playing *{active_summary}*! Finish it before starting another game.")
                            return jsonify({'status': 'ok'}), 200

                        tokens = text.split()[1:]
                        bet_inr = parse_user_amount("10", user_id)
                        mode = None
                        rw_label = None
                        invalid_rw = False
                        current_bal = user_balances.get(user_id, 0.0)
                        
                        for tok in tokens:
                            low_tok = tok.lower()
                            if low_tok in ["crazy", "normal"]:
                                mode = low_tok
                            elif re.fullmatch(r"\d+r\d+w", low_tok):
                                if low_tok in VALID_RW_MODES:
                                    rw_label = low_tok
                                else:
                                    invalid_rw = True
                            else:
                                parsed = parse_user_amount(tok, user_id)
                                if parsed is not None:
                                    bet_inr = parsed

                        if rw_label is not None and mode is None:
                            mode = "normal"
                                    
                        if invalid_rw:
                            send_message(chat_id, "⚠️ Invalid RW mode! Allowed modes: `1r1w`, `2r1w`, `3r1w`, `1r2w`, `2r2w`, `3r2w`, `1r3w`, `2r3w`, `3r3w`.")
                        elif bet_inr is None or bet_inr <= 0:
                            send_message(chat_id, "⚠️ Enter a valid bet amount.")
                        elif bet_inr < MIN_BET or bet_inr > MAX_BET:
                            send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                        elif current_bal < bet_inr:
                            send_message(
                                chat_id,
                                f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                            )
                        else:
                            gid = generate_game_id()
                            g_name = GAME_NAME_MAP.get(triggered_game, "Game")
                            if rw_label is not None and mode is not None:
                                conf_msg = build_match_confirmation_text(user_id, triggered_game, bet_inr, mode, rw_label, game_id=gid)
                                sent = send_message(
                                    chat_id, conf_msg, reply_markup=match_confirm_keyboard(chat_type),
                                    reply_to_message_id=message.get('message_id') if chat_type in ['group', 'supergroup'] else None
                                )
                                msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
                                remember_button_owner(chat_id, msg_id, user_id)
                                pending_game_setup[user_id] = {
                                    "game_id": gid,
                                    "chat_id": chat_id,
                                    "chat_type": chat_type,
                                    "message_id": msg_id,
                                    "trigger_msg_id": message.get('message_id'),
                                    "emoji": triggered_game,
                                    "bet": bet_inr,
                                    "mode": mode,
                                    "rw_label": rw_label
                                }
                            elif mode is None:
                                setup_msg = (
                                    f"🎮 *{g_name} ({triggered_game}) Setup* (`{gid}`)\n"
                                    f"💰 Bet: *{format_money(bet_inr, user_id)}*\n\n"
                                    "Select Mode:"
                                )
                                sent = send_message(chat_id, setup_msg, reply_markup=game_style_keyboard())
                                msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
                                remember_button_owner(chat_id, msg_id, user_id)
                                pending_game_setup[user_id] = {
                                    "game_id": gid,
                                    "chat_id": chat_id,
                                    "chat_type": chat_type,
                                    "message_id": msg_id,
                                    "emoji": triggered_game,
                                    "bet": bet_inr,
                                    "mode": None,
                                    "rw_label": None
                                }
                            else:
                                mode_title = "🔥 CRAZY MODE (Lowest Sum Wins)" if mode == "crazy" else "⚡ NORMAL MODE (Highest Sum Wins)"
                                rw_msg = (
                                    f"🎯 *Select RW Mode* (`{gid}` | {g_name} {triggered_game} | {mode_title})\n"
                                    f"💰 Bet: *{format_money(bet_inr, user_id)}*\n\nTap a mode below:"
                                )
                                sent = send_message(chat_id, rw_msg, reply_markup=rw_mode_keyboard())
                                msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
                                remember_button_owner(chat_id, msg_id, user_id)
                                pending_game_setup[user_id] = {
                                    "game_id": gid,
                                    "chat_id": chat_id,
                                    "chat_type": chat_type,
                                    "message_id": msg_id,
                                    "emoji": triggered_game,
                                    "bet": bet_inr,
                                    "mode": mode,
                                    "rw_label": None
                                }

        elif 'callback_query' in data:
            query = data['callback_query']
            callback_query_id = query['id']
            callback_data = query['data']
            chat_id = query['message']['chat']['id']
            chat_type = query['message']['chat']['type']
            message_id = query['message']['message_id']
            user_id = query['from']['id']
            
            if callback_data.startswith("mtx_ok_") or callback_data.startswith("mtx_no_"):
                is_confirm = callback_data.startswith("mtx_ok_")
                token = callback_data.replace("mtx_ok_", "", 1) if is_confirm else callback_data.replace("mtx_no_", "", 1)
                entry = pending_manual_txns.get(token)
                if not entry:
                    answer_callback(callback_query_id, "Transaction already processed or expired.")
                    remove_inline_keyboard(chat_id, message_id)
                    return jsonify({'status': 'ok'}), 200
                if user_id != entry.get("initiator_id"):
                    answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                    return jsonify({'status': 'ok'}), 200
                pending_manual_txns.pop(token, None)
                remove_inline_keyboard(chat_id, message_id)
                if is_confirm:
                    execute_manual_txn(entry)
                    answer_callback(callback_query_id, "Transaction confirmed!")
                else:
                    edit_message(chat_id, message_id, "❌ *Transaction Cancelled.*")
                    answer_callback(callback_query_id, "Transaction cancelled.")
                return jsonify({'status': 'ok'}), 200

            # Another player tapped someone else's buttons: warn them, change nothing.
            shared_buttons = ("pvp_acc_", "pvp_can_", "adm_", "admin_wd_", "infopg_", "pm_again_", "pm_double_", "myhistpg_")
            if not callback_data.startswith(shared_buttons):
                btn_owner = find_button_owner(chat_id, message_id)
                if btn_owner is not None and btn_owner != user_id:
                    answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                    return jsonify({'status': 'ok'}), 200

            if chat_type == 'private' and not DM_GAMES_ENABLED and (callback_data.startswith("pm_again_") or callback_data.startswith("pm_double_")):
                answer_callback(callback_query_id, "❌ Games in DM are currently turned off.")
                remove_inline_keyboard(chat_id, message_id)
                send_message(chat_id, build_dm_games_off_text())
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("pm_again_") or callback_data.startswith("pm_double_"):
                is_double = callback_data.startswith("pm_double_")
                token = callback_data.replace("pm_double_", "", 1) if is_double else callback_data.replace("pm_again_", "", 1)
                payload = post_match_actions.get(token)
                if not payload:
                    answer_callback(callback_query_id, "This action has already been used or expired.")
                    remove_inline_keyboard(chat_id, message_id)
                    return jsonify({'status': 'ok'}), 200
                if user_id != payload.get("owner_id"):
                    answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                    return jsonify({'status': 'ok'}), 200
                active_summary = get_active_game_summary(user_id)
                if active_summary:
                    answer_callback(callback_query_id, f"Finish your active {active_summary} game first!")
                    return jsonify({'status': 'ok'}), 200
                post_match_actions.pop(token, None)
                factor = 2.0 if is_double else 1.0
                execute_post_match_restart(chat_id, message_id, user_id, payload, factor, callback_query_id)
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("hlp_"):
                if user_id not in admin_list:
                    answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                    return jsonify({'status': 'ok'}), 200
                note = handle_helper_button(callback_data)
                h_text, h_kb = build_helper_panel()
                edit_message(chat_id, message_id, h_text, reply_markup=h_kb)
                answer_callback(callback_query_id, note)
                return jsonify({'status': 'ok'}), 200

            answer_callback(callback_query_id)
            
            if not callback_data.startswith(("mn_", "tw_", "pf_")) and not callback_data.startswith("adm_") and not callback_data.startswith("bj_") and not callback_data.startswith("gs_") and not callback_data.startswith("rw_") and not callback_data.startswith("mc_") and not callback_data.startswith("pvp_") and not callback_data.startswith("infopg_") and not callback_data.startswith("myhistpg_"):
                remove_inline_keyboard(chat_id, message_id)
            
            register_user_identity(query.get('from'))

            if callback_data.startswith("infopg_"):
                if user_id not in admin_list:
                    pass  # normal users get no reply to admin commands
                    return jsonify({'status': 'ok'}), 200
                try:
                    _, raw_uid, section, raw_page = callback_data.split("_", 3)
                    target_uid = int(raw_uid)
                    page = int(raw_page)
                    sec_text, sec_kb = build_user_info_section_page(target_uid, section, page)
                    edit_message(chat_id, message_id, sec_text, reply_markup=sec_kb)
                except Exception as e:
                    print(f"Info pagination error: {e}")
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("myhistpg_"):
                try:
                    _, raw_uid, raw_page = callback_data.split("_", 2)
                    target_uid = int(raw_uid)
                    page = int(raw_page)
                    if user_id != target_uid and user_id not in admin_list:
                        answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                        return jsonify({'status': 'ok'}), 200
                    hist_text, hist_kb = build_user_history_page(target_uid, page=page)
                    edit_message(chat_id, message_id, hist_text, reply_markup=hist_kb)
                except Exception as e:
                    print(f"History pagination error: {e}")
                return jsonify({'status': 'ok'}), 200

            if callback_data == "gs_cancel":
                setup = pending_game_setup.pop(user_id, None)
                if setup and setup.get("game_id") in game_id_registry:
                    mark_game_finished(setup["game_id"], "cancelled")
                target_chat = (setup or {}).get("chat_id") or chat_id
                target_msg = (setup or {}).get("message_id") or message_id
                for cid, ch in list(open_pvp_challenges.items()):
                    if ch["host_id"] == user_id:
                        if ch.get("game_id"):
                            mark_game_finished(ch["game_id"], "cancelled")
                        open_pvp_challenges.pop(cid, None)
                edit_message(target_chat, target_msg, "❌ Game cancelled.")
                return jsonify({'status': 'ok'}), 200

            if callback_data in ["gs_style_crazy", "gs_style_normal"]:
                if user_id not in pending_game_setup:
                    edit_message(chat_id, message_id, "⚠️ Session expired. Start a new game command.")
                    return jsonify({'status': 'ok'}), 200
                setup = pending_game_setup[user_id]
                chosen_mode = "crazy" if callback_data == "gs_style_crazy" else "normal"
                setup["mode"] = chosen_mode
                target_chat = setup.get("chat_id") or chat_id
                target_msg = setup.get("message_id") or message_id
                target_chat_type = setup.get("chat_type") or chat_type
                setup["message_id"] = target_msg
                bet_inr = setup["bet"]
                emoji = setup["emoji"]
                gid = setup.get("game_id")
                current_bal = user_balances.get(user_id, 0.0)

                if setup.get("rw_label") in VALID_RW_MODES:
                    if bet_inr < MIN_BET or bet_inr > MAX_BET:
                        pending_game_setup.pop(user_id, None)
                        edit_message(target_chat, target_msg, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                    elif current_bal < bet_inr:
                        pending_game_setup.pop(user_id, None)
                        edit_message(
                            target_chat,
                            target_msg,
                            f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                        )
                    else:
                        conf_msg = build_match_confirmation_text(user_id, emoji, bet_inr, chosen_mode, setup["rw_label"], game_id=gid)
                        edit_message(target_chat, target_msg, conf_msg, reply_markup=match_confirm_keyboard(target_chat_type))
                    return jsonify({'status': 'ok'}), 200

                g_name = GAME_NAME_MAP.get(emoji, "Game")
                mode_title = "🔥 CRAZY MODE (Lowest Sum Wins)" if chosen_mode == "crazy" else "⚡ NORMAL MODE (Highest Sum Wins)"
                rw_msg = (
                    f"🎯 *Select RW Mode* (`{gid}` | {g_name} {emoji} | {mode_title})\n"
                    f"💰 Bet: *{format_money(bet_inr, user_id)}*\n\nTap a mode below:"
                )
                edit_message(target_chat, target_msg, rw_msg, reply_markup=rw_mode_keyboard())
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("rw_pick_"):
                chosen_rw = callback_data.replace("rw_pick_", "")
                if user_id not in pending_game_setup or chosen_rw not in VALID_RW_MODES:
                    edit_message(chat_id, message_id, "⚠️ RW selection expired. Start the game command again.")
                    return jsonify({'status': 'ok'}), 200

                setup = pending_game_setup[user_id]
                target_chat = setup.get("chat_id") or chat_id
                target_msg = setup.get("message_id") or message_id
                target_chat_type = setup.get("chat_type") or chat_type
                setup["message_id"] = target_msg
                bet_inr = setup["bet"]
                mode = setup["mode"] or "normal"
                setup["mode"] = mode
                setup["rw_label"] = chosen_rw
                emoji = setup["emoji"]
                gid = setup.get("game_id")
                current_bal = user_balances.get(user_id, 0.0)

                if bet_inr < MIN_BET or bet_inr > MAX_BET:
                    pending_game_setup.pop(user_id, None)
                    edit_message(target_chat, target_msg, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                elif current_bal < bet_inr:
                    pending_game_setup.pop(user_id, None)
                    edit_message(
                        target_chat,
                        target_msg,
                        f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                    )
                else:
                    conf_msg = build_match_confirmation_text(user_id, emoji, bet_inr, mode, chosen_rw, game_id=gid)
                    edit_message(target_chat, target_msg, conf_msg, reply_markup=match_confirm_keyboard(target_chat_type))
                return jsonify({'status': 'ok'}), 200

            if callback_data == "mc_bot":
                if user_id not in pending_game_setup:
                    edit_message(chat_id, message_id, "⚠️ Confirmation expired. Start a new game command.")
                    return jsonify({'status': 'ok'}), 200
                conf = pending_game_setup.pop(user_id)
                target_chat = conf.get("chat_id") or chat_id
                target_msg = conf.get("message_id") or message_id
                active_summary = get_active_game_summary(user_id)
                if active_summary:
                    edit_message(target_chat, target_msg, f"⚠️ You are already playing *{active_summary}*! Finish it before starting another game.")
                    return jsonify({'status': 'ok'}), 200
                bet_inr = conf["bet"]
                gid = conf.get("game_id") or generate_game_id()
                current_bal = user_balances.get(user_id, 0.0)
                if bet_inr < MIN_BET or bet_inr > MAX_BET:
                    edit_message(target_chat, target_msg, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                elif current_bal < bet_inr:
                    edit_message(
                        target_chat,
                        target_msg,
                        f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                    )
                else:
                    start_versus_match(target_chat, target_msg, user_id, conf["emoji"], bet_inr, conf["mode"] or "normal", conf["rw_label"], game_id=gid, trigger_msg_id=conf.get("trigger_msg_id"))
                return jsonify({'status': 'ok'}), 200

            if callback_data == "mc_player":
                if user_id not in pending_game_setup:
                    edit_message(chat_id, message_id, "⚠️ Confirmation expired. Start a new game command.")
                    return jsonify({'status': 'ok'}), 200
                conf = pending_game_setup.pop(user_id)
                target_chat = conf.get("chat_id") or chat_id
                target_msg = conf.get("message_id") or message_id
                target_chat_type = conf.get("chat_type") or chat_type

                if target_chat_type == "private":
                    edit_message(target_chat, target_msg, "❌ Against Player is only available in groups!")
                    return jsonify({'status': 'ok'}), 200

                active_summary = get_active_game_summary(user_id)
                if active_summary:
                    edit_message(target_chat, target_msg, f"⚠️ You are already playing *{active_summary}*! Finish it before starting a PvP challenge.")
                    return jsonify({'status': 'ok'}), 200

                bet_inr = conf["bet"]
                current_bal = user_balances.get(user_id, 0.0)
                if bet_inr < MIN_BET or bet_inr > MAX_BET:
                    edit_message(target_chat, target_msg, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                    return jsonify({'status': 'ok'}), 200
                if current_bal < bet_inr:
                    edit_message(
                        target_chat,
                        target_msg,
                        f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                    )
                    return jsonify({'status': 'ok'}), 200

                challenge_id = uuid.uuid4().hex[:8]
                gid = conf.get("game_id") or generate_game_id()
                mode = conf["mode"] or "normal"
                rw_label = conf["rw_label"] or "1r1w"
                rolls_per_round, target_wins = VALID_RW_MODES[rw_label]
                mode_label = "CRAZY (Lowest Sum Wins)" if mode == "crazy" else "NORMAL (Highest Sum Wins)"
                g_name = GAME_NAME_MAP.get(conf["emoji"], "Game")

                open_pvp_challenges[challenge_id] = {
                    "game_id": gid,
                    "chat_id": target_chat,
                    "message_id": target_msg,
                    "host_id": user_id,
                    "emoji": conf["emoji"],
                    "bet": bet_inr,
                    "mode": mode,
                    "rw_label": rw_label,
                    "rolls_per_round": rolls_per_round,
                    "target_wins": target_wins,
                }
                invite_msg = (
                    "⚔️ *Player vs Player Challenge!*\n\n"
                    f"🆔 *Game ID:* `{gid}`\n"
                    f"👤 *Challenger:* {tag_player(user_id)}\n"
                    f"🎮 *Game:* {g_name} ({conf['emoji']})\n"
                    f"⚙️ *Mode:* *{mode_label}*\n"
                    f"🏆 *RW Format:* `{rw_label}` (First to *{target_wins}*)\n"
                    f"💰 *Bet Each:* *{format_money(bet_inr, user_id)}*\n\n"
                    "Tap *Accept* to start:"
                )
                kb = {
                    "inline_keyboard": [
                        [
                            {"text": "✅ Accept Challenge", "callback_data": f"pvp_acc_{challenge_id}"},
                            {"text": "❌ Cancel", "callback_data": f"pvp_can_{challenge_id}"}
                        ]
                    ]
                }
                edit_message(target_chat, target_msg, invite_msg, reply_markup=kb)
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("pvp_can_"):
                cid = callback_data.replace("pvp_can_", "")
                ch = open_pvp_challenges.get(cid)
                if not ch:
                    edit_message(chat_id, message_id, "⚠️ Challenge already closed or expired.")
                    return jsonify({'status': 'ok'}), 200
                if user_id != ch["host_id"] and user_id not in admin_list:
                    answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                    return jsonify({'status': 'ok'}), 200
                if ch.get("game_id"):
                    mark_game_finished(ch["game_id"], "cancelled")
                open_pvp_challenges.pop(cid, None)
                edit_message(ch.get("chat_id") or chat_id, ch.get("message_id") or message_id, f"❌ PvP Challenge `{cid}` cancelled.")
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("pvp_acc_"):
                cid = callback_data.replace("pvp_acc_", "")
                ch = open_pvp_challenges.get(cid)
                if not ch:
                    edit_message(chat_id, message_id, "⚠️ Challenge already accepted or expired.")
                    return jsonify({'status': 'ok'}), 200

                host_id = ch["host_id"]
                if user_id == host_id:
                    answer_callback(callback_query_id, "You cannot accept your own challenge!")
                    return jsonify({'status': 'ok'}), 200

                active_summary = get_active_game_summary(user_id)
                if active_summary:
                    answer_callback(callback_query_id, f"Finish your active {active_summary} game first!")
                    return jsonify({'status': 'ok'}), 200

                host_active = get_active_game_summary(host_id)
                if host_active:
                    if ch.get("game_id"):
                        mark_game_finished(ch["game_id"], "cancelled")
                    open_pvp_challenges.pop(cid, None)
                    target_chat = ch.get("chat_id") or chat_id
                    target_msg = ch.get("message_id") or message_id
                    edit_message(target_chat, target_msg, f"⚠️ Challenger is already in *{host_active}*. Challenge cancelled.")
                    return jsonify({'status': 'ok'}), 200

                bet_inr = ch["bet"]
                target_chat = ch.get("chat_id") or chat_id
                target_msg = ch.get("message_id") or message_id

                if user_balances.get(host_id, 0.0) < bet_inr:
                    if ch.get("game_id"):
                        mark_game_finished(ch["game_id"], "cancelled")
                    open_pvp_challenges.pop(cid, None)
                    edit_message(target_chat, target_msg, "❌ Challenger has insufficient balance. Challenge cancelled.")
                    return jsonify({'status': 'ok'}), 200

                if user_balances.get(user_id, 0.0) < bet_inr:
                    answer_callback(callback_query_id, "Insufficient balance to accept!")
                    return jsonify({'status': 'ok'}), 200

                open_pvp_challenges.pop(cid, None)
                user_balances[host_id] = user_balances.get(host_id, 0.0) - bet_inr
                user_balances[user_id] = user_balances.get(user_id, 0.0) - bet_inr

                gid = ch.get("game_id") or generate_game_id()
                match_id = f"pvp_{cid}"
                register_game_record(
                    gid,
                    "pvp_match",
                    host_id,
                    bet_inr,
                    meta={"match_id": match_id, "p1_id": host_id, "p2_id": user_id},
                    refund_on_cancel=True
                )
                active_pvp_games[match_id] = {
                    "game_id": gid,
                    "chat_id": target_chat,
                    "p1_id": host_id,
                    "p2_id": user_id,
                    "emoji": ch["emoji"],
                    "bet": bet_inr,
                    "mode": ch["mode"],
                    "rw_label": ch["rw_label"],
                    "rolls_per_round": ch["rolls_per_round"],
                    "target_wins": ch["target_wins"],
                    "round_num": 1,
                    "p1_wins": 0,
                    "p2_wins": 0,
                    "p1_rolls": [],
                    "p2_rolls": [],
                    "turn": host_id,
                }
                active_games[host_id] = match_id
                active_games[user_id] = match_id

                start_text = (
                    f"🎮 *PvP Match Started!* (`{gid}` | {ch['emoji']} | `{ch['rw_label']}`)\n"
                    f"👤 {tag_player(host_id)} vs {tag_player(user_id)} | Bet: *{format_money(bet_inr, user_id)}*\n"
                    f"🎯 First to *{ch['target_wins']}* round win(s) | *{ch['rolls_per_round']}* roll(s)/round\n\n"
                    f"👉 *Round 1 —* {tag_player(host_id)}, *send* `{ch['emoji']}` *x{ch['rolls_per_round']} in chat!*"
                )
                edit_message(target_chat, target_msg, start_text)
                schedule_pvp_turn_timeout(target_chat, match_id, active_pvp_games[match_id])
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith(("mn_", "tw_", "pf_")):
                handle_fair_callback(chat_id, message_id, user_id, callback_data)
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("bj_"):
                if user_id not in active_bj_games:
                    edit_message(chat_id, message_id, "⚠️ Blackjack session expired. Start a new game with `/bj <amount>`.")
                    return jsonify({'status': 'ok'}), 200

                bj = active_bj_games[user_id]
                target_chat = bj.get("chat_id") or chat_id
                target_msg = bj.get("message_id") or message_id

                if callback_data == "bj_hit":
                    bj["player_cards"].append(bj_draw(bj))
                    p_tot = calculate_hand_total(bj["player_cards"])
                    if p_tot > 21:
                        finish_bj_game(target_chat, target_msg, user_id, bj, "bust")
                    elif p_tot == 21:
                        play_dealer_and_settle(target_chat, target_msg, user_id, bj)
                    else:
                        msg = (
                            f"🃏 *Blackjack (Hit)* (`{bj.get('game_id')}`)\n\n"
                            f"👤 Your Hand: {format_cards(bj['player_cards'])} (*{p_tot}*)\n"
                            f"🤖 Dealer Shows: `{bj['dealer_cards'][0]}` `[?]`\n"
                            f"💰 Bet: {format_money(bj['bet'], user_id)}\n\n"
                            f"Choose your next move:" + bj_fair_footer(bj)
                        )
                        edit_message(target_chat, target_msg, msg, reply_markup=bj_action_keyboard(can_double=False))

                elif callback_data == "bj_stand":
                    play_dealer_and_settle(target_chat, target_msg, user_id, bj)

                elif callback_data == "bj_double":
                    extra_bet = bj["bet"]
                    if user_balances.get(user_id, 0.0) < extra_bet:
                        p_tot = calculate_hand_total(bj["player_cards"])
                        msg = (
                            f"🃏 *Blackjack* (`{bj.get('game_id')}`)\n\n"
                            f"👤 Your Hand: {format_cards(bj['player_cards'])} (*{p_tot}*)\n"
                            f"🤖 Dealer Shows: `{bj['dealer_cards'][0]}` `[?]`\n"
                            f"💰 Bet: {format_money(bj['bet'], user_id)}\n\n"
                            f"❌ Insufficient balance to Double! Choose Hit or Stand:" + bj_fair_footer(bj)
                        )
                        edit_message(target_chat, target_msg, msg, reply_markup=bj_action_keyboard(can_double=False))
                        return jsonify({'status': 'ok'}), 200

                    user_balances[user_id] = user_balances.get(user_id, 0.0) - extra_bet
                    bj["bet"] += extra_bet
                    bj["doubled"] = True
                    bj["player_cards"].append(bj_draw(bj))
                    p_tot = calculate_hand_total(bj["player_cards"])

                    if p_tot > 21:
                        finish_bj_game(target_chat, target_msg, user_id, bj, "bust")
                    else:
                        play_dealer_and_settle(target_chat, target_msg, user_id, bj)

                return jsonify({'status': 'ok'}), 200
                
            if callback_data == "curr_inr":
                user_currency[user_id] = 'INR'
                persist_user(user_id)
                send_message(chat_id, "✅ Currency successfully set to *INR (₹)*!")
            elif callback_data == "curr_usdt":
                user_currency[user_id] = 'USDT'
                persist_user(user_id)
                send_message(chat_id, "✅ Currency successfully set to *USD ($)*!")
                
            elif callback_data == "btn_deposit":
                if chat_type != 'private':
                    send_message(chat_id, f"❌ Deposit can only be done in Bot's DM!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                    return jsonify({'status': 'ok'}), 200

                if not DEPOSIT_ENABLED:
                    send_message(chat_id, "❌ Deposits are currently disabled by Admin.")
                    return jsonify({'status': 'ok'}), 200
                deposit_states[user_id] = True
                send_message(chat_id, "💳 *Please enter the amount you want to deposit (e.g. 200):*")
                
            elif callback_data == "btn_withdraw":
                if chat_type != 'private':
                    send_message(chat_id, f"❌ Withdrawal can only be done in Bot's DM!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                    return jsonify({'status': 'ok'}), 200

                if not WITHDRAW_ENABLED:
                    send_message(chat_id, "❌ Withdrawals are currently disabled by Admin.")
                    return jsonify({'status': 'ok'}), 200
                withdrawal_states[user_id] = {'step': 'waiting_amount'}
                send_message(chat_id, "💸 *Withdrawal Flow*\n\nPlease enter the amount you want to withdraw:")
                
            elif callback_data.startswith("adm_"):
                if user_id not in admin_list:
                    pass  # normal users get no reply to admin commands
                    return jsonify({'status': 'ok'}), 200
                    
                if callback_data == "adm_add_bal":
                    admin_states[user_id] = {'action': 'add_bal'}
                    send_message(chat_id, "➕ *Enter User ID and Amount to add*\nFormat: `<user_id> <amount>`")
                elif callback_data == "adm_deduct_bal":
                    admin_states[user_id] = {'action': 'deduct_bal'}
                    send_message(chat_id, "➖ *Enter User ID and Amount to deduct*\nFormat: `<user_id> <amount>`")
                elif callback_data == "adm_user_stats":
                    admin_states[user_id] = {'action': 'user_stats'}
                    send_message(chat_id, "📊 *Enter User ID to view stats:*")
                elif callback_data == "adm_users":
                    txt = "👥 *Registered Users & Balances:*\n"
                    for uid, bal in user_balances.items():
                        status = "🔴 BANNED" if uid in banned_users else "🟢 Active"
                        txt += f"- `{uid}`: {format_money(bal, uid)} [{status}]\n"
                    send_message(chat_id, txt)
                elif callback_data == "adm_ban":
                    admin_states[user_id] = {'action': 'ban_user'}
                    send_message(chat_id, "🚫 *Enter User ID to Ban:*")
                elif callback_data == "adm_unban":
                    admin_states[user_id] = {'action': 'unban_user'}
                    send_message(chat_id, "✅ *Enter User ID to Unban:*")
                elif callback_data == "adm_last_dep":
                    txt = "📥 *Last 50 Deposits:*\n"
                    for d in deposit_history[-50:]:
                        t_str = f" [{d['time']}]" if d.get("time") else ""
                        txt += f"- User `{d['user']}`: {format_money(d['amount'], d['user'])} (UTR: `{d['utr']}`){t_str}\n"
                    if not deposit_history: txt += "No deposits recorded yet."
                    send_message(chat_id, txt)
                elif callback_data == "adm_last_wd":
                    txt = "📤 *Last 50 Withdrawals:*\n"
                    for w in withdrawal_history[-50:]:
                        t_str = f" [{w['time']}]" if w.get("time") else ""
                        txt += f"- User `{w['user']}`: {format_money(w['amount'], w['user'])} to `{w['upi']}`{t_str}\n"
                    if not withdrawal_history: txt += "No withdrawals recorded yet."
                    send_message(chat_id, txt)
                elif callback_data == "adm_grant":
                    admin_states[user_id] = {'action': 'grant_admin'}
                    send_message(chat_id, "👑 *Enter User ID to grant Admin rights:*")
                elif callback_data == "adm_revoke":
                    admin_states[user_id] = {'action': 'revoke_admin'}
                    send_message(chat_id, "⛔ *Enter User ID to revoke Admin rights:*")
                elif callback_data == "adm_bc_all":
                    admin_states[user_id] = {'action': 'broadcast_all'}
                    send_message(chat_id, "📢 *Enter message to broadcast to all users:*")
                elif callback_data == "adm_bc_priv":
                    admin_states[user_id] = {'action': 'broadcast_private'}
                    send_message(chat_id, "💬 *Enter User ID and Message*\nFormat: `<user_id> <message>`")
                elif callback_data == "adm_toggle_maint":
                    MAINTENANCE_MODE = not MAINTENANCE_MODE
                    send_message(chat_id, f"🛠 Maintenance Mode is now: {'🔴 ON' if MAINTENANCE_MODE else '🟢 OFF'}")
                elif callback_data == "adm_toggle_dep":
                    DEPOSIT_ENABLED = not DEPOSIT_ENABLED
                    send_message(chat_id, f"💳 Deposits are now: {'🟢 Enabled' if DEPOSIT_ENABLED else '🔴 Disabled'}")
                elif callback_data == "adm_toggle_wd":
                    WITHDRAW_ENABLED = not WITHDRAW_ENABLED
                    send_message(chat_id, f"💸 Withdrawals are now: {'🟢 Enabled' if WITHDRAW_ENABLED else '🔴 Disabled'}")
                
            elif callback_data == "wd_cancel":
                if user_id in withdrawal_states:
                    user_balances[user_id] = user_balances.get(user_id, 0.0) + withdrawal_states[user_id].get('amount', 0)
                    del withdrawal_states[user_id]
                send_message(chat_id, "❌ Withdrawal request cancelled. Funds refunded.")
                
            elif callback_data == "wd_confirm":
                if user_id in withdrawal_states:
                    st = withdrawal_states[user_id]
                    raw_amt = st['amount']
                    if user_balances.get(user_id, 0.0) < raw_amt:
                        send_message(chat_id, "❌ Insufficient balance.")
                        del withdrawal_states[user_id]
                        return jsonify({'status': 'ok'}), 200
                        
                    user_balances[user_id] = user_balances.get(user_id, 0.0) - raw_amt
                    if user_id not in user_withdrawals: user_withdrawals[user_id] = 0.0
                    user_withdrawals[user_id] += raw_amt
                    
                    ts_wd = current_timestamp()
                    withdrawal_history.append({
                        'user': user_id,
                        'amount': raw_amt,
                        'upi': st['upi_id'],
                        'time': ts_wd
                    })
                    persist_withdrawal(user_id, raw_amt, st['upi_id'], ts_wd)
                    persist_user(user_id)
                    
                    amt_str = format_money(raw_amt, user_id)
                    upi_id = st['upi_id']
                    
                    send_message(chat_id, "📤 *Withdrawal Request Submitted!*\n\nYour request has been sent to the admin for verification. You will be notified once processed.")
                    
                    admin_msg = (
                        "🚨 *NEW WITHDRAWAL REQUEST*\n\n"
                        f"👤 User ID: `{user_id}`\n"
                        f"💰 Amount: *{amt_str}*\n"
                        f"🏦 UPI ID: `{upi_id}`"
                    )
                    channel_log_msg = (
                        "🚨 *NEW WITHDRAWAL REQUEST*\n\n"
                        f"👤 User ID: `{mask_user_id_for_log(user_id)}`\n"
                        f"💰 Amount: *{amt_str}*\n"
                        f"🏦 UPI ID: `{mask_upi_id_for_log(upi_id)}`"
                    )
                    admin_keyboard = {
                        "inline_keyboard": [
                            [
                                {"text": "✅ Paid", "callback_data": f"admin_wd_paid_{user_id}_{raw_amt}"},
                                {"text": "❌ Reject", "callback_data": f"admin_wd_reject_{user_id}_{raw_amt}"}
                            ]
                        ]
                    }
                    send_message(ADMIN_USER_ID, admin_msg, reply_markup=admin_keyboard)
                    withdraw_log_channel = normalize_channel_id(WITHDRAW_LOG_CHANNEL_ID)
                    if withdraw_log_channel:
                        send_message(withdraw_log_channel, channel_log_msg)
                    del withdrawal_states[user_id]
                
            elif callback_data.startswith("admin_wd_paid_") or callback_data.startswith("admin_wd_reject_"):
                if user_id in admin_list:
                    parts = callback_data.split('_')
                    action = parts[2]
                    target_user = int(parts[3])
                    raw_amt = float(parts[4])
                    amt_str = format_money(raw_amt, target_user)
                    
                    if action == "paid":
                        success_msg = (
                            "🎉 *Withdrawal Approved & Paid!* ✨\n\n"
                            f"Dear User, your withdrawal of *{amt_str}* has been successfully processed and transferred to your account/UPI ID. 🚀\n\n"
                            f"Thank you for playing with *{BOT_USERNAME}*! 🎰"
                        )
                        send_message(target_user, success_msg)
                        send_message(chat_id, f"✅ Successfully marked withdrawal for user `{target_user}` as Paid.")
                    elif action == "reject":
                        withdrawal_states[user_id] = {
                            'step': 'waiting_reject_reason',
                            'target_user': target_user,
                            'raw_amount': raw_amt,
                            'amount_str': amt_str
                        }
                        send_message(chat_id, f"✍️ *Please enter the rejection reason for user `{target_user}` in chat:*")
                else:
                    pass  # normal users get no reply to admin commands
                
            elif callback_data == "play_bot_first":
                remove_inline_keyboard(chat_id, message_id)
                with get_turn_lock(f"pvb_{user_id}"):
                    if user_id not in active_games or isinstance(active_games[user_id], str):
                        send_message(chat_id, "⚠️ Session expired. Start a new game.")
                        return jsonify({'status': 'ok'}), 200
                        
                    game = active_games[user_id]
                    if game.get("step") != "selecting_turn":
                        return jsonify({'status': 'ok'}), 200
                    game["turn_token"] = None
                    game["start_message_id"] = None
                    emoji = game["emoji"]
                    rolls_needed = game["rolls_per_round"]
                    game["current_user_rolls"] = []
                    game["current_bot_rolls"] = []
                    
                    game["first_turn"] = "bot"
                    game["step"] = "waiting_user_second"
                    player_tag = format_user_mention(user_id)
                    trig_id = game.get("trigger_msg_id")
                    send_message(chat_id, f"🤖 Bot is throwing `{emoji}` x{rolls_needed} first for {player_tag}...", reply_to_message_id=trig_id)
                    
                    b_vals = roll_bot_series(chat_id, emoji, rolls_needed, reply_to_message_id=trig_id)
                    game["current_bot_rolls"] = b_vals
                    b_expr = "+".join(map(str, b_vals))
                    
                    send_message(chat_id, f"🤖 Bot Roll: `{b_expr}` (*{sum(b_vals)}*)\n\n👉 *Now* {tag_player(user_id)}*'s turn! Send `{emoji}` x{rolls_needed} in chat.*")
                    schedule_pvb_turn_timeout(chat_id, user_id, game)
                
        return jsonify({'status': 'ok'}), 200
    except Exception as e:
        print(f"❌ Webhook Error: {e}")
        return jsonify({'status': 'error', 'message': str(e)}), 200


# ===================== 🤖 /helper COMMAND + HELPER WEBHOOK =====================
def _public_base_url():
    env = os.environ.get("PUBLIC_URL")
    if env:
        return env.rstrip("/")
    host = request.headers.get("X-Forwarded-Host") or request.host
    return f"https://{host}"

def helper_set_hook(h, base_url):
    """Button taps on helper messages (Bet Again / Bet Double) come back to this server."""
    data = _helper_post(h, "setWebhook", {
        "url": f"{base_url}/helper-webhook/{h['id']}",
        "secret_token": helper_hook_secret(h["token"]),
        "allowed_updates": ["callback_query"],
        "drop_pending_updates": True,
    }, timeout=10)
    h["hook"] = bool(data and data.get("ok"))
    return h["hook"]

def build_helper_panel():
    on_count = sum(1 for h in HELPER_BOTS if h.get("enabled"))
    lines = [f"🤖 *Helper Bots* ({len(HELPER_BOTS)}/{MAX_HELPERS}) · {on_count} ON", ""]
    if not HELPER_BOTS:
        lines.append("No helper added yet. Main bot is throwing emojis itself.")
    for i, h in enumerate(HELPER_BOTS, 1):
        state = "🟢 ON" if h.get("enabled") else "🔴 OFF"
        btn = "" if h.get("hook") else " · ⚠️ buttons not linked"
        lines.append(f"{i}. @{_md_safe(h.get('username'))} — {state}{btn}")
    lines += [
        "",
        "Helpers throw every emoji in groups and send the round / final round messages.",
        "Main bot throws only in DMs, or as backup if no helper can.",
        "",
        "`/helper add <token>` — add (send in bot DM)",
        "`/helper remove 1` · `/helper on 1` · `/helper off 1`",
        "`/helper on all` · `/helper off all`",
        "`/helper test` — send in the group to check helpers",
    ]
    rows = []
    for i, h in enumerate(HELPER_BOTS, 1):
        rows.append([
            {"text": f"{i}. @{h.get('username')} {'🟢 ON' if h.get('enabled') else '🔴 OFF'}", "callback_data": f"hlp_tg_{h['id']}"},
            {"text": "🗑 Remove", "callback_data": f"hlp_rm_{h['id']}"},
        ])
    return "\n".join(lines), ({"inline_keyboard": rows} if rows else None)

def _find_helper(ref):
    ref = str(ref or "").strip().lstrip("@").lower()
    if ref.isdigit() and 1 <= int(ref) <= len(HELPER_BOTS):
        return HELPER_BOTS[int(ref) - 1]
    for h in HELPER_BOTS:
        if str(h.get("username", "")).lower() == ref or str(h.get("id")) == ref:
            return h
    return None

def _remove_helper(h):
    _helper_post(h, "deleteWebhook", {"drop_pending_updates": True})
    if h in HELPER_BOTS:
        HELPER_BOTS.remove(h)
    save_helpers()

def handle_helper_button(data):
    try:
        hid = int(data.rsplit("_", 1)[1])
    except Exception:
        return "Expired."
    h = next((x for x in HELPER_BOTS if x.get("id") == hid), None)
    if not h:
        return "Helper already removed."
    if data.startswith("hlp_tg_"):
        h["enabled"] = not h.get("enabled")
        save_helpers()
        return f"@{h.get('username')} is now {'ON' if h['enabled'] else 'OFF'}"
    if data.startswith("hlp_rm_"):
        _remove_helper(h)
        return f"@{h.get('username')} removed"
    return ""

def handle_helper_command(chat_id, chat_type, text, message):
    parts = text.split()
    sub = parts[1].lower() if len(parts) > 1 else ""
    arg = parts[2] if len(parts) > 2 else ""

    if sub == "add":
        if chat_type != "private":
            try:
                requests.post(f"{TELEGRAM_API_URL}/deleteMessage", json={"chat_id": chat_id, "message_id": message.get("message_id")}, timeout=3)
            except Exception:
                pass
            send_message(chat_id, "🔒 Never send a bot token in a group. Send `/helper add <token>` in my DM.\nIf others saw it, open @BotFather → /revoke for that bot and use the new token.")
            return
        token = arg.strip()
        if not re.match(r"^\d{5,}:[A-Za-z0-9_-]{30,}$", token):
            send_message(chat_id, "⚠️ Usage: `/helper add <bot token>`\nCreate a new bot in @BotFather (/newbot) and paste its token here.")
            return
        if TELEGRAM_BOT_TOKEN and token.split(":")[0] == str(TELEGRAM_BOT_TOKEN).split(":")[0]:
            send_message(chat_id, "⚠️ That is the main bot's own token. Use a new bot from @BotFather.")
            return
        if any(h.get("token") == token or str(h.get("id")) == token.split(":")[0] for h in HELPER_BOTS):
            send_message(chat_id, "⚠️ This helper is already added.")
            return
        if len(HELPER_BOTS) >= MAX_HELPERS:
            send_message(chat_id, f"⚠️ Max {MAX_HELPERS} helpers. Remove one first with `/helper remove <number>`.")
            return
        try:
            me = requests.get(f"https://api.telegram.org/bot{token}/getMe", timeout=8).json()
        except Exception:
            me = None
        if not me or not me.get("ok") or not (me.get("result") or {}).get("is_bot"):
            send_message(chat_id, "❌ Token not working. Copy it again from @BotFather.")
            return
        r = me["result"]
        h = {"id": r["id"], "username": r.get("username") or str(r["id"]), "token": token, "enabled": True, "hook": False}
        hook_ok = helper_set_hook(h, _public_base_url())
        HELPER_BOTS.append(h)
        save_helpers()
        n = len(HELPER_BOTS)
        uname = _md_safe(h["username"])
        msg = (
            f"✅ *Helper {n} added:* @{uname} (🟢 ON)\n\n"
            f"Next step: add @{uname} to your game group(s).\n"
            "If members can't send stickers/GIFs in that group, make the helper an admin.\n"
            "Then send `/helper test` in the group."
        )
        if not hook_ok:
            msg += "\n\n⚠️ Could not link its buttons — final round messages with buttons will be sent by the main bot. Try `/helper add` again later."
        send_message(chat_id, msg)
        return

    if sub in ("remove", "del", "delete", "rm"):
        h = _find_helper(arg)
        if not h:
            send_message(chat_id, "⚠️ Usage: `/helper remove <number>` (see `/helper`)")
            return
        _remove_helper(h)
        send_message(chat_id, f"🗑 Helper @{_md_safe(h.get('username'))} removed.")
        return

    if sub in ("on", "off"):
        want = sub == "on"
        targets = HELPER_BOTS if arg.lower() == "all" else [x for x in [_find_helper(arg)] if x]
        if not targets:
            send_message(chat_id, f"⚠️ Usage: `/helper {sub} <number>` or `/helper {sub} all`")
            return
        for h in targets:
            h["enabled"] = want
            if want:
                _helper_cooldown.pop(h.get("id"), None)
                for k in [k for k in _helper_chat_block if k[0] == h.get("id")]:
                    _helper_chat_block.pop(k, None)
        save_helpers()
        names = ", ".join("@" + _md_safe(h.get("username")) for h in targets)
        send_message(chat_id, f"{'🟢' if want else '🔴'} {names} {'ON' if want else 'OFF'}.")
        return

    if sub == "test":
        if chat_type == "private":
            send_message(chat_id, "ℹ️ Send `/helper test` inside the game group.")
            return
        report = []
        for i, h in enumerate(HELPER_BOTS, 1):
            uname = _md_safe(h.get("username"))
            if not h.get("enabled"):
                report.append(f"{i}. @{uname} — 🔴 OFF")
                continue
            _helper_chat_block.pop((h.get("id"), chat_id), None)
            data = _helper_post(h, "sendMessage", {"chat_id": chat_id, "text": f"🤖 Helper {i} ready ✅"})
            if data and data.get("ok"):
                report.append(f"{i}. @{uname} — ✅ ready")
            else:
                why = (data or {}).get("description", "no reply")
                report.append(f"{i}. @{uname} — ❌ {_md_safe(why)}")
        if not report:
            report.append("No helpers added. Use `/helper add <token>` in my DM.")
        send_message(chat_id, "🧪 *Helper test*\n" + "\n".join(report))
        return

    p_text, p_kb = build_helper_panel()
    send_message(chat_id, p_text, reply_markup=p_kb)

@app.route('/helper-webhook/<int:helper_id>', methods=['POST'])
def helper_webhook(helper_id):
    """Button taps on messages a helper sent arrive here and are handled exactly
    like main-bot taps, but the replies go out through that helper."""
    h = next((x for x in HELPER_BOTS if x.get("id") == helper_id), None)
    if not h:
        return jsonify({'status': 'ok'}), 200
    got = request.headers.get("X-Telegram-Bot-Api-Secret-Token", "")
    if not _hb_hmac.compare_digest(got, helper_hook_secret(h["token"])):
        return "Unauthorized", 401
    data = request.get_json(silent=True) or {}
    if 'callback_query' not in data:
        return jsonify({'status': 'ok'}), 200
    prev = getattr(_tg_ctx, "api", None)
    _tg_ctx.api = helper_api(h)
    try:
        return telegram_webhook()
    finally:
        _tg_ctx.api = prev

@app.route('/zapupi-webhook', methods=['POST'])
def zapupi_webhook():
    try:
        data = request.get_json()
        if not data: 
            return jsonify({'status': 'error', 'message': 'No data'}), 400
        
        order_id = data.get('order_id')
        status = data.get('status')
        amount = float(data.get('amount', 0))
        utr = data.get('utr', '')
        
        if status and status.lower() == 'success':
            remark = data.get('remark', '')
            chat_id = None
            
            if '|' in remark:
                parts = remark.split('|')
                for p in parts:
                    if p.isdigit():
                        chat_id = int(p)
                        break
            elif remark.isdigit():
                chat_id = int(remark)
                
            if chat_id:
                if chat_id not in user_balances: 
                    user_balances[chat_id] = 0.0
                    user_currency[chat_id] = 'INR'
                user_balances[chat_id] += amount
                
                if chat_id not in user_deposits: user_deposits[chat_id] = 0.0
                user_deposits[chat_id] += amount
                
                ts_dep = current_timestamp()
                deposit_history.append({
                    'user': chat_id,
                    'amount': amount,
                    'utr': utr,
                    'time': ts_dep
                })
                persist_deposit(chat_id, amount, utr, ts_dep)
                persist_user(chat_id)
                
                success_msg = f"✅ *Deposit Successful!* 🎉\n\nAdded: {format_money(amount, chat_id)}\nNew Balance: {format_money(user_balances[chat_id], chat_id)}\nOrder ID: `{order_id}`\nUTR: `{utr}`"
                send_message(chat_id, success_msg)
                    
        return jsonify({'status': 'ok'}), 200
    except Exception as e:
        print(f"❌ ZapUPI Webhook Error: {e}")
        return jsonify({'status': 'error', 'message': str(e)}), 200


init_db()
load_all_from_db()
init_fair_db()
load_fair_from_db()

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
