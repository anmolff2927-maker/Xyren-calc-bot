import os
import re
import logging
from flask import Flask, request, jsonify

app = Flask(__name__)

# LOGGING
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# API SETTINGS
TELEGRAM_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
TELEGRAM_URL = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"

def send_message(chat_id, text):
    try:
        import requests
        response = requests.post(
            TELEGRAM_URL,
            json={
                "chat_id": chat_id,
                "text": text
            },
            timeout=20
        )
        return response.ok
    except Exception:
        logger.exception("Telegram send error")
        return False

def calculate(expression):
    # Security: Allow only numbers and basic math operators
    if not re.match(r"^[\d\+\-\*\/\.\(\)\s]+$", expression):
        return "Please send a valid math expression (e.g., 20+35, 45*7)"
    
    try:
        result = eval(expression, {"__builtins__": None}, {})
        return str(result)
    except ZeroDivisionError:
        return "Error: Division by zero is not allowed!"
    except Exception:
        return "Error in calculation. Please check your expression."

@app.route("/", methods=["GET"])
def home():
    return "Xyren Calculator Bot is running!"

@app.route("/health", methods=["GET"])
def health():
    return jsonify({"status": "online", "bot": "Xyren Calculator Bot"})

@app.route("/webhook", methods=["POST"])
def webhook():
    if not TELEGRAM_TOKEN:
        return jsonify({"error": "Bot token missing"}), 500

    try:
        update = request.get_json(silent=True) or {}
        message = update.get("message", {})

        if not message:
            return jsonify({"ok": True})

        chat_id = message.get("chat", {}).get("id")
        text = message.get("text", "").strip()

        if not chat_id or not text:
            return jsonify({"ok": True})

        # START COMMAND WITH YOUR CUSTOM MESSAGE
        if text == "/start":
            send_message(
                chat_id,
                "Hy there,\n\n"
                "I am xyren Calculator 🤖\n"
                "You can use me as a calculator\n"
                "You can ask me quies like 20+35,45*7 etc...."
            )
            return jsonify({"ok": True})

        # CALCULATE RESULT DIRECTLY
        answer = calculate(text)
        send_message(chat_id, f"ans: {answer}")

        return jsonify({"ok": True})

    except Exception:
        logger.exception("Webhook error")
        return jsonify({"ok": True})

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
  
