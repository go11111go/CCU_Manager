# -*- coding: utf-8 -*-
# ============================================================
# CCU MANAGER v1.3.1 (Updated - restored full implementation)
# - Atomic refresh_servers (rebuild + _refresh_in_progress)
# - Restored ConfigEditorCCU visual editor
# - All previously implemented logic preserved (fallen_tracked, restore limits, UI, etc.)
# ============================================================

import ctypes
import json
import os
import random
import re
import socket
import threading
import time
import webbrowser
import sys
import traceback
from datetime import datetime
from typing import Any, Dict, List, Optional, Tuple, Set
from tkinter import simpledialog
from datetime import timedelta

import requests
import tkinter as tk
import tkinter.font as tkfont
from tkinter import ttk, messagebox, scrolledtext

# Friendly constant for "Статус" using Unicode escapes to avoid encoding issues
STATUS_TEXT = "\u0421\u0442\u0430\u0442\u0443\u0441"

# --- DPI awareness ---
try:
    ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception:
    try:
        ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass

# --- App directories ---
APP_DIR = os.path.dirname(os.path.abspath(__file__))
SETTINGS_DIR = os.path.join(APP_DIR, "settings")
BACKUPS_DIR = os.path.join(APP_DIR, "backups")
LOGS_DIR = os.path.join(APP_DIR, "logs")

for _d in (SETTINGS_DIR, BACKUPS_DIR, LOGS_DIR):
    try:
        os.makedirs(_d, exist_ok=True)
    except Exception:
        pass

# --- Config files ---
CONFIG_CCU = os.path.join(SETTINGS_DIR, "config_ccu.json")
TEMPLATES_PEAKS = os.path.join(SETTINGS_DIR, "templates_peaks.json")
SESSION_STATE_FILE = os.path.join(SETTINGS_DIR, "ccu_session_state.json")
CCU_LOG_FILE = os.path.join(LOGS_DIR, "ccu_manager.log")
DEFAULT_IPC_PASSWORD = "1"

# ============================================================
# STATUS ICONS (Base64 PNG)
# ============================================================

STATUS_ICONS_B64 = {
    "green": b"iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAAUklEQVR4nGNgGGjAiFPmDMN/DDETTPVMRGvGIY5pAC7NOOSZ8EkSYwgTNkFSDMEeBiSAYWUAlkSCF0DVM2ETJFYzpgHEGIImjz0McBlCqjeJAQBEvhIaFzNxxgAAAABJRU5ErkJggg==",
    "yellow": b"iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAAU0lEQVR4nN2SOw4AIAhDkUN6SC+Jk4u0pEwmduznJRLNXmuwIJZFKs/cd3XM/ARgY5Z7FSoQR2YHAm/Q0U8A9Ekqnb4jUx0ngAK5c3gDBuk+U9IG05sbGvHyZTAAAAAASUVORK5CYII=",
    "red": b"iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAAVUlEQVR4nGNgGGjAiEviv7HxfwzFZ89iqGciVjMucQwDcGnGJc+ET5IYQ5iwCZJiCNYwIAUMJwOwJRJ8AKaeCZsgsZoxDCDGEHR5rGGAyxBSvUkUAADgliQaQfNU8gAAAABJRU5ErkJggg==",
    "gray": b"iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAAVElEQVR4nGNgGGjAiEuioaHhPxYxDPVMxGrGJY5hAC7NuOSZ8EkSYwgTNkFSDMEaBqSA4WQAtkSCD8DUo0cjUYYgq8OWkPAagi6PKyljNYRUbxIFAJmQJBqp9MVOAAAAAElFTkSuQmCC"
}


def _init_status_icons(master):
    """Initialize status icons from base64 data."""
    icons = {}
    for key, b64_data in STATUS_ICONS_B64.items():
        try:
            b64_str = b64_data.decode("ascii")
            icons[key] = tk.PhotoImage(master=master, data=b64_str)
        except Exception:
            icons[key] = tk.PhotoImage(master=master)
    return icons


# ============================================================
# UTILITY
# ============================================================

class GameNameCache:
    """Thread-safe singleton cache for Steam game names."""
    _instance = None
    _lock = threading.Lock()
    
    def __new__(cls):
        if cls._instance is None:
            with cls._lock:
                # Double-check locking pattern
                if cls._instance is None:
                    cls._instance = super().__new__(cls)
                    cls._instance._cache = {}
                    cls._instance._cache_lock = threading.Lock()
        return cls._instance
    
    def get(self, app_id: int, timeout=2):
        """Get game name from cache or fetch from Steam API."""
        with self._cache_lock:
            if app_id in self._cache:
                return self._cache[app_id]
        
        try:
            url = "https://store.steampowered.com/api/appdetails"
            resp = requests.get(
                url,
                params={"appids": app_id, "l": "ru"},
                timeout=timeout
            )
            data = resp.json()
            app_data = data.get(str(app_id), {})
            if app_data.get("success"):
                name = app_data["data"].get("name")
                if name:
                    with self._cache_lock:
                        self._cache[app_id] = name
                    return name
        except Exception as e:
            print(f"Warning: Failed to fetch game name for app_id {app_id}: {e}")
        
        return None


# Module-level singleton instance for efficient access
_game_name_cache_instance = GameNameCache()


def get_game_name(app_id: int, timeout=2):
    """Fetch game name from Steam API with caching."""
    return _game_name_cache_instance.get(app_id, timeout)


def _now_ts() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def _ensure_http(url: str) -> str:
    """Ensure URL has http:// or https:// prefix."""
    u = (url or "").strip()
    if not u:
        return u
    if re.match(r"^https?://", u, flags=re.IGNORECASE):
        return u
    return "http://" + u


def _make_request(method: str, base_url: str, path: str, ipc_password: str, 
                   timeout: int = 10, json_payload=None):
    """
    Helper to make HTTP requests and handle common error cases.
    Returns (success: bool, response_or_none, data_or_none, error_message_or_none).
    - On connection error: (False, None, None, error_message)
    - On JSON parse error: (False, response, None, error_message)
    - On success: (True, response, data, None)
    """
    url = _ensure_http(base_url).rstrip("/") + path
    headers = _auth_headers(ipc_password)
    
    try:
        if method.upper() == "POST":
            resp = requests.post(url, headers=headers, json=json_payload, timeout=timeout)
        else:  # GET
            resp = requests.get(url, headers=headers, timeout=timeout)
    except requests.RequestException as e:
        return False, None, None, f"Connection error: {e}"
    
    try:
        data = resp.json()
        return True, resp, data, None
    except (ValueError, requests.exceptions.JSONDecodeError) as e:
        return False, resp, None, f"Invalid JSON (HTTP {resp.status_code}): {resp.text[:300]}"




def _fmt_duration(seconds: int) -> str:
    seconds = max(0, int(seconds))
    if seconds >= 3600:
        h = seconds // 3600
        m = (seconds % 3600) // 60
        return f"{h} ч. {m:02d} мин."
    m = seconds // 60
    s = seconds % 60
    return f"{m} мин. {s:02d} сек."


def _time_to_seconds(time_str: str) -> int:
    try:
        parts = time_str.split(":")
        if len(parts) != 2:
            return 0
        h, m = int(parts[0]), int(parts[1])
        return h * 3600 + m * 60
    except Exception:
        return 0


def _time_until(target_time_str: str) -> int:
    now = datetime.now()
    target_sec = _time_to_seconds(target_time_str)
    now_sec = now.hour * 3600 + now.minute * 60 + now.second
    if target_sec > now_sec:
        result = target_sec - now_sec
    else:
        result = 86400 - now_sec + target_sec
    return result


# ============================================================
# CONFIG
# ============================================================

def load_json_config(path: str, default_obj: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    if default_obj is None:
        default_obj = {}
    if not os.path.exists(path):
        try:
            os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        except Exception:
            pass
        with open(path, "w", encoding="utf-8") as f:
            json.dump(default_obj, f, ensure_ascii=False, indent=4)
        return default_obj.copy()
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            return data
    except Exception as e:
        print(f"Warning: Failed to load config from {path}: {e}")
    try:
        bak = path + ".broken_" + datetime.now().strftime("%Y%m%d_%H%M%S") + ".bak"
        if os.path.exists(path):
            try:
                os.replace(path, bak)
            except Exception as e:
                print(f"Warning: Failed to backup broken config {path}: {e}")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(default_obj, f, ensure_ascii=False, indent=4)
    except Exception as e:
        print(f"Error: Failed to recreate config {path}: {e}")
    return default_obj.copy()


def save_json_config(path: str, obj: Dict[str, Any]) -> None:
    """Save JSON config with atomic write for data safety."""
    try:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    except Exception as e:
        print(f"Warning: Failed to create config directory for {path}: {e}")
    tmp = path + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(obj, f, ensure_ascii=False, indent=4)
        os.replace(tmp, path)
    except Exception as e:
        print(f"Error: Failed to save config to {path}: {e}")


def default_config_ccu() -> Dict[str, Any]:
    return {
        "ipc_password": DEFAULT_IPC_PASSWORD,
        "game_id": 730,
        "peak": 500,
        "bottom": 150,
        "time_peak": "20:00",
        "time_bottom": "06:00",
        "base_days": 7,
        "randomize": {
            "enabled": False,
            "type": "percentage",
            "min": -15,
            "max": 15
        },
        "delay": {
            "enabled": False,
            "delay_after_peak": "00:00",
            "delay_after_bottom": "00:00"
        },
        "gradual_decay": {
            "enabled": False,
            "additional_days": []
        },
        "instances": [
            {"name": "GAME_1", "url": "localhost:1001", "active": True}
        ]
    }


# ============================================================
# ASF API HELPERS
# ============================================================

def _auth_headers(ipc_password: str) -> Dict[str, str]:
    headers = {"Accept": "application/json", "Content-Type": "application/json; charset=utf-8"}
    if ipc_password:
        headers["Authentication"] = ipc_password
    return headers


def send_command(base_url: str, command: str, ipc_password: str, timeout: int = 10) -> Tuple[bool, str]:
    """Send command to ASF API."""
    payload = {"Command": command}
    success, resp, data, error_msg = _make_request("POST", base_url, "/Api/Command", ipc_password, timeout, payload)
    
    if not success:
        return False, error_msg
    
    cmd_success = bool(data.get("Success", resp.ok))
    message = data.get("Message")
    cmd_result = data.get("Result")
    parts: List[str] = [f"HTTP {resp.status_code}"]
    if message:
        parts.append(str(message))
    if cmd_result is not None and cmd_result != "":
        parts.append(str(cmd_result)[:200])
    if len(parts) == 1:
        parts.append(str(data)[:200])
    return cmd_success, " | ".join(parts)


def _get_json(base_url: str, path: str, ipc_password: str, timeout: int = 10) -> Tuple[bool, Any, str]:
    """Get JSON data from ASF API."""
    success, resp, data, error_msg = _make_request("GET", base_url, path, ipc_password, timeout)
    
    if not success:
        return False, None, f"{path}: {error_msg}"
    
    if isinstance(data, dict):
        ok = bool(data.get("Success", resp.ok))
        msg = str(data.get("Message", "")) if isinstance(data.get("Message", ""), (str, int, float)) else ""
        diag = f"{path}: HTTP {resp.status_code}" + (f" | {msg}" if msg else "")
        return ok, data, diag
    return False, data, f"{path}: HTTP {resp.status_code} (unexpected format)"


def _extract_bots_map(api_dict: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    if not isinstance(api_dict, dict):
        return None
    result = api_dict.get("Result")
    if result is None:
        return None
    if isinstance(result, dict):
        if "Bots" in result and isinstance(result["Bots"], dict):
            return result["Bots"]
        dict_values = list(result.values())
        if dict_values and all(isinstance(v, dict) for v in dict_values):
            return result
    if isinstance(result, list):
        out: Dict[str, Any] = {}
        for i, item in enumerate(result):
            if isinstance(item, dict):
                name = str(item.get("BotName") or item.get("Name") or f"Bot_{i + 1}")
                out[name] = item
        return out if out else None
    return None

def fast_port_check(host, port, timeout=0.3):
    try:
        with socket.create_connection((host, port), timeout=timeout):
            return True
    except Exception:
        return False


def get_bots_asf(base_url: str, ipc_password: str, timeout: int = 10) -> Tuple[bool, Optional[Dict[str, Any]], str]:
    """
    Возвращает состояние ботов на сервере ASF.
    Возвращает (успех, словарь данных, описание ошибки/результат).
    """
    last_diag = ""
    for path in ("/Api/Bots/ASF", "/Api/Bot/ASF"):
        ok, data, diag = _get_json(base_url, path, ipc_password, timeout=timeout)
        last_diag = diag
        if ok and isinstance(data, dict):
            bots_map = _extract_bots_map(data)
            if bots_map:
                return True, bots_map, diag
    return False, None, last_diag

def _get_bool(d: Dict[str, Any], keys: List[str]) -> Optional[bool]:
    for k in keys:
        if k in d:
            v = d.get(k)
            if isinstance(v, bool):
                return v
            if isinstance(v, (int, float)) and v in (0, 1):
                return bool(v)
            if isinstance(v, str):
                low = v.strip().lower()
                if low in ("true", "yes", "1"):
                    return True
                if low in ("false", "no", "0"):
                    return False
    return None


def is_online_bot(bot: Dict[str, Any]) -> Optional[bool]:
    v = _get_bool(bot, ["IsConnectedAndLoggedOn", "IsConnectedAndLoggedOnToSteam"])
    if v is not None:
        return v
    v = _get_bool(bot, ["IsConnected", "Connected"])
    if v is not None:
        return v
    v = _get_bool(bot, ["IsRunning", "Running", "KeepRunning"])
    if v is not None:
        return v
    return None


def compute_metrics_from_bots(bots_map: Dict[str, Any]) -> Tuple[int, int, int]:
    total = len(bots_map)
    online = 0
    offline = 0
    for _, bot_obj in bots_map.items():
        if not isinstance(bot_obj, dict):
            continue
        on = is_online_bot(bot_obj)
        if on is True:
            online += 1
        else:
            offline += 1
    if total >= 0 and online >= 0:
        offline = max(0, total - online)
    return total, online, offline


def get_bot_names(base_url: str, ipc_password: str) -> List[str]:
    ok, bots_map, _ = get_bots_asf(base_url, ipc_password)
    if ok and bots_map:
        return list(bots_map.keys())
    return []


def get_online_bots(base_url: str, ipc_password: str) -> List[str]:
    ok, bots_map, _ = get_bots_asf(base_url, ipc_password)
    if ok and bots_map:
        return [name for name, bot in bots_map.items() if is_online_bot(bot)]
    return []


def get_offline_bots(base_url: str, ipc_password: str) -> List[str]:
    ok, bots_map, _ = get_bots_asf(base_url, ipc_password)
    if ok and bots_map:
        return [name for name, bot in bots_map.items() if not is_online_bot(bot)]
    return []


# ============================================================
# LOGGER
# ============================================================

class CCULogger:
    def __init__(self, log_file: str):
        self.log_file = log_file
        self.ui_callback = None
        self._lock = threading.Lock()

    def set_ui_callback(self, callback):
        self.ui_callback = callback

    def _log(self, level: str, message: str):
        timestamp = _now_ts()
        full_msg = f"[{timestamp}] [{level}] {message}"
        with self._lock:
            try:
                with open(self.log_file, "a", encoding="utf-8") as f:
                    f.write(full_msg + "\n")
            except Exception:
                pass
        if self.ui_callback:
            try:
                self.ui_callback(level, full_msg)
            except Exception:
                pass

    def info(self, message: str):
        self._log("INF", message)

    def action(self, message: str):
        self._log("ACT", message)

    def ok(self, message: str):
        self._log("OK", message)

    def warn(self, message: str):
        self._log("WARN", message)

    def error(self, message: str):
        self._log("ERR", message)

    def alert(self, message: str):
        self._log("ALERT", message)


# ============================================================
# CCU WAVE ENGINE
# ============================================================

class CCUWaveEngine:
    def __init__(self, config: Dict[str, Any], logger: CCULogger):
        self.config = config
        self._last_logged_interval = None
        self.logger = logger
        self.last_sync_time = None  # Таймстемп последней синхронизации
        self.sync_interval = 10  # Интервал между синхронизациями (секунды)
        self.failed_instances = set()  # Набор недоступных серверов
        self.ipc_password = str(config.get("ipc_password", DEFAULT_IPC_PASSWORD) or DEFAULT_IPC_PASSWORD)
        self.is_running = False
        self.stop_event = threading.Event()
        self.current_phase = "idle"
        self.current_day = 1
        self.current_online = 0
        self.target_value = 0
        self.all_bots: Dict[str, List[str]] = {}
        self.bots_in_game: Dict[str, List[str]] = {}
        self.bots_should_be_in_game: List[str] = []
        self.on_status_update = None
        self.on_phase_change = None

        # Track fallen bots per instance (url -> set of bot names)
        self._fallen_tracked: Dict[str, Set[str]] = {}
        # Track restore attempts: url -> bot -> (count, last_attempt_ts)
        self._restore_attempts: Dict[str, Dict[str, Tuple[int, float]]] = {}

        # Parameters for restore attempts
        self._restore_max_attempts = 2
        self._restore_cooldown = 60.0  # seconds
        self.asf_online = 0  # реальный онлайн из ASF (только инфо)
        self.command_stop_event = threading.Event()
        self.command_thread = None
        self.current_interval = None

    def recalculate_global_interval(self):
        """
        Пересчитывает и сохраняет глобальный интервал времени.
        """
        if self.current_phase == "ascending":
            target_time = self.config.get("time_peak", "20:00")
        else:
            target_time = self.config.get("time_bottom", "06:00")

        seconds_available = _time_until(target_time)
        total_bots = max(1, self.current_online or self.get_total_bots_count())  # Минимум 1 бот

        if seconds_available <= 0:
            interval = 1.0
            self.logger.warn("Часы пика истекли. Установлен минимальный интервал: 1 секунда.")
        else:
            interval = seconds_available / total_bots

        # Логируем только если интервал изменился на ±1 секунду
        if abs(self.current_interval - interval) >= 1:
            self.logger.info(f"Рассчитанный глобальный интервал: {interval:.2f} секунд")
        self.current_interval = max(1, interval)

    def detect_phase_by_time(self) -> str:
        now_sec = datetime.now().hour * 3600 + datetime.now().minute * 60
        peak_sec = _time_to_seconds(self.config.get("time_peak", "20:00"))
        bottom_sec = _time_to_seconds(self.config.get("time_bottom", "06:00"))

        if bottom_sec < peak_sec:
            # Если "дно" до "пика" (например, 06:00 < 20:00)
            if bottom_sec <= now_sec < peak_sec:
                return "ascending"  # Режим "До пика"
            else:
                return "descending"  # Режим "До дна"
        else:
            # Если "дно" после полуночи, а "пик" до полуночи (например, 22:00 < 06:00)
            if now_sec >= bottom_sec or now_sec < peak_sec:
                return "ascending"  # Режим "До пика"
            else:
                return "descending"  # Режим "До дна"

    def reload_config(self, config: Dict[str, Any]):
        self.config = config
        self.ipc_password = str(config.get("ipc_password", DEFAULT_IPC_PASSWORD) or DEFAULT_IPC_PASSWORD)

    def get_active_instances(self) -> List[Dict[str, Any]]:
        """
        Возвращает список только активных серверов.
        Серверы с active=False игнорируются.
        """
        instances = self.config.get("instances", [])
        return [inst for inst in instances if inst.get("active", True)]

    def get_current_peak_bottom(self) -> Tuple[int, int]:
        base_peak = self.config.get("peak", 500)
        base_bottom = self.config.get("bottom", 150)
        base_days = self.config.get("base_days", 7)
        gradual = self.config.get("gradual_decay", {})
        if not gradual.get("enabled", False):
            return base_peak, base_bottom
        if self.current_day <= base_days:
            return base_peak, base_bottom
        additional_days = gradual.get("additional_days", [])
        day_index = self.current_day - base_days - 1
        if day_index < len(additional_days):
            day_config = additional_days[day_index]
            return day_config.get("peak", base_peak), day_config.get("bottom", base_bottom)
        return 0, 0

    def calculate_step_interval(self, current: int, target: int, seconds_available: int) -> float:
        """
        Рассчитывает интервал (в секундах) между командами play и reset на каждого бота.
        """
        diff = max(1, abs(target - current))  # минимальная разница = 1
        if seconds_available <= 0:
            self.logger.warn(
                "Недостаточно очищенного времени для расчета интервалов. Используется минимальный интервал.")
            return 1.0
        else:
            interval = seconds_available / diff
            self.logger.info(f"Рассчитанный интервал: {interval:.2f} секунд")
            return interval
        phase_ru = {
            "ascending": "До пика",
            "descending": "До дна",
            "idle": "Ожидание"
        }.get(self.current_phase, self.current_phase)

        time_left_str = _fmt_duration(seconds_available)

        self.logger.info("[Расчёт интервала]")
        self.logger.info(f"Режим: {phase_ru}")
        self.logger.info(
            f"Онлайн: алгоритм={current} | Цель={target} | Осталось={diff}"
        )
        self.logger.info(f"Осталось времени: {time_left_str}")
        self.logger.info(f"Интервал: {result:.2f} сек.")
        return result

    def apply_randomization(self, value: int) -> int:
        rand_config = self.config.get("randomize", {})
        if not rand_config.get("enabled", False):
            return value
        rand_type = rand_config.get("type", "percentage")
        rand_min = rand_config.get("min", -15)
        rand_max = rand_config.get("max", 15)
        if rand_type == "percentage":
            factor = random.uniform(1 + rand_min / 100, 1 + rand_max / 100)
            return int(value * factor)
        else:
            offset = random.randint(rand_min, rand_max)
            return value + offset

    def sync_bots_state_from_asf(self):
        """
        Производит синхронизацию всех инстансов с ASF, но с учетом интервала синхронизации.
        """
        now = time.time()

        if self.last_sync_time and now - self.last_sync_time < self.sync_interval:
            self.logger.info("Синхронизация уже выполнена недавно. Пропуск.")
            return

        self.last_sync_time = now

        game_id = self.config.get("game_id", 730)
        self.bots_in_game = {}
        self.current_online = 0
        self.asf_online = 0

        for inst in self.get_active_instances():
            url = inst.get("url", "")
            inst_name = inst.get("name", url)

            ok, bots_map, error_message = get_bots_asf(url, self.ipc_password)

            # Проверяем доступность сервера
            if not ok or not bots_map:
                if inst_name not in self.failed_instances:
                    self.logger.warn(f"[{inst_name}] Сервер недоступен. Переход в режим оффлайн (всех ботов: 0)")
                    self.failed_instances.add(inst_name)
                self.bots_in_game[url] = []
                continue
            else:
                # Если сервер снова стал доступен, удаляем его из списка недоступных
                if inst_name in self.failed_instances:
                    self.logger.info(f"[{inst_name}] Сервер снова доступен!")
                    self.failed_instances.remove(inst_name)

            # Собираем данные о боте
            playing = [bot_name for bot_name, bot_obj in bots_map.items() if self._is_bot_playing(bot_obj, game_id)]

            self.bots_in_game[url] = playing
            count = len(playing)

            self.current_online += count
            self.asf_online += len(bots_map)

            # Если сервер доступен, но все боты оффлайн, добавляем дополнительное сообщение
            if len(playing) == 0 and bots_map:
                self.logger.warn(
                    f"[{inst_name}] Все {len(bots_map)} ботов находятся оффлайн. Проверьте настройки или состояние.")

            self.logger.info(f"[{inst_name}] Состояние: Онлайн {len(playing)}, Оффлайн {len(bots_map) - len(playing)}")

        # Добавьте дополнительную проверку и предупреждения
        self.logger.info(f"Синхронизация завершена. Общий онлайн (ASF): {self.asf_online}.")
        if abs(self.asf_online - self.current_online) > 50:  # Если разница 50+ ботов
            self.logger.warn("Значительное расхождение между ожидаемым и фактическим онлайном.")

    def collect_all_bots(self):
        """
        Собрать информацию обо всех доступных ботах.
        """
        self.all_bots.clear()
        instances = self.get_active_instances()
        for inst in instances:
            url = inst.get("url", "")
            bots = get_bot_names(url, self.ipc_password)
            self.all_bots[url] = bots
            self.logger.info(f"[{inst.get('name', url)}] Найдено {len(bots)} ботов")

    def get_total_bots_count(self) -> int:
        return sum(len(bots) for bots in self.all_bots.values())

    def get_current_online_count(self) -> int:
        total = 0
        instances = self.get_active_instances()
        for inst in instances:
            url = inst.get("url", "")
            ok, bots_map, _ = get_bots_asf(url, self.ipc_password)
            if ok and bots_map:
                _, online, _ = compute_metrics_from_bots(bots_map)
                total += online
        return total

    def send_play_command(self, instance_url: str, bot_name: str, game_id: int) -> bool:
        command = f"play {bot_name} {game_id}"
        ok, _ = send_command(instance_url, command, self.ipc_password)
        return ok

    def send_reset_command(self, instance_url: str, bot_name: str) -> bool:
        command = f"reset {bot_name}"
        ok, _ = send_command(instance_url, command, self.ipc_password)
        return ok

    def get_bots_to_add(self, count: int) -> List[Tuple[str, str]]:
        """
        Возвращает список ботов, ещё не находящихся в игре, для их запуска.
        """
        result = []
        instances = self.get_active_instances()

        for inst in instances:
            url = inst.get("url", "")
            all_bots = set(self.all_bots.get(url, []))
            playing_bots = set(self.bots_in_game.get(url, []))  # Боты, уже в игре
            available_bots = list(all_bots - playing_bots)  # Только боты, которые не в игре

            bots_to_add = available_bots[:count - len(result)]
            result.extend([(url, bot) for bot in bots_to_add])
            if len(result) >= count:
                break

        if len(result) < count:
            self.logger.warn("Не хватает ботов для запуска. Проверьте конфигурацию.")
        return result

    def get_bots_to_remove(self, count: int) -> List[Tuple[str, str]]:
        result = []
        instances = self.get_active_instances()
        removed = 0
        while removed < count:
            removed_this_round = False
            for inst in instances:
                url = inst.get("url", "")
                in_game = self.bots_in_game.get(url, [])
                if in_game and removed < count:
                    bot = in_game[-1]
                    result.append((url, bot))
                    removed += 1
                    removed_this_round = True
            if not removed_this_round:
                break
        return result

    def _is_bot_playing(self, bot_obj: Dict[str, Any], expected_game_id: int) -> Optional[bool]:
        """
        Heuristic to detect if bot is already playing the target game.
        Returns True if playing expected_game_id, False if definitely not, None if unknown.
        """
        if not isinstance(bot_obj, dict):
            return None
        # Direct flags
        playing_flags = _get_bool(bot_obj, ["IsPlaying", "IsInGame", "Playing"])
        if playing_flags is True:
            # If we have GameID or AppID fields, compare
            try:
                gid = bot_obj.get("GameID") or bot_obj.get("AppID") or bot_obj.get("PlayingGameID")
                if gid:
                    try:
                        return int(gid) == int(expected_game_id)
                    except Exception:
                        return True
                return True
            except Exception:
                return True
        if playing_flags is False:
            return False
        # Check known fields for game id/name
        try:
            gid = bot_obj.get("GameID") or bot_obj.get("AppID") or bot_obj.get("PlayingGameID")
            if gid:
                try:
                    return int(gid) == int(expected_game_id)
                except Exception:
                    # Unknown format but non-empty -> assume playing
                    return True
        except Exception:
            pass
        # If Game/PlayingGameName exists and clearly empty -> not playing
        name = bot_obj.get("Game") or bot_obj.get("PlayingGameName") or bot_obj.get("GameName")
        if name:
            # If name is present but empty or "-" treat as not playing
            if isinstance(name, str) and name.strip():
                # we can't be certain it's the expected game, but it's playing something
                return True
            return False
        return None

    def check_and_restore_fallen_bots(self):
        """
        Восстанавливаем упавших ботов. Управляем каждым входом отдельно, не ожидая всех.
        """
        game_id = self.config.get("game_id", 730)
        instances = self.get_active_instances()
        for inst in instances:
            url = inst.get("url", "")
            name = inst.get("name", url)

            # Инициализация трекеров состояний
            fallen_set = self._fallen_tracked.setdefault(url, set())  # Хранит имена упавших ботов
            attempts_map = self._restore_attempts.setdefault(url, {})  # Хранит попытки восстановления для каждого бота

            # Получаем список всех ботов, которые должны находиться в игре
            should_be = set(self.bots_in_game.get(url, []))
            ok, bots_map, _ = get_bots_asf(url, self.ipc_password)
            currently_online = set(get_online_bots(url, self.ipc_password)) if ok else set()

            # Боты, вылетевшие из игры
            fallen = should_be - currently_online

            # Новые упавшие боты
            new_fallen = sorted(list(fallen - fallen_set))
            for bot in new_fallen:
                self.logger.alert(f"[{name}] Обнаружен вылет аккаунта {bot}, предпринимаем восстановление!")
                fallen_set.add(bot)
                attempts_map[bot] = (0, 0.0)  # Инициализация попыток восстановления

            # Восстанавливаем соединения
            for bot in sorted(fallen):
                count, last_ts = attempts_map.get(bot, (0, 0.0))
                now_ts = time.time()

                # Пропускаем ботов, с исчерпанными попытками
                if count >= self._restore_max_attempts:
                    continue

                # Пропускаем ботов на кулдауне
                if now_ts - last_ts < self._restore_cooldown:
                    continue

                # Пытаемся снова восстановить
                try:
                    success = self.send_play_command(url, bot, game_id)
                except Exception:
                    success = False

                if success:
                    self.logger.ok(f"[{name}] Аккаунт {bot} успешно возвращён!")
                    fallen_set.discard(bot)
                    attempts_map.pop(bot, None)
                else:
                    attempts_map[bot] = (count + 1, now_ts)
                    self.logger.warn(f"[{name}] Не удалось вернуть {bot} в игру. Попыток: {count + 1}")

    def update_status(self):
        """
        Обновляет статус текущего цикла работы двигателя и передаёт обновлённые данные в UI.
        """
        if self.on_status_update:
            peak, bottom = self.get_current_peak_bottom()
            self.on_status_update(
                phase=self.current_phase,
                peak=peak,
                bottom=bottom,
                online=self.current_online,
                day=self.current_day
            )

    def run_wave_cycle(self):
        """
        Основной цикл работы: управляет фазами "до пика" и "до дна".
        """
        game_id = self.config.get("game_id", 730)
        self.logger.info("=" * 50)

        # Единоразовая синхронизация перед запуском
        self.collect_all_bots()
        self.sync_bots_state_from_asf()
        total_bots = self.get_total_bots_count()
        self.logger.info(f"Всего ботов: {total_bots} (ONLINE: {self.current_online})")

        # Сохраняем текущую фазу
        previous_phase = self.current_phase

        # Основной рабочий цикл
        while self.is_running and not self.stop_event.is_set():
            try:
                # Определяем текущую фазу работы
                self.current_phase = self.detect_phase_by_time()

                # Выполняем синхронизацию только при смене фазы
                if self.current_phase != previous_phase:
                    self.logger.info(
                        f"Смена фазы с {previous_phase} на {self.current_phase}. Выполняем синхронизацию...")
                    self.sync_bots_state_from_asf()
                    previous_phase = self.current_phase  # Обновляем трекер фазы

                # Перерасчёт глобального интервала
                self.recalculate_global_interval()
                self.update_status()

                # Проверка и восстановление упавших ботов
                self.check_and_restore_fallen_bots()

            except Exception as e:
                self.logger.error(f"Ошибка в основном цикле: {e}")
                self.is_running = False
                break

            # Ждём окончания текущего интервала
            time.sleep(max(1, self.current_interval))

    def command_worker(self):
        self.logger.info("Command worker запущен")

        while self.is_running and not self.command_stop_event.is_set():
            interval = max(1, int(self.current_interval or 5))
            phase = self.current_phase

            if phase == "ascending":
                bots = self.get_bots_to_add(1)
                if bots:
                    url, bot = bots[0]
                    if self.send_play_command(url, bot, self.config.get("game_id")):
                        self.bots_in_game.setdefault(url, []).append(bot)
                        self.logger.ok(f"[{url}] {bot} play (принудительно)")

            elif phase == "descending":
                bots = self.get_bots_to_remove(1)
                if bots:
                    url, bot = bots[0]
                    if self.send_reset_command(url, bot):
                        if url in self.bots_in_game and bot in self.bots_in_game[url]:
                            self.bots_in_game[url].remove(bot)
                        self.logger.ok(f"[{url}] {bot} reset (принудительно)")

            for _ in range(interval):
                if not self.is_running or self.command_stop_event.is_set():
                    break
                time.sleep(1)

        self.logger.info("Command worker остановлен")

    def start(self, resume=False):
        if self.is_running:
            return

        # Обнуляем текущее состояние перед запуском
        self.is_running = True
        self.stop_event.clear()

        # Немедленная синхронизация состояния
        self.recalculate_global_interval()
        self.update_status()

        # Пересчёт интервала
        self.recalculate_global_interval()

        # Режим работы и запуск цикла
        now = datetime.now().hour * 3600 + datetime.now().minute * 60
        peak_sec = _time_to_seconds(self.config.get("time_peak", "20:00"))
        bottom_sec = _time_to_seconds(self.config.get("time_bottom", "06:00"))

        if bottom_sec < peak_sec:
            self.current_phase = "ascending" if bottom_sec <= now < peak_sec else "descending"
        else:
            self.current_phase = "ascending" if now < peak_sec or now >= bottom_sec else "descending"

        if not resume:
            self.current_day = 1
            self.current_online = 0
            self.bots_in_game = {}
            self._fallen_tracked = {}
            self._restore_attempts = {}

        threading.Thread(target=self.run_wave_cycle, daemon=True).start()

        # Включаем worker для команд
        self.command_thread = threading.Thread(
            target=self.command_worker,
            daemon=True
        )
        self.command_thread.start()

    def stop(self):
        self.stop_event.set()
        self.is_running = False
        # Save session state after stopping
        self.save_session_state()

    def save_session_state(self):
        state = {
            "is_running": self.is_running,
            "current_phase": self.current_phase,
            "current_day": self.current_day,
            "current_online": self.current_online,
            "bots_in_game": self.bots_in_game,
            "timestamp": _now_ts(),
            # Persist fallen and attempts for continuity
            "fallen_tracked": {k: list(v) for k, v in self._fallen_tracked.items()},
            "restore_attempts": {k: {bot: [cnt, ts] for bot, (cnt, ts) in v.items()} for k, v in
                                 self._restore_attempts.items()}
        }
        save_json_config(SESSION_STATE_FILE, state)

    def load_session_state(self) -> Optional[Dict[str, Any]]:
        if os.path.exists(SESSION_STATE_FILE):
            st = load_json_config(SESSION_STATE_FILE, {})
            # restore fallen & attempts if present
            try:
                fallen = st.get("fallen_tracked", {})
                self._fallen_tracked = {k: set(v) for k, v in fallen.items()}
                attempts = st.get("restore_attempts", {})
                self._restore_attempts = {k: {bot: (int(vals[0]), float(vals[1])) for bot, vals in v.items()} for k, v
                                          in attempts.items()}
            except Exception:
                pass
            return st
        return None

    def clear_session_state(self):
        try:
            if os.path.exists(SESSION_STATE_FILE):
                os.remove(SESSION_STATE_FILE)
        except Exception:
            pass


# ============================================================
# UI widgets
# ============================================================

class TimeSpinnerSeparate(ttk.Frame):
    def __init__(self, parent, initial_value="00:00", **kwargs):
        super().__init__(parent, **kwargs)
        h, m = self._parse(initial_value)

        self.var_h = tk.StringVar(value=f"{h:02d}")
        self.var_m = tk.StringVar(value=f"{m:02d}")
        self._repeat_id = None

        entry_opts = dict(width=3, justify=tk.CENTER)

        ttk.Entry(self, textvariable=self.var_h, **entry_opts).grid(row=0, column=0)
        self._arrows(self._inc_h, self._dec_h).grid(row=0, column=1, padx=(2, 4))

        ttk.Label(self, text=":").grid(row=0, column=2)

        ttk.Entry(self, textvariable=self.var_m, **entry_opts).grid(row=0, column=3)
        self._arrows(self._inc_m, self._dec_m).grid(row=0, column=4, padx=(2, 0))

    def _arrows(self, up, down):
        f = ttk.Frame(self)
        btn_up = tk.Button(f, text="▲", font=("Segoe UI", 5),
                           width=2, padx=0, pady=0, relief="ridge", borderwidth=1,
                           highlightthickness=0, bg="#f6f6f6", activebackground="#eeeeee")
        btn_up.pack()
        btn_up.bind("<ButtonPress-1>", lambda e: self._start_repeat(up))
        btn_up.bind("<ButtonRelease-1>", lambda e: self._stop_repeat())

        btn_down = tk.Button(f, text="▼", font=("Segoe UI", 5),
                             width=2, padx=0, pady=0, relief="ridge", borderwidth=1,
                             highlightthickness=0, bg="#f6f6f6", activebackground="#eeeeee")
        btn_down.pack()
        btn_down.bind("<ButtonPress-1>", lambda e: self._start_repeat(down))
        btn_down.bind("<ButtonRelease-1>", lambda e: self._stop_repeat())
        return f

    def _start_repeat(self, func):
        func()  # Execute once immediately
        self._repeat_id = self.after(500, lambda: self._continue_repeat(func))

    def _continue_repeat(self, func):
        func()
        self._repeat_id = self.after(50, lambda: self._continue_repeat(func))

    def _stop_repeat(self):
        if self._repeat_id:
            self.after_cancel(self._repeat_id)
            self._repeat_id = None

    def _parse(self, val):
        try:
            h, m = map(int, val.split(":"))
            return max(0, min(23, h)), max(0, min(59, m))
        except (ValueError, AttributeError):
            return 0, 0

    def _inc_h(self):
        self.var_h.set(f"{(int(self.var_h.get()) + 1) % 24:02d}")

    def _dec_h(self):
        self.var_h.set(f"{(int(self.var_h.get()) - 1) % 24:02d}")

    def _inc_m(self):
        self.var_m.set(f"{(int(self.var_m.get()) + 1) % 60:02d}")

    def _dec_m(self):
        self.var_m.set(f"{(int(self.var_m.get()) - 1) % 60:02d}")

    def get(self):
        return f"{int(self.var_h.get()):02d}:{int(self.var_m.get()):02d}"

    def set(self, v):
        h, m = self._parse(v)
        self.var_h.set(f"{h:02d}")
        self.var_m.set(f"{m:02d}")


class NumberSpinner(ttk.Frame):
    def __init__(self, parent, initial_value=0, min_val=None, max_val=None, width=6, **kwargs):
        super().__init__(parent, **kwargs)
        self.min_val = min_val
        self.max_val = max_val
        self.var = tk.StringVar(value=str(initial_value))
        self._repeat_id = None

        ttk.Entry(self, textvariable=self.var, width=width, justify=tk.CENTER).grid(row=0, column=0)

        f = ttk.Frame(self)
        f.grid(row=0, column=1, padx=(2, 0))

        self.btn_up = tk.Button(f, text="▲", font=("Segoe UI", 5),
                                width=2, padx=0, pady=0, relief="ridge", borderwidth=1,
                                highlightthickness=0, bg="#f6f6f6", activebackground="#eeeeee")
        self.btn_up.pack()
        self.btn_up.bind("<ButtonPress-1>", lambda e: self._start_repeat(self._increment))
        self.btn_up.bind("<ButtonRelease-1>", lambda e: self._stop_repeat())

        self.btn_down = tk.Button(f, text="▼", font=("Segoe UI", 5),
                                  width=2, padx=0, pady=0, relief="ridge", borderwidth=1,
                                  highlightthickness=0, bg="#f6f6f6", activebackground="#eeeeee")
        self.btn_down.pack()
        self.btn_down.bind("<ButtonPress-1>", lambda e: self._start_repeat(self._decrement))
        self.btn_down.bind("<ButtonRelease-1>", lambda e: self._stop_repeat())

    def _start_repeat(self, func):
        func()  # Execute once immediately
        self._repeat_id = self.after(500, lambda: self._continue_repeat(func))

    def _continue_repeat(self, func):
        func()
        self._repeat_id = self.after(50, lambda: self._continue_repeat(func))

    def _stop_repeat(self):
        if self._repeat_id:
            self.after_cancel(self._repeat_id)
            self._repeat_id = None

    def _increment(self):
        try:
            val = int(self.var.get()) + 1
        except (ValueError, TypeError):
            val = 0
        if self.max_val is not None:
            val = min(val, self.max_val)
        self.var.set(str(val))

    def _decrement(self):
        try:
            val = int(self.var.get()) - 1
        except (ValueError, TypeError):
            val = 0
        if self.min_val is not None:
            val = max(val, self.min_val)
        self.var.set(str(val))

    def get(self):
        return self.var.get()

    def set(self, v):
        self.var.set(str(v))


# ============================================================
# TemplatesWindow (unchanged)
# ============================================================

class TemplatesWindow(tk.Toplevel):
    def __init__(self, parent: tk.Tk):
        super().__init__(parent)
        self.title("Шаблоны пик/дно")
        self.transient(parent)

        # Allow closing with Esc key
        self.bind("<Escape>", lambda e: self.destroy())

        self.templates_data = load_json_config(TEMPLATES_PEAKS, {"templates": []})
        self.templates = self.templates_data.get("templates", [])

        width, height = 500, 450
        x = (self.winfo_screenwidth() // 2) - (width // 2)
        y = (self.winfo_screenheight() // 2) - (height // 2)
        self.geometry(f"{width}x{height}+{x}+{y}")
        self.resizable(False, False)

        frm = ttk.Frame(self, padding=10)
        frm.pack(fill=tk.BOTH, expand=True)

        btn = ttk.Frame(frm)
        btn.pack(fill=tk.X, pady=(0, 8))

        ttk.Button(btn, text="Добавить", command=self.add_template).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn, text="Удалить", command=self.del_template).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn, text="Закрыть", command=self.destroy).pack(side=tk.RIGHT, padx=5)

        columns = ("name", "peak", "bottom")
        self.tree = ttk.Treeview(frm, columns=columns, show="headings", height=15)

        self.tree.heading("name", text="Имя", anchor=tk.W)
        self.tree.heading("peak", text="Пик", anchor=tk.CENTER)
        self.tree.heading("bottom", text="Дно", anchor=tk.CENTER)

        self.tree.column("name", width=250, anchor=tk.W)
        self.tree.column("peak", width=100, anchor=tk.CENTER)
        self.tree.column("bottom", width=100, anchor=tk.CENTER)

        vsb = ttk.Scrollbar(frm, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self._populate()

    def _populate(self):
        self.tree.delete(*self.tree.get_children())
        for i, tpl in enumerate(self.templates):
            self.tree.insert("", tk.END, iid=str(i),
                             values=(tpl.get("name", ""), tpl.get("peak", 0), tpl.get("bottom", 0)))

    def add_template(self):
        name = simpledialog.askstring("Шаблон", "Имя шаблона:", parent=self)
        if not name:
            return
        peak = simpledialog.askinteger("Шаблон", "Пик:", parent=self)
        if peak is None:
            return
        bottom = simpledialog.askinteger("Шаблон", "Дно:", parent=self)
        if bottom is None:
            return

        self.templates.append({"name": name, "peak": peak, "bottom": bottom})
        self._save()
        self._populate()

    def del_template(self):
        sel = self.tree.selection()
        if not sel:
            return
        idx = int(sel[0])
        if 0 <= idx < len(self.templates):
            self.templates.pop(idx)
            self._save()
            self._populate()

    def _save(self):
        self.templates_data["templates"] = self.templates
        save_json_config(TEMPLATES_PEAKS, self.templates_data)

class ExitAllAccountsDialog(tk.Toplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.result = None

        self.title("Подтверждение")
        self.transient(parent)
        self.grab_set()
        self.resizable(False, False)

        # Закрытие = отмена
        self.protocol("WM_DELETE_WINDOW", self._cancel)
        self.bind("<Escape>", lambda e: self._cancel())

        # Размер и центрирование
        w, h = 420, 160
        self.update_idletasks()
        x = parent.winfo_rootx() + parent.winfo_width() // 2 - w // 2
        y = parent.winfo_rooty() + parent.winfo_height() // 2 - h // 2
        self.geometry(f"{w}x{h}+{x}+{y}")

        # Основной контейнер
        main = ttk.Frame(self, padding=(20, 18))
        main.pack(fill=tk.BOTH, expand=True)

        # Текст
        lbl = ttk.Label(
            main,
            text="Выйти из игры на всех аккаунтах?",
            anchor="center",
            justify="center",
            font=("Segoe UI", 10)
        )
        lbl.pack(fill=tk.X, pady=(0, 18))

        # Кнопки
        btns = ttk.Frame(main)
        btns.pack(fill=tk.X)

        ttk.Button(
            btns,
            text="Да",
            width=16,
            command=self._yes
        ).pack(side=tk.LEFT, padx=(0, 10))

        ttk.Button(
            btns,
            text="Нет",
            width=16,
            command=self._no
        ).pack(side=tk.LEFT)

        self.wait_window(self)

    def _yes(self):
        self.result = True
        self.destroy()

    def _no(self):
        self.result = False
        self.destroy()

    def _cancel(self):
        self.result = None
        self.destroy()


def ask_exit_all_accounts(parent):
    dlg = ExitAllAccountsDialog(parent)
    return dlg.result

# ============================================================
# BOTS VIEW WINDOW (unchanged)
# ============================================================

class BotsViewWindow(tk.Toplevel):
    def __init__(self, parent: tk.Tk, instance: Dict[str, Any], ipc_password: str, app):
        super().__init__(parent)
        self.title(f"Список аккаунтов: {instance.get('name', 'Server')}")
        self.instance = instance
        self.ipc_password = ipc_password
        self.app = app
        self.transient(parent)

        # Allow closing with Esc key
        self.bind("<Escape>", lambda e: self.destroy())

        width = 600
        height = 450
        x = (self.winfo_screenwidth() // 2) - (width // 2)
        y = (self.winfo_screenheight() // 2) - (height // 2)
        self.geometry(f"{width}x{height}+{x}+{y}")

        self._build()
        self.refresh()

    def refresh(self):
        """
        Обновляет данные о состоянии ботов для докладного окна.
        """
        try:
            url = self.instance.get("url")
            if not url:
                return

            # Получаем состояние ботов
            ok, bots_map, _ = get_bots_asf(url, self.ipc_password)

            # Очищаем дерево перед обновлением
            self.tree.delete(*self.tree.get_children())

            total = online = offline = 0
            icons = self.app.status_icons

            if ok and bots_map:
                for bot, info in bots_map.items():
                    is_online = is_online_bot(info)

                    if is_online is True:
                        icon = icons["green"]
                        online += 1
                    else:
                        icon = icons["gray"]
                        offline += 1

                    self.tree.insert(
                        "",
                        tk.END,
                        image=icon,
                        values=(bot,)
                    )
                    total += 1

            # Обновляем информацию о состоянии в заголовке окна
            self.info_var.set(f"Всего: {total} | Онлайн: {online} | Офлайн: {offline}")

        except Exception:
            self.info_var.set("Ошибка обновления")

    def _copy_login(self):
        """
        Копирует логин выбранного бота в буфер обмена
        """
        try:
            selected = self.tree.selection()
            if not selected:
                return

            item = selected[0]
            values = self.tree.item(item, "values")
            if not values:
                return

            login = values[0]

            self.clipboard_clear()
            self.clipboard_append(login)

        except Exception:
            pass

    def _on_right_click(self, event):
        """
        ПКМ по списку аккаунтов — показать контекстное меню
        """
        try:
            iid = self.tree.identify_row(event.y)
            if not iid:
                return

            self.tree.selection_set(iid)
            self.tree.focus(iid)

            self.ctx_menu.tk_popup(event.x_root, event.y_root)
        finally:
            try:
                self.ctx_menu.grab_release()
            except Exception:
                pass

    def _build(self):
        frm = ttk.Frame(self, padding=6)
        frm.pack(fill=tk.BOTH, expand=True)

        top = ttk.Frame(frm)
        top.pack(fill=tk.X, pady=(0, 6))

        # Info label for totals
        self.info_var = tk.StringVar(value="Всего: 0 | Онлайн: 0 | Офлайн: 0")
        ttk.Label(top, textvariable=self.info_var, anchor="w").pack(side=tk.LEFT, padx=4)

        btn_frame = ttk.Frame(top)
        btn_frame.pack(side=tk.RIGHT)
        ttk.Button(btn_frame, text="🔄 Обновить", command=self.refresh).pack(side=tk.LEFT, padx=4)
        ttk.Button(btn_frame, text="Закрыть", command=self.destroy).pack(side=tk.LEFT, padx=4)

        columns = ("name",)
        self.tree = ttk.Treeview(frm, columns=columns, show="tree headings")

        self.tree.heading("#0", text=STATUS_TEXT, anchor=tk.CENTER)
        self.tree.heading("name", text="Аккаунт", anchor=tk.W)

        # Wider status column to avoid overlap
        self.tree.column("#0", width=80, minwidth=60, anchor=tk.CENTER, stretch=False)
        self.tree.column("name", width=420, anchor=tk.W)

        vsb = ttk.Scrollbar(frm, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)

        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # Context menu to copy login (no dialogs)
        self.ctx_menu = tk.Menu(self, tearoff=0)
        self.ctx_menu.add_command(label="Копировать логин", command=self._copy_login)

        # Bind right-click to open context menu, and Ctrl+C
        self.tree.bind("<Button-3>", self._on_right_click)
        self.tree.bind("<Control-c>", lambda e: self._copy_login())
        self.tree.bind("<Control-C>", lambda e: self._copy_login())

# ============================================================
# ConfigEditorCCU: restored original visual editor
# ============================================================

class ConfigEditorCCU(tk.Toplevel):
    _bold_style_inited = False

    def __init__(self, parent: tk.Tk, config: Dict[str, Any], on_saved_callback):
        if not ConfigEditorCCU._bold_style_inited:
            style = ttk.Style()
            style.configure("Bold.TLabelframe.Label", font=("Segoe UI", 9, "bold"))
            style.configure("Bold.TCheckbutton", font=("Segoe UI", 9, "bold"))
            ConfigEditorCCU._bold_style_inited = True

        super().__init__(parent)
        self.title("Редактировать конфиг CCU")
        self.config_data = config.copy()
        self.on_saved_callback = on_saved_callback
        self.transient(parent)
        self.grab_set()

        # Allow closing with Esc key
        self.bind("<Escape>", lambda e: self._on_cancel())

        width = 1150
        height = 825
        x = (self.winfo_screenwidth() // 2) - (width // 2)
        y = (self.winfo_screenheight() // 2) - (height // 2)
        self.geometry(f"{width}x{height}+{x}+{y}")
        self.resizable(True, True)

        # containers for dynamic rows
        self._server_rows: List[Dict[str, Any]] = []
        self._gradual_rows: List[Dict[str, Any]] = []

        self._build()

    def _build(self):
        frm = ttk.Frame(self, padding=8)
        frm.pack(fill=tk.BOTH, expand=True)

        # Top area: three sections side by side
        top = ttk.Frame(frm)
        top.pack(fill=tk.X, pady=(0, 6))

        left = ttk.LabelFrame(top, text="Основные параметры", padding=8, style="Bold.TLabelframe")
        left.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 6))

        middle = ttk.LabelFrame(top, text="Дополнительные опции", padding=8, style="Bold.TLabelframe")
        middle.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 6))

        right = ttk.LabelFrame(top, text="Плавный спад", padding=8, style="Bold.TLabelframe")
        right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # LEFT: main params
        ttk.Label(left, text="Game ID:").grid(row=0, column=0, sticky="w", pady=2)
        self.entry_game_id = ttk.Entry(left, width=12)
        self.entry_game_id.grid(row=0, column=1, sticky="w", pady=2)

        ttk.Label(left, text="IPC Password:").grid(row=1, column=0, sticky="w", pady=2)
        self.entry_ipc = ttk.Entry(left, width=12)
        self.entry_ipc.grid(row=1, column=1, sticky="w", pady=2)

        ttk.Label(left, text="Пик:").grid(row=2, column=0, sticky="w", pady=2)
        self.entry_peak = ttk.Entry(left, width=8)
        self.entry_peak.grid(row=2, column=1, sticky="w", pady=2)

        ttk.Label(left, text="Дно:").grid(row=3, column=0, sticky="w", pady=2)
        self.entry_bottom = ttk.Entry(left, width=8)
        self.entry_bottom.grid(row=3, column=1, sticky="w", pady=2)

        ttk.Label(left, text="Время пика:").grid(row=4, column=0, sticky="w", pady=2)
        self.time_peak_widget = TimeSpinnerSeparate(left, initial_value=self.config_data.get("time_peak", "20:00"))
        self.time_peak_widget.grid(row=4, column=1, sticky="w", pady=2)

        ttk.Label(left, text="Время дна:").grid(row=5, column=0, sticky="w", pady=2)
        self.time_bottom_widget = TimeSpinnerSeparate(left, initial_value=self.config_data.get("time_bottom", "06:00"))
        self.time_bottom_widget.grid(row=5, column=1, sticky="w", pady=2)

        ttk.Label(left, text="Базовые дни:").grid(row=6, column=0, sticky="w", pady=2)
        self.spin_base_days = NumberSpinner(left, initial_value=self.config_data.get("base_days", 7), min_val=1,
                                            width=8)
        self.spin_base_days.grid(row=6, column=1, sticky="w", pady=2)

        # MIDDLE: randomize & delay
        randomize_cfg = self.config_data.get("randomize", {})
        self.rand_var = tk.IntVar(value=1 if randomize_cfg.get("enabled", False) else 0)
        self.chk_random = ttk.Checkbutton(middle, text="Рандомизация", variable=self.rand_var,
                                          style="Bold.TCheckbutton")
        self.chk_random.grid(row=0, column=0, columnspan=2, sticky="w")

        ttk.Label(middle, text="Тип:").grid(row=1, column=0, sticky="w", pady=2)
        self.rand_type = tk.StringVar(value=randomize_cfg.get("type", "percentage"))
        self.combo_rand_type = ttk.Combobox(middle, values=["Проценты", "Значения"], textvariable=self.rand_type,
                                            width=12, state="readonly")
        self.combo_rand_type.grid(row=1, column=1, sticky="w", pady=2)

        ttk.Label(middle, text="Мин:").grid(row=2, column=0, sticky="w", pady=2)
        self.spin_rand_min = NumberSpinner(middle, initial_value=randomize_cfg.get("min", -15),
                                           width=6)
        self.spin_rand_min.grid(row=2, column=1, sticky="w", pady=2)

        ttk.Label(middle, text="Макс:").grid(row=3, column=0, sticky="w", pady=2)
        self.spin_rand_max = NumberSpinner(middle, initial_value=randomize_cfg.get("max", 15),
                                           width=6)
        self.spin_rand_max.grid(row=3, column=1, sticky="w", pady=2)

        delay_cfg = self.config_data.get("delay", {})
        self.delay_var = tk.IntVar(value=1 if delay_cfg.get("enabled", False) else 0)
        self.chk_delay = ttk.Checkbutton(middle, text="Задержка", variable=self.delay_var, style="Bold.TCheckbutton")
        self.chk_delay.grid(row=4, column=0, columnspan=2, sticky="w", pady=(8, 2))

        ttk.Label(middle, text="После пика:").grid(row=5, column=0, sticky="w", pady=2)
        self.delay_after_peak = TimeSpinnerSeparate(middle, initial_value=delay_cfg.get(
            "delay_after_peak", "00:00"))
        self.delay_after_peak.grid(row=5, column=1, sticky="w", pady=2)

        ttk.Label(middle, text="После дна:").grid(row=6, column=0, sticky="w", pady=2)
        self.delay_after_bottom = TimeSpinnerSeparate(middle, initial_value=delay_cfg.get(
            "delay_after_bottom", "00:00"))
        self.delay_after_bottom.grid(row=6, column=1, sticky="w", pady=2)

        # RIGHT: gradual decay (additional days)
        gradual_cfg = self.config_data.get("gradual_decay", {})
        self.gradual_var = tk.IntVar(value=1 if gradual_cfg.get("enabled", False) else 0)
        self.chk_gradual = ttk.Checkbutton(right, text="Включить", variable=self.gradual_var)
        self.chk_gradual.pack(anchor="nw")

        days_frame = ttk.Frame(right)
        days_frame.pack(fill=tk.BOTH, expand=True, pady=(6, 0))

        self.gradual_days_container = ttk.Frame(days_frame)
        self.gradual_days_container.pack(fill=tk.BOTH, expand=True)

        # load existing additional_days
        additional_days = gradual_cfg.get("additional_days", [])
        for day in additional_days:
            self._add_gradual_row(day.get("peak", 0), day.get("bottom", 0))
        # one empty by default
        if not additional_days:
            self._add_gradual_row(0, 0)

        ttk.Button(right, text="+ Добавить день", command=lambda: self._add_gradual_row(0, 0)).pack(anchor="nw", pady=4)

        # SERVERS section (full width)
        srv_frame = ttk.LabelFrame(frm, text="Серверы", padding=8, style="Bold.TLabelframe")
        srv_frame.pack(fill=tk.BOTH, expand=True, pady=(8, 0))

        # Create a canvas with scrollbar for servers
        canvas = tk.Canvas(srv_frame, height=150)
        scrollbar = ttk.Scrollbar(srv_frame, orient="vertical", command=canvas.yview)
        self.servers_container = ttk.Frame(canvas)

        canvas.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        canvas_window = canvas.create_window((0, 0), window=self.servers_container, anchor="nw")

        # Store canvas reference for auto-scroll
        self._servers_canvas = canvas

        def configure_scroll_region(event):
            canvas.configure(scrollregion=canvas.bbox("all"))

        self.servers_container.bind("<Configure>", configure_scroll_region)

        # header row
        hdr = ttk.Frame(self.servers_container)
        hdr.pack(fill=tk.X, pady=(0, 4))
        ttk.Label(hdr, text="", width=3).pack(side=tk.LEFT)
        ttk.Label(hdr, text="Имя:", width=20).pack(side=tk.LEFT, padx=(4, 6))
        ttk.Label(hdr, text="URL:", width=40).pack(side=tk.LEFT, padx=(6, 4))

        # populate rows from config
        instances = self.config_data.get("instances", [])
        for inst in instances:
            name = inst.get("name", "")
            url = inst.get("url", "")
            active = inst.get("active", True)
            self._add_server_row(name, url, bool(active))

        # If no instances, add one empty row
        if not instances:
            self._add_server_row("GAME_1", "localhost:7722", True)

        add_btn = ttk.Button(srv_frame, text="+ Добавить", command=lambda: self._add_server_row("", "", False))
        add_btn.pack(side=tk.LEFT, pady=(6, 0))

        # Bottom buttons
        bottom = ttk.Frame(frm)
        bottom.pack(fill=tk.X, pady=(8, 0))

        ttk.Button(bottom, text="Закрыть", command=self._on_cancel).pack(side=tk.RIGHT, padx=6)
        ttk.Button(bottom, text="Сохранить", command=self._on_save).pack(side=tk.RIGHT, padx=6)

        # Fill fields with current config
        self._load_values_into_widgets()

    def _add_gradual_row(self, peak=0, bottom=0):
        row = ttk.Frame(self.gradual_days_container)
        row.pack(fill=tk.X, pady=2, padx=4)

        # Day number within gradual decline (1st additional day, 2nd additional day, etc.)
        day_num = len(self._gradual_rows) + 1
        ttk.Label(row, text=f"День {day_num}:").pack(side=tk.LEFT, padx=(0, 6))

        ttk.Label(row, text="Пик:").pack(side=tk.LEFT, padx=(0, 4))
        peak_e = ttk.Entry(row, width=6)
        peak_e.pack(side=tk.LEFT)
        peak_e.insert(0, str(peak))

        ttk.Label(row, text="Дно:").pack(side=tk.LEFT, padx=(6, 4))
        bottom_e = ttk.Entry(row, width=6)
        bottom_e.pack(side=tk.LEFT)
        bottom_e.insert(0, str(bottom))

        btn = ttk.Button(row, text="✖", width=3, command=lambda r=row: self._remove_gradual_row(r))
        btn.pack(side=tk.RIGHT, padx=4)

        self._gradual_rows.append({"frame": row, "peak": peak_e, "bottom": bottom_e})

    def _remove_gradual_row(self, frame):
        for r in list(self._gradual_rows):
            if r["frame"] == frame:
                try:
                    r["frame"].pack_forget()
                    r["frame"].destroy()
                except Exception:
                    pass
                self._gradual_rows.remove(r)
                break

    def _add_server_row(self, name="", url="", active=False):
        # Генерация нового имени и URL (GAME_X + следующий порт)
        if not name and not url:
            last_idx = 0
            last_port = 0

            for r in self._server_rows:
                try:
                    n = r["name"].get()
                    if n.startswith("GAME_"):
                        last_idx = max(last_idx, int(n.replace("GAME_", "")))
                except (ValueError, AttributeError, KeyError):
                    pass

                try:
                    u = r["url"].get()
                    if ":" in u:
                        last_port = max(last_port, int(u.split(":")[-1]))
                except (ValueError, AttributeError, KeyError):
                    pass

            name = f"GAME_{last_idx + 1}"
            url = f"localhost:{last_port + 1 if last_port else 7722}"

        row = ttk.Frame(self.servers_container)
        row.pack(fill=tk.X, pady=2, padx=4)

        var_active = tk.IntVar(value=1 if active else 0)
        chk = ttk.Checkbutton(row, variable=var_active)
        chk.pack(side=tk.LEFT, padx=(0, 6))

        ent_name = ttk.Entry(row, width=25)
        ent_name.pack(side=tk.LEFT, padx=(0, 6))
        ent_name.insert(0, name)

        ent_url = ttk.Entry(row, width=50)
        ent_url.pack(side=tk.LEFT, padx=(0, 6))
        ent_url.insert(0, url)

        btn = ttk.Button(row, text="✖", width=3, command=lambda r=row: self._remove_server_row(r))
        btn.pack(side=tk.RIGHT, padx=4)

        self._server_rows.append({"frame": row, "active": var_active, "name": ent_name, "url": ent_url})

        # Авто-прокрутка вниз при добавлении строки
        self.servers_container.update_idletasks()
        self._servers_canvas.yview_moveto(1.0)

    def _remove_server_row(self, frame):
        for r in list(self._server_rows):
            if r["frame"] == frame:
                try:
                    r["frame"].pack_forget()
                    r["frame"].destroy()
                except Exception:
                    pass
                self._server_rows.remove(r)
                break

    def _load_values_into_widgets(self):
        cfg = self.config_data
        # main
        self.entry_game_id.delete(0, tk.END)
        self.entry_game_id.insert(0, str(cfg.get("game_id", "")))

        self.entry_ipc.delete(0, tk.END)
        self.entry_ipc.insert(0, str(cfg.get("ipc_password", "")))

        self.entry_peak.delete(0, tk.END)
        self.entry_peak.insert(0, str(cfg.get("peak", "")))

        self.entry_bottom.delete(0, tk.END)
        self.entry_bottom.insert(0, str(cfg.get("bottom", "")))

        self.time_peak_widget.set(cfg.get("time_peak", "20:00"))
        self.time_bottom_widget.set(cfg.get("time_bottom", "06:00"))

        self.spin_base_days.set(str(cfg.get("base_days", 7)))

        # randomize
        rand = cfg.get("randomize", {})
        self.rand_var.set(1 if rand.get("enabled", False) else 0)
        # Convert from English to Russian
        rand_type_eng = rand.get("type", "percentage")
        rand_type_rus = "Проценты" if rand_type_eng == "percentage" else "Значения"
        self.rand_type.set(rand_type_rus)
        self.spin_rand_min.set(str(rand.get("min", -15)))
        self.spin_rand_max.set(str(rand.get("max", 15)))

        # delay
        delay = cfg.get("delay", {})
        self.delay_var.set(1 if delay.get("enabled", False) else 0)
        self.delay_after_peak.set(delay.get("delay_after_peak", "00:00"))
        self.delay_after_bottom.set(delay.get("delay_after_bottom", "00:00"))

        # gradual handled already during build

    def _gather_values_from_widgets(self) -> Dict[str, Any]:
        cfg = self.config_data.copy()

        # main
        try:
            cfg["game_id"] = int(self.entry_game_id.get())
        except Exception:
            cfg["game_id"] = self.entry_game_id.get()
        cfg["ipc_password"] = self.entry_ipc.get()
        try:
            cfg["peak"] = int(self.entry_peak.get())
        except Exception:
            cfg["peak"] = 0
        try:
            cfg["bottom"] = int(self.entry_bottom.get())
        except Exception:
            cfg["bottom"] = 0
        cfg["time_peak"] = self.time_peak_widget.get()
        cfg["time_bottom"] = self.time_bottom_widget.get()
        try:
            cfg["base_days"] = int(self.spin_base_days.get())
        except Exception:
            cfg["base_days"] = 1

        # randomize
        # Convert from Russian to English
        rand_type_rus = self.rand_type.get()
        rand_type_eng = "percentage" if rand_type_rus == "Проценты" else "absolute"
        cfg["randomize"] = {
            "enabled": bool(self.rand_var.get()),
            "type": rand_type_eng,
            "min": int(self.spin_rand_min.get()),
            "max": int(self.spin_rand_max.get())
        }

        # delay
        cfg["delay"] = {
            "enabled": bool(self.delay_var.get()),
            "delay_after_peak": self.delay_after_peak.get(),
            "delay_after_bottom": self.delay_after_bottom.get()
        }

        # gradual decay
        cfg["gradual_decay"] = {"enabled": bool(self.gradual_var.get()), "additional_days": []}
        for r in self._gradual_rows:
            try:
                p = int(r["peak"].get())
            except Exception:
                p = 0
            try:
                b = int(r["bottom"].get())
            except Exception:
                b = 0
            cfg["gradual_decay"]["additional_days"].append({"peak": p, "bottom": b})

        # instances
        cfg["instances"] = []
        for r in self._server_rows:
            name = r["name"].get().strip()
            url = r["url"].get().strip()
            active = bool(r["active"].get())
            if not name and not url:
                continue
            cfg["instances"].append({"name": name or "unnamed", "url": url, "active": active})

        return cfg

    def _on_save(self):
        new_cfg = self._gather_values_from_widgets()
        # basic validation
        if not new_cfg.get("instances"):
            if not messagebox.askyesno("Подтверждение", "Список инстансов пуст. Сохранить всё равно?"):
                return
        try:
            save_json_config(CONFIG_CCU, new_cfg)
            # call callback
            try:
                if callable(self.on_saved_callback):
                    self.on_saved_callback()
            except Exception:
                pass
            self.destroy()
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось сохранить конфиг: {e}")

    def _on_cancel(self):
        self.destroy()

    def _on_right_click(self, event):
        iid = self.tree.identify_row(event.y)
        if iid:
            try:
                self.tree.selection_set(iid)
                self.tree.focus(iid)
            except Exception:
                pass
            try:
                self.ctx_menu.tk_popup(event.x_root, event.y_root)
            finally:
                self.ctx_menu.grab_release()

    def _copy_login(self):
        sel = self.tree.selection()
        if not sel:
            return
        iid = sel[0]
        try:
            vals = self.tree.item(iid, "values")
            name = vals[0] if vals else ""
        except Exception:
            name = ""
        if name:
            try:
                self.clipboard_clear()
                self.clipboard_append(name)
            except Exception:
                pass

    def refresh(self):
        self.tree.delete(*self.tree.get_children())

        url = self.instance.get("url", "")
        ok, bots_map, _ = get_bots_asf(url, self.ipc_password)
        if not ok or not bots_map:
            self.info_var.set("Всего: 0 | Онлайн: 0 | Офлайн: 0")
            return

        total, online, offline = compute_metrics_from_bots(bots_map)
        self.info_var.set(f"Всего: {total} | Онлайн: {online} | Офлайн: {offline}")

        for name, bot in bots_map.items():
            online_state = is_online_bot(bot)
            if online_state is True:
                icon_key = "green"
            elif online_state is False:
                icon_key = "red"
            else:
                icon_key = "gray"
            self.tree.insert("", tk.END, image=self.app.status_icons.get(icon_key), values=(name,))

# ============================================================
# CCUManagerApp (full)
# ============================================================

class CCUManagerApp:
    def __init__(self, root: tk.Tk):
        self.command_thread = None
        self.command_stop_event = threading.Event()
        self.root = root
        self.root.title("CCU Manager v1.3.1")
        self.root.geometry("1200x900")

        # Prepare logger and config
        self.logger = CCULogger(CCU_LOG_FILE)
        self.config = load_json_config(CONFIG_CCU, default_config_ccu())
        self.ipc_password = str(self.config.get("ipc_password", DEFAULT_IPC_PASSWORD) or DEFAULT_IPC_PASSWORD)
        self.status_icons = _init_status_icons(self.root)

        self.engine = CCUWaveEngine(self.config, self.logger)
        self.engine.on_status_update = self._on_engine_status_update
        self.monitor_thread = None
        self.monitor_stop = threading.Event()

        # Treeview heading style tweak for padding
        style = ttk.Style()
        style.configure("Treeview.Heading", padding=(6, 2))
        style.configure("Treeview", rowheight=28)

        # Flag to prevent concurrent refreshes
        self._refresh_in_progress = False

        self._build_ui()
        self._check_session_recovery()
        self._start_monitoring()

    def refresh_process_status(self):
        if not self.engine.is_running:
            self.logger.info("Обновление статуса: движок не запущен")
            return

        # ASF онлайн
        self.engine.sync_bots_state_from_asf()

        # режим по времени
        try:
            self.engine.current_phase = self.engine.detect_phase_by_time()
        except Exception:
            pass

        # статус UI
        self.engine.update_status()

        # сбор данных для лога
        phase = self.engine.current_phase
        phase_ru = {
            "ascending": "До пика",
            "descending": "До дна",
            "idle": "Ожидание"
        }.get(phase, phase)

        peak, bottom = self.engine.get_current_peak_bottom()
        target = peak if phase == "ascending" else bottom

        online_alg = self.engine.current_online
        asf_online = getattr(self.engine, "asf_online", None)

        self.logger.info("Ручное обновление статуса:")
        self.logger.info(f"Режим: {phase_ru}")
        self.logger.info(f"Целевой онлайн: {target}")

        if isinstance(asf_online, int):
            diff = asf_online - online_alg
            self.logger.info(
                f"Онлайн: алгоритм={online_alg} | ASF={asf_online} | Δ={diff}"
            )

            if abs(diff) >= 50:
                self.logger.warn("ASF и алгоритм сильно расходятся")
        else:
            self.logger.info(f"Онлайн (алгоритм): {online_alg}")

        self.logger.info("Обновление статуса завершено")

    def _build_ui(self):
        # Global deselect when clicking outside treeviews
        self.root.bind("<Button-1>", self._global_deselect)

        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self.tab_servers = ttk.Frame(self.notebook)
        self.notebook.add(self.tab_servers, text="Серверы")
        self._build_tab_servers()

        self.tab_monitor = ttk.Frame(self.notebook)
        self.notebook.add(self.tab_monitor, text="Мониторинг")
        self._build_tab_monitor()

    def _global_deselect(self, event):
        widget = event.widget
        w = widget

        # ⛔ НЕ трогаем Text / ScrolledText (лог должен нормально выделяться)
        while w is not None:
            if isinstance(w, (ttk.Treeview, tk.Text)):
                return
            w = getattr(w, "master", None)

        if hasattr(self, "server_tree"):
            try:
                self.server_tree.selection_remove(self.server_tree.selection())
            except Exception:
                pass

    def _build_tab_servers(self):
        main = ttk.Frame(self.tab_servers, padding=5)
        main.pack(fill=tk.BOTH, expand=True)

        top = ttk.LabelFrame(main, text="Инстансы ASF")
        top.pack(fill=tk.BOTH, expand=True, pady=5)

        columns = ("name", "url", "all", "online", "offline")
        self.server_tree = ttk.Treeview(top, columns=columns, show="tree headings", height=8)

        self.server_tree.heading("#0", text=STATUS_TEXT, anchor=tk.CENTER)
        self.server_tree.heading("name", text="Имя")
        self.server_tree.heading("url", text="URL")
        self.server_tree.heading("all", text="Всего")
        self.server_tree.heading("online", text="Онлайн")
        self.server_tree.heading("offline", text="Офлайн")

        # Make status column wider so it doesn't overlap text
        self.server_tree.column("#0", width=80, minwidth=80, anchor=tk.CENTER, stretch=False)
        self.server_tree.column("name", width=160, minwidth=120, anchor=tk.W, stretch=False)
        self.server_tree.column("url", width=300, minwidth=200, anchor=tk.W, stretch=True)
        self.server_tree.column("all", width=90, minwidth=60, anchor=tk.CENTER, stretch=False)
        self.server_tree.column("online", width=100, minwidth=60, anchor=tk.CENTER, stretch=False)
        self.server_tree.column("offline", width=100, minwidth=60, anchor=tk.CENTER, stretch=False)

        vsb = ttk.Scrollbar(top, orient="vertical", command=self.server_tree.yview)
        self.server_tree.configure(yscrollcommand=vsb.set)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.server_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # Bind click on empty area to deselect
        self.server_tree.bind("<Button-1>", self._on_server_left_click)
        self.server_tree.bind("<Button-3>", self._on_server_right_click)
        self.server_tree.bind("<Double-Button-1>", self._on_server_double_click)

        self.server_menu = tk.Menu(self.root, tearoff=0)
        self.server_menu.add_command(label="🌐 Открыть URL", command=self._ctx_open_server_url)
        self.server_menu.add_command(label="🔄 Обновить сервер", command=self._ctx_refresh_server)

        btn_frame = ttk.Frame(main)
        btn_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=5)

        # store refresh button so we can disable during update
        self.btn_refresh_servers = ttk.Button(btn_frame, text="Обнов. статус серверов", command=self.refresh_servers)
        self.btn_refresh_servers.pack(side=tk.LEFT, padx=5)

        ttk.Button(btn_frame, text="Шаблоны пик/дно", command=self.manage_templates).pack(side=tk.RIGHT, padx=5)
        self.btn_edit_config_btn = ttk.Button(btn_frame, text="Редактировать конфиг", command=self.open_config_editor)
        self.btn_edit_config_btn.pack(side=tk.RIGHT, padx=5)

        self._populate_servers()

    def _on_server_left_click(self, event):
        try:
            iid = self.server_tree.identify_row(event.y)
            if not iid:
                try:
                    self.server_tree.selection_remove(self.server_tree.selection())
                except Exception:
                    pass
                return "break"
        except Exception:
            pass

    def _build_tab_monitor(self):
        main = ttk.Frame(self.tab_monitor, padding=5)
        main.pack(fill=tk.BOTH, expand=True)

        status_frame = ttk.LabelFrame(main, text="Статус", padding=5)
        status_frame.pack(fill=tk.X, pady=(0, 5))

        self.status_var = tk.StringVar(
            value="Статус: Ожидание | Пик: --- | Дно: --- | Онлайн: --- | Офлайн: --- | До: ---")
        ttk.Label(status_frame, textvariable=self.status_var, font=("Arial", 10, "bold")).pack(padx=5, pady=5)

        log_frame = ttk.LabelFrame(main, text="Лог", padding=5)
        log_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 5))

        # Create a frame to hold the text widget and scrollbars
        text_frame = ttk.Frame(log_frame)
        text_frame.pack(fill=tk.BOTH, expand=True)

        # Monospace font for readability
        mono_font = ("Consolas", 10) if "Consolas" in tkfont.families() else ("Courier New", 10)

        self.log_widget = scrolledtext.ScrolledText(
            text_frame, height=20,
            wrap=tk.WORD, font=mono_font
        )
        self.log_widget.pack(fill=tk.BOTH, expand=True)

        # --- Make log read-only without DISABLED (copy always works) ---
        def _block_edit(event):
            return "break"

        for seq in (
                "<BackSpace>",
                "<Delete>",
                "<<Paste>>",
                "<<Cut>>"
        ):
            self.log_widget.bind(seq, _block_edit)

        # --- Restore standard Copy behavior (Ctrl+C, any layout) ---
        def _on_copy(event=None):
            try:
                self.log_widget.event_generate("<<Copy>>")
            except Exception:
                pass
            return "break"

        # --- Restore Copy for ANY keyboard layout (RU / EN) ---
        def _on_copy_any(event):
            # Ctrl is pressed (0x4) and there is a selection
            if event.state & 0x4:
                try:
                    self.log_widget.event_generate("<<Copy>>")
                    return "break"
                except Exception:
                    pass
            return None

        self.log_widget.bind("<Control-KeyPress>", _on_copy_any)
        self.log_widget.bind("<Control-Insert>", _on_copy_any)

        # Tag colors - text-only (no background)
        self.log_widget.tag_config("INF", foreground="#444444")  # subdued gray
        self.log_widget.tag_config("ACT", foreground="#666666")  # muted gray
        self.log_widget.tag_config("OK", foreground="#0A7F0A")  # dark green
        self.log_widget.tag_config("WARN", foreground="#BF6A00")  # warm orange
        self.log_widget.tag_config("ERR", foreground="#8B0000")  # dark red
        self.log_widget.tag_config("ALERT", foreground="#8B0000", font=(mono_font[0], mono_font[1], "bold"))

        self.logger.set_ui_callback(self._log_to_ui)

        # Buttons at bottom
        btn_frame = ttk.Frame(main, padding=(0, 5, 0, 0))
        btn_frame.pack(side=tk.BOTTOM, fill=tk.X)

        self.btn_start = ttk.Button(btn_frame, text="▶ Запуск", command=self.start_work)
        self.btn_start.pack(side=tk.LEFT, padx=5)

        self.btn_stop = ttk.Button(btn_frame, text="⬛ Стоп", command=self.stop_work, state=tk.DISABLED)
        self.btn_stop.pack(side=tk.LEFT, padx=5)

        ttk.Button(
            btn_frame,
            text="🔄 Обновить статус",
            command=self.refresh_process_status
        ).pack(side=tk.LEFT, padx=5)

        ttk.Button(
            btn_frame,
            text="🧹 Очистить лог",
            command=self.clear_log
        ).pack(side=tk.LEFT, padx=15)

        ttk.Button(btn_frame, text="Редактировать конфиг", command=self.open_config_editor).pack(side=tk.RIGHT, padx=5)

    def clear_log(self):
        self.log_widget.delete("1.0", tk.END)

    def _log_to_ui(self, level: str, message: str):
        def update():
            try:
                self.log_widget.insert(tk.END, message + "\n", level)
            except Exception:
                self.log_widget.insert(tk.END, message + "\n")
            self.log_widget.see(tk.END)

        self.root.after(0, update)

    def _on_engine_status_update(self, phase: str, peak: int, bottom: int, online: int, day: int):
        """
        Обновляет строку состояния и передаёт информацию о состоянии в UI.
        """
        instances = self.engine.get_active_instances()
        total_bots = sum(len(self.engine.all_bots.get(inst.get("url", ""), [])) for inst in instances)
        offline = total_bots - online

        time_peak = self.config.get("time_peak", "20:00")
        time_bottom = self.config.get("time_bottom", "06:00")

        now = datetime.now()
        today = now.date()

        # Определяем время до пика или дна
        peak_h, peak_m = map(int, time_peak.split(":"))
        bottom_h, bottom_m = map(int, time_bottom.split(":"))

        peak_dt = datetime.combine(today, datetime.min.time()).replace(hour=peak_h, minute=peak_m)
        bottom_dt = datetime.combine(today, datetime.min.time()).replace(hour=bottom_h, minute=bottom_m)

        if peak_dt <= now:
            peak_dt += timedelta(days=1)
        if bottom_dt <= now:
            bottom_dt += timedelta(days=1)

        seconds_to_peak = max(0, int((peak_dt - now).total_seconds()))
        seconds_to_bottom = max(0, int((bottom_dt - now).total_seconds()))

        if seconds_to_peak <= seconds_to_bottom:
            target_text = f"До пика: {_fmt_duration(seconds_to_peak)} ({time_peak})"
        else:
            target_text = f"До дна: {_fmt_duration(seconds_to_bottom)} ({time_bottom})"

        phase_translation = {
            "idle": "Ожидание",
            "ascending": "До пика ↑",
            "descending": "До дна ↓",
        }

        phase_ru = phase_translation.get(phase, phase)

        status = (
            f"Статус: {phase_ru} | День: {day} | "
            f"Пик: {peak} | Дно: {bottom} | "
            f"Онлайн (алгоритм): {online} | Онлайн (ASF): {self.engine.asf_online} | "
            f"Офлайн: {offline} | {target_text}"
        )
        self.root.after(0, lambda: self.status_var.set(status))

    def _on_server_right_click(self, event):
        iid = self.server_tree.identify_row(event.y)
        if not iid:
            return
        self.server_tree.selection_set(iid)
        self.server_tree.focus(iid)
        try:
            self.server_menu.tk_popup(event.x_root, event.y_root)
        finally:
            self.server_menu.grab_release()

    def _ctx_open_server_url(self):
        sel = self.server_tree.selection()
        if not sel:
            return
        iid = sel[0]
        if not iid.startswith("inst_"):
            return
        try:
            i = int(iid.replace("inst_", ""))
        except Exception:
            return
        instances = self.config.get("instances", [])
        if i < len(instances):
            url = instances[i].get("url", "")
            full_url = _ensure_http(url)
            if full_url:
                webbrowser.open(full_url)

    def _ctx_refresh_server(self):
        # For simplicity and to avoid partial updates we refresh all atomically
        if self._refresh_in_progress:
            return
        self.refresh_servers()

    def _populate_servers(self):
        self.server_tree.delete(*self.server_tree.get_children())
        instances = self.config.get("instances", [])
        for i, inst in enumerate(instances):
            name = inst.get("name", f"Server {i + 1}")
            url = inst.get("url", "")
            active = inst.get("active", True)
            icon_key = "gray" if not active else "red"
            self.server_tree.insert("", tk.END, iid=f"inst_{i}",
                                    image=self.status_icons.get(icon_key),
                                    values=(name, url, "---", "---", "---"))

    def refresh_servers(self):
        # Prevent concurrent refreshes
        if self._refresh_in_progress:
            return
        self._refresh_in_progress = True
        # disable refresh buttons to give visual feedback
        try:
            if hasattr(self, "btn_refresh_servers"):
                self.btn_refresh_servers.config(state=tk.DISABLED)
        except Exception:
            pass

        instances = self.config.get("instances", [])

        def worker():
            results = []  # (i, name, url, total, online, offline, icon_key)

            for i, inst in enumerate(instances):
                url = inst.get("url", "")
                active = inst.get("active", True)
                name = inst.get("name", "")

                if not active:
                    total = online = offline = 0
                    icon_key = "gray"
                else:
                    # безопасный разбор host:port
                    u = url.replace("http://", "").replace("https://", "")
                    host, port = u.split(":") if ":" in u else (u, "")
                    port = int(port) if port.isdigit() else None

                    ok = False
                    bots_map = None

                    # быстрый TCP-чек
                    if port and fast_port_check(host, port):
                        ok, bots_map, _ = get_bots_asf(
                            url,
                            self.ipc_password,
                            timeout=0.8
                        )

                    if ok and bots_map:
                        total, online, offline = compute_metrics_from_bots(bots_map)
                        icon_key = "green" if online > 0 else "yellow"
                    else:
                        total = online = offline = 0
                        icon_key = "red"

                results.append((i, name, url, total, online, offline, icon_key))

            # Apply results atomically in UI thread
            def apply():
                try:
                    # preserve selection and scroll position
                    try:
                        sel = self.server_tree.selection()
                        yview = self.server_tree.yview()
                    except Exception:
                        sel = None
                        yview = (0.0, 1.0)
                    self.server_tree.delete(*self.server_tree.get_children())
                    for i, name, url, total, online, offline, icon_key in results:
                        iid = f"inst_{i}"
                        self.server_tree.insert("", tk.END, iid=iid,
                                                image=self.status_icons.get(icon_key),
                                                values=(name, url, str(total), str(online), str(offline)))
                    # restore selection and scroll
                    try:
                        if sel:
                            self.server_tree.selection_set(sel)
                        self.server_tree.yview_moveto(yview[0])
                    except Exception:
                        pass
                finally:
                    self._refresh_in_progress = False
                    try:
                        if hasattr(self, "btn_refresh_servers"):
                            self.btn_refresh_servers.config(state=tk.NORMAL)
                    except Exception:
                        pass

            self.root.after(0, apply)

        threading.Thread(target=worker, daemon=True).start()

    def _on_server_double_click(self, event):
        iid = self.server_tree.identify_row(event.y)
        if not iid or not iid.startswith("inst_"):
            return
        try:
            idx = int(iid.replace("inst_", ""))
        except ValueError:
            return
        instances = self.config.get("instances", [])
        if 0 <= idx < len(instances):
            BotsViewWindow(self.root, instances[idx], self.ipc_password, self)

    def view_bots(self):
        sel = self.server_tree.selection()
        if not sel:
            messagebox.showwarning("Выбор", "Выберите сервер для просмотра")
            return
        iid = sel[0]
        if not iid.startswith("inst_"):
            messagebox.showwarning("Выбор", "Выберите сервер для просмотра")
            return
        try:
            i = int(iid.replace("inst_", ""))
        except ValueError:
            messagebox.showwarning("Выбор", "Выберите сервер для просмотра")
            return
        instances = self.config.get("instances", [])
        if 0 <= i < len(instances):
            BotsViewWindow(self.root, instances[i], self.ipc_password, self)

    def open_config_editor(self):
        ConfigEditorCCU(self.root, self.config, self._on_config_saved)

    def _on_config_saved(self):
        self.config = load_json_config(CONFIG_CCU, default_config_ccu())
        self.ipc_password = str(self.config.get("ipc_password", DEFAULT_IPC_PASSWORD) or DEFAULT_IPC_PASSWORD)
        self.engine.reload_config(self.config)
        self._populate_servers()

    def manage_templates(self):
        TemplatesWindow(self.root)

    def start_work(self):
        """
        Метод запуска работы.
        """
        if self.engine.is_running:
            self.logger.info("Уже выполняется процесс работы.")
            return

        self.logger.info("Выполняется начальная синхронизация состояния ASF...")
        self.engine.sync_bots_state_from_asf()

        # Проверяем, есть ли доступные боты для запуска
        total_bots = sum(len(bots) for bots in self.engine.bots_in_game.values())  # Берём только доступные инстансы
        if total_bots == 0:
            self.logger.warn("Не хватает ботов для запуска. Проверьте конфигурацию.")
            return

        self.logger.info(f"Всего ботов: {total_bots} (ONLINE: {self.engine.current_online})")

        # Запуск основного рабочего цикла
        self.engine.start(resume=False)
        self.btn_start.config(state=tk.DISABLED)
        self.btn_stop.config(state=tk.NORMAL)
        self.log_widget.config(state=tk.NORMAL)
        self.log_widget.focus_set()

    def stop_work(self):
        if not self.engine.is_running:
            return

        result = ask_exit_all_accounts(self.root)

        # Отмена (крестик / Esc)
        if result is None:
            return

        # Да — выйти из игры на всех аккаунтах
        if result is True:
            instances = self.engine.get_active_instances()
            for inst in instances:
                url = inst.get("url", "")
                send_command(url, "reset ASF", self.ipc_password)

        # Нет — просто останавливаем движок
        self.engine.stop()
        self.btn_start.config(state=tk.NORMAL)
        self.btn_stop.config(state=tk.DISABLED)

    def _start_monitoring(self):
        def monitor():
            while not self.monitor_stop.is_set():
                if self.engine.is_running:
                    self.engine.check_and_restore_fallen_bots()
                    self.engine.save_session_state()
                time.sleep(10)

        self.monitor_thread = threading.Thread(target=monitor, daemon=True)
        self.monitor_thread.start()

    def _check_session_recovery(self):
        state = self.engine.load_session_state()
        if state and state.get("is_running"):
            result = messagebox.askyesno(
                "Восстановление",
                "Обнаружена незавершённая сессия. Продолжить работу?"
            )

            # 🔧 ВАЖНО: вернуть фокус в лог (иначе текст не выделяется)
            self.root.after(0, lambda: self.log_widget.focus_force())

            if result:
                self.engine.current_day = state.get("current_day", 1)
                self.engine.current_online = state.get("current_online", 0)
                self.engine.bots_in_game = state.get("bots_in_game", {})
                self.engine.start()
                self.btn_start.config(state=tk.DISABLED)
                self.btn_stop.config(state=tk.NORMAL)
            else:
                self.engine.clear_session_state()

    def on_close(self):
        if self.engine.is_running:
            result = ask_exit_all_accounts(self.root)

            # Отмена (крестик / Esc)
            if result is None:
                return

            # Да — выйти из игры на всех аккаунтах (НЕ сохраняем состояние)
            if result is True:
                instances = self.engine.get_active_instances()
                for inst in instances:
                    url = inst.get("url", "")
                    send_command(url, "reset ASF", self.ipc_password)
                self.engine.clear_session_state()

            # Нет — сохраняем состояние для resume
            else:
                self.engine.save_session_state()

            self.engine.command_stop_event.set()

            self.engine.stop()

        self.monitor_stop.set()
        self.root.destroy()

def main():
        root = tk.Tk()
        app = CCUManagerApp(root)
        root.protocol("WM_DELETE_WINDOW", app.on_close)
        root.mainloop()

if __name__ == "__main__":
        try:
            main()
        except Exception:
            print("\n===== ПРОИЗОШЛА ОШИБКА =====\n")
            traceback.print_exc()
            print("\nНажмите любую клавишу для выхода...")
            input()
            sys.exit(1)
