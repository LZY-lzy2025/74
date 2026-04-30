import os
import requests
from bs4 import BeautifulSoup
import base64
import re
import urllib.parse
import json
from datetime import datetime, timedelta
import pytz
from playwright.sync_api import sync_playwright, TimeoutError as PlaywrightTimeoutError
from flask import Flask, jsonify, Response
from apscheduler.schedulers.background import BackgroundScheduler
import gc  # 新增：用于强制垃圾回收
from contextlib import suppress
import threading
import atexit
from requests.adapters import HTTPAdapter
import ctypes
import resource
from collections import deque
import subprocess
import sys

app = Flask(__name__)
OUTPUT_FILE = 'output/extracted_ids.txt'
ROUTE_STATE_FILE = 'output/decoded_routes.jsonl'
LAST_RUN_TIME = "尚未执行"
REFRESH_INTERVAL_RUNS = 2
SCRAPE_JOB_LOCK = threading.Lock()
PAGE_GOTO_TIMEOUT_MS = 20000
PAGE_GOTO_RETRY_TIMEOUT_MS = 35000
PAGE_WAIT_FOR_PAPS_MS = 10000
PAGE_WAIT_FOR_PAPS_RETRY_MS = 15000
PAGE_GOTO_MAX_RETRIES = 2
MAX_EVENTS_PER_ROUTE = 30
ROUTE_DIAGNOSTIC_RETENTION_HOURS = 5
MEMORY_SNAPSHOT_LIMIT = 200
MEMORY_SNAPSHOTS = deque(maxlen=MEMORY_SNAPSHOT_LIMIT)
SCRAPE_SUBPROCESS_TIMEOUT_SEC = 11 * 60
LAST_SUBPROCESS_PID = None
LAST_SUBPROCESS_STARTED_AT = None


def release_memory():
    """
    主动触发 Python GC，并尝试调用 libc.malloc_trim(0) 归还堆内存给操作系统。
    说明：不改变抓取逻辑，仅用于降低长时间运行后的 RSS 持续攀升。
    """
    gc.collect()
    gc.collect()
    with suppress(Exception):
        libc = ctypes.CDLL("libc.so.6")
        libc.malloc_trim(0)


def get_rss_mb():
    """获取当前进程 RSS（MB），优先读取 /proc，失败时回退到 resource。"""
    with suppress(Exception):
        with open("/proc/self/status", "r", encoding="utf-8") as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    parts = line.split()
                    if len(parts) >= 2:
                        return round(int(parts[1]) / 1024, 2)
    with suppress(Exception):
        # Linux 下 ru_maxrss 单位通常是 KB；回退场景只用于趋势观察
        return round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024, 2)
    return -1.0


def log_memory_snapshot(stage, run_at):
    rss_mb = get_rss_mb()
    snapshot = {
        "time": run_at,
        "stage": stage,
        "rss_mb": rss_mb if rss_mb >= 0 else None
    }
    MEMORY_SNAPSHOTS.append(snapshot)
    return snapshot


def read_cgroup_memory_mb():
    """读取容器(cgroup)内存占用，优先兼容 cgroup v2，再回退 v1。"""
    for candidate in ("/sys/fs/cgroup/memory.current", "/sys/fs/cgroup/memory/memory.usage_in_bytes"):
        with suppress(Exception):
            with open(candidate, "r", encoding="utf-8") as f:
                raw = f.read().strip()
                if raw:
                    return round(int(raw) / (1024 * 1024), 2)
    return None


def read_cgroup_memory_limit_mb():
    """读取容器(cgroup)内存上限，无法识别时返回 None。"""
    for candidate in ("/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory/memory.limit_in_bytes"):
        with suppress(Exception):
            with open(candidate, "r", encoding="utf-8") as f:
                raw = f.read().strip()
                if not raw or raw == "max":
                    return None
                limit_bytes = int(raw)
                # 极大值一般代表未限制，按未知处理
                if limit_bytes <= 0 or limit_bytes >= (1 << 60):
                    return None
                return round(limit_bytes / (1024 * 1024), 2)
    return None


def is_pid_alive(pid):
    if not pid:
        return False
    with suppress(Exception):
        os.kill(pid, 0)
        return True
    return False

# ==========================================
# 核心：内置轻量级 XXTEA 解密算法
# ==========================================
def str2long(s, w):
    v = []
    for i in range(0, len(s), 4):
        v0 = s[i]
        v1 = s[i+1] if i+1 < len(s) else 0
        v2 = s[i+2] if i+2 < len(s) else 0
        v3 = s[i+3] if i+3 < len(s) else 0
        v.append(v0 | (v1 << 8) | (v2 << 16) | (v3 << 24))
    if w:
        v.append(len(s))
    return v

def long2str(v, w):
    vl = len(v)
    if vl == 0: return b""
    n = (vl - 1) << 2
    if w:
        m = v[-1]
        if (m < n - 3) or (m > n): return None
        n = m
    s = bytearray()
    for i in range(vl):
        s.append(v[i] & 0xff)
        s.append((v[i] >> 8) & 0xff)
        s.append((v[i] >> 16) & 0xff)
        s.append((v[i] >> 24) & 0xff)
    return bytes(s[:n]) if w else bytes(s)

def xxtea_decrypt(data, key):
    if not data: return b""
    v = str2long(data, False)
    k = str2long(key, False)
    if len(k) < 4:
        k.extend([0] * (4 - len(k)))
    n = len(v) - 1
    if n < 1: return b""
    
    z = v[n]
    y = v[0]
    delta = 0x9E3779B9
    q = 6 + 52 // (n + 1)
    sum_val = (q * delta) & 0xffffffff
    
    while sum_val != 0:
        e = (sum_val >> 2) & 3
        for p in range(n, 0, -1):
            z = v[p - 1]
            mx = (((z >> 5) ^ (y << 2)) + ((y >> 3) ^ (z << 4))) ^ ((sum_val ^ y) + (k[(p & 3) ^ e] ^ z))
            y = v[p] = (v[p] - mx) & 0xffffffff
        z = v[n]
        mx = (((z >> 5) ^ (y << 2)) + ((y >> 3) ^ (z << 4))) ^ ((sum_val ^ y) + (k[(0 & 3) ^ e] ^ z))
        y = v[0] = (v[0] - mx) & 0xffffffff
        sum_val = (sum_val - delta) & 0xffffffff
        
    return long2str(v, True)

def decode_stream_from_id(raw_id):
    """将抓取到的 ID 解密为直播源 URL，失败返回 None。"""
    target_key = b"ABCDEFGHIJKLMNOPQRSTUVWX"
    try:
        decoded_id = urllib.parse.unquote(raw_id)
        pad = 4 - (len(decoded_id) % 4)
        if pad != 4:
            decoded_id += "=" * pad
        bin_data = base64.b64decode(decoded_id)
        decrypted_bytes = xxtea_decrypt(bin_data, target_key)
        if not decrypted_bytes:
            return None
        json_str = decrypted_bytes.decode('utf-8', errors='ignore')
        data = json.loads(json_str)
        return data.get("url")
    except Exception:
        return None

def get_keep_window(now, tz):
    """保留窗口：当前时间前后 7 小时内。"""
    keep_start = now - timedelta(hours=7)
    keep_end = now + timedelta(hours=7)
    return keep_start, keep_end

def load_existing_records(now, tz):
    """加载历史成功记录，并按照保留窗口过滤。"""
    keep_start, keep_end = get_keep_window(now, tz)
    records = []
    if os.path.exists(OUTPUT_FILE):
        with open(OUTPUT_FILE, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if not line or not line.startswith('{'):
                    continue
                try:
                    item = json.loads(line)
                    item_match_time = item.get("match_time")
                    if not item_match_time:
                        continue
                    match_time = datetime.strptime(item_match_time, "%Y-%m-%d %H:%M:%S")
                    match_time = tz.localize(match_time)
                    if keep_start <= match_time <= keep_end and item.get("source_url") and item.get("stream_url"):
                        records.append(item)
                except Exception:
                    continue
    return records

def load_route_states(now, tz):
    """加载线路解密状态，并清理保留窗口外数据。"""
    keep_start, keep_end = get_keep_window(now, tz)
    states = {}
    if os.path.exists(ROUTE_STATE_FILE):
        with open(ROUTE_STATE_FILE, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    item = json.loads(line)
                    source_url = item.get("source_url")
                    match_time_str = item.get("match_time")
                    if not source_url or not match_time_str:
                        continue
                    match_time = tz.localize(datetime.strptime(match_time_str, "%Y-%m-%d %H:%M:%S"))
                    if keep_start <= match_time <= keep_end:
                        states[source_url] = item
                except Exception:
                    continue
    return states

def save_route_states(states):
    os.makedirs('output', exist_ok=True)
    with open(ROUTE_STATE_FILE, 'w', encoding='utf-8') as f:
        for item in states.values():
            f.write(json.dumps(item, ensure_ascii=False) + '\n')

def append_route_event(route_state, stage, message, extra=None):
    """记录线路处理过程中的事件轨迹，便于逐步排查。"""
    events = route_state.setdefault("events", [])
    payload = {
        "time": route_state.get("last_checked_at"),
        "stage": stage,
        "message": message
    }
    if extra:
        payload["extra"] = extra
    events.append(payload)
    if len(events) > MAX_EVENTS_PER_ROUTE:
        del events[:-MAX_EVENTS_PER_ROUTE]

def should_schedule_refresh(route_state):
    """只要已抓到直播源，就按固定抓取轮次触发重抓。"""
    if not route_state.get("resolved") or not route_state.get("stream_url"):
        route_state["refresh_counter"] = 0
        return False

    refresh_counter = route_state.get("refresh_counter", 0) + 1
    if refresh_counter >= REFRESH_INTERVAL_RUNS:
        route_state["refresh_counter"] = 0
        return True

    route_state["refresh_counter"] = refresh_counter
    return False

def has_paps_request(requests_list):
    return any("paps.html?id=" in req_url for req_url in requests_list)

def prune_route_states(route_states, now, tz):
    """定时清理旧线路状态，避免状态文件与内存持续增长。"""
    keep_start, keep_end = get_keep_window(now, tz)
    stale_urls = []
    for source_url, state in route_states.items():
        match_time_str = state.get("match_time")
        if not match_time_str:
            stale_urls.append(source_url)
            continue
        try:
            match_time = tz.localize(datetime.strptime(match_time_str, "%Y-%m-%d %H:%M:%S"))
        except Exception:
            stale_urls.append(source_url)
            continue
        if not (keep_start <= match_time <= keep_end):
            stale_urls.append(source_url)
    for source_url in stale_urls:
        route_states.pop(source_url, None)


def cleanup_route_diagnostics(route_states, now, tz):
    """
    清理超过保留时长的线路诊断字段，避免排错数据长期占用内存与状态文件。
    不影响核心抓取结果字段（id/source_url/stream_url/match_time 等）。
    """
    cutoff = now - timedelta(hours=ROUTE_DIAGNOSTIC_RETENTION_HOURS)
    for state in route_states.values():
        checked_at = state.get("last_checked_at")
        if not checked_at:
            continue
        try:
            checked_dt = tz.localize(datetime.strptime(checked_at, "%Y-%m-%d %H:%M:%S"))
        except Exception:
            continue

        if checked_dt < cutoff:
            state["events"] = []
            state["last_error"] = None
            state["last_request_count"] = 0
            state["last_seen_paps_url"] = None

# ==========================================
# 爬虫任务逻辑
# ==========================================
def scrape_job_once(run_label=None):
    tz = pytz.timezone('Asia/Shanghai')
    now = datetime.now(tz)
    run_label = run_label or now.strftime('%Y-%m-%d %H:%M:%S')
    print(f"[{run_label}] 开始执行抓取任务...")
    log_memory_snapshot("start", run_label)
    try:
        
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36'
        }
        
        try:
            with requests.Session() as session:
                session.mount('http://', HTTPAdapter(pool_connections=10, pool_maxsize=10, max_retries=0))
                session.mount('https://', HTTPAdapter(pool_connections=10, pool_maxsize=10, max_retries=0))
                res = session.get('https://www.74001.tv', headers=headers, timeout=10)
                res.raise_for_status()
                soup = BeautifulSoup(res.text, 'html.parser')

                # 存储比赛基础信息：match_id -> info_dict
                match_infos = {}
                lower_bound = now - timedelta(hours=4)
                upper_bound = now + timedelta(hours=1)

                for a in soup.select('a.clearfix'):
                    href = a.get('href')
                    time_str = a.get('t-nzf-o')
                    if href and '/bofang/' in href and time_str:
                        try:
                            if len(time_str) == 10:
                                time_str += " 00:00:00"
                            match_time = tz.localize(datetime.strptime(time_str, '%Y-%m-%d %H:%M:%S'))
                            
                            if lower_bound <= match_time <= upper_bound:
                                match_id = href.split('/')[-1]
                                
                                em_tag = a.select_one('.eventtime em')
                                league = em_tag.text.strip() if em_tag else "未知联赛"
                                
                                zhudui_tag = a.select_one('.zhudui p')
                                home = zhudui_tag.text.strip() if zhudui_tag else "未知主队"
                                
                                kedui_tag = a.select_one('.kedui p')
                                away = kedui_tag.text.strip() if kedui_tag else "未知客队"
                                
                                time_i_tag = a.select_one('.eventtime i')
                                display_time = time_i_tag.text.strip() if time_i_tag else match_time.strftime('%H:%M')
                                
                                match_infos[match_id] = {
                                    'match_time': match_time.strftime('%Y-%m-%d %H:%M:%S'),
                                    'time': display_time,
                                    'league': league,
                                    'home': home,
                                    'away': away
                                }
                        except Exception:
                            continue

                play_url_to_info = {}
                for match_id, info in match_infos.items():
                    link = f"https://www.74001.tv/live/{match_id}"
                    try:
                        res = session.get(link, headers=headers, timeout=10)
                        res.raise_for_status()
                        soup = BeautifulSoup(res.text, 'html.parser')
                        for dd in soup.select('dd[nz-g-c]'):
                            if dd.get('nz-g-ca'):
                                continue  # 直接跳过播线路

                            b64_str = dd.get('nz-g-c')
                            if b64_str:
                                b64_str += "=" * ((4 - len(b64_str) % 4) % 4)
                                decoded = base64.b64decode(b64_str).decode('utf-8', errors='ignore')
                                m = re.search(r'ftp:\*\*(.*?)(?:::|$)', decoded)
                                if m:
                                    raw_url = m.group(1)
                                    url = 'http://' + raw_url.replace('!', '.').replace('&nbsp', 'com').replace('*', '/')
                                    play_url_to_info[url] = info
                    except Exception:
                        continue
        except Exception as e:
            print(f"获取主页失败: {e}")
            return

        existing_records = load_existing_records(now, tz)
        route_states = load_route_states(now, tz)

        for url, info in play_url_to_info.items():
            old = route_states.get(url, {})
            route_states[url] = {
                "source_url": url,
                "match_time": info["match_time"],
                "time": info["time"],
                "league": info["league"],
                "home": info["home"],
                "away": info["away"],
                "resolved": old.get("resolved", False),
                "id": old.get("id"),
                "stream_url": old.get("stream_url"),
                "refresh_counter": old.get("refresh_counter", 0),
                "last_stage": old.get("last_stage", "initialized"),
                "last_error": old.get("last_error"),
                "last_checked_at": old.get("last_checked_at"),
                "attempt_count": old.get("attempt_count", 0),
                "last_request_count": old.get("last_request_count", 0),
                "last_seen_paps_url": old.get("last_seen_paps_url"),
                "events": []
            }
            append_route_event(route_states[url], "initialized", "线路进入本轮调度队列")

        refresh_candidates = set()
        for source_url, state in route_states.items():
            if should_schedule_refresh(state):
                refresh_candidates.add(source_url)

        success_by_source_url = {
            source_url for source_url, state in route_states.items()
            if state.get("resolved") and state.get("stream_url")
        } - refresh_candidates

        final_data = []
        for source_url in success_by_source_url:
            state = route_states[source_url]
            if state.get("id") and state.get("stream_url"):
                final_data.append({
                    'id': state["id"],
                    'source_url': source_url,
                    'stream_url': state["stream_url"],
                    'match_time': state["match_time"],
                    'time': state["time"],
                    'league': state["league"],
                    'home': state["home"],
                    'away': state["away"]
                })
        final_data_index = {item["source_url"]: idx for idx, item in enumerate(final_data)}

        for item in existing_records:
            if item["source_url"] not in success_by_source_url:
                final_data_index[item["source_url"]] = len(final_data)
                final_data.append(item)
                success_by_source_url.add(item["source_url"])
            
        seen_ids = set()
        seen_source_urls = set(success_by_source_url)

        for item in final_data:
            if item.get("id"):
                seen_ids.add(item["id"])

        # ====== Playwright 抓取流程 (含全面防泄漏防护) ======
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                args=[
                    '--no-sandbox',
                    '--disable-setuid-sandbox',
                    '--disable-dev-shm-usage',
                    '--disable-gpu',
                    '--js-flags="--max-old-space-size=512"', # 限制 V8 引擎最大内存为 512MB
                    '--disable-background-networking',       # 禁用后台网络请求
                    '--disable-background-timer-throttling'  # 禁用后台节流
                ]
            )

            try: # 【关键修复】：外层 try...finally 确保进程终结
                for url, info in play_url_to_info.items():
                    if url in success_by_source_url:
                        route_states[url]["last_stage"] = "cached_success"
                        route_states[url]["last_error"] = None
                        route_states[url]["last_checked_at"] = LAST_RUN_TIME
                        append_route_event(route_states[url], "cached_success", "命中缓存成功线路，本轮跳过Playwright抓取")
                        continue

                    context = browser.new_context(
                        user_agent='Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
                        viewport={'width': 1280, 'height': 720},
                        extra_http_headers={
                            'Accept-Language': 'zh-CN,zh;q=0.9',
                            'Referer': 'https://www.74001.tv/'
                        }
                    )
                    page = context.new_page()
                    page.add_init_script("Object.defineProperty(navigator, 'webdriver', {get: () => undefined})")

                    requests_list = []

                    # 【关键修复】：使用具名函数避免闭包导致的循环引用
                    def handle_request(request):
                        requests_list.append(request.url)

                    try:
                        route_states[url]["attempt_count"] = route_states[url].get("attempt_count", 0) + 1
                        route_states[url]["last_stage"] = "page_loading"
                        route_states[url]["last_error"] = None
                        route_states[url]["last_checked_at"] = LAST_RUN_TIME
                        append_route_event(route_states[url], "page_loading", "开始使用Playwright加载线路页面")

                        page.on("request", handle_request)

                        last_timeout_error = None
                        for attempt in range(1, PAGE_GOTO_MAX_RETRIES + 1):
                            goto_timeout = PAGE_GOTO_TIMEOUT_MS if attempt == 1 else PAGE_GOTO_RETRY_TIMEOUT_MS
                            wait_for_paps_ms = PAGE_WAIT_FOR_PAPS_MS if attempt == 1 else PAGE_WAIT_FOR_PAPS_RETRY_MS
                            try:
                                page.goto(url, wait_until='commit', timeout=goto_timeout)
                                last_timeout_error = None
                            except PlaywrightTimeoutError as e:
                                last_timeout_error = str(e)
                                append_route_event(
                                    route_states[url],
                                    "goto_timeout",
                                    "页面加载超时，准备按策略重试",
                                    {"attempt": attempt, "timeout_ms": goto_timeout}
                                )
                                if has_paps_request(requests_list):
                                    append_route_event(
                                        route_states[url],
                                        "goto_timeout_but_paps_seen",
                                        "虽然页面超时，但已经捕获到播放器ID请求，继续解析",
                                        {"attempt": attempt}
                                    )
                                    last_timeout_error = None
                            waited_ms = 0
                            while waited_ms < wait_for_paps_ms and not has_paps_request(requests_list):
                                page.wait_for_timeout(500)
                                waited_ms += 500
                            if has_paps_request(requests_list):
                                last_timeout_error = None
                                break
                        if last_timeout_error:
                            raise PlaywrightTimeoutError(last_timeout_error)

                        route_states[url]["last_request_count"] = len(requests_list)
                        route_states[url]["last_stage"] = "searching_paps_id"
                        append_route_event(
                            route_states[url],
                            "searching_paps_id",
                            "页面加载完成，开始扫描请求列表中的播放器ID",
                            {"request_count": len(requests_list)}
                        )

                        found_paps = False
                        for req_url in requests_list:
                            if 'paps.html?id=' in req_url:
                                found_paps = True
                                route_states[url]["last_seen_paps_url"] = req_url
                                append_route_event(
                                    route_states[url],
                                    "paps_found",
                                    "检测到播放器ID请求",
                                    {"paps_url": req_url}
                                )
                                extracted_id = req_url.split('paps.html?id=')[-1]
                                can_replace = url in refresh_candidates
                                if (can_replace or extracted_id not in seen_ids) and (can_replace or url not in seen_source_urls):
                                    stream_url = decode_stream_from_id(extracted_id)
                                    if stream_url:
                                        route_states[url]["resolved"] = True
                                        route_states[url]["id"] = extracted_id
                                        route_states[url]["stream_url"] = stream_url
                                        route_states[url]["refresh_counter"] = 0
                                        route_states[url]["last_stage"] = "resolved"
                                        route_states[url]["last_error"] = None
                                        append_route_event(
                                            route_states[url],
                                            "resolved",
                                            "线路解密成功，已得到stream_url",
                                            {"stream_url": stream_url}
                                        )
                                        new_item = {
                                            'id': extracted_id,
                                            'source_url': url,
                                            'stream_url': stream_url,
                                            'match_time': info['match_time'],
                                            'time': info['time'],
                                            'league': info['league'],
                                            'home': info['home'],
                                            'away': info['away']
                                        }
                                        if can_replace and url in final_data_index:
                                            final_data[final_data_index[url]] = new_item
                                        else:
                                            final_data_index[url] = len(final_data)
                                            final_data.append(new_item)
                                        seen_ids.add(extracted_id)
                                        seen_source_urls.add(url)
                                    else:
                                        route_states[url]["last_stage"] = "decode_failed"
                                        route_states[url]["last_error"] = "提取到ID，但解密后未得到stream_url"
                                        append_route_event(
                                            route_states[url],
                                            "decode_failed",
                                            "提取到ID但解密失败，未获得可用stream_url"
                                        )
                                else:
                                    route_states[url]["last_stage"] = "skipped_duplicate"
                                    route_states[url]["last_error"] = "提取到的ID或线路已存在，跳过覆盖"
                                    append_route_event(
                                        route_states[url],
                                        "skipped_duplicate",
                                        "线路或ID已存在，按去重规则跳过覆盖",
                                        {"can_replace": can_replace}
                                    )
                                break
                        if not found_paps:
                            route_states[url]["last_stage"] = "missing_paps_id"
                            route_states[url]["last_error"] = "页面请求中未发现 paps.html?id=..."
                            sample_urls = requests_list[:5]
                            append_route_event(
                                route_states[url],
                                "missing_paps_id",
                                "未在请求列表中发现播放器ID请求，可能是线路失效/前端策略变更",
                                {"sample_requests": sample_urls}
                            )
                    except Exception as e:
                        print(f"解析页面失败 {url}: {e}")
                        route_states[url]["last_stage"] = "page_error"
                        route_states[url]["last_error"] = str(e)
                        route_states[url]["last_checked_at"] = LAST_RUN_TIME
                        append_route_event(route_states[url], "page_error", "页面处理异常", {"error": str(e)})
                        continue
                    finally:
                        # 【关键修复】：清理监听事件，切断闭包引用，主动关闭上下文
                        with suppress(Exception):
                            page.remove_listener("request", handle_request)
                        requests_list.clear()
                        with suppress(Exception):
                            page.close()
                        with suppress(Exception):
                            context.close()
            finally:
                # 【关键修复】：彻底关闭无头浏览器进程
                browser.close()
        # ==========================================

        os.makedirs('output', exist_ok=True)
        with open(OUTPUT_FILE, 'w', encoding='utf-8') as f:
            for item in final_data:
                f.write(json.dumps(item, ensure_ascii=False) + '\n')
        prune_route_states(route_states, now, tz)
        cleanup_route_diagnostics(route_states, now, tz)
        save_route_states(route_states)
        
        print(f"任务完成，共保存 {len(final_data)} 个记录。")
        release_memory()
        log_memory_snapshot("after_release", run_label)
    finally:
        release_memory()
        log_memory_snapshot("finally_release", run_label)


def scrape_job():
    if not SCRAPE_JOB_LOCK.acquire(blocking=False):
        print("上一次抓取任务仍在执行，跳过本轮调度。")
        return

    global LAST_RUN_TIME, LAST_SUBPROCESS_PID, LAST_SUBPROCESS_STARTED_AT
    try:
        tz = pytz.timezone('Asia/Shanghai')
        now = datetime.now(tz)
        LAST_RUN_TIME = now.strftime('%Y-%m-%d %H:%M:%S')
        log_memory_snapshot("scheduler_start", LAST_RUN_TIME)

        env = os.environ.copy()
        env["SCRAPE_ONCE"] = "1"
        env["SCRAPE_RUN_LABEL"] = LAST_RUN_TIME

        try:
            proc = subprocess.Popen([sys.executable, os.path.abspath(__file__)], env=env)
            LAST_SUBPROCESS_PID = proc.pid
            LAST_SUBPROCESS_STARTED_AT = LAST_RUN_TIME
            result = proc.wait(timeout=SCRAPE_SUBPROCESS_TIMEOUT_SEC)
            log_memory_snapshot("scheduler_after_subprocess", LAST_RUN_TIME)
            if result != 0:
                print(f"抓取子进程退出异常，exit_code={result}")
        except subprocess.TimeoutExpired:
            print(f"抓取子进程超时（>{SCRAPE_SUBPROCESS_TIMEOUT_SEC}秒），已终止本轮。")
            with suppress(Exception):
                proc.kill()
                proc.wait(timeout=5)
            log_memory_snapshot("scheduler_timeout", LAST_RUN_TIME)
        finally:
            LAST_SUBPROCESS_PID = None
    finally:
        release_memory()
        log_memory_snapshot("scheduler_finally", LAST_RUN_TIME)
        SCRAPE_JOB_LOCK.release()

# ==========================================
# 统一的播放列表生成逻辑
# ==========================================
def generate_playlist(fmt="m3u", mode="clean"):
    if not os.path.exists(OUTPUT_FILE):
        return "请稍后再试，爬虫尚未生成数据"
        
    with open(OUTPUT_FILE, 'r', encoding='utf-8') as f:
        lines = [line.strip() for line in f.readlines() if line.strip()]
    
    if fmt == "m3u":
        content = "#EXTM3U\n"
    else:
        content = "74体育,#genre#\n"
        
    index = 1
    
    for line in lines:
        try:
            if line.startswith('{'):
                item = json.loads(line)
                # 修复名字空格
                channel_name = f"{item['time']} {item['home']}VS{item['away']}".replace(" ", "")
                # 设置固定分组为 74体育
                group_title = "74体育" 
                stream_url = item.get("stream_url")
            else:
                channel_name = f"74体育 {index}"
                # 设置固定分组为 74体育
                group_title = "74体育" 
                stream_url = decode_stream_from_id(line)

            if stream_url:
                if mode == "plus":
                    stream_url = f"{stream_url}|Referer="

                if fmt == "m3u":
                    content += f'#EXTINF:-1 group-title="{group_title}",{channel_name}\n{stream_url}\n'
                else:
                    content += f'{channel_name},{stream_url}\n'

                index += 1
        except Exception:
            continue
            
    return content

# ==========================================
# Web 接口
# ==========================================
@app.route('/')
def index():
    return jsonify({
        "status": "running",
        "last_run_time": LAST_RUN_TIME,
        "endpoints": ["/ids", "/m3u", "/m3u_plus", "/txt", "/txt_plus", "/memory_stats"]
    })

@app.route('/memory_stats')
def get_memory_stats():
    current_rss = get_rss_mb()
    cgroup_usage_mb = read_cgroup_memory_mb()
    cgroup_limit_mb = read_cgroup_memory_limit_mb()
    return jsonify({
        "last_run_time": LAST_RUN_TIME,
        "current_rss_mb": current_rss if current_rss >= 0 else None,
        "cgroup_memory_usage_mb": cgroup_usage_mb,
        "cgroup_memory_limit_mb": cgroup_limit_mb,
        "subprocess": {
            "pid": LAST_SUBPROCESS_PID,
            "is_running": is_pid_alive(LAST_SUBPROCESS_PID),
            "started_at": LAST_SUBPROCESS_STARTED_AT
        },
        "snapshot_limit": MEMORY_SNAPSHOT_LIMIT,
        "snapshots": list(MEMORY_SNAPSHOTS)
    })

@app.route('/m3u')
def get_m3u_clean():
    return Response(generate_playlist("m3u", "clean"), mimetype='text/plain; charset=utf-8', headers={"Access-Control-Allow-Origin": "*"})

@app.route('/m3u_plus')
def get_m3u_plus():
    return Response(generate_playlist("m3u", "plus"), mimetype='text/plain; charset=utf-8', headers={"Access-Control-Allow-Origin": "*"})

@app.route('/txt')
def get_txt_clean():
    return Response(generate_playlist("txt", "clean"), mimetype='text/plain; charset=utf-8', headers={"Access-Control-Allow-Origin": "*"})

@app.route('/txt_plus')
def get_txt_plus():
    return Response(generate_playlist("txt", "plus"), mimetype='text/plain; charset=utf-8', headers={"Access-Control-Allow-Origin": "*"})

if __name__ == "__main__":
    if os.getenv("SCRAPE_ONCE") == "1":
        scrape_job_once(os.getenv("SCRAPE_RUN_LABEL"))
        raise SystemExit(0)

    scheduler = BackgroundScheduler(
        timezone="Asia/Shanghai",
        executors={"default": {"type": "threadpool", "max_workers": 1}},
        job_defaults={"coalesce": True, "max_instances": 1, "misfire_grace_time": 60}
    )
    scheduler.add_job(scrape_job, 'interval', minutes=12, next_run_time=datetime.now())
    scheduler.start()
    atexit.register(lambda: scheduler.shutdown(wait=False))
    app.run(host='0.0.0.0', port=5000, use_reloader=False)
