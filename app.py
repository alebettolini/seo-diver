import os
import re
import ssl
import time
import json
import gzip
import random
import sqlite3
import asyncio
import hashlib
import tempfile
import warnings
from io import BytesIO
from datetime import datetime
from urllib.parse import urljoin, urlparse, urlunparse, urldefrag, parse_qsl, urlencode
from urllib.robotparser import RobotFileParser
from collections import deque, defaultdict, Counter

import streamlit as st
import pandas as pd
import requests
from bs4 import BeautifulSoup
from openpyxl import Workbook

try:
    import psutil
    HAS_PSUTIL = True
except ImportError:
    HAS_PSUTIL = False

try:
    import tldextract
    HAS_TLDEXTRACT = True
except ImportError:
    HAS_TLDEXTRACT = False

try:
    import extruct
    HAS_EXTRUCT = True
except ImportError:
    HAS_EXTRUCT = False

try:
    import aiohttp
    HAS_AIOHTTP = True
except ImportError:
    HAS_AIOHTTP = False

warnings.filterwarnings("ignore")

# ==============================================================================
# 1. CORE REGEX, CONSTANTS & URL HELPERS
# ==============================================================================
RE_SITEMAP_DIRECTIVE = re.compile(r'^\s*Sitemap:\s*(\S+)', re.M | re.I)
RE_CONTENT_TYPE_CHARSET = re.compile(r'charset=([\w-]+)', re.I)
RE_META_DESCRIPTION = re.compile(r'^description$', re.I)
RE_META_ROBOTS = re.compile(r'^(googlebot|bingbot|robots)$', re.I)
RE_LINK_CANONICAL = re.compile(r'<([^>]+)>;\s*rel="?canonical"?', re.I)
RE_SCRIPT_LDJSON = re.compile(r'ld\+json', re.I)
RE_SPA_MOUNT = re.compile(r'^(root|app|__next)$', re.I)

TITLE_GLYPH_WIDTHS = {'default': 7.0, 'narrow': 3.5, 'wide': 10.0}
NARROW_CHARS = set("ijlI|.,;:'!`")
WIDE_CHARS = set("WMmw")
TITLE_PIXEL_MAX, META_PIXEL_MAX = 580, 920

NON_HTML_EXTS = {
    '.xml', '.gz', '.zip', '.rar', '.tar', '.7z', '.pdf', '.doc', '.docx',
    '.xls', '.xlsx', '.ppt', '.pptx', '.jpg', '.jpeg', '.png', '.gif',
    '.webp', '.svg', '.avif', '.ico', '.bmp', '.tiff', '.mp3', '.mp4',
    '.avi', '.mov', '.wmv', '.flv', '.mkv', '.webm', '.css', '.js',
    '.json', '.txt', '.csv', '.woff', '.woff2', '.ttf', '.eot', '.rss',
    '.atom'
}

def extract_registered_domain(netloc):
    if HAS_TLDEXTRACT:
        ext = tldextract.extract(netloc)
        if ext.registered_domain:
            return ext.registered_domain.lower()
    parts = netloc.split('.')
    return ".".join(parts[-2:]).lower() if len(parts) >= 2 else netloc.lower()

def normalize_url(url: str, strip_trailing_slash: bool = False, strip_www: bool = False) -> str:
    try:
        url, _ = urldefrag(url)
        p = urlparse(url)
        hostname = (p.hostname or "").lower()
        if strip_www and hostname.startswith("www."):
            hostname = hostname[4:]
        port = p.port
        if (p.scheme == 'http' and port == 80) or (p.scheme == 'https' and port == 443) or not port:
            netloc = hostname
        else:
            netloc = f"{hostname}:{port}"
        path = p.path or '/'
        path = re.sub(r'/{2,}', '/', path)
        if strip_trailing_slash and len(path) > 1 and path.endswith('/'):
            path = path.rstrip('/')
        
        query = p.query
        if query:
            qsl = parse_qsl(query, keep_blank_values=True)
            qsl.sort()
            query = urlencode(qsl)
            
        return urlunparse((p.scheme.lower(), netloc, path, p.params, query, ''))
    except Exception:
        return url

def is_crawlable_url(url: str) -> bool:
    """Ensure child sitemaps, non-HTML documents, and assets are filtered out."""
    try:
        p = urlparse(url)
        if p.scheme not in ('http', 'https'):
            return False
        path = p.path.lower()
        if any(path.endswith(ext) for ext in NON_HTML_EXTS):
            return False
        if 'sitemap' in path and path.endswith('.xml'):
            return False
        return True
    except Exception:
        return False

def estimate_pixel_width(text, scale=1.0):
    if not text:
        return 0
    total = sum(TITLE_GLYPH_WIDTHS['narrow'] if c in NARROW_CHARS else TITLE_GLYPH_WIDTHS['wide'] if c in WIDE_CHARS else TITLE_GLYPH_WIDTHS['default'] for c in text)
    return round(total * scale, 1)

def recursive_schema_types(obj):
    types = []
    if isinstance(obj, dict):
        if '@type' in obj:
            t = obj['@type']
            types.extend(t if isinstance(t, list) else [t])
        for v in obj.values():
            types.extend(recursive_schema_types(v))
    elif isinstance(obj, list):
        for item in obj:
            types.extend(recursive_schema_types(item))
    return [str(t) for t in types]

def extract_images(soup, base):
    images, seen = [], set()
    for img in soup.find_all('img'):
        src = img.get('src') or img.get('data-src') or img.get('data-original')
        if src:
            url = urldefrag(urljoin(base, src.strip()))[0]
            if url not in seen:
                seen.add(url)
                images.append({
                    "src": url,
                    "alt": (img.get('alt') or '').strip(),
                    "loading": img.get('loading', '')
                })
    return images

def sanitize_excel(val):
    if isinstance(val, str) and val.startswith(('=', '+', '-', '@')):
        return "'" + val
    return val

class ResponseShim:
    def __init__(self, status_code, url, headers, content, history=None):
        self.status_code = status_code
        self.url = url
        self.headers = headers
        self.content = content
        self.history = history or []
        try:
            self.text = content.decode('utf-8', errors='replace')
        except Exception:
            self.text = ""

def content_for_hashing(soup):
    """
    Extract clean body content for duplicate detection hashing.
    Only removes <nav>, <header>, <footer>, <aside>, <script>, <style>, <noscript>, <template>, <iframe>, <svg>.
    Does NOT strip article/product body containers so blog posts and products never produce a null Content Hash.
    """
    try:
        body = soup.find('body') or soup
        c_soup = BeautifulSoup(str(body), 'html.parser')
        for tag in list(c_soup(['nav', 'header', 'footer', 'aside', 'script', 'style', 'noscript', 'template', 'iframe', 'svg'])):
            try:
                if tag.parent:
                    tag.decompose()
            except Exception:
                pass
        
        main = c_soup.find('main') or c_soup.find('article') or c_soup.find(attrs={'role': 'main'})
        target = main if main else c_soup
        text = target.get_text(separator=' ', strip=True)
        return ' '.join(text.lower().split())
    except Exception:
        return ""

# ==============================================================================
# 2. HTML PARSER & DATA ROW BUILDER
# ==============================================================================
def build_row(url, depth, is_in_scope_fn, resp=None, exc=None, in_sitemap=False):
    row = {
        "Address": url, "Status Code": 0, "Final URL": "", "Content Type": "",
        "In Sitemap": "Yes" if in_sitemap else "No", "Crawl Depth": depth,
        "Indexability": "Error", "Indexability Reason": "",
        "URL Underscore": "Yes" if "_" in urlparse(url).path else "No",
        "URL Uppercase": "Yes" if any(c.isupper() for c in urlparse(url).path) else "No",
        "Title 1": "", "Title Status": "Error", "Title Length": 0, "Title Pixel Width (est.)": 0,
        "Meta Description 1": "", "Meta Status": "Error", "Meta Length": 0, "Meta Pixel Width (est.)": 0,
        "Meta Robots": "", "X-Robots-Tag": "", "Schema Types": "None",
        "H1-1": "", "H1 Count": 0, "H2 Count": 0, "H3 Count": 0, "H2-1": "", "H3-1": "",
        "Hreflang Tags": "", "Hreflang Count": 0,
        "Canonical Link": "", "Canonical Count": 0, "Canonical Match": "N/A", "Canonical In Scope": "N/A",
        "Lang Attribute": "", "Viewport Meta": "", "Charset": "",
        "Redirect Chain": "None", "Redirect Hops": 0, "Has Redirect Loop": "No",
        "Word Count": 0, "Text/HTML Ratio (%)": 0, "SPA App Shell": "No",
        "Internal Outlinks": 0, "External Outlinks": 0, "Nofollow Outlinks": 0,
        "Size (KB)": 0, "TTFB (s)": 0, "Content Hash": "", "Last-Modified": "", "ETag": "",
    }
    if exc:
        row["Indexability"] = "Error"
        row["Indexability Reason"] = f"{type(exc).__name__}: {str(exc)[:200]}"
        return row, [], []

    row["Status Code"] = resp.history[0].status_code if resp.history else resp.status_code
    row["Final URL"] = resp.url
    row["Content Type"] = resp.headers.get('content-type', '')
    row["Size (KB)"] = round(len(resp.content) / 1024, 2)
    row["Last-Modified"] = resp.headers.get('last-modified', '')
    row["ETag"] = resp.headers.get('etag', '')
    row["X-Robots-Tag"] = resp.headers.get('x-robots-tag', '')

    if resp.history:
        chain = [f"{h.status_code} {h.url}" for h in resp.history] + [f"{resp.status_code} {resp.url}"]
        row["Redirect Chain"] = " > ".join(chain)
        row["Redirect Hops"] = len(resp.history)
        if len(set([h.url for h in resp.history] + [resp.url])) < len(resp.history) + 1:
            row["Has Redirect Loop"] = "Yes"
        if len(resp.history) > 5:
            row["Has Redirect Loop"] = "Yes (Exceeded 5 hops)"
            row["Indexability"] = "Error"
            row["Indexability Reason"] = "Redirect Loop (>5 hops)"
            return row, [], []

    if row["Status Code"] in (301, 302, 303, 307, 308):
        row["Indexability"] = "Redirected"
        row["Indexability Reason"] = f"Redirected via {row['Status Code']} to {row['Final URL']}"
        return row, [], []
    if row["Status Code"] >= 400:
        row["Indexability"] = "Non-Indexable"
        row["Indexability Reason"] = f"Status {row['Status Code']}"
        return row, [], []

    ct = row["Content Type"].lower()
    if 'text/html' not in ct and 'application/xhtml' not in ct:
        row["Indexability"] = "Non-HTML"
        row["Indexability Reason"] = f"Content-Type: {ct}"
        return row, [], []

    try:
        soup = BeautifulSoup(resp.text, 'lxml')
    except Exception:
        soup = BeautifulSoup(resp.text, 'html.parser')

    html_tag = soup.find('html')
    if html_tag:
        row["Lang Attribute"] = html_tag.get('lang', '')
    vp = soup.find('meta', attrs={'name': 'viewport'})
    row["Viewport Meta"] = vp.get('content', '') if vp else ''
    
    charset = soup.find('meta', charset=True)
    if charset:
        row["Charset"] = charset.get('charset', '')
    else:
        ct_meta = soup.find('meta', attrs={'http-equiv': re.compile(r'^content-type$', re.I)})
        if ct_meta:
            m = RE_CONTENT_TYPE_CHARSET.search(ct_meta.get('content', ''))
            if m: row["Charset"] = m.group(1)

    t = soup.find('title')
    title = t.text.strip() if t and t.text else ""
    row["Title 1"] = title
    row["Title Length"] = len(title)
    pw_title = estimate_pixel_width(title)
    row["Title Pixel Width (est.)"] = pw_title
    row["Title Status"] = "Missing" if not title else "Too Long" if pw_title > TITLE_PIXEL_MAX else "Too Short" if pw_title < 200 else "Good"

    md = soup.find('meta', attrs={'name': RE_META_DESCRIPTION})
    desc = md.get('content', '').strip() if md and md.get('content') else ""
    row["Meta Description 1"] = desc
    row["Meta Length"] = len(desc)
    pw_meta = estimate_pixel_width(desc, 1.0)
    row["Meta Pixel Width (est.)"] = pw_meta
    row["Meta Status"] = "Missing" if not desc else "Too Long" if pw_meta > META_PIXEL_MAX else "Too Short" if pw_meta < 400 else "Good"

    rmeta = soup.find('meta', attrs={'name': RE_META_ROBOTS})
    row["Meta Robots"] = rmeta.get('content', '').strip() if rmeta and rmeta.get('content') else ""

    http_canon = None
    link_header = resp.headers.get('link', '')
    if link_header:
        m = RE_LINK_CANONICAL.search(link_header)
        if m: http_canon = urljoin(resp.url, m.group(1).strip())
    
    canons = soup.find_all('link', rel=lambda x: x and 'canonical' in (x if isinstance(x, str) else ' '.join(x)).lower())
    canon_seen = set()
    if http_canon:
        canon_seen.add(normalize_url(http_canon, strip_trailing_slash=True, strip_www=True))
    for c in canons:
        href = c.get('href', '').strip()
        if href:
            canon_seen.add(normalize_url(urljoin(resp.url, href), strip_trailing_slash=True, strip_www=True))
    row["Canonical Count"] = len(canon_seen)
    canon_link = http_canon or (urljoin(resp.url, canons[0].get('href', '').strip()) if canons and canons[0].get('href', '').strip() else "")
    row["Canonical Link"] = canon_link
    
    # Path & host normalized canonical matching
    if canon_link:
        norm_canon = normalize_url(canon_link, strip_trailing_slash=True, strip_www=True)
        norm_resp = normalize_url(resp.url, strip_trailing_slash=True, strip_www=True)
        row["Canonical Match"] = "Self" if norm_canon == norm_resp else "Different"
        row["Canonical In Scope"] = "Yes" if is_in_scope_fn(canon_link) else "No"

    directives = {d.strip().lower() for d in re.split(r'[,\s]+', row["Meta Robots"] + ',' + row["X-Robots-Tag"]) if d.strip()}
    reasons = []
    if 'noindex' in directives or 'none' in directives:
        reasons.append("noindex directive")
    if row["Canonical Match"] == "Different":
        reasons.append(f"canonicalized to {row['Canonical Link']}")
    row["Indexability"] = "Non-Indexable" if reasons else "Indexable"
    row["Indexability Reason"] = "; ".join(reasons)

    h1s = [h.get_text(strip=True) for h in soup.find_all('h1')]
    h2s = [h.get_text(strip=True) for h in soup.find_all('h2')]
    h3s = [h.get_text(strip=True) for h in soup.find_all('h3')]
    row["H1-1"] = h1s[0] if h1s else ""
    row["H1 Count"] = len(h1s)
    row["H2-1"] = h2s[0] if h2s else ""
    row["H2 Count"] = len(h2s)
    row["H3-1"] = h3s[0] if h3s else ""
    row["H3 Count"] = len(h3s)

    hreflang_pairs = []
    for link in soup.find_all('link', rel=lambda x: x and 'alternate' in (x if isinstance(x, str) else ' '.join(x)).lower()):
        hl = link.get('hreflang')
        href = link.get('href')
        if hl and href:
            hreflang_pairs.append((hl.strip().lower(), urljoin(resp.url, href.strip())))
    row["Hreflang Tags"] = json.dumps(hreflang_pairs) if hreflang_pairs else ""
    row["Hreflang Count"] = len(hreflang_pairs)

    schema_types = []
    for script in soup.find_all('script', type=RE_SCRIPT_LDJSON):
        if not script.string:
            continue
        try:
            schema_types.extend(recursive_schema_types(json.loads(script.string)))
        except Exception:
            pass
    if HAS_EXTRUCT:
        try:
            extracted = extruct.extract(resp.text, base_url=resp.url, syntaxes=['microdata', 'rdfa', 'opengraph'])
            for item in extracted.get('microdata', []):
                if item.get('type'):
                    t = item['type'] if isinstance(item['type'], list) else [item['type']]
                    schema_types.extend(x.rsplit('/', 1)[-1] for x in t)
        except Exception:
            pass
    row["Schema Types"] = ", ".join(sorted(set(schema_types))) if schema_types else "None"

    link_rows = []
    int_out, ext_out, nofollow_out = 0, 0, 0
    for a in soup.find_all('a', href=True):
        raw_href = a['href'].strip()
        if not raw_href or raw_href.startswith(('javascript:', 'mailto:', 'tel:', '#')):
            continue
        target = urldefrag(urljoin(resp.url, raw_href))[0]
        anchor = a.get_text(strip=True) or ("[img alt: " + (a.find('img').get('alt', '').strip()) + "]" if a.find('img') and a.find('img').get('alt') else "[No Text]")
        rel = a.get('rel') or []
        if isinstance(rel, str):
            rel = rel.split()
        is_nofollow = 'nofollow' in [r.lower() for r in rel]
        in_scope = is_in_scope_fn(target)
        link_rows.append({
            "source": resp.url,
            "destination": normalize_url(target),
            "anchor": anchor,
            "nofollow": is_nofollow,
            "in_scope": in_scope
        })
        if in_scope: int_out += 1
        else: ext_out += 1
        if is_nofollow: nofollow_out += 1
    row["Internal Outlinks"], row["External Outlinks"], row["Nofollow Outlinks"] = int_out, ext_out, nofollow_out

    image_rows = [{
        "address": img['src'],
        "alt": img['alt'] or "(Missing)",
        "parent_page": resp.url,
        "loading": img['loading'],
        "size_kb": 0
    } for img in extract_images(soup, resp.url)]

    # Compute visible text and word count
    clean_soup = BeautifulSoup(resp.text, 'html.parser')
    for tag in list(clean_soup(['script', 'style', 'noscript', 'template', 'iframe', 'svg'])):
        try:
            if tag.parent: tag.decompose()
        except Exception: pass
    
    main = clean_soup.find('main') or clean_soup.find('article') or clean_soup.find(attrs={'role': 'main'})
    visible_target = main if main else clean_soup
    body_text = visible_target.get_text(separator=' ', strip=True)
    row["Word Count"] = len(body_text.split())
    
    if row["Word Count"] < 100 and clean_soup.find(id=RE_SPA_MOUNT):
        row["SPA App Shell"] = "Yes"
        
    if len(resp.content) > 100:
        row["Text/HTML Ratio (%)"] = round(len(body_text) / len(resp.content) * 100, 2)

    # Content Deduplication Hash (preserves article and product content containers)
    normalized_content = content_for_hashing(clean_soup)
    row["Content Hash"] = hashlib.md5(normalized_content.encode('utf-8', errors='replace')).hexdigest() if normalized_content else ""

    return row, link_rows, image_rows

# ==============================================================================
# 3. SITEMAP & ROBOTS DISCOVERY ENGINE
# ==============================================================================
def discover_sitemaps(session, target_hostname, root_domain, is_in_scope_fn):
    candidate_hosts = {target_hostname, f"www.{target_hostname.replace('www.', '')}", target_hostname.replace('www.', '')}
    candidates = set()
    for host in candidate_hosts:
        candidates.add(f"https://{host}/sitemap.xml")
        candidates.add(f"https://{host}/sitemap_index.xml")
        candidates.add(f"https://{host}/wp-sitemap.xml")
        try:
            r = session.get(f"https://{host}/robots.txt", timeout=8)
            if r.status_code == 200:
                for sm in RE_SITEMAP_DIRECTIVE.findall(r.text):
                    candidates.add(sm.strip())
        except Exception:
            pass

    seen_sitemaps = set()
    all_urls = set()
    queue = deque(candidates)

    while queue:
        sm_url = queue.popleft()
        if sm_url in seen_sitemaps:
            continue
        seen_sitemaps.add(sm_url)
        try:
            r = session.get(sm_url, timeout=12)
            if r.status_code != 200:
                continue
            text = r.text
            if sm_url.endswith('.gz') or 'gzip' in r.headers.get('Content-Type', '').lower():
                try:
                    text = gzip.decompress(r.content).decode('utf-8', errors='replace')
                except Exception:
                    continue
            
            soup = BeautifulSoup(text, 'lxml-xml' if 'xml' in text[:200] else 'html.parser')
            # Extract child sitemaps strictly into the sitemap parsing queue
            for sm in soup.find_all('sitemap'):
                loc = sm.find('loc')
                if loc and loc.text and loc.text.strip():
                    child_sm = loc.text.strip()
                    if child_sm not in seen_sitemaps:
                        queue.append(child_sm)
            # Extract page URLs strictly from <url><loc> entries
            for u in soup.find_all('url'):
                loc = u.find('loc')
                if loc and loc.text and loc.text.strip().startswith('http'):
                    all_urls.add(loc.text.strip())
        except Exception:
            continue

    sitemap_pages = set()
    for u in all_urls:
        norm = normalize_url(u)
        if is_in_scope_fn(norm) and is_crawlable_url(norm):
            sitemap_pages.add(norm)
    return sitemap_pages

# ==============================================================================
# 4. ASYNC CRAWLER ENGINE (STREAMLIT DIRECT RUNNER)
# ==============================================================================
RETRY_STATUSES = {429, 503, 520, 522, 524}
MAX_RETRIES = 3

async def execute_crawl(config, progress_callback, status_callback):
    base_url = config['base_url']
    target_hostname = config['target_hostname']
    root_domain = config['root_domain']
    base_path = config['base_path']
    scope_mode = config['scope_mode']
    crawl_limit = config['crawl_limit']
    concurrency = config['concurrency']
    stealth_jitter = config['stealth_jitter']
    respect_robots = config['respect_robots']
    headers = config['headers']
    db_path = config['db_path']

    # Pre-flight probe to discover preferred canonical host
    with requests.Session() as s:
        s.headers.update(headers)
        try:
            r_init = s.get(base_url, timeout=10, allow_redirects=True)
            soup_init = BeautifulSoup(r_init.text, 'html.parser')
            canon_init = soup_init.find('link', rel=lambda x: x and 'canonical' in (x if isinstance(x, str) else ' '.join(x)).lower())
            if canon_init and canon_init.get('href'):
                p_can = urlparse(urljoin(r_init.url, canon_init['href']))
                if p_can.hostname and extract_registered_domain(p_can.hostname) == root_domain:
                    target_hostname = p_can.hostname.lower()
            elif r_init.url:
                p_fin = urlparse(r_init.url)
                if p_fin.hostname and extract_registered_domain(p_fin.hostname) == root_domain:
                    target_hostname = p_fin.hostname.lower()
        except Exception:
            pass

    target_apex = target_hostname.replace("www.", "")

    def is_in_scope(url: str) -> bool:
        try:
            p = urlparse(url)
        except Exception:
            return False
        hostname = (p.hostname or "").lower()
        if not hostname:
            return False
        if scope_mode == "Root Domain & All Subdomains":
            return extract_registered_domain(hostname) == root_domain
        if scope_mode == "This Subdomain Only (Apex + WWW)":
            return hostname.replace("www.", "") == target_apex
        if scope_mode == "This Subfolder Only":
            matches_host = (hostname.replace("www.", "") == target_apex)
            return matches_host and p.path.startswith(base_path)
        return False

    conn = sqlite3.connect(db_path, isolation_level=None)
    conn.execute("PRAGMA journal_mode=WAL;")
    conn.execute("PRAGMA synchronous=NORMAL;")
    conn.execute("PRAGMA busy_timeout=10000;")
    cur = conn.cursor()
    cur.execute("CREATE TABLE IF NOT EXISTS pages (address TEXT PRIMARY KEY, data TEXT)")
    cur.execute("CREATE TABLE IF NOT EXISTS links (source TEXT, destination TEXT, anchor TEXT, nofollow INTEGER, in_scope INTEGER)")
    cur.execute("CREATE TABLE IF NOT EXISTS images (address TEXT, alt TEXT, parent_page TEXT, loading TEXT, size_kb REAL)")
    cur.execute("CREATE TABLE IF NOT EXISTS errors (url TEXT, error_type TEXT, message TEXT, ts TEXT)")
    cur.execute("CREATE TABLE IF NOT EXISTS sitemaps (url TEXT PRIMARY KEY)")

    status_callback("🔍 Discovering XML sitemaps and parsing robots.txt...")
    with requests.Session() as s:
        s.headers.update(headers)
        sitemap_pages = discover_sitemaps(s, target_hostname, root_domain, is_in_scope)

    cur.execute("BEGIN TRANSACTION")
    cur.executemany("INSERT OR IGNORE INTO sitemaps VALUES (?)", [(u,) for u in sitemap_pages])
    cur.execute("COMMIT")

    robots_parser = RobotFileParser()
    if respect_robots:
        try:
            r = requests.get(f"https://{target_hostname}/robots.txt", headers=headers, timeout=8)
            if r.status_code == 200:
                robots_parser.parse(r.text.splitlines())
        except Exception:
            pass

    # Architectural Fix 1 & 2: Seed queue with ONLY the Start URL at Depth 0
    visited, queued, queue = set(), set(), deque()
    seed = normalize_url(base_url)
    if is_crawlable_url(seed):
        queue.append((seed, 0))
        queued.add(seed)

    host_locks = defaultdict(asyncio.Lock)
    host_last_req = defaultdict(lambda: 0.0)

    async def polite_delay(host):
        delay = 0.4 + (random.uniform(0.1, 0.4) if stealth_jitter else 0.0)
        async with host_locks[host]:
            elapsed = time.time() - host_last_req[host]
            if elapsed < delay:
                await asyncio.sleep(delay - elapsed)
            host_last_req[host] = time.time()

    ssl_ctx = ssl.create_default_context()
    ssl_ctx.check_hostname = False
    ssl_ctx.verify_mode = ssl.CERT_NONE

    async def fetch_async(session_aio, url, depth):
        host = urlparse(url).hostname or target_hostname
        last_status = None
        for attempt in range(MAX_RETRIES + 1):
            await polite_delay(host)
            start = time.time()
            try:
                async with session_aio.get(url, timeout=aiohttp.ClientTimeout(total=25), allow_redirects=True, ssl=ssl_ctx) as resp:
                    if resp.status in RETRY_STATUSES and attempt < MAX_RETRIES:
                        last_status = resp.status
                        await asyncio.sleep(1.5 * (attempt + 1))
                        continue
                    content = await resp.read()
                    hist = [ResponseShim(h.status, str(h.url), {}, b'') for h in resp.history]
                    shim = ResponseShim(resp.status, str(resp.url), {k.lower(): v for k, v in resp.headers.items()}, content, hist)
                    row, links, images = build_row(url, depth, is_in_scope, resp=shim, in_sitemap=(url in sitemap_pages))
                    row["TTFB (s)"] = round(time.time() - start, 3)
                    del shim
                    del content
                    return row, links, images, None
            except Exception as e:
                if attempt < MAX_RETRIES:
                    await asyncio.sleep(1.0 * (attempt + 1))
                    continue
                row, links, images = build_row(url, depth, is_in_scope, exc=e, in_sitemap=(url in sitemap_pages))
                return row, links, images, e

        shim = ResponseShim(last_status or 0, url, {}, b'')
        row, links, images = build_row(url, depth, is_in_scope, resp=shim, in_sitemap=(url in sitemap_pages))
        return row, links, images, None

    connector = aiohttp.TCPConnector(limit=concurrency * 2, force_close=True, ssl=ssl_ctx)
    pages_counted, processed, error_count = 0, 0, 0
    fetch_ceiling = crawl_limit * 3
    start_time_crawl = time.time()

    async with aiohttp.ClientSession(connector=connector, headers=headers) as aio_session:
        while (queue or (pages_counted < crawl_limit and any(u not in visited and u not in queued for u in sitemap_pages))) and pages_counted < crawl_limit and processed < fetch_ceiling:
            # Low-priority queue padding from sitemap discovery only after primary site graph is explored
            if not queue and pages_counted < crawl_limit:
                unvisited_sitemap = [u for u in sitemap_pages if u not in visited and u not in queued]
                if unvisited_sitemap:
                    for u in unvisited_sitemap[:(crawl_limit - pages_counted)]:
                        queue.append((u, 1))
                        queued.add(u)

            if not queue:
                break

            batch = []
            while queue and len(batch) < concurrency and pages_counted < crawl_limit:
                url, depth = queue.popleft()
                if url in visited:
                    continue
                if respect_robots and not robots_parser.can_fetch(headers.get("User-Agent", "*"), url):
                    cur.execute("INSERT INTO errors VALUES (?,?,?,?)", (url, "RobotsBlocked", "Disallowed by robots.txt", datetime.now().isoformat()))
                    visited.add(url)
                    continue
                visited.add(url)
                batch.append((url, depth))

            if not batch:
                break

            tasks = [fetch_async(aio_session, u, d) for u, d in batch]
            results = await asyncio.gather(*tasks)

            cur.execute("BEGIN TRANSACTION")
            for (url, depth), res_tuple in zip(batch, results):
                row, links, images, exc = res_tuple
                cur.execute("INSERT OR REPLACE INTO pages VALUES (?, ?)", (row['Address'], json.dumps(row, default=str)))
                if links:
                    cur.executemany("INSERT INTO links VALUES (?,?,?,?,?)", [(r['source'], r['destination'], r['anchor'], int(r['nofollow']), int(r['in_scope'])) for r in links])
                if images:
                    cur.executemany("INSERT INTO images VALUES (?,?,?,?,?)", [(r['address'], r['alt'], r['parent_page'], r['loading'], r['size_kb']) for r in images])
                if exc:
                    cur.execute("INSERT INTO errors VALUES (?,?,?,?)", (url, type(exc).__name__, str(exc)[:500], datetime.now().isoformat()))
                    error_count += 1

                final_norm = normalize_url(row['Final URL']) if row.get('Final URL') else ""
                if final_norm and final_norm != normalize_url(url) and is_in_scope(final_norm) and final_norm not in visited and final_norm not in queued:
                    if is_crawlable_url(final_norm):
                        queue.appendleft((final_norm, depth))
                        queued.add(final_norm)

                for ln in links:
                    dest = ln['destination']
                    if ln['in_scope'] and not ln['nofollow'] and dest not in visited and dest not in queued:
                        if is_crawlable_url(dest):
                            queue.append((dest, depth + 1))
                            queued.add(dest)

                processed += 1
                if row.get('Indexability') != 'Redirected':
                    pages_counted += 1
                
                elapsed = max(0.1, time.time() - start_time_crawl)
                speed = round(processed / elapsed, 1)
                mem = round(psutil.Process(os.getpid()).memory_info().rss / 1024 / 1024, 1) if HAS_PSUTIL else 0.0
                progress_callback(min(pages_counted / crawl_limit, 1.0), pages_counted, processed, len(queue), speed, mem, row.get("TTFB (s)", 0.0))
            cur.execute("COMMIT")

        status_callback("📏 Measuring image payload sizes...")
        cur.execute("SELECT DISTINCT address FROM images")
        img_urls = [r[0] for r in cur.fetchall()]
        if img_urls:
            sem = asyncio.Semaphore(15)
            async def get_img_size(u):
                async with sem:
                    try:
                        async with aio_session.head(u, timeout=aiohttp.ClientTimeout(total=6), ssl=ssl_ctx) as r_img:
                            cl = r_img.headers.get('Content-Length')
                            if cl and cl.isdigit():
                                return u, round(int(cl) / 1024, 2)
                    except Exception:
                        pass
                    return u, 0.0

            img_sizes = await asyncio.gather(*[get_img_size(u) for u in img_urls])
            cur.execute("BEGIN TRANSACTION")
            cur.executemany("UPDATE images SET size_kb = ? WHERE address = ?", [(sz, u) for u, sz in img_sizes])
            cur.execute("COMMIT")

    conn.close()
    return target_hostname

# ==============================================================================
# 5. POST-CRAWL DATA ANALYSIS & REPORT GENERATOR
# ==============================================================================
def run_full_analysis(db_path):
    conn = sqlite3.connect(db_path)
    sitemap_pages_set = set([r[0] for r in conn.execute("SELECT url FROM sitemaps")])
    
    rows = [json.loads(r[0]) for r in conn.execute("SELECT data FROM pages")]
    df_internal = pd.DataFrame(rows) if rows else pd.DataFrame()
    df_links = pd.read_sql_query("SELECT source, destination, anchor, nofollow, in_scope as [In Scope] FROM links", conn)
    df_images = pd.read_sql_query("SELECT address, alt as [Alt Text], size_kb as [Size (KB)], parent_page as [Parent Page], loading FROM images", conn)
    df_errors = pd.read_sql_query("SELECT url as [Address], error_type as [Error Type], message as Message, ts as Timestamp FROM errors", conn)
    
    df_links_internal = df_links[df_links['In Scope'] == 1].drop(columns=['In Scope']).copy() if not df_links.empty else pd.DataFrame(columns=['source', 'destination', 'anchor', 'nofollow'])
    df_links_external = df_links[df_links['In Scope'] == 0].drop(columns=['In Scope']).copy() if not df_links.empty else pd.DataFrame(columns=['source', 'destination', 'anchor', 'nofollow'])

    if not df_internal.empty and not df_links_internal.empty:
        df_internal['__norm'] = df_internal['Address'].apply(normalize_url)
        unique_inlinks = df_links_internal.groupby('destination')['source'].nunique()
        total_inlinks = df_links_internal['destination'].value_counts()
        df_internal['Unique Inlinks'] = df_internal['__norm'].map(unique_inlinks).fillna(0).astype(int)
        df_internal['Total Inlinks'] = df_internal['__norm'].map(total_inlinks).fillna(0).astype(int)
        df_internal.drop(columns=['__norm'], inplace=True)
    elif not df_internal.empty:
        df_internal['Unique Inlinks'] = 0
        df_internal['Total Inlinks'] = 0

    hreflang_issues = 0
    if not df_internal.empty and 'Hreflang Tags' in df_internal.columns:
        crawled_urls = set(df_internal['Address'].apply(normalize_url))
        def count_missing_hreflang(tags_json):
            if not tags_json: return 0
            try:
                pairs = json.loads(tags_json)
                return sum(1 for _, href in pairs if normalize_url(href) not in crawled_urls)
            except:
                return 0
        df_internal['Missing Return Hreflang'] = df_internal['Hreflang Tags'].apply(count_missing_hreflang)
        hreflang_issues = df_internal['Missing Return Hreflang'].sum()

    df_duplicates = pd.DataFrame()
    spa_shell_count = 0
    if not df_internal.empty:
        df_200 = df_internal[df_internal['Status Code'] == 200]
        dup_titles = df_200[df_200['Title 1'].astype(bool)]['Title 1'].value_counts()
        dup_h1s = df_200[df_200['H1-1'].astype(bool)]['H1-1'].value_counts()
        dup_hashes = df_200[df_200['Content Hash'].astype(bool)]['Content Hash'].value_counts()

        df_internal['Duplicate Title'] = df_internal['Title 1'].map(lambda t: dup_titles.get(t, 0) > 1 if t else False)
        df_internal['Duplicate H1'] = df_internal['H1-1'].map(lambda h: dup_h1s.get(h, 0) > 1 if h else False)
        df_internal['Duplicate Content'] = df_internal['Content Hash'].map(lambda h: dup_hashes.get(h, 0) > 1 if h else False)

        dup_rows = []
        for title, cnt in dup_titles[dup_titles > 1].items():
            dup_rows.append({"Duplicate Type": "Title", "Value": str(title)[:120], "Count": int(cnt)})
        for h1, cnt in dup_h1s[dup_h1s > 1].items():
            dup_rows.append({"Duplicate Type": "H1", "Value": str(h1)[:120], "Count": int(cnt)})
        for h, cnt in dup_hashes[dup_hashes > 1].items():
            sample = df_200[df_200['Content Hash'] == h]['Title 1'].iloc[0] if not df_200[df_200['Content Hash'] == h].empty else ''
            dup_rows.append({"Duplicate Type": "Body Content", "Value": f"[{h[:8]}] {sample}"[:120], "Count": int(cnt)})
        df_duplicates = pd.DataFrame(dup_rows)
        
        if not dup_hashes.empty and dup_hashes.iloc[0] > (len(df_200) * 0.75) and len(df_200) >= 5:
            spa_shell_count = int(dup_hashes.iloc[0])

    crawled_urls = set(df_internal['Address'].apply(normalize_url)) if not df_internal.empty else set()
    orphan_pages = sitemap_pages_set - crawled_urls
    df_orphans = pd.DataFrame([{"Address": u, "Type": "In sitemap, not reached by crawl"} for u in sorted(orphan_pages)]) if orphan_pages else pd.DataFrame(columns=['Address', 'Type'])

    # Architectural Fix 3: Complete Issues Summary Aggregation
    issues = []
    def add_issue(cat, sev, count, desc):
        if count > 0:
            issues.append({"Category": cat, "Severity": sev, "Count": int(count), "Description": desc})

    if not df_internal.empty:
        parsed = df_internal[(df_internal['Status Code'] == 200) & (df_internal['Word Count'] > 0)]
        
        # Architecture & Status Issues
        if spa_shell_count > 0:
            add_issue("Architecture", "Critical", spa_shell_count, "Client-Side Rendered (SPA) Shell Detected — Routes return identical raw HTML shell")
        add_issue("Status", "Critical", (df_internal['Status Code'] >= 500).sum(), "5xx Server Errors")
        add_issue("Status", "Critical", (df_internal['Status Code'] == 404).sum(), "404 Not Found Pages")
        add_issue("Status", "High", (df_internal['Status Code'].isin([301, 308])).sum(), "Permanent Redirects (301/308)")
        
        # Broken Internal Links (4xx/5xx)
        if not df_links_internal.empty:
            status_map = dict(zip(df_internal['Address'].apply(normalize_url), df_internal['Status Code']))
            dest_statuses = df_links_internal['destination'].map(status_map).fillna(0)
            broken_int_links_count = int((dest_statuses >= 400).sum())
            add_issue("Links", "High", broken_int_links_count, "Broken Internal Links (4xx/5xx Destination)")

        # Title Tag Issues
        add_issue("Titles", "High", (parsed['Title Status'] == 'Missing').sum(), "Missing Title Tags")
        add_issue("Titles", "Medium", (parsed['Title Status'] == 'Too Short').sum(), "Short Title Tags (<200px)")
        add_issue("Titles", "Medium", (parsed['Title Status'] == 'Too Long').sum(), "Titles Exceeding 580px")
        add_issue("Titles", "High", parsed.get('Duplicate Title', pd.Series()).sum(), "Duplicate Titles")
        
        # Meta Description Issues
        add_issue("Meta Description", "High", (parsed['Meta Status'] == 'Missing').sum(), "Missing Meta Descriptions")
        add_issue("Meta Description", "Medium", (parsed['Meta Status'] == 'Too Long').sum(), "Oversized Meta Descriptions (>920px)")
        add_issue("Meta Description", "Low", (parsed['Meta Status'] == 'Too Short').sum(), "Short Meta Descriptions (<400px)")

        # Heading Tag Issues (H1)
        add_issue("Headings", "High", (parsed['H1 Count'] == 0).sum(), "Missing H1 Tags")
        add_issue("Headings", "Medium", (parsed['H1 Count'] > 1).sum(), "Multiple H1 Tags")
        add_issue("Headings", "High", parsed.get('Duplicate H1', pd.Series()).sum(), "Duplicate H1 Tags")

        # Content Issues
        add_issue("Content", "High", parsed.get('Duplicate Content', pd.Series()).sum(), "Identical Body Content (Hash Match)")
        add_issue("Content", "Medium", (parsed['Word Count'] < 200).sum(), "Thin Content (<200 words)")
        
        # Canonical Issues
        add_issue("Canonical", "High", (parsed['Canonical Count'] > 1).sum(), "Multiple Canonical Tags")
        add_issue("Canonical", "Medium", (parsed['Canonical Match'] == 'Different').sum(), "Canonicalized to a Different URL")
        
        # Hreflang Issues
        add_issue("Hreflang", "High", hreflang_issues, "Missing Return Hreflang Link")

    # Image Issues (Missing Alt & Payload Size > 100 KB)
    if not df_images.empty:
        missing_alt_count = int((df_images['Alt Text'].isin(['(Missing)', '', None]) | df_images['Alt Text'].isna()).sum())
        oversized_images_count = int((df_images['Size (KB)'] > 100).sum())
        add_issue("Images", "Medium", missing_alt_count, "Images Missing Alt Text")
        add_issue("Images", "Medium", oversized_images_count, "Images Over 100 KB (Unoptimized)")

    df_issues = pd.DataFrame(issues) if issues else pd.DataFrame(columns=['Category', 'Severity', 'Count', 'Description'])
    if not df_issues.empty:
        severity_order = {"Critical": 0, "High": 1, "Medium": 2, "Low": 3}
        df_issues['__sort'] = df_issues['Severity'].map(severity_order)
        df_issues = df_issues.sort_values(['__sort', 'Count'], ascending=[True, False]).drop(columns=['__sort'])

    conn.close()
    return {
        "Issues Summary": df_issues,
        "Internal Pages": df_internal,
        "Duplicates": df_duplicates if not df_duplicates.empty else pd.DataFrame(columns=['Duplicate Type', 'Value', 'Count']),
        "Internal Links": df_links_internal,
        "External Links": df_links_external,
        "Images": df_images if not df_images.empty else pd.DataFrame(columns=['address', 'Alt Text', 'Size (KB)', 'Parent Page', 'loading']),
        "Orphan Pages": df_orphans,
        "Crawl Errors": df_errors if not df_errors.empty else pd.DataFrame(columns=['Address', 'Error Type', 'Message', 'Timestamp'])
    }

# ==============================================================================
# 6. IN-MEMORY EXCEL EXPORTER
# ==============================================================================
def create_excel_report(data_dict):
    output = BytesIO()
    wb = Workbook(write_only=True)
    for sheet_name, df in data_dict.items():
        ws = wb.create_sheet(title=sheet_name[:31])
        if isinstance(df, pd.DataFrame):
            ws.append(list(df.columns) if not df.empty else ["No data recorded"])
            for row in df.itertuples(index=False):
                sanitized_row = [sanitize_excel(val) for val in row]
                sanitized_row = [v[:32700] if isinstance(v, str) else v for v in sanitized_row]
                ws.append(sanitized_row)
    wb.save(output)
    output.seek(0)
    return output

# ==============================================================================
# 7. STREAMLIT APPLICATION INTERFACE
# ==============================================================================
st.set_page_config(page_title="SEO-Diver Auditor", page_icon="🕷️", layout="wide")

st.title("🕷️ SEO-Diver Technical Auditor")
st.caption("Automated technical SEO crawler, duplicate content analyzer, and indexability engine.")

st.sidebar.header("Crawl Parameters")
start_url = st.sidebar.text_input("Start URL", "https://www.example.com/").strip().rstrip('/')
if not start_url.startswith(('http://', 'https://')):
    start_url = 'https://' + start_url

scope_mode = st.sidebar.selectbox(
    "Crawl Scope",
    ["This Subdomain Only (Apex + WWW)", "Root Domain & All Subdomains", "This Subfolder Only"],
    index=0
)

col_a, col_b = st.sidebar.columns(2)
with col_a:
    crawl_limit = st.number_input("Crawl Limit", min_value=10, max_value=20000, value=250, step=50)
with col_b:
    concurrency = st.slider("Concurrency", min_value=1, max_value=16, value=6)

ua_choice = st.sidebar.selectbox(
    "User-Agent Identity",
    ["Chrome (Default - Anti-WAF)", "DeepseekDiver (Bot)", "Googlebot"]
)
ua_map = {
    "Chrome (Default - Anti-WAF)": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "DeepseekDiver (Bot)": "DeepseekDiver/3.6 (+SEO audit)",
    "Googlebot": "Mozilla/5.0 (compatible; Googlebot/2.1; +http://www.google.com/bot.html)"
}
chosen_ua = ua_map[ua_choice]

stealth_jitter = st.sidebar.toggle("Enable Stealth Jitter (Anti-WAF)", value=True)
respect_robots = st.sidebar.toggle("Respect robots.txt", value=False)

start_crawl_button = st.sidebar.button("🚀 Start SEO Audit", type="primary", use_container_width=True)

if start_crawl_button:
    parsed_base = urlparse(start_url)
    target_hostname = parsed_base.hostname.lower() if parsed_base.hostname else parsed_base.netloc.lower()
    root_domain = extract_registered_domain(target_hostname)
    base_path = parsed_base.path.rstrip('/') or '/'

    temp_db = tempfile.NamedTemporaryFile(delete=False, suffix=".db").name

    headers = {
        "User-Agent": chosen_ua,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
        "Accept-Encoding": "gzip, deflate, br",
    }

    config = {
        "base_url": start_url,
        "target_hostname": target_hostname,
        "root_domain": root_domain,
        "base_path": base_path,
        "scope_mode": scope_mode,
        "crawl_limit": crawl_limit,
        "concurrency": concurrency,
        "stealth_jitter": stealth_jitter,
        "respect_robots": respect_robots,
        "headers": headers,
        "db_path": temp_db
    }

    status_box = st.status("Initializing SEO Crawler...", expanded=True)
    prog_bar = status_box.progress(0.0)
    metrics_placeholder = status_box.empty()
    stats_placeholder = status_box.empty()

    def update_progress(ratio, pages, total_fetches, queue_len, speed, mem, ttfb):
        prog_bar.progress(ratio)
        metrics_placeholder.markdown(f"**Pages Parsed:** `{pages}/{crawl_limit}` | **Total Fetches:** `{total_fetches}` | **Queue Remaining:** `{queue_len}`")
        stats_placeholder.markdown(f"⏱ **Speed:** `{speed} req/s` | 🧠 **RAM:** `{mem} MB` | ⚡ **Active TTFB:** `{ttfb}s`")

    def update_status(text):
        status_box.write(text)

    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    try:
        final_target_host = loop.run_until_complete(execute_crawl(config, update_progress, update_status))
    finally:
        loop.close()

    status_box.update(label="Crawling Complete! Analyzing data...", state="running")
    results = run_full_analysis(temp_db)
    status_box.update(label="✅ Audit Complete!", state="complete", expanded=False)

    st.session_state['audit_results'] = results
    st.session_state['audit_url'] = final_target_host

if 'audit_results' in st.session_state:
    res = st.session_state['audit_results']
    host = st.session_state['audit_url']

    st.subheader(f"Audit Dashboard: {host}")

    df_int = res['Internal Pages']
    kpi1, kpi2, kpi3, kpi4 = st.columns(4)
    with kpi1:
        st.metric("Total Crawled Pages", len(df_int))
    with kpi2:
        indexable_count = (df_int['Indexability'] == 'Indexable').sum() if not df_int.empty else 0
        st.metric("Indexable Pages", int(indexable_count))
    with kpi3:
        broken_count = (df_int['Status Code'] >= 400).sum() if not df_int.empty else 0
        st.metric("4xx/5xx Errors", int(broken_count))
    with kpi4:
        dup_count = df_int['Duplicate Title'].sum() if ('Duplicate Title' in df_int.columns) else 0
        st.metric("Duplicate Titles", int(dup_count))

    excel_file = create_excel_report(res)
    st.download_button(
        label="📥 Download Full Excel Workbook (.xlsx)",
        data=excel_file,
        file_name=f"technical_seo_audit_{host}_{datetime.now().strftime('%Y%m%d_%H%M')}.xlsx",
        mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
        type="primary"
    )

    tab_issues, tab_internal, tab_duplicates, tab_links, tab_images, tab_orphans, tab_errors = st.tabs([
        "⚠️ Issues Summary",
        "📄 Internal Pages",
        "👥 Duplicates",
        "🔗 Internal Links",
        "🖼️ Images",
        "👤 Orphan Pages",
        "🚨 Crawl Errors"
    ])

    with tab_issues:
        if not res['Issues Summary'].empty:
            st.dataframe(res['Issues Summary'], use_container_width=True, hide_index=True)
        else:
            st.success("No technical issues flagged!")

    with tab_internal:
        if not df_int.empty:
            cols_to_show = ['Address', 'Status Code', 'Indexability', 'Indexability Reason', 'Title 1', 'Word Count', 'SPA App Shell', 'Canonical Match', 'TTFB (s)']
            st.dataframe(df_int[[c for c in cols_to_show if c in df_int.columns]], use_container_width=True)

    with tab_duplicates:
        if not res['Duplicates'].empty:
            st.dataframe(res['Duplicates'], use_container_width=True, hide_index=True)
        else:
            st.info("No duplicate content or titles identified.")

    with tab_links:
        if not res['Internal Links'].empty:
            st.dataframe(res['Internal Links'].head(1000), use_container_width=True)

    with tab_images:
        if not res['Images'].empty:
            st.dataframe(res['Images'].head(1000), use_container_width=True)

    with tab_orphans:
        if not res['Orphan Pages'].empty:
            st.dataframe(res['Orphan Pages'], use_container_width=True, hide_index=True)
        else:
            st.success("Zero orphan URLs detected.")

    with tab_errors:
        if not res['Crawl Errors'].empty:
            st.dataframe(res['Crawl Errors'], use_container_width=True, hide_index=True)
        else:
            st.success("Zero crawl-time network/bot errors.")
