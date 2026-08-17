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
import gc
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
# 1. CORE REGEX, CONSTANTS & STANDARDS
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
MAX_HTML_BODY_BYTES = 4 * 1024 * 1024  # 4MB cap to prevent OOM on giant files

NON_HTML_EXTS = {
    '.xml', '.gz', '.zip', '.rar', '.tar', '.7z', '.pdf', '.doc', '.docx',
    '.xls', '.xlsx', '.ppt', '.pptx', '.jpg', '.jpeg', '.png', '.gif',
    '.webp', '.svg', '.avif', '.ico', '.bmp', '.tiff', '.mp3', '.mp4',
    '.avi', '.mov', '.wmv', '.flv', '.mkv', '.webm', '.css', '.js',
    '.json', '.txt', '.csv', '.woff', '.woff2', '.ttf', '.eot', '.rss',
    '.atom'
}

ISO_639_1_LANGS = {
    'aa', 'ab', 'ae', 'af', 'ak', 'am', 'an', 'ar', 'as', 'av', 'ay', 'az',
    'ba', 'be', 'bg', 'bh', 'bi', 'bm', 'bn', 'bo', 'br', 'bs', 'ca', 'ce',
    'ch', 'co', 'cr', 'cs', 'cu', 'cv', 'cy', 'da', 'de', 'dv', 'dz', 'ee',
    'el', 'en', 'eo', 'es', 'et', 'eu', 'fa', 'ff', 'fi', 'fj', 'fo', 'fr',
    'fy', 'ga', 'gd', 'gl', 'gn', 'gu', 'gv', 'ha', 'he', 'hi', 'ho', 'hr',
    'ht', 'hu', 'hy', 'hz', 'ia', 'id', 'ie', 'ig', 'ii', 'ik', 'io', 'is',
    'it', 'iu', 'ja', 'jv', 'ka', 'kg', 'ki', 'kj', 'kk', 'kl', 'km', 'kn',
    'ko', 'kr', 'ks', 'ku', 'kv', 'kw', 'ky', 'la', 'lb', 'lg', 'li', 'ln',
    'lo', 'lt', 'lu', 'lv', 'mg', 'mh', 'mi', 'mk', 'ml', 'mn', 'mr', 'ms',
    'mt', 'my', 'na', 'nb', 'nd', 'ne', 'ng', 'nl', 'nn', 'no', 'nr', 'nv',
    'ny', 'oc', 'oj', 'om', 'or', 'os', 'pa', 'pi', 'pl', 'ps', 'pt', 'qu',
    'rm', 'rn', 'ro', 'ru', 'rw', 'sa', 'sc', 'sd', 'se', 'sg', 'si', 'sk',
    'sl', 'sm', 'sn', 'so', 'sq', 'sr', 'ss', 'st', 'su', 'sv', 'sw', 'ta',
    'te', 'tg', 'th', 'ti', 'tk', 'tl', 'tn', 'to', 'tr', 'ts', 'tt', 'tw',
    'ty', 'ug', 'uk', 'ur', 'uz', 've', 'vi', 'vo', 'wa', 'wo', 'xh', 'yi',
    'yo', 'za', 'zh', 'zu'
}

ISO_3166_1_COUNTRIES = {
    'ad', 'ae', 'af', 'ag', 'ai', 'al', 'am', 'ao', 'aq', 'ar', 'as', 'at',
    'au', 'aw', 'ax', 'az', 'ba', 'bb', 'bd', 'be', 'bf', 'bg', 'bh', 'bi',
    'bj', 'bl', 'bm', 'bn', 'bo', 'bq', 'br', 'bs', 'bt', 'bv', 'bw', 'by',
    'bz', 'ca', 'cc', 'cd', 'cf', 'cg', 'ch', 'ci', 'ck', 'cl', 'cm', 'cn',
    'co', 'cr', 'cu', 'cv', 'cw', 'cx', 'cy', 'cz', 'de', 'dj', 'dk', 'dm',
    'do', 'dz', 'ec', 'ee', 'eg', 'eh', 'er', 'es', 'et', 'fi', 'fj', 'fk',
    'fm', 'fo', 'fr', 'ga', 'gb', 'gd', 'ge', 'gf', 'gg', 'gh', 'gi', 'gl',
    'gm', 'gn', 'gp', 'gq', 'gr', 'gs', 'gt', 'gu', 'gw', 'gy', 'hk', 'hm',
    'hn', 'hr', 'ht', 'hu', 'id', 'ie', 'il', 'im', 'in', 'io', 'iq', 'ir',
    'is', 'it', 'je', 'jm', 'jo', 'jp', 'ke', 'kg', 'kh', 'ki', 'km', 'kn',
    'kp', 'kr', 'kw', 'ky', 'kz', 'la', 'lb', 'lc', 'li', 'lk', 'lr', 'ls',
    'lt', 'lu', 'lv', 'ly', 'ma', 'mc', 'md', 'me', 'mf', 'mg', 'mh', 'mk',
    'ml', 'mm', 'mn', 'mo', 'mp', 'mq', 'mr', 'ms', 'mt', 'mu', 'mv', 'mw',
    'mx', 'my', 'mz', 'na', 'nc', 'ne', 'nf', 'ng', 'ni', 'nl', 'no', 'np',
    'nr', 'nu', 'nz', 'om', 'pa', 'pe', 'pf', 'pg', 'ph', 'pk', 'pl', 'pm',
    'pn', 'pr', 'ps', 'pt', 'pw', 'py', 'qa', 're', 'ro', 'rs', 'ru', 'rw',
    'sa', 'sb', 'sc', 'sd', 'se', 'sg', 'sh', 'si', 'sj', 'sk', 'sl', 'sm',
    'sn', 'so', 'sr', 'ss', 'st', 'sv', 'sx', 'sy', 'sz', 'tc', 'td', 'tf',
    'tg', 'th', 'tj', 'tk', 'tl', 'tm', 'tn', 'to', 'tr', 'tt', 'tv', 'tw',
    'tz', 'ua', 'ug', 'um', 'us', 'uy', 'uz', 'va', 'vc', 've', 'vg', 'vi',
    'vn', 'vu', 'wf', 'ws', 'ye', 'yt', 'za', 'zm', 'zw'
}

# ==============================================================================
# 2. ADVANCED MATHEMATICAL & INTELLIGENCE ENGINES
# ==============================================================================
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

def compute_simhash_64(text: str) -> int:
    if not text or len(text.strip()) < 10:
        return 0
    words = re.findall(r'\w+', text.lower())
    if not words:
        return 0
    
    features = []
    for i in range(len(words) - 2):
        features.append(f"{words[i]}_{words[i+1]}_{words[i+2]}")
    features.extend(words[:150])  # Cap tokens to maintain fast hashing
    
    feature_counts = Counter(features)
    v = [0] * 64
    for feat, count in feature_counts.items():
        h = int(hashlib.md5(feat.encode('utf-8')).hexdigest()[:16], 16)
        for i in range(64):
            bit = (h >> i) & 1
            if bit == 1:
                v[i] += count
            else:
                v[i] -= count
                
    fingerprint = 0
    for i in range(64):
        if v[i] > 0:
            fingerprint |= (1 << i)
    return fingerprint

def simhash_similarity(h1: int, h2: int) -> float:
    if h1 == 0 or h2 == 0:
        return 0.0
    x = h1 ^ h2
    hamming_dist = bin(x).count('1')
    return round((1.0 - (hamming_dist / 64.0)) * 100, 1)

def calculate_internal_pagerank(df_pages, df_links_internal, damping=0.85, max_iter=100, tol=1e-6):
    if df_pages.empty:
        return {}, {}, {}
    
    nodes = list(df_pages['Address'].apply(normalize_url).unique())
    N = len(nodes)
    if N == 0:
        return {}, {}, {}
    
    node_set = set(nodes)
    outlinks = defaultdict(set)
    inlinks = defaultdict(set)
    
    if not df_links_internal.empty:
        for _, row in df_links_internal.iterrows():
            s = normalize_url(row['source'])
            d = normalize_url(row['destination'])
            if s in node_set and d in node_set and s != d:
                outlinks[s].add(d)
                inlinks[d].add(s)
                
    pr = {node: 1.0 / N for node in nodes}
    
    for _ in range(max_iter):
        dangling_sum = sum(pr[n] for n in nodes if len(outlinks[n]) == 0)
        new_pr = {}
        total_diff = 0.0
        
        for n in nodes:
            in_sum = sum(pr[in_node] / len(outlinks[in_node]) for in_node in inlinks[n])
            rank = ((1.0 - damping) / N) + (damping * (dangling_sum / N)) + (damping * in_sum)
            new_pr[n] = rank
            total_diff += abs(rank - pr[n])
            
        pr = new_pr
        if total_diff < tol:
            break
            
    min_pr = min(pr.values()) if pr else 1e-12
    max_pr = max(pr.values()) if pr else 1.0
    
    score_dict = {}
    for n, val in pr.items():
        if max_pr == min_pr:
            score_dict[n] = 50.0
        else:
            log_min = -12.0 if min_pr <= 0 else min(0.0, float(__import__('math').log10(min_pr)))
            log_max = float(__import__('math').log10(max_pr))
            log_val = float(__import__('math').log10(val))
            norm = (log_val - log_min) / (log_max - log_min + 1e-9)
            score_dict[n] = round(max(0.0, min(100.0, norm * 100)), 1)
            
    sorted_nodes = sorted(nodes, key=lambda x: pr[x])
    percentile_dict = {n: round((idx / max(1, N - 1)) * 100, 1) for idx, n in enumerate(sorted_nodes)}
    
    return pr, score_dict, percentile_dict

def validate_hreflang_matrix(df_internal):
    if df_internal.empty or 'Hreflang Tags' not in df_internal.columns:
        return pd.DataFrame(), 0
    
    crawled_map = {normalize_url(row['Address']): row for _, row in df_internal.iterrows()}
    records = []
    
    for _, page in df_internal.iterrows():
        source_url = normalize_url(page['Address'])
        tags_json = page.get('Hreflang Tags', '')
        if not tags_json:
            continue
        try:
            pairs = json.loads(tags_json)
        except Exception:
            continue
            
        has_self_ref = False
        for hl_code, target_url in pairs:
            norm_target = normalize_url(target_url)
            hl_code_clean = hl_code.strip().lower()
            
            if norm_target == source_url:
                has_self_ref = True
                
            iso_error = ""
            if hl_code_clean != 'x-default':
                parts = hl_code_clean.split('-')
                if len(parts) == 1:
                    if parts[0] not in ISO_639_1_LANGS:
                        iso_error = f"Invalid Language Code '{parts[0]}'"
                elif len(parts) == 2:
                    if parts[0] not in ISO_639_1_LANGS:
                        iso_error = f"Invalid Language Code '{parts[0]}'"
                    elif parts[1] not in ISO_3166_1_COUNTRIES:
                        if parts[1] == 'uk':
                            iso_error = "Invalid Country 'uk' (Use 'gb' for Great Britain)"
                        else:
                            iso_error = f"Invalid Country Code '{parts[1]}'"
                else:
                    iso_error = f"Malformed Hreflang Syntax '{hl_code_clean}'"
                    
            return_status = "Valid"
            target_status = "Unknown"
            
            if norm_target in crawled_map:
                target_page = crawled_map[norm_target]
                target_status = str(target_page.get('Status Code', '200'))
                if target_page.get('Indexability') == 'Non-Indexable':
                    target_status += " (Non-Indexable)"
                    
                target_tags = target_page.get('Hreflang Tags', '')
                reciprocal_found = False
                if target_tags:
                    try:
                        t_pairs = json.loads(target_tags)
                        for _, t_target in t_pairs:
                            if normalize_url(t_target) == source_url:
                                reciprocal_found = True
                                break
                    except Exception:
                        pass
                if not reciprocal_found:
                    return_status = "Missing Return Tag"
            else:
                target_status = "Not Crawled / External"
                return_status = "Unverified (External URL)"
                
            records.append({
                "Source URL": source_url,
                "Hreflang Code": hl_code_clean,
                "Target URL": target_url,
                "Target Status": target_status,
                "Return Tag Status": return_status,
                "ISO Validation": iso_error if iso_error else "Valid",
                "Has Self-Ref": "Yes" if has_self_ref else "Pending"
            })
            
        if not has_self_ref and pairs:
            for r in records:
                if r["Source URL"] == source_url:
                    r["Has Self-Ref"] = "No (Missing Self-Reference)"

    df_hreflang = pd.DataFrame(records)
    issue_count = 0
    if not df_hreflang.empty:
        issue_count = (
            (df_hreflang['Return Tag Status'] == 'Missing Return Tag') |
            (df_hreflang['ISO Validation'] != 'Valid') |
            (df_hreflang['Has Self-Ref'].str.startswith('No')) |
            (df_hreflang['Target Status'].str.contains('Non-Indexable|404|500', na=False))
        ).sum()
        
    return df_hreflang, int(issue_count)

def parse_gsc_performance_data(file_bytes_or_buffer):
    try:
        df = pd.read_csv(file_bytes_or_buffer)
        col_map = {}
        for col in df.columns:
            c_low = col.lower().strip()
            if 'page' in c_low or 'url' in c_low or 'top pages' in c_low:
                col_map[col] = 'GSC_URL'
            elif 'click' in c_low:
                col_map[col] = 'GSC_Clicks'
            elif 'impression' in c_low:
                col_map[col] = 'GSC_Impressions'
            elif 'ctr' in c_low:
                col_map[col] = 'GSC_CTR'
            elif 'position' in c_low:
                col_map[col] = 'GSC_Position'
                
        df = df.rename(columns=col_map)
        if 'GSC_URL' not in df.columns:
            return pd.DataFrame()
            
        df['__norm_gsc'] = df['GSC_URL'].apply(lambda u: normalize_url(str(u), strip_trailing_slash=True, strip_www=True))
        for num_col in ['GSC_Clicks', 'GSC_Impressions', 'GSC_Position']:
            if num_col in df.columns:
                df[num_col] = pd.to_numeric(df[num_col].astype(str).str.replace(',', ''), errors='coerce').fillna(0)
        if 'GSC_CTR' in df.columns:
            df['GSC_CTR'] = df['GSC_CTR'].astype(str).str.rstrip('%')
            df['GSC_CTR'] = pd.to_numeric(df['GSC_CTR'], errors='coerce').fillna(0)
            
        return df[['__norm_gsc', 'GSC_URL', 'GSC_Clicks', 'GSC_Impressions', 'GSC_CTR', 'GSC_Position']].drop_duplicates(subset=['__norm_gsc'])
    except Exception:
        return pd.DataFrame()

# ==============================================================================
# 3. HTML PARSER & CONTENT EXTRACTION
# ==============================================================================
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
        "Size (KB)": 0, "TTFB (s)": 0, "Content Hash": "", "SimHash": 0, "Last-Modified": "", "ETag": "",
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

    # Compute visible text, word count & SimHash
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

    # Content Deduplication Hash (Exact MD5 + 64-bit SimHash)
    normalized_content = content_for_hashing(clean_soup)
    row["Content Hash"] = hashlib.md5(normalized_content.encode('utf-8', errors='replace')).hexdigest() if normalized_content else ""
    row["SimHash"] = compute_simhash_64(normalized_content) if normalized_content else 0

    return row, link_rows, image_rows

# ==============================================================================
# 4. SITEMAP & HARDENED ASYNC CRAWLER ENGINE
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
            for sm in soup.find_all('sitemap'):
                loc = sm.find('loc')
                if loc and loc.text and loc.text.strip():
                    child_sm = loc.text.strip()
                    if child_sm not in seen_sitemaps:
                        queue.append(child_sm)
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

    visited, queued, queue = set(), set(), deque()
    seed = normalize_url(base_url)
    if is_crawlable_url(seed):
        queue.append((seed, 0))
        queued.add(seed)

    host_locks = defaultdict(asyncio.Lock)
    host_last_req = defaultdict(lambda: 0.0)

    async def polite_delay(host):
        delay = 0.35 + (random.uniform(0.1, 0.3) if stealth_jitter else 0.0)
        async with host_locks[host]:
            elapsed = time.time() - host_last_req[host]
            if elapsed < delay:
                await asyncio.sleep(delay - elapsed)
            host_last_req[host] = time.time()

    ssl_ctx = ssl.create_default_context()
    ssl_ctx.check_hostname = False
    ssl_ctx.verify_mode = ssl.CERT_NONE

    # Hardened fetch_async: Inspects headers first, streams body with 4MB max cap
    async def fetch_async(session_aio, url, depth):
        host = urlparse(url).hostname or target_hostname
        last_status = None
        for attempt in range(MAX_RETRIES + 1):
            await polite_delay(host)
            start = time.time()
            try:
                async with session_aio.get(url, timeout=aiohttp.ClientTimeout(total=20), allow_redirects=True, ssl=ssl_ctx) as resp:
                    if resp.status in RETRY_STATUSES and attempt < MAX_RETRIES:
                        last_status = resp.status
                        await asyncio.sleep(1.2 * (attempt + 1))
                        continue
                    
                    resp_headers = {k.lower(): v for k, v in resp.headers.items()}
                    ct = resp_headers.get('content-type', '').lower()
                    
                    # Memory Guard: If non-HTML (e.g. PDF, video, zip), don't buffer massive payload
                    if 'text/html' not in ct and 'application/xhtml' not in ct:
                        shim = ResponseShim(resp.status, str(resp.url), resp_headers, b'')
                        row, links, images = build_row(url, depth, is_in_scope, resp=shim, in_sitemap=(url in sitemap_pages))
                        row["TTFB (s)"] = round(time.time() - start, 3)
                        return row, links, images, None
                        
                    # Stream read HTML body up to MAX_HTML_BODY_BYTES to prevent memory blowout
                    content = await resp.content.read(MAX_HTML_BODY_BYTES)
                    hist = [ResponseShim(h.status, str(h.url), {}, b'') for h in resp.history]
                    shim = ResponseShim(resp.status, str(resp.url), resp_headers, content, hist)
                    row, links, images = build_row(url, depth, is_in_scope, resp=shim, in_sitemap=(url in sitemap_pages))
                    row["TTFB (s)"] = round(time.time() - start, 3)
                    del shim
                    del content
                    return row, links, images, None
            except Exception as e:
                if attempt < MAX_RETRIES:
                    await asyncio.sleep(0.8 * (attempt + 1))
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
    last_ui_update = 0.0

    async with aiohttp.ClientSession(connector=connector, headers=headers) as aio_session:
        while (queue or (pages_counted < crawl_limit and any(u not in visited and u not in queued for u in sitemap_pages))) and pages_counted < crawl_limit and processed < fetch_ceiling:
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
                
            cur.execute("COMMIT")

            # Throttled Streamlit UI Update (every 400ms) to prevent WebSocket queue drops
            now = time.time()
            if now - last_ui_update > 0.4 or pages_counted >= crawl_limit:
                elapsed = max(0.1, now - start_time_crawl)
                speed = round(processed / elapsed, 1)
                mem = round(psutil.Process(os.getpid()).memory_info().rss / 1024 / 1024, 1) if HAS_PSUTIL else 0.0
                progress_callback(min(pages_counted / crawl_limit, 1.0), pages_counted, processed, len(queue), speed, mem, row.get("TTFB (s)", 0.0))
                last_ui_update = now

            # Periodic memory garbage collection every 250 pages
            if processed % 250 == 0:
                gc.collect()

        # Chunked Image Payload Sizer (Batched in 50s with max limit to avoid OOM)
        status_callback("📏 Measuring image payload sizes in batches...")
        cur.execute("SELECT DISTINCT address FROM images LIMIT 2500")
        img_urls = [r[0] for r in cur.fetchall()]
        if img_urls:
            sem = asyncio.Semaphore(12)
            async def get_img_size(u):
                async with sem:
                    try:
                        async with aio_session.head(u, timeout=aiohttp.ClientTimeout(total=4), ssl=ssl_ctx) as r_img:
                            cl = r_img.headers.get('Content-Length')
                            if cl and cl.isdigit():
                                return u, round(int(cl) / 1024, 2)
                    except Exception:
                        pass
                    return u, 0.0

            chunk_size = 50
            for i in range(0, len(img_urls), chunk_size):
                chunk = img_urls[i:i+chunk_size]
                img_sizes = await asyncio.gather(*[get_img_size(u) for u in chunk])
                cur.execute("BEGIN TRANSACTION")
                cur.executemany("UPDATE images SET size_kb = ? WHERE address = ?", [(sz, u) for u, sz in img_sizes])
                cur.execute("COMMIT")

    conn.close()
    gc.collect()
    return target_hostname

# ==============================================================================
# 5. POST-CRAWL DATA ANALYSIS & TIER 1 INTELLIGENCE
# ==============================================================================
def run_full_analysis(db_path, gsc_df=None, pr_damping=0.85, simhash_threshold=85.0):
    conn = sqlite3.connect(db_path)
    sitemap_pages_set = set([r[0] for r in conn.execute("SELECT url FROM sitemaps")])
    
    rows = [json.loads(r[0]) for r in conn.execute("SELECT data FROM pages")]
    df_internal = pd.DataFrame(rows) if rows else pd.DataFrame()
    df_links = pd.read_sql_query("SELECT source, destination, anchor, nofollow, in_scope as [In Scope] FROM links", conn)
    df_images = pd.read_sql_query("SELECT address, alt as [Alt Text], size_kb as [Size (KB)], parent_page as [Parent Page], loading FROM images", conn)
    df_errors = pd.read_sql_query("SELECT url as [Address], error_type as [Error Type], message as Message, ts as Timestamp FROM errors", conn)
    
    df_links_internal = df_links[df_links['In Scope'] == 1].drop(columns=['In Scope']).copy() if not df_links.empty else pd.DataFrame(columns=['source', 'destination', 'anchor', 'nofollow'])
    df_links_external = df_links[df_links['In Scope'] == 0].drop(columns=['In Scope']).copy() if not df_links.empty else pd.DataFrame(columns=['source', 'destination', 'anchor', 'nofollow'])

    # 1. Internal Link Count Calculation
    if not df_internal.empty and not df_links_internal.empty:
        df_internal['__norm'] = df_internal['Address'].apply(normalize_url)
        unique_inlinks = df_links_internal.groupby('destination')['source'].nunique()
        total_inlinks = df_links_internal['destination'].value_counts()
        df_internal['Unique Inlinks'] = df_internal['__norm'].map(unique_inlinks).fillna(0).astype(int)
        df_internal['Total Inlinks'] = df_internal['__norm'].map(total_inlinks).fillna(0).astype(int)
    elif not df_internal.empty:
        df_internal['__norm'] = df_internal['Address'].apply(normalize_url)
        df_internal['Unique Inlinks'] = 0
        df_internal['Total Inlinks'] = 0

    # 2. Internal PageRank Computation
    pr_raw, pr_score, pr_percentile = calculate_internal_pagerank(df_internal, df_links_internal, damping=pr_damping)
    if not df_internal.empty:
        df_internal['Internal PageRank'] = df_internal['__norm'].map(pr_raw).fillna(0.0)
        df_internal['PageRank Score'] = df_internal['__norm'].map(pr_score).fillna(0.0)
        df_internal['PageRank Percentile'] = df_internal['__norm'].map(pr_percentile).fillna(0.0)

    # 3. Link Equity Waste & Sinkhole Identification
    df_equity_sinkholes = pd.DataFrame()
    if not df_internal.empty:
        high_equity_mask = df_internal['PageRank Percentile'] >= 70.0
        broken_mask = df_internal['Status Code'] >= 400
        redirect_mask = df_internal['Status Code'].isin([301, 302, 307, 308])
        non_indexable_mask = (df_internal['Indexability'] == 'Non-Indexable') & (df_internal['Status Code'] == 200)
        
        sinkhole_mask = high_equity_mask & (broken_mask | redirect_mask | non_indexable_mask)
        if sinkhole_mask.any():
            df_equity_sinkholes = df_internal[sinkhole_mask][[
                'Address', 'Status Code', 'Indexability', 'Indexability Reason',
                'PageRank Score', 'PageRank Percentile', 'Unique Inlinks', 'Crawl Depth'
            ]].sort_values('PageRank Score', ascending=False)

    # 4. Optimized SimHash Near-Duplicate Detection (Capped pairwise loop to prevent OOM)
    near_dup_records = []
    if not df_internal.empty and 'SimHash' in df_internal.columns:
        pages_with_hash = df_internal[df_internal['SimHash'] > 0][['Address', 'Title 1', 'SimHash', 'Word Count', 'Status Code']]
        pages_with_hash = pages_with_hash[pages_with_hash['Status Code'] == 200].to_dict('records')
        
        # Limit comparisons to max 2,000 pages to avoid quadratic memory freeze
        limit_pages = pages_with_hash[:2000]
        for i in range(len(limit_pages)):
            for j in range(i + 1, min(i + 200, len(limit_pages))):
                p1, p2 = limit_pages[i], limit_pages[j]
                sim = simhash_similarity(p1['SimHash'], p2['SimHash'])
                if sim >= simhash_threshold:
                    near_dup_records.append({
                        "Page A": p1['Address'],
                        "Page B": p2['Address'],
                        "Similarity (%)": sim,
                        "Title A": p1['Title 1'][:80],
                        "Title B": p2['Title 1'][:80],
                        "Words A": p1['Word Count'],
                        "Words B": p2['Word Count'],
                        "Severity": "Critical" if sim >= 95.0 else "High"
                    })
    df_near_duplicates = pd.DataFrame(near_dup_records)
    if not df_near_duplicates.empty:
        df_near_duplicates = df_near_duplicates.sort_values('Similarity (%)', ascending=False)

    # 5. Hreflang Validation Matrix
    df_hreflang_matrix, hreflang_issues_count = validate_hreflang_matrix(df_internal)

    # 6. Exact Duplicates
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

    # 7. GSC Data Fusion Integration
    df_gsc_fusion = pd.DataFrame()
    gsc_at_risk_count = 0
    if gsc_df is not None and not gsc_df.empty and not df_internal.empty:
        df_internal['__norm_gsc'] = df_internal['Address'].apply(lambda u: normalize_url(u, strip_trailing_slash=True, strip_www=True))
        df_gsc_merged = pd.merge(df_internal, gsc_df, on='__norm_gsc', how='inner')
        if not df_gsc_merged.empty:
            df_gsc_fusion = df_gsc_merged[[
                'Address', 'Status Code', 'Indexability', 'Indexability Reason',
                'GSC_Clicks', 'GSC_Impressions', 'GSC_CTR', 'GSC_Position',
                'PageRank Score', 'PageRank Percentile', 'Unique Inlinks', 'Crawl Depth', 'Title 1'
            ]].sort_values('GSC_Clicks', ascending=False)
            
            at_risk_mask = (df_gsc_fusion['GSC_Clicks'] > 0) & ((df_gsc_fusion['Status Code'] >= 400) | (df_gsc_fusion['Indexability'] == 'Non-Indexable'))
            gsc_at_risk_count = int(at_risk_mask.sum())
        df_internal.drop(columns=['__norm_gsc'], errors='ignore', inplace=True)

    # 8. Orphan URLs
    crawled_urls = set(df_internal['Address'].apply(normalize_url)) if not df_internal.empty else set()
    orphan_pages = sitemap_pages_set - crawled_urls
    df_orphans = pd.DataFrame([{"Address": u, "Type": "In sitemap, not reached by crawl"} for u in sorted(orphan_pages)]) if orphan_pages else pd.DataFrame(columns=['Address', 'Type'])

    # 9. Complete Issues Summary Aggregation
    issues = []
    def add_issue(cat, sev, count, desc):
        if count > 0:
            issues.append({"Category": cat, "Severity": sev, "Count": int(count), "Description": desc})

    if not df_internal.empty:
        parsed = df_internal[(df_internal['Status Code'] == 200) & (df_internal['Word Count'] > 0)]
        
        if spa_shell_count > 0:
            add_issue("Architecture", "Critical", spa_shell_count, "Client-Side Rendered (SPA) Shell Detected — Routes return identical raw HTML shell")
        if not df_equity_sinkholes.empty:
            add_issue("Link Equity", "Critical", len(df_equity_sinkholes), "PageRank Equity Sinkholes (High PageRank to Non-Indexable/Broken/Redirected URLs)")
        if gsc_at_risk_count > 0:
            add_issue("Traffic Risk", "Critical", gsc_at_risk_count, "High Organic Traffic Pages at Risk (GSC Clicked Pages Returning 4xx/5xx/Noindex)")

        add_issue("Status", "Critical", (df_internal['Status Code'] >= 500).sum(), "5xx Server Errors")
        add_issue("Status", "Critical", (df_internal['Status Code'] == 404).sum(), "404 Not Found Pages")
        add_issue("Status", "High", (df_internal['Status Code'].isin([301, 308])).sum(), "Permanent Redirects (301/308)")
        
        if not df_links_internal.empty:
            status_map = dict(zip(df_internal['Address'].apply(normalize_url), df_internal['Status Code']))
            dest_statuses = df_links_internal['destination'].map(status_map).fillna(0)
            broken_int_links_count = int((dest_statuses >= 400).sum())
            add_issue("Links", "High", broken_int_links_count, "Broken Internal Links (4xx/5xx Destination)")

        if not df_near_duplicates.empty:
            add_issue("Content", "High", len(df_near_duplicates), f"Near-Duplicate Content Pairs (SimHash Similarity ≥ {simhash_threshold}%)")

        add_issue("Titles", "High", (parsed['Title Status'] == 'Missing').sum(), "Missing Title Tags")
        add_issue("Titles", "Medium", (parsed['Title Status'] == 'Too Short').sum(), "Short Title Tags (<200px)")
        add_issue("Titles", "Medium", (parsed['Title Status'] == 'Too Long').sum(), "Titles Exceeding 580px")
        add_issue("Titles", "High", parsed.get('Duplicate Title', pd.Series()).sum(), "Duplicate Titles")
        
        add_issue("Meta Description", "High", (parsed['Meta Status'] == 'Missing').sum(), "Missing Meta Descriptions")
        add_issue("Meta Description", "Medium", (parsed['Meta Status'] == 'Too Long').sum(), "Oversized Meta Descriptions (>920px)")
        add_issue("Meta Description", "Low", (parsed['Meta Status'] == 'Too Short').sum(), "Short Meta Descriptions (<400px)")

        add_issue("Headings", "High", (parsed['H1 Count'] == 0).sum(), "Missing H1 Tags")
        add_issue("Headings", "Medium", (parsed['H1 Count'] > 1).sum(), "Multiple H1 Tags")
        add_issue("Headings", "High", parsed.get('Duplicate H1', pd.Series()).sum(), "Duplicate H1 Tags")

        add_issue("Content", "High", parsed.get('Duplicate Content', pd.Series()).sum(), "Identical Body Content (MD5 Exact Match)")
        add_issue("Content", "Medium", (parsed['Word Count'] < 200).sum(), "Thin Content (<200 words)")
        
        add_issue("Canonical", "High", (parsed['Canonical Count'] > 1).sum(), "Multiple Canonical Tags")
        add_issue("Canonical", "Medium", (parsed['Canonical Match'] == 'Different').sum(), "Canonicalized to a Different URL")
        
        add_issue("Hreflang", "High", hreflang_issues_count, "Hreflang Validation Errors (Missing Return Tag, Invalid ISO Code, or Missing Self-Ref)")

    if not df_images.empty:
        missing_alt_count = int((df_images['Alt Text'].isin(['(Missing)', '', None]) | df_images['Alt Text'].isna()).sum())
        oversized_images_count = int((df_images['Size (KB)'] > 100).sum())
        add_issue("Images", "Medium", missing_alt_count, "Images Missing Alt Text")
        add_issue("Images", "Medium", oversized_images_count, "Images Over 100 KB (Unoptimized Payload)")

    df_issues = pd.DataFrame(issues) if issues else pd.DataFrame(columns=['Category', 'Severity', 'Count', 'Description'])
    if not df_issues.empty:
        severity_order = {"Critical": 0, "High": 1, "Medium": 2, "Low": 3}
        df_issues['__sort'] = df_issues['Severity'].map(severity_order)
        df_issues = df_issues.sort_values(['__sort', 'Count'], ascending=[True, False]).drop(columns=['__sort'])

    df_internal.drop(columns=['__norm'], errors='ignore', inplace=True)
    conn.close()
    gc.collect()
    
    return {
        "Issues Summary": df_issues,
        "Internal Pages": df_internal,
        "PageRank & Equity": df_equity_sinkholes if not df_equity_sinkholes.empty else pd.DataFrame(columns=['Address', 'Status Code', 'Indexability', 'PageRank Score', 'Unique Inlinks']),
        "Near Duplicates (SimHash)": df_near_duplicates if not df_near_duplicates.empty else pd.DataFrame(columns=['Page A', 'Page B', 'Similarity (%)', 'Severity']),
        "Hreflang Matrix": df_hreflang_matrix if not df_hreflang_matrix.empty else pd.DataFrame(columns=['Source URL', 'Hreflang Code', 'Target URL', 'Return Tag Status', 'ISO Validation']),
        "GSC Performance Fusion": df_gsc_fusion if not df_gsc_fusion.empty else pd.DataFrame(columns=['Address', 'GSC_Clicks', 'GSC_Impressions', 'Status Code', 'PageRank Score']),
        "Duplicates (Exact)": df_duplicates if not df_duplicates.empty else pd.DataFrame(columns=['Duplicate Type', 'Value', 'Count']),
        "Internal Links": df_links_internal,
        "External Links": df_links_external,
        "Images": df_images if not df_images.empty else pd.DataFrame(columns=['address', 'Alt Text', 'Size (KB)', 'Parent Page', 'loading']),
        "Orphan Pages": df_orphans,
        "Crawl Errors": df_errors if not df_errors.empty else pd.DataFrame(columns=['Address', 'Error Type', 'Message', 'Timestamp'])
    }

# ==============================================================================
# 6. MULTI-TAB IN-MEMORY EXCEL EXPORTER
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
# 7. STREAMLIT ENTERPRISE AUDITOR INTERFACE
# ==============================================================================
st.set_page_config(page_title="SEO-Diver Enterprise Auditor", page_icon="🕷️", layout="wide")

st.title("🕷️ SEO-Diver Technical Auditor — Enterprise Tier 1")
st.caption("Enterprise technical SEO crawler: Internal PageRank modeling, SimHash near-duplicate clustering, Hreflang reciprocity matrix, and Google Search Console performance data fusion.")

st.sidebar.header("🎯 Crawl Parameters")
start_url = st.sidebar.text_input("Start URL", "https://almarai.com/").strip().rstrip('/')
if not start_url.startswith(('http://', 'https://')):
    start_url = 'https://' + start_url

scope_mode = st.sidebar.selectbox(
    "Crawl Scope",
    ["This Subdomain Only (Apex + WWW)", "Root Domain & All Subdomains", "This Subfolder Only"],
    index=0
)

col_a, col_b = st.sidebar.columns(2)
with col_a:
    crawl_limit = st.number_input("Crawl Limit", min_value=10, max_value=50000, value=2500, step=250)
with col_b:
    concurrency = st.slider("Concurrency", min_value=1, max_value=24, value=8)

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

with st.sidebar.expander("⚙️ Tier 1 Advanced Algorithms", expanded=False):
    pr_damping = st.slider("PageRank Damping Factor", min_value=0.50, max_value=0.95, value=0.85, step=0.05)
    simhash_threshold = st.slider("SimHash Duplicate Threshold (%)", min_value=70, max_value=98, value=85, step=1)
    stealth_jitter = st.toggle("Enable Stealth Jitter (Anti-WAF)", value=True)
    respect_robots = st.toggle("Respect robots.txt", value=False)

st.sidebar.markdown("---")
st.sidebar.subheader("📈 Google Search Console (GSC)")
gsc_file = st.sidebar.file_uploader("Upload GSC Pages.csv", type=["csv", "txt"], help="Upload an exported Pages.csv from Google Search Console to correlate organic traffic with technical health.")

gsc_data = None
if gsc_file is not None:
    gsc_data = parse_gsc_performance_data(gsc_file)
    if not gsc_data.empty:
        st.sidebar.success(f"✓ Ingested {len(gsc_data):,} GSC URLs")
    else:
        st.sidebar.error("Could not parse GSC CSV format.")

start_crawl_button = st.sidebar.button("🚀 Run Enterprise Audit", type="primary", use_container_width=True)

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

    status_box = st.status("Initializing Enterprise SEO Crawler...", expanded=True)
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

    status_box.update(label="Crawling Complete! Computing Graph PageRank & SimHash...", state="running")
    results = run_full_analysis(temp_db, gsc_df=gsc_data, pr_damping=pr_damping, simhash_threshold=simhash_threshold)
    status_box.update(label="✅ Enterprise Audit Complete!", state="complete", expanded=False)

    st.session_state['audit_results'] = results
    st.session_state['audit_url'] = final_target_host

if 'audit_results' in st.session_state:
    res = st.session_state['audit_results']
    host = st.session_state['audit_url']

    st.subheader(f"📊 Audit Dashboard: {host}")

    df_int = res['Internal Pages']
    kpi1, kpi2, kpi3, kpi4, kpi5 = st.columns(5)
    with kpi1:
        st.metric("Total Crawled Pages", len(df_int))
    with kpi2:
        indexable_count = (df_int['Indexability'] == 'Indexable').sum() if not df_int.empty else 0
        st.metric("Indexable Pages", int(indexable_count))
    with kpi3:
        broken_count = (df_int['Status Code'] >= 400).sum() if not df_int.empty else 0
        st.metric("4xx/5xx Errors", int(broken_count))
    with kpi4:
        sinkholes_count = len(res['PageRank & Equity']) if not res['PageRank & Equity'].empty else 0
        st.metric("PageRank Sinkholes", int(sinkholes_count))
    with kpi5:
        near_dups_count = len(res['Near Duplicates (SimHash)']) if not res['Near Duplicates (SimHash)'].empty else 0
        st.metric("Near-Duplicate Pairs", int(near_dups_count))

    excel_file = create_excel_report(res)
    st.download_button(
        label="📥 Download Enterprise Excel Workbook (.xlsx)",
        data=excel_file,
        file_name=f"enterprise_seo_audit_{host}_{datetime.now().strftime('%Y%m%d_%H%M')}.xlsx",
        mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
        type="primary"
    )

    tab_issues, tab_internal, tab_pagerank, tab_simhash, tab_hreflang, tab_gsc, tab_duplicates, tab_links, tab_images, tab_orphans, tab_errors = st.tabs([
        "⚠️ Issues Summary",
        "📄 Internal Pages",
        "📊 PageRank & Equity",
        "🧬 Near-Duplicates",
        "🌐 Hreflang Matrix",
        "📈 GSC Fusion",
        "👥 Exact Duplicates",
        "🔗 Links",
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
            cols_to_show = [
                'Address', 'Status Code', 'Indexability', 'Indexability Reason',
                'PageRank Score', 'PageRank Percentile', 'Unique Inlinks', 'Crawl Depth',
                'Title 1', 'Word Count', 'Canonical Match', 'TTFB (s)'
            ]
            st.dataframe(df_int[[c for c in cols_to_show if c in df_int.columns]], use_container_width=True)

    with tab_pagerank:
        st.markdown("### 📊 Internal PageRank & Link Equity Distribution")
        st.caption("Measures how internal link equity flows through the website topology. Highlights **PageRank Sinkholes** (high link equity wasted on broken or non-indexable URLs).")
        
        if not df_int.empty and 'PageRank Score' in df_int.columns:
            col_pr1, col_pr2 = st.columns(2)
            with col_pr1:
                st.markdown("#### 🏆 Top 15 Highest PageRank Pages")
                top_pr = df_int.sort_values('PageRank Score', ascending=False)[[
                    'Address', 'PageRank Score', 'PageRank Percentile', 'Unique Inlinks', 'Crawl Depth', 'Indexability'
                ]].head(15)
                st.dataframe(top_pr, use_container_width=True, hide_index=True)
                
            with col_pr2:
                st.markdown("#### 🚨 Top Link Equity Sinkholes")
                if not res['PageRank & Equity'].empty:
                    st.dataframe(res['PageRank & Equity'].head(15), use_container_width=True, hide_index=True)
                else:
                    st.success("Zero Link Equity Sinkholes detected! Internal equity is distributed cleanly.")

    with tab_simhash:
        st.markdown("### 🧬 SimHash 64-bit Near-Duplicate Content Clusters")
        st.caption(f"Identifies pages with body content similarity ≥ {simhash_threshold}% (e.g. faceted products, regional duplicate pages, thin variants).")
        if not res['Near Duplicates (SimHash)'].empty:
            st.dataframe(res['Near Duplicates (SimHash)'], use_container_width=True, hide_index=True)
        else:
            st.success("Zero near-duplicate content pairs identified.")

    with tab_hreflang:
        st.markdown("### 🌐 Multi-Lingual Hreflang Validation Matrix")
        st.caption("Audits reciprocal return tags, self-referential tags, and ISO 639-1 / ISO 3166-1 syntax conformance.")
        if not res['Hreflang Matrix'].empty:
            st.dataframe(res['Hreflang Matrix'], use_container_width=True, hide_index=True)
        else:
            st.info("No hreflang tags found on crawled pages.")

    with tab_gsc:
        st.markdown("### 📈 Google Search Console (GSC) Performance Fusion")
        st.caption("Correlates real-world Google organic search traffic (Clicks, Impressions, CTR, Position) with crawler indexability and PageRank.")
        if not res['GSC Performance Fusion'].empty:
            st.dataframe(res['GSC Performance Fusion'], use_container_width=True, hide_index=True)
        else:
            st.info("Upload a Google Search Console `Pages.csv` export in the sidebar to view organic performance fusion.")

    with tab_duplicates:
        st.markdown("### 👥 Exact MD5 Duplicates")
        if not res['Duplicates (Exact)'].empty:
            st.dataframe(res['Duplicates (Exact)'], use_container_width=True, hide_index=True)
        else:
            st.info("No exact duplicate content or titles identified.")

    with tab_links:
        st.markdown("### 🔗 Internal Links Graph")
        if not res['Internal Links'].empty:
            st.dataframe(res['Internal Links'].head(1000), use_container_width=True)

    with tab_images:
        st.markdown("### 🖼️ Image Assets & Payloads")
        if not res['Images'].empty:
            st.dataframe(res['Images'].head(1000), use_container_width=True)

    with tab_orphans:
        st.markdown("### 👤 Orphan Pages (In Sitemap but Not Crawled)")
        if not res['Orphan Pages'].empty:
            st.dataframe(res['Orphan Pages'], use_container_width=True, hide_index=True)
        else:
            st.success("Zero orphan URLs detected.")

    with tab_errors:
        st.markdown("### 🚨 Crawl & Network Errors")
        if not res['Crawl Errors'].empty:
            st.dataframe(res['Crawl Errors'], use_container_width=True, hide_index=True)
        else:
            st.success("Zero crawl-time network/bot errors.")
