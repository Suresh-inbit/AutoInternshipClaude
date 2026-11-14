#!/usr/bin/env python3
"""Find internships and entry-level jobs in India on companies' own job boards.

  python find_india_jobs.py --folder "<job-search folder>" [--role "computer vision" --role "machine learning" ...]
                            [--location Chennai --location Bengaluru ...] [--keyword ...] [--exclude-keyword ...]
                            [--level early|intern|any] [--primary-only] [--days N] [--limit N] [--company NAME] [--append]

The SimplifyJobs and speedyapply lists (find_internships.py) cover U.S. internships only. This script asks the
public job boards of the employers in references/india-companies.json (Greenhouse, Lever, Ashby, SmartRecruiters,
Workday, Amazon) for their open jobs, keeps the ones in the chosen Indian cities (or remote in India) whose titles
match the user's target roles and level, and drops ones already in the tracker or jobs.txt.

Search preferences come from the command line, else profile.json, else these defaults (reported under
`defaults_used`, so the skill can ask the user to confirm or change them and save the answer to the profile):
  targetRoles        ["computer vision", "machine learning"]   (role families in ROLE_WORDS; the first is primary)
  preferredLocations Bengaluru, Hyderabad, Chennai, Pune, Mumbai, Delhi NCR, Remote
  jobLevel           early: interns, new-grad and entry-level titles and titles that name no level; no senior ones
  excludeKeywords    []  (titles to drop, grown from the user's feedback on earlier results)

With --append the matches go into jobs.txt in the same format as find_internships.py, and the queue is sorted
the same way (two per company), with the user's primary role first. Prints JSON.
"""
import argparse
import concurrent.futures as cf
import datetime as dt
import json
import os
import re
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import find_internships as fi  # noqa: E402  (shared queue, tracker and dedupe helpers)

CONFIG = os.path.join(HERE, '..', 'references', 'india-companies.json')
USER_AGENT = 'Mozilla/5.0 (compatible; AutoInternship job-search script; reads public job postings)'

CITY_ALIASES = {
    'chennai': ['chennai', 'madras'],
    'bengaluru': ['bengaluru', 'bangalore', 'blr'],
    'bangalore': ['bengaluru', 'bangalore', 'blr'],
    'hyderabad': ['hyderabad', 'secunderabad', 'hyd'],
    'hyd': ['hyderabad', 'secunderabad'],
    'coimbatore': ['coimbatore', 'kovai'],
    'pune': ['pune'], 'mumbai': ['mumbai', 'bombay', 'navi mumbai'], 'delhi': ['delhi', 'new delhi'],
    'delhi ncr': ['delhi', 'new delhi', 'gurgaon', 'gurugram', 'noida', 'ncr'], 'ncr': ['delhi', 'gurgaon', 'gurugram', 'noida', 'ncr'],
    'gurgaon': ['gurgaon', 'gurugram'], 'gurugram': ['gurgaon', 'gurugram'], 'noida': ['noida'],
    'kochi': ['kochi', 'cochin'], 'trivandrum': ['trivandrum', 'thiruvananthapuram'], 'mysuru': ['mysuru', 'mysore'],
}
DEFAULT_LOCATIONS = ['Bengaluru', 'Hyderabad', 'Chennai', 'Pune', 'Mumbai', 'Delhi NCR', 'Remote']
INDIA = re.compile(r'\b(india|ind|bengaluru|bangalore|chennai|hyderabad|coimbatore|pune|mumbai|delhi|gurgaon|gurugram|noida|'
                   r'kolkata|ahmedabad|kochi|trivandrum|thiruvananthapuram|mysore|mysuru|karnataka|tamil nadu|telangana|maharashtra)\b', re.I)

# Role families a profile's targetRoles can name, each with the title words that count as a match. The first
# target role is the primary one: its matches go first in the results and the queue.
CV_WORDS = ['computer vision', 'vision', 'image', 'imaging', 'camera', 'perception', '3d', 'graphics', 'render', 'video analytics',
            'video understanding', 'visual computing', 'visual search',
            'slam', 'robot', 'robotics', 'algo', 'algorithm', 'algorithms', 'autonomous', 'adas', 'multimodal', 'multi-modal', 'generative', 'diffusion', 'gaussian', 'nerf',
            'photogrammetry', 'point cloud', 'lidar', 'optical', 'optics', 'gpu', 'cuda']
ML_WORDS = ['machine learning', 'deep learning', 'ml', 'ai', 'applied scientist', 'research', 'data scientist', 'scientist']
ROLE_WORDS = {
    'computer vision': CV_WORDS,
    'machine learning': ML_WORDS,
    'data science': ['data scientist', 'data science', 'analytics', 'data analyst', 'statistician', 'statistics'],
    'software': ['software', 'sde', 'developer', 'backend', 'back end', 'frontend', 'front end', 'full stack', 'fullstack'],
    'robotics': ['robot', 'robotics', 'slam', 'motion control', 'autonomous', 'perception', 'ros', 'mechatronics'],
    'embedded': ['embedded', 'firmware', 'fpga', 'vlsi', 'asic', 'rtl', 'hardware', 'silicon'],
    'research': ['research', 'researcher', 'scientist', 'algorithm'],
}
ROLE_ALIASES = {'cv': 'computer vision', 'vision': 'computer vision', 'ml': 'machine learning', 'ai': 'machine learning',
                'ai/ml': 'machine learning', 'ds': 'data science', 'data': 'data science', 'swe': 'software',
                'sde': 'software', 'software engineering': 'software', 'hardware': 'embedded', 'vlsi': 'embedded'}
DEFAULT_ROLES = ['computer vision', 'machine learning']


def role_family(name):
    key = str(name).strip().lower()
    return ROLE_ALIASES.get(key, key)
INTERN = re.compile(r'\b(intern|internship|interns|trainee|apprentice|co-?op|fresher|new grad|graduate|campus|university|'
                    r'student)\b', re.I)
# A year in the title ("2027 Graduate", "BGSW_2026_...") usually marks a campus hire, but not over "Senior"
CAMPUS_YEAR = re.compile(r'(?<!\d)202[6-9](?!\d)')
ENTRY = re.compile(r'\b(entry|junior|jr|associate|engineer i|engineer 1|level 1|l1|sde ?1|sde-?i|early career)\b', re.I)
SENIOR = re.compile(r'\b(senior|sr|staff|principal|lead|leader|manager|director|head|architect|vp|vice president|'
                    r'engineer (2|3|4)|sde ?(2|3)|experts?|specialists?|consultant|chief|distinguished|fellow)\b', re.I)
# "Applied Scientist II", "SDE IV", "Data Scientist III": a level two or above, written in capitals in the title
LEVEL_UP = re.compile(r'(?<![A-Za-z])(II|III|IV|V)(?![A-Za-z])')
# Titles that match a keyword but aren't engineering or research ("Visual Designer", "Technical Support Engineer (GPU)")
DEFAULT_EXCLUDE = ['designer', 'sales', 'marketing', 'recruit', 'support engineer', 'technical support', 'consultant',
                   'operations', 'governance', 'economist', 'admin', 'account manager', 'legal', 'finance', 'mechanics',
                   'product research', 'strategy']


class Down(Exception):
    pass


_last, _lock = {}, threading.Lock()


def get(url, data=None, headers=None):
    host = urllib.parse.urlparse(url).netloc
    h = {'User-Agent': USER_AGENT, 'Accept': 'application/json', **(headers or {})}
    if data is not None:
        data = json.dumps(data).encode()
        h['Content-Type'] = 'application/json'
    for attempt in (1, 2):
        with _lock:  # at most one request a second per site, across all threads
            start = max(time.monotonic(), _last.get(host, -1) + 1.0)
            _last[host] = start
        time.sleep(max(0, start - time.monotonic()))
        try:
            with urllib.request.urlopen(urllib.request.Request(url, data=data, headers=h), timeout=25) as r:
                final, body = r.geturl(), r.read().decode('utf-8', 'replace')
            break
        except urllib.error.HTTPError as e:
            if e.code in (429, 503) and attempt == 1:
                time.sleep(5); continue
            raise Down(f'answered {e.code}')
        except (urllib.error.URLError, TimeoutError, OSError) as e:
            if attempt == 1 and 'timed out' in str(getattr(e, 'reason', e)):
                continue  # one retry for a slow handshake
            raise Down(f"couldn't connect ({getattr(e, 'reason', e)})")
    if 'maintenance' in final or '/outage' in final:
        raise Down('down for maintenance (Workday is often down on weekends); try again later')
    try:
        return json.loads(body)
    except ValueError:
        raise Down("answered with a web page, not job data (board name may be wrong)")


def iso(value):
    """'YYYY-MM-DD' from an ISO string or a millisecond timestamp, else ''."""
    if isinstance(value, (int, float)) and value > 0:
        return dt.date.fromtimestamp(value / 1000 if value > 1e11 else value).isoformat()
    m = re.match(r'(\d{4}-\d{2}-\d{2})', str(value or ''))
    return m.group(1) if m else ''


# ---- one reader per kind of job board: each returns [{'role', 'locations', 'url', 'posted'}] ----

def greenhouse(c, terms):
    d = get(f"https://boards-api.greenhouse.io/v1/boards/{c['token']}/jobs")
    return [{'role': j['title'], 'locations': [j.get('location', {}).get('name', '')], 'url': j['absolute_url'],
             'posted': iso(j.get('first_published') or j.get('updated_at'))} for j in d.get('jobs', [])]


def lever(c, terms):
    d = get(f"https://api.lever.co/v0/postings/{c['token']}?mode=json")
    out = []
    for j in d:
        cat = j.get('categories') or {}
        locs = cat.get('allLocations') or [cat.get('location', '')]
        if j.get('workplaceType') == 'remote':
            locs = locs + [f"Remote ({j.get('country') or ''})"]
        out.append({'role': j['text'], 'locations': locs, 'url': j['hostedUrl'], 'posted': iso(j.get('createdAt'))})
    return out


def ashby(c, terms):
    d = get(f"https://api.ashbyhq.com/posting-api/job-board/{c['token']}")
    out = []
    for j in d.get('jobs', []):
        locs = [j.get('location', '')] + [s.get('location', '') for s in j.get('secondaryLocations') or []]
        addr = ((j.get('address') or {}).get('postalAddress') or {}).get('addressCountry')
        if j.get('isRemote'):
            locs.append(f"Remote ({addr or ''})")
        out.append({'role': j['title'], 'locations': locs, 'url': j['jobUrl'], 'posted': iso(j.get('publishedAt'))})
    return out


def smartrecruiters(c, terms):
    out, offset = [], 0
    while True:
        d = get(f"https://api.smartrecruiters.com/v1/companies/{c['token']}/postings?country=in&limit=100&offset={offset}")
        for j in d.get('content', []):
            loc = j.get('location') or {}
            place = ', '.join(x for x in (loc.get('city'), loc.get('region'), 'India') if x)
            if loc.get('remote'):
                place += ' (Remote)'
            out.append({'role': j['name'], 'locations': [place],
                        'url': f"https://jobs.smartrecruiters.com/{c['token']}/{j['id']}", 'posted': iso(j.get('releasedDate'))})
        offset += 100
        if offset >= d.get('totalFound', 0) or offset >= 1500:
            return out


def find_facet(facets, name='India'):
    """(facet parameter, value id) for the facet value named India, searched through Workday's nested facets."""
    for f in facets or []:
        for v in f.get('values') or []:
            if str(v.get('descriptor', '')).strip().lower() == name.lower() and v.get('id'):
                return f.get('facetParameter'), v['id']
            if v.get('values'):
                hit = find_facet([{'facetParameter': v.get('facetParameter') or f.get('facetParameter'), 'values': v['values']}], name)
                if hit:
                    return hit
    return None


def workday(c, terms):
    host, site = c['host'], c['site']
    api = f"https://{host}/wday/cxs/{host.split('.')[0]}/{site}/jobs"
    first = get(api, {'appliedFacets': {}, 'limit': 1, 'offset': 0, 'searchText': ''})
    facet = find_facet(first.get('facets'))
    applied = {facet[0]: [facet[1]]} if facet else {}
    out, seen = [], set()
    for term in terms:
        for offset in (0, 20):
            d = get(api, {'appliedFacets': applied, 'limit': 20, 'offset': offset, 'searchText': term})
            for j in d.get('jobPostings', []):
                path = j.get('externalPath') or ''
                if not path or path in seen:
                    continue
                seen.add(path)
                loc = j.get('locationsText') or ''
                if facet and not INDIA.search(loc):
                    loc = f'{loc} (India)'  # "2 Locations": the India filter already holds
                out.append({'role': j.get('title', ''), 'locations': [loc], 'url': f'https://{host}/en-US/{site}{path}',
                            'posted': posted_on(j.get('postedOn'))})
            if offset + 20 >= d.get('total', 0):
                break
    return out


def posted_on(text):
    """Workday says 'Posted Today', 'Posted 3 Days Ago' or 'Posted 30+ Days Ago'."""
    t = str(text or '').lower()
    if 'today' in t:
        return dt.date.today().isoformat()
    if 'yesterday' in t:
        return (dt.date.today() - dt.timedelta(days=1)).isoformat()
    m = re.search(r'(\d+)\+? days', t)
    return (dt.date.today() - dt.timedelta(days=int(m.group(1)))).isoformat() if m else ''


def amazon(c, terms):
    out, seen = [], set()
    for term in terms:
        q = urllib.parse.urlencode({'base_query': term, 'normalized_country_code[]': 'IND', 'result_limit': 100, 'sort': 'recent'})
        for j in get(f'https://www.amazon.jobs/en/search.json?{q}').get('jobs', []):
            if j['id_icims'] in seen:
                continue
            seen.add(j['id_icims'])
            out.append({'role': j['title'], 'locations': [j.get('normalized_location') or j.get('location', '')],
                        'url': f"https://www.amazon.jobs{j['job_path']}", 'posted': iso_amazon(j.get('posted_date'))})
    return out


def iso_amazon(text):
    try:
        return dt.datetime.strptime(str(text).strip(), '%B %d, %Y').date().isoformat()
    except ValueError:
        return ''


READERS = {'greenhouse': greenhouse, 'lever': lever, 'ashby': ashby, 'smartrecruiters': smartrecruiters,
           'workday': workday, 'amazon': amazon}


# ---- filters ----

def place_match(locations, prefs):
    """The first preferred place a posting is in, or None. 'Remote' needs a remote posting in India."""
    text = ' ; '.join(l for l in locations if l).lower()
    for p in prefs:
        key = p.strip().lower()
        if key == 'remote':
            if re.search(r'\bremote\b|work from home|wfh', text) and (INDIA.search(text) or re.search(r'\(\s*\)', text)):
                return 'Remote'
            continue
        if any(re.search(rf'\b{re.escape(a)}\b', text) for a in CITY_ALIASES.get(key, [key])):
            return p
    return None


def word_hit(title, words):
    t = title.lower()
    return next((w for w in words if re.search(rf'(?<![a-z0-9]){re.escape(w)}(?![a-z0-9])', t)), None)


def level_of(title):
    title = title.replace('_', ' ')  # Bosch writes 'EMT3_VM_Gen_AI_ML_Senior_Developer'
    if INTERN.search(title):
        return 'intern'
    if SENIOR.search(title) or LEVEL_UP.search(title):
        return 'senior'
    if CAMPUS_YEAR.search(title):
        return 'intern'
    if ENTRY.search(title):
        return 'entry'
    return 'unspecified'


def priority(listing):
    """The queue tag for jobs.txt. Batches take the queue by its 'fame' tag (1 first), so for India it carries the
    user's priority instead: 1 primary-role internship or entry role, 2 other primary-role job, 3 other target role
    at a well-known company, 4 the rest."""
    if listing['primary']:
        return 1 if listing['level'] in ('intern', 'entry') else 2
    return 3 if listing['fame'] <= 2 else 4


def as_list(value):
    if isinstance(value, str):
        return [v.strip() for v in value.split(',') if v.strip()]
    return [str(v).strip() for v in value or [] if str(v).strip()]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--folder', default='.')
    ap.add_argument('--role', action='append', default=[], help='target role family, first is primary: ' + ', '.join(ROLE_WORDS))
    ap.add_argument('--location', action='append', default=[])
    ap.add_argument('--keyword', action='append', default=[], help='title words to match instead of the role families')
    ap.add_argument('--exclude-keyword', action='append', default=[])
    ap.add_argument('--level', choices=['early', 'intern', 'any'],
                    help='early: interns, entry level and titles without a level; intern: interns only; any: all levels')
    ap.add_argument('--primary-only', action='store_true', help='keep matches for the first target role only')
    ap.add_argument('--company', action='append', default=[], help='search only these companies (names from the config)')
    ap.add_argument('--days', type=int)
    ap.add_argument('--limit', type=int, default=40)
    ap.add_argument('--append', action='store_true')
    a = ap.parse_args()

    folder = os.path.abspath(a.folder)
    profile = fi.load_profile(folder)
    defaults_used = []
    roles = [role_family(r) for r in (a.role or as_list(profile.get('targetRoles')))]
    if not roles:
        roles, _ = list(DEFAULT_ROLES), defaults_used.append('targetRoles')
    unknown = [r for r in roles if r not in ROLE_WORDS]
    if unknown and not a.keyword:
        fi.out({'ok': False, 'error': f'unknown role family: {", ".join(unknown)}. Use --keyword for other titles.',
                'role_families': list(ROLE_WORDS)}, 1)
    prefs = a.location or as_list(profile.get('preferredLocations'))
    if not prefs:
        prefs, _ = list(DEFAULT_LOCATIONS), defaults_used.append('preferredLocations')
    level_pref = a.level or str(profile.get('jobLevel') or '').strip().lower()
    if level_pref not in ('early', 'intern', 'any'):
        level_pref, _ = 'early', defaults_used.append('jobLevel')
    a.level = level_pref
    config = json.load(open(CONFIG, encoding='utf-8'))
    companies = config['companies']
    if a.company:
        wanted = {fi.norm(c) for c in a.company}
        companies = [c for c in companies if fi.norm(c['company']) in wanted]
        if not companies:
            fi.out({'ok': False, 'error': 'no company by that name in india-companies.json',
                    'companies': [c['company'] for c in config['companies']]}, 1)

    # (family, words) in the user's order; the first family is primary
    if a.keyword:
        families = [('keyword', [k.lower() for k in a.keyword])]
    else:
        families = [(r, ROLE_WORDS[r]) for r in roles]
        if a.primary_only:
            families = families[:1]
    primary = families[0][0]
    # Workday and Amazon search by text: one query per target role, plus "intern"
    search_terms = (a.keyword[:4] if a.keyword else [r for r, _ in families][:3] + ['intern'])

    def run(c):
        try:
            return c, READERS[c['ats']](c, search_terms), None
        except Down as e:
            return c, [], str(e)
        except Exception as e:  # a board changed its format: report it, keep the rest
            return c, [], f'unreadable answer ({type(e).__name__}: {str(e)[:80]})'

    with cf.ThreadPoolExecutor(8) as ex:
        fetched = list(ex.map(run, companies))

    tracked = fi.tracker_index(folder)
    jobs_path = os.path.join(folder, 'jobs.txt')
    queued, lines = fi.jobs_keys(jobs_path)
    cutoff = (dt.date.today() - dt.timedelta(days=a.days)).isoformat() if a.days else None
    ex_words = [k.lower() for k in a.exclude_keyword + as_list(profile.get('excludeKeywords'))] + DEFAULT_EXCLUDE
    skipped = {'location': 0, 'keyword': 0, 'level': 0, 'too_old': 0, 'already_tracked': 0, 'already_in_jobs_txt': 0, 'duplicate': 0}
    failed, results, seen = [], [], set()
    for c, jobs, err in fetched:
        if err:
            failed.append({'company': c['company'], 'board': c.get('host') or c['ats'], 'error': err})
        for j in jobs:
            place = place_match(j['locations'], prefs)
            if not place:
                skipped['location'] += 1; continue
            title = j['role'] or ''
            match, word = next(((f, w) for f, words in families for w in [word_hit(title, words)] if w), (None, None))
            focus = role_family(c.get('focus') or '')
            if not match and focus in dict(families) and not a.keyword and (
                    INTERN.search(title) or word_hit(title, ['software', 'research', 'engineering roles'])):
                match, word = focus, f'{focus} company'  # at a company built on that role, its intern and software roles count
            elif match and match != primary and focus == primary:
                match = primary  # an ML title at a computer-vision company is vision work
            if not match or word_hit(title, ex_words):
                skipped['keyword'] += 1; continue
            level = level_of(title)
            if level == 'senior' and a.level != 'any' or (a.level == 'intern' and level != 'intern'):
                skipped['level'] += 1; continue
            if cutoff and j['posted'] and j['posted'] < cutoff:
                skipped['too_old'] += 1; continue
            keys = fi.posting_keys(j['url'], c['company'])
            if (keys | {fi.name_key(c['company'], title)}) & tracked.keys():
                skipped['already_tracked'] += 1; continue
            if keys & queued:
                skipped['already_in_jobs_txt'] += 1; continue
            dup = (fi.norm(c['company']), fi.norm(title), place)
            if dup in seen:
                skipped['duplicate'] += 1; continue
            seen.add(dup)
            results.append({'company': c['company'], 'role': title, 'locations': [l for l in j['locations'] if l][:3],
                            'place': place, 'posted': j['posted'], 'level': level, 'match': match,
                            'primary': match == primary, 'matched_word': word, 'fame': c.get('fame', 4),
                            'url': j['url'], 'board': c['ats']})

    # Primary-role matches first, then the other roles in the user's order; interns first; best-known; newest
    level_rank = {'intern': 0, 'entry': 1, 'unspecified': 2, 'senior': 3}
    role_rank = {f: i for i, (f, _) in enumerate(families)}
    results.sort(key=lambda r: r['posted'] or '', reverse=True)
    results.sort(key=lambda r: (role_rank[r['match']], level_rank[r['level']], r['fame']))
    total = len(results)
    listings = results[:a.limit]

    added, order = 0, {}
    if a.append and listings:
        new_lines = [f"{l['url']}  # {l['company']} | {l['role']} | {', '.join(l['locations'])} | posted {l['posted'] or 'unknown'}"
                     f" | fame {priority(l)}" for l in listings]
        done_at = next((i for i, l in enumerate(lines) if l.strip().lower() == '# done'), len(lines))
        pending, rest = lines[:done_at], lines[done_at:]
        while pending and not pending[-1].strip():
            pending.pop()
        merged = fi.sort_queue(pending + new_lines + ([''] if rest else []) + rest, fi.recent_counts(tracked))
        fi.write_lines(jobs_path, merged)
        added, order = len(new_lines), fi.sort_summary(merged)

    fi.out({'ok': True, 'companies_searched': len(companies) - len(failed), 'sources_failed': failed,
            'filters': {'roles': [f for f, _ in families], 'locations': prefs, 'level': a.level,
                        'keywords': a.keyword or None, 'exclude_keywords': as_list(profile.get('excludeKeywords')) + a.exclude_keyword,
                        'days': a.days},
            'defaults_used': defaults_used,
            'matches': total, 'matches_by_role': {f: sum(r['match'] == f for r in results) for f, _ in families},
            'shown': len(listings),
            'added_to_jobs_txt': added, **order, 'skipped': skipped, 'listings': listings,
            'search_by_hand': config.get('browser_only', [])})


if __name__ == '__main__':
    main()
