"""
SASTRA SoME End Semester Examination Duty Portal
=================================================
Files required in the same folder as app.py:
  1. Faculty_Master.xlsx  — columns: S.No. | ID No. | NAME OF STAFF | Designation
                            (+ optional valuation date cols V1..V5)
  2. Offline_Duty.xlsx    — offline exam slots  (col A: Date | col B: FN/AN | col C: count)
  3. sastra_logo.png      — university logo (optional)
  4. faculty_passwords.json — auto-created on first run; keyed by Faculty ID No.

Login:
  Faculty portal : enter your Faculty ID (e.g. C870, RS602) + password
  Default password on first login: "sastra" (forced change on first use)
  Admin panel    : any faculty marked is_admin=true in faculty_passwords.json

v5 — ID-based login | bcrypt passwords | resubmission | accommodation stats
     Core optimizer: scipy HiGHS MILP | Smart Greedy | OR-Tools CP-SAT
     NOTE: Online duty suspended this semester — all duties are Offline only.
"""

import os
import io
import json
import secrets
import datetime
import warnings
import logging
import calendar as calmod
import urllib.parse
from collections import defaultdict

import numpy as np
import pandas as pd
import streamlit as st
import altair as alt
from supabase import create_client, Client

logging.getLogger("streamlit").setLevel(logging.ERROR)

try:
    import bcrypt
    BCRYPT_OK = True
except ImportError:
    BCRYPT_OK = False

try:
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import csc_matrix
    SCIPY_OK = True
except ImportError:
    SCIPY_OK = False

try:
    import ctypes
    ctypes.windll.kernel32.SetErrorMode(0x8007)
except Exception:
    pass

try:
    from ortools.sat.python import cp_model
    _test = cp_model.CpModel()
    del _test
    ORTOOLS_OK = True
except Exception:
    ORTOOLS_OK = False

warnings.filterwarnings("ignore")

# ─── File names ──────────────────────────────────────────────── #
FACULTY_FILE      = "Faculty_Master.xlsx"
OFFLINE_FILE      = "Offline_Duty.xlsx"
ONLINE_FILE       = "Online_Duty.xlsx"
WILLINGNESS_FILE  = "Willingness.xlsx"
LOGO_FILE         = "sastra_logo.png"
FINAL_ALLOC_FILE  = "Final_Allocation.xlsx"
ALLOC_REPORT_FILE = "Allocation_Report.xlsx"
GATE_FILE         = "allotment_gate.txt"
PASSWORDS_FILE    = "faculty_passwords.json"

DEFAULT_PASSWORD  = "sastra"   # every new faculty's first-time password
ADMIN_IDS        = {"C2086"}  # Faculty IDs that are always admin

# ─── Designation rules ───────────────────────────────────────── #
# Map raw Excel designation strings → internal codes
DESIG_MAP = {
    # Professor
    "professor":                    "P",
    "prof":                         "P",
    "prof.":                        "P",
    "p":                            "P",
    # Associate Professor
    "acp":                          "ACP",
    "associate professor":          "ACP",
    "assoc. professor":             "ACP",
    "assoc professor":              "ACP",
    # Senior Assistant Professor
    "sap":                          "SAP",
    "senior assistant professor":   "SAP",
    "sr. assistant professor":      "SAP",
    "sr assistant professor":       "SAP",
    # Assistant Professor Grade III / AP3
    "ap 3":                         "AP3",
    "ap3":                          "AP3",
    "ap-3":                         "AP3",
    "ap iii":                       "AP3",
    "assistant professor 3":        "AP3",
    "assistant professor iii":      "AP3",
    "assistant professor grade 3":  "AP3",
    "assistant professor grade iii":"AP3",
    "assistant professor - iii":    "AP3",
    "assistant professor - 3":      "AP3",
    "asst. professor 3":            "AP3",
    "asst professor 3":             "AP3",
    # Assistant Professor Grade II / AP2
    "ap 2":                         "AP2",
    "ap2":                          "AP2",
    "ap-2":                         "AP2",
    "ap ii":                        "AP2",
    "assistant professor 2":        "AP2",
    "assistant professor ii":       "AP2",
    "assistant professor grade 2":  "AP2",
    "assistant professor grade ii": "AP2",
    "assistant professor - ii":     "AP2",
    "assistant professor - 2":      "AP2",
    "asst. professor 2":            "AP2",
    "asst professor 2":             "AP2",
    # Teaching Assistant
    "teaching assistant":           "TA",
    "ta":                           "TA",
    # Research Assistant
    "research assistant":           "RA",
    "ra":                           "RA",
}

def _map_desig(raw: str) -> str:
    """Map a raw designation string to a DESIG_MAP code.
    Falls back to substring/keyword matching before defaulting to TA."""
    s = str(raw).strip().lower()
    # Exact match first
    if s in DESIG_MAP:
        return DESIG_MAP[s]
    # Already a known code (e.g. stored as "P", "ACP" etc.)
    up = s.upper()
    if up in ("P", "ACP", "SAP", "AP3", "AP2", "TA", "RA"):
        return up
    # Keyword fallback
    if "research assistant" in s or s == "ra":
        return "RA"
    if "teaching assistant" in s or s == "ta":
        return "TA"
    if "senior assistant" in s or "sr" in s.split():
        return "SAP"
    if "associate" in s:
        return "ACP"
    if "professor" in s or "prof" in s:
        # Try to detect grade/level
        for token in s.replace("-", " ").split():
            if token in ("3", "iii", "grade3", "gradeiii"):
                return "AP3"
            if token in ("2", "ii", "grade2", "gradeii"):
                return "AP2"
        return "P"   # Plain "professor" → P
    # Last resort
    return "TA"
# Option B: Online duty suspended — all designations use Offline only
DESIG_RULES = {
    "P":   (1, 1, ["Offline"]),   # Online duty suspended this semester
    "ACP": (2, 2, ["Offline"]),   # Both duties now offline
    "SAP": (2, 2, ["Offline"]),
    "AP3": (3, 3, ["Offline"]),
    "AP2": (3, 3, ["Offline"]),
    "TA":  (4, 4, ["Offline"]),   # 4 duties this semester (overridden per-faculty below)
    "RA":  (4, 4, ["Offline"]),
}
DESIG_FULL = {
    "P":   "Professor",
    "ACP": "Associate Professor",
    "SAP": "Senior Assistant Professor",
    "AP3": "Assistant Professor - III",
    "AP2": "Assistant Professor - II",
    "TA":  "Teaching Assistant",
    "RA":  "Research Assistant",
}

# ── Per-faculty designation overrides ───────────────────────────────────────
# Use when the Supabase designation field is NULL/blank/incorrect for a faculty.
# Key = exact faculty name (as stored in Supabase), Value = designation code
FACULTY_DESIG_OVERRIDE_RAW: dict = {
    "Dr. Anjan Kumar Dash": "P",
    # Add more overrides here as needed, e.g.:
    # "Dr. Some Name": "ACP",
}
DUTY_STRUCTURE = {"P": 3, "ACP": 6, "SAP": 6, "AP3": 9, "AP2": 9, "TA": 11, "RA": 11}

# ── Willingness match scores ──────────────────────────────────── #
W_EXACT      = 100_000
W_ACP_ONLINE =  80_000
W_FLIP       =  60_000
W_ADJ1       =  40_000
W_ADJ2       =  20_000
W_VAL_ADJ    =   5_000
W_NON_SUB    =     100
PENALTY      =      10

DESIG_PRIORITY = {
    "P":   6_000_000,
    "ACP": 5_000_000,
    "SAP": 4_000_000,
    "AP3": 3_000_000,
    "AP2": 2_000_000,
    "TA":        0,
    "RA":        0,
}

WILL_TAGS = {
    "Willingness-Exact", "Willingness-ACPOnline",
    "Willingness-SessionFlip", "Willingness-±1Day",
    "Willingness-±2Day", "Willingness-ValAdj",
    "SAP-OnlineFallback"
}

# ─── Page config ─────────────────────────────────────────────── #
st.set_page_config(page_title="SASTRA Duty Portal", layout="wide")
st.markdown("""
<style>
.stApp{background:#f4f7fb}
.main .block-container{max-width:1200px;padding-top:1.2rem;padding-bottom:1.5rem}
.card{background:linear-gradient(180deg,#fff 0%,#f8fafc 100%);border:1px solid #dbe3ef;
      border-radius:14px;padding:16px 18px;box-shadow:0 10px 24px rgba(15,23,42,.08);margin-bottom:12px}
.panel{background:#fff;border:1px solid #e2e8f0;border-radius:14px;
       padding:14px 16px;box-shadow:0 8px 20px rgba(15,23,42,.06);margin-bottom:10px}
.card-title{font-size:1.08rem;font-weight:700;color:#0f172a;margin-bottom:.2rem}
.card-sub{font-size:.93rem;color:#334155;margin-bottom:0}
.sec-title{font-size:1rem;font-weight:700;color:#0b3a67;margin-bottom:.35rem}
.stButton>button{border-radius:10px;border:1px solid #cbd5e1;font-weight:600}
.stDownloadButton>button{border-radius:10px;font-weight:600}
.blink{font-weight:700;color:#800000;padding:10px 12px;border:2px solid #800000;
       background:#fffaf5;border-radius:6px;animation:pulse 2.4s ease-in-out infinite}
@keyframes pulse{0%{opacity:1}50%{opacity:.35}100%{opacity:1}}
</style>
""", unsafe_allow_html=True)


# ═══════════════════════════════════════════════════════════════ #
#               SUPABASE CLIENT                                  #
# ═══════════════════════════════════════════════════════════════ #
@st.cache_resource
def _sb() -> Client:
    return create_client(st.secrets["SUPABASE_URL"], st.secrets["SUPABASE_KEY"])

# ── DB helpers ────────────────────────────────────────────────── #
def db_get_faculty_by_id(fid: str):
    r = _sb().table("faculty").select("*").eq("faculty_id", _norm_id(fid)).execute()
    return r.data[0] if r.data else None

def db_get_faculty_by_email(email: str):
    r = _sb().table("faculty").select("*").eq("email", email.strip().lower()).execute()
    return r.data[0] if r.data else None

def db_get_all_faculty():
    r = _sb().table("faculty").select("*").order("name").execute()
    return r.data or []

def db_update_password(fid: str, h: str, must_change: bool = False):
    _sb().table("faculty").update({"password_hash": h, "must_change_pw": must_change}).eq("faculty_id", fid).execute()

def db_reset_faculty_pw(fid: str):
    h = hash_password(DEFAULT_PASSWORD)
    _sb().table("faculty").update({"password_hash": h, "must_change_pw": True}).eq("faculty_id", _norm_id(fid)).execute()

def db_set_admin(fid: str, val: bool):
    _sb().table("faculty").update({"is_admin": val}).eq("faculty_id", _norm_id(fid)).execute()

def db_create_reset_token(fid: str) -> str:
    import secrets as _sec
    token = _sec.token_urlsafe(32)
    exp   = (datetime.datetime.utcnow() + datetime.timedelta(hours=24)).isoformat()
    _sb().table("password_reset_tokens").insert({"faculty_id": fid, "token": token, "expires_at": exp}).execute()
    return token

def db_validate_reset_token(token: str):
    r = _sb().table("password_reset_tokens").select("*").eq("token", token).eq("used", False).execute()
    if not r.data: return None
    row = r.data[0]
    exp = row["expires_at"].replace("Z","").split(".")[0]
    if datetime.datetime.utcnow() > datetime.datetime.fromisoformat(exp): return None
    return row

def db_consume_reset_token(token: str):
    _sb().table("password_reset_tokens").update({"used": True}).eq("token", token).execute()

def db_get_offline_slots():
    r = _sb().table("offline_duty").select("*").execute()
    return r.data or []

def db_get_online_slots():
    return []          # No online duty this semester

def db_get_all_willingness_rows():
    r = _sb().table("willingness").select("*").order("faculty_name").execute()
    return r.data or []

def db_get_willingness_for(fid: str):
    r = _sb().table("willingness").select("*").eq("faculty_id", fid).execute()
    return r.data or []

def db_already_submitted(fid: str) -> bool:
    r = _sb().table("willingness").select("id").eq("faculty_id", fid).execute()
    return bool(r.data)

def db_submit_willingness(fid: str, faculty_name: str, slots: list):
    _sb().table("willingness").delete().eq("faculty_id", fid).execute()
    def _to_iso(d):
        # slots["Date"] is a python date object from selectbox
        if hasattr(d, "strftime"):
            return d.strftime("%Y-%m-%d")
        # fallback: parse string in any format → ISO
        return pd.to_datetime(str(d), dayfirst=True).strftime("%Y-%m-%d")
    rows = [{"faculty_id": fid, "faculty_name": faculty_name,
             "duty_date": _to_iso(s["Date"]), "session": s["Session"]} for s in slots]
    if rows: _sb().table("willingness").insert(rows).execute()

def db_clear_all_willingness():
    _sb().table("willingness").delete().neq("id", 0).execute()

def db_save_allocation(records: list):
    _sb().table("final_allocation").delete().neq("id", 0).execute()
    if records: _sb().table("final_allocation").insert(records).execute()

def db_get_allocation_for(fid: str):
    r = _sb().table("final_allocation").select("*").eq("faculty_id", fid).order("duty_date").execute()
    return r.data or []

def db_get_all_allocation():
    r = _sb().table("final_allocation").select("*").order("duty_date").execute()
    return r.data or []

def db_get_setting(key: str, default: str = "") -> str:
    # Try session state cache first (avoids a DB round-trip and works even if table missing)
    _ss_key = f"_setting_{key}"
    if _ss_key in st.session_state:
        return st.session_state[_ss_key]
    try:
        r = _sb().table("portal_settings").select("value").eq("key", key).execute()
        val = r.data[0]["value"] if r.data else default
        st.session_state[_ss_key] = val
        return val
    except Exception:
        return default

def db_set_setting(key: str, value: str):
    # Always update session-state cache so the UI reflects the change immediately
    st.session_state[f"_setting_{key}"] = value
    try:
        # Try upsert with explicit conflict column first (requires 'key' to be PK/unique)
        _sb().table("portal_settings").upsert(
            {"key": key, "value": value},
            on_conflict="key"
        ).execute()
    except Exception:
        try:
            # Fallback: delete then insert
            _sb().table("portal_settings").delete().eq("key", key).execute()
            _sb().table("portal_settings").insert({"key": key, "value": value}).execute()
        except Exception:
            # Table may not exist — setting is preserved in session state only
            pass


# ═══════════════════════════════════════════════════════════════ #
#                   ALLOTMENT GATE                               #
# ═══════════════════════════════════════════════════════════════ #
def gate_is_open() -> bool:
    return db_get_setting("allotment_gate", "0") == "1"

def set_gate(open_: bool):
    db_set_setting("allotment_gate", "1" if open_ else "0")


# ═══════════════════════════════════════════════════════════════ #
#              PASSWORD HELPERS (bcrypt)                         #
# ═══════════════════════════════════════════════════════════════ #
def hash_password(plain: str) -> str:
    if BCRYPT_OK:
        return bcrypt.hashpw(plain.encode(), bcrypt.gensalt()).decode()
    # Fallback: SHA-256 prefixed (insecure, encourages installing bcrypt)
    import hashlib
    return "sha256:" + hashlib.sha256(plain.encode()).hexdigest()

def verify_password(plain: str, hashed: str) -> bool:
    if not hashed:
        return False
    try:
        if hashed.startswith("sha256:"):
            import hashlib
            return hashed == "sha256:" + hashlib.sha256(plain.encode()).hexdigest()
        if BCRYPT_OK:
            return bcrypt.checkpw(plain.encode(), hashed.encode())
    except Exception:
        pass
    return False


# ═══════════════════════════════════════════════════════════════ #
#           PASSWORD HELPERS (Supabase-backed)                   #
# ═══════════════════════════════════════════════════════════════ #
def _norm_id(fid: str) -> str:
    return str(fid).strip().upper().replace(" ", "")

def pw_get(fid: str) -> dict | None:
    """Return faculty row from Supabase as password-compatible dict."""
    row = db_get_faculty_by_id(fid)
    if not row: return None
    return {"password_hash": row["password_hash"],
            "must_change_pw": row.get("must_change_pw", True),
            "is_admin": row.get("is_admin", False)}

def pw_ensure(fid: str):
    """No-op: faculty are pre-loaded via load_to_supabase.py."""
    pass

def pw_update(fid: str, new_hash: str, must_change: bool = False):
    db_update_password(_norm_id(fid), new_hash, must_change)

def pw_reset(fid: str):
    db_reset_faculty_pw(_norm_id(fid))

def pw_set_admin(fid: str, is_admin: bool):
    db_set_admin(_norm_id(fid), is_admin)

def pw_ensure_all(id_list: list):
    """No-op: faculty are pre-loaded via load_to_supabase.py."""
    pass


# ═══════════════════════════════════════════════════════════════ #
#                     UTILITY FUNCTIONS                          #
# ═══════════════════════════════════════════════════════════════ #
def clean(x):
    return str(x).strip().lower()

# Build clean-keyed lookup after clean() is available
FACULTY_DESIG_OVERRIDE = {clean(k): v for k, v in FACULTY_DESIG_OVERRIDE_RAW.items()}

# ── TA/RA duty-count group (4 or 5 duties, may select Saturday dates) ── #
_SAT_PREASSIGN_RAW = [
    "Shri Sangeethkumar Gopaldas", "Shri S. Antony", "Shri S. Balamurli",
    "Shri R. Rajesh", "Shri. P. Vijay Guru", "Shri E. Ezekiel",
    "Shri S. Balaganesh", "Shri S. Varadharajan", "Ms S. Kiruba Kari",
    "Shri V. Adhavan", "Ms. P. Abirami", "Shri V. Ramesh Srenyvasan",
    "Shri P. Panneerselvam", "Shri S. Sabrish", "Shri S. Manikandan",
    "Shri P. Sarathkumar", "Shri C. Frizil Kinsly", "Shri Sudhakar S",
    "Shri N. Arun Kumar",
]
SAT_PREASSIGN_CLEAN = {clean(n) for n in _SAT_PREASSIGN_RAW}

# Faculty receiving 5 duties; all others in the list get 4 duties
_FIVE_DUTY_RAW = [
    "Shri C. Frizil Kinsly", "Shri P. Sarathkumar", "Shri S. Manikandan",
    "Shri S. Sabrish", "Shri P. Panneerselvam",
]
FIVE_DUTY_CLEAN = {clean(n) for n in _FIVE_DUTY_RAW}

# Per-faculty exam dates (raw, for display highlights in calendar & UI)
FACULTY_EXAM_DATES_CLEAN: dict = {
    clean("Shri. P. Vijay Guru"):       {datetime.date(2026, 5, 20)},
    clean("Shri E. Ezekiel"):           {datetime.date(2026, 5, 11)},
    clean("Shri S. Varadharajan"):      {datetime.date(2026, 5, 22)},
    clean("Ms S. Kiruba Kari"):         {datetime.date(2026, 5, 11),
                                         datetime.date(2026, 5, 31)},
    clean("Shri V. Adhavan"):           {datetime.date(2026, 5, 11),
                                         datetime.date(2026, 5, 31)},
    clean("Shri V. Ramesh Srenyvasan"): {datetime.date(2026, 5, 11),
                                         datetime.date(2026, 5, 31)},
    clean("Shri S. Sabrish"):           {datetime.date(2026, 5, 22)},
    clean("Shri P. Sarathkumar"):       {datetime.date(2026, 5, 18)},
    clean("Shri N. Arun Kumar"):        {datetime.date(2026, 5, 26)},
}

def _prev_working_day(d: datetime.date, steps: int) -> datetime.date:
    """Return the date `steps` working days before d (skips Sundays only, Sat allowed for duty)."""
    cur = d
    for _ in range(steps):
        cur -= datetime.timedelta(days=1)
        while cur.weekday() == 6:   # skip Sundays only
            cur -= datetime.timedelta(days=1)
    return cur

def _expand_exam_blackout(exam_dates: set, buffer: int = 2) -> set:
    """Return exam_dates expanded with n-1 and n-2 working days before each exam date."""
    expanded = set(exam_dates)
    for d in exam_dates:
        for step in range(1, buffer + 1):
            expanded.add(_prev_working_day(d, step))
    return expanded

# Per-faculty ALLOTMENT blackout = exam dates + n-1, n-2 working days before each exam date.
# These dates are fully blocked from the willingness selector AND the optimizer.
FACULTY_BLACKOUT_CLEAN: dict = {
    fc: _expand_exam_blackout(dates)
    for fc, dates in FACULTY_EXAM_DATES_CLEAN.items()
}


def fac_duty_range(fn: str, desig: str) -> tuple:
    """Return (min_duties, max_duties) for a faculty member.
    Overrides DESIG_RULES for the Saturday TA/RA group."""
    fc = clean(fn)
    if fc in FIVE_DUTY_CLEAN:
        return 5, 5
    if fc in SAT_PREASSIGN_CLEAN:
        return 4, 4
    dr = DESIG_RULES.get(desig, DESIG_RULES["TA"])
    return dr[0], dr[1]


def normalize_session(v):
    t = str(v).strip().upper()
    if t in {"FN", "FORENOON", "MORNING", "AM"}:
        return "FN"
    if t in {"AN", "AFTERNOON", "EVENING", "PM"}:
        return "AN"
    return t

def parse_date_safe(val):
    """Robust multi-format date parser."""
    if val is None:
        return pd.NaT
    if isinstance(val, pd.Timestamp):
        return val
    if isinstance(val, (datetime.datetime, datetime.date)):
        return pd.Timestamp(val)
    s = str(val).strip()
    for fmt in ("%Y-%m-%d", "%d-%m-%Y", "%d/%m/%Y", "%d-%m-%y"):
        try:
            return pd.to_datetime(s, format=fmt)
        except Exception:
            pass
    return pd.to_datetime(s, dayfirst=True, errors="coerce")

def fmt_day(val):
    dt = pd.to_datetime(val, dayfirst=True, errors="coerce")
    return f"{dt.strftime('%d-%m-%Y')} ({dt.strftime('%A')})" if pd.notna(dt) else str(val)

def demand_category(req: int) -> str:
    if req < 3:  return "Low (<3)"
    if req <= 7: return "Medium (3-7)"
    return "High (>7)"

def valuation_dates_for(row):
    return sorted({
        pd.to_datetime(row[c], dayfirst=True).date()
        for c in ["V1", "V2", "V3", "V4", "V5"]
        if c in row.index and pd.notna(row[c])
    })

def qp_dates_for(row):
    return sorted({
        pd.to_datetime(row[c], dayfirst=True, errors="coerce").strftime("%d-%m-%Y")
        for c in row.index
        if "QP" in str(c).upper()
        and "DATE" in str(c).upper()
        and pd.notna(row[c])
        and pd.notna(pd.to_datetime(row[c], dayfirst=True, errors="coerce"))
    })

def fac_mask(df, sel_clean):
    if df.empty:
        return pd.Series([], dtype=bool)
    cols = [c for c in df.columns if "name" in c.lower() or "faculty" in c.lower()]
    mask = pd.Series([False] * len(df), index=df.index)
    for c in cols:
        mask = mask | (df[c].astype(str).apply(clean) == sel_clean)
    return mask

def wa_link(phone, msg):
    p = str(phone).strip().replace("+", "").replace(" ", "").replace("-", "")
    return f"https://wa.me/{p}?text={urllib.parse.quote(msg)}"

def build_msg(name, will, val, inv, qp, match_str="", dev_lines=None):
    lines = [
        f"Dear {name},", "",
        "Examination Duty Details:", "",
        "1) Invigilation Dates (Final Allotment):",
        *(inv or ["Not allotted yet"]), "",
        "2) Valuation Dates (Full Day):",
        *(val or ["Not available"]), "",
        "3) QP Feedback Dates:",
        *(qp or ["Not available"]), "",
    ]
    if match_str:
        lines += [
            "4) Willingness Match Summary:",
            f"   {match_str}",
            *(dev_lines or []), "",
        ]
    lines.append("- SASTRA SoME Examination Committee")
    return "\n".join(lines)

def detect_semester(slot_dates=None):
    override = st.session_state.get("semester_override", "Auto-detect")
    if override and override != "Auto-detect":
        return override
    now = datetime.date.today()
    if slot_dates:
        months = {d.month for d in slot_dates}
        if months & {5, 6}:
            return "Even Semester (May/Jun 2026 End-Semester)"
        if months & {11, 12, 1}:
            return "Odd Semester (Nov/Dec End-Semester)"
    if now.month in (5, 6):
        return "Even Semester (May/Jun 2026 End-Semester)"
    if now.month in (11, 12, 1):
        return "Odd Semester (Nov/Dec End-Semester)"
    return "End-Semester Examination"

def get_exam_period(slot_dates):
    if not slot_dates:
        return None, None
    sd = sorted(slot_dates)
    return sd[0], sd[-1]

def render_header(logo=True):
    if logo and os.path.exists(LOGO_FILE):
        _, c2, _ = st.columns([2, 1, 2])
        with c2:
            st.image(LOGO_FILE, width=180)
    st.markdown(
        "<h2 style='text-align:center;margin-bottom:.25rem'>"
        "SASTRA SoME End Semester Examination Duty Portal</h2>",
        unsafe_allow_html=True)
    st.markdown(
        "<h4 style='text-align:center;margin-top:0'>"
        "School of Mechanical Engineering</h4>",
        unsafe_allow_html=True)
    st.markdown("---")


# ═══════════════════════════════════════════════════════════════ #
#               PARSE DUTY FILE                                  #
# ═══════════════════════════════════════════════════════════════ #
def parse_duty_file(filepath, duty_type):
    if not os.path.exists(filepath):
        return []
    try:
        raw = pd.read_excel(filepath, header=None)
    except Exception:
        return []
    try:
        pd.to_datetime(raw.iloc[0, 0])
        start = 0
    except Exception:
        start = 1
    slots = []
    for i in range(start, len(raw)):
        row = raw.iloc[i]
        d    = row.iloc[0]
        sess = row.iloc[1] if len(row) > 1 else None
        req  = row.iloc[2] if len(row) > 2 else 1
        if pd.isna(d):
            continue
        sn = normalize_session(sess)
        if sn not in ("FN", "AN"):
            continue
        try:
            date = pd.to_datetime(d).date()
        except Exception:
            continue
        try:
            required = max(int(float(req)), 0)
        except Exception:
            required = 1
        slots.append({"date": date, "session": sn, "required": required, "type": duty_type})
    return slots

@st.cache_data(ttl=300)
def load_slots(off_path, on_path):
    """Load offline duty slots from Supabase. No online duty this semester."""
    def rows_to_df(rows):
        if not rows:
            df = pd.DataFrame(columns=["Date","Session","Required"])
            df["Date"] = pd.to_datetime(df["Date"]); return df
        df = pd.DataFrame(rows)
        df.rename(columns={"duty_date":"Date","session":"Session","required":"Required"}, inplace=True)
        df["Date"]     = pd.to_datetime(df["Date"], errors="coerce")
        df["Session"]  = df["Session"].apply(normalize_session)
        df["Required"] = pd.to_numeric(df["Required"], errors="coerce").fillna(1).astype(int)
        return df[["Date","Session","Required"]]
    _empty = pd.DataFrame(columns=["Date","Session","Required"])
    _empty["Date"] = pd.to_datetime(_empty["Date"])
    return rows_to_df(db_get_offline_slots()), _empty


# ═══════════════════════════════════════════════════════════════ #
#            WILLINGNESS FUNCTIONS (Supabase-backed)             #
# ═══════════════════════════════════════════════════════════════ #
def load_willingness():
    rows = db_get_all_willingness_rows()
    if not rows:
        return pd.DataFrame(columns=["Faculty","Date","Session","FacultyClean"])
    df = pd.DataFrame(rows)
    df.rename(columns={"faculty_name":"Faculty","duty_date":"Date","session":"Session"}, inplace=True)
    df["Faculty"] = df["Faculty"].astype(str).str.strip()
    # Supabase stores dates as YYYY-MM-DD — convert to dd-mm-yyyy so all
    # existing code that uses dayfirst=True parses them correctly
    def _reformat(v):
        s = str(v).strip()
        try:
            return pd.to_datetime(s, format="%Y-%m-%d").strftime("%d-%m-%Y")
        except Exception:
            return s
    df["Date"]         = df["Date"].apply(_reformat)
    df["Session"]      = df["Session"].astype(str).str.strip().str.upper()
    df["FacultyClean"] = df["Faculty"].apply(clean)
    return df[["Faculty","Date","Session","FacultyClean"]].reset_index(drop=True)

def get_all_willingness():
    return load_willingness()

def save_submission(faculty_name, slots):
    fid = st.session_state.get("_logged_fid", faculty_name)
    db_submit_willingness(fid, faculty_name, slots)

def already_submitted(faculty_name: str) -> bool:
    fid = st.session_state.get("_logged_fid", "")
    if fid:
        return db_already_submitted(fid)
    wl = load_willingness()
    return clean(faculty_name) in wl["FacultyClean"].tolist() if not wl.empty else False


# ═══════════════════════════════════════════════════════════════ #
#        FEATURE 1 — SLOT PROBABILITY INDICATOR                  #
# ═══════════════════════════════════════════════════════════════ #
def slot_probability(all_will_df, duty_df, date_val, session_val):
    seats = 0
    if not duty_df.empty:
        m = duty_df[
            (duty_df["Date"].dt.date == date_val) &
            (duty_df["Session"].str.upper() == session_val.upper())]
        if not m.empty:
            seats = int(m["Required"].sum())

    applicants = 0
    if not all_will_df.empty and "Date" in all_will_df.columns:
        norm = pd.to_datetime(all_will_df["Date"], dayfirst=True, errors="coerce")
        applicants = int((
            (norm.dt.date == date_val) &
            (all_will_df["Session"].str.upper() == session_val.upper())
        ).sum())

    if seats == 0:
        return {"seats": 0, "applicants": applicants,
                "probability": 0.0, "label": "No slot on this day", "colour": "#94a3b8"}
    if applicants == 0:
        return {"seats": seats, "applicants": 0,
                "probability": 100.0, "label": "High — you'd be first!", "colour": "#16a34a"}
    prob = min(seats / applicants, 1.0) * 100
    if prob >= 70:   label, colour = "High",                "#16a34a"
    elif prob >= 40: label, colour = "Medium",              "#f59e0b"
    else:            label, colour = "Low — many applicants","#dc2626"
    return {"seats": seats, "applicants": applicants,
            "probability": prob, "label": label, "colour": colour}

def render_prob_bar(info: dict, session_label: str):
    pct    = info["probability"]
    colour = info["colour"]
    st.markdown(f"""
<div style="background:#fff;border:1px solid #e2e8f0;border-radius:10px;
            padding:10px 14px;margin-bottom:8px;">
  <div style="font-weight:700;font-size:.95rem;color:#0f172a;margin-bottom:4px;">
    {session_label} &nbsp;·&nbsp;
    <span style="color:{colour}">{pct:.0f}% allocation probability</span>
  </div>
  <div style="background:#e5e7eb;border-radius:6px;height:12px;width:100%;margin:4px 0">
    <div style="background:{colour};border-radius:6px;height:12px;width:{pct:.0f}%"></div>
  </div>
  <div style="font-size:.82rem;color:#475569;margin-top:3px;">
    🎯 Seats: <b>{info['seats']}</b> &nbsp;|&nbsp;
    👥 Applied so far: <b>{info['applicants']}</b> &nbsp;|&nbsp;
    {info['label']}
  </div>
</div>""", unsafe_allow_html=True)


# ═══════════════════════════════════════════════════════════════ #
#        DEVIATION ANALYSIS  (admin-only)                        #
# ═══════════════════════════════════════════════════════════════ #
def classify_duty(alloc_by: str, duty_date, duty_sess: str, will_set: set):
    ab = str(alloc_by).strip()
    if ab == "Willingness-Exact":
        return ("Exact Match", "✅",
                "Allotted on your exact submitted date & session", True)
    if ab == "Willingness-ACPOnline":
        return ("Session Adjusted", "🔄",
                "Your offline-date willingness was used to fill your online duty slot", True)
    if ab == "Willingness-SessionFlip":
        opp = "AN" if duty_sess == "FN" else "FN"
        return ("Session Adjusted", "🔄",
                f"You submitted {duty_date.strftime('%d-%m-%Y')} {opp} → allotted {duty_sess} "
                f"(same date, session swapped)", True)
    if ab == "Willingness-±1Day":
        closest = ""
        for direction in [1, -1]:
            adj = duty_date + datetime.timedelta(days=direction)
            for s in ["FN", "AN"]:
                if (adj, s) in will_set:
                    d = "after" if direction > 0 else "before"
                    closest = (f"You submitted {adj.strftime('%d-%m-%Y')} {s} "
                               f"→ duty shifted 1 working day {d} "
                               f"to {duty_date.strftime('%d-%m-%Y')} {duty_sess}")
                    break
            if closest: break
        return ("Date Adjusted (±1 day)", "📅",
                closest or "Allotted 1 working day from your submitted willingness", True)
    if ab == "Willingness-±2Day":
        return ("Date Adjusted (±2 days)", "📆",
                f"Allotted 2 working days from your submitted willingness "
                f"({duty_date.strftime('%d-%m-%Y')} {duty_sess})", True)
    if ab == "SAP-OnlineFallback":
        return ("SAP Online Fallback", "🔁",
                "SAP faculty assigned to online slot as fallback (P/ACP unavailable)", True)
    if ab == "Willingness-ValAdj":
        return ("Valuation-Adjacent", "🗓️",
                f"Allotted on a weekday adjacent to your valuation date "
                f"({duty_date.strftime('%d-%m-%Y')} {duty_sess})", True)
    if ab in ("Auto-Assigned", "Gap-Fill") or ab.startswith("Gap-Fill"):
        return ("Auto-Assigned", "⚙️",
                "No willingness submitted — system assigned this duty to meet slot requirements",
                False)
    return ("Not in Willingness", "🔴",
            f"No willingness found near {duty_date.strftime('%d-%m-%Y')} {duty_sess} "
            f"— system assigned to meet slot requirements", False)

def render_deviation_section(allot_rows: pd.DataFrame, will_set: set):
    if allot_rows.empty:
        st.info("No allotment data found for this faculty yet.")
        return "Not available", []

    duty_rows = []
    for _, ar in allot_rows.iterrows():
        norm = pd.to_datetime(ar["Date"], dayfirst=True, errors="coerce")
        if pd.isna(norm): continue
        sess     = str(ar.get("Session", "")).strip().upper()
        dtype    = str(ar.get("Type", "")).strip()
        alloc_by = str(ar.get("Allocated_By", "")).strip()
        status, emoji, detail, is_matched = classify_duty(
            alloc_by, norm.date(), sess, will_set)
        duty_rows.append({
            "norm_date": norm.date(), "sess": sess, "dtype": dtype,
            "status": status, "emoji": emoji, "detail": detail,
            "is_matched": is_matched,
            "date_fmt": fmt_day(norm.strftime("%d-%m-%Y")),
        })

    total    = len(duty_rows)
    n_exact  = sum(1 for d in duty_rows if d["status"] == "Exact Match")
    n_sess   = sum(1 for d in duty_rows if d["status"] == "Session Adjusted")
    n_adj1   = sum(1 for d in duty_rows if d["status"] == "Date Adjusted (±1 day)")
    n_adj2   = sum(1 for d in duty_rows if d["status"] == "Date Adjusted (±2 days)")
    n_valadj = sum(1 for d in duty_rows if d["status"] == "Valuation-Adjacent")
    n_no     = sum(1 for d in duty_rows if not d["is_matched"])
    n_matched = n_exact + n_sess + n_adj1 + n_adj2 + n_valadj
    match_pct = n_matched / total * 100 if total else 0.0
    dev_pct   = 100.0 - match_pct
    allot_set = {(d["norm_date"], d["sess"]) for d in duty_rows}
    exact_overlap = len(will_set & allot_set)
    will_used_pct = exact_overlap / len(will_set) * 100 if will_set else 0.0

    st.markdown("---")
    st.markdown("### 📊 Willingness Match & Deviation")
    m1, m2, m3, m4 = st.columns(4)
    with m1: st.metric("Duties Allotted", total)
    with m2: st.metric("Willingness Match", f"{match_pct:.1f}%",
                       delta=f"{n_matched} of {total} within window")
    with m3: st.metric("Deviation", f"{dev_pct:.1f}%",
                       delta=f"{n_no} unmatched" if n_no else "None",
                       delta_color="inverse" if n_no else "off")
    with m4: st.metric("Your Exact Slots Used", f"{will_used_pct:.1f}%",
                       help=f"{exact_overlap} of your {len(will_set)} submitted slots allotted exactly")

    if total == 0:
        return "Not available", []
    elif dev_pct == 0.0:
        st.success("🎉 All duties were allotted exactly as per submitted willingness!")
    elif n_no == 0:
        st.info(f"ℹ️ All {total} duties fall within the willingness window. "
                f"{n_sess + n_adj1 + n_adj2} minor adjustment(s) made.")
    else:
        st.warning(f"⚠️ {n_no} of {total} duties could not be matched and were system-assigned.")

    STATUS_BG = {
        "Exact Match":              ("#d1fae5", "#065f46"),
        "Session Adjusted":         ("#fef3c7", "#92400e"),
        "Date Adjusted (±1 day)":   ("#ffedd5", "#9a3412"),
        "Date Adjusted (±2 days)":  ("#ffe4e6", "#881337"),
        "Valuation-Adjacent":       ("#ede9fe", "#5b21b6"),
        "Not in Willingness":       ("#fee2e2", "#991b1b"),
        "Auto-Assigned":            ("#e5e7eb", "#374151"),
    }
    rows_html = ""
    for d in duty_rows:
        bg, fg = STATUS_BG.get(d["status"], ("#e5e7eb", "#374151"))
        rows_html += (
            f"<tr>"
            f"<td style='padding:7px 10px;font-size:.87rem'>{d['date_fmt']}</td>"
            f"<td style='padding:7px 10px;text-align:center;font-weight:700'>{d['sess']}</td>"
            f"<td style='padding:7px 10px;text-align:center'>{d['dtype']}</td>"
            f"<td style='padding:7px 10px'><span style='display:inline-block;padding:2px 10px;"
            f"border-radius:12px;font-size:.8rem;font-weight:700;background:{bg};color:{fg}'>"
            f"{d['emoji']} {d['status']}</span></td>"
            f"<td style='padding:7px 10px;font-size:.82rem;color:#475569'>{d['detail']}</td>"
            f"</tr>")

    st.markdown(f"""
<div style="overflow-x:auto">
<table style="width:100%;border-collapse:collapse;background:#fff;
              border-radius:10px;overflow:hidden;box-shadow:0 2px 8px rgba(0,0,0,.06)">
  <thead>
    <tr style="background:#f1f5f9;font-size:.85rem;font-weight:700;color:#0f172a;">
      <th style="padding:8px 10px;text-align:left">Allotted Date</th>
      <th style="padding:8px 10px;text-align:center">Session</th>
      <th style="padding:8px 10px;text-align:center">Type</th>
      <th style="padding:8px 10px;text-align:left">Match Status</th>
      <th style="padding:8px 10px;text-align:left">Detail</th>
    </tr>
  </thead>
  <tbody>{rows_html}</tbody>
</table></div>""", unsafe_allow_html=True)

    st.markdown("#### Summary by Category")
    bd = pd.DataFrame({
        "Category": [
            "✅ Exact Match",
            "🔄 Session Adjusted (FN↔AN, same date)",
            "📅 Date Adjusted (±1 working day)",
            "📆 Date Adjusted (±2 working days)",
            "🗓️ Valuation-Adjacent (day before/after val date)",
            "🔴 Not in Willingness / Auto-Assigned",
        ],
        "Count": [n_exact, n_sess, n_adj1, n_adj2, n_valadj, n_no],
        "Share %": [f"{v/total*100:.1f}%" if total else "—"
                    for v in [n_exact, n_sess, n_adj1, n_adj2, n_valadj, n_no]],
        "Meaning": [
            "Allotted on the exact date & session you submitted",
            "Same date, but morning/afternoon slot was swapped",
            "Duty shifted by 1 working day from your submitted date",
            "Duty shifted by 2 working days from your submitted date",
            "Allotted on a weekday adjacent to your valuation date",
            "No matching date — system assigned to fill slot",
        ],
    })
    st.dataframe(bd, use_container_width=True, hide_index=True)

    dev_lines = [f"Overall match: {match_pct:.1f}%  ({n_matched}/{total} duties within window)"]
    if n_no == 0 and dev_pct == 0:
        dev_lines.append("All duties allotted exactly as per your willingness.")
    else:
        if n_exact  > 0: dev_lines.append(f"  ✅ Exact match        : {n_exact} duty(ies)")
        if n_sess   > 0: dev_lines.append(f"  🔄 Session swapped   : {n_sess} duty(ies)")
        if n_adj1   > 0: dev_lines.append(f"  📅 Date shifted ±1   : {n_adj1} duty(ies)")
        if n_adj2   > 0: dev_lines.append(f"  📆 Date shifted ±2   : {n_adj2} duty(ies)")
        if n_valadj > 0: dev_lines.append(f"  🗓️ Val-adjacent      : {n_valadj} duty(ies)")
        if n_no     > 0: dev_lines.append(f"  🔴 System-assigned   : {n_no} duty(ies)")
    match_str = f"Match {match_pct:.1f}%  ({n_matched}/{total})  |  Deviation {dev_pct:.1f}%"
    return match_str, dev_lines


# ═══════════════════════════════════════════════════════════════ #
#                    CALENDAR HEATMAP                            #
# ═══════════════════════════════════════════════════════════════ #
def render_calendar(duty_df, val_dates, title, exam_dates=None, buffer_dates=None, sat_blocked_dates=None):
    st.markdown(f"#### {title}")
    if duty_df.empty:
        st.info("No slot data available.")
        return

    slot_day_set = set(duty_df["Date"].dt.date)
    if not slot_day_set:
        return
    first_slot = min(slot_day_set)
    last_slot  = max(slot_day_set)

    months = sorted({(d.year, d.month) for d in duty_df["Date"]})
    sg = duty_df.groupby(["Date", "Session"], as_index=False)["Required"].sum()
    duty_map = {(row["Date"].date(), str(row["Session"]).upper()): int(row["Required"])
                for _, row in sg.iterrows()}
    val_set          = set(val_dates)
    exam_set         = set(exam_dates)         if exam_dates         else set()
    buffer_set       = set(buffer_dates)       if buffer_dates       else set()
    sat_blocked_set  = set(sat_blocked_dates)  if sat_blocked_dates  else set()
    WD_ORDER = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]

    _exam_legend = (
        "<span style='background:#fee2e2;border:1px solid #fca5a5;border-radius:4px;"
        "padding:2px 8px;margin-right:6px'>🚫 Exam Date (Locked)</span>"
    ) if exam_set else ""
    _buf_legend = (
        "<span style='background:#ffedd5;border:1px solid #fdba74;border-radius:4px;"
        "padding:2px 8px;margin-right:6px'>⛔ Buffer Day (n−1, n−2)</span>"
    ) if buffer_set else ""
    _sat_blk_legend = (
        "<span style='background:#f1f5f9;border:1px solid #94a3b8;border-radius:4px;"
        "padding:2px 8px;margin-right:6px'>🚷 Saturday (Not for your designation)</span>"
    ) if sat_blocked_set else ""
    st.markdown(
        "<span style='font-size:.82rem'>"
        "<span style='background:#fce7f3;border:1px solid #f9a8d4;border-radius:4px;"
        "padding:2px 8px;margin-right:6px'>🩷 Valuation Locked</span>"
        + _sat_blk_legend + _exam_legend + _buf_legend +
        "<span style='background:#fff;border:1px solid #cbd5e1;border-radius:4px;"
        "padding:2px 8px'>🔢 Number = duties required on that day/session</span>"
        "</span>", unsafe_allow_html=True)
    st.markdown("")

    for yr, mo in months:
        ms   = pd.Timestamp(year=yr, month=mo, day=1)
        me   = ms + pd.offsets.MonthEnd(0)
        days = pd.date_range(ms, me, freq="D")
        fw   = ms.weekday()
        grid = []; week = [None] * fw
        for dt in days:
            dt_date = dt.date()
            cell = dt_date if (first_slot <= dt_date <= last_slot) else None
            week.append(cell)
            if len(week) == 7:
                grid.append(week); week = []
        if week:
            week += [None] * (7 - len(week)); grid.append(week)
        grid = [w for w in grid if any(d is not None for d in w)]

        st.markdown(
            f"<div style='font-size:.95rem;font-weight:700;color:#1e3a5f;"
            f"margin:14px 0 4px 0'>{calmod.month_name[mo]} {yr}</div>",
            unsafe_allow_html=True)

        TH_DAY  = ("background:#1e3a5f;color:#fff;font-size:.8rem;font-weight:700;"
                   "text-align:center;padding:7px 4px;border:1px solid #2d4f7c;")
        TH_SESS = ("background:#dbeafe;color:#1e40af;font-size:.7rem;font-weight:700;"
                   "text-align:center;padding:4px 2px;border:1px solid #bfdbfe;width:44px;")
        TD_BASE = ("text-align:center;padding:5px 2px;border:1px solid #e2e8f0;"
                   "vertical-align:middle;min-width:44px;")

        hdr1 = "".join(f"<th colspan='2' style='{TH_DAY}'>{wd}</th>" for wd in WD_ORDER)
        hdr2 = "".join(f"<th style='{TH_SESS}'>FN</th><th style='{TH_SESS}'>AN</th>"
                       for _ in WD_ORDER)
        rows_html = ""
        for week_dates in grid:
            date_row = ""
            for dt in week_dates:
                if dt is None:
                    date_row += ("<td colspan='2' style='background:#fff;"
                                 "border:1px solid #e2e8f0;height:20px'></td>")
                else:
                    is_val    = dt in val_set
                    is_exam   = dt in exam_set
                    is_buffer = dt in buffer_set
                    is_sat_blk  = (dt in sat_blocked_set)
                    is_sun      = dt.weekday() == 6
                    if is_val:
                        bg, color = "#fce7f3", "#be185d"
                        label = f"{dt.day} 🔒"
                    elif is_exam:
                        bg, color = "#fee2e2", "#dc2626"
                        label = f"{dt.day} 🚫"
                    elif is_buffer:
                        bg, color = "#ffedd5", "#c2410c"
                        label = f"{dt.day} ⛔"
                    elif is_sat_blk:
                        bg, color = "#f1f5f9", "#94a3b8"
                        label = f"{dt.day} 🚷"
                    else:
                        bg    = "#fff"
                        color = "#94a3b8" if is_sun else "#0f172a"
                        label = str(dt.day)
                    date_row += (f"<td colspan='2' style='background:{bg};"
                                 f"border:1px solid #e2e8f0;text-align:center;"
                                 f"padding:4px 2px 2px 2px;vertical-align:middle'>"
                                 f"<span style='font-size:.88rem;font-weight:800;color:{color}'>"
                                 f"{label}</span></td>")
            rows_html += f"<tr>{date_row}</tr>"

            duty_row = ""
            for dt in week_dates:
                if dt is None:
                    duty_row += ("<td style='background:#fff;border:1px solid #e2e8f0;"
                                 "min-width:44px;height:24px'></td>" * 2)
                else:
                    is_val    = dt in val_set
                    is_exam   = dt in exam_set
                    is_buffer = dt in buffer_set
                    is_sat_blk_row = (dt in sat_blocked_set)
                    for sess in ["FN", "AN"]:
                        req = duty_map.get((dt, sess), 0)
                        if is_val:
                            bg, content = "#fce7f3", ""
                        elif is_exam:
                            bg, content = "#fee2e2", ""
                        elif is_buffer:
                            bg, content = "#ffedd5", ""
                        elif is_sat_blk_row:
                            bg, content = "#f1f5f9", ""
                        elif req == 0:
                            bg, content = "#fff", ""
                        else:
                            bg = "#fff"
                            content = (f"<span style='font-size:.72rem;font-style:italic;"
                                       f"font-weight:700;color:#2563eb'>{req}</span>")
                        duty_row += f"<td style='{TD_BASE}background:{bg}'>{content}</td>"
            rows_html += f"<tr>{duty_row}</tr>"

        st.markdown(f"""
<div style="overflow-x:auto;margin-bottom:20px;border-radius:10px;
            box-shadow:0 2px 12px rgba(15,23,42,.08);border:1px solid #e2e8f0">
<table style="border-collapse:collapse;width:100%;table-layout:fixed;
              font-family:Inter,sans-serif;border-radius:10px;overflow:hidden">
  <thead><tr>{hdr1}</tr><tr>{hdr2}</tr></thead>
  <tbody>{rows_html}</tbody>
</table></div>""", unsafe_allow_html=True)

    st.caption("FN = Forenoon  |  AN = Afternoon  |  Numbers = duties required on that day/session")


# ═══════════════════════════════════════════════════════════════ #
#   OPTIMIZER  — MILP (scipy HiGHS) + Smart Greedy + CP-SAT     #
# ═══════════════════════════════════════════════════════════════ #
def _load_core(log):
    if not SCIPY_OK:
        raise RuntimeError("scipy not installed. Run:  pip install scipy")

    # ── Load faculty from Supabase ────────────────────────────────
    fac_rows = db_get_all_faculty()
    if not fac_rows:
        raise RuntimeError("No faculty found in Supabase.")
    fr = pd.DataFrame(fac_rows)
    fr["Name"]        = fr["name"].astype(str).str.strip()
    fr["Designation"] = fr["designation"].astype(str).apply(_map_desig)
    # Apply per-faculty overrides
    for _i, _r in fr.iterrows():
        _fc = clean(_r["Name"])
        if _fc in FACULTY_DESIG_OVERRIDE:
            fr.at[_i, "Designation"] = FACULTY_DESIG_OVERRIDE[_fc]
    fr["ID No."]      = fr["faculty_id"].astype(str).apply(_norm_id)
    fr = fr.dropna(subset=["Name"]).reset_index(drop=True)

    ALL_FAC = fr["Name"].tolist()
    FAC_IDX = {n: i for i, n in enumerate(ALL_FAC)}
    N_FAC   = len(ALL_FAC)
    fac_d   = {r["Name"]: (r["Designation"] if r["Designation"] in DESIG_RULES else "TA")
               for _, r in fr.iterrows()}
    dgroups = defaultdict(list)
    for n, d in fac_d.items():
        dgroups[d].append(n)

    # ── Valuation dates from Supabase (ISO format YYYY-MM-DD) ─────
    fac_val = {}
    for _, r in fr.iterrows():
        vd = set()
        for c in ["v1","v2","v3","v4","v5"]:
            val = r.get(c)
            if val and str(val).strip() not in ("", "None", "NaT", "nan"):
                try:
                    vd.add(pd.to_datetime(str(val).strip()[:10],
                                          format="%Y-%m-%d").date())
                except Exception:
                    pass
        fac_val[r["Name"]] = vd

    # ── Load slots from Supabase (offline only) ───────────────────
    def _rows_to_slots(rows, duty_type):
        slots = []
        for r in rows:
            try:
                dt   = pd.to_datetime(str(r["duty_date"]).strip()[:10],
                                      format="%Y-%m-%d").date()
                sess = normalize_session(r["session"])
                req  = max(int(r.get("required", 1)), 0)
                if sess in ("FN", "AN"):
                    slots.append({"date": dt, "session": sess,
                                  "required": req, "type": duty_type})
            except Exception:
                pass
        return slots

    s_off = _rows_to_slots(db_get_offline_slots(), "Offline")
    s_on  = []   # No online duty this semester
    ALL_S = s_off
    NS    = len(ALL_S)
    slot_dates = {s["date"] for s in ALL_S}

    wdf = get_all_willingness().drop(columns=["FacultyClean"], errors="ignore")
    if not wdf.empty:
        wdf["Date"]    = pd.to_datetime(wdf["Date"], dayfirst=True, errors="coerce")
        wdf["Session"] = wdf["Session"].astype(str).str.strip().str.upper()
        wdf = wdf.dropna(subset=["Date"])
    submitted  = set(wdf["Faculty"].str.strip().unique()) if not wdf.empty else set()
    non_sub    = [n for n in ALL_FAC if n not in submitted]
    sub_counts = {}
    if not wdf.empty:
        for n, grp in wdf.groupby("Faculty"):
            sub_counts[n.strip()] = len(grp)

    log(f"  Faculty        : {N_FAC}")
    log(f"  Slots          : {NS}  (offline only — online duty suspended)")
    log(f"  Seats needed   : {sum(s['required'] for s in ALL_S)}")
    log(f"  Willingness    : {len(submitted)} submitted | {len(non_sub)} not submitted")

    SAT_DESIG = {"TA", "RA"}
    sap_faculty  = [n for n in ALL_FAC if fac_d.get(n) == "SAP"]
    sap_fallback = sap_faculty[:2]
    acp_faculty  = [n for n in ALL_FAC if fac_d.get(n) == "ACP"]
    acp_2online  = set()   # No online duty
    acp_2offline = set(acp_faculty)

    log(f"\n  ── Capacity Check ───────────────────────────────────")
    any_cap_warn = False
    for sl in ALL_S:
        avail = 0
        for fn in ALL_FAC:
            d2 = fac_d.get(fn, "TA")
            allowed = DESIG_RULES[d2][2]
            if sl["type"] not in allowed: continue
            if sl["date"] in fac_val.get(fn, set()): continue
            if sl["date"].weekday() == 5 and d2 not in SAT_DESIG: continue
            avail += 1
        if avail < sl["required"]:
            ds = sl["date"].strftime("%d-%m-%Y")
            log(f"  ⚠ {ds} {sl['session']} {sl['type']} — need {sl['required']} avail {avail}")
            any_cap_warn = True
    if not any_cap_warn:
        log(f"  ✓ All {NS} slots have sufficient eligible faculty")

    fexp = defaultdict(dict)
    def sset(d, k, val): d[k] = max(d.get(k, 0), val)
    def next_biz(d, steps):
        step = 1 if steps > 0 else -1
        cur = d; cnt = 0
        while cnt < abs(steps):
            cur += datetime.timedelta(days=step)
            if cur.weekday() < 5: cnt += 1
        return cur

    for _, row in wdf.iterrows():
        n = str(row.get("Faculty","")).strip()
        if n not in FAC_IDX: continue
        dt2  = row["Date"].date()
        sess = str(row["Session"]).strip().upper()
        opp  = "AN" if sess == "FN" else "FN"
        allowed = DESIG_RULES[fac_d.get(n, "TA")][2]
        for tp in allowed:
            sset(fexp[n], (dt2, sess, tp), W_EXACT)
        for tp in allowed:
            sset(fexp[n], (dt2, opp, tp), W_FLIP)
        for direction in [+1,-1]:
            adj = next_biz(dt2, direction)
            if adj not in slot_dates: continue
            for s2 in ["FN","AN"]:
                for tp in allowed:
                    sset(fexp[n], (adj, s2, tp), W_ADJ1)
        for direction in [+2,-2]:
            adj = next_biz(dt2, direction)
            if adj not in slot_dates: continue
            for s2 in ["FN","AN"]:
                for tp in allowed:
                    sset(fexp[n], (adj, s2, tp), W_ADJ2)

    for n in ALL_FAC:
        allowed = DESIG_RULES[fac_d.get(n, "TA")][2]
        for vd in fac_val.get(n, set()):
            for direction in [+1,-1]:
                adj = next_biz(vd, direction)
                if adj not in slot_dates: continue
                for s2 in ["FN","AN"]:
                    for tp in allowed:
                        k = (adj, s2, tp)
                        if fexp[n].get(k, 0) < W_VAL_ADJ:
                            sset(fexp[n], k, W_VAL_ADJ)

    for n in non_sub:
        allowed = DESIG_RULES[fac_d.get(n, "TA")][2]
        for s in ALL_S:
            if s["type"] in allowed:
                sset(fexp[n], (s["date"], s["session"], s["type"]), W_NON_SUB)

    def tag(fn, k, sc):
        if fn in non_sub:          return "Auto-Assigned"
        if sc >= W_EXACT:          return "Willingness-Exact"
        if sc >= W_ACP_ONLINE:     return "Willingness-ACPOnline"
        if sc >= W_FLIP:           return "Willingness-SessionFlip"
        if sc >= W_ADJ1:           return "Willingness-±1Day"
        if sc >= W_ADJ2:           return "Willingness-±2Day"
        if sc >= W_VAL_ADJ:        return "Willingness-ValAdj"
        if fn in sap_fallback:     return "SAP-OnlineFallback"
        return "OR-Assigned"

    def is_eligible(fn, sl):
        d2 = fac_d.get(fn, "TA")
        allowed = DESIG_RULES[d2][2]
        if sl["type"] not in allowed:                                        return False
        if sl["date"] in fac_val.get(fn, set()):                            return False
        # Per-faculty blackout dates (exam on that day etc.)
        if clean(fn) in FACULTY_BLACKOUT_CLEAN and sl["date"] in FACULTY_BLACKOUT_CLEAN[clean(fn)]:
            return False
        if sl["date"].weekday() == 5 and d2 not in SAT_DESIG:              return False
        return True

    # ── Per-faculty duty ranges ───────────────────────────────────────
    fac_duties = {fn: fac_duty_range(fn, fac_d.get(fn, "TA")) for fn in ALL_FAC}

    return dict(
        fr=fr, ALL_FAC=ALL_FAC, FAC_IDX=FAC_IDX, N_FAC=N_FAC,
        fac_d=fac_d, dgroups=dgroups, fac_val=fac_val,
        s_off=s_off, s_on=s_on, ALL_S=ALL_S, NS=NS,
        slot_dates=slot_dates, wdf=wdf,
        submitted=submitted, non_sub=non_sub, sub_counts=sub_counts,
        fexp=fexp, tag=tag, is_eligible=is_eligible,
        sap_fallback=sap_fallback, SAT_DESIG=SAT_DESIG,
        acp_2online=acp_2online, acp_2offline=acp_2offline,
        fac_duties=fac_duties,
    )


def _build_summary(assigned, core):
    ALL_FAC = core["ALL_FAC"]; fac_d = core["fac_d"]
    ALL_S   = core["ALL_S"];   submitted = core["submitted"]
    sub_counts = core["sub_counts"]
    alloc = pd.DataFrame(assigned)
    alloc["Date"] = pd.to_datetime(alloc["Date"]).dt.strftime("%d-%m-%Y")
    alloc = alloc.sort_values(["Date","Session","Name"]).reset_index(drop=True)
    alloc.insert(0, "Sl.No", alloc.index + 1)

    sumrows = []
    fac_duties_bs = core.get("fac_duties", {})
    for fn in ALL_FAC:
        d2 = fac_d[fn]; dr = DESIG_RULES[d2]
        min_d, _ = fac_duties_bs.get(fn, (dr[0], dr[1]))
        rf = alloc[alloc["Name"] == fn]; ab = rf["Allocated_By"]
        tot = len(rf); wt = int(ab.isin(WILL_TAGS).sum())
        sumrows.append({
            "Name": fn, "Designation": d2,
            "Submitted":        "Yes" if fn in submitted else "No",
            "Submitted_Count":  sub_counts.get(fn, 0),
            "Required_Duties":  min_d, "Assigned_Duties": tot,
            "Willingness_Total":wt,
            "Match_%":          f"{wt/tot*100:.0f}%" if tot else "N/A",
            "Exact_Match":      int((ab=="Willingness-Exact").sum()),
            "ACP_Online":       int((ab=="Willingness-ACPOnline").sum()),
            "Session_Flip":     int((ab=="Willingness-SessionFlip").sum()),
            "Adj_±1Day":        int((ab=="Willingness-±1Day").sum()),
            "Adj_±2Day":        int((ab=="Willingness-±2Day").sum()),
            "Val_Adj":          int((ab=="Willingness-ValAdj").sum()),
            "SAP_Online":       int((ab=="SAP-OnlineFallback").sum()),
            "Auto_Assigned":    int(ab.isin(["Auto-Assigned","OR-Assigned","Gap-Fill"]).sum()),
            "Online":  int((rf["Type"]=="Online").sum()),
            "Offline": int((rf["Type"]=="Offline").sum()),
            "Gap":     max(min_d-tot, 0),
        })
    sumdf = pd.DataFrame(sumrows)

    slotrows = []
    for sl in ALL_S:
        ds = pd.Timestamp(sl["date"]).strftime("%d-%m-%Y")
        na = len(alloc[(alloc["Date"]==ds)&(alloc["Session"]==sl["session"])&(alloc["Type"]==sl["type"])])
        slotrows.append({
            "Date": ds, "Session": sl["session"], "Type": sl["type"],
            "Required": sl["required"], "Assigned": na,
            "Status": "✓" if na >= sl["required"] else f"✗ short {sl['required']-na}"
        })
    slotdf = pd.DataFrame(slotrows)

    desigrows = []
    for d2 in DESIG_RULES:
        sub2 = sumdf[sumdf["Designation"]==d2]
        if sub2.empty: continue
        dr = DESIG_RULES[d2]
        on = int(sub2["Online"].sum()); of = int(sub2["Offline"].sum())
        desigrows.append({
            "Designation": d2, "Faculty_Count": len(sub2),
            "Duties_Per_Person": dr[0], "Total_Required": dr[0]*len(sub2),
            "Total_Assigned": on+of,
            "Willingness_Matched": int(sub2["Willingness_Total"].sum()),
            "Auto_Assigned": int(sub2["Auto_Assigned"].sum()),
            "Online": on, "Offline": of,
        })
    desigdf = pd.DataFrame(desigrows)
    return alloc, sumdf, slotdf, desigdf


def _greedy_solve(core, log):
    ALL_FAC = core["ALL_FAC"]; fac_d = core["fac_d"]
    ALL_S   = core["ALL_S"];   fexp  = core["fexp"]
    tag     = core["tag"];     is_eligible = core["is_eligible"]
    non_sub = core["non_sub"]; SAT_DESIG = core["SAT_DESIG"]
    sap_fallback = core["sap_fallback"]
    acp_2online  = core["acp_2online"]
    acp_2offline = core["acp_2offline"]

    alloc_count  = defaultdict(int)
    used_dt_sess = defaultdict(set)
    acp_online   = defaultdict(int)
    acp_offline  = defaultdict(int)

    def rem(fn):
        _, max_d = fac_duty_range(fn, fac_d.get(fn, "TA"))
        return max_d - alloc_count[fn]

    def eligible(fn, sl):
        if not is_eligible(fn, sl):        return False
        if rem(fn) <= 0:                   return False
        if (sl["date"], sl["session"]) in used_dt_sess[fn]: return False
        d2 = fac_d[fn]
        if d2 == "ACP":
            if sl["type"] == "Offline":
                limit_off = 2
                if acp_offline[fn] >= limit_off: return False
        return True

    def score(fn, sl):
        k  = (sl["date"], sl["session"], sl["type"])
        sc = fexp[fn].get(k, 0)
        return (sc, -alloc_count[fn], -DESIG_PRIORITY.get(fac_d[fn], 0))

    assigned = []
    for sl in sorted(ALL_S, key=lambda s: -s["required"]):
        needed = sl["required"]
        cands  = sorted([fn for fn in ALL_FAC if eligible(fn, sl)],
                        key=lambda fn: score(fn, sl), reverse=True)
        for fn in cands[:needed]:
            k  = (sl["date"], sl["session"], sl["type"])
            sc = fexp[fn].get(k, 0)
            assigned.append({"Name": fn, "Date": sl["date"],
                             "Session": sl["session"], "Type": sl["type"],
                             "Allocated_By": tag(fn, k, sc)})
            alloc_count[fn] += 1
            used_dt_sess[fn].add((sl["date"], sl["session"]))
            if fac_d[fn] == "ACP":
                if sl["type"] == "Offline": acp_offline[fn] += 1

        filled = sum(1 for a in assigned
                     if a["Date"]==sl["date"] and a["Session"]==sl["session"] and a["Type"]==sl["type"])
        if filled < needed:
            extras = sorted(
                [fn for fn in ALL_FAC
                 if is_eligible(fn, sl) and (sl["date"],sl["session"]) not in used_dt_sess[fn]
                 and fn not in [a["Name"] for a in assigned
                                if a["Date"]==sl["date"] and a["Session"]==sl["session"] and a["Type"]==sl["type"]]],
                key=lambda fn: score(fn, sl), reverse=True)
            for fn in extras[:needed-filled]:
                k  = (sl["date"], sl["session"], sl["type"])
                sc = fexp[fn].get(k, 0)
                assigned.append({"Name": fn, "Date": sl["date"],
                                 "Session": sl["session"], "Type": sl["type"],
                                 "Allocated_By": tag(fn, k, sc)})
                alloc_count[fn] += 1
                used_dt_sess[fn].add((sl["date"], sl["session"]))

    for fn in ALL_FAC:
        min_d, _ = fac_duty_range(fn, fac_d.get(fn, "TA"))
        needed = min_d - alloc_count[fn]
        if needed <= 0: continue
        for sl in sorted(ALL_S, key=lambda s: fexp[fn].get(
                (s["date"],s["session"],s["type"]),0), reverse=True):
            if needed <= 0: break
            if not is_eligible(fn, sl): continue
            if (sl["date"],sl["session"]) in used_dt_sess[fn]: continue
            k  = (sl["date"], sl["session"], sl["type"])
            sc = fexp[fn].get(k, 0)
            assigned.append({"Name": fn, "Date": sl["date"],
                             "Session": sl["session"], "Type": sl["type"],
                             "Allocated_By": tag(fn, k, sc)})
            alloc_count[fn] += 1
            used_dt_sess[fn].add((sl["date"],sl["session"]))
            needed -= 1

    return assigned


def _cpsat_solve(core, log):
    if not ORTOOLS_OK:
        log("  CP-SAT not available.")
        return None

    ALL_FAC = core["ALL_FAC"]; FAC_IDX = core["FAC_IDX"]
    N_FAC   = core["N_FAC"];   fac_d   = core["fac_d"]
    ALL_S   = core["ALL_S"];   NS      = core["NS"]
    fexp    = core["fexp"];    tag     = core["tag"]
    submitted  = core["submitted"]; non_sub = core["non_sub"]
    is_eligible = core["is_eligible"]
    dt_sess = defaultdict(list)
    for si, sl in enumerate(ALL_S):
        dt_sess[(sl["date"], sl["session"])].append(si)

    SLACK_PENALTY = 10_000_000
    GAP_PENALTY   =    500_000

    try:
        mdl = cp_model.CpModel()
        x = {}
        for fi, fn in enumerate(ALL_FAC):
            for si, sl in enumerate(ALL_S):
                x[(fi, si)] = mdl.NewBoolVar(f"x_{fi}_{si}")
                if not is_eligible(fn, sl):
                    mdl.Add(x[(fi, si)] == 0)

        sv = {}
        for si, sl in enumerate(ALL_S):
            sv[si] = mdl.NewIntVar(0, sl["required"], f"sv_{si}")

        gv = {}
        for fi, fn in enumerate(ALL_FAC):
            min_d, _ = fac_duty_range(fn, fac_d.get(fn, "TA"))
            gv[fi] = mdl.NewIntVar(0, min_d, f"gv_{fi}")

        obj_terms = []
        for fi, fn in enumerate(ALL_FAC):
            for si, sl in enumerate(ALL_S):
                if not is_eligible(fn, sl): continue
                k  = (sl["date"], sl["session"], sl["type"])
                sc = fexp[fn].get(k, 0)
                if sc > 0:
                    obj_terms.append(sc * x[(fi, si)])
                elif fn in submitted:
                    obj_terms.append(-PENALTY * x[(fi, si)])
        for si in range(NS):
            obj_terms.append(-SLACK_PENALTY * sv[si])
        for fi in range(N_FAC):
            obj_terms.append(-GAP_PENALTY * gv[fi])
        mdl.Maximize(sum(obj_terms))

        for si, sl in enumerate(ALL_S):
            mdl.Add(sum(x[(f, si)] for f in range(N_FAC)) + sv[si] == sl["required"])
        for fi, fn in enumerate(ALL_FAC):
            min_d, max_d = fac_duty_range(fn, fac_d.get(fn, "TA"))
            mdl.Add(sum(x[(fi, s)] for s in range(NS)) <= max_d)
            mdl.Add(sum(x[(fi, s)] for s in range(NS)) + gv[fi] == min_d)
        for fi in range(N_FAC):
            for sil in dt_sess.values():
                if len(sil) > 1:
                    mdl.Add(sum(x[(fi, si)] for si in sil) <= 1)

        acp_2offline = core["acp_2offline"]
        off_i = [i for i, s in enumerate(ALL_S) if s["type"] == "Offline"]
        for fn in ALL_FAC:
            if fac_d[fn] != "ACP": continue
            fi = FAC_IDX[fn]
            if off_i: mdl.Add(sum(x[(fi, si)] for si in off_i) <= 2)



        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds  = 300
        solver.parameters.num_search_workers   = 4
        solver.parameters.log_search_progress  = False

        status = solver.Solve(mdl)
        log(f"  CP-SAT status : {solver.StatusName(status)}")
        log(f"  Wall time     : {solver.WallTime():.1f}s")

        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            log("  ⚠ CP-SAT could not find a solution — skipping Method C")
            return None

        assigned = []
        for fi, fn in enumerate(ALL_FAC):
            for si, sl in enumerate(ALL_S):
                if solver.Value(x[(fi, si)]) == 1:
                    k  = (sl["date"], sl["session"], sl["type"])
                    sc = fexp[fn].get(k, 0)
                    assigned.append({"Name": fn, "Date": sl["date"],
                                     "Session": sl["session"], "Type": sl["type"],
                                     "Allocated_By": tag(fn, k, sc)})

        slack_total = sum(solver.Value(sv[si]) for si in range(NS))
        gap_total   = sum(solver.Value(gv[fi]) for fi in range(N_FAC))
        if slack_total > 0:
            log(f"  ⚠ Unfilled seats : {slack_total}")
            for si, sl in enumerate(ALL_S):
                sk = solver.Value(sv[si])
                if sk > 0:
                    log(f"    {sl['date'].strftime('%d-%m-%Y')} {sl['session']} {sl['type']} short {sk}")
        else:
            log("  ✓ All slots fully filled")
        if gap_total > 0:
            log(f"  ⚠ Faculty gaps   : {gap_total}")
        else:
            log("  ✓ All faculty assigned correct duty count")
        return assigned

    except Exception as e:
        log(f"  ✗ CP-SAT error: {e}")
        return None


def _milp_solve(core, log):
    ALL_FAC = core["ALL_FAC"]; FAC_IDX = core["FAC_IDX"]
    N_FAC   = core["N_FAC"];   fac_d   = core["fac_d"]
    ALL_S   = core["ALL_S"];   NS      = core["NS"]
    fexp    = core["fexp"];    tag     = core["tag"]
    submitted = core["submitted"]; non_sub = core["non_sub"]
    is_eligible = core["is_eligible"]
    sap_fallback = core["sap_fallback"]

    SLACK_PENALTY = 10_000_000
    GAP_PENALTY   =    500_000

    def v(fi, si): return fi * NS + si
    def sv(si):    return N_FAC * NS + si
    def gv(fi):    return N_FAC * NS + NS + fi

    NV    = N_FAC * NS + NS + N_FAC
    c_obj = np.zeros(NV)
    lb    = np.zeros(NV)
    ub    = np.ones(NV)

    for fi, fn in enumerate(ALL_FAC):
        for si, sl in enumerate(ALL_S):
            if not is_eligible(fn, sl):
                ub[v(fi, si)] = 0.0; continue
            k  = (sl["date"], sl["session"], sl["type"])
            sc = fexp[fn].get(k, 0)
            if sc > 0:
                c_obj[v(fi, si)] = -float(sc)
            elif fn in submitted:
                c_obj[v(fi, si)] = float(PENALTY)

    for si, sl in enumerate(ALL_S):
        ub[sv(si)]    = float(sl["required"])
        c_obj[sv(si)] = float(SLACK_PENALTY)

    for fi, fn in enumerate(ALL_FAC):
        min_d, _ = fac_duty_range(fn, fac_d.get(fn, "TA"))
        ub[gv(fi)]    = float(min_d)
        c_obj[gv(fi)] = float(GAP_PENALTY)

    rA, cA, dA, blo, bhi = [], [], [], [], []
    nc = [0]
    def add_con(vids, coeffs, lo, hi):
        for vi, co in zip(vids, coeffs):
            rA.append(nc[0]); cA.append(vi); dA.append(float(co))
        blo.append(float(lo)); bhi.append(float(hi)); nc[0] += 1

    for si, sl in enumerate(ALL_S):
        add_con([v(f,si) for f in range(N_FAC)] + [sv(si)],
                [1]*N_FAC + [1], sl["required"], sl["required"])

    for fi, fn in enumerate(ALL_FAC):
        min_d, max_d = fac_duty_range(fn, fac_d.get(fn, "TA"))
        add_con([v(fi,s) for s in range(NS)], [1]*NS, 0, max_d)
        add_con([v(fi,s) for s in range(NS)] + [gv(fi)],
                [1]*NS + [1], min_d, min_d)

    dt_sess = defaultdict(list)
    for si, sl in enumerate(ALL_S):
        dt_sess[(sl["date"], sl["session"])].append(si)
    for fi in range(N_FAC):
        for sil in dt_sess.values():
            if len(sil) > 1:
                add_con([v(fi,si) for si in sil], [1]*len(sil), 0, 1)

    acp_2offline = core["acp_2offline"]
    off_i = [i for i, s in enumerate(ALL_S) if s["type"] == "Offline"]
    for fn in ALL_FAC:
        if fac_d[fn] != "ACP": continue
        fi = FAC_IDX[fn]
        if off_i:
            add_con([v(fi,si) for si in off_i], [1]*len(off_i), 0, 2)

    from scipy.sparse import csc_matrix
    A = csc_matrix((dA, (rA, cA)), shape=(nc[0], NV))
    log(f"  Variables    : {NV}  Constraints: {nc[0]}")

    res = milp(
        c=c_obj,
        constraints=LinearConstraint(A, blo, bhi),
        integrality=np.ones(NV),
        bounds=Bounds(lb=lb, ub=ub),
        options={"disp": False, "time_limit": 300}
    )
    log(f"  HiGHS status : {res.message}")

    if res.status not in (0, 1):
        log("  ⚠ MILP failed — using greedy fallback")
        return _greedy_solve(core, log)

    xh = np.round(res.x).astype(int)
    assigned = []
    for fi, fn in enumerate(ALL_FAC):
        for si, sl in enumerate(ALL_S):
            if xh[v(fi, si)] == 1:
                k  = (sl["date"], sl["session"], sl["type"])
                sc = fexp[fn].get(k, 0)
                assigned.append({"Name": fn, "Date": sl["date"],
                                 "Session": sl["session"], "Type": sl["type"],
                                 "Allocated_By": tag(fn, k, sc)})

    slack_slots = [(si, sl) for si, sl in enumerate(ALL_S) if xh[sv(si)] > 0]
    gap_fac     = [(fi, fn) for fi, fn in enumerate(ALL_FAC) if xh[gv(fi)] > 0]
    if slack_slots:
        log(f"  ⚠ Unfilled seats: {sum(xh[sv(si)] for si,_ in slack_slots)}")
        for si, sl in slack_slots:
            log(f"    {sl['date'].strftime('%d-%m-%Y')} {sl['session']} {sl['type']} short {xh[sv(si)]}")
    else:
        log("  ✓ All slots fully filled")
    if gap_fac:
        log(f"  ⚠ Faculty duty gaps: {sum(xh[gv(fi)] for fi,_ in gap_fac)}")
        for fi, fn in gap_fac:
            log(f"    {fn} — short {xh[gv(fi)]}")
    else:
        log("  ✓ All faculty assigned correct duty count")

    return assigned


def _log_result(assigned, core, method, log):
    ALL_FAC   = core["ALL_FAC"]; fac_d    = core["fac_d"]
    submitted = core["submitted"]; non_sub = core["non_sub"]
    ALL_S     = core["ALL_S"];   sub_counts = core["sub_counts"]
    sap_fallback = core["sap_fallback"]

    alloc, sumdf, slotdf, desigdf = _build_summary(assigned, core)
    tot = len(alloc); ab2 = alloc["Allocated_By"]
    unmet = slotdf[~slotdf["Status"].str.startswith("✓")]
    gaps  = sumdf[sumdf["Gap"] > 0]
    sub_alloc = alloc[alloc["Name"].isin(submitted)]
    will_matched = int(sub_alloc["Allocated_By"].isin(WILL_TAGS).sum()) if not sub_alloc.empty else 0
    will_total   = len(sub_alloc)
    overall_pct  = will_matched / will_total * 100 if will_total > 0 else 0

    log(f"\n  {'='*54}")
    log(f"  RESULT  [{method}]")
    log(f"  {'='*54}")
    log(f"  Total assignments   : {tot}")
    log(f"  ├─ Exact            : {int((ab2=='Willingness-Exact').sum())}")
    log(f"  ├─ Session flip     : {int((ab2=='Willingness-SessionFlip').sum())}")
    log(f"  ├─ ±1 day           : {int((ab2=='Willingness-±1Day').sum())}")
    log(f"  ├─ ±2 days          : {int((ab2=='Willingness-±2Day').sum())}")
    log(f"  ├─ Val-adjacent     : {int((ab2=='Willingness-ValAdj').sum())}")
    log(f"  └─ Auto/OR-assigned : {int(ab2.isin(['Auto-Assigned','OR-Assigned','Gap-Fill']).sum())}")
    log(f"\n  ★ Willingness match : {overall_pct:.1f}%  ({will_matched}/{will_total})")
    log(f"  Slots filled        : {len(slotdf)-len(unmet)}/{len(slotdf)}"
        + (" ✓" if len(unmet)==0 else f"  ⚠ {len(unmet)} unmet"))
    log(f"  Faculty targets     : {len(sumdf)-len(gaps)}/{len(sumdf)}"
        + (" ✓" if len(gaps)==0 else f"  ⚠ {len(gaps)} short"))

    acp = sumdf[sumdf["Designation"]=="ACP"]
    p   = sumdf[sumdf["Designation"]=="P"]
    log(f"  P   (1 offline)     : {len(p[p['Offline']>=1])}/{len(p)}")
    log(f"  ACP summary (all offline this semester):")
    for _, r in acp.iterrows():
        off_c = int(r["Offline"])
        log(f"    {r['Name']:<32} {off_c} offline")

    return alloc, sumdf, slotdf, desigdf, overall_pct, len(unmet), len(gaps)


def run_optimizer(log_box):
    log_lines = []
    def log(m=""):
        log_lines.append(m)
        log_box.code("\n".join(log_lines), language="text")

    log("=" * 62)
    log("  SASTRA SoME Duty Optimizer  v4")
    log(f"  Method A: scipy HiGHS MILP")
    log(f"  Method B: Smart Greedy")
    log(f"  Method C: OR-Tools CP-SAT  ({'✅ Available' if ORTOOLS_OK else '❌ Not available'})")
    log(f"  NOTE: Online duty suspended — all slots are Offline this semester")
    log("=" * 62)

    log("\n  Loading data...")
    core = _load_core(log)
    results = {}

    log("\n" + "─"*62)
    log("  METHOD A — scipy HiGHS MILP")
    log("─"*62)
    try:
        assigned_A = _milp_solve(core, log)
        alloc_A, sumdf_A, slotdf_A, desigdf_A, pct_A, unmet_A, gaps_A = \
            _log_result(assigned_A, core, "MILP", log)
        results["MILP"] = dict(alloc=alloc_A, sumdf=sumdf_A, slotdf=slotdf_A,
                               desigdf=desigdf_A, pct=pct_A, unmet=unmet_A, gaps=gaps_A)
    except Exception as e:
        log(f"  ✗ MILP error: {e} — using greedy fallback")
        assigned_A = _greedy_solve(core, log)
        alloc_A, sumdf_A, slotdf_A, desigdf_A, pct_A, unmet_A, gaps_A = \
            _log_result(assigned_A, core, "MILP→Greedy", log)
        results["MILP"] = dict(alloc=alloc_A, sumdf=sumdf_A, slotdf=slotdf_A,
                               desigdf=desigdf_A, pct=pct_A, unmet=unmet_A, gaps=gaps_A)

    log("\n" + "─"*62)
    log("  METHOD B — Smart Greedy")
    log("─"*62)
    try:
        assigned_B = _greedy_solve(core, log)
        alloc_B, sumdf_B, slotdf_B, desigdf_B, pct_B, unmet_B, gaps_B = \
            _log_result(assigned_B, core, "Greedy", log)
        results["Greedy"] = dict(alloc=alloc_B, sumdf=sumdf_B, slotdf=slotdf_B,
                                 desigdf=desigdf_B, pct=pct_B, unmet=unmet_B, gaps=gaps_B)
    except Exception as e:
        log(f"  ✗ Greedy error: {e}")
        results["Greedy"] = results["MILP"]
        pct_B, unmet_B, gaps_B = pct_A, unmet_A, gaps_A
        alloc_B, sumdf_B, slotdf_B = alloc_A, sumdf_A, slotdf_A

    pct_C = unmet_C = gaps_C = None
    alloc_C = sumdf_C = slotdf_C = desigdf_C = None
    if ORTOOLS_OK:
        log("\n" + "─"*62)
        log("  METHOD C — OR-Tools CP-SAT")
        log("─"*62)
        try:
            assigned_C = _cpsat_solve(core, log)
            if assigned_C is not None:
                alloc_C, sumdf_C, slotdf_C, desigdf_C, pct_C, unmet_C, gaps_C = \
                    _log_result(assigned_C, core, "CP-SAT", log)
                results["CP-SAT"] = dict(alloc=alloc_C, sumdf=sumdf_C, slotdf=slotdf_C,
                                         desigdf=desigdf_C, pct=pct_C, unmet=unmet_C, gaps=gaps_C)
        except Exception as e:
            log(f"  ✗ CP-SAT error: {e}")
    else:
        log("\n  METHOD C — OR-Tools CP-SAT  ❌ Skipped (not installed)")

    log("\n" + "═"*62)
    log("  COMPARISON SUMMARY")
    log("═"*62)
    hdr = f"  {'Metric':<30} {'MILP':>10} {'Greedy':>10}"
    if pct_C is not None: hdr += f" {'CP-SAT':>10}"
    log(hdr); log("  " + "─"*58)
    def _row(label, vA, vB, vC, fmt="{}"):
        fA = fmt.format(vA) if vA is not None else "—"
        fB = fmt.format(vB) if vB is not None else "—"
        line = f"  {label:<30} {fA:>10} {fB:>10}"
        if pct_C is not None: line += f" {(fmt.format(vC) if vC is not None else '—'):>10}"
        log(line)
    _row("Willingness match %", pct_A, pct_B, pct_C, fmt="{:.1f}%")
    _row("Unmet slots",         unmet_A, unmet_B, unmet_C)
    _row("Faculty duty gaps",   gaps_A,  gaps_B,  gaps_C)
    _row("Total assignments",   len(alloc_A), len(alloc_B),
         len(alloc_C) if alloc_C is not None else None)
    log("  " + "─"*58)

    candidates = [("MILP", pct_A, unmet_A, gaps_A), ("Greedy", pct_B, unmet_B, gaps_B)]
    if pct_C is not None: candidates.append(("CP-SAT", pct_C, unmet_C, gaps_C))
    candidates.sort(key=lambda x: (x[2], x[3], -x[1]))
    rec = candidates[0][0]
    method_letter = {"MILP":"A","Greedy":"B","CP-SAT":"C"}[rec]
    log(f"  ★ Recommendation : METHOD {method_letter} ({rec})")

    alloc_A.to_excel("Final_Allocation_MILP.xlsx",   index=False)
    alloc_B.to_excel("Final_Allocation_Greedy.xlsx", index=False)
    if alloc_C is not None:
        alloc_C.to_excel("Final_Allocation_CPSAT.xlsx", index=False)

    best = results[rec]
    best["alloc"].to_excel(FINAL_ALLOC_FILE, index=False)
    with pd.ExcelWriter(ALLOC_REPORT_FILE, engine="openpyxl") as writer:
        best["alloc"].to_excel(writer,   sheet_name="Full_Allocation",   index=False)
        best["sumdf"].to_excel(writer,   sheet_name="Faculty_Summary",   index=False)
        best["slotdf"].to_excel(writer,  sheet_name="Slot_Verification", index=False)
        alloc_A.to_excel(writer, sheet_name="MILP_Allocation",   index=False)
        alloc_B.to_excel(writer, sheet_name="Greedy_Allocation", index=False)
        if alloc_C is not None:
            alloc_C.to_excel(writer, sheet_name="CPSAT_Allocation", index=False)

    st.session_state.update({
        "alloc_milp":    alloc_A,   "alloc_greedy":  alloc_B,   "alloc_cpsat":   alloc_C,
        "sumdf_milp":    sumdf_A,   "sumdf_greedy":  sumdf_B,   "sumdf_cpsat":   sumdf_C,
        "slotdf_milp":   slotdf_A,  "slotdf_greedy": slotdf_B,  "slotdf_cpsat":  slotdf_C,
        "pct_milp":      pct_A,     "pct_greedy":    pct_B,     "pct_cpsat":     pct_C,
        "unmet_milp":    unmet_A,   "unmet_greedy":  unmet_B,   "unmet_cpsat":   unmet_C,
        "gaps_milp":     gaps_A,    "gaps_greedy":   gaps_B,    "gaps_cpsat":    gaps_C,
        "recommended":   rec,       "cpsat_ok":      ORTOOLS_OK,
    })
    log(f"\n  Saved: {FINAL_ALLOC_FILE}  ({rec} — default)")
    return best["alloc"], best["sumdf"], best["slotdf"], best.get("desigdf", pd.DataFrame())


# ═══════════════════════════════════════════════════════════════ #
#              SESSION STATE DEFAULTS                            #
# ═══════════════════════════════════════════════════════════════ #
_defaults = {
    "logged_in":           False,
    "faculty_id":          "",
    "faculty_name":        "",
    "faculty_clean":       "",
    "is_admin":            False,
    "must_change_pw":      False,
    "panel_mode":          "User View",
    "user_panel_mode":     "Willingness",
    "selected_faculty":    "",
    "selected_slots":      [],
    "confirm_delete":          False,
    "confirm_delete_will":     False,
    "confirm_delete_allot":    False,
    "confirm_full_reset":      False,
    "pending_submissions": pd.DataFrame(columns=["Faculty", "Date", "Session"]),
}
for k, val in _defaults.items():
    if k not in st.session_state:
        st.session_state[k] = val


# ═══════════════════════════════════════════════════════════════ #
#                      LOGIN PAGE                                #
# ═══════════════════════════════════════════════════════════════ #
def page_login(fac_df):
    render_header(logo=True)
    _, c2, _ = st.columns([1, 2, 1])
    with c2:
        st.markdown(
            '<div class="card"><div class="card-title">🔒 Faculty Login</div>'
            '<p class="card-sub">Enter your Faculty ID and password to continue.</p></div>',
            unsafe_allow_html=True)

        if not BCRYPT_OK:
            st.warning("⚠ bcrypt not installed — run `pip install bcrypt` for full security.")

        fid_input = st.text_input("Faculty ID", placeholder="e.g. C870 or RS602").strip().upper().replace(" ", "")
        pwd = st.text_input("Password", type="password")

        if st.button("Sign In", use_container_width=True):
            if not fid_input or not pwd:
                st.error("Please enter both your Faculty ID and password.")
            else:
                db_row = db_get_faculty_by_id(fid_input)
                if not db_row:
                    st.error(
                        f"Faculty ID **{fid_input}** not found. "
                        "Enter your ID exactly as on your ID card (e.g. C2086, RS1051). "
                        "Contact admin if this persists.")
                elif verify_password(pwd, db_row["password_hash"]):
                    st.session_state.logged_in      = True
                    st.session_state.faculty_id     = fid_input
                    st.session_state._logged_fid    = fid_input
                    st.session_state.faculty_name   = str(db_row["name"]).strip()
                    st.session_state.faculty_clean  = clean(db_row["name"])
                    st.session_state.is_admin       = db_row.get("is_admin", False)
                    st.session_state.must_change_pw = db_row.get("must_change_pw", False)
                    st.rerun()
                else:
                    st.error(f"Incorrect password. Default first-time password is: **{DEFAULT_PASSWORD}**")

        st.markdown(
            f'<div class="blink" style="text-align:center;font-size:.96rem;margin-top:10px">'
            f'🔑 <strong>First-time login:</strong> your password is '
            f'<strong style="font-size:1.05rem;text-decoration:underline">{DEFAULT_PASSWORD}</strong>. '
            f'&nbsp;You will be <strong>prompted to change it</strong> on first login.'
            f'</div>',
            unsafe_allow_html=True)

    st.markdown("---")
    st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
    st.stop()


# ═══════════════════════════════════════════════════════════════ #
#             FORCE PASSWORD CHANGE PAGE                         #
# ═══════════════════════════════════════════════════════════════ #
def page_force_change_password():
    render_header(logo=False)
    fid  = st.session_state.faculty_id
    name = st.session_state.faculty_name
    st.markdown(f"### 🔑 Set Your Password")
    st.markdown(
        f"<div style='text-align:center;font-size:1rem;font-weight:600;color:#0b3a67;"
        f"margin-bottom:8px'>Welcome, {name}</div>",
        unsafe_allow_html=True)
    st.info("You must set a new password before continuing. "
            "It must be at least 6 characters and must not be the default password.")
    np1 = st.text_input("New Password", type="password", key="fc_np1")
    np2 = st.text_input("Confirm New Password", type="password", key="fc_np2")
    if st.button("Set Password & Continue", use_container_width=True, type="primary"):
        if len(np1) < 6:
            st.error("Password must be at least 6 characters.")
        elif np1 == DEFAULT_PASSWORD:
            st.error(f"New password cannot be the default password ({DEFAULT_PASSWORD}).")
        elif np1 != np2:
            st.error("Passwords do not match.")
        else:
            pw_update(fid, hash_password(np1), must_change=False)
            st.session_state.must_change_pw = False
            st.success("Password set successfully! Continuing…")
            st.rerun()
    st.markdown("---")
    st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
    st.stop()


# ═══════════════════════════════════════════════════════════════ #
#            CHANGE PASSWORD SECTION (logged-in user)            #
# ═══════════════════════════════════════════════════════════════ #
def section_change_password():
    fid = st.session_state.faculty_id
    with st.expander("🔑 Change My Password"):
        op  = st.text_input("Current Password", type="password", key="usr_op")
        np1 = st.text_input("New Password (min 6 chars)", type="password", key="usr_np1")
        np2 = st.text_input("Confirm New Password", type="password", key="usr_np2")
        if st.button("Update Password", key="usr_upd_pw"):
            entry = pw_get(fid)
            if not entry or not verify_password(op, entry["password_hash"]):
                st.error("Current password is incorrect.")
            elif len(np1) < 6:
                st.error("New password must be at least 6 characters.")
            elif np1 != np2:
                st.error("Passwords do not match.")
            elif np1 == DEFAULT_PASSWORD:
                st.error(f"Cannot reuse the default password ({DEFAULT_PASSWORD}).")
            else:
                pw_update(fid, hash_password(np1), must_change=False)
                st.success("Password updated successfully.")


# ═══════════════════════════════════════════════════════════════ #
#                        ADMIN VIEW                              #
# ═══════════════════════════════════════════════════════════════ #
def page_admin(fac_df, offline_df, online_df):
    st.markdown(
        '<div class="card"><div class="card-title">🔒 Admin Panel</div>'
        '<p class="card-sub">Full administrative access.</p></div>',
        unsafe_allow_html=True)

    t1, t2, t3, t4, t5 = st.tabs([
        "📋 Willingness Records",
        "🤖 Run Optimizer",
        "📊 View Results",
        "👥 Faculty Accounts",
        "⚙️ Portal Settings",
    ])

    # ── Tab 1: Willingness Records ──────────────────────────────── #
    with t1:
        st.markdown("### 📋 Willingness Records")
        st.caption("All willingness submitted by faculty via this portal.")

        w_all = get_all_willingness()
        if w_all.empty:
            st.info("No willingness data collected yet.")
        else:
            vdf = w_all.drop(columns=["FacultyClean"], errors="ignore").reset_index(drop=True)
            if "Sl.No" not in vdf.columns:
                vdf.insert(0, "Sl.No", vdf.index + 1)
            sub_cnt_val = vdf["Faculty"].nunique() if "Faculty" in vdf.columns else 0
            c1, c2, c3 = st.columns(3)
            c1.metric("Faculty Submitted",  sub_cnt_val)
            c2.metric("Not Yet Submitted",  len(fac_df) - sub_cnt_val)
            c3.metric("Total Rows",          len(vdf))
            st.dataframe(vdf, use_container_width=True, hide_index=True)

            st.markdown("#### ⬇ Download Collected Willingness")
            dl1, dl2 = st.columns(2)
            with dl1:
                st.download_button(
                    "⬇ Download as CSV",
                    data=vdf[["Faculty", "Date", "Session"]].to_csv(index=False).encode("utf-8"),
                    file_name="Willingness.csv", mime="text/csv",
                    use_container_width=True)
            with dl2:
                _buf = io.BytesIO()
                vdf[["Faculty", "Date", "Session"]].to_excel(_buf, index=False, engine="openpyxl")
                st.download_button(
                    "⬇ Download as Excel (.xlsx)",
                    data=_buf.getvalue(),
                    file_name="Willingness.xlsx",
                    mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                    use_container_width=True)

        st.markdown("---")
        st.markdown("#### 🗑 Reset Portal Data")
        st.caption("Use these buttons at the start of a new exam cycle. Each action is permanent.")

        rc1, rc2 = st.columns(2)
        with rc1:
            st.markdown("**Delete Willingness Only**")
            st.checkbox("Confirm delete willingness", key="confirm_delete_will")
            if st.button("🗑 Delete All Willingness", type="primary",
                         use_container_width=True, key="btn_del_will"):
                if st.session_state.get("confirm_delete_will"):
                    db_clear_all_willingness()
                    st.success("✅ All willingness deleted.")
                    del st.session_state["confirm_delete_will"]
                    st.rerun()
                else:
                    st.error("Tick the confirmation checkbox first.")

        with rc2:
            st.markdown("**Delete Allotment Only**")
            st.checkbox("Confirm delete allotment", key="confirm_delete_allot")
            if st.button("🗑 Delete All Allotment", type="primary",
                         use_container_width=True, key="btn_del_allot"):
                if st.session_state.get("confirm_delete_allot"):
                    _sb().table("final_allocation").delete().neq("id", 0).execute()
                    st.success("✅ All allotment records deleted.")
                    del st.session_state["confirm_delete_allot"]
                    st.rerun()
                else:
                    st.error("Tick the confirmation checkbox first.")

        st.markdown("---")
        st.markdown("**Full Reset — Delete Both Willingness & Allotment**")
        st.caption("Use this to completely reset before a new examination cycle.")
        st.checkbox("I confirm full reset of all willingness and allotment data",
                    key="confirm_full_reset")
        if st.button("⚠ Full Reset (Willingness + Allotment)", type="primary",
                     use_container_width=True, key="btn_full_reset"):
            if st.session_state.get("confirm_full_reset"):
                db_clear_all_willingness()
                _sb().table("final_allocation").delete().neq("id", 0).execute()
                st.success("✅ Full reset complete — all willingness and allotment records deleted.")
                del st.session_state["confirm_full_reset"]
                st.rerun()
            else:
                st.error("Tick the confirmation checkbox first.")

    # ── Tab 2: Run Optimizer ─────────────────────────────────────── #
    with t2:
        st.markdown("### 🤖 Run Allocation Optimizer")
        st.info("ℹ️ Online duty is suspended this semester. All duties are offline only.")
        st.markdown("#### 📁 Data Source Status (Supabase)")
        _w_all  = get_all_willingness()
        _wrows  = len(_w_all)
        _wfac   = _w_all["Faculty"].nunique() if not _w_all.empty and "Faculty" in _w_all.columns else 0
        _off_ok = len(offline_df) > 0
        st.markdown(f"""
| Source | Purpose | Status |
|---|---|---|
| Supabase `faculty` | Faculty list + designations | ✅ {len(fac_df)} records |
| Supabase `offline_duty` | Offline exam slots | {"✅ " + str(len(offline_df)) + " slots" if _off_ok else "❌ No data"} |
| Supabase `willingness`  | Faculty willingness | ✅ {_wrows} rows, {_wfac} faculty |
""")
        c1, c2, c3 = st.columns(3)
        c1.metric("Total Faculty",         len(fac_df))
        c2.metric("Willingness Submitted", f"{_wfac}/{len(fac_df)}")
        c3.metric("Willingness Rows",      _wrows)

        if not _off_ok:
            st.error("No offline duty slots in Supabase. Run load_to_supabase.py.")
        elif not ORTOOLS_OK and not SCIPY_OK:
            st.error("No solver available. Run:  pip install ortools  OR  pip install scipy")
        else:
            solver_label = "OR-Tools CP-SAT ✅" if ORTOOLS_OK else "scipy HiGHS (fallback) ⚠"
            st.info(f"🔧 Active solver: **{solver_label}**"
                    + ("" if ORTOOLS_OK else
                       " — install OR-Tools for better results:  `pip install ortools`"))

            st.markdown("#### 🔍 Pre-Run Diagnostic")
            diag_wdf        = get_all_willingness()
            slot_dates_diag = set(offline_df["Date"].dt.date.dropna())

            if not diag_wdf.empty and slot_dates_diag:
                wdf_diag = diag_wdf.copy()
                wdf_diag["_date"] = pd.to_datetime(
                    wdf_diag["Date"], dayfirst=True, errors="coerce").dt.date
                will_dates_diag = set(wdf_diag["_date"].dropna())
                overlap_diag    = will_dates_diag & slot_dates_diag
                only_will_diag  = will_dates_diag - slot_dates_diag

                d1, d2, d3 = st.columns(3)
                d1.metric("Slot Dates",        len(slot_dates_diag))
                d2.metric("Willingness Dates", len(will_dates_diag))
                d3.metric("✅ Overlapping",     len(overlap_diag),
                          delta="⚠ ZERO — dates don't match!" if len(overlap_diag) == 0 else None,
                          delta_color="inverse" if len(overlap_diag) == 0 else "off")

                if len(overlap_diag) == 0:
                    st.error("🚨 **CRITICAL: Zero date overlap!** Willingness dates don't match any exam slots.")
                elif len(only_will_diag) > len(overlap_diag):
                    st.warning(f"⚠️ {len(only_will_diag)} willingness dates outside slot period "
                               f"(only {len(overlap_diag)}/{len(will_dates_diag)} overlap).")
                else:
                    st.success(f"✅ {len(overlap_diag)} overlapping dates — good coverage.")

                if only_will_diag:
                    with st.expander(f"📋 {len(only_will_diag)} willingness dates NOT in any slot"):
                        bad = wdf_diag[wdf_diag["_date"].isin(only_will_diag)]\
                            .drop(columns=["_date", "FacultyClean"], errors="ignore")\
                            .reset_index(drop=True)
                        st.dataframe(bad, use_container_width=True, hide_index=True)
            else:
                st.info("Upload willingness and ensure slot files exist to run diagnostic.")

            st.markdown("---")
            st.info("💡 Recommended: Disable allotment view (Portal Settings) before running.")
            if st.button("▶ Run Optimizer", type="primary", use_container_width=True):
                lb2 = st.empty()
                with st.spinner("Running MILP optimization…"):
                    try:
                        alloc_out, sumdf_out, slotdf_out, _ = run_optimizer(lb2)
                        st.success("✅ Optimization complete! Go to **📊 View Results** to review.")
                        st.balloons()
                    except Exception as e:
                        import traceback
                        st.error(f"Optimizer error: {e}")
                        st.code(traceback.format_exc(), language="text")

    # ── Tab 3: View Results ─────────────────────────────────────── #
    with t3:
        st.markdown("### 📊 Allocation Results")

        pct_m   = st.session_state.get("pct_milp",    None)
        pct_g   = st.session_state.get("pct_greedy",  None)
        unmet_m = st.session_state.get("unmet_milp",  None)
        unmet_g = st.session_state.get("unmet_greedy",None)
        rec     = st.session_state.get("recommended", "MILP")

        if pct_m is not None and pct_g is not None:
            st.markdown("#### ⚖️ Method Comparison")
            c1, c2 = st.columns(2)
            def method_card(col, name, pct, unmet, is_rec):
                bg   = "#d1fae5" if is_rec else "#f1f5f9"
                bdr  = "#6ee7b7" if is_rec else "#e2e8f0"
                badge = " ⭐ Recommended" if is_rec else ""
                col.markdown(f"""
<div style="background:{bg};border:2px solid {bdr};border-radius:12px;
            padding:16px 18px;text-align:center">
  <div style="font-size:1.05rem;font-weight:800;color:#0f172a">{name}{badge}</div>
  <div style="font-size:2rem;font-weight:900;color:#0b3a67;margin:8px 0">{pct:.1f}%</div>
  <div style="font-size:.85rem;color:#475569">Willingness Match</div>
  <div style="margin-top:8px;font-size:.9rem;color:{'#065f46' if unmet==0 else '#991b1b'};font-weight:700">
    {'✅ All slots filled' if unmet==0 else f'⚠ {unmet} slot(s) unmet'}
  </div>
</div>""", unsafe_allow_html=True)

            with c1: method_card(c1, "Method A — MILP",   pct_m, unmet_m, rec=="MILP")
            with c2: method_card(c2, "Method B — Greedy", pct_g, unmet_g, rec=="Greedy")

            chosen = st.radio(
                "**Select method to activate as Final Allocation:**",
                ["Method A — MILP", "Method B — Greedy"],
                index=0 if rec=="MILP" else 1,
                horizontal=True, key="method_choice")

            if st.button("✅ Apply Selected Method", type="primary", use_container_width=True):
                chosen_key = "MILP" if "MILP" in chosen else "Greedy"
                sel_alloc  = st.session_state.get(f"alloc_{chosen_key.lower()}")
                sel_sumdf  = st.session_state.get(f"sumdf_{chosen_key.lower()}")
                sel_slotdf = st.session_state.get(f"slotdf_{chosen_key.lower()}")
                if sel_alloc is not None:
                    _recs = []
                    for _, _ar in sel_alloc.iterrows():
                        _nm = str(_ar.get("Name","")).strip()
                        _fid_match = fac_df[fac_df["Name"].str.strip().str.lower() == _nm.lower()]
                        _fid_val   = str(_fid_match.iloc[0]["ID No."]) if not _fid_match.empty else _nm
                        _recs.append({
                            "faculty_id":   _fid_val,
                            "faculty_name": _nm,
                            "designation":  str(_ar.get("Designation","")),
                            "duty_date":    str(pd.to_datetime(_ar["Date"], dayfirst=True).date()),
                            "session":      str(_ar.get("Session","")).strip().upper(),
                            "duty_type":    str(_ar.get("Type","Offline")).strip(),
                            "allocated_by": str(_ar.get("Allocated_By","")).strip(),
                        })
                    db_save_allocation(_recs)
                    sel_alloc.to_excel(FINAL_ALLOC_FILE, index=False)
                    with pd.ExcelWriter(ALLOC_REPORT_FILE, engine="openpyxl") as writer:
                        sel_alloc.to_excel(writer,  sheet_name="Full_Allocation",   index=False)
                        sel_sumdf.to_excel(writer,  sheet_name="Faculty_Summary",   index=False)
                        sel_slotdf.to_excel(writer, sheet_name="Slot_Verification", index=False)
                    st.success(f"✅ {chosen_key} method saved to Supabase and Excel.")
                    st.session_state["recommended"] = chosen_key
                    st.rerun()

            st.markdown("#### ⬇ Download Both Results")
            dl1, dl2 = st.columns(2)
            with dl1:
                fp = "Final_Allocation_MILP.xlsx"
                if os.path.exists(fp):
                    with open(fp, "rb") as fh:
                        st.download_button("⬇ MILP Allocation", data=fh.read(),
                            file_name=fp, use_container_width=True,
                            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
            with dl2:
                fp = "Final_Allocation_Greedy.xlsx"
                if os.path.exists(fp):
                    with open(fp, "rb") as fh:
                        st.download_button("⬇ Greedy Allocation", data=fh.read(),
                            file_name=fp, use_container_width=True,
                            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
            st.markdown("---")

        _db_alloc_rows = db_get_all_allocation()
        if _db_alloc_rows:
            av = pd.DataFrame(_db_alloc_rows)
            av.rename(columns={"faculty_name":"Name","duty_date":"Date","session":"Session",
                                "duty_type":"Type","allocated_by":"Allocated_By",
                                "designation":"Designation"}, inplace=True)
            av["Date"] = pd.to_datetime(av["Date"], errors="coerce").dt.strftime("%d-%m-%Y")
        elif os.path.exists(FINAL_ALLOC_FILE):
            av = pd.read_excel(FINAL_ALLOC_FILE)
        else:
            av = pd.DataFrame()

        if av.empty:
            st.info("No results yet. Run the optimizer first.")
        else:
            rep = {}
            if os.path.exists(ALLOC_REPORT_FILE):
                xl2 = pd.ExcelFile(ALLOC_REPORT_FILE)
                for sh in xl2.sheet_names: rep[sh] = xl2.parse(sh)

            tot2 = len(av)
            if tot2 > 0 and "Allocated_By" in av.columns:
                ab3    = av["Allocated_By"]
                will_m = int(ab3.isin(WILL_TAGS).sum())
                aut    = int(ab3.isin(["Auto-Assigned","OR-Assigned","Gap-Fill"]).sum())
                c1, c2, c3, c4 = st.columns(4)
                c1.metric("Total Assignments",   tot2)
                c2.metric("Willingness Matched", will_m)
                c3.metric("Auto-Assigned",        aut)
                c4.metric("Overall Match %",      f"{will_m/tot2*100:.1f}%")

            for sh_name, label in [("Designation_Summary","Designation Summary"),
                                   ("Slot_Verification",  "Slot Verification"),
                                   ("Faculty_Summary",    "Faculty Summary")]:
                if sh_name in rep:
                    st.markdown(f"#### {label}")
                    if sh_name == "Slot_Verification" and "Status" in rep[sh_name].columns:
                        um = rep[sh_name][~rep[sh_name]["Status"].str.startswith("✓")]
                        ts = len(rep[sh_name]); ms2 = ts - len(um)
                        if len(um) == 0:
                            st.metric("Slots Fulfilled", f"{ms2}/{ts}", delta="✅ All Slots Met")
                        else:
                            st.metric("Slots Fulfilled", f"{ms2}/{ts}",
                                      delta=f"⚠ {len(um)} unmet", delta_color="inverse")
                            for _, r in um.iterrows():
                                st.error(f"⚠ {r['Date']} {r['Session']} {r['Type']} — {r['Status']}")
                    st.dataframe(rep[sh_name], use_container_width=True, hide_index=True)

            st.markdown("---")
            st.markdown("#### 🔍 Per-Faculty Deviation Analysis")
            admin_fnames = fac_df["Name"].dropna().drop_duplicates().tolist()
            admin_sel    = st.selectbox("Select Faculty", admin_fnames, key="admin_dev_sel")
            admin_sc     = clean(admin_sel)
            wd_admin     = load_willingness()
            admin_will_set = set()
            if not wd_admin.empty:
                wm_a = fac_mask(wd_admin, admin_sc)
                wr_a = wd_admin[wm_a]
                if not wr_a.empty and {"Date","Session"}.issubset(wr_a.columns):
                    for d2, s2 in zip(wr_a["Date"], wr_a["Session"]):
                        nd = pd.to_datetime(d2, dayfirst=True, errors="coerce")
                        if pd.notna(nd):
                            admin_will_set.add((nd.date(), str(s2).upper()))
            am_a = fac_mask(av, admin_sc)
            render_deviation_section(av[am_a].copy(), admin_will_set)

            st.markdown("---")
            st.markdown("#### Full Allocation Table")
            st.dataframe(av, use_container_width=True, hide_index=True)
            col1, col2 = st.columns(2)
            with col1:
                if os.path.exists(FINAL_ALLOC_FILE):
                    with open(FINAL_ALLOC_FILE, "rb") as fh:
                        st.download_button("⬇ Final_Allocation.xlsx", data=fh.read(),
                            file_name="Final_Allocation.xlsx",
                            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
            with col2:
                if os.path.exists(ALLOC_REPORT_FILE):
                    with open(ALLOC_REPORT_FILE, "rb") as fh:
                        st.download_button("⬇ Allocation_Report.xlsx", data=fh.read(),
                            file_name="Allocation_Report.xlsx",
                            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

    # ── Tab 4: Faculty Accounts ─────────────────────────────────── #
    with t4:
        st.markdown("### 👥 Faculty Account Management")
        st.caption("View all faculty accounts, reset passwords, and manage admin rights.")

        all_fac_rows = db_get_all_faculty()
        id_name_map  = {r["faculty_id"]: r["name"] for r in all_fac_rows}
        acc_rows = []
        for r in all_fac_rows:
            acc_rows.append({
                "ID No.":          r["faculty_id"],
                "Name":            r["name"],
                "Raw Designation": r["designation"],
                "Resolved Code":   _map_desig(r["designation"]) if clean(r["name"]) not in FACULTY_DESIG_OVERRIDE
                                   else f"{FACULTY_DESIG_OVERRIDE[clean(r['name'])]} ⚠️override",
                "Full Name":       DESIG_FULL.get(_map_desig(r["designation"]), "Unknown") if clean(r["name"]) not in FACULTY_DESIG_OVERRIDE
                                   else DESIG_FULL.get(FACULTY_DESIG_OVERRIDE[clean(r["name"])], "Unknown"),
                "Must Change":     "⚠ Yes" if r.get("must_change_pw") else "No",
                "Is Admin":        "👑 Yes" if r.get("is_admin") else "No",
            })
        acc_df = pd.DataFrame(acc_rows)
        acc_df.insert(0, "Sl.No", acc_df.index + 1)
        st.dataframe(acc_df, use_container_width=True, hide_index=True)

        st.markdown("---")
        st.markdown("#### 🔑 Reset a Faculty's Password")
        st.caption(f"Resets password to default (**{DEFAULT_PASSWORD}**) and forces change on next login.")
        id_options = [f"{fid} — {nm}" for fid, nm in id_name_map.items()]
        reset_sel  = st.selectbox("Select Faculty to Reset", id_options, key="admin_reset_sel")
        reset_fid  = reset_sel.split(" — ")[0]
        if st.button("Reset Password", key="btn_reset_pw"):
            db_reset_faculty_pw(reset_fid)
            st.success(f"Password for **{id_name_map.get(reset_fid, reset_fid)}** reset to default.")

        st.markdown("---")
        st.markdown("#### 🔄 Reset ALL Faculty Passwords in One Go")
        st.caption(f"Resets every faculty's password to **{DEFAULT_PASSWORD}** and forces a change on next login. "
                   f"Use at the start of a new semester before faculty begin logging in.")
        _col_warn, _col_btn = st.columns([3, 1])
        with _col_warn:
            st.warning("⚠️ This will log out and force password change for **all** faculty. "
                       "Only proceed if you are sure.")
        st.checkbox("I confirm bulk reset of all faculty passwords", key="confirm_bulk_pw_reset")
        if st.button("🔄 Reset ALL Passwords Now", type="primary",
                     use_container_width=True, key="btn_bulk_reset_pw"):
            if st.session_state.get("confirm_bulk_pw_reset"):
                _reset_h = hash_password(DEFAULT_PASSWORD)
                _all_rows = db_get_all_faculty()
                _count = 0
                for _r in _all_rows:
                    _sb().table("faculty").update({
                        "password_hash": _reset_h, "must_change_pw": True
                    }).eq("faculty_id", _r["faculty_id"]).execute()
                    _count += 1
                del st.session_state["confirm_bulk_pw_reset"]
                st.success(f"✅ {_count} faculty passwords reset to **{DEFAULT_PASSWORD}**. "
                           f"All faculty will be prompted to change on next login.")
                st.rerun()
            else:
                st.error("Tick the confirmation checkbox first.")

        st.markdown("---")
        st.markdown("#### 👑 Toggle Admin Rights")
        toggle_sel  = st.selectbox("Select Faculty", id_options, key="admin_toggle_sel")
        toggle_fid  = toggle_sel.split(" — ")[0]
        toggle_row  = db_get_faculty_by_id(toggle_fid)
        cur_admin   = toggle_row.get("is_admin", False) if toggle_row else False
        st.info(f"**{id_name_map.get(toggle_fid, toggle_fid)}** is currently: "
                f"{'👑 Admin' if cur_admin else 'Regular Faculty'}")
        col_a, col_b = st.columns(2)
        with col_a:
            if st.button("Grant Admin", disabled=cur_admin, use_container_width=True):
                db_set_admin(toggle_fid, True)
                st.success(f"Admin rights granted to {id_name_map.get(toggle_fid, toggle_fid)}."); st.rerun()
        with col_b:
            if st.button("Revoke Admin", disabled=not cur_admin, use_container_width=True):
                db_set_admin(toggle_fid, False)
                st.success(f"Admin rights revoked from {id_name_map.get(toggle_fid, toggle_fid)}."); st.rerun()

        st.markdown("---")
        st.markdown("#### 🔒 Change My Admin Password")
        with st.expander("Change Admin Password"):
            op  = st.text_input("Current Password", type="password", key="adm_op")
            np1 = st.text_input("New Password", type="password", key="adm_np1")
            np2 = st.text_input("Confirm New Password", type="password", key="adm_np2")
            if st.button("Update Admin Password", key="adm_upd_pw"):
                entry = pw_get(st.session_state.faculty_id)
                if not entry or not verify_password(op, entry["password_hash"]):
                    st.error("Current password is incorrect.")
                elif len(np1) < 6:
                    st.error("Password must be at least 6 characters.")
                elif np1 != np2:
                    st.error("Passwords do not match.")
                else:
                    pw_update(st.session_state.faculty_id, hash_password(np1))
                    st.success("Admin password updated successfully.")

    # ── Tab 5: Portal Settings ──────────────────────────────────── #
    with t5:
        st.markdown("### ⚙️ Portal Settings")
        st.markdown("---")
        st.markdown("#### 🔒 Allotment View — User Access Control")
        is_open = gate_is_open()
        if is_open:
            st.markdown(
                "<div style='background:#d1fae5;border:1.5px solid #6ee7b7;"
                "border-radius:10px;padding:12px 18px;margin-bottom:14px'>"
                "<span style='font-size:1.05rem;font-weight:700;color:#065f46'>"
                "🟢  Allotment view is ENABLED — faculty can see their allotment.</span>"
                "</div>", unsafe_allow_html=True)
        else:
            st.markdown(
                "<div style='background:#fee2e2;border:1.5px solid #fca5a5;"
                "border-radius:10px;padding:12px 18px;margin-bottom:14px'>"
                "<span style='font-size:1.05rem;font-weight:700;color:#991b1b'>"
                "🔴  Allotment view is DISABLED — faculty see a waiting message.</span>"
                "</div>", unsafe_allow_html=True)
        en_col, dis_col = st.columns(2)
        with en_col:
            if st.button("✅ Enable Allotment View", use_container_width=True,
                         disabled=is_open, type="primary"):
                set_gate(True); st.success("Enabled."); st.rerun()
        with dis_col:
            if st.button("🔴 Disable Allotment View", use_container_width=True,
                         disabled=not is_open):
                set_gate(False); st.warning("Disabled."); st.rerun()
        st.caption("Workflow: Disable → Run Optimizer → Review → Enable.")

        st.markdown("---")
        st.markdown("#### 🔄 Clear App Cache")
        st.caption("Forces a reload of faculty, slots, and willingness data from Supabase. "
                   "Use after updating designations in Supabase or after applying overrides.")
        if st.button("🔄 Clear All Cached Data", use_container_width=True):
            st.cache_data.clear()
            st.success("✅ Cache cleared — all data will reload fresh from Supabase.")
            st.rerun()




# ═══════════════════════════════════════════════════════════════ #
#             ALLOTMENT VIEW (faculty self-service)              #
# ═══════════════════════════════════════════════════════════════ #
def page_allotment(fac_df, sel_name, sel_clean, frow, offline_df, online_df):
    st.markdown("### My Allotment Details")

    _aslot_dates = set(offline_df["Date"].dt.date.dropna())
    _as, _ae     = get_exam_period(_aslot_dates)
    if _as and _ae:
        st.markdown(
            f"<div style='background:#e0f2fe;border:1.5px solid #38bdf8;border-radius:10px;"
            f"padding:10px 16px;margin-bottom:12px;font-size:.93rem;color:#0c4a6e'>"
            f"📅 <b>Exam Period:</b> "
            f"<b>{_as.strftime('%d-%m-%Y')} ({_as.strftime('%A')})</b>"
            f" → <b>{_ae.strftime('%d-%m-%Y')} ({_ae.strftime('%A')})</b>"
            f"</div>", unsafe_allow_html=True)

    if not gate_is_open():
        st.markdown(
            "<div style='background:#fef3c7;border:2px solid #f59e0b;border-radius:12px;"
            "padding:22px 26px;text-align:center;margin:18px 0'>"
            "<div style='font-size:2.2rem;margin-bottom:8px'>⏳</div>"
            "<div style='font-size:1.15rem;font-weight:700;color:#92400e'>"
            "Allotment results are being processed</div>"
            "<div style='font-size:.93rem;color:#78350f;margin-top:6px'>"
            "The Examination Committee is reviewing the final allocation. "
            "Please check back shortly.</div>"
            "</div>", unsafe_allow_html=True)
        return

    vd = [f"{fmt_day(d.strftime('%d-%m-%Y'))} - Full Day" for d in valuation_dates_for(frow)]
    qd = [fmt_day(d) for d in qp_dates_for(frow)]

    wd2   = load_willingness()
    wdisp = []
    will_pairs: set = set()
    if not wd2.empty:
        wm = fac_mask(wd2, sel_clean); wr = wd2[wm]
        if not wr.empty and {"Date", "Session"}.issubset(wr.columns):
            for d2, s2 in zip(wr["Date"], wr["Session"]):
                nd = pd.to_datetime(d2, dayfirst=True, errors="coerce")
                if pd.notna(nd):
                    wdisp.append(f"{fmt_day(d2)} - {str(s2).upper()}")
                    will_pairs.add((nd.date(), str(s2).upper()))

    _logged_fid_allot = st.session_state.get("_logged_fid", "")
    _allot_db_rows    = db_get_allocation_for(_logged_fid_allot) if _logged_fid_allot else []
    idisp = []
    allot_pairs: set = set()
    for _arow in _allot_db_rows:
        _raw_d  = _arow.get("duty_date","")
        _sess   = str(_arow.get("session","")).strip().upper()
        _mode   = str(_arow.get("duty_type","")).strip()
        _sat_tag = ""
        try:
            if pd.to_datetime(_raw_d).weekday() == 5:
                _sat_tag = " — Saturday"
        except: pass
        idisp.append(f"{fmt_day(_raw_d)} - {_sess} ({_mode}){_sat_tag}")
        nd2 = pd.to_datetime(_raw_d, errors="coerce")
        if pd.notna(nd2):
            allot_pairs.add((nd2.date(), _sess))

    if will_pairs:
        matched = len(will_pairs & allot_pairs)
        acc_pct = f"{matched/len(will_pairs)*100:.1f}%  ({matched}/{len(will_pairs)})"
    else:
        acc_pct = "Not available"

    c1, c2 = st.columns(2)
    with c1:
        st.markdown('<div class="panel"><div class="sec-title">📝 Willingness Submitted</div></div>',
                    unsafe_allow_html=True)
        st.dataframe(pd.DataFrame({"Date & Session": wdisp or ["Not submitted"]}),
                     use_container_width=True, hide_index=True)
        st.markdown('<div class="panel"><div class="sec-title">🏛️ IG Duty Allotment</div></div>',
                    unsafe_allow_html=True)
        st.dataframe(pd.DataFrame({"Date, Session & Type": idisp or ["Not allotted yet"]}),
                     use_container_width=True, hide_index=True)
    with c2:
        st.markdown('<div class="panel"><div class="sec-title">📋 Valuation Dates</div></div>',
                    unsafe_allow_html=True)
        st.dataframe(pd.DataFrame({"Date": vd or ["Not available"]}),
                     use_container_width=True, hide_index=True)
        st.markdown('<div class="panel"><div class="sec-title">💬 QP Feedback Dates</div></div>',
                    unsafe_allow_html=True)
        st.dataframe(pd.DataFrame({"Date": qd or ["Not available"]}),
                     use_container_width=True, hide_index=True)

    st.markdown(
        f"<div style='margin-top:10px;padding:12px 16px;background:#f0fdf4;"
        f"border:1.5px solid #86efac;border-radius:10px;font-size:.9rem;color:#166534'>"
        f"📊 <b>Willingness Accommodation:</b> {acc_pct}</div>",
        unsafe_allow_html=True)

    st.markdown(
        "<div style='margin-top:10px;padding:10px 14px;background:#f1f5f9;"
        "border-radius:8px;border:1px solid #cbd5e1;font-size:.82rem;color:#475569'>"
        "📩 For support or clarification, contact the "
        "<strong>University Examination Committee, SoME</strong>.</div>",
        unsafe_allow_html=True)

    msg = build_msg(sel_name, wdisp, vd, idisp, qd)
    st.markdown('<div class="panel"><div class="sec-title">📲 Share via WhatsApp</div></div>',
                unsafe_allow_html=True)
    st.markdown("**Message Preview:**")
    st.code(msg, language="text")
    wph = st.text_input("WhatsApp Number (with country code)", placeholder="+919876543210")
    if wph.strip():
        lnk = wa_link(wph.strip(), msg)
        st.markdown(
            f'<a href="{lnk}" target="_blank" style="display:inline-block;'
            f'background:#25D366;color:white;padding:10px 22px;border-radius:10px;'
            f'font-weight:700;text-decoration:none;margin-top:6px">'
            f'📲 Open WhatsApp &amp; Send</a>', unsafe_allow_html=True)
    else:
        st.caption("Enter your WhatsApp number above to generate the send link.")


# ═══════════════════════════════════════════════════════════════ #
#             WILLINGNESS SUBMISSION PAGE                        #
# ═══════════════════════════════════════════════════════════════ #
def page_willingness(fac_df, offline_df, online_df, sel_name, frow):
    sel_clean = clean(sel_name)
    desig2    = str(frow["Designation"]).strip().upper()
    val_d2    = valuation_dates_for(frow)
    val_s2    = set(val_d2)
    fn_clean  = clean(sel_name)
    min_d, _  = fac_duty_range(sel_name, desig2)
    if fn_clean in FIVE_DUTY_CLEAN:
        req_cnt = 12    # Last 4 TA: 5 duties → 12 willingness options
    elif fn_clean in SAT_PREASSIGN_CLEAN:
        req_cnt = 11    # First 13 TA + RA: 4 duties → 11 willingness options
    else:
        req_cnt = DUTY_STRUCTURE.get(desig2, 0)

    if req_cnt == 0:
        st.warning(f"Designation '{desig2}' not recognised. Contact admin.")
        return

    # All designations use offline slots this semester
    sopts = offline_df.copy()
    sopts["Date"]     = pd.to_datetime(sopts["Date"], errors="coerce")
    sopts["DateOnly"] = sopts["Date"].dt.date
    fac_blackout_dates = FACULTY_BLACKOUT_CLEAN.get(fn_clean, set())   # n, n-1, n-2
    fac_exam_dates     = FACULTY_EXAM_DATES_CLEAN.get(fn_clean, set()) # exam day only (for highlight)

    # Determine if this designation is NOT allowed on Saturdays
    _sat_blocked_desig = desig2 not in {"TA", "RA"}

    # Saturday dates in the slot list — used for calendar highlight + selector filter
    _all_sat_dates = {d for d in sopts["DateOnly"].dropna().unique() if d.weekday() == 5}

    valid_d = sorted([
        d for d in sopts["DateOnly"].dropna().unique()
        if d not in val_s2
        and d not in fac_blackout_dates
        and not (_sat_blocked_desig and d.weekday() == 5)   # block Saturdays for P/ACP/SAP/AP3/AP2
    ])

    if st.session_state.selected_faculty != sel_clean:
        st.session_state.selected_faculty = sel_clean
        st.session_state.selected_slots   = []
        st.session_state["picked_date"]   = valid_d[0] if valid_d else None

    if "picked_date" not in st.session_state:
        st.session_state["picked_date"] = valid_d[0] if valid_d else None

    # Show exam period banner
    _slot_dates_user = set(offline_df["Date"].dt.date.dropna())
    _exam_start, _exam_end = get_exam_period(_slot_dates_user)

    _period_str = ""
    if _exam_start and _exam_end:
        _period_str = (
            f"📅 <b>Exam Period:</b> "
            f"<b>{_exam_start.strftime('%d-%m-%Y')} ({_exam_start.strftime('%A')})</b>"
            f" → <b>{_exam_end.strftime('%d-%m-%Y')} ({_exam_end.strftime('%A')})</b>")

    st.markdown(
        f"<div style='background:#e0f2fe;border:1.5px solid #38bdf8;border-radius:10px;"
        f"padding:10px 16px;margin-bottom:4px;font-size:.93rem;color:#0c4a6e'>"
        f"{_period_str}</div>", unsafe_allow_html=True)

    left, right = st.columns([1, 1.4])

    with left:
        st.subheader("Willingness Submission")

        st.write(f"**Designation:** {DESIG_FULL.get(desig2, desig2)}")
        if desig2 not in DESIG_RULES:
            st.error(f"⚠️ Designation code '{desig2}' not recognised. "
                     f"Raw value in DB: '{frow.get('designation', '?')}'. Contact admin.")
            return
        duties_label = str(min_d) if min_d else str(DESIG_RULES.get(desig2,(0,0,[]))[0])
        st.write(f"**Duties to be Allotted:** {duties_label}")
        st.write(f"**Options to Select:** {req_cnt}")

        # Exam date notice (only for faculty with exam dates)
        if fac_exam_dates:
            _exam_rows = "".join(
                f"<li style='margin:3px 0'><b>{d.strftime('%d-%m-%Y (%A)')}</b></li>"
                for d in sorted(fac_exam_dates)
            )
            _buf_dates = fac_blackout_dates - fac_exam_dates
            _buf_rows  = "".join(
                f"<li style='margin:3px 0'>{d.strftime('%d-%m-%Y (%A)')} (buffer)</li>"
                for d in sorted(_buf_dates)
            )
            _buf_note  = (
                f"<div style='font-size:.78rem;color:#b45309;margin-top:4px'>"
                f"📌 Buffer (n−1, n−2 working days before exam) also locked — "
                f"no duty will be assigned: "
                + ", ".join(d.strftime("%d-%m-%Y") for d in sorted(_buf_dates))
                + "</div>"
            ) if _buf_dates else ""
            st.markdown(f"""
<div style="background:#fee2e2;border:2px solid #ef4444;border-radius:12px;
            padding:12px 16px;margin:8px 0 12px 0">
  <div style="font-size:.93rem;font-weight:800;color:#991b1b">
    🚫 Exam Dates — Locked (cannot be selected)
  </div>
  <ul style="font-size:.87rem;color:#7f1d1d;margin:6px 0 2px 16px;padding:0">
    {_exam_rows}
  </ul>
  {_buf_note}
  <div style="font-size:.78rem;color:#b91c1c;margin-top:6px;border-top:1px solid #fca5a5;padding-top:5px">
    ⚠️ You have exams on the above dates. These and their buffer days are excluded from selection and allotment.
  </div>
</div>""", unsafe_allow_html=True)

        # Saturday blocked notice for non-TA/RA designations
        if _sat_blocked_desig and _all_sat_dates:
            _sat_list = " &nbsp;·&nbsp; ".join(
                f"<b>{d.strftime('%d-%m-%Y')}</b>" for d in sorted(_all_sat_dates)
            )
            st.markdown(f"""
<div style="background:#f1f5f9;border:2px solid #94a3b8;border-radius:12px;
            padding:12px 16px;margin:8px 0 12px 0">
  <div style="font-size:.93rem;font-weight:800;color:#334155">
    🚷 Saturday Duties — Not Applicable for Your Designation
  </div>
  <div style="font-size:.83rem;color:#475569;margin-top:5px">
    Saturdays are reserved for TA/RA faculty only.
    The following dates are <b>excluded</b> from your date selector and will not be allotted to you:
  </div>
  <div style="font-size:.82rem;color:#64748b;margin-top:6px;
              border-top:1px solid #cbd5e1;padding-top:6px">
    {_sat_list}
  </div>
</div>""", unsafe_allow_html=True)

        st.markdown("""
<div style="background:#f0f7ff;border:1.5px solid #93c5fd;border-radius:12px;
            padding:14px 16px;margin:8px 0 14px 0">
  <div style="font-size:.88rem;font-weight:800;color:#1e3a5f;margin-bottom:8px">
    ℹ️ How Your Duty Will Be Allotted
  </div>
  <table style="width:100%;margin-top:8px;border-collapse:collapse;font-size:.81rem">
    <tr>
      <td style="padding:4px 8px;width:28px">✅</td>
      <td style="padding:4px 6px;font-weight:700;color:#065f46;width:180px">Exact Match</td>
      <td style="padding:4px 6px;color:#374151">Allotted on the exact date &amp; session you submit</td>
    </tr>
    <tr style="background:#f8fafc">
      <td style="padding:4px 8px">🔄</td>
      <td style="padding:4px 6px;font-weight:700;color:#92400e">Session Adjusted</td>
      <td style="padding:4px 6px;color:#374151">Same date, FN↔AN swapped if needed</td>
    </tr>
    <tr>
      <td style="padding:4px 8px">📅</td>
      <td style="padding:4px 6px;font-weight:700;color:#9a3412">Date Adjusted</td>
      <td style="padding:4px 6px;color:#374151">Shifted ±1 working day from your submitted date</td>
    </tr>
    <tr style="background:#f8fafc">
      <td style="padding:4px 8px">🗓️</td>
      <td style="padding:4px 6px;font-weight:700;color:#5b21b6">Valuation-Adjacent</td>
      <td style="padding:4px 6px;color:#374151">Day before/after your valuation date</td>
    </tr>
    <tr>
      <td style="padding:4px 8px">🔴</td>
      <td style="padding:4px 6px;font-weight:700;color:#991b1b">System-Assigned</td>
      <td style="padding:4px 6px;color:#374151">No match — assigned to meet slot requirements</td>
    </tr>
  </table>
  <div style="font-size:.78rem;color:#64748b;margin-top:10px;border-top:1px solid #bfdbfe;padding-top:8px">
    💡 Submit dates spread across the exam period to maximise your match rate.
    Valuation dates are automatically protected.
  </div>
</div>""", unsafe_allow_html=True)

        if not valid_d:
            st.warning("No dates available for selection.")
        else:
            picked = st.selectbox(
                "Choose Offline Date",
                valid_d, key="picked_date",
                format_func=lambda d: d.strftime("%d-%m-%Y (%A)"))
            avail = set(sopts[sopts["DateOnly"] == picked]["Session"]
                        .dropna().astype(str).str.upper())

            all_will_now   = get_all_willingness()
            any_prob_shown = False
            for sess_opt in ["FN", "AN"]:
                if sess_opt in avail:
                    prob_info = slot_probability(all_will_now, sopts, picked, sess_opt)
                    if prob_info["seats"] > 0:
                        render_prob_bar(prob_info, sess_opt)
                        any_prob_shown = True
            if any_prob_shown:
                st.caption("⚡ Probability = available seats ÷ total applicants for that session.")

            b1, b2 = st.columns(2)
            with b1:
                add_fn = st.button(
                    "➕ Add FN", use_container_width=True,
                    disabled=("FN" not in avail or
                              len(st.session_state.selected_slots) >= req_cnt))
            with b2:
                add_an = st.button(
                    "➕ Add AN", use_container_width=True,
                    disabled=("AN" not in avail or
                              len(st.session_state.selected_slots) >= req_cnt))

            def add_slot(sess):
                exist = {s["Date"] for s in st.session_state.selected_slots}
                sl2   = {"Date": picked, "Session": sess}
                if picked in val_s2:
                    st.warning("Valuation date — cannot select.")
                elif picked in exist:
                    st.warning("Both FN and AN on same date not allowed.")
                elif len(st.session_state.selected_slots) >= req_cnt:
                    st.warning("Count reached.")
                elif sl2 in st.session_state.selected_slots:
                    st.warning("Already selected.")
                else:
                    st.session_state.selected_slots.append(sl2)

            if add_fn: add_slot("FN")
            if add_an: add_slot("AN")

        st.session_state.selected_slots = st.session_state.selected_slots[:req_cnt]
        st.write(f"**Selected:** {len(st.session_state.selected_slots)} / {req_cnt}")

        sdf = pd.DataFrame(st.session_state.selected_slots)
        if not sdf.empty:
            sdf = sdf.sort_values(["Date", "Session"]).reset_index(drop=True)
            sdf.insert(0, "Sl.No", sdf.index + 1)
            sdf["Day"]  = pd.to_datetime(sdf["Date"]).dt.day_name()
            sdf["Date"] = pd.to_datetime(sdf["Date"]).dt.strftime("%d-%m-%Y")
            st.dataframe(sdf[["Sl.No", "Date", "Day", "Session"]],
                         use_container_width=True, hide_index=True)
            rm = st.selectbox("Sl.No to remove", options=sdf["Sl.No"].tolist())
            if st.button("🗑 Remove Row", use_container_width=True):
                tgt = sdf[sdf["Sl.No"] == rm].iloc[0]
                td  = pd.to_datetime(tgt["Date"], dayfirst=True).date()
                ts  = tgt["Session"]
                st.session_state.selected_slots = [
                    s for s in st.session_state.selected_slots
                    if not (s["Date"] == td and s["Session"] == ts)]
                st.rerun()

        is_already = already_submitted(sel_name)
        st.markdown("### Submit Willingness")
        rem2 = max(req_cnt - len(st.session_state.selected_slots), 0)

        if is_already:
            st.warning("⚠ You have already submitted. Submitting again will **replace** your previous choices.")
        if rem2 == 0 and req_cnt > 0:
            st.success(f"✅ All {req_cnt} options selected. Ready to submit.")
        elif not is_already:
            st.info(f"Select {rem2} more option(s) to enable submission.")

        if st.button("✅ Submit Willingness",
                     disabled=(len(st.session_state.selected_slots) != req_cnt),
                     use_container_width=True):
            save_submission(sel_name, st.session_state.selected_slots)
            st.session_state.selected_slots = []
            action = "re-submitted" if is_already else "submitted"
            st.toast(f"Willingness {action} successfully! ✅", icon="✅")
            st.success(
                "Thank you for submitting. The final duty allocation will be carried out "
                "using MILP optimization. Check this portal for allotment updates.")

    with right:
        # All designations see the Offline Duty Calendar this semester
        render_calendar(offline_df, val_s2, "Offline Duty Calendar",
                        exam_dates=fac_exam_dates,
                        buffer_dates=(fac_blackout_dates - fac_exam_dates),
                        sat_blocked_dates=(_all_sat_dates if _sat_blocked_desig else set()))


# ═══════════════════════════════════════════════════════════════ #
#                         MAIN ROUTER                            #
# ═══════════════════════════════════════════════════════════════ #
def main():
    # ── 1. Load faculty + slots from Supabase ────────────────────
    @st.cache_data(ttl=300)
    def _load_fac():
        rows = db_get_all_faculty()
        if not rows:
            st.error("No faculty found in Supabase. Run load_to_supabase.py first.")
            st.stop()
        df = pd.DataFrame(rows)
        df["ID No."]      = df["faculty_id"].astype(str).apply(_norm_id)
        df["Name"]        = df["name"].astype(str).str.strip()
        df["NAME OF STAFF"] = df["Name"]
        df["Designation"] = df["designation"].astype(str).apply(_map_desig)
        # Apply per-faculty overrides (handles NULL/blank Supabase values)
        for _i, _r in df.iterrows():
            _fc = clean(_r["Name"])
            if _fc in FACULTY_DESIG_OVERRIDE:
                df.at[_i, "Designation"] = FACULTY_DESIG_OVERRIDE[_fc]
        df["Clean"]       = df["Name"].apply(clean)
        for col in ["v1","v2","v3","v4","v5"]:
            cap = col.upper()
            df[cap] = pd.to_datetime(df[col], errors="coerce") if col in df.columns else pd.NaT
        return df

    fac_df = _load_fac()
    offline_df, online_df = load_slots(OFFLINE_FILE, ONLINE_FILE)

    # ── 2. Login gate ─────────────────────────────────────────────
    if not st.session_state.logged_in:
        page_login(fac_df)
        return

    # ── 3. Force password change ──────────────────────────────────
    if st.session_state.must_change_pw:
        page_force_change_password()
        return

    # ── 4. Header + notice banner ─────────────────────────────────
    render_header(logo=False)
    st.markdown(
        "<div class='blink'><strong>Note:</strong> The University Examination Committee "
        "sincerely appreciates your cooperation. Every effort will be made to accommodate "
        "your willingness. Final duty allocation is carried out using AI-assisted MILP "
        "optimization.</div>", unsafe_allow_html=True)
    st.markdown("")

    # ── 5. Welcome row + logout ───────────────────────────────────
    col_title, col_logout = st.columns([6, 1])
    with col_logout:
        if st.button("🚪 Logout"):
            for k in ["logged_in", "faculty_id", "faculty_name", "faculty_clean",
                      "is_admin", "must_change_pw", "selected_slots", "selected_faculty"]:
                st.session_state[k] = (
                    [] if k == "selected_slots"
                    else (False if k not in ("faculty_id", "faculty_name", "faculty_clean") else ""))
            st.rerun()
    with col_title:
        fid_disp  = st.session_state.faculty_id
        name_disp = st.session_state.faculty_name
        is_admin  = st.session_state.is_admin
        badge     = " 👑 Admin" if is_admin else ""
        st.markdown(
            f"**Welcome, {name_disp}** &nbsp; <span style='color:#64748b;font-size:.88rem'>"
            f"({fid_disp})</span>{badge}",
            unsafe_allow_html=True)

    # ── 6. Main panel routing ─────────────────────────────────────
    if is_admin:
        menu = st.radio("Main Menu", ["User View", "Admin View"],
                        horizontal=True, key="panel_mode")
        if menu == "Admin View":
            page_admin(fac_df, offline_df, online_df)
            st.markdown("---")
            st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
            return

    # ── 7. User view panel ────────────────────────────────────────
    sub = st.radio("View", ["Willingness", "My Allotment", "Change Password"],
                   horizontal=True, key="user_panel_mode")

    sel_name  = st.session_state.faculty_name
    sel_clean = st.session_state.faculty_clean
    fmatch    = fac_df[fac_df["Clean"] == sel_clean]

    if fmatch.empty:
        st.error("Your faculty record was not found. Contact admin.")
        st.stop()

    frow = fmatch.iloc[0]

    if sub == "My Allotment":
        page_allotment(fac_df, sel_name, sel_clean, frow, offline_df, online_df)
    elif sub == "Change Password":
        section_change_password()
    else:
        page_willingness(fac_df, offline_df, online_df, sel_name, frow)

    st.markdown("---")
    st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")


main()
