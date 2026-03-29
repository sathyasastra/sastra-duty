"""
SASTRA SoME End Semester Examination Duty Portal
=================================================
Backend  : Supabase (PostgreSQL)
Auth     : Faculty ID + bcrypt/SHA-256 password (stored in faculty table)
Deploy   : Streamlit Cloud — no local files needed

Supabase tables required (run setup_supabase_final.sql once):
  faculty           — id, faculty_id, name, designation, password_hash,
                       must_change_pw, is_admin, v1..v5, qp_date_1, qp_date_2
  offline_duty      — id, duty_date, session, required
  online_duty       — id, duty_date, session, required
  willingness       — id, faculty_id, faculty_name, duty_date, session, submitted_at
  final_allocation  — id, faculty_id, faculty_name, duty_date, session, type, allocated_by
  portal_settings   — key, value  (stores gate open/closed and semester override)

v6 — Full Supabase backend | ID login | bcrypt | MILP + Greedy + CP-SAT optimizer
"""

import io
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

logging.getLogger("streamlit").setLevel(logging.ERROR)
warnings.filterwarnings("ignore")

# ── Optional heavy deps ───────────────────────────────────────── #
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

# ── Supabase ──────────────────────────────────────────────────── #
from supabase import create_client, Client

SUPABASE_URL = "https://gjezjvlzgsenedjsgmxx.supabase.co"
SUPABASE_KEY = "sb_publishable_ieyOcCgGt2qlacbfEVTLZA_nVHpwbNb"
LOGO_FILE    = "sastra_logo.png"

@st.cache_resource
def get_sb() -> Client:
    return create_client(SUPABASE_URL, SUPABASE_KEY)

# ── Constants ─────────────────────────────────────────────────── #
DEFAULT_PASSWORD = "sastra"
ADMIN_IDS        = {"C2086"}   # always admin — add more IDs as needed

DESIG_MAP = {
    "professor": "P", "acp": "ACP", "sap": "SAP",
    "ap 3": "AP3", "ap3": "AP3", "ap 2": "AP2", "ap2": "AP2",
    "teaching assistant": "TA", "ta": "TA",
    "research assistant": "RA", "ra": "RA",
}
DESIG_RULES = {
    "P":   (1, 1, ["Online"]),
    "ACP": (2, 2, ["Online", "Offline"]),
    "SAP": (3, 3, ["Offline"]),
    "AP3": (3, 3, ["Offline"]),
    "AP2": (3, 3, ["Offline"]),
    "TA":  (3, 3, ["Offline"]),
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
DUTY_STRUCTURE = {"P": 3, "ACP": 5, "SAP": 7, "AP3": 7, "AP2": 7, "TA": 9, "RA": 9}

W_EXACT = 100_000; W_ACP_ONLINE = 80_000; W_FLIP = 60_000
W_ADJ1  =  40_000; W_ADJ2       = 20_000; W_VAL_ADJ = 5_000
W_NON_SUB = 100;   PENALTY = 10

DESIG_PRIORITY = {
    "P": 6_000_000, "ACP": 5_000_000, "SAP": 4_000_000,
    "AP3": 3_000_000, "AP2": 2_000_000, "TA": 0, "RA": 0,
}
WILL_TAGS = {
    "Willingness-Exact", "Willingness-ACPOnline", "Willingness-SessionFlip",
    "Willingness-±1Day", "Willingness-±2Day", "Willingness-ValAdj", "SAP-OnlineFallback",
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
#                    SUPABASE DATA HELPERS                       #
# ═══════════════════════════════════════════════════════════════ #

@st.cache_data(ttl=120)
def db_get_all_faculty():
    sb = get_sb()
    res = sb.table("faculty").select("*").order("name").execute()
    return res.data or []

@st.cache_data(ttl=300)
def db_get_offline_duty():
    sb = get_sb()
    res = sb.table("offline_duty").select("*").execute()
    rows = res.data or []
    if not rows:
        return pd.DataFrame(columns=["Date","Session","Required"])
    df = pd.DataFrame(rows)
    df.rename(columns={"duty_date":"Date","session":"Session","required":"Required"}, inplace=True)
    df["Date"]     = pd.to_datetime(df["Date"], errors="coerce")
    df["Session"]  = df["Session"].apply(normalize_session)
    df["Required"] = pd.to_numeric(df["Required"], errors="coerce").fillna(1).astype(int)
    return df[["Date","Session","Required"]]

@st.cache_data(ttl=300)
def db_get_online_duty():
    sb = get_sb()
    res = sb.table("online_duty").select("*").execute()
    rows = res.data or []
    if not rows:
        return pd.DataFrame(columns=["Date","Session","Required"])
    df = pd.DataFrame(rows)
    df.rename(columns={"duty_date":"Date","session":"Session","required":"Required"}, inplace=True)
    df["Date"]     = pd.to_datetime(df["Date"], errors="coerce")
    df["Session"]  = df["Session"].apply(normalize_session)
    df["Required"] = pd.to_numeric(df["Required"], errors="coerce").fillna(1).astype(int)
    return df[["Date","Session","Required"]]

def db_get_faculty_by_id(fid: str):
    sb = get_sb()
    fid = _norm_id(fid)
    res = sb.table("faculty").select("*").eq("faculty_id", fid).execute()
    return res.data[0] if res.data else None

def db_update_password(fid: str, new_hash: str, must_change: bool = False):
    sb = get_sb()
    sb.table("faculty").update({
        "password_hash": new_hash,
        "must_change_pw": must_change,
    }).eq("faculty_id", _norm_id(fid)).execute()
    db_get_all_faculty.clear()

def db_set_admin(fid: str, is_admin: bool):
    sb = get_sb()
    sb.table("faculty").update({"is_admin": is_admin}).eq("faculty_id", _norm_id(fid)).execute()
    db_get_all_faculty.clear()

def db_reset_password(fid: str):
    db_update_password(fid, hash_password(DEFAULT_PASSWORD), must_change=True)

def db_get_all_willingness():
    sb = get_sb()
    res = sb.table("willingness").select("*").order("faculty_name").execute()
    return res.data or []

def db_get_willingness_for(fid: str):
    sb = get_sb()
    res = sb.table("willingness").select("*").eq("faculty_id", _norm_id(fid)).execute()
    return res.data or []

def db_already_submitted(fid: str) -> bool:
    sb = get_sb()
    res = sb.table("willingness").select("id").eq("faculty_id", _norm_id(fid)).execute()
    return bool(res.data)

def db_submit_willingness(fid: str, faculty_name: str, slots: list):
    sb = get_sb()
    fid = _norm_id(fid)
    sb.table("willingness").delete().eq("faculty_id", fid).execute()
    rows = [{"faculty_id": fid, "faculty_name": faculty_name,
             "duty_date": s["Date"].strftime("%Y-%m-%d"), "session": s["Session"]}
            for s in slots]
    if rows:
        sb.table("willingness").insert(rows).execute()

def db_delete_all_willingness():
    sb = get_sb()
    sb.table("willingness").delete().neq("id", 0).execute()

def db_get_allotment_for(fid: str):
    sb = get_sb()
    res = sb.table("final_allocation").select("*").eq("faculty_id", _norm_id(fid)).execute()
    return res.data or []

def db_get_all_allotment():
    sb = get_sb()
    res = sb.table("final_allocation").select("*").order("duty_date").execute()
    return res.data or []

def db_save_allotment(records: list):
    sb = get_sb()
    sb.table("final_allocation").delete().neq("id", 0).execute()
    if records:
        sb.table("final_allocation").insert(records).execute()

def db_get_setting(key: str, default=""):
    sb = get_sb()
    try:
        res = sb.table("portal_settings").select("value").eq("key", key).execute()
        return res.data[0]["value"] if res.data else default
    except Exception:
        return default

def db_set_setting(key: str, value: str):
    sb = get_sb()
    try:
        existing = sb.table("portal_settings").select("id").eq("key", key).execute()
        if existing.data:
            sb.table("portal_settings").update({"value": value}).eq("key", key).execute()
        else:
            sb.table("portal_settings").insert({"key": key, "value": value}).execute()
    except Exception:
        pass


# ═══════════════════════════════════════════════════════════════ #
#                    PORTAL SETTINGS (gate)                      #
# ═══════════════════════════════════════════════════════════════ #
def gate_is_open() -> bool:
    return db_get_setting("gate", "0") == "1"

def set_gate(open_: bool):
    db_set_setting("gate", "1" if open_ else "0")


# ═══════════════════════════════════════════════════════════════ #
#              PASSWORD HELPERS                                   #
# ═══════════════════════════════════════════════════════════════ #
def _norm_id(fid: str) -> str:
    return str(fid).strip().upper().replace(" ", "")

def hash_password(plain: str) -> str:
    if BCRYPT_OK:
        return bcrypt.hashpw(plain.encode(), bcrypt.gensalt()).decode()
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
#                     UTILITY FUNCTIONS                          #
# ═══════════════════════════════════════════════════════════════ #
def clean(x):
    return str(x).strip().lower()

def normalize_session(v):
    t = str(v).strip().upper()
    if t in {"FN","FORENOON","MORNING","AM"}: return "FN"
    if t in {"AN","AFTERNOON","EVENING","PM"}: return "AN"
    return t

def parse_date_safe(val):
    if val is None: return pd.NaT
    if isinstance(val, pd.Timestamp): return val
    if isinstance(val, (datetime.datetime, datetime.date)): return pd.Timestamp(val)
    s = str(val).strip()
    for fmt in ("%Y-%m-%d","%d-%m-%Y","%d/%m/%Y","%d-%m-%y"):
        try: return pd.to_datetime(s, format=fmt)
        except: pass
    return pd.to_datetime(s, dayfirst=True, errors="coerce")

def fmt_day(val):
    dt = parse_date_safe(val)
    return f"{dt.strftime('%d-%m-%Y')} ({dt.strftime('%A')})" if pd.notna(dt) else str(val)

def valuation_dates_for_row(frow: dict):
    dates = []
    for col in ["v1","v2","v3","v4","v5"]:
        val = frow.get(col)
        if val:
            ts = parse_date_safe(val)
            if pd.notna(ts): dates.append(ts.date())
    return sorted(set(dates))

def qp_dates_for_row(frow: dict):
    dates = []
    for col in ["qp_date_1","qp_date_2"]:
        val = frow.get(col)
        if val:
            ts = parse_date_safe(val)
            if pd.notna(ts): dates.append(ts.strftime("%d-%m-%Y"))
    return sorted(set(dates))

def wa_link(phone, msg):
    p = str(phone).strip().replace("+","").replace(" ","").replace("-","")
    return f"https://wa.me/{p}?text={urllib.parse.quote(msg)}"

def detect_semester(slot_dates=None):
    override = st.session_state.get("semester_override") or db_get_setting("semester", "")
    if override and override != "Auto-detect":
        return override
    now = datetime.date.today()
    if slot_dates:
        months = {d.month for d in slot_dates if hasattr(d, "month")}
        if months & {5,6}: return "Even Semester (Apr/May End-Semester)"
        if months & {11,12,1}: return "Odd Semester (Nov/Dec End-Semester)"
    if now.month in (4,5,6): return "Even Semester (Apr/May End-Semester)"
    if now.month in (11,12,1): return "Odd Semester (Nov/Dec End-Semester)"
    return "End-Semester Examination"

def get_exam_period(slot_dates):
    if not slot_dates: return None, None
    sd = sorted(d for d in slot_dates if d is not None)
    return (sd[0], sd[-1]) if sd else (None, None)

def render_header(logo=True):
    import os
    if logo and os.path.exists(LOGO_FILE):
        _, c2, _ = st.columns([2,1,2])
        with c2: st.image(LOGO_FILE, width=180)
    st.markdown("<h2 style='text-align:center;margin-bottom:.25rem'>"
                "SASTRA SoME End Semester Examination Duty Portal</h2>", unsafe_allow_html=True)
    st.markdown("<h4 style='text-align:center;margin-top:0'>"
                "School of Mechanical Engineering</h4>", unsafe_allow_html=True)
    st.markdown("---")

def fac_df_from_db() -> pd.DataFrame:
    """Convert Supabase faculty rows to a DataFrame matching legacy expectations."""
    rows = db_get_all_faculty()
    if not rows:
        return pd.DataFrame(columns=["faculty_id","Name","Designation","Clean"])
    df = pd.DataFrame(rows)
    df.rename(columns={"name":"Name","designation":"Designation"}, inplace=True)
    df["Designation"] = df["Designation"].apply(
        lambda x: DESIG_MAP.get(str(x).strip().lower(), str(x).strip().upper()))
    df["Clean"] = df["Name"].apply(clean)
    return df


# ═══════════════════════════════════════════════════════════════ #
#                    WILLINGNESS HELPERS                         #
# ═══════════════════════════════════════════════════════════════ #
def get_all_willingness_df() -> pd.DataFrame:
    """All committed willingness from Supabase as a tidy DataFrame."""
    rows = db_get_all_willingness()
    if not rows:
        return pd.DataFrame(columns=["Faculty","Date","Session","FacultyClean"])
    df = pd.DataFrame(rows)
    df.rename(columns={"faculty_name":"Faculty","duty_date":"Date","session":"Session"}, inplace=True)
    df["Faculty"]      = df["Faculty"].astype(str).str.strip()
    df["Date"]         = df["Date"].astype(str).str.strip()
    df["Session"]      = df["Session"].astype(str).str.strip().str.upper()
    df["FacultyClean"] = df["Faculty"].apply(clean)
    return df

def slot_probability(offline_df, online_df, des: str, date_val, session_val: str):
    duty_df = online_df if des == "P" else offline_df
    seats = 0
    if not duty_df.empty:
        m = duty_df[(duty_df["Date"].dt.date == date_val) &
                    (duty_df["Session"].str.upper() == session_val.upper())]
        if not m.empty:
            seats = int(m["Required"].sum())

    all_will = get_all_willingness_df()
    applicants = 0
    if not all_will.empty and "Date" in all_will.columns:
        norm = pd.to_datetime(all_will["Date"], dayfirst=True, errors="coerce")
        applicants = int(((norm.dt.date == date_val) &
                          (all_will["Session"].str.upper() == session_val.upper())).sum())

    if seats == 0:
        return {"seats":0,"applicants":applicants,"probability":0.0,"label":"No slot","colour":"#94a3b8"}
    if applicants == 0:
        return {"seats":seats,"applicants":0,"probability":100.0,"label":"High — first!","colour":"#16a34a"}
    prob = min(seats/applicants,1.0)*100
    if prob >= 70:   label,colour = "High","#16a34a"
    elif prob >= 40: label,colour = "Medium","#f59e0b"
    else:            label,colour = "Low — many applicants","#dc2626"
    return {"seats":seats,"applicants":applicants,"probability":prob,"label":label,"colour":colour}

def render_prob_bar(info: dict, session_label: str):
    pct=info["probability"]; colour=info["colour"]
    st.markdown(f"""
<div style="background:#fff;border:1px solid #e2e8f0;border-radius:10px;padding:10px 14px;margin-bottom:8px;">
  <div style="font-weight:700;font-size:.95rem;color:#0f172a;margin-bottom:4px;">
    {session_label} &nbsp;·&nbsp; <span style="color:{colour}">{pct:.0f}% allocation probability</span>
  </div>
  <div style="background:#e5e7eb;border-radius:6px;height:12px;width:100%;margin:4px 0">
    <div style="background:{colour};border-radius:6px;height:12px;width:{pct:.0f}%"></div>
  </div>
  <div style="font-size:.82rem;color:#475569;margin-top:3px;">
    🎯 Seats: <b>{info['seats']}</b> &nbsp;|&nbsp;
    👥 Applied so far: <b>{info['applicants']}</b> &nbsp;|&nbsp; {info['label']}
  </div>
</div>""", unsafe_allow_html=True)


# ═══════════════════════════════════════════════════════════════ #
#                    CALENDAR HEATMAP                            #
# ═══════════════════════════════════════════════════════════════ #
def render_calendar(duty_df, val_dates, title):
    st.markdown(f"#### {title}")
    if duty_df.empty:
        st.info("No slot data available.")
        return

    slot_day_set = set(duty_df["Date"].dt.date)
    if not slot_day_set: return
    first_slot = min(slot_day_set); last_slot = max(slot_day_set)
    months = sorted({(d.year,d.month) for d in duty_df["Date"]})
    sg = duty_df.groupby(["Date","Session"],as_index=False)["Required"].sum()
    duty_map = {(row["Date"].date(), str(row["Session"]).upper()): int(row["Required"])
                for _,row in sg.iterrows()}
    val_set = set(val_dates)
    WD_ORDER = ["Mon","Tue","Wed","Thu","Fri","Sat","Sun"]

    st.markdown(
        "<span style='font-size:.82rem'>"
        "<span style='background:#fce7f3;border:1px solid #f9a8d4;border-radius:4px;"
        "padding:2px 8px;margin-right:6px'>🩷 Valuation Locked</span>"
        "<span style='background:#fff;border:1px solid #cbd5e1;border-radius:4px;"
        "padding:2px 8px'>🔢 Number = duties required</span>"
        "</span>", unsafe_allow_html=True)

    for yr,mo in months:
        ms = pd.Timestamp(year=yr,month=mo,day=1)
        me = ms + pd.offsets.MonthEnd(0)
        days = pd.date_range(ms,me,freq="D")
        fw = ms.weekday()
        grid=[]; week=[None]*fw
        for dt in days:
            dt_date = dt.date()
            cell = dt_date if (first_slot<=dt_date<=last_slot) else None
            week.append(cell)
            if len(week)==7: grid.append(week); week=[]
        if week:
            week+=[None]*(7-len(week)); grid.append(week)
        grid=[w for w in grid if any(d is not None for d in w)]

        st.markdown(f"<div style='font-size:.95rem;font-weight:700;color:#1e3a5f;"
                    f"margin:14px 0 4px 0'>{calmod.month_name[mo]} {yr}</div>",
                    unsafe_allow_html=True)

        TH_DAY  = "background:#1e3a5f;color:#fff;font-size:.8rem;font-weight:700;text-align:center;padding:7px 4px;border:1px solid #2d4f7c;"
        TH_SESS = "background:#dbeafe;color:#1e40af;font-size:.7rem;font-weight:700;text-align:center;padding:4px 2px;border:1px solid #bfdbfe;width:44px;"
        TD_BASE = "text-align:center;padding:5px 2px;border:1px solid #e2e8f0;vertical-align:middle;min-width:44px;"

        hdr1 = "".join(f"<th colspan='2' style='{TH_DAY}'>{wd}</th>" for wd in WD_ORDER)
        hdr2 = "".join(f"<th style='{TH_SESS}'>FN</th><th style='{TH_SESS}'>AN</th>" for _ in WD_ORDER)
        rows_html = ""
        for week_dates in grid:
            date_row = ""
            for dt in week_dates:
                if dt is None:
                    date_row += "<td colspan='2' style='background:#fff;border:1px solid #e2e8f0;height:20px'></td>"
                else:
                    is_val=dt in val_set; is_sun=dt.weekday()==6
                    bg="#fce7f3" if is_val else "#fff"
                    color="#be185d" if is_val else ("#94a3b8" if is_sun else "#0f172a")
                    label=f"{dt.day}"+(" 🔒" if is_val else "")
                    date_row+=(f"<td colspan='2' style='background:{bg};border:1px solid #e2e8f0;"
                               f"text-align:center;padding:4px 2px 2px 2px;vertical-align:middle'>"
                               f"<span style='font-size:.88rem;font-weight:800;color:{color}'>{label}</span></td>")
            rows_html+=f"<tr>{date_row}</tr>"
            duty_row=""
            for dt in week_dates:
                if dt is None:
                    duty_row+="<td style='background:#fff;border:1px solid #e2e8f0;min-width:44px;height:24px'></td>"*2
                else:
                    is_val=dt in val_set
                    for sess in ["FN","AN"]:
                        req=duty_map.get((dt,sess),0)
                        if is_val: bg,content="#fce7f3",""
                        elif req==0: bg,content="#fff",""
                        else:
                            bg="#fff"
                            content=f"<span style='font-size:.72rem;font-style:italic;font-weight:700;color:#2563eb'>{req}</span>"
                        duty_row+=f"<td style='{TD_BASE}background:{bg}'>{content}</td>"
            rows_html+=f"<tr>{duty_row}</tr>"

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
#                   DEVIATION ANALYSIS                           #
# ═══════════════════════════════════════════════════════════════ #
def classify_duty(alloc_by, duty_date, duty_sess, will_set):
    ab = str(alloc_by).strip()
    if ab=="Willingness-Exact":
        return ("Exact Match","✅","Allotted on exact date & session submitted",True)
    if ab=="Willingness-ACPOnline":
        return ("Session Adjusted","🔄","Offline-date willingness used for online duty slot",True)
    if ab=="Willingness-SessionFlip":
        opp="AN" if duty_sess=="FN" else "FN"
        return ("Session Adjusted","🔄",f"Submitted {duty_date.strftime('%d-%m-%Y')} {opp} → allotted {duty_sess}",True)
    if ab=="Willingness-±1Day":
        return ("Date Adjusted (±1 day)","📅","Allotted 1 working day from submitted willingness",True)
    if ab=="Willingness-±2Day":
        return ("Date Adjusted (±2 days)","📆","Allotted 2 working days from submitted willingness",True)
    if ab=="SAP-OnlineFallback":
        return ("SAP Online Fallback","🔁","SAP assigned to online slot as fallback",True)
    if ab=="Willingness-ValAdj":
        return ("Valuation-Adjacent","🗓️",f"Allotted on weekday adjacent to valuation date",True)
    if ab in ("Auto-Assigned","Gap-Fill") or ab.startswith("Gap-Fill"):
        return ("Auto-Assigned","⚙️","No willingness — system assigned to meet slot requirements",False)
    return ("Not in Willingness","🔴",f"No match near {duty_date.strftime('%d-%m-%Y')} {duty_sess}",False)

def render_deviation_section(allot_rows: pd.DataFrame, will_set: set):
    if allot_rows.empty:
        st.info("No allotment data found for this faculty yet.")
        return "Not available", []
    duty_rows=[]
    for _,ar in allot_rows.iterrows():
        norm=parse_date_safe(ar["duty_date"] if "duty_date" in ar.index else ar.get("Date",""))
        if pd.isna(norm): continue
        sess=str(ar.get("session",ar.get("Session",""))).strip().upper()
        dtype=str(ar.get("type",ar.get("Type",""))).strip()
        alloc_by=str(ar.get("allocated_by",ar.get("Allocated_By",""))).strip()
        status,emoji,detail,is_matched=classify_duty(alloc_by,norm.date(),sess,will_set)
        duty_rows.append({"norm_date":norm.date(),"sess":sess,"dtype":dtype,
                          "status":status,"emoji":emoji,"detail":detail,"is_matched":is_matched,
                          "date_fmt":fmt_day(norm)})

    total=len(duty_rows)
    n_exact=sum(1 for d in duty_rows if d["status"]=="Exact Match")
    n_sess=sum(1 for d in duty_rows if d["status"]=="Session Adjusted")
    n_adj1=sum(1 for d in duty_rows if d["status"]=="Date Adjusted (±1 day)")
    n_adj2=sum(1 for d in duty_rows if d["status"]=="Date Adjusted (±2 days)")
    n_valadj=sum(1 for d in duty_rows if d["status"]=="Valuation-Adjacent")
    n_no=sum(1 for d in duty_rows if not d["is_matched"])
    n_matched=n_exact+n_sess+n_adj1+n_adj2+n_valadj
    match_pct=n_matched/total*100 if total else 0.0

    st.markdown("### 📊 Willingness Match & Deviation")
    m1,m2,m3,m4=st.columns(4)
    with m1: st.metric("Duties Allotted",total)
    with m2: st.metric("Willingness Match",f"{match_pct:.1f}%",delta=f"{n_matched}/{total} within window")
    with m3: st.metric("Deviation",f"{100-match_pct:.1f}%",
                       delta=f"{n_no} unmatched" if n_no else "None",
                       delta_color="inverse" if n_no else "off")
    allot_set={(d["norm_date"],d["sess"]) for d in duty_rows}
    exact_ov=len(will_set&allot_set)
    with m4: st.metric("Exact Slots Used",f"{exact_ov/len(will_set)*100:.1f}%" if will_set else "N/A")

    STATUS_BG={
        "Exact Match":("#d1fae5","#065f46"),
        "Session Adjusted":("#fef3c7","#92400e"),
        "Date Adjusted (±1 day)":("#ffedd5","#9a3412"),
        "Date Adjusted (±2 days)":("#ffe4e6","#881337"),
        "Valuation-Adjacent":("#ede9fe","#5b21b6"),
        "Not in Willingness":("#fee2e2","#991b1b"),
        "Auto-Assigned":("#e5e7eb","#374151"),
    }
    rows_html=""
    for d in duty_rows:
        bg,fg=STATUS_BG.get(d["status"],("#e5e7eb","#374151"))
        rows_html+=(f"<tr><td style='padding:7px 10px;font-size:.87rem'>{d['date_fmt']}</td>"
                    f"<td style='padding:7px 10px;text-align:center;font-weight:700'>{d['sess']}</td>"
                    f"<td style='padding:7px 10px;text-align:center'>{d['dtype']}</td>"
                    f"<td style='padding:7px 10px'><span style='display:inline-block;padding:2px 10px;"
                    f"border-radius:12px;font-size:.8rem;font-weight:700;background:{bg};color:{fg}'>"
                    f"{d['emoji']} {d['status']}</span></td>"
                    f"<td style='padding:7px 10px;font-size:.82rem;color:#475569'>{d['detail']}</td></tr>")

    st.markdown(f"""<div style="overflow-x:auto"><table style="width:100%;border-collapse:collapse;
background:#fff;border-radius:10px;overflow:hidden;box-shadow:0 2px 8px rgba(0,0,0,.06)">
<thead><tr style="background:#f1f5f9;font-size:.85rem;font-weight:700;color:#0f172a;">
<th style="padding:8px 10px;text-align:left">Allotted Date</th>
<th style="padding:8px 10px;text-align:center">Session</th>
<th style="padding:8px 10px;text-align:center">Type</th>
<th style="padding:8px 10px;text-align:left">Match Status</th>
<th style="padding:8px 10px;text-align:left">Detail</th>
</tr></thead><tbody>{rows_html}</tbody></table></div>""", unsafe_allow_html=True)

    dev_lines=[f"Overall match: {match_pct:.1f}% ({n_matched}/{total})"]
    if n_exact>0:  dev_lines.append(f"  ✅ Exact: {n_exact}")
    if n_sess>0:   dev_lines.append(f"  🔄 Session flip: {n_sess}")
    if n_adj1>0:   dev_lines.append(f"  📅 ±1 day: {n_adj1}")
    if n_adj2>0:   dev_lines.append(f"  📆 ±2 days: {n_adj2}")
    if n_valadj>0: dev_lines.append(f"  🗓️ Val-adjacent: {n_valadj}")
    if n_no>0:     dev_lines.append(f"  🔴 System-assigned: {n_no}")
    return f"Match {match_pct:.1f}% ({n_matched}/{total})", dev_lines


# ═══════════════════════════════════════════════════════════════ #
#                      OPTIMIZER                                 #
# ═══════════════════════════════════════════════════════════════ #
def _slots_from_db(offline_df, online_df):
    """Convert offline/online DataFrames → list of slot dicts for optimizer."""
    slots = []
    for _, row in offline_df.iterrows():
        if pd.isna(row["Date"]): continue
        slots.append({"date":row["Date"].date(),"session":str(row["Session"]).upper(),
                      "required":int(row["Required"]),"type":"Offline"})
    for _, row in online_df.iterrows():
        if pd.isna(row["Date"]): continue
        slots.append({"date":row["Date"].date(),"session":str(row["Session"]).upper(),
                      "required":int(row["Required"]),"type":"Online"})
    return slots

def _load_core(log, offline_df, online_df):
    if not SCIPY_OK:
        raise RuntimeError("scipy not installed — run: pip install scipy")

    all_fac_rows = db_get_all_faculty()
    if not all_fac_rows:
        raise RuntimeError("No faculty found in Supabase. Run seed SQL first.")

    # Build faculty structures
    ALL_FAC, FAC_IDX, fac_d, fac_val = [], {}, {}, {}
    dgroups = defaultdict(list)
    for r in all_fac_rows:
        n   = str(r["name"]).strip()
        raw = str(r.get("designation","TA")).strip()
        d   = DESIG_MAP.get(raw.lower(), raw.upper())
        if d not in DESIG_RULES: d = "TA"
        ALL_FAC.append(n)
        FAC_IDX[n] = len(ALL_FAC)-1
        fac_d[n]   = d
        dgroups[d].append(n)
        vd = set()
        for c in ["v1","v2","v3","v4","v5"]:
            if r.get(c):
                try: vd.add(parse_date_safe(r[c]).date())
                except: pass
        fac_val[n] = vd

    N_FAC = len(ALL_FAC)
    ALL_S = _slots_from_db(offline_df, online_df)
    NS    = len(ALL_S)
    slot_dates = {s["date"] for s in ALL_S}

    # Willingness
    wdf = get_all_willingness_df().drop(columns=["FacultyClean"],errors="ignore")
    if not wdf.empty:
        wdf["Date"]    = pd.to_datetime(wdf["Date"], dayfirst=True, errors="coerce")
        wdf["Session"] = wdf["Session"].str.upper()
        wdf = wdf.dropna(subset=["Date"])
    submitted  = set(wdf["Faculty"].str.strip().unique()) if not wdf.empty else set()
    non_sub    = [n for n in ALL_FAC if n not in submitted]
    sub_counts = {}
    if not wdf.empty:
        for n,grp in wdf.groupby("Faculty"):
            sub_counts[n.strip()] = len(grp)

    log(f"  Faculty: {N_FAC} | Slots: {NS} ({sum(1 for s in ALL_S if s['type']=='Offline')} off + {sum(1 for s in ALL_S if s['type']=='Online')} on)")
    log(f"  Seats needed: {sum(s['required'] for s in ALL_S)}")
    log(f"  Willingness: {len(submitted)} submitted | {len(non_sub)} not submitted")

    SAT_DESIG    = {"TA","RA"}
    sap_faculty  = [n for n in ALL_FAC if fac_d.get(n)=="SAP"]
    sap_fallback = sap_faculty[:2]
    acp_faculty  = [n for n in ALL_FAC if fac_d.get(n)=="ACP"]
    acp_2online  = set(acp_faculty[:2])
    acp_2offline = set(acp_faculty[-2:])

    # Score expansion
    fexp = defaultdict(dict)
    def sset(d,k,val): d[k]=max(d.get(k,0),val)
    def next_biz(d, steps):
        step=1 if steps>0 else -1; cur=d; cnt=0
        while cnt<abs(steps):
            cur+=datetime.timedelta(days=step)
            if cur.weekday()<5: cnt+=1
        return cur

    for _,row in wdf.iterrows():
        n=str(row.get("Faculty","")).strip()
        if n not in FAC_IDX: continue
        dt2=row["Date"].date(); sess=str(row["Session"]).upper(); opp="AN" if sess=="FN" else "FN"
        allowed=DESIG_RULES[fac_d.get(n,"TA")][2]
        for tp in allowed: sset(fexp[n],(dt2,sess,tp),W_EXACT)
        if fac_d.get(n)=="ACP":
            for s2 in ["FN","AN"]: sset(fexp[n],(dt2,s2,"Online"),W_ACP_ONLINE)
            for direction in [+1,-1]:
                adj=next_biz(dt2,direction)
                if adj in slot_dates:
                    for s2 in ["FN","AN"]: sset(fexp[n],(adj,s2,"Online"),W_ACP_ONLINE-5_000)
        for tp in allowed: sset(fexp[n],(dt2,opp,tp),W_FLIP)
        for direction in [+1,-1]:
            adj=next_biz(dt2,direction)
            if adj not in slot_dates: continue
            for s2 in ["FN","AN"]:
                for tp in allowed: sset(fexp[n],(adj,s2,tp),W_ADJ1)
        for direction in [+2,-2]:
            adj=next_biz(dt2,direction)
            if adj not in slot_dates: continue
            for s2 in ["FN","AN"]:
                for tp in allowed: sset(fexp[n],(adj,s2,tp),W_ADJ2)

    for n in ALL_FAC:
        allowed=DESIG_RULES[fac_d.get(n,"TA")][2]
        for vd in fac_val.get(n,set()):
            for direction in [+1,-1]:
                adj=next_biz(vd,direction)
                if adj not in slot_dates: continue
                for s2 in ["FN","AN"]:
                    for tp in allowed:
                        k=(adj,s2,tp)
                        if fexp[n].get(k,0)<W_VAL_ADJ: sset(fexp[n],k,W_VAL_ADJ)

    for n in non_sub:
        allowed=DESIG_RULES[fac_d.get(n,"TA")][2]
        for s in ALL_S:
            if s["type"] in allowed: sset(fexp[n],(s["date"],s["session"],s["type"]),W_NON_SUB)

    for n in ALL_FAC:
        if fac_d.get(n)=="ACP":
            for s in ALL_S:
                if s["type"]=="Online":
                    k=(s["date"],s["session"],"Online")
                    if fexp[n].get(k,0)==0: sset(fexp[n],k,1_000)

    for n in sap_fallback:
        for s in ALL_S:
            if s["type"]=="Online":
                k=(s["date"],s["session"],"Online")
                if fexp[n].get(k,0)==0: sset(fexp[n],k,500)

    def tag(fn,k,sc):
        if fn in non_sub:       return "Auto-Assigned"
        if sc>=W_EXACT:         return "Willingness-Exact"
        if sc>=W_ACP_ONLINE:    return "Willingness-ACPOnline"
        if sc>=W_FLIP:          return "Willingness-SessionFlip"
        if sc>=W_ADJ1:          return "Willingness-±1Day"
        if sc>=W_ADJ2:          return "Willingness-±2Day"
        if sc>=W_VAL_ADJ:       return "Willingness-ValAdj"
        if fn in sap_fallback:  return "SAP-OnlineFallback"
        return "OR-Assigned"

    def is_eligible(fn,sl):
        d2=fac_d.get(fn,"TA"); allowed=DESIG_RULES[d2][2]
        eff=list(allowed)+(["Online"] if fn in sap_fallback else [])
        if sl["type"] not in eff: return False
        if sl["type"]=="Offline" and sl["date"] in fac_val.get(fn,set()): return False
        if sl["type"]=="Offline" and sl["date"].weekday()==5 and d2 not in SAT_DESIG: return False
        if sl["type"]=="Online"  and sl["date"].weekday()==5 and d2 not in {"P","ACP"}: return False
        return True

    return dict(ALL_FAC=ALL_FAC,FAC_IDX=FAC_IDX,N_FAC=N_FAC,fac_d=fac_d,
                dgroups=dgroups,fac_val=fac_val,ALL_S=ALL_S,NS=NS,
                slot_dates=slot_dates,wdf=wdf,submitted=submitted,non_sub=non_sub,
                sub_counts=sub_counts,fexp=fexp,tag=tag,is_eligible=is_eligible,
                sap_fallback=sap_fallback,SAT_DESIG=SAT_DESIG,
                acp_2online=acp_2online,acp_2offline=acp_2offline)

def _build_summary(assigned, core):
    ALL_FAC=core["ALL_FAC"]; fac_d=core["fac_d"]
    ALL_S=core["ALL_S"];     submitted=core["submitted"]
    sub_counts=core["sub_counts"]
    alloc=pd.DataFrame(assigned)
    alloc["Date"]=pd.to_datetime(alloc["Date"]).dt.strftime("%d-%m-%Y")
    alloc=alloc.sort_values(["Date","Session","Name"]).reset_index(drop=True)
    alloc.insert(0,"Sl.No",alloc.index+1)
    sumrows=[]
    for fn in ALL_FAC:
        d2=fac_d[fn]; dr=DESIG_RULES[d2]
        rf=alloc[alloc["Name"]==fn]; ab=rf["Allocated_By"]
        tot=len(rf); wt=int(ab.isin(WILL_TAGS).sum())
        sumrows.append({"Name":fn,"Designation":d2,
            "Submitted":"Yes" if fn in submitted else "No",
            "Submitted_Count":sub_counts.get(fn,0),
            "Required_Duties":dr[0],"Assigned_Duties":tot,
            "Willingness_Total":wt,
            "Match_%":f"{wt/tot*100:.0f}%" if tot else "N/A",
            "Exact_Match":int((ab=="Willingness-Exact").sum()),
            "Session_Flip":int((ab=="Willingness-SessionFlip").sum()),
            "Adj_±1Day":int((ab=="Willingness-±1Day").sum()),
            "Auto_Assigned":int(ab.isin(["Auto-Assigned","OR-Assigned","Gap-Fill"]).sum()),
            "Online":int((rf["Type"]=="Online").sum()),
            "Offline":int((rf["Type"]=="Offline").sum()),
            "Gap":max(dr[0]-tot,0)})
    sumdf=pd.DataFrame(sumrows)
    slotrows=[]
    for sl in ALL_S:
        ds=pd.Timestamp(sl["date"]).strftime("%d-%m-%Y")
        na=len(alloc[(alloc["Date"]==ds)&(alloc["Session"]==sl["session"])&(alloc["Type"]==sl["type"])])
        slotrows.append({"Date":ds,"Session":sl["session"],"Type":sl["type"],
                         "Required":sl["required"],"Assigned":na,
                         "Status":"✓" if na>=sl["required"] else f"✗ short {sl['required']-na}"})
    slotdf=pd.DataFrame(slotrows)
    return alloc,sumdf,slotdf

def _greedy_solve(core,log):
    ALL_FAC=core["ALL_FAC"]; fac_d=core["fac_d"]; ALL_S=core["ALL_S"]
    fexp=core["fexp"];       tag=core["tag"];       is_eligible=core["is_eligible"]
    non_sub=core["non_sub"]; sap_fallback=core["sap_fallback"]
    acp_2online=core["acp_2online"]; acp_2offline=core["acp_2offline"]
    alloc_count=defaultdict(int); used_dt_sess=defaultdict(set)
    acp_online=defaultdict(int); acp_offline=defaultdict(int)
    def rem(fn): return DESIG_RULES[fac_d[fn]][1]-alloc_count[fn]
    def eligible(fn,sl):
        if not is_eligible(fn,sl): return False
        if rem(fn)<=0: return False
        if (sl["date"],sl["session"]) in used_dt_sess[fn]: return False
        d2=fac_d[fn]
        if d2=="ACP":
            if sl["type"]=="Online" and acp_online[fn]>=(2 if fn in acp_2online else 1): return False
            if sl["type"]=="Offline" and acp_offline[fn]>=(2 if fn in acp_2offline else 1): return False
        if fn in sap_fallback and sl["type"]=="Online" and alloc_count[fn]>=DESIG_RULES[d2][0]: return False
        return True
    def score(fn,sl):
        k=(sl["date"],sl["session"],sl["type"]); sc=fexp[fn].get(k,0)
        return (sc,-alloc_count[fn],-DESIG_PRIORITY.get(fac_d[fn],0))
    assigned=[]
    for sl in sorted(ALL_S,key=lambda s:(s["type"]!="Online",-s["required"])):
        needed=sl["required"]
        cands=sorted([fn for fn in ALL_FAC if eligible(fn,sl)],key=lambda fn:score(fn,sl),reverse=True)
        for fn in cands[:needed]:
            k=(sl["date"],sl["session"],sl["type"]); sc=fexp[fn].get(k,0)
            assigned.append({"Name":fn,"Date":sl["date"],"Session":sl["session"],
                             "Type":sl["type"],"Allocated_By":tag(fn,k,sc)})
            alloc_count[fn]+=1; used_dt_sess[fn].add((sl["date"],sl["session"]))
            if fac_d[fn]=="ACP":
                if sl["type"]=="Online": acp_online[fn]+=1
                if sl["type"]=="Offline": acp_offline[fn]+=1
        filled=sum(1 for a in assigned if a["Date"]==sl["date"] and a["Session"]==sl["session"] and a["Type"]==sl["type"])
        if filled<needed:
            extras=sorted([fn for fn in ALL_FAC
                           if is_eligible(fn,sl) and (sl["date"],sl["session"]) not in used_dt_sess[fn]
                           and fn not in [a["Name"] for a in assigned
                                          if a["Date"]==sl["date"] and a["Session"]==sl["session"] and a["Type"]==sl["type"]]],
                          key=lambda fn:score(fn,sl),reverse=True)
            for fn in extras[:needed-filled]:
                k=(sl["date"],sl["session"],sl["type"]); sc=fexp[fn].get(k,0)
                assigned.append({"Name":fn,"Date":sl["date"],"Session":sl["session"],
                                 "Type":sl["type"],"Allocated_By":tag(fn,k,sc)})
                alloc_count[fn]+=1; used_dt_sess[fn].add((sl["date"],sl["session"]))
    for fn in ALL_FAC:
        needed=DESIG_RULES[fac_d[fn]][0]-alloc_count[fn]
        if needed<=0: continue
        for sl in sorted(ALL_S,key=lambda s:fexp[fn].get((s["date"],s["session"],s["type"]),0),reverse=True):
            if needed<=0: break
            if not is_eligible(fn,sl): continue
            if (sl["date"],sl["session"]) in used_dt_sess[fn]: continue
            k=(sl["date"],sl["session"],sl["type"]); sc=fexp[fn].get(k,0)
            assigned.append({"Name":fn,"Date":sl["date"],"Session":sl["session"],
                             "Type":sl["type"],"Allocated_By":tag(fn,k,sc)})
            alloc_count[fn]+=1; used_dt_sess[fn].add((sl["date"],sl["session"])); needed-=1
    return assigned

def _milp_solve(core,log):
    ALL_FAC=core["ALL_FAC"]; FAC_IDX=core["FAC_IDX"]; N_FAC=core["N_FAC"]
    fac_d=core["fac_d"];     ALL_S=core["ALL_S"];      NS=core["NS"]
    fexp=core["fexp"];       tag=core["tag"];           submitted=core["submitted"]
    is_eligible=core["is_eligible"]; acp_2online=core["acp_2online"]; acp_2offline=core["acp_2offline"]
    SLACK_PENALTY=10_000_000; GAP_PENALTY=500_000
    def v(fi,si): return fi*NS+si
    def sv(si):   return N_FAC*NS+si
    def gv(fi):   return N_FAC*NS+NS+fi
    NV=N_FAC*NS+NS+N_FAC
    c_obj=np.zeros(NV); lb=np.zeros(NV); ub=np.ones(NV)
    for fi,fn in enumerate(ALL_FAC):
        for si,sl in enumerate(ALL_S):
            if not is_eligible(fn,sl): ub[v(fi,si)]=0.0; continue
            k=(sl["date"],sl["session"],sl["type"]); sc=fexp[fn].get(k,0)
            if sc>0: c_obj[v(fi,si)]=-float(sc)
            elif fn in submitted: c_obj[v(fi,si)]=float(PENALTY)
    for si,sl in enumerate(ALL_S):
        ub[sv(si)]=float(sl["required"]); c_obj[sv(si)]=float(SLACK_PENALTY)
    for fi,fn in enumerate(ALL_FAC):
        dr=DESIG_RULES[fac_d[fn]]; ub[gv(fi)]=float(dr[0]); c_obj[gv(fi)]=float(GAP_PENALTY)
    rA,cA,dA,blo,bhi=[],[],[],[],[]
    nc=[0]
    def add_con(vids,coeffs,lo,hi):
        for vi,co in zip(vids,coeffs): rA.append(nc[0]);cA.append(vi);dA.append(float(co))
        blo.append(float(lo));bhi.append(float(hi));nc[0]+=1
    for si,sl in enumerate(ALL_S):
        add_con([v(f,si) for f in range(N_FAC)]+[sv(si)],[1]*N_FAC+[1],sl["required"],sl["required"])
    for fi,fn in enumerate(ALL_FAC):
        dr=DESIG_RULES[fac_d[fn]]
        add_con([v(fi,s) for s in range(NS)],[1]*NS,0,dr[1])
        add_con([v(fi,s) for s in range(NS)]+[gv(fi)],[1]*NS+[1],dr[0],dr[0])
    dt_sess=defaultdict(list)
    for si,sl in enumerate(ALL_S): dt_sess[(sl["date"],sl["session"])].append(si)
    for fi in range(N_FAC):
        for sil in dt_sess.values():
            if len(sil)>1: add_con([v(fi,si) for si in sil],[1]*len(sil),0,1)
    on_i=[i for i,s in enumerate(ALL_S) if s["type"]=="Online"]
    off_i=[i for i,s in enumerate(ALL_S) if s["type"]=="Offline"]
    for fn in ALL_FAC:
        if fac_d[fn]!="ACP": continue
        fi=FAC_IDX[fn]; max_on=2 if fn in acp_2online else 1; max_off=2 if fn in acp_2offline else 1
        if on_i: add_con([v(fi,si) for si in on_i],[1]*len(on_i),0,max_on)
        if off_i: add_con([v(fi,si) for si in off_i],[1]*len(off_i),0,max_off)
    A=csc_matrix((dA,(rA,cA)),shape=(nc[0],NV))
    log(f"  Variables: {NV}  Constraints: {nc[0]}")
    res=milp(c=c_obj,constraints=LinearConstraint(A,blo,bhi),
             integrality=np.ones(NV),bounds=Bounds(lb=lb,ub=ub),
             options={"disp":False,"time_limit":300})
    log(f"  HiGHS status: {res.message}")
    if res.status not in (0,1):
        log("  ⚠ MILP failed — using greedy fallback"); return _greedy_solve(core,log)
    xh=np.round(res.x).astype(int)
    assigned=[]
    for fi,fn in enumerate(ALL_FAC):
        for si,sl in enumerate(ALL_S):
            if xh[v(fi,si)]==1:
                k=(sl["date"],sl["session"],sl["type"]); sc=fexp[fn].get(k,0)
                assigned.append({"Name":fn,"Date":sl["date"],"Session":sl["session"],
                                 "Type":sl["type"],"Allocated_By":tag(fn,k,sc)})
    slack_slots=[(si,sl) for si,sl in enumerate(ALL_S) if xh[sv(si)]>0]
    if slack_slots: log(f"  ⚠ Unfilled seats: {sum(xh[sv(si)] for si,_ in slack_slots)}")
    else: log("  ✓ All slots fully filled")
    gap_fac=[(fi,fn) for fi,fn in enumerate(ALL_FAC) if xh[gv(fi)]>0]
    if gap_fac: log(f"  ⚠ Faculty duty gaps: {sum(xh[gv(fi)] for fi,_ in gap_fac)}")
    else: log("  ✓ All faculty assigned correct duty count")
    return assigned

def _log_and_save(assigned, core, method, log):
    alloc,sumdf,slotdf=_build_summary(assigned,core)
    submitted=core["submitted"]; ALL_S=core["ALL_S"]
    tot=len(alloc); ab2=alloc["Allocated_By"]
    unmet=slotdf[~slotdf["Status"].str.startswith("✓")]
    sub_alloc=alloc[alloc["Name"].isin(submitted)]
    will_matched=int(sub_alloc["Allocated_By"].isin(WILL_TAGS).sum()) if not sub_alloc.empty else 0
    will_total=len(sub_alloc)
    pct=will_matched/will_total*100 if will_total>0 else 0
    log(f"\n  {'='*50}")
    log(f"  RESULT [{method}]  — Match: {pct:.1f}%  Unmet: {len(unmet)}  Gaps: {len(sumdf[sumdf['Gap']>0])}")
    log(f"  Total: {tot}  Exact: {int((ab2=='Willingness-Exact').sum())}  "
        f"Auto: {int(ab2.isin(['Auto-Assigned','OR-Assigned','Gap-Fill']).sum())}")
    return alloc,sumdf,slotdf,pct,len(unmet),len(sumdf[sumdf["Gap"]>0])

def run_optimizer(log_box, offline_df, online_df):
    log_lines=[]
    def log(m=""):
        log_lines.append(m); log_box.code("\n".join(log_lines),language="text")

    log("="*60)
    log("  SASTRA SoME Duty Optimizer  v6  (Supabase backend)")
    log(f"  MILP: {'✅' if SCIPY_OK else '❌'}  Greedy: ✅  CP-SAT: {'✅' if ORTOOLS_OK else '❌'}")
    log("="*60)
    log("\n  Loading data from Supabase...")
    core=_load_core(log,offline_df,online_df)

    log("\n" + "─"*60)
    log("  METHOD A — scipy HiGHS MILP"); log("─"*60)
    try:
        aA=_milp_solve(core,log); alloc_A,sumdf_A,slotdf_A,pct_A,unmet_A,gaps_A=_log_and_save(aA,core,"MILP",log)
    except Exception as e:
        log(f"  ✗ MILP error: {e} → greedy fallback")
        aA=_greedy_solve(core,log); alloc_A,sumdf_A,slotdf_A,pct_A,unmet_A,gaps_A=_log_and_save(aA,core,"MILP→Greedy",log)

    log("\n" + "─"*60)
    log("  METHOD B — Smart Greedy"); log("─"*60)
    try:
        aB=_greedy_solve(core,log); alloc_B,sumdf_B,slotdf_B,pct_B,unmet_B,gaps_B=_log_and_save(aB,core,"Greedy",log)
    except Exception as e:
        log(f"  ✗ Greedy error: {e}"); alloc_B,sumdf_B,slotdf_B,pct_B,unmet_B,gaps_B=alloc_A,sumdf_A,slotdf_A,pct_A,unmet_A,gaps_A

    candidates=[("MILP",pct_A,unmet_A,gaps_A,alloc_A,sumdf_A,slotdf_A),
                ("Greedy",pct_B,unmet_B,gaps_B,alloc_B,sumdf_B,slotdf_B)]
    candidates.sort(key=lambda x:(x[2],x[3],-x[1]))
    rec_name,_,_,_,best_alloc,best_sumdf,best_slotdf=candidates[0]
    log(f"\n  ★ Recommendation: {rec_name}")

    # Save best allotment to Supabase
    log("  Saving to Supabase final_allocation table...")
    fac_id_map = {str(r["name"]).strip(): str(r["faculty_id"]).strip()
                  for r in db_get_all_faculty()}
    records=[]
    for _,row in best_alloc.iterrows():
        fid=fac_id_map.get(str(row["Name"]).strip(), "")
        records.append({
            "faculty_id":   fid,
            "faculty_name": str(row["Name"]),
            "duty_date":    pd.to_datetime(row["Date"],dayfirst=True).strftime("%Y-%m-%d"),
            "session":      str(row["Session"]),
            "type":         str(row["Type"]),
            "allocated_by": str(row["Allocated_By"]),
        })
    db_save_allotment(records)
    log(f"  ✅ Saved {len(records)} records to Supabase")

    st.session_state.update({
        "alloc_milp":alloc_A,"alloc_greedy":alloc_B,
        "sumdf_milp":sumdf_A,"sumdf_greedy":sumdf_B,
        "slotdf_milp":slotdf_A,"slotdf_greedy":slotdf_B,
        "pct_milp":pct_A,"pct_greedy":pct_B,
        "unmet_milp":unmet_A,"unmet_greedy":unmet_B,
        "gaps_milp":gaps_A,"gaps_greedy":gaps_B,
        "recommended":rec_name,
    })
    return best_alloc,best_sumdf,best_slotdf


# ═══════════════════════════════════════════════════════════════ #
#              SESSION STATE DEFAULTS                            #
# ═══════════════════════════════════════════════════════════════ #
for k,v in [("logged_in",False),("faculty_id",""),("faculty_name",""),
            ("faculty_row",None),("is_admin",False),("must_change_pw",False),
            ("panel_mode","User View"),("user_panel_mode","Willingness"),
            ("selected_faculty",""),("selected_slots",[]),
            ("confirm_delete",False),("semester_override","")]:
    if k not in st.session_state: st.session_state[k]=v


# ═══════════════════════════════════════════════════════════════ #
#                        LOGIN PAGE                              #
# ═══════════════════════════════════════════════════════════════ #
def page_login():
    render_header(logo=True)
    _,c2,_=st.columns([1,2,1])
    with c2:
        st.markdown('<div class="card"><div class="card-title">🔒 Faculty Login</div>'
                    '<p class="card-sub">Enter your Faculty ID and password to continue.</p></div>',
                    unsafe_allow_html=True)
        fid_input=st.text_input("Faculty ID",placeholder="e.g. C870, RS1051, C2086").strip().upper().replace(" ","")
        pwd=st.text_input("Password",type="password")
        if st.button("Sign In",use_container_width=True):
            if not fid_input or not pwd:
                st.error("Please enter both Faculty ID and password.")
            else:
                frow=db_get_faculty_by_id(fid_input)
                if not frow:
                    st.error(f"Faculty ID **{fid_input}** not found. Check your ID card and try again.")
                elif verify_password(pwd,frow.get("password_hash","")):
                    st.session_state.logged_in      =True
                    st.session_state.faculty_id     =fid_input
                    st.session_state.faculty_name   =frow["name"]
                    st.session_state.faculty_row    =frow
                    # Force admin for ADMIN_IDS — update DB if needed
                    is_admin=frow.get("is_admin",False) or (fid_input in ADMIN_IDS)
                    if fid_input in ADMIN_IDS and not frow.get("is_admin",False):
                        db_set_admin(fid_input,True)
                    st.session_state.is_admin       =is_admin
                    st.session_state.must_change_pw =frow.get("must_change_pw",True)
                    st.rerun()
                else:
                    st.error(f"Incorrect password. Default first-time password is: **{DEFAULT_PASSWORD}**")
        st.caption(f"First-time login: password is **{DEFAULT_PASSWORD}** — you'll be asked to change it.")
    st.markdown("---")
    st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
    st.stop()


# ═══════════════════════════════════════════════════════════════ #
#             FORCE PASSWORD CHANGE PAGE                         #
# ═══════════════════════════════════════════════════════════════ #
def page_force_change_password():
    render_header(logo=False)
    fid=st.session_state.faculty_id; name=st.session_state.faculty_name
    st.markdown(f"### 🔑 Set Your Password, {name.split()[0]}")
    st.info(f"You must set a new password (min 6 chars, not '{DEFAULT_PASSWORD}') before continuing.")
    np1=st.text_input("New Password",type="password",key="fc_np1")
    np2=st.text_input("Confirm New Password",type="password",key="fc_np2")
    if st.button("Set Password & Continue",use_container_width=True,type="primary"):
        if len(np1)<6: st.error("Password must be at least 6 characters.")
        elif np1==DEFAULT_PASSWORD: st.error(f"Cannot use '{DEFAULT_PASSWORD}' as your password.")
        elif np1!=np2: st.error("Passwords do not match.")
        else:
            db_update_password(fid,hash_password(np1),must_change=False)
            st.session_state.must_change_pw=False
            st.success("Password set! Continuing…"); st.rerun()
    st.stop()


# ═══════════════════════════════════════════════════════════════ #
#            CHANGE PASSWORD SECTION                             #
# ═══════════════════════════════════════════════════════════════ #
def section_change_password():
    fid=st.session_state.faculty_id; frow=st.session_state.faculty_row
    with st.expander("🔑 Change My Password"):
        op =st.text_input("Current Password",type="password",key="usr_op")
        np1=st.text_input("New Password (min 6 chars)",type="password",key="usr_np1")
        np2=st.text_input("Confirm New Password",type="password",key="usr_np2")
        if st.button("Update Password",key="usr_upd_pw"):
            if not verify_password(op,frow.get("password_hash","")):
                st.error("Current password is incorrect.")
            elif len(np1)<6: st.error("New password must be at least 6 characters.")
            elif np1!=np2: st.error("Passwords do not match.")
            elif np1==DEFAULT_PASSWORD: st.error(f"Cannot reuse the default password.")
            else:
                db_update_password(fid,hash_password(np1)); st.success("Password updated successfully.")


# ═══════════════════════════════════════════════════════════════ #
#                    ALLOTMENT VIEW                              #
# ═══════════════════════════════════════════════════════════════ #
def page_allotment():
    frow=st.session_state.faculty_row
    fid=st.session_state.faculty_id; name=st.session_state.faculty_name
    st.markdown("### My Allotment Details")

    _off=db_get_offline_duty(); _on=db_get_online_duty()
    _all_dates={d.date() for d in list(_off["Date"])+list(_on["Date"]) if pd.notna(d)}
    _sem=detect_semester(_all_dates); _s,_e=get_exam_period(_all_dates)
    if _s and _e:
        st.markdown(
            f"<div style='background:#e0f2fe;border:1.5px solid #38bdf8;border-radius:10px;"
            f"padding:10px 16px;margin-bottom:12px;font-size:.93rem;color:#0c4a6e'>"
            f"🎓 <b>{_sem}</b>&nbsp;&nbsp;|&nbsp;&nbsp; 📅 "
            f"<b>{_s.strftime('%d-%m-%Y') if hasattr(_s,'strftime') else _s}</b>"
            f" → <b>{_e.strftime('%d-%m-%Y') if hasattr(_e,'strftime') else _e}</b>"
            f"</div>",unsafe_allow_html=True)

    if not gate_is_open():
        st.markdown(
            "<div style='background:#fef3c7;border:2px solid #f59e0b;border-radius:12px;"
            "padding:22px 26px;text-align:center;margin:18px 0'>"
            "<div style='font-size:2.2rem;margin-bottom:8px'>⏳</div>"
            "<div style='font-size:1.15rem;font-weight:700;color:#92400e'>Allotment results are being processed</div>"
            "<div style='font-size:.93rem;color:#78350f;margin-top:6px'>"
            "The Examination Committee is reviewing the final allocation. Please check back shortly.</div>"
            "</div>",unsafe_allow_html=True)
        return

    val_dates=valuation_dates_for_row(frow)
    vd=[f"{pd.Timestamp(d).strftime('%d-%m-%Y')} ({pd.Timestamp(d).strftime('%A')}) - Full Day" for d in val_dates]
    qd=[fmt_day(d) for d in qp_dates_for_row(frow)]

    will_data=db_get_willingness_for(fid)
    will_display=[]; will_pairs=set()
    for w in will_data:
        ts=parse_date_safe(w["duty_date"]); s=normalize_session(w["session"])
        if pd.notna(ts):
            will_display.append(f"{fmt_day(ts)} - {s}"); will_pairs.add((ts.date(),s))

    allot_data=db_get_allotment_for(fid)
    allot_display=[]; allot_pairs=set()
    for a in allot_data:
        ts=parse_date_safe(a["duty_date"]); s=normalize_session(a.get("session",""))
        dtype=str(a.get("type","")).strip()
        sat_tag=" — Saturday" if pd.notna(ts) and ts.weekday()==5 else ""
        if pd.notna(ts):
            allot_display.append(f"{fmt_day(ts)} - {s} ({dtype}){sat_tag}")
            allot_pairs.add((ts.date(),s))

    acc_pct=(f"{len(will_pairs&allot_pairs)/len(will_pairs)*100:.1f}%"
             f"  ({len(will_pairs&allot_pairs)}/{len(will_pairs)})"
             if will_pairs else "Not available")

    c1,c2=st.columns(2)
    with c1:
        st.markdown('<div class="panel"><div class="sec-title">📝 Willingness Submitted</div></div>',unsafe_allow_html=True)
        st.dataframe(pd.DataFrame({"Date & Session":will_display or ["Not submitted"]}),use_container_width=True,hide_index=True)
        st.markdown('<div class="panel"><div class="sec-title">🏛️ IG Duty Allotment</div></div>',unsafe_allow_html=True)
        st.dataframe(pd.DataFrame({"Date, Session & Type":allot_display or ["Not allotted yet"]}),use_container_width=True,hide_index=True)
    with c2:
        st.markdown('<div class="panel"><div class="sec-title">📋 Valuation Dates</div></div>',unsafe_allow_html=True)
        st.dataframe(pd.DataFrame({"Date":vd or ["Not available"]}),use_container_width=True,hide_index=True)
        st.markdown('<div class="panel"><div class="sec-title">💬 QP Feedback Dates</div></div>',unsafe_allow_html=True)
        st.dataframe(pd.DataFrame({"Date":qd or ["Not available"]}),use_container_width=True,hide_index=True)

    st.markdown(f"<div style='margin-top:10px;padding:12px 16px;background:#f0fdf4;"
                f"border:1.5px solid #86efac;border-radius:10px;font-size:.9rem;color:#166534'>"
                f"📊 <b>Willingness Accommodation:</b> {acc_pct}</div>",unsafe_allow_html=True)

    msg_lines=[f"Dear {name},","","Examination Duty Details:","",
               "Invigilation:",*(allot_display or ["Not allotted yet"]),"",
               "Valuation:",*(vd or ["Not available"]),"",
               "QP Feedback:",*(qd or ["Not available"]),"",
               f"Willingness Accommodation: {acc_pct}","","-- SASTRA SoME Examination Committee"]
    msg="\n".join(msg_lines)
    st.markdown('<div class="panel"><div class="sec-title">📲 Share via WhatsApp</div></div>',unsafe_allow_html=True)
    st.code(msg,language="text")
    wph=st.text_input("WhatsApp Number (with country code)",placeholder="+919876543210")
    if wph.strip():
        st.markdown(f'<a href="{wa_link(wph,msg)}" target="_blank" style="display:inline-block;'
                    f'background:#25D366;color:white;padding:10px 22px;border-radius:10px;'
                    f'font-weight:700;text-decoration:none;margin-top:6px">📲 Open WhatsApp & Send</a>',
                    unsafe_allow_html=True)


# ═══════════════════════════════════════════════════════════════ #
#               WILLINGNESS SUBMISSION PAGE                      #
# ═══════════════════════════════════════════════════════════════ #
def page_willingness(offline_df, online_df):
    frow=st.session_state.faculty_row
    fid=st.session_state.faculty_id; name=st.session_state.faculty_name
    desig=str(frow.get("designation","")).strip()
    desig=DESIG_MAP.get(desig.lower(),desig.upper())
    req_cnt=DUTY_STRUCTURE.get(desig,0)
    if req_cnt==0:
        st.warning(f"Designation '{desig}' not recognised. Contact admin."); return

    val_dates=valuation_dates_for_row(frow); val_set=set(val_dates)
    sopts=online_df.copy() if desig=="P" else offline_df.copy()
    sopts["DateOnly"]=sopts["Date"].dt.date
    valid_d=sorted([d for d in sopts["DateOnly"].dropna().unique() if d not in val_set])

    if st.session_state.selected_faculty!=fid:
        st.session_state.selected_faculty=fid; st.session_state.selected_slots=[]
        st.session_state["picked_date"]=valid_d[0] if valid_d else None
    if "picked_date" not in st.session_state:
        st.session_state["picked_date"]=valid_d[0] if valid_d else None

    # Exam period banner
    _all_dates={d.date() for d in list(offline_df["Date"])+list(online_df["Date"]) if pd.notna(d)}
    _sem=detect_semester(_all_dates); _s,_e=get_exam_period(_all_dates)
    _period=""
    if _s and _e:
        _period=(f"&nbsp;&nbsp;|&nbsp;&nbsp;📅 Exam Period: "
                 f"<b>{_s.strftime('%d-%m-%Y')} ({_s.strftime('%A')})</b>"
                 f" → <b>{_e.strftime('%d-%m-%Y')} ({_e.strftime('%A')})</b>")
    st.markdown(f"<div style='background:#e0f2fe;border:1.5px solid #38bdf8;border-radius:10px;"
                f"padding:10px 16px;margin-bottom:4px;font-size:.93rem;color:#0c4a6e'>"
                f"🎓 <b>{_sem}</b>{_period}</div>",unsafe_allow_html=True)

    left,right=st.columns([1,1.4])
    with left:
        st.subheader("Willingness Submission")
        st.write(f"**Faculty ID:** {fid}")
        st.write(f"**Designation:** {DESIG_FULL.get(desig,desig)}")
        duties_min,duties_max=DESIG_RULES.get(desig,(0,0,[]))[:2]
        st.write(f"**Duties to be Allotted:** {duties_min if duties_min==duties_max else f'{duties_min}–{duties_max}'}")
        st.write(f"**Options to Select:** {req_cnt}")

        st.markdown("""
<div style="background:#f0f7ff;border:1.5px solid #93c5fd;border-radius:12px;padding:14px 16px;margin:8px 0 14px 0">
  <div style="font-size:.88rem;font-weight:800;color:#1e3a5f;margin-bottom:8px">ℹ️ How Your Duty Will Be Allotted</div>
  <table style="width:100%;margin-top:8px;border-collapse:collapse;font-size:.81rem">
    <tr><td style="padding:4px 8px">✅</td><td style="padding:4px 6px;font-weight:700;color:#065f46">Exact Match</td>
        <td style="padding:4px 6px;color:#374151">Allotted on the exact date & session you submit</td></tr>
    <tr style="background:#f8fafc"><td style="padding:4px 8px">🔄</td><td style="padding:4px 6px;font-weight:700;color:#92400e">Session Adjusted</td>
        <td style="padding:4px 6px;color:#374151">Same date, FN↔AN swapped if needed</td></tr>
    <tr><td style="padding:4px 8px">📅</td><td style="padding:4px 6px;font-weight:700;color:#9a3412">Date Adjusted</td>
        <td style="padding:4px 6px;color:#374151">Shifted ±1 working day from your submitted date</td></tr>
    <tr style="background:#f8fafc"><td style="padding:4px 8px">🔴</td><td style="padding:4px 6px;font-weight:700;color:#991b1b">System-Assigned</td>
        <td style="padding:4px 6px;color:#374151">No match — assigned to meet slot requirements</td></tr>
  </table>
  <div style="font-size:.78rem;color:#64748b;margin-top:10px;border-top:1px solid #bfdbfe;padding-top:8px">
    💡 Submit dates spread across the exam period to maximise your match rate.
  </div>
</div>""",unsafe_allow_html=True)

        if desig=="ACP":
            st.info("ACP faculty: select offline dates — one online duty will be assigned automatically.")

        if not valid_d:
            st.warning("No dates available for selection.")
        else:
            picked=st.selectbox("Choose Online Date" if desig=="P" else "Choose Offline Date",
                                valid_d,key="picked_date",format_func=lambda d:d.strftime("%d-%m-%Y (%A)"))
            avail=set(sopts[sopts["DateOnly"]==picked]["Session"].dropna().astype(str).str.upper())

            # Slot probability
            for sess_opt in ["FN","AN"]:
                if sess_opt in avail:
                    prob=slot_probability(offline_df,online_df,desig,picked,sess_opt)
                    if prob["seats"]>0: render_prob_bar(prob,sess_opt)

            b1,b2=st.columns(2)
            with b1:
                add_fn=st.button("➕ Add FN",use_container_width=True,
                                 disabled=("FN" not in avail or len(st.session_state.selected_slots)>=req_cnt))
            with b2:
                add_an=st.button("➕ Add AN",use_container_width=True,
                                 disabled=("AN" not in avail or len(st.session_state.selected_slots)>=req_cnt))

            def add_slot(sess):
                exist={s["Date"] for s in st.session_state.selected_slots}
                sl2={"Date":picked,"Session":sess}
                if picked in val_set: st.warning("Valuation date — cannot select.")
                elif picked in exist: st.warning("Both FN and AN on same date not allowed.")
                elif len(st.session_state.selected_slots)>=req_cnt: st.warning("Count reached.")
                elif sl2 in st.session_state.selected_slots: st.warning("Already selected.")
                else: st.session_state.selected_slots.append(sl2)

            if add_fn: add_slot("FN")
            if add_an: add_slot("AN")

        st.session_state.selected_slots=st.session_state.selected_slots[:req_cnt]
        st.write(f"**Selected:** {len(st.session_state.selected_slots)} / {req_cnt}")

        sdf=pd.DataFrame(st.session_state.selected_slots)
        if not sdf.empty:
            sdf=sdf.sort_values(["Date","Session"]).reset_index(drop=True)
            sdf.insert(0,"Sl.No",sdf.index+1)
            sdf["Day"]=pd.to_datetime(sdf["Date"]).dt.day_name()
            sdf["Date"]=pd.to_datetime(sdf["Date"]).dt.strftime("%d-%m-%Y")
            st.dataframe(sdf[["Sl.No","Date","Day","Session"]],use_container_width=True,hide_index=True)
            rm=st.selectbox("Sl.No to remove",options=sdf["Sl.No"].tolist())
            if st.button("🗑 Remove Row",use_container_width=True):
                tgt=sdf[sdf["Sl.No"]==rm].iloc[0]
                td=pd.to_datetime(tgt["Date"],dayfirst=True).date(); ts=tgt["Session"]
                st.session_state.selected_slots=[s for s in st.session_state.selected_slots
                                                 if not (s["Date"]==td and s["Session"]==ts)]
                st.rerun()

        is_already=db_already_submitted(fid)
        st.markdown("### Submit Willingness")
        rem2=max(req_cnt-len(st.session_state.selected_slots),0)
        if is_already:
            st.warning("⚠ You have already submitted. Submitting again will **replace** your previous choices.")
        if rem2==0 and req_cnt>0:
            st.success(f"✅ All {req_cnt} options selected. Ready to submit.")
        elif not is_already:
            st.info(f"Select {rem2} more option(s) to enable submission.")

        if st.button("✅ Submit Willingness",
                     disabled=(len(st.session_state.selected_slots)!=req_cnt),
                     use_container_width=True):
            db_submit_willingness(fid,name,st.session_state.selected_slots)
            st.session_state.selected_slots=[]
            action="re-submitted" if is_already else "submitted"
            st.toast(f"Willingness {action} successfully! ✅",icon="✅")
            st.success("Thank you! Final allocation will be via MILP optimization. Check back for updates.")

    with right:
        render_calendar(online_df if desig=="P" else offline_df,val_set,
                        "Online Duty Calendar" if desig=="P" else "Offline Duty Calendar")


# ═══════════════════════════════════════════════════════════════ #
#                        ADMIN PAGE                              #
# ═══════════════════════════════════════════════════════════════ #
def page_admin(offline_df, online_df):
    st.markdown('<div class="card"><div class="card-title">🔒 Admin Panel</div></div>',unsafe_allow_html=True)
    t1,t2,t3,t4,t5=st.tabs(["📋 Willingness","🤖 Run Optimizer","📊 Results","👥 Accounts","⚙️ Settings"])

    # ── Tab 1: Willingness ─────────────────────────────────────── #
    with t1:
        st.markdown("### 📋 Willingness Records")
        all_fac=db_get_all_faculty()
        wrows=db_get_all_willingness()
        if not wrows:
            st.info("No willingness data yet.")
        else:
            wdf=pd.DataFrame(wrows)
            cols_show=["faculty_id","faculty_name","duty_date","session","submitted_at"]
            cols_show=[c for c in cols_show if c in wdf.columns]
            wdf2=wdf[cols_show].copy()
            wdf2.columns=["Faculty ID","Name","Date","Session","Submitted At"][:len(cols_show)]
            wdf2.insert(0,"Sl.No",range(1,len(wdf2)+1))
            c1,c2,c3=st.columns(3)
            c1.metric("Faculty Submitted",wdf["faculty_id"].nunique() if "faculty_id" in wdf.columns else 0)
            c2.metric("Not Yet Submitted",len(all_fac)-wdf["faculty_id"].nunique() if "faculty_id" in wdf.columns else len(all_fac))
            c3.metric("Total Rows",len(wdf2))
            st.dataframe(wdf2,use_container_width=True,hide_index=True)
            # Download as Excel in-memory
            buf=io.BytesIO(); wdf2.to_excel(buf,index=False,engine="openpyxl")
            st.download_button("⬇ Download Willingness Excel",data=buf.getvalue(),
                               file_name="Willingness.xlsx",
                               mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                               use_container_width=True)
        st.markdown("---")
        st.markdown("#### ⚠ Delete All Willingness Records")
        st.checkbox("Confirm deletion of all willingness records",key="confirm_delete")
        if st.button("Delete All Willingness",type="primary"):
            if st.session_state.confirm_delete:
                db_delete_all_willingness(); st.success("All records deleted."); st.rerun()
            else: st.error("Tick the confirmation checkbox first.")

    # ── Tab 2: Run Optimizer ───────────────────────────────────── #
    with t2:
        st.markdown("### 🤖 Run Allocation Optimizer")
        st.info("Duty slot data is loaded from Supabase (offline_duty / online_duty tables). "
                "Results are saved to the final_allocation table automatically.")

        if offline_df.empty and online_df.empty:
            st.error("No duty slots found in Supabase. Populate offline_duty and online_duty tables first.")
        else:
            c1,c2,c3=st.columns(3)
            c1.metric("Offline Slots",len(offline_df))
            c2.metric("Online Slots",len(online_df))
            wrows2=db_get_all_willingness()
            fid_set=set(r["faculty_id"] for r in wrows2) if wrows2 else set()
            c3.metric(f"Faculty Submitted",f"{len(fid_set)}/{len(db_get_all_faculty())}")

            solver_lbl="OR-Tools CP-SAT ✅" if ORTOOLS_OK else ("scipy HiGHS ✅" if SCIPY_OK else "❌ No solver")
            st.info(f"🔧 Solver: **{solver_lbl}**")

            if st.button("▶ Run Optimizer",type="primary",use_container_width=True):
                lb2=st.empty()
                with st.spinner("Running optimization…"):
                    try:
                        _,_,_=run_optimizer(lb2,offline_df,online_df)
                        st.success("✅ Done! Go to **📊 Results** to review, then enable Allotment View in Settings.")
                        st.balloons()
                    except Exception as e:
                        import traceback
                        st.error(f"Optimizer error: {e}")
                        st.code(traceback.format_exc(),language="text")

    # ── Tab 3: Results ─────────────────────────────────────────── #
    with t3:
        st.markdown("### 📊 Allocation Results")
        pct_m=st.session_state.get("pct_milp"); pct_g=st.session_state.get("pct_greedy")
        unmet_m=st.session_state.get("unmet_milp"); unmet_g=st.session_state.get("unmet_greedy")
        rec=st.session_state.get("recommended","MILP")

        if pct_m is not None and pct_g is not None:
            st.markdown("#### ⚖️ Method Comparison")
            c1,c2=st.columns(2)
            def mcard(col,name,pct,unmet,is_rec):
                bg="#d1fae5" if is_rec else "#f1f5f9"; bdr="#6ee7b7" if is_rec else "#e2e8f0"
                col.markdown(f"""<div style="background:{bg};border:2px solid {bdr};border-radius:12px;
padding:16px 18px;text-align:center">
  <div style="font-size:1.05rem;font-weight:800;color:#0f172a">{name}{"  ⭐" if is_rec else ""}</div>
  <div style="font-size:2rem;font-weight:900;color:#0b3a67;margin:8px 0">{pct:.1f}%</div>
  <div style="font-size:.85rem;color:#475569">Willingness Match</div>
  <div style="margin-top:8px;font-size:.9rem;color:{'#065f46' if unmet==0 else '#991b1b'};font-weight:700">
    {'✅ All slots filled' if unmet==0 else f'⚠ {unmet} slot(s) unmet'}</div>
</div>""",unsafe_allow_html=True)
            with c1: mcard(c1,"Method A — MILP",pct_m,unmet_m,rec=="MILP")
            with c2: mcard(c2,"Method B — Greedy",pct_g,unmet_g,rec=="Greedy")

            chosen=st.radio("**Apply as Final Allocation:**",
                            ["Method A — MILP","Method B — Greedy"],
                            index=0 if rec=="MILP" else 1,horizontal=True)
            if st.button("✅ Apply & Save to Supabase",type="primary",use_container_width=True):
                chosen_key="MILP" if "MILP" in chosen else "Greedy"
                sel_alloc=st.session_state.get(f"alloc_{chosen_key.lower()}")
                if sel_alloc is not None:
                    fac_id_map={str(r["name"]).strip():str(r["faculty_id"]).strip()
                                for r in db_get_all_faculty()}
                    records=[]
                    for _,row in sel_alloc.iterrows():
                        fid2=fac_id_map.get(str(row["Name"]).strip(),"")
                        records.append({
                            "faculty_id":fid2,"faculty_name":str(row["Name"]),
                            "duty_date":pd.to_datetime(row["Date"],dayfirst=True).strftime("%Y-%m-%d"),
                            "session":str(row["Session"]),"type":str(row["Type"]),
                            "allocated_by":str(row["Allocated_By"]),
                        })
                    db_save_allotment(records)
                    st.success(f"✅ {chosen_key} method saved to Supabase ({len(records)} records)")
                    st.rerun()

            # Download in-memory Excel
            st.markdown("#### ⬇ Download Results")
            d1,d2=st.columns(2)
            for col,key,label in [(d1,"milp","MILP"),(d2,"greedy","Greedy")]:
                df_dl=st.session_state.get(f"alloc_{key}")
                if df_dl is not None:
                    buf=io.BytesIO(); df_dl.to_excel(buf,index=False,engine="openpyxl")
                    col.download_button(f"⬇ {label} Allocation",data=buf.getvalue(),
                                        file_name=f"Allocation_{label}.xlsx",
                                        mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                                        use_container_width=True)
            st.markdown("---")

        # Live results from Supabase
        allot_rows=db_get_all_allotment()
        if not allot_rows:
            st.info("No allocation in database yet. Run the optimizer first.")
        else:
            av=pd.DataFrame(allot_rows)
            tot2=len(av); ab3=av.get("allocated_by",pd.Series(dtype=str))
            if "allocated_by" in av.columns:
                will_m=int(av["allocated_by"].isin(WILL_TAGS).sum())
                aut=int(av["allocated_by"].isin(["Auto-Assigned","OR-Assigned","Gap-Fill"]).sum())
                c1,c2,c3,c4=st.columns(4)
                c1.metric("Total Assignments",tot2); c2.metric("Willingness Matched",will_m)
                c3.metric("Auto-Assigned",aut); c4.metric("Match %",f"{will_m/tot2*100:.1f}%" if tot2 else "—")

            st.markdown("#### 🔍 Per-Faculty Deviation Analysis")
            all_fac2=db_get_all_faculty()
            fac_options=[f"{r['faculty_id']} — {r['name']}" for r in all_fac2]
            admin_sel=st.selectbox("Select Faculty",fac_options,key="admin_dev_sel")
            sel_fid2=admin_sel.split(" — ")[0]
            will2=db_get_willingness_for(sel_fid2)
            will_set2=set()
            for w in will2:
                ts=parse_date_safe(w["duty_date"]); s=normalize_session(w["session"])
                if pd.notna(ts): will_set2.add((ts.date(),s))
            fac_allot=av[av["faculty_id"]==sel_fid2].copy() if "faculty_id" in av.columns else pd.DataFrame()
            render_deviation_section(fac_allot,will_set2)

            st.markdown("#### Full Allocation Table")
            st.dataframe(av,use_container_width=True,hide_index=True)
            buf=io.BytesIO(); av.to_excel(buf,index=False,engine="openpyxl")
            st.download_button("⬇ Download Full Allocation",data=buf.getvalue(),
                               file_name="Final_Allocation.xlsx",
                               mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

    # ── Tab 4: Faculty Accounts ─────────────────────────────────── #
    with t4:
        st.markdown("### 👥 Faculty Account Management")
        all_fac3=db_get_all_faculty()
        acc_rows=[]
        for r in all_fac3:
            acc_rows.append({"ID No.":r["faculty_id"],"Name":r["name"],
                             "Designation":r["designation"],
                             "Password":("✅ Set" if r.get("password_hash") else "❌ Not set"),
                             "Must Change":"⚠ Yes" if r.get("must_change_pw") else "No",
                             "Admin":"👑 Yes" if r.get("is_admin") else "No"})
        st.dataframe(pd.DataFrame(acc_rows),use_container_width=True,hide_index=True)

        st.markdown("---")
        st.markdown("#### 🔑 Reset Faculty Password")
        st.caption(f"Resets to default password (**{DEFAULT_PASSWORD}**) and forces change on next login.")
        fac_opts=[f"{r['faculty_id']} — {r['name']}" for r in all_fac3]
        reset_sel=st.selectbox("Select Faculty",fac_opts,key="admin_reset_sel")
        reset_fid=reset_sel.split(" — ")[0]
        if st.button("Reset Password",key="btn_reset_pw"):
            db_reset_password(reset_fid)
            st.success(f"Password for **{reset_sel.split(' — ')[1]}** reset to default.")

        st.markdown("---")
        st.markdown("#### 👑 Toggle Admin Rights")
        tog_sel=st.selectbox("Select Faculty",fac_opts,key="tog_sel")
        tog_fid=tog_sel.split(" — ")[0]
        tog_row=next((r for r in all_fac3 if r["faculty_id"]==tog_fid),{})
        cur_adm=tog_row.get("is_admin",False)
        st.info(f"**{tog_sel.split(' — ')[1]}** is currently: {'👑 Admin' if cur_adm else 'Regular Faculty'}")
        ca,cb=st.columns(2)
        with ca:
            if st.button("Grant Admin",disabled=cur_adm,use_container_width=True):
                db_set_admin(tog_fid,True); st.success("Admin granted."); st.rerun()
        with cb:
            if st.button("Revoke Admin",disabled=not cur_adm,use_container_width=True):
                db_set_admin(tog_fid,False); st.success("Admin revoked."); st.rerun()

        st.markdown("---")
        with st.expander("🔒 Change My Admin Password"):
            op=st.text_input("Current Password",type="password",key="adm_op")
            np1=st.text_input("New Password",type="password",key="adm_np1")
            np2=st.text_input("Confirm",type="password",key="adm_np2")
            if st.button("Update Admin Password"):
                frow=st.session_state.faculty_row
                if not verify_password(op,frow.get("password_hash","")):
                    st.error("Current password incorrect.")
                elif len(np1)<6: st.error("Min 6 characters.")
                elif np1!=np2: st.error("Passwords don't match.")
                else:
                    db_update_password(st.session_state.faculty_id,hash_password(np1))
                    st.success("Password updated.")

    # ── Tab 5: Settings ────────────────────────────────────────── #
    with t5:
        st.markdown("### ⚙️ Portal Settings")
        st.markdown("---")
        st.markdown("#### 🔒 Allotment View — User Access Control")
        is_open=gate_is_open()
        if is_open:
            st.markdown("<div style='background:#d1fae5;border:1.5px solid #6ee7b7;border-radius:10px;"
                        "padding:12px 18px;margin-bottom:14px'><span style='font-size:1.05rem;font-weight:700;"
                        "color:#065f46'>🟢 Allotment view is ENABLED</span></div>",unsafe_allow_html=True)
        else:
            st.markdown("<div style='background:#fee2e2;border:1.5px solid #fca5a5;border-radius:10px;"
                        "padding:12px 18px;margin-bottom:14px'><span style='font-size:1.05rem;font-weight:700;"
                        "color:#991b1b'>🔴 Allotment view is DISABLED</span></div>",unsafe_allow_html=True)
        ec,dc=st.columns(2)
        with ec:
            if st.button("✅ Enable Allotment View",use_container_width=True,disabled=is_open,type="primary"):
                set_gate(True); st.success("Enabled."); st.rerun()
        with dc:
            if st.button("🔴 Disable Allotment View",use_container_width=True,disabled=not is_open):
                set_gate(False); st.warning("Disabled."); st.rerun()

        st.markdown("---")
        st.markdown("#### 🗓️ Semester Setting")
        sem_opts=["Auto-detect","Even Semester (Apr/May End-Semester)","Odd Semester (Nov/Dec End-Semester)"]
        cur_sem=db_get_setting("semester","Auto-detect") or "Auto-detect"
        new_sem=st.selectbox("Semester Display Mode",sem_opts,
                             index=sem_opts.index(cur_sem) if cur_sem in sem_opts else 0)
        if new_sem!=cur_sem:
            db_set_setting("semester",new_sem)
            st.session_state["semester_override"]=new_sem
            st.success(f"Semester set to: **{new_sem}**"); st.rerun()


# ═══════════════════════════════════════════════════════════════ #
#                         MAIN ROUTER                            #
# ═══════════════════════════════════════════════════════════════ #
def main():
    if not st.session_state.logged_in:
        page_login(); return

    if st.session_state.must_change_pw:
        page_force_change_password(); return

    # Load duty data (cached)
    offline_df=db_get_offline_duty()
    online_df=db_get_online_duty()

    render_header(logo=False)
    st.markdown(
        "<div class='blink'><strong>Note:</strong> The University Examination Committee sincerely "
        "appreciates your cooperation. Every effort will be made to accommodate your willingness. "
        "Final duty allocation is carried out using AI-assisted MILP optimization.</div>",
        unsafe_allow_html=True)
    st.markdown("")

    col_title,col_logout=st.columns([6,1])
    with col_logout:
        if st.button("🚪 Logout"):
            for k in ["logged_in","faculty_id","faculty_name","faculty_row","is_admin",
                      "must_change_pw","selected_slots","selected_faculty"]:
                st.session_state[k]=([] if k=="selected_slots" else
                                     (False if k not in ("faculty_id","faculty_name","faculty_row") else
                                      ("" if k!="faculty_row" else None)))
            st.rerun()
    with col_title:
        fid=st.session_state.faculty_id; name=st.session_state.faculty_name
        is_admin=st.session_state.is_admin
        st.markdown(f"**Welcome, {name}** &nbsp;<span style='color:#64748b;font-size:.88rem'>({fid})</span>"
                    +(" 👑 Admin" if is_admin else ""),unsafe_allow_html=True)

    if is_admin:
        menu=st.radio("Main Menu",["User View","Admin View"],horizontal=True,key="panel_mode")
        if menu=="Admin View":
            page_admin(offline_df,online_df)
            st.markdown("---")
            st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
            return

    sub=st.radio("View",["Willingness","My Allotment","Change Password"],horizontal=True,key="user_panel_mode")
    if sub=="My Allotment":    page_allotment()
    elif sub=="Change Password": section_change_password()
    else:                       page_willingness(offline_df,online_df)

    st.markdown("---")
    st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")

main()
