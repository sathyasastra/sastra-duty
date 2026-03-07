"""
SASTRA SoME End Semester Examination Duty Portal
=================================================
Files required in the same folder as app.py:
  1. Faculty_Master.xlsx  — faculty list + designation + optional valuation date cols (V1..V5)
  2. Offline_Duty.xlsx    — offline exam slots  (col A: Date | col B: FN/AN | col C: count)
  3. Online_Duty.xlsx     — online exam slots   (col A: Date | col B: FN/AN | col C: count)
  4. sastra_logo.png      — university logo (optional)
  5. Willingness.xlsx     — faculty willingness collected via this portal

Login credentials:
  Faculty portal : SASTRA / SASTRA
  Admin panel    : sathya

v3 improvements:
  1. Slot allocation probability shown live during willingness submission
  2. Admin enable/disable toggle for allotment view (gate file: allotment_gate.txt)
  3. Deviation analysis in allotment page — ADMIN ONLY
  4. Date overlap diagnostic tool in Admin Tab 2
  5. ACP online limit raised to 2 to cover unfilled online slots
  6. Detailed match-failure report in optimizer log
"""

import os
import datetime
import warnings
import calendar as calmod
import urllib.parse
from collections import defaultdict

import numpy as np
import pandas as pd
import streamlit as st
import altair as alt

try:
    from ortools.sat.python import cp_model
    ORTOOLS_OK = True
except ImportError:
    ORTOOLS_OK = False

try:
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import csc_matrix
    SCIPY_OK = True
except ImportError:
    SCIPY_OK = False

warnings.filterwarnings("ignore")

# ─── File names ──────────────────────────────────────────────── #
FACULTY_FILE      = "Faculty_Master.xlsx"
OFFLINE_FILE      = "Offline_Duty.xlsx"
ONLINE_FILE       = "Online_Duty.xlsx"
WILLINGNESS_FILE  = "Willingness.xlsx"
LOGO_FILE         = "sastra_logo.png"
FINAL_ALLOC_FILE  = "Final_Allocation.xlsx"
ALLOC_REPORT_FILE = "Allocation_Report.xlsx"
GATE_FILE         = "allotment_gate.txt"   # "1" = open, "0" = locked

# ─── Designation rules ───────────────────────────────────────── #
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

# ── Willingness match scores ──────────────────────────────────── #
W_EXACT      = 100_000   # exact date + session match
W_ACP_ONLINE =  80_000   # ACP offline→online mapping
W_FLIP       =  60_000   # same date, opposite session (FN↔AN)
W_ADJ1       =  40_000   # ±1 business day adjacency
W_VAL_ADJ    =   5_000   # adjacent to own valuation date
W_NON_SUB    =     100   # no willingness submitted
PENALTY      =      10   # submitted but slot outside window (discourage)

# ── Designation priority (higher = preferred for slot filling) ── #
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
    "Willingness-SessionFlip", "Willingness-±1Day", "Willingness-ValAdj"
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
#              ALLOTMENT GATE  (Feature 2)                       #
# ═══════════════════════════════════════════════════════════════ #
def gate_is_open() -> bool:
    try:
        with open(GATE_FILE) as f:
            return f.read().strip() == "1"
    except FileNotFoundError:
        return False

def set_gate(open_: bool):
    with open(GATE_FILE, "w") as f:
        f.write("1" if open_ else "0")


# ═══════════════════════════════════════════════════════════════ #
#                     UTILITY FUNCTIONS                          #
# ═══════════════════════════════════════════════════════════════ #
def clean(x):
    return str(x).strip().lower()

def normalize_session(v):
    t = str(v).strip().upper()
    if t in {"FN", "FORENOON", "MORNING", "AM"}:
        return "FN"
    if t in {"AN", "AFTERNOON", "EVENING", "PM"}:
        return "AN"
    return t

def fmt_day(val):
    dt = pd.to_datetime(val, dayfirst=True, errors="coerce")
    return f"{dt.strftime('%d-%m-%Y')} ({dt.strftime('%A')})" if pd.notna(dt) else str(val)

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
    """Auto-detect ODD or EVEN semester from slot dates or current month.
    Admin can override via Portal Settings → Semester Setting."""
    # Admin override takes priority
    override = st.session_state.get("semester_override", "Auto-detect")
    if override and override != "Auto-detect":
        return override

    now = datetime.date.today()
    # Use slot dates if available
    if slot_dates:
        months = {d.month for d in slot_dates}
        if months & {5, 6}:
            return "Even Semester (Apr/May End-Semester)"
        if months & {11, 12, 1}:
            return "Odd Semester (Nov/Dec End-Semester)"
    # Fallback: current month
    if now.month in (4, 5, 6):
        return "Even Semester (Apr/May End-Semester)"
    if now.month in (11, 12, 1):
        return "Odd Semester (Nov/Dec End-Semester)"
    return "End-Semester Examination"

def get_exam_period(slot_dates):
    """Return (start_date, end_date) string from slot dates."""
    if not slot_dates:
        return None, None
    sd = sorted(slot_dates)
    return sd[0], sd[-1]


    if logo and os.path.exists(LOGO_FILE):
        _, c2, _ = st.columns([2, 1, 2])
        with c2:
            st.image(LOGO_FILE, width=180)
    st.markdown(
        "<h2 style='text-align:center;margin-bottom:.25rem'>"
        "SASTRA SoME End Semester Examination Duty Portal</h2>",
        unsafe_allow_html=True
    )
    st.markdown(
        "<h4 style='text-align:center;margin-top:0'>"
        "School of Mechanical Engineering</h4>",
        unsafe_allow_html=True
    )
    st.markdown("---")


# ═══════════════════════════════════════════════════════════════ #
#               PARSE DUTY FILE (shared helper)                  #
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

@st.cache_data
def load_slots(off_path, on_path):
    def to_df(slots):
        if not slots:
            df = pd.DataFrame(columns=["Date", "Session", "Required"])
            df["Date"] = pd.to_datetime(df["Date"])
            return df
        df = pd.DataFrame(slots)
        df["Date"]     = pd.to_datetime(df["date"], errors="coerce")
        df["Session"]  = df["session"]
        df["Required"] = df["required"].astype(int)
        return df[["Date", "Session", "Required"]]
    return to_df(parse_duty_file(off_path, "Offline")), to_df(parse_duty_file(on_path, "Online"))


# ═══════════════════════════════════════════════════════════════ #
#               WILLINGNESS FILE FUNCTIONS                       #
# ═══════════════════════════════════════════════════════════════ #
def load_willingness():
    # NOTE: Disk/GitHub file is intentionally NOT used.
    # Workflow: Faculty submit via portal → Admin downloads CSV → Admin uploads in Tab 1 → Run Optimizer
    uploaded_bytes = st.session_state.get("uploaded_willingness_bytes", None)
    source = None
    if uploaded_bytes is not None:
        try:
            import io
            source = io.BytesIO(uploaded_bytes)
        except Exception:
            source = None
    if source is None:
        # No uploaded file — return empty (pending_submissions handled separately in get_all_willingness)
        return pd.DataFrame(columns=["Faculty", "Date", "Session", "FacultyClean"])

    try:
        xl = pd.ExcelFile(source)
        df = None
        for sh in xl.sheet_names:
            c = xl.parse(sh)
            c.columns = c.columns.str.strip()
            if {"Faculty", "Date", "Session"}.issubset(set(c.columns)):
                df = c[["Faculty", "Date", "Session"]].copy()
                break
        if df is None:
            c = xl.parse(xl.sheet_names[0])
            c.columns = c.columns.str.strip()
            if len(c.columns) >= 3:
                c = c.rename(columns={c.columns[0]: "Faculty", c.columns[1]: "Date", c.columns[2]: "Session"})
                df = c[["Faculty", "Date", "Session"]].copy()
            else:
                df = pd.DataFrame(columns=["Faculty", "Date", "Session"])
    except Exception:
        df = pd.DataFrame(columns=["Faculty", "Date", "Session"])

    df["Faculty"]      = df["Faculty"].astype(str).str.strip()
    df["Date"]         = df["Date"].astype(str).str.strip()
    df["Session"]      = df["Session"].astype(str).str.strip().str.upper()
    df["FacultyClean"] = df["Faculty"].apply(clean)
    return df.dropna(subset=["Faculty"]).reset_index(drop=True)

def get_all_willingness():
    committed = load_willingness().drop(columns=["FacultyClean"], errors="ignore")
    pending   = st.session_state.get(
        "pending_submissions", pd.DataFrame(columns=["Faculty", "Date", "Session"]))
    combined  = pd.concat([committed, pending], ignore_index=True)
    combined  = combined.drop_duplicates(subset=["Faculty", "Date", "Session"])
    combined["FacultyClean"] = combined["Faculty"].apply(clean)
    return combined

def save_submission(faculty_name, slots):
    new_rows = pd.DataFrame([
        {"Faculty": faculty_name,
         "Date": item["Date"].strftime("%d-%m-%Y"),
         "Session": item["Session"]}
        for item in slots
    ])
    if "pending_submissions" not in st.session_state:
        st.session_state.pending_submissions = pd.DataFrame(columns=["Faculty", "Date", "Session"])
    st.session_state.pending_submissions = pd.concat(
        [st.session_state.pending_submissions, new_rows], ignore_index=True)


# ═══════════════════════════════════════════════════════════════ #
#        FEATURE 1 — SLOT PROBABILITY INDICATOR                  #
# ═══════════════════════════════════════════════════════════════ #
def slot_probability(all_will_df, duty_df, date_val, session_val):
    seats = 0
    if not duty_df.empty:
        m = duty_df[
            (duty_df["Date"].dt.date == date_val) &
            (duty_df["Session"].str.upper() == session_val.upper())
        ]
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
        prob, label, colour = 0.0, "No slot on this day", "#94a3b8"
    elif applicants == 0:
        prob, label, colour = 100.0, "High — you'd be first!", "#16a34a"
    else:
        prob = min(seats / applicants, 1.0) * 100
        if prob >= 70:
            prob, label, colour = prob, "High", "#16a34a"
        elif prob >= 40:
            prob, label, colour = prob, "Medium", "#f59e0b"
        else:
            prob, label, colour = prob, "Low — many applicants", "#dc2626"

    return {"seats": seats, "applicants": applicants,
            "probability": prob, "label": label, "colour": colour}

def render_prob_bar(info: dict, session_label: str):
    pct    = info["probability"]
    colour = info["colour"]
    w      = f"{pct:.0f}%"
    st.markdown(f"""
<div style="background:#fff;border:1px solid #e2e8f0;border-radius:10px;
            padding:10px 14px;margin-bottom:8px;">
  <div style="font-weight:700;font-size:.95rem;color:#0f172a;margin-bottom:4px;">
    {session_label} &nbsp;·&nbsp;
    <span style="color:{colour}">{pct:.0f}% allocation probability</span>
  </div>
  <div style="background:#e5e7eb;border-radius:6px;height:12px;width:100%;margin:4px 0">
    <div style="background:{colour};border-radius:6px;height:12px;width:{w}"></div>
  </div>
  <div style="font-size:.82rem;color:#475569;margin-top:3px;">
    🎯 Seats: <b>{info['seats']}</b> &nbsp;|&nbsp;
    👥 Applied so far: <b>{info['applicants']}</b> &nbsp;|&nbsp;
    {info['label']}
  </div>
</div>
""", unsafe_allow_html=True)


# ═══════════════════════════════════════════════════════════════ #
#        DEVIATION ANALYSIS  (admin-only helper)                 #
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
                    direction_lbl = "after" if direction > 0 else "before"
                    closest = (f"You submitted {adj.strftime('%d-%m-%Y')} {s} "
                               f"→ duty shifted 1 working day {direction_lbl} "
                               f"to {duty_date.strftime('%d-%m-%Y')} {duty_sess}")
                    break
            if closest: break
        return ("Date Adjusted (±1 day)", "📅",
                closest or f"Allotted 1 working day from your submitted willingness", True)

    if ab == "Willingness-ValAdj":
        return ("Valuation-Adjacent", "🗓️",
                f"Allotted on a weekday adjacent to your valuation date "
                f"({duty_date.strftime('%d-%m-%Y')} {duty_sess})", True)

    if ab in ("Auto-Assigned", "Gap-Fill"):
        return ("Auto-Assigned", "⚙️",
                "No willingness submitted — system assigned this duty to meet slot requirements",
                False)

    return ("Not in Willingness", "🔴",
            f"No willingness found near {duty_date.strftime('%d-%m-%Y')} {duty_sess} "
            f"— system assigned to meet slot requirements", False)


def render_deviation_section(allot_rows: pd.DataFrame, will_set: set):
    """Admin-only: full deviation analysis with metrics, per-duty table, and summary."""
    if allot_rows.empty:
        st.info("No allotment data found for this faculty yet.")
        return "Not available", []

    duty_rows = []
    for _, ar in allot_rows.iterrows():
        norm = pd.to_datetime(ar["Date"], dayfirst=True, errors="coerce")
        if pd.isna(norm):
            continue
        sess     = str(ar.get("Session", "")).strip().upper()
        dtype    = str(ar.get("Type", "")).strip()
        alloc_by = str(ar.get("Allocated_By", "")).strip()
        status, emoji, detail, is_matched = classify_duty(
            alloc_by, norm.date(), sess, will_set)
        duty_rows.append({
            "norm_date":  norm.date(),
            "sess":       sess,
            "dtype":      dtype,
            "status":     status,
            "emoji":      emoji,
            "detail":     detail,
            "is_matched": is_matched,
            "date_fmt":   fmt_day(norm.strftime("%d-%m-%Y")),
        })

    total     = len(duty_rows)
    n_exact   = sum(1 for d in duty_rows if d["status"] == "Exact Match")
    n_sess    = sum(1 for d in duty_rows if d["status"] == "Session Adjusted")
    n_adj     = sum(1 for d in duty_rows if "Date Adjusted" in d["status"])
    n_valadj  = sum(1 for d in duty_rows if d["status"] == "Valuation-Adjacent")
    n_no      = sum(1 for d in duty_rows if not d["is_matched"])
    n_matched = n_exact + n_sess + n_adj + n_valadj

    match_pct = n_matched / total * 100 if total else 0.0
    dev_pct   = 100.0 - match_pct

    allot_set    = {(d["norm_date"], d["sess"]) for d in duty_rows}
    exact_overlap = len(will_set & allot_set)
    will_used_pct = exact_overlap / len(will_set) * 100 if will_set else 0.0

    st.markdown("---")
    st.markdown("### 📊 Willingness Match & Deviation")

    m1, m2, m3, m4 = st.columns(4)
    with m1:
        st.metric("Duties Allotted", total)
    with m2:
        st.metric("Willingness Match", f"{match_pct:.1f}%",
                  delta=f"{n_matched} of {total} within window")
    with m3:
        st.metric("Deviation", f"{dev_pct:.1f}%",
                  delta=f"{n_no} unmatched" if n_no else "None",
                  delta_color="inverse" if n_no else "off")
    with m4:
        st.metric("Your Exact Slots Used", f"{will_used_pct:.1f}%",
                  help=f"{exact_overlap} of your {len(will_set)} submitted slots allotted exactly")

    if total == 0:
        return "Not available", []
    elif dev_pct == 0.0:
        st.success("🎉 All duties were allotted exactly as per submitted willingness!")
    elif n_no == 0:
        st.info(
            f"ℹ️ All {total} duties fall within the willingness window. "
            f"{n_sess + n_adj} minor adjustment(s) were made "
            f"(session swap or date shift of ±1/±2 days)."
        )
    else:
        st.warning(
            f"⚠️ {n_no} of {total} duties could not be matched to any submitted willingness "
            "and were system-assigned to meet examination slot requirements."
        )

    st.markdown("#### Duty-wise Breakdown")

    STATUS_BG = {
        "Exact Match":            ("#d1fae5", "#065f46"),
        "Session Adjusted":       ("#fef3c7", "#92400e"),
        "Date Adjusted (±1 day)": ("#ffedd5", "#9a3412"),
        "Valuation-Adjacent":     ("#ede9fe", "#5b21b6"),
        "Not in Willingness":     ("#fee2e2", "#991b1b"),
        "Auto-Assigned":          ("#e5e7eb", "#374151"),
    }

    rows_html = ""
    for d in duty_rows:
        bg, fg = STATUS_BG.get(d["status"], ("#e5e7eb", "#374151"))
        rows_html += f"""
<tr>
  <td style="padding:7px 10px;font-size:.87rem;">{d['date_fmt']}</td>
  <td style="padding:7px 10px;text-align:center;font-weight:700">{d['sess']}</td>
  <td style="padding:7px 10px;text-align:center;">{d['dtype']}</td>
  <td style="padding:7px 10px;">
    <span style="display:inline-block;padding:2px 10px;border-radius:12px;
                 font-size:.8rem;font-weight:700;background:{bg};color:{fg};">
      {d['emoji']} {d['status']}
    </span>
  </td>
  <td style="padding:7px 10px;font-size:.82rem;color:#475569;">{d['detail']}</td>
</tr>"""

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
</table>
</div>
""", unsafe_allow_html=True)

    st.markdown("#### Summary by Category")
    bd = pd.DataFrame({
        "Category": [
            "✅ Exact Match",
            "🔄 Session Adjusted (FN↔AN, same date)",
            "📅 Date Adjusted (±1 working day)",
            "🗓️ Valuation-Adjacent (day before/after val date)",
            "🔴 Not in Willingness / Auto-Assigned",
        ],
        "Count": [n_exact, n_sess, n_adj, n_valadj, n_no],
        "Share %": [
            f"{n_exact/total*100:.1f}%"   if total else "—",
            f"{n_sess/total*100:.1f}%"    if total else "—",
            f"{n_adj/total*100:.1f}%"     if total else "—",
            f"{n_valadj/total*100:.1f}%"  if total else "—",
            f"{n_no/total*100:.1f}%"      if total else "—",
        ],
        "Meaning": [
            "Allotted on the exact date & session you submitted",
            "Same date, but morning/afternoon slot was swapped",
            "Duty shifted by 1 working day from your submitted date",
            "Allotted on a weekday adjacent to your valuation date",
            "No matching date — system assigned to fill slot",
        ],
    })
    st.dataframe(bd, use_container_width=True, hide_index=True)

    dev_lines = [f"Overall match: {match_pct:.1f}%  ({n_matched}/{total} duties within willingness window)"]
    if n_no == 0 and dev_pct == 0:
        dev_lines.append("All duties allotted exactly as per your willingness.")
    else:
        if n_exact   > 0: dev_lines.append(f"  ✅ Exact match          : {n_exact} duty(ies)")
        if n_sess    > 0: dev_lines.append(f"  🔄 Session swapped      : {n_sess} duty(ies) (FN↔AN, same date)")
        if n_adj     > 0: dev_lines.append(f"  📅 Date shifted         : {n_adj} duty(ies) (±1 working day)")
        if n_valadj  > 0: dev_lines.append(f"  🗓️ Valuation-adjacent   : {n_valadj} duty(ies) (day before/after val date)")
        if n_no      > 0: dev_lines.append(f"  🔴 System-assigned      : {n_no} duty(ies) (outside willingness window)")

    match_str = f"Match {match_pct:.1f}%  ({n_matched}/{total})  |  Deviation {dev_pct:.1f}%"
    return match_str, dev_lines


# ═══════════════════════════════════════════════════════════════ #
#                    CALENDAR HEATMAP                            #
# ═══════════════════════════════════════════════════════════════ #
def demand_cat(r):
    if r == 0:   return "No Duty"
    if r < 3:    return "Low (<3)"
    if r <= 7:   return "Medium (3-7)"
    return "High (>7)"

def calendar_frame(duty_df, val_dates, year, month):
    sg   = duty_df.groupby(["Date", "Session"], as_index=False)["Required"].sum()
    dmap = {(d.date(), s): int(r) for d, s, r in zip(sg["Date"], sg["Session"], sg["Required"])}
    ms   = pd.Timestamp(year=year, month=month, day=1)
    fw   = ms.weekday()
    WD   = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
    rows = []
    for dt in pd.date_range(ms, ms + pd.offsets.MonthEnd(0), freq="D"):
        wk = ((dt.day + fw - 1) // 7) + 1
        do = dt.date()
        for sess in ["FN", "AN"]:
            req = dmap.get((do, sess), 0)
            cat = "Valuation Locked" if do in val_dates else demand_cat(req)
            rows.append({"Date": dt, "Week": wk, "Weekday": WD[dt.weekday()],
                         "DayNum": dt.day, "Session": sess, "Required": req,
                         "Category": cat, "DateLabel": dt.strftime("%d-%m-%Y")})
    return pd.DataFrame(rows)

def render_calendar(duty_df, val_dates, title):
    st.markdown(f"#### {title}")
    if duty_df.empty:
        st.info("No slot data available.")
        return

    months = sorted({(d.year, d.month) for d in duty_df["Date"]})

    sg = duty_df.groupby(["Date", "Session"], as_index=False)["Required"].sum()
    duty_map = {}
    for _, row in sg.iterrows():
        duty_map[(row["Date"].date(), str(row["Session"]).upper())] = int(row["Required"])

    val_set = set(val_dates)
    WD_ORDER = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]

    st.markdown(
        "<span style='font-size:.82rem'>"
        "<span style='background:#fce7f3;border:1px solid #f9a8d4;border-radius:4px;"
        "padding:2px 8px;margin-right:6px'>🩷 Valuation Locked</span>"
        "<span style='background:#fff;border:1px solid #cbd5e1;border-radius:4px;"
        "padding:2px 8px'>🔢 Number = duties required</span>"
        "</span>",
        unsafe_allow_html=True
    )
    st.markdown("")

    for yr, mo in months:
        ms   = pd.Timestamp(year=yr, month=mo, day=1)
        me   = ms + pd.offsets.MonthEnd(0)
        days = pd.date_range(ms, me, freq="D")

        fw = ms.weekday()
        grid = []
        week = [None] * fw
        for dt in days:
            week.append(dt.date())
            if len(week) == 7:
                grid.append(week)
                week = []
        if week:
            week += [None] * (7 - len(week))
            grid.append(week)

        st.markdown(
            f"<div style='font-size:.95rem;font-weight:700;color:#1e3a5f;"
            f"margin:14px 0 4px 0'>{calmod.month_name[mo]} {yr}</div>",
            unsafe_allow_html=True
        )

        TH_DAY = (
            "background:#1e3a5f;color:#fff;font-size:.8rem;font-weight:700;"
            "text-align:center;padding:7px 4px;border:1px solid #2d4f7c;"
        )
        TH_SESS = (
            "background:#dbeafe;color:#1e40af;font-size:.7rem;font-weight:700;"
            "text-align:center;padding:4px 2px;border:1px solid #bfdbfe;width:44px;"
        )
        TD_BASE = (
            "text-align:center;padding:5px 2px;border:1px solid #e2e8f0;"
            "vertical-align:middle;min-width:44px;"
        )

        hdr1 = "".join(f"<th colspan='2' style='{TH_DAY}'>{wd}</th>" for wd in WD_ORDER)
        hdr2 = "".join(
            f"<th style='{TH_SESS}'>FN</th><th style='{TH_SESS}'>AN</th>"
            for _ in WD_ORDER
        )

        rows_html = ""
        for week_dates in grid:
            date_row = ""
            for dt in week_dates:
                if dt is None:
                    date_row += (
                        "<td colspan='2' style='background:#ffffff;"
                        "border:1px solid #e2e8f0;height:20px'></td>"
                    )
                else:
                    is_val = dt in val_set
                    is_sun = dt.weekday() == 6
                    bg     = "#fce7f3" if is_val else "#ffffff"
                    color  = "#be185d" if is_val else ("#94a3b8" if is_sun else "#0f172a")
                    label  = f"{dt.day}" + (" 🔒" if is_val else "")
                    date_row += (
                        f"<td colspan='2' style='background:{bg};"
                        f"border:1px solid #e2e8f0;text-align:center;"
                        f"padding:4px 2px 2px 2px;vertical-align:middle'>"
                        f"<span style='font-size:.88rem;font-weight:800;color:{color}'>"
                        f"{label}</span></td>"
                    )
            rows_html += f"<tr>{date_row}</tr>"

            duty_row = ""
            for dt in week_dates:
                if dt is None:
                    duty_row += (
                        "<td style='background:#ffffff;border:1px solid #e2e8f0;"
                        "min-width:44px;height:24px'></td>"
                        "<td style='background:#ffffff;border:1px solid #e2e8f0;"
                        "min-width:44px;height:24px'></td>"
                    )
                else:
                    is_val = dt in val_set
                    for sess in ["FN", "AN"]:
                        req = duty_map.get((dt, sess), 0)
                        if is_val:
                            bg      = "#fce7f3"
                            content = ""
                        elif req == 0:
                            bg      = "#ffffff"
                            content = ""
                        else:
                            bg      = "#ffffff"
                            content = (
                                f"<span style='font-size:.72rem;font-style:italic;"
                                f"font-weight:700;color:#2563eb;letter-spacing:.01em'>"
                                f"{req}</span>"
                            )
                        duty_row += (
                            f"<td style='{TD_BASE}background:{bg};'>"
                            f"{content}</td>"
                        )
            rows_html += f"<tr>{duty_row}</tr>"

        table_html = f"""
<div style="overflow-x:auto;margin-bottom:20px;border-radius:10px;
            box-shadow:0 2px 12px rgba(15,23,42,.08);border:1px solid #e2e8f0">
<table style="border-collapse:collapse;width:100%;table-layout:fixed;
              font-family:Inter,sans-serif;border-radius:10px;overflow:hidden">
  <thead>
    <tr>{hdr1}</tr>
    <tr>{hdr2}</tr>
  </thead>
  <tbody>{rows_html}</tbody>
</table>
</div>
"""
        st.markdown(table_html, unsafe_allow_html=True)

    st.caption("FN = Forenoon  |  AN = Afternoon  |  Numbers = duties required")


# ═══════════════════════════════════════════════════════════════ #
#           OPTIMIZER  (Greedy + Slot Completion)                #
# ═══════════════════════════════════════════════════════════════ #
def run_optimizer(log_box):
    log_lines = []
    def log(m=""):
        log_lines.append(m)
        log_box.code("\n".join(log_lines), language="text")

    log("=" * 62)
    log("  SASTRA SoME Duty Optimizer  (Greedy + Slot Completion)")
    log("  Slot-fill guaranteed | val-safe | session-flip |")
    log("  ±1 biz-day adj | Sat→TA/RA | seniority | ACP 1+1")
    log("=" * 62)

    if not ORTOOLS_OK:
        raise RuntimeError(
            "OR-Tools not installed. Run: pip install ortools")

    # ── Load faculty ─────────────────────────────────────────────
    fr = pd.read_excel(FACULTY_FILE)
    fr.columns = fr.columns.str.strip()
    col_names  = fr.columns.tolist()
    if len(col_names) < 2:
        raise RuntimeError("Faculty_Master.xlsx must have at least 2 columns.")
    fr.rename(columns={col_names[0]: "Name", col_names[1]: "Designation"}, inplace=True)
    fr = fr.dropna(subset=["Name"]).reset_index(drop=True)
    fr["Name"]        = fr["Name"].astype(str).str.strip()
    fr["Designation"] = fr["Designation"].astype(str).str.strip().str.upper()

    ALL_FAC = fr["Name"].tolist()
    FAC_IDX = {n: i for i, n in enumerate(ALL_FAC)}
    N_FAC   = len(ALL_FAC)
    fac_d   = {row["Name"]: (row["Designation"] if row["Designation"] in DESIG_RULES else "TA")
               for _, row in fr.iterrows()}

    # ── ACP type limits ───────────────────────────────────────────
    # Online limit raised to 2 so unfilled online slots can be covered
    # when P-faculty alone are insufficient (e.g. 24-May, 31-May FN)
    acp_online_limit  = {n: 2 for n in ALL_FAC if fac_d.get(n) == "ACP"}
    acp_offline_limit = {n: 1 for n in ALL_FAC if fac_d.get(n) == "ACP"}

    dgroups = defaultdict(list)
    for n, d in fac_d.items():
        dgroups[d].append(n)
    log(f"\n  Faculty loaded     : {N_FAC}")

    # ── Per-faculty valuation dates ──────────────────────────────
    fac_val_dates = {}
    for _, frow in fr.iterrows():
        fname  = frow["Name"]
        vdates = set()
        for c in ["V1", "V2", "V3", "V4", "V5"]:
            if c in frow.index and pd.notna(frow[c]):
                try:
                    vdates.add(pd.to_datetime(frow[c], dayfirst=True).date())
                except Exception:
                    pass
        fac_val_dates[fname] = vdates
    log(f"  Valuation dates    : {sum(1 for v in fac_val_dates.values() if v)} faculty")

    # ── Load willingness ─────────────────────────────────────────
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

    under_sub = []
    for n in submitted:
        required = DESIG_RULES.get(fac_d.get(n, "TA"), (0,0))[0]
        given    = sub_counts.get(n, 0)
        if given < required:
            under_sub.append((n, given, required))

    log(f"  Willingness loaded : {len(submitted)} submitted | {len(non_sub)} not submitted")
    if under_sub:
        log(f"  ⚠ Under-submitted  : {len(under_sub)} faculty submitted fewer dates than required:")
        for n, given, req in sorted(under_sub, key=lambda x: x[0]):
            log(f"      {n}  →  submitted {given} / required {req}")
    if non_sub:
        log(f"  ⚠ No submission    : {len(non_sub)} faculty — will be auto-assigned:")
        for n in non_sub:
            log(f"      {n}")

    log("")
    for fp, lbl in [(OFFLINE_FILE, "Offline"), (ONLINE_FILE, "Online")]:
        log(f"  {lbl:8} : {'✓ found' if os.path.exists(fp) else '✗ MISSING — ' + fp}")

    # ── Load slots ───────────────────────────────────────────────
    s_off = parse_duty_file(OFFLINE_FILE, "Offline")
    s_on  = parse_duty_file(ONLINE_FILE,  "Online")
    ALL_S = s_off + s_on
    NS    = len(ALL_S)
    if NS == 0:
        raise RuntimeError("No exam slots found. Check Offline_Duty.xlsx / Online_Duty.xlsx.")
    log(f"  Slots parsed       : {NS}  ({len(s_off)} offline + {len(s_on)} online)")
    log(f"  Total seats needed : {sum(s['required'] for s in ALL_S)}")

    SAT_DESIG  = {"TA", "RA"}
    slot_dates = {s["date"] for s in ALL_S}

    def is_weekend(d): return d.weekday() >= 5

    def next_biz_day(d, steps):
        step = 1 if steps > 0 else -1
        cur  = d
        cnt  = 0
        while cnt < abs(steps):
            cur += datetime.timedelta(days=step)
            if not is_weekend(cur):
                cnt += 1
        return cur

    # ── Score matrix ─────────────────────────────────────────────
    fexp         = defaultdict(dict)
    fac_will_set = defaultdict(set)

    def set_score(d, k, val):
        d[k] = max(d.get(k, 0), val)

    for _, row in wdf.iterrows():
        n = str(row.get("Faculty", "")).strip()
        if n not in FAC_IDX:
            continue
        dt2     = row["Date"].date()
        sess    = str(row["Session"]).strip().upper()
        opp     = "AN" if sess == "FN" else "FN"
        allowed = DESIG_RULES[fac_d.get(n, "TA")][2]
        fac_will_set[n].add((dt2, sess))

        for tp in allowed:
            set_score(fexp[n], (dt2, sess, tp), W_EXACT)

        if fac_d.get(n) == "ACP":
            for s2 in ["FN", "AN"]:
                set_score(fexp[n], (dt2, s2, "Online"), W_ACP_ONLINE)

        for tp in allowed:
            set_score(fexp[n], (dt2, opp, tp), W_FLIP)

        for direction in [+1, -1]:
            adj = next_biz_day(dt2, direction)
            if adj not in slot_dates:
                continue
            for s2 in ["FN", "AN"]:
                for tp in allowed:
                    set_score(fexp[n], (adj, s2, tp), W_ADJ1)

    for n in ALL_FAC:
        allowed = DESIG_RULES[fac_d.get(n, "TA")][2]
        for vd in fac_val_dates.get(n, set()):
            for direction in [+1, -1]:
                adj = next_biz_day(vd, direction)
                if adj not in slot_dates:
                    continue
                for s2 in ["FN", "AN"]:
                    for tp in allowed:
                        k = (adj, s2, tp)
                        if fexp[n].get(k, 0) < W_VAL_ADJ:
                            set_score(fexp[n], k, W_VAL_ADJ)

    for n in non_sub:
        allowed = DESIG_RULES[fac_d.get(n, "TA")][2]
        for s in ALL_S:
            if s["type"] in allowed:
                set_score(fexp[n], (s["date"], s["session"], s["type"]), W_NON_SUB)

    log(f"  Preference window  : exact + flip + ±1 biz-day (exam dates only)")

    # ── Date overlap diagnostic ───────────────────────────────────
    log(f"\n  ── Date Overlap Diagnostic ──────────────────────────")
    slot_date_set = {s["date"] for s in ALL_S}
    if not wdf.empty:
        will_dates = set(wdf["Date"].dt.date.dropna())
        overlap    = will_dates & slot_date_set
        only_will  = will_dates - slot_date_set
        only_slot  = slot_date_set - will_dates
        log(f"  Slot dates         : {len(slot_date_set)}  "
            f"({min(slot_date_set).strftime('%d-%m-%Y')} → {max(slot_date_set).strftime('%d-%m-%Y')})")
        log(f"  Willingness dates  : {len(will_dates)}  "
            f"({min(will_dates).strftime('%d-%m-%Y')} → {max(will_dates).strftime('%d-%m-%Y')})")
        log(f"  ✓ Overlapping dates: {len(overlap)}")
        if only_will:
            log(f"  ⚠ Will-only dates  : {len(only_will)} dates NOT in any slot "
                f"(these cannot match) — e.g. {sorted(only_will)[:3]}")
        if only_slot:
            log(f"  ⚠ Slot-only dates  : {len(only_slot)} slot dates with NO willingness submitted "
                f"— e.g. {sorted(only_slot)[:3]}")
        if len(overlap) == 0:
            log("  ✗ CRITICAL: Zero overlap between willingness dates and slot dates!")
            log("    → Check date format in Willingness.xlsx (must be DD-MM-YYYY or Excel date)")
            log("    → Check that Willingness.xlsx covers the exam period")
    else:
        log("  ⚠ No willingness data — all assignments will be auto-assigned")

    log(f"\n  Solver: Greedy + Slot Completion Pass")

    # ── Tag helper ───────────────────────────────────────────────
    def tag(fn, k, sc):
        if fn in non_sub:        return "Auto-Assigned"
        if sc >= W_EXACT:        return "Willingness-Exact"
        if sc >= W_ACP_ONLINE:   return "Willingness-ACPOnline"
        if sc >= W_FLIP:         return "Willingness-SessionFlip"
        if sc >= W_ADJ1:         return "Willingness-±1Day"
        if sc >= W_VAL_ADJ:      return "Willingness-ValAdj"
        return "OR-Assigned"

    # ── Greedy solver ─────────────────────────────────────────────
    assigned = []
    log("  Running greedy solver (seniority + willingness priority)...")

    alloc_count    = defaultdict(int)
    used_dates     = defaultdict(set)
    acp_type_count = defaultdict(lambda: {"Online": 0, "Offline": 0})

    def remaining(n):
        return DESIG_RULES[fac_d[n]][0] - alloc_count[n]

    def ok(n, dt_, tp_):
        desig_ = fac_d[n]
        if tp_ not in DESIG_RULES[desig_][2]:                    return False
        if dt_ in fac_val_dates.get(n, set()):                   return False
        if dt_ in used_dates[n]:                                  return False
        if remaining(n) <= 0:                                     return False
        if dt_.weekday() == 5 and desig_ not in SAT_DESIG:       return False
        if desig_ == "ACP":
            if tp_ == "Online"  and acp_type_count[n]["Online"]  >= acp_online_limit.get(n, 1):  return False
            if tp_ == "Offline" and acp_type_count[n]["Offline"] >= acp_offline_limit.get(n, 1): return False
        return True

    # Pass 1: fill slots largest-first
    for sl in sorted(ALL_S, key=lambda s: -s["required"]):
        d2, s2, r2, t2 = sl["date"], sl["session"], sl["required"], sl["type"]
        k     = (d2, s2, t2)
        cands = sorted(
            [(n, fexp[n].get(k, 0)) for n in ALL_FAC if ok(n, d2, t2)],
            key=lambda z: (
                -DESIG_PRIORITY.get(fac_d[z[0]], 0),
                -z[1],
                alloc_count[z[0]]
            ))
        for fn, sc in cands[:r2]:
            alloc_count[fn] += 1
            used_dates[fn].add(d2)
            if fac_d[fn] == "ACP":
                acp_type_count[fn][t2] += 1
            assigned.append({"Name": fn, "Date": d2, "Session": s2,
                             "Type": t2, "Allocated_By": tag(fn, k, sc)})

    # Pass 2: fill remaining faculty duty quotas
    for fn in ALL_FAC:
        if remaining(fn) <= 0:
            continue
        for sl in sorted(ALL_S, key=lambda s: s["date"]):
            if remaining(fn) <= 0:
                break
            d2, s2, t2 = sl["date"], sl["session"], sl["type"]
            if not ok(fn, d2, t2):
                continue
            alloc_count[fn] += 1
            used_dates[fn].add(d2)
            if fac_d[fn] == "ACP":
                acp_type_count[fn][t2] += 1
            assigned.append({"Name": fn, "Date": d2, "Session": s2,
                             "Type": t2, "Allocated_By": "Gap-Fill"})

    # ══════════════════════════════════════════════════════════════
    #  MANDATORY SLOT COMPLETION PASS
    # ══════════════════════════════════════════════════════════════
    log("\n  ── Slot Completion Pass ─────────────────────────────")

    cur_alloc   = defaultdict(int)
    cur_dates   = defaultdict(set)
    acp_tc      = defaultdict(lambda: {"Online": 0, "Offline": 0})
    slot_filled = defaultdict(int)

    for row in assigned:
        fn = row["Name"]; d2 = row["Date"]; t2 = row["Type"]
        cur_alloc[fn] += 1
        cur_dates[fn].add(d2)
        if fac_d.get(fn) == "ACP":
            acp_tc[fn][t2] += 1
        slot_filled[(d2, row["Session"], t2)] += 1

    gaps_before = sum(
        max(0, sl["required"] - slot_filled.get((sl["date"], sl["session"], sl["type"]), 0))
        for sl in ALL_S)
    log(f"  Gaps after solver  : {gaps_before}")

    for sl in ALL_S:
        key    = (sl["date"], sl["session"], sl["type"])
        needed = sl["required"] - slot_filled[key]
        if needed <= 0:
            continue

        for relax in range(6):
            if needed <= 0:
                break
            cands = []
            for fn in ALL_FAC:
                desig_ = fac_d[fn]
                # Relax 5: ignore type constraint (last resort — any faculty fills any slot)
                if relax < 5 and sl["type"] not in DESIG_RULES[desig_][2]:
                    continue
                if relax < 3 and sl["date"] in fac_val_dates.get(fn, set()):
                    continue
                if relax < 2 and sl["date"].weekday() == 5 and desig_ not in SAT_DESIG:
                    continue
                if desig_ == "ACP":
                    lim_on  = acp_online_limit.get(fn, 1)
                    lim_off = acp_offline_limit.get(fn, 1)
                    if sl["type"] == "Online"  and acp_tc[fn]["Online"]  >= lim_on:  continue
                    if sl["type"] == "Offline" and acp_tc[fn]["Offline"] >= lim_off: continue
                if relax < 1 and sl["date"] in cur_dates[fn]:
                    continue
                # Relax 4: ignore max duty limit (force-fill critical unmet slots)
                if relax < 4 and cur_alloc[fn] >= DESIG_RULES[desig_][1]:
                    continue
                cands.append((fn, fexp[fn].get(key, 0)))

            cands.sort(key=lambda z: (
                -DESIG_PRIORITY.get(fac_d[z[0]], 0),
                -z[1],
                cur_alloc[z[0]]
            ))

            for fn, sc in cands:
                if needed <= 0:
                    break
                cur_alloc[fn] += 1
                cur_dates[fn].add(sl["date"])
                if fac_d.get(fn) == "ACP":
                    acp_tc[fn][sl["type"]] += 1
                slot_filled[key] += 1
                needed -= 1
                lbl = "Gap-Fill" if relax == 0 else f"Gap-Fill-R{relax+1}"
                assigned.append({"Name": fn, "Date": sl["date"],
                                 "Session": sl["session"], "Type": sl["type"],
                                 "Allocated_By": lbl})

        if needed > 0:
            log(f"  ⚠ Unfillable: {needed} seat(s) at "
                f"{sl['date']} {sl['session']} {sl['type']} "
                f"(insufficient eligible faculty)")

    gaps_after = sum(
        max(0, sl["required"] - slot_filled.get((sl["date"], sl["session"], sl["type"]), 0))
        for sl in ALL_S)
    log(f"  Gaps after completion: {gaps_after}  "
        f"{'✓ All slots filled!' if gaps_after == 0 else '⚠ Some seats unfilled'}")

    # ── Build output dataframes ───────────────────────────────────
    if not assigned:
        raise RuntimeError("No assignments produced. Check input files.")

    alloc = pd.DataFrame(assigned)
    alloc["Date"] = pd.to_datetime(alloc["Date"]).dt.strftime("%d-%m-%Y")
    alloc = alloc.sort_values(["Date", "Session", "Name"]).reset_index(drop=True)
    alloc.insert(0, "Sl.No", alloc.index + 1)

    sumrows = []
    for fn in ALL_FAC:
        d2  = fac_d[fn]; dr = DESIG_RULES[d2]
        rf  = alloc[alloc["Name"] == fn]; ab = rf["Allocated_By"]
        tot = len(rf)
        wt  = int(ab.isin(WILL_TAGS).sum())
        sumrows.append({
            "Name": fn, "Designation": d2,
            "Submitted":          "Yes" if fn in submitted else "No",
            "Submitted_Count":    sub_counts.get(fn, 0),
            "Required_Duties":    dr[0],
            "Submission_Shortfall": max(0, dr[0] - sub_counts.get(fn, 0)),
            "Assigned_Duties":    tot,
            "Willingness_Total": wt,
            "Match_%":          f"{wt/tot*100:.0f}%" if tot else "N/A",
            "Exact_Match":      int((ab == "Willingness-Exact").sum()),
            "ACP_Online":       int((ab == "Willingness-ACPOnline").sum()),
            "Session_Flip":     int((ab == "Willingness-SessionFlip").sum()),
            "Adj_±1Day":        int((ab == "Willingness-±1Day").sum()),
            "Val_Adj":          int((ab == "Willingness-ValAdj").sum()),
            "Auto_Assigned":    int(ab.isin(["Auto-Assigned","OR-Assigned",
                                             "Gap-Fill","Gap-Fill-R2",
                                             "Gap-Fill-R3","Gap-Fill-R4",
                                             "Gap-Fill-R5"]).sum()),
            "Online":           int((rf["Type"] == "Online").sum()),
            "Offline":          int((rf["Type"] == "Offline").sum()),
            "Gap":              max(dr[0] - tot, 0),
        })
    sumdf = pd.DataFrame(sumrows)

    slotrows = []
    for sl in ALL_S:
        ds  = pd.Timestamp(sl["date"]).strftime("%d-%m-%Y")
        na  = len(alloc[(alloc["Date"] == ds) &
                        (alloc["Session"] == sl["session"]) &
                        (alloc["Type"]    == sl["type"])])
        slotrows.append({
            "Date": ds, "Session": sl["session"], "Type": sl["type"],
            "Required": sl["required"], "Assigned": na,
            "Status": "✓" if na >= sl["required"] else f"✗ short {sl['required']-na}"
        })
    slotdf = pd.DataFrame(slotrows)

    desigrows = []
    for d2 in DESIG_RULES:
        sub2 = sumdf[sumdf["Designation"] == d2]
        if sub2.empty: continue
        on   = int(sub2["Online"].sum())
        of   = int(sub2["Offline"].sum())
        dr   = DESIG_RULES[d2]
        desigrows.append({
            "Designation": d2, "Faculty_Count": len(sub2),
            "Duties_Per_Person": dr[0],
            "Total_Required":   dr[0] * len(sub2),
            "Total_Assigned":   on + of,
            "Willingness_Matched": int(sub2["Willingness_Total"].sum()),
            "Auto_Assigned":    int(sub2["Auto_Assigned"].sum()),
            "Online": on, "Offline": of
        })
    desigdf = pd.DataFrame(desigrows)

    # ── Save to Excel ─────────────────────────────────────────────
    alloc.to_excel(FINAL_ALLOC_FILE, index=False)
    with pd.ExcelWriter(ALLOC_REPORT_FILE, engine="openpyxl") as writer:
        desigdf.to_excel(writer, sheet_name="Designation_Summary", index=False)
        sumdf.to_excel(writer,   sheet_name="Faculty_Summary",     index=False)
        slotdf.to_excel(writer,  sheet_name="Slot_Verification",   index=False)
        alloc.to_excel(writer,   sheet_name="Full_Allocation",     index=False)

    # ── Summary log ───────────────────────────────────────────────
    tot  = len(alloc); ab2 = alloc["Allocated_By"]
    unmet = slotdf[~slotdf["Status"].str.startswith("✓")]
    gaps  = sumdf[sumdf["Gap"] > 0]

    sub_alloc      = alloc[alloc["Name"].isin(submitted)]
    will_matched   = int(sub_alloc["Allocated_By"].isin(WILL_TAGS).sum()) if not sub_alloc.empty else 0
    will_total_sub = len(sub_alloc)
    overall_match_pct = (will_matched / will_total_sub * 100) if will_total_sub > 0 else 0

    sub_sumdf  = sumdf[sumdf["Submitted"] == "Yes"].copy()
    sub_sumdf["_pct"] = sub_sumdf.apply(
        lambda r: r["Willingness_Total"] / r["Assigned_Duties"] * 100
        if r["Assigned_Duties"] > 0 else 0, axis=1)
    above80 = int((sub_sumdf["_pct"] >= 80).sum())

    log(f"\n{'='*62}\n  RESULTS\n{'='*62}")
    log(f"  Total assignments          : {tot}")
    log(f"  ├─ Exact willingness       : {int((ab2 == 'Willingness-Exact').sum())}")
    log(f"  ├─ ACP offline→online      : {int((ab2 == 'Willingness-ACPOnline').sum())}")
    log(f"  ├─ Session flip FN↔AN      : {int((ab2 == 'Willingness-SessionFlip').sum())}")
    log(f"  ├─ Adjacent ±1 biz-day     : {int((ab2 == 'Willingness-±1Day').sum())}")
    log(f"  ├─ Valuation-adj           : {int((ab2 == 'Willingness-ValAdj').sum())}")
    log(f"  └─ Auto / Gap-Fill         : {int(ab2.isin(['Auto-Assigned','OR-Assigned','Gap-Fill','Gap-Fill-R2','Gap-Fill-R3','Gap-Fill-R4']).sum())}")
    log(f"\n  ★ Overall willingness match: {overall_match_pct:.1f}%  ({will_matched}/{will_total_sub})")
    log(f"  ★ Faculty ≥80% match       : {above80}/{len(sub_sumdf)}")

    log(f"\n  Designation-wise breakdown:")
    for dg in ["P", "ACP", "SAP", "AP3", "AP2", "TA", "RA"]:
        sub2 = sumdf[sumdf["Designation"] == dg]
        if sub2.empty: continue
        prio_lbl = "⭐ priority" if DESIG_PRIORITY.get(dg, 0) > 0 else "  fill-in"
        avg_m = sub2.apply(
            lambda r: r["Willingness_Total"] / r["Assigned_Duties"] * 100
            if r["Assigned_Duties"] > 0 else 0, axis=1).mean()
        log(f"  {dg:4} [{prio_lbl}]: {len(sub2):3} faculty | "
            f"avg match {avg_m:.0f}% | auto {int(sub2['Auto_Assigned'].sum())}")

    if not unmet.empty:
        log(f"\n  ⚠ Unfilled slots ({len(unmet)}):")
        for _, r in unmet.iterrows():
            log(f"    {r['Date']} {r['Session']} {r['Type']} — {r['Status']}")
    else:
        log(f"\n  ✓ All {len(slotdf)} slots fully filled")

    if not gaps.empty:
        log(f"  ⚠ Faculty under-assigned ({len(gaps)}):")
        for _, r in gaps.iterrows():
            log(f"    {r['Name']} ({r['Designation']}) — {r['Gap']} duty gap")
    else:
        log(f"  ✓ All faculty assigned correct duty count")

    if non_sub:
        log(f"\n  ⚠ No-submission faculty ({len(non_sub)}) — auto-assigned:")
        for n in non_sub:
            log(f"      {n}  ({fac_d.get(n,'?')})")
    if under_sub:
        log(f"\n  ⚠ Under-submitted faculty ({len(under_sub)}):")
        for n, given, req in under_sub:
            rf2   = alloc[alloc["Name"] == n]
            exact = int(rf2["Allocated_By"].isin(WILL_TAGS).sum())
            log(f"      {n}  ({fac_d.get(n,'?')})  submitted {given}/{req}  →  {exact} matched")

    # ── Match failure analysis ────────────────────────────────────
    log(f"\n  ── Why Match Rate Is Low ────────────────────────────")
    if not wdf.empty:
        slot_date_set2 = {s["date"] for s in ALL_S}
        will_dates2    = set(wdf["Date"].dt.date.dropna())
        overlap2       = will_dates2 & slot_date_set2
        only_will2     = will_dates2 - slot_date_set2
        if len(overlap2) == 0:
            log("  ✗ CRITICAL: Zero date overlap between willingness and slots.")
            log("    Faculty submitted dates that are NOT exam days.")
            log("    Fix: Re-collect willingness using the portal calendar.")
        elif len(only_will2) > len(overlap2):
            log(f"  ⚠ {len(only_will2)} willingness dates fall outside slot dates.")
            log(f"    Only {len(overlap2)} willingness dates coincide with actual exam days.")
            log("    Fix: Ask faculty to re-submit using the portal calendar.")
        else:
            log(f"  ✓ Date overlap exists ({len(overlap2)} dates).")
            log("    Low match likely due to seat contention — many faculty chose same dates.")
            log("    Encourage faculty to spread willingness across different dates.")
    log(f"  Tip: Match rate improves when faculty submit MORE dates spread across the exam period.")

    return alloc, sumdf, slotdf, desigdf


# ═══════════════════════════════════════════════════════════════ #
#                   SESSION STATE DEFAULTS                       #
# ═══════════════════════════════════════════════════════════════ #
_defaults = {
    "logged_in":           False,
    "admin_authenticated": False,
    "panel_mode":          "User View",
    "user_panel_mode":     "Willingness",
    "selected_faculty":    "",
    "selected_slots":      [],
    "confirm_delete":      False,
    "pending_submissions": pd.DataFrame(columns=["Faculty", "Date", "Session"]),
}
for k, val in _defaults.items():
    if k not in st.session_state:
        st.session_state[k] = val


# ═══════════════════════════════════════════════════════════════ #
#                         LOGIN                                  #
# ═══════════════════════════════════════════════════════════════ #
if not st.session_state.logged_in:
    render_header(logo=True)
    _, c2, _ = st.columns([1, 2, 1])
    with c2:
        st.markdown(
            '<div class="card"><div class="card-title">🔒 Faculty Login</div>'
            '<p class="card-sub">Enter your credentials to access the portal.</p></div>',
            unsafe_allow_html=True)
        un = st.text_input("Username")
        pw = st.text_input("Password", type="password")
        if st.button("Sign In", use_container_width=True):
            if un == "SASTRA" and pw == "SASTRA":
                st.session_state.logged_in = True
                st.rerun()
            else:
                st.error("Invalid credentials.")
    st.markdown("---")
    st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
    st.stop()


# ═══════════════════════════════════════════════════════════════ #
#                      LOAD CORE DATA                            #
# ═══════════════════════════════════════════════════════════════ #
if not os.path.exists(FACULTY_FILE):
    st.error(f"**{FACULTY_FILE}** not found. Place it in the same folder as app.py.")
    st.stop()

fac_df = pd.read_excel(FACULTY_FILE)
fac_df.columns = fac_df.columns.str.strip()
_fc = fac_df.columns.tolist()
fac_df.rename(columns={_fc[0]: "Name", _fc[1]: "Designation"}, inplace=True)
fac_df = fac_df.dropna(subset=["Name"]).reset_index(drop=True)
fac_df["Name"]  = fac_df["Name"].astype(str).str.strip()
fac_df["Clean"] = fac_df["Name"].apply(clean)

offline_df, online_df = load_slots(OFFLINE_FILE, ONLINE_FILE)


# ═══════════════════════════════════════════════════════════════ #
#                  HEADER + NOTICE BANNER                        #
# ═══════════════════════════════════════════════════════════════ #
render_header(logo=False)
st.markdown(
    "<div class='blink'><strong>Note:</strong> The University Examination Committee "
    "sincerely appreciates your cooperation. Every effort will be made to accommodate "
    "your willingness while adhering to institutional requirements. Final duty allocation "
    "is carried out using AI-assisted MILP optimization.</div>",
    unsafe_allow_html=True)
st.markdown("")

panel_mode = st.radio("Main Menu", ["User View", "Admin View"], horizontal=True, key="panel_mode")


# ═══════════════════════════════════════════════════════════════ #
#                        ADMIN VIEW                              #
# ═══════════════════════════════════════════════════════════════ #
if panel_mode == "Admin View":
    st.markdown(
        '<div class="card"><div class="card-title">🔒 Admin View</div>'
        '<p class="card-sub">Protected. Enter admin password to continue.</p></div>',
        unsafe_allow_html=True)
    if not st.session_state.admin_authenticated:
        ap = st.text_input("Admin Password", type="password", key="admpw")
        if st.button("Unlock", use_container_width=True):
            if ap == "sathya":
                st.session_state.admin_authenticated = True
                st.rerun()
            else:
                st.error("Incorrect password.")
    else:
        st.success("✅ Admin unlocked.")

        t1, t2, t3, t4 = st.tabs([
            "📋 Willingness Records",
            "🤖 Run Optimizer",
            "📊 View Results",
            "⚙️ Portal Settings",
        ])

        # ── Tab 1: Willingness Records ────────────────────────────
        with t1:
            st.markdown("### Willingness Records")

            st.info(
                "📋 **Workflow:** Faculty submit willingness via this portal → "
                "Admin downloads the collected data as Excel below → "
                "Admin uploads it here to use for optimization. "
                "**The system does NOT read Willingness.xlsx from GitHub/disk automatically.**"
            )

            st.markdown("#### 📤 Upload Collected Willingness File")
            up_src = "uploaded" if st.session_state.get("uploaded_willingness_bytes") else "none"
            if up_src == "uploaded":
                st.success("✅ Willingness file uploaded by admin — optimizer will use this file.")
            else:
                st.warning(
                    "⚠ No willingness file uploaded yet. "
                    "Download the collected willingness below and upload it here before running the optimizer."
                )

            uploaded_will = st.file_uploader(
                "Upload Willingness.xlsx",
                type=["xlsx", "xls"],
                key="will_uploader",
                help="Upload the faculty willingness Excel file."
            )
            if uploaded_will is not None:
                st.session_state["uploaded_willingness_bytes"] = uploaded_will.read()
                st.success(f"✅ '{uploaded_will.name}' uploaded successfully.")
                st.rerun()

            if st.session_state.get("uploaded_willingness_bytes"):
                if st.button("🗑 Remove Uploaded File (revert to folder file)", type="secondary"):
                    del st.session_state["uploaded_willingness_bytes"]
                    st.rerun()

            st.markdown("---")
            st.markdown("#### 📋 Current Willingness Data")
            w_all = get_all_willingness()
            if w_all.empty:
                st.info("No willingness data found.")
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
                st.download_button(
                    "⬇ Download as CSV",
                    data=vdf[["Faculty", "Date", "Session"]].to_csv(index=False).encode("utf-8"),
                    file_name="Willingness.csv", mime="text/csv")
                import io as _io
                _buf = _io.BytesIO()
                vdf[["Faculty", "Date", "Session"]].to_excel(_buf, index=False, engine="openpyxl")
                st.download_button(
                    "⬇ Download as Excel (.xlsx)",
                    data=_buf.getvalue(),
                    file_name="Willingness.xlsx",
                    mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
                )
                st.caption("⬆ After downloading, go to **Tab 2 → Run Optimizer** and upload this file there before running.")

            st.markdown("---")
            st.markdown("#### ⚠ Clear In-Session Submissions")
            st.checkbox("Confirm clearing all in-session submissions", key="confirm_delete")
            if st.button("Clear Session Submissions", type="primary"):
                if st.session_state.confirm_delete:
                    st.session_state.pending_submissions = pd.DataFrame(columns=["Faculty", "Date", "Session"])
                    st.success("Cleared.")
                    st.session_state.confirm_delete = False
                    st.rerun()
                else:
                    st.error("Tick the confirmation checkbox first.")

        # ── Tab 2: Run Optimizer ──────────────────────────────────
        with t2:
            st.markdown("### Run Allocation Optimizer")
            def fstat(f): return "✅ Found" if os.path.exists(f) else "❌ Missing"
            if st.session_state.get("uploaded_willingness_bytes"):
                wstat = "✅ Uploaded by admin (ready for optimizer)"
            else:
                wstat = "⚠ Not uploaded yet — go to Tab 1 to download & re-upload willingness"
            st.markdown(f"""
| File | Purpose | Status |
|---|---|---|
| `Faculty_Master.xlsx` | Faculty list + designations | {fstat(FACULTY_FILE)} |
| `Offline_Duty.xlsx`   | Offline exam slots          | {fstat(OFFLINE_FILE)} |
| `Online_Duty.xlsx`    | Online exam slots           | {fstat(ONLINE_FILE)} |
| `Willingness.xlsx`    | Faculty willingness         | {wstat} |
""")
            wn = get_all_willingness()
            sc2 = wn["Faculty"].nunique() if not wn.empty and "Faculty" in wn.columns else 0
            c1, c2, c3 = st.columns(3)
            c1.metric("Total Faculty",         len(fac_df))
            c2.metric("Willingness Submitted", f"{sc2}/{len(fac_df)}")
            c3.metric("Willingness Rows",      len(wn))

            if not os.path.exists(FACULTY_FILE) or not os.path.exists(OFFLINE_FILE):
                st.error("Faculty_Master.xlsx and Offline_Duty.xlsx are required.")
            elif not ORTOOLS_OK:
                st.error("OR-Tools not installed. Run: pip install ortools")
            else:
                # ── Date Overlap Diagnostic Panel ─────────────────────
                st.markdown("#### 🔍 Pre-Run Diagnostic")
                diag_wdf = get_all_willingness()
                diag_off = parse_duty_file(OFFLINE_FILE, "Offline")
                diag_on  = parse_duty_file(ONLINE_FILE,  "Online")
                diag_slots = diag_off + diag_on
                slot_dates_diag = {s["date"] for s in diag_slots}

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
                        st.error(
                            "🚨 **CRITICAL: Zero date overlap detected!**\n\n"
                            "The dates submitted in Willingness.xlsx do NOT match any exam slot dates.\n\n"
                            "**Likely causes:**\n"
                            "- Faculty submitted dates outside the exam period\n"
                            "- Date format mismatch in Willingness.xlsx (e.g. text vs Excel date)\n"
                            "- Wrong Willingness.xlsx file uploaded\n\n"
                            "**Fix:** Ask faculty to resubmit using this portal's calendar, "
                            "or verify Willingness.xlsx date column format."
                        )
                    elif len(only_will_diag) > len(overlap_diag):
                        st.warning(
                            f"⚠️ **{len(only_will_diag)} willingness dates fall outside exam slot dates** "
                            f"(only {len(overlap_diag)} of {len(will_dates_diag)} dates overlap). "
                            f"Match rate will be low. Ask faculty to resubmit using the portal calendar."
                        )
                    else:
                        st.success(
                            f"✅ {len(overlap_diag)} willingness dates overlap with slot dates. "
                            f"Good coverage — optimizer should produce reasonable match rates."
                        )

                    # Show slot date range vs willingness date range
                    if slot_dates_diag and will_dates_diag:
                        st.markdown(
                            f"**Slot period:** {min(slot_dates_diag).strftime('%d-%m-%Y')} → "
                            f"{max(slot_dates_diag).strftime('%d-%m-%Y')}  &nbsp;|&nbsp;  "
                            f"**Willingness period:** {min(will_dates_diag).strftime('%d-%m-%Y')} → "
                            f"{max(will_dates_diag).strftime('%d-%m-%Y')}",
                            unsafe_allow_html=True
                        )

                    # Show non-overlapping willingness dates as a table
                    if only_will_diag:
                        with st.expander(f"📋 View {len(only_will_diag)} willingness date(s) NOT in any slot"):
                            bad_rows = wdf_diag[wdf_diag["_date"].isin(only_will_diag)]\
                                .drop(columns=["_date","FacultyClean"], errors="ignore")\
                                .reset_index(drop=True)
                            st.dataframe(bad_rows, use_container_width=True, hide_index=True)
                        # Per-faculty breakdown
                        with st.expander("👥 Which faculty submitted dates outside the exam period?"):
                            _bad_fac = wdf_diag[wdf_diag["_date"].isin(only_will_diag)].copy()
                            _bad_fac_grp = (
                                _bad_fac.groupby("Faculty")
                                .agg(OutOfRange_Dates=("Date", "count"))
                                .reset_index()
                                .sort_values("OutOfRange_Dates", ascending=False)
                            )
                            st.dataframe(_bad_fac_grp, use_container_width=True, hide_index=True)
                            st.warning(
                                "⬆ These faculty submitted willingness on dates that are NOT exam days. "
                                "Please ask them to log in again and resubmit using the portal calendar. "
                                "The portal's date picker only shows valid exam dates, "
                                "so resubmitting via the portal will fix this automatically."
                            )
                else:
                    st.info("Upload willingness data and ensure slot files exist to run diagnostic.")

                st.markdown("---")
                st.info(
                    "💡 Recommended: Disable the allotment view (Portal Settings) before "
                    "running, then re-enable after reviewing results.")
                if st.button("▶ Run Optimizer", type="primary", use_container_width=True):
                    lb2 = st.empty()
                    will_bytes_snapshot = st.session_state.get("uploaded_willingness_bytes", None)
                    with st.spinner("Running optimization..."):
                        try:
                            if will_bytes_snapshot is not None:
                                st.session_state["uploaded_willingness_bytes"] = will_bytes_snapshot
                            alloc_out, sumdf_out, slotdf_out, _ = run_optimizer(lb2)
                            st.success("✅ Optimization complete! Review results, then enable the allotment view.")

                            wd_check = get_all_willingness()
                            fr_check = pd.read_excel(FACULTY_FILE)
                            fr_check.columns = fr_check.columns.str.strip()
                            fr_check.rename(columns={fr_check.columns[0]: "Name",
                                                     fr_check.columns[1]: "Designation"}, inplace=True)
                            fr_check["Name"]        = fr_check["Name"].astype(str).str.strip()
                            fr_check["Designation"] = fr_check["Designation"].astype(str).str.strip().str.upper()

                            sub_set  = set(wd_check["Faculty"].str.strip().unique()) if not wd_check.empty else set()
                            sub_cnt  = {}
                            if not wd_check.empty:
                                for nm, grp in wd_check.groupby("Faculty"):
                                    sub_cnt[nm.strip()] = len(grp)

                            no_sub_names    = []
                            under_sub_names = []
                            for _, frow in fr_check.iterrows():
                                nm   = frow["Name"]
                                desig = str(frow["Designation"]).strip().upper()
                                req  = DESIG_RULES.get(desig if desig in DESIG_RULES else "TA", (0,0))[0]
                                if nm not in sub_set:
                                    no_sub_names.append((nm, desig, req))
                                elif sub_cnt.get(nm, 0) < req:
                                    under_sub_names.append((nm, desig, sub_cnt.get(nm,0), req))

                            if no_sub_names or under_sub_names:
                                st.markdown("---")
                                st.markdown("#### ⚠️ Willingness Submission Issues")
                                if no_sub_names:
                                    st.error(f"**{len(no_sub_names)} faculty did not submit willingness:**")
                                    rows = [{"Name": nm, "Designation": DESIG_FULL.get(d, d),
                                             "Required Duties": r} for nm, d, r in no_sub_names]
                                    st.dataframe(pd.DataFrame(rows), use_container_width=True, hide_index=True)
                                if under_sub_names:
                                    st.warning(f"**{len(under_sub_names)} faculty submitted fewer dates than required:**")
                                    rows = [{"Name": nm, "Designation": DESIG_FULL.get(d, d),
                                             "Submitted": g, "Required": r,
                                             "Shortfall": r - g}
                                            for nm, d, g, r in under_sub_names]
                                    st.dataframe(pd.DataFrame(rows), use_container_width=True, hide_index=True)

                            st.balloons()
                        except Exception as e:
                            import traceback
                            st.error(f"Optimizer error: {e}")
                            st.code(traceback.format_exc(), language="text")

        # ── Tab 3: View Results ───────────────────────────────────
        with t3:
            st.markdown("### Allocation Results")
            if not os.path.exists(FINAL_ALLOC_FILE):
                st.info("No results yet. Run the optimizer first.")
            else:
                av  = pd.read_excel(FINAL_ALLOC_FILE)
                rep = {}
                if os.path.exists(ALLOC_REPORT_FILE):
                    xl2 = pd.ExcelFile(ALLOC_REPORT_FILE)
                    for sh in xl2.sheet_names: rep[sh] = xl2.parse(sh)

                tot2 = len(av)
                if tot2 > 0 and "Allocated_By" in av.columns:
                    ab3    = av["Allocated_By"]
                    will_m = int(ab3.isin(WILL_TAGS).sum())
                    aut    = int(ab3.isin(["Auto-Assigned", "OR-Assigned", "Gap-Fill", "Gap-Fill-R2", "Gap-Fill-R3", "Gap-Fill-R4", "Gap-Fill-R5"]).sum())
                    c1, c2, c3, c4 = st.columns(4)
                    c1.metric("Total Assignments",  int(tot2))
                    c2.metric("Willingness Matched", will_m)
                    c3.metric("Auto-Assigned",        aut)
                    c4.metric("Overall Match %",      f"{will_m / tot2 * 100:.1f}%")

                for sh_name, label in [("Designation_Summary", "Designation Summary"),
                                       ("Slot_Verification",   "Slot Verification"),
                                       ("Faculty_Summary",     "Faculty Summary")]:
                    if sh_name in rep:
                        st.markdown(f"#### {label}")
                        if sh_name == "Slot_Verification" and "Status" in rep[sh_name].columns:
                            um = rep[sh_name][~rep[sh_name]["Status"].str.startswith("✓")]
                            total_slots = len(rep[sh_name])
                            met_slots   = total_slots - len(um)
                            if len(um) == 0:
                                st.metric("Slots Fulfilled", f"{met_slots}/{total_slots}",
                                          delta="✅ All Slots Met")
                            else:
                                st.metric("Slots Fulfilled", f"{met_slots}/{total_slots}",
                                          delta=f"⚠ {len(um)} unmet — see rows below",
                                          delta_color="inverse")
                                st.error(
                                    f"⚠️ **{len(um)} slot(s) could not be fully filled.** "
                                    "This usually means there are not enough eligible faculty for that "
                                    "specific slot type. "
                                    "**Fix:** Increase faculty count in Faculty_Master.xlsx, "
                                    "or reduce the required count in Offline_Duty.xlsx / Online_Duty.xlsx."
                                )
                        st.dataframe(rep[sh_name], use_container_width=True, hide_index=True)

                st.markdown("---")
                st.markdown("#### 🔍 Per-Faculty Deviation Analysis")
                st.caption("Select a faculty member to inspect their willingness match and deviation details.")
                admin_fnames = fac_df["Name"].dropna().drop_duplicates().tolist()
                admin_sel    = st.selectbox("Select Faculty", admin_fnames, key="admin_dev_sel")
                admin_sc     = clean(admin_sel)

                wd_admin = load_willingness()
                admin_will_set = set()
                if not wd_admin.empty:
                    wm_admin = fac_mask(wd_admin, admin_sc)
                    wr_admin = wd_admin[wm_admin]
                    if not wr_admin.empty and {"Date", "Session"}.issubset(wr_admin.columns):
                        for d2, s2 in zip(wr_admin["Date"], wr_admin["Session"]):
                            nd = pd.to_datetime(d2, dayfirst=True, errors="coerce")
                            if pd.notna(nd):
                                admin_will_set.add((nd.date(), str(s2).upper()))

                am_admin = fac_mask(av, admin_sc)
                admin_allot_rows = av[am_admin].copy()
                render_deviation_section(admin_allot_rows, admin_will_set)

                st.markdown("---")
                st.markdown("#### Full Allocation Table")
                st.dataframe(av, use_container_width=True, hide_index=True)
                col1, col2 = st.columns(2)
                with col1:
                    with open(FINAL_ALLOC_FILE, "rb") as fh:
                        st.download_button("⬇ Final_Allocation.xlsx", data=fh.read(),
                            file_name="Final_Allocation.xlsx",
                            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
                with col2:
                    with open(ALLOC_REPORT_FILE, "rb") as fh:
                        st.download_button("⬇ Allocation_Report.xlsx", data=fh.read(),
                            file_name="Allocation_Report.xlsx",
                            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

        # ── Tab 4: Portal Settings ────────────────────────────────
        with t4:
            st.markdown("### ⚙️ Portal Settings")
            st.markdown("---")
            st.markdown("#### 🔒 Allotment View — User Access Control")
            st.markdown(
                "Control whether faculty can see their final duty allotment. "
                "**Disable** before running the optimizer. "
                "**Enable** once you have reviewed and approved the allocation.")

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
                    set_gate(True)
                    st.success("Allotment view ENABLED.")
                    st.rerun()
            with dis_col:
                if st.button("🔴 Disable Allotment View", use_container_width=True,
                             disabled=not is_open):
                    set_gate(False)
                    st.warning("Allotment view DISABLED.")
                    st.rerun()

            st.caption(
                "📌 Recommended workflow: Disable → Run Optimizer (Tab 2) → "
                "Review in View Results (Tab 3) → Enable when satisfied.")

            st.markdown("---")
            st.markdown("#### 🗓️ Semester Setting")
            st.markdown(
                "Set which semester is displayed in the portal banner and allotment views. "
                "**Auto-detect** uses the exam slot dates (recommended). "
                "Use manual override only if the auto-detection is incorrect.")
            _sem_options = [
                "Auto-detect",
                "Even Semester (Apr/May End-Semester)",
                "Odd Semester (Nov/Dec End-Semester)",
            ]
            _cur_sem = st.session_state.get("semester_override", "Auto-detect")
            _new_sem = st.selectbox(
                "Semester Display Mode",
                _sem_options,
                index=_sem_options.index(_cur_sem) if _cur_sem in _sem_options else 0,
                key="sem_select"
            )
            if _new_sem != _cur_sem:
                st.session_state["semester_override"] = _new_sem
                st.success(f"Semester set to: **{_new_sem}**")
                st.rerun()

            _preview_slots = parse_duty_file(OFFLINE_FILE, "Offline") + parse_duty_file(ONLINE_FILE, "Online")
            _preview_dates = {s["date"] for s in _preview_slots}
            st.caption(
                f"🔍 Currently showing: **{detect_semester(_preview_dates)}**  "
                f"(Auto-detect reads exam slot months)")

            st.markdown("---")
            st.markdown("#### 🔐 Admin Session")
            if st.button("🔒 Lock Admin View", use_container_width=True):
                st.session_state.admin_authenticated = False
                st.rerun()

    st.markdown("---")
    st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
    st.stop()


# ═══════════════════════════════════════════════════════════════ #
#                        USER VIEW                               #
# ═══════════════════════════════════════════════════════════════ #
user_mode = st.radio("User View", ["Willingness", "Allotment"],
                     horizontal=True, key="user_panel_mode")


# ─── ALLOTMENT VIEW ──────────────────────────────────────────── #
if user_mode == "Allotment":
    st.markdown("### My Allotment Details")

    # Exam period + semester banner
    _aslots = parse_duty_file(OFFLINE_FILE, "Offline") + parse_duty_file(ONLINE_FILE, "Online")
    _aslot_dates = {s["date"] for s in _aslots}
    _asem = detect_semester(_aslot_dates)
    _as, _ae = get_exam_period(_aslot_dates)
    if _as and _ae:
        st.markdown(
            f"<div style='background:#e0f2fe;border:1.5px solid #38bdf8;border-radius:10px;"
            f"padding:10px 16px;margin-bottom:12px;font-size:.93rem;color:#0c4a6e'>"
            f"🎓 <b>{_asem}</b>&nbsp;&nbsp;|&nbsp;&nbsp; 📅 Exam Period: "
            f"<b>{_as.strftime('%d-%m-%Y')} ({_as.strftime('%A')})</b>"
            f" → <b>{_ae.strftime('%d-%m-%Y')} ({_ae.strftime('%A')})</b>"
            f"</div>",
            unsafe_allow_html=True
        )

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
        st.markdown("---")
        st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
        st.stop()

    fnames = fac_df["Name"].dropna().drop_duplicates().tolist()
    sn = st.selectbox("Select Your Name", fnames, key="aname")
    sc = clean(sn)
    frd = fac_df[fac_df["Clean"] == sc]

    vd, qd = [], []
    if not frd.empty:
        fr2 = frd.iloc[0]
        vd = [f"{fmt_day(d.strftime('%d-%m-%Y'))} - Full Day" for d in valuation_dates_for(fr2)]
        qd = [fmt_day(d) for d in qp_dates_for(fr2)]

    wd2 = load_willingness()
    wdisp = []
    if not wd2.empty:
        wm = fac_mask(wd2, sc)
        wr = wd2[wm]
        if not wr.empty and {"Date", "Session"}.issubset(wr.columns):
            for d2, s2 in zip(wr["Date"], wr["Session"]):
                wdisp.append(f"{fmt_day(d2)} - {str(s2).upper()}")

    adf = pd.read_excel(FINAL_ALLOC_FILE) if os.path.exists(FINAL_ALLOC_FILE) else pd.DataFrame()
    idisp = []
    if not adf.empty:
        am = fac_mask(adf, sc)
        allot_rows = adf[am].copy()
        if not allot_rows.empty and {"Date", "Session"}.issubset(allot_rows.columns):
            for _, ar in allot_rows.iterrows():
                dtype    = str(ar.get("Type", "")).strip()
                raw_date = ar["Date"]
                try:
                    dt_obj   = pd.to_datetime(raw_date, dayfirst=True)
                    sat_tag  = " — Saturday" if dt_obj.weekday() == 5 else ""
                except Exception:
                    sat_tag  = ""
                idisp.append(f"{fmt_day(raw_date)} - {str(ar['Session']).upper()} ({dtype}){sat_tag}")

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
        "<div style='margin-top:10px;padding:10px 14px;background:#f1f5f9;"
        "border-radius:8px;border:1px solid #cbd5e1;font-size:.82rem;color:#475569'>"
        "📩 For any specific support or clarification regarding your duty allotment, "
        "please contact the <strong>University Examination Committee, "
        "School of Mechanical Engineering (SoME)</strong>."
        "</div>",
        unsafe_allow_html=True
    )

    msg = build_msg(sn, wdisp, vd, idisp, qd)
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
            f'📲 Open WhatsApp &amp; Send</a>',
            unsafe_allow_html=True)
    else:
        st.caption("Enter your WhatsApp number above to generate the send link.")

    st.markdown("---")
    st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
    st.stop()


# ─── WILLINGNESS SUBMISSION ───────────────────────────────────── #
fnames2   = fac_df["Name"].dropna().drop_duplicates().tolist()

# ── Exam period + semester banner ──────────────────────────────
_all_slots_user = parse_duty_file(OFFLINE_FILE, "Offline") + parse_duty_file(ONLINE_FILE, "Online")
_slot_dates_user = {s["date"] for s in _all_slots_user}
_sem_label = detect_semester(_slot_dates_user)
_exam_start, _exam_end = get_exam_period(_slot_dates_user)

_period_str = ""
if _exam_start and _exam_end:
    _period_str = (
        f"&nbsp;&nbsp;|&nbsp;&nbsp; 📅 Exam Period: "
        f"<b>{_exam_start.strftime('%d-%m-%Y')} ({_exam_start.strftime('%A')})</b>"
        f" → <b>{_exam_end.strftime('%d-%m-%Y')} ({_exam_end.strftime('%A')})</b>"
    )

st.markdown(
    f"<div style='background:#e0f2fe;border:1.5px solid #38bdf8;border-radius:10px;"
    f"padding:10px 16px;margin-bottom:4px;font-size:.93rem;color:#0c4a6e'>"
    f"🎓 <b>{_sem_label}</b>{_period_str}"
    f"</div>",
    unsafe_allow_html=True
)

if _exam_start and _exam_end:
    st.markdown(
        f"<div style='background:#fef9c3;border:1.5px solid #fde047;border-radius:10px;"
        f"padding:10px 16px;margin-bottom:12px;font-size:.9rem;color:#713f12'>"
        f"⚠️ <b>Important:</b> Please select willingness dates <b>only within the exam period</b> "
        f"(<b>{_exam_start.strftime('%d %b %Y')}</b> to <b>{_exam_end.strftime('%d %b %Y')}</b>). "
        f"Dates outside this range cannot be matched and will reduce your allocation priority."
        f"</div>",
        unsafe_allow_html=True
    )

sel_name  = st.selectbox("Select Your Name", fnames2)
sel_clean = clean(sel_name)
fmatch    = fac_df[fac_df["Clean"] == sel_clean]

if fmatch.empty:
    st.error("Faculty not found. Contact admin.")
    st.stop()

frow2   = fmatch.iloc[0]
desig2  = str(frow2["Designation"]).strip().upper()
req_cnt = DUTY_STRUCTURE.get(desig2, 0)
val_d2  = valuation_dates_for(frow2)
val_s2  = set(val_d2)

if req_cnt == 0:
    st.warning(f"Designation '{desig2}' not recognised. Contact admin.")

sopts = online_df.copy() if desig2 == "P" else offline_df.copy()
sopts["Date"]     = pd.to_datetime(sopts["Date"], errors="coerce")
sopts["DateOnly"] = sopts["Date"].dt.date
valid_d = sorted([d for d in sopts["DateOnly"].dropna().unique() if d not in val_s2])

if st.session_state.selected_faculty != sel_clean:
    st.session_state.selected_faculty = sel_clean
    st.session_state.selected_slots   = []
    st.session_state["picked_date"]   = valid_d[0] if valid_d else None

if "picked_date" not in st.session_state:
    st.session_state["picked_date"] = valid_d[0] if valid_d else None

left, right = st.columns([1, 1.4])

with left:
    st.subheader("Willingness Submission")
    st.write(f"**Designation:** {DESIG_FULL.get(desig2, desig2)}")
    duties_min, duties_max = DESIG_RULES.get(desig2, (0, 0, []))[:2]
    duties_label = str(duties_min) if duties_min == duties_max else f"{duties_min}–{duties_max}"
    st.write(f"**Duties to be Allotted:** {duties_label}")
    st.write(f"**Options to Select:** {req_cnt}")

    st.markdown("""
<div style="background:#f0f7ff;border:1.5px solid #93c5fd;border-radius:12px;
            padding:14px 16px;margin:8px 0 14px 0">
  <div style="font-size:.88rem;font-weight:800;color:#1e3a5f;margin-bottom:8px;">
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
</div>
""", unsafe_allow_html=True)

    if desig2 == "ACP":
        st.info(
            "ACP faculty will receive one Online and one Offline duty. "
            "Please select all available dates from the Offline calendar. "
            "Online duty will be assigned automatically from your submitted dates.")

    if not valid_d:
        st.warning("No dates available for selection.")
    else:
        picked = st.selectbox(
            "Choose Online Date" if desig2 == "P" else "Choose Offline Date",
            valid_d, key="picked_date",
            format_func=lambda d: d.strftime("%d-%m-%Y (%A)"))
        avail = set(sopts[sopts["DateOnly"] == picked]["Session"].dropna().astype(str).str.upper())

        all_will_now = get_all_willingness()
        any_prob_shown = False
        for sess_opt in ["FN", "AN"]:
            if sess_opt in avail:
                prob_info = slot_probability(all_will_now, sopts, picked, sess_opt)
                seats_val = prob_info["seats"]
                appl_val  = prob_info["applicants"]
                if seats_val > 0 and appl_val >= 3 * seats_val:
                    render_prob_bar(prob_info, sess_opt)
                    any_prob_shown = True
        if any_prob_shown:
            st.caption("⚡ Probability shown when demand is 3× or more than available seats.")

        b1, b2 = st.columns(2)
        with b1:
            add_fn = st.button("➕ Add FN", use_container_width=True,
                disabled=("FN" not in avail or len(st.session_state.selected_slots) >= req_cnt))
        with b2:
            add_an = st.button("➕ Add AN", use_container_width=True,
                disabled=("AN" not in avail or len(st.session_state.selected_slots) >= req_cnt))

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
        st.dataframe(sdf[["Sl.No", "Date", "Day", "Session"]], use_container_width=True, hide_index=True)
        rm = st.selectbox("Sl.No to remove", options=sdf["Sl.No"].tolist())
        if st.button("🗑 Remove Row", use_container_width=True):
            tgt = sdf[sdf["Sl.No"] == rm].iloc[0]
            td  = pd.to_datetime(tgt["Date"], dayfirst=True).date()
            ts  = tgt["Session"]
            st.session_state.selected_slots = [
                s for s in st.session_state.selected_slots
                if not (s["Date"] == td and s["Session"] == ts)]
            st.rerun()

    wl2 = load_willingness()
    already = (sel_clean in wl2["FacultyClean"].tolist()
               if not wl2.empty and "FacultyClean" in wl2.columns else False)
    pend = st.session_state.get("pending_submissions", pd.DataFrame(columns=["Faculty", "Date", "Session"]))
    if not pend.empty and "Faculty" in pend.columns:
        already = already or (sel_name in pend["Faculty"].tolist())

    st.markdown("### Submit Willingness")
    rem2 = max(req_cnt - len(st.session_state.selected_slots), 0)

    if already:
        st.warning("⚠ You have already submitted your willingness.")
    elif rem2 == 0 and req_cnt > 0:
        st.success(f"✅ All {req_cnt} options selected. Ready to submit.")
    else:
        st.info(f"Select {rem2} more option(s) to enable submission.")

    if st.button("✅ Submit Willingness",
                 disabled=(already or len(st.session_state.selected_slots) != req_cnt),
                 use_container_width=True):
        save_submission(sel_name, st.session_state.selected_slots)
        st.session_state.selected_slots = []
        st.toast("Willingness submitted successfully! ✅", icon="✅")
        st.success(
            "Thank you for submitting. The final duty allocation will be carried out "
            "using MILP optimization. Check this portal for allotment updates.")

with right:
    if desig2 == "P":
        render_calendar(online_df, val_s2, "Online Duty Calendar")
    else:
        render_calendar(offline_df, val_s2, "Offline Duty Calendar")

st.markdown("---")
st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
