-- ================================================================
-- SASTRA SoME Duty Portal — Supabase Schema
-- Run this ONCE in Supabase → SQL Editor → New Query → Run
-- ================================================================

-- 1. Faculty (login + profile + valuation dates)
CREATE TABLE IF NOT EXISTS faculty (
    id              SERIAL PRIMARY KEY,
    faculty_id      TEXT UNIQUE NOT NULL,        -- e.g. C870, RS1051
    name            TEXT NOT NULL,
    designation     TEXT NOT NULL,               -- raw string from Excel e.g. "AP 3"
    email           TEXT,
    phone           TEXT,
    password_hash   TEXT NOT NULL,
    must_change_pw  BOOLEAN DEFAULT TRUE,
    is_admin        BOOLEAN DEFAULT FALSE,
    v1 DATE, v2 DATE, v3 DATE, v4 DATE, v5 DATE,
    qp_date_1 DATE, qp_date_2 DATE,
    created_at      TIMESTAMPTZ DEFAULT NOW()
);

-- 2. Password reset tokens
CREATE TABLE IF NOT EXISTS password_reset_tokens (
    id          SERIAL PRIMARY KEY,
    faculty_id  TEXT REFERENCES faculty(faculty_id) ON DELETE CASCADE,
    token       TEXT UNIQUE NOT NULL,
    expires_at  TIMESTAMPTZ NOT NULL,
    used        BOOLEAN DEFAULT FALSE,
    created_at  TIMESTAMPTZ DEFAULT NOW()
);

-- 3. Offline duty slots
CREATE TABLE IF NOT EXISTS offline_duty (
    id          SERIAL PRIMARY KEY,
    duty_date   DATE NOT NULL,
    session     TEXT NOT NULL,   -- FN or AN
    required    INTEGER NOT NULL DEFAULT 1
);

-- 4. Online duty slots
CREATE TABLE IF NOT EXISTS online_duty (
    id          SERIAL PRIMARY KEY,
    duty_date   DATE NOT NULL,
    session     TEXT NOT NULL,
    required    INTEGER NOT NULL DEFAULT 1
);

-- 5. Willingness submitted by faculty
CREATE TABLE IF NOT EXISTS willingness (
    id           SERIAL PRIMARY KEY,
    faculty_id   TEXT REFERENCES faculty(faculty_id) ON DELETE CASCADE,
    faculty_name TEXT NOT NULL,
    duty_date    DATE NOT NULL,
    session      TEXT NOT NULL,
    submitted_at TIMESTAMPTZ DEFAULT NOW(),
    UNIQUE(faculty_id, duty_date, session)
);

-- 6. Final allocation output
CREATE TABLE IF NOT EXISTS final_allocation (
    id           SERIAL PRIMARY KEY,
    faculty_id   TEXT REFERENCES faculty(faculty_id) ON DELETE CASCADE,
    faculty_name TEXT NOT NULL,
    designation  TEXT NOT NULL,
    duty_date    DATE NOT NULL,
    session      TEXT NOT NULL,
    duty_type    TEXT NOT NULL,     -- Offline or Online
    allocated_by TEXT,              -- Willingness-Exact, Auto-Assigned etc.
    allocated_at TIMESTAMPTZ DEFAULT NOW()
);

-- 7. Portal settings (gate open/closed, semester override etc.)
CREATE TABLE IF NOT EXISTS portal_settings (
    key   TEXT PRIMARY KEY,
    value TEXT NOT NULL
);

-- Default settings
INSERT INTO portal_settings (key, value)
VALUES ('allotment_gate', '0'),
       ('semester_override', 'Auto-detect')
ON CONFLICT (key) DO NOTHING;
