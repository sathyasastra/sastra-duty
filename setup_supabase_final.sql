-- ============================================================
-- SASTRA SoME Duty Portal — Supabase Schema Setup
-- Run this entire script once in Supabase SQL Editor
-- ============================================================

-- 1. Faculty accounts (login + profile)
CREATE TABLE IF NOT EXISTS faculty (
    id              SERIAL PRIMARY KEY,
    faculty_id      TEXT UNIQUE NOT NULL,        -- e.g. C870, RS602, C2086
    name            TEXT NOT NULL,
    designation     TEXT NOT NULL,
    email           TEXT,
    password_hash   TEXT NOT NULL,               -- bcrypt hash
    must_change_pw  BOOLEAN DEFAULT TRUE,        -- force change on first login
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
    session     TEXT NOT NULL,
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

-- 6. Final allocation
CREATE TABLE IF NOT EXISTS final_allocation (
    id           SERIAL PRIMARY KEY,
    faculty_id   TEXT REFERENCES faculty(faculty_id) ON DELETE CASCADE,
    faculty_name TEXT NOT NULL,
    designation  TEXT NOT NULL,
    duty_date    DATE NOT NULL,
    session      TEXT NOT NULL,
    mode         TEXT NOT NULL,
    allot_reason TEXT,
    allocated_at TIMESTAMPTZ DEFAULT NOW()
);

-- ============================================================
-- NOTE: Faculty IDs are taken directly from Faculty_Master.xlsx
-- (format: C870, RS602, C2086 etc.) — no ID generation needed.
-- ============================================================
