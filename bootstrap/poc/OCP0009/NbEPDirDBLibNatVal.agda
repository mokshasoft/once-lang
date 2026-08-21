------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — WHAT A CLOSED `Nat` EVALUATES TO (THE DATA).
--
-- ★ THIS MODULE IS DELIBERATELY THREE LINES OF CONTENT AND TWO IMPORTS.
--   `amrec-unfold-z`/`-s` are conditional on the measure reaching a
--   numeral, and at an OPEN context that premise is real information the
--   CALLER supplies.  Stating it needs nothing but `⟶*`.
--
-- ⚠ THE THEOREM `natEval` — that a CLOSED `Nat` always reaches a numeral
--   — now lives in `…LibNatEval`, because its proof runs through
--   canonicity and drags `…Canon → …Fund → …FundSem`/`…FundSN` with it.
--   Keeping the two together made `…LibAmrec` pay for canonicity on
--   behalf of 31 importers, none of whom used it (`PERF-2026-08-21.md`
--   §2: 18–23% of every amrec client's interface closure).
--
--   ⇒ IF YOU ADD ANYTHING HERE, CHECK ITS IMPORTS.  The value of this
--     module is precisely that it is cheap to depend on.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibNatVal where

open import poc.OCP0009.NbEPDirDBPi using ( RTm; ε; nzero; nsuc )
open import poc.OCP0009.NbEPDirDBType using ( _⟶*_ )

data NatVal (n : RTm ε) : Set where
  nv-zero : n ⟶* nzero                → NatVal n
  nv-suc  : (k : RTm ε) → n ⟶* nsuc k → NatVal n
