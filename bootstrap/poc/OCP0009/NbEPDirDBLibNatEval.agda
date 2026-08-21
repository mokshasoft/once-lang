------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — A CLOSED `Nat` REACHES A NUMERAL (THE THEOREM).
--
-- ★ SPLIT OUT OF `…LibNatVal` 2026-08-21, AND THE SPLIT IS THE POINT.
--   `NatVal` is a three-constructor datatype needing only `Pi`/`Type`.
--   `natEval` is a THEOREM whose proof runs through canonicity, so it
--   drags `…Canon → …Fund → …FundSem`/`…FundSN` — ~5.5 MB of interface
--   and six modules — into everything that imports it.
--
--   ⇒ MEASURED (`PERF-2026-08-21.md` §2): `…LibAmrec` imported this for
--     its CLOSED-CARRIER convenience layer alone (43 lines out of 3472),
--     and passed the whole canonicity stack on to its 31 importers.
--     Separating the datatype from the theorem cuts 18–23% off every
--     amrec client's interface closure. Nothing was weakened; the cost
--     simply now falls on the code that actually uses the theorem.
--
-- ⚠ THE BOUNDARY IS CANONICITY, NOT NORMALISATION.  `wnorm` works at an
--   ARBITRARY context; `canNat` is `RTm ε` only.  At an OPEN context a
--   measure still normalises — to a NEUTRAL containing the free variable,
--   which is not a numeral and never will be.  There the premise is
--   genuine information the caller supplies and no library can discharge
--   it.  Two lemmas, two domains; the conditional form in `…LibAmrec` is
--   the correct one whenever anything is open, not a weaker fallback.
--   ⭐ That is exactly why the gcd clients never needed this module.
--
-- THE PROOF IS `consistency`'s PATTERN, three steps:
--   1. `wnorm c-◇` — the closed term reaches a normal form;
--   2. that form cannot step, so `progress` gives `Canon` and `canNat`
--      gives `NatShape`: it is `nzero` or `nsuc k`;
--   3. compose with the reduction from step 1.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibNatEval where

open import normalizer.Syntax.Types using ( ⊥-elim )
open import poc.OCP0009.NbEPDirDBPi using ( RTm; ε; Nat )
open import poc.OCP0009.NbEPDirDBType using ( ◇; _⊢_∷_; c-◇ )
open import poc.OCP0009.NbEPDirDBLR using ( mkWN )
open import poc.OCP0009.NbEPDirDBFund using ( wnorm )
open import poc.OCP0009.NbEPDirDBSubj using ( sr* )
open import poc.OCP0009.NbEPDirDBCanon
  using ( progress; prog-can; prog-step; canNat; ns-zero; ns-suc )
open import poc.OCP0009.NbEPDirDBLibNatVal using ( NatVal; nv-zero; nv-suc )

natEval : {n : RTm ε} → ◇ ⊢ n ∷ Nat → NatVal n
natEval {n = n} d with wnorm c-◇ d
... | mkWN v r nrm snv with progress (sr* d r)
...   | prog-step st = ⊥-elim (nrm st)
...   | prog-can can with canNat (sr* d r) can
...     | ns-zero  = nv-zero r
...     | ns-suc k = nv-suc k r
