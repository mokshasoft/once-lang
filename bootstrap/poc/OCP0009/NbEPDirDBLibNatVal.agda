------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — A CLOSED `Nat` REACHES A NUMERAL.
--
-- ★ WHY THE LIBRARY WANTS THIS.  `amrec-unfold-z`/`-s` are conditional on
--   the measure reaching a numeral — `subTm (single x) m ⟶* nzero` or
--   `⟶* nsuc k`.  At a CLOSED carrier value that premise is not
--   information the caller has; it is a THEOREM, and making users prove it
--   would be ceremony.  This module proves it once so the closed case can
--   discharge it.
--
-- ⚠ AND THE BOUNDARY IS CANONICITY, NOT NORMALISATION.  `wnorm` works at
--   an ARBITRARY context; `canNat` is `RTm ε` only.  So at an OPEN context
--   a measure still normalises — its normal form is just a NEUTRAL
--   containing the free variable, which is not a numeral and never will
--   be.  There the premise is genuine information the caller supplies and
--   the library cannot.  Two lemmas, two domains; the conditional form is
--   not a weaker fallback.
--
-- THE PROOF IS `consistency`'s PATTERN, three steps:
--   1. `wnorm c-◇` — the closed term reaches a normal form;
--   2. that form cannot step, so `progress` gives `Canon` and `canNat`
--      gives `NatShape`: it is `nzero` or `nsuc k`;
--   3. compose with the reduction from step 1.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibNatVal where

open import normalizer.Syntax.Types using ( _≡_; refl; ⊥-elim )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; RTm; RTy; nzero; nsuc; Nat )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _⊢_∷_; _⟶*_; done; step; ⊢ctx_; c-◇ )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans )
open import poc.OCP0009.NbEPDirDBLR using ( WN; mkWN; IsNormal )
open import poc.OCP0009.NbEPDirDBFund using ( wnorm )
open import poc.OCP0009.NbEPDirDBSubj using ( sr* )
open import poc.OCP0009.NbEPDirDBCanon
  using ( Prog; prog-can; prog-step; progress; canNat; NatShape; ns-zero; ns-suc )

------------------------------------------------------------------------
-- what a closed `Nat` evaluates to
------------------------------------------------------------------------

data NatVal (n : RTm ε) : Set where
  nv-zero : n ⟶* nzero            → NatVal n
  nv-suc  : (k : RTm ε) → n ⟶* nsuc k → NatVal n

------------------------------------------------------------------------
-- ★★ THE THEOREM.
------------------------------------------------------------------------

natEval : {n : RTm ε} → ◇ ⊢ n ∷ Nat → NatVal n
natEval {n = n} d with wnorm c-◇ d
... | mkWN v r nrm snv with progress (sr* d r)
...   | prog-step st = ⊥-elim (nrm st)
...   | prog-can can with canNat (sr* d r) can
...     | ns-zero  = nv-zero r
...     | ns-suc k = nv-suc k r
