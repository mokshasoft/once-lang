------------------------------------------------------------------------
-- OCP-0009 — ACKERMANN, the example `⊢lexrec` was built to unlock.
--
-- ⚠⚠ THIS FILE IS DELIBERATELY RED.  It is written FIRST, as the test
--   that states the missing power, and it goes green only once
--   `⊢lexrec` is generalised to an arbitrary carrier.
--
-- WHY ACKERMANN NEEDS A PAIR CARRIER.  Its descent is genuinely on the
-- PAIR (m, n):
--     ack 0       n       = suc n
--     ack (suc m) 0       = ack m 1                 -- m drops
--     ack (suc m) (suc n) = ack m (ack (suc m) n)   -- inner: m held, n
--                                                   --   drops; outer: m
--                                                   --   drops
-- so the two measures are μ₁ = fst and μ₂ = snd on ℕ×ℕ.  `⊢amrec` cannot
-- do it (a SINGLE ℕ measure), which is exactly what ARCHITECTURE recorded
-- as "Ackermann-style terminations are out of reach".
--
-- ★ EVERYTHING THE KERNEL NEEDS IS ALREADY THERE:
--     ⌜Σ⌝/⊢⌜Σ⌝, ⊢pair/⊢fst/⊢snd, βfst/βsnd (so the projections COMPUTE),
--     El-⌜Σ⌝ : El (⌜Σ⌝ c d) ⟶ᵀ Σ' (El c) (El d), El-⌜Nat⌝, and
--     `sub-lemma`, which is what makes ⊢lexrec INSTANTIABLE at all.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesAck where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Nat; U
        ; RTm; var; nzero; nsuc; lam; app; pair; fst; snd; ⌜Σ⌝; ⌜Nat⌝
        ; Π; subTy )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; there; ⊢lam; ⊢fst; ⊢snd; ⊢⌜Nat⌝; ⊢⌜Σ⌝
        ; _⊢ty_; ty-Nat; ty-El )

------------------------------------------------------------------------
-- 1. THE CARRIER: ℕ × ℕ, as a CODE so it can be a `U`-element.
------------------------------------------------------------------------

pairCode : {Γ : Cx} → RTm Γ
pairCode = ⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝

⊢pairCode : ◇ ⊢ pairCode ∷ U
⊢pairCode = ⊢⌜Σ⌝ ⊢⌜Nat⌝ ⊢⌜Nat⌝

------------------------------------------------------------------------
-- 2. THE TWO MEASURES — the projections.
------------------------------------------------------------------------

ackμ₁ ackμ₂ : {Γ : Cx} → RTm Γ
ackμ₁ = lam (fst (var vz))
ackμ₂ = lam (snd (var vz))

------------------------------------------------------------------------
-- 3. ★ THE RED LINE.
--
-- `⊢lexrec` lives at Γ₅, whose measure slots are `Π Nat Nat` — the
-- carrier is BAKED IN as `Nat`, not a variable.  So instantiating it via
-- `sub-lemma` demands exactly this obligation, and it is UNMEETABLE:
-- under `Π Nat _` the bound variable is a `Nat`, and `⊢fst` needs a
-- `Σ'`.  No substitution can repair it, because σ cannot rewrite the
-- domain that Γ₅ fixed.
--
-- THIS IS THE MISSING POWER, stated as a type.  It goes green when the
-- carrier becomes a context variable `A : U` (as in Dogfood's Γ₄), at
-- which point the obligation reads `Π (El A) Nat` with A := pairCode.
------------------------------------------------------------------------

⊢ackμ₁-at-Nat-carrier : ◇ ⊢ ackμ₁ ∷ Π Nat Nat
⊢ackμ₁-at-Nat-carrier = ⊢lam ty-Nat (⊢fst (⊢var here))
