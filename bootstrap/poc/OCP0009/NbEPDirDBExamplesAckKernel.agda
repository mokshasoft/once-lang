------------------------------------------------------------------------
-- OCP-0009 — ACKERMANN THE CHEAP WAY, as a COST CONTROL.
--
-- Ackermann is definable in System T by NESTED `natrec` with a
-- higher-order motive — the outer recursion on `m` returns a FUNCTION
-- `Nat → Nat`, the inner one recurses on `n`:
--
--     ack 0       = suc
--     ack (suc m) = λ n → natrec (ack m 1) (λ n' r → ack m r) n
--
-- so it needs NO well-founded machinery at all: no `⊢lexrec`, no measure,
-- no `Hom Nat` order, no `Γ₅`.  That makes it the right control for "how
-- much of the lexrec cost is the DERIVATION and how much is the deep
-- generic CONTEXT `Γ₅`?"
--
-- ⚠ This is NOT a replacement for `⊢lexrec`.  It proves nothing about
--   lexicographic descent — it exploits the fact that Ackermann happens to
--   be structurally recursive at higher type.  `⊢lexrec` earns its keep on
--   the recursions that are NOT (`div`, `gcd`, quicksort on a pair
--   measure).  Kept only as the cost baseline.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesAckKernel where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; RTy; Nat; RTm; var; vz; vs; nzero; nsuc; natrec; lam; app; Π )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ty-Nat; ty-Π )

------------------------------------------------------------------------
-- THE TERM.  ctx inside the step: vz = n, vs = ackm, vs² = m', vs³ = m
------------------------------------------------------------------------

ackStep : RTm ((((⌊ ◇ ⌋ ∙) ∙) ∙))
ackStep =
  lam (natrec (app (var (vs vz)) (nsuc nzero))            -- ack (suc m) 0     = ack m 1
              (app (var (vs (vs (vs vz)))) (var vz))      -- ack (suc m) (suc n) = ack m r
              (var vz))

ackTm : RTm ⌊ ◇ ⌋
ackTm = lam (natrec (lam (nsuc (var vz))) ackStep (var vz))

------------------------------------------------------------------------
-- THE DERIVATION.  The outer `natrec` motive is `Π Nat Nat` — a FUNCTION,
-- which is the whole trick; the inner motive is plain `Nat`.
------------------------------------------------------------------------

⊢ack : ◇ ⊢ ackTm ∷ Π Nat (Π Nat Nat)
⊢ack =
  ⊢lam ty-Nat
    (⊢natrec (ty-Π ty-Nat ty-Nat)
             (⊢lam ty-Nat (⊢nsuc (⊢var here)))
             (⊢lam ty-Nat
               (⊢natrec ty-Nat
                        (⊢app (⊢var (there here)) (⊢nsuc ⊢nzero))
                        (⊢app (⊢var (there (there (there here)))) (⊢var here))
                        (⊢var here)))
             (⊢var here))
