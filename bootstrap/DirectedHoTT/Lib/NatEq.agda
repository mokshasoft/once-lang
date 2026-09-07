------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ DECIDABLE EQUALITY ON `Nat`, AT THE OBJECT LEVEL,
-- as a 0/1-valued term.
--
--     eqNatTm a b  =  isZero ((a ∸ b) ⊔ (b ∸ a))
--
-- ★ WHY MONUS AND NOT A DOUBLE `natrec`.  `a ≡ b` iff neither monus is
--   positive, and `Lib/Monus` already proves what that needs
--   (`monus-zero`, `monus-suc`, and `a ≤ b → a ∸ b ≡ 0` — see
--   `eq4-order-premise-bridge`).  A nested `natrec` would have to
--   re-derive all of it inside a step whose motive is a function.
--
-- ⚠ BOOLEANS ARE `0`/`1` HERE, matching `tools/gen-knot.py`'s `BOOL_PREM`
--   convention ("booleans are `0`/`1` at the object level") and
--   `Knot/Pw`'s constant-`Nat` motive.  `isZero` returns `1` on zero, so
--   `eqNatTm a a ⟶* 1`.
--
-- ★ THE FIRST CUSTOMER is the occurrence check's `cVar-vz` row: a
--   variable at LEVEL `m` occurs at level `k` exactly when `k ≡ m`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.NatEq where
open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; natrec; nzero; Nat )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢natrec; ⊢nzero; ty-Nat )
open import DirectedHoTT.Lib.NatNum using ( num; ⊢num )
open import DirectedHoTT.Lib.NatMax using ( maxTm; ⊢max )
open import DirectedHoTT.Lib.Monus using ( monusTm; ⊢monus )

-- ★ `isZero 0 = 1`, `isZero (suc _) = 0`.  ⚠ The step ignores BOTH the
--   number and the IH, so it is `nzero` outright — `Lib/Monus.predTm`
--   is the same shape with the number kept instead.
isZeroTm : {Γ : Cx} → RTm Γ → RTm Γ
isZeroTm n = natrec (num 1) nzero n

⊢isZero : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} →
          Γ ⊢ n ∷ Nat → Γ ⊢ isZeroTm n ∷ Nat
⊢isZero dn = ⊢natrec ty-Nat (⊢num 1) ⊢nzero dn

eqNatTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
eqNatTm a b = isZeroTm (maxTm (monusTm a b) (monusTm b a))

⊢eqNat : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ eqNatTm a b ∷ Nat
⊢eqNat da db = ⊢isZero (⊢max (⊢monus da db) (⊢monus db da))
