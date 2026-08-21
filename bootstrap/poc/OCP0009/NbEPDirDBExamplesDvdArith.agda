------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — `…LibDvdArith` EXERCISED.
--
-- ⚠ EVERY LIBRARY IS EXERCISED BY AN EXAMPLE (standing rule, 2026-08-21).
--   `…LibDvdArith` is green on its own; that says its definitions
--   typecheck, not that a client can call them.  This file calls them.
--
-- ★ TWO LEVELS, and both are needed:
--
--   1. AT VARIABLES — the theorems' actual content.  `⊢assoc` and `⊢dist`
--      are stated at arbitrary `Γ ⊢ · ∷ Nat`, so instantiating them at
--      CONTEXT VARIABLES is the honest test: nothing computes, and the
--      internal `natrec`s have to carry the whole proof.
--
--   2. AT NUMERALS — `2 ∣ 4` and `2 ∣ 6` give `2 ∣ 10`, with the witness
--      `2 + 3 = 5`.  ⭐ This is the level that exercises `mul-suc`, the
--      computation rule `…LibMul` was missing: the hypotheses' equations
--      `4 ≡ 2 * 2` and `6 ≡ 3 * 2` only hold because `mulTm` REDUCES, and
--      the reduct needs the peel `mul-suc` supplies.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesDvdArith where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; Nat
        ; RTm; var; nzero; nsuc )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc
        ; _⟶*_; done; step; natrec-zero; natrec-suc
        ; csymᵀ )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; ⟶ᵀ*-Idʳ )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-nsuc )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMul using ( mulTm; ⊢mul; mul-zero )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( IdN; reflN; ⊢reflN )
open import poc.OCP0009.NbEPDirDBLibDvd using ( dvdT; dvd-intro )
open import poc.OCP0009.NbEPDirDBLibDvdArith
  using ( assocB; ⊢assoc; distB; ⊢dist; mul-suc; dvdSum; ⊢dvd-plus )

------------------------------------------------------------------------
-- 1. AT VARIABLES.  Context `◇ ▹ Nat ▹ Nat ▹ Nat`: [0] = c, [1] = b,
--    [2] = a.
------------------------------------------------------------------------

Γ₃ : Ctx
Γ₃ = ((◇ ▹ Nat) ▹ Nat) ▹ Nat

A B C : RTm ⌊ Γ₃ ⌋
A = var (vs (vs vz))
B = var (vs vz)
C = var vz

dA : Γ₃ ⊢ A ∷ Nat
dA = ⊢var (there (there here))

dB : Γ₃ ⊢ B ∷ Nat
dB = ⊢var (there here)

dC : Γ₃ ⊢ C ∷ Nat
dC = ⊢var here

-- ★ `(a + b) + c = a + (b + c)` at three OPEN naturals.
assoc-open : Γ₃ ⊢ _ ∷ IdN (plusTm (plusTm A B) C) (plusTm A (plusTm B C))
assoc-open = ⊢assoc dA dB dC

-- ★ `(a + b) * c = a * c + b * c` at three OPEN naturals.
dist-open : Γ₃ ⊢ _ ∷ IdN (mulTm (plusTm A B) C)
                         (plusTm (mulTm A C) (mulTm B C))
dist-open = ⊢dist dA dB dC

------------------------------------------------------------------------
-- 2. AT NUMERALS — `2 ∣ 4`, `2 ∣ 6`, therefore `2 ∣ (4 + 6)`.
--
-- ⚠ THE HYPOTHESES ARE NOT FREE.  `dvdT 2 4` wants `4 ≡ 2 * 2`, and
--   `mulTm 2 2` reduces to `4` only by unfolding `mul-suc` twice and
--   `mul-zero` once, each under the `plusTm` that `mul-suc` leaves behind.
------------------------------------------------------------------------

n0 n1 n2 n3 n4 n6 : {Γ : Cx} → RTm Γ
n0 = nzero
n1 = nsuc n0
n2 = nsuc n1
n3 = nsuc n2
n4 = nsuc n3
n6 = nsuc (nsuc n4)

⊢n2 : Γ₃ ⊢ n2 ∷ Nat
⊢n2 = ⊢nsuc (⊢nsuc ⊢nzero)

⊢n3 : Γ₃ ⊢ n3 ∷ Nat
⊢n3 = ⊢nsuc ⊢n2

⊢n4 : Γ₃ ⊢ n4 ∷ Nat
⊢n4 = ⊢nsuc ⊢n3

⊢n6 : Γ₃ ⊢ n6 ∷ Nat
⊢n6 = ⊢nsuc (⊢nsuc ⊢n4)

-- ⚠ `mul-suc` LEAVES A `+` BEHIND, so each rung needs `2 + ·` discharged
--   too — `mul k 2 ⟶* 2 + (k-1)*2`, not straight to a numeral.  ⭐ `plusTm`
--   recurses on its FIRST argument, so `2 + X` peels in three definitional
--   steps whatever `X` is; that is the whole of `plus2`.
plus2 : {Γ : Cx} {X Y : RTm Γ} → X ⟶* Y → plusTm n2 X ⟶* nsuc (nsuc Y)
plus2 r =
  ⟶*-trans (step (natrec-suc _ _ _) done)
    (⟶*-nsuc (⟶*-trans (step (natrec-suc _ _ _) done)
      (⟶*-nsuc (⟶*-trans (step (natrec-zero _ _) done) r))))

-- `k * 2 ⟶* <the numeral>`, by `mul-suc` down to `mul-zero`.
mul2-0 : mulTm n0 (n2 {⌊ Γ₃ ⌋}) ⟶* n0
mul2-0 = mul-zero n2

mul2-1 : mulTm n1 (n2 {⌊ Γ₃ ⌋}) ⟶* n2
mul2-1 = ⟶*-trans (mul-suc n0 n2) (plus2 mul2-0)

mul2-2 : mulTm n2 (n2 {⌊ Γ₃ ⌋}) ⟶* n4
mul2-2 = ⟶*-trans (mul-suc n1 n2) (plus2 mul2-1)

mul2-3 : mulTm n3 (n2 {⌊ Γ₃ ⌋}) ⟶* n6
mul2-3 = ⟶*-trans (mul-suc n2 n2) (plus2 mul2-2)

-- `4 ≡ 2 * 2` and `6 ≡ 3 * 2`, internally.
eq4 : Γ₃ ⊢ reflN n4 ∷ IdN n4 (mulTm n2 n2)
eq4 = ⊢conv (⊢reflN ⊢n4) (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idʳ mul2-2)))

eq6 : Γ₃ ⊢ reflN n6 ∷ IdN n6 (mulTm n3 n2)
eq6 = ⊢conv (⊢reflN ⊢n6) (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idʳ mul2-3)))

d2∣4 : Γ₃ ⊢ _ ∷ dvdT n2 n4
d2∣4 = dvd-intro ⊢n2 ⊢n4 ⊢n2 eq4

d2∣6 : Γ₃ ⊢ _ ∷ dvdT n2 n6
d2∣6 = dvd-intro ⊢n2 ⊢n6 ⊢n3 eq6

-- ★★★ THE EXERCISE: divisibility is closed under `+`.
d2∣10 : Γ₃ ⊢ dvdSum n2 n4 n6 _ _ ∷ dvdT n2 (plusTm n4 n6)
d2∣10 = ⊢dvd-plus ⊢n2 ⊢n4 ⊢n6 d2∣4 d2∣6

------------------------------------------------------------------------
-- 3. …AND AT VARIABLES, WHICH IS WHAT GAP B ACTUALLY NEEDS.  gcd's step
--    hands over hypotheses about OPEN terms, so this is the shape the
--    divisibility spec will call.
------------------------------------------------------------------------

-- ★ THE SHAPE GAP B WILL CALL, and the reason it is stated as a module
--   rather than a closed term: gcd's step supplies its hypotheses at
--   whatever context the recursion has reached, so the client is always
--   "some Γ with these five terms typed", never a fixed context.
module OpenSum (Γ : Ctx) (d x y hx hy : RTm ⌊ Γ ⌋)
               (dd  : Γ ⊢ d  ∷ Nat)
               (dx  : Γ ⊢ x  ∷ Nat)
               (dy  : Γ ⊢ y  ∷ Nat)
               (dhx : Γ ⊢ hx ∷ dvdT d x)
               (dhy : Γ ⊢ hy ∷ dvdT d y)
               where

  sum : Γ ⊢ dvdSum d x y hx hy ∷ dvdT d (plusTm x y)
  sum = ⊢dvd-plus dd dx dy dhx dhy
