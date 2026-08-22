------------------------------------------------------------------------
-- OCP-0009 — ACKERMANN, the example `⊢lexrec` was built to unlock.
--
-- ★ THIS FILE USED TO BE DELIBERATELY RED.  It was written first, as the
--   test that states the missing power: `⊢lexrec` lived at a Γ₅ whose
--   measure slots were `Π Nat Nat`, so the carrier was BAKED IN as `Nat`
--   and the obligation below was UNMEETABLE — under `Π Nat _` the bound
--   variable is a `Nat`, and `⊢fst` needs a `Σ'`.
--
--   It is green now.  `⊢lexrec`'s carrier is a context variable `A : U`
--   (see NbEPDirDBExamplesLex), so the obligation reads `Π (El A) Nat`
--   with A := `pairCode`, and that is exactly what `⊢fst`/`⊢snd` prove.
--
-- WHY ACKERMANN NEEDS A PAIR CARRIER.  Its descent is genuinely on the
-- PAIR (m, n):
--     ack 0       n       = suc n
--     ack (suc m) 0       = ack m 1                 -- m drops
--     ack (suc m) (suc n) = ack m (ack (suc m) n)   -- inner: m held, n
--                                                   --   drops; outer: m
--                                                   --   drops
-- so the two measures are μ₁ = fst and μ₂ = snd on ℕ×ℕ.  `⊢amrec` cannot
-- do it (a SINGLE ℕ measure), which is what ARCHITECTURE recorded as
-- "Ackermann-style terminations are out of reach".
--
-- ⚠ SCOPE — read this before claiming Ackermann is derived.  What is
--   machine-checked below is the INSTANTIATION DATA: all four of Γ₅'s
--   slots at the pair carrier (A, cP, μ₁, μ₂).  The fifth ingredient, the
--   STEP function `stp : LStepT`, is the Ackermann recursion itself and is
--   NOT written here — it is the remaining work, and it is the interesting
--   part.  See the closing note.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Ack where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Nat; U; Σ'
        ; RTm; var; lam; fst; snd; ⌜Σ⌝; ⌜Nat⌝
        ; Π )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⟶ᵀ_; El-⌜Σ⌝; El-⌜Nat⌝
        ; _⊢_∷_; ⊢var; here; ⊢lam; ⊢fst; ⊢snd; ⊢conv; ⊢⌜Nat⌝; ⊢⌜Σ⌝
        ; _⊢ty_; ty-El )
open import DirectedHoTT.Metatheory.Injectivity
  using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ )

------------------------------------------------------------------------
-- 1. THE CARRIER: ℕ × ℕ, as a CODE so it can be a `U`-element — which is
--    what Γ₅'s carrier slot `A : U` demands.
------------------------------------------------------------------------

pairCode : {Γ : Cx} → RTm Γ
pairCode = ⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝

⊢pairCode : ◇ ⊢ pairCode ∷ U
⊢pairCode = ⊢⌜Σ⌝ ⊢⌜Nat⌝ ⊢⌜Nat⌝

-- `El` of the code REDUCES to the pair type — it is not definitional, so
-- every projection below goes through `⊢conv`.
El-pair : El (pairCode {⌊ ◇ ▹ El pairCode ⌋}) ⟶ᵀ* Σ' (El ⌜Nat⌝) (El ⌜Nat⌝)
El-pair = stepᵀ (El-⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝) doneᵀ

El-nat : El (⌜Nat⌝ {⌊ ◇ ▹ El pairCode ⌋}) ⟶ᵀ* Nat
El-nat = stepᵀ El-⌜Nat⌝ doneᵀ

------------------------------------------------------------------------
-- 2. ★ THE OBLIGATION THAT WAS UNMEETABLE.  The two measures, at the
--    PAIR carrier — `μ₁ = fst`, `μ₂ = snd`.
------------------------------------------------------------------------

ackμ₁ ackμ₂ : {Γ : Cx} → RTm Γ
ackμ₁ = lam (fst (var vz))
ackμ₂ = lam (snd (var vz))

⊢ackμ₁ : ◇ ⊢ ackμ₁ ∷ Π (El pairCode) Nat
⊢ackμ₁ =
  ⊢lam (ty-El ⊢pairCode)
    (⊢conv (⊢fst (⊢conv (⊢var here) (red→≅ᵀ El-pair)))
           (red→≅ᵀ El-nat))

-- ⚠ `⊢snd`'s result is `subTy (single (fst p)) B`.  Here B is `El ⌜Nat⌝`,
--   a CLOSED code, so the substitution computes away and the conversion is
--   the same `El-⌜Nat⌝` as for `fst`.  A dependent second component would
--   not be so kind.
⊢ackμ₂ : ◇ ⊢ ackμ₂ ∷ Π (El pairCode) Nat
⊢ackμ₂ =
  ⊢lam (ty-El ⊢pairCode)
    (⊢conv (⊢snd (⊢conv (⊢var here) (red→≅ᵀ El-pair)))
           (red→≅ᵀ El-nat))

------------------------------------------------------------------------
-- 3. THE MOTIVE.  Ackermann returns a `Nat` whatever the pair, so the
--    motive is constant — but it still has to be a CODE-valued function,
--    because Γ₅'s `cP` slot is `Π (El A) U`.
------------------------------------------------------------------------

ackMot : {Γ : Cx} → RTm Γ
ackMot = lam ⌜Nat⌝

⊢ackMot : ◇ ⊢ ackMot ∷ Π (El pairCode) U
⊢ackMot = ⊢lam (ty-El ⊢pairCode) ⊢⌜Nat⌝

------------------------------------------------------------------------
-- ★★ WHAT THIS BUYS, AND WHAT IS LEFT.
--
-- Γ₅ = ((( ◇ ▹ U ) ▹ Π (El A) U ) ▹ Π (El A) Nat ) ▹ Π (El A) Nat
--         ↑ A        ↑ cP           ↑ μ₁            ↑ μ₂
--
-- All four slots are now inhabited at the pair carrier, machine-checked:
--     A  := pairCode   ⊢pairCode
--     cP := ackMot     ⊢ackMot
--     μ₁ := ackμ₁      ⊢ackμ₁     ← was unmeetable at the ℕ carrier
--     μ₂ := ackμ₂      ⊢ackμ₂     ← ditto
--
-- ⚠ STILL OPEN, and it is the interesting half: the STEP function
--   `stp : LStepT`, i.e. Ackermann's own recursion, which must produce
--   `P x` from `rec₁ : (y) → μ₁ y < μ₁ x → P y` and
--   `rec₂ : (y) → μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y`.  Its three cases are
--   the three Ackermann equations, and each picks a recursor:
--     ack 0       n       ↦ suc n            no recursive call
--     ack (suc m) 0       ↦ rec₁ (m, 1)      fst drops
--     ack (suc m) (suc n) ↦ rec₁ (m, rec₂ (suc m, n))
--                                            inner rec₂: fst held, snd
--                                            drops; outer rec₁: fst drops
--   Writing it needs case analysis on both components, i.e. two `natrec`s
--   on `fst x` and `snd x` with the pair rebuilt by `⊢pair` — mechanical,
--   but not short, and it is what would let `⊢lexrec` be applied end to
--   end via `sub-lemma`.
--
-- ⚠ AND NOTE WHAT ACKERMANN DOES *NOT* SHOW.  It is structurally
--   recursive at higher type (see SpikeAckT: nested `natrec` with motive
--   `Nat → Nat`, 0.61s / 0.14 GB), so it never NEEDED a measure.  It is a
--   demonstration that the lexicographic combinator applies, not evidence
--   that it is necessary.  For that, `div`/`gcd`/quicksort are the cases.
------------------------------------------------------------------------
