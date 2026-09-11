------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ `Lib/IFold`'s REDUCTION LAYER, ONCE.
--
-- ★★★ WHY THIS EXISTS.  `Lib/ISzRed` and `Lib/IOccRed` carried two
--   copies of the same development — an `AllIH` family and three
--   reduction lemmas over it — that differ in FOUR knobs and NOTHING
--   else.  Measured, side by side:
--
--       ISzRed                          IOccRed
--       AllIH (r : Maybeℕ)              AllIH (k : RTm Γ)
--       sameSortAt r j                  scopeAt true j
--       addIf (a + m)                   maxIf (maxℕ a m)
--       IHof b h m = h ⟶* num m         IHof b k h m = app h k ⟶* num m
--
--   and the three lemma BODIES are identical line for line:
--
--       Tail-red p iι       ha aih-ι          = ha
--       Tail-red p (iκ κ C) ha (aih-κ h)      = Tail-red p C ha h
--       Tail-red p (iρ j C) ha (aih-ρ m hm h) =
--         Tail-red p C (Step-red (pick p j) … ha hm) h
--       SumStep-red true  … = Tail-red … hm h
--       SumStep-red false … = Sum-red  … h
--
-- ★★ AND THE OBJECT-LEVEL FUNCTIONS WERE ALREADY SHARED.  `szsTail` and
--   `occTail` are BOTH `IFold.Fold.ifTail`, renamed at two
--   instantiations (`Lib/ISzSort:41`, `Lib/IOcc:128`).  Only the
--   REDUCTION layer was duplicated — so this module is exactly the
--   missing twin of `IFold.Fold`, and it takes the same knobs.
--
-- ⚠⚠ IT MUST INSTANTIATE `IFold.Fold` ITSELF, not take `ifTail`/`ifSum`
--   as parameters.  The lemmas PATTERN-MATCH on the `ICon`, so the fold
--   has to COMPUTE; an opaque function parameter is stuck and every
--   clause fails.  ⇒ the 13 `Fold` parameters are re-taken here, and the
--   client passes the same ones it already passes to `Fold`.
--
-- ⚠⚠ AND THE REDUCTION KNOBS LIVE IN A NESTED `Red`, not alongside the
--   fold's.  `step-red`'s conclusion must mention `ifStep`, which only
--   exists once `Fold` is opened — and a top-level COPY of it does not
--   serve: `stepOf op b acc h` and `ifStep b acc h` agree only AFTER
--   casing on `b`, and at the `iρ` clause `b` is `pick r j`, abstract.
--   Measured: that exact mismatch, `stepOf … != ifStep …`.
--   ⇒ two levels.  `comb`/`IHof` stay top-level because they do not
--     mention the fold at all.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.IFoldRed where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; subst )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; Sub; Ren; ICon; iι; iρ; iκ; fst; snd; subTy; renTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢ty_; _⊢_∷_; _⟶*_ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )
import DirectedHoTT.Lib.IFold as IF

-- ★ the unit of evidence a SKIPPED field supplies.
data OK : Set where
  ok : OK

-- ★ the two helpers the reduction parameters' TYPES need, hence
--   top-level: a module parameter's type cannot mention its own body.
comb : (ℕ → ℕ → ℕ) → 𝔹 → ℕ → ℕ → ℕ
comb nop true  a m = nop a m
comb nop false a m = a

IHof : {Γ : Cx} {Ext : Cx → Set} →
       ({Γ' : Cx} → Ext Γ' → RTm Γ' → ℕ → Set) →
       𝔹 → Ext Γ → RTm Γ → ℕ → Set
IHof H true  e h m = H e h m
IHof H false e h m = OK

------------------------------------------------------------------------
-- ★★★ THE MODULE.  Parameters 1–13 are `IFold.Fold`'s, verbatim;
--   14–18 are the reduction layer's, and they are exactly the four knobs
--   the two clients differed by (plus the `iι` base, which is the one
--   place their proofs genuinely diverge: `done` for `sz`, one β for
--   `occ`, because `occ`'s motive is `Π Nat Nat` and `sz`'s is `Nat`).
------------------------------------------------------------------------

module FoldRed
  (R    : Set)
  (rsum : {Δ : Cx} → ICon Δ → R)
  (pick : {Δ : Cx} → R → RTm Δ → 𝔹)
  (A    : {Γ : Cx} → RTy Γ)
  (tyA  : {Γ : Ctx} → Γ ⊢ty A)
  (subA : {Γ Δ : Cx} {σ : Sub Γ Δ} → subTy σ A ≡ A)
  (renA : {Γ Δ : Cx} {ρ : Ren Γ Δ} → renTy ρ A ≡ A)
  (z    : {Γ : Cx} → RTm Γ)
  (op   : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ)
  (nd   : {Γ : Cx} → RTm Γ → RTm Γ)
  (⊢z   : {Γ : Ctx} → Γ ⊢ z ∷ A)
  (⊢op  : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
          Γ ⊢ a ∷ A → Γ ⊢ b ∷ A → Γ ⊢ op a b ∷ A)
  (⊢nd  : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ A → Γ ⊢ nd a ∷ A)
  ------------------------------------------------------------------------
  where

  open IF.Fold R rsum pick A tyA subA renA z op nd ⊢z ⊢op ⊢nd public

  module Red
    (Ext   : Cx → Set)
    (Holds : {Γ : Cx} → Ext Γ → RTm Γ → ℕ → Set)
    (nop   : ℕ → ℕ → ℕ)
    (step-red : {Γ : Cx} (b : 𝔹) (e : Ext Γ) {acc h : RTm Γ} (a m : ℕ) →
                Holds e acc a → IHof Holds b e h m →
                Holds e (ifStep b acc h) (comb nop b a m))
    (sum-base : {Γ : Cx} (e : Ext Γ) → Holds e (z {Γ}) zero)
    -- ★★★ THE SEEDING OBLIGATION — not an arbitrary algebraic law.
    --   `ifSumStep true` seeds the accumulator with the first counted
    --   field and then hands off to `ifTail`, which expects `m` — but the
    --   `AllIH` node carries `comb nop true zero m`, i.e. `nop zero m`.
    --   `ISzRed` got away with it because `0 + m` REDUCES to `m`, and
    --   `IOccRed` because `maxℕ 0 m` does.  With `nop` abstract neither
    --   holds, and the mismatch is exactly `(nop zero m) != m`.
    --
    --   ★★★ WHAT IT ACTUALLY SAYS.  `ifSum` SEEDS with the first counted
    --     field instead of starting at `z`, which is what keeps a
    --     trailing `op _ z` out of the emitted term (`Lib/IFold:303`).
    --     `nop zero m ≡ m` is EXACTLY the statement that seeding agrees
    --     with "start at `z` and combine" — i.e. it is that
    --     optimisation's CORRECTNESS CONDITION.  ⇒ it cannot be dropped
    --     without either giving up the seeding or moving the obligation
    --     into every client row; both were tried and both are worse.
    --
    --   ⚠ It is nonetheless the first non-TYPING law in this library
    --     tree — `FUTURE.md`'s audit found 57 law-carrying parameters,
    --     every one a typing or stability law, and named `op`'s missing
    --     unit law specifically.  It costs `λ m → refl` at both clients:
    --     `0 + m` and `maxℕ zero m` both reduce to `m` (the latter via
    --     `maxℕ a b = a + monusℕ b a` and `monusℕ a zero = a`).
    (seed-sound : (m : ℕ) → nop zero m ≡ m)
    where

    ------------------------------------------------------------------------
    -- ★ ONE NODE PER FIELD.  ⚠ `m` is EXPLICIT: at a skipped field
    --   `IHof _ false _ _ m` is `OK` and `m` would be a meta with nothing
    --   to solve it.  Skipped fields pass `0`.
    ------------------------------------------------------------------------
    data AllIH {Γ : Cx} (r : R) (e : Ext Γ) :
               {Δ : Cx} → ℕ → ICon Δ → RTm Γ → ℕ → Set where
      aih-ι : {a : ℕ} {Δ : Cx} {ihs : RTm Γ} → AllIH r e a (iι {Δ}) ihs a
      aih-κ : {a : ℕ} {Δ : Cx} {κ : RTm Δ} {C : ICon (Δ ∙)} {ihs : RTm Γ} {n : ℕ} →
              AllIH r e a C ihs n → AllIH r e a (iκ κ C) ihs n
      aih-ρ : {a : ℕ} {Δ : Cx} {j : RTm Δ} {C : ICon (Δ ∙)} {ihs : RTm Γ} {n : ℕ}
              (m : ℕ) →
              IHof Holds (pick r j) e (fst ihs) m →
              AllIH r e (comb nop (pick r j) a m) C (snd ihs) n →
              AllIH r e a (iρ j C) ihs n

    ------------------------------------------------------------------------
    -- ★★★ THE THREE LEMMAS, ONCE.
    ------------------------------------------------------------------------
    ifTail-red : {Γ : Cx} (r : R) (e : Ext Γ) {Δ : Cx} (C : ICon Δ)
                 {acc ihs : RTm Γ} {a n : ℕ} →
                 Holds e acc a → AllIH r e a C ihs n →
                 Holds e (ifTail r C acc ihs) n
    ifTail-red r e iι       ha aih-ι          = ha
    ifTail-red r e (iκ κ C) ha (aih-κ h)      = ifTail-red r e C ha h
    ifTail-red r e (iρ j C) ha (aih-ρ m hm h) =
      ifTail-red r e C (step-red (pick r j) e _ m ha hm) h

    ifSum-red : {Γ : Cx} (r : R) (e : Ext Γ) {Δ : Cx} (C : ICon Δ)
                {ihs : RTm Γ} {n : ℕ} →
                AllIH r e zero C ihs n → Holds e (ifSum r C ihs) n
    ifSumStep-red : {Γ : Cx} (b : 𝔹) (r : R) (e : Ext Γ) {Δ : Cx} (C : ICon (Δ ∙))
                    {ihs : RTm Γ} (m : ℕ) {n : ℕ} →
                    IHof Holds b e (fst ihs) m →
                    AllIH r e (comb nop b zero m) C (snd ihs) n →
                    Holds e (ifSumStep b r C ihs) n

    ifSum-red r e iι       aih-ι          = sum-base e
    ifSum-red r e (iκ κ C) (aih-κ h)      = ifSum-red r e C h
    ifSum-red r e (iρ j C) (aih-ρ m hm h) = ifSumStep-red (pick r j) r e C m hm h

    ifSumStep-red {Γ} true r e {Δ} C {ihs} m {n} hm h =
      ifTail-red r e C hm
        (subst (λ a → AllIH r e a C (snd ihs) n) (seed-sound m) h)
    ifSumStep-red false r e C m hm h = ifSum-red r e C h
