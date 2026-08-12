------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — THE PAIR-CARRIER KIT.
--
-- `Σ' Nat Nat` with the two projections as measures is the carrier every
-- lexicographic use site has needed so far, and every one of them has had
-- to rebuild the same six lines. This is those lines, once.
--
-- ★★ D10 — THE DESCENT HELPERS TAKE THEIR TERMS EXPLICITLY, AND THAT IS
--    NOT A STYLE CHOICE.  A recursive call descends by projecting out of
--    a pair it has just BUILT, so the projection's argument is the
--    recursive call's own argument — and when that argument is itself a
--    nested recursive call, an IMPLICIT solved by unification against it
--    is the `agda-plus-inversion-trap` in another costume.  Measured on
--    `SpikeLexAck` (Ackermann, whose outer call consumes its inner one):
--
--      inner call inline, implicits    192.5 s / 4.41 GB
--      hoisted behind a `Def`, explicit 10.1 s / 0.84 GB
--
--    19× time, 5.3× memory, both cold on an idle box.  ⚠ 4.41 GB against
--    a 5.5 GB cap is a 20% margin, so the inline form fails as soon as
--    anything else is running — which is how this was found.
--
--    ⇒ **Hoist a nested recursive call to a top-level `Def` with an
--      explicit type, and pass these helpers their terms.**  Callers get
--      the second half for free by using this module; the first half is
--      theirs and is documented at `WF-LIBRARY.md` D10.
--
-- ⚠ NOT a general Σ kit.  Both components are `Nat` because the measures
--   must be, and `⊢absurd` is code-indexed so the motive is a code.  A
--   genuinely generic pair carrier waits on the inductive-types axis.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibPair where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Σ'
        ; RTm; var; nzero; nsuc; pair; fst; snd; ⌜Nat⌝ )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; _⊢ty_; ⊢var; here; ⊢conv; ⊢fst; ⊢snd
        ; ty-Nat; ty-Σ
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; El-⌜Nat⌝; Hom-Nat-ss
        ; ξ-nsuc; ξ-Homˡ; βfst; βsnd )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )

------------------------------------------------------------------------
-- the carrier and its two measures.  ★ A TYPE, so `⊢fst`/`⊢snd` apply
-- DIRECTLY — no `El-⌜Σ⌝` anywhere, which is D4 paying at the carrier.
------------------------------------------------------------------------

PairT : {Γ : Cx} → RTy Γ
PairT = Σ' Nat Nat

⊢PairT : {Γ : Ctx} → Γ ⊢ty PairT
⊢PairT = ty-Σ ty-Nat ty-Nat

msr₁ msr₂ : {Γ : Cx} → RTm (Γ ∙)
msr₁ = fst (var vz)
msr₂ = snd (var vz)

⊢msr₁ : {Γ : Ctx} → (Γ ▹ PairT) ⊢ msr₁ ∷ Nat
⊢msr₁ = ⊢fst (⊢var here)

⊢msr₂ : {Γ : Ctx} → (Γ ▹ PairT) ⊢ msr₂ ∷ Nat
⊢msr₂ = ⊢snd (⊢var here)

------------------------------------------------------------------------
-- the motive is a CODE, so results cross `El ⌜Nat⌝ ≅ᵀ Nat` once in each
-- direction.  ⚠ `asN` is what a NESTED call needs: the inner call's
-- result is a motive value and the outer call's pair wants a number.
------------------------------------------------------------------------

elNat : {Γ : Cx} → El (⌜Nat⌝ {Γ}) ≅ᵀ Nat
elNat = red→≅ᵀ (stepᵀ El-⌜Nat⌝ doneᵀ)

asP : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
asP d = ⊢conv d (csymᵀ elNat)

asN : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Nat
asN d = ⊢conv d elNat

------------------------------------------------------------------------
-- ★★ THE THREE DESCENTS.  Every recursive call at a pair carrier
-- discharges its order obligations with these, and there are only three
-- because a lexicographic call either DROPS a component or HOLDS it:
--
--   dropˡ   `nsuc (fst (pair a b)) ≤ nsuc a`   — μ₁ strictly down (rec₁)
--   dropʳ   `nsuc (snd (pair a b)) ≤ nsuc b`   — μ₂ strictly down (rec₂)
--   holdˡ   `fst (pair a b) ≤ a`               — μ₁ held           (rec₂)
--
-- Each is one β on the projection out of the built pair, then (for the
-- strict ones) a single `Hom-Nat-ss` peel — the successor-cancellation
-- that is a lemma in any other setting and a REDUCTION here.
--
-- ⚠ `a` and `b` are EXPLICIT.  See the header.
------------------------------------------------------------------------

dropˡ : {Γ : Ctx} (a b : RTm ⌊ Γ ⌋) → Γ ⊢ a ∷ Nat →
        Γ ⊢ reflTm a ∷ Hom Nat (nsuc (fst (pair a b))) (nsuc a)
dropˡ a b da =
  ⊢conv (⊢le-refl da)
        (csymᵀ (ctrnᵀ (red→≅ᵀ (stepᵀ (ξ-Homˡ (ξ-nsuc (βfst _ _))) doneᵀ))
                      (red→≅ᵀ (stepᵀ (Hom-Nat-ss _ _) doneᵀ))))

dropʳ : {Γ : Ctx} (a b : RTm ⌊ Γ ⌋) → Γ ⊢ b ∷ Nat →
        Γ ⊢ reflTm b ∷ Hom Nat (nsuc (snd (pair a b))) (nsuc b)
dropʳ a b db =
  ⊢conv (⊢le-refl db)
        (csymᵀ (ctrnᵀ (red→≅ᵀ (stepᵀ (ξ-Homˡ (ξ-nsuc (βsnd _ _))) doneᵀ))
                      (red→≅ᵀ (stepᵀ (Hom-Nat-ss _ _) doneᵀ))))

holdˡ : {Γ : Ctx} (a b : RTm ⌊ Γ ⌋) → Γ ⊢ a ∷ Nat →
        Γ ⊢ reflTm a ∷ Hom Nat (fst (pair a b)) a
holdˡ a b da =
  ⊢conv (⊢le-refl da)
        (csymᵀ (red→≅ᵀ (stepᵀ (ξ-Homˡ (βfst _ _)) doneᵀ)))

-- ★ and the μ₂-held twin, for completeness: a call that holds the SECOND
--   component (μ₁ strictly down, μ₂ unchanged) — the n₂-RESET's shape.
holdʳ : {Γ : Ctx} (a b : RTm ⌊ Γ ⌋) → Γ ⊢ b ∷ Nat →
        Γ ⊢ reflTm b ∷ Hom Nat (snd (pair a b)) b
holdʳ a b db =
  ⊢conv (⊢le-refl db)
        (csymᵀ (red→≅ᵀ (stepᵀ (ξ-Homˡ (βsnd _ _)) doneᵀ)))
