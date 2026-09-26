------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★ `size` DESCENDS AT AN `app` NODE, IN THE
-- OBJECT LANGUAGE.
--
-- HANDOFF-2026-08-25 step 1b's arithmetic half, split out because it is
-- about `Examples/Scoped` and NOT about `⊢amrec`: the recursor's step
-- needs `size f < size (app f a)` as a `Hom Nat`, and that is a fact
-- about the eliminator and `+`, provable on its own.
--
-- ★ THE SHAPE.  `size` at an `app` node runs `msize-app`, whose body is
--   `suc (fst ih + fst (snd ih))` — so the node's measure is ONE MORE
--   than the sum of its children's.  Descent is then `x ≤ x + y` under a
--   successor, i.e. `Lib/ArithLe.⊢le-sum` plus `Hom-Nat-ss`.
--
-- ⚠ THE PAYLOAD IS A VARIABLE, and that is deliberate.  Stated at a
--   literal `pair f (pair a unit)` this lemma would be useless to its
--   customer: an `imethTy` method receives the payload as a BOUND
--   VARIABLE `p` and the scrutinee as `icon 2 p`, never as a pair it can
--   project by `βfst`.  So the reduction below is proved at an arbitrary
--   `p`, with `fst p` / `fst (snd p)` left as projections.
--
-- ⚠ AND AT AN ARBITRARY INDEX `n`, for the same reason: §9.1's method
--   QUANTIFIES over the index, so `n` is a bound variable there too and
--   `nzero` would not match.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.ScopedSize where
open import Agda.Builtin.Nat using ( zero; suc )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶*-trans; ⟶*-nsuc )
open import DirectedHoTT.Lib.Nat     using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.ArithLe using ( leSumTm; ⊢le-sum )
open import DirectedHoTT.Lib.Sugar   using ( conₗ )
open import DirectedHoTT.Lib.Tel     using ( nthᵗ-z; nthᵗ-s )
open import DirectedHoTT.Lib.TelFold using ( sizeAlg; fold-ι )
open import DirectedHoTT.Examples.Scoped
  using ( TmTs; TmD; INat; Tm; size; ⊢size; msize )

------------------------------------------------------------------------
-- 0. THE `app` NODE AT AN ABSTRACT PAYLOAD.
------------------------------------------------------------------------

appNode : {Γ : Cx} → RTm Γ → RTm Γ
appNode p = conₗ (suc (suc zero)) p

------------------------------------------------------------------------
-- 1. THE REDUCTION.  `size n (app f a) ⟶* suc (size n f + size n a)`.
--
-- The library fold's ι (`fold-ι`) delivers `suc (fst h + fst (snd h))`
-- with `h` the walked hypotheses — both recursive calls at the AMBIENT
-- index `n` (D074: `app`'s fields sit at the fibre's own index) — and
-- three projections finish it.
------------------------------------------------------------------------

sizeApp : {Γ : Cx} (n p : RTm Γ) →
          size n (appNode p)
            ⟶* nsuc (plusTm (size n (fst p)) (size n (fst (snd p))))
sizeApp n p =
  ⟶*-trans (fold-ι sizeAlg {Ts = TmTs} {i = n} {p = p} (nthᵗ-s (nthᵗ-s nthᵗ-z)))
    (⟶*-nsuc
      (step (ξ-natrecⁿ (βfst _ _))
      (step (ξ-natrecᶻ (ξ-fst (βsnd _ _)))
      (step (ξ-natrecᶻ (βfst _ _)) done))))

-- lift a term reduction into a `Hom`'s RIGHT endpoint.
homʳStar : {Γ : Cx} {A : RTy Γ} {t u u' : RTm Γ} →
           u ⟶* u' → Hom A t u ⟶ᵀ* Hom A t u'
homʳStar done       = doneᵀ
homʳStar (step r q) = stepᵀ (ξ-Homʳ r) (homʳStar q)

------------------------------------------------------------------------
-- 2. ★★ THE DESCENT CERTIFICATE — `size n f < size n (app f a)`.
--
-- ⚠ BOTH children are asked for at the AMBIENT index `n`.  The payload's
--   second field is typed at `w n` under the `Σ'` binder, so a caller
--   pays one `wk-single` to hand it over — exactly the cast
--   `Scoped.⊢tapp` already pays, and it belongs at the caller because it
--   is the caller who knows the payload's shape.
------------------------------------------------------------------------

descAppTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
descAppTm n p = leSumTm (size n (fst p)) (size n (fst (snd p)))

⊢desc-app : {Γ : Ctx} {n p : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ El ⌜Nat⌝ →
            Γ ⊢ fst p ∷ Tm n → Γ ⊢ fst (snd p) ∷ Tm n →
            Γ ⊢ descAppTm n p
              ∷ Hom Nat (nsuc (size n (fst p))) (size n (appNode p))
⊢desc-app {n = n} {p = p} dn df da =
  ⊢conv (⊢conv (⊢le-sum (⊢size dn df) (⊢size dn da))
               (csymᵀ (credᵀ (Hom-Nat-ss _ _))))
        (csymᵀ (red→≅ᵀ (homʳStar (sizeApp n p))))
