------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ THE OCCURRENCE FOLD: `Lib/IFold` AT A **NON-`Nat`**
-- MOTIVE, the first such instantiation.
--
--     motive  Π Nat Nat     -- a de Bruijn LEVEL in, a 0/1 boolean out
--     z       λ k. 0
--     op      pointwise `max`   (`∨` on 0/1)
--     nd      the identity      (a node contributes nothing of itself)
--
-- ★★★ WHY A **LEVEL** AND NOT AN INDEX, which is the whole reason this
--   motive is CONSTANT.  The spec's occurrence check shifts its variable
--   under a binder:
--
--       occTm x (lam t) = occTm (vs x) t
--
--   so an index-carrying fold would need the motive to depend on the
--   INDEX (`Π (K (sVar , d)) Nat`) and `Lib/IFold` would have to be
--   generalised much further.  A LEVEL is unchanged under a binder — the
--   new binder takes a fresh higher level — so the passenger is the same
--   at every depth and the motive is a closed `Π Nat Nat`.
--
-- ⚠ AND `Π Nat Nat` IS SUBSTITUTION- AND RENAMING-STABLE DEFINITIONALLY,
--   exactly as `Nat` is:
--       subTy σ (Π A B) = Π (subTy σ A) (subTy (extS σ) B)   and
--       subTy σ Nat     = Nat
--   ⇒ `subA` and `renA` are `refl`, which is why the generalisation of
--     `Lib/IFold` was enough and no stability plumbing is needed here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.IOcc where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; RTy; vz; vs; var; lam; app; Π; Nat; nzero; renTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢lam; ⊢app; ⊢nzero
        ; ty-Π; ty-Nat )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true )
open import DirectedHoTT.Lib.NatMax using ( maxTm; ⊢max )
open import normalizer.Syntax.Types using ( refl )
import DirectedHoTT.Lib.IFold as IF

-- ★ THE MOTIVE.
OccTy : {Γ : Cx} → RTy Γ
OccTy = Π Nat Nat

ty-OccTy : {Γ : Ctx} → Γ ⊢ty OccTy
ty-OccTy = ty-Π ty-Nat ty-Nat

-- ★ THE ALGEBRA, pointwise in the level.
occZ : {Γ : Cx} → RTm Γ
occZ = lam nzero

⊢occZ : {Γ : Ctx} → Γ ⊢ occZ ∷ OccTy
⊢occZ = ⊢lam ty-Nat ⊢nzero

-- ★★★ `maxFn` IS CLOSED, AND THAT IS THE POINT.
--
-- ⚠⚠ THE OBVIOUS DEFINITION DOES NOT WORK, and cost a long investigation:
--       occOp f g = lam (maxTm (app (renTm vs f) (var vz)) …)
--   puts the accumulator UNDER A `lam`, so `renTm vs (occOp a b)` is
--   `lam (renTm (extR vs) …)`.  A fold CHAINS its accumulator
--   (`occOp (occOp a b) c`), so from the THIRD recursive field on, every
--   goal carries an `extR` that nothing can discharge.  `Lib/ISz` never
--   meets this: its `op = plusTm` builds no lambda, so `Knot/SzAgree`'s
--   rows have no weakening to cancel and were no guide here.
--
-- ★ WITH `f` AND `g` AS ARGUMENTS OF A CLOSED COMBINATOR, a renaming
--   distributes over the `app`s and stops at `maxFn` itself:
--
--       renTm vs (occOp (occOp a b) c)
--         ≡ occOp (occOp (renTm vs a) (renTm vs b)) (renTm vs c)
--
--   holds by `refl` — DEFINITIONALLY.  No naturality lemma is needed;
--   there is nothing left to prove.
--
-- ★ It also improves the term-size story: `maxTm a b = plusTm a (monusTm
--   b a)` mentions `a` twice, and that duplication now sits inside a
--   CLOSED `Def` (shared) rather than being inlined per application.
--   See `maxtm-is-non-linear`.
maxFn : {Γ : Cx} → RTm Γ
maxFn = lam (lam (lam (maxTm (app (var (vs (vs vz))) (var vz))
                             (app (var (vs vz))      (var vz)))))

⊢maxFn : {Γ : Ctx} → Γ ⊢ maxFn ∷ Π OccTy (Π OccTy OccTy)
⊢maxFn =
  ⊢lam ty-OccTy
   (⊢lam ty-OccTy
     (⊢lam ty-Nat
       (⊢max (⊢app (⊢var (there (there here))) (⊢var here))
             (⊢app (⊢var (there here))         (⊢var here)))))

occOp : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
occOp f g = app (app maxFn f) g

⊢occOp : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ OccTy → Γ ⊢ b ∷ OccTy → Γ ⊢ occOp a b ∷ OccTy
⊢occOp da db = ⊢app (⊢app ⊢maxFn da) db

-- ⚠ `nd` IS THE IDENTITY, where `sz`/`depth` use `nsuc`.  A node
--   contributes nothing to whether a VARIABLE occurs — only its children
--   do.  (The one row where that is wrong is `cVar-vz`, which has no
--   children at all and is overridden at the call site.)
occNd : {Γ : Cx} → RTm Γ → RTm Γ
occNd a = a

⊢occNd : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ OccTy → Γ ⊢ occNd a ∷ OccTy
⊢occNd d = d

-- ★★★ EVERY CHILD COUNTS — `rsum`/`pick` are `Lib/ISz`'s, not
--   `Lib/ISzSort`'s: an occurrence in a cross-sort child is still an
--   occurrence.
open IF.Fold 𝔹 (λ _ → true) (λ b _ → b)
             OccTy ty-OccTy refl refl
             occZ occOp occNd ⊢occZ ⊢occOp ⊢occNd public
  renaming ( ifStep    to occStep    ; ⊢ifStep    to ⊢occStep
           ; ifSumStep to occSumStep ; ⊢ifSumStep to ⊢occSumStep
           ; ifTail    to occTail    ; ⊢ifTail    to ⊢occTail
           ; ifSum     to occSum     ; ⊢ifSum     to ⊢occSum
           ; ifMethod  to occMethod  ; ⊢ifMethod  to ⊢occMethod
           ; ifMeths   to occMeths   ; ⊢ifMeths   to ⊢occMeths
           ; ifMeths-sel to occMeths-sel )
