------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ⚠⚠ THE `◇` METHOD, AND WHY IT IS A HAZARD.
--
-- `PLAN-JUDGEMENT` step 2 needs object-level weakening over the knot,
-- and the obvious motive is the UNIFORM shift that `Examples/WkTm` and
-- `Examples/WkFin` both use:
--
--     M(i,t) = K (pair (fst ⟨i⟩) (nsuc (snd ⟨i⟩)))
--
-- ⚠ SCOPE, STATED HONESTLY.  ONE method is built here — `◇`'s, the row
-- the fork turns on.  The claim that the other 54 are fine at this
-- motive is a ROW WALK ON PAPER (`HANDOFF-2026-08-27` §A′), not a
-- compile; do not quote it as one.
--
-- 54 of the 55 rows are fine at it.  ⚠ `◇` IS NOT.  Its method holds
-- `snd ⟨i⟩ ≡ nzero` and would have to prove `nsuc (snd ⟨i⟩) ≡ nzero` to
-- rebuild ITSELF — weakening a CONTEXT is not a thing, and there is no
-- context one slot deeper to hand back.
--
-- ⚠⚠⚠ AND THAT IS NOT WHAT HAPPENS.  `K (sCtx, 1)` is INHABITED, so the
--   method can be written with a different constructor and it TYPE-
--   CHECKS.  This file is that method.  It compiles, it is well typed,
--   and **it invents a context out of nothing**:
--
--       ⋄ ↦ ◇ ▹ Nat            -- a type that was never there
--
--   ⇒ the hazard is a GREEN BUILD, not a red one.  Nothing downstream
--     would notice, because there is no `Ctx`-weakening specification
--     for this to violate.  `verification-that-covers-less-than-it-
--     claims`, reached from a new direction, and the reason this file
--     exists at all: `Examples/Vec.no-cons-at-zero` builds a hazard on
--     purpose for the same reason.
--
-- ★ WHY IT IS A FORK AND NOT A BLOCKER.  No SYNTAX sort has a `Ctx`
--   field — `Ctx` is mentioned only by JUDGEMENTS — so a traversal
--   entered at `sTy` never reduces this method.  A `renTy` built over
--   the uniform motive is CORRECT WHERE IT IS USED and merely CLAIMS
--   more than it delivers.  See `HANDOFF-2026-08-27` §A′ for the fork.
--
-- ★★ AND THE COST IS TWO TRANSPORTS AND NOTHING ELSE — the second
--   result, and it was measured after a wrong guess.  The index is a
--   PAIR and BOTH components are known only through their fords, so the
--   answer moves along two `Id`s where `WkFin`'s `fsuc` moved along one.
--
--   ⚠ THE `wk-single` ONE EXPECTS DOES NOT APPEAR.  The outer
--   transport's family mentions the inner component, which is weakened
--   past the transport's own binder and then substituted — the round
--   trip that is PROPOSITIONAL in general.  Here it is definitional,
--   because that component is `snd` of a VARIABLE and both actions
--   COMPUTE on variables.  That is `Knot/Build`'s finding (c) again, in
--   the place it was least expected.  ⇒ **measured**: replacing either
--   `wk-single` with `refl` type-checks, so both casts were removed.
--
--   ⇒ a pair-indexed transport costs two `jsub`s, flat.  That is the
--   shape every index telescope in the judgement layer will have, and
--   `_∋_∷_`'s is THREE components.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.WkEmp where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; vz; vs
        ; RTy; RTm; El; Unit; Nat; Σ'
        ; var; pair; fst; snd; nzero; nsuc; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝
        ; jsub; lam; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢lam
        ; ⊢fst; ⊢snd; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢jsub
        ; ty-El; ty-Unit; ty-Σ; ty-IMu
        ; imethTy
        ; _≅ᵀ_; csymᵀ; credᵀ; El-⌜IMu⌝ )
open import DirectedHoTT.Lib.ArithComm using ( IdN; symN; ⊢symN; elIdN )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sCtx; ⊢sCtx; toI; fromI; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K; cCtx-emp )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagCtx-emp )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-NatK; ⊢Ty-NatK )
open import DirectedHoTT.Examples.Knot.Build
  using ( Ctx-empK; ⊢Ctx-empK; Ctx-extK; ⊢Ctx-extK )

------------------------------------------------------------------------
-- 0. `El (⌜IMu⌝ …) ≅ᵀ K …`, both ways.  `⊢jsub`'s family is a CODE and
--    its endpoints are `El` of one, so every transport crosses this.
------------------------------------------------------------------------

toK : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
      Γ ⊢ t ∷ K i → Γ ⊢ t ∷ El (⌜IMu⌝ KnotD IPair i)
toK d = ⊢conv d (csymᵀ (credᵀ El-⌜IMu⌝))

fromK : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
        Γ ⊢ t ∷ El (⌜IMu⌝ KnotD IPair i) → Γ ⊢ t ∷ K i
fromK d = ⊢conv d (credᵀ El-⌜IMu⌝)

-- a ford witness, as the `IdN` the transports want
fordAs : {Γ : Ctx} {a b t : RTm ⌊ Γ ⌋} →
         Γ ⊢ t ∷ El (⌜Id⌝ ⌜Nat⌝ a b) → Γ ⊢ t ∷ IdN a b
fordAs {a = a} {b = b} d = ⊢conv d (elIdN a b)

------------------------------------------------------------------------
-- 1. THE MOTIVE — the UNIFORM shift, exactly `WkTm`'s, over a PAIR
--    index rather than a `Nat` one.
------------------------------------------------------------------------

wkMot : {Γ : Cx} → RTy ((Γ ∙) ∙)
wkMot = K (pair (fst (var (vs vz))) (nsuc (snd (var (vs vz)))))

⊢wkMot : {Γ : Ctx} →
         ((Γ ▹ εwkTy IPair) ▹ K (var vz)) ⊢ty wkMot
⊢wkMot = ty-IMu KnotWf (⊢ixP (⊢fst (⊢var (there here)))
                             (⊢nsuc (⊢snd (⊢var (there here)))))

------------------------------------------------------------------------
-- 2. `cCtx-emp`'s PAYLOAD — two fords and nothing else.
------------------------------------------------------------------------

tyPayEmp : {Γ : Ctx} → (Γ ▹ Σ' Nat Nat) ⊢ty
           Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var vz)) sCtx))
             (Σ' (El (⌜Id⌝ ⌜Nat⌝ (snd (var (vs vz))) nzero)) Unit)
tyPayEmp =
  ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var here))) (toI ⊢sCtx)))
    (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢snd (⊢var (there here)))) (toI ⊢nzero)))
          ty-Unit)

------------------------------------------------------------------------
-- 3. ⚠⚠ THE METHOD.  READ THE HEADER BEFORE READING THIS.
--
-- `⋄ ↦ ◇ ▹ Nat`.  It is well typed and it is WRONG, and the point of
-- the file is that Agda cannot tell.
------------------------------------------------------------------------

-- the invented context, at depth 1
junkCtx : {Γ : Cx} → RTm Γ
junkCtx = Ctx-extK nzero Ctx-empK Ty-NatK

⊢junkCtx : {Δ : Ctx} → Δ ⊢ junkCtx ∷ K (pair sCtx (nsuc nzero))
⊢junkCtx = ⊢Ctx-extK 0 ⊢Ctx-empK (⊢Ty-NatK 0)

wkEmp : {Γ : Cx} → RTm Γ
wkEmp =
  lam (lam (lam
    -- transport 2: `pair sCtx (nsuc (snd ⟨i⟩))`  ⇝  `pair (fst ⟨i⟩) …`
    (jsub (⌜IMu⌝ KnotD IPair
            (pair (var vz) (nsuc (snd (var (vs (vs (vs vz))))))))
          (symN (fst (var (vs (vs vz)))) (fst (var (vs vz))))
    -- transport 1: `pair sCtx (nsuc nzero)`  ⇝  `pair sCtx (nsuc (snd ⟨i⟩))`
      (jsub (⌜IMu⌝ KnotD IPair (pair sCtx (nsuc (var vz))))
            (symN (snd (var (vs (vs vz)))) (fst (snd (var (vs vz)))))
            junkCtx))))

⊢wkEmp : {Γ : Ctx} → Γ ⊢ wkEmp ∷ imethTy KnotD IPair tagCtx-emp cCtx-emp wkMot
⊢wkEmp =
  ⊢lam ⊢IPair
    (⊢lam tyPayEmp
      (⊢lam ty-Unit
        (fromK
            (⊢jsub (⊢⌜IMu⌝ KnotWf
                     (⊢ixP (fromI (⊢var here))
                           (⊢nsuc (⊢snd (⊢var (there (there (there here))))))))
                   (toI ⊢sCtx)
                   (toI (⊢fst (⊢var (there (there here)))))
                   (⊢symN (⊢fst (⊢var (there (there here)))) ⊢sCtx
                          (fordAs (⊢fst (⊢var (there here)))))
                   (toK
                       (fromK
                         (⊢jsub (⊢⌜IMu⌝ KnotWf
                                  (⊢ixP ⊢sCtx (⊢nsuc (fromI (⊢var here)))))
                                (toI ⊢nzero)
                                (toI (⊢snd (⊢var (there (there here)))))
                                (⊢symN (⊢snd (⊢var (there (there here)))) ⊢nzero
                                       (fordAs (⊢fst (⊢snd (⊢var (there here))))))
                                (toK ⊢junkCtx))))))))
