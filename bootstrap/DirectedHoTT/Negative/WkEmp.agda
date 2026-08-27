------------------------------------------------------------------------
-- ⚠⚠⚠ THIS MODULE IS **RED**.  IT NO LONGER TYPECHECKS, DELIBERATELY —
--     the encoding it is written against was RETIRED on 2026-08-27 and
--     this file is the measurement that retired it.  It is kept because
--     what it measured is not re-derivable from the code that replaced
--     it: the replacement has no `◇` method to go wrong.
--
--     It mentions `sCtx`, `cCtx-emp` and `Knot/Build`'s `Ctx-*K`, all of
--     which are gone.  Do not repair it.
--
-- ★★★ WHAT IT MEASURED, and it decided a design fork.
--
--   `Ctx` was briefly the 8th SORT of the knot (tag 7, rows 54–55).
--   `PLAN-JUDGEMENT` step 2 then needs object-level weakening over that
--   knot, and the obvious motive is the UNIFORM shift `Examples/WkTm`
--   and `Examples/WkFin` both use:
--
--       M(i,t) = K (pair (fst ⟨i⟩) (nsuc (snd ⟨i⟩)))
--
--   54 of the 55 rows are fine at it (a ROW WALK ON PAPER, not a
--   compile).  `◇` is not: its method holds `snd ⟨i⟩ ≡ nzero` and would
--   have to prove `nsuc (snd ⟨i⟩) ≡ nzero` to rebuild itself.  Weakening
--   a CONTEXT is not a thing.
--
--   ⚠⚠ AND IT DID NOT FAIL — IT FABRICATED.  `K (sCtx, 1)` is
--   INHABITED, so a DIFFERENT constructor closes the goal.  This file
--   COMPILED, green, under `--safe`, with an empty trust surface, and
--   what it computed was
--
--       ⋄  ↦  ◇ ▹ Nat            -- a type that was never there
--
--   There is no `Ctx`-weakening specification for that to violate, so
--   nothing downstream would have noticed.  ⇒ the hazard was a GREEN
--   BUILD, not a red one: `verification-that-covers-less-than-it-claims`
--   reached from a new direction.
--
-- ★★ AND A SECOND RESULT, WHICH SURVIVES THE RETIREMENT.  A pair-indexed
--   transport costs TWO `jsub`s, FLAT — one per index component, where
--   `WkFin`'s `fsuc` moved along one.
--
--   ⚠ The `wk-single` one expects does NOT appear.  The outer
--   transport's family mentions the inner component, weakened past the
--   transport's own binder and then substituted — PROPOSITIONAL in
--   general, DEFINITIONAL here, because that component is `snd` of a
--   VARIABLE and both actions COMPUTE on variables (`Knot/Build`'s
--   finding (c)).  MEASURED: replacing either `wk-single` with `refl`
--   type-checked, so both casts came out.
--
-- ⇒ THE FORK IT DECIDED.  `Ctx` is not a sort of the syntax — `_▹_`
--   carries an `RTy ⌊ Γ ⌋`, so `Ctx` depends on the syntax and the
--   syntax never depends back, and a one-directional dependency is a
--   STRATUM rather than a member.  It now has its own 2-row family over
--   a bare depth in `Examples/Knot/CtxD`, which needs no tag ford and
--   has no `◇` method to get wrong.  `HANDOFF-2026-08-27` §A′ has the
--   full argument.
--
-- ⚠ NOTE WHAT `Examples/Knot/CtxD` §5 DOES WITH THE SAME TERM.  `◇ ▹ Nat`
--   is an ordinary INHABITANT there, built from its parts.  Here it was
--   the answer a weakening invented out of nothing.  That difference is
--   what the fork was about.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.WkEmp where
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
