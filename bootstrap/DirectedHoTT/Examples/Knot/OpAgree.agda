-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★ THE NAMED OPERATIONS AGREE (PLAN-FAITHFUL F3).
--
-- Every operation a judgement row cites (`sub0`, `wk`, and `Knot/SubEnv`'s
-- `nrsK` … `wk2uK`) is a traversal under a named ENVIRONMENT.  Each
-- environment REPRESENTS the Spec substitution the kernel's rule uses, so
-- by F2 the operation at quoted arguments reduces to the quotation of the
-- Spec operation:
--
--   sub0 1 ⌜Γ⌝ ⌜t⌝ ⌜u⌝  ⟶*  ⌜ t[u] ⌝        nrsK ⌜Γ⌝ ⌜A⌝  ⟶*  ⌜ A[nrs] ⌝   …
--
-- The representations are the substitutions' own clauses read back
-- (`cons-z` at the fresh variable, `cons-s` elsewhere).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.OpAgree where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Variance using ( pwShift )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-con; ⟶*-pairˡ; ⟶*-pairʳ )
open import DirectedHoTT.Metatheory.TySub using ( wk-cancel-tm )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTm-var; subTy-var )
open import DirectedHoTT.Lib.FinFam using ( ffz; ffs )
open import DirectedHoTT.Lib.Sugar using ( conₗ; v₀; v₁; _,ₚ_ )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Sub
open import DirectedHoTT.Examples.Knot.SubEnv
open import DirectedHoTT.Examples.Knot.Ctx using ( quoteCtx; cext )
open import DirectedHoTT.Examples.Knot.JudgeIx using ( DF; mc )
import DirectedHoTT.Examples.Knot.Ren as KR
open import DirectedHoTT.Examples.Knot.RenAgree using ( RepR; ren-agree-ty; ren-agree-tm )
open import DirectedHoTT.Examples.Knot.SubAgree using ( RepS; module ES; module TRR; repS-lift; repR-wk; sub-agree-ty; sub-agree-tm )

private
  variable
    Γ Δ Θ : Cx

------------------------------------------------------------------------
-- 1. THE ENVIRONMENTS REPRESENT the kernel's substitutions.
------------------------------------------------------------------------

-- `single u = (id , u)`
repS-single : {u : RTm Γ} {d : RTm Θ} → RepS (single u) (app (app SINGLE d) (quoteTm u {Θ}))
repS-single vz     = step (ξ-appˡ (ξ-appˡ (β _ _))) (step (ξ-appˡ (β _ _)) ES.cons-z)
repS-single (vs x) = step (ξ-appˡ (ξ-appˡ (β _ _))) (step (ξ-appˡ (β _ _)) (⟶*-trans ES.cons-s (step (β _ _) done)))

-- `nrs`: the fresh variable is `nsuc` of the previous one
repS-nrs : RepS {Γ ∙} {(Γ ∙) ∙} {Θ} nrs (ENRS (dep Γ))
repS-nrs vz     = ES.cons-z
repS-nrs (vs x) = ⟶*-trans ES.cons-s (step (β _ _) done)

-- `pairS`: the fresh variable is the pair of the two new ones
repS-pairS : RepS {Γ ∙} {(Γ ∙) ∙} {Θ} pairS (EPAIR (dep Γ))
repS-pairS vz     = ES.cons-z
repS-pairS (vs x) = ⟶*-trans ES.cons-s (step (β _ _) done)

-- `fsucS`: the fresh variable is `fsuc` of the new one
repS-fsucS : RepS {Γ ∙} {Γ ∙} {Θ} fsucS (EFSUC (dep Γ))
repS-fsucS vz     = ES.cons-z
repS-fsucS (vs x) = ⟶*-trans ES.cons-s (step (β _ _) done)

-- `methS`: the scrutinee is `con` of the payload
repS-methS : RepS {(Γ ∙) ∙} {((Γ ∙) ∙) ∙} {Θ} methS (EMETH (dep Γ))
repS-methS vz          = ES.cons-z
repS-methS (vs vz)     = ⟶*-trans ES.cons-s ES.cons-z
repS-methS (vs (vs x)) = ⟶*-trans ES.cons-s (⟶*-trans ES.cons-s (step (β _ _) done))

-- `single2 i t`: the two binders of a motive instantiated at once
repS-inst : {i t : RTm Γ} → RepS {(Γ ∙) ∙} {Γ} {Θ} (single2 i t) (EINST (dep Γ) (quoteTm i) (quoteTm t))
repS-inst vz          = ES.cons-z
repS-inst (vs vz)     = ⟶*-trans ES.cons-s ES.cons-z
repS-inst (vs (vs x)) = ⟶*-trans ES.cons-s (⟶*-trans ES.cons-s (step (β _ _) done))

-- renamings used as substitutions: `pwShift`, and the motive's lifts
repS-pwS : RepS {(Γ ∙) ∙} {(Γ ∙) ∙} {Θ} ⟨ pwShift ⟩ᵣ (EPWS (dep Γ))
repS-pwS vz     = ES.cons-z
repS-pwS (vs x) = ⟶*-trans ES.cons-s (step (β _ _) done)

repS-wk1 : RepS {Γ} {Γ ∙} {Θ} ⟨ vs ⟩ᵣ WK1
repS-wk1 x = step (β _ _) done

repS-wk2 : RepS {Γ} {(Γ ∙) ∙} {Θ} ⟨ (λ x → vs (vs x)) ⟩ᵣ WK2
repS-wk2 x = step (β _ _) done

------------------------------------------------------------------------
-- 2. ★★ THE OPERATIONS AGREE.
------------------------------------------------------------------------

-- a term's two binders instantiated one at a time ARE `single2`
inst-single2 : (i t : RTm Γ) (s : RTm ((Γ ∙) ∙)) → subTm (single t) (subTm (extS (single i)) s) ≡ subTm (single2 i t) s
inst-single2 i t s = trans (subTm-subTm s) (subTm-cong pt s)
  where
    pt : (x : Var (_ ∙ ∙)) → (single t ∘ₛ extS (single i)) x ≡ single2 i t x
    pt vz          = refl
    pt (vs vz)     = wk-cancel-tm t i
    pt (vs (vs x)) = refl

private
  -- a motive's two binders instantiated one at a time ARE `single2`
  iinst-single2 : (i t : RTm Γ) (M : RTy ((Γ ∙) ∙)) → iinst i t M ≡ subTy (single2 i t) M
  iinst-single2 i t M = trans (subTy-subTy M) (subTy-cong pt M)
    where
      pt : (x : Var (_ ∙ ∙)) → (single t ∘ₛ extS (single i)) x ≡ single2 i t x
      pt vz          = refl
      pt (vs vz)     = wk-cancel-tm t i
      pt (vs (vs x)) = refl


  -- two lifts of a renaming, as a substitution
  lift2-ren : (ρ : Ren Γ Δ) (M : RTy ((Γ ∙) ∙)) → subTy (extS (extS ⟨ ρ ⟩ᵣ)) M ≡ renTy (extR (extR ρ)) M
  lift2-ren ρ M = trans (subTy-cong pt M) (subTy-var (extR (extR ρ)) M)
    where
      pt : (x : Var (_ ∙ ∙)) → extS (extS ⟨ ρ ⟩ᵣ) x ≡ ⟨ extR (extR ρ) ⟩ᵣ x
      pt vz          = refl
      pt (vs vz)     = refl
      pt (vs (vs x)) = refl

  ⟶≡ : {t u u' : RTm Θ} → u ≡ u' → t ⟶* u → t ⟶* u'
  ⟶≡ refl r = r

opaque
  unfolding sub0 KR.wk nrsK pairSK fsucSK methSK lift2K iinstK iinstTmK pwShK wk2uK

  -- β's substitution
  sub0-agree-ty : (A : RTy (Γ ∙)) (u : RTm Γ) → sub0 0 (dep Γ) (quoteTy A {Θ}) (quoteTm u) ⟶* quoteTy (subTy (single u) A)
  sub0-agree-ty A u = sub-agree-ty A repS-single

  sub0-agree-tm : (t : RTm (Γ ∙)) (u : RTm Γ) → sub0 1 (dep Γ) (quoteTm t {Θ}) (quoteTm u) ⟶* quoteTm (subTm (single u) t)
  sub0-agree-tm t u = sub-agree-tm t repS-single

  -- weakening
  wk-agree-ty : (A : RTy Γ) → KR.wk 0 (dep Γ) (quoteTy A {Θ}) ⟶* quoteTy (renTy vs A)
  wk-agree-ty A = ren-agree-ty A repR-wk

  wk-agree-tm : (t : RTm Γ) → KR.wk 1 (dep Γ) (quoteTm t {Θ}) ⟶* quoteTm (renTm vs t)
  wk-agree-tm t = ren-agree-tm t repR-wk

  -- the eliminators' motive re-basings
  nrs-agree : (A : RTy (Γ ∙)) → nrsK (dep Γ) (quoteTy A {Θ}) ⟶* quoteTy (subTy nrs A)
  nrs-agree A = sub-agree-ty A repS-nrs

  pairS-agree : (A : RTy (Γ ∙)) → pairSK (dep Γ) (quoteTy A {Θ}) ⟶* quoteTy (subTy pairS A)
  pairS-agree A = sub-agree-ty A repS-pairS

  fsucS-agree : (A : RTy (Γ ∙)) → fsucSK (dep Γ) (quoteTy A {Θ}) ⟶* quoteTy (subTy fsucS A)
  fsucS-agree A = sub-agree-ty A repS-fsucS

  methS-agree : (M : RTy ((Γ ∙) ∙)) → methSK (dep Γ) (quoteTy M {Θ}) ⟶* quoteTy (subTy methS M)
  methS-agree M = sub-agree-ty M repS-methS

  -- the motive instantiated at an index and a scrutinee
  iinst-agree : (i t : RTm Γ) (M : RTy ((Γ ∙) ∙)) → iinstK (dep Γ) (quoteTm i {Θ}) (quoteTm t) (quoteTy M) ⟶* quoteTy (iinst i t M)
  iinst-agree i t M = ⟶≡ (cong (λ X → quoteTy X) (sym (iinst-single2 i t M))) (sub-agree-ty M repS-inst)

  -- …and a term's two binders at once (natrec-suc, psplit-β)
  inst-agree : (i t : RTm Γ) (s : RTm ((Γ ∙) ∙)) →
               iinstTmK (dep Γ) (quoteTm i {Θ}) (quoteTm t) (quoteTm s) ⟶* quoteTm (subTm (single t) (subTm (extS (single i)) s))
  inst-agree i t s = ⟶≡ (cong (λ X → quoteTm X) (sym (inst-single2 i t s))) (sub-agree-tm s repS-inst)

  -- `tr-pw`'s shift
  pwSh-agree : (t : RTm ((Γ ∙) ∙)) → pwShK (dep Γ) (quoteTm t {Θ}) ⟶* quoteTm (renTm pwShift t)
  pwSh-agree t = ⟶≡ (cong (λ X → quoteTm X) (subTm-var pwShift t)) (sub-agree-tm t repS-pwS)

  -- `DIh-ρ`'s double lift, and `MethTy`'s
  wk2u-agree : (M : RTy ((Γ ∙) ∙)) → wk2uK (dep Γ) (quoteTy M {Θ}) ⟶* quoteTy (renTy (extR (extR vs)) M)
  wk2u-agree M = ⟶≡ (cong (λ X → quoteTy X) (lift2-ren vs M)) (sub-agree-ty M (repS-lift (repS-lift repS-wk1)))

  lift2-agree : (M : RTy ((Γ ∙) ∙)) → lift2K (dep Γ) (quoteTy M {Θ}) ⟶* quoteTy (wk2M M)
  lift2-agree M = ⟶≡ (cong (λ X → quoteTy X) (lift2-ren (λ x → vs (vs x)) M)) (sub-agree-ty M (repS-lift (repS-lift repS-wk2)))

------------------------------------------------------------------------
-- 3. ★ THE COMPOSITE CODES a row's index cites.
------------------------------------------------------------------------

-- reduction in a node's i-th field
node-1 : {k : ℕ} {a a' r : RTm Θ} → a ⟶* a' → conₗ k (a ,ₚ r) ⟶* conₗ k (a' ,ₚ r)
node-1 r = ⟶*-con (⟶*-pairʳ (⟶*-pairˡ r))

node-2 : {k : ℕ} {a b b' r : RTm Θ} → b ⟶* b' → conₗ k (a ,ₚ b ,ₚ r) ⟶* conₗ k (a ,ₚ b' ,ₚ r)
node-2 r = ⟶*-con (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ r)))

node-3 : {k : ℕ} {a b c c' r : RTm Θ} → c ⟶* c' → conₗ k (a ,ₚ b ,ₚ c ,ₚ r) ⟶* conₗ k (a ,ₚ b ,ₚ c' ,ₚ r)
node-3 r = ⟶*-con (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ r))))

node-4 : {k : ℕ} {a b c d d' r : RTm Θ} → d ⟶* d' → conₗ k (a ,ₚ b ,ₚ c ,ₚ d ,ₚ r) ⟶* conₗ k (a ,ₚ b ,ₚ c ,ₚ d' ,ₚ r)
node-4 r = ⟶*-con (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ r)))))

opaque
  unfolding KR.wk methSK lift2K MethTyK

  -- a description's type: `Π (El I) (Desc I)`
  DF-agree : (I : RTm Γ) → DF (dep Γ) (quoteTm I {Θ}) ⟶* quoteTy (DescF I)
  DF-agree I = node-2 (node-1 (wk-agree-tm I))

  -- the motive's context `(Γ ▹ El I) ▹ IMu I D (var vz)`
  mc-agree : (G : Ctx) (I D : RTm ⌊ G ⌋) →
             mc (dep ⌊ G ⌋) (quoteCtx G {Θ}) (quoteTm I) (quoteTm D) ⟶* quoteCtx (motCtx G I D)
  mc-agree G I D = node-2 (⟶*-trans (node-1 (wk-agree-tm I)) (node-2 (wk-agree-tm D)))

  -- the eliminator's method type
  MethTy-agree : (I D : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
                 MethTyK (dep Γ) (quoteTm I {Θ}) (quoteTm D) (quoteTy M) ⟶* quoteTy (MethTy I D M)
  MethTy-agree {Γ} {Θ} I D M =
    node-2 (⟶*-trans (node-1 A2r) (node-2 (⟶*-trans (node-1 A3r) (node-2 (methS-agree M)))))
    where
      j : RTm Θ
      j = dep Γ
      wD wwD' : RTm Θ
      wD = KR.wk 1 j (quoteTm D)
      wwD' = KR.wk 1 (nsuc j) wD
      wwD : wwD' ⟶* quoteTm (renTm vs (renTm vs D))
      wwD = ⟶*-trans (TRR.trav-t-mono (wk-agree-tm D)) (wk-agree-tm (renTm vs D))
      A2r : kEl (kdpay (KR.wk 1 j (quoteTm I)) wD (kapp wD v0))
            ⟶* quoteTy (El (dpay (renTm vs I) (renTm vs D) (app (renTm vs D) v₀)))
      A2r = node-1 (⟶*-trans (node-1 (wk-agree-tm I)) (⟶*-trans (node-2 (wk-agree-tm D)) (node-3 (node-1 (wk-agree-tm D)))))
      A3r : kDIh wwD' (lift2K j (quoteTy M)) (kapp wwD' v1) v0
            ⟶* quoteTy (DIh (renTm vs (renTm vs D)) (wk2M M) (app (renTm vs (renTm vs D)) v₁) v₀)
      A3r = ⟶*-trans (node-1 wwD) (⟶*-trans (node-2 (lift2-agree M)) (node-3 (node-1 wwD)))
