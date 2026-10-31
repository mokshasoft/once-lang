-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.NuForce
--
-- plan 0.135 S3: WHAT FORCING A ν DOES, proved at each introduction form.
-- A ν's witness (`NuV`) carries its force (`ForceRuns`); `Out` spends it and
-- `in-ν`/`Ana` owe it. Both owe it the way `curry` owes `CallRuns`: the
-- block the code cell names is entered by a call, and the block-call lemma
-- (S2) turns the block body's own correctness into the callee's run.
--
-- `in-ν`'s block is the identity (`mov-to-output`, which IS `emitted 0 _ id`),
-- so its force is the block-call lemma at `id` on the stored layer, plus the
-- fact that forcing an `in-ν` gives back the layer it wrapped (`out-in-ν`).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.NuForce (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.BlockCall o tbl
open import Once.CCC.Codegen.IRObsCorrect.Simple o tbl using (module Simp)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; StoredValue; readReg; Input1; mov-to-output; block-layout)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation)
open import Once.CCC.Label using (ℓ)
open import Once.IRTy using (WellFormedFI; ⟦_⟧TI; ν-type; ⌈_⌉; ⌈_⌉F; ⌈⟧TI-commute; WellFormedFI-irrelevant)
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.IRTy using (IRTy; IRFunctor; _⊕_; _⊗_; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Data.List.Relation.Unary.All using ([])
open import Relation.Binary.PropositionalEquality.Properties using (subst-sym-subst)
import Once.Denotation.ValueDomain as ValueDomain
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; injectᵇ; forgetᵇ; coerce-functor-D; coerce-functor⁻¹-D)
open import Once.Spec.Type
  using (Base; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; WFFun; ∅ₖ)
import Once.Spec.Type as TW
import Once.Semantics.Machine as Val
open import Once.Denotation.Approx using (done; NotCut; budgetLeft)
open import Once.IR.Semantics.Iterative using (T∞)
import Once.Spec.Type
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Maybe using (just; nothing)
open import Data.List.Properties using (++-identityʳ)
open import Once.Res using (Res; stopped; returns; mapRes; is-stopped)
open import Once.Denotation.Approx using (Ap; cut; approx; approxBlock; thenAp; run-approx-bind)
open import Once.IR.Semantics.Iterative using (return∞; fmap∞; module T∞)
open import Once.IR.Semantics.StreamInf using (anaᴵ; anaRun; anaBlock; mapAnaᴵ)
open import Once.Spec.Polynomial using (SFunctor; ⟦_⟧SF)
open import Once.IR.Semantics.FunctorMeaning using (translateF)
open import Once.Spec.Word using (Carrier)
open import Once.IRTy.WF using (base-⌈⌉)
import Once.IRTy as IRTy′
import Once.IR.Semantics.Trace as TM

module NuForceC {FS : FrameSemantics} where

  open Core {FS}
  open LocState using (regs)
  module BC = BlockCallC {FS}
  open Simp {FS} using (obs-correct-id)

  ------------------------------------------------------------------------
  -- A run is a run of every computation with the same approximation.
  ------------------------------------------------------------------------
  crun-retarget : ∀ {B} {R : AllocMode → AllocState {FS} → AllocState {FS} → ValueDomain.⟦ B ⟧ᴰᴵ → LocState FS → Set}
                    {prog fs ret-pc rs} {c c′ : T∞ ValueDomain.⟦ B ⟧ᴰᴵ} {k}
                → runAt (floc fs) (⟪ c′ ⟫ k) ≡ runAt (floc fs) (⟪ c ⟫ k)
                → CalleeRunP {prog = prog} {B} R fs ret-pc rs c k → CalleeRunP {prog = prog} {B} R fs ret-pc rs c′ k
  crun-retarget {fs = fs} {k = k} e (callee-run st se om ca ru li re sp nr nl pl ev lg pr mp fp bm fsp) =
    callee-run st se om ca ru
      (λ p → li (trans (cong is-stopped (sym er)) p))
      (λ p → re (trans (sym er) p))
      (λ p → sp (trans (cong is-stopped (sym er)) p))
      (λ p → nr (trans (sym er) p))
      (λ p → nl (subst NotCut er p))
      (λ p → pl (trans (sym er) p))
      (trans ev (sym ee))
      (trans lg (cong (λ t → LocState.ev-log (floc fs) DL.++ t) (sym ee)))
      (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls ru) (sym er) pr)
      (λ p → mp (subst NotCut er p))
      (λ p → fp (trans (sym er) p))
      (λ p → bm (subst NotCut er p))
      (λ p → fsp (trans (sym er) p))
    where
      er = cong proj₂ e
      ee = cong proj₁ e

  ------------------------------------------------------------------------
  -- FORCING AN `in-ν` GIVES BACK ITS LAYER: the coercions `in-ν` and `Out`
  -- put around the layer are inverse (at `K` positions the functor is well
  -- formed, so the value is a base value and each coercion is the identity
  -- up to its structure).
  ------------------------------------------------------------------------
  base-rt : ∀ {A} (b : Base ∅ₖ A) (x : Val.⟦ A ⟧)
          → Val.coerce-base-to-full b (Val.coerce-full-to-base A x) ≡ x
  base-rt b-Unit       x        = refl
  base-rt b-Void       ()
  base-rt b-Int        x        = refl
  base-rt b-Float      x        = refl
  base-rt (b-* a b) (x , y)  = cong₂ _,_ (base-rt a x) (base-rt b y)
  base-rt (b-+ a b)  (inj₁ x) = cong inj₁ (base-rt a x)
  base-rt (b-+ a b)  (inj₂ y) = cong inj₂ (base-rt b y)

  ν-rt : ∀ {F} (wf : WFFun ∅ₖ F) (X : Set) (x : Val.⟦ F ⟧F X)
       → Val.coerce-ν-out wf X (Val.coerce-ν-in F X x) ≡ x
  ν-rt (TW.wf-K b)       X x        = base-rt b x
  ν-rt TW.wf-Id          X x        = refl
  ν-rt (TW.wf-⊕ f g)   X (inj₁ x) = cong inj₁ (ν-rt f X x)
  ν-rt (TW.wf-⊕ f g)   X (inj₂ y) = cong inj₂ (ν-rt g X y)
  ν-rt (TW.wf-⊗ f g)  X (x , y)  = cong₂ _,_ (ν-rt f X x) (ν-rt g X y)

  if-rt : ∀ {A} (b : Base ∅ₖ A) (y : ⟦ A ⟧ᴰ) → injectᵇ b (forgetᵇ b y) ≡ y
  if-rt b-Unit       y        = refl
  if-rt b-Void       ()
  if-rt b-Int        y        = refl
  if-rt b-Float      y        = refl
  if-rt (b-* a b) (x , y)  = cong₂ _,_ (if-rt a x) (if-rt b y)
  if-rt (b-+ a b)  (inj₁ x) = cong inj₁ (if-rt a x)
  if-rt (b-+ a b)  (inj₂ y) = cong inj₂ (if-rt b y)

  cf-rt : ∀ {F} (wf : WFFun ∅ₖ F) C (y : ⟦ Once.Spec.Type.⟦ F ⟧F C ⟧ᴰ)
        → coerce-functor⁻¹-D wf C (coerce-functor-D wf C y) ≡ y
  cf-rt (TW.wf-K b)       C y        = if-rt b y
  cf-rt TW.wf-Id          C y        = refl
  cf-rt (TW.wf-⊕ f g)   C (inj₁ y) = cong inj₁ (cf-rt f C y)
  cf-rt (TW.wf-⊕ f g)   C (inj₂ y) = cong inj₂ (cf-rt g C y)
  cf-rt (TW.wf-⊗ f g)  C (x , y)  = cong₂ _,_ (cf-rt f C x) (cf-rt g C y)

  out-in-ν : ∀ {F} (wf wf′ : WellFormedFI F) (x : ValueDomain.⟦ ⟦ F ⟧TI (ν-type F) ⟧ᴰᴵ) (k : ℕ)
           → ⟪ evalᴰ (Out wf′) (retVal (evalᴰ (in-ν wf) x)) ⟫ k ≡ ⟪ evalᴰ (id {⟦ F ⟧TI (ν-type F)}) x ⟫ k
  out-in-ν {F} wf wf′ x k rewrite WellFormedFI-irrelevant wf′ wf =
    cong (λ z → TM.ret (done z k))
      (trans (cong (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym e))
               (trans (cong (coerce-functor⁻¹-D w ⌈ ν-type F ⌉) (ν-rt w _ _)) (cf-rt w ⌈ ν-type F ⌉ _)))
             (subst-sym-subst e))
    where
      e = ⌈⟧TI-commute F (ν-type F)
      w = wf-⌈⌉ wf

  ------------------------------------------------------------------------
  -- `in-ν`'s FORCE. The block is `id`; its input is the stored layer, valid
  -- at the force because everything live at construction is still live and
  -- unchanged (`SeedKept`, then the caller's `incl`/`agree`), and its
  -- result is a valid layer, i.e. a `LayerV` of valid νs.
  ------------------------------------------------------------------------
  SeedKept : AllocState {FS} → LocState FS → AllocState {FS} → LocState FS → Set
  SeedKept alloc s alloc′ s′ =
    (∀ l′ → Live alloc l′ → Live alloc′ l′) × (∀ l′ → Live alloc l′ → readLoc s′ l′ ≡ readLoc s l′)

  force-layer : ∀ {F} (wf : WellFormedFI F) (l : ℕ) (prog : AbstractTrace) (j : ℕ) (mIn : AllocMode)
                  (x : ValueDomain.⟦ ⟦ F ⟧TI (ν-type F) ⟧ᴰᴵ) (s : LocState FS) (alloc : AllocState {FS})
              → AllSlotStable prog → BlockRuns prog
              → SpanAt prog j (block-layout (ℓ o l , 0 , mov-to-output ∷ []))
              → LabelsAt prog (suc j) (mov-to-output ∷ [])
              → InputAt {prog} {⟦ F ⟧TI (ν-type F)} mIn alloc x s
              → ∀ alloc′ s′ seed → SeedKept alloc s alloc′ s′ → seed ≡ readReg (regs s) Input1
              → ForceRuns {prog = prog} {F} (λ m′ a′ v′ l′ s″ → NuV {prog = prog} {F} m′ a′ v′ l′ s″)
                  alloc′ s′ seed j (retVal (evalᴰ (in-ν wf) x))
  force-layer {F} wf l prog j mIn x s alloc ss cr sp lab inp alloc′ s′ seed (incl₀ , agree₀) seq
              wf′ fs pre ret-pc k rs pc nh fr fa ns incl agree i1 =
    crun-map {prog = prog} (rp-map {prog = prog} (valid→layer {prog = prog} wf {ν-type F} unν))
      (crun-retarget (cong (runAt (floc fs)) (out-in-ν wf wf′ x k))
        (BC.block-call (id {⟦ F ⟧TI (ν-type F)}) obs-correct-id (suc l) prog (ℓ o l) 0 j ss cr sp [] lab
           fs pre mIn x ret-pc k rs pc nh fr fa ns (callee-input inp)))
    where
      unν : ∀ {m a v lc st} → ValidAtWF {prog = prog} m a {ν-type F} v lc st → NuV {prog = prog} {F} m a v lc st
      unν (valid-ν-wf nv) = nv

      in1 : readReg (regs (floc fs)) Input1 ≡ readReg (regs s) Input1
      in1 = trans i1 seq

      live-pre : ∀ l′ → Live alloc l′ → Live pre l′
      live-pre l′ b = incl l′ (incl₀ l′ b)

      callee-input : InputAt {prog} {⟦ F ⟧TI (ν-type F)} mIn alloc x s
                   → InputAt {prog} {⟦ F ⟧TI (ν-type F)} mIn (BC.callee-alloc 0 fs) x (BC.callee-loc 0 fs)
      callee-input (in-reg fit e) = in-reg fit (trans in1 e)
      callee-input (in-unit e)    = in-unit e
      callee-input (in-loc loc valid bf e) =
        in-loc loc
          (validityWF-heap-transport (Live alloc) (λ _ b → b)
             (λ l′ b → trans (BC.callee-heap 0 fs l′ (live-pre l′ b)) (trans (agree l′ (incl₀ l′ b)) (agree₀ l′ b)))
             (λ l′ b → BC.live-callee 0 fs pre fa l′ (live-pre l′ b))
             x loc bf valid)
          (BC.live-callee 0 fs pre fa loc (live-pre loc bf))
          (trans in1 e)

  ------------------------------------------------------------------------
  -- FORCING AN `Ana` IS RUNNING ITS COALGEBRA, the result re-suspended.
  -- Stated at the RUN (`runAt`), which is all a `CalleeRunP` reads: equality
  -- of the approximation TREES would need function extensionality at every
  -- `call` node, the run does not.
  ------------------------------------------------------------------------
  mapAp : ∀ {X Y : Set} → (X → Y) → Ap X → Ap Y
  mapAp f (done x r) = done (f x) r
  mapAp f cut        = cut

  mapRun : ∀ {X Y : Set} → (X → Y) → TM.Run (Ap X) → TM.Run (Ap Y)
  mapRun f R = proj₁ R , mapRes (mapAp f) (proj₂ R)

  thenAp-ret : ∀ {X Y : Set} (ι : TM.Interp) h es (ρ : Res (Ap X)) (f : X → Y)
             → thenAp ι h es ρ (λ x → return∞ (f x)) ≡ mapRun f (es , ρ)
  thenAp-ret ι h es stopped              f = refl
  thenAp-ret ι h es (returns cut)        f = refl
  thenAp-ret ι h es (returns (done x r)) f = cong (λ z → z , returns (done (f x) r)) (++-identityʳ es)

  run-fmap : ∀ {X Y : Set} (ι : TM.Interp) h r (m : T∞ X) (f : X → Y)
           → TM.run ι h (approx r (fmap∞ f m)) ≡ mapRun f (TM.run ι h (approx r m))
  run-fmap ι h r m f = trans (run-approx-bind ι h r m (λ x → return∞ (f x))) (thenAp-ret ι h _ _ f)

  mutual
    run-anaB : ∀ (H : SFunctor) {A : Set} (c : A → T∞ (⟦ H ⟧SF A)) (ι : TM.Interp) h r
                 (b : TM.T (⟦ H ⟧SF A ⊎ T∞ (⟦ H ⟧SF A)))
             → TM.run ι h (approxBlock r (anaBlock H c b))
               ≡ mapRun (mapAnaᴵ H H c) (TM.run ι h (approxBlock r b))
    run-anaB H c ι h r       (TM.ret (inj₁ l)) = refl
    run-anaB H c ι h zero    (TM.ret (inj₂ m)) = refl
    run-anaB H c ι h (suc r) (TM.ret (inj₂ m)) = run-anaB H c ι h r (T∞.force m)
    run-anaB H c ι h r       (TM.call o a κ)   = run-ana-call H c ι h r o a κ (TM.callAnswer ι h o a)
    run-anaB H c ι h r       (TM.halt o a)     = refl

    run-ana-call : ∀ (H : SFunctor) {A : Set} (c : A → T∞ (⟦ H ⟧SF A)) (ι : TM.Interp) h r
                     (o : TM.CallOp) (a : _) (κ : _ → TM.T (⟦ H ⟧SF A ⊎ T∞ (⟦ H ⟧SF A))) mb
                 → TM.run-call ι h o a (λ b → approxBlock r (anaBlock H c (κ b))) mb
                   ≡ mapRun (mapAnaᴵ H H c) (TM.run-call ι h o a (λ b → approxBlock r (κ b)) mb)
    run-ana-call H c ι h r o a κ (just b) =
      cong (TM.consE (TM.callEvent o a)) (run-anaB H c ι (h DL.++ DL.[ TM.callEvent o a ]) r (κ b))
    run-ana-call H c ι h r o a κ nothing = refl

  -- Four maps are one when they compose to it pointwise.
  mapRun-4 : ∀ {X₀ X₁ X₂ X₃ Y : Set} (f₁ : X₃ → Y) (f₂ : X₂ → X₃) (f₃ : X₁ → X₂) (f₄ : X₀ → X₁) (g : X₀ → Y)
           → (∀ y → f₁ (f₂ (f₃ (f₄ y))) ≡ g y)
           → ∀ es (ρ : Res (Ap X₀)) → mapRun f₁ (mapRun f₂ (mapRun f₃ (mapRun f₄ (es , ρ)))) ≡ mapRun g (es , ρ)
  mapRun-4 f₁ f₂ f₃ f₄ g eq es stopped              = refl
  mapRun-4 f₁ f₂ f₃ f₄ g eq es (returns cut)        = refl
  mapRun-4 f₁ f₂ f₃ f₄ g eq es (returns (done y r)) = cong (λ z → es , returns (done z r)) (eq y)

  -- The coercions around a sum / product split along `⌈⟧TI-commute`.
  sub+₁ : ∀ {X X′ Y Y′ : Once.Spec.Type.Type} (p : X ≡ X′) (q : Y ≡ Y′) (z : ⟦ X ⟧ᴰ)
        → subst (λ Ty → ⟦ Ty ⟧ᴰ) (cong₂ Once.Spec.Type._+_ p q) (inj₁ z) ≡ inj₁ (subst (λ Ty → ⟦ Ty ⟧ᴰ) p z)
  sub+₁ refl refl z = refl
  sub+₂ : ∀ {X X′ Y Y′ : Once.Spec.Type.Type} (p : X ≡ X′) (q : Y ≡ Y′) (z : ⟦ Y ⟧ᴰ)
        → subst (λ Ty → ⟦ Ty ⟧ᴰ) (cong₂ Once.Spec.Type._+_ p q) (inj₂ z) ≡ inj₂ (subst (λ Ty → ⟦ Ty ⟧ᴰ) q z)
  sub+₂ refl refl z = refl
  sub* : ∀ {X X′ Y Y′ : Once.Spec.Type.Type} (p : X ≡ X′) (q : Y ≡ Y′) (z : ⟦ X ⟧ᴰ) (w : ⟦ Y ⟧ᴰ)
       → subst (λ Ty → ⟦ Ty ⟧ᴰ) (cong₂ Once.Spec.Type._*_ p q) (z , w)
         ≡ (subst (λ Ty → ⟦ Ty ⟧ᴰ) p z , subst (λ Ty → ⟦ Ty ⟧ᴰ) q w)
  sub* refl refl z w = refl
  subsym+₁ : ∀ {X X′ Y Y′ : Once.Spec.Type.Type} (p : X ≡ X′) (q : Y ≡ Y′) (z : ⟦ X′ ⟧ᴰ)
           → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (cong₂ Once.Spec.Type._+_ p q)) (inj₁ z) ≡ inj₁ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym p) z)
  subsym+₁ refl refl z = refl
  subsym+₂ : ∀ {X X′ Y Y′ : Once.Spec.Type.Type} (p : X ≡ X′) (q : Y ≡ Y′) (z : ⟦ Y′ ⟧ᴰ)
           → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (cong₂ Once.Spec.Type._+_ p q)) (inj₂ z) ≡ inj₂ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym q) z)
  subsym+₂ refl refl z = refl
  subsym* : ∀ {X X′ Y Y′ : Once.Spec.Type.Type} (p : X ≡ X′) (q : Y ≡ Y′) (z : ⟦ X′ ⟧ᴰ) (w : ⟦ Y′ ⟧ᴰ)
          → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (cong₂ Once.Spec.Type._*_ p q)) (z , w)
            ≡ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym p) z , subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym q) w)
  subsym* refl refl z w = refl

  module AnaDen {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
                (coalg : IR (E IRTy′.* A) (⟦ F ⟧TI A)) (e : ValueDomain.⟦ E ⟧ᴰᴵ) where

    H : SFunctor
    H = translateF Carrier Carrier ⌈ F ⌉F

    P : Once.Spec.Type.Type → Set
    P Ty = ⟦ Ty ⟧ᴰ

    -- the coalgebra `Ana`'s denotation unfolds (DenotTrace), at this env
    c′ : ⟦ ⌈ A ⌉ ⟧ᴰ → T∞ (⟦ H ⟧SF ⟦ ⌈ A ⌉ ⟧ᴰ)
    c′ a′ = fmap∞ (Val.coerce-ν-in ⌈ F ⌉F ⟦ ⌈ A ⌉ ⟧ᴰ)
              (fmap∞ (λ x → coerce-functor-D (wf-⌈⌉ wf) ⌈ A ⌉ (subst P (⌈⟧TI-commute F A) x))
                     (evalᴰ coalg (e , a′)))

    -- THE RE-SUSPENSION, structurally: every recursive position becomes the
    -- `Ana` value of the pair `(e , a′)`.
    rsd : ∀ {G : IRFunctor} → WellFormedFI G
        → ValueDomain.⟦ ⟦ G ⟧TI A ⟧ᴰᴵ → ValueDomain.⟦ ⟦ G ⟧TI (ν-type F) ⟧ᴰᴵ
    rsd (wf-K _)      y        = y
    rsd wf-Id         y        = retVal (evalᴰ (Ana wf coalg) (e , y))
    rsd (wf-Sum f g)  (inj₁ y) = inj₁ (rsd f y)
    rsd (wf-Sum f g)  (inj₂ y) = inj₂ (rsd g y)
    rsd (wf-Prod f g) (y , z)  = (rsd f y , rsd g z)

    -- what `Out ∘ Ana` does to one layer, without the outer transports
    Ψ : ∀ {G : IRFunctor} (wG : WellFormedFI G)
      → ⟦ Once.Spec.Type.⟦ ⌈ G ⌉F ⟧F ⌈ A ⌉ ⟧ᴰ → ⟦ Once.Spec.Type.⟦ ⌈ G ⌉F ⟧F ⌈ ν-type F ⌉ ⟧ᴰ
    Ψ {G} wG z =
      coerce-functor⁻¹-D (wf-⌈⌉ wG) ⌈ ν-type F ⌉
        (Val.coerce-ν-out (wf-⌈⌉ wG) _
          (mapAnaᴵ H (translateF Carrier Carrier ⌈ G ⌉F) c′
            (Val.coerce-ν-in ⌈ G ⌉F ⟦ ⌈ A ⌉ ⟧ᴰ (coerce-functor-D (wf-⌈⌉ wG) ⌈ A ⌉ z))))

    coh : ∀ {G : IRFunctor} (wG : WellFormedFI G) (y : ValueDomain.⟦ ⟦ G ⟧TI A ⟧ᴰᴵ)
        → subst P (sym (⌈⟧TI-commute G (ν-type F))) (Ψ wG (subst P (⌈⟧TI-commute G A) y)) ≡ rsd wG y
    coh (wf-K b) y = trans (cong (injectᵇ (base-⌈⌉ b)) (base-rt (base-⌈⌉ b) _)) (if-rt (base-⌈⌉ b) y)
    coh wf-Id y = refl
    coh {G₁ ⊕ G₂} (wf-Sum f g) (inj₁ y) =
      trans (cong (λ z → subst P (sym (⌈⟧TI-commute (G₁ ⊕ G₂) (ν-type F))) (Ψ (wf-Sum f g) z))
                  (sub+₁ (⌈⟧TI-commute G₁ A) (⌈⟧TI-commute G₂ A) y))
     (trans (subsym+₁ (⌈⟧TI-commute G₁ (ν-type F)) (⌈⟧TI-commute G₂ (ν-type F)) _)
            (cong inj₁ (coh f y)))
    coh {G₁ ⊕ G₂} (wf-Sum f g) (inj₂ y) =
      trans (cong (λ z → subst P (sym (⌈⟧TI-commute (G₁ ⊕ G₂) (ν-type F))) (Ψ (wf-Sum f g) z))
                  (sub+₂ (⌈⟧TI-commute G₁ A) (⌈⟧TI-commute G₂ A) y))
     (trans (subsym+₂ (⌈⟧TI-commute G₁ (ν-type F)) (⌈⟧TI-commute G₂ (ν-type F)) _)
            (cong inj₂ (coh g y)))
    coh {G₁ ⊗ G₂} (wf-Prod f g) (y , z) =
      trans (cong (λ w → subst P (sym (⌈⟧TI-commute (G₁ ⊗ G₂) (ν-type F))) (Ψ (wf-Prod f g) w))
                  (sub* (⌈⟧TI-commute G₁ A) (⌈⟧TI-commute G₂ A) y z))
     (trans (subsym* (⌈⟧TI-commute G₁ (ν-type F)) (⌈⟧TI-commute G₂ (ν-type F)) _ _)
            (cong₂ _,_ (coh f y) (coh g z)))

    -- THE LEMMA.
    out-ana : ∀ (wf′ : WellFormedFI F) (a : ValueDomain.⟦ A ⟧ᴰᴵ) (k : ℕ) (s : LocState FS)
            → runAt s (⟪ evalᴰ (Out wf′) (retVal (evalᴰ (Ana wf coalg) (e , a))) ⟫ k)
              ≡ runAt s (⟪ fmap∞ (rsd wf) (evalᴰ coalg (e , a)) ⟫ k)
    out-ana wf′ a k s rewrite WellFormedFI-irrelevant wf′ wf =
      trans (run-fmap ι h k (anaRun H c′ (c′ a)) gOut)
     (trans (cong (mapRun gOut) (run-anaB H c′ ι h k (T∞.force (c′ a))))
     (trans (cong (λ R → mapRun gOut (mapRun (mapAnaᴵ H H c′) R)) (run-fmap ι h k (fmap∞ cf M) cin))
     (trans (cong (λ R → mapRun gOut (mapRun (mapAnaᴵ H H c′) (mapRun cin R))) (run-fmap ι h k M cf))
     (trans (mapRun-4 gOut (mapAnaᴵ H H c′) cin cf (rsd wf) (coh wf)
              (proj₁ (TM.run ι h (approx k M))) (proj₂ (TM.run ι h (approx k M))))
            (sym (run-fmap ι h k M (rsd wf)))))))
      where
        ι = ιᶠ
        M = evalᴰ coalg (e , a)
        h = LocState.ev-log s
        gOut = λ layer → subst P (sym (⌈⟧TI-commute F (ν-type F)))
                           (coerce-functor⁻¹-D (wf-⌈⌉ wf) ⌈ ν-type F ⌉ (Val.coerce-ν-out (wf-⌈⌉ wf) _ layer))
        cin = Val.coerce-ν-in ⌈ F ⌉F ⟦ ⌈ A ⌉ ⟧ᴰ
        cf  = λ x → coerce-functor-D (wf-⌈⌉ wf) ⌈ A ⌉ (subst P (⌈⟧TI-commute F A) x)
