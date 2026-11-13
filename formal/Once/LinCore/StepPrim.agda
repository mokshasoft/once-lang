-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.StepPrim — plan 0.146 B1.4b (D417, step 3): the local step
-- theorem's PRIMITIVES (`prim ds g ⨾ k`).
--
-- The primitives with no code (ρ, λ, α and their inverses, `drop`, a
-- closure's tag) leave the words where they are: the next value's words ARE
-- the old value's (§1). The others run their `LowerSim*` lemma (§2); an
-- allocation's cell is the image's next id when the flat heap counter is the
-- image's, and no value held has a cell at or past it.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++; ++-identityʳ; ++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Bool using (false)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.StepPrim
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; _∷ˢ_; Slots; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw
open import Once.LinCore.LowerSimB fmt ans bw
open import Once.LinCore.LowerSimC fmt ans bw
open import Once.LinCore.LowerSimD fmt ans bw
open import Once.LinCore.ImagePt fmt ans bw using (Sub; next)
open import Once.LinCore.LowAt fmt ans bw using (Inside; module At)
open import Once.LinCore.StepLocal fmt ans bw using (module Loc)
import Once.LinCore.Moves

------------------------------------------------------------------------
-- 1. ★ THE WORDS STAY: a value's words are its image's under ρ, λ, α, and
-- under a closure's tag.
------------------------------------------------------------------------

module PrimW {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf

  -- the top value replaced by one of the same words
  retop : ∀ {rd sm φ A B S} {a : MV A} {b : MV B} {os : Stk S}
        → wsz A ≡ wsz B → (∀ {w} → VW rd a w → VW rd b w) → StkW rd sm φ (a ∷ˢ os) → StkW rd sm φ (b ∷ˢ os)
  retop {sm = sm} {φ} {S = S} e f ((w , p , sl) , rest) =
    (w , f p , subst (λ z → SlotsAt sm (budget φ ∸ (z + ws S)) w) e sl) , rest

  ρ-W : ∀ {rd A} {x : MV A} {w} → VW rd (mpair x mone) w → VW rd x w
  ρ-W {rd} {x = x} (vpair {wa = wa} p vone) = subst (VW rd x) (sym (++-identityʳ wa)) p

  ρ⁻-W : ∀ {rd A} {x : MV A} {w} → VW rd x w → VW rd (mpair x mone) w
  ρ⁻-W {rd} {x = x} {w} p = subst (VW rd (mpair x mone)) (++-identityʳ w) (vpair p vone)

  λ-W : ∀ {rd A} {x : MV A} {w} → VW rd (mpair mone x) w → VW rd x w
  λ-W (vpair vone p) = p

  λ⁻-W : ∀ {rd A} {x : MV A} {w} → VW rd x w → VW rd (mpair mone x) w
  λ⁻-W p = vpair vone p

  α-W : ∀ {rd A B C} {a : MV A} {b : MV B} {c : MV C} {w} → VW rd (mpair (mpair a b) c) w → VW rd (mpair a (mpair b c)) w
  α-W {rd} {a = a} {b} {c} (vpair {wb = wc} (vpair {wa = wa} {wb} pa pb) pc) =
    subst (VW rd (mpair a (mpair b c))) (sym (++-assoc wa wb wc)) (vpair pa (vpair pb pc))

  α⁻-W : ∀ {rd A B C} {a : MV A} {b : MV B} {c : MV C} {w} → VW rd (mpair a (mpair b c)) w → VW rd (mpair (mpair a b) c) w
  α⁻-W {rd} {a = a} {b} {c} (vpair {wa = wa} pa (vpair {wa = wb} {wc} pb pc)) =
    subst (VW rd (mpair (mpair a b) c)) (++-assoc wa wb wc) (vpair (vpair pa pb) pc)

  -- a closure's tag: no words of its own
  wsz-tag : ∀ F {l X} → wsz (LF∙ F X) ≡ wsz (LF∙ F (Ct l X))
  wsz-tag Idf      = refl
  wsz-tag Kone     = refl
  wsz-tag Kzero    = refl
  wsz-tag (Kb b)   = refl
  wsz-tag (Kμ G)   = refl
  wsz-tag (G ⊕f H) = cong suc (cong₂ _⊔_ (wsz-tag G) (wsz-tag H))
  wsz-tag (G ⊗f H) = cong₂ _+_ (wsz-tag G) (wsz-tag H)

  tag-W : ∀ F {l X rd} {x : MV (LF∙ F X)} {w} → VW rd x w → VW rd (tag {l} F x) w
  tag-W Idf      p           = vct p
  tag-W Kone     p           = p
  tag-W Kzero    {x = ()}    p
  tag-W (Kb b)   p           = p
  tag-W (Kμ G)   p           = p
  tag-W (G ⊕f H) (vinl p e)  = vinl (tag-W G p) (trans e (cong₂ _⊔_ (wsz-tag G) (wsz-tag H)))
  tag-W (G ⊕f H) (vinr p e)  = vinr (tag-W H p) (trans e (cong₂ _⊔_ (wsz-tag G) (wsz-tag H)))
  tag-W (G ⊗f H) (vpair p q) = vpair (tag-W G p) (tag-W H q)

------------------------------------------------------------------------
-- 2. ★ THE PRIMITIVES, at a path of a root.
------------------------------------------------------------------------

module Prims {FS : FrameSemantics} (U : Univ)
             (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
             (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
             (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS)
             (prog : AbstractTrace)
             {sh₀ U₀} (root : Codeᴵ sh₀ U₀) (j : ℕ)
             (L₀ : At.Low U ncty ldConst (frameOf root) j root)
             (R : Inside prog (At.code U ncty ldConst (frameOf root) j L₀)) where

  open Loc {FS} U ncty ldConst wordOf prog root j L₀ R
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf
  open SimB {FS} U wordOf
  open SimC {FS} U wordOf
  open SimD {FS} U wordOf
  open PrimW {FS} U wordOf
  open CfgW
  open In U
  open Lowering U ncty ldConst
  open At U ncty ldConst φ j using (lcin)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc)
  open import Once.LinCore.Moves {FS} using (Ran; slot)

  private
    -- a lemma that also states the heap counter: as a straight run
    drop-next : ∀ {sb} {m′ : Cfg sb} {fs N a} {P : FlatState → Set}
              → Σ FlatState (λ fs′ → FlatStepsAPI.FlatSteps {FS} prog N fs fs′
                                     × CfgW (LocState.heapMem (floc fs′)) (slot fs′) φ m′ × P fs′ × Ran N a (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′)
              → Gives fs N a m′
    drop-next (fs′ , st , C′ , _ , Rn) = fs′ , st , C′ , Rn

  -- the words of a value of the same size, in place
  same : ∀ {Γ} {ds : Defs Γ} {Es A B S V} {g : LTm Γ A B} {k : Codeᴵ (Es ∣ B ∷ S) V} (s : Sub root (prim ds g ⨾ k))
           {es : Slots Es} {a : MV A} {b : MV B} {os : Stk S} {fs}
       → insC s ≡ [] → wsz A ≡ wsz B → (∀ {rd w} → VW rd a w → VW rd b w)
       → Here s (es ∥ a ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ b ∷ˢ os)
  same s e sz f H = empty s H e (λ C → cfgK s (c-env C) (retop sz f (c-stk C)))

  st-ρ : ∀ {Γ} {ds : Defs Γ} {Es A S V} {k : Codeᴵ (Es ∣ A ∷ S) V} (s : Sub root (prim ds (ρl {A = A}) ⨾ k))
           {es : Slots Es} {x : MV A} {os : Stk S} {fs}
       → Here s (es ∥ mpair x mone ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ x ∷ˢ os)
  st-ρ {A = A} s = same s refl (+-identityʳ (wsz A)) ρ-W

  st-ρ⁻ : ∀ {Γ} {ds : Defs Γ} {Es A S V} {k : Codeᴵ (Es ∣ (A ⊗t One) ∷ S) V} (s : Sub root (prim ds (ρl⁻ {A = A}) ⨾ k))
            {es : Slots Es} {x : MV A} {os : Stk S} {fs}
        → Here s (es ∥ x ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ mpair x mone ∷ˢ os)
  st-ρ⁻ {A = A} s = same s refl (sym (+-identityʳ (wsz A))) ρ⁻-W

  st-λ : ∀ {Γ} {ds : Defs Γ} {Es A S V} {k : Codeᴵ (Es ∣ A ∷ S) V} (s : Sub root (prim ds (lul {A = A}) ⨾ k))
           {es : Slots Es} {x : MV A} {os : Stk S} {fs}
       → Here s (es ∥ mpair mone x ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ x ∷ˢ os)
  st-λ s = same s refl refl λ-W

  st-λ⁻ : ∀ {Γ} {ds : Defs Γ} {Es A S V} {k : Codeᴵ (Es ∣ (One ⊗t A) ∷ S) V} (s : Sub root (prim ds (lul⁻ {A = A}) ⨾ k))
            {es : Slots Es} {x : MV A} {os : Stk S} {fs}
        → Here s (es ∥ x ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ mpair mone x ∷ˢ os)
  st-λ⁻ s = same s refl refl λ⁻-W

  st-α : ∀ {Γ} {ds : Defs Γ} {Es A B C S V} {k : Codeᴵ (Es ∣ (A ⊗t (B ⊗t C)) ∷ S) V}
           (s : Sub root (prim ds (lassoc {A = A} {B} {C}) ⨾ k))
           {es : Slots Es} {a : MV A} {b : MV B} {c : MV C} {os : Stk S} {fs}
       → Here s (es ∥ mpair (mpair a b) c ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ mpair a (mpair b c) ∷ˢ os)
  st-α {A = A} {B} {C} s = same s refl (+-assoc (wsz A) (wsz B) (wsz C)) α-W

  st-α⁻ : ∀ {Γ} {ds : Defs Γ} {Es A B C S V} {k : Codeᴵ (Es ∣ ((A ⊗t B) ⊗t C) ∷ S) V}
            (s : Sub root (prim ds (lassoc⁻ {A = A} {B} {C}) ⨾ k))
            {es : Slots Es} {a : MV A} {b : MV B} {c : MV C} {os : Stk S} {fs}
        → Here s (es ∥ mpair a (mpair b c) ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ mpair (mpair a b) c ∷ˢ os)
  st-α⁻ {A = A} {B} {C} s = same s refl (sym (+-assoc (wsz A) (wsz B) (wsz C))) α⁻-W

  st-clo : ∀ {Γ} {ds : Defs Γ} {Es F l k′ g X A B S V} {p : Γ ∋[ l ] sg k′ g X A B}
             {k : Codeᴵ (Es ∣ LF∙ F (Ct l X) ∷ S) V} (s : Sub root (prim ds (lclo F p) ⨾ k))
             {es : Slots Es} {x : MV (LF∙ F X)} {os : Stk S} {fs}
         → Here s (es ∥ x ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ tag F x ∷ˢ os)
  st-clo {F = F} s = same s refl (wsz-tag F) (tag-W F)

  -- `drop`: no words; the dropped value's are left below the stack
  st-drop : ∀ {Γ} {ds : Defs Γ} {Es A S V} {k : Codeᴵ (Es ∣ One ∷ S) V} (s : Sub root (prim ds (drop {A = A}) ⨾ k))
              {es : Slots Es} {v : MV A} {os : Stk S} {fs}
          → Here s (es ∥ v ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ mone ∷ˢ os)
  st-drop s H = empty s H refl (λ C → cfgK s (c-env C) (unit-W (proj₂ (c-stk C))))

  ----------------------------------------------------------------------
  -- ★ the primitives with code
  ----------------------------------------------------------------------

  private
    len-++3 : ∀ (x y z : AbstractTrace) → length (x ++ y ++ z) ≡ length x + (length y + length z)
    len-++3 x y z = trans (length-++ x) (cong (length x +_) (length-++ y))

    len-stores : ∀ b n → length (stores b n) ≡ n
    len-stores b zero    = refl
    len-stores b (suc n) = cong suc (len-stores (suc b) n)

  st-lswap : ∀ {Γ} {ds : Defs Γ} {Es A B S V} {k : Codeᴵ (Es ∣ (B ⊗t A) ∷ S) V}
               (s : Sub root (prim ds (lswap {A = A} {B}) ⨾ k))
               {es : Slots Es} {a : MV A} {b : MV B} {os : Stk S} {fs}
           → Here s (es ∥ mpair a b ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ mpair b a ∷ˢ os)
  st-lswap {A = A} {B} {S} s {fs = fs} H =
    let t = Tp φ (A ∷ B ∷ S) in
    straight s H _ 0
      (sym (trans (len-++3 (mvSS t (t ∸ wsz A) (wsz A)) (mvSS (t + wsz A) t (wsz B)) (mvSS (t ∸ wsz A) (t + wsz B) (wsz A)))
                  (cong₂ _+_ (len-mvSS t (t ∸ wsz A) (wsz A))
                    (cong₂ _+_ (len-mvSS (t + wsz A) t (wsz B)) (len-mvSS (t ∸ wsz A) (t + wsz B) (wsz A))))))
      (λ sg h C → lswap-sim prog fs φ sg h C (proj₂ (ins-fits s)))

  st-inl : ∀ {Γ} {ds : Defs Γ} {Es A B S V} {k : Codeᴵ (Es ∣ (A ⊕t B) ∷ S) V}
             (s : Sub root (prim ds (linl {A = A} {B}) ⨾ k))
             {es : Slots Es} {a : MV A} {os : Stk S} {fs}
         → Here s (es ∥ a ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ minl {B = B} a ∷ˢ os)
  st-inl {A = A} {B} {S} s {fs = fs} H =
    let bot = Tp φ S ; M = wsz A ⊔ wsz B in
    straight s H _ 0
      (sym (trans (length-++ (mvSS (bot ∸ wsz A) (bot ∸ M) (wsz A)))
                  (cong₂ _+_ (len-mvSS (bot ∸ wsz A) (bot ∸ M) (wsz A)) (cong (λ z → suc (suc z)) (len-stores (bot ∸ (M ∸ wsz A)) (M ∸ wsz A))))))
      (λ sg h C → linl-sim prog fs φ sg h C (proj₂ (shape-fits (next s))))

  st-inr : ∀ {Γ} {ds : Defs Γ} {Es A B S V} {k : Codeᴵ (Es ∣ (A ⊕t B) ∷ S) V}
             (s : Sub root (prim ds (linr {A = A} {B}) ⨾ k))
             {es : Slots Es} {b : MV B} {os : Stk S} {fs}
         → Here s (es ∥ b ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ minr {A = A} b ∷ˢ os)
  st-inr {A = A} {B} {S} s {fs = fs} H =
    let bot = Tp φ S ; M = wsz A ⊔ wsz B in
    straight s H _ 0
      (sym (trans (length-++ (mvSS (bot ∸ wsz B) (bot ∸ M) (wsz B)))
                  (cong₂ _+_ (len-mvSS (bot ∸ wsz B) (bot ∸ M) (wsz B)) (cong (λ z → suc (suc z)) (len-stores (bot ∸ (M ∸ wsz B)) (M ∸ wsz B))))))
      (λ sg h C → linr-sim prog fs φ sg h C (proj₂ (shape-fits (next s))))

  st-out : ∀ {Γ} {ds : Defs Γ} {Es F S V} {k : Codeᴵ (Es ∣ LF∙ F (μt F) ∷ S) V}
             (s : Sub root (prim ds (lOutμ {F = F}) ⨾ k))
             {es : Slots Es} {i} {v : MV (LF∙ F (μt F))} {os : Stk S} {fs}
         → Here s (es ∥ mmu i v ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ v ∷ˢ os)
  st-out {F = F} {S} s {fs = fs} H =
    let bot = Tp φ S ; wL = wsz (LF∙ F (μt F)) in
    straight s H _ 0
      (sym (cong suc (trans (length-++ (mvPS 0 (bot ∸ wL) wL)) (cong (_+ 1) (len-mvPS 0 (bot ∸ wL) wL)))))
      (λ sg h C → lOutμ-sim prog fs φ sg h C (proj₂ (shape-fits (next s))))

  -- an allocation: the image's next id is the flat heap counter, and no
  -- value held has a cell at or past it
  Fresh : ∀ {sh} → Cfg sh → FlatState → Set
  Fresh m fs = ∀ j → AllocState.next-heap-ref (falloc fs) ≤ serial j → cntE (Cfg.envs m) j ≡ 0 × cntS (Cfg.opds m) j ≡ 0

  st-in : ∀ {Γ} {ds : Defs Γ} {Es F S V} {k : Codeᴵ (Es ∣ μt F ∷ S) V}
            (s : Sub root (prim ds (lIn {F = F}) ⨾ k))
            {es : Slots Es} {v : MV (LF∙ F (μt F))} {os : Stk S} {fs}
        → Here s (es ∥ v ∷ˢ os) fs → Fresh (es ∥ v ∷ˢ os) fs
        → Moved (next s) fs 1 (es ∥ mmu (szμ F , AllocState.next-heap-ref (falloc fs)) v ∷ˢ os)
  st-in {F = F} {S} s {fs = fs} H fr =
    let bot = Tp φ S ; wL = wsz (LF∙ F (μt F)) in
    straight s H _ 1
      (sym (cong (λ z → suc (suc z)) (trans (length-++ (mvSP (bot ∸ wL) 0 wL)) (cong (_+ 2) (len-mvSP (bot ∸ wL) 0 wL)))))
      (λ sg h C → drop-next (lIn-sim prog fs φ refl fr sg h C (proj₂ (shape-fits (next s)))))

  st-const : ∀ {Γ} {ds : Defs Γ} {Es b S V} {v : ⟦ b ⟧b} {k : Codeᴵ (Es ∣ Bt b ∷ S) V}
               (s : Sub root (prim ds (lconst v) ⨾ k))
               {es : Slots Es} {os : Stk S} {fs}
           → FlatMachine.flat-exec-instr {FS} (ldConst v) prog fs
             ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = suc (fpc fs) }
           → Here s (es ∥ mone ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ mbase v ∷ˢ os)
  st-const {v = v} s {fs = fs} eld H =
    straight s H _ 0 refl (λ sg h C → lconst-sim prog fs φ v (ldConst v) eld sg h C (proj₂ (shape-fits (next s))))

  private
    len-cell : ∀ w jb jc jf bot → length (header w jb jc jf ++ mvSP (bot ∸ w) hdr w ++ mov-to-output ∷ store-at-slot (bot ∸ 1) ∷ [])
                                ≡ 10 + (Once.LinCore.Moves.ln {FS} w + 2)
    len-cell w jb jc jf bot =
      cong (10 +_) (trans (length-++ (mvSP (bot ∸ w) hdr w)) (cong (_+ 2) (len-mvSP (bot ∸ w) hdr w)))

  st-lam : ∀ {Γ} {ds : Defs Γ} {Es g X A B S V} {b : Tm Γ One (X ⊗t A) B} {γ : Gd g b}
             {k : Codeᴵ (Es ∣ Fn once g A B ∷ S) V} (s : Sub root (prim ds (llam b γ) ⨾ k))
             {es : Slots Es} {x : MV X} {os : Stk S} {fs}
         → Here s (es ∥ x ∷ˢ os) fs → Fresh (es ∥ x ∷ˢ os) fs
         → Moved (next s) fs 1 (es ∥ mfn (szc X , AllocState.next-heap-ref (falloc fs)) (c1 ds b γ) x ∷ˢ os)
  st-lam {X = X} {S = S} s {fs = fs} H fr =
    let ev = proj₁ (lcin (lowAt s)) in
    straight s H _ 1 (sym (len-cell (wsz X) (idx (proj₁ ev)) (idx (inC (proj₂ ev))) (idx (inF (proj₂ ev))) (Tp φ S)))
      (λ sg h C → drop-next (llam-sim prog fs φ (proj₁ ev) (proj₂ ev) fr sg h C (proj₂ (shape-fits (next s)))))

  st-lamω : ∀ {Γ} {ds : Defs Γ} {Es g X A B S V} {b : Tm Γ X A B} {γ : Gd g b}
              {k : Codeᴵ (Es ∣ Fn many g A B ∷ S) V} (s : Sub root (prim ds (llamω b γ) ⨾ k))
              {es : Slots Es} {x : MV X} {os : Stk S} {fs}
          → Here s (es ∥ x ∷ˢ os) fs → Fresh (es ∥ x ∷ˢ os) fs
          → Moved (next s) fs 1 (es ∥ mfn (szc X , AllocState.next-heap-ref (falloc fs)) (cω ds b γ) x ∷ˢ os)
  st-lamω {X = X} {S = S} s {fs = fs} H fr =
    let ev = proj₁ (lcin (lowAt s)) in
    straight s H _ 1 (sym (len-cell (wsz X) (idx (proj₁ ev)) (idx (inC (proj₂ ev))) (idx (inF (proj₂ ev))) (Tp φ S)))
      (λ sg h C → drop-next (llamω-sim prog fs φ (proj₁ ev) (proj₂ ev) fr sg h C (proj₂ (shape-fits (next s)))))

  st-unf : ∀ {Γ} {ds : Defs Γ} {Es F S₀ S V} {k : Codeᴵ (Es ∣ Nu F ∷ S) V}
             (s : Sub root (prim ds (lunf {F = F} {S₀}) ⨾ k))
             {es : Slots Es} {p : MV (Coalg F S₀ ⊗t S₀)} {os : Stk S} {fs}
         → Here s (es ∥ p ∷ˢ os) fs → Fresh (es ∥ p ∷ˢ os) fs
         → Moved (next s) fs 1 (es ∥ mnu (szν F S₀ , AllocState.next-heap-ref (falloc fs)) p ∷ˢ os)
  st-unf {F = F} {S₀} {S} s {fs = fs} H fr =
    let ev = proj₁ (lcin (lowAt s)) ; n = proj₁ ev ; o = proj₂ ev in
    straight s H _ 1
      (sym (len-cell (wsz (cty (F , S₀))) (idx (inO o n)) (idx (inC (ncty n))) (idx (inF (ncty n))) (Tp φ S)))
      (λ sg h C → drop-next (lunf-sim prog fs φ n o (ncty n) fr sg h C (proj₂ (shape-fits (next s)))))
