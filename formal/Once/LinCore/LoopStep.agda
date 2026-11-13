-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LoopStep — plan 0.146 B1.4b (D417, step 3): THE LOOP'S
-- STEPS against its lowering.
--
-- A loop `loop b ⨾ k` at a path `s` lowers to its head label `Lh`, the body
-- (whose `end` is `jmp Ld`), the dispatch at `Ld` (`dispC`: read the tag,
-- on 1 shift the next state and `jmp Lh`, on 0 jump to `Li`, shift the
-- result), then `k`'s code. The image enters the body pushing the dispatch
-- (`i-loop`), returns to it at the body's end (`i-reti`), and there takes
-- `k` or the loop again (`i-case₁`/`i-case₂` at the dispatch point). On the
-- flat side: the head label's step; the body end's jump; the dispatch's
-- label, the branch and its shift, and on 1 the jump back to the loop's
-- own address.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (+-comm; +-suc)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++; ++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Bool using (false)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.LoopStep
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
open import Once.LinCore.LowerSimD fmt ans bw using (module SimD)
open import Once.LinCore.ImagePt fmt ans bw using (Sub; next; body)
open import Once.LinCore.LowAt fmt ans bw using (Inside; in-trans; in-∷; in-mid; module At)
open import Once.LinCore.PointAt fmt ans bw using (module Fetch)
open import Once.LinCore.StepLocal fmt ans bw using (module Loc)
import Once.LinCore.Moves

module Loops {FS : FrameSemantics} (U : Univ)
             (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
             (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
             (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS)
             (prog : AbstractTrace)
             {sh₀ U₀} (root : Codeᴵ sh₀ U₀) (j : ℕ)
             (L₀ : At.Low U ncty ldConst (frameOf root) j root)
             (R : Inside prog (At.code U ncty ldConst (frameOf root) j L₀)) where

  open Loc {FS} U ncty ldConst wordOf prog root j L₀ R
  open Here
  open At U ncty ldConst φ j using (code; lm; lfin; lcin; ins; sub-low; dispC; disp-in)
  open Lowering U ncty ldConst
  open Rel {FS} U wordOf
  open SimD {FS} U wordOf using (case₁-sim; case₂-sim)
  open Fetch {FS} using (in-seg)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc; find-label; do-jump)
  open FlatStepsAPI {FS} using (FlatSteps; step-at; FlatSteps-++; flat-label; flat-jmp)
  open import Once.LinCore.Moves {FS} using (Seg; Seg-++ˡ; slot; Keep; k-halt; keep-pc; keep-trans; Old)

  ----------------------------------------------------------------------
  -- 1. AT AN ADDRESS: the flat pc, running, the configuration in the frame.
  ----------------------------------------------------------------------

  record HereQ {sh} (q : ℕ) (m : Cfg sh) (fs : FlatState) : Set where
    field
      q-pc  : fpc fs ≡ q
      q-run : LocState.halted (floc fs) ≡ false
      q-cfg : CfgW (LocState.heapMem (floc fs)) (slot fs) φ m
  open HereQ

  -- a loop's dispatch, inside the program
  dispIn : ∀ {E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
         → (s : Sub root (loop b ⨾ k)) → Inside prog (dispC (lowAt s))
  dispIn s = in-trans (here-in s) (disp-in (lowAt s))

  posD : ∀ {E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
       → Sub root (loop b ⨾ k) → ℕ
  posD s = length (proj₁ (dispIn s))

  ----------------------------------------------------------------------
  -- 2. ★ ENTERING: the head label, then the body.
  ----------------------------------------------------------------------

  loop-enter : ∀ {E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
                 (s : Sub root (loop b ⨾ k)) {m : Cfg (E ∷ Es ∣ A ∷ S)} {fs}
             → Here s m fs → Moved (body s) fs 0 m
  loop-enter s {fs = fs} H =
    1 , record fs { fpc = suc (fpc fs) } ,
    step-at _ (h-run H , proj₁ (seg-at s H)) (flat-label prog fs (jl j (lm (lowAt s)))) FlatStepsAPI.[] ,
    record { h-pc = trans (cong suc (h-pc H)) (sym pos-body) ; h-run = h-run H ; h-cfg = h-cfg H } ,
    keep-pc _ , refl , (λ _ _ → refl) , (λ _ _ → refl)
    where
      pR = proj₁ R ; pS = proj₁ (ins (sub-low L₀ s))
      pos-body : pos (body s) ≡ suc (pos s)
      pos-body = trans (pos-def (body s)) (trans (cong length (sym (++-assoc pR pS (instr-ctrl (c-label (jl j (lm (lowAt s)))) ∷ []))))
                   (trans (length-++ (pR ++ pS)) (trans (+-comm (length (pR ++ pS)) 1) (cong suc (sym (pos-def s))))))

  ----------------------------------------------------------------------
  -- 3. ★ A BODY'S END: the jump to its loop's dispatch.
  ----------------------------------------------------------------------

  end-jump : ∀ {sh} (s : Sub root (end {sh})) {L rest} {m : Cfg sh} {fs}
           → Labelled → lfin (lowAt s) ≡ instr-ctrl (c-jmp L) ∷ [] → (ins′ : Inside prog (instr-ctrl (c-label L) ∷ rest))
           → Here s m fs
           → Σ FlatState λ fs′ → FlatSteps prog 1 fs fs′ × HereQ (length (proj₁ ins′)) m fs′ × Keep fs fs′
               × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs)
               × Old (AllocState.next-heap-ref (falloc fs)) fs fs′ × (∀ x → budget φ ≤ x → slot fs′ x ≡ slot fs x)
  end-jump s {L} {fs = fs} lab e ins′ H =
    record fs { fpc = length (proj₁ ins′) } ,
    step-at _ (h-run H , proj₁ (subst (Seg prog (fpc fs)) e (seg-at s H)))
      (trans (flat-jmp prog fs L) (cong (λ x → do-jump x fs) (lab ins′))) FlatStepsAPI.[] ,
    record { q-pc = refl ; q-run = h-run H ; q-cfg = h-cfg H } ,
    keep-pc _ , refl , (λ _ _ → refl) , (λ _ _ → refl)

  ----------------------------------------------------------------------
  -- 4. ★ THE DISPATCH: its label, the tag read; on 0 the jump to `Li` and
  -- the result shifted (then `k`), on 1 the next state shifted and the
  -- jump back to the loop's head.
  ----------------------------------------------------------------------

  private
    past : ∀ q n → q + suc n ≡ n + suc q
    past q n = trans (+-suc q n) (trans (cong suc (+-comm q n)) (sym (+-suc n q)))

    four : ∀ p n → n + (3 + suc p) ≡ p + suc (suc (suc (suc n)))
    four = solve-∀

    len-mvSSd : ∀ a b n → length (mvSSd a b n) ≡ Once.LinCore.Moves.ln {FS} n
    len-mvSSd a b zero    = refl
    len-mvSSd a b (suc n) = cong (λ z → suc (suc z)) (len-mvSSd a b n)

  disp-exit : ∀ {E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
                → Labelled → ∀ (s : Sub root (loop b ⨾ k)) {es : Slots (E ∷ Es)} {os : Stk S} {v : MV B} {fs}
            → HereQ (posD s) (es ∥ minl {B = A} v ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ v ∷ˢ os)
  disp-exit {E} {Es} {A} {B} {S} {b = b} {k} lab s {es} {os} {v} {fs} H =
    fin (case₁-sim prog fs₁ φ {E ∷ Es} {B} {A} {S} {es} {os} {v} Li q seg (lab labLi)
           (Seg-++ˡ prog q (instr-ctrl (c-label Li) ∷ MB) kcode (in-seg labLi)) (q-run H) (q-cfg H))
    where
      L = lowAt s
      m = lm L ; fin′ = lfin L ; eb = proj₁ (lcin L) ; ek = proj₂ (lcin L)
      Lh = jl j m ; Ld = jl j (suc m) ; Li = jl j (suc (suc m))
      lb = lowC φ j (suc (suc (suc m))) (instr-ctrl (c-jmp Ld) ∷ []) b eb
      t = Tp φ ((B ⊕t A) ∷ S) ; bot = Tp φ S
      MA = mvSSd (suc t) (bot ∸ wsz A) (wsz A) ; MB = mvSSd (suc t) (bot ∸ wsz B) (wsz B)
      kcode = proj₁ (lowC φ j (proj₂ lb) fin′ k ek)
      sD : Seg prog (fpc fs) (dispC L)
      sD = subst (λ z → Seg prog z (dispC L)) (sym (q-pc H)) (in-seg (dispIn s))
      fs₁ = record fs { fpc = suc (fpc fs) }
      seg = Seg-++ˡ prog (suc (fpc fs)) (lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero Li) ∷ []) _ (proj₂ sD)
      labLi : Inside prog (instr-ctrl (c-label Li) ∷ MB ++ kcode)
      labLi = in-trans (dispIn s) (in-trans in-∷ (in-trans in-∷ (in-trans in-∷ (in-trans in-∷
                (in-trans (in-mid MA (instr-ctrl (c-jmp Lh) ∷ instr-ctrl (c-label Li) ∷ MB) kcode) in-∷)))))
      q = length (proj₁ labLi)
      pR = proj₁ R ; pS = proj₁ (ins (sub-low L₀ s)) ; dP = proj₁ (dispIn s)
      Y = instr-ctrl (c-label Ld) ∷ lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero Li) ∷ (MA ++ instr-ctrl (c-jmp Lh) ∷ [])
      Z = instr-ctrl (c-label Li) ∷ MB
      Y′ = instr-ctrl (c-label Ld) ∷ lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero Li) ∷ (MA ++ instr-ctrl (c-jmp Lh) ∷ Z)
      lists : (dP ++ Y) ++ Z ≡ pR ++ (pS ++ (instr-ctrl (c-label Lh) ∷ (proj₁ lb ++ Y′)))
      lists = trans (++-assoc dP Y Z)
                (trans (cong (λ w → dP ++ (instr-ctrl (c-label Ld) ∷ lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero Li) ∷ w))
                             (++-assoc MA (instr-ctrl (c-jmp Lh) ∷ []) Z))
                  (trans (++-assoc (pR ++ pS) (instr-ctrl (c-label Lh) ∷ proj₁ lb) Y′)
                         (++-assoc pR pS (instr-ctrl (c-label Lh) ∷ (proj₁ lb ++ Y′)))))
      pos-exit : pos (next s) ≡ Once.LinCore.Moves.ln {FS} (wsz B) + suc q
      pos-exit = trans (pos-def (next s)) (trans (cong length (sym lists))
                   (trans (length-++ (dP ++ Y)) (trans (cong (λ z → q + suc z) (len-mvSSd (suc t) (bot ∸ wsz B) (wsz B))) (past q _))))
      fin : _ → Moved (next s) fs 0 (es ∥ v ∷ˢ os)
      fin (fs′ , st , C′ , pc , K , nx , hp , tp) =
        _ , fs′ , step-at fs₁ (q-run H , proj₁ sD) (flat-label prog fs Ld) st ,
        record { h-pc = trans pc (sym pos-exit) ; h-run = trans (k-halt K) (q-run H) ; h-cfg = C′ } ,
        keep-trans (keep-pc _) K , nx , (λ hl _ → cong (λ h → h hl) hp) , tp

  disp-again : ∀ {E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
                 → Labelled → ∀ (s : Sub root (loop b ⨾ k)) {es : Slots (E ∷ Es)} {os : Stk S} {a : MV A} {fs}
             → HereQ (posD s) (es ∥ minr {A = B} a ∷ˢ os) fs → Moved s fs 0 (es ∥ a ∷ˢ os)
  disp-again {E} {Es} {A} {B} {S} {b = b} {k} lab s {es} {os} {a} {fs} H =
    fin (case₂-sim prog fs₁ φ {E ∷ Es} {B} {A} {S} {es} {os} {a} Li seg (q-run H) (q-cfg H))
    where
      L = lowAt s
      m = lm L ; fin′ = lfin L ; eb = proj₁ (lcin L) ; ek = proj₂ (lcin L)
      Lh = jl j m ; Ld = jl j (suc m) ; Li = jl j (suc (suc m))
      lb = lowC φ j (suc (suc (suc m))) (instr-ctrl (c-jmp Ld) ∷ []) b eb
      t = Tp φ ((B ⊕t A) ∷ S) ; bot = Tp φ S
      MA = mvSSd (suc t) (bot ∸ wsz A) (wsz A) ; MB = mvSSd (suc t) (bot ∸ wsz B) (wsz B)
      kcode = proj₁ (lowC φ j (proj₂ lb) fin′ k ek)
      X = instr-ctrl (c-jmp Lh) ∷ instr-ctrl (c-label Li) ∷ MB
      sD : Seg prog (fpc fs) (dispC L)
      sD = subst (λ z → Seg prog z (dispC L)) (sym (q-pc H)) (in-seg (dispIn s))
      fs₁ = record fs { fpc = suc (fpc fs) }
      seg = Seg-++ˡ prog (suc (fpc fs)) (lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero Li) ∷ MA) X
              (Seg-++ˡ prog (suc (fpc fs)) (lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero Li) ∷ (MA ++ X)) kcode (proj₂ sD))
      jmpIn : Inside prog (instr-ctrl (c-jmp Lh) ∷ instr-ctrl (c-label Li) ∷ MB ++ kcode)
      jmpIn = in-trans (dispIn s) (in-trans in-∷ (in-trans in-∷ (in-trans in-∷ (in-trans in-∷ (in-mid MA X kcode)))))
      dP = proj₁ (dispIn s)
      at-jmp : Once.LinCore.Moves.ln {FS} (wsz A) + (3 + suc (fpc fs)) ≡ length (proj₁ jmpIn)
      at-jmp = trans (cong (λ z → Once.LinCore.Moves.ln {FS} (wsz A) + (3 + suc z)) (q-pc H))
                 (trans (four (posD s) _)
                   (sym (trans (length-++ dP {instr-ctrl (c-label Ld) ∷ lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero Li) ∷ MA})
                          (cong (λ z → posD s + suc (suc (suc (suc z)))) (len-mvSSd (suc t) (bot ∸ wsz A) (wsz A))))))
      fin : _ → Moved s fs 0 (es ∥ a ∷ˢ os)
      fin (fs₂ , st , C′ , pc , K , nx , hp , tp) =
        _ , record fs₂ { fpc = pos s } ,
        step-at fs₁ (q-run H , proj₁ sD) (flat-label prog fs Ld)
          (FlatSteps-++ st (step-at {i = instr-ctrl (c-jmp Lh)} _ (h₂ , proj₁ (subst (λ z → Seg prog z (instr-ctrl (c-jmp Lh) ∷ instr-ctrl (c-label Li) ∷ MB ++ kcode)) (sym (trans pc at-jmp)) (in-seg jmpIn)))
                              (trans (flat-jmp prog fs₂ Lh) (trans (cong (λ x → do-jump x fs₂) (lab (here-in s)))
                                                                   (cong (λ z → record fs₂ { fpc = z }) (sym (pos-def s))))) FlatStepsAPI.[])) ,
        record { h-pc = refl ; h-run = h₂ ; h-cfg = C′ } ,
        keep-trans (keep-pc _) (keep-trans K (keep-pc _)) , nx , (λ hl _ → cong (λ h → h hl) hp) , tp
        where
          h₂ : LocState.halted (floc fs₂) ≡ false
          h₂ = trans (k-halt K) (q-run H)
