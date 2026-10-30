-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Round   (plan 0.125 S3, cata M4 stage C)
--
-- ONE PASS OF THE FLATTEN LOOP (`Text.Pieces.flatTxt`), from the loop head
-- `ℓ l1` with todo `xs` and eval `es`, as an abstract `Walk`:
--
--   * `Exit.out` (todo empty): the head's three rows and the branch, which
--     finds the sentinel's tag and jumps to the exit label `ℓ (l1+1)`; one
--     past that label, todo `[]`, eval `es`.
--   * `Round.round` (todo `t ∷ ts`): the head, the branch falls through
--     (`t`'s word is a pointer, `node-nz`), the inline pop (todo := `ts`,
--     the word into `Input1` and tmp), `push2` onto eval, `Input1` := the
--     node again, `visit-walk` on the node's TOP LAYER (`μ-word`: the node's
--     validity is its layer's, at the same place), and the back edge
--     `c-jmp ℓ l1` (`find-label` resolves it to the head). Back at the head
--     with todo `pushAllV (kidsI …) ts`, eval `t ∷ es`.
--
-- Slots kept (`KL n c`): the value stack's (`n+2`) and every slot from the
-- call slots `c` on (the closure record, the argument pair); everything
-- below the frontier `n` is the walk's `Seg`. The run is silent.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.Round (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Meaning o using (μ-layer-val)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Visit o tbl using (module CataVisitC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Layer o using (kidsI; pushAllV)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Text o tbl using (module Pieces; module SlotArith; module OffArith)
open import Once.CCC.Codegen.IRToTrace o using (push2; visit-walk; fsize)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue; readReg; Output; Input1
        ; SV-Ptr; SV-Tag; sv-as-loc; store-at-slot; load-from-slot; load-indirect; load-indirect-suc; mov-to-input
        ; instr-ctrl; c-branch-tag-zero; c-jmp; c-label; writeReg-preserves)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot)
open import Once.CCC.Label using (ℓ)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F; μ-type)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Nat using (s≤s; z≤n; _*_)
open import Data.Nat.Properties using (+-monoʳ-<; m<m+n)

open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

private
  pos22 : ∀ (v b : ℕ) → v + (22 + b) ≡ (22 + v) + b
  pos22 = solve 2 (λ v b → v :+ (con 22 :+ b) := (con 22 :+ v) :+ b) refl

module CataRoundC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open CataStepsC {FS}
  open CataStackC {FS}
  open CataWalkC {FS}
  open CataVisitC {FS} using (module Visit)
  open FlatStepsAPI {FS} using (flat-tag-branch-yes; flat-tag-branch-not)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  -- the slots the loop keeps: the value stack's, and the call slots on
  KL : ℕ → ℕ → ℕ → Set
  KL n c j = (j ≡ n + 2) ⊎ (c ≤ j)

  -- a node's word is a word of its top layer, at the same place
  μ-word : ∀ {prog a F} (wf : WellFormedFI F) {t w s}
         → WordAt prog a (μ-type F) t w s → WordAt prog a (⟦ F ⟧TI (μ-type F)) (μ-layer-val wf t) w s
  μ-word wf (w-ptr loc e lv val) = w-ptr loc e lv (μ-layer {wf = wf} val)
  μ-word wf (w-inl (rep-prim ()) e)
  μ-word wf (w-inl (rep-unit () _) e)

  -- a control step as a segment
  seg-ctrl : ∀ {a₀ : AllocState {FS}} {n : ℕ} (t : FlatState) (k : ℕ) → SegA a₀ n t (record t { fpc = k })
  seg-ctrl t k = record { mem = λ _ _ → refl ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }

  module Loop (prog : AbstractTrace) {F : IRFunctor} (wf : WellFormedFI F) (n c l1 : ℕ) (sn : HeapLocation)
              (cb : n + 7 + 4 * fsize ⌈ F ⌉F ≤ c) (H : ℕ)
              (span : SpanAt prog H (Pieces.flatTxt ⌈ F ⌉F n l1))
              (hd : find-label prog (ℓ o l1) ≡ just H)
              (ex : find-label prog (ℓ o (suc l1)) ≡ just ((23 + length (Pieces.visitTxt ⌈ F ⌉F n l1)) + H))
              (lv : LabelsAt prog (22 + H) (Pieces.visitTxt ⌈ F ⌉F n l1)) where

    open Pieces ⌈ F ⌉F n l1

    n7≤c : n + 7 ≤ c
    n7≤c = ≤-trans (m≤m+n (n + 7) (4 * fsize ⌈ F ⌉F)) cb

    open SlotArith n c n7≤c
    open OffArith n

    NE : ElemP ⟦ μ-type F ⟧
    NE = NodeE prog F

    K : ℕ → Set
    K = KL n c

    VL : ℕ
    VL = length visitTxt

    -- the exit label's row
    XL : ℕ
    XL = (23 + VL) + H

    module V = Visit prog F n n (n + 4) (n + 5) sn c ≤-refl (m≤m+n n 4) (m≤m+n n 5) n≢4 n≢5 4≢5

    -- the loop's slots, as the visit walk keeps them
    kv : ∀ j → K j → V.KV (n + 7) j
    kv _ (inj₁ refl) = inj₁ (+-monoʳ-< n (s≤s (s≤s (s≤s z≤n)))) , (λ e → off0-≢ {2} (λ ()) (sym e)) , off-≢ (λ ()) , off-≢ (λ ())
    kv j (inj₂ c≤j)  = inj₂ c≤j , far lt0 c≤j , far lt4 c≤j , far lt5 c≤j

    k≢n : ∀ j → K j → j ≢ n
    k≢n _ (inj₁ refl) e = off0-≢ {2} (λ ()) (sym e)
    k≢n j (inj₂ c≤j)    = far lt0 c≤j

    k≢3 : ∀ j → K j → j ≢ n + 3
    k≢3 _ (inj₁ refl) = off-≢ (λ ())
    k≢3 j (inj₂ c≤j)  = far lt3 c≤j

    k-push : ∀ j → K j → (j ≢ suc n) × (j ≢ n + 4) × (j ≢ n + 5)
    k-push _ (inj₁ refl) = (λ e → off-≢ {2} {1} (λ ()) (trans e suc-is)) , off-≢ (λ ()) , off-≢ (λ ())
    k-push j (inj₂ c≤j)  = far lt1 c≤j , far lt4 c≤j , far lt5 c≤j

    -- the exit label and the back edge, as rows of the text
    fetch-exit : fetch flatTxt (23 + VL) ≡ just (instr-ctrl (c-label (ℓ o (suc l1))))
    fetch-exit = subst (λ z → fetch (visitTxt ++ exitTxt) z ≡ just (instr-ctrl (c-label (ℓ o (suc l1)))))
                       (+-comm VL 1) (fetch-++-right visitTxt exitTxt 1)

    fetch-jmp : fetch flatTxt (22 + VL) ≡ just (instr-ctrl (c-jmp (ℓ o l1)))
    fetch-jmp = subst (λ z → fetch (visitTxt ++ exitTxt) z ≡ just (instr-ctrl (c-jmp (ℓ o l1))))
                      (+-identityʳ VL) (fetch-++-right visitTxt exitTxt 0)

    -- what one pass ends with
    EQ : List ⟦ μ-type F ⟧ → List ⟦ μ-type F ⟧ → FlatState → Set
    EQ xs es τ = StackAt NE (falloc τ) (floc τ) n sn xs × StackAt NE (falloc τ) (floc τ) (suc n) sn es

    --------------------------------------------------------------------
    -- THE HEAD: label, load todo, mov-to-input — common to both exits.
    --------------------------------------------------------------------
    module Head (σ : FlatState) (xs es : List ⟦ μ-type F ⟧) (pcH : fpc σ ≡ H) (nh : halted (floc σ) ≡ false)
                (st : StackAt NE (falloc σ) (floc σ) n sn xs) (se : StackAt NE (falloc σ) (floc σ) (suc n) sn es) where

      span′ : SpanAt prog (fpc σ) flatTxt
      span′ = subst (λ b → SpanAt prog b flatTxt) (sym pcH) span

      s₀ = floc σ
      a₀ = falloc σ
      f₀ = current-frame a₀
      tp = StackAt.top st

      h1 h2 h3 : FlatState
      h1 = record σ { fpc = suc (fpc σ) }
      h2 = St (load-from-slot n) h1
      h3 = St mov-to-input h2

      wf2 : InstrWF (floc h1) (falloc h1) (load-from-slot n)
      wf2 = SV-Ptr (AtDynamic tp) , StackAt.slot st
      nh2 : halted (floc h2) ≡ false
      nh2 = exec-abstract-preserves-halted-WF (load-from-slot n) s₀ a₀ nh wf2
      nh3 : halted (floc h3) ≡ false
      nh3 = exec-abstract-preserves-halted-WF mov-to-input (floc h2) (falloc h2) nh2 tt
      in3 : readReg (regs (floc h3)) Input1 ≡ SV-Ptr (AtDynamic tp)
      in3 = trans (in-movin (floc h2) (falloc h2)) (out-lslot n s₀ a₀ _ (StackAt.slot st))

      kp3 : Kp a₀ s₀ (falloc h3) (floc h3)
      kp3 = kp-∘ (kp-q (load-from-slot n) h1 nhw-load-from-slot refl tt tt) (kp-q mov-to-input h2 nhw-mov-to-input refl tt tt)
      cf3 : current-frame (falloc h3) ≡ f₀
      cf3 = trans (exec-abstract-preserves-frame mov-to-input (floc h2) (falloc h2))
                  (exec-abstract-preserves-frame (load-from-slot n) s₀ a₀)
      sl3 : ∀ j → readLoc (floc h3) (AtStack f₀ j) ≡ readLoc s₀ (AtStack f₀ j)
      sl3 j = trans (sl-keep mov-to-input (floc h2) (falloc h2) f₀ j nhw-mov-to-input refl)
                    (sl-keep (load-from-slot n) s₀ a₀ f₀ j nhw-load-from-slot refl)
      hk3 : ∀ hl → readLoc (floc h3) (AtDynamic hl) ≡ readLoc s₀ (AtDynamic hl)
      hk3 hl = trans (hp-keep mov-to-input (floc h2) (falloc h2) hl nhw-mov-to-input)
                     (hp-keep (load-from-slot n) s₀ a₀ hl nhw-load-from-slot)

      st3 : StackAt NE (falloc h3) (floc h3) n sn xs
      st3 = stack-keep node-tr kp3 cf3 (sl3 n) st
      se3 : StackAt NE (falloc h3) (floc h3) (suc n) sn es
      se3 = stack-keep node-tr kp3 cf3 (sl3 (suc n)) se

      -- the branch reads the top block's cell 0
      cond : tag-zf (flat-read-tag (floc h3)) ≡ DL.null xs
      cond = stack-tag node-nz st3 in3

      walk : Walk prog n K σ (3 + fpc σ) (λ _ → ⊤)
      walk =
        walk-∘ {prog} {n} {K} {σ} (walk-ctrl {Q = λ _ → ⊤} σ (instr-ctrl (c-label (ℓ o l1))) (suc (fpc σ)) nh (span′ 0 _ refl) refl refl tt tt)
        (walk-∘ {prog} {n} {K} {h1} (walk-q {Q = λ _ → ⊤} h1 (load-from-slot n) refl nh (span′ 1 _ refl) wf2 nhw-load-from-slot refl tt tt refl tt tt)
                (walk-q {Q = λ _ → ⊤} h2 mov-to-input refl nh2 (span′ 2 _ refl) tt nhw-mov-to-input refl tt tt refl tt tt))

    --------------------------------------------------------------------
    -- THE EXIT: todo is empty, the branch jumps out.
    --------------------------------------------------------------------
    module Exit (σ : FlatState) (es : List ⟦ μ-type F ⟧) (pcH : fpc σ ≡ H) (nh : halted (floc σ) ≡ false)
                (st : StackAt NE (falloc σ) (floc σ) n sn []) (se : StackAt NE (falloc σ) (floc σ) (suc n) sn es) where

      open Head σ [] es pcH nh st se

      x1 : FlatState
      x1 = record h3 { fpc = XL }

      wb : Walk prog n K h3 XL (λ _ → ⊤)
      wb = walk-ctrl h3 (instr-ctrl (c-branch-tag-zero (ℓ o (suc l1)))) XL nh3 (span′ 3 _ refl)
             (trans (flat-tag-branch-yes prog h3 (ℓ o (suc l1)) cond) (cong (λ mj → do-jump mj h3) ex)) refl tt tt

      wl : Walk prog n K x1 (suc XL) (EQ [] es)
      wl = walk-ctrl x1 (instr-ctrl (c-label (ℓ o (suc l1)))) (suc XL) nh3 (span (23 + VL) _ fetch-exit) refl refl tt (st3 , se3)

      abstract
        out : Walk prog n K σ (suc XL) (EQ [] es)
        out = walk-∘ {prog} {n} {K} {σ} walk (walk-∘ {prog} {n} {K} {h3} wb wl)

    --------------------------------------------------------------------
    -- ONE ROUND: todo is `t ∷ ts`.
    --------------------------------------------------------------------
    RQ : ⟦ μ-type F ⟧ → List ⟦ μ-type F ⟧ → List ⟦ μ-type F ⟧ → FlatState → Set
    RQ t ts es = EQ (pushAllV (kidsI wf (μ-type F) (μ-layer-val wf t)) ts) (t ∷ es)

    module Round (σ : FlatState) (t : ⟦ μ-type F ⟧) (ts es : List ⟦ μ-type F ⟧) (pcH : fpc σ ≡ H) (nh : halted (floc σ) ≡ false)
                 (st : StackAt NE (falloc σ) (floc σ) n sn (t ∷ ts)) (se : StackAt NE (falloc σ) (floc σ) (suc n) sn es) where

      open Head σ (t ∷ ts) es pcH nh st se

      -- the top block, taken apart
      data Top : Set where
        top-is : (w : StoredValue FS) (nb : HeapLocation)
               → readLoc s₀ (AtDynamic tp) ≡ just w → NE a₀ s₀ t w
               → readLoc s₀ (AtDynamic (sucHL tp)) ≡ just (SV-Ptr (AtDynamic nb))
               → Chain NE a₀ s₀ sn nb ts → Top

      uncons : ∀ {b} → Chain NE a₀ s₀ sn b (t ∷ ts) → b ≡ tp → Top
      uncons (ch-cons w lv r0 e r1 ch) refl = top-is w _ r0 e r1 ch

      tp-cell : Top
      tp-cell = uncons (StackAt.chain st) refl

      module T (w : StoredValue FS) (nb : HeapLocation)
               (c0 : readLoc s₀ (AtDynamic tp) ≡ just w) (ew : NE a₀ s₀ t w)
               (c1 : readLoc s₀ (AtDynamic (sucHL tp)) ≡ just (SV-Ptr (AtDynamic nb)))
               (rest : Chain NE a₀ s₀ sn nb ts) where

        tmp : ℕ
        tmp = n + 3

        h4 p1 p2 p3 p4 p5 p6 : FlatState
        h4 = record h3 { fpc = suc (fpc h3) }
        p1 = St load-indirect-suc h4
        p2 = St (store-at-slot n) p1
        p3 = St load-indirect p2
        p4 = St mov-to-input p3
        p5 = St (store-at-slot tmp) p4
        p6 = St (load-from-slot tmp) p5

        Inp Oup : FlatState → StoredValue FS
        Inp q = readReg (regs (floc q)) Input1
        Oup q = readReg (regs (floc q)) Output

        sl : FlatState → ℕ → Maybe (StoredValue FS)
        sl q j = readLoc (floc q) (AtStack f₀ j)

        hk : ∀ (i : AbstractInstr) (q : FlatState) hl → InstrNoHeapWrite i
           → readLoc (floc (St i q)) (AtDynamic hl) ≡ readLoc (floc q) (AtDynamic hl)
        hk i q hl nhw = hp-keep i (floc q) (falloc q) hl nhw

        -- the branch falls through: the top element is a node, not the tag
        cond-no : tag-zf (flat-read-tag (floc h3)) ≡ false
        cond-no = cond

        c0-3 : readLoc (floc h3) (AtDynamic tp) ≡ just w
        c0-3 = trans (hk3 tp) c0
        c1-3 : readLoc (floc h3) (AtDynamic (sucHL tp)) ≡ just (SV-Ptr (AtDynamic nb))
        c1-3 = trans (hk3 (sucHL tp)) c1

        -- row 4: Output := next
        wf-p1 : InstrWF (floc h4) (falloc h4) load-indirect-suc
        wf-p1 = AtDynamic tp , cong sv-as-loc in3 , SV-Ptr (AtDynamic nb) , c1-3
        nh-p1 : halted (floc p1) ≡ false
        nh-p1 = exec-abstract-preserves-halted-WF load-indirect-suc (floc h4) (falloc h4) nh3 wf-p1
        out-p1 : Oup p1 ≡ SV-Ptr (AtDynamic nb)
        out-p1 = out-lind-suc (floc h4) (falloc h4) (AtDynamic tp) _ in3 c1-3
        in-p1 : Inp p1 ≡ SV-Ptr (AtDynamic tp)
        in-p1 = trans (load-ind-suc-preserves-input (floc h4) (falloc h4) (AtDynamic tp) _ (cong sv-as-loc in3) c1-3) in3
        cf-p1 : current-frame (falloc p1) ≡ f₀
        cf-p1 = trans (exec-abstract-preserves-frame load-indirect-suc (floc h4) (falloc h4)) cf3

        -- row 5: todo := next
        nh-p2 : halted (floc p2) ≡ false
        nh-p2 = exec-abstract-preserves-halted-WF (store-at-slot n) (floc p1) (falloc p1) nh-p1 tt
        td-p2 : sl p2 n ≡ just (SV-Ptr (AtDynamic nb))
        td-p2 = trans (sl-same n (floc p1) (falloc p1) f₀ cf-p1) (cong just out-p1)
        in-p2 : Inp p2 ≡ SV-Ptr (AtDynamic tp)
        in-p2 = trans (reg-store n (floc p1) (falloc p1) Input1) in-p1
        cf-p2 : current-frame (falloc p2) ≡ f₀
        cf-p2 = trans (exec-abstract-preserves-frame (store-at-slot n) (floc p1) (falloc p1)) cf-p1

        c0-p2 : readLoc (floc p2) (AtDynamic tp) ≡ just w
        c0-p2 = trans (hk (store-at-slot n) p1 tp nhw-store-at-slot) (trans (hk load-indirect-suc h4 tp nhw-load-indirect-suc) c0-3)

        -- row 6: Output := the node
        wf-p3 : InstrWF (floc p2) (falloc p2) load-indirect
        wf-p3 = AtDynamic tp , cong sv-as-loc in-p2 , w , c0-p2
        nh-p3 : halted (floc p3) ≡ false
        nh-p3 = exec-abstract-preserves-halted-WF load-indirect (floc p2) (falloc p2) nh-p2 wf-p3
        out-p3 : Oup p3 ≡ w
        out-p3 = out-lind (floc p2) (falloc p2) (AtDynamic tp) w in-p2 c0-p2
        td-p3 : sl p3 n ≡ just (SV-Ptr (AtDynamic nb))
        td-p3 = trans (sl-keep load-indirect (floc p2) (falloc p2) f₀ n nhw-load-indirect refl) td-p2
        cf-p3 : current-frame (falloc p3) ≡ f₀
        cf-p3 = trans (exec-abstract-preserves-frame load-indirect (floc p2) (falloc p2)) cf-p2

        -- row 7: Input1 := the node
        nh-p4 : halted (floc p4) ≡ false
        nh-p4 = exec-abstract-preserves-halted-WF mov-to-input (floc p3) (falloc p3) nh-p3 tt
        out-p4 : Oup p4 ≡ w
        out-p4 = trans (writeReg-preserves (regs (floc p3)) Input1 Output (readReg (regs (floc p3)) Output) (λ ())) out-p3
        td-p4 : sl p4 n ≡ just (SV-Ptr (AtDynamic nb))
        td-p4 = trans (sl-keep mov-to-input (floc p3) (falloc p3) f₀ n nhw-mov-to-input refl) td-p3
        cf-p4 : current-frame (falloc p4) ≡ f₀
        cf-p4 = trans (exec-abstract-preserves-frame mov-to-input (floc p3) (falloc p3)) cf-p3

        -- row 8: tmp := the node
        nh-p5 : halted (floc p5) ≡ false
        nh-p5 = exec-abstract-preserves-halted-WF (store-at-slot tmp) (floc p4) (falloc p4) nh-p4 tt
        tmp-p5 : sl p5 tmp ≡ just w
        tmp-p5 = trans (sl-same tmp (floc p4) (falloc p4) f₀ cf-p4) (cong just out-p4)
        td-p5 : sl p5 n ≡ just (SV-Ptr (AtDynamic nb))
        td-p5 = trans (sl-other tmp n (floc p4) (falloc p4) f₀ (off0-≢ (λ ()))) td-p4
        cf-p5 : current-frame (falloc p5) ≡ f₀
        cf-p5 = trans (exec-abstract-preserves-frame (store-at-slot tmp) (floc p4) (falloc p4)) cf-p4

        -- row 9: Output := the node
        wf-p6 : InstrWF (floc p5) (falloc p5) (load-from-slot tmp)
        wf-p6 = w , at-cf (floc p5) (falloc p5) cf-p5 tmp-p5
        nh-p6 : halted (floc p6) ≡ false
        nh-p6 = exec-abstract-preserves-halted-WF (load-from-slot tmp) (floc p5) (falloc p5) nh-p5 wf-p6
        out-p6 : Oup p6 ≡ w
        out-p6 = out-lslot tmp (floc p5) (falloc p5) w (proj₂ wf-p6)
        td-p6 : sl p6 n ≡ just (SV-Ptr (AtDynamic nb))
        td-p6 = trans (sl-keep (load-from-slot tmp) (floc p5) (falloc p5) f₀ n nhw-load-from-slot refl) td-p5
        tmp-p6 : sl p6 tmp ≡ just w
        tmp-p6 = trans (sl-keep (load-from-slot tmp) (floc p5) (falloc p5) f₀ tmp nhw-load-from-slot refl) tmp-p5
        cf-p6 : current-frame (falloc p6) ≡ f₀
        cf-p6 = trans (exec-abstract-preserves-frame (load-from-slot tmp) (floc p5) (falloc p5)) cf-p5

        -- every slot but todo and tmp
        slots6 : ∀ j → j ≢ n → j ≢ tmp → sl p6 j ≡ sl σ j
        slots6 j j≢n j≢t =
          trans (sl-keep (load-from-slot tmp) (floc p5) (falloc p5) f₀ j nhw-load-from-slot refl)
          (trans (sl-other tmp j (floc p4) (falloc p4) f₀ j≢t)
          (trans (sl-keep mov-to-input (floc p3) (falloc p3) f₀ j nhw-mov-to-input refl)
          (trans (sl-keep load-indirect (floc p2) (falloc p2) f₀ j nhw-load-indirect refl)
          (trans (sl-other n j (floc p1) (falloc p1) f₀ j≢n)
          (trans (sl-keep load-indirect-suc (floc h4) (falloc h4) f₀ j nhw-load-indirect-suc refl) (sl3 j))))))

        runA : SRun prog 10 σ p6
        runA =
          s-at h1 (nh , span′ 0 _ refl) refl refl tt (
          s-at h2 (nh , span′ 1 _ refl) refl refl tt (
          s-at h3 (nh2 , span′ 2 _ refl) refl refl tt (
          s-at h4 (nh3 , span′ 3 _ refl) (flat-tag-branch-not prog h3 (ℓ o (suc l1)) cond-no) refl tt (
          s-at p1 (nh3 , span′ 4 _ refl) refl refl tt (
          s-at p2 (nh-p1 , span′ 5 _ refl) refl refl tt (
          s-at p3 (nh-p2 , span′ 6 _ refl) refl refl tt (
          s-at p4 (nh-p3 , span′ 7 _ refl) refl refl tt (
          s-at p5 (nh-p4 , span′ 8 _ refl) refl refl tt (
          s-at p6 (nh-p5 , span′ 9 _ refl) refl refl tt s-nil)))))))))

        abstract
          segA : SegA a₀ n σ p6
          segA =
            segA-∘ (seg-ctrl σ (suc (fpc σ)))
            (segA-∘ (seg-q (load-from-slot n) h1 nhw-load-from-slot refl tt tt)
            (segA-∘ (seg-q mov-to-input h2 nhw-mov-to-input refl tt tt)
            (segA-∘ (seg-ctrl h3 (suc (fpc h3)))
            (segA-∘ (seg-q load-indirect-suc h4 nhw-load-indirect-suc refl tt tt)
            (segA-∘ (seg-store n p1 cf-p1 ≤-refl)
            (segA-∘ (seg-q load-indirect p2 nhw-load-indirect refl tt tt)
            (segA-∘ (seg-q mov-to-input p3 nhw-mov-to-input refl tt tt)
            (segA-∘ (seg-store tmp p4 cf-p4 (m≤m+n n 3))
                    (seg-q (load-from-slot tmp) p5 nhw-load-from-slot refl tt tt)))))))))

        kp6 : Kp a₀ s₀ (falloc p6) (floc p6)
        kp6 = seg-kp segA

        wA : Walk prog n K σ (10 + fpc σ) (λ _ → ⊤)
        wA = record
          { τ = p6 ; steps = 10 ; run = runA ; seg = segA ; nh = nh-p6 ; pc = refl ; ret = refl ; clo = refl ; lnk = refl
          ; cf = cf-p6 ; slots = λ j kj → slots6 j (k≢n j kj) (k≢3 j kj) ; post = tt }

        -- the stacks at p6
        todo6 : StackAt NE (falloc p6) (floc p6) n sn ts
        todo6 = stack-at nb (at-cf (floc p6) (falloc p6) cf-p6 td-p6) (chain-tr node-tr kp6 rest)
                  (trans (proj₂ kp6 _ (StackAt.sent-live st)) (StackAt.sent st)) (proj₁ kp6 _ (StackAt.sent-live st))
        eval6 : StackAt NE (falloc p6) (floc p6) (suc n) sn es
        eval6 = stack-keep node-tr kp6 cf-p6 (slots6 (suc n) s≢n (λ e → off-≢ {1} {3} (λ ()) (trans (sym suc-is) e))) se

        ex6 : NE (falloc p6) (floc p6) t (Oup p6)
        ex6 = subst (λ z → WordAt prog (falloc p6) (μ-type F) t z (floc p6)) (sym out-p6) (word-tr kp6 ew)

        ------------------------------------------------------------------
        -- rows 10-19: push2 onto eval
        ------------------------------------------------------------------
        SP1 = span-drop prog headTxt {pushTxt ++ (reloadTxt ++ (visitTxt ++ exitTxt))} (fpc σ) span′
        SPB : SpanAt prog (fpc p6) pushTxt
        SPB = span-take prog pushTxt {reloadTxt ++ (visitTxt ++ exitTxt)} (10 + fpc σ) SP1

        pu : Push2Out NE prog n (suc n) (n + 4) (n + 5) sn p6 t es
        pu = push2-run NE node-tr prog n (suc n) (n + 4) (n + 5) sn p6 t es SPB nh-p6
               (n≤1+n n) (m≤m+n n 4) (m≤m+n n 5) s≢4 s≢5 4≢5 ex6 eval6

        τ7 = Push2Out.τ pu
        kp7 : Kp (falloc p6) (floc p6) (falloc τ7) (floc τ7)
        kp7 = seg-kp (Push2Out.seg pu)

        sl7 : ∀ j → j ≢ suc n → j ≢ n + 4 → j ≢ n + 5
            → readLoc (floc τ7) (AtStack (current-frame (falloc τ7)) j) ≡ readLoc (floc p6) (AtStack (current-frame (falloc p6)) j)
        sl7 j a b c′ = trans (cong (λ f → readLoc (floc τ7) (AtStack f j)) (Push2Out.cf pu)) (Push2Out.slots pu j a b c′)

        tmp7 : readLoc (floc τ7) (AtStack (current-frame (falloc τ7)) tmp) ≡ just w
        tmp7 = trans (sl7 tmp (λ e → off-≢ {3} {1} (λ ()) (trans e suc-is)) (off-≢ (λ ())) (off-≢ (λ ())))
                     (at-cf (floc p6) (falloc p6) cf-p6 tmp-p6)
        todo7 : StackAt NE (falloc τ7) (floc τ7) n sn ts
        todo7 = stack-keep node-tr kp7 (Push2Out.cf pu) (Push2Out.slots pu n (λ e → s≢n (sym e)) n≢4 n≢5) todo6
        ew7 : NE (falloc τ7) (floc τ7) t w
        ew7 = word-tr (kp-∘ kp6 kp7) ew

        wB : Walk prog n K p6 (10 + fpc p6) (λ q → StackAt NE (falloc q) (floc q) (suc n) sn (t ∷ es))
        wB = push-walk k-push pu

        ------------------------------------------------------------------
        -- rows 20-21: Input1 := the node
        ------------------------------------------------------------------
        q1 q2 : FlatState
        q1 = St (load-from-slot tmp) τ7
        q2 = St mov-to-input q1

        pc7 : fpc τ7 ≡ 20 + fpc σ
        pc7 = Push2Out.pc pu

        wf-q1 : InstrWF (floc τ7) (falloc τ7) (load-from-slot tmp)
        wf-q1 = w , tmp7
        nh-q1 : halted (floc q1) ≡ false
        nh-q1 = exec-abstract-preserves-halted-WF (load-from-slot tmp) (floc τ7) (falloc τ7) (Push2Out.nh pu) wf-q1
        nh-q2 : halted (floc q2) ≡ false
        nh-q2 = exec-abstract-preserves-halted-WF mov-to-input (floc q1) (falloc q1) nh-q1 tt
        in-q2 : Inp q2 ≡ w
        in-q2 = trans (in-movin (floc q1) (falloc q1)) (out-lslot tmp (floc τ7) (falloc τ7) w tmp7)

        kpq : Kp (falloc τ7) (floc τ7) (falloc q2) (floc q2)
        kpq = kp-∘ (kp-q (load-from-slot tmp) τ7 nhw-load-from-slot refl tt tt) (kp-q mov-to-input q1 nhw-mov-to-input refl tt tt)
        cfq : current-frame (falloc q2) ≡ current-frame (falloc τ7)
        cfq = trans (exec-abstract-preserves-frame mov-to-input (floc q1) (falloc q1))
                    (exec-abstract-preserves-frame (load-from-slot tmp) (floc τ7) (falloc τ7))
        slq : ∀ j → readLoc (floc q2) (AtStack (current-frame (falloc τ7)) j) ≡ readLoc (floc τ7) (AtStack (current-frame (falloc τ7)) j)
        slq j = trans (sl-keep mov-to-input (floc q1) (falloc q1) _ j nhw-mov-to-input refl)
                      (sl-keep (load-from-slot tmp) (floc τ7) (falloc τ7) _ j nhw-load-from-slot refl)

        ft-q : ∀ (k : ℕ) {i : AbstractInstr} → fetch flatTxt (20 + k) ≡ just i → fetch prog (k + fpc τ7) ≡ just i
        ft-q k {i} e = subst (λ z → fetch prog (k + z) ≡ just i) (sym pc7)
                         (subst (λ z → fetch prog z ≡ just i) (pos20 k (fpc σ)) (span′ (20 + k) i e))
          where
            pos20 : ∀ (a b : ℕ) → (20 + a) + b ≡ a + (20 + b)
            pos20 = solve 2 (λ a b → (con 20 :+ a) :+ b := a :+ (con 20 :+ b)) refl

        wC : Walk prog n K τ7 (fpc q2) (λ _ → ⊤)
        wC = walk-∘ {prog} {n} {K} {τ7}
               (walk-q {Q = λ _ → ⊤} τ7 (load-from-slot tmp) refl (Push2Out.nh pu) (ft-q 0 refl) wf-q1 nhw-load-from-slot refl tt tt refl tt tt)
               (walk-q {Q = λ _ → ⊤} q1 mov-to-input refl nh-q1 (ft-q 1 refl) tt nhw-mov-to-input refl tt tt refl tt tt)

        todo-q : StackAt NE (falloc q2) (floc q2) n sn ts
        todo-q = stack-keep node-tr kpq cfq (slq n) todo7
        eval-q : StackAt NE (falloc q2) (floc q2) (suc n) sn (t ∷ es)
        eval-q = stack-keep node-tr kpq cfq (slq (suc n)) (Push2Out.stack pu)
        wd-q : V.InWord (⟦ F ⟧TI (μ-type F)) (μ-layer-val wf t) q2
        wd-q = subst (λ z → WordAt prog (falloc q2) (⟦ F ⟧TI (μ-type F)) (μ-layer-val wf t) z (floc q2)) (sym in-q2)
                     (μ-word wf (word-tr kpq ew7))

        ------------------------------------------------------------------
        -- the visit walk on the node's top layer
        ------------------------------------------------------------------
        pc22 : fpc q2 ≡ 22 + fpc σ
        pc22 = cong (λ z → suc (suc z)) pc7

        SPV : SpanAt prog (fpc q2) visitTxt
        SPV = subst (λ b → SpanAt prog b visitTxt) (sym pc22)
                (span-take prog visitTxt {exitTxt} (22 + fpc σ)
                  (span-drop prog (headTxt ++ (pushTxt ++ reloadTxt)) {visitTxt ++ exitTxt} (fpc σ) span′))
        LAV : LabelsAt prog (fpc q2) visitTxt
        LAV = subst (λ b → LabelsAt prog b visitTxt) (sym (trans pc22 (cong (22 +_) pcH))) lv

        wv : Walk prog n (V.KV (n + 7)) q2 (VL + fpc q2) (V.VQ wf (μ-layer-val wf t) ts)
        wv = V.visit wf (n + 7) (l1 + 4) q2 (μ-layer-val wf t) ts (m≤m+n n 7)
               (m<m+n n (s≤s z≤n))
               (+-monoʳ-< n (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
               (+-monoʳ-< n (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
               cb SPV LAV nh-q2 wd-q todo-q

        τv = Walk.τ wv

        eval-v : StackAt NE (falloc τv) (floc τv) (suc n) sn (t ∷ es)
        eval-v = stack-keep node-tr (walk-kp wv) (Walk.cf wv)
                   (Walk.slots wv (suc n) (inj₁ (subst (_< n + 7) (sym suc-is) (+-monoʳ-< n (s≤s (s≤s z≤n)))) , s≢n , s≢4 , s≢5)) eval-q

        ------------------------------------------------------------------
        -- the back edge
        ------------------------------------------------------------------
        pc-v : fpc τv ≡ (22 + VL) + fpc σ
        pc-v = trans (Walk.pc wv) (trans (cong (VL +_) pc22) (pos22 VL (fpc σ)))

        wj : Walk prog n K τv H (RQ t ts es)
        wj = walk-ctrl τv (instr-ctrl (c-jmp (ℓ o l1))) H (Walk.nh wv)
               (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-jmp (ℓ o l1)))) (sym pc-v) (span′ (22 + VL) _ fetch-jmp))
               (cong (λ mj → do-jump mj τv) hd) refl tt (Walk.post wv , eval-v)

        result : Walk prog n K σ H (RQ t ts es)
        result = walk-∘ {prog} {n} {K} {σ} wA (walk-∘ {prog} {n} {K} {p6} wB
                   (walk-∘ {prog} {n} {K} {τ7} wC (walk-∘ {prog} {n} {K} {q2} (walk-K kv wv) wj)))

      abstract
        round : Walk prog n K σ H (RQ t ts es)
        round with tp-cell
        ... | top-is w nb c0 ew c1 rest = T.result w nb c0 ew c1 rest
