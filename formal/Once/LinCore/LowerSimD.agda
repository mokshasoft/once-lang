-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimD — plan 0.146 B1.4b, `LowerSim` layer (4),
-- continued: the BRANCHES. A `case` tests the tag on the stack; `inl` jumps
-- to its label (given: the whole-run relation resolves it), `inr` falls
-- through; each shifts its payload up to the result's place.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n; _⊔_)
import Data.Nat.Properties
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-trans; ≤-reflexive; m≤n+m; m≤m+n; +-monoˡ-<; <-≤-trans)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using ( StoredValue; SV-Ptr; SV-Tag; readReg; writeReg; Input1; Output; lea-slot; mov-to-input; instr-ctrl
        ; c-branch-tag-zero; c-label; module AllocState; module LocState; module MemOps )
open import Once.CCC.Machine.Locations using (AtStack)
open import Once.CCC.Label using (LabelId)

module Once.LinCore.LowerSimD
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV; minl; minr)
open import Once.LinCore.Machine fmt ans bw using (Stk; _∷ˢ_; Slots; _∥_)
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw
open import Once.LinCore.MoveCode using (mvSSd)

module SimD {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf
  open CfgW
  open import Once.LinCore.Moves {FS} using (Seg; slot; mvSSd-run; MovedD; d-moved; d-rest; d-heap; d-pc; d-alloc; lea-step; mov-in-step
                                           ; Keep; keep-trans; keepD; keepS; keep-regs; keep-pc; keep-store; Ran; ran-trans; ran-regs; ran-store)
    renaming (ln to nsteps; d-halt to dm-halt)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc; fetch; find-label)
  open LocState using (heapMem) renaming (halted to fhalted)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps; step-at; FlatSteps-++; flat-tag-branch-yes; flat-tag-branch-not; flat-label)
    renaming ([] to done)

  -- the words a descending move leaves at its destination
  slots-movedD : ∀ {fs fs′ a b n} (w : List W) → MovedD fs fs′ a b n → SlotsAt (slot fs) a w → length w ≡ n
               → SlotsAt (slot fs′) b w
  slots-movedD {fs} {fs′} {a} {b} {n} w M s refl =
    subst (λ z → SlotsAt (slot fs′) z w) (Data.Nat.Properties.+-identityʳ b)
      (go w 0 (subst (λ z → SlotsAt (slot fs) z w) (sym (Data.Nat.Properties.+-identityʳ a)) s) (λ k k< → d-moved M k k<))
    where
      go : ∀ (v : List W) j → SlotsAt (slot fs) (a + j) v
         → (∀ k → k < j + length v → slot fs′ (b + k) ≡ slot fs (a + k)) → SlotsAt (slot fs′) (b + j) v
      go []      j s h = tt
      go (x ∷ v) j (e , s) h =
        trans (h j (subst (j <_) (sym (+-suc j (length v))) (s≤s (m≤m+n j (length v))))) e ,
        subst (λ z → SlotsAt (slot fs′) z v) (+-suc b j)
          (go v (suc j) (subst (λ z → SlotsAt (slot fs) z v) (sym (+-suc a j)) s)
             (λ k k< → h k (subst (k <_) (sym (+-suc j (length v))) k<)))

  -- the arithmetic of a sum on the stack
  private
    new-top : ∀ B a s → (B ∸ s) ∸ a ≡ B ∸ (a + s)
    new-top B a s = trans (Data.Nat.Properties.∸-+-assoc B s a) (cong (B ∸_) (+-comm s a))

    suc-∸ : ∀ m n → n < m → suc (m ∸ suc n) ≡ m ∸ n
    suc-∸ (suc m) zero    _        = refl
    suc-∸ (suc m) (suc n) (s≤s lt) = suc-∸ m n lt

  -- ★ a sum's payload shifted up from just past its tag to its own place
  -- (the result of a `case`): the rest of the stack and the environment kept
  shift-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es P S} {es : Slots Es} {os : Stk S} {p : MV P} (src : ℕ) (wP : List W)
            → Seg prog (fpc fs) (mvSSd src ((budget φ ∸ ws S) ∸ wsz P) (wsz P))
            → fhalted (floc fs) ≡ false
            → EnvW (heapMem (floc fs)) (slot fs) es → StkW (heapMem (floc fs)) (slot fs) φ os
            → VW (heapMem (floc fs)) p wP → SlotsAt (slot fs) src wP
            → src ≤ (budget φ ∸ ws S) ∸ wsz P → EP φ ≤ src → ws Es ≤ EP φ → ws (P ∷ S) ≤ OP φ
            → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz P)) fs fs′
                × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ p ∷ˢ os) × fpc fs′ ≡ nsteps (wsz P) + fpc fs × Keep fs fs′ × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs) × heapMem (floc fs′) ≡ heapMem (floc fs)
  shift-sim prog fs φ {Es} {P} {S} {es} {os} {p} src wP s h ev st pp sp up ep efit fit =
    fin (mvSSd-run prog fs src dst (wsz P) s h
           (λ k k< → def k k<)
           (λ k k′ lt _ e → Data.Nat.Properties.<-irrefl (sym e)
                              (Data.Nat.Properties.<-≤-trans (Data.Nat.Properties.+-monoʳ-< src lt) (Data.Nat.Properties.+-monoˡ-≤ k up))))
    where
      dst = (budget φ ∸ ws S) ∸ wsz P
      def : ∀ k → k < wsz P → Σ W λ v → slot fs (src + k) ≡ just v
      def k k< with slots-def {slot fs} {src} wP sp k (subst (k <_) (sym (vw-len pp)) k<)
      ... | (v , e) = v , trans (cong (slot fs) (+-comm src k)) e
      fitB : wsz P + ws S ≤ budget φ
      fitB = ≤-trans fit (m≤n+m (OP φ) (EP φ))
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) (wsz P)) fitB
      -- the destination: [dst, bot)
      in-dst : ∀ k → k < wsz P → dst + k < budget φ ∸ ws S
      in-dst k k< = Data.Nat.Properties.<-≤-trans (Data.Nat.Properties.+-monoʳ-< dst k<) (≤-reflexive (Data.Nat.Properties.m∸n+n≡m (≤∸ (wsz P) (ws S) (budget φ) fitB)))
      fin : Σ FlatState (λ fs′ → FlatSteps prog (nsteps (wsz P)) fs fs′ × MovedD fs fs′ src dst (wsz P))
          → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz P)) fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ p ∷ˢ os) × fpc fs′ ≡ nsteps (wsz P) + fpc fs × Keep fs fs′ × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs) × heapMem (floc fs′) ≡ heapMem (floc fs)
      fin (fs′ , st′ , M) =
        fs′ , st′ ,
        record { c-env  = subst (λ r → EnvW r (slot fs′) es) (sym (d-heap M))
                            (envW-frame es (λ x x< → d-rest M x (λ k k< e → Data.Nat.Properties.<-irrefl e
                                              (Data.Nat.Properties.<-≤-trans x< (≤-trans efit (≤-trans ep (≤-trans up (m≤m+n dst k))))))) ev)
               ; c-stk  = ( wP , subst (λ r → VW r p wP) (sym (d-heap M)) pp
                          , subst (λ z → SlotsAt (slot fs′) z wP) (new-top (budget φ) (wsz P) (ws S)) (slots-movedD wP M sp (vw-len pp)) )
                        , subst (λ r → StkW r (slot fs′) φ os) (sym (d-heap M))
                            (stkW-frame os fitS (λ x lo _ → d-rest M x (λ k k< e → Data.Nat.Properties.<-irrefl (sym e)
                                                   (Data.Nat.Properties.<-≤-trans (in-dst k k<) lo))) st)
               ; c-efit = efit ; c-sfit = fit } ,
        d-pc M , keepD M , cong AllocState.next-heap-ref (d-alloc M) , d-heap M

  open FlatMachine {FS} using (do-jump; tag-test; flat-read-tag)

  private
    -- the sum's place, its payload's
    sum-at : ∀ (φ : Frame) A B S → budget φ ∸ ws ((A ⊕t B) ∷ S) ≡ (budget φ ∸ ws S) ∸ suc (wsz A ⊔ wsz B)
    sum-at φ A B S = sym (new-top (budget φ) (suc (wsz A ⊔ wsz B)) (ws S))

    pay-up : ∀ (φ : Frame) A B S P → wsz P ≤ wsz A ⊔ wsz B → ws ((A ⊕t B) ∷ S) ≤ OP φ
           → suc (budget φ ∸ ws ((A ⊕t B) ∷ S)) ≤ (budget φ ∸ ws S) ∸ wsz P
    pay-up φ A B S P pM fit =
      ≤-trans (≤-reflexive (trans (cong suc (sum-at φ A B S)) (suc-∸ (budget φ ∸ ws S) (wsz A ⊔ wsz B) M<)))
              (Data.Nat.Properties.∸-monoʳ-≤ (budget φ ∸ ws S) pM)
      where M< : wsz A ⊔ wsz B < budget φ ∸ ws S
            M< = ≤∸ (suc (wsz A ⊔ wsz B)) (ws S) (budget φ) (≤-trans fit (m≤n+m (OP φ) (EP φ)))

  -- ★ `case`, `inl`: the tag is 0, the branch taken to the label; the label;
  -- the payload shifted up
  case₁-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es A B S} {es : Slots Es} {os : Stk S} {a : MV A}
                (L₁ : LabelId) (q : ℕ)
            → let t = budget φ ∸ ws ((A ⊕t B) ∷ S) ; bot = budget φ ∸ ws S in
              Seg prog (fpc fs) (lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero L₁) ∷ [])
            → find-label prog L₁ ≡ just q
            → Seg prog q (instr-ctrl (c-label L₁) ∷ mvSSd (suc t) (bot ∸ wsz A) (wsz A))
            → fhalted (floc fs) ≡ false
            → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ minl {B = B} a ∷ˢ os)
            → Σ FlatState λ fs′ → FlatSteps prog (4 + nsteps (wsz A)) fs fs′
                × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ a ∷ˢ os) × fpc fs′ ≡ nsteps (wsz A) + suc q × Keep fs fs′ × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs) × heapMem (floc fs′) ≡ heapMem (floc fs)
  case₁-sim prog fs φ {Es} {A} {B} {S} {es} {os} {a} L₁ q (f₁ , f₂ , f₃ , _) fl (fq , sq) h C = fin (c-stk C)
    where
      t = budget φ ∸ ws ((A ⊕t B) ∷ S)
      cf = AllocState.current-frame (falloc fs)
      fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (SV-Ptr (AtStack cf t)) } ; fpc = suc (fpc fs) }
      fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 (SV-Ptr (AtStack cf t)) } ; fpc = suc (fpc fs₁) }
      fs₃ = record fs₂ { fpc = q }
      fs₄ = record fs₃ { fpc = suc q }
      k₄ : Keep fs fs₄
      k₄ = keep-trans {fs₂ = fs₁} (keep-regs _ _) (keep-trans {fs₂ = fs₂} (keep-regs _ _) (keep-trans {fs₂ = fs₃} (keep-pc _) (keep-pc _)))
      Res = Σ FlatState λ fs′ → FlatSteps prog (4 + nsteps (wsz A)) fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ a ∷ˢ os) × fpc fs′ ≡ nsteps (wsz A) + suc q × Keep fs fs′ × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs) × heapMem (floc fs′) ≡ heapMem (floc fs)
      fin : StkW (heapMem (floc fs)) (slot fs) φ (minl {B = B} a ∷ˢ os) → Res
      fin ((_ , vinl {wa = wa} {pad} pa len , (e0 , s′)) , rest) = done-shift (shift-sim prog fs₄ φ {Es} {A} {S} {es} {os} {a} (suc t) wa sq h
                                         (c-env C) rest pa (proj₁ (slots-++ {slot fs} wa pad s′))
                                         (pay-up φ A B S A (Data.Nat.Properties.m≤m⊔n (wsz A) (wsz B)) (c-sfit C))
                                         (≤-trans (env-below φ (ws ((A ⊕t B) ∷ S)) (c-sfit C)) (Data.Nat.Properties.n≤1+n t))
                                         (c-efit C)
                                         (≤-trans (Data.Nat.Properties.+-monoˡ-≤ (ws S) (≤-trans (Data.Nat.Properties.m≤m⊔n (wsz A) (wsz B)) (Data.Nat.Properties.n≤1+n _))) (c-sfit C)))
        where
          branch : FlatMachine.flat-exec-instr {FS} (instr-ctrl (c-branch-tag-zero L₁)) prog fs₂ ≡ fs₃
          branch = trans (flat-tag-branch-yes prog fs₂ L₁ (cong tag-test e0)) (cong (λ m → do-jump m fs₂) fl)
          done-shift : Σ FlatState (λ fs′ → FlatSteps prog (nsteps (wsz A)) fs₄ fs′
                         × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ a ∷ˢ os) × fpc fs′ ≡ nsteps (wsz A) + fpc fs₄ × Keep fs₄ fs′ × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs₄) × heapMem (floc fs′) ≡ heapMem (floc fs₄)) → Res
          done-shift (fs′ , st , C′ , pc , K , nx , hp) =
            fs′ , step-at fs₁ (h , f₁) (lea-step fs t) (step-at fs₂ (h , f₂) (mov-in-step fs₁)
                    (step-at fs₃ (h , f₃) branch (step-at fs₄ (h , fq) (flat-label prog fs₃ L₁) st))) ,
            C′ , pc , keep-trans k₄ K , nx , hp

  -- ★ `case`, `inr`: the tag is 1, the branch falls through; the payload shifted up
  case₂-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es A B S} {es : Slots Es} {os : Stk S} {b : MV B} (L₁ : LabelId)
            → let t = budget φ ∸ ws ((A ⊕t B) ∷ S) ; bot = budget φ ∸ ws S in
              Seg prog (fpc fs) (lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero L₁) ∷ mvSSd (suc t) (bot ∸ wsz B) (wsz B))
            → fhalted (floc fs) ≡ false
            → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ minr {A = A} b ∷ˢ os)
            → Σ FlatState λ fs′ → FlatSteps prog (3 + nsteps (wsz B)) fs fs′
                × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ b ∷ˢ os) × fpc fs′ ≡ nsteps (wsz B) + (3 + fpc fs) × Keep fs fs′ × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs) × heapMem (floc fs′) ≡ heapMem (floc fs)
  case₂-sim prog fs φ {Es} {A} {B} {S} {es} {os} {b} L₁ (f₁ , f₂ , f₃ , sq) h C = fin (c-stk C)
    where
      t = budget φ ∸ ws ((A ⊕t B) ∷ S)
      cf = AllocState.current-frame (falloc fs)
      fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (SV-Ptr (AtStack cf t)) } ; fpc = suc (fpc fs) }
      fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 (SV-Ptr (AtStack cf t)) } ; fpc = suc (fpc fs₁) }
      fs₃ = record fs₂ { fpc = suc (fpc fs₂) }
      k₃ : Keep fs fs₃
      k₃ = keep-trans {fs₂ = fs₁} (keep-regs _ _) (keep-trans {fs₂ = fs₂} (keep-regs _ _) (keep-pc _))
      Res = Σ FlatState λ fs′ → FlatSteps prog (3 + nsteps (wsz B)) fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ b ∷ˢ os) × fpc fs′ ≡ nsteps (wsz B) + (3 + fpc fs) × Keep fs fs′ × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs) × heapMem (floc fs′) ≡ heapMem (floc fs)
      fin : StkW (heapMem (floc fs)) (slot fs) φ (minr {A = A} b ∷ˢ os) → Res
      fin ((_ , vinr {wb = wb} {pad} pb len , (e1 , s′)) , rest) = done-shift (shift-sim prog fs₃ φ {Es} {B} {S} {es} {os} {b} (suc t) wb sq h
                                         (c-env C) rest pb (proj₁ (slots-++ {slot fs} wb pad s′))
                                         (pay-up φ A B S B (Data.Nat.Properties.m≤n⊔m (wsz A) (wsz B)) (c-sfit C))
                                         (≤-trans (env-below φ (ws ((A ⊕t B) ∷ S)) (c-sfit C)) (Data.Nat.Properties.n≤1+n t))
                                         (c-efit C)
                                         (≤-trans (Data.Nat.Properties.+-monoˡ-≤ (ws S) (≤-trans (Data.Nat.Properties.m≤n⊔m (wsz A) (wsz B)) (Data.Nat.Properties.n≤1+n _))) (c-sfit C)))
        where
          done-shift : Σ FlatState (λ fs′ → FlatSteps prog (nsteps (wsz B)) fs₃ fs′
                         × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ b ∷ˢ os) × fpc fs′ ≡ nsteps (wsz B) + fpc fs₃ × Keep fs₃ fs′ × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs₃) × heapMem (floc fs′) ≡ heapMem (floc fs₃)) → Res
          done-shift (fs′ , st , C′ , pc , K , nx , hp) =
            fs′ , step-at fs₁ (h , f₁) (lea-step fs t) (step-at fs₂ (h , f₂) (mov-in-step fs₁)
                    (step-at fs₃ (h , f₃) (flat-tag-branch-not prog fs₂ L₁ (cong tag-test e1)) st)) ,
            C′ , pc , keep-trans k₃ K , nx , hp

  open import Once.LinCore.Machine fmt ans bw using (see; vw)
  open import Once.LinCore.Moves {FS} using (MovedS; m-pc; m-alloc; m-heap)
  open import Once.LinCore.MoveCode using (mvSS)

  private
    pay-in : ∀ e P E₁ E₂ → wsz P ≤ wsz E₁ ⊔ wsz E₂ → suc e + wsz P ≤ suc (wsz E₁ ⊔ wsz E₂) + e
    pay-in e P E₁ E₂ pM = s≤s (≤-trans (≤-reflexive (+-comm e (wsz P)))
                                       (Data.Nat.Properties.+-monoˡ-≤ e pM))

  -- ★ `ecase`, `inl`: the viewed tag is 0, the branch taken; the left payload a new view
  ecase₁-sim : ∀ prog (fs : FlatState) (φ : Frame) {E₁ E₂ Es S} {es : Slots ((E₁ ⊕t E₂) ∷ Es)} {os : Stk S} {e₁ : MV E₁}
                 (L₁ : LabelId) (q : ℕ)
             → see es ≡ minl e₁
             → Seg prog (fpc fs) (lea-slot (ws Es) ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero L₁) ∷ [])
             → find-label prog L₁ ≡ just q
             → Seg prog q (instr-ctrl (c-label L₁) ∷ mvSS (suc (ws Es)) (ws Es + wsz (E₁ ⊕t E₂)) (wsz E₁))
             → fhalted (floc fs) ≡ false
             → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ os)
             → ws (E₁ ∷ (E₁ ⊕t E₂) ∷ Es) ≤ EP φ
             → Σ FlatState λ fs′ → FlatSteps prog (4 + nsteps (wsz E₁)) fs fs′
                 × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw e₁ es ∥ os)
                 × fpc fs′ ≡ nsteps (wsz E₁) + suc q × Keep fs fs′ × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs) × heapMem (floc fs′) ≡ heapMem (floc fs)
  ecase₁-sim prog fs φ {E₁} {E₂} {Es} {S} {es} {os} {e₁} L₁ q eq (f₁ , f₂ , f₃ , _) fl (fq , sq) h C fit = fin (topW es (c-env C))
    where
      cf = AllocState.current-frame (falloc fs)
      fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (SV-Ptr (AtStack cf (ws Es))) } ; fpc = suc (fpc fs) }
      fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 (SV-Ptr (AtStack cf (ws Es))) } ; fpc = suc (fpc fs₁) }
      fs₃ = record fs₂ { fpc = q }
      fs₄ = record fs₃ { fpc = suc q }
      k₄ : Keep fs fs₄
      k₄ = keep-trans {fs₂ = fs₁} (keep-regs _ _) (keep-trans {fs₂ = fs₂} (keep-regs _ _) (keep-trans {fs₂ = fs₃} (keep-pc _) (keep-pc _)))
      Res = Σ FlatState λ fs′ → FlatSteps prog (4 + nsteps (wsz E₁)) fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw e₁ es ∥ os)
              × fpc fs′ ≡ nsteps (wsz E₁) + suc q × Keep fs fs′ × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs) × heapMem (floc fs′) ≡ heapMem (floc fs)
      fin : Σ (List W) (λ w → VW (heapMem (floc fs)) (see es) w × SlotsAt (slot fs) (ws Es) w) → Res
      fin (w , pw , sw) = inv (subst (λ z → VW (heapMem (floc fs)) z w) eq pw) sw
        where
          inv : VW (heapMem (floc fs)) (minl {B = E₂} e₁) w → SlotsAt (slot fs) (ws Es) w → Res
          inv (vinl {wa = wa} {pad} pa len) (e0 , s′) =
            done-view (view-sim prog fs₄ φ {E₁ ⊕t E₂} {E₁} {Es} {S} {es} {os} {e₁} (suc (ws Es)) wa pa
                         (proj₁ (slots-++ {slot fs} wa pad s′))
                         (pay-in (ws Es) E₁ E₁ E₂ (Data.Nat.Properties.m≤m⊔n (wsz E₁) (wsz E₂)))
                         sq h C fit)
            where
              branch : FlatMachine.flat-exec-instr {FS} (instr-ctrl (c-branch-tag-zero L₁)) prog fs₂ ≡ fs₃
              branch = trans (flat-tag-branch-yes prog fs₂ L₁ (cong tag-test e0)) (cong (λ m → do-jump m fs₂) fl)
              done-view : Σ FlatState (λ fs′ → FlatSteps prog (nsteps (wsz E₁)) fs₄ fs′
                            × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw e₁ es ∥ os)
                            × MovedS fs₄ fs′ (suc (ws Es)) (ws Es + wsz (E₁ ⊕t E₂)) (wsz E₁)) → Res
              done-view (fs′ , st , C′ , M) =
                fs′ , step-at fs₁ (h , f₁) (lea-step fs (ws Es)) (step-at fs₂ (h , f₂) (mov-in-step fs₁)
                        (step-at fs₃ (h , f₃) branch (step-at fs₄ (h , fq) (flat-label prog fs₃ L₁) st))) ,
                C′ , m-pc M , keep-trans k₄ (keepS M) , cong AllocState.next-heap-ref (m-alloc M) , m-heap M

  -- ★ `ecase`, `inr`: the viewed tag is 1, the branch falls through; the right payload a new view
  ecase₂-sim : ∀ prog (fs : FlatState) (φ : Frame) {E₁ E₂ Es S} {es : Slots ((E₁ ⊕t E₂) ∷ Es)} {os : Stk S} {e₂ : MV E₂}
                 (L₁ : LabelId)
             → see es ≡ minr e₂
             → Seg prog (fpc fs) (lea-slot (ws Es) ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero L₁)
                                  ∷ mvSS (suc (ws Es)) (ws Es + wsz (E₁ ⊕t E₂)) (wsz E₂))
             → fhalted (floc fs) ≡ false
             → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ os)
             → ws (E₂ ∷ (E₁ ⊕t E₂) ∷ Es) ≤ EP φ
             → Σ FlatState λ fs′ → FlatSteps prog (3 + nsteps (wsz E₂)) fs fs′
                 × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw e₂ es ∥ os)
                 × fpc fs′ ≡ nsteps (wsz E₂) + (3 + fpc fs) × Keep fs fs′ × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs) × heapMem (floc fs′) ≡ heapMem (floc fs)
  ecase₂-sim prog fs φ {E₁} {E₂} {Es} {S} {es} {os} {e₂} L₁ eq (f₁ , f₂ , f₃ , sq) h C fit = fin (topW es (c-env C))
    where
      cf = AllocState.current-frame (falloc fs)
      fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (SV-Ptr (AtStack cf (ws Es))) } ; fpc = suc (fpc fs) }
      fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 (SV-Ptr (AtStack cf (ws Es))) } ; fpc = suc (fpc fs₁) }
      fs₃ = record fs₂ { fpc = suc (fpc fs₂) }
      k₃ : Keep fs fs₃
      k₃ = keep-trans {fs₂ = fs₁} (keep-regs _ _) (keep-trans {fs₂ = fs₂} (keep-regs _ _) (keep-pc _))
      Res = Σ FlatState λ fs′ → FlatSteps prog (3 + nsteps (wsz E₂)) fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw e₂ es ∥ os) × fpc fs′ ≡ nsteps (wsz E₂) + (3 + fpc fs) × Keep fs fs′ × AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs) × heapMem (floc fs′) ≡ heapMem (floc fs)
      fin : Σ (List W) (λ w → VW (heapMem (floc fs)) (see es) w × SlotsAt (slot fs) (ws Es) w) → Res
      fin (w , pw , sw) = inv (subst (λ z → VW (heapMem (floc fs)) z w) eq pw) sw
        where
          inv : VW (heapMem (floc fs)) (minr {A = E₁} e₂) w → SlotsAt (slot fs) (ws Es) w → Res
          inv (vinr {wb = wb} {pad} pb len) (e1 , s′) =
            done-view (view-sim prog fs₃ φ {E₁ ⊕t E₂} {E₂} {Es} {S} {es} {os} {e₂} (suc (ws Es)) wb pb
                         (proj₁ (slots-++ {slot fs} wb pad s′))
                         (pay-in (ws Es) E₂ E₁ E₂ (Data.Nat.Properties.m≤n⊔m (wsz E₁) (wsz E₂)))
                         sq h C fit)
            where
              done-view : Σ FlatState (λ fs′ → FlatSteps prog (nsteps (wsz E₂)) fs₃ fs′
                            × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw e₂ es ∥ os)
                            × MovedS fs₃ fs′ (suc (ws Es)) (ws Es + wsz (E₁ ⊕t E₂)) (wsz E₂)) → Res
              done-view (fs′ , st , C′ , M) =
                fs′ , step-at fs₁ (h , f₁) (lea-step fs (ws Es)) (step-at fs₂ (h , f₂) (mov-in-step fs₁)
                        (step-at fs₃ (h , f₃) (flat-tag-branch-not prog fs₂ L₁ (cong tag-test e1)) st)) ,
                C′ , m-pc M , keep-trans k₃ (keepS M) , cong AllocState.next-heap-ref (m-alloc M) , m-heap M

  ----------------------------------------------------------------------
  -- ★ `lconst`: a base word onto the stack, in place of a unit. The loader
  -- (`Lower`'s parameter `ldConst`) is given by what it does: `Output` its word.
  ----------------------------------------------------------------------

  open import Once.CCC.Machine.SMCore using (AbstractInstr; store-at-slot)
  open import Once.LinCore.Moves {FS} using (store-step; store-same; store-other)
  open import Once.LinCore.Events fmt ans bw using (mone; mbase)

  lconst-sim : ∀ prog (fs : FlatState) (φ : Frame) {b Es S} {es : Slots Es} {os : Stk S} (v : ⟦ b ⟧b) (ld : AbstractInstr)
             → FlatMachine.flat-exec-instr {FS} ld prog fs
               ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = suc (fpc fs) }
             → Seg prog (fpc fs) (ld ∷ store-at-slot ((budget φ ∸ ws S) ∸ 1) ∷ [])
             → fhalted (floc fs) ≡ false
             → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ mone ∷ˢ os)
             → ws (Bt b ∷ S) ≤ OP φ
             → Σ FlatState λ fs′ → FlatSteps prog 2 fs fs′ × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ mbase v ∷ˢ os) × Ran 2 0 (AllocState.next-heap-ref (falloc fs)) fs fs′
  lconst-sim prog fs φ {b} {Es} {S} {es} {os} v ld eld (f₁ , f₂ , _) h C fit =
    fs₂ ,
    step-at fs₁ (h , f₁) eld (step-at fs₂ (h , f₂) (store-step fs₁ dst) done) ,
    record { c-env  = envW-frame es (λ x x< → store-other (floc fs₁) cf dst (wordOf v) x
                                     (λ e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans x< env≤))) (c-env C)
           ; c-stk  = ( wordOf v ∷ [] , vbase
                      , (trans (cong (slot fs₂) (sym (new-top (budget φ) 1 (ws S)))) (store-same (floc fs₁) cf dst (wordOf v)) , tt) )
                    , stkW-frame os fitS (λ x lo _ → store-other (floc fs₁) cf dst (wordOf v) x
                                             (λ e → Data.Nat.Properties.<-irrefl e (<-≤-trans b1<b lo))) (proj₂ (c-stk C))
           ; c-efit = c-efit C ; c-sfit = fit }
    , ran-trans (ran-regs _) (ran-store fs₁ dst _)
    where
      cf = AllocState.current-frame (falloc fs)
      bot = budget φ ∸ ws S
      dst = bot ∸ 1
      fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = suc (fpc fs) }
      fs₂ = record fs₁ { floc = MemOps.writeLoc {FS} (floc fs₁) (AtStack cf dst) (wordOf v) ; fpc = suc (fpc fs₁) }
      fitB : 1 + ws S ≤ budget φ
      fitB = ≤-trans fit (m≤n+m (OP φ) (EP φ))
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) 1) fitB
      env≤ : ws Es ≤ dst
      env≤ = ≤-trans (c-efit C) (subst (EP φ ≤_) (sym (new-top (budget φ) 1 (ws S))) (env-below φ (1 + ws S) fit))
      b1<b : dst < bot
      b1<b = Data.Nat.Properties.∸-monoʳ-< {o = 0} (s≤s z≤n) (≤∸ 1 (ws S) (budget φ) fitB)
