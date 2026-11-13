-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimF — plan 0.146 B1.4b, `LowerSim` layer (4),
-- continued: A BLOCK'S PROLOGUE. After the call's way in (`call-in`,
-- `call-in-v`), `Input1` is the caller's argument area; the prologue copies
-- the argument's words to the top of the callee's operand region, and a
-- block that reads the caller's top view copies its words to the bottom of
-- the environment region (`view-in`). Then the callee's configuration — its
-- view, the argument — is in its frame.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-trans; <-≤-trans; ≤-reflexive; m≤m+n; m≤n+m)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.LowerSimF
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV)
open import Once.LinCore.Machine fmt ans bw using (Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; _∥_)
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw
open import Once.LinCore.MoveCode using (mvPS)
import Once.LinCore.Moves

module SimF {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc; fret)
  open FlatStepsAPI {FS} using (FlatSteps; step-at; FlatSteps-++)
  open import Once.LinCore.Moves {FS}
    using (Seg; Seg-++ˡ; Seg-++ʳ; slot; mvPS-run; MovedP; p-moved; p-rest; p-heap; p-halt; p-pc; restore-step; Ran; ranP; ran-trans; ran-regs)

  private
    frame-eq : ∀ {f g x y} → AtStack {FS} f x ≡ AtStack g y → f ≡ g
    frame-eq refl = refl

  -- words read through a pointer into another frame, at the destination
  slots-movedP : ∀ {fs fs′ cf area o b} (w : List W)
               → MovedP fs fs′ (AtStack cf area) o b (length w)
               → SlotsAt (LocState.stackMem (floc fs) cf) (o + area) w → SlotsAt (slot fs′) b w
  slots-movedP {fs} {fs′} {cf} {area} {o} {b} w M s = go w 0 s (λ k k< → p-moved M k k<)
    where
      go : ∀ (v : List W) j → SlotsAt (LocState.stackMem (floc fs) cf) (j + (o + area)) v
         → (∀ k → k < j + length v → slot fs′ (k + b) ≡ LocState.stackMem (floc fs) cf ((k + o) + area))
         → SlotsAt (slot fs′) (j + b) v
      go []      j s h = tt
      go (x ∷ v) j (e , s) h =
        trans (h j (subst (j <_) (sym (+-suc j (length v))) (Data.Nat.s≤s (m≤m+n j (length v)))))
              (trans (cong (LocState.stackMem (floc fs) cf) (+-assoc j o area)) e) ,
        go v (suc j) s (λ k k< → h k (subst (k <_) (sym (+-suc j (length v))) k<))

  private
    -- words defined, read through the pointer
    def-at : ∀ {fs cf area o} (w : List W) → SlotsAt (LocState.stackMem (floc fs) cf) (o + area) w
           → ∀ k → k < length w → Σ W λ v → MemOps.readLoc {FS} (floc fs) (offsetLoc (AtStack cf area) (k + o)) ≡ just v
    def-at {fs} {cf} {area} {o} w s k k< with slots-def {LocState.stackMem (floc fs) cf} {o + area} w s k k<
    ... | (v , e) = v , trans (cong (LocState.stackMem (floc fs) cf) (+-assoc k o area)) e

  ----------------------------------------------------------------------
  -- ★ THE ARGUMENT IN: its words from the caller's area to the top of the
  -- callee's operand region.
  ----------------------------------------------------------------------

  arg-in : ∀ prog (fs : FlatState) (φ′ : Frame) (cf : FrameSemantics.Frame FS) (area o : ℕ) {A} {a : MV A} (wa : List W)
         → ¬ AllocState.current-frame (falloc fs) ≡ cf
         → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr (AtStack cf area)
         → VW (LocState.heapMem (floc fs)) a wa → SlotsAt (LocState.stackMem (floc fs) cf) (o + area) wa
         → Seg prog (fpc fs) (mvPS o (budget φ′ ∸ ws (A ∷ [])) (wsz A))
         → LocState.halted (floc fs) ≡ false
         → Σ FlatState λ fs′ → FlatSteps prog (Once.LinCore.Moves.ln {FS} (wsz A)) fs fs′
             × VW (LocState.heapMem (floc fs′)) a wa × SlotsAt (slot fs′) (budget φ′ ∸ ws (A ∷ [])) wa
             × MovedP fs fs′ (AtStack cf area) o (budget φ′ ∸ ws (A ∷ [])) (wsz A)
  arg-in prog fs φ′ cf area o {A} {a} wa ne inp pa sa seg h
    with mvPS-run prog fs (AtStack cf area) o (budget φ′ ∸ ws (A ∷ [])) (wsz A) seg h inp
           (λ k k< → def-at {fs} {cf} {area} {o} wa sa k (subst (k <_) (sym (vw-len pa)) k<))
           (λ k k′ _ _ e → ne (frame-eq e))
  ... | (fs′ , st , M) =
    fs′ , st , subst (λ r → VW r a wa) (sym (p-heap M)) pa ,
    slots-movedP wa (subst (MovedP fs fs′ (AtStack cf area) o (budget φ′ ∸ ws (A ∷ []))) (sym (vw-len pa)) M) sa , M

  ----------------------------------------------------------------------
  -- ★ THE CALLEE'S CONFIGURATION: the argument alone, or the caller's top
  -- view beside it. The slots from the region's top up (the save slots) as
  -- they were.
  ----------------------------------------------------------------------

  private
    -- a word moved below the region's top is not at or above it
    under-top : ∀ B n k x → n ≤ B → k < n → B ≤ x → ¬ x ≡ k + (B ∸ n)
    under-top B n k x le k< B≤x e =
      Data.Nat.Properties.<-irrefl (sym e)
        (<-≤-trans (Data.Nat.Properties.+-monoˡ-< (B ∸ n) k<)
          (≤-trans (≤-reflexive (Data.Nat.Properties.m+[n∸m]≡n le)) B≤x))
      where import Data.Nat.Properties

    lt0 : ∀ {k n} → k < n → k < n + 0
    lt0 {k} {n} k< = subst (k <_) (sym (Data.Nat.Properties.+-identityʳ n)) k<
      where import Data.Nat.Properties

  enter-n : ∀ prog (fs : FlatState) (φ′ : Frame) (cf : FrameSemantics.Frame FS) (area o : ℕ) {A} {a : MV A} (wa : List W)
          → ¬ AllocState.current-frame (falloc fs) ≡ cf
          → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr (AtStack cf area)
          → VW (LocState.heapMem (floc fs)) a wa → SlotsAt (LocState.stackMem (floc fs) cf) (o + area) wa
          → Seg prog (fpc fs) (mvPS o (budget φ′ ∸ ws (A ∷ [])) (wsz A))
          → LocState.halted (floc fs) ≡ false
          → ws (A ∷ []) ≤ OP φ′
          → Σ FlatState λ fs′ → FlatSteps prog (Once.LinCore.Moves.ln {FS} (wsz A)) fs fs′
              × CfgW (LocState.heapMem (floc fs′)) (slot fs′) φ′ ([]ᵉ ∥ a ∷ˢ []ˢ)
              × Ran (Once.LinCore.Moves.ln {FS} (wsz A)) 0 (AllocState.next-heap-ref (falloc fs)) fs fs′
              × (∀ x → budget φ′ ≤ x → slot fs′ x ≡ slot fs x)
  enter-n prog fs φ′ cf area o {A} {a} wa ne inp pa sa seg h fit
    with arg-in prog fs φ′ cf area o wa ne inp pa sa seg h
  ... | (fs′ , st , pa′ , sa′ , M) =
    fs′ , st ,
    record { c-env = tt ; c-stk = ((wa , pa′ , sa′) , tt) ; c-efit = z≤n ; c-sfit = fit } ,
    ranP M ,
    (λ x B≤x → p-rest M x (λ k k< → under-top (budget φ′) (ws (A ∷ [])) k x (≤-trans fit (m≤n+m (OP φ′) (EP φ′))) (lt0 k<) B≤x))

  enter-j : ∀ prog (fs : FlatState) (φ′ : Frame) (cf : FrameSemantics.Frame FS) (area o v sv : ℕ) {E A} {e : MV E} {a : MV A}
              (we wa : List W)
          → ¬ AllocState.current-frame (falloc fs) ≡ cf
          → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr (AtStack cf area)
          → slot fs sv ≡ just (SV-Ptr (AtStack cf v)) → budget φ′ ≤ sv
          → VW (LocState.heapMem (floc fs)) a wa → SlotsAt (LocState.stackMem (floc fs) cf) (o + area) wa
          → VW (LocState.heapMem (floc fs)) e we → SlotsAt (LocState.stackMem (floc fs) cf) v we
          → Seg prog (fpc fs) (mvPS o (budget φ′ ∸ ws (A ∷ [])) (wsz A) ++ restore-input sv ∷ mvPS 0 0 (wsz E))
          → LocState.halted (floc fs) ≡ false
          → ws (E ∷ []) ≤ EP φ′ → ws (A ∷ []) ≤ OP φ′
          → Σ FlatState λ fs′ → FlatSteps prog (Once.LinCore.Moves.ln {FS} (wsz A) + suc (Once.LinCore.Moves.ln {FS} (wsz E))) fs fs′
              × CfgW (LocState.heapMem (floc fs′)) (slot fs′) φ′ (vw e []ᵉ ∥ a ∷ˢ []ˢ)
              × Ran (Once.LinCore.Moves.ln {FS} (wsz A) + suc (Once.LinCore.Moves.ln {FS} (wsz E))) 0 (AllocState.next-heap-ref (falloc fs)) fs fs′
              × (∀ x → budget φ′ ≤ x → slot fs′ x ≡ slot fs x)
  enter-j prog fs φ′ cf area o v sv {E} {A} {e} {a} we wa ne inp ev sv≥ pa sa pe se seg h fitE fitA
    with arg-in prog fs φ′ cf area o wa ne inp pa sa (Seg-++ˡ prog (fpc fs) (mvPS o dst (wsz A)) _ seg) h
    where dst = budget φ′ ∸ ws (A ∷ [])
  ... | (fs₁ , st₁ , pa₁ , sa₁ , M₁) = fin (mvPS-run prog fs₂ (AtStack cf v) 0 0 (wsz E) seg₃ h₁ refl def₃ (λ k k′ _ _ e′ → ne₁ (frame-eq e′)))
    where
      import Data.Nat.Properties
      dst = budget φ′ ∸ ws (A ∷ [])
      B≤ : ws (A ∷ []) ≤ budget φ′
      B≤ = ≤-trans fitA (m≤n+m (OP φ′) (EP φ′))
      top₁ : ∀ x → budget φ′ ≤ x → slot fs₁ x ≡ slot fs x
      top₁ x B≤x = p-rest M₁ x (λ k k< → under-top (budget φ′) (ws (A ∷ [])) k x B≤ (lt0 k<) B≤x)
      h₁ : LocState.halted (floc fs₁) ≡ false
      h₁ = trans (p-halt M₁) h
      fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 (SV-Ptr (AtStack cf v)) } ; fpc = suc (fpc fs₁) }
      rest₁ : Seg prog (fpc fs₁) (restore-input sv ∷ mvPS 0 0 (wsz E))
      rest₁ = subst (λ z → Seg prog z (restore-input sv ∷ mvPS 0 0 (wsz E)))
                (trans (cong (fpc fs +_) (len-mvPS o dst (wsz A))) (trans (Data.Nat.Properties.+-comm (fpc fs) _) (sym (p-pc M₁))))
                (Seg-++ʳ prog (fpc fs) (mvPS o dst (wsz A)) _ seg)
      seg₃ : Seg prog (fpc fs₂) (mvPS 0 0 (wsz E))
      seg₃ = proj₂ rest₁
      ne₁ : ¬ AllocState.current-frame (falloc fs₂) ≡ cf
      ne₁ = λ e′ → ne (trans (sym (cong AllocState.current-frame (Once.LinCore.Moves.p-alloc M₁))) e′)
      -- the caller's frame, as it was
      cfr : ∀ x → LocState.stackMem (floc fs₂) cf x ≡ LocState.stackMem (floc fs) cf x
      cfr x = Once.LinCore.Moves.p-frame M₁ cf x (λ e′ → ne (sym e′))
      se₂ : SlotsAt (LocState.stackMem (floc fs₂) cf) (0 + v) we
      se₂ = slots-frame {LocState.stackMem (floc fs) cf} {LocState.stackMem (floc fs₂) cf} we (λ k _ → cfr (k + v)) se
      def₃ : ∀ k → k < wsz E → Σ W λ x → MemOps.readLoc {FS} (floc fs₂) (offsetLoc (AtStack cf v) (k + 0)) ≡ just x
      def₃ k k< = def-at {fs₂} {cf} {v} {0} we se₂ k (subst (k <_) (sym (vw-len pe)) k<)
      fin : Σ FlatState (λ fs₃ → FlatSteps prog (Once.LinCore.Moves.ln {FS} (wsz E)) fs₂ fs₃ × MovedP fs₂ fs₃ (AtStack cf v) 0 0 (wsz E)) → _
      fin (fs₃ , st₃ , M₃) =
        fs₃ ,
        FlatSteps-++ st₁ (step-at fs₂ (h₁ , proj₁ rest₁) (restore-step fs₁ sv (trans (top₁ sv sv≥) ev)) st₃) ,
        record { c-env = ((we , subst (λ r → VW r e we) (sym hp) pe
                         , slots-movedP we (subst (MovedP fs₂ fs₃ (AtStack cf v) 0 0) (sym (vw-len pe)) M₃) se₂) , tt)
               ; c-stk = ((wa , subst (λ r → VW r a wa) (sym (p-heap M₃)) pa₁
                         , slots-frame {slot fs₁} {slot fs₃} wa (λ k k< → p-rest M₃ (k + dst) (λ k′ k′< e′ → past-env k k′ k′< e′)) sa₁) , tt)
               ; c-efit = fitE ; c-sfit = fitA } ,
        ran-trans (ranP M₁) (ran-trans (ran-regs _) (ranP M₃)) ,
        (λ x B≤x → trans (p-rest M₃ x (λ k′ k′< e′ → Data.Nat.Properties.<-irrefl (sym e′) (<-≤-trans (lt-env k′ k′<) (≤-trans dst≤B B≤x))))
                         (top₁ x B≤x))
        where
          hp : LocState.heapMem (floc fs₃) ≡ LocState.heapMem (floc fs)
          hp = trans (p-heap M₃) (p-heap M₁)
          wE≤dst : wsz E ≤ dst
          wE≤dst = ≤-trans (≤-trans (≤-reflexive (sym (Data.Nat.Properties.+-identityʳ (wsz E)))) fitE) (env-below φ′ (ws (A ∷ [])) fitA)
          dst≤B : dst ≤ budget φ′
          dst≤B = Data.Nat.Properties.m∸n≤m (budget φ′) (ws (A ∷ []))
          lt-env : ∀ k′ → k′ < wsz E → k′ + 0 < dst
          lt-env k′ k′< = <-≤-trans (subst (_< wsz E) (sym (Data.Nat.Properties.+-identityʳ k′)) k′<) wE≤dst
          past-env : ∀ k k′ → k′ < wsz E → ¬ k + dst ≡ k′ + 0
          past-env k k′ k′< e′ = Data.Nat.Properties.<-irrefl (sym e′) (<-≤-trans (lt-env k′ k′<) (m≤n+m dst k))

  ----------------------------------------------------------------------
  -- ★ THE WAY OUT: the result's words into the caller's area, the return;
  -- the caller's configuration, with the result on top, in its frame.
  ----------------------------------------------------------------------

  open import Once.LinCore.LowerSimE {FS} using (CallOut; call-out; co-frame; co-moved; co-rest; co-halt)
  open import Once.LinCore.MoveCode using (mvSP)

  -- words copied, slot by slot
  slots-copied : ∀ {sm sm′ : ℕ → Maybe W} {src d} (w : List W)
               → (∀ k → k < length w → sm′ (k + d) ≡ sm (k + src)) → SlotsAt sm src w → SlotsAt sm′ d w
  slots-copied {sm} {sm′} {src} {d} w h s = go w 0 s (λ k k< → h k k<)
    where
      go : ∀ (v : List W) j → SlotsAt sm (j + src) v → (∀ k → k < j + length v → sm′ (k + d) ≡ sm (k + src)) → SlotsAt sm′ (j + d) v
      go []      j s h′ = tt
      go (x ∷ v) j (e , s) h′ =
        trans (h′ j (subst (j <_) (sym (+-suc j (length v))) (Data.Nat.s≤s (m≤m+n j (length v))))) e ,
        go v (suc j) s (λ k k< → h′ k (subst (k <_) (sym (+-suc j (length v))) k<))

  -- a value of `M` words' room below the stack's rest: where a part of it starts
  area-gen : ∀ Bg wX M s → wX ≤ M → M + s ≤ Bg → (M ∸ wX) + ((Bg ∸ s) ∸ M) ≡ Bg ∸ (wX + s)
  area-gen Bg wX M s le fit =
    trans (+-comm (M ∸ wX) _)
      (trans (sym (Data.Nat.Properties.+-∸-assoc ((Bg ∸ s) ∸ M) le))
        (trans (cong (_∸ wX) (Data.Nat.Properties.m∸n+n≡m M≤))
          (trans (Data.Nat.Properties.∸-+-assoc Bg s wX) (cong (Bg ∸_) (+-comm s wX)))))
    where
      import Data.Nat.Properties
      M≤ : M ≤ Bg ∸ s
      M≤ = ≤∸ M s Bg fit

  private
    slot-eq : ∀ {f g x y} → AtStack {FS} f x ≡ AtStack g y → x ≡ y
    slot-eq refl = refl

  leave : ∀ prog (fs : FlatState) (φ φ′ : Frame) (cfc : FrameSemantics.Frame FS) (area M bb pc : ℕ) (rest : List ℕ)
            (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ) {Es B S} {es : Slots Es} {os : Stk S} {b : MV B} (wb : List W)
        → fret fs ≡ pc ∷ rest → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
        → ¬ cfc ≡ AllocState.current-frame (falloc fs)
        → slot fs (budget φ′) ≡ just (SV-Ptr (AtStack cfc area))
        → VW (LocState.heapMem (floc fs)) b wb → SlotsAt (slot fs) (budget φ′ ∸ ws (B ∷ [])) wb
        → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
        → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) φ os
        → area ≡ (budget φ ∸ ws S) ∸ M → wsz B ≤ M → M + ws S ≤ OP φ → ws Es ≤ EP φ → ws (B ∷ S) ≤ OP φ
        → Seg prog (fpc fs) (restore-input (budget φ′) ∷ mvSP (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B) ++ instr-ctrl (c-ret bb) ∷ [])
        → LocState.halted (floc fs) ≡ false
        → Σ FlatState λ fs′ → FlatSteps prog (suc (Once.LinCore.Moves.ln {FS} (wsz B) + 1)) fs fs′
            × CfgW (LocState.heapMem (floc fs′)) (slot fs′) φ (es ∥ b ∷ˢ os)
            × CallOut fs fs′ cfc area (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B) pc rest sv sl
  leave prog fs φ φ′ cfc area M bb pc rest sv sl {Es} {B} {S} {es} {os} {b} wb hret hsv ne ep pb sb ev st refl le fitM fitE fitB seg h
    with call-out prog fs cfc area (budget φ′) (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B) bb pc rest sv sl hret hsv ne ep
           (λ k k< → slots-def wb sb k (subst (k <_) (sym (vw-len pb)) k<)) seg h
  ... | (fs′ , st′ , CO) =
    fs′ , st′ ,
    subst (λ g → CfgW (LocState.heapMem (floc fs′)) (LocState.stackMem (floc fs′) g) φ (es ∥ b ∷ˢ os)) (sym (co-frame CO))
      (record { c-env  = envW-heap es (λ i k _ → hp (cellLoc i k)) (envW-frame es (λ x x< → kept x (inj₁ x<)) ev)
              ; c-stk  = ( wb , vw-frame pb (λ i k _ → hp (cellLoc i k))
                         , subst (λ z → SlotsAt (LocState.stackMem (floc fs′) cfc) z wb)
                             (area-gen (budget φ) (wsz B) M (ws S) le (≤-trans fitM (m≤n+m (OP φ) (EP φ))))
                             (slots-copied wb (λ k k< → trans (cong (LocState.stackMem (floc fs′) cfc) (sym (+-assoc k (M ∸ wsz B) area)))
                                                            (co-moved CO k (subst (k <_) (vw-len pb) k<))) sb) )
                       , stkW-heap os (λ i k _ → hp (cellLoc i k))
                           (stkW-frame os fitS (λ x lo _ → kept x (inj₂ lo)) st)
              ; c-efit = fitE ; c-sfit = fitB }) ,
    CO
    where
      import Data.Nat.Properties
      open import Data.Sum using (_⊎_; inj₁; inj₂)
      bot = budget φ ∸ ws S
      hp : ∀ hl → LocState.heapMem (floc fs′) hl ≡ LocState.heapMem (floc fs) hl
      hp hl = co-rest CO (AtDynamic hl) (λ k k< ())
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) M) (≤-trans fitM (m≤n+m (OP φ) (EP φ)))
      -- the area lies above the environment and below the rest of the stack
      area≥ : ws Es ≤ (budget φ ∸ ws S) ∸ M
      area≥ = ≤-trans fitE (≤-trans (env-below φ (M + ws S) fitM)
                (≤-reflexive (trans (cong (budget φ ∸_) (+-comm M (ws S))) (sym (Data.Nat.Properties.∸-+-assoc (budget φ) (ws S) M)))))
      area-top : ((budget φ ∸ ws S) ∸ M) + M ≡ bot
      area-top = Data.Nat.Properties.m∸n+n≡m (≤∸ M (ws S) (budget φ) (≤-trans fitM (m≤n+m (OP φ) (EP φ))))
      moved< : ∀ k → k < wsz B → (k + (M ∸ wsz B)) + ((budget φ ∸ ws S) ∸ M) < bot
      moved< k k< = <-≤-trans (Data.Nat.Properties.+-monoˡ-< _ (<-≤-trans (Data.Nat.Properties.+-monoˡ-< (M ∸ wsz B) k<)
                                (≤-reflexive (Data.Nat.Properties.m+[n∸m]≡n le))))
                      (≤-reflexive (trans (+-comm M _) area-top))
      kept : ∀ x → (x < ws Es) ⊎ (bot ≤ x) → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x
      kept x side = co-rest CO (AtStack cfc x) (λ k k< e′ → off-area k k< (slot-eq e′) side)
        where
          off-area : ∀ k → k < wsz B → x ≡ (k + (M ∸ wsz B)) + ((budget φ ∸ ws S) ∸ M) → (x < ws Es) ⊎ (bot ≤ x) → ⊥
          off-area k k< e (inj₁ x<) = Data.Nat.Properties.<-irrefl e
                                     (<-≤-trans x< (≤-trans area≥ (m≤n+m _ (k + (M ∸ wsz B)))))
          off-area k k< e (inj₂ ge) = Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans (moved< k k<) ge)
