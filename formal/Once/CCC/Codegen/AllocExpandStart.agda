-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandStart — the start's set-up, and the first relation (D468, 3c3b).
--
-- After `c-start` the expansion saves Output and Input1 in the record's
-- scratch words, bumps the sentinel (the expanded run's first block), points
-- every head at it, writes its word (the tag 0) and puts the registers back.
-- The primitive's state after `c-start` and the expanded one after the set-up
-- are related: nothing is live, so the renaming is the identity and the lists
-- are empty.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandStart {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
import Data.Nat.Properties
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState; fetch; fetch-++-left; fetch-++-right)
open FlatState
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps; FlatSteps-++)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandRen {FS} using (ref-of; rec-loc; blk)
open import Once.CCC.Codegen.AllocExpandRun {FS}
open import Once.CCC.Codegen.AllocExpandFree {FS} using (hw-same; hw-other)
open MemOps {FS} using (writeLocToHeap)

module SetupRun (C : Classes) (prog : AbstractTrace) (x : FlatState)
                (fe : ∀ j i → fetch (setup C) j ≡ just i → fetch prog (j + fpc x) ≡ just i)
                (hx : LocState.halted (floc x) ≡ false) (nx : AllocState.next-heap-ref (falloc x) ≡ 1)
                (fr1 : AllocState.freed (falloc x) 1 ≡ false) where

  O = readReg (LocState.regs (floc x)) Output
  I = readReg (LocState.regs (floc x)) Input1

  y₁ = record x  { floc = writeLocToHeap (floc x) (rec-loc w-s1) O ; fpc = suc (fpc x) }
  y₂ = record y₁ { floc = record (floc y₁) { regs = writeReg (LocState.regs (floc y₁)) Output I } ; fpc = suc (fpc y₁) }
  y₃ = record y₂ { floc = writeLocToHeap (floc y₂) (rec-loc w-s2) I ; fpc = suc (fpc y₂) }
  y₄ = record y₃ { floc = record (floc y₃) { regs = writeReg (LocState.regs (floc y₃)) Output (blk (AllocState.next-heap-ref (falloc y₃))) }
                 ; falloc = record (falloc y₃) { next-heap-ref = suc (AllocState.next-heap-ref (falloc y₃))
                                               ; block-size = size-with 1 (AllocState.next-heap-ref (falloc y₃)) (AllocState.block-size (falloc y₃)) }
                 ; fpc = suc (fpc y₃) }

  run₄ : FlatSteps prog 4 x y₄
  run₄ = FlatSteps-++ (run-store-rec prog x w-s1 0 nx hx (fe 0 (store-rec w-s1) refl))
        (FlatSteps-++ (run-mov-out prog y₁ hx (fe 1 mov-to-output refl))
        (FlatSteps-++ (run-store-rec prog y₂ w-s2 0 nx hx (fe 2 (store-rec w-s2) refl))
                      (run-alloc prog y₃ 1 hx (fe 3 (instr-alloc-heap 1) refl))))

  -- the heads, from the sentinel's pointer in Output
  nx₄ : AllocState.next-heap-ref (falloc y₄) ≡ suc 1
  nx₄ = cong suc nx

  rest = mov-to-input ∷ instr-load-tag-lit 0 ∷ store-at 0 ∷ load-rec w-s2 ∷ mov-to-input ∷ load-rec w-s1 ∷ []

  fe-heads : ∀ j i → fetch (heads C (count C)) j ≡ just i → fetch prog (j + fpc y₄) ≡ just i
  fe-heads j i e = subst (λ z → fetch prog z ≡ just i)
                     (trans (cong (_+ fpc x) (Data.Nat.Properties.+-comm 4 j)) (Data.Nat.Properties.+-assoc j 4 (fpc x)))
                     (fe (4 + j) i (fetch-++-left (heads C (count C)) rest j i e))

  HR = heads-run C prog y₄ (count C) 1 nx₄ hx fe-heads
  z  = proj₁ HR
  stH = proj₁ (proj₂ HR)
  H  = proj₂ (proj₂ HR)
  open HeadsOut

  heads-len : ∀ c → length (heads C c) ≡ c
  heads-len zero    = refl
  heads-len (suc c) = cong suc (heads-len c)

  -- the fetches past the heads
  fe-rest : ∀ j i → fetch rest j ≡ just i → fetch prog (j + fpc z) ≡ just i
  fe-rest j i e =
    subst (λ q → fetch prog q ≡ just i)
          (trans (cong (λ t → (4 + (t + j)) + fpc x) (heads-len (count C)))
                 (trans (shuffle (count C) j (fpc x)) (cong (j +_) (sym (h-pc H)))))
          (fe (4 + (length (heads C (count C)) + j)) i (trans (fetch-++-right (heads C (count C)) rest j) e))
    where
      shuffle : ∀ c j′ x′ → (4 + (c + j′)) + x′ ≡ j′ + (c + (4 + x′))
      shuffle = solve-∀

  hz : LocState.halted (floc z) ≡ false
  hz = trans (proj₁ (h-flags H)) hx
  nz : AllocState.next-heap-ref (falloc z) ≡ suc 1
  nz = trans (cong AllocState.next-heap-ref (h-alloc H)) nx₄
  out-z : readReg (LocState.regs (floc z)) Output ≡ blk 1
  out-z = trans (cong (λ rs → readReg rs Output) (h-regs H)) (cong blk nx)

  z₁ = record z  { floc = record (floc z) { regs = writeReg (LocState.regs (floc z)) Input1 (readReg (LocState.regs (floc z)) Output) } ; fpc = suc (fpc z) }
  z₂ = record z₁ { floc = record (floc z₁) { regs = writeReg (LocState.regs (floc z₁)) Output (SV-Tag 0) } ; fpc = suc (fpc z₁) }
  z₃ = record z₂ { floc = writeLocToHeap (floc z₂) (heap-loc (mkHeapRef 1) 0) (SV-Tag 0) ; fpc = suc (fpc z₂) }
  z₄ = record z₃ { floc = record (floc z₃) { regs = writeReg (LocState.regs (floc z₃)) Output I } ; fpc = suc (fpc z₃) }
  z₅ = record z₄ { floc = record (floc z₄) { regs = writeReg (LocState.regs (floc z₄)) Input1 I } ; fpc = suc (fpc z₄) }
  z₆ = record z₅ { floc = record (floc z₅) { regs = writeReg (LocState.regs (floc z₅)) Output O } ; fpc = suc (fpc z₅) }

  private
    head≢ : ∀ k → k < 3 → ∀ c′ → ¬ rec-loc k ≡ rec-loc (head-word c′)
    head≢ k lt c′ e = Data.Nat.Properties.<-irrefl (cong HeapLocation.heap-offset e)
                        (Data.Nat.Properties.<-≤-trans lt (Data.Nat.Properties.m≤m+n 3 c′))
    blk1≢rec : ∀ k → ¬ heap-loc (mkHeapRef 1) 0 ≡ rec-loc k
    blk1≢rec k ()

  -- the scratch words, read back past the heads and the sentinel's word
  s2 : LocState.heapMem (floc z₃) (rec-loc w-s2) ≡ just I
  s2 = trans (hw-other (LocState.heapMem (floc z)) (heap-loc (mkHeapRef 1) 0) (rec-loc w-s2) (SV-Tag 0) (blk1≢rec w-s2))
         (trans (h-other H (rec-loc w-s2) (λ c′ _ → head≢ 2 (s≤s (s≤s (s≤s z≤n))) c′))
                (hw-same (LocState.heapMem (floc y₁)) (rec-loc w-s2) I))
  s1 : LocState.heapMem (floc z₅) (rec-loc w-s1) ≡ just O
  s1 = trans (hw-other (LocState.heapMem (floc z)) (heap-loc (mkHeapRef 1) 0) (rec-loc w-s1) (SV-Tag 0) (blk1≢rec w-s1))
         (trans (h-other H (rec-loc w-s1) (λ c′ _ → head≢ 1 (s≤s (s≤s z≤n)) c′))
           (trans (hw-other (LocState.heapMem (floc y₁)) (rec-loc w-s2) (rec-loc w-s1) I (λ ()))
                  (hw-same (LocState.heapMem (floc x)) (rec-loc w-s1) O)))

  ib : ExecFinal.in-block? {FS} (ExecFinal.live-size {FS} (falloc z₂)) (AtDynamic (heap-loc (mkHeapRef 1) 0)) ≡ true
  ib = trans (cong (λ al → ExecFinal.in-block? {FS} (ExecFinal.live-size {FS} al) (AtDynamic (heap-loc (mkHeapRef 1) 0))) (h-alloc H))
             (live1 false fr1)
    where
      live1 : ∀ b → AllocState.freed (falloc x) 1 ≡ b → ExecFinal.in-block? {FS} (ExecFinal.live-size {FS} (falloc y₄)) (AtDynamic (heap-loc (mkHeapRef 1) 0)) ≡ true
      live1 false e = trans (cong (λ t → 0 Data.Nat.<ᵇ (Data.Bool.if t then 0 else size-with 1 (AllocState.next-heap-ref (falloc x)) (AllocState.block-size (falloc x)) 1)) e)
                            (cong (λ t → 0 Data.Nat.<ᵇ size-with 1 t (AllocState.block-size (falloc x)) 1) nx)
      live1 true  e = ⊥-elim (true≢false (trans (sym e) fr1))
        where
          true≢false : ¬ (true ≡ false)
          true≢false ()

  run-rest : FlatSteps prog 6 z z₆
  run-rest = FlatSteps-++ (run-mov-in prog z hz (fe-rest 0 mov-to-input refl))
            (FlatSteps-++ (run-tag prog z₁ 0 hz (fe-rest 1 (instr-load-tag-lit 0) refl))
            (FlatSteps-++ (run-store-at0 prog z₂ 1 out-z ib hz (fe-rest 2 (store-at 0) refl))
            (FlatSteps-++ (run-load-rec prog z₃ w-s2 1 I nz hz (fe-rest 3 (load-rec w-s2) refl) s2)
            (FlatSteps-++ (run-mov-in prog z₄ hz (fe-rest 4 mov-to-input refl))
                          (run-load-rec prog z₅ w-s1 1 O nz hz (fe-rest 5 (load-rec w-s1) refl) s1)))))

  -- the sentinel's word
  sent : LocState.heapMem (floc z₆) (heap-loc (mkHeapRef 1) 0) ≡ just (SV-Tag 0)
  sent = hw-same (LocState.heapMem (floc z)) (heap-loc (mkHeapRef 1) 0) (SV-Tag 0)

  run : FlatSteps prog (4 + (count C + 6)) x z₆
  run = FlatSteps-++ run₄ (FlatSteps-++ stH run-rest)

------------------------------------------------------------------------
-- ★ The first relation
------------------------------------------------------------------------

open import Once.CCC.Codegen.AllocExpandRen {FS} using (rv; rhl)
open import Once.CCC.Codegen.AllocExpandRel {FS} using (Rel; Live; Chain)
open import Once.CCC.Codegen.AllocExpandStep {FS} using (module L)
open import Once.CCC.Codegen.AllocExpandPc {FS} using (off; off-suc)
open import Data.List.Relation.Unary.AllPairs using ([])
import Data.Maybe

rv-id : ∀ v → rv (λ r → r) v ≡ v
rv-id (SV-Ptr (AtStack _ _)) = refl
rv-id (SV-Ptr (AtDynamic (heap-loc (mkHeapRef r) o))) = refl
rv-id (SV-Tag _) = refl
rv-id (SV-Lit _ _) = refl
rv-id (SV-Code _) = refl

mrv-id : ∀ mv → Data.Maybe.map (rv (λ r → r)) mv ≡ mv
mrv-id (just v) = cong just (rv-id v)
mrv-id nothing  = refl

-- the primitive's start: nothing allocated past the record, nothing held
record Start (s : FlatState) : Set where
  field
    s-heap  : ∀ hl → LocState.heapMem (floc s) hl ≡ nothing
    s-next  : AllocState.next-heap-ref (falloc s) ≡ 1
    s-free  : ∀ r → AllocState.freed (falloc s) r ≡ false
    s-size  : ∀ r → AllocState.block-size (falloc s) r ≡ 0
    s-ret   : fret s ≡ []
    s-halt  : LocState.halted (floc s) ≡ false

module First (C : Classes) (P : AbstractTrace) (Sz : ℕ → Set) (x : FlatState) (S : Start x)
             (fe : ∀ j i → fetch (setup C) j ≡ just i → fetch (expand C P) (j + fpc x) ≡ just i)
             (pc1 : fpc x ≡ 1) (link : flink x ≡ nothing)
             (b : ℕ) (st : fetch P 0 ≡ just (instr-ctrl (c-start b))) where
  open Start S
  module SR = SetupRun C (expand C P) x fe s-halt s-next (s-free 1)
  open SR using (z; z₆; H; O; I)
  open HeadsOut

  -- the setup's length: the expanded pc after it
  setup-len : length (setup C) ≡ 4 + (count C + 6)
  setup-len = cong (4 +_) (trans (Data.List.Properties.length-++ (heads C (count C))) (cong (_+ 6) (SR.heads-len (count C))))
    where import Data.List.Properties

  R₀ : Rel C P Sz x z₆
  R₀ = record
    { ρ = λ r → r ; σ = 1 ; lists = λ _ → []
    ; r-pc = trans (cong (λ t → 6 + t) (h-pc H))
               (trans (cong (λ t → 6 + (count C + (4 + t))) pc1)
                 (trans (arith (count C))
                   (sym (trans (cong (off C 0 P) pc1) (trans (off-suc C 0 P 0 (instr-ctrl (c-start b)) st)
                               (trans (cong (_+ length (expand-at C 0 (instr-ctrl (c-start b)))) (off-zero P))
                                      (cong suc setup-len)))))))
    ; r-ret = trans (proj₁ (h-rest H)) (trans s-ret (cong (Data.List.map (off C 0 P)) (sym s-ret)))
    ; r-link = trans (proj₂ (proj₂ (h-rest H))) (trans link (cong (Data.Maybe.map (off C 0 P)) (sym link)))
    ; r-frame = cong AllocState.current-frame (h-alloc H) ; r-saved = cong AllocState.saved-frames (h-alloc H)
    ; r-slots = cong AllocState.frame-slots (h-alloc H) ; r-next-slot = cong AllocState.next-slot (h-alloc H)
    ; r-inj = λ r r′ l → ⊥-elim (none r l)
    ; r-loc = record
        { l-regs = λ { Input1 → sym (rv-id I) ; Output → sym (rv-id O) }
        ; l-stack = λ f k → trans (cong (λ m → m f k) (h-stack H)) (sym (mrv-id (LocState.stackMem (floc x) f k)))
        ; l-heap = λ hl v l e → ⊥-elim (nothing≢ (trans (sym (s-heap hl)) e))
        ; l-live = λ hl v e → ⊥-elim (nothing≢ (trans (sym (s-heap hl)) e))
        ; l-halt = proj₁ (h-flags H) ; l-fault = proj₁ (proj₂ (h-flags H))
        ; l-left = proj₁ (proj₂ (proj₂ (h-flags H))) ; l-log = proj₂ (proj₂ (proj₂ (h-flags H))) }
    ; r-clo = trans (proj₁ (proj₂ (h-rest H))) (sym (rv-id (fclosure x)))
    ; r-size = λ r _ → subst (_≤ AllocState.block-size (falloc z₆) r) (sym (s-size r)) z≤n
    ; r-below = λ r l → ⊥-elim (none r l)
    ; r-not-σ = λ r l → ⊥-elim (none r l)
    ; r-not-free = λ r c b l → ⊥-elim (none r l)
    ; r-heads = λ c c< → blk 1 , head c c< , refl
    ; r-sent = SR.sent
    ; r-lpos = λ c b ()
    ; r-σpos = s≤s z≤n
    ; r-lbelow = λ c b ()
    ; r-lσ = λ c b ()
    ; r-luniq = λ c → []
    ; r-lone = λ c c′ b ()
    ; r-σbelow = subst (1 <_) (sym SR.nz) (s≤s (s≤s z≤n))
    ; r-pnext = subst (0 <_) (sym s-next) (s≤s z≤n)
    ; r-pfresh = λ r _ → s-free r
    ; r-ρbelow = λ r lt → subst (r <_) (sym (cong AllocState.next-heap-ref (h-alloc H))) (Data.Nat.Properties.m<n⇒m<1+n lt)
    ; r-nofree = λ r → trans (cong (λ al → AllocState.freed al r) (h-alloc H)) (s-free r)
    ; r-unsized = λ r _ → s-size r
    ; r-rec0 = s-size 0
    ; r-csize = λ r l → ⊥-elim (none r l)
    ; r-lsize = λ c b () }
    where
      arith : ∀ c → 6 + (c + (4 + 1)) ≡ 0 + suc (4 + (c + 6))
      arith = solve-∀
      off-zero : ∀ Q → off C 0 Q 0 ≡ 0
      off-zero []      = refl
      off-zero (_ ∷ _) = refl
      nothing≢ : ∀ {v : StoredValue FS} → ¬ (nothing ≡ just v)
      nothing≢ ()
      none : ∀ r → ¬ Live (falloc x) r
      none r (pos , lt , _) = Data.Nat.Properties.<-irrefl refl (Data.Nat.Properties.<-≤-trans pos (Data.Nat.Properties.≤-pred (subst (r <_) s-next lt)))
      head : ∀ c → c < count C → LocState.heapMem (floc z₆) (rec-loc (head-word c)) ≡ just (blk 1)
      head c c< = trans (hw-other (LocState.heapMem (floc z)) (heap-loc (mkHeapRef 1) 0) (rec-loc (head-word c)) (SV-Tag 0) (λ ()))
                        (trans (h-head H c c<) (cong (λ t → just (blk t)) s-next))
