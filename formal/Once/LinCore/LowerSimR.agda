-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimR — plan 0.146 B1.4b (D417), `LowerSim` layer (4),
-- continued: A COPY TRAMPOLINE'S `reclose`. A fresh block; the viewed
-- cell's three code words copied into it (its save slot `s₂` the old cell,
-- `s₃` the new); its first word its own address; the copy's words (the
-- frame's first slots) after the header.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (+-comm; ≤-trans; <-≤-trans; ≤-reflexive; m≤m+n; m≤n+m)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; HeapRef; module HeapLocation; offsetHL)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.LowerSimR
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (Id; serial)
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw using (module Sim)
open import Once.LinCore.Lower fmt ans bw using (hdr)
open import Once.LinCore.MoveCode using (mvSP)
import Once.LinCore.Moves

module SimR {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf using (<ᵇ-true; size-with-same)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc; fret; fetch)
  open FlatStepsAPI {FS} using (FlatSteps; step-at; FlatSteps-++) renaming ([] to done)
  open LocState using (heapMem; stackMem) renaming (halted to fhalted)
  open import Once.CCC.Machine.SMPrimitives using (module MemoryOps)
  open MemoryOps {FS} using (readLoc-writeLoc-same)
  open MemOps {FS} using (writeLoc; readLoc; writeLoc-preserves-other; writeLocToHeap)

  -- a heap write, whatever the word: only the heap changes
  wl-heap : ∀ (s : LocState FS) hl (v : W) → writeLoc s (AtDynamic hl) v ≡ writeLocToHeap s hl v
  wl-heap s hl (SV-Ptr (AtStack f k))   = refl
  wl-heap s hl (SV-Ptr (AtDynamic h))   = refl
  wl-heap s hl (SV-Tag t)               = refl
  wl-heap s hl (SV-Lit p v)             = refl
  wl-heap s hl (SV-Code c)              = refl
  open ExecFinal {FS} using (in-block?)
  open import Once.LinCore.Moves {FS}
    using (Seg; slot; restore-step; loadat-step; storeat-step; InBlk; alloc-step; store-step; mov-out-step; store-same; store-other; store-frame
          ; mvSP-run; MovedW; w-moved; w-rest; w-pc; w-alloc; w-in; w-ret) renaming (ln to nsteps; w-halt to wm-halt; w-log to wm-log)
  open Sim {FS} U wordOf using (slots-def; slots-at)

  ref-of : HeapLocation → ℕ
  ref-of hl = HeapRef.ref-id (HeapLocation.heap-ref hl)

  off-of : HeapLocation → ℕ
  off-of hl = HeapLocation.heap-offset hl

  ----------------------------------------------------------------------
  -- ★ A HEAP CHANGED ONLY IN A FRESH BLOCK `r`, below `n` words.
  ----------------------------------------------------------------------

  Fr : (HeapLocation → Maybe W) → (HeapLocation → Maybe W) → ℕ → ℕ → Set
  Fr h h′ r n = ∀ hl → (h′ hl ≡ h hl) ⊎ (ref-of hl ≡ r × off-of hl < n)

  fr-refl : ∀ {h r n} → Fr h h r n
  fr-refl hl = inj₁ refl

  fr-trans : ∀ {h h′ h″ r n} → Fr h h′ r n → Fr h′ h″ r n → Fr h h″ r n
  fr-trans F G hl = go (F hl) (G hl)
    where
      go : _ → _ → _
      go (inj₁ e) (inj₁ e′) = inj₁ (trans e′ e)
      go (inj₁ _) (inj₂ b)  = inj₂ b
      go (inj₂ b) _         = inj₂ b

  private
    loc-ref : ∀ {hl hl′ : HeapLocation} → AtDynamic {FS} hl ≡ AtDynamic hl′ → ref-of hl ≡ ref-of hl′
    loc-ref refl = refl
    loc-off : ∀ {hl hl′ : HeapLocation} → AtDynamic {FS} hl ≡ AtDynamic hl′ → off-of hl ≡ off-of hl′
    loc-off refl = refl

  -- one store into the fresh block
  fr-store : ∀ (s : LocState FS) r k (v : W) {n} → k < n
           → Fr (heapMem s) (heapMem (writeLoc s (AtDynamic (heap-loc (mkHeapRef r) k)) v)) r n
  fr-store s r k v {n} k< hl = by (ref-of hl ≟ r) (off-of hl ≟ k)
    where
      by : Dec (ref-of hl ≡ r) → Dec (off-of hl ≡ k) → _
      by (yes er) (yes ek) = inj₂ (er , subst (_< n) (sym ek) k<)
      by (no ne)  _        = inj₁ (writeLoc-preserves-other s _ (AtDynamic hl) v (λ e → ne (sym (loc-ref e))))
      by (yes _)  (no ne)  = inj₁ (writeLoc-preserves-other s _ (AtDynamic hl) v (λ e → ne (sym (loc-off e))))

  private
    sw-other : ∀ n r (szs : ℕ → ℕ) q → ¬ q ≡ r → size-with n r szs q ≡ szs q
    sw-other n r szs q ne = go (q ≟ r)
      where
        go : (d : Dec (q ≡ r)) → size-with-aux n {q} {r} szs d ≡ szs q
        go (yes e) = ⊥-elim (ne e)
        go (no _)  = refl

  -- ★ every written word still in its block, the fresh block's below its size (D424)
  inb-fresh : ∀ {fs fs′ : FlatState} (r n : ℕ)
            → AllocState.next-heap-ref (falloc fs) ≡ r → AllocState.next-heap-ref (falloc fs′) ≡ suc r
            → AllocState.block-size (falloc fs′) ≡ size-with n r (AllocState.block-size (falloc fs))
            → Fr (heapMem (floc fs)) (heapMem (floc fs′)) r n
            → InBlk fs → InBlk fs′
  inb-fresh {fs} {fs′} r n er en eb F I hl {v} e = go (F hl)
    where
      import Data.Nat.Properties
      go : _ → _
      go (inj₁ same) = after (I hl (trans (sym same) e))
        where
          after : ref-of hl < AllocState.next-heap-ref (falloc fs) × in-block? (AllocState.block-size (falloc fs)) (AtDynamic hl) ≡ true
                → ref-of hl < AllocState.next-heap-ref (falloc fs′) × in-block? (AllocState.block-size (falloc fs′)) (AtDynamic hl) ≡ true
          after (lt , ib) =
            subst (ref-of hl <_) (sym en) (Data.Nat.Properties.≤-trans (subst (ref-of hl <_) er lt) (Data.Nat.Properties.n≤1+n r)) ,
            trans (cong (λ bs → off-of hl Data.Nat.<ᵇ bs (ref-of hl)) eb)
              (trans (cong (off-of hl Data.Nat.<ᵇ_) (sw-other n r (AllocState.block-size (falloc fs)) (ref-of hl)
                        (λ e′ → Data.Nat.Properties.<-irrefl e′ (subst (ref-of hl <_) er lt)))) ib)
      go (inj₂ (refl , o<)) =
        subst (ref-of hl <_) (sym en) (Data.Nat.Properties.n<1+n r) ,
        trans (cong (λ bs → off-of hl Data.Nat.<ᵇ bs r) eb)
          (trans (cong (off-of hl Data.Nat.<ᵇ_) (size-with-same n r (AllocState.block-size (falloc fs)))) (<ᵇ-true o<))

  ----------------------------------------------------------------------
  -- ★ ONE CODE WORD COPIED: the old cell's word `k` into the new cell's.
  ----------------------------------------------------------------------

  record WC (a a′ : FlatState) (r k : ℕ) (v : W) : Set where
    field
      wc-pc    : fpc a′ ≡ suc (suc (suc (suc (fpc a))))
      wc-alloc : falloc a′ ≡ falloc a
      wc-ret   : fret a′ ≡ fret a
      wc-halt  : fhalted (floc a′) ≡ fhalted (floc a)
      wc-log   : LocState.ev-log (floc a′) ≡ LocState.ev-log (floc a)
      wc-stack : stackMem (floc a′) ≡ stackMem (floc a)
      wc-in    : readReg (LocState.regs (floc a′)) Input1 ≡ SV-Ptr (AtDynamic (heap-loc (mkHeapRef r) 0))
      wc-new   : heapMem (floc a′) (heap-loc (mkHeapRef r) (k + 0)) ≡ just v
      wc-fr    : ∀ {n} → k + 0 < n → Fr (heapMem (floc a)) (heapMem (floc a′)) r n
      wc-other : ∀ hl → ¬ AtDynamic {FS} (heap-loc (mkHeapRef r) (k + 0)) ≡ AtDynamic hl → heapMem (floc a′) hl ≡ heapMem (floc a) hl
  open WC public

  word-copy : ∀ prog (a : FlatState) (s₂ s₃ k ro r : ℕ) (v : W)
            → Seg prog (fpc a) (restore-input s₂ ∷ load-at k ∷ restore-input s₃ ∷ store-at k ∷ [])
            → fhalted (floc a) ≡ false
            → slot a s₂ ≡ just (SV-Ptr (AtDynamic (heap-loc (mkHeapRef ro) 0))) → heapMem (floc a) (heap-loc (mkHeapRef ro) (k + 0)) ≡ just v
            → slot a s₃ ≡ just (SV-Ptr (AtDynamic (heap-loc (mkHeapRef r) 0)))
            → in-block? (AllocState.block-size (falloc a)) (AtDynamic (heap-loc (mkHeapRef r) (k + 0))) ≡ true
            → Σ FlatState λ a′ → FlatSteps prog 4 a a′ × WC a a′ r k v
  word-copy prog a s₂ s₃ k ro r v (g₁ , g₂ , g₃ , g₄ , _) h e₂ ev e₃ ib =
    a₄ ,
    step-at a₁ (h , g₁) (restore-step a s₂ e₂) (step-at a₂ (h , g₂) (loadat-step a₁ k refl ev)
    (step-at a₃ (h , g₃) (restore-step a₂ s₃ e₃) (step-at a₄ (h , g₄) (storeat-step a₃ k refl ib) done))) ,
    record { wc-pc = refl ; wc-alloc = refl ; wc-ret = refl
           ; wc-halt = cong fhalted (wl-heap (floc a₃) _ v) ; wc-log = cong LocState.ev-log (wl-heap (floc a₃) _ v) ; wc-stack = cong stackMem (wl-heap (floc a₃) _ v)
           ; wc-in = cong (λ s′ → readReg (LocState.regs s′) Input1) (wl-heap (floc a₃) _ v)
           ; wc-new = readLoc-writeLoc-same (floc a₃) (AtDynamic (heap-loc (mkHeapRef r) (k + 0))) v
           ; wc-fr = λ k< → fr-store (floc a₃) r (k + 0) v k<
           ; wc-other = λ hl ne → writeLoc-preserves-other (floc a₃) _ (AtDynamic hl) v ne }
    where
      a₁ = record a { floc = record (floc a) { regs = writeReg (LocState.regs (floc a)) Input1 (SV-Ptr (AtDynamic (heap-loc (mkHeapRef ro) 0))) } ; fpc = suc (fpc a) }
      a₂ = record a₁ { floc = record (floc a₁) { regs = writeReg (LocState.regs (floc a₁)) Output v } ; fpc = suc (fpc a₁) }
      a₃ = record a₂ { floc = record (floc a₂) { regs = writeReg (LocState.regs (floc a₂)) Input1 (SV-Ptr (AtDynamic (heap-loc (mkHeapRef r) 0))) } ; fpc = suc (fpc a₂) }
      a₄ = record a₃ { floc = writeLoc (floc a₃) (AtDynamic (heap-loc (mkHeapRef r) (k + 0))) v ; fpc = suc (fpc a₃) }

  ----------------------------------------------------------------------
  -- ★ THE `reclose` RUN: a fresh block `r`, its header copied, the copy's
  -- words (slots 0..w) after it; save slot `s₃` the new cell.
  ----------------------------------------------------------------------

  record ReCl (fs fs′ : FlatState) (s₃ sz : ℕ) (w₁ w₂ w₃ : W) (wx : List W) : Set where
    field
      rc-pc    : fpc fs′ ≡ nsteps (length wx) + suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (fpc fs))))))))))))))))
      rc-alloc : falloc fs′ ≡ record (falloc fs) { next-heap-ref = suc (AllocState.next-heap-ref (falloc fs))
                                                  ; block-size = size-with (hdr + length wx) (AllocState.next-heap-ref (falloc fs)) (AllocState.block-size (falloc fs)) }
      rc-ret   : fret fs′ ≡ fret fs
      rc-halt  : fhalted (floc fs′) ≡ fhalted (floc fs)
      rc-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)
      rc-s₃    : slot fs′ s₃ ≡ just (cellPtr (sz , AllocState.next-heap-ref (falloc fs)))
      rc-slot  : ∀ x → ¬ s₃ ≡ x → slot fs′ x ≡ slot fs x
      rc-other : ∀ f x → ¬ AllocState.current-frame (falloc fs) ≡ f → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x
      rc-cell  : At (heapMem (floc fs′)) (sz , AllocState.next-heap-ref (falloc fs)) 0
                    (cellPtr (sz , AllocState.next-heap-ref (falloc fs)) ∷ w₁ ∷ w₂ ∷ w₃ ∷ wx)
      rc-fr    : Fr (heapMem (floc fs)) (heapMem (floc fs′)) (AllocState.next-heap-ref (falloc fs)) (hdr + length wx)
  open ReCl public

  private
    -- a word copy keeps the frame's slots
    slot-wc : ∀ {a a′ r k v} → WC a a′ r k v → ∀ x → slot a′ x ≡ slot a x
    slot-wc {a} {a′} W x = trans (cong (λ m → m (AllocState.current-frame (falloc a′)) x) (wc-stack W))
                                 (cong (λ al → stackMem (floc a) (AllocState.current-frame al) x) (wc-alloc W))
    stk-wc : ∀ {a a′ r k v} → WC a a′ r k v → ∀ f x → stackMem (floc a′) f x ≡ stackMem (floc a) f x
    stk-wc W f x = cong (λ m → m f x) (wc-stack W)
    other-ref : ∀ {r r′ o o′} → ¬ r ≡ r′ → ¬ AtDynamic {FS} (heap-loc (mkHeapRef r) o) ≡ AtDynamic (heap-loc (mkHeapRef r′) o′)
    other-ref ne refl = ne refl
    other-off : ∀ {r o o′} → ¬ o ≡ o′ → ¬ AtDynamic {FS} (heap-loc (mkHeapRef r) o) ≡ AtDynamic (heap-loc (mkHeapRef r) o′)
    other-off ne refl = ne refl
    sw-in : ∀ n r (szs : ℕ → ℕ) o → o < n → in-block? (size-with n r szs) (AtDynamic (heap-loc (mkHeapRef r) o)) ≡ true
    sw-in n r szs o o< = trans (cong (o Data.Nat.<ᵇ_) (size-with-same n r szs)) (<ᵇ-true o<)

  reclose-run : ∀ prog (fs : FlatState) (s₂ s₃ sz : ℕ) (i : Id) (w₁ w₂ w₃ : W) (wx : List W)
              → Seg prog (fpc fs) (instr-alloc-heap (hdr + length wx) ∷ store-at-slot s₃
                                   ∷ restore-input s₂ ∷ load-at 1 ∷ restore-input s₃ ∷ store-at 1
                                   ∷ restore-input s₂ ∷ load-at 2 ∷ restore-input s₃ ∷ store-at 2
                                   ∷ restore-input s₂ ∷ load-at 3 ∷ restore-input s₃ ∷ store-at 3
                                   ∷ mov-to-output ∷ store-at 0 ∷ mvSP 0 hdr (length wx))
              → fhalted (floc fs) ≡ false
              → slot fs s₂ ≡ just (cellPtr i) → ¬ s₃ ≡ s₂ → (∀ k → k < length wx → ¬ s₃ ≡ k)
              → heapMem (floc fs) (cellLoc i 1) ≡ just w₁ → heapMem (floc fs) (cellLoc i 2) ≡ just w₂
              → heapMem (floc fs) (cellLoc i 3) ≡ just w₃
              → ¬ serial i ≡ AllocState.next-heap-ref (falloc fs)
              → SlotsAt (slot fs) 0 wx
              → Σ FlatState λ fs′ → FlatSteps prog (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (nsteps (length wx)))))))))))))))))) fs fs′
                  × ReCl fs fs′ s₃ sz w₁ w₂ w₃ wx
  reclose-run prog fs s₂ s₃ sz i w₁ w₂ w₃ wx (g₁ , g₂ , c₁ , c₂ , c₃ , c₄ , d₁ , d₂ , d₃ , d₄ , e₁ , e₂ , e₃ , e₄ , m₁ , m₂ , sm) h
              s₂i ne₂₃ ne-k ev₁ ev₂ ev₃ ne-i sw =
    copy₁ (word-copy prog fs₂ s₂ s₃ 1 (serial i) r w₁ (c₁ , c₂ , c₃ , c₄ , tt) h s₂₂ ev₁ s₃₂ (sw-in n r bs 1 (s≤s (s≤s z≤n))))
    where
      import Data.Nat.Properties
      w = length wx
      n = hdr + w
      r = AllocState.next-heap-ref (falloc fs)
      bs = AllocState.block-size (falloc fs)
      cf = AllocState.current-frame (falloc fs)
      P = heap-loc (mkHeapRef r) 0
      fs₁ = record fs { floc   = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (SV-Ptr (AtDynamic P)) }
                      ; falloc = record (falloc fs) { next-heap-ref = suc r ; block-size = size-with n r bs }
                      ; fpc    = suc (fpc fs) }
      fs₂ = record fs₁ { floc = writeLoc (floc fs₁) (AtStack cf s₃) (SV-Ptr (AtDynamic P)) ; fpc = suc (fpc fs₁) }
      s₂₂ : slot fs₂ s₂ ≡ just (cellPtr i)
      s₂₂ = trans (store-other (floc fs₁) cf s₃ _ s₂ ne₂₃) s₂i
      s₃₂ : slot fs₂ s₃ ≡ just (SV-Ptr (AtDynamic P))
      s₃₂ = store-same (floc fs₁) cf s₃ _
      ne-old : ∀ {o o′} → ¬ AtDynamic {FS} (heap-loc (mkHeapRef r) o) ≡ AtDynamic (heap-loc (mkHeapRef (serial i)) o′)
      ne-old = other-ref (λ e → ne-i (sym e))
      ne34 : ∀ {a b} → a < 4 → 4 ≤ b → ¬ a ≡ b
      ne34 a< le e = Data.Nat.Properties.<-irrefl e (<-≤-trans a< le)
      copy₁ : Σ FlatState (λ a → FlatSteps prog 4 fs₂ a × WC fs₂ a r 1 w₁) → _
      copy₁ (a , st₁ , W₁) =
        copy₂ (word-copy prog a s₂ s₃ 2 (serial i) r w₂ (subst (λ z → Seg prog z (restore-input s₂ ∷ load-at 2 ∷ restore-input s₃ ∷ store-at 2 ∷ [])) (sym (wc-pc W₁)) (d₁ , d₂ , d₃ , d₄ , tt)) (trans (wc-halt W₁) h)
                 (trans (slot-wc W₁ s₂) s₂₂) (trans (wc-other W₁ _ ne-old) ev₂) (trans (slot-wc W₁ s₃) s₃₂)
                 (trans (cong (λ al → in-block? (AllocState.block-size al) (AtDynamic (heap-loc (mkHeapRef r) 2))) (wc-alloc W₁))
                        (sw-in n r bs 2 (s≤s (s≤s (s≤s z≤n))))))
        where
          copy₂ : Σ FlatState (λ b → FlatSteps prog 4 a b × WC a b r 2 w₂) → _
          copy₂ (b , st₂ , W₂) =
            copy₃ (word-copy prog b s₂ s₃ 3 (serial i) r w₃
                     (subst (λ z → Seg prog z (restore-input s₂ ∷ load-at 3 ∷ restore-input s₃ ∷ store-at 3 ∷ [])) (sym (trans (wc-pc W₂) (cong (λ z → suc (suc (suc (suc z)))) (wc-pc W₁)))) (e₁ , e₂ , e₃ , e₄ , tt)) (trans (wc-halt W₂) (trans (wc-halt W₁) h))
                     (trans (slot-wc W₂ s₂) (trans (slot-wc W₁ s₂) s₂₂))
                     (trans (wc-other W₂ _ ne-old) (trans (wc-other W₁ _ ne-old) ev₃))
                     (trans (slot-wc W₂ s₃) (trans (slot-wc W₁ s₃) s₃₂))
                     (trans (cong (λ al → in-block? (AllocState.block-size al) (AtDynamic (heap-loc (mkHeapRef r) 3))) (trans (wc-alloc W₂) (wc-alloc W₁)))
                            (sw-in n r bs 3 (s≤s (s≤s (s≤s (s≤s z≤n)))))))
            where
              copy₃ : Σ FlatState (λ c → FlatSteps prog 4 b c × WC b c r 3 w₃) → _
              copy₃ (c , st₃ , W₃) = fin (mvSP-run prog fs₁₆ (AtDynamic P) 0 hdr w segM h₁₆ in₁₆ def ib (λ k k′ _ _ ()))
                where
                  pc-c : fpc c ≡ suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (fpc fs))))))))))))))
                  pc-c = trans (wc-pc W₃) (cong (λ z → suc (suc (suc (suc z)))) (trans (wc-pc W₂) (cong (λ z → suc (suc (suc (suc z)))) (wc-pc W₁))))
                  h-c : fhalted (floc c) ≡ false
                  h-c = trans (wc-halt W₃) (trans (wc-halt W₂) (trans (wc-halt W₁) h))
                  al-c : falloc c ≡ falloc fs₂
                  al-c = trans (wc-alloc W₃) (trans (wc-alloc W₂) (wc-alloc W₁))
                  in-c : readReg (LocState.regs (floc c)) Input1 ≡ SV-Ptr (AtDynamic P)
                  in-c = wc-in W₃
                  fs₁₅ = record c { floc = record (floc c) { regs = writeReg (LocState.regs (floc c)) Output (readReg (LocState.regs (floc c)) Input1) }
                                  ; fpc = suc (fpc c) }
                  ib0 : in-block? (AllocState.block-size (falloc fs₁₅)) (offsetLoc (AtDynamic P) 0) ≡ true
                  ib0 = trans (cong (λ al → in-block? (AllocState.block-size al) (AtDynamic (heap-loc (mkHeapRef r) 0))) al-c) (sw-in n r bs 0 (s≤s z≤n))
                  fs₁₆ = record fs₁₅ { floc = writeLoc (floc fs₁₅) (offsetLoc (AtDynamic P) 0) (readReg (LocState.regs (floc fs₁₅)) Output)
                                     ; fpc = suc (fpc fs₁₅) }
                  wl₁₆ = wl-heap (floc fs₁₅) (heap-loc (mkHeapRef r) 0) (readReg (LocState.regs (floc fs₁₅)) Output)
                  h₁₆ : fhalted (floc fs₁₆) ≡ false
                  h₁₆ = trans (cong fhalted wl₁₆) h-c
                  in₁₆ : readReg (LocState.regs (floc fs₁₆)) Input1 ≡ SV-Ptr (AtDynamic P)
                  in₁₆ = trans (cong (λ s′ → readReg (LocState.regs s′) Input1) wl₁₆) in-c
                  -- the frame's slots: as at fs₂
                  stk₁₆ : ∀ f x → stackMem (floc fs₁₆) f x ≡ stackMem (floc fs₂) f x
                  stk₁₆ f x = trans (cong (λ s′ → stackMem s′ f x) wl₁₆) (trans (stk-wc W₃ f x) (trans (stk-wc W₂ f x) (stk-wc W₁ f x)))
                  cf₁₆ : AllocState.current-frame (falloc fs₁₆) ≡ cf
                  cf₁₆ = cong AllocState.current-frame al-c
                  slot₁₆ : ∀ x → slot fs₁₆ x ≡ slot fs₂ x
                  slot₁₆ x = trans (cong (λ g → stackMem (floc fs₁₆) g x) cf₁₆) (stk₁₆ cf x)
                  segM : Seg prog (fpc fs₁₆) (mvSP 0 hdr w)
                  segM = subst (λ z → Seg prog (suc (suc z)) (mvSP 0 hdr w)) (sym pc-c) sm
                  def : ∀ k → k < w → Σ W λ v → slot fs₁₆ (k + 0) ≡ just v
                  def k k< = hit (slots-def {slot fs} {0} wx sw k k<)
                    where
                      hit : Σ W (λ v → slot fs (k + 0) ≡ just v) → Σ W λ v → slot fs₁₆ (k + 0) ≡ just v
                      hit (v , e) = v , trans (slot₁₆ (k + 0)) (trans (store-other (floc fs₁) cf s₃ _ (k + 0)
                                                (λ e′ → ne-k k k< (trans e′ (Data.Nat.Properties.+-identityʳ k)))) e)
                  ib : ∀ k → k < w → in-block? (AllocState.block-size (falloc fs₁₆)) (offsetLoc (AtDynamic P) (k + hdr)) ≡ true
                  ib k k< = trans (cong (λ al → in-block? (AllocState.block-size al) (AtDynamic (heap-loc (mkHeapRef r) ((k + hdr) + 0)))) al-c)
                                  (sw-in n r bs ((k + hdr) + 0)
                                     (subst (_< n) (sym (trans (Data.Nat.Properties.+-identityʳ (k + hdr)) (+-comm k hdr)))
                                        (Data.Nat.Properties.+-monoʳ-< hdr k<)))
                  fin : Σ FlatState (λ fs′ → FlatSteps prog (nsteps w) fs₁₆ fs′ × MovedW fs₁₆ fs′ (AtDynamic P) 0 hdr w) → _
                  fin (fs′ , stM , M) =
                    fs′ ,
                    step-at fs₁ (h , g₁) (alloc-step fs n) (step-at fs₂ (h , g₂) (store-step fs₁ s₃)
                      (FlatSteps-++ st₁ (FlatSteps-++ st₂ (FlatSteps-++ st₃
                        (step-at fs₁₅ (h-c , subst (λ z → fetch prog z ≡ just mov-to-output) (sym pc-c) m₁)
                           (mov-out-step c)
                        (step-at fs₁₆ (h-c , subst (λ z → fetch prog (suc z) ≡ just (store-at 0)) (sym pc-c) m₂)
                           (storeat-step fs₁₅ 0 in-c ib0) stM)))))) ,
                    record { rc-pc = trans (w-pc M) (cong (λ z → nsteps w + suc (suc z)) pc-c)
                           ; rc-alloc = trans (w-alloc M) al-c
                           ; rc-ret = trans (w-ret M) (trans (wc-ret W₃) (trans (wc-ret W₂) (wc-ret W₁)))
                           ; rc-halt = trans (wm-halt M) (trans (cong fhalted wl₁₆) (trans (wc-halt W₃) (trans (wc-halt W₂) (wc-halt W₁))))
                           ; rc-log = trans (wm-log M) (trans (cong LocState.ev-log wl₁₆) (trans (wc-log W₃) (trans (wc-log W₂) (wc-log W₁))))
                           ; rc-s₃ = trans (stM′ s₃) s₃₂
                           ; rc-slot = λ x ne → trans (stM′ x) (store-other (floc fs₁) cf s₃ _ x ne)
                           ; rc-other = λ f x ne → trans (stF f x) (store-frame (floc fs₁) cf s₃ _ f x ne)
                           ; rc-cell = cell
                           ; rc-fr = fr-trans (fr-trans (fr-trans (wc-fr W₁ (s≤s (s≤s z≤n))) (wc-fr W₂ (s≤s (s≤s (s≤s z≤n)))))
                                                (wc-fr W₃ (s≤s (s≤s (s≤s (s≤s z≤n))))))
                                       (fr-trans {heapMem (floc c)} {heapMem (floc fs₁₆)}
                                                    (fr-store (floc fs₁₅) r 0 (readReg (LocState.regs (floc fs₁₅)) Output) {n} (s≤s z≤n))
                                                 frM) }
                    where
                      stF : ∀ f x → stackMem (floc fs′) f x ≡ stackMem (floc fs₂) f x
                      stF f x = trans (w-rest M (AtStack f x) (λ k k< ())) (stk₁₆ f x)
                      stM′ : ∀ x → slot fs′ x ≡ slot fs₂ x
                      stM′ x = trans (cong (λ g → stackMem (floc fs′) g x) (cong AllocState.current-frame (w-alloc M)))
                                     (trans (w-rest M (AtStack (AllocState.current-frame (falloc fs₁₆)) x) (λ k k< ())) (slot₁₆ x))
                      -- the move's writes: inside the fresh block's words
                      frM : Fr (heapMem (floc fs₁₆)) (heapMem (floc fs′)) r n
                      frM hl = by (ref-of hl ≟ r) (off-of hl Data.Nat.<? n)
                        where
                          by : Dec (ref-of hl ≡ r) → Dec (off-of hl < n) → _
                          by (yes er) (yes o<) = inj₂ (er , o<)
                          by (no ne) _ = inj₁ (w-rest M (AtDynamic hl) (λ k k< e → ne (loc-ref e)))
                          by (yes _) (no o≮) = inj₁ (w-rest M (AtDynamic hl) (λ k k< e → o≮ (subst (_< n) (sym (loc-off e))
                                                 (subst (_< n) (sym (trans (Data.Nat.Properties.+-identityʳ (k + hdr)) (+-comm k hdr)))
                                                   (Data.Nat.Properties.+-monoʳ-< hdr k<)))))
                      -- the new cell's words
                      w0 : heapMem (floc fs′) (heap-loc (mkHeapRef r) 0) ≡ just (cellPtr (sz , r))
                      w0 = trans (w-rest M (AtDynamic (heap-loc (mkHeapRef r) 0)) (λ k k< e → ne34 (s≤s z≤n) (≤-trans (m≤n+m 4 k) (≤-reflexive (sym (Data.Nat.Properties.+-identityʳ (k + 4))))) (loc-off e)))
                             (trans (readLoc-writeLoc-same (floc fs₁₅) (AtDynamic (heap-loc (mkHeapRef r) 0)) _) (cong just in-c))
                      hd : ∀ j → 1 ≤ j → j < 4 → heapMem (floc fs′) (heap-loc (mkHeapRef r) j) ≡ heapMem (floc c) (heap-loc (mkHeapRef r) j)
                      hd j 1≤ j< = trans (w-rest M (AtDynamic (heap-loc (mkHeapRef r) j)) (λ k k< e → ne34 j< (≤-trans (m≤n+m 4 k) (≤-reflexive (sym (Data.Nat.Properties.+-identityʳ (k + 4))))) (loc-off e)))
                                    (trans (cong (λ s′ → heapMem s′ (heap-loc (mkHeapRef r) j)) wl₁₆)
                                       (writeLocToHeap-other j 1≤))
                        where
                          writeLocToHeap-other : ∀ j → 1 ≤ j → heapMem (writeLocToHeap (floc fs₁₅) (heap-loc (mkHeapRef r) 0) (readReg (LocState.regs (floc fs₁₅)) Output)) (heap-loc (mkHeapRef r) j) ≡ heapMem (floc c) (heap-loc (mkHeapRef r) j)
                          writeLocToHeap-other j le = trans (sym (cong (λ s′ → heapMem s′ (heap-loc (mkHeapRef r) j)) wl₁₆))
                                                        (writeLoc-preserves-other (floc fs₁₅) (AtDynamic (heap-loc (mkHeapRef r) 0)) (AtDynamic (heap-loc (mkHeapRef r) j)) (readReg (LocState.regs (floc fs₁₅)) Output)
                                                           (other-off (λ e → Data.Nat.Properties.<-irrefl e le)))
                      cell : At (heapMem (floc fs′)) (sz , r) 0 (cellPtr (sz , r) ∷ w₁ ∷ w₂ ∷ w₃ ∷ wx)
                      cell = w0
                           , trans (hd 1 (s≤s z≤n) (s≤s (s≤s z≤n))) (trans (wc-other W₃ _ (other-off (λ ()))) (trans (wc-other W₂ _ (other-off (λ ()))) (wc-new W₁)))
                           , trans (hd 2 (s≤s z≤n) (s≤s (s≤s (s≤s z≤n)))) (trans (wc-other W₃ _ (other-off (λ ()))) (wc-new W₂))
                           , trans (hd 3 (s≤s z≤n) (s≤s (s≤s (s≤s (s≤s z≤n))))) (wc-new W₃)
                           , slots-at {heapMem (floc fs′)} {slot fs} {sz , r} wx hdr 0
                               (λ k k< → trans (cong (λ z → heapMem (floc fs′) (heap-loc (mkHeapRef r) z)) (sym (Data.Nat.Properties.+-identityʳ (k + hdr))))
                                           (trans (w-moved M k k<) (trans (slot₁₆ (k + 0)) (store-other (floc fs₁) cf s₃ _ (k + 0)
                                             (λ e′ → ne-k k k< (trans e′ (Data.Nat.Properties.+-identityʳ k)))))))
                               sw
