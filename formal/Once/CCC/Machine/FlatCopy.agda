-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatCopy — COPYING A FLAT VALUE'S WORDS (plan 0.123 B.4 α).
--
-- A compound component is EMBEDDED in its container (D375, D378): building a
-- pair, a sum or a node copies the component's words into the new block
-- instead of storing a pointer. The copy is the same everywhere, so it is one
-- trace and one run, used by every construct:
--
--   copy-from src blk off i k — the k words from word i of the value whose
--   address is in slot `src`, to the block whose address is in slot `blk`,
--   from its word `off + i`: per word,
--     restore-input src ; load-at i ; restore-input blk ; store-at (off + i)
--
-- `copy-run`: given the slots hold the two (heap) addresses, of DIFFERENT
-- blocks, and the source's words are written, the copy runs (no fault), moves
-- no allocator, and leaves word `off + i + j` of the block equal to word `i + j`
-- of the source; nothing else in the heap or the stack changes.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.FlatCopy {FS : FrameSemantics} where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.List using ([]; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-cancelʳ-≡; +-cancelˡ-≡; 0≢1+n)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; offsetHL; module HeapLocation)
open HeapLocation using (heap-ref)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore
open MemOps {FS}
open AbstractExec {FS}
open import Once.CCC.Machine.SMPrimitives using (module MemoryOps)
open MemoryOps {FS} using (readLoc-writeLoc-same)
open AllocState using (current-frame)
open LocState using (halted; regs)
open ExecFinal {FS} using (in-block?)
open AllocState using (block-size)
open import Once.CCC.Codegen.FlatLayout using (copy-from) public

-- D379: each destination word is a cell of the destination's block
InBlock : AllocState {FS} → HeapLocation → ℕ → Set
InBlock alloc dh n = in-block? (block-size alloc) (AtDynamic (offsetHL dh n)) ≡ true

-- the state after one word: the three register writes, then the one heap write
one-word : ∀ (s : LocState FS) (sh dh : HeapLocation) (w : StoredValue FS) (off i : ℕ) → LocState FS
one-word s sh dh w off i =
  writeLoc (record s { regs = writeReg (writeReg (writeReg (regs s) Input1 (SV-Ptr (AtDynamic sh)))
                                         Output w) Input1 (SV-Ptr (AtDynamic dh)) })
           (AtDynamic (offsetHL dh (off + i))) w

-- ONE WORD: the four instructions are the one heap write
copy-one : ∀ (src blk off i k : ℕ) (s : LocState FS) (alloc : AllocState {FS})
             (sh dh : HeapLocation) (w : StoredValue FS)
         → halted s ≡ false
         → readLoc s (AtStack (current-frame alloc) src) ≡ just (SV-Ptr (AtDynamic sh))
         → readLoc s (AtDynamic (offsetHL sh i)) ≡ just w
         → readLoc s (AtStack (current-frame alloc) blk) ≡ just (SV-Ptr (AtDynamic dh))
         → InBlock alloc dh (off + i)
         → exec-trace (copy-from src blk off i (suc k)) s alloc
           ≡ exec-trace (copy-from src blk off (suc i) k) (one-word s sh dh w off i) alloc
copy-one src blk off i k s alloc sh dh w h rs rw rb ib rewrite h | rs | h | rw | rb | ib = refl

------------------------------------------------------------------------
-- ONE HEAP WRITE (its value abstract): it keeps the run going, leaves the
-- stack, and changes one cell.
------------------------------------------------------------------------
private
  wl-halted : ∀ (s : LocState FS) (hl : HeapLocation) (w : StoredValue FS)
            → halted (writeLoc s (AtDynamic hl) w) ≡ halted s
  wl-halted s hl (SV-Ptr (AtStack _ _))  = refl
  wl-halted s hl (SV-Ptr (AtDynamic _))  = refl
  wl-halted s hl (SV-Tag _)              = refl
  wl-halted s hl (SV-Lit _ _)            = refl
  wl-halted s hl (SV-Code _)             = refl

  wl-stack : ∀ (s : LocState FS) (hl : HeapLocation) (w : StoredValue FS) f k
           → readLoc (writeLoc s (AtDynamic hl) w) (AtStack f k) ≡ readLoc s (AtStack f k)
  wl-stack s hl w f k = writeLoc-preserves-other s (AtDynamic hl) (AtStack f k) w (λ ())

  wl-other : ∀ (s : LocState FS) (hl hl' : HeapLocation) (w : StoredValue FS)
           → AtDynamic hl ≢ AtDynamic hl'
           → readLoc (writeLoc s (AtDynamic hl) w) (AtDynamic hl') ≡ readLoc s (AtDynamic hl')
  wl-other s hl hl' w ne = writeLoc-preserves-other s (AtDynamic hl) (AtDynamic hl') w ne

  -- offsets within a block are distinct cells; cells of different blocks too
  dyn-inj : ∀ {x y : HeapLocation} → AtDynamic {FS} x ≡ AtDynamic y → x ≡ y
  dyn-inj refl = refl

  off-ne : ∀ (dh : HeapLocation) a b → ¬ (a ≡ b) → AtDynamic {FS} (offsetHL dh a) ≢ AtDynamic (offsetHL dh b)
  off-ne dh a b ne e = ne (+-cancelʳ-≡ (HeapLocation.heap-offset dh) a b (cong HeapLocation.heap-offset (dyn-inj e)))

  blk-ne : ∀ (sh dh : HeapLocation) a b → ¬ (heap-ref sh ≡ heap-ref dh)
         → AtDynamic {FS} (offsetHL sh a) ≢ AtDynamic (offsetHL dh b)
  blk-ne sh dh a b ne e = ne (cong heap-ref (dyn-inj e))

  -- a register write changes no memory
  regs-mem : ∀ (s : LocState FS) r loc → readLoc (record s { regs = r }) loc ≡ readLoc s loc
  regs-mem s r (AtStack _ _)  = refl
  regs-mem s r (AtDynamic _)  = refl

------------------------------------------------------------------------
-- THE RUN, k words from word i on (stated over the run's result `r`, so a step
-- transports along `copy-one`'s equation)
------------------------------------------------------------------------
CopyOut : (off i k : ℕ) (sh dh : HeapLocation) (s : LocState FS) (alloc : AllocState {FS})
        → LocState FS × AllocState {FS} → Set
CopyOut off i k sh dh s alloc r =
    (proj₂ r ≡ alloc)
  × (halted (proj₁ r) ≡ false)
  × (∀ j → j < k → readLoc (proj₁ r) (AtDynamic (offsetHL dh (off + (i + j))))
                   ≡ readLoc s (AtDynamic (offsetHL sh (i + j))))
  × (∀ loc → (∀ j → j < k → loc ≢ AtDynamic (offsetHL dh (off + (i + j))))
           → readLoc (proj₁ r) loc ≡ readLoc s loc)

copy-run : ∀ (src blk off i k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (sh dh : HeapLocation)
         → ¬ (heap-ref sh ≡ heap-ref dh)
         → halted s ≡ false
         → readLoc s (AtStack (current-frame alloc) src) ≡ just (SV-Ptr (AtDynamic sh))
         → readLoc s (AtStack (current-frame alloc) blk) ≡ just (SV-Ptr (AtDynamic dh))
         → (∀ j → j < k → Σ (StoredValue FS) (λ w → readLoc s (AtDynamic (offsetHL sh (i + j))) ≡ just w))
         → (∀ j → j < k → InBlock alloc dh (off + (i + j)))
         → CopyOut off i k sh dh s alloc (exec-trace (copy-from src blk off i k) s alloc)
copy-run src blk off i zero s alloc sh dh ne h rs rb wr ibs =
  refl , h , (λ j ()) , (λ loc _ → refl)
copy-run src blk off i (suc k) s alloc sh dh ne h rs rb wr ibs =
  subst (CopyOut off i (suc k) sh dh s alloc) (sym eq) out
  where
    w  = proj₁ (wr 0 (s≤s z≤n))
    rw : readLoc s (AtDynamic (offsetHL sh i)) ≡ just w
    rw = subst (λ x → readLoc s (AtDynamic (offsetHL sh x)) ≡ just w) (+-identityʳ i) (proj₂ (wr 0 (s≤s z≤n)))
    s₀ = record s { regs = writeReg (writeReg (writeReg (regs s) Input1 (SV-Ptr (AtDynamic sh)))
                                     Output w) Input1 (SV-Ptr (AtDynamic dh)) }
    s₁ = one-word s sh dh w off i
    eq : exec-trace (copy-from src blk off i (suc k)) s alloc
       ≡ exec-trace (copy-from src blk off (suc i) k) s₁ alloc
    eq = copy-one src blk off i k s alloc sh dh w h rs rw rb
           (subst (λ x → InBlock alloc dh (off + x)) (+-identityʳ i) (ibs 0 (s≤s z≤n)))
    -- what the one write leaves
    s₁-other : ∀ loc → loc ≢ AtDynamic (offsetHL dh (off + i)) → readLoc s₁ loc ≡ readLoc s loc
    s₁-other loc ne′ = trans (writeLoc-preserves-other s₀ _ loc w (λ e → ne′ (sym e))) (regs-mem s _ loc)
    ih = copy-run src blk off (suc i) k s₁ alloc sh dh ne
           (trans (wl-halted s₀ (offsetHL dh (off + i)) w) h)
           (trans (wl-stack s₀ (offsetHL dh (off + i)) w _ src) rs)
           (trans (wl-stack s₀ (offsetHL dh (off + i)) w _ blk) rb)
           (λ j j<k → proj₁ (wr (suc j) (s≤s j<k))
                    , trans (s₁-other _ (blk-ne sh dh (suc (i + j)) (off + i) ne))
                            (subst (λ x → readLoc s (AtDynamic (offsetHL sh x)) ≡ just (proj₁ (wr (suc j) (s≤s j<k))))
                                   (+-suc i j) (proj₂ (wr (suc j) (s≤s j<k)))))
           (λ j j<k → subst (λ x → InBlock alloc dh (off + x)) (+-suc i j) (ibs (suc j) (s≤s j<k)))
    r = exec-trace (copy-from src blk off (suc i) k) s₁ alloc
    out : CopyOut off i (suc k) sh dh s alloc r
    out = proj₁ ih , proj₁ (proj₂ ih) , copied , other
      where
        later : ∀ j′ → j′ < k → AtDynamic (offsetHL dh (off + (i + 0))) ≢ AtDynamic (offsetHL dh (off + (suc i + j′)))
        later j′ _ = off-ne dh _ _ (λ e → 0≢1+n (+-cancelˡ-≡ i 0 (suc j′) (trans (+-cancelˡ-≡ off _ _ e) (sym (+-suc i j′)))))
        copied : ∀ j → j < suc k → readLoc (proj₁ r) (AtDynamic (offsetHL dh (off + (i + j))))
                                 ≡ readLoc s (AtDynamic (offsetHL sh (i + j)))
        copied zero _ =
          trans (proj₂ (proj₂ (proj₂ ih)) _ (λ j′ j′<k e → later j′ j′<k e))
         (trans (subst (λ x → readLoc s₁ (AtDynamic (offsetHL dh (off + x))) ≡ just w) (sym (+-identityʳ i))
                       (readLoc-writeLoc-same s₀ (AtDynamic (offsetHL dh (off + i))) w))
                (sym (subst (λ x → readLoc s (AtDynamic (offsetHL sh x)) ≡ just w) (sym (+-identityʳ i)) rw)))
        copied (suc j) (s≤s j<k) =
          subst (λ x → readLoc (proj₁ r) (AtDynamic (offsetHL dh (off + x))) ≡ readLoc s (AtDynamic (offsetHL sh x)))
                (sym (+-suc i j))
                (trans (proj₁ (proj₂ (proj₂ ih)) j j<k)
                       (s₁-other _ (blk-ne sh dh (suc i + j) (off + i) ne)))
        other : ∀ loc → (∀ j → j < suc k → loc ≢ AtDynamic (offsetHL dh (off + (i + j))))
              → readLoc (proj₁ r) loc ≡ readLoc s loc
        other loc nr =
          trans (proj₂ (proj₂ (proj₂ ih)) loc
                   (λ j′ j′<k → subst (λ x → loc ≢ AtDynamic (offsetHL dh (off + x))) (+-suc i j′) (nr (suc j′) (s≤s j′<k))))
                (s₁-other loc (subst (λ x → loc ≢ AtDynamic (offsetHL dh (off + x))) (+-identityʳ i) (nr 0 (s≤s z≤n))))
