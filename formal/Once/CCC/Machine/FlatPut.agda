-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatPut
--
-- plan 0.123 B.4 α: WRITING A COMPONENT INTO A BLOCK (`FlatLayout.put`).
--
-- `put C stash blk off` writes the value whose register form is in slot
-- `stash` into the block in slot `blk`, at word `off`: a node's or scalar's
-- word by one `store-at`, a flat value's words by a copy (`FlatCopy`). Its
-- run, stated over `exec-trace`: the allocator stays, the run stays live, only
-- the destination's words change, and the value is valid at the destination.
--
-- The value is valid at an EARLIER allocator `a₀`, under which the
-- destination block was not yet live: that is what makes "every cell the value
-- reads is not one the put writes" a fact rather than a premise.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractTrace)

module Once.CCC.Machine.FlatPut {FS : FrameSemantics} {prog : AbstractTrace} where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-comm; +-monoʳ-≤; ≤-trans; +-suc; +-cancelˡ-≡)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapRef; HeapLocation; heap-loc; offsetHL; module HeapLocation)
open HeapLocation using (heap-ref)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap; AbstractTrace)
open MemOps {FS}
open AbstractExec {FS} using (exec-trace)
open import Once.CCC.Machine.SMPrimitives using (module MemoryOps)
open MemoryOps {FS} using (readLoc-writeLoc-same)
open AllocState using (current-frame)
open LocState using (halted; regs)
open import Once.IR using (AllocMode; Stack; Heap)
open import Once.IRTy using (IRTy; Unit; Void; _*_; _⇛_; μ-type; ν-type; Int; Float; FitsInRegI; fits-int; fits-float)
  renaming (_+_ to _+ᵀ_)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (Kind; word; flat; kind; put; put-k; copy-from)
open import Once.CCC.Machine.ValueRel
open ClosureWellFormedBase {FS}
open ClosureWellFormedDef {FS} {prog} using (ValidAtWF; CellAt; validityWF-heap-transport)
open import Once.CCC.Machine.FlatCopy {FS} using (copy-run; copy-input1; CopyOut; InBlock; wl-halted; regs-mem; Disj; heap-disj; stack-disj)
open import Once.CCC.Machine.ValueRelocate {FS} {prog} using (module Relocate)
open import Once.CCC.Machine.FlatWords {FS} {prog} using (words)
open import Once.Denotation.ValueDomain using () renaming (⟦_⟧ᴰᴵ to ⟦_⟧)

------------------------------------------------------------------------
-- The value to put, in its register form (as `Output`/`Input1` hold it), valid
-- at the earlier allocator `a₀` in the current state.
------------------------------------------------------------------------
data Src (a₀ : AllocState {FS}) (s : LocState FS) : (C : IRTy) → ⟦ C ⟧ → StoredValue FS → Set where
  src-node   : ∀ {C c cl m} → IsNode C → Live a₀ cl → ValidAtWF m a₀ {C} c cl s → Src a₀ s C c (SV-Ptr cl)
  src-scalar : ∀ {C c} (fit : FitsInRegI C) → Src a₀ s C c (prim-sv fit c)
  -- (anywhere live: a heap block's cell or a frame slot, D374)
  src-flat   : ∀ {C c m sl} → IsFlat C → Live a₀ sl
             → ValidAtWF m a₀ {C} c sl s → Src a₀ s C c (SV-Ptr sl)
  src-unit   : ∀ {w} → Src a₀ s Unit tt w

-- the value stays valid while the cells `a₀` had live read the same
src-tr : ∀ {a₀ : AllocState {FS}} {s s′ : LocState FS} {C c w}
       → (∀ l → Live a₀ l → readLoc s′ l ≡ readLoc s l) → Src a₀ s C c w → Src a₀ s′ C c w
src-tr keep (src-node nd lv v) =
  src-node nd lv (validityWF-heap-transport (Live _) (λ _ b → b) keep (λ _ b → b) (λ _ _ ib → ib) _ _ lv v)
src-tr keep (src-scalar fit) = src-scalar fit
src-tr keep (src-flat fl lv v) =
  src-flat fl lv (validityWF-heap-transport (Live _) (λ _ b → b) keep (λ _ b → b) (λ _ _ ib → ib) _ _ lv v)
src-tr keep src-unit = src-unit

-- the destination's word `j`, from `off`, of the block `rd`
dst : HeapRef → ℕ → ℕ → ValueLocation FS
dst rd off j = AtDynamic (offsetHL (heap-loc rd 0) (off + j))

record PutOut (C : IRTy) (c : ⟦ C ⟧) (off : ℕ) (rd : HeapRef)
              (s : LocState FS) (alloc : AllocState {FS}) (r : LocState FS × AllocState {FS}) : Set where
  field
    alloc-eq : proj₂ r ≡ alloc
    live     : halted (proj₁ r) ≡ false
    other    : ∀ loc → (∀ j → j < size C → loc ≢ dst rd off j) → readLoc (proj₁ r) loc ≡ readLoc s loc
    cell     : CellAt alloc C c (AtDynamic (offsetHL (heap-loc rd 0) off)) (proj₁ r)
    -- `Input1` stays at the block, if that is where it was
    input1   : readReg (regs s) Input1 ≡ SV-Ptr (AtDynamic (heap-loc rd 0))
             → readReg (regs (proj₁ r)) Input1 ≡ SV-Ptr (AtDynamic (heap-loc rd 0))

private
  node-kind : ∀ {C : IRTy} → IsNode C → kind C ≡ word
  node-kind {μ-type _} _ = refl
  node-kind {ν-type _} _ = refl
  node-kind {_ ⇛ _}    _ = refl

  scalar-kind : ∀ {C : IRTy} → FitsInRegI C → kind C ≡ word
  scalar-kind fits-int   = refl
  scalar-kind fits-float = refl

  flat-kind : ∀ {C : IRTy} → IsFlat C → kind C ≡ flat
  flat-kind {Unit}   _ = refl
  flat-kind {_ * _}  _ = refl
  flat-kind {_ +ᵀ _} _ = refl

  node-size : ∀ {C : IRTy} → IsNode C → size C ≡ 1
  node-size {μ-type _} _ = refl
  node-size {ν-type _} _ = refl
  node-size {_ ⇛ _}    _ = refl

  scalar-size : ∀ {C : IRTy} → FitsInRegI C → size C ≡ 1
  scalar-size fits-int   = refl
  scalar-size fits-float = refl

  put-word : ∀ {C : IRTy} stash blk off → kind C ≡ word
           → put C stash blk off ≡ restore-input blk ∷ load-from-slot stash ∷ store-at off ∷ []
  put-word {C} stash blk off e rewrite e = refl

  put-flat : ∀ {C : IRTy} stash blk off → kind C ≡ flat → put C stash blk off ≡ copy-from stash blk off 0 (size C)
  put-flat {C} stash blk off e rewrite e = refl

------------------------------------------------------------------------
-- ONE WORD: `restore-input blk; load-from-slot stash; store-at off` is one write
------------------------------------------------------------------------
word-state : LocState FS → HeapRef → ℕ → StoredValue FS → LocState FS
word-state s rd off w =
  writeLoc (record s { regs = writeReg (writeReg (regs s) Input1 (SV-Ptr (AtDynamic (heap-loc rd 0)))) Output w })
           (AtDynamic (offsetHL (heap-loc rd 0) off)) w

word-exec : ∀ (stash blk off : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (rd : HeapRef) (w : StoredValue FS)
          → halted s ≡ false
          → readLoc s (AtStack (current-frame alloc) stash) ≡ just w
          → readLoc s (AtStack (current-frame alloc) blk) ≡ just (SV-Ptr (AtDynamic (heap-loc rd 0)))
          → InBlk alloc (AtDynamic (offsetHL (heap-loc rd 0) off))
          → exec-trace (restore-input blk ∷ load-from-slot stash ∷ store-at off ∷ []) s alloc
            ≡ (word-state s rd off w , alloc)
word-exec stash blk off s alloc rd w h rs rb ib rewrite h | rb | h | rs | ib = refl

------------------------------------------------------------------------
-- THE PUT
------------------------------------------------------------------------
module _ (C : IRTy) {c : ⟦ C ⟧} (stash blk off : ℕ) (s : LocState FS) (alloc a₀ : AllocState {FS})
         (w : StoredValue FS) (rd : HeapRef) (N : ℕ)
         (h     : halted s ≡ false)
         (rs    : readLoc s (AtStack (current-frame alloc) stash) ≡ just w)
         (rb    : readLoc s (AtStack (current-frame alloc) blk) ≡ just (SV-Ptr (AtDynamic (heap-loc rd 0))))
         (bft   : ∀ l → Live a₀ l → Live alloc l)
         (bk    : BlocksKept a₀ alloc)
         (fresh : ∀ o → Live a₀ (AtDynamic (heap-loc rd o)) → ⊥)
         (dlive : ∀ o → Live alloc (AtDynamic (heap-loc rd o)))
         (fits  : off + size C ≤ N)
         (din   : ∀ o → o < N → InBlk alloc (AtDynamic (heap-loc rd o)))
  where

  private
    off0 : ∀ j → offsetHL (heap-loc rd 0) j ≡ heap-loc rd j
    off0 j = cong (heap-loc rd) (+-identityʳ j)

    -- a destination word is in the block
    din′ : ∀ j → j < size C → InBlk alloc (dst rd off j)
    din′ j j< = subst (λ z → InBlk alloc (AtDynamic z)) (sym (off0 (off + j)))
                      (din (off + j) (≤-trans (subst (_≤ off + size C) (+-suc off j) (+-monoʳ-≤ off j<)) fits))

    -- the destination is not where anything `a₀` had live is
    not-dst : ∀ l → Live a₀ l → ∀ j → l ≢ dst rd off j
    not-dst l lv j e = fresh _ (subst (Live a₀) (trans e (cong AtDynamic (off0 (off + j)))) lv)

  -- a word kind: one write
  put-word-out : kind C ≡ word → size C ≡ 1
               → (∀ {s′} → readLoc s′ (AtDynamic (offsetHL (heap-loc rd 0) off)) ≡ just w → (∀ l → Live a₀ l → readLoc s′ l ≡ readLoc s l)
                         → CellAt alloc C c (AtDynamic (offsetHL (heap-loc rd 0) off)) s′)
               → PutOut C c off rd s alloc (exec-trace (put C stash blk off) s alloc)
  put-word-out kw sz mk =
    subst (λ t → PutOut C c off rd s alloc (exec-trace t s alloc)) (sym (put-word stash blk off kw))
      (subst (PutOut C c off rd s alloc) (sym (word-exec stash blk off s alloc rd w h rs rb
                                                 (subst (InBlk alloc) eq0 (din′ 0 p0))))
        record
          { alloc-eq = refl
          ; live     = trans (wl-halted s₁ (offsetHL (heap-loc rd 0) off) w) h
          ; other    = λ loc nd → trans (writeLoc-preserves-other s₁ _ loc w (λ e → nd 0 p0 (trans (sym e) (sym eq0))))
                                        (regs-mem s _ loc)
          ; cell     = mk (readLoc-writeLoc-same s₁ (AtDynamic (offsetHL (heap-loc rd 0) off)) w)
                          (λ l lv → trans (writeLoc-preserves-other s₁ _ l w (λ e → not-dst l lv 0 (trans (sym e) (sym eq0))))
                                          (regs-mem s _ l))
          ; input1   = λ _ → cong (λ q → readReg q Input1) (writeLoc-regs s₁ (AtDynamic (offsetHL (heap-loc rd 0) off)) w) })
    where
      p0 : 0 < size C
      p0 = subst (0 <_) (sym sz) (s≤s z≤n)
      eq0 : dst rd off 0 ≡ AtDynamic (offsetHL (heap-loc rd 0) off)
      eq0 = cong (λ z → AtDynamic (offsetHL (heap-loc rd 0) z)) (+-identityʳ off)
      s₁ = record s { regs = writeReg (writeReg (regs s) Input1 (SV-Ptr (AtDynamic (heap-loc rd 0)))) Output w }

  put-run : Src a₀ s C c w → PutOut C c off rd s alloc (exec-trace (put C stash blk off) s alloc)
  -- a node: its pointer word; the node stays where it is
  put-run (src-node {cl = cl} nd lv v) =
    put-word-out (node-kind nd) (node-size nd)
      (λ {s′} r keep → cell-ptr nd r
                         (bft cl lv)
                         (validityWF-heap-transport (Live a₀) (λ _ b → b) keep bft bk _ cl lv v))
  -- a scalar: its word
  put-run (src-scalar fit) =
    put-word-out (scalar-kind fit) (scalar-size fit)
      (λ {s′} r keep → cell-inline (rep-prim fit)
                         r)
  -- Unit: nothing
  put-run src-unit = record
    { alloc-eq = refl ; live = h ; other = λ _ _ → refl ; cell = cell-flat {mC = Heap} tt (λ ()) valid-unit-wf
    ; input1 = λ i1 → i1 }
  -- a flat value: its words, copied
  put-run (src-flat {sl = sl} fl lv v) =
    subst (λ t → PutOut C c off rd s alloc (exec-trace t s alloc)) (sym (put-flat stash blk off (flat-kind fl)))
      record
        { alloc-eq = proj₁ co
        ; live     = proj₁ (proj₂ co)
        ; other    = proj₂ (proj₂ (proj₂ co))
        ; cell     = cell-flat fl
                       (λ p → dlive _ , subst (λ z → InBlk alloc (AtDynamic (offsetHL (heap-loc rd 0) z))) (+-identityʳ off) (din′ 0 p))
                       (subst (λ z → ValidAtWF Heap alloc {C} c (AtDynamic z) s′) (sym (off0 off))
                          (RL.reloc-v C sl off agree fl fits v))
        ; input1   = copy-input1 stash blk off 0 (size C) s alloc sl dh ne h rs rb
                       (λ j j< → words C fl v j j<) (λ j j< → din′ j j<)
        }
    where
      dh = heap-loc rd 0
      -- the source is no word of the fresh block
      ne : Disj sl dh
      ne = disj sl lv
        where
          disj : ∀ l → Live a₀ l → Disj l dh
          disj (AtStack f k) _ = stack-disj f k dh
          disj (AtDynamic (heap-loc r o)) lv′ =
            heap-disj (heap-loc r o) dh (λ e → fresh o (subst (λ z → Live a₀ (AtDynamic (heap-loc z o))) e lv′))
      co = copy-run stash blk off 0 (size C) s alloc sl dh ne h rs rb
             (λ j j< → words C fl v j j<)
             (λ j j< → din′ j j<)
      s′ = proj₁ (exec-trace (copy-from stash blk off 0 (size C)) s alloc)
      keep : ∀ l → Live a₀ l → readLoc s′ l ≡ readLoc s l
      keep l b = proj₂ (proj₂ (proj₂ co)) l (λ j _ → not-dst l b j)
      module RL = Relocate {a₀} {alloc} {s} {s′} rd dlive keep bft bk N din
      agree : RL.Agree (size C) sl off
      agree = RL.mk-agree λ j j< →
        subst (λ z → readLoc s′ (AtDynamic (heap-loc rd z)) ≡ readLoc s (offsetLoc sl j))
              (trans (+-identityʳ (off + j)) (+-comm off j))
              (proj₁ (proj₂ (proj₂ co)) j j<)

------------------------------------------------------------------------
-- D382: THE PADDING FILL, `c` words from `from` of the block in `Input1`
------------------------------------------------------------------------
open import Once.CCC.Codegen.FlatLayout using (fill)

record FillOut (from c : ℕ) (rd : HeapRef) (s : LocState FS) (alloc : AllocState {FS})
               (r : LocState FS × AllocState {FS}) : Set where
  field
    alloc-eq : proj₂ r ≡ alloc
    live     : halted (proj₁ r) ≡ false
    input1   : readReg (regs (proj₁ r)) Input1 ≡ readReg (regs s) Input1
    written  : ∀ j → j < c → Written (proj₁ r) (dst rd from j)
    other    : ∀ loc → (∀ j → j < c → loc ≢ dst rd from j) → readLoc (proj₁ r) loc ≡ readLoc s loc

fill-exec : ∀ (from c : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (rd : HeapRef)
          → halted s ≡ false
          → readReg (regs s) Input1 ≡ SV-Ptr (AtDynamic (heap-loc rd 0))
          → (∀ j → j < c → InBlk alloc (dst rd from j))
          → FillOut from c rd s alloc (exec-trace (fill from c) s alloc)
fill-exec from zero s alloc rd h i1 ib =
  record { alloc-eq = refl ; live = h ; input1 = refl ; written = λ _ () ; other = λ _ _ → refl }
fill-exec from (suc c) s alloc rd h i1 ib =
  subst (FillOut from (suc c) rd s alloc) (sym step) out
  where
    tag = SV-Tag {FS} 0
    s₀  = record s { regs = writeReg (regs s) Output tag }
    here = AtDynamic (offsetHL (heap-loc rd 0) from)
    s₁  = writeLoc s₀ here tag
    eq0 : dst rd from 0 ≡ here
    eq0 = cong (λ z → AtDynamic (offsetHL (heap-loc rd 0) z)) (+-identityʳ from)
    ib0 : InBlk alloc here
    ib0 = subst (InBlk alloc) eq0 (ib 0 (s≤s z≤n))
    step : exec-trace (fill from (suc c)) s alloc ≡ exec-trace (fill (suc from) c) s₁ alloc
    step rewrite h | h | i1 | ib0 = refl
    h₁ : halted s₁ ≡ false
    h₁ = trans (wl-halted s₀ (offsetHL (heap-loc rd 0) from) tag) h
    i1₁ : readReg (regs s₁) Input1 ≡ SV-Ptr (AtDynamic (heap-loc rd 0))
    i1₁ = i1
    shift : ∀ j → dst rd (suc from) j ≡ dst rd from (suc j)
    shift j = cong (λ z → AtDynamic (offsetHL (heap-loc rd 0) z)) (sym (+-suc from j))
    ih = fill-exec (suc from) c s₁ alloc rd h₁ i1₁ (λ j j< → subst (InBlk alloc) (sym (shift j)) (ib (suc j) (s≤s j<)))
    s₁-other : ∀ loc → loc ≢ here → readLoc s₁ loc ≡ readLoc s loc
    s₁-other loc ne = trans (writeLoc-preserves-other s₀ here loc tag (λ e → ne (sym e))) (regs-mem s _ loc)
    later : ∀ j → j < c → here ≢ dst rd (suc from) j
    later j _ e = 0≢s (+-cancelˡ-≡ from 0 (suc j) (trans (+-identityʳ from) (off-inj (trans e (shift j)))))
      where
        off-of : ValueLocation FS → ℕ
        off-of (AtDynamic (heap-loc _ o)) = o
        off-of (AtStack _ _)              = 0
        off-inj : ∀ {a b} → AtDynamic {FS} (offsetHL (heap-loc rd 0) a) ≡ AtDynamic (offsetHL (heap-loc rd 0) b) → a ≡ b
        off-inj {a} {b} q = trans (sym (+-identityʳ a)) (trans (cong off-of q) (+-identityʳ b))
        0≢s : 0 ≡ suc j → ⊥
        0≢s ()
    out : FillOut from (suc c) rd s alloc (exec-trace (fill (suc from) c) s₁ alloc)
    out = record
      { alloc-eq = FillOut.alloc-eq ih
      ; live     = FillOut.live ih
      ; input1   = FillOut.input1 ih
      ; written  = λ { zero _ → _ , trans (FillOut.other ih (dst rd from 0) (λ j j< e → later j j< (trans (sym eq0) e)))
                                         (trans (cong (readLoc s₁) eq0) (readLoc-writeLoc-same s₀ here tag))
                     ; (suc j) (s≤s j<) → subst (Written (proj₁ (exec-trace (fill (suc from) c) s₁ alloc))) (shift j) (FillOut.written ih j j<) }
      ; other    = λ loc nd → trans (FillOut.other ih loc (λ j j< e → nd (suc j) (s≤s j<) (trans e (shift j))))
                                    (s₁-other loc (λ e → nd 0 (s≤s z≤n) (trans e (sym eq0))))
      }
