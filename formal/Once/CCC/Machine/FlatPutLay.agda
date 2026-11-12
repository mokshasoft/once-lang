-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatPutLay
--
-- plan 0.123 α2: WRITING A FORCED LAYER'S COMPONENT INTO A BLOCK — `FlatPut`
-- at `LayerV`. The re-suspension (`Resusp`) builds each layer it rebuilds by
-- `put`s of components that are themselves re-suspended layers: valid at
-- `LayerV G R`, whose recursive positions are `R` (an `Ana` suspension), not
-- at `ValidAtWF`. The run is `FlatPut`'s (`word-exec`, `FlatCopy.copy-run`);
-- what differs is the relation the destination is valid at, which moves by
-- `Relocate.Lay` and `R-tr`.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractTrace)

module Once.CCC.Machine.FlatPutLay {FS : FrameSemantics} {prog : AbstractTrace} where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-comm; +-monoʳ-≤; ≤-trans; +-suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapRef; HeapLocation; heap-loc; offsetHL)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap; AbstractTrace)
open MemOps {FS}
open AbstractExec {FS} using (exec-trace)
open import Once.CCC.Machine.SMPrimitives using (module MemoryOps)
open MemoryOps {FS} using (readLoc-writeLoc-same)
open AllocState using (current-frame)
open LocState using (halted; regs)
open import Once.IR using (AllocMode; Stack; Heap)
open import Once.IRTy using (IRTy; Unit; ν-type; μ-type; _⇛[_]_; _*_; FitsInRegI; fits-int; fits-float; IRFunctor; WellFormedFI; ⟦_⟧TI) renaming (_+_ to _+ᵀ_)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (Kind; word; flat; kind; put; copy-from)
open import Once.CCC.Machine.ValueRel
open ClosureWellFormedBase {FS}
open import Once.CCC.Machine.FlatCopy {FS} using (copy-run; copy-input1; wl-halted; regs-mem; Disj; heap-disj; stack-disj)
open import Once.CCC.Machine.ValueRelocate {FS} {prog} using (module Relocate)
open import Once.CCC.Machine.FlatWords {FS} {prog} using (module LayWords)
open import Once.CCC.Machine.FlatPut {FS} {prog} using (dst; word-state; word-exec)
open import Data.List using (_++_)
open import Once.Denotation.ValueDomain using () renaming (⟦_⟧ᴰᴵ to ⟦_⟧)
open import Once.CCC.Machine.SMCore using (restore-input; load-from-slot; store-at)

module PutLay {F : IRFunctor} (R : VTy (ν-type F))
  -- an `R` stays one while what was live stays live, unchanged, its blocks kept
  (R-tr : ∀ {a a′ : AllocState {FS}} {s s′ : LocState FS}
        → (∀ l → Live a l → Live a′ l) → (∀ l → Live a l → readLoc s′ l ≡ readLoc s l) → BlocksKept a a′
        → ∀ {m v l} → R m a v l s → R m a′ v l s′) where

  private
    X = ν-type F

  -- a re-suspended component, as a value to put: a ν position's pointer, a
  -- scalar's word, a flat layer where it lies, or a `Unit` (no words)
  data LSrc (a₀ : AllocState {FS}) (s : LocState FS) {G : IRFunctor} (wG : WellFormedFI G)
            : ⟦ ⟦ G ⟧TI X ⟧ → StoredValue FS → Set where
    ls-node   : ∀ {v cl m} → IsNode (⟦ G ⟧TI X) → Live a₀ cl → LayerV G {X} R m a₀ v cl s → LSrc a₀ s wG v (SV-Ptr cl)
    ls-scalar : ∀ {v} (fit : FitsInRegI (⟦ G ⟧TI X)) → LSrc a₀ s wG v (prim-sv fit v)
    ls-flat   : ∀ {v sl m} → IsFlat (⟦ G ⟧TI X) → Live a₀ sl → LayerV G {X} R m a₀ v sl s → LSrc a₀ s wG v (SV-Ptr sl)
    ls-unit   : ∀ {v w} → ⟦ G ⟧TI X ≡ Unit → (∀ {a s′ l} → LayerV G {X} R Heap a v l s′) → LSrc a₀ s wG v w

  record PutOutL {G : IRFunctor} (wG : WellFormedFI G) (c : ⟦ ⟦ G ⟧TI X ⟧) (off : ℕ) (rd : HeapRef)
                 (a₀ : AllocState {FS}) (s : LocState FS) (alloc : AllocState {FS})
                 (r : LocState FS × AllocState {FS}) : Set where
    field
      alloc-eq : proj₂ r ≡ alloc
      live     : halted (proj₁ r) ≡ false
      other    : ∀ loc → (∀ j → j < size (⟦ G ⟧TI X) → loc ≢ dst rd off j) → readLoc (proj₁ r) loc ≡ readLoc s loc
      cell     : CellAtP {⟦ G ⟧TI X} (LayerV G {X} R) alloc c (AtDynamic (offsetHL (heap-loc rd 0) off)) (proj₁ r)
      cell-at  : ∀ (s″ : LocState FS)
               → (∀ j → j < size (⟦ G ⟧TI X) → readLoc s″ (dst rd off j) ≡ readLoc (proj₁ r) (dst rd off j))
               → (∀ l → Live a₀ l → readLoc s″ l ≡ readLoc s l)
               → CellAtP {⟦ G ⟧TI X} (LayerV G {X} R) alloc c (AtDynamic (offsetHL (heap-loc rd 0) off)) s″
      input1   : readReg (regs s) Input1 ≡ SV-Ptr (AtDynamic (heap-loc rd 0))
               → readReg (regs (proj₁ r)) Input1 ≡ SV-Ptr (AtDynamic (heap-loc rd 0))

  private
    node-kind : ∀ {C : IRTy} → IsNode C → kind C ≡ word
    node-kind {μ-type _} _ = refl
    node-kind {ν-type _} _ = refl
    node-kind {_ ⇛[ _ ] _} _ = refl

    scalar-kind : ∀ {C : IRTy} → FitsInRegI C → kind C ≡ word
    scalar-kind fits-int   = refl
    scalar-kind fits-float = refl

    flat-kind : ∀ {C : IRTy} → IsFlat C → kind C ≡ flat
    flat-kind {Unit} _ = refl
    flat-kind {_ * _} _ = refl
    flat-kind {_ +ᵀ _} _ = refl

    node-size : ∀ {C : IRTy} → IsNode C → size C ≡ 1
    node-size {μ-type _} _ = refl
    node-size {ν-type _} _ = refl
    node-size {_ ⇛[ _ ] _} _ = refl

    scalar-size : ∀ {C : IRTy} → FitsInRegI C → size C ≡ 1
    scalar-size fits-int   = refl
    scalar-size fits-float = refl

    put-word : ∀ {C : IRTy} stash blk off → kind C ≡ word
             → put C stash blk off ≡ restore-input blk ∷ load-from-slot stash ∷ store-at off ∷ []
    put-word {C} stash blk off e rewrite e = refl

    put-flat : ∀ {C : IRTy} stash blk off → kind C ≡ flat → put C stash blk off ≡ copy-from stash blk off 0 (size C)
    put-flat {C} stash blk off e rewrite e = refl

    put-unit : ∀ {C : IRTy} stash blk off → C ≡ Unit → put C stash blk off ≡ []
    put-unit stash blk off refl = refl

  ----------------------------------------------------------------------
  -- THE PUT (`FlatPut.put-run`'s parameters, at a layer `wG`)
  ----------------------------------------------------------------------
  module _ {G : IRFunctor} (wG : WellFormedFI G) {c : ⟦ ⟦ G ⟧TI X ⟧} (stash blk off : ℕ) (s : LocState FS)
           (alloc a₀ : AllocState {FS}) (w : StoredValue FS) (rd : HeapRef) (N : ℕ)
           (h     : halted s ≡ false)
           (rs    : readLoc s (AtStack (current-frame alloc) stash) ≡ just w)
           (rb    : readLoc s (AtStack (current-frame alloc) blk) ≡ just (SV-Ptr (AtDynamic (heap-loc rd 0))))
           (bft   : ∀ l → Live a₀ l → Live alloc l)
           (bk    : BlocksKept a₀ alloc)
           (fresh : ∀ o → Live a₀ (AtDynamic (heap-loc rd o)) → ⊥)
           (dlive : ∀ o → Live alloc (AtDynamic (heap-loc rd o)))
           (fits  : off + size (⟦ G ⟧TI X) ≤ N)
           (din   : ∀ o → o < N → InBlk alloc (AtDynamic (heap-loc rd o)))
    where

    private
      T = ⟦ G ⟧TI X
      Out = PutOutL wG c off rd a₀ s alloc

      off0 : ∀ j → offsetHL (heap-loc rd 0) j ≡ heap-loc rd j
      off0 j = cong (heap-loc rd) (+-identityʳ j)

      din′ : ∀ j → j < size T → InBlk alloc (dst rd off j)
      din′ j j< = subst (λ z → InBlk alloc (AtDynamic z)) (sym (off0 (off + j)))
                        (din (off + j) (≤-trans (subst (_≤ off + size T) (+-suc off j) (+-monoʳ-≤ off j<)) fits))

      not-dst : ∀ l → Live a₀ l → ∀ j → l ≢ dst rd off j
      not-dst l lv j e = fresh _ (subst (Live a₀) (trans e (cong AtDynamic (off0 (off + j)))) lv)

      here-in : 0 < size T → Here alloc (AtDynamic (offsetHL (heap-loc rd 0) off))
      here-in p = dlive _ , subst (λ z → InBlk alloc (AtDynamic (offsetHL (heap-loc rd 0) z))) (+-identityʳ off) (din′ 0 p)

    -- a word kind: one write
    put-word-out : kind T ≡ word → size T ≡ 1
                 → (∀ {s′} → readLoc s′ (AtDynamic (offsetHL (heap-loc rd 0) off)) ≡ just w
                           → (∀ l → Live a₀ l → readLoc s′ l ≡ readLoc s l)
                           → CellAtP {T} (LayerV G {X} R) alloc c (AtDynamic (offsetHL (heap-loc rd 0) off)) s′)
                 → Out (exec-trace (put T stash blk off) s alloc)
    put-word-out kw sz mk =
      subst (λ t → Out (exec-trace t s alloc)) (sym (put-word {T} stash blk off kw))
        (subst Out (sym (word-exec stash blk off s alloc rd w h rs rb (subst (InBlk alloc) eq0 (din′ 0 p0))))
          record
            { alloc-eq = refl
            ; live     = trans (wl-halted s₁ (offsetHL (heap-loc rd 0) off) w) h
            ; other    = λ loc nd → trans (writeLoc-preserves-other s₁ _ loc w (λ e → nd 0 p0 (trans (sym e) (sym eq0))))
                                          (regs-mem s _ loc)
            ; cell     = mk (readLoc-writeLoc-same s₁ (AtDynamic (offsetHL (heap-loc rd 0) off)) w)
                            (λ l lv → trans (writeLoc-preserves-other s₁ _ l w (λ e → not-dst l lv 0 (trans (sym e) (sym eq0))))
                                            (regs-mem s _ l))
            ; cell-at  = λ s″ eqd keep″ →
                mk (trans (subst (λ z → readLoc s″ z ≡ readLoc (writeLoc s₁ (AtDynamic (offsetHL (heap-loc rd 0) off)) w) z)
                                 eq0 (eqd 0 p0))
                          (readLoc-writeLoc-same s₁ (AtDynamic (offsetHL (heap-loc rd 0) off)) w))
                   keep″
            ; input1   = λ _ → cong (λ q → readReg q Input1) (writeLoc-regs s₁ (AtDynamic (offsetHL (heap-loc rd 0) off)) w) })
      where
        p0 : 0 < size T
        p0 = subst (0 <_) (sym sz) (s≤s z≤n)
        eq0 : dst rd off 0 ≡ AtDynamic (offsetHL (heap-loc rd 0) off)
        eq0 = cong (λ z → AtDynamic (offsetHL (heap-loc rd 0) z)) (+-identityʳ off)
        s₁ = record s { regs = writeReg (writeReg (regs s) Input1 (SV-Ptr (AtDynamic (heap-loc rd 0)))) Output w }

    put-lay-run : LSrc a₀ s wG c w → Out (exec-trace (put T stash blk off) s alloc)
    -- a ν position: its pointer word; the suspension stays where it is
    put-lay-run (ls-node {cl = cl} nd lv v) =
      put-word-out (node-kind nd) (node-size nd)
        node-cell
      where
        node-cell : ∀ {s′} → readLoc s′ (AtDynamic (offsetHL (heap-loc rd 0) off)) ≡ just (SV-Ptr cl)
                  → (∀ l → Live a₀ l → readLoc s′ l ≡ readLoc s l)
                  → CellAtP {T} (LayerV G {X} R) alloc c (AtDynamic (offsetHL (heap-loc rd 0) off)) s′
        node-cell {s′} r keep = cell-ptr nd r (bft cl lv) (RL.lay-tr wG nd lv v)
          where module RL = Relocate.Lay {a₀} {alloc} {s} {s′} rd dlive keep bft bk N din R (λ _ q → R-tr bft keep bk q)
    -- a scalar: its word
    put-lay-run (ls-scalar fit) =
      put-word-out (scalar-kind fit) (scalar-size fit) (λ r _ → cell-inline (rep-prim fit) r)
    -- Unit: nothing
    put-lay-run (ls-unit e mk) =
      subst (λ t → Out (exec-trace t s alloc)) (sym (put-unit stash blk off e))
        record
          { alloc-eq = refl ; live = h ; other = λ _ _ → refl
          ; cell     = cell-flat fl (λ p → ⊥-elim (z0 p)) mk
          ; cell-at  = λ _ _ _ → cell-flat fl (λ p → ⊥-elim (z0 p)) mk
          ; input1   = λ i1 → i1 }
      where
        fl : IsFlat T
        fl = subst IsFlat (sym e) tt
        z0 : 0 < size T → ⊥
        z0 p with subst (0 <_) (cong size e) p
        ... | ()
    -- a flat layer: its words, copied
    put-lay-run (ls-flat {sl = sl} fl lv v) =
      subst (λ t → Out (exec-trace t s alloc)) (sym (put-flat {T} stash blk off (flat-kind fl)))
        record
          { alloc-eq = proj₁ co
          ; live     = proj₁ (proj₂ co)
          ; other    = proj₂ (proj₂ (proj₂ co))
          ; cell     = cell-at′ s′ (λ _ _ → refl) keep
          ; cell-at  = cell-at′
          ; input1   = copy-input1 stash blk off 0 (size T) s alloc sl dh ne h rs rb
                         (λ j j< → LayWords.lay-words R wG fl v j j<) (λ j j< → din′ j j<)
          }
      where
        dh = heap-loc rd 0
        ne : Disj sl dh
        ne = disj sl lv
          where
            disj : ∀ l → Live a₀ l → Disj l dh
            disj (AtStack f k) _ = stack-disj f k dh
            disj (AtDynamic (heap-loc r o)) lv′ =
              heap-disj (heap-loc r o) dh (λ e → fresh o (subst (λ z → Live a₀ (AtDynamic (heap-loc z o))) e lv′))
        co = copy-run stash blk off 0 (size T) s alloc sl dh ne h rs rb
               (λ j j< → LayWords.lay-words R wG fl v j j<)
               (λ j j< → din′ j j<)
        s′ = proj₁ (exec-trace (copy-from stash blk off 0 (size T)) s alloc)
        keep : ∀ l → Live a₀ l → readLoc s′ l ≡ readLoc s l
        keep l b = proj₂ (proj₂ (proj₂ co)) l (λ j _ → not-dst l b j)
        cell-at′ : ∀ (s″ : LocState FS)
                 → (∀ j → j < size T → readLoc s″ (dst rd off j) ≡ readLoc s′ (dst rd off j))
                 → (∀ l → Live a₀ l → readLoc s″ l ≡ readLoc s l)
                 → CellAtP {T} (LayerV G {X} R) alloc c (AtDynamic (offsetHL (heap-loc rd 0) off)) s″
        cell-at′ s″ eqd keep″ =
          cell-flat fl here-in
            (subst (λ z → LayerV G {X} R Heap alloc c (AtDynamic z) s″) (sym (off0 off))
               (RL″.reloc-lay wG sl off agree″ fl fits v))
          where
            module RL″ = Relocate.Lay {a₀} {alloc} {s} {s″} rd dlive keep″ bft bk N din R (λ _ q → R-tr bft keep″ bk q)
            agree″ : Relocate.Agree {a₀} {alloc} {s} {s″} rd dlive keep″ bft bk N din (size T) sl off
            agree″ = Relocate.mk-agree λ j j< →
              subst (λ z → readLoc s″ (AtDynamic (heap-loc rd z)) ≡ readLoc s (offsetLoc sl j))
                    (trans (+-identityʳ (off + j)) (+-comm off j))
                    (trans (eqd j j<) (proj₁ (proj₂ (proj₂ co)) j j<))
