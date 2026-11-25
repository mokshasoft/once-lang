-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandStep — the renaming through memory (D470, 3c3b).
--
-- The memory half of the expansion's simulation, below the instructions: the
-- renaming commutes with offsets and fixes every non-pointer value; a write at a
-- live cell, done at its renamed cell, keeps the live cells related (the
-- renaming is injective on the live blocks) and leaves every other expanded word
-- — the record, the sentinel, the free blocks — as it was.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandStep {FS : FrameSemantics} where

open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef; offsetHL; _≟HL_)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Codegen.AllocExpandRen {FS} using (ref-of; rhl; rloc; rv; blk)
open MemOps {FS} using (writeHeapMem; writeHeapMem-aux)

------------------------------------------------------------------------
-- The renaming on addresses and values
------------------------------------------------------------------------

rhl-off : ∀ ρ (hl : HeapLocation) k → rhl ρ (offsetHL hl k) ≡ offsetHL (rhl ρ hl) k
rhl-off ρ (heap-loc r o) k = refl

ref-off : ∀ (hl : HeapLocation) k → ref-of (offsetHL hl k) ≡ ref-of hl
ref-off (heap-loc r o) k = refl

-- the renamed cell of a block is the block's renamed ref at the same offset
rhl-at : ∀ ρ r o → rhl ρ (heap-loc (mkHeapRef r) o) ≡ heap-loc (mkHeapRef (ρ r)) o
rhl-at ρ r o = refl

-- distinct live cells stay distinct (the renaming injective on their refs)
rhl-apart : ∀ ρ (hl hl′ : HeapLocation) → (ref-of hl ≡ ref-of hl′ → ¬ HeapLocation.heap-offset hl ≡ HeapLocation.heap-offset hl′)
          → (ρ (ref-of hl) ≡ ρ (ref-of hl′) → ref-of hl ≡ ref-of hl′)
          → ¬ rhl ρ hl ≡ rhl ρ hl′
rhl-apart ρ (heap-loc (mkHeapRef r) o) (heap-loc (mkHeapRef r′) o′) off inj e =
  off (inj (cong (λ x → HeapRef.ref-id (HeapLocation.heap-ref x)) e)) (cong HeapLocation.heap-offset e)

-- cells are equal when their refs and offsets are
hl-eq : ∀ (hl hl′ : HeapLocation) → ref-of hl ≡ ref-of hl′ → HeapLocation.heap-offset hl ≡ HeapLocation.heap-offset hl′ → hl ≡ hl′
hl-eq (heap-loc (mkHeapRef r) o) (heap-loc (mkHeapRef .r) .o) refl refl = refl

------------------------------------------------------------------------
-- A write, done on both sides
------------------------------------------------------------------------

module _ (ρ : ℕ → ℕ) (Lv : ℕ → Set)
         (inj : ∀ r r′ → Lv r → Lv r′ → ρ r ≡ ρ r′ → r ≡ r′) where

  -- the live cells of `h` are `g`'s at their renamed cells
  HeapR : HeapMem FS → HeapMem FS → Set
  HeapR h g = ∀ hl v → Lv (ref-of hl) → h hl ≡ just v → g (rhl ρ hl) ≡ just (rv ρ v)

  private
    w-same : ∀ (h : HeapMem FS) hl v → writeHeapMem h hl v hl ≡ just v
    w-same h hl v = w-same-aux (hl ≟HL hl)
      where
        w-same-aux : ∀ (d : Relation.Nullary.Dec (hl ≡ hl)) → writeHeapMem-aux {hl = hl} {hl' = hl} d (h hl) v ≡ just v
        w-same-aux (yes _) = refl
        w-same-aux (no ne) = Data.Empty.⊥-elim (ne refl)
          where import Data.Empty

    w-other : ∀ (h : HeapMem FS) hl hl′ v → ¬ hl ≡ hl′ → writeHeapMem h hl v hl′ ≡ h hl′
    w-other h hl hl′ v ne = w-other-aux (hl ≟HL hl′)
      where
        w-other-aux : ∀ (d : Relation.Nullary.Dec (hl ≡ hl′)) → writeHeapMem-aux {hl = hl} {hl' = hl′} d (h hl′) v ≡ h hl′
        w-other-aux (yes e) = Data.Empty.⊥-elim (ne e)
          where import Data.Empty
        w-other-aux (no _)  = refl

  -- ★ a write at a live cell, and at its renamed cell, keeps the live cells related
  heap-write : ∀ {h g} hl₀ v → Lv (ref-of hl₀) → HeapR h g
             → HeapR (writeHeapMem h hl₀ v) (writeHeapMem g (rhl ρ hl₀) (rv ρ v))
  heap-write {h} {g} hl₀ v₀ lv₀ R hl v lv e = go (hl₀ ≟HL hl)
    where
      go : Relation.Nullary.Dec (hl₀ ≡ hl) → writeHeapMem g (rhl ρ hl₀) (rv ρ v₀) (rhl ρ hl) ≡ just (rv ρ v)
      go (yes refl) = trans (w-same g (rhl ρ hl₀) (rv ρ v₀)) (cong (λ z → just (rv ρ z)) (just-inj (trans (sym (w-same h hl₀ v₀)) e)))
        where
          just-inj : ∀ {a b : StoredValue FS} → just a ≡ just b → a ≡ b
          just-inj refl = refl
      go (no ne) =
        trans (w-other g (rhl ρ hl₀) (rhl ρ hl) (rv ρ v₀)
                 (rhl-apart ρ hl₀ hl (λ er eo → ne (hl-eq hl₀ hl er eo)) (inj (ref-of hl₀) (ref-of hl) lv₀ lv)))
              (R hl v lv (trans (sym (w-other h hl₀ hl v₀ ne)) e))

  -- ★ a write at a renamed live cell leaves an expanded word no live block is renamed to
  heap-write-off : ∀ (g : HeapMem FS) hl₀ v (q : HeapLocation) → Lv (ref-of hl₀)
                 → (∀ r → Lv r → ¬ ρ r ≡ ref-of q)
                 → writeHeapMem g (rhl ρ hl₀) v q ≡ g q
  heap-write-off g hl₀ v q lv₀ miss = w-other g (rhl ρ hl₀) q v (λ e → miss (ref-of hl₀) lv₀ (cong ref-of e))

------------------------------------------------------------------------
-- ★ The LocState relation: registers and stack by the renaming, the live
-- heap by `HeapR`, the flags and the log equal
------------------------------------------------------------------------

open MemOps {FS} using (writeStackMem; writeStackMem-aux; writeLocToStack; readLoc; writeLoc)
open import Data.Bool using (Bool)
open import Data.List using (List)
open import Once.IR.Semantics.Event using (SigOpEvent)

open import Once.Type using (FitsInReg)

module L (ρ : ℕ → ℕ) (Lv : ℕ → Set) (inj : ∀ r r′ → Lv r → Lv r′ → ρ r ≡ ρ r′ → r ≡ r′) where

  record LRel (s t : LocState FS) : Set where
    field
      l-regs  : ∀ r → readReg (LocState.regs t) r ≡ rv ρ (readReg (LocState.regs s) r)
      l-stack : ∀ f k → LocState.stackMem t f k ≡ Data.Maybe.map (rv ρ) (LocState.stackMem s f k)
      l-heap  : HeapR ρ Lv inj (LocState.heapMem s) (LocState.heapMem t)
      l-live  : ∀ hl v → LocState.heapMem s hl ≡ just v → Lv (ref-of hl)
      l-halt  : LocState.halted t ≡ LocState.halted s
      l-fault : LocState.faulted t ≡ LocState.faulted s
      l-left  : LocState.left t ≡ LocState.left s
      l-log   : LocState.ev-log t ≡ LocState.ev-log s
  open LRel public

  -- a register written on both sides, with the renamed value
  lrel-reg : ∀ {s t} r v → LRel s t
           → LRel (record s { regs = writeReg (LocState.regs s) r v }) (record t { regs = writeReg (LocState.regs t) r (rv ρ v) })
  lrel-reg {s} {t} r v R = record
    { l-regs = regs′ r ; l-stack = l-stack R ; l-heap = l-heap R ; l-live = l-live R
    ; l-halt = l-halt R ; l-fault = l-fault R ; l-left = l-left R ; l-log = l-log R }
    where
      regs′ : ∀ r₀ r′ → readReg (writeReg (LocState.regs t) r₀ (rv ρ v)) r′ ≡ rv ρ (readReg (writeReg (LocState.regs s) r₀ v) r′)
      regs′ Input1 Input1 = refl
      regs′ Input1 Output = l-regs R Output
      regs′ Output Input1 = l-regs R Input1
      regs′ Output Output = refl

  -- a fault on both sides
  lrel-fault : ∀ {s t} → LRel s t → LRel (record s { halted = Data.Bool.true ; faulted = Data.Bool.true })
                                          (record t { halted = Data.Bool.true ; faulted = Data.Bool.true })
  lrel-fault R = record
    { l-regs = l-regs R ; l-stack = l-stack R ; l-heap = l-heap R ; l-live = l-live R
    ; l-halt = refl ; l-fault = refl ; l-left = l-left R ; l-log = l-log R }
    where import Data.Bool

  -- a stack slot written on both sides
  lrel-stack-write : ∀ {s t} f k v → LRel s t
                   → LRel (writeLocToStack s f k v) (writeLocToStack t f k (rv ρ v))
  lrel-stack-write {s} {t} f k v R = record
    { l-regs = l-regs R ; l-stack = stk ; l-heap = l-heap R ; l-live = l-live R
    ; l-halt = l-halt R ; l-fault = l-fault R ; l-left = l-left R ; l-log = l-log R }
    where
      stk : ∀ f′ k′ → writeStackMem (LocState.stackMem t) f k (rv ρ v) f′ k′
                    ≡ Data.Maybe.map (rv ρ) (writeStackMem (LocState.stackMem s) f k v f′ k′)
      stk f′ k′ = aux (FrameSemantics._≟F_ FS f f′) (k Data.Nat.≟ k′)
        where
          aux : ∀ (df : Relation.Nullary.Dec (f ≡ f′)) (dk : Relation.Nullary.Dec (k ≡ k′))
              → writeStackMem-aux df dk (LocState.stackMem t f′ k′) (rv ρ v)
                ≡ Data.Maybe.map (rv ρ) (writeStackMem-aux df dk (LocState.stackMem s f′ k′) v)
          aux (no _)  _       = l-stack R f′ k′
          aux (yes _) (yes _) = refl
          aux (yes _) (no _)  = l-stack R f′ k′

  -- a slot's value, read on both sides
  read-stack : ∀ {s t} f k → LRel s t → readLoc t (AtStack f k) ≡ Data.Maybe.map (rv ρ) (readLoc s (AtStack f k))
  read-stack f k R = l-stack R f k

  ------------------------------------------------------------------------
  -- The register and slot instructions commute with the renaming (the frames
  -- are the same on both sides)
  ------------------------------------------------------------------------

  open AbstractExec {FS} using (exec-load-from-slot-with-value; exec-restore-input-with-value; exec-abstract)

  load-slot-rel : ∀ {s t} mv al al′ → LRel s t
                → LRel (proj₁ (exec-load-from-slot-with-value mv s al)) (proj₁ (exec-load-from-slot-with-value (Data.Maybe.map (rv ρ) mv) t al′))
  load-slot-rel (just v) al al′ R = lrel-reg Output v R
  load-slot-rel nothing  al al′ R = lrel-fault R

  restore-rel : ∀ {s t} mv al al′ → LRel s t
              → LRel (proj₁ (exec-restore-input-with-value mv s al)) (proj₁ (exec-restore-input-with-value (Data.Maybe.map (rv ρ) mv) t al′))
  restore-rel (just v) al al′ R = lrel-reg Input1 v R
  restore-rel nothing  al al′ R = lrel-fault R

  -- the renamed value of a register, as the expanded side reads it
  reg-is : ∀ {s t} r → LRel s t → readReg (LocState.regs t) r ≡ rv ρ (readReg (LocState.regs s) r)
  reg-is r R = l-regs R r

  -- a register's value replaced by an equal one
  subst-reg : ∀ {s t} r {v w} → v ≡ w → LRel s (record t { regs = writeReg (LocState.regs t) r v })
            → LRel s (record t { regs = writeReg (LocState.regs t) r w })
  subst-reg r refl R = R

  -- the instructions whose effect is the registers and the current frame's slots
  module Slots {al al′ : AllocState {FS}} (cf : AllocState.current-frame al′ ≡ AllocState.current-frame al) where
    private
      cf′ = AllocState.current-frame al

    mov-out : ∀ {s t} → LRel s t → LRel (proj₁ (exec-abstract mov-to-output s al)) (proj₁ (exec-abstract mov-to-output t al′))
    mov-out {s} {t} R = subst-reg {t = t} Output (sym (reg-is Input1 R)) (lrel-reg Output (readReg (LocState.regs s) Input1) R)

    mov-in : ∀ {s t} → LRel s t → LRel (proj₁ (exec-abstract mov-to-input s al)) (proj₁ (exec-abstract mov-to-input t al′))
    mov-in {s} {t} R = subst-reg {t = t} Input1 (sym (reg-is Output R)) (lrel-reg Input1 (readReg (LocState.regs s) Output) R)

    from-slot : ∀ {s t} k → LRel s t → LRel (proj₁ (exec-abstract (load-from-slot k) s al)) (proj₁ (exec-abstract (load-from-slot k) t al′))
    from-slot {s} {t} k R =
      Relation.Binary.PropositionalEquality.subst (λ mv → LRel (proj₁ (exec-load-from-slot-with-value (readLoc s (AtStack cf′ k)) s al))
                                                              (proj₁ (exec-load-from-slot-with-value mv t al′)))
        (sym (trans (cong (λ f → readLoc t (AtStack f k)) cf) (read-stack cf′ k R)))
        (load-slot-rel (readLoc s (AtStack cf′ k)) al al′ R)

    restore : ∀ {s t} k → LRel s t → LRel (proj₁ (exec-abstract (restore-input k) s al)) (proj₁ (exec-abstract (restore-input k) t al′))
    restore {s} {t} k R =
      Relation.Binary.PropositionalEquality.subst (λ mv → LRel (proj₁ (exec-restore-input-with-value (readLoc s (AtStack cf′ k)) s al))
                                                              (proj₁ (exec-restore-input-with-value mv t al′)))
        (sym (trans (cong (λ f → readLoc t (AtStack f k)) cf) (read-stack cf′ k R)))
        (restore-rel (readLoc s (AtStack cf′ k)) al al′ R)

    to-slot : ∀ {s t} k → LRel s t → LRel (proj₁ (exec-abstract (store-at-slot k) s al)) (proj₁ (exec-abstract (store-at-slot k) t al′))
    to-slot {s} {t} k R =
      Relation.Binary.PropositionalEquality.subst₂ (λ f v → LRel (writeLocToStack s cf′ k (readReg (LocState.regs s) Output)) (writeLocToStack t f k v))
        (sym cf) (sym (reg-is Output R))
        (lrel-stack-write cf′ k (readReg (LocState.regs s) Output) R)

    lea : ∀ {s t} k → LRel s t → LRel (proj₁ (exec-abstract (lea-slot k) s al)) (proj₁ (exec-abstract (lea-slot k) t al′))
    lea {s} {t} k R =
      Relation.Binary.PropositionalEquality.subst (λ f → LRel (record s { regs = writeReg (LocState.regs s) Output (SV-Ptr (AtStack cf′ k)) })
                                                             (record t { regs = writeReg (LocState.regs t) Output (SV-Ptr (AtStack f k)) }))
        (sym cf) (lrel-reg Output (SV-Ptr (AtStack cf′ k)) R)

  -- constants: the renaming fixes literals, tags and code
  const-rel : ∀ {s t} v → rv ρ v ≡ v → LRel s t
            → LRel (record s { regs = writeReg (LocState.regs s) Output v }) (record t { regs = writeReg (LocState.regs t) Output v })
  const-rel {s} {t} v fix R = subst-reg {t = t} Output fix (lrel-reg Output v R)

  ------------------------------------------------------------------------
  -- The gates, on renamed pointers
  ------------------------------------------------------------------------

  open ExecFinal {FS} using (frame-gate; heap-gate; live-frames; exec-load-at-resolved; exec-load-with-value)

  as-loc-rv : ∀ v → sv-as-loc (rv ρ v) ≡ Data.Maybe.map (rloc ρ) (sv-as-loc v)
  as-loc-rv (SV-Ptr l)   = refl
  as-loc-rv (SV-Tag _)   = refl
  as-loc-rv (SV-Lit _ _) = refl
  as-loc-rv (SV-Code _)  = refl

  frame-gate-rv : ∀ (al al′ : AllocState {FS}) k → live-frames al′ ≡ live-frames al → ∀ ml
                → frame-gate al′ k (Data.Maybe.map (rloc ρ) ml) ≡ Data.Maybe.map (rloc ρ) (frame-gate al k ml)
  frame-gate-rv al al′ k lf (just (AtStack f j)) = stk (Data.Bool.Bool) (cong (λ w → ExecFinal.in-window {FS} w f (k + j)) lf)
    where
      import Data.Bool
      stk : Set → ExecFinal.in-window {FS} (live-frames al′) f (k + j) ≡ ExecFinal.in-window {FS} (live-frames al) f (k + j)
          → ExecFinal.stack-gate {FS} (ExecFinal.in-window {FS} (live-frames al′) f (k + j)) (AtStack f j)
            ≡ Data.Maybe.map (rloc ρ) (ExecFinal.stack-gate {FS} (ExecFinal.in-window {FS} (live-frames al) f (k + j)) (AtStack f j))
      stk _ e = trans (cong (λ b → ExecFinal.stack-gate {FS} b (AtStack f j)) e) (sg (ExecFinal.in-window {FS} (live-frames al) f (k + j)))
        where
          sg : ∀ b → ExecFinal.stack-gate {FS} b (AtStack f j) ≡ Data.Maybe.map (rloc ρ) (ExecFinal.stack-gate {FS} b (AtStack f j))
          sg Data.Bool.true  = refl
          sg Data.Bool.false = refl
  frame-gate-rv al al′ k lf (just (AtDynamic hl)) = refl
  frame-gate-rv al al′ k lf nothing = refl

  heap-gate-rv : ∀ ml → heap-gate (Data.Maybe.map (rloc ρ) ml) ≡ Data.Maybe.map (rloc ρ) (heap-gate ml)
  heap-gate-rv (just (AtStack _ _))  = refl
  heap-gate-rv (just (AtDynamic _))  = refl
  heap-gate-rv nothing               = refl

  ------------------------------------------------------------------------
  -- ★ A load at an offset: the primitive's, if it does not fault, read a held
  -- cell, whose renamed cell holds the renamed value
  ------------------------------------------------------------------------

  load-val-rel : ∀ {s t} mv mw → (∀ v → mv ≡ just v → mw ≡ just (rv ρ v)) → LocState.faulted (exec-load-with-value Output mv s) ≡ Data.Bool.false
               → LRel s t → LRel (exec-load-with-value Output mv s) (exec-load-with-value Output mw t)
  load-val-rel (just v) mw f _ R = Relation.Binary.PropositionalEquality.subst (λ m → LRel _ (exec-load-with-value Output m _)) (sym (f v refl)) (lrel-reg Output v R)
    where import Data.Bool
  load-val-rel nothing  mw f () R
    where import Data.Bool

  load-at-rel : ∀ {s t} k ml → LRel s t
              → LocState.faulted (exec-load-at-resolved k Output ml s) ≡ Data.Bool.false
              → LRel (exec-load-at-resolved k Output ml s) (exec-load-at-resolved k Output (Data.Maybe.map (rloc ρ) ml) t)
  load-at-rel k nothing                R ()
    where import Data.Bool
  load-at-rel {s} {t} k (just (AtStack f j)) R h =
    load-val-rel (readLoc s (AtStack f (k + j))) (readLoc t (AtStack f (k + j)))
      (λ v e → trans (l-stack R f (k + j)) (cong (Data.Maybe.map (rv ρ)) e)) h R
  load-at-rel {s} {t} k (just (AtDynamic hl)) R h =
    load-val-rel (readLoc s (AtDynamic (offsetHL hl k))) (readLoc t (AtDynamic (offsetHL (rhl ρ hl) k)))
      (λ v e → trans (cong (LocState.heapMem t) (sym (rhl-off ρ hl k)))
                     (l-heap R (offsetHL hl k) v (l-live R (offsetHL hl k) v e) e)) h R

  ------------------------------------------------------------------------
  -- ★ A store at an offset: into a live block's cell, and its renamed cell
  ------------------------------------------------------------------------

  open ExecFinal {FS} using (exec-store-at-resolved; exec-store-in-block; in-block?; exec-addr-at-resolved; exec-addr-in-block)
  open MemOps {FS} using (writeLocToHeap)

  -- a heap write is a write of the heap
  dyn-write : ∀ (s : LocState FS) hl v → writeLoc s (AtDynamic hl) v ≡ writeLocToHeap s hl v
  dyn-write s hl (SV-Ptr (AtStack _ _)) = refl
  dyn-write s hl (SV-Ptr (AtDynamic _)) = refl
  dyn-write s hl (SV-Tag _)             = refl
  dyn-write s hl (SV-Lit _ _)           = refl
  dyn-write s hl (SV-Code _)            = refl

  lrel-heap-write : ∀ {s t} hl v → Lv (ref-of hl) → LRel s t
                  → LRel (writeLocToHeap s hl v) (writeLocToHeap t (rhl ρ hl) (rv ρ v))
  lrel-heap-write {s} {t} hl v lv R = record
    { l-regs = l-regs R ; l-stack = l-stack R
    ; l-heap = heap-write ρ Lv inj {h = LocState.heapMem s} {g = LocState.heapMem t} hl v lv (l-heap R)
    ; l-live = live′
    ; l-halt = l-halt R ; l-fault = l-fault R ; l-left = l-left R ; l-log = l-log R }
    where
      live′ : ∀ hl′ v′ → MemOps.writeHeapMem {FS} (LocState.heapMem s) hl v hl′ ≡ just v′ → Lv (ref-of hl′)
      live′ hl′ v′ e = aux (hl ≟HL hl′) e
        where
          aux : ∀ (d : Relation.Nullary.Dec (hl ≡ hl′)) → MemOps.writeHeapMem-aux {FS} {hl = hl} {hl' = hl′} d (LocState.heapMem s hl′) v ≡ just v′ → Lv (ref-of hl′)
          aux (yes refl) _ = lv
          aux (no _)     e′ = l-live R hl′ v′ e′

  store-at-rel : ∀ {s t} (bs bs′ : ℕ → ℕ) k ml v → LRel s t
               → (∀ hl → in-block? bs (AtDynamic hl) ≡ Data.Bool.true → Lv (ref-of hl))
               → (∀ hl → in-block? bs (AtDynamic hl) ≡ Data.Bool.true → in-block? bs′ (AtDynamic (rhl ρ hl)) ≡ Data.Bool.true)
               → LocState.faulted (exec-store-at-resolved bs k ml v s) ≡ Data.Bool.false
               → LRel (exec-store-at-resolved bs k ml v s) (exec-store-at-resolved bs′ k (Data.Maybe.map (rloc ρ) ml) (rv ρ v) t)
  store-at-rel bs bs′ k nothing v R lv mono ()
    where import Data.Bool
  store-at-rel {s} {t} bs bs′ k (just (AtStack f j)) v R lv mono h = lrel-stack-write f (k + j) v R
  store-at-rel {s} {t} bs bs′ k (just (AtDynamic hl)) v R lv mono h = go (in-block? bs (AtDynamic (offsetHL hl k))) refl h
    where
      import Data.Bool
      go : ∀ b → in-block? bs (AtDynamic (offsetHL hl k)) ≡ b
         → LocState.faulted (exec-store-in-block b (AtDynamic (offsetHL hl k)) v s) ≡ Data.Bool.false
         → LRel (exec-store-in-block b (AtDynamic (offsetHL hl k)) v s)
                (exec-store-in-block (in-block? bs′ (AtDynamic (offsetHL (rhl ρ hl) k))) (AtDynamic (offsetHL (rhl ρ hl) k)) (rv ρ v) t)
      go Data.Bool.false _ ()
      go Data.Bool.true  e _ =
        Relation.Binary.PropositionalEquality.subst
          (λ b′ → LRel (writeLoc s (AtDynamic (offsetHL hl k)) v) (exec-store-in-block b′ (AtDynamic (offsetHL (rhl ρ hl) k)) (rv ρ v) t))
          (sym (trans (cong (λ q → in-block? bs′ (AtDynamic q)) (sym (rhl-off ρ hl k))) (mono (offsetHL hl k) e)))
          (Relation.Binary.PropositionalEquality.subst₂ LRel (sym (dyn-write s (offsetHL hl k) v))
             (sym (trans (dyn-write t (offsetHL (rhl ρ hl) k) (rv ρ v)) (cong (λ q → writeLocToHeap t q (rv ρ v)) (sym (rhl-off ρ hl k)))))
             (lrel-heap-write (offsetHL hl k) v (lv (offsetHL hl k) e) R))

  ------------------------------------------------------------------------
  -- An address at an offset: inside the block on both sides
  ------------------------------------------------------------------------

  addr-at-rel : ∀ {s t} (bs bs′ : ℕ → ℕ) k ml → LRel s t
              → (∀ hl → in-block? bs (AtDynamic hl) ≡ Data.Bool.true → in-block? bs′ (AtDynamic (rhl ρ hl)) ≡ Data.Bool.true)
              → LocState.faulted (exec-addr-at-resolved bs k ml s) ≡ Data.Bool.false
              → LRel (exec-addr-at-resolved bs k ml s) (exec-addr-at-resolved bs′ k (Data.Maybe.map (rloc ρ) ml) t)
  addr-at-rel bs bs′ k nothing R mono ()
    where import Data.Bool
  addr-at-rel {s} {t} bs bs′ k (just (AtStack f j)) R mono h = lrel-reg Output (SV-Ptr (AtStack f (k + j))) R
  addr-at-rel {s} {t} bs bs′ k (just (AtDynamic hl)) R mono h = go (in-block? bs (AtDynamic (offsetHL hl k))) refl h
    where
      import Data.Bool
      go : ∀ b → in-block? bs (AtDynamic (offsetHL hl k)) ≡ b
         → LocState.faulted (exec-addr-in-block b (AtDynamic (offsetHL hl k)) s) ≡ Data.Bool.false
         → LRel (exec-addr-in-block b (AtDynamic (offsetHL hl k)) s)
                (exec-addr-in-block (in-block? bs′ (AtDynamic (offsetHL (rhl ρ hl) k))) (AtDynamic (offsetHL (rhl ρ hl) k)) t)
      go Data.Bool.false _ ()
      go Data.Bool.true  e _ =
        Relation.Binary.PropositionalEquality.subst
          (λ b′ → LRel (record s { regs = writeReg (LocState.regs s) Output (SV-Ptr (AtDynamic (offsetHL hl k))) })
                       (exec-addr-in-block b′ (AtDynamic (offsetHL (rhl ρ hl) k)) t))
          (sym (trans (cong (λ q → in-block? bs′ (AtDynamic q)) (sym (rhl-off ρ hl k))) (mono (offsetHL hl k) e)))
          (Relation.Binary.PropositionalEquality.subst
             (λ q → LRel (record s { regs = writeReg (LocState.regs s) Output (SV-Ptr (AtDynamic (offsetHL hl k))) })
                         (record t { regs = writeReg (LocState.regs t) Output (SV-Ptr (AtDynamic q)) }))
             (rhl-off ρ hl k)
             (lrel-reg Output (SV-Ptr (AtDynamic (offsetHL hl k))) R))

  ------------------------------------------------------------------------
  -- The constants and the worklist (slots of the current frame)
  ------------------------------------------------------------------------

  module Rest {al al′ : AllocState {FS}} (cf : AllocState.current-frame al′ ≡ AllocState.current-frame al) where
    private
      cf′ = AllocState.current-frame al

    tag-lit : ∀ {s t} n → LRel s t → LRel (proj₁ (exec-abstract (instr-load-tag-lit n) s al)) (proj₁ (exec-abstract (instr-load-tag-lit n) t al′))
    tag-lit n R = const-rel (SV-Tag n) refl R

    code-addr : ∀ {s t} l → LRel s t → LRel (proj₁ (exec-abstract (instr-load-code-addr l) s al)) (proj₁ (exec-abstract (instr-load-code-addr l) t al′))
    code-addr l R = const-rel (SV-Code l) refl R

    load-const : ∀ {s t} {A} (p : FitsInReg A) v → LRel s t
               → LRel (proj₁ (exec-abstract (instr-load-const p v) s al)) (proj₁ (exec-abstract (instr-load-const p v) t al′))
    load-const p v R = const-rel (SV-Lit p (AbstractExec.lit-value {FS} p v)) refl R

    wl-push : ∀ {s t} k → LRel s t → LRel (proj₁ (exec-abstract (worklist-push k) s al)) (proj₁ (exec-abstract (worklist-push k) t al′))
    wl-push {s} {t} k R = Slots.to-slot {al = al} {al′ = al′} cf k R

    wl-pop : ∀ {s t} k → LRel s t → LRel (proj₁ (exec-abstract (worklist-pop k) s al)) (proj₁ (exec-abstract (worklist-pop k) t al′))
    wl-pop {s} {t} k R = Slots.from-slot {al = al} {al′ = al′} cf k R

------------------------------------------------------------------------
-- The relation over two equivalent liveness predicates
------------------------------------------------------------------------

lrel-conv : ∀ {ρ} {Lv Lv′ : ℕ → Set} {inj inj′} {s t}
          → (∀ r → Lv′ r → Lv r) → (∀ r → Lv r → Lv′ r)
          → L.LRel ρ Lv inj s t → L.LRel ρ Lv′ inj′ s t
lrel-conv {ρ} to fro R = record
  { l-regs = L.LRel.l-regs R ; l-stack = L.LRel.l-stack R
  ; l-heap = λ hl v lv e → L.LRel.l-heap R hl v (to _ lv) e
  ; l-live = λ hl v e → fro _ (L.LRel.l-live R hl v e)
  ; l-halt = L.LRel.l-halt R ; l-fault = L.LRel.l-fault R ; l-left = L.LRel.l-left R ; l-log = L.LRel.l-log R }
