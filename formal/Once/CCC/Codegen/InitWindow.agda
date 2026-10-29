-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.InitWindow   (Plan 0.123 A.4 step 4, part 1)
--
-- EVERY BLOCK IS WRITTEN BEFORE IT IS READ, as a fact about the emitted
-- code. Each `instr-alloc-heap` is followed by a straight-line WINDOW that
-- writes both cells of the fresh block through its pointer before any load
-- goes through that pointer, and before any control transfer. Inside the
-- window only loads of OTHER (older) blocks happen.
--
-- `Win out in1 stash w0 w1 t` reads `t` from the allocation on, tracking
-- statically where the fresh pointer is: in `Output` (`out`), in `Input1`
-- (`in1`), in at most one stash slot, and which of its two cells are
-- written. The window closes when both are (`w-done`); what follows is
-- unconstrained here, and `InitDisc` checks it for allocations of its own.
--
-- The run invariant (part 2) reads this: while a window is open, the fresh
-- block is referenced only from the places recorded, so a load through
-- `Input1` never reads it, and every other block is fully written.
------------------------------------------------------------------------

module Once.CCC.Codegen.InitWindow where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; T)
open import Data.Bool.Properties using (T-∧)
open import Data.Product using (proj₁; proj₂)
open import Function.Bundles using (Equivalence)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.Machine.SMCore using
  ( AbstractInstr; AbstractTrace; LabelId
  ; instr-alloc-heap; store-at-slot; load-from-slot; restore-input; mov-to-input
  ; load-indirect; load-indirect-suc; store-indirect; store-indirect-suc
  ; instr-load-tag-lit; instr-load-code-addr )

-- a slot that is not the stash
Apart : ℕ → Maybe ℕ → Set
Apart s nothing  = ⊤
Apart s (just q) = ¬ (s ≡ q)

data Win : (out in1 : Bool) (stash : Maybe ℕ) (w0 w1 : Bool) → AbstractTrace → Set where
  -- both cells written: the block is complete, the window closes
  w-done        : ∀ {o i p t} → Win o i p true true t
  -- the fresh pointer is stashed, once
  w-stash       : ∀ {i w0 w1 s t} → Win true i (just s) w0 w1 t
                → Win true i nothing w0 w1 (store-at-slot s ∷ t)
  -- any other slot store leaves the stash alone and stores no fresh pointer
  w-store-slot  : ∀ {i p w0 w1 s t} → Apart s p → Win false i p w0 w1 t
                → Win false i p w0 w1 (store-at-slot s ∷ t)
  w-mov-in      : ∀ {o i p w0 w1 t} → Win o o p w0 w1 t
                → Win o i p w0 w1 (mov-to-input ∷ t)
  w-load-stash  : ∀ {o i s w0 w1 t} → Win true i (just s) w0 w1 t
                → Win o i (just s) w0 w1 (load-from-slot s ∷ t)
  w-load-slot   : ∀ {o i p s w0 w1 t} → Apart s p → Win false i p w0 w1 t
                → Win o i p w0 w1 (load-from-slot s ∷ t)
  w-restore-stash : ∀ {o i s w0 w1 t} → Win o true (just s) w0 w1 t
                  → Win o i (just s) w0 w1 (restore-input s ∷ t)
  w-restore-slot  : ∀ {o i p s w0 w1 t} → Apart s p → Win o false p w0 w1 t
                  → Win o i p w0 w1 (restore-input s ∷ t)
  -- a load goes through an OLDER block only, and reads no fresh pointer
  w-load        : ∀ {o p w0 w1 t} → Win false false p w0 w1 t
                → Win o false p w0 w1 (load-indirect ∷ t)
  w-load-suc    : ∀ {o p w0 w1 t} → Win false false p w0 w1 t
                → Win o false p w0 w1 (load-indirect-suc ∷ t)
  -- a store never stores the fresh pointer; through it, it writes a cell
  w-store       : ∀ {i p w0 w1 t} → Win false i p (i ∨ w0) w1 t
                → Win false i p w0 w1 (store-indirect ∷ t)
  w-store-suc   : ∀ {i p w0 w1 t} → Win false i p w0 (i ∨ w1) t
                → Win false i p w0 w1 (store-indirect-suc ∷ t)
  w-tag         : ∀ {o i p w0 w1 n t} → Win false i p w0 w1 t
                → Win o i p w0 w1 (instr-load-tag-lit n ∷ t)
  w-code        : ∀ {o i p w0 w1 l t} → Win false i p w0 w1 t
                → Win o i p w0 w1 (instr-load-code-addr l ∷ t)

-- the window right after an allocation: the pointer is in `Output` only
WinFrom : AbstractTrace → Set
WinFrom = Win true false nothing false false

not-alloc? : AbstractInstr → Bool
not-alloc? (instr-alloc-heap _) = false
{-# CATCHALL #-}
not-alloc? _                    = true

NotAlloc : AbstractInstr → Set
NotAlloc i = T (not-alloc? i)

data InitDisc : AbstractTrace → Set where
  []    : InitDisc []
  _∷_   : ∀ {i t} → NotAlloc i → InitDisc t → InitDisc (i ∷ t)
  alloc : ∀ {n t} → WinFrom t → InitDisc t → InitDisc (instr-alloc-heap n ∷ t)

-- A window closes inside its own code, so code after it changes nothing.
win-++ : ∀ {o i p w0 w1 t} u → Win o i p w0 w1 t → Win o i p w0 w1 (t ++ u)
win-++ u w-done                = w-done
win-++ u (w-stash w)           = w-stash (win-++ u w)
win-++ u (w-store-slot a w)    = w-store-slot a (win-++ u w)
win-++ u (w-mov-in w)          = w-mov-in (win-++ u w)
win-++ u (w-load-stash w)      = w-load-stash (win-++ u w)
win-++ u (w-load-slot a w)     = w-load-slot a (win-++ u w)
win-++ u (w-restore-stash w)   = w-restore-stash (win-++ u w)
win-++ u (w-restore-slot a w)  = w-restore-slot a (win-++ u w)
win-++ u (w-load w)            = w-load (win-++ u w)
win-++ u (w-load-suc w)        = w-load-suc (win-++ u w)
win-++ u (w-store w)           = w-store (win-++ u w)
win-++ u (w-store-suc w)       = w-store-suc (win-++ u w)
win-++ u (w-tag w)             = w-tag (win-++ u w)
win-++ u (w-code w)            = w-code (win-++ u w)

init-++ : ∀ {a b} → InitDisc a → InitDisc b → InitDisc (a ++ b)
init-++ []            db = db
init-++ (na ∷ da)     db = na ∷ init-++ da db
init-++ {instr-alloc-heap _ ∷ a} {b} (alloc w da) db = alloc (win-++ b w) (init-++ da db)

-- Code with no allocation decides by computation: `ok _ refl`.
noalloc? : AbstractTrace → Bool
noalloc? []      = true
noalloc? (i ∷ t) = not-alloc? i ∧ noalloc? t

ok : ∀ t → T (noalloc? t) → InitDisc t
ok []      _ = []
ok (i ∷ t) p = proj₁ (Equivalence.to T-∧ p) ∷ ok t (proj₂ (Equivalence.to T-∧ p))

------------------------------------------------------------------------
-- THE THREE WINDOW SHAPES the code generator emits. After the allocation:
-- stash the pointer, put it in `Input1`, then write the two cells, each from
-- a value `Src` loads that is not the fresh pointer (a slot other than the
-- stash, a tag, a code address).
------------------------------------------------------------------------
data Src (p : ℕ) : AbstractInstr → Set where
  s-slot : ∀ {s} → ¬ (s ≡ p) → Src p (load-from-slot s)
  s-tag  : ∀ {n} → Src p (instr-load-tag-lit n)
  s-code : ∀ {l} → Src p (instr-load-code-addr l)

src : ∀ {p x o i w0 w1 t} → Src p x → Win false i (just p) w0 w1 t → Win o i (just p) w0 w1 (x ∷ t)
src (s-slot ne) w = w-load-slot ne w
src s-tag       w = w-tag w
src s-code      w = w-code w

-- `x ; store ; y ; store-suc`
std : ∀ {p x y t} → Src p x → Src p y
    → WinFrom (store-at-slot p ∷ mov-to-input ∷ x ∷ store-indirect ∷ y ∷ store-indirect-suc ∷ t)
std sx sy = w-stash (w-mov-in (src sx (w-store (src sy (w-store-suc w-done)))))

-- `x ; store ; store-suc` (one value fills both cells)
std1 : ∀ {p x t} → Src p x
     → WinFrom (store-at-slot p ∷ mov-to-input ∷ x ∷ store-indirect ∷ store-indirect-suc ∷ t)
std1 sx = w-stash (w-mov-in (src sx (w-store (w-store-suc w-done))))

-- `x ; store-suc ; y ; store` (payload first)
stdr : ∀ {p x y t} → Src p x → Src p y
     → WinFrom (store-at-slot p ∷ mov-to-input ∷ x ∷ store-indirect-suc ∷ y ∷ store-indirect ∷ t)
stdr sx sy = w-stash (w-mov-in (src sx (w-store-suc (src sy (w-store w-done)))))
