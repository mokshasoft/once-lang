------------------------------------------------------------------------
-- Once.CCC.Examples.NatFoldLoop
--
-- Plan 0.27 (A2): a real X86-64 loop folding a HEAP-allocated μ-value.
--
-- A NatF value (NatF = K Unit ⊕ Id) lives on the heap as tagged nodes:
--   zero  : [node]   = 0                       (tag 0)
--   suc n : [node]   = 1 ; [node+8] = &n        (tag 1 + child pointer)
-- (matching the heap sum-node layout: tag at base, payload at base+8.)
--
-- The loop reads a node's tag, dispatches, follows the child pointer, and
-- loops back (backward jump). For NatF the catamorphism that counts the
-- `suc`s (depth) is an accumulator fold — a single backward loop, no
-- worklist needed. This exercises heap reads + tag dispatch + the loop
-- back-edge end-to-end on the verified CPU: the core A2 mechanism. (The
-- general post-order Cata for trees adds a worklist on top of this.)
------------------------------------------------------------------------

module Once.CCC.Examples.NatFoldLoop where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.Target.X86-64.Syntax
open import Once.CCC.Target.X86-64.Semantics

------------------------------------------------------------------------
-- Heap: Nat = 3 = suc (suc (suc zero)), nodes at 8 / 16 / 32 / 48.
--   8:  [8]=0                       zero
--   16: [16]=1, [24]=8              suc → zero
--   32: [32]=1, [40]=16             suc → 16
--   48: [48]=1, [56]=32             suc → 32   (root, value 3)
------------------------------------------------------------------------
heap : Memory
heap = writeMem (writeMem (writeMem (writeMem (writeMem (writeMem (writeMem
         emptyMemory
         8 0) 16 1) 24 8) 32 1) 40 16) 48 1) 56 32

------------------------------------------------------------------------
-- The fold loop (count the suc's = the Nat's value):
--   label 0:  mov rcx,[rdi] ; cmp rcx,0 ; je 1 ; add rax,1 ; mov rdi,[rdi+8] ; jmp 0
--   label 1:  end
------------------------------------------------------------------------
fold-prog : Program
fold-prog =
    label 0
  ∷ mov (reg rcx) (mem (base rdi))          -- rcx := tag
  ∷ cmp (reg rcx) (imm 0)
  ∷ je 1                                      -- zero → done
  ∷ add (reg rax) (imm 1)                     -- count this suc
  ∷ mov (reg rdi) (mem (base+disp rdi 8))     -- rdi := child pointer
  ∷ jmp 0                                      -- BACKWARD loop
  ∷ label 1
  ∷ []

-- Start with rdi = root (48), heap installed.
start : State
start = record initState
          { regs = writeReg (State.regs initState) rdi 48
          ; memory = heap }

-- Folding the heap Nat 3 yields 3 in rax.
fold-runs : map (λ fs → readReg (State.regs fs) rax) (run fold-prog start) ≡ just 3
fold-runs = refl
