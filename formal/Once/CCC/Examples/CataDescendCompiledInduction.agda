-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Examples.CataDescendCompiledInduction
--
-- Plan 0.30 #1 (abstract↔binary bridge): the BINARY side of the cata
-- descend fold. `AbstractCataFoldInduction` proved the abstract machine
-- (`exec-loop`/`exec-case-dispatch`) folds every heap-Nat; this proves
-- the *actual x86-64 the binary emits* — `compile-trace-cnt`'s loop
-- lowering — does the same, run by the real CPU model `Semantics.exec`
-- (fuel + `find-label` back-edges), ∀-n by fuel induction.
--
-- Both sides compute the μ-value's depth `n`, so they correspond: the
-- compiled loop refines the proven abstract fold. This is the genuine
-- abstract↔binary edge for x86-64, on the live `compile-trace-cnt` path
-- (NOT the straight-line `exec-prog`/`compile-trace` simulation, which
-- emits `ud2` for control flow and so cannot model a loop).
--
-- The compiled loop is more involved than `NatFoldLoopInduction`'s
-- hand-written `fold-prog`: it carries a persistent `rbx` loop flag (the
-- abstract `Scratch`) and a NESTED `je` for the tag dispatch — exactly
-- what `compile-trace-cnt (instr-loop [case-on-tag …])` emits.
------------------------------------------------------------------------

module Once.CCC.Examples.CataDescendCompiledInduction where

open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.Bool using (false)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Data.Product using (proj₂)

open import Once.CCC.Target.X86-64.Syntax
open import Once.CCC.Target.X86-64.Semantics
open State using (regs)

open import Once.CCC.Machine.SMCore
  using (AbstractTrace; instr-case-on-tag; instr-reg-op; scratch-zero;
         input2-inc; load-indirect-suc; mov-to-input; instr-loop)
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace-cnt)

------------------------------------------------------------------------
-- The compiled descend-loop = compile-trace-cnt 0 (instr-loop
--   [case-on-tag [scratch-zero] [input2-inc, load-indirect-suc,
--                                mov-to-input]]).
-- Labels: 0=top, 1=end, 2=inl(tag 0), 3=dispatch-end.
--   rbx = loop flag (Scratch), rsi = depth (Input2), rdi = cursor
--   (Input1), rax = scratch.
------------------------------------------------------------------------
descend-prog : Program
descend-prog =
    label 0
  ∷ cmp (reg rbx) (imm 0)                           -- loop flag == 0?
  ∷ je 1                                            --   → end
  ∷ cmp (mem (base+disp rdi 0)) (imm 0)             -- node tag == 0?
  ∷ je 2                                            --   → inl (zero)
  ∷ add (reg rsi) (imm 1)                           -- inr: depth++
  ∷ mov (reg rax) (mem (base+disp rdi slot-size))   --   load child ptr
  ∷ mov (reg rdi) (reg rax)                         --   descend
  ∷ jmp 3
  ∷ label 2                                         -- inl: zero node
  ∷ mov (reg rbx) (imm 0)                           --   clear loop flag
  ∷ label 3
  ∷ jmp 0                                           -- back to top
  ∷ label 1                                         -- end
  ∷ []

------------------------------------------------------------------------
-- Faithfulness: descend-prog IS exactly what the live backend emits for
-- the cata descend loop — `compile-trace-cnt 0 (instr-loop body)` where
-- `body` is IRToTrace's descend-body. So `fold-correct` is a theorem
-- about the ACTUAL binary code, not a hand-written stand-in.
------------------------------------------------------------------------
abstract-descend-body : AbstractTrace
abstract-descend-body =
  instr-case-on-tag
    (instr-reg-op scratch-zero ∷ [])
    (instr-reg-op input2-inc ∷ load-indirect-suc ∷ mov-to-input ∷ [])
  ∷ []

faithful : descend-prog ≡ proj₂ (compile-trace-cnt 0 (instr-loop abstract-descend-body ∷ []))
faithful = refl

------------------------------------------------------------------------
-- Heap representation of a NatF μ-value (tagged nodes, child at +slot).
------------------------------------------------------------------------
data HeapNat (m : Memory) : ℕ → ℕ → Set where  -- HeapNat m ptr n
  hz : ∀ {ptr}
     → m ptr ≡ just 0
     → HeapNat m ptr 0
  hs : ∀ {ptr child n}
     → m ptr ≡ just 1
     → m (ptr + slot-size) ≡ just child
     → HeapNat m child n
     → HeapNat m ptr (suc n)

------------------------------------------------------------------------
-- Loop-head state (pc 0, not halted). rbx/rdi/rsi read via hypotheses;
-- flags are a spectator (the first `cmp rbx,0` overwrites them).
------------------------------------------------------------------------
head : RegFile → Flags → Memory → State
head rf fl m = mkstate rf m fl 0 false

rsi-of : State → ℕ
rsi-of s = readReg (regs s) rsi

-- Fuel: 11 steps per suc layer; 14 to bottom out on zero (set flag,
-- loop back, re-test, branch to end, halt).
needed : ℕ → ℕ
needed zero    = 14
needed (suc n) = 11 + needed n

------------------------------------------------------------------------
-- One suc-iteration: peel 11 steps, bumping rsi and descending rdi to
-- the child. Only the two memory reads (tag, child) are neutral.
------------------------------------------------------------------------
iter : ∀ (R : ℕ) (rf : RegFile) (fl : Flags) (m : Memory) (ptr child acc : ℕ)
     → readReg rf rbx ≡ 1
     → readReg rf rdi ≡ ptr
     → readReg rf rsi ≡ acc
     → m ptr ≡ just 1
     → m (ptr + slot-size) ≡ just child
     → exec (11 + R) descend-prog (head rf fl m)
       ≡ exec R descend-prog
           (head (writeReg (writeReg (writeReg rf rsi (acc + 1)) rax child) rdi child)
                 (mkflags ((acc + 1) ≡ᵇ 0) false false) m)
iter R rf fl m ptr child acc rbx-eq rdi-eq rsi-eq tag-eq child-eq
  rewrite rbx-eq | rdi-eq | +-identityʳ ptr | tag-eq | rdi-eq | child-eq | rsi-eq = refl

------------------------------------------------------------------------
-- ∀-n: the compiled loop folds any heap-Nat into rsi = acc + n.
------------------------------------------------------------------------
fold-correct : ∀ (n extra : ℕ) (rf : RegFile) (fl : Flags) (m : Memory) (ptr acc : ℕ)
             → readReg rf rbx ≡ 1
             → readReg rf rdi ≡ ptr
             → readReg rf rsi ≡ acc
             → HeapNat m ptr n
             → map rsi-of (exec (needed n + extra) descend-prog (head rf fl m))
               ≡ just (acc + n)
-- zero: tag 0 → je 2 (clear flag) → loop back → cmp rbx 0 true → je 1 →
-- halt. rsi = acc.
fold-correct zero extra rf fl m ptr acc rbx-eq rdi-eq rsi-eq (hz tag0-eq)
  rewrite rbx-eq | rdi-eq | +-identityʳ ptr | tag0-eq | rsi-eq | +-identityʳ acc = refl
-- suc k: one iter, then the IH folds the child with acc+1.
fold-correct (suc k) extra rf fl m ptr acc rbx-eq rdi-eq rsi-eq (hs tag-eq child-eq hchild) =
  trans (cong (map rsi-of)
              (iter (needed k + extra) rf fl m ptr _ acc rbx-eq rdi-eq rsi-eq tag-eq child-eq))
        (trans (fold-correct k extra _ (mkflags ((acc + 1) ≡ᵇ 0) false false) m _ (acc + 1)
                  rbx-eq refl refl hchild)
               (cong just (+-assoc acc 1 k)))

------------------------------------------------------------------------
-- Corollary: from a clean depth (rsi = 0), the compiled loop yields n.
------------------------------------------------------------------------
fold-clean : ∀ (n extra : ℕ) (rf : RegFile) (fl : Flags) (m : Memory) (ptr : ℕ)
           → readReg rf rbx ≡ 1
           → readReg rf rdi ≡ ptr
           → readReg rf rsi ≡ 0
           → HeapNat m ptr n
           → map rsi-of (exec (needed n + extra) descend-prog (head rf fl m)) ≡ just n
fold-clean n extra rf fl m ptr rbx-eq rdi-eq rsi0 h =
  fold-correct n extra rf fl m ptr 0 rbx-eq rdi-eq rsi0 h
