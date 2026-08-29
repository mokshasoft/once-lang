-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.MemEffectCore  (Plan 0.54 Phase B / Option 2)
--
-- The arch-generic MEMORY EFFECT + its CCC-preservation. Only spill (`Xmov-r-m`)
-- writes memory — to a scratch slot in the reserved frame BELOW the entry stack
-- frontier; every other instruction leaves memory untouched. The single
-- per-arch obligation is `scratch-below`: a spill's scratch address is `<`
-- the frontier, given the shared in-frame witness (`slot < required-scratch`).
-- Both x86-64 (`rsp − N`, satisfies it from `0 < rsp`) and riscv64
-- (`sp + offset`, satisfies it from the slot bound) discharge the SAME obligation.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Arith.Backend.XInstr.Syntax

module Once.Arith.Backend.MemEffectCore
  {State Memory RegFile Reg : Set}
  (memory       : State → Memory)
  (regs         : State → RegFile)
  (readReg      : RegFile → Reg → ℕ)
  (writeMem     : Memory → ℕ → ℕ → Memory)
  (AgreeMemFrom : ℕ → Memory → Memory → Set)
  (AgreeMemFrom-refl : ∀ fr m → AgreeMemFrom fr m m)
  (writeMem-below-preserves : ∀ m fr addr val → addr < fr → AgreeMemFrom fr m (writeMem m addr val))
  (arith-reg    : XReg → Reg)
  (scratch-addr : State → XScratch → ℕ)
  (frontier     : State → ℕ)
  (InFrame      : XInstr → Set)
  -- The single per-arch obligation, with both a positive frontier (x86-64 uses it)
  -- and the in-frame witness (riscv64 uses it) available; each ignores the other.
  (scratch-below : ∀ s sc src fr → frontier s ≡ fr → 0 < fr → InFrame (Xmov-r-m sc src) →
                   scratch-addr s sc < fr)
  where

mem-effect : XInstr → State → Memory
mem-effect (Xmov-r-m sc src) s =
  writeMem (memory s) (scratch-addr s sc) (readReg (regs s) (arith-reg src))
mem-effect _ s = memory s

mem-preserves : ∀ i s fr → frontier s ≡ fr → 0 < fr → InFrame i →
                AgreeMemFrom fr (memory s) (mem-effect i s)
mem-preserves (Xmov-r-m sc src)   s fr f≡ 0<fr inf =
  writeMem-below-preserves (memory s) fr (scratch-addr s sc)
    (readReg (regs s) (arith-reg src)) (scratch-below s sc src fr f≡ 0<fr inf)
mem-preserves (Xmov-imm _ _)      s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xmov-rr _ _)       s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xmov-m-r _ _)      s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xmov-arg _ _)      s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xadd-rr _ _)       s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xsub-rr _ _)       s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Ximul-rr _ _)      s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xneg-r _)          s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xdiv-rrr _ _ _)    s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xrem-rrr _ _ _)    s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xdiv-safe-rrr _ _ _) s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xrem-safe-rrr _ _ _) s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xshl-rri _ _ _)    s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xsdiv-pow2-rri _ _ _) s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
-- PLAN 0.75 F4: no float instruction writes memory — only the spill does.
mem-preserves (Xfadd-rr _ _)       s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xfsub-rr _ _)       s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xfmul-rr _ _)       s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xfdiv-rrr _ _ _)    s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xfsubr-rr _ _)      s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xfneg-r _)          s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xi2f-r _ _)         s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xmov-fimm _ _)      s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xmov-farg _ _)      s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
mem-preserves (Xmov-out _)        s fr _ _ _ = AgreeMemFrom-refl fr (memory s)
