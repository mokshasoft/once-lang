-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.Confine  (Plan 0.54 Phase B / Option 1)
--
-- The arith block's REGISTER-CONFINEMENT proof: every physical register
-- the x86-64 arith emit can write is `owner`ed by `io`/`arith`/`free` —
-- NEVER `ccc`. So the emitted arith subroutine cannot clobber a register
-- CCC keeps live across the `call once_arith.block.*` site.
--
-- This is the compiler-logic half of the arith slice of `asm-trace-correct`
-- (the "does-not-clobber-CCC" claim), made DEFINITIONAL via the shared
-- `Once.Target.X86-64.PhysReg` partition (Plan 0.55). The residual — that
-- the CPU actually writes only `writes i` when executing `instr-text i` — is
-- the explicit per-instruction ISA axiom (the honest boundary; Option 1).
--
-- `writes i` OVER-APPROXIMATES the clobber set of `instr-text i` (read off
-- Emit.agda), so `All NotCCC (writes i)` ⇒ the real clobber set is non-CCC.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.Confine where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Once.Arith.Backend.XInstr.Syntax
open import Once.Target.X86-64.PhysReg using (Reg; rax; rdx; owner; ccc; convention)
open import Once.Arith.Backend.X86-64.Emit using (arith-reg; arith-disjoint)
open import Once.Arith.Backend.Adequacy using (ArithEmitConfined)

------------------------------------------------------------------------
-- The clobber footprint of each XInstr (over-approximation of the
-- registers its `instr-text` clause writes; see Emit.agda line-by-line).
------------------------------------------------------------------------

writes : XInstr → List Reg
writes (Xmov-imm dst _)         = arith-reg dst ∷ []
writes (Xmov-rr dst _)          = arith-reg dst ∷ []
writes (Xmov-r-m _ _)           = []                            -- scratch memory only
writes (Xmov-m-r dst _)         = arith-reg dst ∷ []
writes (Xmov-arg dst _)         = arith-reg dst ∷ rax ∷ []      -- multi-hop walks via %rax
writes (Xadd-rr dst _)          = arith-reg dst ∷ []
writes (Xsub-rr dst _)          = arith-reg dst ∷ []
writes (Ximul-rr dst _)         = arith-reg dst ∷ []
writes (Xneg-r dst)             = arith-reg dst ∷ []
writes (Xdiv-rrr dst _ _)       = arith-reg dst ∷ rax ∷ rdx ∷ []
writes (Xrem-rrr dst _ _)       = arith-reg dst ∷ rax ∷ rdx ∷ []
writes (Xdiv-safe-rrr dst _ _)  = arith-reg dst ∷ rax ∷ rdx ∷ []
writes (Xrem-safe-rrr dst _ _)  = arith-reg dst ∷ rax ∷ rdx ∷ []
writes (Xshl-rri dst _ _)       = arith-reg dst ∷ []
writes (Xsdiv-pow2-rri dst _ _) = arith-reg dst ∷ rax ∷ []
writes (Xmov-out _)             = rax ∷ []

------------------------------------------------------------------------
-- Confinement: no written register is CCC-owned.
------------------------------------------------------------------------

NotCCC : Reg → Set
NotCCC r = owner r ≢ ccc

-- `arith-reg x` is `arith`-owned (arith-disjoint), and `arith ≢ ccc`.
arith-notccc : ∀ x → NotCCC (arith-reg x)
arith-notccc x rewrite arith-disjoint x = λ ()

-- `owner rax = io`, `owner rdx = free`; both ≢ ccc definitionally.
rax-notccc : NotCCC rax
rax-notccc = λ ()

rdx-notccc : NotCCC rdx
rdx-notccc = λ ()

confined : ∀ i → All NotCCC (writes i)
confined (Xmov-imm dst _)         = arith-notccc dst ∷ []
confined (Xmov-rr dst _)          = arith-notccc dst ∷ []
confined (Xmov-r-m _ _)           = []
confined (Xmov-m-r dst _)         = arith-notccc dst ∷ []
confined (Xmov-arg dst _)         = arith-notccc dst ∷ rax-notccc ∷ []
confined (Xadd-rr dst _)          = arith-notccc dst ∷ []
confined (Xsub-rr dst _)          = arith-notccc dst ∷ []
confined (Ximul-rr dst _)         = arith-notccc dst ∷ []
confined (Xneg-r dst)             = arith-notccc dst ∷ []
confined (Xdiv-rrr dst _ _)       = arith-notccc dst ∷ rax-notccc ∷ rdx-notccc ∷ []
confined (Xrem-rrr dst _ _)       = arith-notccc dst ∷ rax-notccc ∷ rdx-notccc ∷ []
confined (Xdiv-safe-rrr dst _ _)  = arith-notccc dst ∷ rax-notccc ∷ rdx-notccc ∷ []
confined (Xrem-safe-rrr dst _ _)  = arith-notccc dst ∷ rax-notccc ∷ rdx-notccc ∷ []
confined (Xshl-rri dst _ _)       = arith-notccc dst ∷ []
confined (Xsdiv-pow2-rri dst _ _) = arith-notccc dst ∷ rax-notccc ∷ []
confined (Xmov-out _)             = rax-notccc ∷ []

------------------------------------------------------------------------
-- x86-64 instance of the generic field-① obligation.
------------------------------------------------------------------------

confined-instance : ArithEmitConfined convention
confined-instance = record { writes = writes ; confined = confined }
