-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV64.Confine  (Plan 0.54 Phase B / Option 1)
--
-- riscv64 witness for the generic field-① confinement obligation: every
-- physical register the riscv64 arith emit writes is `arith` (a3/a4/a5) or
-- `io` (a0 path-walk scratch) — NEVER `ccc`. Definitional via the shared
-- `Once.Target.RiscV64.PhysReg` partition (`arith-disjoint`). RV64M `div`/`rem`
-- are single-instruction (dst only), so the footprints are even simpler than
-- x86-64's rax/rdx idivq.
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV64.Confine where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Once.Arith.Backend.XInstr.Syntax
open import Once.Target.RiscV64.PhysReg using (Reg; a0; owner; ccc; convention)
open import Once.Arith.Backend.RiscV64.Emit using (arith-reg; arith-disjoint)
open import Once.Arith.Backend.Adequacy using (ArithEmitConfined)

writes : XInstr → List Reg
writes (Xmov-imm dst _)         = arith-reg dst ∷ []
writes (Xmov-rr dst _)          = arith-reg dst ∷ []
writes (Xmov-r-m _ _)           = []                         -- scratch memory only
writes (Xmov-m-r dst _)         = arith-reg dst ∷ []
writes (Xmov-arg dst _)         = arith-reg dst ∷ a0 ∷ []    -- multi-hop walks via a0
writes (Xadd-rr dst _)          = arith-reg dst ∷ []
writes (Xsub-rr dst _)          = arith-reg dst ∷ []
writes (Ximul-rr dst _)         = arith-reg dst ∷ []
writes (Xneg-r dst)             = arith-reg dst ∷ []
writes (Xdiv-rrr dst _ _)       = arith-reg dst ∷ []
writes (Xrem-rrr dst _ _)       = arith-reg dst ∷ []
writes (Xdiv-safe-rrr dst _ _)  = arith-reg dst ∷ []
writes (Xrem-safe-rrr dst _ _)  = arith-reg dst ∷ []
writes (Xshl-rri dst _ _)       = arith-reg dst ∷ []
writes (Xsdiv-pow2-rri dst _ _) = arith-reg dst ∷ a0 ∷ []
-- PLAN 0.75 F4: the float instructions write their destination GPR (the
-- pattern lives in a GPR between operations) and, on x86-64, `rax` for the
-- sign-flip mask.
--
-- THE `%xmm` / `ft*` CLOBBER IS OUTSIDE THIS MODEL, and that is part of the
-- named `float-xinstr-sim` residual rather than a separate omission: the
-- machine's `Reg` type has no float registers at all, so there is nothing here
-- to declare them clobbered. Whoever gives the arches float registers must
-- extend these two lists at the same time.
writes (Xfadd-rr dst _)         = arith-reg dst ∷ []
writes (Xfsub-rr dst _)         = arith-reg dst ∷ []
writes (Xfmul-rr dst _)         = arith-reg dst ∷ []
writes (Xfsubr-rr dst _)        = arith-reg dst ∷ []
writes (Xfneg-r dst)            = arith-reg dst ∷ []
writes (Xi2f-r dst _)           = arith-reg dst ∷ []
writes (Xmov-fimm dst _)        = arith-reg dst ∷ []
writes (Xmov-farg dst _)        = arith-reg dst ∷ []
writes (Xmov-out _)             = a0 ∷ []

NotCCC : Reg → Set
NotCCC r = owner r ≢ ccc

arith-notccc : ∀ x → NotCCC (arith-reg x)
arith-notccc x rewrite arith-disjoint x = λ ()

a0-notccc : NotCCC a0
a0-notccc = λ ()

confined : ∀ i → All NotCCC (writes i)
confined (Xmov-imm dst _)         = arith-notccc dst ∷ []
confined (Xmov-rr dst _)          = arith-notccc dst ∷ []
confined (Xmov-r-m _ _)           = []
confined (Xmov-m-r dst _)         = arith-notccc dst ∷ []
confined (Xmov-arg dst _)         = arith-notccc dst ∷ a0-notccc ∷ []
confined (Xadd-rr dst _)          = arith-notccc dst ∷ []
confined (Xsub-rr dst _)          = arith-notccc dst ∷ []
confined (Ximul-rr dst _)         = arith-notccc dst ∷ []
confined (Xneg-r dst)             = arith-notccc dst ∷ []
confined (Xdiv-rrr dst _ _)       = arith-notccc dst ∷ []
confined (Xrem-rrr dst _ _)       = arith-notccc dst ∷ []
confined (Xdiv-safe-rrr dst _ _)  = arith-notccc dst ∷ []
confined (Xrem-safe-rrr dst _ _)  = arith-notccc dst ∷ []
confined (Xshl-rri dst _ _)       = arith-notccc dst ∷ []
confined (Xsdiv-pow2-rri dst _ _) = arith-notccc dst ∷ a0-notccc ∷ []
confined (Xfadd-rr dst _)         = arith-notccc dst ∷ []
confined (Xfsub-rr dst _)         = arith-notccc dst ∷ []
confined (Xfmul-rr dst _)         = arith-notccc dst ∷ []
confined (Xfsubr-rr dst _)        = arith-notccc dst ∷ []
confined (Xfneg-r dst)            = arith-notccc dst ∷ []
confined (Xi2f-r dst _)           = arith-notccc dst ∷ []
confined (Xmov-fimm dst _)        = arith-notccc dst ∷ []
confined (Xmov-farg dst _)        = arith-notccc dst ∷ []
confined (Xmov-out _)             = a0-notccc ∷ []

confined-instance : ArithEmitConfined convention
confined-instance = record { writes = writes ; confined = confined }
