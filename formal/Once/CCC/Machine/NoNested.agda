-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.NoNested
--
-- WHERE THE TWO LOWERINGS COINCIDE — a predicate on the ABSTRACT trace, and
-- therefore shared by every target (plan 0.65, 2026-08-12).
--
-- Each backend has two lowerings: the plain block-wise fold (`compile-trace`)
-- and the label-threading one the compiler actually emits
-- (`compile-trace-cnt`). They differ on exactly two constructors —
-- `instr-case-on-tag` and `instr-loop`, where the fold emits a sentinel and
-- the threaded version emits the real label/branch expansion. `NoNested` marks
-- the traces where they agree, which is what lets a correspondence proved over
-- the fold be ABOUT the emitted program.
--
-- WHY IT IS HERE. It lived in `Target.X86-64.AbstractToX86` and mentions no
-- x86: `AbstractInstr`, `⊥`/`⊤` and the `EmittableI` fence, all of which the
-- three targets share. Porting riscv64's emitter to match x86-64's found the
-- asymmetry — riscv64 had none of this — and copying six definitions into a
-- second (then a third) target would have been the wrong repair. What is
-- genuinely per-arch is only `compile-trace-cnt-agrees`, which names that
-- arch's own two lowerings and stays with its emitter.
------------------------------------------------------------------------

module Once.CCC.Machine.NoNested where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to all-[]; _∷_ to _all∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.FrameFree using (EmittableI)

-- `compile-trace` (below) is the plain fold; `compile-trace-cnt` (above) is what
-- the compiler actually emits (`Once.Target.X86-64`). They differ on EXACTLY two
-- constructors — `instr-case-on-tag` and `instr-loop`, where the fold emits the
-- `ud2` sentinel and the threaded version emits the real label/branch lowering.
-- `NoNested` marks the traces where they coincide, so a correspondence proved
-- over the fold transfers to the emitted program.
NoNestedI : AbstractInstr → Set
NoNestedI (instr-case-on-tag _ _) = ⊥
NoNestedI (instr-loop _)          = ⊥
NoNestedI _                       = ⊤

NoNested : AbstractTrace → Set
NoNested []       = ⊤
NoNested (i ∷ is) = NoNestedI i × NoNested is

-- Item 6 (2026-08-01): the unemittable set (`FrameFreeI`'s ⊥ cases) SUBSUMES
-- the nested set, so every emitted trace is `NoNested` — which makes
-- `compile-trace-cnt` and the plain `compile-trace` coincide on every emitted
-- program (`compile-trace-cnt-agrees` applies unconditionally at the apex,
-- retiring the `conc-flat-sim-nested` split).
-- Plan 0.63: the EMITTER FENCE suffices — the closure markers carry no
-- nested trace either, so widening from `FrameFreeI` costs nothing here.
no-nested-of-frame-free : ∀ (i : AbstractInstr) → EmittableI i → NoNestedI i
no-nested-of-frame-free mov-to-output           _ = tt
no-nested-of-frame-free mov-to-input            _ = tt
no-nested-of-frame-free load-indirect           _ = tt
no-nested-of-frame-free load-indirect-suc       _ = tt
no-nested-of-frame-free (load-from-slot _)      _ = tt
no-nested-of-frame-free (store-at-slot _)       _ = tt
no-nested-of-frame-free store-indirect          _ = tt
no-nested-of-frame-free store-indirect-suc      _ = tt
no-nested-of-frame-free (lea-slot _)            _ = tt
no-nested-of-frame-free (restore-input _)       _ = tt
no-nested-of-frame-free (lea-indexed _)         ()
no-nested-of-frame-free (instr-alloc-stack _)   ()
no-nested-of-frame-free (instr-dealloc-stack _) ()
no-nested-of-frame-free (instr-push-frame _)    ()
no-nested-of-frame-free instr-pop-frame         ()
no-nested-of-frame-free (instr-loop _)          ()
no-nested-of-frame-free (instr-case-on-tag _ _) ()
no-nested-of-frame-free (instr-reclaim-to _)    _ = tt
no-nested-of-frame-free instr-call-closure      _ = tt
no-nested-of-frame-free (worklist-init _)       _ = tt
no-nested-of-frame-free (worklist-push _)       _ = tt
no-nested-of-frame-free (worklist-pop _)        _ = tt
no-nested-of-frame-free (worklist-check _)      _ = tt
no-nested-of-frame-free (instr-sigop _)         _ = tt
no-nested-of-frame-free (instr-load-const _ _)  _ = tt
no-nested-of-frame-free (instr-load-code-addr _) _ = tt
no-nested-of-frame-free instr-save-closure-reg  _ = tt
no-nested-of-frame-free (instr-load-tag-lit _)  _ = tt
no-nested-of-frame-free (instr-alloc-heap _)    _ = tt
no-nested-of-frame-free (instr-reg-op _)        _ = tt
no-nested-of-frame-free (instr-ctrl _)          _ = tt

no-nested-of-all : ∀ (t : AbstractTrace) → All EmittableI t → NoNested t
no-nested-of-all []       _          = tt
no-nested-of-all (i ∷ is) (fi all∷ fis) =
  no-nested-of-frame-free i fi , no-nested-of-all is fis

-- can only transport the correspondence when the two lowerings coincide).
NoNestedI? : (i : AbstractInstr) → Dec (NoNestedI i)
NoNestedI? (instr-case-on-tag _ _) = no (λ z → z)
NoNestedI? (instr-loop _)          = no (λ z → z)
NoNestedI? mov-to-output           = yes tt
NoNestedI? mov-to-input            = yes tt
NoNestedI? load-indirect           = yes tt
NoNestedI? load-indirect-suc       = yes tt
NoNestedI? (load-from-slot _)      = yes tt
NoNestedI? (store-at-slot _)       = yes tt
NoNestedI? store-indirect          = yes tt
NoNestedI? store-indirect-suc      = yes tt
NoNestedI? (lea-slot _)            = yes tt
NoNestedI? (restore-input _)       = yes tt
NoNestedI? (lea-indexed _)         = yes tt
NoNestedI? (instr-alloc-stack _)   = yes tt
NoNestedI? (instr-dealloc-stack _) = yes tt
NoNestedI? (instr-reclaim-to _)    = yes tt
NoNestedI? (instr-push-frame _)    = yes tt
NoNestedI? instr-pop-frame         = yes tt
NoNestedI? instr-call-closure      = yes tt
NoNestedI? (worklist-init _)       = yes tt
NoNestedI? (worklist-push _)       = yes tt
NoNestedI? (worklist-pop _)        = yes tt
NoNestedI? (worklist-check _)      = yes tt
NoNestedI? (instr-sigop _)         = yes tt
NoNestedI? (instr-load-const _ _)  = yes tt
NoNestedI? (instr-load-code-addr _) = yes tt
NoNestedI? instr-save-closure-reg  = yes tt
NoNestedI? (instr-load-tag-lit _)  = yes tt
NoNestedI? (instr-alloc-heap _)    = yes tt
NoNestedI? (instr-reg-op _)        = yes tt
NoNestedI? (instr-ctrl _)          = yes tt

NoNested? : (t : AbstractTrace) → Dec (NoNested t)
NoNested? []       = yes tt
NoNested? (i ∷ is) with NoNestedI? i | NoNested? is
... | yes p | yes q = yes (p , q)
... | no ¬p | _     = no (λ z → ¬p (proj₁ z))
... | _     | no ¬q = no (λ z → ¬q (proj₂ z))
