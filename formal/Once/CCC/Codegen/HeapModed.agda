-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.HeapModed
--
-- HEAP-MODEDNESS: every allocation the IR asks for is on the heap. It is what
-- makes an emitted trace FRAME-FREE (`FrameFreeTrace`: no frame op and no
-- `lea-slot`), and since plan 0.86 stage G no IR node carries a mode, so it
-- holds of every IR (`heap-moded`).
--
-- D367: moved here from `ShapeTable`, the typed shape checker of plan 0.62,
-- which is gone — the site facts it was meant to feed are read off the
-- program's own run instead (`RunWF`). This predicate was the one part of it
-- something else consumed.
------------------------------------------------------------------------

module Once.CCC.Codegen.HeapModed where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Once.IR

HeapModed : ∀ {A B} → IR A B → Set
HeapModed id        = ⊤
HeapModed fst       = ⊤
HeapModed snd       = ⊤
HeapModed terminal  = ⊤
HeapModed initial   = ⊤
HeapModed apply     = ⊤
HeapModed (g ∘ f)   = HeapModed f × HeapModed g
-- Stage G: a pair carries NO mode any more, so it contributes no `IsHeap`
-- obligation — only its components can be heap-moded.
HeapModed ⟨ f , g ⟩ = HeapModed f × HeapModed g
-- 0.86 stage G: `curry` has no mode, so there is no `IsHeap` to demand —
-- the heap lowering is the only one.
HeapModed (curry b)   = HeapModed b
-- 0.86 stage G: the injections have no mode, so no `IsHeap` obligation —
-- the heap lowering is the only one. Since the whole of stage G landed, the
-- same holds for `In`/`in-ν`: `IsHeap` now has NO producer among the IR
-- constructors, and `HeapModed` is a conjunction of `⊤`s over the structure.
HeapModed inl       = ⊤
HeapModed inr       = ⊤
HeapModed (case f g) = HeapModed f × HeapModed g
HeapModed (In _)  = ⊤
HeapModed (out-μ _) = ⊤
HeapModed (Cata _ alg) = HeapModed alg
HeapModed (Out _)   = ⊤
HeapModed (in-ν _) = ⊤
HeapModed (Ana _ coalg) = HeapModed coalg
HeapModed (Iter coalg) = HeapModed coalg
HeapModed (SigOp _) = ⊤
HeapModed (Call _) = ⊤
HeapModed (const _ _) = ⊤

-- Since stage G no IR node carries a mode, so EVERY IR is heap-moded. This
-- used to be assumed at each arch's apex (`main-heap-moded`, a postulate).
heap-moded : ∀ {A B} (ir : IR A B) → HeapModed ir
heap-moded id           = tt
heap-moded fst          = tt
heap-moded snd          = tt
heap-moded terminal     = tt
heap-moded initial      = tt
heap-moded apply        = tt
heap-moded (g ∘ f)      = heap-moded f , heap-moded g
heap-moded ⟨ f , g ⟩    = heap-moded f , heap-moded g
heap-moded (curry b)    = heap-moded b
heap-moded inl          = tt
heap-moded inr          = tt
heap-moded (case f g)   = heap-moded f , heap-moded g
heap-moded (In _)       = tt
heap-moded (out-μ _)    = tt
heap-moded (Cata _ alg) = heap-moded alg
heap-moded (Out _)      = tt
heap-moded (in-ν _)     = tt
heap-moded (Ana _ c)    = heap-moded c
heap-moded (Iter c)    = heap-moded c
heap-moded (SigOp _)    = tt
heap-moded (Call _)     = tt
heap-moded (const _ _)  = tt
