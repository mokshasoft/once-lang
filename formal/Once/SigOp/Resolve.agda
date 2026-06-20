-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.SigOp.Resolve
--
-- Plan 0.38 M0.2: LATE interpretation resolution as a single boundary
-- pass — the same shape as the arith compiler's `rewrite-ir`
-- (`Once.Arith.Machine.Rewrite`), which lifts arith subtrees to
-- `arith.block.<digest>` SigOps in one `IR → IR` walk with no parameter
-- cascade. An interpretation is just another SigOp producer
-- (`name → SigOpInfo`), so it is wired the same way.
--
-- Elaboration emits `SigOp` nodes carrying the real *name* with a generic
-- placeholder `semM`/`effect` (interpretation-free — the core never
-- string-matches `"linux.exit"`). `resolveSigOps I` walks the IR and
-- replaces each `SigOp` node's info with the interpretation's declared
-- `I.info name`. Downstream (`eval`/codegen/`⟦_⟧ᴰ`) reads the resolved,
-- self-describing node unchanged.
------------------------------------------------------------------------

module Once.SigOp.Resolve where

open import Once.IR
open import Once.SigOp.Info using (name)
open import Once.SigOp.Interpretation using (Interpretation)

module _ (I : Interpretation) where
  open Interpretation I using (info)

  -- | Replace every `SigOp` node's placeholder info with the
  -- interpretation's declared `SigOpInfo` for that name. Pure structural
  -- recursion (no `TERMINATING`); identity on every non-`SigOp` node.
  resolveSigOps    : ∀ {A B} → IR A B → IR A B
  resolveSigOps-nt : ∀ {G F} → NatTr G F → NatTr G F

  resolveSigOps id              = id
  resolveSigOps (g ∘ f)         = resolveSigOps g ∘ resolveSigOps f
  resolveSigOps fst             = fst
  resolveSigOps snd             = snd
  resolveSigOps (⟨ f , g ⟩ m)   = ⟨ resolveSigOps f , resolveSigOps g ⟩ m
  resolveSigOps (inl m)         = inl m
  resolveSigOps (inr m)         = inr m
  resolveSigOps (case f g)      = case (resolveSigOps f) (resolveSigOps g)
  resolveSigOps terminal        = terminal
  resolveSigOps initial         = initial
  resolveSigOps (curry f m)     = curry (resolveSigOps f) m
  resolveSigOps apply           = apply
  resolveSigOps arr             = arr
  resolveSigOps (In w m)        = In w m
  resolveSigOps (out-μ w)       = out-μ w
  resolveSigOps (Cata w f)      = Cata w (resolveSigOps f)
  resolveSigOps (Para w f)      = Para w (resolveSigOps f)
  resolveSigOps (Out w)         = Out w
  resolveSigOps (in-ν w m)      = in-ν w m
  resolveSigOps (Ana w f)       = Ana w (resolveSigOps f)
  resolveSigOps (Hylo w₁ w₂ f g) = Hylo w₁ w₂ (resolveSigOps f) (resolveSigOps-nt g)
  resolveSigOps (Fuse w₁ w₂ f g) = Fuse w₁ w₂ (resolveSigOps f) (resolveSigOps-nt g)
  resolveSigOps (free-heap r)   = free-heap r
  resolveSigOps (const p v)     = const p v
  resolveSigOps (SigOp si)      = SigOp (info (name si))

  resolveSigOps-nt ntId         = ntId
  resolveSigOps-nt (ntK ir)     = ntK (resolveSigOps ir)
  resolveSigOps-nt (ntFst t)    = ntFst (resolveSigOps-nt t)
  resolveSigOps-nt (ntSnd t)    = ntSnd (resolveSigOps-nt t)
  resolveSigOps-nt (ntCase t u) = ntCase (resolveSigOps-nt t) (resolveSigOps-nt u)
  resolveSigOps-nt (ntInl t)    = ntInl (resolveSigOps-nt t)
  resolveSigOps-nt (ntInr t)    = ntInr (resolveSigOps-nt t)
  resolveSigOps-nt (ntPair t u) = ntPair (resolveSigOps-nt t) (resolveSigOps-nt u)
