-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Measure.Copies — `once stats`: the copies a program's core makes
-- (plan 0.157 S2, D6: a linear program copies nothing).
--
-- Counted over the table's bodies (the bridge's output, before lowering):
--   dups         every `dup`
--   dup-cells    a `dup` at a type that owns cells (a deep copy at run time)
--   bcopy-cells  a lent value copied out at a type that owns cells
--   clo-cells    a many-use closure whose environment owns cells: each LENT call
--                (a fold's layer, a loop's round) copies that environment (D480)
-- A `dup` or `bcopy` at a type without cells is words, not cells.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.Measure.Copies (fmt : TargetNum) where

open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List)
import Data.List as L

open import Once.LinCore.Core fmt

-- a type whose values own cells
cells : LTy → Bool
cells One        = false
cells Zero       = false
cells (Bt _)     = false
cells (A ⊗t B)   = cells A ∨ cells B
cells (A ⊕t B)   = cells A ∨ cells B
cells (Ct _ X)   = cells X
cells (Fn _ _ _ _) = true
cells (Nu _)     = true
cells (μt _)     = true

record Copies : Set where
  constructor copies
  field
    dups dup-cells bcopy-cells clo-cells : ℕ

private
  none : Copies
  none = copies 0 0 0 0

  _⊞_ : Copies → Copies → Copies
  copies a b c d ⊞ copies a′ b′ c′ d′ = copies (a + a′) (b + b′) (c + c′) (d + d′)

  bump : Bool → ℕ → ℕ
  bump b n = if b then suc n else n

tm : ∀ {Γ E A B} → Tm Γ E A B → Copies
tm (f ∘l g)          = tm f ⊞ tm g
tm (f ⊗l g)          = tm f ⊞ tm g
tm (lcase f g)       = tm f ⊞ tm g
tm (lcata F f)       = tm f
tm (lend f)          = tm f
tm (blift f)         = tm f
tm (bfst f)          = tm f
tm (bsnd f)          = tm f
tm (bcaseE f g)      = tm f ⊞ tm g
tm (bout f)          = tm f
tm (llam b _)        = tm b
tm (llamω b _)       = tm b
tm (llamωᶜ {X = X} b _) = copies 0 0 0 (bump (cells X) 0) ⊞ tm b
tm (liter f _)       = tm f
tm (dup {A = A})     = copies 1 (bump (cells A) 0) 0 0
tm (bcopy {E = E})   = copies 0 0 (bump (cells E) 0) 0
{-# CATCHALL #-}
tm _                 = none

body : ∀ {Γ σ} → Body Γ σ → Copies
body (b1 t _) = tm t
body (bω t _) = tm t

defs : ∀ {Γ} → Defs Γ → Copies
defs ε        = none
defs (ds ▸ b) = defs ds ⊞ body b

-- ★ plan 0.157 S2: where the closures that copy their environment on a lent call are:
-- each `llamωᶜ` whose environment owns cells, by its environment's type and its body's head
showT : LTy → String
showT One          = "1"
showT Zero         = "0"
showT (Bt _)       = "w"
showT (A ⊗t B)     = "(" ++ showT A ++ "*" ++ showT B ++ ")"
showT (A ⊕t B)     = "(" ++ showT A ++ "+" ++ showT B ++ ")"
showT (Ct _ X)     = "C" ++ showT X
showT (Fn _ _ _ _) = "Fn"
showT (Nu _)       = "Nu"
showT (μt _)       = "Mu"

private
  headOf : ∀ {Γ E A B} → Tm Γ E A B → String
  headOf (f ∘l g)   = headOf f ++ "." ++ headOf g
  headOf (f ⊗l g)   = "<" ++ headOf f ++ "|" ++ headOf g ++ ">"
  headOf lunf       = "unf"
  headOf lid        = "id"
  headOf lassoc     = "a"
  headOf (lapp _)   = "app"
  {-# CATCHALL #-}
  headOf _          = "_"

  sitesT : ∀ {Γ E A B} → Tm Γ E A B → List String
  sitesT (f ∘l g)          = sitesT f L.++ sitesT g
  sitesT (f ⊗l g)          = sitesT f L.++ sitesT g
  sitesT (lcase f g)       = sitesT f L.++ sitesT g
  sitesT (lcata F f)       = sitesT f
  sitesT (lend f)          = sitesT f
  sitesT (blift f)         = sitesT f
  sitesT (bfst f)          = sitesT f
  sitesT (bsnd f)          = sitesT f
  sitesT (bcaseE f g)      = sitesT f L.++ sitesT g
  sitesT (bout f)          = sitesT f
  sitesT (llam b _)        = sitesT b
  sitesT (llamω b _)       = sitesT b
  sitesT (llamωᶜ {X = X} b _) =
    (if cells X then (showT X ++ ":" ++ headOf b) L.∷ L.[] else L.[]) L.++ sitesT b
  sitesT (liter f _)       = sitesT f
  {-# CATCHALL #-}
  sitesT _                 = L.[]

  sitesB : ∀ {Γ σ} → Body Γ σ → List String
  sitesB (b1 t _) = sitesT t
  sitesB (bω t _) = sitesT t

clo-sites : ∀ {Γ} → Defs Γ → List String
clo-sites ε        = L.[]
clo-sites (ds ▸ b) = clo-sites ds L.++ sitesB b

show-sites : List String → String
show-sites xs = "clo-sites:" ++ L.foldr (λ s acc → " " ++ s ++ acc) "" xs

show-copies : Copies → String
show-copies (copies a b c d) =
  "copies: dups=" ++ show a ++ " dup-cells=" ++ show b ++ " bcopy-cells=" ++ show c ++ " clo-cells=" ++ show d
