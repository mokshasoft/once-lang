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

open import Data.Bool using (Bool; true; false; _∨_; _∧_; not; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (zero)
open import Once.LinCore.TyEq fmt using (eqT)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List)
import Data.List as L

open import Once.LinCore.Core fmt
open import Once.LinCore.CopyFree fmt using (cells)

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

-- ★ D498 (measured before it is built): which closures' LENT entries a lent call can reach.
-- A lent call through a code word (`bev`) is at a closure type; inside a many-use closure's
-- LENT body it counts only if that closure's type is itself lent-called (a least fixpoint);
-- owned bodies and the table's bodies always count.
private
  Fact : Set
  Fact = Maybe LTy × LTy

  under? : LTy → List Fact → List Fact
  under? T = L.map (λ { (nothing , t) → (just T , t) ; (just c , t) → (just c , t) })

  facts : ∀ {Γ E A B} → Tm Γ E A B → List Fact
  -- the owned entry's lent calls, by its certificate (`o-ev` applies owned: none)
  factsO : ∀ {Γ E A B} (b : Tm Γ E A B) → Own b → List Fact
  factsO b o-bg                         = facts b
  factsO _ o-ev                         = L.[]
  factsO (bfst f) (o-fst o)             = factsO f o
  factsO (bsnd f) (o-snd o)             = factsO f o
  factsO (bfst f ∘l bsnd g) (o-split p q) = factsO f p L.++ factsO g q
  factsO (lcase f g) (o-case p q)       = factsO f p L.++ factsO g q
  factsO ((bfst f ⊗l bsnd g) ∘l s) (o-fork p q) = factsO f p L.++ factsO g q L.++ facts s
  factsO (blift g ∘l t) (o-lift p)      = facts g L.++ factsO t p
  factsO (t ∘l blift f) (o-pre p)       = factsO t p L.++ facts f
  facts (f ∘l g)          = facts f L.++ facts g
  facts (f ⊗l g)          = facts f L.++ facts g
  facts (lcase f g)       = facts f L.++ facts g
  facts (lcata F f)       = facts f
  facts (lend f)          = facts f
  facts (blift f)         = facts f
  facts (bfst f)          = facts f
  facts (bsnd f)          = facts f
  facts (bcaseE f g)      = facts f L.++ facts g
  facts (bout f)          = facts f
  facts (liter f _)       = facts f
  facts (bev {g = g} {A} {B}) = (nothing , Fn many g A B) L.∷ L.[]
  facts (llam b _)        = facts b
  facts (llamω {g = g} {A = A} {B} b _) = under? (Fn many g A B) (facts b) L.++ factsO b (ownOf b)
  facts (llamωᶜ b₀ _)     = facts b₀
  {-# CATCHALL #-}
  facts _                 = L.[]

  factsB : ∀ {Γ σ} → Body Γ σ → List Fact
  factsB (b1 t _) = facts t
  factsB (bω t _) = facts t

  factsD : ∀ {Γ} → Defs Γ → List Fact
  factsD ε        = L.[]
  factsD (ds ▸ b) = factsD ds L.++ factsB b

  elemT : LTy → List LTy → Bool
  elemT t = L.foldr (λ u acc → eqT t u ∨ acc) false

  stepL : List Fact → List LTy → List LTy
  stepL fs l = L.foldr (λ { (nothing , t) acc → if elemT t acc then acc else t L.∷ acc
                          ; (just c , t) acc → if elemT c l ∧ not (elemT t acc) then t L.∷ acc else acc }) l fs

  iter : ℕ → List Fact → List LTy → List LTy
  iter zero    fs l = l
  iter (suc k) fs l = iter k fs (stepL fs l)

  -- each many-use closure: its type, whether its environment owns cells
  closT : ∀ {Γ E A B} → Tm Γ E A B → List (LTy × Bool)
  closT (f ∘l g)          = closT f L.++ closT g
  closT (f ⊗l g)          = closT f L.++ closT g
  closT (lcase f g)       = closT f L.++ closT g
  closT (lcata F f)       = closT f
  closT (lend f)          = closT f
  closT (blift f)         = closT f
  closT (bfst f)          = closT f
  closT (bsnd f)          = closT f
  closT (bcaseE f g)      = closT f L.++ closT g
  closT (bout f)          = closT f
  closT (liter f _)       = closT f
  closT (llam b _)        = closT b
  closT (llamω {g = g} {X} {A} {B} b _)  = (Fn many g A B , false) L.∷ closT b
  closT (llamωᶜ {g = g} {X} {A} {B} b₀ _) = (Fn many g A B , cells X) L.∷ closT b₀
  {-# CATCHALL #-}
  closT _                 = L.[]

  closD : ∀ {Γ} → Defs Γ → List (LTy × Bool)
  closD ε             = L.[]
  closD (ds ▸ b1 t _) = closD ds L.++ closT t
  closD (ds ▸ bω t _) = closD ds L.++ closT t

  count : ∀ {X : Set} → (X → Bool) → List X → ℕ
  count p = L.foldr (λ x n → if p x then suc n else n) 0

lent-reach : ∀ {Γ} → Defs Γ → String
lent-reach ds =
  "lent-entries: total=" ++ show (L.length cs) ++ " pruned=" ++ show (count (λ c → not (elemT (proj₁ c) l)) cs)
  ++ " copying=" ++ show (count proj₂ cs) ++ " copying-pruned=" ++ show (count (λ c → proj₂ c ∧ not (elemT (proj₁ c) l)) cs)
  where
    fs = factsD ds
    l  = iter (suc (L.length fs)) fs L.[]
    cs = closD ds

show-copies : Copies → String
show-copies (copies a b c d) =
  "copies: dups=" ++ show a ++ " dup-cells=" ++ show b ++ " bcopy-cells=" ++ show c ++ " clo-cells=" ++ show d
