-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.CopyFree — plan 0.157 S2 step 3 (D6, D500): a core term that
-- names no copy of a value with cells.
--
-- A core term copies cells in three ways (`Measure.Copies` counts them):
--   * `dup` at a type that owns cells (a deep copy);
--   * `bcopy` at a type that owns cells (a lent value copied out);
--   * a closure that owns its environment (`llamωᶜ`) with cells, at a type the
--     program calls LENT (D498): its lent entry copies the environment.
-- `CF lc t`: none of them anywhere in `t` (a `llamω`'s lent body included;
-- its owned body is `Own.ownT`'s, which moves what the lent body reads).
-- `lc`: the program's lent-called closure types (`Keys.Univ.lct`).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.LinCore.CopyFree (fmt : TargetNum) where

open import Data.Bool using (Bool; true; false; _∨_; _∧_; not; T; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

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

-- no cells: a copy of it is words
NC : LTy → Set
NC A = T (not (cells A))

-- ★ an observation of a ν of layer `G` copies its coalgebra (`Core.strO`, D496): a
-- product gives the owned coalgebra to the side with seed positions (the right if it
-- has some) and LENDS it to the other, which copies it at each of its own seeds
coCopies : LF → Bool
coCopies Idf      = false
coCopies Kone     = false
coCopies Kzero    = false
coCopies (Kb b)   = false
coCopies (Kμ G)   = false
coCopies (G ⊕f H) = coCopies G ∨ coCopies H
coCopies (G ⊗f H) = if hasId H then hasId G ∨ coCopies H else coCopies G

module _ (lc : LTy → Bool) where

  -- ★ the term names no copy of cells
  CF : ∀ {Γ E A B} → Tm Γ E A B → Set
  CF (f ∘l g)          = CF f × CF g
  CF (f ⊗l g)          = CF f × CF g
  CF (lcase f g)       = CF f × CF g
  CF (lcata F f)       = CF f
  CF (lend f)          = CF f
  CF (blift f)         = CF f
  CF (bfst f)          = CF f
  CF (bsnd f)          = CF f
  CF (bcaseE f g)      = CF f × CF g
  CF (bout f)          = CF f
  CF (llam b _)        = CF b
  CF (llamω b _)       = CF b
  CF (llamωᶜ {g = g} {X = X} {A = A} {B = B} b _) = CF b × (T (not (lc (Fn many g A B))) ⊎ NC X)
  CF (liter f _)       = CF f
  CF (dup {A = A})     = NC A
  CF (bcopy {E = E})   = NC E
  -- a ν: observing it (`obsT`, D496) copies its coalgebra where a layer branches
  CF (lunf {F = F})    = T (not (coCopies F))
  {-# CATCHALL #-}
  CF _                 = ⊤

  -- a body, a table: no copy of cells in any of it
  CFB : ∀ {L σ} → Body L σ → Set
  CFB (b1 t _) = CF t
  CFB (bω t _) = CF t

  CFD : ∀ {L} → Defs L → Set
  CFD ε        = ⊤
  CFD (ds ▸ b) = CFD ds × CFB b

------------------------------------------------------------------------
-- The Booleans the conditions come in.
------------------------------------------------------------------------

nc-∨ : ∀ {a b : Bool} → T (not a) → T (not b) → T (not (a ∨ b))
nc-∨ {false} {false} _ _ = tt

T-∧ : ∀ {a b : Bool} → T (a ∧ b) → T a × T b
T-∧ {true} {true} _ = tt , tt

not-∨ʳ : ∀ {a b : Bool} → T (not (a ∨ b)) → T (not b)
not-∨ʳ {false} {false} _ = tt

not-∨ˡ : ∀ {a b : Bool} → T (not (a ∨ b)) → T (not a)
not-∨ˡ {false} {false} _ = tt

notnot : ∀ {a : Bool} → T (not (not a)) → T a
notnot {true} _ = tt

------------------------------------------------------------------------
-- The entries the lowering adds copy nothing more than the body names
-- (D501 route (1)): a many-use closure's OWNED entry (`ownω`, D493) moves
-- what its lent body reads; a closure owning its environment's LENT entry
-- (`cin`, D480) copies the environment, words when it has no cells.
------------------------------------------------------------------------

module _ (lc : LTy → Bool) where

  cf-own : ∀ {Γ X A B} {b : Tm Γ X A B} (o : Own b) → CF lc b → CF lc (ownT o)
  cf-own o-bg          c                = _ , c
  cf-own o-ev          c                = tt
  cf-own (o-fst o)     c                = cf-own o c , _
  cf-own (o-snd o)     c                = cf-own o c , _
  cf-own (o-split p q) (c₁ , c₂)        = cf-own p c₁ , ((tt , cf-own q c₂) , tt)
  cf-own (o-case p q)  (c₁ , c₂)        = (cf-own p c₁ , cf-own q c₂) , tt
  cf-own (o-fork p q)  ((c₁ , c₂) , cs) = (cf-own p c₁ , cf-own q c₂) , (_ , cs)
  cf-own (o-lift p)    (cg , ct)        = cg , cf-own p ct
  cf-own (o-pre p)     (ct , cf)        = cf-own p ct , (tt , cf)

  cf-ownω : ∀ {Γ X A B} (b : Tm Γ X A B) → CF lc b → CF lc (ownω b)
  cf-ownω b c = subst (CF lc) (sym (ownω-≡ b)) (cf-own (ownOf b) c)

  cf-cin : ∀ {Γ X A B} (b₀ : Tm Γ One (X ⊗t A) B) → NC X → CF lc b₀ → CF lc (cin b₀)
  cf-cin b₀ nx c = c , ((nx , tt) , tt)

  -- ★ a ν's observation (`kobs`'s code) copies nothing where its layer does not branch
  cf-strL : ∀ {Γ} F G S → T (not (hasId G)) → CF lc (strL {Γ} F G S)
  cf-strL F Idf      S ()
  cf-strL F Kone     S t = tt
  cf-strL F Kzero    S t = tt
  cf-strL F (Kb b)   S t = tt
  cf-strL F (Kμ G)   S t = tt
  cf-strL F (G ⊕f H) S t = (tt , cf-strL F G S (not-∨ˡ t)) , (tt , cf-strL F H S (not-∨ʳ t))
  cf-strL F (G ⊗f H) S t = cf-strL F G S (not-∨ˡ t) , cf-strL F H S (not-∨ʳ t)

  cf-strO : ∀ {Γ} F G S → T (not (coCopies G)) → CF lc (strO {Γ} F G S)
  cf-strP : ∀ {Γ} F G H S (b : Bool) → hasId H ≡ b → T (not (if b then hasId G ∨ coCopies H else coCopies G))
          → CF lc (strP {Γ} F G H S b)
  cf-strO F Idf      S t = tt
  cf-strO F Kone     S t = _
  cf-strO F Kzero    S t = _
  cf-strO F (Kb b)   S t = _
  cf-strO F (Kμ G)   S t = _
  cf-strO F (G ⊕f H) S t = ((tt , cf-strO F G S (not-∨ˡ t)) , (tt , cf-strO F H S (not-∨ʳ t))) , tt
  cf-strO F (G ⊗f H) S t = cf-strP F G H S (hasId H) refl t
  cf-strP F G H S true  e t =
    (tt , cf-strO F H S (not-∨ʳ t)) , (tt , (_ , (tt , (cf-strL F G S (not-∨ˡ t) , tt))))
  cf-strP F G H S false e t =
    (cf-strO F G S t , tt) , (tt , (tt , cf-strL F H S (subst (λ b → T (not b)) (sym e) tt)))

  cf-mapNu : ∀ {Γ} F G S → T (not (coCopies F)) → CF lc (mapNu {Γ} F G S)
  cf-mapNu F Idf      S t = t
  cf-mapNu F Kone     S t = tt
  cf-mapNu F Kzero    S t = tt
  cf-mapNu F (Kb b)   S t = tt
  cf-mapNu F (Kμ G)   S t = tt
  cf-mapNu F (G ⊕f H) S t = (tt , cf-mapNu F G S t) , (tt , cf-mapNu F H S t)
  cf-mapNu F (G ⊗f H) S t = cf-mapNu F G S t , cf-mapNu F H S t

  cf-obsT : ∀ {Γ} F S → T (not (coCopies F)) → CF lc (obsT {Γ} F S)
  cf-obsT F S t = cf-mapNu F F S t , (cf-strO F F S t , tt)
