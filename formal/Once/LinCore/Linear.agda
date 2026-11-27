-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Linear — plan 0.157 S2 step 3, D500 (decided by the user):
-- `Linear₀`, the first stage of D6's linearity, on the checked program, and
-- its complement: the places where the program is NOT linear, which the
-- compiler names in a warning ("copied here").
--
-- A use of a variable whose type owns cells is OWNING unless it is a read
-- the bridge reads in place (D477, D481, D494, D495, D499). The program is
-- not linear where:
--   * the context is split between two uses (an application, a pair, a
--     case's scrutinee and arms, a `let`, a combinator's parts) and both use
--     a variable owning cells, and no read applies there;
--   * a many-use closure consumes captures owning cells on each call (its
--     body is no read of them), or any closure that does is at a type the
--     program calls lent (D498: its lent entry copies them; D500 addendum);
--   * a fork's two arms take overlapping parts of an argument owning cells.
-- The sites are computed by the same structure as the bridge (`FromExpr.Lq`),
-- so that "no site" is the premise of `NoCopy` (the bridge lemma follows).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.LinCore.Linear (fmt : TargetNum) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)

import Once.Spec.Grade as G
open import Once.Spec.Type using (Ty; _⇒[_]_)
import Once.Spec.Type
import Once.Spec.Context as SC
open import Once.Spec.Context using (Ctx; Usage; []; _∷_; _+ᵘ_; _*ᵘ_)
open import Once.Context using (_⊔ᵘ_)
open import Once.Surface.Map
open import Once.Surface.Syntax

open import Once.LinCore.Core fmt using (LTy; Fn; many; One; Nu)
open import Once.LinCore.CopyFree fmt using (coCopies)
open import Once.LinCore.FromIR fmt using (grade)
open import Once.LinCore.FromExpr fmt
  using (ty; flat?; used?; capCells?; rdl?; rdw?; rdx?; pth?; cp?; CP; cp; arm?; Arm; arm-map; arm-comp; PjL; pjl; IsPj; pj-id; pj-fst; pj-snd)

------------------------------------------------------------------------
-- 1. A SITE: what is owned twice, and which variables (de Bruijn, innermost 0).
------------------------------------------------------------------------

Site : Set
Site = String × List ℕ

-- the variables both shares hold whose types own cells
sharedIx : ∀ {m n} (Γ : Ctx m n) → Usage n → Usage n → List ℕ
sharedIx SC.∅          []        []        = []
sharedIx (Γ SC.▸ A) (q₁ ∷ Ψ₁) (q₂ ∷ Ψ₂) =
  (if used? q₁ ∧ used? q₂ ∧ not (flat? A) then 0 ∷ [] else []) ++ map suc (sharedIx Γ Ψ₁ Ψ₂)

-- the captures whose types own cells
capIx : ∀ {m n} (Γ : Ctx m n) → Usage n → List ℕ
capIx SC.∅          []      = []
capIx (Γ SC.▸ A) (q ∷ Ψ) = (if used? q ∧ not (flat? A) then 0 ∷ [] else []) ++ map suc (capIx Γ Ψ)

site : String → List ℕ → List Site
site k []         = []
site k vs@(_ ∷ _) = (k , vs) ∷ []

splitSite : ∀ {m n} (Γ : Ctx m n) → String → Usage n → Usage n → List Site
splitSite Γ k Ψ₁ Ψ₂ = site k (sharedIx Γ Ψ₁ Ψ₂)

isJust : ∀ {X : Set} → Maybe X → Bool
isJust (just _) = true
isJust nothing  = false

isMany : G.Quantity → Bool
isMany G.Many = true
isMany G.One  = false
isMany G.Zero = false

------------------------------------------------------------------------
-- 2. A FORK'S ARMS: overlapping parts of the argument (`FromExpr.splitP`).
------------------------------------------------------------------------

module _ where
  -- two projections that take overlapping parts with cells (a copy of the smaller)
  ov : ∀ {m} {A Af Ag : Ty m} {pf : Map A Af} {pg : Map A Ag} → IsPj pf → IsPj pg → Bool
  ov (pj-id {A = A})  pj-id        = not (flat? A)
  ov pj-id            (pj-fst {A = X}) = not (flat? X)
  ov pj-id            (pj-snd {B = Y}) = not (flat? Y)
  ov (pj-fst {A = X}) pj-id        = not (flat? X)
  ov (pj-snd {B = Y}) pj-id        = not (flat? Y)
  ov (pj-fst {A = X}) pj-fst       = not (flat? X)
  ov (pj-snd {B = Y}) pj-snd       = not (flat? Y)
  ov pj-fst           pj-snd       = false
  ov pj-snd           pj-fst       = false

  -- the projection an arm takes (the whole argument when it is no projection)
  armK : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m} {k} {f : Expr Γ Ψ (A ⇒[ k ] B)}
       → Maybe (Arm f) → (∀ {Af} {mp : Map A Af} → IsPj mp → Bool) → Bool
  armK nothing                       c = c pj-id
  armK (just (arm-map (pjl p)))      c = c p
  armK (just (arm-comp h (pjl p)))   c = c p

------------------------------------------------------------------------
-- 3. ★ THE SITES, clause for clause the bridge. `lc`: the program's
-- lent-called closure types (D498), for the whole-program condition.
------------------------------------------------------------------------

module _ (lc : LTy → Bool) where

  -- a closure over captures: does it consume them where that copies?
  cloSite : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) (q : G.Quantity) (read : Bool) (T : LTy) → List Site
  cloSite Γ Ψ q read T =
    -- (only a LENT call copies them, D498: owned, the closure is applied once and consumed)
    if not read ∧ lc T
    then site "a closure consumes its captures and the program calls closures of its type lent" (capIx Γ Ψ)
    else []

  -- an application at `Many`: a case combinator branches (its arms distributed; the argument
  -- read or split off); else the argument read in place where it saves a copy (`appR`), or the split
  appSite : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m} (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Many G.pure ] B))
            (x : Expr Γ Ψ₂ A) → Maybe (CP f) → List Site
  appSite {Γ = Γ} {Ψ₁} {Ψ₂} f x (just _) =
    if isJust (rdw? x) then [] else splitSite Γ "a case combinator and its argument" Ψ₁ (G.Many *ᵘ Ψ₂)
  appSite {Γ = Γ} {Ψ₁} {Ψ₂} f x nothing =
    if isJust (pth? f) ∧ isJust (rdx? Ψ₁ Ψ₂ x) then []
    else splitSite Γ "the function and the argument of an application" Ψ₁ (G.Many *ᵘ Ψ₂)

  -- a closure whose environment holds a closure or a ν (so owns cells), at type `T`
  heldSite : String → LTy → List Site
  heldSite k T = if lc T then (k , []) ∷ [] else []

  -- ★ a ν whose layer branches: each observation copies its coalgebra (`Core.strO`, D496)
  nuSite : LTy → List Site
  nuSite (Nu F) = if coCopies F then ("an unfold whose layer branches: each observation copies its coalgebra" , []) ∷ [] else []
  {-# CATCHALL #-}
  nuSite _      = []

  -- a structure map whose code builds such a closure (`FromExpr.mapT`)
  mapSite : ∀ {m} {A B : Ty m} → Map A B → List Site
  mapSite {B = B} (mp-apply _ _ (G.fin G.actᶠ)) = heldSite "an action suspended over a closure, called lent" (ty B)
  mapSite {B = B} (mp-apply _ _ G.eff)          = heldSite "an action suspended over a closure, called lent" (ty B)
  mapSite {B = B} (mp-Out _ G.actᶠ _)           = heldSite "an unfolding suspended over its stream, called lent" (ty B)
  {-# CATCHALL #-}
  mapSite _ = []

  -- the function of an application at `Many`: a case combinator applied at once is a BRANCH
  -- (the bridge distributes the context to its arms, no split of its own), else as it stands
  sitesFn : ∀ {m n} {Γ : Ctx m n} {Ψ₁ : Usage n} {A B : Ty m} (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Many G.pure ] B))
          → Maybe (CP f) → List Site

  sites : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} → Expr Γ Ψ A → List Site
  sites (var i) = []
  sites {Γ = Γ} (lam {Ψ = Ψ} {q' = G.Zero} {π = π} {A = A} {B = B} q _ e) =
    sites e ++ cloSite Γ Ψ q false (ty (A ⇒[ G.mk-kind q π ] B))
  sites {Γ = Γ} (lam {Ψ = Ψ} {q' = G.One} {π = π} {A = A} {B = B} q _ e) =
    sites e ++ cloSite Γ Ψ q (isJust (rdl? e)) (ty (A ⇒[ G.mk-kind q π ] B))
  sites {Γ = Γ} (lam {Ψ = Ψ} {q' = G.Many} {π = π} {A = A} {B = B} q _ e) =
    sites e ++ cloSite Γ Ψ q (isJust (rdl? e)) (ty (A ⇒[ G.mk-kind q π ] B))
  sites (app {q = G.Zero} f x) = sites f
  sites {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} f x) =
    sites f ++ sites x ++ splitSite Γ "the function and the argument of an application" Ψ₁ (G.One *ᵘ Ψ₂)
  sites (app {q = G.Many} f x) = sitesFn f (cp? f) ++ sites x ++ appSite f x (cp? f)
  sites {Γ = Γ} (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {B = B} {q = G.Zero} {π = π} f x) =
    sites f ++ cloSite Γ Ψ₁ G.One false (Fn many (grade π) One (ty B))
  sites {Γ = Γ} (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {B = B} {q = G.One} {π = π} f x) =
    sites f ++ sites x ++ splitSite Γ "the function and the argument of a suspended application" Ψ₁ (G.One *ᵘ Ψ₂)
    ++ cloSite Γ (Ψ₁ +ᵘ (G.One *ᵘ Ψ₂)) G.One false (Fn many (grade π) One (ty B))
  sites {Γ = Γ} (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {B = B} {q = G.Many} {π = π} f x) =
    sites f ++ sites x ++ splitSite Γ "the function and the argument of a suspended application" Ψ₁ (G.Many *ᵘ Ψ₂)
    ++ cloSite Γ (Ψ₁ +ᵘ (G.Many *ᵘ Ψ₂)) G.One false (Fn many (grade π) One (ty B))
  sites {Γ = Γ} (pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
    sites a ++ sites b ++ (if isJust (rdw? a) then [] else splitSite Γ "the two components of a pair" Ψ₁ Ψ₂)
  sites (fst' p) = sites p
  sites (snd' p) = sites p
  sites (inl' a) = sites a
  sites (inr' b) = sites b
  sites {Γ = Γ} (case' {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} s l r) =
    sites s ++ sites l ++ sites r
    ++ (if isJust (rdw? s) then [] else splitSite Γ "a case's scrutinee and its arms" Ψs (Ψₗ ⊔ᵘ Ψᵣ))
  sites unit = []
  sites (absurd v) = sites v
  sites (let' {q = G.Zero} e1 e2) = sites e2
  sites {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} e1 e2) =
    sites e1 ++ sites e2 ++ splitSite Γ "a let's body and its binding" Ψ₂ (G.One *ᵘ Ψ₁)
  sites {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} e1 e2) =
    sites e1 ++ sites e2 ++ splitSite Γ "a let's body and its binding" Ψ₂ (G.Many *ᵘ Ψ₁)
  sites (int n) = []
  sites (float d) = []
  sites (num h o e) = sites e
  sites (coerce p f) = sites f
  sites (sigOp name c) = []
  sites (closure name) = []
  sites (poly name _) = []
  sites (closed e) = sites e
  sites (lift-morphism mp) = mapSite mp
  sites (morph-app mp x) = sites x ++ mapSite mp
  sites {Γ = Γ} (comp' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) =
    sites f ++ sites g ++ splitSite Γ "the two closures of a composition" Ψ₁ (G.Many *ᵘ Ψ₂)
  sites {Γ = Γ} (copair' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) =
    sites f ++ sites g ++ splitSite Γ "the two arms of a case combinator" Ψ₁ Ψ₂
  sites {Γ = Γ} (fork' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) =
    sites f ++ sites g ++ splitSite Γ "the two arms of a fork" Ψ₁ Ψ₂
    ++ (if armK (arm? f) (λ p → armK (arm? g) (λ q → ov p q))
        then ("a fork's two arms take overlapping parts of its argument" , []) ∷ [] else [])
  sites (curry' {A = A} {B = B} {C = C} {π₀ = π₀} {π = π} f) =
    sites f ++ heldSite "a curried closure over its function, called lent" (ty (A ⇒[ G.mk-kind G.Many π₀ ] (B ⇒[ G.mk-kind G.Many π ] C)))
    ++ heldSite "a curried closure over its function and first argument, called lent" (ty (B ⇒[ G.mk-kind G.Many π ] C))
  sites (cata wfF alg) = sites alg
  sites (ana {F = F} {A = A} {π₀ = π₀} {φ = φ} wfF coalg) =
    sites coalg ++ heldSite "an unfold over its coalgebra, called lent" (ty (A ⇒[ G.mk-kind G.Many π₀ ] Once.Spec.Type.ν F φ))
    ++ nuSite (ty (Once.Spec.Type.ν F φ))
  sites (loop round) = sites round

  sitesFn (copair' f g) (just (cp _ _)) = sites f ++ sites g
  sitesFn f             nothing         = sites f

  -- ★ `Linear₀`: no site
  linear? : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} → Expr Γ Ψ A → Bool
  linear? e = nullL (sites e)
    where
      nullL : List Site → Bool
      nullL []      = true
      nullL (_ ∷ _) = false
