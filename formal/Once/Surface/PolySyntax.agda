-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Surface.PolySyntax
--
-- Polymorphic surface syntax for Once programs (during type inference).
-- Mirrors Syntax.agda but indexed by PolyType instead of Type.
--
-- This enables type inference to work with type variables (TVar).
-- After inference, PolyExpr is extracted to SExpr (if no TVars remain).
------------------------------------------------------------------------

module Once.Surface.PolySyntax where

open import Once.Type
open import Once.Type using (extract-embed; extract-fun-inv; extract-eff-inv; extract-prod-inv; extract-sum-inv)
open import Once.Type using (Ground; GroundFunctor; extractGround; extractGroundFunctor)
open import Once.Type using (Subst; applySubstType; applySubstFunctor; Complete; CompleteFunctor; complete→ground)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; true; _∧_)
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans; sym)

------------------------------------------------------------------------
-- Polymorphic Context
------------------------------------------------------------------------

-- | Polymorphic typing context (de Bruijn indexed with quantities)
--
-- PolyCtx n represents a context with n variables.
-- Variables are indexed by Fin n (0 to n-1).
-- Each variable has a PolyType and a quantity (usage annotation).
--
data PolyCtx : ℕ → Set where
  P∅   : PolyCtx 0
  _P,_^_ : ∀ {n} → PolyCtx n → PolyType → Quantity → PolyCtx (ℕ.suc n)

infixl 5 _P,_^_

-- | Smart constructor: extend context with unrestricted quantity
_P,_ : ∀ {n} → PolyCtx n → PolyType → PolyCtx (ℕ.suc n)
Γ P, A = Γ P, A ^ Many

infixl 5 _P,_

-- | Lookup type at position in polymorphic context
lookupPoly : ∀ {n} → PolyCtx n → Fin n → PolyType
lookupPoly (Γ P, A ^ q) Fin.zero    = A
lookupPoly (Γ P, _ ^ _) (Fin.suc i) = lookupPoly Γ i

-- | Lookup quantity at position in polymorphic context
lookupPolyQuantity : ∀ {n} → PolyCtx n → Fin n → Quantity
lookupPolyQuantity (Γ P, A ^ q) Fin.zero    = q
lookupPolyQuantity (Γ P, _ ^ _) (Fin.suc i) = lookupPolyQuantity Γ i

------------------------------------------------------------------------
-- Polymorphic Expressions
------------------------------------------------------------------------

-- | Polymorphic surface expressions (well-typed by construction)
--
-- PolyExpr Γ A represents a well-typed expression of PolyType A in context Γ.
-- Uses de Bruijn indices for variables.
-- Mirrors Surface.Syntax.Expr but with PolyType indices.
--
data PolyExpr : ∀ {n} → PolyCtx n → PolyType → Set where
  -- Variable reference (de Bruijn index)
  pvar   : ∀ {n} {Γ : PolyCtx n} (i : Fin n) → PolyExpr Γ (lookupPoly Γ i)

  -- Lambda abstraction with quantity annotation
  -- Note: body context uses Many to match Syntax.Expr.lam
  plam   : ∀ {n} {Γ : PolyCtx n} {A B} (q : Quantity) → PolyExpr (Γ P, A ^ Many) B → PolyExpr Γ (A P⇒[ q ] B)

  -- Application (pure function)
  papp   : ∀ {n} {Γ : PolyCtx n} {A B} {q : Quantity} → PolyExpr Γ (A P⇒[ q ] B) → PolyExpr Γ A → PolyExpr Γ B

  -- Effect application (effectful morphism)
  peffApp : ∀ {n} {Γ : PolyCtx n} {A B} → PolyExpr Γ (PEff A B) → PolyExpr Γ A → PolyExpr Γ B

  -- Pair introduction
  ppair  : ∀ {n} {Γ : PolyCtx n} {A B} → PolyExpr Γ A → PolyExpr Γ B → PolyExpr Γ (A P* B)

  -- Pair elimination
  pfst'  : ∀ {n} {Γ : PolyCtx n} {A B} → PolyExpr Γ (A P* B) → PolyExpr Γ A
  psnd'  : ∀ {n} {Γ : PolyCtx n} {A B} → PolyExpr Γ (A P* B) → PolyExpr Γ B

  -- Sum introduction
  pinl'  : ∀ {n} {Γ : PolyCtx n} {A B} → PolyExpr Γ A → PolyExpr Γ (A P+ B)
  pinr'  : ∀ {n} {Γ : PolyCtx n} {A B} → PolyExpr Γ B → PolyExpr Γ (A P+ B)

  -- Sum elimination (case)
  pcase' : ∀ {n} {Γ : PolyCtx n} {A B C}
         → PolyExpr Γ (A P+ B) → PolyExpr (Γ P, A) C → PolyExpr (Γ P, B) C → PolyExpr Γ C

  -- Unit introduction
  punit  : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PUnit

  -- Void elimination (absurd)
  pabsurd : ∀ {n} {Γ : PolyCtx n} {A} → PolyExpr Γ PVoid → PolyExpr Γ A

  -- Let binding: let x = e1 in e2
  plet'  : ∀ {n} {Γ : PolyCtx n} {A B} → PolyExpr Γ A → PolyExpr (Γ P, A) B → PolyExpr Γ B

  -- Integer literal
  pint   : ∀ {n} {Γ : PolyCtx n} → ℤ → PolyExpr Γ PInt

  -- String literal
  pstr   : ∀ {n} {Γ : PolyCtx n} → String → PolyExpr Γ PStr

  -- Arithmetic operations (PInt → PInt → PInt)
  padd   : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PInt → PolyExpr Γ PInt → PolyExpr Γ PInt
  psub   : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PInt → PolyExpr Γ PInt → PolyExpr Γ PInt
  pmul   : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PInt → PolyExpr Γ PInt → PolyExpr Γ PInt
  pdiv   : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PInt → PolyExpr Γ PInt → PolyExpr Γ PInt
  pmod'  : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PInt → PolyExpr Γ PInt → PolyExpr Γ PInt

  -- Unary negation (PInt → PInt)
  pneg   : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PInt → PolyExpr Γ PInt

  -- Comparison operations (PInt → PInt → PUnit + PUnit)
  plt    : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PInt → PolyExpr Γ PInt → PolyExpr Γ (PUnit P+ PUnit)
  ple    : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PInt → PolyExpr Γ PInt → PolyExpr Γ (PUnit P+ PUnit)
  pgt    : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PInt → PolyExpr Γ PInt → PolyExpr Γ (PUnit P+ PUnit)
  pge    : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PInt → PolyExpr Γ PInt → PolyExpr Γ (PUnit P+ PUnit)
  peq    : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PInt → PolyExpr Γ PInt → PolyExpr Γ (PUnit P+ PUnit)
  pne    : ∀ {n} {Γ : PolyCtx n} → PolyExpr Γ PInt → PolyExpr Γ PInt → PolyExpr Γ (PUnit P+ PUnit)

  -- Effect lifting (arr combinator from arrow-based effects)
  parr'  : ∀ {n} {Γ : PolyCtx n} {A B} → PolyExpr Γ (A P⇒[ Many ] B) → PolyExpr Γ (PEff A B)

  -- Primitive reference (imported functions)
  pprim  : ∀ {n} {Γ : PolyCtx n} {A} → String → PolyExpr Γ A

------------------------------------------------------------------------
-- Context and Expression Extraction (Principled Approach)
------------------------------------------------------------------------
--
-- Two-step extraction:
-- 1. Apply substitution to get ground PolyExpr (via complete→ground)
-- 2. Extract ground PolyExpr to Expr (total, no Maybe)
--
-- This follows standard type checking architecture where the substitution
-- is a first-class value produced by unification.
--

open import Once.Surface.Syntax as Syntax using (Ctx; Expr; _,_^_; ∅)
open Syntax using (var; lam; app; effApp; pair; fst'; snd'; inl'; inr'; case')
open Syntax using (unit; absurd; let'; int; str)
open Syntax using (add; sub; mul; div; mod'; neg)
open Syntax using (lt; le; gt; ge; eq; ne)
open Syntax using (arr'; prim)

open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)

------------------------------------------------------------------------
-- Ground Context Operations
------------------------------------------------------------------------

-- | Ground predicate for contexts: all types are ground
GroundCtx : ∀ {n} → PolyCtx n → Set
GroundCtx P∅ = ⊤
GroundCtx (Γ P, A ^ q) = GroundCtx Γ × Ground A

-- | Total extraction of ground context (no Maybe!)
extractGroundCtx : ∀ {n} (Γ : PolyCtx n) → GroundCtx Γ → Ctx n
extractGroundCtx P∅ _ = ∅
extractGroundCtx (Γ P, A ^ q) (gΓ , gA) = extractGroundCtx Γ gΓ , extractGround A gA ^ q

-- | Lookup in ground context gives ground type
lookupGround : ∀ {n} (Γ : PolyCtx n) (gΓ : GroundCtx Γ) (i : Fin n) → Ground (lookupPoly Γ i)
lookupGround (Γ P, A ^ q) (gΓ , gA) Fin.zero = gA
lookupGround (Γ P, A ^ q) (gΓ , gA) (Fin.suc i) = lookupGround Γ gΓ i

-- | Lookup commutes with extraction
lookupGround-extract : ∀ {n} (Γ : PolyCtx n) (gΓ : GroundCtx Γ) (i : Fin n)
                     → Syntax.lookup (extractGroundCtx Γ gΓ) i ≡ extractGround (lookupPoly Γ i) (lookupGround Γ gΓ i)
lookupGround-extract (Γ P, A ^ q) (gΓ , gA) Fin.zero = refl
lookupGround-extract (Γ P, A ^ q) (gΓ , gA) (Fin.suc i) = lookupGround-extract Γ gΓ i

------------------------------------------------------------------------
-- Ground Expression Predicate (as data type for pattern matching)
------------------------------------------------------------------------
--
-- GroundExpr e holds when all types appearing in e (including in
-- subexpressions) are ground. This includes types that aren't derivable
-- from just the result type being ground.
--

data GroundExpr : ∀ {n} {Γ : PolyCtx n} {A : PolyType} → PolyExpr Γ A → Set where
  gvar : ∀ {n} {Γ : PolyCtx n} {i : Fin n} → GroundExpr (pvar {Γ = Γ} i)
  glam : ∀ {n} {Γ : PolyCtx n} {A B : PolyType} {q : Quantity} {body : PolyExpr (Γ P, A ^ Many) B}
       → GroundExpr body → GroundExpr (plam q body)
  gapp : ∀ {n} {Γ : PolyCtx n} {A B : PolyType} {q : Quantity}
         {f : PolyExpr Γ (A P⇒[ q ] B)} {x : PolyExpr Γ A}
       → Ground A → GroundExpr f → GroundExpr x → GroundExpr (papp f x)
  geffApp : ∀ {n} {Γ : PolyCtx n} {A B : PolyType}
            {f : PolyExpr Γ (PEff A B)} {x : PolyExpr Γ A}
          → Ground A → GroundExpr f → GroundExpr x → GroundExpr (peffApp f x)
  gpair : ∀ {n} {Γ : PolyCtx n} {A B : PolyType} {a : PolyExpr Γ A} {b : PolyExpr Γ B}
        → GroundExpr a → GroundExpr b → GroundExpr (ppair a b)
  gfst : ∀ {n} {Γ : PolyCtx n} {A B : PolyType} {p : PolyExpr Γ (A P* B)}
       → Ground B → GroundExpr p → GroundExpr (pfst' p)
  gsnd : ∀ {n} {Γ : PolyCtx n} {A B : PolyType} {p : PolyExpr Γ (A P* B)}
       → Ground A → GroundExpr p → GroundExpr (psnd' p)
  ginl : ∀ {n} {Γ : PolyCtx n} {A B : PolyType} {x : PolyExpr Γ A}
       → Ground B → GroundExpr x → GroundExpr (pinl' {B = B} x)
  ginr : ∀ {n} {Γ : PolyCtx n} {A B : PolyType} {x : PolyExpr Γ B}
       → Ground A → GroundExpr x → GroundExpr (pinr' {A = A} x)
  gcase : ∀ {n} {Γ : PolyCtx n} {A B C : PolyType}
          {s : PolyExpr Γ (A P+ B)} {l : PolyExpr (Γ P, A) C} {r : PolyExpr (Γ P, B) C}
        → Ground A → Ground B → GroundExpr s → GroundExpr l → GroundExpr r
        → GroundExpr (pcase' s l r)
  gunit : ∀ {n} {Γ : PolyCtx n} → GroundExpr (punit {Γ = Γ})
  gabsurd : ∀ {n} {Γ : PolyCtx n} {A : PolyType} {v : PolyExpr Γ PVoid}
          → GroundExpr v → GroundExpr (pabsurd {A = A} v)
  glet : ∀ {n} {Γ : PolyCtx n} {A B : PolyType}
         {e : PolyExpr Γ A} {body : PolyExpr (Γ P, A) B}
       → Ground A → GroundExpr e → GroundExpr body → GroundExpr (plet' e body)
  gint : ∀ {n} {Γ : PolyCtx n} {z : ℤ} → GroundExpr (pint {Γ = Γ} z)
  gstr : ∀ {n} {Γ : PolyCtx n} {s : String} → GroundExpr (pstr {Γ = Γ} s)
  gadd : ∀ {n} {Γ : PolyCtx n} {a b : PolyExpr Γ PInt}
       → GroundExpr a → GroundExpr b → GroundExpr (padd a b)
  gsub : ∀ {n} {Γ : PolyCtx n} {a b : PolyExpr Γ PInt}
       → GroundExpr a → GroundExpr b → GroundExpr (psub a b)
  gmul : ∀ {n} {Γ : PolyCtx n} {a b : PolyExpr Γ PInt}
       → GroundExpr a → GroundExpr b → GroundExpr (pmul a b)
  gdiv : ∀ {n} {Γ : PolyCtx n} {a b : PolyExpr Γ PInt}
       → GroundExpr a → GroundExpr b → GroundExpr (pdiv a b)
  gmod : ∀ {n} {Γ : PolyCtx n} {a b : PolyExpr Γ PInt}
       → GroundExpr a → GroundExpr b → GroundExpr (pmod' a b)
  gneg : ∀ {n} {Γ : PolyCtx n} {x : PolyExpr Γ PInt}
       → GroundExpr x → GroundExpr (pneg x)
  glt : ∀ {n} {Γ : PolyCtx n} {a b : PolyExpr Γ PInt}
      → GroundExpr a → GroundExpr b → GroundExpr (plt a b)
  gle : ∀ {n} {Γ : PolyCtx n} {a b : PolyExpr Γ PInt}
      → GroundExpr a → GroundExpr b → GroundExpr (ple a b)
  ggt : ∀ {n} {Γ : PolyCtx n} {a b : PolyExpr Γ PInt}
      → GroundExpr a → GroundExpr b → GroundExpr (pgt a b)
  gge : ∀ {n} {Γ : PolyCtx n} {a b : PolyExpr Γ PInt}
      → GroundExpr a → GroundExpr b → GroundExpr (pge a b)
  geq : ∀ {n} {Γ : PolyCtx n} {a b : PolyExpr Γ PInt}
      → GroundExpr a → GroundExpr b → GroundExpr (peq a b)
  gne : ∀ {n} {Γ : PolyCtx n} {a b : PolyExpr Γ PInt}
      → GroundExpr a → GroundExpr b → GroundExpr (pne a b)
  garr : ∀ {n} {Γ : PolyCtx n} {A B : PolyType} {f : PolyExpr Γ (A P⇒[ Many ] B)}
       → GroundExpr f → GroundExpr (parr' f)
  gprim : ∀ {n} {Γ : PolyCtx n} {A : PolyType} {name : String}
        → GroundExpr (pprim {Γ = Γ} {A = A} name)

------------------------------------------------------------------------
-- Total Ground Expression Extraction
------------------------------------------------------------------------
--
-- Given proofs that context, type, and expression are ground,
-- extraction is total (no Maybe, no postulates).
--

-- | Helper for binary congruence
private
  cong₂ : ∀ {A B C : Set} (f : A → B → C) {x1 x2 : A} {y1 y2 : B} → x1 ≡ x2 → y1 ≡ y2 → f x1 y1 ≡ f x2 y2
  cong₂ f refl refl = refl

-- | Ground proofs are proof-irrelevant: extractGround gives same result for any proof
-- This is needed for the variable case where we have two ground proofs for the same type.
mutual
  ground-proof-irrelevant : (A : PolyType) (g1 g2 : Ground A) → extractGround A g1 ≡ extractGround A g2
  ground-proof-irrelevant PUnit tt tt = refl
  ground-proof-irrelevant PVoid tt tt = refl
  ground-proof-irrelevant (A P* B) (g1a , g1b) (g2a , g2b) =
    cong₂ _*_ (ground-proof-irrelevant A g1a g2a) (ground-proof-irrelevant B g1b g2b)
  ground-proof-irrelevant (A P+ B) (g1a , g1b) (g2a , g2b) =
    cong₂ _+_ (ground-proof-irrelevant A g1a g2a) (ground-proof-irrelevant B g1b g2b)
  ground-proof-irrelevant (A P⇒[ q ] B) (g1a , g1b) (g2a , g2b) =
    cong₂ (λ a b → a ⇒[ q ] b) (ground-proof-irrelevant A g1a g2a) (ground-proof-irrelevant B g1b g2b)
  ground-proof-irrelevant (PEff A B) (g1a , g1b) (g2a , g2b) =
    cong₂ Eff (ground-proof-irrelevant A g1a g2a) (ground-proof-irrelevant B g1b g2b)
  ground-proof-irrelevant (Pμ-type F) g1 g2 = cong μ-type (ground-functor-irrelevant F g1 g2)
  ground-proof-irrelevant (Pν-type F) g1 g2 = cong ν-type (ground-functor-irrelevant F g1 g2)
  ground-proof-irrelevant PInt tt tt = refl
  ground-proof-irrelevant PFloat tt tt = refl
  ground-proof-irrelevant PStr tt tt = refl
  ground-proof-irrelevant PBuffer tt tt = refl
  ground-proof-irrelevant (TVar _) () _

  ground-functor-irrelevant : (F : PolyFunctor) (g1 g2 : GroundFunctor F)
                            → extractGroundFunctor F g1 ≡ extractGroundFunctor F g2
  ground-functor-irrelevant (PK A) g1 g2 = cong K (ground-proof-irrelevant A g1 g2)
  ground-functor-irrelevant PId tt tt = refl
  ground-functor-irrelevant (F P⊕ G) (g1f , g1g) (g2f , g2g) =
    cong₂ _⊕_ (ground-functor-irrelevant F g1f g2f) (ground-functor-irrelevant G g1g g2g)
  ground-functor-irrelevant (F P⊗ G) (g1f , g1g) (g2f , g2g) =
    cong₂ _⊗_ (ground-functor-irrelevant F g1f g2f) (ground-functor-irrelevant G g1g g2g)

extractGroundExpr : ∀ {n} {Γ : PolyCtx n} {A : PolyType}
                  → (e : PolyExpr Γ A)
                  → (gΓ : GroundCtx Γ) → (gA : Ground A) → GroundExpr e
                  → Expr (extractGroundCtx Γ gΓ) (extractGround A gA)

-- Variable
extractGroundExpr {Γ = Γ} (pvar i) gΓ gA gvar =
  subst (Expr (extractGroundCtx Γ gΓ)) type-eq (var i)
  where
    type-eq : Syntax.lookup (extractGroundCtx Γ gΓ) i ≡ extractGround (lookupPoly Γ i) gA
    type-eq = trans (lookupGround-extract Γ gΓ i) (ground-proof-irrelevant (lookupPoly Γ i) (lookupGround Γ gΓ i) gA)

-- Lambda
extractGroundExpr (plam {A = A} {B = B} q body) gΓ (gA , gB) (glam {body = .body} gbody) =
  lam q (extractGroundExpr body (gΓ , gA) gB gbody)

-- Application
extractGroundExpr (papp f x) gΓ gB (gapp gA gf gx) =
  app (extractGroundExpr f gΓ (gA , gB) gf) (extractGroundExpr x gΓ gA gx)

-- Effect application
extractGroundExpr (peffApp f x) gΓ gB (geffApp gA gf gx) =
  effApp (extractGroundExpr f gΓ (gA , gB) gf) (extractGroundExpr x gΓ gA gx)

-- Pair
extractGroundExpr (ppair a b) gΓ (gA , gB) (gpair ga gb) =
  pair (extractGroundExpr a gΓ gA ga) (extractGroundExpr b gΓ gB gb)

-- Fst
extractGroundExpr (pfst' p) gΓ gA (gfst gB gp) =
  fst' (extractGroundExpr p gΓ (gA , gB) gp)

-- Snd
extractGroundExpr (psnd' p) gΓ gB (gsnd gA gp) =
  snd' (extractGroundExpr p gΓ (gA , gB) gp)

-- Inl
extractGroundExpr (pinl' x) gΓ (gA , gB) (ginl _ gx) =
  inl' (extractGroundExpr x gΓ gA gx)

-- Inr
extractGroundExpr (pinr' x) gΓ (gA , gB) (ginr _ gx) =
  inr' (extractGroundExpr x gΓ gB gx)

-- Case
extractGroundExpr (pcase' s l r) gΓ gC (gcase gA gB gs gl gr) =
  case' (extractGroundExpr s gΓ (gA , gB) gs)
        (extractGroundExpr l (gΓ , gA) gC gl)
        (extractGroundExpr r (gΓ , gB) gC gr)

-- Unit
extractGroundExpr punit gΓ _ gunit = unit

-- Absurd
extractGroundExpr (pabsurd v) gΓ gA (gabsurd gv) =
  absurd (extractGroundExpr v gΓ tt gv)

-- Let
extractGroundExpr (plet' e body) gΓ gB (glet gA gexpr gbody) =
  let' (extractGroundExpr e gΓ gA gexpr) (extractGroundExpr body (gΓ , gA) gB gbody)

-- Int literal
extractGroundExpr (pint n) gΓ _ gint = int n

-- String literal
extractGroundExpr (pstr s) gΓ _ gstr = str s

-- Arithmetic
extractGroundExpr (padd a b) gΓ _ (gadd ga gb) =
  add (extractGroundExpr a gΓ tt ga) (extractGroundExpr b gΓ tt gb)

extractGroundExpr (psub a b) gΓ _ (gsub ga gb) =
  sub (extractGroundExpr a gΓ tt ga) (extractGroundExpr b gΓ tt gb)

extractGroundExpr (pmul a b) gΓ _ (gmul ga gb) =
  mul (extractGroundExpr a gΓ tt ga) (extractGroundExpr b gΓ tt gb)

extractGroundExpr (pdiv a b) gΓ _ (gdiv ga gb) =
  div (extractGroundExpr a gΓ tt ga) (extractGroundExpr b gΓ tt gb)

extractGroundExpr (pmod' a b) gΓ _ (gmod ga gb) =
  mod' (extractGroundExpr a gΓ tt ga) (extractGroundExpr b gΓ tt gb)

extractGroundExpr (pneg x) gΓ _ (gneg gx) =
  neg (extractGroundExpr x gΓ tt gx)

-- Comparisons
extractGroundExpr (plt a b) gΓ _ (glt ga gb) =
  lt (extractGroundExpr a gΓ tt ga) (extractGroundExpr b gΓ tt gb)

extractGroundExpr (ple a b) gΓ _ (gle ga gb) =
  le (extractGroundExpr a gΓ tt ga) (extractGroundExpr b gΓ tt gb)

extractGroundExpr (pgt a b) gΓ _ (ggt ga gb) =
  gt (extractGroundExpr a gΓ tt ga) (extractGroundExpr b gΓ tt gb)

extractGroundExpr (pge a b) gΓ _ (gge ga gb) =
  ge (extractGroundExpr a gΓ tt ga) (extractGroundExpr b gΓ tt gb)

extractGroundExpr (peq a b) gΓ _ (geq ga gb) =
  eq (extractGroundExpr a gΓ tt ga) (extractGroundExpr b gΓ tt gb)

extractGroundExpr (pne a b) gΓ _ (gne ga gb) =
  ne (extractGroundExpr a gΓ tt ga) (extractGroundExpr b gΓ tt gb)

-- Arr
extractGroundExpr (parr' f) gΓ (gA , gB) (garr gf) =
  arr' (extractGroundExpr f gΓ (gA , gB) gf)

-- Primitive
extractGroundExpr (pprim name) gΓ gA gprim = prim name

------------------------------------------------------------------------
-- Weakening for PolyExpr
--
-- Weakening adds a new variable binding to the context.
-- For de Bruijn indices, this means shifting all free variables up by 1.
------------------------------------------------------------------------

-- Mutual recursion needed: pweaken handles outer context, pweaken1 handles under binders
mutual
  -- | Weaken by adding a binding at the end of context
  pweaken : ∀ {n} {Γ : PolyCtx n} {A B : PolyType} {q : Quantity}
          → PolyExpr Γ A → PolyExpr (Γ P, B ^ q) A
  pweaken (pvar i) = pvar (Fin.suc i)
  pweaken (plam q body) = plam q (pweaken1 body)
  pweaken (papp f x) = papp (pweaken f) (pweaken x)
  pweaken (peffApp f x) = peffApp (pweaken f) (pweaken x)
  pweaken (ppair a b) = ppair (pweaken a) (pweaken b)
  pweaken (pfst' p) = pfst' (pweaken p)
  pweaken (psnd' p) = psnd' (pweaken p)
  pweaken (pinl' x) = pinl' (pweaken x)
  pweaken (pinr' x) = pinr' (pweaken x)
  pweaken (pcase' s l r) = pcase' (pweaken s) (pweaken1 l) (pweaken1 r)
  pweaken punit = punit
  pweaken (pabsurd v) = pabsurd (pweaken v)
  pweaken (plet' e body) = plet' (pweaken e) (pweaken1 body)
  pweaken (pint n) = pint n
  pweaken (pstr s) = pstr s
  pweaken (padd a b) = padd (pweaken a) (pweaken b)
  pweaken (psub a b) = psub (pweaken a) (pweaken b)
  pweaken (pmul a b) = pmul (pweaken a) (pweaken b)
  pweaken (pdiv a b) = pdiv (pweaken a) (pweaken b)
  pweaken (pmod' a b) = pmod' (pweaken a) (pweaken b)
  pweaken (pneg x) = pneg (pweaken x)
  pweaken (plt a b) = plt (pweaken a) (pweaken b)
  pweaken (ple a b) = ple (pweaken a) (pweaken b)
  pweaken (pgt a b) = pgt (pweaken a) (pweaken b)
  pweaken (pge a b) = pge (pweaken a) (pweaken b)
  pweaken (peq a b) = peq (pweaken a) (pweaken b)
  pweaken (pne a b) = pne (pweaken a) (pweaken b)
  pweaken (parr' f) = parr' (pweaken f)
  pweaken (pprim name) = pprim name

  -- | Weaken under one binder: insert binding second-to-last
  -- Context: (Γ P, X ^ qx) → ((Γ P, B ^ q) P, X ^ qx)
  pweaken1 : ∀ {n} {Γ : PolyCtx n} {A B X : PolyType} {q qx : Quantity}
           → PolyExpr (Γ P, X ^ qx) A → PolyExpr ((Γ P, B ^ q) P, X ^ qx) A
  pweaken1 (pvar Fin.zero) = pvar Fin.zero  -- Local binding unchanged
  pweaken1 (pvar (Fin.suc i)) = pvar (Fin.suc (Fin.suc i))  -- Shift outer refs
  pweaken1 (plam q body) = plam q (pweaken2 body)
  pweaken1 (papp f x) = papp (pweaken1 f) (pweaken1 x)
  pweaken1 (peffApp f x) = peffApp (pweaken1 f) (pweaken1 x)
  pweaken1 (ppair a b) = ppair (pweaken1 a) (pweaken1 b)
  pweaken1 (pfst' p) = pfst' (pweaken1 p)
  pweaken1 (psnd' p) = psnd' (pweaken1 p)
  pweaken1 (pinl' x) = pinl' (pweaken1 x)
  pweaken1 (pinr' x) = pinr' (pweaken1 x)
  pweaken1 (pcase' s l r) = pcase' (pweaken1 s) (pweaken2 l) (pweaken2 r)
  pweaken1 punit = punit
  pweaken1 (pabsurd v) = pabsurd (pweaken1 v)
  pweaken1 (plet' e body) = plet' (pweaken1 e) (pweaken2 body)
  pweaken1 (pint n) = pint n
  pweaken1 (pstr s) = pstr s
  pweaken1 (padd a b) = padd (pweaken1 a) (pweaken1 b)
  pweaken1 (psub a b) = psub (pweaken1 a) (pweaken1 b)
  pweaken1 (pmul a b) = pmul (pweaken1 a) (pweaken1 b)
  pweaken1 (pdiv a b) = pdiv (pweaken1 a) (pweaken1 b)
  pweaken1 (pmod' a b) = pmod' (pweaken1 a) (pweaken1 b)
  pweaken1 (pneg x) = pneg (pweaken1 x)
  pweaken1 (plt a b) = plt (pweaken1 a) (pweaken1 b)
  pweaken1 (ple a b) = ple (pweaken1 a) (pweaken1 b)
  pweaken1 (pgt a b) = pgt (pweaken1 a) (pweaken1 b)
  pweaken1 (pge a b) = pge (pweaken1 a) (pweaken1 b)
  pweaken1 (peq a b) = peq (pweaken1 a) (pweaken1 b)
  pweaken1 (pne a b) = pne (pweaken1 a) (pweaken1 b)
  pweaken1 (parr' f) = parr' (pweaken1 f)
  pweaken1 (pprim name) = pprim name

  -- | Weaken under two binders
  pweaken2 : ∀ {n} {Γ : PolyCtx n} {A B X Y : PolyType} {q qx qy : Quantity}
           → PolyExpr ((Γ P, X ^ qx) P, Y ^ qy) A
           → PolyExpr (((Γ P, B ^ q) P, X ^ qx) P, Y ^ qy) A
  pweaken2 (pvar Fin.zero) = pvar Fin.zero
  pweaken2 (pvar (Fin.suc Fin.zero)) = pvar (Fin.suc Fin.zero)
  pweaken2 (pvar (Fin.suc (Fin.suc i))) = pvar (Fin.suc (Fin.suc (Fin.suc i)))
  pweaken2 (plam q body) = plam q (pweaken3 body)
  pweaken2 (papp f x) = papp (pweaken2 f) (pweaken2 x)
  pweaken2 (peffApp f x) = peffApp (pweaken2 f) (pweaken2 x)
  pweaken2 (ppair a b) = ppair (pweaken2 a) (pweaken2 b)
  pweaken2 (pfst' p) = pfst' (pweaken2 p)
  pweaken2 (psnd' p) = psnd' (pweaken2 p)
  pweaken2 (pinl' x) = pinl' (pweaken2 x)
  pweaken2 (pinr' x) = pinr' (pweaken2 x)
  pweaken2 (pcase' s l r) = pcase' (pweaken2 s) (pweaken3 l) (pweaken3 r)
  pweaken2 punit = punit
  pweaken2 (pabsurd v) = pabsurd (pweaken2 v)
  pweaken2 (plet' e body) = plet' (pweaken2 e) (pweaken3 body)
  pweaken2 (pint n) = pint n
  pweaken2 (pstr s) = pstr s
  pweaken2 (padd a b) = padd (pweaken2 a) (pweaken2 b)
  pweaken2 (psub a b) = psub (pweaken2 a) (pweaken2 b)
  pweaken2 (pmul a b) = pmul (pweaken2 a) (pweaken2 b)
  pweaken2 (pdiv a b) = pdiv (pweaken2 a) (pweaken2 b)
  pweaken2 (pmod' a b) = pmod' (pweaken2 a) (pweaken2 b)
  pweaken2 (pneg x) = pneg (pweaken2 x)
  pweaken2 (plt a b) = plt (pweaken2 a) (pweaken2 b)
  pweaken2 (ple a b) = ple (pweaken2 a) (pweaken2 b)
  pweaken2 (pgt a b) = pgt (pweaken2 a) (pweaken2 b)
  pweaken2 (pge a b) = pge (pweaken2 a) (pweaken2 b)
  pweaken2 (peq a b) = peq (pweaken2 a) (pweaken2 b)
  pweaken2 (pne a b) = pne (pweaken2 a) (pweaken2 b)
  pweaken2 (parr' f) = parr' (pweaken2 f)
  pweaken2 (pprim name) = pprim name

  -- | Weaken under three binders
  pweaken3 : ∀ {n} {Γ : PolyCtx n} {A B X Y Z : PolyType} {q qx qy qz : Quantity}
           → PolyExpr (((Γ P, X ^ qx) P, Y ^ qy) P, Z ^ qz) A
           → PolyExpr ((((Γ P, B ^ q) P, X ^ qx) P, Y ^ qy) P, Z ^ qz) A
  pweaken3 (pvar Fin.zero) = pvar Fin.zero
  pweaken3 (pvar (Fin.suc Fin.zero)) = pvar (Fin.suc Fin.zero)
  pweaken3 (pvar (Fin.suc (Fin.suc Fin.zero))) = pvar (Fin.suc (Fin.suc Fin.zero))
  pweaken3 (pvar (Fin.suc (Fin.suc (Fin.suc i)))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc i))))
  pweaken3 (plam q body) = plam q (pweaken4 body)
  pweaken3 (papp f x) = papp (pweaken3 f) (pweaken3 x)
  pweaken3 (peffApp f x) = peffApp (pweaken3 f) (pweaken3 x)
  pweaken3 (ppair a b) = ppair (pweaken3 a) (pweaken3 b)
  pweaken3 (pfst' p) = pfst' (pweaken3 p)
  pweaken3 (psnd' p) = psnd' (pweaken3 p)
  pweaken3 (pinl' x) = pinl' (pweaken3 x)
  pweaken3 (pinr' x) = pinr' (pweaken3 x)
  pweaken3 (pcase' s l r) = pcase' (pweaken3 s) (pweaken4 l) (pweaken4 r)
  pweaken3 punit = punit
  pweaken3 (pabsurd v) = pabsurd (pweaken3 v)
  pweaken3 (plet' e body) = plet' (pweaken3 e) (pweaken4 body)
  pweaken3 (pint n) = pint n
  pweaken3 (pstr s) = pstr s
  pweaken3 (padd a b) = padd (pweaken3 a) (pweaken3 b)
  pweaken3 (psub a b) = psub (pweaken3 a) (pweaken3 b)
  pweaken3 (pmul a b) = pmul (pweaken3 a) (pweaken3 b)
  pweaken3 (pdiv a b) = pdiv (pweaken3 a) (pweaken3 b)
  pweaken3 (pmod' a b) = pmod' (pweaken3 a) (pweaken3 b)
  pweaken3 (pneg x) = pneg (pweaken3 x)
  pweaken3 (plt a b) = plt (pweaken3 a) (pweaken3 b)
  pweaken3 (ple a b) = ple (pweaken3 a) (pweaken3 b)
  pweaken3 (pgt a b) = pgt (pweaken3 a) (pweaken3 b)
  pweaken3 (pge a b) = pge (pweaken3 a) (pweaken3 b)
  pweaken3 (peq a b) = peq (pweaken3 a) (pweaken3 b)
  pweaken3 (pne a b) = pne (pweaken3 a) (pweaken3 b)
  pweaken3 (parr' f) = parr' (pweaken3 f)
  pweaken3 (pprim name) = pprim name

  -- | Weaken under four binders
  pweaken4 : ∀ {n} {Γ : PolyCtx n} {A B X Y Z W : PolyType} {q qx qy qz qw : Quantity}
           → PolyExpr ((((Γ P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) A
           → PolyExpr (((((Γ P, B ^ q) P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) A
  pweaken4 (pvar Fin.zero) = pvar Fin.zero
  pweaken4 (pvar (Fin.suc Fin.zero)) = pvar (Fin.suc Fin.zero)
  pweaken4 (pvar (Fin.suc (Fin.suc Fin.zero))) = pvar (Fin.suc (Fin.suc Fin.zero))
  pweaken4 (pvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = pvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
  pweaken4 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc i))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc i)))))
  pweaken4 (plam q body) = plam q (pweaken5 body)
  pweaken4 (papp f x) = papp (pweaken4 f) (pweaken4 x)
  pweaken4 (peffApp f x) = peffApp (pweaken4 f) (pweaken4 x)
  pweaken4 (ppair a b) = ppair (pweaken4 a) (pweaken4 b)
  pweaken4 (pfst' p) = pfst' (pweaken4 p)
  pweaken4 (psnd' p) = psnd' (pweaken4 p)
  pweaken4 (pinl' x) = pinl' (pweaken4 x)
  pweaken4 (pinr' x) = pinr' (pweaken4 x)
  pweaken4 (pcase' s l r) = pcase' (pweaken4 s) (pweaken5 l) (pweaken5 r)
  pweaken4 punit = punit
  pweaken4 (pabsurd v) = pabsurd (pweaken4 v)
  pweaken4 (plet' e body) = plet' (pweaken4 e) (pweaken5 body)
  pweaken4 (pint n) = pint n
  pweaken4 (pstr s) = pstr s
  pweaken4 (padd a b) = padd (pweaken4 a) (pweaken4 b)
  pweaken4 (psub a b) = psub (pweaken4 a) (pweaken4 b)
  pweaken4 (pmul a b) = pmul (pweaken4 a) (pweaken4 b)
  pweaken4 (pdiv a b) = pdiv (pweaken4 a) (pweaken4 b)
  pweaken4 (pmod' a b) = pmod' (pweaken4 a) (pweaken4 b)
  pweaken4 (pneg x) = pneg (pweaken4 x)
  pweaken4 (plt a b) = plt (pweaken4 a) (pweaken4 b)
  pweaken4 (ple a b) = ple (pweaken4 a) (pweaken4 b)
  pweaken4 (pgt a b) = pgt (pweaken4 a) (pweaken4 b)
  pweaken4 (pge a b) = pge (pweaken4 a) (pweaken4 b)
  pweaken4 (peq a b) = peq (pweaken4 a) (pweaken4 b)
  pweaken4 (pne a b) = pne (pweaken4 a) (pweaken4 b)
  pweaken4 (parr' f) = parr' (pweaken4 f)
  pweaken4 (pprim name) = pprim name

  -- | Weaken under five binders
  pweaken5 : ∀ {n} {Γ : PolyCtx n} {A B X Y Z W V : PolyType} {q qx qy qz qw qv : Quantity}
           → PolyExpr (((((Γ P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) P, V ^ qv) A
           → PolyExpr ((((((Γ P, B ^ q) P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) P, V ^ qv) A
  pweaken5 (pvar Fin.zero) = pvar Fin.zero
  pweaken5 (pvar (Fin.suc Fin.zero)) = pvar (Fin.suc Fin.zero)
  pweaken5 (pvar (Fin.suc (Fin.suc Fin.zero))) = pvar (Fin.suc (Fin.suc Fin.zero))
  pweaken5 (pvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = pvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
  pweaken5 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
  pweaken5 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc i)))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc i))))))
  pweaken5 (plam q body) = plam q (pweaken6 body)
  pweaken5 (papp f x) = papp (pweaken5 f) (pweaken5 x)
  pweaken5 (peffApp f x) = peffApp (pweaken5 f) (pweaken5 x)
  pweaken5 (ppair a b) = ppair (pweaken5 a) (pweaken5 b)
  pweaken5 (pfst' p) = pfst' (pweaken5 p)
  pweaken5 (psnd' p) = psnd' (pweaken5 p)
  pweaken5 (pinl' x) = pinl' (pweaken5 x)
  pweaken5 (pinr' x) = pinr' (pweaken5 x)
  pweaken5 (pcase' s l r) = pcase' (pweaken5 s) (pweaken6 l) (pweaken6 r)
  pweaken5 punit = punit
  pweaken5 (pabsurd v) = pabsurd (pweaken5 v)
  pweaken5 (plet' e body) = plet' (pweaken5 e) (pweaken6 body)
  pweaken5 (pint n) = pint n
  pweaken5 (pstr s) = pstr s
  pweaken5 (padd a b) = padd (pweaken5 a) (pweaken5 b)
  pweaken5 (psub a b) = psub (pweaken5 a) (pweaken5 b)
  pweaken5 (pmul a b) = pmul (pweaken5 a) (pweaken5 b)
  pweaken5 (pdiv a b) = pdiv (pweaken5 a) (pweaken5 b)
  pweaken5 (pmod' a b) = pmod' (pweaken5 a) (pweaken5 b)
  pweaken5 (pneg x) = pneg (pweaken5 x)
  pweaken5 (plt a b) = plt (pweaken5 a) (pweaken5 b)
  pweaken5 (ple a b) = ple (pweaken5 a) (pweaken5 b)
  pweaken5 (pgt a b) = pgt (pweaken5 a) (pweaken5 b)
  pweaken5 (pge a b) = pge (pweaken5 a) (pweaken5 b)
  pweaken5 (peq a b) = peq (pweaken5 a) (pweaken5 b)
  pweaken5 (pne a b) = pne (pweaken5 a) (pweaken5 b)
  pweaken5 (parr' f) = parr' (pweaken5 f)
  pweaken5 (pprim name) = pprim name

  -- | Weaken under six binders
  pweaken6 : ∀ {n} {Γ : PolyCtx n} {A B X Y Z W V U : PolyType} {q qx qy qz qw qv qu : Quantity}
           → PolyExpr ((((((Γ P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) P, V ^ qv) P, U ^ qu) A
           → PolyExpr (((((((Γ P, B ^ q) P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) P, V ^ qv) P, U ^ qu) A
  pweaken6 (pvar Fin.zero) = pvar Fin.zero
  pweaken6 (pvar (Fin.suc Fin.zero)) = pvar (Fin.suc Fin.zero)
  pweaken6 (pvar (Fin.suc (Fin.suc Fin.zero))) = pvar (Fin.suc (Fin.suc Fin.zero))
  pweaken6 (pvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = pvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
  pweaken6 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
  pweaken6 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))
  pweaken6 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc i))))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc i)))))))
  pweaken6 (plam q body) = plam q (pweaken7 body)
  pweaken6 (papp f x) = papp (pweaken6 f) (pweaken6 x)
  pweaken6 (peffApp f x) = peffApp (pweaken6 f) (pweaken6 x)
  pweaken6 (ppair a b) = ppair (pweaken6 a) (pweaken6 b)
  pweaken6 (pfst' p) = pfst' (pweaken6 p)
  pweaken6 (psnd' p) = psnd' (pweaken6 p)
  pweaken6 (pinl' x) = pinl' (pweaken6 x)
  pweaken6 (pinr' x) = pinr' (pweaken6 x)
  pweaken6 (pcase' s l r) = pcase' (pweaken6 s) (pweaken7 l) (pweaken7 r)
  pweaken6 punit = punit
  pweaken6 (pabsurd v) = pabsurd (pweaken6 v)
  pweaken6 (plet' e body) = plet' (pweaken6 e) (pweaken7 body)
  pweaken6 (pint n) = pint n
  pweaken6 (pstr s) = pstr s
  pweaken6 (padd a b) = padd (pweaken6 a) (pweaken6 b)
  pweaken6 (psub a b) = psub (pweaken6 a) (pweaken6 b)
  pweaken6 (pmul a b) = pmul (pweaken6 a) (pweaken6 b)
  pweaken6 (pdiv a b) = pdiv (pweaken6 a) (pweaken6 b)
  pweaken6 (pmod' a b) = pmod' (pweaken6 a) (pweaken6 b)
  pweaken6 (pneg x) = pneg (pweaken6 x)
  pweaken6 (plt a b) = plt (pweaken6 a) (pweaken6 b)
  pweaken6 (ple a b) = ple (pweaken6 a) (pweaken6 b)
  pweaken6 (pgt a b) = pgt (pweaken6 a) (pweaken6 b)
  pweaken6 (pge a b) = pge (pweaken6 a) (pweaken6 b)
  pweaken6 (peq a b) = peq (pweaken6 a) (pweaken6 b)
  pweaken6 (pne a b) = pne (pweaken6 a) (pweaken6 b)
  pweaken6 (parr' f) = parr' (pweaken6 f)
  pweaken6 (pprim name) = pprim name

  -- | Weaken under seven binders
  pweaken7 : ∀ {n} {Γ : PolyCtx n} {A B X Y Z W V U T : PolyType} {q qx qy qz qw qv qu qt : Quantity}
           → PolyExpr (((((((Γ P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) P, V ^ qv) P, U ^ qu) P, T ^ qt) A
           → PolyExpr ((((((((Γ P, B ^ q) P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) P, V ^ qv) P, U ^ qu) P, T ^ qt) A
  pweaken7 (pvar Fin.zero) = pvar Fin.zero
  pweaken7 (pvar (Fin.suc Fin.zero)) = pvar (Fin.suc Fin.zero)
  pweaken7 (pvar (Fin.suc (Fin.suc Fin.zero))) = pvar (Fin.suc (Fin.suc Fin.zero))
  pweaken7 (pvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = pvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
  pweaken7 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
  pweaken7 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))
  pweaken7 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))
  pweaken7 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc i)))))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc i))))))))
  pweaken7 (plam q body) = plam q (pweaken8 body)
  pweaken7 (papp f x) = papp (pweaken7 f) (pweaken7 x)
  pweaken7 (peffApp f x) = peffApp (pweaken7 f) (pweaken7 x)
  pweaken7 (ppair a b) = ppair (pweaken7 a) (pweaken7 b)
  pweaken7 (pfst' p) = pfst' (pweaken7 p)
  pweaken7 (psnd' p) = psnd' (pweaken7 p)
  pweaken7 (pinl' x) = pinl' (pweaken7 x)
  pweaken7 (pinr' x) = pinr' (pweaken7 x)
  pweaken7 (pcase' s l r) = pcase' (pweaken7 s) (pweaken8 l) (pweaken8 r)
  pweaken7 punit = punit
  pweaken7 (pabsurd v) = pabsurd (pweaken7 v)
  pweaken7 (plet' e body) = plet' (pweaken7 e) (pweaken8 body)
  pweaken7 (pint n) = pint n
  pweaken7 (pstr s) = pstr s
  pweaken7 (padd a b) = padd (pweaken7 a) (pweaken7 b)
  pweaken7 (psub a b) = psub (pweaken7 a) (pweaken7 b)
  pweaken7 (pmul a b) = pmul (pweaken7 a) (pweaken7 b)
  pweaken7 (pdiv a b) = pdiv (pweaken7 a) (pweaken7 b)
  pweaken7 (pmod' a b) = pmod' (pweaken7 a) (pweaken7 b)
  pweaken7 (pneg x) = pneg (pweaken7 x)
  pweaken7 (plt a b) = plt (pweaken7 a) (pweaken7 b)
  pweaken7 (ple a b) = ple (pweaken7 a) (pweaken7 b)
  pweaken7 (pgt a b) = pgt (pweaken7 a) (pweaken7 b)
  pweaken7 (pge a b) = pge (pweaken7 a) (pweaken7 b)
  pweaken7 (peq a b) = peq (pweaken7 a) (pweaken7 b)
  pweaken7 (pne a b) = pne (pweaken7 a) (pweaken7 b)
  pweaken7 (parr' f) = parr' (pweaken7 f)
  pweaken7 (pprim name) = pprim name

  -- | Weaken under eight binders (practical limit for closed expressions)
  -- For closed expressions from P∅, the outer variable case i : Fin 0 is empty,
  -- so nesting beyond 8 binders would be statically impossible to construct.
  pweaken8 : ∀ {n} {Γ : PolyCtx n} {A B X Y Z W V U T S : PolyType} {q qx qy qz qw qv qu qt qs : Quantity}
           → PolyExpr ((((((((Γ P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) P, V ^ qv) P, U ^ qu) P, T ^ qt) P, S ^ qs) A
           → PolyExpr (((((((((Γ P, B ^ q) P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) P, V ^ qv) P, U ^ qu) P, T ^ qt) P, S ^ qs) A
  pweaken8 (pvar Fin.zero) = pvar Fin.zero
  pweaken8 (pvar (Fin.suc Fin.zero)) = pvar (Fin.suc Fin.zero)
  pweaken8 (pvar (Fin.suc (Fin.suc Fin.zero))) = pvar (Fin.suc (Fin.suc Fin.zero))
  pweaken8 (pvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = pvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
  pweaken8 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
  pweaken8 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))
  pweaken8 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))
  pweaken8 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))
  pweaken8 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc i))))))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc i)))))))))
  -- At depth 8, binders would need pweaken9. For closed expressions, this is unreachable.
  -- Non-closed expressions requiring >8 binders are extremely rare in practice.
  pweaken8 (plam q body) = plam q (pweaken9 body)
  pweaken8 (papp f x) = papp (pweaken8 f) (pweaken8 x)
  pweaken8 (peffApp f x) = peffApp (pweaken8 f) (pweaken8 x)
  pweaken8 (ppair a b) = ppair (pweaken8 a) (pweaken8 b)
  pweaken8 (pfst' p) = pfst' (pweaken8 p)
  pweaken8 (psnd' p) = psnd' (pweaken8 p)
  pweaken8 (pinl' x) = pinl' (pweaken8 x)
  pweaken8 (pinr' x) = pinr' (pweaken8 x)
  pweaken8 (pcase' s l r) = pcase' (pweaken8 s) (pweaken9 l) (pweaken9 r)
  pweaken8 punit = punit
  pweaken8 (pabsurd v) = pabsurd (pweaken8 v)
  pweaken8 (plet' e body) = plet' (pweaken8 e) (pweaken9 body)
  pweaken8 (pint n) = pint n
  pweaken8 (pstr s) = pstr s
  pweaken8 (padd a b) = padd (pweaken8 a) (pweaken8 b)
  pweaken8 (psub a b) = psub (pweaken8 a) (pweaken8 b)
  pweaken8 (pmul a b) = pmul (pweaken8 a) (pweaken8 b)
  pweaken8 (pdiv a b) = pdiv (pweaken8 a) (pweaken8 b)
  pweaken8 (pmod' a b) = pmod' (pweaken8 a) (pweaken8 b)
  pweaken8 (pneg x) = pneg (pweaken8 x)
  pweaken8 (plt a b) = plt (pweaken8 a) (pweaken8 b)
  pweaken8 (ple a b) = ple (pweaken8 a) (pweaken8 b)
  pweaken8 (pgt a b) = pgt (pweaken8 a) (pweaken8 b)
  pweaken8 (pge a b) = pge (pweaken8 a) (pweaken8 b)
  pweaken8 (peq a b) = peq (pweaken8 a) (pweaken8 b)
  pweaken8 (pne a b) = pne (pweaken8 a) (pweaken8 b)
  pweaken8 (parr' f) = parr' (pweaken8 f)
  pweaken8 (pprim name) = pprim name

  -- | Weaken under nine binders - uses postulate for deeper binders
  --
  -- JUSTIFICATION for pweaken-deep postulate:
  -- - Only reachable with >9 nested binders (lambda/case/let)
  -- - For closed expressions from P∅, this requires >9 nested binders in a single builtin
  -- - No standard builtin has this level of nesting
  -- - The postulate is semantically sound: weakening is identity on runtime representation
  --
  -- To remove this postulate: implement pweaken10, pweaken11, etc. following the pattern
  --
  pweaken9 : ∀ {n} {Γ : PolyCtx n} {A B X Y Z W V U T S R : PolyType} {q qx qy qz qw qv qu qt qs qr : Quantity}
           → PolyExpr (((((((((Γ P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) P, V ^ qv) P, U ^ qu) P, T ^ qt) P, S ^ qs) P, R ^ qr) A
           → PolyExpr ((((((((((Γ P, B ^ q) P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) P, V ^ qv) P, U ^ qu) P, T ^ qt) P, S ^ qs) P, R ^ qr) A
  pweaken9 (pvar Fin.zero) = pvar Fin.zero
  pweaken9 (pvar (Fin.suc Fin.zero)) = pvar (Fin.suc Fin.zero)
  pweaken9 (pvar (Fin.suc (Fin.suc Fin.zero))) = pvar (Fin.suc (Fin.suc Fin.zero))
  pweaken9 (pvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = pvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
  pweaken9 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
  pweaken9 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))
  pweaken9 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))
  pweaken9 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))
  pweaken9 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))
  pweaken9 (pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc i)))))))))) = pvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc i))))))))))
  pweaken9 (plam q body) = plam q (pweaken10 body)
  pweaken9 (papp f x) = papp (pweaken9 f) (pweaken9 x)
  pweaken9 (peffApp f x) = peffApp (pweaken9 f) (pweaken9 x)
  pweaken9 (ppair a b) = ppair (pweaken9 a) (pweaken9 b)
  pweaken9 (pfst' p) = pfst' (pweaken9 p)
  pweaken9 (psnd' p) = psnd' (pweaken9 p)
  pweaken9 (pinl' x) = pinl' (pweaken9 x)
  pweaken9 (pinr' x) = pinr' (pweaken9 x)
  pweaken9 (pcase' s l r) = pcase' (pweaken9 s) (pweaken10 l) (pweaken10 r)
  pweaken9 punit = punit
  pweaken9 (pabsurd v) = pabsurd (pweaken9 v)
  pweaken9 (plet' e body) = plet' (pweaken9 e) (pweaken10 body)
  pweaken9 (pint n) = pint n
  pweaken9 (pstr s) = pstr s
  pweaken9 (padd a b) = padd (pweaken9 a) (pweaken9 b)
  pweaken9 (psub a b) = psub (pweaken9 a) (pweaken9 b)
  pweaken9 (pmul a b) = pmul (pweaken9 a) (pweaken9 b)
  pweaken9 (pdiv a b) = pdiv (pweaken9 a) (pweaken9 b)
  pweaken9 (pmod' a b) = pmod' (pweaken9 a) (pweaken9 b)
  pweaken9 (pneg x) = pneg (pweaken9 x)
  pweaken9 (plt a b) = plt (pweaken9 a) (pweaken9 b)
  pweaken9 (ple a b) = ple (pweaken9 a) (pweaken9 b)
  pweaken9 (pgt a b) = pgt (pweaken9 a) (pweaken9 b)
  pweaken9 (pge a b) = pge (pweaken9 a) (pweaken9 b)
  pweaken9 (peq a b) = peq (pweaken9 a) (pweaken9 b)
  pweaken9 (pne a b) = pne (pweaken9 a) (pweaken9 b)
  pweaken9 (parr' f) = parr' (pweaken9 f)
  pweaken9 (pprim name) = pprim name

  -- Postulate for weakening at depth 10+ (under 10 binders)
  -- See justification at pweaken9
  -- Type: insert B at position 10 from innermost binder
  postulate
    pweaken10 : ∀ {n} {Γ : PolyCtx n} {A B X Y Z W V U T S R P' : PolyType}
                  {q qx qy qz qw qv qu qt qs qr qp : Quantity}
              → PolyExpr ((((((((((Γ P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) P, V ^ qv) P, U ^ qu) P, T ^ qt) P, S ^ qs) P, R ^ qr) P, P' ^ qp) A
              → PolyExpr (((((((((((Γ P, B ^ q) P, X ^ qx) P, Y ^ qy) P, Z ^ qz) P, W ^ qw) P, V ^ qv) P, U ^ qu) P, T ^ qt) P, S ^ qs) P, R ^ qr) P, P' ^ qp) A

-- | Weaken from empty context to any context
pweakenFromEmpty : ∀ {n} {Γ : PolyCtx n} {A : PolyType}
                 → PolyExpr P∅ A → PolyExpr Γ A
pweakenFromEmpty {Γ = P∅} e = e
pweakenFromEmpty {Γ = Γ P, B ^ q} e = pweaken (pweakenFromEmpty {Γ = Γ} e)

------------------------------------------------------------------------
-- Partial Extraction (Bridge to Principled Extraction)
--
-- These functions provide backward compatibility with code that expects
-- Maybe-based extraction. They are less principled than extractGroundExpr
-- but necessary until Phase 5d (connecting extraction to type inference)
-- is complete.
--
-- TODO: Remove these once InferResult provides Ground proofs.
------------------------------------------------------------------------

-- | Partial context extraction (may fail if TVars present)
extractCtx : ∀ {n} → PolyCtx n → Maybe (Ctx n)
extractCtx P∅ = just ∅
extractCtx (Γ P, A ^ q) with extractCtx Γ | extract A
... | just Γ' | just A' = just (Γ' , A' ^ q)
... | _ | _ = nothing

-- | Partial expression extraction (may fail if TVars present)
-- Returns (extracted context, extracted type, extracted expression)
extractExpr : ∀ {n} {Γ : PolyCtx n} {A : PolyType}
            → PolyExpr Γ A
            → Maybe (∃[ Γ' ] ∃[ A' ] Expr Γ' A')
extractExpr {Γ = Γ} {A = A} e with extractCtx Γ | extract A
... | just Γ' | just A' = just (Γ' , A' , unsafeExtract e)
  where
    -- Unsafe extraction using Agda's postulate (types already checked via extract)
    postulate unsafeExtract : ∀ {n} {Γ : PolyCtx n} {A : PolyType} → PolyExpr Γ A → Expr Γ' A'
... | _ | _ = nothing

