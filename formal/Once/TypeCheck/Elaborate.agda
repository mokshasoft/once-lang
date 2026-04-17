-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck.Elaborate
--
-- Combined type inference and elaboration.
-- Produces intrinsically-typed Surface.Syntax.Expr directly from RawExpr.
--
-- This avoids the problem with separate Resolve step needing subexpression
-- types that aren't available.
--
-- Part of OCP-0004: MAlonzo Compiler Replacement
------------------------------------------------------------------------

module Once.TypeCheck.Elaborate where

open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using (_≟_)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤?_; _⊔_)
open import Data.Nat as Nat
open import Data.Nat.Properties using (≤-refl; n<1+n; +-identityʳ; +-suc; +-comm)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin as Fin using (_↑ˡ_)
open import Data.Vec using (Vec; []; _∷_; tail) renaming (lookup to Vec-lookup)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym)
open import Induction.WellFounded using (Acc; acc; WfRec)
open import Data.Nat.Induction using (<-wellFounded)

open import Once.Type
open Once.Type using (showQuantity; showType; showPolyType; PolyType; PolyFunctor;
                       PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff; Pμ-type; Pν-type;
                       PInt; PFloat; PStr; PBuffer; TVar;
                       PK; PId; _P⊕_; _P⊗_;
                       embed; extract; embedFunctor; extractFunctor;
                       Ground; GroundFunctor; extractGround; embed-ground; extractGround-embed;
                       ground?) public
open import Once.CCC.IR as IR
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Context using (Ctx; ∅; Binding; mkBinding; name; type)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.Surface.Syntax as Surface using (lookup; lookupQuantity; lookupUsage; tailUsage; _≤ᵘ?_)
  renaming (Ctx to SCtx; Expr to SExpr; ∅ to S∅; _,_ to _S,_; _,_^_ to _S,_^_)
open import Once.Surface.Thinning
  using (weaken; exchange; exchange₂; exchange₃; exchange₄; exchange₅; exchange₆; exchange₇; exchange₈)
open import Once.Surface.Elaborate as Elab using (elaborate; ⟦_⟧ᶜ)
open import Once.Surface.PolySyntax as Poly
  using (PolyCtx; P∅; _P,_; _P,_^_; PolyExpr; lookupPoly; lookupPolyQuantity;
         pvar; plam; papp; peffApp; ppair; pfst'; psnd'; pinl'; pinr'; pcase';
         punit; pabsurd; plet'; pint; pstr; padd; psub; pmul; pdiv; pmod'; pneg;
         plt; ple; pgt; pge; peq; pne; parr'; pprim;
         extractCtx; extractExpr; pweaken; pweakenFromEmpty;
         GroundCtx; extractGroundCtx; groundCtx?; groundExpr?; extractGroundExpr)
open import Once.Postulates using (coerceQuantity)

------------------------------------------------------------------------
-- Weakening from Empty Context
------------------------------------------------------------------------

-- | Weaken from empty context to arbitrary context
--
-- Built-in expressions have no free variables, so we can weaken them
-- from ∅ to any context Γ by repeatedly applying weaken.
--
-- Note: weaken and exchange functions are now imported from Once.Surface.Thinning
--
weakenFromEmpty : ∀ {n} {Γ : SCtx n} {A : Type} → SExpr S∅ A → SExpr Γ A
weakenFromEmpty {Γ = S∅} e = e
weakenFromEmpty {Γ = Γ S, B ^ Many} e = weaken {A = B} {q = Many} (weakenFromEmpty {Γ = Γ} e)
-- For non-Many quantities, coerce (Step 2: infrastructure only, actual tracking in Step 3)
weakenFromEmpty {Γ = Γ S, B ^ q} e = coerceQuantity (weaken {A = B} {q = q} (weakenFromEmpty {Γ = Γ} e))

------------------------------------------------------------------------
-- Type Equality (Decidable with proof)
------------------------------------------------------------------------

-- | Decidable functor and type equality (mutually recursive)
mutual
  -- | Decidable functor equality
  _≟F_ : (F G : Functor) → Dec (F ≡ G)
  K A ≟F K B with A ≟T B
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  Id ≟F Id = yes refl
  (F₁ ⊕ G₁) ≟F (F₂ ⊕ G₂) with F₁ ≟F F₂ | G₁ ≟F G₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  (F₁ ⊗ G₁) ≟F (F₂ ⊗ G₂) with F₁ ≟F F₂ | G₁ ≟F G₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  -- Mismatched constructors
  K _ ≟F Id = no λ ()
  K _ ≟F (_ ⊕ _) = no λ ()
  K _ ≟F (_ ⊗ _) = no λ ()
  Id ≟F K _ = no λ ()
  Id ≟F (_ ⊕ _) = no λ ()
  Id ≟F (_ ⊗ _) = no λ ()
  (_ ⊕ _) ≟F K _ = no λ ()
  (_ ⊕ _) ≟F Id = no λ ()
  (_ ⊕ _) ≟F (_ ⊗ _) = no λ ()
  (_ ⊗ _) ≟F K _ = no λ ()
  (_ ⊗ _) ≟F Id = no λ ()
  (_ ⊗ _) ≟F (_ ⊕ _) = no λ ()

  -- | Decidable type equality
  _≟T_ : (A B : Type) → Dec (A ≡ B)
  Unit ≟T Unit = yes refl
  Void ≟T Void = yes refl
  Int ≟T Int = yes refl
  Float ≟T Float = yes refl
  Str ≟T Str = yes refl
  Buffer ≟T Buffer = yes refl
  (A₁ Once.Type.* B₁) ≟T (A₂ Once.Type.* B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  (A₁ Once.Type.+ B₁) ≟T (A₂ Once.Type.+ B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  (A₁ ⇒[ q₁ ] B₁) ≟T (A₂ ⇒[ q₂ ] B₂) with A₁ ≟T A₂ | q₁ ≟q q₂ | B₁ ≟T B₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q | _ = no λ { refl → ¬q refl }
  ... | _ | _ | no ¬r = no λ { refl → ¬r refl }
  (Eff A₁ B₁) ≟T (Eff A₂ B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  -- OCP-0003: Fix removed
  -- TVar removed from Type; now in PolyType (see Once.Type)
  -- All other combinations are unequal
  Unit ≟T Void = no λ ()
  Unit ≟T Int = no λ ()
  Unit ≟T Float = no λ ()
  Unit ≟T Str = no λ ()
  Unit ≟T Buffer = no λ ()
  Unit ≟T (_ Once.Type.* _) = no λ ()
  Unit ≟T (_ Once.Type.+ _) = no λ ()
  Unit ≟T (_ ⇒[ _ ] _) = no λ ()
  Unit ≟T Eff _ _ = no λ ()
  Void ≟T Unit = no λ ()
  Void ≟T Int = no λ ()
  Void ≟T Float = no λ ()
  Void ≟T Str = no λ ()
  Void ≟T Buffer = no λ ()
  Void ≟T (_ Once.Type.* _) = no λ ()
  Void ≟T (_ Once.Type.+ _) = no λ ()
  Void ≟T (_ ⇒[ _ ] _) = no λ ()
  Void ≟T Eff _ _ = no λ ()
  Int ≟T Unit = no λ ()
  Int ≟T Void = no λ ()
  Int ≟T Float = no λ ()
  Int ≟T Str = no λ ()
  Int ≟T Buffer = no λ ()
  Int ≟T (_ Once.Type.* _) = no λ ()
  Int ≟T (_ Once.Type.+ _) = no λ ()
  Int ≟T (_ ⇒[ _ ] _) = no λ ()
  Int ≟T Eff _ _ = no λ ()
  Float ≟T Unit = no λ ()
  Float ≟T Void = no λ ()
  Float ≟T Int = no λ ()
  Float ≟T Str = no λ ()
  Float ≟T Buffer = no λ ()
  Float ≟T (_ Once.Type.* _) = no λ ()
  Float ≟T (_ Once.Type.+ _) = no λ ()
  Float ≟T (_ ⇒[ _ ] _) = no λ ()
  Float ≟T Eff _ _ = no λ ()
  Str ≟T Unit = no λ ()
  Str ≟T Void = no λ ()
  Str ≟T Int = no λ ()
  Str ≟T Float = no λ ()
  Str ≟T Buffer = no λ ()
  Str ≟T (_ Once.Type.* _) = no λ ()
  Str ≟T (_ Once.Type.+ _) = no λ ()
  Str ≟T (_ ⇒[ _ ] _) = no λ ()
  Str ≟T Eff _ _ = no λ ()
  Buffer ≟T Unit = no λ ()
  Buffer ≟T Void = no λ ()
  Buffer ≟T Int = no λ ()
  Buffer ≟T Float = no λ ()
  Buffer ≟T Str = no λ ()
  Buffer ≟T (_ Once.Type.* _) = no λ ()
  Buffer ≟T (_ Once.Type.+ _) = no λ ()
  Buffer ≟T (_ ⇒[ _ ] _) = no λ ()
  Buffer ≟T Eff _ _ = no λ ()
  (_ Once.Type.* _) ≟T Unit = no λ ()
  (_ Once.Type.* _) ≟T Void = no λ ()
  (_ Once.Type.* _) ≟T Int = no λ ()
  (_ Once.Type.* _) ≟T Float = no λ ()
  (_ Once.Type.* _) ≟T Str = no λ ()
  (_ Once.Type.* _) ≟T Buffer = no λ ()
  (_ Once.Type.* _) ≟T (_ Once.Type.+ _) = no λ ()
  (_ Once.Type.* _) ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ Once.Type.* _) ≟T Eff _ _ = no λ ()
  (_ Once.Type.+ _) ≟T Unit = no λ ()
  (_ Once.Type.+ _) ≟T Void = no λ ()
  (_ Once.Type.+ _) ≟T Int = no λ ()
  (_ Once.Type.+ _) ≟T Float = no λ ()
  (_ Once.Type.+ _) ≟T Str = no λ ()
  (_ Once.Type.+ _) ≟T Buffer = no λ ()
  (_ Once.Type.+ _) ≟T (_ Once.Type.* _) = no λ ()
  (_ Once.Type.+ _) ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ Once.Type.+ _) ≟T Eff _ _ = no λ ()
  (_ ⇒[ _ ] _) ≟T Unit = no λ ()
  (_ ⇒[ _ ] _) ≟T Void = no λ ()
  (_ ⇒[ _ ] _) ≟T Int = no λ ()
  (_ ⇒[ _ ] _) ≟T Float = no λ ()
  (_ ⇒[ _ ] _) ≟T Str = no λ ()
  (_ ⇒[ _ ] _) ≟T Buffer = no λ ()
  (_ ⇒[ _ ] _) ≟T (_ Once.Type.* _) = no λ ()
  (_ ⇒[ _ ] _) ≟T (_ Once.Type.+ _) = no λ ()
  (_ ⇒[ _ ] _) ≟T Eff _ _ = no λ ()
  Eff _ _ ≟T Unit = no λ ()
  Eff _ _ ≟T Void = no λ ()
  Eff _ _ ≟T Int = no λ ()
  Eff _ _ ≟T Float = no λ ()
  Eff _ _ ≟T Str = no λ ()
  Eff _ _ ≟T Buffer = no λ ()
  Eff _ _ ≟T (_ Once.Type.* _) = no λ ()
  Eff _ _ ≟T (_ Once.Type.+ _) = no λ ()
  Eff _ _ ≟T (_ ⇒[ _ ] _) = no λ ()
  -- TVar removed from Type; now in PolyType (see Once.Type)
  -- OCP-0003: μ-type and ν-type cases
  (μ-type F₁) ≟T (μ-type F₂) with F₁ ≟F F₂
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  (ν-type F₁) ≟T (ν-type F₂) with F₁ ≟F F₂
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  μ-type _ ≟T Unit = no λ ()
  μ-type _ ≟T Void = no λ ()
  μ-type _ ≟T Int = no λ ()
  μ-type _ ≟T Float = no λ ()
  μ-type _ ≟T Str = no λ ()
  μ-type _ ≟T Buffer = no λ ()
  μ-type _ ≟T (_ Once.Type.* _) = no λ ()
  μ-type _ ≟T (_ Once.Type.+ _) = no λ ()
  μ-type _ ≟T (_ ⇒[ _ ] _) = no λ ()
  μ-type _ ≟T Eff _ _ = no λ ()
  μ-type _ ≟T ν-type _ = no λ ()
  ν-type _ ≟T Unit = no λ ()
  ν-type _ ≟T Void = no λ ()
  ν-type _ ≟T Int = no λ ()
  ν-type _ ≟T Float = no λ ()
  ν-type _ ≟T Str = no λ ()
  ν-type _ ≟T Buffer = no λ ()
  ν-type _ ≟T (_ Once.Type.* _) = no λ ()
  ν-type _ ≟T (_ Once.Type.+ _) = no λ ()
  ν-type _ ≟T (_ ⇒[ _ ] _) = no λ ()
  ν-type _ ≟T Eff _ _ = no λ ()
  ν-type _ ≟T μ-type _ = no λ ()
  Unit ≟T μ-type _ = no λ ()
  Unit ≟T ν-type _ = no λ ()
  Void ≟T μ-type _ = no λ ()
  Void ≟T ν-type _ = no λ ()
  Int ≟T μ-type _ = no λ ()
  Int ≟T ν-type _ = no λ ()
  Float ≟T μ-type _ = no λ ()
  Float ≟T ν-type _ = no λ ()
  Str ≟T μ-type _ = no λ ()
  Str ≟T ν-type _ = no λ ()
  Buffer ≟T μ-type _ = no λ ()
  Buffer ≟T ν-type _ = no λ ()
  (_ Once.Type.* _) ≟T μ-type _ = no λ ()
  (_ Once.Type.* _) ≟T ν-type _ = no λ ()
  (_ Once.Type.+ _) ≟T μ-type _ = no λ ()
  (_ Once.Type.+ _) ≟T ν-type _ = no λ ()
  (_ ⇒[ _ ] _) ≟T μ-type _ = no λ ()
  (_ ⇒[ _ ] _) ≟T ν-type _ = no λ ()
  Eff _ _ ≟T μ-type _ = no λ ()
  Eff _ _ ≟T ν-type _ = no λ ()
  -- GuardedT removed: productivity follows from IR totality
  -- TVar removed from Type; now in PolyType (see Once.Type)

------------------------------------------------------------------------
-- PolyType Equality (for type checking during inference)
------------------------------------------------------------------------

-- | Decidable PolyFunctor and PolyType equality (mutually recursive)
mutual
  -- | Decidable PolyFunctor equality
  _≟PF_ : (F G : PolyFunctor) → Dec (F ≡ G)
  PK A ≟PF PK B with A ≟PT B
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  PId ≟PF PId = yes refl
  (F₁ P⊕ G₁) ≟PF (F₂ P⊕ G₂) with F₁ ≟PF F₂ | G₁ ≟PF G₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  (F₁ P⊗ G₁) ≟PF (F₂ P⊗ G₂) with F₁ ≟PF F₂ | G₁ ≟PF G₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  -- Mismatched constructors
  PK _ ≟PF PId = no λ ()
  PK _ ≟PF (_ P⊕ _) = no λ ()
  PK _ ≟PF (_ P⊗ _) = no λ ()
  PId ≟PF PK _ = no λ ()
  PId ≟PF (_ P⊕ _) = no λ ()
  PId ≟PF (_ P⊗ _) = no λ ()
  (_ P⊕ _) ≟PF PK _ = no λ ()
  (_ P⊕ _) ≟PF PId = no λ ()
  (_ P⊕ _) ≟PF (_ P⊗ _) = no λ ()
  (_ P⊗ _) ≟PF PK _ = no λ ()
  (_ P⊗ _) ≟PF PId = no λ ()
  (_ P⊗ _) ≟PF (_ P⊕ _) = no λ ()

  -- | Decidable PolyType equality
  -- Note: TVars are compared by name (structural equality)
  _≟PT_ : (A B : PolyType) → Dec (A ≡ B)
  PUnit ≟PT PUnit = yes refl
  PVoid ≟PT PVoid = yes refl
  PInt ≟PT PInt = yes refl
  PFloat ≟PT PFloat = yes refl
  PStr ≟PT PStr = yes refl
  PBuffer ≟PT PBuffer = yes refl
  (A₁ P* B₁) ≟PT (A₂ P* B₂) with A₁ ≟PT A₂ | B₁ ≟PT B₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  (A₁ P+ B₁) ≟PT (A₂ P+ B₂) with A₁ ≟PT A₂ | B₁ ≟PT B₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  (A₁ P⇒[ q₁ ] B₁) ≟PT (A₂ P⇒[ q₂ ] B₂) with A₁ ≟PT A₂ | B₁ ≟PT B₂ | q₁ Once.Type.≟q q₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q | _ = no λ { refl → ¬q refl }
  ... | _ | _ | no ¬r = no λ { refl → ¬r refl }
  (PEff A₁ B₁) ≟PT (PEff A₂ B₂) with A₁ ≟PT A₂ | B₁ ≟PT B₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  (Pμ-type F₁) ≟PT (Pμ-type F₂) with F₁ ≟PF F₂
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  (Pν-type F₁) ≟PT (Pν-type F₂) with F₁ ≟PF F₂
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  (TVar x) ≟PT (TVar y) with x Data.String.≟ y
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  -- All other combinations are not equal
  PUnit ≟PT PVoid = no λ ()
  PUnit ≟PT PInt = no λ ()
  PUnit ≟PT PFloat = no λ ()
  PUnit ≟PT PStr = no λ ()
  PUnit ≟PT PBuffer = no λ ()
  PUnit ≟PT (_ P* _) = no λ ()
  PUnit ≟PT (_ P+ _) = no λ ()
  PUnit ≟PT (_ P⇒[ _ ] _) = no λ ()
  PUnit ≟PT PEff _ _ = no λ ()
  PUnit ≟PT Pμ-type _ = no λ ()
  PUnit ≟PT Pν-type _ = no λ ()
  PUnit ≟PT TVar _ = no λ ()
  PVoid ≟PT PUnit = no λ ()
  PVoid ≟PT PInt = no λ ()
  PVoid ≟PT PFloat = no λ ()
  PVoid ≟PT PStr = no λ ()
  PVoid ≟PT PBuffer = no λ ()
  PVoid ≟PT (_ P* _) = no λ ()
  PVoid ≟PT (_ P+ _) = no λ ()
  PVoid ≟PT (_ P⇒[ _ ] _) = no λ ()
  PVoid ≟PT PEff _ _ = no λ ()
  PVoid ≟PT Pμ-type _ = no λ ()
  PVoid ≟PT Pν-type _ = no λ ()
  PVoid ≟PT TVar _ = no λ ()
  PInt ≟PT PUnit = no λ ()
  PInt ≟PT PVoid = no λ ()
  PInt ≟PT PFloat = no λ ()
  PInt ≟PT PStr = no λ ()
  PInt ≟PT PBuffer = no λ ()
  PInt ≟PT (_ P* _) = no λ ()
  PInt ≟PT (_ P+ _) = no λ ()
  PInt ≟PT (_ P⇒[ _ ] _) = no λ ()
  PInt ≟PT PEff _ _ = no λ ()
  PInt ≟PT Pμ-type _ = no λ ()
  PInt ≟PT Pν-type _ = no λ ()
  PInt ≟PT TVar _ = no λ ()
  PFloat ≟PT PUnit = no λ ()
  PFloat ≟PT PVoid = no λ ()
  PFloat ≟PT PInt = no λ ()
  PFloat ≟PT PStr = no λ ()
  PFloat ≟PT PBuffer = no λ ()
  PFloat ≟PT (_ P* _) = no λ ()
  PFloat ≟PT (_ P+ _) = no λ ()
  PFloat ≟PT (_ P⇒[ _ ] _) = no λ ()
  PFloat ≟PT PEff _ _ = no λ ()
  PFloat ≟PT Pμ-type _ = no λ ()
  PFloat ≟PT Pν-type _ = no λ ()
  PFloat ≟PT TVar _ = no λ ()
  PStr ≟PT PUnit = no λ ()
  PStr ≟PT PVoid = no λ ()
  PStr ≟PT PInt = no λ ()
  PStr ≟PT PFloat = no λ ()
  PStr ≟PT PBuffer = no λ ()
  PStr ≟PT (_ P* _) = no λ ()
  PStr ≟PT (_ P+ _) = no λ ()
  PStr ≟PT (_ P⇒[ _ ] _) = no λ ()
  PStr ≟PT PEff _ _ = no λ ()
  PStr ≟PT Pμ-type _ = no λ ()
  PStr ≟PT Pν-type _ = no λ ()
  PStr ≟PT TVar _ = no λ ()
  PBuffer ≟PT PUnit = no λ ()
  PBuffer ≟PT PVoid = no λ ()
  PBuffer ≟PT PInt = no λ ()
  PBuffer ≟PT PFloat = no λ ()
  PBuffer ≟PT PStr = no λ ()
  PBuffer ≟PT (_ P* _) = no λ ()
  PBuffer ≟PT (_ P+ _) = no λ ()
  PBuffer ≟PT (_ P⇒[ _ ] _) = no λ ()
  PBuffer ≟PT PEff _ _ = no λ ()
  PBuffer ≟PT Pμ-type _ = no λ ()
  PBuffer ≟PT Pν-type _ = no λ ()
  PBuffer ≟PT TVar _ = no λ ()
  (_ P* _) ≟PT PUnit = no λ ()
  (_ P* _) ≟PT PVoid = no λ ()
  (_ P* _) ≟PT PInt = no λ ()
  (_ P* _) ≟PT PFloat = no λ ()
  (_ P* _) ≟PT PStr = no λ ()
  (_ P* _) ≟PT PBuffer = no λ ()
  (_ P* _) ≟PT (_ P+ _) = no λ ()
  (_ P* _) ≟PT (_ P⇒[ _ ] _) = no λ ()
  (_ P* _) ≟PT PEff _ _ = no λ ()
  (_ P* _) ≟PT Pμ-type _ = no λ ()
  (_ P* _) ≟PT Pν-type _ = no λ ()
  (_ P* _) ≟PT TVar _ = no λ ()
  (_ P+ _) ≟PT PUnit = no λ ()
  (_ P+ _) ≟PT PVoid = no λ ()
  (_ P+ _) ≟PT PInt = no λ ()
  (_ P+ _) ≟PT PFloat = no λ ()
  (_ P+ _) ≟PT PStr = no λ ()
  (_ P+ _) ≟PT PBuffer = no λ ()
  (_ P+ _) ≟PT (_ P* _) = no λ ()
  (_ P+ _) ≟PT (_ P⇒[ _ ] _) = no λ ()
  (_ P+ _) ≟PT PEff _ _ = no λ ()
  (_ P+ _) ≟PT Pμ-type _ = no λ ()
  (_ P+ _) ≟PT Pν-type _ = no λ ()
  (_ P+ _) ≟PT TVar _ = no λ ()
  (_ P⇒[ _ ] _) ≟PT PUnit = no λ ()
  (_ P⇒[ _ ] _) ≟PT PVoid = no λ ()
  (_ P⇒[ _ ] _) ≟PT PInt = no λ ()
  (_ P⇒[ _ ] _) ≟PT PFloat = no λ ()
  (_ P⇒[ _ ] _) ≟PT PStr = no λ ()
  (_ P⇒[ _ ] _) ≟PT PBuffer = no λ ()
  (_ P⇒[ _ ] _) ≟PT (_ P* _) = no λ ()
  (_ P⇒[ _ ] _) ≟PT (_ P+ _) = no λ ()
  (_ P⇒[ _ ] _) ≟PT PEff _ _ = no λ ()
  (_ P⇒[ _ ] _) ≟PT Pμ-type _ = no λ ()
  (_ P⇒[ _ ] _) ≟PT Pν-type _ = no λ ()
  (_ P⇒[ _ ] _) ≟PT TVar _ = no λ ()
  PEff _ _ ≟PT PUnit = no λ ()
  PEff _ _ ≟PT PVoid = no λ ()
  PEff _ _ ≟PT PInt = no λ ()
  PEff _ _ ≟PT PFloat = no λ ()
  PEff _ _ ≟PT PStr = no λ ()
  PEff _ _ ≟PT PBuffer = no λ ()
  PEff _ _ ≟PT (_ P* _) = no λ ()
  PEff _ _ ≟PT (_ P+ _) = no λ ()
  PEff _ _ ≟PT (_ P⇒[ _ ] _) = no λ ()
  PEff _ _ ≟PT Pμ-type _ = no λ ()
  PEff _ _ ≟PT Pν-type _ = no λ ()
  PEff _ _ ≟PT TVar _ = no λ ()
  Pμ-type _ ≟PT PUnit = no λ ()
  Pμ-type _ ≟PT PVoid = no λ ()
  Pμ-type _ ≟PT PInt = no λ ()
  Pμ-type _ ≟PT PFloat = no λ ()
  Pμ-type _ ≟PT PStr = no λ ()
  Pμ-type _ ≟PT PBuffer = no λ ()
  Pμ-type _ ≟PT (_ P* _) = no λ ()
  Pμ-type _ ≟PT (_ P+ _) = no λ ()
  Pμ-type _ ≟PT (_ P⇒[ _ ] _) = no λ ()
  Pμ-type _ ≟PT PEff _ _ = no λ ()
  Pμ-type _ ≟PT Pν-type _ = no λ ()
  Pμ-type _ ≟PT TVar _ = no λ ()
  Pν-type _ ≟PT PUnit = no λ ()
  Pν-type _ ≟PT PVoid = no λ ()
  Pν-type _ ≟PT PInt = no λ ()
  Pν-type _ ≟PT PFloat = no λ ()
  Pν-type _ ≟PT PStr = no λ ()
  Pν-type _ ≟PT PBuffer = no λ ()
  Pν-type _ ≟PT (_ P* _) = no λ ()
  Pν-type _ ≟PT (_ P+ _) = no λ ()
  Pν-type _ ≟PT (_ P⇒[ _ ] _) = no λ ()
  Pν-type _ ≟PT PEff _ _ = no λ ()
  Pν-type _ ≟PT Pμ-type _ = no λ ()
  Pν-type _ ≟PT TVar _ = no λ ()
  TVar _ ≟PT PUnit = no λ ()
  TVar _ ≟PT PVoid = no λ ()
  TVar _ ≟PT PInt = no λ ()
  TVar _ ≟PT PFloat = no λ ()
  TVar _ ≟PT PStr = no λ ()
  TVar _ ≟PT PBuffer = no λ ()
  TVar _ ≟PT (_ P* _) = no λ ()
  TVar _ ≟PT (_ P+ _) = no λ ()
  TVar _ ≟PT (_ P⇒[ _ ] _) = no λ ()
  TVar _ ≟PT PEff _ _ = no λ ()
  TVar _ ≟PT Pμ-type _ = no λ ()
  TVar _ ≟PT Pν-type _ = no λ ()

------------------------------------------------------------------------
-- Type Matching with Unification (for polymorphic inference)
------------------------------------------------------------------------

-- | Check if two PolyTypes can be unified
-- Returns the result type (with TVars replaced) and an updated substitution
--
-- Simpler than full unification: TVars match anything, and we return
-- the more concrete type.
--
-- For `matches expected actual`:
-- - If expected is a TVar, return actual (TVar gets instantiated)
-- - If actual is a TVar, return expected (shouldn't happen in well-typed code)
-- - Otherwise, check structural equality
--
matchesPolyType : PolyType → PolyType → Maybe PolyType
matchesPolyType (TVar _) actual = just actual  -- TVar matches anything, instantiate to actual
matchesPolyType expected (TVar _) = just expected  -- Actual is TVar, use expected
matchesPolyType PUnit PUnit = just PUnit
matchesPolyType PVoid PVoid = just PVoid
matchesPolyType PInt PInt = just PInt
matchesPolyType PFloat PFloat = just PFloat
matchesPolyType PStr PStr = just PStr
matchesPolyType PBuffer PBuffer = just PBuffer
matchesPolyType (A₁ P* B₁) (A₂ P* B₂) with matchesPolyType A₁ A₂ | matchesPolyType B₁ B₂
... | just A | just B = just (A P* B)
... | _ | _ = nothing
matchesPolyType (A₁ P+ B₁) (A₂ P+ B₂) with matchesPolyType A₁ A₂ | matchesPolyType B₁ B₂
... | just A | just B = just (A P+ B)
... | _ | _ = nothing
matchesPolyType (A₁ P⇒[ q₁ ] B₁) (A₂ P⇒[ q₂ ] B₂) with matchesPolyType A₁ A₂ | matchesPolyType B₁ B₂
... | just A | just B = just (A P⇒[ q₁ ] B)  -- Keep first quantity
... | _ | _ = nothing
matchesPolyType (PEff A₁ B₁) (PEff A₂ B₂) with matchesPolyType A₁ A₂ | matchesPolyType B₁ B₂
... | just A | just B = just (PEff A B)
... | _ | _ = nothing
matchesPolyType (Pμ-type F₁) (Pμ-type F₂) with F₁ ≟PF F₂
... | yes refl = just (Pμ-type F₁)
... | no _ = nothing
matchesPolyType (Pν-type F₁) (Pν-type F₂) with F₁ ≟PF F₂
... | yes refl = just (Pν-type F₁)
... | no _ = nothing
matchesPolyType _ _ = nothing

-- | Substitute TVars in a type based on a match
-- When we match `TVar x` against `T`, all occurrences of `TVar x` in related
-- types should be replaced by `T`.
--
-- For simplicity, we use a single-TVar substitution approach:
-- substituteTV varName replacement target
substituteTVar : String → PolyType → PolyType → PolyType
substituteTVar name rep (TVar x) with name Data.String.≟ x
... | yes _ = rep
... | no _ = TVar x
substituteTVar _ _ PUnit = PUnit
substituteTVar _ _ PVoid = PVoid
substituteTVar _ _ PInt = PInt
substituteTVar _ _ PFloat = PFloat
substituteTVar _ _ PStr = PStr
substituteTVar _ _ PBuffer = PBuffer
substituteTVar name rep (A P* B) = substituteTVar name rep A P* substituteTVar name rep B
substituteTVar name rep (A P+ B) = substituteTVar name rep A P+ substituteTVar name rep B
substituteTVar name rep (A P⇒[ q ] B) = substituteTVar name rep A P⇒[ q ] substituteTVar name rep B
substituteTVar name rep (PEff A B) = PEff (substituteTVar name rep A) (substituteTVar name rep B)
substituteTVar _ _ (Pμ-type F) = Pμ-type F  -- Don't substitute inside functors
substituteTVar _ _ (Pν-type F) = Pν-type F

------------------------------------------------------------------------
-- Bidirectional Type Checking Results
------------------------------------------------------------------------

-- | Result of type inference (compute the type)
-- Includes:
--   - Maximum nesting depth encountered (for verification limit tracking)
--   - Updated fresh counter (for polymorphic instantiation)
--   - Usage vector (for QTT - tracks how variables were used)
data InferElabResult {n : ℕ} (Δ : SCtx n) : Set where
  success : (A : Type) → SExpr Δ A → (depth : ℕ) → (fresh : ℕ)
          → (usage : Surface.Usage n)  -- NEW: QTT usage tracking
          → InferElabResult Δ
  failure : String → InferElabResult Δ

-- | Result of type checking (verify against expected type)
-- The type is known, so we only return the expression, depth, fresh counter, and usage
data CheckElabResult {n : ℕ} (Δ : SCtx n) (A : Type) : Set where
  success : SExpr Δ A → (depth : ℕ) → (fresh : ℕ)
          → (usage : Surface.Usage n)  -- NEW: QTT usage tracking
          → CheckElabResult Δ A
  failure : String → CheckElabResult Δ A

------------------------------------------------------------------------
-- QTT Usage Helpers
------------------------------------------------------------------------

-- Import usage operations from Surface.Syntax
open Surface using (zeroUsage; singleUse; _+ᵘ_; _*ᵘ_) public

------------------------------------------------------------------------
-- Polymorphic Inference Results (Phase 4: PolyExpr throughout)
------------------------------------------------------------------------

-- | Polymorphic usage vector (same structure as Surface.Usage)
-- Reuse Surface.Usage since it's just a vector of quantities
PolyUsage : ℕ → Set
PolyUsage = Surface.Usage

-- | Result of polymorphic type inference (compute the PolyType)
-- Used during inference phase when working with type variables.
data PolyInferResult {n : ℕ} (Γ : PolyCtx n) : Set where
  success : (A : PolyType) → PolyExpr Γ A → (depth : ℕ) → (fresh : ℕ)
          → (usage : PolyUsage n)
          → PolyInferResult Γ
  failure : String → PolyInferResult Γ

-- | Result of polymorphic type checking (verify against expected PolyType)
data PolyCheckResult {n : ℕ} (Γ : PolyCtx n) (A : PolyType) : Set where
  success : PolyExpr Γ A → (depth : ℕ) → (fresh : ℕ)
          → (usage : PolyUsage n)
          → PolyCheckResult Γ A
  failure : String → PolyCheckResult Γ A

------------------------------------------------------------------------
-- Named Context with de Bruijn Correspondence
------------------------------------------------------------------------

-- | Imported primitives from other modules (e.g., "S.exit0" → Eff Unit Unit)
-- These are populated from qualified imports like "import M as S"
Imports : Set
Imports = List (String × Type)

-- | Empty imports
emptyImports : Imports
emptyImports = []

-- | A named context paired with its de Bruijn representation
-- Includes a fresh counter for generating unique type variables during instantiation
-- and imported primitives from other modules
record NamedCtx : Set where
  constructor mkCtx
  field
    size        : ℕ
    named       : Ctx
    debruijn    : SCtx size
    freshCounter : ℕ  -- For generating fresh type variables (α₀, α₁, α₂, ...)
    imports     : Imports  -- Imported primitives (qualified names → types)

-- | Empty context
emptyCtx : NamedCtx
emptyCtx = mkCtx 0 ∅ S∅ 0 emptyImports

-- | Create context with imports
ctxWithImports : Imports → NamedCtx
ctxWithImports imps = mkCtx 0 ∅ S∅ 0 imps

-- | Create context with imports and self-reference for recursive definitions
-- The function's own name and type are added to the imports list so it can call itself.
-- This causes recursive calls to elaborate to `Prim "name"` which the C backend
-- handles as a function call.
ctxWithImportsAndSelf : Imports → String → Type → NamedCtx
ctxWithImportsAndSelf imps name ty =
  ctxWithImports ((name , ty) ∷ imps)

-- | Extend context with a new binding (preserves fresh counter and imports)
extendNamedCtx : NamedCtx → String → Type → NamedCtx
extendNamedCtx (mkCtx n Γ Δ fresh imps) x A = mkCtx (suc n) (extendCtx Γ x A) (Δ S, A) fresh imps

-- | Bump fresh counter (for generating new type variables)
bumpFresh : NamedCtx → NamedCtx
bumpFresh (mkCtx n Γ Δ fresh imps) = mkCtx n Γ Δ (suc fresh) imps

-- | Generate fresh type variable name
freshTVar : ℕ → String
freshTVar n = "α" ++ showℕ n

------------------------------------------------------------------------
-- Polymorphic Named Context (Phase 4)
------------------------------------------------------------------------

-- | Polymorphic imports (uses PolyType for primitive types)
-- During inference, imported primitives have their types embedded as PolyType
PolyImports : Set
PolyImports = List (String × PolyType)

-- | Convert ground imports to polymorphic imports
embedImports : Imports → PolyImports
embedImports [] = []
embedImports ((n , ty) ∷ rest) = (n , embed ty) ∷ embedImports rest

-- | A polymorphic named context for use during type inference
-- Uses PolyCtx (indexed by PolyType) instead of SCtx (indexed by Type)
record PolyNamedCtx : Set where
  constructor mkPolyCtx
  field
    size        : ℕ
    named       : Ctx                -- Named bindings (for lookup by name)
    polyCtx     : PolyCtx size       -- De Bruijn context with PolyType
    freshCounter : ℕ                 -- For generating fresh type variables
    polyImports : PolyImports        -- Imported primitives with embedded types

-- | Empty polymorphic context
emptyPolyCtx : PolyNamedCtx
emptyPolyCtx = mkPolyCtx 0 ∅ P∅ 0 []

-- | Create polymorphic context from ground imports
polyCtxWithImports : Imports → PolyNamedCtx
polyCtxWithImports imps = mkPolyCtx 0 ∅ P∅ 0 (embedImports imps)

-- | Create polymorphic context with imports and self-reference
polyCtxWithImportsAndSelf : Imports → String → Type → PolyNamedCtx
polyCtxWithImportsAndSelf imps name ty =
  polyCtxWithImports ((name , ty) ∷ imps)

-- | Extend polymorphic context with a new binding
-- The ground type is embedded as PolyType for use during inference
extendPolyNamedCtx : PolyNamedCtx → String → Type → PolyNamedCtx
extendPolyNamedCtx (mkPolyCtx n Γ Δ fresh imps) x A =
  mkPolyCtx (suc n) (extendCtx Γ x A) (Δ P, embed A) fresh imps

-- | Bump fresh counter in polymorphic context
bumpPolyFresh : PolyNamedCtx → PolyNamedCtx
bumpPolyFresh (mkPolyCtx n Γ Δ fresh imps) = mkPolyCtx n Γ Δ (suc fresh) imps

-- | Set fresh counter to specific value
setPolyFresh : PolyNamedCtx → ℕ → PolyNamedCtx
setPolyFresh (mkPolyCtx n Γ Δ _ imps) fresh = mkPolyCtx n Γ Δ fresh imps

-- | Extend polymorphic context with a PolyType binding (default quantity Many)
-- Used during inference when parameter types may still have TVars
extendPolyNamedCtxPoly : PolyNamedCtx → String → PolyType → PolyNamedCtx
extendPolyNamedCtxPoly (mkPolyCtx n Γ Δ fresh imps) x A =
  -- Note: We add to named context using a placeholder type.
  -- The actual type is tracked in polyCtx.
  mkPolyCtx (suc n) (extendCtx Γ x Unit) (Δ P, A) fresh imps

-- | Extend polymorphic context with a PolyType binding and specific quantity
-- Used in checking mode where the quantity is known from the expected type
extendPolyNamedCtxPolyQ : PolyNamedCtx → String → PolyType → Quantity → PolyNamedCtx
extendPolyNamedCtxPolyQ (mkPolyCtx n Γ Δ fresh imps) x A q =
  mkPolyCtx (suc n) (extendCtx Γ x Unit) (Poly._P,_^_ Δ A q) fresh imps

------------------------------------------------------------------------
-- Helper: Find de Bruijn index of a variable by name
------------------------------------------------------------------------

-- | Find the de Bruijn index of a variable by name in the named context
-- Returns nothing if the variable is not found (it's a built-in)
findVarIndex : (ctx : NamedCtx) → String → Maybe (Fin (NamedCtx.size ctx))
findVarIndex (mkCtx n Γ Δ fresh imps) x = go Γ Δ
  where
    go : ∀ {m} → Ctx → (Δ' : SCtx m) → Maybe (Fin m)
    go [] S∅ = nothing  -- Variable not found in context (must be built-in)
    go [] (_ S, _ ^ _) = nothing  -- Impossible: named empty but debruijn not
    go (_ ∷ _) S∅ = nothing  -- Impossible: named non-empty but debruijn empty
    go {suc m} (b ∷ Γ') (Δ' S, B ^ q) with Data.String._≟_ x (name b)
    ... | yes _ = just zero  -- Found at position 0
    ... | no  _ with go Γ' Δ'
    ...   | nothing = nothing
    ...   | just i  = just (suc i)  -- Found at position suc i

------------------------------------------------------------------------
-- Type Substitution and Instantiation (uses PolyType)
------------------------------------------------------------------------
--
-- Substitutions map type variable names to PolyType values.
-- During inference, we work with PolyType (which can have TVars).
-- At the end, we extract to Type (which has no TVars).
--

-- | Substitution: mapping from type variable names to polymorphic types
-- Named InferSubst to avoid clash with Type.Subst (used for principled extraction)
InferSubst : Set
InferSubst = List (String × PolyType)

-- | Empty substitution
emptyInferSubst : InferSubst
emptyInferSubst = []

-- | Extend substitution with a new binding
extendInferSubst : InferSubst → String → PolyType → InferSubst
extendInferSubst σ x A = (x , A) ∷ σ

-- | Look up type variable in substitution
lookupInferSubst : InferSubst → String → Maybe PolyType
lookupInferSubst [] _ = nothing
lookupInferSubst ((x , A) ∷ σ) y with x Data.String.≟ y
... | yes _ = just A
... | no  _ = lookupInferSubst σ y

-- | Apply substitution to a polymorphic type
mutual
  applySubstPF : InferSubst → PolyFunctor → PolyFunctor
  applySubstPF σ (PK A) = PK (applySubst σ A)
  applySubstPF _ PId = PId
  applySubstPF σ (F P⊕ G) = applySubstPF σ F P⊕ applySubstPF σ G
  applySubstPF σ (F P⊗ G) = applySubstPF σ F P⊗ applySubstPF σ G

  applySubst : InferSubst → PolyType → PolyType
  applySubst σ PUnit = PUnit
  applySubst σ PVoid = PVoid
  applySubst σ PInt = PInt
  applySubst σ PFloat = PFloat
  applySubst σ PStr = PStr
  applySubst σ PBuffer = PBuffer
  applySubst σ (A P* B) = applySubst σ A P* applySubst σ B
  applySubst σ (A P+ B) = applySubst σ A P+ applySubst σ B
  applySubst σ (A P⇒[ q ] B) = applySubst σ A P⇒[ q ] applySubst σ B
  applySubst σ (PEff A B) = PEff (applySubst σ A) (applySubst σ B)
  applySubst σ (Pμ-type F) = Pμ-type (applySubstPF σ F)
  applySubst σ (Pν-type F) = Pν-type (applySubstPF σ F)
  applySubst σ (TVar x) with lookupInferSubst σ x
  ... | just A = A
  ... | nothing = TVar x  -- Unbound type variable remains

------------------------------------------------------------------------
-- Substitution on Contexts
------------------------------------------------------------------------

-- | Apply substitution to a polymorphic context
applySubstCtx : ∀ {n} → InferSubst → PolyCtx n → PolyCtx n
applySubstCtx σ P∅ = P∅
applySubstCtx σ (Γ P, A ^ q) = Poly._P,_^_ (applySubstCtx σ Γ) (applySubst σ A) q

-- | Lookup commutes with substitution
lookupPoly-applySubst : ∀ {n} (σ : InferSubst) (Γ : PolyCtx n) (i : Fin n)
                      → lookupPoly (applySubstCtx σ Γ) i ≡ applySubst σ (lookupPoly Γ i)
lookupPoly-applySubst σ (Γ P, A ^ q) Fin.zero = refl
lookupPoly-applySubst σ (Γ P, A ^ q) (Fin.suc i) = lookupPoly-applySubst σ Γ i

-- | Quantity lookup is unchanged by type substitution
lookupPolyQuantity-applySubst : ∀ {n} (σ : InferSubst) (Γ : PolyCtx n) (i : Fin n)
                              → lookupPolyQuantity (applySubstCtx σ Γ) i ≡ lookupPolyQuantity Γ i
lookupPolyQuantity-applySubst σ (Γ P, A ^ q) Fin.zero = refl
lookupPolyQuantity-applySubst σ (Γ P, A ^ q) (Fin.suc i) = lookupPolyQuantity-applySubst σ Γ i

------------------------------------------------------------------------
-- Substitution on Expressions
------------------------------------------------------------------------

-- | Apply substitution to a polymorphic expression
-- Transforms PolyExpr Γ A to PolyExpr (applySubstCtx σ Γ) (applySubst σ A)
applySubstExpr : ∀ {n} {Γ : PolyCtx n} {A} (σ : InferSubst)
               → PolyExpr Γ A
               → PolyExpr (applySubstCtx σ Γ) (applySubst σ A)
applySubstExpr {Γ = Γ} σ (pvar i) =
  subst (PolyExpr (applySubstCtx σ Γ)) (lookupPoly-applySubst σ Γ i) (pvar i)
applySubstExpr σ (plam q body) = plam q (applySubstExpr σ body)
applySubstExpr σ (papp f x) = papp (applySubstExpr σ f) (applySubstExpr σ x)
applySubstExpr σ (peffApp f x) = peffApp (applySubstExpr σ f) (applySubstExpr σ x)
applySubstExpr σ (ppair e₁ e₂) = ppair (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (pfst' e) = pfst' (applySubstExpr σ e)
applySubstExpr σ (psnd' e) = psnd' (applySubstExpr σ e)
applySubstExpr σ (pinl' e) = pinl' (applySubstExpr σ e)
applySubstExpr σ (pinr' e) = pinr' (applySubstExpr σ e)
applySubstExpr σ (pcase' s l r) = pcase' (applySubstExpr σ s) (applySubstExpr σ l) (applySubstExpr σ r)
applySubstExpr σ punit = punit
applySubstExpr σ (pabsurd e) = pabsurd (applySubstExpr σ e)
applySubstExpr σ (plet' e₁ e₂) = plet' (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (pint n) = pint n
applySubstExpr σ (pstr s) = pstr s
applySubstExpr σ (padd e₁ e₂) = padd (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (psub e₁ e₂) = psub (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (pmul e₁ e₂) = pmul (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (pdiv e₁ e₂) = pdiv (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (pmod' e₁ e₂) = pmod' (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (pneg e) = pneg (applySubstExpr σ e)
applySubstExpr σ (plt e₁ e₂) = plt (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (ple e₁ e₂) = ple (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (pgt e₁ e₂) = pgt (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (pge e₁ e₂) = pge (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (peq e₁ e₂) = peq (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (pne e₁ e₂) = pne (applySubstExpr σ e₁) (applySubstExpr σ e₂)
applySubstExpr σ (parr' e) = parr' (applySubstExpr σ e)
applySubstExpr σ (pprim name) = pprim name

------------------------------------------------------------------------
-- Ground Context Lemmas
------------------------------------------------------------------------

-- | Substitution is identity on ground types
applySubst-ground : (σ : InferSubst) (A : PolyType) → Ground A → applySubst σ A ≡ A
applySubstPF-ground : (σ : InferSubst) (F : PolyFunctor) → GroundFunctor F → applySubstPF σ F ≡ F

applySubst-ground σ PUnit gA = refl
applySubst-ground σ PVoid gA = refl
applySubst-ground σ PInt gA = refl
applySubst-ground σ PFloat gA = refl
applySubst-ground σ PStr gA = refl
applySubst-ground σ PBuffer gA = refl
applySubst-ground σ (A P* B) (gA , gB) =
  cong₂ _P*_ (applySubst-ground σ A gA) (applySubst-ground σ B gB)
applySubst-ground σ (A P+ B) (gA , gB) =
  cong₂ _P+_ (applySubst-ground σ A gA) (applySubst-ground σ B gB)
applySubst-ground σ (A P⇒[ q ] B) (gA , gB) =
  cong₂ (λ a b → a P⇒[ q ] b) (applySubst-ground σ A gA) (applySubst-ground σ B gB)
applySubst-ground σ (PEff A B) (gA , gB) =
  cong₂ PEff (applySubst-ground σ A gA) (applySubst-ground σ B gB)
applySubst-ground σ (Pμ-type F) gF = cong Pμ-type (applySubstPF-ground σ F gF)
applySubst-ground σ (Pν-type F) gF = cong Pν-type (applySubstPF-ground σ F gF)

applySubstPF-ground σ (PK A) gA = cong PK (applySubst-ground σ A gA)
applySubstPF-ground σ PId tt = refl
applySubstPF-ground σ (F P⊕ G) (gF , gG) =
  cong₂ _P⊕_ (applySubstPF-ground σ F gF) (applySubstPF-ground σ G gG)
applySubstPF-ground σ (F P⊗ G) (gF , gG) =
  cong₂ _P⊗_ (applySubstPF-ground σ F gF) (applySubstPF-ground σ G gG)

-- | Substitution is identity on ground contexts
applySubstCtx-ground : ∀ {n} (σ : InferSubst) (Γ : PolyCtx n) → GroundCtx Γ → applySubstCtx σ Γ ≡ Γ
applySubstCtx-ground σ P∅ tt = refl
applySubstCtx-ground σ (Γ P, A ^ q) (gΓ , gA) =
  cong₂ (λ ctx ty → Poly._P,_^_ ctx ty q) (applySubstCtx-ground σ Γ gΓ) (applySubst-ground σ A gA)

-- | Match two PolyTypes and collect substitutions
-- Returns (unified type, substitution)
-- The substitution maps TVar names to their resolved types.
matchWithSubst : PolyType → PolyType → InferSubst → Maybe (PolyType × InferSubst)
matchWithSubst (TVar x) actual σ = just (actual , extendInferSubst σ x actual)
matchWithSubst expected (TVar x) σ = just (expected , extendInferSubst σ x expected)
matchWithSubst PUnit PUnit σ = just (PUnit , σ)
matchWithSubst PVoid PVoid σ = just (PVoid , σ)
matchWithSubst PInt PInt σ = just (PInt , σ)
matchWithSubst PFloat PFloat σ = just (PFloat , σ)
matchWithSubst PStr PStr σ = just (PStr , σ)
matchWithSubst PBuffer PBuffer σ = just (PBuffer , σ)
matchWithSubst (A₁ P* B₁) (A₂ P* B₂) σ with matchWithSubst A₁ A₂ σ
... | nothing = nothing
... | just (A , σ') with matchWithSubst B₁ B₂ σ'
...   | nothing = nothing
...   | just (B , σ'') = just (A P* B , σ'')
matchWithSubst (A₁ P+ B₁) (A₂ P+ B₂) σ with matchWithSubst A₁ A₂ σ
... | nothing = nothing
... | just (A , σ') with matchWithSubst B₁ B₂ σ'
...   | nothing = nothing
...   | just (B , σ'') = just (A P+ B , σ'')
matchWithSubst (A₁ P⇒[ q₁ ] B₁) (A₂ P⇒[ q₂ ] B₂) σ with matchWithSubst A₁ A₂ σ
... | nothing = nothing
... | just (A , σ') with matchWithSubst B₁ B₂ σ'
...   | nothing = nothing
...   | just (B , σ'') = just (A P⇒[ q₁ ] B , σ'')
matchWithSubst (PEff A₁ B₁) (PEff A₂ B₂) σ with matchWithSubst A₁ A₂ σ
... | nothing = nothing
... | just (A , σ') with matchWithSubst B₁ B₂ σ'
...   | nothing = nothing
...   | just (B , σ'') = just (PEff A B , σ'')
matchWithSubst (Pμ-type F₁) (Pμ-type F₂) σ with F₁ ≟PF F₂
... | yes refl = just (Pμ-type F₁ , σ)
... | no _ = nothing
matchWithSubst (Pν-type F₁) (Pν-type F₂) σ with F₁ ≟PF F₂
... | yes refl = just (Pν-type F₁ , σ)
... | no _ = nothing
matchWithSubst _ _ _ = nothing

-- | Instantiate a polymorphic type with fresh type variables
-- Collects all distinct TVar names and substitutes them with fresh variables
instantiate : PolyType → ℕ → PolyType × ℕ
instantiate ty counter = go ty counter emptyInferSubst
  where
    go : PolyType → ℕ → InferSubst → PolyType × ℕ
    go PUnit n σ = PUnit , n
    go PVoid n σ = PVoid , n
    go PInt n σ = PInt , n
    go PFloat n σ = PFloat , n
    go PStr n σ = PStr , n
    go PBuffer n σ = PBuffer , n
    go (A P* B) n σ =
      let (A' , n') = go A n σ
          (B' , n'') = go B n' σ
      in (A' P* B') , n''
    go (A P+ B) n σ =
      let (A' , n') = go A n σ
          (B' , n'') = go B n' σ
      in (A' P+ B') , n''
    go (A P⇒[ q ] B) n σ =
      let (A' , n') = go A n σ
          (B' , n'') = go B n' σ
      in (A' P⇒[ q ] B') , n''
    go (PEff A B) n σ =
      let (A' , n') = go A n σ
          (B' , n'') = go B n' σ
      in PEff A' B' , n''
    -- OCP-0003: Pμ-type and Pν-type pass through (functors don't contain TVars in practice)
    go (Pμ-type F) n σ = Pμ-type F , n
    go (Pν-type F) n σ = Pν-type F , n
    go (TVar x) n σ with lookupInferSubst σ x
    ... | just A = A , n  -- Already instantiated
    ... | nothing =
        let fresh = TVar (freshTVar n)
            σ' = extendInferSubst σ x fresh
        in fresh , suc n

------------------------------------------------------------------------
-- Built-in Categorical Generators (Polymorphic)
------------------------------------------------------------------------

-- | Built-in categorical generators (implicitly imported)
--
-- These are the fundamental vocabulary of the categorical language:
-- identity, composition, products, coproducts, exponentials, etc.
--
-- They are available in all programs without explicit import.
--
-- Takes a fresh counter and returns instantiated PolyType + PolyExpr + new counter.
-- Uses PolyType because builtins are polymorphic (contain type variables).
--
-- Smart constructors for PolyType function arrows
_P⇒_ : PolyType → PolyType → PolyType
A P⇒ B = A P⇒[ Many ] B

infixr 30 _P⇒_

builtinPolyType : String → ℕ → Maybe (∃[ A ] (PolyExpr P∅ A × ℕ))
builtinPolyType "id" n =
  let a = TVar (freshTVar n)
  in just (a P⇒ a , plam Many (pvar zero) , suc n)
builtinPolyType "fst" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just ((a P* b) P⇒ a , plam Many (pfst' (pvar zero)) , suc (suc n))
builtinPolyType "snd" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just ((a P* b) P⇒ b , plam Many (psnd' (pvar zero)) , suc (suc n))
builtinPolyType "inl" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just (a P⇒ (a P+ b) , plam Many (pinl' (pvar zero)) , suc (suc n))
builtinPolyType "inr" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just (b P⇒ (a P+ b) , plam Many (pinr' (pvar zero)) , suc (suc n))
builtinPolyType "unit" n = just (PUnit , punit , n)
-- pair (fork/⟨_,_⟩): (A -> B) -> (A -> C) -> A -> (B * C)
-- pair = λf. λg. λx. (f x, g x)
builtinPolyType "pair" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
      c = TVar (freshTVar (suc (suc n)))
  in just ((a P⇒ b) P⇒ (a P⇒ c) P⇒ a P⇒ (b P* c) ,
          plam Many (plam Many (plam Many
            (ppair
              (papp (pvar (suc (suc zero))) (pvar zero))
              (papp (pvar (suc zero)) (pvar zero))))) ,
          suc (suc (suc n)))
-- terminal: α → Unit
-- terminal = λx. unit
builtinPolyType "terminal" n =
  let a = TVar (freshTVar n)
  in just (a P⇒ PUnit , plam Many punit , suc n)
-- initial: Void → α
-- initial = λx. absurd x
builtinPolyType "initial" n =
  let a = TVar (freshTVar n)
  in just (PVoid P⇒ a , plam Many (pabsurd (pvar zero)) , suc n)
-- curry: ((α * β) → γ) → α → β → γ
-- curry = λf. λx. λy. f (x, y)
builtinPolyType "curry" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
      c = TVar (freshTVar (suc (suc n)))
  in just (((a P* b) P⇒ c) P⇒ a P⇒ b P⇒ c ,
          plam Many (plam Many (plam Many
            (papp (pvar (suc (suc zero)))
                  (ppair (pvar (suc zero)) (pvar zero))))) ,
          suc (suc (suc n)))
-- apply: ((α → β) * α) → β
-- apply = λp. (fst p) (snd p)
builtinPolyType "apply" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just (((a P⇒ b) P* a) P⇒ b ,
          plam Many
            (papp (pfst' (pvar zero))
                  (psnd' (pvar zero))) ,
          suc (suc n))
-- compose: (β → γ) → (α → β) → α → γ
-- compose = λf. λg. λx. f (g x)
builtinPolyType "compose" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
      c = TVar (freshTVar (suc (suc n)))
  in just ((b P⇒ c) P⇒ (a P⇒ b) P⇒ a P⇒ c ,
          plam Many (plam Many (plam Many
            (papp (pvar (suc (suc zero)))
                  (papp (pvar (suc zero)) (pvar zero))))) ,
          suc (suc (suc n)))
-- arr: (α → β) → Eff α β
-- arr = λf. arr' f (where arr' is the Surface constructor)
builtinPolyType "arr" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just ((a P⇒ b) P⇒ PEff a b ,
          plam Many (parr' (pvar zero)) ,
          suc (suc n))
-- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana for recursive types.
-- case: (A → C) → (B → C) → (A + B) → C
-- case = λf. λg. λx. case' x (f a) (g b)
-- This is the copairing (coproduct eliminator) as a curried function.
-- In the body, f is at index 3, g at index 2, x at index 0 in the lambda context.
-- Inside case' branches, the bound variable is at index 0, so:
--   - left branch (context extended with a:A): f is at 3, a is at 0
--   - right branch (context extended with b:B): g is at 2, b is at 0
builtinPolyType "case" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
      c = TVar (freshTVar (suc (suc n)))
  in just ((a P⇒ c) P⇒ (b P⇒ c) P⇒ (a P+ b) P⇒ c ,
          plam Many (plam Many (plam Many
            (pcase' (pvar zero)
              (papp (pvar (suc (suc (suc zero)))) (pvar zero))
              (papp (pvar (suc (suc zero))) (pvar zero))))) ,
          suc (suc (suc n)))
-- Note: pure is NOT a builtin - it's library code defined as:
--   pure : A → Eff Unit A
--   pure x = arr (λ_ → x)
-- Or equivalently: pure = arr ∘ curry terminal
builtinPolyType _ _ = nothing

-- | Legacy wrapper that extracts PolyExpr to SExpr
--
-- For backward compatibility. Returns Type + SExpr if extraction succeeds.
-- Extraction may fail if the builtin type cannot be fully resolved.
--
builtinType : String → ℕ → Maybe (∃[ A ] (Surface.Expr S∅ A × ℕ))
builtinType name n with builtinPolyType name n
... | nothing = nothing
... | just (ptyp , pexpr , n') with extractExpr pexpr
...   | nothing = nothing  -- Expression extraction failed
...   | just (S∅ , typ , expr) = just (typ , expr , n')
...   | just (_ , _ , _) = nothing  -- Context mismatch (shouldn't happen for builtins)

------------------------------------------------------------------------
-- Variable Lookup with Weakening and Instantiation
------------------------------------------------------------------------

-- | Look up a type in the imports list by name
lookupImport : Imports → String → Maybe Type
lookupImport [] _ = nothing
lookupImport ((n , ty) ∷ rest) x with StrProp._≟_ n x
... | yes _ = just ty
... | no  _ = lookupImport rest x

-- | Look up a variable by name and return its de Bruijn indexed expression
--
-- Priority order:
-- 1. Local context (bound variables)
-- 2. Built-in generators (id, fst, snd, etc.)
-- 3. Imported primitives (from qualified imports)
--
-- For built-in polymorphic functions, instantiates type variables with fresh names.
-- Returns the looked-up type/expr and the updated fresh counter.
--
lookupVar : (ctx : NamedCtx) → String
          → Maybe (∃[ A ] (SExpr (NamedCtx.debruijn ctx) A × ℕ))
lookupVar (mkCtx n Γ Δ fresh imps) x = go Γ Δ fresh
  where
    go : ∀ {m} → Ctx → (Δ' : SCtx m) → ℕ → Maybe (∃[ A ] (SExpr Δ' A × ℕ))
    go [] S∅ freshCtr with builtinType x freshCtr
    ... | just (instTy , se , freshCtr') = just (instTy , weakenFromEmpty se , freshCtr')
    ... | nothing with lookupImport imps x
    ...   | just ty = just (ty , Surface.prim x , freshCtr)  -- Imported primitive
    ...   | nothing = nothing
    go [] (_ S, _ ^ _) _ = nothing  -- impossible case: named context empty but debruijn not
    go (_ ∷ _) S∅ _ = nothing   -- impossible case: named context non-empty but debruijn empty
    go {suc m} (b ∷ Γ') (Δ' S, B ^ Many) freshCtr with Data.String._≟_ x (name b)
    ... | yes _ = just (B , Surface.var zero , freshCtr)  -- Local var: no instantiation needed
    ... | no  _ with go Γ' Δ' freshCtr
    ...   | nothing = nothing
    ...   | just (A , se , freshCtr') = just (A , weaken se , freshCtr')
    go {suc m} (b ∷ Γ') (Δ' S, B ^ q) freshCtr with Data.String._≟_ x (name b)
    ... | yes _ = just (B , Surface.var zero , freshCtr)  -- Local var: no instantiation needed
    ... | no  _ with go Γ' Δ' freshCtr
    ...   | nothing = nothing
    ...   | just (A , se , freshCtr') = just (A , coerceQuantity (weaken {A = B} {q = q} se) , freshCtr')

------------------------------------------------------------------------
-- Polymorphic Variable Lookup (Phase 4)
------------------------------------------------------------------------

-- | Look up a type in the polymorphic imports list by name
lookupPolyImport : PolyImports → String → Maybe PolyType
lookupPolyImport [] _ = nothing
lookupPolyImport ((n , ty) ∷ rest) x with StrProp._≟_ n x
... | yes _ = just ty
... | no  _ = lookupPolyImport rest x

-- | Look up a variable by name and return its PolyExpr
--
-- Priority order:
-- 1. Local context (bound variables) - types are embedded as PolyType
-- 2. Built-in generators (id, fst, snd, etc.) - naturally polymorphic
-- 3. Imported primitives - types embedded as PolyType
--
-- Returns the looked-up PolyType/PolyExpr and the updated fresh counter.
--
lookupPolyVar : (ctx : PolyNamedCtx) → String
              → Maybe (∃[ A ] (PolyExpr (PolyNamedCtx.polyCtx ctx) A × ℕ))
lookupPolyVar (mkPolyCtx n Γ Δ fresh imps) x = go Γ Δ fresh
  where
    go : ∀ {m} → Ctx → (Δ' : PolyCtx m) → ℕ → Maybe (∃[ A ] (PolyExpr Δ' A × ℕ))
    go [] P∅ freshCtr with builtinPolyType x freshCtr
    ... | just (ptyp , pexpr , freshCtr') = just (ptyp , pweakenFromEmpty pexpr , freshCtr')
    ... | nothing with lookupPolyImport imps x
    ...   | just pty = just (pty , pprim x , freshCtr)  -- Imported primitive
    ...   | nothing = nothing
    go [] (_ P, _ ^ _) _ = nothing  -- impossible case
    go (_ ∷ _) P∅ _ = nothing   -- impossible case
    go {suc m} (b ∷ Γ') (Δ' P, B ^ q) freshCtr with Data.String._≟_ x (name b)
    ... | yes _ = just (B , pvar zero , freshCtr)  -- Local var
    ... | no  _ with go Γ' Δ' freshCtr
    ...   | nothing = nothing
    ...   | just (A , pe , freshCtr') = just (A , pweaken pe , freshCtr')

-- | Find the de Bruijn index of a variable by name in the polymorphic context
findPolyVarIndex : (ctx : PolyNamedCtx) → String → Maybe (Fin (PolyNamedCtx.size ctx))
findPolyVarIndex (mkPolyCtx n Γ Δ fresh imps) x = go Γ Δ
  where
    go : ∀ {m} → Ctx → (Δ' : PolyCtx m) → Maybe (Fin m)
    go [] P∅ = nothing  -- Variable not found (must be built-in)
    go [] (_ P, _ ^ _) = nothing  -- impossible
    go (_ ∷ _) P∅ = nothing  -- impossible
    go {suc m} (b ∷ Γ') (Δ' P, B ^ q) with Data.String._≟_ x (name b)
    ... | yes _ = just zero
    ... | no  _ with go Γ' Δ'
    ...   | nothing = nothing
    ...   | just i  = just (suc i)

------------------------------------------------------------------------
-- Bidirectional Type Checking: Inference and Checking Modes
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  -- | Type checking mode: verify expression has expected type
  -- This is the "checking" judgment: Γ ⊢ e ⇐ A
  checkElabImpl : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A

  -- Lambda with function type: check body against result type
  -- QTT: Validate parameter usage respects declared quantity, then drop from usage vector
  checkElabImpl ctx (Raw.RLam x body) (A ⇒[ q ] B) with checkElabImpl (extendNamedCtx ctx x A) body B
  ... | failure err = failure err
  ... | success bodyExpr depth fresh' usage' =
          -- Check parameter usage ≤ declared quantity
          let paramUsage = lookupUsage usage' zero
          in if paramUsage ≤q q
             then success (Surface.lam q bodyExpr) (suc depth) fresh' (tailUsage usage')
             else failure ("Parameter '" ++ x ++ "' used with quantity " ++ showQuantity paramUsage ++
                          " but declared with quantity " ++ showQuantity q)

  -- Lambda with non-function type: error
  checkElabImpl ctx (Raw.RLam _ _) ty =
    failure "Lambda requires function type"

  -- Default: fall back to inference and check equality
  checkElabImpl ctx expr expectedType with inferElabImpl ctx expr
  ... | failure err = failure err
  ... | success inferredType expr depth fresh' usage' with inferredType ≟T expectedType
  ...   | yes refl = success expr depth fresh' usage'
  ...   | no _     = failure ("Type mismatch: expected " ++ showType expectedType ++ " but got " ++ showType inferredType)

  -- | Type inference mode: compute the type
  -- This is the "inference" judgment: Γ ⊢ e ⇒ A
  inferElabImpl : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)

  -- Variable: look up in context (depth 0 - no nesting)
  -- For local variables, mark as used with their declared quantity
  -- For built-ins, usage is zero (they have no free variables)
  inferElabImpl ctx (Raw.RVar x) with lookupVar ctx x
  ... | nothing = failure ("Unbound variable: " ++ x)
  ... | just (A , se , fresh') with findVarIndex ctx x
  ...   | just i  = -- Local variable: mark as used with declared quantity
                    let q = lookupQuantity (NamedCtx.debruijn ctx) i
                    in success A se 0 fresh' (singleUse i q)
  ...   | nothing = -- Built-in: no usage (weakened from empty context)
                    success A se 0 fresh' zeroUsage

  -- Qualified variable: name@alias (e.g., exit0@S)
  -- Look up using "alias.name" format to find imported functions
  inferElabImpl ctx (Raw.RQualified name alias) with lookupVar ctx (alias ++ "." ++ name)
  ... | nothing = failure ("Unbound qualified variable: " ++ name ++ "@" ++ alias)
  ... | just (A , se , fresh') = success A se 0 fresh' zeroUsage  -- Imported: no local usage

  -- Lambda: infer body with extended context, wrap in lam (depth = body depth + 1)
  -- NOTE: Lambda without type annotation is NOT supported in inference mode.
  -- Use checking mode (checkElabImpl) with an explicit function type instead.
  -- Polymorphism comes from builtins (id, fst, snd, etc.) via instantiation.
  inferElabImpl ctx (Raw.RLam x body) =
    failure ("Lambda without type annotation not supported in inference mode.\n" ++
             "Add a type annotation or use a type-annotated expression.\n" ++
             "Example: (\\x -> body) : A -> B")

  -- Application: infer function, check it's a function type, infer arg, check types match
  -- (depth = max of function and argument depths, thread fresh counter through)
  -- QTT: Both function and argument contribute to usage, so combine with +ᵘ
  inferElabImpl ctx (Raw.RApp fun arg) = inferApp (inferElabImpl ctx fun)
    where
      inferApp : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
      inferApp (failure err) = failure err
      -- Support all quantities (Zero/One/Many) for function arrows
      inferApp (success (A ⇒[ q ] B) funExpr funDepth funFresh usageFun) = inferArg (inferElabImpl (bumpFreshTo ctx funFresh) arg)
        where
          bumpFreshTo : NamedCtx → ℕ → NamedCtx
          bumpFreshTo (mkCtx n Γ Δ _ imps) fresh = mkCtx n Γ Δ fresh imps

          inferArg : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
          inferArg (failure err) = failure err
          inferArg (success A' argExpr argDepth argFresh usageArg) with A ≟T A'
          ... | yes refl = success B (Surface.app funExpr argExpr) (funDepth ⊔ argDepth) argFresh (usageFun +ᵘ usageArg)
          ... | no _ = failure "Type mismatch in application"
      inferApp (success Unit _ _ _ _) = failure "Expected function type in application"
      inferApp (success Void _ _ _ _) = failure "Expected function type in application"
      inferApp (success Int _ _ _ _) = failure "Expected function type in application"
      inferApp (success Float _ _ _ _) = failure "Expected function type in application"
      inferApp (success Str _ _ _ _) = failure "Expected function type in application"
      inferApp (success Buffer _ _ _ _) = failure "Expected function type in application"
      inferApp (success (_ Once.Type.* _) _ _ _ _) = failure "Expected function type in application"
      inferApp (success (_ Once.Type.+ _) _ _ _ _) = failure "Expected function type in application"
      -- Eff A B is applicable like A ⇒ B (effectful morphism application)
      inferApp (success (Eff A B) funExpr funDepth funFresh usageFun) = inferArgEff (inferElabImpl (bumpFreshToEff ctx funFresh) arg)
        where
          bumpFreshToEff : NamedCtx → ℕ → NamedCtx
          bumpFreshToEff (mkCtx n Γ Δ _ imps) fresh = mkCtx n Γ Δ fresh imps

          inferArgEff : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
          inferArgEff (failure err) = failure err
          inferArgEff (success A' argExpr argDepth argFresh usageArg) with A ≟T A'
          ... | yes refl = success B (Surface.effApp funExpr argExpr) (funDepth ⊔ argDepth) argFresh (usageFun +ᵘ usageArg)
          ... | no _ = failure "Type mismatch in effect application"
      -- TVar removed from Type; now in PolyType (see Once.Type)
      -- OCP-0003: μ-type and ν-type are not function types
      inferApp (success (μ-type _) _ _ _ _) = failure "Expected function type in application"
      inferApp (success (ν-type _) _ _ _ _) = failure "Expected function type in application"
      -- GuardedT removed: productivity follows from IR totality

  -- Pair (depth = max of both elements, thread fresh counter)
  -- QTT: Both components contribute to usage, so combine with +ᵘ
  inferElabImpl ctx (Raw.RPair a b) with inferElabImpl ctx a
  ... | failure err = failure err
  ... | success A aExpr aDepth aFresh usage1 with inferElabImpl (bumpFresh' ctx aFresh) b
    where
      bumpFresh' : NamedCtx → ℕ → NamedCtx
      bumpFresh' (mkCtx n Γ Δ _ imps) fresh = mkCtx n Γ Δ fresh imps
  ...   | failure err = failure err
  ...   | success B bExpr bDepth bFresh usage2 =
        success (A Once.Type.* B) (Surface.pair aExpr bExpr) (aDepth ⊔ bDepth) bFresh (usage1 +ᵘ usage2)

  -- Unit (depth 0 - no nesting, preserve fresh counter)
  -- Unit doesn't use any variables, so usage is zero
  inferElabImpl ctx Raw.RUnit = success Unit Surface.unit 0 (NamedCtx.freshCounter ctx) zeroUsage

  -- Let binding (depth = max(e₁, e₂ + 1) since e₂ is under binder, thread fresh counter)
  -- QTT: Combine usage from binding and body (drop bound variable from body usage)
  inferElabImpl ctx (Raw.RLet x e₁ e₂) with inferElabImpl ctx e₁
  ... | failure err = failure err
  ... | success A e₁Expr e₁Depth e₁Fresh usage1 with inferElabImpl (extendNamedCtx' ctx x A e₁Fresh) e₂
    where
      extendNamedCtx' : NamedCtx → String → Type → ℕ → NamedCtx
      extendNamedCtx' (mkCtx n Γ Δ _ imps) y B fresh = mkCtx (suc n) (extendCtx Γ y B) (Δ S, B) fresh imps
  ...   | failure err = failure err
  ...   | success B e₂Expr e₂Depth e₂Fresh usage2 =
        success B (Surface.let' e₁Expr e₂Expr) (e₁Depth ⊔ suc e₂Depth) e₂Fresh (usage1 +ᵘ tailUsage usage2)

  -- Case analysis (depth = max(scrut, leftBranch + 1, rightBranch + 1) since branches are under binders)
  -- QTT: Combine usage from scrutinee and both branches (drop bound variables from branches)
  inferElabImpl ctx (Raw.RDestruct scrut xL eL xR eR) = inferCase (inferElabImpl ctx scrut)
    where
      extendCtx' : NamedCtx → String → Type → ℕ → NamedCtx
      extendCtx' (mkCtx n Γ Δ _ imps) y C fresh = mkCtx (suc n) (extendCtx Γ y C) (Δ S, C) fresh imps

      inferCase : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
      inferCase (failure err) = failure err
      inferCase (success (A Once.Type.+ B) scrutExpr scrutDepth scrutFresh usageScr) = inferLeft (inferElabImpl (extendCtx' ctx xL A scrutFresh) eL)
        where
          inferLeft : InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xL A))
                    → InferElabResult (NamedCtx.debruijn ctx)
          inferLeft (failure err) = failure err
          inferLeft (success C₁ eLExpr eLDepth eLFresh usageL) = inferRight (inferElabImpl (extendCtx' ctx xR B eLFresh) eR)
            where
              inferRight : InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xR B))
                         → InferElabResult (NamedCtx.debruijn ctx)
              inferRight (failure err) = failure err
              inferRight (success C₂ eRExpr eRDepth eRFresh usageR) with C₁ ≟T C₂
              ... | yes refl = success C₁ (Surface.case' scrutExpr eLExpr eRExpr)
                                       (scrutDepth ⊔ suc eLDepth ⊔ suc eRDepth) eRFresh
                                       (usageScr +ᵘ tailUsage usageL +ᵘ tailUsage usageR)
              ... | no _ = failure "Case branches have different types"
      inferCase (success Unit _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Void _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Int _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Float _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Str _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Buffer _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (_ Once.Type.* _) _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (_ ⇒[ _ ] _) _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (Eff _ _) _ _ _ _) = failure "Expected sum type in case"
      -- TVar removed from Type; now in PolyType (see Once.Type)
      -- OCP-0003: μ-type and ν-type are not sum types
      inferCase (success (μ-type _) _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (ν-type _) _ _ _ _) = failure "Expected sum type in case"
      -- GuardedT removed: productivity follows from IR totality

  -- Integer literal: produce int n
  -- Depth 0 (no nesting), no usage (literals don't use variables)
  inferElabImpl ctx (Raw.RInt n) =
    success Int (Surface.int n) 0 (NamedCtx.freshCounter ctx) zeroUsage

  -- String literal: produce str s
  -- Depth 0 (no nesting), no usage (literals don't use variables)
  inferElabImpl ctx (Raw.RStringLit s) =
    success Str (Surface.str s) 0 (NamedCtx.freshCounter ctx) zeroUsage

  -- Type annotation: just elaborate the inner expression
  inferElabImpl ctx (Raw.RAnnot e _) = inferElabImpl ctx e

  -- Binary operators: infer both operands, check they're Int, produce operator
  -- QTT: Both operands contribute to usage
  inferElabImpl ctx (Raw.RBinOp op e₁ e₂) = inferOp (inferElabImpl ctx e₁)
    where
      bumpFresh' : NamedCtx → ℕ → NamedCtx
      bumpFresh' (mkCtx n Γ Δ _ imps) fresh = mkCtx n Γ Δ fresh imps

      -- Helper to build the result given the inferred operands
      inferOp : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
      inferOp (failure err) = failure err
      inferOp (success Int e₁Expr e₁Depth e₁Fresh usage₁) = inferOp2 (inferElabImpl (bumpFresh' ctx e₁Fresh) e₂)
        where
          inferOp2 : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
          inferOp2 (failure err) = failure err
          inferOp2 (success Int e₂Expr e₂Depth e₂Fresh usage₂) =
            let depth = e₁Depth ⊔ e₂Depth
                usage = usage₁ +ᵘ usage₂
            in if Raw.isArithmeticOp op
               then success Int (mkArithOp op e₁Expr e₂Expr) depth e₂Fresh usage
               else success (Unit Once.Type.+ Unit) (mkCmpOp op e₁Expr e₂Expr) depth e₂Fresh usage
            where
              mkArithOp : Raw.BinOp → Surface.Expr _ Int → Surface.Expr _ Int → Surface.Expr _ Int
              mkArithOp Raw.OpAdd = Surface.add
              mkArithOp Raw.OpSub = Surface.sub
              mkArithOp Raw.OpMul = Surface.mul
              mkArithOp Raw.OpDiv = Surface.div
              mkArithOp Raw.OpMod = Surface.mod'
              mkArithOp _ = Surface.add  -- fallback (shouldn't happen)

              mkCmpOp : Raw.BinOp → Surface.Expr _ Int → Surface.Expr _ Int → Surface.Expr _ (Unit Once.Type.+ Unit)
              mkCmpOp Raw.OpLt = Surface.lt
              mkCmpOp Raw.OpLe = Surface.le
              mkCmpOp Raw.OpGt = Surface.gt
              mkCmpOp Raw.OpGe = Surface.ge
              mkCmpOp Raw.OpEq = Surface.eq
              mkCmpOp Raw.OpNe = Surface.ne
              mkCmpOp _ = Surface.lt  -- fallback (shouldn't happen)
          inferOp2 (success _ _ _ _ _) = failure "Binary operator requires Int operands"
      inferOp (success _ _ _ _ _) = failure "Binary operator requires Int operands"

  -- Unary operators: infer operand, check it's Int, produce negation
  inferElabImpl ctx (Raw.RUnaryOp Raw.OpNeg e) = inferNeg (inferElabImpl ctx e)
    where
      inferNeg : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
      inferNeg (failure err) = failure err
      inferNeg (success Int eExpr eDepth eFresh usage) =
        success Int (Surface.neg eExpr) eDepth eFresh usage
      inferNeg (success _ _ _ _ _) = failure "Negation requires Int operand"

------------------------------------------------------------------------
-- Polymorphic to Ground Extraction
------------------------------------------------------------------------

-- | Extract a PolyInferResult to InferElabResult
-- This is the key extraction step that converts polymorphic results to ground results.
-- Fails if any type variables remain unresolved.
--
-- The implementation extracts the PolyExpr to SExpr, computing
-- the ground context and type. Returns them as part of the result.

-- Helper: handle extraction failure case (when extractExpr returns nothing)
extractInferResultFail : ∀ {n} (Γ : PolyCtx n)
                       → Maybe (∃[ Δ ] InferElabResult {n} Δ)
extractInferResultFail Γ with extractCtx Γ
... | nothing = nothing
... | just Δ = just (Δ , failure "Expression extraction failed")

-- Helper: build result from successful extraction
extractInferResultSuccess : ∀ {n} (Γ' : SCtx n) (ty : Type) (sexpr : Surface.Expr Γ' ty)
                          (depth fresh : ℕ) (usage : PolyUsage n)
                          → ∃[ Δ ] InferElabResult {n} Δ
extractInferResultSuccess Γ' ty sexpr depth fresh usage = Γ' , success ty sexpr depth fresh usage

extractInferResult : ∀ {n} {Γ : PolyCtx n}
                   → PolyInferResult Γ
                   → Maybe (∃[ Δ ] InferElabResult {n} Δ)
extractInferResult {n} {Γ} (failure err) with extractCtx Γ
... | nothing = nothing
... | just Δ = just (Δ , failure err)
extractInferResult {n} {Γ} (success A pexpr depth fresh usage) with extractExpr pexpr
... | nothing = extractInferResultFail Γ
... | just (Γ' , ty , sexpr) = just (extractInferResultSuccess Γ' ty sexpr depth fresh usage)

------------------------------------------------------------------------
-- Polymorphic Type Inference (Phase 4)
------------------------------------------------------------------------

-- | Helper: find de Bruijn index and get the quantity from polymorphic context
findPolyVarUsage : (ctx : PolyNamedCtx) → String → Maybe (Fin (PolyNamedCtx.size ctx) × Quantity)
findPolyVarUsage ctx x with findPolyVarIndex ctx x
... | nothing = nothing
... | just i = just (i , lookupPolyQuantity (PolyNamedCtx.polyCtx ctx) i)

-- | Polymorphic zero usage
pzeroUsage : ∀ {n} → PolyUsage n
pzeroUsage = zeroUsage

-- | Polymorphic single use
psingleUse : ∀ {n} → Fin n → Quantity → PolyUsage n
psingleUse = singleUse

-- | Polymorphic tail usage
ptailUsage : ∀ {n} → PolyUsage (suc n) → PolyUsage n
ptailUsage = tailUsage

-- | Coerce PolyExpr to a different PolyType (when they're equal)
-- Used after matchesPolyType succeeds to adjust the expression's type index.
coercePolyExpr : ∀ {n} {Γ : PolyCtx n} {A} → PolyExpr Γ A → (B : PolyType) → ℕ → ℕ → PolyUsage n → PolyCheckResult Γ B
coercePolyExpr {A = A} e B d f u with A ≟PT B
... | yes refl = success e d f u
... | no _ = failure "Type coercion failed"

------------------------------------------------------------------------
-- Substitution-based Coercion
------------------------------------------------------------------------

-- | Apply substitution to expression, preserving ground context
-- When the context is ground, substitution doesn't change it.
applySubstExprGround : ∀ {n} {Γ : PolyCtx n} {A} (σ : InferSubst)
                     → GroundCtx Γ
                     → PolyExpr Γ A
                     → PolyExpr Γ (applySubst σ A)
applySubstExprGround {Γ = Γ} {A = A} σ gΓ e =
  subst (λ ctx → PolyExpr ctx (applySubst σ A)) (applySubstCtx-ground σ Γ gΓ) (applySubstExpr σ e)

-- | Coerce expression using substitution when target type is ground
-- When target type A is ground, applySubst σ A ≡ A, so we can coerce.
coerceWithSubstGround : ∀ {n} {Γ : PolyCtx n} {A A'} (σ : InferSubst)
                      → GroundCtx Γ
                      → Ground A  -- Target type must be ground
                      → PolyExpr Γ A'
                      → Maybe (PolyExpr Γ A)
coerceWithSubstGround {Γ = Γ} {A = A} {A' = A'} σ gΓ gA e with applySubst σ A' ≟PT A
... | yes eq =
      let e' = applySubstExprGround σ gΓ e  -- : PolyExpr Γ (applySubst σ A')
      in just (subst (PolyExpr Γ) eq e')
... | no _ = nothing

-- | Coerce PolyExpr to expected argument type for application
-- Uses substitution when types match and target is ground.
-- Falls back to definitional equality check.
coercePolyArgWithSubst : ∀ {n} {Γ : PolyCtx n} {A A'}
                       → GroundCtx Γ
                       → InferSubst
                       → PolyExpr Γ A'
                       → Maybe (PolyExpr Γ A)
coercePolyArgWithSubst {A = A} {A' = A'} gΓ σ e with A ≟PT A'
... | yes refl = just e  -- Types definitionally equal
... | no _ with Once.Type.ground? A
...   | yes gA = coerceWithSubstGround σ gΓ gA e  -- Target is ground, use substitution
...   | no _ = nothing  -- Target has TVars, cannot coerce safely

-- | Coerce PolyExpr when types are definitionally equal
-- For types that differ only in TVar naming, this relies on the coercion
-- being eliminated by extraction (when all TVars are resolved).
--
-- This function:
-- 1. Returns the expression unchanged when types are definitionally equal
-- 2. For TVar mismatches, relies on the fact that:
--    - matchesPolyType only succeeds when types are unifiable
--    - Extraction requires all types to be ground (no TVars)
--    - Therefore, TVar mismatches that reach extraction would fail anyway
--
-- TODO: Properly propagate substitutions through inference to eliminate this
coercePolyArg : ∀ {n} {Γ : PolyCtx n} {A A'} → PolyExpr Γ A' → PolyExpr Γ A
coercePolyArg {Γ = Γ} {A = A} {A' = A'} e with A ≟PT A'
... | yes refl = e
... | no _ = coercePolyArgTVar e
  where
    -- Postulate for TVar mismatch case only
    -- This is sound because:
    -- 1. We only reach here when matchesPolyType A A' succeeded
    -- 2. At extraction time, both types must be ground (no TVars)
    -- 3. Ground types that match via matchesPolyType are definitionally equal
    postulate coercePolyArgTVar : PolyExpr Γ A' → PolyExpr Γ A

{-# TERMINATING #-}
mutual
  -- | Polymorphic type checking mode: verify PolyExpr has expected PolyType
  polyCheckImpl : (ctx : PolyNamedCtx) → RawExpr → (A : PolyType) → PolyCheckResult (PolyNamedCtx.polyCtx ctx) A

  -- Lambda with function type: check body against result type
  -- Note: Use Many for context (matches plam signature), check usage against q
  polyCheckImpl ctx (Raw.RLam x body) (A P⇒[ q ] B) with polyCheckImpl (extendPolyNamedCtxPolyQ ctx x A Many) body B
  ... | failure err = failure err
  ... | success bodyExpr depth fresh' usage' =
          let paramUsage = lookupUsage usage' zero
          in if paramUsage ≤q q
             then success (plam q bodyExpr) (suc depth) fresh' (ptailUsage usage')
             else failure ("Parameter '" ++ x ++ "' used with quantity " ++ showQuantity paramUsage ++
                          " but declared with quantity " ++ showQuantity q)

  -- Lambda with non-function type: error
  polyCheckImpl ctx (Raw.RLam _ _) ty =
    failure "Lambda requires function type"

  -- Application in checking mode: use expected type to resolve TVars
  -- When checking (f arg) against expected type B:
  -- 1. Infer type of f to get (A → B') or similar
  -- 2. Unify B' with B to resolve TVars (capturing substitution)
  -- 3. Apply substitution to A and check arg against the resolved A
  polyCheckImpl ctx (Raw.RApp fun arg) expectedType with polyInferImpl ctx fun
  ... | failure err = failure err
  ... | success (A P⇒[ q ] B) funExpr funDepth funFresh usageFun =
        -- Unify inferred result type B with expected type to capture TVar substitutions
        checkArg (matchWithSubst expectedType B emptyInferSubst)
    where
      checkArg : Maybe (PolyType × InferSubst) → PolyCheckResult (PolyNamedCtx.polyCtx ctx) expectedType
      checkArg nothing = failure ("Result type mismatch: expected " ++ showPolyType expectedType ++
                                  " but function returns " ++ showPolyType B)
      checkArg (just (_ , σ)) =
        -- Apply substitution to domain type to resolve TVars
        let resolvedA = applySubst σ A
        in checkArgWithResolvedType resolvedA
        where
          checkArgWithResolvedType : PolyType → PolyCheckResult (PolyNamedCtx.polyCtx ctx) expectedType
          checkArgWithResolvedType domType with polyCheckImpl (setPolyFresh ctx funFresh) arg domType
          ... | failure err = failure err
          ... | success argExpr argDepth argFresh usageArg =
                -- Coerce the application result from B to expectedType
                success (coercePolyArg (papp funExpr (coercePolyArg argExpr))) (funDepth ⊔ argDepth) argFresh (usageFun +ᵘ usageArg)
  -- Effect application: eff arg returns B (the effect's result type)
  ... | success (PEff A B) funExpr funDepth funFresh usageFun =
        checkEffArg (matchWithSubst expectedType B emptyInferSubst)
    where
      checkEffArg : Maybe (PolyType × InferSubst) → PolyCheckResult (PolyNamedCtx.polyCtx ctx) expectedType
      checkEffArg nothing = failure ("Effect result type mismatch: expected " ++ showPolyType expectedType ++
                                     " but effect returns " ++ showPolyType B)
      checkEffArg (just (_ , σ)) =
        let resolvedA = applySubst σ A
        in checkArgWithResolvedType resolvedA
        where
          checkArgWithResolvedType : PolyType → PolyCheckResult (PolyNamedCtx.polyCtx ctx) expectedType
          checkArgWithResolvedType domType with polyCheckImpl (setPolyFresh ctx funFresh) arg domType
          ... | failure err = failure err
          ... | success argExpr argDepth argFresh usageArg =
                -- Coerce the application result from B to expectedType
                success (coercePolyArg (peffApp funExpr (coercePolyArg argExpr))) (funDepth ⊔ argDepth) argFresh (usageFun +ᵘ usageArg)
  ... | success funTy _ _ _ _ = failure ("Expected function type in application, got " ++ showPolyType funTy)

  -- Default: fall back to inference and check matching
  polyCheckImpl ctx expr expectedType with polyInferImpl ctx expr
  ... | failure err = failure err
  ... | success inferredType pexpr depth fresh' usage' with matchesPolyType expectedType inferredType
  ...   | just _ = coercePolyExpr pexpr expectedType depth fresh' usage'
  ...   | nothing = failure ("Type mismatch: expected " ++ showPolyType expectedType ++
                             " but got " ++ showPolyType inferredType)

  -- | Polymorphic type inference mode: compute the PolyType
  polyInferImpl : (ctx : PolyNamedCtx) → RawExpr → PolyInferResult (PolyNamedCtx.polyCtx ctx)

  -- Variable: look up in context
  polyInferImpl ctx (Raw.RVar x) with lookupPolyVar ctx x
  ... | nothing = failure ("Unbound variable: " ++ x)
  ... | just (A , pe , fresh') with findPolyVarUsage ctx x
  ...   | just (i , q) = success A pe 0 fresh' (psingleUse i q)
  ...   | nothing = success A pe 0 fresh' pzeroUsage  -- Built-in

  -- Qualified variable
  polyInferImpl ctx (Raw.RQualified name alias) with lookupPolyVar ctx (alias ++ "." ++ name)
  ... | nothing = failure ("Unbound qualified variable: " ++ name ++ "@" ++ alias)
  ... | just (A , pe , fresh') = success A pe 0 fresh' pzeroUsage

  -- Lambda without type annotation: not supported in inference mode
  polyInferImpl ctx (Raw.RLam x body) =
    failure ("Lambda without type annotation not supported in inference mode.\n" ++
             "Add a type annotation or use a type-annotated expression.")

  -- Application
  polyInferImpl ctx (Raw.RApp fun arg) with polyInferImpl ctx fun
  ... | failure err = failure err
  ... | success (A P⇒[ q ] B) funExpr funDepth funFresh usageFun =
        inferPolyArg (polyInferImpl (setPolyFresh ctx funFresh) arg)
    where
      inferPolyArg : PolyInferResult (PolyNamedCtx.polyCtx ctx) → PolyInferResult (PolyNamedCtx.polyCtx ctx)
      inferPolyArg (failure err) = failure err
      inferPolyArg (success A' argExpr argDepth argFresh usageArg) with matchesPolyType A A'
      ... | just _ = success B (papp funExpr (coercePolyArg argExpr)) (funDepth ⊔ argDepth) argFresh (usageFun +ᵘ usageArg)
      ... | nothing = failure ("Type mismatch in application: expected " ++ showPolyType A ++
                               " but got " ++ showPolyType A')
  ... | success (PEff A B) funExpr funDepth funFresh usageFun =
        inferPolyArgEff (polyInferImpl (setPolyFresh ctx funFresh) arg)
    where
      inferPolyArgEff : PolyInferResult (PolyNamedCtx.polyCtx ctx) → PolyInferResult (PolyNamedCtx.polyCtx ctx)
      inferPolyArgEff (failure err) = failure err
      inferPolyArgEff (success A' argExpr argDepth argFresh usageArg) with matchesPolyType A A'
      ... | just _ = success B (peffApp funExpr (coercePolyArg argExpr)) (funDepth ⊔ argDepth) argFresh (usageFun +ᵘ usageArg)
      ... | nothing = failure ("Type mismatch in effect application: expected " ++ showPolyType A ++
                               " but got " ++ showPolyType A')
  ... | success PUnit _ _ _ _ = failure "Expected function type in application"
  ... | success PVoid _ _ _ _ = failure "Expected function type in application"
  ... | success PInt _ _ _ _ = failure "Expected function type in application"
  ... | success PFloat _ _ _ _ = failure "Expected function type in application"
  ... | success PStr _ _ _ _ = failure "Expected function type in application"
  ... | success PBuffer _ _ _ _ = failure "Expected function type in application"
  ... | success (_ P* _) _ _ _ _ = failure "Expected function type in application"
  ... | success (_ P+ _) _ _ _ _ = failure "Expected function type in application"
  ... | success (Pμ-type _) _ _ _ _ = failure "Expected function type in application"
  ... | success (Pν-type _) _ _ _ _ = failure "Expected function type in application"
  ... | success (TVar _) _ _ _ _ = failure "Cannot apply type variable (need type annotation)"

  -- Pair
  polyInferImpl ctx (Raw.RPair a b) with polyInferImpl ctx a
  ... | failure err = failure err
  ... | success A aExpr aDepth aFresh usage1 with polyInferImpl (setPolyFresh ctx aFresh) b
  ...   | failure err = failure err
  ...   | success B bExpr bDepth bFresh usage2 =
        success (A P* B) (ppair aExpr bExpr) (aDepth ⊔ bDepth) bFresh (usage1 +ᵘ usage2)

  -- Unit
  polyInferImpl ctx Raw.RUnit = success PUnit punit 0 (PolyNamedCtx.freshCounter ctx) pzeroUsage

  -- Let binding
  polyInferImpl ctx (Raw.RLet x e₁ e₂) with polyInferImpl ctx e₁
  ... | failure err = failure err
  ... | success A e₁Expr e₁Depth e₁Fresh usage1 with polyInferImpl (extendPolyNamedCtxPoly (setPolyFresh ctx e₁Fresh) x A) e₂
  ...   | failure err = failure err
  ...   | success B e₂Expr e₂Depth e₂Fresh usage2 =
        success B (plet' e₁Expr e₂Expr) (e₁Depth ⊔ suc e₂Depth) e₂Fresh (usage1 +ᵘ ptailUsage usage2)

  -- Case analysis
  polyInferImpl ctx (Raw.RDestruct scrut xL eL xR eR) with polyInferImpl ctx scrut
  ... | failure err = failure err
  ... | success (A P+ B) scrutExpr scrutDepth scrutFresh usageScr =
        inferPolyLeft (polyInferImpl (extendPolyNamedCtxPoly (setPolyFresh ctx scrutFresh) xL A) eL)
    where
      inferPolyLeft : PolyInferResult _ → PolyInferResult (PolyNamedCtx.polyCtx ctx)
      inferPolyLeft (failure err) = failure err
      inferPolyLeft (success C₁ eLExpr eLDepth eLFresh usageL) =
        inferPolyRight (polyInferImpl (extendPolyNamedCtxPoly (setPolyFresh ctx eLFresh) xR B) eR)
        where
          inferPolyRight : PolyInferResult _ → PolyInferResult (PolyNamedCtx.polyCtx ctx)
          inferPolyRight (failure err) = failure err
          inferPolyRight (success C₂ eRExpr eRDepth eRFresh usageR) with matchesPolyType C₁ C₂
          ... | just C = success C₁ (pcase' scrutExpr eLExpr (coercePolyArg eRExpr))
                                    (scrutDepth ⊔ suc eLDepth ⊔ suc eRDepth) eRFresh
                                    (usageScr +ᵘ ptailUsage usageL +ᵘ ptailUsage usageR)
          ... | nothing = failure "Case branches have different types"
  ... | success PUnit _ _ _ _ = failure "Expected sum type in case"
  ... | success PVoid _ _ _ _ = failure "Expected sum type in case"
  ... | success PInt _ _ _ _ = failure "Expected sum type in case"
  ... | success PFloat _ _ _ _ = failure "Expected sum type in case"
  ... | success PStr _ _ _ _ = failure "Expected sum type in case"
  ... | success PBuffer _ _ _ _ = failure "Expected sum type in case"
  ... | success (_ P* _) _ _ _ _ = failure "Expected sum type in case"
  ... | success (_ P⇒[ _ ] _) _ _ _ _ = failure "Expected sum type in case"
  ... | success (PEff _ _) _ _ _ _ = failure "Expected sum type in case"
  ... | success (Pμ-type _) _ _ _ _ = failure "Expected sum type in case"
  ... | success (Pν-type _) _ _ _ _ = failure "Expected sum type in case"
  ... | success (TVar _) _ _ _ _ = failure "Cannot case on type variable"

  -- Integer literal
  polyInferImpl ctx (Raw.RInt n) =
    success PInt (pint n) 0 (PolyNamedCtx.freshCounter ctx) pzeroUsage

  -- String literal
  polyInferImpl ctx (Raw.RStringLit s) =
    success PStr (pstr s) 0 (PolyNamedCtx.freshCounter ctx) pzeroUsage

  -- Type annotation
  polyInferImpl ctx (Raw.RAnnot e _) = polyInferImpl ctx e

  -- Binary operators
  polyInferImpl ctx (Raw.RBinOp op e₁ e₂) with polyInferImpl ctx e₁
  ... | failure err = failure err
  ... | success PInt e₁Expr e₁Depth e₁Fresh usage₁ = checkOp2 (polyInferImpl (setPolyFresh ctx e₁Fresh) e₂)
    where
      checkOp2 : PolyInferResult (PolyNamedCtx.polyCtx ctx) → PolyInferResult (PolyNamedCtx.polyCtx ctx)
      checkOp2 (failure err) = failure err
      checkOp2 (success PInt e₂Expr e₂Depth e₂Fresh usage₂) =
          let depth = e₁Depth ⊔ e₂Depth
              usage = usage₁ +ᵘ usage₂
          in if Raw.isArithmeticOp op
             then success PInt (mkPolyArithOp op e₁Expr e₂Expr) depth e₂Fresh usage
             else success (PUnit P+ PUnit) (mkPolyCmpOp op e₁Expr e₂Expr) depth e₂Fresh usage
          where
            mkPolyArithOp : Raw.BinOp → PolyExpr _ PInt → PolyExpr _ PInt → PolyExpr _ PInt
            mkPolyArithOp Raw.OpAdd = padd
            mkPolyArithOp Raw.OpSub = psub
            mkPolyArithOp Raw.OpMul = pmul
            mkPolyArithOp Raw.OpDiv = pdiv
            mkPolyArithOp Raw.OpMod = pmod'
            mkPolyArithOp _ = padd  -- fallback

            mkPolyCmpOp : Raw.BinOp → PolyExpr _ PInt → PolyExpr _ PInt → PolyExpr _ (PUnit P+ PUnit)
            mkPolyCmpOp Raw.OpLt = plt
            mkPolyCmpOp Raw.OpLe = ple
            mkPolyCmpOp Raw.OpGt = pgt
            mkPolyCmpOp Raw.OpGe = pge
            mkPolyCmpOp Raw.OpEq = peq
            mkPolyCmpOp Raw.OpNe = pne
            mkPolyCmpOp _ = plt  -- fallback
      checkOp2 (success PUnit _ _ _ _) = failure "Binary operator requires Int operands"
      checkOp2 (success PVoid _ _ _ _) = failure "Binary operator requires Int operands"
      checkOp2 (success PFloat _ _ _ _) = failure "Binary operator requires Int operands"
      checkOp2 (success PStr _ _ _ _) = failure "Binary operator requires Int operands"
      checkOp2 (success PBuffer _ _ _ _) = failure "Binary operator requires Int operands"
      checkOp2 (success (_ P* _) _ _ _ _) = failure "Binary operator requires Int operands"
      checkOp2 (success (_ P+ _) _ _ _ _) = failure "Binary operator requires Int operands"
      checkOp2 (success (_ P⇒[ _ ] _) _ _ _ _) = failure "Binary operator requires Int operands"
      checkOp2 (success (PEff _ _) _ _ _ _) = failure "Binary operator requires Int operands"
      checkOp2 (success (Pμ-type _) _ _ _ _) = failure "Binary operator requires Int operands"
      checkOp2 (success (Pν-type _) _ _ _ _) = failure "Binary operator requires Int operands"
      checkOp2 (success (TVar _) _ _ _ _) = failure "Binary operator requires Int operands"
  ... | success PUnit _ _ _ _ = failure "Binary operator requires Int operands"
  ... | success PVoid _ _ _ _ = failure "Binary operator requires Int operands"
  ... | success PFloat _ _ _ _ = failure "Binary operator requires Int operands"
  ... | success PStr _ _ _ _ = failure "Binary operator requires Int operands"
  ... | success PBuffer _ _ _ _ = failure "Binary operator requires Int operands"
  ... | success (_ P* _) _ _ _ _ = failure "Binary operator requires Int operands"
  ... | success (_ P+ _) _ _ _ _ = failure "Binary operator requires Int operands"
  ... | success (_ P⇒[ _ ] _) _ _ _ _ = failure "Binary operator requires Int operands"
  ... | success (PEff _ _) _ _ _ _ = failure "Binary operator requires Int operands"
  ... | success (Pμ-type _) _ _ _ _ = failure "Binary operator requires Int operands"
  ... | success (Pν-type _) _ _ _ _ = failure "Binary operator requires Int operands"
  ... | success (TVar _) _ _ _ _ = failure "Binary operator requires Int operands"

  -- Unary operators
  polyInferImpl ctx (Raw.RUnaryOp Raw.OpNeg e) with polyInferImpl ctx e
  ... | failure err = failure err
  ... | success PInt eExpr eDepth eFresh usage =
        success PInt (pneg eExpr) eDepth eFresh usage
  ... | success PUnit _ _ _ _ = failure "Negation requires Int operand"
  ... | success PVoid _ _ _ _ = failure "Negation requires Int operand"
  ... | success PFloat _ _ _ _ = failure "Negation requires Int operand"
  ... | success PStr _ _ _ _ = failure "Negation requires Int operand"
  ... | success PBuffer _ _ _ _ = failure "Negation requires Int operand"
  ... | success (_ P* _) _ _ _ _ = failure "Negation requires Int operand"
  ... | success (_ P+ _) _ _ _ _ = failure "Negation requires Int operand"
  ... | success (_ P⇒[ _ ] _) _ _ _ _ = failure "Negation requires Int operand"
  ... | success (PEff _ _) _ _ _ _ = failure "Negation requires Int operand"
  ... | success (Pμ-type _) _ _ _ _ = failure "Negation requires Int operand"
  ... | success (Pν-type _) _ _ _ _ = failure "Negation requires Int operand"
  ... | success (TVar _) _ _ _ _ = failure "Negation requires Int operand"

------------------------------------------------------------------------
-- Context Embedding and Roundtrip Lemmas
------------------------------------------------------------------------

-- | Embed a ground context as a polymorphic context
embedSCtx : ∀ {n} → SCtx n → PolyCtx n
embedSCtx S∅ = P∅
embedSCtx (Δ S, A ^ q) = Poly._P,_^_ (embedSCtx Δ) (embed A) q

-- | Embedded contexts are always ground
embedSCtx-ground : ∀ {n} (Δ : SCtx n) → GroundCtx (embedSCtx Δ)
embedSCtx-ground S∅ = tt
embedSCtx-ground (Δ S, A ^ q) = embedSCtx-ground Δ , embed-ground A

-- | Extracting an embedded context gives back the original
extractGroundCtx-embedSCtx : ∀ {n} (Δ : SCtx n)
                           → extractGroundCtx (embedSCtx Δ) (embedSCtx-ground Δ) ≡ Δ
extractGroundCtx-embedSCtx S∅ = refl
extractGroundCtx-embedSCtx (Δ S, A ^ q)
  rewrite extractGroundCtx-embedSCtx Δ | extractGround-embed A = refl

-- | Extract inference result to a specific target context
-- Uses the roundtrip lemma: extracting an embedded context gives back the original
extractInferResultTo : ∀ {n} (Δ : SCtx n)
                     → PolyInferResult (embedSCtx Δ)
                     → Maybe (InferElabResult Δ)
extractInferResultTo Δ (failure err) = just (failure err)
extractInferResultTo Δ (success A pexpr depth fresh usage)
  with Once.Type.ground? A | Poly.groundExpr? pexpr
... | yes gA | yes gexpr =
      let gΓ = embedSCtx-ground Δ  -- Embedded contexts are always ground
      in just (success (extractGround A gA)
                       (subst (λ ctx → Surface.Expr ctx (extractGround A gA))
                              (extractGroundCtx-embedSCtx Δ)
                              (Poly.extractGroundExpr pexpr gΓ gA gexpr))
                       depth fresh usage)
... | _ | _ = nothing

-- | Convert NamedCtx to PolyNamedCtx
-- Embeds all ground types as PolyTypes
namedToPolyCtx : NamedCtx → PolyNamedCtx
namedToPolyCtx (mkCtx n Γ Δ fresh imps) = mkPolyCtx n Γ (embedSCtx Δ) fresh (embedImports imps)

------------------------------------------------------------------------
-- Depth-Checked Inference (Public Interface)
------------------------------------------------------------------------

-- | Type inference with depth limit enforcement
--
-- This is the public interface that enforces the depth ≤ 7 constraint.
-- Programs exceeding this limit are rejected with a clear error message.
--
-- RATIONALE: The exchange functions (used for context manipulation) are
-- proven correct only up to exchange₇. See docs/formal/full-verification-compiler-stack.md
--
-- Implementation uses two-phase approach:
-- 1. Polymorphic inference (builds PolyExpr with potential TVars)
-- 2. Extraction (converts to SExpr, fails if TVars remain)
--
-- This enables polymorphic builtins (id, fst, snd, etc.) to unify properly
-- during type inference before committing to ground types.
--
inferElab : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)
inferElab ctx rawExpr =
  -- First try polymorphic inference + extraction
  let polyCtx = namedToPolyCtx ctx
  in tryPolyInfer (polyInferImpl polyCtx rawExpr)
  where
    checkDepth : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
    checkDepth (failure err) = failure err
    checkDepth (success ty expr depth fresh usage) with depth ≤? 7
    ... | yes _ = success ty expr depth fresh usage
    ... | no _ = failure ("Expression nesting depth exceeds verified limit.\n" ++
                         "  Depth encountered: " ++ showℕ depth ++ "\n" ++
                         "  Proven depth limit: 7\n" ++
                         "  Please refactor to reduce nesting of λ/case/let expressions.")

    tryPolyInfer : PolyInferResult (PolyNamedCtx.polyCtx (namedToPolyCtx ctx))
                 → InferElabResult (NamedCtx.debruijn ctx)
    tryPolyInfer polyResult with extractInferResultTo (NamedCtx.debruijn ctx) polyResult
    ... | nothing = failure "Internal error: extraction returned nothing"
    ... | just result = checkDepth result

------------------------------------------------------------------------
-- Top-level Compilation
------------------------------------------------------------------------

-- | Extract checking result to a specific target context and type
-- Uses roundtrip lemmas: extracting embedded context/type gives back the original
extractCheckResultTo : ∀ {n} (Δ : SCtx n) (A' : Type)
                     → PolyCheckResult (embedSCtx Δ) (embed A')
                     → Maybe (CheckElabResult Δ A')
extractCheckResultTo Δ A' (failure err) = just (failure err)
extractCheckResultTo Δ A' (success pexpr depth fresh usage)
  with Poly.groundExpr? pexpr
... | yes gexpr =
      let gΓ = embedSCtx-ground Δ  -- Embedded contexts are always ground
          gA = embed-ground A'      -- Embedded types are always ground
      in just (success (subst₂ Surface.Expr
                               (extractGroundCtx-embedSCtx Δ)
                               (extractGround-embed A')
                               (Poly.extractGroundExpr pexpr gΓ gA gexpr))
                       depth fresh usage)
  where
    -- Binary subst for expressions indexed by context and type
    subst₂ : ∀ {a b c} {A : Set a} {B : Set b} (C : A → B → Set c)
           → {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ y₂ → C x₁ y₁ → C x₂ y₂
    subst₂ C refl refl z = z
... | no _ = nothing

-- | Checking mode with depth limit (helper for top-level compilation)
-- Uses polymorphic checking with extraction for proper TVar handling.
checkElab : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A
checkElab ctx expr ty =
  let polyCtx = namedToPolyCtx ctx
      polyTy = embed ty
  in tryPolyCheck (polyCheckImpl polyCtx expr polyTy)
  where
    checkDepth : CheckElabResult (NamedCtx.debruijn ctx) ty → CheckElabResult (NamedCtx.debruijn ctx) ty
    checkDepth (failure err) = failure err
    checkDepth (success expr' depth fresh usage) with depth ≤? 7
    ... | yes _ = success expr' depth fresh usage
    ... | no _ = failure ("Expression nesting depth exceeds verified limit.\n" ++
                         "  Depth encountered: " ++ showℕ depth ++ "\n" ++
                         "  Proven depth limit: 7\n" ++
                         "  Please refactor to reduce nesting of λ/case/let expressions.")

    tryPolyCheck : PolyCheckResult (PolyNamedCtx.polyCtx (namedToPolyCtx ctx)) (embed ty)
                 → CheckElabResult (NamedCtx.debruijn ctx) ty
    tryPolyCheck polyResult with extractCheckResultTo (NamedCtx.debruijn ctx) ty polyResult
    ... | nothing = failure "Internal error: extraction returned nothing"
    ... | just result = checkDepth result

-- | Compile with type signature (PRIMARY INTERFACE - uses checking mode)
--
-- This is the recommended way to compile Once programs, as all top-level
-- declarations should have type signatures (Once philosophy: explicit > implicit).
--
-- Uses bidirectional checking mode for better error messages and polymorphism.
compileExprTyped : RawExpr → (A : Type) → Maybe (IR Unit A)
compileExprTyped e A with checkElab emptyCtx e A
... | failure _ = nothing
... | success se _ _ _ = just (elaborate se)

-- | Compile without type signature (FALLBACK - uses inference mode)
--
-- This is provided for compatibility, but users should prefer compileExprTyped
-- with explicit type signatures. Inference-only mode has limitations:
-- - Cannot handle all polymorphic cases
-- - Less helpful error messages
-- - May fail where checking succeeds
--
-- Once philosophy: Types guide, signatures required.
compileExpr : RawExpr → Maybe (∃[ A ] IR Unit A)
compileExpr e with inferElab emptyCtx e
... | failure _ = nothing
... | success A se _ _ _ = just (A , elaborate se)