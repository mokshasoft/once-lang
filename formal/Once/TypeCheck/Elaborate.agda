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
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; inspect; [_])
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
matchesPolyType (A₁ P⇒[ q₁ ] B₁) (A₂ P⇒[ q₂ ] B₂) with q₁ ≟q q₂ | matchesPolyType A₁ A₂ | matchesPolyType B₁ B₂
... | yes refl | just A | just B = just (A P⇒[ q₁ ] B)  -- Quantities must match
... | _ | _ | _ = nothing
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

-- | Ground types that match via matchesPolyType are definitionally equal
-- This is the key lemma for eliminating the coercePolyArg postulate.
--
-- Proof: Ground types have no TVars, so the TVar cases in matchesPolyType
-- are never reached. The remaining cases all require structural equality.
matchesPolyType-ground-eq : (A B : PolyType) → Ground A → Ground B
                          → (C : PolyType) → matchesPolyType A B ≡ just C
                          → A ≡ B
matchesPolyType-ground-eq PUnit PUnit _ _ .PUnit refl = refl
matchesPolyType-ground-eq PVoid PVoid _ _ .PVoid refl = refl
matchesPolyType-ground-eq PInt PInt _ _ .PInt refl = refl
matchesPolyType-ground-eq PFloat PFloat _ _ .PFloat refl = refl
matchesPolyType-ground-eq PStr PStr _ _ .PStr refl = refl
matchesPolyType-ground-eq PBuffer PBuffer _ _ .PBuffer refl = refl
matchesPolyType-ground-eq (A₁ P* B₁) (A₂ P* B₂) (gA₁ , gB₁) (gA₂ , gB₂) C eq
  with matchesPolyType A₁ A₂ | matchesPolyType B₁ B₂ | inspect (matchesPolyType A₁) A₂ | inspect (matchesPolyType B₁) B₂
... | just A | just B | [ eqA ] | [ eqB ] with eq
...   | refl = cong₂ _P*_ (matchesPolyType-ground-eq A₁ A₂ gA₁ gA₂ A eqA)
                          (matchesPolyType-ground-eq B₁ B₂ gB₁ gB₂ B eqB)
matchesPolyType-ground-eq (A₁ P* B₁) (A₂ P* B₂) _ _ C () | nothing | nothing | _ | _
matchesPolyType-ground-eq (A₁ P* B₁) (A₂ P* B₂) _ _ C () | nothing | just _ | _ | _
matchesPolyType-ground-eq (A₁ P* B₁) (A₂ P* B₂) _ _ C () | just _ | nothing | _ | _
matchesPolyType-ground-eq (A₁ P+ B₁) (A₂ P+ B₂) (gA₁ , gB₁) (gA₂ , gB₂) C eq
  with matchesPolyType A₁ A₂ | matchesPolyType B₁ B₂ | inspect (matchesPolyType A₁) A₂ | inspect (matchesPolyType B₁) B₂
... | just A | just B | [ eqA ] | [ eqB ] with eq
...   | refl = cong₂ _P+_ (matchesPolyType-ground-eq A₁ A₂ gA₁ gA₂ A eqA)
                          (matchesPolyType-ground-eq B₁ B₂ gB₁ gB₂ B eqB)
matchesPolyType-ground-eq (A₁ P+ B₁) (A₂ P+ B₂) _ _ C () | nothing | nothing | _ | _
matchesPolyType-ground-eq (A₁ P+ B₁) (A₂ P+ B₂) _ _ C () | nothing | just _ | _ | _
matchesPolyType-ground-eq (A₁ P+ B₁) (A₂ P+ B₂) _ _ C () | just _ | nothing | _ | _
matchesPolyType-ground-eq (A₁ P⇒[ q₁ ] B₁) (A₂ P⇒[ q₂ ] B₂) (gA₁ , gB₁) (gA₂ , gB₂) C eq
  with q₁ ≟q q₂ | matchesPolyType A₁ A₂ | matchesPolyType B₁ B₂ | inspect (matchesPolyType A₁) A₂ | inspect (matchesPolyType B₁) B₂
... | yes refl | just A | just B | [ eqA ] | [ eqB ] with eq
...   | refl = cong₂ (λ a b → a P⇒[ q₁ ] b)
                     (matchesPolyType-ground-eq A₁ A₂ gA₁ gA₂ A eqA)
                     (matchesPolyType-ground-eq B₁ B₂ gB₁ gB₂ B eqB)
matchesPolyType-ground-eq (A₁ P⇒[ _ ] B₁) (A₂ P⇒[ _ ] B₂) _ _ C () | no _ | _ | _ | _ | _
matchesPolyType-ground-eq (A₁ P⇒[ q ] B₁) (A₂ P⇒[ .q ] B₂) _ _ C () | yes refl | nothing | nothing | _ | _
matchesPolyType-ground-eq (A₁ P⇒[ q ] B₁) (A₂ P⇒[ .q ] B₂) _ _ C () | yes refl | nothing | just _ | _ | _
matchesPolyType-ground-eq (A₁ P⇒[ q ] B₁) (A₂ P⇒[ .q ] B₂) _ _ C () | yes refl | just _ | nothing | _ | _
matchesPolyType-ground-eq (PEff A₁ B₁) (PEff A₂ B₂) (gA₁ , gB₁) (gA₂ , gB₂) C eq
  with matchesPolyType A₁ A₂ | matchesPolyType B₁ B₂ | inspect (matchesPolyType A₁) A₂ | inspect (matchesPolyType B₁) B₂
... | just A | just B | [ eqA ] | [ eqB ] with eq
...   | refl = cong₂ PEff (matchesPolyType-ground-eq A₁ A₂ gA₁ gA₂ A eqA)
                          (matchesPolyType-ground-eq B₁ B₂ gB₁ gB₂ B eqB)
matchesPolyType-ground-eq (PEff A₁ B₁) (PEff A₂ B₂) _ _ C () | nothing | nothing | _ | _
matchesPolyType-ground-eq (PEff A₁ B₁) (PEff A₂ B₂) _ _ C () | nothing | just _ | _ | _
matchesPolyType-ground-eq (PEff A₁ B₁) (PEff A₂ B₂) _ _ C () | just _ | nothing | _ | _
matchesPolyType-ground-eq (Pμ-type F₁) (Pμ-type F₂) gF₁ gF₂ C eq with F₁ ≟PF F₂
... | yes refl with eq
...   | refl = refl
matchesPolyType-ground-eq (Pμ-type F₁) (Pμ-type F₂) _ _ C eq | no _ with eq
... | ()
matchesPolyType-ground-eq (Pν-type F₁) (Pν-type F₂) gF₁ gF₂ C eq with F₁ ≟PF F₂
... | yes refl with eq
...   | refl = refl
matchesPolyType-ground-eq (Pν-type F₁) (Pν-type F₂) _ _ C eq | no _ with eq
... | ()
-- Remaining cases are structural mismatches that can't succeed
matchesPolyType-ground-eq PUnit (A P* B) _ _ C ()
matchesPolyType-ground-eq PUnit (A P+ B) _ _ C ()
matchesPolyType-ground-eq PUnit (A P⇒[ _ ] B) _ _ C ()
matchesPolyType-ground-eq PUnit (PEff A B) _ _ C ()
matchesPolyType-ground-eq PUnit (Pμ-type _) _ _ C ()
matchesPolyType-ground-eq PUnit (Pν-type _) _ _ C ()
matchesPolyType-ground-eq PVoid (A P* B) _ _ C ()
matchesPolyType-ground-eq PVoid (A P+ B) _ _ C ()
matchesPolyType-ground-eq PVoid (A P⇒[ _ ] B) _ _ C ()
matchesPolyType-ground-eq PVoid (PEff A B) _ _ C ()
matchesPolyType-ground-eq PVoid (Pμ-type _) _ _ C ()
matchesPolyType-ground-eq PVoid (Pν-type _) _ _ C ()
matchesPolyType-ground-eq PInt (A P* B) _ _ C ()
matchesPolyType-ground-eq PInt (A P+ B) _ _ C ()
matchesPolyType-ground-eq PInt (A P⇒[ _ ] B) _ _ C ()
matchesPolyType-ground-eq PInt (PEff A B) _ _ C ()
matchesPolyType-ground-eq PInt (Pμ-type _) _ _ C ()
matchesPolyType-ground-eq PInt (Pν-type _) _ _ C ()
matchesPolyType-ground-eq PFloat (A P* B) _ _ C ()
matchesPolyType-ground-eq PFloat (A P+ B) _ _ C ()
matchesPolyType-ground-eq PFloat (A P⇒[ _ ] B) _ _ C ()
matchesPolyType-ground-eq PFloat (PEff A B) _ _ C ()
matchesPolyType-ground-eq PFloat (Pμ-type _) _ _ C ()
matchesPolyType-ground-eq PFloat (Pν-type _) _ _ C ()
matchesPolyType-ground-eq PStr (A P* B) _ _ C ()
matchesPolyType-ground-eq PStr (A P+ B) _ _ C ()
matchesPolyType-ground-eq PStr (A P⇒[ _ ] B) _ _ C ()
matchesPolyType-ground-eq PStr (PEff A B) _ _ C ()
matchesPolyType-ground-eq PStr (Pμ-type _) _ _ C ()
matchesPolyType-ground-eq PStr (Pν-type _) _ _ C ()
matchesPolyType-ground-eq PBuffer (A P* B) _ _ C ()
matchesPolyType-ground-eq PBuffer (A P+ B) _ _ C ()
matchesPolyType-ground-eq PBuffer (A P⇒[ _ ] B) _ _ C ()
matchesPolyType-ground-eq PBuffer (PEff A B) _ _ C ()
matchesPolyType-ground-eq PBuffer (Pμ-type _) _ _ C ()
matchesPolyType-ground-eq PBuffer (Pν-type _) _ _ C ()
-- Continue for structural mismatches in reverse direction
matchesPolyType-ground-eq (A P* B) PUnit _ _ C ()
matchesPolyType-ground-eq (A P* B) PVoid _ _ C ()
matchesPolyType-ground-eq (A P* B) PInt _ _ C ()
matchesPolyType-ground-eq (A P* B) PFloat _ _ C ()
matchesPolyType-ground-eq (A P* B) PStr _ _ C ()
matchesPolyType-ground-eq (A P* B) PBuffer _ _ C ()
matchesPolyType-ground-eq (A P* B) (_ P+ _) _ _ C ()
matchesPolyType-ground-eq (A P* B) (_ P⇒[ _ ] _) _ _ C ()
matchesPolyType-ground-eq (A P* B) (PEff _ _) _ _ C ()
matchesPolyType-ground-eq (A P* B) (Pμ-type _) _ _ C ()
matchesPolyType-ground-eq (A P* B) (Pν-type _) _ _ C ()
matchesPolyType-ground-eq (A P+ B) PUnit _ _ C ()
matchesPolyType-ground-eq (A P+ B) PVoid _ _ C ()
matchesPolyType-ground-eq (A P+ B) PInt _ _ C ()
matchesPolyType-ground-eq (A P+ B) PFloat _ _ C ()
matchesPolyType-ground-eq (A P+ B) PStr _ _ C ()
matchesPolyType-ground-eq (A P+ B) PBuffer _ _ C ()
matchesPolyType-ground-eq (A P+ B) (_ P* _) _ _ C ()
matchesPolyType-ground-eq (A P+ B) (_ P⇒[ _ ] _) _ _ C ()
matchesPolyType-ground-eq (A P+ B) (PEff _ _) _ _ C ()
matchesPolyType-ground-eq (A P+ B) (Pμ-type _) _ _ C ()
matchesPolyType-ground-eq (A P+ B) (Pν-type _) _ _ C ()
matchesPolyType-ground-eq (A P⇒[ _ ] B) PUnit _ _ C ()
matchesPolyType-ground-eq (A P⇒[ _ ] B) PVoid _ _ C ()
matchesPolyType-ground-eq (A P⇒[ _ ] B) PInt _ _ C ()
matchesPolyType-ground-eq (A P⇒[ _ ] B) PFloat _ _ C ()
matchesPolyType-ground-eq (A P⇒[ _ ] B) PStr _ _ C ()
matchesPolyType-ground-eq (A P⇒[ _ ] B) PBuffer _ _ C ()
matchesPolyType-ground-eq (A P⇒[ _ ] B) (_ P* _) _ _ C ()
matchesPolyType-ground-eq (A P⇒[ _ ] B) (_ P+ _) _ _ C ()
matchesPolyType-ground-eq (A P⇒[ _ ] B) (PEff _ _) _ _ C ()
matchesPolyType-ground-eq (A P⇒[ _ ] B) (Pμ-type _) _ _ C ()
matchesPolyType-ground-eq (A P⇒[ _ ] B) (Pν-type _) _ _ C ()
matchesPolyType-ground-eq (PEff A B) PUnit _ _ C ()
matchesPolyType-ground-eq (PEff A B) PVoid _ _ C ()
matchesPolyType-ground-eq (PEff A B) PInt _ _ C ()
matchesPolyType-ground-eq (PEff A B) PFloat _ _ C ()
matchesPolyType-ground-eq (PEff A B) PStr _ _ C ()
matchesPolyType-ground-eq (PEff A B) PBuffer _ _ C ()
matchesPolyType-ground-eq (PEff A B) (_ P* _) _ _ C ()
matchesPolyType-ground-eq (PEff A B) (_ P+ _) _ _ C ()
matchesPolyType-ground-eq (PEff A B) (_ P⇒[ _ ] _) _ _ C ()
matchesPolyType-ground-eq (PEff A B) (Pμ-type _) _ _ C ()
matchesPolyType-ground-eq (PEff A B) (Pν-type _) _ _ C ()
matchesPolyType-ground-eq (Pμ-type _) PUnit _ _ C ()
matchesPolyType-ground-eq (Pμ-type _) PVoid _ _ C ()
matchesPolyType-ground-eq (Pμ-type _) PInt _ _ C ()
matchesPolyType-ground-eq (Pμ-type _) PFloat _ _ C ()
matchesPolyType-ground-eq (Pμ-type _) PStr _ _ C ()
matchesPolyType-ground-eq (Pμ-type _) PBuffer _ _ C ()
matchesPolyType-ground-eq (Pμ-type _) (_ P* _) _ _ C ()
matchesPolyType-ground-eq (Pμ-type _) (_ P+ _) _ _ C ()
matchesPolyType-ground-eq (Pμ-type _) (_ P⇒[ _ ] _) _ _ C ()
matchesPolyType-ground-eq (Pμ-type _) (PEff _ _) _ _ C ()
matchesPolyType-ground-eq (Pμ-type _) (Pν-type _) _ _ C ()
matchesPolyType-ground-eq (Pν-type _) PUnit _ _ C ()
matchesPolyType-ground-eq (Pν-type _) PVoid _ _ C ()
matchesPolyType-ground-eq (Pν-type _) PInt _ _ C ()
matchesPolyType-ground-eq (Pν-type _) PFloat _ _ C ()
matchesPolyType-ground-eq (Pν-type _) PStr _ _ C ()
matchesPolyType-ground-eq (Pν-type _) PBuffer _ _ C ()
matchesPolyType-ground-eq (Pν-type _) (_ P* _) _ _ C ()
matchesPolyType-ground-eq (Pν-type _) (_ P+ _) _ _ C ()
matchesPolyType-ground-eq (Pν-type _) (_ P⇒[ _ ] _) _ _ C ()
matchesPolyType-ground-eq (Pν-type _) (PEff _ _) _ _ C ()
matchesPolyType-ground-eq (Pν-type _) (Pμ-type _) _ _ C ()

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
matchWithSubst (A₁ P⇒[ q₁ ] B₁) (A₂ P⇒[ q₂ ] B₂) σ with q₁ ≟q q₂
... | no _ = nothing
... | yes refl with matchWithSubst A₁ A₂ σ
...   | nothing = nothing
...   | just (A , σ') with matchWithSubst B₁ B₂ σ'
...     | nothing = nothing
...     | just (B , σ'') = just (A P⇒[ q₁ ] B , σ'')
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

------------------------------------------------------------------------
-- Substitution Extension Lemmas
------------------------------------------------------------------------

-- | Looking up a just-extended variable returns the value
extendInferSubst-lookup-eq : ∀ (σ : InferSubst) (x : String) (A : PolyType)
                           → lookupInferSubst (extendInferSubst σ x A) x ≡ just A
extendInferSubst-lookup-eq σ x A with x Data.String.≟ x
... | yes _ = refl
... | no x≢x = ⊥-elim (x≢x refl)
  where open import Data.Empty using (⊥-elim)

-- | Applying extended substitution to the variable gives the value
applySubst-extend-var : ∀ (σ : InferSubst) (x : String) (A : PolyType)
                      → applySubst (extendInferSubst σ x A) (TVar x) ≡ A
applySubst-extend-var σ x A with lookupInferSubst (extendInferSubst σ x A) x
                               | extendInferSubst-lookup-eq σ x A
... | just .A | refl = refl
... | nothing | ()

------------------------------------------------------------------------
-- Signature Matching (New architecture: bidirectional, no HM unification)
------------------------------------------------------------------------
--
-- A SigMap records an assignment from signature-variable names to ground
-- Types during a single one-shot structural match of a PolyType signature
-- against a ground Type. Unlike InferSubst, a SigMap is:
--
--   * Local to one signature-matching operation (not threaded globally).
--   * Consistency-checked on repeated variables.
--   * Produces ground Type results directly.
--
-- This is the bidirectional-typechecking equivalent of "signature
-- specialization at the use site" per D007 and Phase 5 of
-- plans/0.2.5-type-polytype-split.md.

SigMap : Set
SigMap = List (String × Type)

emptySig : SigMap
emptySig = []

-- | Look up a signature variable's current assignment, if any.
lookupSig : SigMap → String → Maybe Type
lookupSig [] _ = nothing
lookupSig ((y , T) ∷ m) x with x StrProp.≟ y
... | yes _ = just T
... | no _  = lookupSig m x

-- | Extend a SigMap with (x, T). Fails if x is already mapped to T' ≢ T.
extendSig : SigMap → String → Type → Maybe SigMap
extendSig m x T with lookupSig m x
... | nothing = just ((x , T) ∷ m)
... | just T' with T ≟T T'
...   | yes _ = just m         -- consistent, existing binding preserved
...   | no _  = nothing         -- inconsistent: same var, different types

-- | Match a polymorphic signature against a ground type.
--
-- Walks P and T in parallel, recording signature-variable bindings in
-- the accumulator. Fails on structural mismatch or inconsistent binding.
--
-- Terminates structurally on P.
--
matchSig : PolyType → Type → SigMap → Maybe SigMap
-- TVar: record (or confirm) a binding for this signature variable.
matchSig (TVar x) T m = extendSig m x T
-- Base types must match exactly.
matchSig PUnit   Unit   m = just m
matchSig PVoid   Void   m = just m
matchSig PInt    Int    m = just m
matchSig PFloat  Float  m = just m
matchSig PStr    Str    m = just m
matchSig PBuffer Buffer m = just m
-- Product: match both components.
matchSig (A₁ P* B₁) (A₂ Once.Type.* B₂) m = matchSig A₁ A₂ m >>= matchSig B₁ B₂
-- Sum: match both components.
matchSig (A₁ P+ B₁) (A₂ Once.Type.+ B₂) m = matchSig A₁ A₂ m >>= matchSig B₁ B₂
-- Function: quantities must match; then match domain and codomain.
matchSig (A₁ P⇒[ q₁ ] B₁) (A₂ ⇒[ q₂ ] B₂) m with q₁ ≟q q₂
... | yes refl = matchSig A₁ A₂ m >>= matchSig B₁ B₂
... | no  _    = nothing
-- Effect: match both components.
matchSig (PEff A₁ B₁) (Eff A₂ B₂) m = matchSig A₁ A₂ m >>= matchSig B₁ B₂
-- Functor fixed points: functors are ground by construction; use decidable equality.
matchSig (Pμ-type F₁) (μ-type F₂) m with embedFunctor F₂ ≟PF F₁
... | yes _ = just m
... | no  _ = nothing
matchSig (Pν-type F₁) (ν-type F₂) m with embedFunctor F₂ ≟PF F₁
... | yes _ = just m
... | no  _ = nothing
-- All other combinations: structural mismatch.
matchSig _ _ _ = nothing

-- | Apply a complete SigMap to a signature to obtain a ground Type.
--
-- Returns nothing if any TVar in the signature has no assignment.
-- Terminates structurally on the signature argument.
--
specialize : SigMap → PolyType → Maybe Type
specializeFunctor : SigMap → PolyFunctor → Maybe Functor
specialize m (TVar x)         = lookupSig m x
specialize m PUnit             = just Unit
specialize m PVoid             = just Void
specialize m PInt              = just Int
specialize m PFloat            = just Float
specialize m PStr              = just Str
specialize m PBuffer           = just Buffer
specialize m (A P* B)          = do
  A' ← specialize m A
  B' ← specialize m B
  just (A' Once.Type.* B')
specialize m (A P+ B)          = do
  A' ← specialize m A
  B' ← specialize m B
  just (A' Once.Type.+ B')
specialize m (A P⇒[ q ] B)     = do
  A' ← specialize m A
  B' ← specialize m B
  just (A' ⇒[ q ] B')
specialize m (PEff A B)        = do
  A' ← specialize m A
  B' ← specialize m B
  just (Eff A' B')
specialize m (Pμ-type F)       = do
  F' ← specializeFunctor m F
  just (μ-type F')
specialize m (Pν-type F)       = do
  F' ← specializeFunctor m F
  just (ν-type F')

specializeFunctor m (PK A) = do
  A' ← specialize m A
  just (K A')
specializeFunctor m PId        = just Id
specializeFunctor m (F P⊕ G) = do
  F' ← specializeFunctor m F
  G' ← specializeFunctor m G
  just (F' ⊕ G')
specializeFunctor m (F P⊗ G) = do
  F' ← specializeFunctor m F
  G' ← specializeFunctor m G
  just (F' ⊗ G')

------------------------------------------------------------------------
-- Per-Builtin Body Specializers
------------------------------------------------------------------------
--
-- The 13 builtin generators have known polymorphic bodies. Rather than
-- writing a generic PolyExpr→Expr specialization walk, we produce each
-- builtin's specialized body directly given the ground type arguments.
-- This is more principled: each builtin's body is a fixed small term
-- and its specialization is a one-line function over ground types.
--
-- All return SExpr S∅ _ (closed expressions); weaken to the actual
-- context with weakenFromEmpty at the call site.

specId : (T : Type) → SExpr S∅ (T ⇒ T)
specId T = Surface.lam Many (Surface.var zero)

specFst : (A B : Type) → SExpr S∅ (A Once.Type.* B ⇒ A)
specFst A B = Surface.lam Many (Surface.fst' (Surface.var zero))

specSnd : (A B : Type) → SExpr S∅ (A Once.Type.* B ⇒ B)
specSnd A B = Surface.lam Many (Surface.snd' (Surface.var zero))

specInl : (A B : Type) → SExpr S∅ (A ⇒ (A Once.Type.+ B))
specInl A B = Surface.lam Many (Surface.inl' (Surface.var zero))

specInr : (A B : Type) → SExpr S∅ (B ⇒ (A Once.Type.+ B))
specInr A B = Surface.lam Many (Surface.inr' (Surface.var zero))

specUnitGen : SExpr S∅ Unit
specUnitGen = Surface.unit

-- pair : (a → b) → (a → c) → a → (b × c)
specPair : (A B C : Type)
         → SExpr S∅ ((A ⇒ B) ⇒ (A ⇒ C) ⇒ A ⇒ (B Once.Type.* C))
specPair A B C =
  Surface.lam Many (Surface.lam Many (Surface.lam Many
    (Surface.pair
      (Surface.app (Surface.var (suc (suc zero))) (Surface.var zero))
      (Surface.app (Surface.var (suc zero)) (Surface.var zero)))))

-- terminal : a → Unit
specTerminal : (A : Type) → SExpr S∅ (A ⇒ Unit)
specTerminal A = Surface.lam Many Surface.unit

-- initial : Void → a
specInitial : (A : Type) → SExpr S∅ (Void ⇒ A)
specInitial A = Surface.lam Many (Surface.absurd (Surface.var zero))

-- curry : ((a × b) → c) → a → b → c
specCurry : (A B C : Type)
          → SExpr S∅ ((A Once.Type.* B ⇒ C) ⇒ A ⇒ B ⇒ C)
specCurry A B C =
  Surface.lam Many (Surface.lam Many (Surface.lam Many
    (Surface.app (Surface.var (suc (suc zero)))
                 (Surface.pair (Surface.var (suc zero)) (Surface.var zero)))))

-- apply : ((a → b) × a) → b
specApply : (A B : Type)
          → SExpr S∅ (((A ⇒ B) Once.Type.* A) ⇒ B)
specApply A B =
  Surface.lam Many
    (Surface.app (Surface.fst' (Surface.var zero))
                 (Surface.snd' (Surface.var zero)))

-- compose : (b → c) → (a → b) → a → c
specCompose : (A B C : Type)
            → SExpr S∅ ((B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
specCompose A B C =
  Surface.lam Many (Surface.lam Many (Surface.lam Many
    (Surface.app (Surface.var (suc (suc zero)))
                 (Surface.app (Surface.var (suc zero)) (Surface.var zero)))))

-- arr : (a → b) → Eff a b
specArr : (A B : Type) → SExpr S∅ ((A ⇒ B) ⇒ Eff A B)
specArr A B = Surface.lam Many (Surface.arr' (Surface.var zero))

------------------------------------------------------------------------
-- Ground Inference/Check Results (new architecture)
------------------------------------------------------------------------
--
-- Unlike PolyInferResult/PolyCheckResult, these carry a ground Type and
-- a ground-indexed Expr — no PolyType, no InferSubst, no extraction step.

data InferRes {n : ℕ} (Δ : SCtx n) : Set where
  successI : (T : Type) → SExpr Δ T
           → (depth : ℕ) → (fresh : ℕ) → Surface.Usage n
           → InferRes Δ
  failureI : String → InferRes Δ

data CheckRes {n : ℕ} (Δ : SCtx n) (T : Type) : Set where
  successC : SExpr Δ T
           → (depth : ℕ) → (fresh : ℕ) → Surface.Usage n
           → CheckRes Δ T
  failureC : String → CheckRes Δ T

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
-- New Ground Inference (Phase B: wired-up alongside old)
------------------------------------------------------------------------
--
-- These functions implement bidirectional type-checking producing ground
-- Type and SExpr directly, without going through PolyExpr or InferSubst.
-- Polymorphic builtins are specialized at their use site via spine
-- detection of App chains whose head is a builtin name.
--
-- The new implementation is additive; old code is retained until
-- coverage is complete and the switch is made.

-- | Walk the left spine of Raw.RApp to extract the head and argument list.
record AppSpine : Set where
  constructor mkSpine
  field
    head : RawExpr
    args : List RawExpr

spineOf : RawExpr → AppSpine
spineOf e = go e []
  where
    go : RawExpr → List RawExpr → AppSpine
    go (Raw.RApp f x) args = go f (x ∷ args)
    go other          args = mkSpine other args

-- | Is this name one of the 13 polymorphic builtins?
isPolyBuiltin : String → Bool
isPolyBuiltin "id"       = true
isPolyBuiltin "fst"      = true
isPolyBuiltin "snd"      = true
isPolyBuiltin "inl"      = true
isPolyBuiltin "inr"      = true
isPolyBuiltin "unit"     = true
isPolyBuiltin "pair"     = true
isPolyBuiltin "terminal" = true
isPolyBuiltin "initial"  = true
isPolyBuiltin "curry"    = true
isPolyBuiltin "apply"    = true
isPolyBuiltin "compose"  = true
isPolyBuiltin "arr"      = true
isPolyBuiltin _          = false

-- | Look up a local variable by name in a NamedCtx.
-- Returns just (i , type-at-i) if found in local bindings, nothing otherwise.
lookupLocal : (ctx : NamedCtx) → String
            → Maybe (∃[ A ] (SExpr (NamedCtx.debruijn ctx) A))
lookupLocal (mkCtx n Γ Δ _ _) x = go Γ Δ
  where
    go : ∀ {m} → Ctx → (Δ' : SCtx m) → Maybe (∃[ A ] (SExpr Δ' A))
    go [] S∅                  = nothing
    go [] (_ S, _ ^ _)        = nothing
    go (_ ∷ _) S∅             = nothing
    go {suc m} (b ∷ Γ') (Δ' S, B ^ Many) with Data.String._≟_ x (name b)
    ... | yes _ = just (B , Surface.var zero)
    ... | no _  with go Γ' Δ'
    ...   | nothing             = nothing
    ...   | just (A , se)       = just (A , weaken se)
    go {suc m} (b ∷ Γ') (Δ' S, B ^ q) with Data.String._≟_ x (name b)
    ... | yes _ = just (B , Surface.var zero)
    ... | no _  with go Γ' Δ'
    ...   | nothing             = nothing
    ...   | just (A , se)       = just (A , coerceQuantity (weaken {A = B} {q = q} se))

-- | Find a local variable's de Bruijn position and quantity by name.
-- Returns nothing if not in local bindings.
findLocalVarUsage : (ctx : NamedCtx) → String → Maybe (Fin (NamedCtx.size ctx) × Quantity)
findLocalVarUsage (mkCtx n Γ Δ _ _) x = go Γ Δ
  where
    go : ∀ {m} → Ctx → SCtx m → Maybe (Fin m × Quantity)
    go [] S∅ = nothing
    go [] (_ S, _ ^ _) = nothing
    go (_ ∷ _) S∅ = nothing
    go {suc m} (b ∷ Γ') (Δ' S, _ ^ q) with Data.String._≟_ x (name b)
    ... | yes _ = just (zero , q)
    ... | no  _ with go Γ' Δ'
    ...   | nothing = nothing
    ...   | just (i , q') = just (suc i , q')

-- | Projection of an InferElabResult as a function-typed result.
-- Used to avoid combinatorial nested-with coverage when the caller needs
-- the inferred type to be a function type. Handles failure propagation
-- and exhaustive non-function-type cases in one place.
data FunProjection {n : ℕ} (Δ : SCtx n) : Set where
  isFun  : (A : Type) (q : Quantity) (B : Type)
         → SExpr Δ (A ⇒[ q ] B) → ℕ → ℕ → Surface.Usage n
         → FunProjection Δ
  notFun : String → FunProjection Δ

asFun : ∀ {n} {Δ : SCtx n} → InferElabResult Δ → FunProjection Δ
asFun (failure err)                           = notFun err
asFun (success (A ⇒[ q ] B) se d f u)          = isFun A q B se d f u
asFun (success Unit _ _ _ _)                  = notFun "expected function type, got Unit"
asFun (success Void _ _ _ _)                  = notFun "expected function type, got Void"
asFun (success Int _ _ _ _)                   = notFun "expected function type, got Int"
asFun (success Float _ _ _ _)                 = notFun "expected function type, got Float"
asFun (success Str _ _ _ _)                   = notFun "expected function type, got Str"
asFun (success Buffer _ _ _ _)                = notFun "expected function type, got Buffer"
asFun (success (_ Once.Type.* _) _ _ _ _)     = notFun "expected function type, got product"
asFun (success (_ Once.Type.+ _) _ _ _ _)     = notFun "expected function type, got sum"
asFun (success (Eff _ _) _ _ _ _)             = notFun "expected function type, got Eff"
asFun (success (μ-type _) _ _ _ _)            = notFun "expected function type, got μ-type"
asFun (success (ν-type _) _ _ _ _)            = notFun "expected function type, got ν-type"

-- | Projection as an Int-typed result. Same pattern as asFun.
data IntProjection {n : ℕ} (Δ : SCtx n) : Set where
  isInt  : SExpr Δ Int → ℕ → ℕ → Surface.Usage n → IntProjection Δ
  notInt : String → IntProjection Δ

asInt : ∀ {n} {Δ : SCtx n} → InferElabResult Δ → IntProjection Δ
asInt (failure err)                           = notInt err
asInt (success Int se d f u)                  = isInt se d f u
asInt (success Unit _ _ _ _)                  = notInt "expected Int, got Unit"
asInt (success Void _ _ _ _)                  = notInt "expected Int, got Void"
asInt (success Float _ _ _ _)                 = notInt "expected Int, got Float"
asInt (success Str _ _ _ _)                   = notInt "expected Int, got Str"
asInt (success Buffer _ _ _ _)                = notInt "expected Int, got Buffer"
asInt (success (_ Once.Type.* _) _ _ _ _)     = notInt "expected Int, got product"
asInt (success (_ Once.Type.+ _) _ _ _ _)     = notInt "expected Int, got sum"
asInt (success (_ ⇒[ _ ] _) _ _ _ _)          = notInt "expected Int, got function"
asInt (success (Eff _ _) _ _ _ _)             = notInt "expected Int, got Eff"
asInt (success (μ-type _) _ _ _ _)            = notInt "expected Int, got μ-type"
asInt (success (ν-type _) _ _ _ _)            = notInt "expected Int, got ν-type"

------------------------------------------------------------------------
-- New Bidirectional Inference/Checking (ground types throughout)
------------------------------------------------------------------------
--
-- These produce InferElabResult/CheckElabResult directly — no PolyExpr
-- intermediate, no InferSubst, no extraction. Polymorphic builtins are
-- specialized at their use site by inline pattern matching on the
-- application chain shape.
--
-- Current coverage: literals, unit, local variables, imports, type
-- annotations, let bindings (monomorphic), pair, case, binops, unary,
-- full applications of polymorphic builtins with all arguments provided,
-- lambdas in check mode, arbitrary applications in infer mode when the
-- function's type is a ground function type.

mutual
  inferNew : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)
  checkNew : (ctx : NamedCtx) → RawExpr → (T : Type) → CheckElabResult (NamedCtx.debruijn ctx) T

  -- ===== inferNew =====

  -- Literals
  inferNew ctx (Raw.RInt n) =
    success Int (Surface.int n) 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage
  inferNew ctx (Raw.RStringLit s) =
    success Str (Surface.str s) 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage
  inferNew ctx Raw.RUnit =
    success Unit Surface.unit 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage

  -- Type annotation: check against the annotated type
  inferNew ctx (Raw.RAnnot e T) with checkNew ctx e T
  ... | success se d f u = success T se d f u
  ... | failure err = failure err

  -- The `unit` builtin is monomorphic: type is Unit.
  inferNew ctx (Raw.RVar "unit") =
    success Unit Surface.unit 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage

  -- Variable lookup (generic). Local first, then import, else fail.
  inferNew ctx (Raw.RVar x) with lookupLocal ctx x
  ... | just (A , se) with findLocalVarUsage ctx x
  ...   | just (i , q) = success A se 0 (NamedCtx.freshCounter ctx) (Surface.singleUse i q)
  ...   | nothing = success A se 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage
  inferNew ctx (Raw.RVar x) | nothing with lookupImport (NamedCtx.imports ctx) x
  ... | just ty = success ty (Surface.prim x) 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage
  ... | nothing = failure ("Unbound or unspecialized variable: " ++ x ++
                           " (polymorphic builtins must appear applied or in check mode)")

  -- Qualified name: look up as "alias.name"
  inferNew ctx (Raw.RQualified name alias) with lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)
  ... | just ty = success ty (Surface.prim (alias ++ "." ++ name)) 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage
  ... | nothing = failure ("Unbound qualified variable: " ++ name ++ "@" ++ alias)

  -- Lambda without annotation: rejected in infer mode
  inferNew ctx (Raw.RLam _ _) =
    failure "Lambda without type annotation not supported in inference mode."

  -- Polymorphic builtin applications (full arity).
  -- id : A → A
  inferNew ctx (Raw.RApp (Raw.RVar "id") arg) with inferNew ctx arg
  ... | failure err = failure err
  ... | success T argE d f u =
        success T (Surface.app (weakenFromEmpty (specId T)) argE) (suc d) f u

  -- fst : (A * B) → A
  inferNew ctx (Raw.RApp (Raw.RVar "fst") arg) with inferNew ctx arg
  ... | failure err = failure err
  ... | success (A Once.Type.* B) argE d f u =
        success A (Surface.app (weakenFromEmpty (specFst A B)) argE) (suc d) f u
  ... | success _ _ _ _ _ = failure "fst requires a pair argument"

  -- snd : (A * B) → B
  inferNew ctx (Raw.RApp (Raw.RVar "snd") arg) with inferNew ctx arg
  ... | failure err = failure err
  ... | success (A Once.Type.* B) argE d f u =
        success B (Surface.app (weakenFromEmpty (specSnd A B)) argE) (suc d) f u
  ... | success _ _ _ _ _ = failure "snd requires a pair argument"

  -- terminal : A → Unit
  inferNew ctx (Raw.RApp (Raw.RVar "terminal") arg) with inferNew ctx arg
  ... | failure err = failure err
  ... | success A argE d f u =
        success Unit (Surface.app (weakenFromEmpty (specTerminal A)) argE) (suc d) f u

  -- arr : (A → B) → Eff A B
  inferNew ctx (Raw.RApp (Raw.RVar "arr") arg) with inferNew ctx arg
  ... | failure err = failure err
  ... | success (A ⇒[ Many ] B) argE d f u =
        success (Eff A B) (Surface.app (weakenFromEmpty (specArr A B)) argE) (suc d) f u
  ... | success _ _ _ _ _ = failure "arr requires a (A → B) pure-function argument"

  -- apply : ((A → B) * A) → B
  inferNew ctx (Raw.RApp (Raw.RVar "apply") arg) with inferNew ctx arg
  ... | failure err = failure err
  ... | success ((A ⇒[ Many ] B) Once.Type.* A') argE d f u with A ≟T A'
  ...   | yes refl = success B (Surface.app (weakenFromEmpty (specApply A B)) argE) (suc d) f u
  ...   | no _ = failure "apply: function domain must match second component"
  inferNew ctx (Raw.RApp (Raw.RVar "apply") _) | success _ _ _ _ _ = failure "apply requires ((A → B) * A)"

  -- compose : (B → C) → (A → B) → A → C  (arity 3)
  inferNew ctx (Raw.RApp (Raw.RApp (Raw.RApp (Raw.RVar "compose") f) g) x) with asFun (inferNew ctx f)
  ... | notFun err = failure ("compose/f: " ++ err)
  ... | isFun B qF C fE df ff uf with qF ≟q Many
  ...   | no _ = failure "compose: f must have Many-arrow function type"
  ...   | yes refl with asFun (inferNew ctx g)
  ...     | notFun err = failure ("compose/g: " ++ err)
  ...     | isFun A qG B' gE dg fg ug with qG ≟q Many | B ≟T B'
  ...       | no _ | _ = failure "compose: g must have Many-arrow function type"
  ...       | yes _ | no _ = failure "compose: g's codomain must match f's domain"
  ...       | yes refl | yes refl with inferNew ctx x
  ...         | failure err = failure err
  ...         | success A' xE dx fx ux with A ≟T A'
  ...           | yes refl = success C
                               (Surface.app (Surface.app
                                 (Surface.app (weakenFromEmpty (specCompose A B C)) fE)
                                 gE) xE)
                               (suc (df ⊔ dg ⊔ dx)) fx (uf +ᵘ ug +ᵘ ux)
  ...           | no _ = failure "compose: x's type must match g's domain"

  -- pair (fork) : (A → B) → (A → C) → A → (B * C)  (arity 3)
  inferNew ctx (Raw.RApp (Raw.RApp (Raw.RApp (Raw.RVar "pair") f) g) x) with asFun (inferNew ctx f)
  ... | notFun err = failure ("pair/f: " ++ err)
  ... | isFun A qF B fE df ff uf with qF ≟q Many
  ...   | no _ = failure "pair: f must have Many-arrow function type"
  ...   | yes refl with asFun (inferNew ctx g)
  ...     | notFun err = failure ("pair/g: " ++ err)
  ...     | isFun A' qG C gE dg fg ug with qG ≟q Many | A ≟T A'
  ...       | no _ | _ = failure "pair: g must have Many-arrow function type"
  ...       | yes _ | no _ = failure "pair: f and g must share the same domain"
  ...       | yes refl | yes refl with inferNew ctx x
  ...         | failure err = failure err
  ...         | success A'' xE dx fx ux with A ≟T A''
  ...           | yes refl = success (B Once.Type.* C)
                               (Surface.app (Surface.app
                                 (Surface.app (weakenFromEmpty (specPair A B C)) fE)
                                 gE) xE)
                               (suc (df ⊔ dg ⊔ dx)) fx (uf +ᵘ ug +ᵘ ux)
  ...           | no _ = failure "pair: x's type must match f/g domain"

  -- curry : ((A * B) → C) → A → B → C  (arity 3)
  inferNew ctx (Raw.RApp (Raw.RApp (Raw.RApp (Raw.RVar "curry") fn) a) b) with asFun (inferNew ctx fn)
  ... | notFun err = failure ("curry/fn: " ++ err)
  ... | isFun domT qF C fnE df ff uf with qF ≟q Many
  ...   | no _ = failure "curry: fn must have Many-arrow function type"
  ...   | yes refl with domT
  ...     | Unit        = failure "curry: fn's domain must be a product (A * B)"
  ...     | Void        = failure "curry: fn's domain must be a product (A * B)"
  ...     | Int         = failure "curry: fn's domain must be a product (A * B)"
  ...     | Float       = failure "curry: fn's domain must be a product (A * B)"
  ...     | Str         = failure "curry: fn's domain must be a product (A * B)"
  ...     | Buffer      = failure "curry: fn's domain must be a product (A * B)"
  ...     | (_ Once.Type.+ _) = failure "curry: fn's domain must be a product (A * B)"
  ...     | (_ ⇒[ _ ] _)       = failure "curry: fn's domain must be a product (A * B)"
  ...     | (Eff _ _)   = failure "curry: fn's domain must be a product (A * B)"
  ...     | (μ-type _)  = failure "curry: fn's domain must be a product (A * B)"
  ...     | (ν-type _)  = failure "curry: fn's domain must be a product (A * B)"
  ...     | (A Once.Type.* B) with inferNew ctx a
  ...       | failure err = failure err
  ...       | success A' aE da fa ua with A ≟T A'
  ...         | no _ = failure "curry: a's type must match the first component"
  ...         | yes refl with inferNew ctx b
  ...           | failure err = failure err
  ...           | success B' bE db fb ub with B ≟T B'
  ...             | yes refl = success C
                                 (Surface.app (Surface.app
                                   (Surface.app (weakenFromEmpty (specCurry A B C)) fnE)
                                   aE) bE)
                                 (suc (df ⊔ da ⊔ db)) fb (uf +ᵘ ua +ᵘ ub)
  ...             | no _ = failure "curry: b's type must match the second component"

  -- Partial or unsupported builtins in infer mode
  inferNew ctx (Raw.RApp (Raw.RVar "inl") _) =
    failure "inl requires check mode (needs target sum type)"
  inferNew ctx (Raw.RApp (Raw.RVar "inr") _) =
    failure "inr requires check mode (needs target sum type)"
  inferNew ctx (Raw.RApp (Raw.RVar "initial") _) =
    failure "initial requires check mode (needs target type)"

  -- Generic application: infer f, project as function type, then infer x.
  inferNew ctx (Raw.RApp f x) with asFun (inferNew ctx f)
  ... | notFun err = failure err
  ... | isFun A q B fE df ff uf with inferNew ctx x
  ...   | failure err = failure err
  ...   | success A' xE dx fx ux with A ≟T A'
  ...     | yes refl = success B (Surface.app fE xE) (df ⊔ dx) fx (uf +ᵘ ux)
  ...     | no _ = failure ("Application: argument type " ++ showType A' ++
                            " does not match function domain " ++ showType A)

  -- Let binding: infer e₁ monomorphically, then e₂ under extended context
  inferNew ctx (Raw.RLet x e₁ e₂) with inferNew ctx e₁
  ... | failure err = failure err
  ... | success A e₁E d₁ f₁ u₁ with inferNew (extendNamedCtx ctx x A) e₂
  ...   | failure err = failure err
  ...   | success B e₂E d₂ f₂ u₂ =
        success B (Surface.let' e₁E e₂E) (d₁ ⊔ suc d₂) f₂ (u₁ +ᵘ Surface.tailUsage u₂)

  -- Pair introduction
  inferNew ctx (Raw.RPair a b) with inferNew ctx a
  ... | failure err = failure err
  ... | success A aE da fa ua with inferNew ctx b
  ...   | failure err = failure err
  ...   | success B bE db fb ub =
        success (A Once.Type.* B) (Surface.pair aE bE) (da ⊔ db) fb (ua +ᵘ ub)

  -- Case (destruct)
  inferNew ctx (Raw.RDestruct scrut xL eL xR eR) with inferNew ctx scrut
  ... | failure err = failure err
  ... | success (A Once.Type.+ B) scrutE ds fs us with inferNew (extendNamedCtx ctx xL A) eL
  ...   | failure err = failure err
  ...   | success C₁ eLE dL fL uL with inferNew (extendNamedCtx ctx xR B) eR
  ...     | failure err = failure err
  ...     | success C₂ eRE dR fR uR with C₁ ≟T C₂
  ...       | yes refl = success C₁ (Surface.case' scrutE eLE eRE)
                           (ds ⊔ suc dL ⊔ suc dR) fR (us +ᵘ Surface.tailUsage uL +ᵘ Surface.tailUsage uR)
  ...       | no _ = failure "Case branches have different types"
  inferNew ctx (Raw.RDestruct _ _ _ _ _) | success _ _ _ _ _ = failure "Case requires a sum-typed scrutinee"

  -- Binary operators: both operands must be Int.
  inferNew ctx (Raw.RBinOp op e₁ e₂) with asInt (inferNew ctx e₁)
  ... | notInt err = failure ("binop left: " ++ err)
  ... | isInt e₁E d₁ f₁ u₁ with asInt (inferNew ctx e₂)
  ...   | notInt err = failure ("binop right: " ++ err)
  ...   | isInt e₂E d₂ f₂ u₂ =
        if Raw.isArithmeticOp op
          then success Int (mkArith op e₁E e₂E) (d₁ ⊔ d₂) f₂ (u₁ +ᵘ u₂)
          else success (Unit Once.Type.+ Unit) (mkCmp op e₁E e₂E) (d₁ ⊔ d₂) f₂ (u₁ +ᵘ u₂)
    where
      mkArith : Raw.BinOp → SExpr _ Int → SExpr _ Int → SExpr _ Int
      mkArith Raw.OpAdd = Surface.add
      mkArith Raw.OpSub = Surface.sub
      mkArith Raw.OpMul = Surface.mul
      mkArith Raw.OpDiv = Surface.div
      mkArith Raw.OpMod = Surface.mod'
      mkArith _ = Surface.add
      mkCmp : Raw.BinOp → SExpr _ Int → SExpr _ Int → SExpr _ (Unit Once.Type.+ Unit)
      mkCmp Raw.OpLt = Surface.lt
      mkCmp Raw.OpLe = Surface.le
      mkCmp Raw.OpGt = Surface.gt
      mkCmp Raw.OpGe = Surface.ge
      mkCmp Raw.OpEq = Surface.eq
      mkCmp Raw.OpNe = Surface.ne
      mkCmp _ = Surface.lt

  -- Unary
  inferNew ctx (Raw.RUnaryOp Raw.OpNeg e) with inferNew ctx e
  ... | failure err = failure err
  ... | success Int eE d f u = success Int (Surface.neg eE) d f u
  ... | success _ _ _ _ _ = failure "Negation requires Int operand"

  -- ===== checkNew =====

  -- Lambda in check mode: destruct function type from expected
  checkNew ctx (Raw.RLam x body) (A ⇒[ q ] B) with checkNew (extendNamedCtx ctx x A) body B
  ... | failure err = failure err
  ... | success bodyE d f u =
        let paramUsage = Surface.lookupUsage u zero
        in if paramUsage ≤q q
             then success (Surface.lam q bodyE) (suc d) f (Surface.tailUsage u)
             else failure ("Parameter '" ++ x ++ "' used with quantity " ++ showQuantity paramUsage ++
                          " but declared with quantity " ++ showQuantity q)
  checkNew ctx (Raw.RLam _ _) _ = failure "Lambda requires function type"

  -- inl in check mode: expected sum type
  checkNew ctx (Raw.RApp (Raw.RVar "inl") arg) (A Once.Type.+ B) with checkNew ctx arg A
  ... | failure err = failure err
  ... | success argE d f u =
        success (Surface.app (weakenFromEmpty (specInl A B)) argE) (suc d) f u
  checkNew ctx (Raw.RApp (Raw.RVar "inl") _) _ = failure "inl expects a sum type in check mode"

  -- inr in check mode
  checkNew ctx (Raw.RApp (Raw.RVar "inr") arg) (A Once.Type.+ B) with checkNew ctx arg B
  ... | failure err = failure err
  ... | success argE d f u =
        success (Surface.app (weakenFromEmpty (specInr A B)) argE) (suc d) f u
  checkNew ctx (Raw.RApp (Raw.RVar "inr") _) _ = failure "inr expects a sum type in check mode"

  -- initial in check mode: Void → A, so arg must have type Void, result T = A
  checkNew ctx (Raw.RApp (Raw.RVar "initial") arg) T with checkNew ctx arg Void
  ... | failure err = failure err
  ... | success argE d f u =
        success (Surface.app (weakenFromEmpty (specInitial T)) argE) (suc d) f u

  -- Generic fallback: infer and match types
  checkNew ctx e T with inferNew ctx e
  ... | failure err = failure err
  ... | success T' eE d f u with T ≟T T'
  ...   | yes refl = success eE d f u
  ...   | no _ = failure ("Type mismatch: expected " ++ showType T ++ " but got " ++ showType T')

-- | Experimental: new-architecture inference entry point (not yet default).
-- Enforces the depth ≤ 7 limit, same as inferElab.
newInferElab : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)
newInferElab ctx rawExpr = checkDepth (inferNew ctx rawExpr)
  where
    checkDepth : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
    checkDepth (failure err) = failure err
    checkDepth (success ty expr depth fresh usage) with depth ≤? 7
    ... | yes _ = success ty expr depth fresh usage
    ... | no _ = failure ("Expression nesting depth exceeds verified limit.\n" ++
                         "  Depth encountered: " ++ showℕ depth ++ "\n" ++
                         "  Proven depth limit: 7\n" ++
                         "  Please refactor to reduce nesting of λ/case/let expressions.")

-- | Experimental: new-architecture checking entry point (not yet default).
newCheckElab : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A
newCheckElab ctx expr ty = checkDepth (checkNew ctx expr ty)
  where
    checkDepth : CheckElabResult (NamedCtx.debruijn ctx) ty → CheckElabResult (NamedCtx.debruijn ctx) ty
    checkDepth (failure err) = failure err
    checkDepth (success expr' depth fresh usage) with depth ≤? 7
    ... | yes _ = success expr' depth fresh usage
    ... | no _ = failure ("Expression nesting depth exceeds verified limit.\n" ++
                         "  Depth encountered: " ++ showℕ depth ++ "\n" ++
                         "  Proven depth limit: 7\n" ++
                         "  Please refactor to reduce nesting of λ/case/let expressions.")

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
-- | Implementation now delegates to newInferElab (bidirectional, ground).
-- The old polymorphic-inference-then-extract path is retained only for the
-- deprecated compile paths while downstream stages are verified.
inferElab : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)
inferElab = newInferElab

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

-- | Implementation delegates to newCheckElab (bidirectional, ground).
checkElab : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A
checkElab = newCheckElab

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