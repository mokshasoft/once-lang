-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.TypeAlgs — the three readings of a printed type
-- (plan 0.124 step 4.2).
--
-- A signature's type reads as itself (its variables lowercase words), an
-- alias's type as itself (it has none), an annotation's ground type, printed
-- as its polynomial type (`toPoly`), as itself when its effectful arrows are
-- the `Eff`/`Act` ones (as read: `Many`).
------------------------------------------------------------------------

module Once.Format.Proof.TypeAlgs where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Once.Spec.Grade using (Quantity; Many; Finite; pureᶠ; actᶠ; fin; eff; mk-kind)
open import Once.Spec.Type using (Ty; Fun; Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_)
open import Once.Spec.Surface.Syntax using (PolyType; PolyFunctor; PUnit; PVoid; PInt; PFloat; _P*_; _P+_; _P⇒[_]_;
  PAct; PEff; Pμ; Pν; PTVar; PK; PId; _P⊕_; _P⊗_)
open import Once.Spec.Surface.Grammar using (TypeAlg; TypeVar; tvar; NoExtra; lowerWord)
open import Once.Format.Print using (toPoly; toPolyF)
import Once.Format.Proof.Types as PT

-- The Spec's algebras (`Grammar.written`, `Grammar.ground`), field for field.
written : (X : _) → TypeAlg PolyType PolyFunctor
written X = record
  { aUnit = PUnit ; aVoid = PVoid ; aInt = PInt ; aFloat = PFloat
  ; aProd = _P*_ ; aSum = _P+_ ; aEff = PEff ; aAct = PAct
  ; aArrow = λ q A B → A P⇒[ q ] B ; aMu = Pμ ; aNu = λ f F → Pν F f
  ; fK = PK ; fId = PId ; fSum = _P⊕_ ; fProd = _P⊗_
  ; Extra = X }

ground : TypeAlg Type (Fun 0)
ground = record
  { aUnit = Unit ; aVoid = Void ; aInt = Int ; aFloat = Float
  ; aProd = _*_ ; aSum = _+_
  ; aEff = λ A B → A ⇒[ mk-kind Many eff ] B ; aAct = λ A B → A ⇒[ mk-kind Many (fin actᶠ) ] B
  ; aArrow = λ q A B → A ⇒[ mk-kind q (fin pureᶠ) ] B ; aMu = μ ; aNu = λ f F → ν F f
  ; fK = K ; fId = Id ; fSum = _⊕_ ; fProd = _⊗_
  ; Extra = NoExtra }

-- | In a signature, a type variable is a lowercase word.
module Sig = PT.Read (written TypeVar) (λ x → lowerWord x ≡ true) PTVar tvar

-- | An alias has no type variables.
module Alias = PT.Read (written NoExtra) (λ _ → ⊥) PTVar (λ ())

-- | An annotation's type is ground.
module Ground = PT.Read ground (λ _ → ⊥) (λ _ → Unit) (λ ())

mutual
  -- | Written types read as themselves.
  sig-id : ∀ P → Sig.⟦ P ⟧ ≡ P
  sig-id PUnit         = refl
  sig-id PVoid         = refl
  sig-id PInt          = refl
  sig-id PFloat        = refl
  sig-id (A P* B)      = cong₂ _P*_ (sig-id A) (sig-id B)
  sig-id (A P+ B)      = cong₂ _P+_ (sig-id A) (sig-id B)
  sig-id (A P⇒[ q ] B) = cong₂ (λ X Y → X P⇒[ q ] Y) (sig-id A) (sig-id B)
  sig-id (PAct A B)    = cong₂ PAct (sig-id A) (sig-id B)
  sig-id (PEff A B)    = cong₂ PEff (sig-id A) (sig-id B)
  sig-id (Pμ F)        = cong Pμ (sigF-id F)
  sig-id (Pν F φ)      = cong (λ G → Pν G φ) (sigF-id F)
  sig-id (PTVar x)     = refl

  sigF-id : ∀ F → Sig.⟦ F ⟧F ≡ F
  sigF-id (PK A)   = cong PK (sig-id A)
  sigF-id PId      = refl
  sigF-id (F P⊕ G) = cong₂ _P⊕_ (sigF-id F) (sigF-id G)
  sigF-id (F P⊗ G) = cong₂ _P⊗_ (sigF-id F) (sigF-id G)

mutual
  alias-id : ∀ P → Alias.⟦ P ⟧ ≡ P
  alias-id PUnit         = refl
  alias-id PVoid         = refl
  alias-id PInt          = refl
  alias-id PFloat        = refl
  alias-id (A P* B)      = cong₂ _P*_ (alias-id A) (alias-id B)
  alias-id (A P+ B)      = cong₂ _P+_ (alias-id A) (alias-id B)
  alias-id (A P⇒[ q ] B) = cong₂ (λ X Y → X P⇒[ q ] Y) (alias-id A) (alias-id B)
  alias-id (PAct A B)    = cong₂ PAct (alias-id A) (alias-id B)
  alias-id (PEff A B)    = cong₂ PEff (alias-id A) (alias-id B)
  alias-id (Pμ F)        = cong Pμ (aliasF-id F)
  alias-id (Pν F φ)      = cong (λ G → Pν G φ) (aliasF-id F)
  alias-id (PTVar x)     = refl

  aliasF-id : ∀ F → Alias.⟦ F ⟧F ≡ F
  aliasF-id (PK A)   = cong PK (alias-id A)
  aliasF-id PId      = refl
  aliasF-id (F P⊕ G) = cong₂ _P⊕_ (aliasF-id F) (aliasF-id G)
  aliasF-id (F P⊗ G) = cong₂ _P⊗_ (aliasF-id F) (aliasF-id G)

mutual
  -- | A ground type whose effectful arrows are as read.
  GroundOK : Type → Set
  GroundOK Unit  = ⊤
  GroundOK Void  = ⊤
  GroundOK Int   = ⊤
  GroundOK Float = ⊤
  GroundOK (A ⇒[ mk-kind q (fin pureᶠ) ] B) = GroundOK A × GroundOK B
  GroundOK (A ⇒[ mk-kind q (fin actᶠ) ] B)  = q ≡ Many × GroundOK A × GroundOK B
  GroundOK (A ⇒[ mk-kind q eff ] B)         = q ≡ Many × GroundOK A × GroundOK B
  GroundOK (A * B) = GroundOK A × GroundOK B
  GroundOK (A + B) = GroundOK A × GroundOK B
  GroundOK (μ F)   = GroundOKF F
  GroundOK (ν F φ) = GroundOKF F

  GroundOKF : Fun 0 → Set
  GroundOKF Id      = ⊤
  GroundOKF (K A)   = GroundOK A
  GroundOKF (F ⊕ G) = GroundOKF F × GroundOKF G
  GroundOKF (F ⊗ G) = GroundOKF F × GroundOKF G

mutual
  -- | …reads back as itself, and has no type variables.
  ground-id : ∀ T → GroundOK T → Ground.⟦ toPoly T ⟧ ≡ T
  ground-id Unit  _ = refl
  ground-id Void  _ = refl
  ground-id Int   _ = refl
  ground-id Float _ = refl
  ground-id (A ⇒[ mk-kind q (fin pureᶠ) ] B) (a , b) = cong₂ (λ X Y → X ⇒[ mk-kind q (fin pureᶠ) ] Y) (ground-id A a) (ground-id B b)
  ground-id (A ⇒[ mk-kind q (fin actᶠ) ] B) (refl , a , b) = cong₂ (λ X Y → X ⇒[ mk-kind Many (fin actᶠ) ] Y) (ground-id A a) (ground-id B b)
  ground-id (A ⇒[ mk-kind q eff ] B) (refl , a , b) = cong₂ (λ X Y → X ⇒[ mk-kind Many eff ] Y) (ground-id A a) (ground-id B b)
  ground-id (A * B) (a , b) = cong₂ _*_ (ground-id A a) (ground-id B b)
  ground-id (A + B) (a , b) = cong₂ _+_ (ground-id A a) (ground-id B b)
  ground-id (μ F)   f = cong μ (groundF-id F f)
  ground-id (ν F φ) f = cong (λ G → ν G φ) (groundF-id F f)

  groundF-id : ∀ F → GroundOKF F → Ground.⟦ toPolyF F ⟧F ≡ F
  groundF-id Id      _ = refl
  groundF-id (K A)   a = cong K (ground-id A a)
  groundF-id (F ⊕ G) (f , g) = cong₂ _⊕_ (groundF-id F f) (groundF-id G g)
  groundF-id (F ⊗ G) (f , g) = cong₂ _⊗_ (groundF-id F f) (groundF-id G g)

mutual
  ground-wf : ∀ T → Ground.WF (toPoly T)
  ground-wf Unit  = tt
  ground-wf Void  = tt
  ground-wf Int   = tt
  ground-wf Float = tt
  ground-wf (A ⇒[ mk-kind q (fin pureᶠ) ] B) = ground-wf A , ground-wf B
  ground-wf (A ⇒[ mk-kind q (fin actᶠ) ] B)  = ground-wf A , ground-wf B
  ground-wf (A ⇒[ mk-kind q eff ] B)         = ground-wf A , ground-wf B
  ground-wf (A * B) = ground-wf A , ground-wf B
  ground-wf (A + B) = ground-wf A , ground-wf B
  ground-wf (μ F)   = groundF-wf F
  ground-wf (ν F φ) = groundF-wf F

  groundF-wf : ∀ F → Ground.WFF (toPolyF F)
  groundF-wf Id      = tt
  groundF-wf (K A)   = ground-wf A
  groundF-wf (F ⊕ G) = groundF-wf F , groundF-wf G
  groundF-wf (F ⊗ G) = groundF-wf F , groundF-wf G
