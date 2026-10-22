-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Check — the compiler's surface typing gives the
-- Spec's (plan 0.121 §3.6, F4).
--
-- The two judgments were transcribed from each other: bidirectional, rule
-- for rule, each naming the core term the expression means. A compiler
-- derivation (`⊢ᵢ`/`⊢ᶜ`/`⊢ᵈ`) of a resolved expression gives the Spec's
-- (`⇒`/`⇐`/`⇐ ⇒[ π ]↦`) of the related expression (`RX`), in related locals
-- (`LR`), at related types (`TyR`), naming a term related to the one the
-- compiler elaborates (`TmR`, `Elaboration.elab*`). A synthesized type is
-- related to the Spec's; a checked one is given related.
--
-- References to the module's own definitions are read through the
-- elaboration's View; what the Spec asks of them — the definition's name and
-- arity, that its type's variables occur, the shape of an arrow schema — is
-- asked of the View's entries (the parameters `h-…`), which the telescope
-- walk discharges.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _<_)
open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Internal.Contract using (ISig)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Signature using (Signature; _∶_)
import Once.Spec.Grade as LG
import Once.Internal.Core.PolyTy as LP
import Once.Spec.Type as ST
import Once.Internal.Elaboration as E
import Once.Internal.Type.Poly as TP
open import Once.Internal.Typing.Scope using (Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.Adequacy.SpecCore.Poly using (declS)
open import Once.Adequacy.SpecCore.Schema using (CleanSig; ptyS)

import Once.Spec.Grade
module Once.Adequacy.SpecFront.Check
  {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) (Σ : Signature)
  (sigop-S : ∀ {c A} → WordName c → (showCanonical c , A) ∈ Fs → (c ∶ declS A) ∈ Σ)
  (nm : Fin s → CanonicalName) (clean : CleanSig S)
  {imps sg : Imports} {polys : PolyCtx} (V : E.View S imps sg polys)
  -- a monomorphic definition in scope: its name, and no type variables
  (h-imp : ∀ {x T} (lk : lookupImport imps x ≡ just T)
         → (nm (E.ImportAt.entryOf (E.View.imported V lk)) ≡ canonical (x ∷ []))
           × (LP.Schema.arity (S LP.!! E.ImportAt.entryOf (E.View.imported V lk)) ≡ 0))
  -- a telescope definition in scope: its name; no type variables exactly when its schema is ground
  (h-poly : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p))
          → nm (E.View.entry V lp) ≡ canonical (x ∷ []))
  (h-ground : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p))
            → TP.Ground sc → LP.Schema.arity (S LP.!! E.View.entry V lp) ≡ 0)
  (h-open : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p))
          → ¬ TP.Ground sc → 0 < LP.Schema.arity (S LP.!! E.View.entry V lp))
  -- …each of its type variables occurs in its type
  (h-occ : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p)) i
         → ST.Occurs i (ptyS (LP.Schema.type (S LP.!! E.View.entry V lp))))
  -- …and an arrow schema is an arrow, its codomain's variables in its domain
  (h-arrow : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p)) {sd sco π′}
           → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco
           → Σ[ X ∈ LP.Ty (LP.Schema.arity (S LP.!! E.View.entry V lp)) ]
             Σ[ Y ∈ LP.Ty (LP.Schema.arity (S LP.!! E.View.entry V lp)) ]
               (LP.Schema.type (S LP.!! E.View.entry V lp) ≡ X LP.⇒[ LG.mk-kind LG.Many π′ ] Y)
               × (∀ i → ST.Occurs i (ptyS Y) → ST.Occurs i (ptyS X)))
  {m : ℕ} (Δ : ST.KCtx m) where

open import Data.Fin using (zero; suc)
open import Data.List using (List)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Data.Maybe using (nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst)

import Once.Internal.Type as LT

import Once.Spec.Type as LT
import Once.Internal.Type.Sub as LS
import Once.Spec.Sub as LS
import Once.Internal.Type.WellFormed as LW
import Once.Spec.Grade as SG
import Once.Spec.Sub as SS
import Once.Spec.Core.Syntax as SC
import Once.Spec.Surface.Syntax as SX
import Once.Internal.Context as LC
open import Once.Internal.Context using (svar)
open import Once.Internal.Syntax using (RawExpr; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Internal.Typing
open import Once.Internal.Typing.Scope using (NamedCtx; mkCtx; classifyAppHead; Binding)
import Data.List.Relation.Unary.Any
import Once.Internal.Core.Syntax S as L
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS; kS)
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.Schema using (defsS; castSub; schS; !!-defsS; InstR; TyR-inst; respects-S; Clean; c-⇒)
open import Once.Adequacy.SpecCore.TermR S
open import Once.Adequacy.SpecFront.Expr
open import Once.Adequacy.SpecFront.Types Δ
open import Once.Adequacy.SpecFront.Terms S {Δ = Δ}
open import Once.Adequacy.SpecFront.Locals Σ S′ nm Δ

import Once.Spec.Surface.Typing Σ S′ nm as SU
import Once.Spec.Core.Derived as SD
open import Once.Adequacy.SpecCore.Prim S using (primS)

private
  module EV = E S

  C : ∀ (n : ℕ) → List Binding → LC.Ctx n → NamedCtx
  C n Γn Γd = mkCtx n Γn Γd imps polys sg

  arity-S : ∀ {s′} (S₀ : LP.Sig Fs s′) (d : Fin s′) → SC.Schema.arity (defsS S₀ SC.!! d) ≡ LP.Schema.arity (S₀ LP.!! d)
  arity-S (S₀ LP.▷ sc) zero    = refl
  arity-S (S₀ LP.▷ sc) (suc d) = arity-S S₀ d

  fin0 : Fin 0 → ⊥
  fin0 ()

------------------------------------------------------------------------
-- What a translated derivation gives
------------------------------------------------------------------------

record Syn {n} (L : SU.Locals m n) (e′ : SX.Expr) (A : LT.Type) (t : L.Tm n) : Set where
  constructor syn
  field
    {A′} : ST.Ty m
    ra   : TyR Δ A A′
    {t′} : SC.Tm S′ m n
    rt   : TmR Δ t t′
    der  : SU._⊢_⇒_↝_ Δ L e′ A′ t′

record Chk {n} (L : SU.Locals m n) (e′ : SX.Expr) (A′ : ST.Ty m) (t : L.Tm n) : Set where
  constructor chk
  field
    {t′} : SC.Tm S′ m n
    rt   : TmR Δ t t′
    der  : SU._⊢_⇐_↝_ Δ L e′ A′ t′

record Dom {n} (L : SU.Locals m n) (e′ : SX.Expr) (A′ : ST.Ty m) (π : LG.Purity) (B : LT.Type) (t : L.Tm n) : Set where
  constructor dom
  field
    {B′} : ST.Ty m
    rb   : TyR Δ B B′
    {t′} : SC.Tm S′ m n
    rt   : TmR Δ t t′
    der  : SU._⊢_⇐_⇒[_]↦_↝_ Δ L e′ A′ (πS π) B′ t′

------------------------------------------------------------------------
-- Heads, and references to definitions
------------------------------------------------------------------------

private
  gen-head : ∀ {g} → g ∈ SU.specialGenerators → classifyAppHead (Once.Internal.Syntax.RResolved (Once.Spec.Name.gen g)) ≡ nothing → ⊥
  gen-head (Data.List.Relation.Unary.Any.here refl) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl)) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl))) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl)))) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl))))) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl)))))) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl))))))) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl)))))))) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl))))))))) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl)))))))))) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl))))))))))) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl)))))))))))) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl))))))))))))) ()
  gen-head (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there ()))))))))))))) _

-- A head the compiler's general application rules take is one the Spec's take.
not-special : ∀ {bound f f′} → classifyAppHead f ≡ nothing → RX bound f f′ → ¬ SU.SpecialHead f′
not-special e (x-res _) (SU.sh-gen g) = gen-head g e
not-special () (x-app (x-res _) _) SU.sh-pair
not-special () (x-app (x-res _) _) SU.sh-compose
not-special () (x-app (x-res _) _) SU.sh-case

-- A reference to a definition with no type variables.
ref0 : ∀ {n} {L : SU.Locals m n} {T} (d : Fin s) {c} → nm d ≡ c → LP.Schema.arity (S LP.!! d) ≡ 0
     → (i : EV.InstanceOf d T) → Syn L (SX.RResolved c) T (L.ref d (proj₁ i))
ref0 d e ar (τ , r , eq) =
  syn (subst (λ X → TyR Δ X (SC.Schema.type (S′ SC.!! d) ST.⟨ castSub S d τ′ ⟩)) eq (ref-type S d (clean d) inst)) (r-ref d inst)
      (SU.s-def d e (castSub S d τ′) (trans (arity-S S d) ar))
  where
    τ′ : ST.TySub (LP.Schema.arity (S LP.!! d)) m
    τ′ i = ⊥-elim (fin0 (subst Fin ar i))
    inst : InstR {Δ = Δ} τ τ′
    inst i = ⊥-elim (fin0 (subst Fin ar i))

-- A variable that occurs in a type: its instance is a part of the instance
-- of the type, so related when that is.
mutual
  occ-R : ∀ {a} {A : LP.Ty a} {τ : LP.GSub a} {X i} → Clean A → ST.Occurs i (ptyS A) → TyR Δ (A LP.⟪ τ ⟫) X
        → Σ[ Y ∈ ST.Ty m ] TyR Δ (τ i) Y
  occ-R Once.Adequacy.SpecCore.Schema.c-var ST.o-var r = _ , r
  occ-R (Once.Adequacy.SpecCore.Schema.c-* a b) (ST.o-*ˡ o) (r-* ra rb) = occ-R a o ra
  occ-R (Once.Adequacy.SpecCore.Schema.c-* a b) (ST.o-*ʳ o) (r-* ra rb) = occ-R b o rb
  occ-R (Once.Adequacy.SpecCore.Schema.c-+ a b) (ST.o-+ˡ o) (r-+ ra rb) = occ-R a o ra
  occ-R (Once.Adequacy.SpecCore.Schema.c-+ a b) (ST.o-+ʳ o) (r-+ ra rb) = occ-R b o rb
  occ-R (c-⇒ a b) (ST.o-⇒ˡ o) (r-⇒ _ ra rb) = occ-R a o ra
  occ-R (c-⇒ a b) (ST.o-⇒ʳ o) (r-⇒ _ ra rb) = occ-R b o rb
  occ-R (Once.Adequacy.SpecCore.Schema.c-μ f) (ST.o-μ o) (r-μ rf) = occF-R f o rf
  occ-R (Once.Adequacy.SpecCore.Schema.c-ν f) (ST.o-ν o) (r-ν _ rf) = occF-R f o rf

  occF-R : ∀ {a} {F : LP.Fun a} {τ : LP.GSub a} {G i} → Once.Adequacy.SpecCore.Schema.CleanF F
         → ST.OccursF i (Once.Adequacy.SpecCore.Schema.pfunS F) → FunR Δ (F LP.⟪ τ ⟫F) G
         → Σ[ Y ∈ ST.Ty m ] TyR Δ (τ i) Y
  occF-R (Once.Adequacy.SpecCore.Schema.c-K a) (ST.o-K o) (r-K ra) = occ-R a o ra
  occF-R (Once.Adequacy.SpecCore.Schema.c-⊕ f g) (ST.o-⊕ˡ o) (r-⊕ rf rg) = occF-R f o rf
  occF-R (Once.Adequacy.SpecCore.Schema.c-⊕ f g) (ST.o-⊕ʳ o) (r-⊕ rf rg) = occF-R g o rg
  occF-R (Once.Adequacy.SpecCore.Schema.c-⊗ f g) (ST.o-⊗ˡ o) (r-⊗ rf rg) = occF-R f o rf
  occF-R (Once.Adequacy.SpecCore.Schema.c-⊗ f g) (ST.o-⊗ʳ o) (r-⊗ rf rg) = occF-R g o rg

-- A reference to a polymorphic definition, at an instance whose type is
-- related: the instance is related, and the Spec's instance has that type.
polyC : ∀ {n} {L : SU.Locals m n} {T X} (d : Fin s) {c} → nm d ≡ c → 0 < LP.Schema.arity (S LP.!! d)
      → (∀ i → ST.Occurs i (ptyS (LP.Schema.type (S LP.!! d))))
      → (i : EV.InstanceOf d T) → TyR Δ T X → Chk L (SX.RResolved c) X (L.ref d (proj₁ i))
polyC {L = L} {X = X} d {c} e pos occ (τ , r , eq) rT =
  chk (r-ref d inst)
      (subst (λ Y → SU._⊢_⇐_↝_ Δ L (SX.RResolved c) Y (SC.ref d (castSub S d τ′))) (sym eqX)
             (SU.c-poly d e (subst (0 <_) (sym (arity-S S d)) pos) (castSub S d τ′) (ref-respects S d r inst)))
  where
    rT′ : TyR Δ (LP.Schema.type (S LP.!! d) LP.⟪ τ ⟫) X
    rT′ = subst (λ Z → TyR Δ Z X) (sym eq) rT
    τ′ : ST.TySub (LP.Schema.arity (S LP.!! d)) m
    τ′ i = proj₁ (occ-R (clean d) (occ i) rT′)
    inst : InstR {Δ = Δ} τ τ′
    inst i = proj₂ (occ-R (clean d) (occ i) rT′)
    eqX : X ≡ SC.Schema.type (S′ SC.!! d) ST.⟨ castSub S d τ′ ⟩
    eqX = TyR-uniqueˢ rT′ (ref-type S d (clean d) inst)

-- A polymorphic arrow reference given its domain: the domain fixes the
-- instance (its codomain's variables occur in it).
private
  castSub-subst : ∀ {s′} (S₀ : LP.Sig Fs s′) (d : Fin s′) (τ : ST.TySub (LP.Schema.arity (S₀ LP.!! d)) m)
                → castSub S₀ d τ ≡ subst (λ sc → ST.TySub (SC.Schema.arity sc) m) (sym (!!-defsS S₀ d)) τ
  castSub-subst (S₀ LP.▷ sc) zero    τ = refl
  castSub-subst (S₀ LP.▷ sc) (suc d) τ = castSub-subst S₀ d τ

  dpoly-at : ∀ {n} {L : SU.Locals m n} {c} (d : Fin s) → nm d ≡ c → (sch : SC.Schema) (e : S′ SC.!! d ≡ sch)
           → 0 < SC.Schema.arity sch
           → ∀ {sd sc π′ A B π} → SC.Schema.type sch ≡ sd SU.⇒⟨ π′ ⟩ sc → (∀ i → ST.Occurs i sc → ST.Occurs i sd)
           → (τ : ST.TySub (SC.Schema.arity sch) m) → ST.Respects (SC.Schema.kinds sch) Δ τ
           → sd ST.⟨ τ ⟩ ≡ A → sc ST.⟨ τ ⟩ ≡ B → π′ SG.⊑π π
           → SU._⊢_⇐_⇒[_]↦_↝_ Δ L (SX.RResolved c) A π B
               (SC.coerce (A SU.⇒⟨ π′ ⟩ B) (A SU.⇒⟨ π ⟩ B) (SC.ref d (subst (λ sc → ST.TySub (SC.Schema.arity sc) m) (sym e) τ)))
  dpoly-at d e′ .(S′ SC.!! d) refl pos te occ τ resp ea eb g = SU.d-poly d e′ pos te occ τ resp ea eb g

  arr-inj : ∀ {A B C D : LT.Type} {k} → (A LT.⇒[ k ] B) ≡ (C LT.⇒[ k ] D) → (A ≡ C) × (B ≡ D)
  arr-inj refl = refl , refl

  clean-⇒ : ∀ {a} {X Y : LP.Ty a} {k} → Clean (X LP.⇒[ k ] Y) → Clean X × Clean Y
  clean-⇒ (c-⇒ x y) = x , y

polyD : ∀ {n} {L : SU.Locals m n} {A B A₀ π π′} (d : Fin s) {c} → nm d ≡ c → 0 < LP.Schema.arity (S LP.!! d)
      → (∀ i → ST.Occurs i (ptyS (LP.Schema.type (S LP.!! d))))
      → (X Y : LP.Ty (LP.Schema.arity (S LP.!! d))) → LP.Schema.type (S LP.!! d) ≡ X LP.⇒[ LG.mk-kind LG.Many π′ ] Y
      → (∀ i → ST.Occurs i (ptyS Y) → ST.Occurs i (ptyS X))
      → (i : EV.InstanceOf d (A LT.⇒[ LG.mk-kind LG.Many π′ ] B)) → TyR Δ A A₀ → π′ Once.Spec.Grade.⊑π π
      → Dom L (SX.RResolved c) A₀ π B
            (L.coerce (A LT.⇒[ LG.mk-kind LG.Many π′ ] B) (A LT.⇒[ LG.mk-kind LG.Many π ] B) (L.ref d (proj₁ i)))
polyD {L = L} {A} {B} {A₀} {π} {π′} d {c} e pos occ X Y te incl (τ , r , eq) rA g =
  dom rb (r-coerce (r-⇒ refl rA rb) (r-⇒ refl rA rb) (r-ref d inst))
      (subst (λ τ₀ → SU._⊢_⇐_⇒[_]↦_↝_ Δ L (SX.RResolved c) A₀ (πS π) B′
                        (SC.coerce (A₀ SU.⇒⟨ πS π′ ⟩ B′) (A₀ SU.⇒⟨ πS π ⟩ B′) (SC.ref d τ₀)))
             (sym (castSub-subst S d τ′))
             (dpoly-at d e (schS (S LP.!! d)) (!!-defsS S d) pos (cong ptyS te) incl τ′ (respects-S r inst) ea refl (⊑π-S g)))
  where
    parts = arr-inj (trans (sym (cong (λ Z → Z LP.⟪ τ ⟫) te)) eq)
    cx = proj₁ (clean-⇒ (subst Clean te (clean d)))
    cy = proj₂ (clean-⇒ (subst Clean te (clean d)))
    rX : TyR Δ (X LP.⟪ τ ⟫) A₀
    rX = subst (λ Z → TyR Δ Z A₀) (sym (proj₁ parts)) rA
    occX : ∀ i → ST.Occurs i (ptyS X)
    occX i = side (subst (ST.Occurs i) (cong ptyS te) (occ i))
      where
        side : ST.Occurs i (ptyS X ST.⇒[ _ ] ptyS Y) → ST.Occurs i (ptyS X)
        side (ST.o-⇒ˡ o) = o
        side (ST.o-⇒ʳ o) = incl i o
    τ′ : ST.TySub (LP.Schema.arity (S LP.!! d)) m
    τ′ i = proj₁ (occ-R cx (occX i) rX)
    inst : InstR {Δ = Δ} τ τ′
    inst i = proj₂ (occ-R cx (occX i) rX)
    B′ : ST.Ty m
    B′ = ptyS Y ST.⟨ τ′ ⟩
    rb : TyR Δ B B′
    rb = subst (λ Z → TyR Δ Z B′) (proj₂ parts) (TyR-inst cy inst)
    ea : ptyS X ST.⟨ τ′ ⟩ ≡ A₀
    ea = TyR-uniqueˢ (TyR-inst cx inst) rX

------------------------------------------------------------------------
-- The translation
------------------------------------------------------------------------

private
  int-is : ∀ {X} → TyR Δ LT.Int X → X ≡ ST.Int
  int-is r-int = refl

  float-is : ∀ {X} → TyR Δ LT.Float X → X ≡ ST.Float
  float-is r-float = refl

  -- a synthesized operand at a base type is the Spec's at it
  atInt : ∀ {n} {L : SU.Locals m n} {e′ t} → Syn L e′ LT.Int t → Σ[ t′ ∈ SC.Tm S′ m n ] (TmR Δ t t′ × SU._⊢_⇒_↝_ Δ L e′ ST.Int t′)
  atInt (syn r-int rt der) = _ , rt , der

  atFloat : ∀ {n} {L : SU.Locals m n} {e′ t} → Syn L e′ LT.Float t → Σ[ t′ ∈ SC.Tm S′ m n ] (TmR Δ t t′ × SU._⊢_⇒_↝_ Δ L e′ ST.Float t′)
  atFloat (syn r-float rt der) = _ , rt , der

  ii : TyR Δ (LT.Int LT.* LT.Int) (ST.Int ST.* ST.Int)
  ii = r-* r-int r-int

  -- the binary operators: the saturated primitive on the pair of operands
  arith : ∀ {n} {L : SU.Locals m n} {op p e₁ e₂ t₁ t₂} → SU.IntArith op (primS p)
        → Syn L e₁ LT.Int t₁ → Syn L e₂ LT.Int t₂ → Syn L (SX.RBinOp op e₁ e₂) LT.Int (L.prim p (L.pair t₁ t₂))
  arith {p = p} ia (syn r-int rt₁ d₁) (syn r-int rt₂ d₂) = syn r-int (r-prim p (r-pair rt₁ rt₂)) (SU.s-arith ia d₁ d₂)

  farith : ∀ {n} {L : SU.Locals m n} {op p e₁ e₂ t₁ t₂} → SU.FloatArith op (primS p)
         → Syn L e₁ LT.Float t₁ → Syn L e₂ LT.Float t₂ → Syn L (SX.RBinOp op e₁ e₂) LT.Float (L.prim p (L.pair t₁ t₂))
  farith {p = p} fa (syn r-float rt₁ d₁) (syn r-float rt₂ d₂) = syn r-float (r-prim p (r-pair rt₁ rt₂)) (SU.s-arith-float fa d₁ d₂)

  farith-il : ∀ {n} {L : SU.Locals m n} {op p e₁ e₂ t₁ t₂} → SU.FloatArith op (primS p)
            → Syn L e₁ LT.Int t₁ → Syn L e₂ LT.Float t₂
            → Syn L (SX.RBinOp op e₁ e₂) LT.Float (L.prim p (L.pair (L.prim L.p-i2f t₁) t₂))
  farith-il {p = p} fa (syn r-int rt₁ d₁) (syn r-float rt₂ d₂) =
    syn r-float (r-prim p (r-pair (r-prim L.p-i2f rt₁) rt₂)) (SU.s-arith-float-il fa d₁ d₂)

  farith-ir : ∀ {n} {L : SU.Locals m n} {op p e₁ e₂ t₁ t₂} → SU.FloatArith op (primS p)
            → Syn L e₁ LT.Float t₁ → Syn L e₂ LT.Int t₂
            → Syn L (SX.RBinOp op e₁ e₂) LT.Float (L.prim p (L.pair t₁ (L.prim L.p-i2f t₂)))
  farith-ir {p = p} fa (syn r-float rt₁ d₁) (syn r-int rt₂ d₂) =
    syn r-float (r-prim p (r-pair rt₁ (r-prim L.p-i2f rt₂))) (SU.s-arith-float-ir fa d₁ d₂)

  cmp : ∀ {n} {L : SU.Locals m n} {op p e₁ e₂ t₁ t₂} → SU.Compare op (primS p)
      → Syn L e₁ LT.Int t₁ → Syn L e₂ LT.Int t₂ → Syn L (SX.RBinOp op e₁ e₂) (LT.Unit LT.+ LT.Unit) (L.prim p (L.pair t₁ t₂))
  cmp {p = p} c (syn r-int rt₁ d₁) (syn r-int rt₂ d₂) = syn (r-+ r-unit r-unit) (r-prim p (r-pair rt₁ rt₂)) (SU.s-compare c d₁ d₂)

mutual
  fwdᵢ : ∀ {n Γn} {Γd : LC.Ctx n} {L : SU.Locals m n} {e A Ψ} (D : C n Γn Γd ⊢ᵢ e ∶ A ⨾ Ψ)
       → LR Γn Γd L → ∀ {e′} → RX (names Γn) e e′ → Syn L e′ A (proj₁ (EV.elabᵢ V D))
  fwdᶜ : ∀ {n Γn} {Γd : LC.Ctx n} {L : SU.Locals m n} {e A Ψ} (D : C n Γn Γd ⊢ᶜ e ∶ A ⨾ Ψ)
       → LR Γn Γd L → ∀ {e′} → RX (names Γn) e e′ → ∀ {A′} → TyR Δ A A′ → Chk L e′ A′ (proj₁ (EV.elabᶜ V D))
  fwdᵈ : ∀ {n Γn} {Γd : LC.Ctx n} {L : SU.Locals m n} {e A B π Ψ} (D : C n Γn Γd ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ)
       → LR Γn Γd L → ∀ {e′} → RX (names Γn) e e′ → ∀ {A′} → TyR Δ A A′ → Dom L e′ A′ π B (proj₁ (EV.elabᵈ V D))

  ----------------------------------------------------------------------
  -- Synthesis
  ----------------------------------------------------------------------

  fwdᵢ (t-int n) lr x-int = syn r-int (r-lit _) (SU.s-int n)
  fwdᵢ (t-float i f l p) lr x-float = syn r-float (r-lit _) (SU.s-float i f l)
  fwdᵢ t-unit lr x-unit = syn r-unit r-unit SU.s-unit
  fwdᵢ t-unit-var lr (x-res _) = syn r-unit r-unit SU.s-unit-g
  fwdᵢ (t-var-local {eV = svar i} lk) lr (x-local _) =
    let (A′ , ra , mem) = lk-R lr i lk in syn ra (r-var i) (SU.s-var mem)
  fwdᵢ {L = L} (t-var-resolved {cn = cn} {T = T} ng wn lk k) lr (x-res _) = res (E.View.declares V lk)
    where
      res : EV.Declared (showCanonical cn) T → Syn L (SX.RResolved cn) T (L.sigop cn T)
      res (EV.declared h g mem) = syn (decl-R k h g) (r-sigop (decl-R k h g)) (SU.s-sigop ng (sigop-S wn mem))
  fwdᵢ (t-var-own _ lk) lr (x-res _) =
    ref0 (E.ImportAt.entryOf (E.View.imported V lk)) (proj₁ (h-imp lk)) (proj₂ (h-imp lk)) (E.ImportAt.instOf (E.View.imported V lk))
  fwdᵢ (t-var-import _ lkl _ _) lr (x-local inb) = ⊥-elim (lk-out lr inb lkl)
  fwdᵢ (t-var-poly-instantiate-infer {g = g} _ _ lp _ refl) lr (x-res _) =
    ref0 (E.View.entry V lp) (h-poly lp) (h-ground lp g) (E.View.ground V lp g)
  fwdᵢ (t-annot rf d) lr (x-annot _ x) =
    let chk rt der = fwdᶜ d lr x (annot-R _ rf) in syn (annot-R _ rf) rt (SU.s-annot der)
  fwdᵢ (t-pair da db) lr (x-pair xa xb) =
    let syn ra rta da′ = fwdᵢ da lr xa ; syn rb rtb db′ = fwdᵢ db lr xb in syn (r-* ra rb) (r-pair rta rtb) (SU.s-pair da′ db′)
  fwdᵢ (t-neg d) lr (x-neg x) =
    let (_ , rt , der) = atInt (fwdᵢ d lr x) in syn r-int (r-prim L.p-neg rt) (SU.s-neg der)
  fwdᵢ (t-neg-float i f l p) lr (x-neg x-float) = syn r-float (r-lit _) (SU.s-neg-float i f l)
  fwdᵢ (t-let {q = q} d₁ d₂) lr (x-let x₁ x₂) =
    let syn r₁ rt₁ d₁′ = fwdᵢ d₁ lr x₁ ; syn r₂ rt₂ d₂′ = fwdᵢ d₂ (lr-▸ lr r₁) x₂
    in syn r₂ (r-let rt₁ rt₂) (SU.s-let (qS q) d₁′ d₂′)
  fwdᵢ (t-case {qL = qL} {qR} ds dl dr J) lr (x-destruct xs xl xr) = case-step (fwdᵢ ds lr xs)
    where
      case-step : Syn _ _ _ _ → Syn _ _ _ _
      case-step (syn (r-+ ra rb) rts ds′) =
        let syn rl rtl dl′ = fwdᵢ dl (lr-▸ lr ra) xl ; syn rr rtr dr′ = fwdᵢ dr (lr-▸ lr rb) xr
            (C′ , rc , J′) = join-S J rl rr
        in syn rc (r-case rts (r-coerce rl rc rtl) (r-coerce rr rc rtr)) (SU.s-case (qS qL) (qS qR) ds′ dl′ dr′ J′)
  fwdᵢ (t-binop-arith {op = OpAdd} _ d₁ d₂) lr (x-binop x₁ x₂) = arith SU.ia-add (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith {op = OpSub} _ d₁ d₂) lr (x-binop x₁ x₂) = arith SU.ia-sub (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith {op = OpMul} _ d₁ d₂) lr (x-binop x₁ x₂) = arith SU.ia-mul (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith {op = OpDiv} _ d₁ d₂) lr (x-binop x₁ x₂) = arith SU.ia-div (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith {op = OpMod} _ d₁ d₂) lr (x-binop x₁ x₂) = arith SU.ia-mod (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith {op = OpLt} () _ _) lr _
  fwdᵢ (t-binop-arith {op = OpLe} () _ _) lr _
  fwdᵢ (t-binop-arith {op = OpGt} () _ _) lr _
  fwdᵢ (t-binop-arith {op = OpGe} () _ _) lr _
  fwdᵢ (t-binop-arith {op = OpEq} () _ _) lr _
  fwdᵢ (t-binop-arith {op = OpNe} () _ _) lr _
  fwdᵢ (t-binop-arith-float {op = OpAdd} _ d₁ d₂) lr (x-binop x₁ x₂) = farith SU.fa-add (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith-float {op = OpSub} _ d₁ d₂) lr (x-binop x₁ x₂) = farith SU.fa-sub (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith-float {op = OpMul} _ d₁ d₂) lr (x-binop x₁ x₂) = farith SU.fa-mul (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith-float {op = OpDiv} _ d₁ d₂) lr (x-binop x₁ x₂) = farith SU.fa-div (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith-float {op = OpMod} () _ _) lr _
  fwdᵢ (t-binop-arith-float {op = OpLt} () _ _) lr _
  fwdᵢ (t-binop-arith-float {op = OpLe} () _ _) lr _
  fwdᵢ (t-binop-arith-float {op = OpGt} () _ _) lr _
  fwdᵢ (t-binop-arith-float {op = OpGe} () _ _) lr _
  fwdᵢ (t-binop-arith-float {op = OpEq} () _ _) lr _
  fwdᵢ (t-binop-arith-float {op = OpNe} () _ _) lr _
  fwdᵢ (t-binop-arith-float-il {op = OpAdd} _ d₁ d₂) lr (x-binop x₁ x₂) = farith-il SU.fa-add (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith-float-il {op = OpSub} _ d₁ d₂) lr (x-binop x₁ x₂) = farith-il SU.fa-sub (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith-float-il {op = OpMul} _ d₁ d₂) lr (x-binop x₁ x₂) = farith-il SU.fa-mul (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith-float-il {op = OpDiv} _ d₁ d₂) lr (x-binop x₁ x₂) = farith-il SU.fa-div (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith-float-il {op = OpMod} () _ _) lr _
  fwdᵢ (t-binop-arith-float-il {op = OpLt} () _ _) lr _
  fwdᵢ (t-binop-arith-float-il {op = OpLe} () _ _) lr _
  fwdᵢ (t-binop-arith-float-il {op = OpGt} () _ _) lr _
  fwdᵢ (t-binop-arith-float-il {op = OpGe} () _ _) lr _
  fwdᵢ (t-binop-arith-float-il {op = OpEq} () _ _) lr _
  fwdᵢ (t-binop-arith-float-il {op = OpNe} () _ _) lr _
  fwdᵢ (t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂) lr (x-binop x₁ x₂) = farith-ir SU.fa-add (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith-float-ir {op = OpSub} _ d₁ d₂) lr (x-binop x₁ x₂) = farith-ir SU.fa-sub (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith-float-ir {op = OpMul} _ d₁ d₂) lr (x-binop x₁ x₂) = farith-ir SU.fa-mul (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂) lr (x-binop x₁ x₂) = farith-ir SU.fa-div (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-arith-float-ir {op = OpMod} () _ _) lr _
  fwdᵢ (t-binop-arith-float-ir {op = OpLt} () _ _) lr _
  fwdᵢ (t-binop-arith-float-ir {op = OpLe} () _ _) lr _
  fwdᵢ (t-binop-arith-float-ir {op = OpGt} () _ _) lr _
  fwdᵢ (t-binop-arith-float-ir {op = OpGe} () _ _) lr _
  fwdᵢ (t-binop-arith-float-ir {op = OpEq} () _ _) lr _
  fwdᵢ (t-binop-arith-float-ir {op = OpNe} () _ _) lr _
  fwdᵢ (t-binop-cmp {op = OpLt} _ d₁ d₂) lr (x-binop x₁ x₂) = cmp SU.cmp-lt (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-cmp {op = OpLe} _ d₁ d₂) lr (x-binop x₁ x₂) = cmp SU.cmp-le (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-cmp {op = OpGt} _ d₁ d₂) lr (x-binop x₁ x₂) = cmp SU.cmp-gt (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-cmp {op = OpGe} _ d₁ d₂) lr (x-binop x₁ x₂) = cmp SU.cmp-ge (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-cmp {op = OpEq} _ d₁ d₂) lr (x-binop x₁ x₂) = cmp SU.cmp-eq (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-cmp {op = OpNe} _ d₁ d₂) lr (x-binop x₁ x₂) = cmp SU.cmp-ne (fwdᵢ d₁ lr x₁) (fwdᵢ d₂ lr x₂)
  fwdᵢ (t-binop-cmp {op = OpAdd} () _ _) lr _
  fwdᵢ (t-binop-cmp {op = OpSub} () _ _) lr _
  fwdᵢ (t-binop-cmp {op = OpMul} () _ _) lr _
  fwdᵢ (t-binop-cmp {op = OpDiv} () _ _) lr _
  fwdᵢ (t-binop-cmp {op = OpMod} () _ _) lr _
  fwdᵢ (t-id-app d) lr (x-app (x-res _) x) =
    let syn ra rt der = fwdᵢ d lr x in syn ra (r-app (idᶜ-R LG.pure ra) rt) (SU.s-id-app der)
  fwdᵢ (t-fst-app d) lr (x-app (x-res _) x) = fst-step (fwdᵢ d lr x)
    where
      fst-step : Syn _ _ _ _ → Syn _ _ _ _
      fst-step (syn (r-* ra rb) rt der) = syn ra (r-app (fstᶜ-R LG.pure ra rb) rt) (SU.s-fst-app der)
  fwdᵢ (t-snd-app d) lr (x-app (x-res _) x) = snd-step (fwdᵢ d lr x)
    where
      snd-step : Syn _ _ _ _ → Syn _ _ _ _
      snd-step (syn (r-* ra rb) rt der) = syn rb (r-app (sndᶜ-R LG.pure ra rb) rt) (SU.s-snd-app der)
  fwdᵢ (t-terminal-app d) lr (x-app (x-res _) x) =
    let syn ra rt der = fwdᵢ d lr x in syn r-unit (r-app (terminalᶜ-R LG.pure ra) rt) (SU.s-terminal-app der)
  fwdᵢ (t-apply-app-infer d) lr (x-app (x-res _) x) = apply-step (fwdᵢ d lr x)
    where
      apply-step : Syn _ _ _ _ → Syn _ _ _ _
      apply-step (syn (r-* (r-⇒ {A′ = A₁} {B′ = B₁} refl ra rb) ra′) rt der) =
        syn rb (r-app (applyᶜ-R ra rb) rt)
            (SU.s-apply-app (subst (λ Z → SU._⊢_⇒_↝_ Δ _ _ ((A₁ SU.⇒⟨ SG.pure ⟩ B₁) ST.* Z) _) (TyR-uniqueˢ ra′ ra) der))
  fwdᵢ (t-apply-eff-app-infer {π = π} {g = g} d) lr (x-app (x-res _) x) = applyEff-step (fwdᵢ d lr x)
    where
      applyEff-step : Syn _ _ _ _ → Syn _ _ _ _
      applyEff-step (syn (r-* (r-⇒ {A′ = A₁} {B′ = B₁} refl ra rb) ra′) rt der) =
        syn (r-⇒ refl r-unit rb) (r-app (applyEffᶜ-R π ra rb) rt)
            (SU.s-apply-eff-app (eff-S g) (subst (λ Z → SU._⊢_⇒_↝_ Δ _ _ ((A₁ SU.⇒⟨ πS π ⟩ B₁) ST.* Z) _) (TyR-uniqueˢ ra′ ra) der))
  fwdᵢ (t-Out-app-infer wf refl d) lr (x-app (x-res _) x) = out-step (fwdᵢ d lr x)
    where
      out-step : Syn _ _ _ _ → Syn _ _ _ _
      out-step (syn (r-ν refl f) rt der) =
        syn (⟦⟧-R f (r-ν refl f)) (r-app (outᶜ-R f) rt) (SU.s-Out-app (wf-S wf f) der)
  fwdᵢ (t-Out-eff-app-infer wf refl d) lr (x-app (x-res _) x) = out-step (fwdᵢ d lr x)
    where
      out-step : Syn _ _ _ _ → Syn _ _ _ _
      out-step (syn (r-ν refl f) rt der) =
        syn (r-⇒ refl r-unit (⟦⟧-R f (r-ν refl f))) (r-app (outActᶜ-R f) rt) (SU.s-Out-act-app (wf-S wf f) der)
  fwdᵢ (t-app nh df dx) lr (x-app xf xx) = app-step (fwdᵢ df lr xf)
    where
      app-step : Syn _ _ _ _ → Syn _ _ _ _
      app-step (syn (r-⇒ refl ra rb) rtf df′) =
        let chk rtx dx′ = fwdᶜ dx lr xx ra in syn rb (r-app rtf rtx) (SU.s-app (not-special nh xf) df′ dx′)
  fwdᵢ (t-effApp {π = π} {g = g} nh df dx) lr (x-app xf xx) = app-step (fwdᵢ df lr xf)
    where
      app-step : Syn _ _ _ _ → Syn _ _ _ _
      app-step (syn (r-⇒ refl ra rb) rtf df′) =
        let chk rtx dx′ = fwdᶜ dx lr xx ra
        in syn (r-⇒ refl r-unit rb) (effAppᶜ-R π rtf rtx) (SU.s-effApp (not-special nh xf) (eff-S g) df′ dx′)
  fwdᵢ (t-app-spine nh dx df) lr (x-app xf xx) =
    let syn rx rtx dx′ = fwdᵢ dx lr xx ; dom rb rtf df′ = fwdᵈ df lr xf rx
    in syn rb (r-app rtf rtx) (SU.s-app-spine (not-special nh xf) dx′ df′)

  ----------------------------------------------------------------------
  -- Checking
  ----------------------------------------------------------------------

  fwdᶜ (t-id-check {π = π}) lr (x-res _) (r-⇒ refl ra ra′) =
    chk (idᶜ-R π ra) (subst (λ Z → SU._⊢_⇐_↝_ Δ _ _ (_ SU.⇒⟨ πS π ⟩ Z) _) (TyR-uniqueˢ ra ra′) SU.c-id)
  fwdᶜ (t-fst-check {π = π}) lr (x-res _) (r-⇒ refl (r-* ra rb) ra′) =
    chk (fstᶜ-R π ra rb) (subst (λ Z → SU._⊢_⇐_↝_ Δ _ _ (_ SU.⇒⟨ πS π ⟩ Z) _) (TyR-uniqueˢ ra ra′) SU.c-fst)
  fwdᶜ (t-snd-check {π = π}) lr (x-res _) (r-⇒ refl (r-* ra rb) rb′) =
    chk (sndᶜ-R π ra rb) (subst (λ Z → SU._⊢_⇐_↝_ Δ _ _ (_ SU.⇒⟨ πS π ⟩ Z) _) (TyR-uniqueˢ rb rb′) SU.c-snd)
  fwdᶜ (t-terminal-morph-check {π = π}) lr (x-res _) (r-⇒ refl ra r-unit) = chk (terminalᶜ-R π ra) SU.c-terminal
  fwdᶜ (t-initial-morph-check {π = π}) lr (x-res _) (r-⇒ refl r-void ra) = chk (initialᶜ-R π ra) SU.c-initial
  fwdᶜ (t-inl-morph-check {π = π}) lr (x-res _) (r-⇒ refl ra (r-+ ra′ rb)) =
    chk (inlᶜ-R π ra rb) (subst (λ Z → SU._⊢_⇐_↝_ Δ _ _ (_ SU.⇒⟨ πS π ⟩ (Z ST.+ _)) _) (TyR-uniqueˢ ra ra′) SU.c-inl)
  fwdᶜ (t-inr-morph-check {π = π}) lr (x-res _) (r-⇒ refl rb (r-+ ra rb′)) =
    chk (inrᶜ-R π ra rb) (subst (λ Z → SU._⊢_⇐_↝_ Δ _ _ (_ SU.⇒⟨ πS π ⟩ (_ ST.+ Z)) _) (TyR-uniqueˢ rb rb′) SU.c-inr)
  fwdᶜ (t-compose-check-g {π = π} dg df) lr (x-app (x-app (x-res _) xf) xg) (r-⇒ refl ra rc) =
    let dom rb rtg dg′ = fwdᵈ dg lr xg ra ; chk rtf df′ = fwdᶜ df lr xf (r-⇒ refl rb rc)
    in chk (composeᶜ-R π ra rtf rtg) (SU.c-compose-g dg′ df′)
  fwdᶜ (t-compose-check-f {π = π} {π′} wf p dg) lr (x-app (x-app (x-res _) xf) xg) (r-⇒ refl ra rc) = comp-step (fwdᵢ wf lr xf)
    where
      comp-step : Syn _ _ _ _ → Chk _ _ _ _
      comp-step (syn (r-⇒ refl rb rc′) rtf df′) =
        let chk rtg dg′ = fwdᶜ dg lr xg (r-⇒ refl ra rb)
        in chk (composeᶜ-R π ra (r-coerce (r-⇒ refl rb rc′) (r-⇒ refl rb rc) rtf) rtg)
               (SU.c-compose-f df′ (sub-S p (r-⇒ refl rb rc′) (r-⇒ refl rb rc)) dg′)
  fwdᶜ (t-case-copair-check {π = π} df dg) lr (x-app (x-app (x-res _) xf) xg) (r-⇒ refl (r-+ ra rb) rc) =
    let chk rtf df′ = fwdᶜ df lr xf (r-⇒ refl ra rc) ; chk rtg dg′ = fwdᶜ dg lr xg (r-⇒ refl rb rc)
    in chk (caseᶜ-R π ra rb rtf rtg) (SU.c-case df′ dg′)
  fwdᶜ (t-pair-morph-check {π = π} df dg) lr (x-app (x-app (x-res _) xf) xg) (r-⇒ refl ra (r-* rb rc)) =
    let chk rtf df′ = fwdᶜ df lr xf (r-⇒ refl ra rb) ; chk rtg dg′ = fwdᶜ dg lr xg (r-⇒ refl ra rc)
    in chk (pairᶜ-R π ra rtf rtg) (SU.c-pair df′ dg′)
  fwdᶜ (t-curry-check {π₀ = π₀} {π} df) lr (x-app (x-res _) xf) (r-⇒ refl ra (r-⇒ refl rb rc)) =
    let chk rtf df′ = fwdᶜ df lr xf (r-⇒ refl (r-* ra rb) rc)
    in chk (curryᶜ-R π₀ π ra rb rtf) (SU.c-curry df′)
  fwdᶜ (t-cata-check {π = π} wf dalg) lr (x-app (x-res _) xa) (r-⇒ refl (r-μ f) ra) =
    let chk rt dalg′ = fwdᶜ dalg lr xa (r-⇒ refl (⟦⟧-R f ra) ra)
    in chk (cataᶜ-R π f rt) (SU.c-cata (wf-S wf f) dalg′)
  fwdᶜ (t-ana-check {π₀ = π₀} {φ = φ} {ua = ua} wf dc) lr (x-app (x-res _) xc) (r-⇒ refl ra (r-ν refl f)) =
    let chk rt dc′ = fwdᶜ dc lr xc (r-⇒ (cong (SG.mk-kind SG.Many) (πS-fin φ)) ra (⟦⟧-R f ra))
    in chk (anaᶜ-R π₀ f ra rt) (SU.c-ana (⊑π-S ua) (wf-S wf f) dc′)
  fwdᶜ (t-loop-check dc) lr (x-app (x-res _) xc) (r-⇒ refl ra rb) =
    let chk rt dc′ = fwdᶜ dc lr xc (r-⇒ refl ra (r-+ rb ra)) in chk (loopᶜ-R ra rt) (SU.c-loop dc′)
  fwdᶜ (t-sub d p) lr x rB =
    let syn rA rt d′ = fwdᵢ d lr x in chk (r-coerce rA rB rt) (SU.c-sub d′ (sub-S p rA rB))
  fwdᶜ (t-lam _ d) lr (x-lam x) (r-⇒ refl ra rb) =
    let chk rt d′ = fwdᶜ d (lr-▸ lr ra) x rb in chk (r-lam ra rt) (SU.c-lam d′)
  fwdᶜ (t-pair-lit-check da db) lr (x-pair xa xb) (r-* ra rb) =
    let chk rta da′ = fwdᶜ da lr xa ra ; chk rtb db′ = fwdᶜ db lr xb rb in chk (r-pair rta rtb) (SU.c-pair-lit da′ db′)
  fwdᶜ (t-In-app-check wf d) lr (x-app (x-res _) x) (r-μ f) =
    let chk rt d′ = fwdᶜ d lr x (⟦⟧-R f (r-μ f)) in chk (r-app (inᶜ-R f) rt) (SU.c-In-app (wf-S wf f) d′)
  fwdᶜ (t-apply-check dp) lr (x-app (x-res _) x) rB = apply-step (fwdᵢ dp lr x)
    where
      apply-step : Syn _ _ _ _ → Chk _ _ _ _
      apply-step (syn (r-* (r-⇒ {A′ = A₁} {B′ = B₁} refl ra rb) ra′) rt der) =
        subst (λ Z → Chk _ _ Z _) (TyR-uniqueˢ rb rB)
          (chk (r-app (applyᶜ-R ra rb) rt)
               (SU.c-apply-app (subst (λ Z → SU._⊢_⇒_↝_ Δ _ _ ((A₁ SU.⇒⟨ SG.pure ⟩ B₁) ST.* Z) _) (TyR-uniqueˢ ra′ ra) der)))
  fwdᶜ (t-inl-app-check d) lr (x-app (x-res _) x) (r-+ ra rb) =
    let chk rt d′ = fwdᶜ d lr x ra in chk (r-app (inlᶜ-R LG.pure ra rb) rt) (SU.c-inl-app d′)
  fwdᶜ (t-inr-app-check d) lr (x-app (x-res _) x) (r-+ ra rb) =
    let chk rt d′ = fwdᶜ d lr x rb in chk (r-app (inrᶜ-R LG.pure ra rb) rt) (SU.c-inr-app d′)
  fwdᶜ (t-initial-app-check d) lr (x-app (x-res _) x) rT =
    let chk rt d′ = fwdᶜ d lr x r-void in chk (r-app (initialᶜ-R LG.pure rT) rt) (SU.c-initial-app d′)
  fwdᶜ (t-var-poly-instantiate _ _ lp ng ins) lr (x-res _) rT =
    polyC (E.View.entry V lp) (h-poly lp) (h-open lp ng) (h-occ lp) (E.View.inst V lp ng ins) rT

  ----------------------------------------------------------------------
  -- An arrow out of a given domain
  ----------------------------------------------------------------------

  fwdᵈ (d-infer {π = π} {π′} w a g) lr x rA = infer-step (fwdᵢ w lr x)
    where
      infer-step : Syn _ _ _ _ → Dom _ _ _ _ _ _
      infer-step (syn (r-⇒ refl rA′ rb) rt der) =
        dom rb (r-coerce (r-⇒ refl rA′ rb) (r-⇒ refl rA rb) rt) (SU.d-infer der (sub-S a rA rA′) (⊑π-S g))
  fwdᵈ (d-poly _ _ lp ng arr cvd ins g) lr (x-res _) rA =
    let (X , Y , te , incl) = h-arrow lp arr cvd
    in polyD (E.View.entry V lp) (h-poly lp) (h-open lp ng) (h-occ lp) X Y te incl (E.View.inst V lp ng ins) rA g
  fwdᵈ (d-lam d) lr (x-lam x) rA =
    let syn rb rt d′ = fwdᵢ d (lr-▸ lr rA) x in dom rb (r-lam rA rt) (SU.d-lam d′)
  fwdᵈ (d-compose {π = π} dg df) lr (x-app (x-app (x-res _) xf) xg) rA =
    let dom rm rtg dg′ = fwdᵈ dg lr xg rA ; dom rb rtf df′ = fwdᵈ df lr xf rm
    in dom rb (composeᶜ-R π rA rtf rtg) (SU.d-compose dg′ df′)
  fwdᵈ (d-id {π = π}) lr (x-res _) rA = dom rA (idᶜ-R π rA) SU.d-id
  fwdᵈ (d-fst {π = π}) lr (x-res _) (r-* ra rb) = dom ra (fstᶜ-R π ra rb) SU.d-fst
  fwdᵈ (d-snd {π = π}) lr (x-res _) (r-* ra rb) = dom rb (sndᶜ-R π ra rb) SU.d-snd
  fwdᵈ (d-terminal {π = π}) lr (x-res _) rA = dom r-unit (terminalᶜ-R π rA) SU.d-terminal
  fwdᵈ (d-initial {π = π}) lr (x-res _) r-void = dom r-void (initialᶜ-R π r-void) SU.d-initial
  fwdᵈ (d-case {π = π} df dg J) lr (x-app (x-app (x-res _) xf) xg) (r-+ ra rb) =
    let dom rcf rtf df′ = fwdᵈ df lr xf ra ; dom rcg rtg dg′ = fwdᵈ dg lr xg rb
        (C′ , rc , J′) = join-S J rcf rcg
    in dom rc (caseᶜ-R π ra rb (r-coerce (r-⇒ refl ra rcf) (r-⇒ refl ra rc) rtf) (r-coerce (r-⇒ refl rb rcg) (r-⇒ refl rb rc) rtg))
           (SU.d-case df′ dg′ J′)
  fwdᵈ (d-pair {π = π} df dg) lr (x-app (x-app (x-res _) xf) xg) rA =
    let dom rb rtf df′ = fwdᵈ df lr xf rA ; dom rc rtg dg′ = fwdᵈ dg lr xg rA
    in dom (r-* rb rc) (pairᶜ-R π rA rtf rtg) (SU.d-pair df′ dg′)
  fwdᵈ (d-cata {π = π} wf dalg) lr (x-app (x-res _) xa) (r-μ f) = cata-step (fwdᵢ dalg lr xa)
    where
      cata-step : Syn _ _ _ _ → Dom _ _ _ _ _ _
      cata-step (syn (r-⇒ refl rl ra) rt der) =
        dom ra (cataᶜ-R π f rt)
            (SU.d-cata (wf-S wf f) (subst (λ Z → SU._⊢_⇒_↝_ Δ _ _ (Z SU.⇒⟨ πS π ⟩ _) _) (TyR-uniqueˢ rl (⟦⟧-R f ra)) der))
