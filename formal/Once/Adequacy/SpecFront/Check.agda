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
--
-- Plan 0.122: the elaborator emits the Spec's core terms; `TyR`/`TmR` are
-- the identity's graphs. A reference's term is the table entry at the
-- instance the compiler's rule names, so its Spec rule is read off the
-- View's entry equation (`refS`/`refC`/`refD`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _<_)
open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Signature using (Signature)
import Once.Spec.Grade as LG
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
import Once.Internal.Elaboration as E
import Once.TypeCheck.View as TView
import Once.Internal.Type.Poly as TP
open import Once.Internal.Typing.Scope using (Imports; PolyCtx; lookupImport; lookupPolyPrefix)

module Once.Adequacy.SpecFront.Check
  (Σ : Signature) {s : ℕ} (S : SC.Defs s) (nm : Fin s → CanonicalName)
  {imps sg : Imports} {polys : PolyCtx} (V : TView.View Σ S imps sg polys)
  -- a monomorphic definition in scope: its name
  (h-imp : ∀ {x T} (lk : lookupImport imps x ≡ just T)
         → nm (TView.ImportAt.entryOf (TView.View.imported V lk)) ≡ canonical (x ∷ []))
  -- a telescope definition in scope: its name; no type variables exactly when its schema is ground
  (h-poly : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p))
          → nm (TView.View.entry V lp) ≡ canonical (x ∷ []))
  (h-ground : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p))
            → TP.Ground sc → SC.Schema.arity (S SC.!! TView.View.entry V lp) ≡ 0)
  (h-open : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p))
          → ¬ TP.Ground sc → 0 < SC.Schema.arity (S SC.!! TView.View.entry V lp))
  -- …and an arrow schema is an arrow, its codomain's variables in its domain
  (h-arrow : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p)) {sd sco π′}
           → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco
           → Σ[ X ∈ ST.Ty (SC.Schema.arity (S SC.!! TView.View.entry V lp)) ]
             Σ[ Y ∈ ST.Ty (SC.Schema.arity (S SC.!! TView.View.entry V lp)) ]
               (SC.Schema.type (S SC.!! TView.View.entry V lp) ≡ X ST.⇒[ LG.mk-kind LG.Many π′ ] Y)
               × (∀ i → ST.Occurs i Y → ST.Occurs i X))
  {m : ℕ} (Δ : ST.KCtx m) where

open import Data.Fin using (zero; suc)
open import Data.List using (List)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Data.Maybe using (nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst)

import Once.Spec.Type as LT
import Once.Spec.Grade as SG
import Once.Spec.Sub as SS
import Once.Spec.Surface.Syntax as SX
import Once.Internal.Context as LC
open import Once.Internal.Context using (svar)
open import Once.Internal.Name using (showCanonical)
open import Once.Internal.Core.Decl using (⌜declS⌝)
open import Once.Internal.Type.Schema using (kinded-instance)
open import Once.Type.Rigid using (ground-kinded)
open import Once.Spec.Surface.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Internal.Syntax using (RawExpr)
open import Once.Internal.Typing
open import Once.Internal.Typing.Scope using (NamedCtx; mkCtx; classifyAppHead; Binding)
import Data.List.Relation.Unary.Any
import Once.Spec.Core.Syntax as L
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS; kS)
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.TermR S
open import Once.Adequacy.SpecFront.Expr
open import Once.Adequacy.SpecFront.Types Δ
open import Once.Adequacy.SpecFront.Terms S {Δ = Δ}
open import Once.Adequacy.SpecFront.Locals Σ S nm Δ
open import Data.Unit using (⊤; tt)
open import Once.TypeCheck.Witness Σ S nm (λ _ → ⊤) (λ _ _ → ⊤) Δ
import Once.Spec.Context as SCx

import Once.Spec.Surface.Typing Σ S nm as SU
import Once.Spec.Core.Derived as SD
open import Once.Adequacy.SpecCore.Prim S using (primS)

private
  module EV = E Σ S
  module VV = TView Σ S

  C : ∀ (n : ℕ) → List (Binding m) → LC.Ctx m n → NamedCtx m
  C n Γn Γd = mkCtx n Γn Γd imps polys sg Δ

------------------------------------------------------------------------
-- What a translated derivation gives
------------------------------------------------------------------------

record Syn {n} (L : SU.Locals m n) (e′ : SX.Expr) (A : ST.Ty m) (t : SC.Tm S m n) (Ψ : SCx.Usage n) : Set where
  constructor syn
  field
    {A′} : ST.Ty m
    ra   : TyR Δ A A′
    {t′} : SC.Tm S m n
    rt   : TmR Δ t t′
    der  : W⇒ L e′ A′ t′ Ψ

record Chk {n} (L : SU.Locals m n) (e′ : SX.Expr) (A′ : ST.Ty m) (t : SC.Tm S m n) (Ψ : SCx.Usage n) : Set where
  constructor chk
  field
    {t′} : SC.Tm S m n
    rt   : TmR Δ t t′
    der  : W⇐ L e′ A′ t′ Ψ

record Dom {n} (L : SU.Locals m n) (e′ : SX.Expr) (A′ : ST.Ty m) (π : LG.Purity) (B : ST.Ty m) (t : SC.Tm S m n) (Ψ : SCx.Usage n) : Set where
  constructor dom
  field
    {B′} : ST.Ty m
    rb   : TyR Δ B B′
    {t′} : SC.Tm S m n
    rt   : TmR Δ t t′
    der  : W↦ L e′ A′ (πS π) B′ t′ Ψ

------------------------------------------------------------------------
-- Heads, and references to definitions
------------------------------------------------------------------------

private
  gen-head : ∀ {g} → g ∈ SU.specialGenerators → classifyAppHead (Once.Spec.Surface.Syntax.RResolved (Once.Spec.Name.gen g)) ≡ nothing → ⊥
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

-- A reference to a table entry: the term the elaborator emits for it is the
-- entry at the instance, once the View's entry equation is read.
module _ {n} {Γd : LC.Ctx m n} {L : SU.Locals m n} where

  private
    Elab : ∀ {Ψ} → ST.Ty m → Set
    Elab {Ψ} A = EV.Elab Δ Γd Ψ A

  retype-tm : ∀ {Ψ A B} (q : A ≡ B) (D : Elab {Ψ} A) → proj₁ (EV.retypeE q D) ≡ proj₁ D
  retype-tm refl D = refl

  syn-retype : ∀ {Ψ A B e′} (q : A ≡ B) (D : Elab {Ψ} A) → Syn L e′ A (proj₁ D) Ψ → Syn L e′ B (proj₁ (EV.retypeE q D)) Ψ
  syn-retype refl D s = s

  chk-retype : ∀ {Ψ A B e′} (q : A ≡ B) (D : Elab {Ψ} A) → Chk L e′ A (proj₁ D) Ψ → Chk L e′ B (proj₁ (EV.retypeE q D)) Ψ
  chk-retype refl D c = c

  -- …with no type variables: synthesized;
  refS : (d : Fin s) {c : CanonicalName} → nm d ≡ c → ∀ {sc} (e : S SC.!! d ≡ sc) τ r
       → SC.Schema.arity (S SC.!! d) ≡ 0
       → Syn L (SX.RResolved c) (SC.Schema.type sc ST.⟨ τ ⟩) (proj₁ (EV.refAt {Δ = Δ} {Γ = Γd} d e τ r)) SCx.zeroUsage
  refS d ne refl τ r ar = syn (tyR _) (tmR _) (w-def d {tt} ne τ ar)

  -- …with some: checked at the instance;
  refC : (d : Fin s) {c : CanonicalName} → nm d ≡ c → ∀ {sc} (e : S SC.!! d ≡ sc) τ r
       → 0 < SC.Schema.arity (S SC.!! d)
       → Chk L (SX.RResolved c) (SC.Schema.type sc ST.⟨ τ ⟩) (proj₁ (EV.refAt {Δ = Δ} {Γ = Γd} d e τ r)) SCx.zeroUsage
  refC d ne refl τ r pos = chk (tmR _) (w-poly d {tt} ne pos τ r)

  -- …and an arrow given its domain.
  private
    ⇒-inj : ∀ {A B C D : ST.Ty m} {k} → (A ST.⇒[ k ] B) ≡ (C ST.⇒[ k ] D) → (A ≡ C) × (B ≡ D)
    ⇒-inj refl = refl , refl

  refD : (d : Fin s) {c : CanonicalName} → nm d ≡ c → ∀ {sc} (e : S SC.!! d ≡ sc) τ r
       → 0 < SC.Schema.arity (S SC.!! d)
       → ∀ {X Y : ST.Ty (SC.Schema.arity (S SC.!! d))} {A B π′ π}
       → SC.Schema.type (S SC.!! d) ≡ X ST.⇒[ LG.mk-kind LG.Many π′ ] Y → (∀ i → ST.Occurs i Y → ST.Occurs i X)
       → (q : SC.Schema.type sc ST.⟨ τ ⟩ ≡ A ST.⇒[ LG.mk-kind LG.Many π′ ] B) → π′ SG.⊑π π
       → Dom L (SX.RResolved c) A π B
             (SC.coerce (A ST.⇒[ LG.mk-kind LG.Many π′ ] B) (A ST.⇒[ LG.mk-kind LG.Many π ] B)
                        (proj₁ (EV.retypeE q (EV.refAt {Δ = Δ} {Γ = Γd} d e τ r)))) SCx.zeroUsage
  refD d ne refl τ r pos {X} {Y} te occ q g =
    subst (λ t → Dom L _ _ _ _ (SC.coerce _ _ t) _) (sym (retype-tm q _))
          (dom (tyR _) (tmR _) (w-poly↦ d {tt} ne pos te occ τ r (proj₁ parts) (proj₂ parts) g))
    where
      parts = ⇒-inj (trans (sym (cong (ST._⟨ τ ⟩) te)) q)

------------------------------------------------------------------------
-- The translation
------------------------------------------------------------------------

private
  int-is : ∀ {X} → TyR Δ LT.Int X → X ≡ ST.Int
  int-is r-int = refl

  float-is : ∀ {X} → TyR Δ LT.Float X → X ≡ ST.Float
  float-is r-float = refl

  -- a synthesized operand at a base type is the Spec's at it
  atInt : ∀ {n} {L : SU.Locals m n} {e′ t Ψ} → Syn L e′ LT.Int t Ψ → Σ[ t′ ∈ SC.Tm S′ m n ] (TmR Δ t t′ × W⇒ L e′ ST.Int t′ Ψ)
  atInt (syn r-int rt der) = _ , rt , der

  atFloat : ∀ {n} {L : SU.Locals m n} {e′ t Ψ} → Syn L e′ LT.Float t Ψ → Σ[ t′ ∈ SC.Tm S′ m n ] (TmR Δ t t′ × W⇒ L e′ ST.Float t′ Ψ)
  atFloat (syn r-float rt der) = _ , rt , der

  ii : TyR Δ (LT.Int LT.* LT.Int) (ST.Int ST.* ST.Int)
  ii = r-* r-int r-int

  -- the binary operators: the saturated primitive on the pair of operands
  arith : ∀ {n} {L : SU.Locals m n} {op p e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} → SU.IntArith op (primS p)
        → Syn L e₁ LT.Int t₁ Ψ₁ → Syn L e₂ LT.Int t₂ Ψ₂ → Syn L (SX.RBinOp op e₁ e₂) LT.Int (L.prim p (L.pair t₁ t₂)) (Ψ₁ SCx.+ᵘ Ψ₂)
  arith {p = p} ia (syn r-int rt₁ d₁) (syn r-int rt₂ d₂) = syn r-int (r-prim p (r-pair rt₁ rt₂)) (w-arith ia d₁ d₂)

  farith : ∀ {n} {L : SU.Locals m n} {op p e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} → SU.FloatArith op (primS p)
         → Syn L e₁ LT.Float t₁ Ψ₁ → Syn L e₂ LT.Float t₂ Ψ₂ → Syn L (SX.RBinOp op e₁ e₂) LT.Float (L.prim p (L.pair t₁ t₂)) (Ψ₁ SCx.+ᵘ Ψ₂)
  farith {p = p} fa (syn r-float rt₁ d₁) (syn r-float rt₂ d₂) = syn r-float (r-prim p (r-pair rt₁ rt₂)) (w-arith-float fa d₁ d₂)

  farith-il : ∀ {n} {L : SU.Locals m n} {op p e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} → SU.FloatArith op (primS p)
            → Syn L e₁ LT.Int t₁ Ψ₁ → Syn L e₂ LT.Float t₂ Ψ₂
            → Syn L (SX.RBinOp op e₁ e₂) LT.Float (L.prim p (L.pair (L.prim L.p-i2f t₁) t₂)) (Ψ₁ SCx.+ᵘ Ψ₂)
  farith-il {p = p} fa (syn r-int rt₁ d₁) (syn r-float rt₂ d₂) =
    syn r-float (r-prim p (r-pair (r-prim L.p-i2f rt₁) rt₂)) (w-arith-float-il fa d₁ d₂)

  farith-ir : ∀ {n} {L : SU.Locals m n} {op p e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} → SU.FloatArith op (primS p)
            → Syn L e₁ LT.Float t₁ Ψ₁ → Syn L e₂ LT.Int t₂ Ψ₂
            → Syn L (SX.RBinOp op e₁ e₂) LT.Float (L.prim p (L.pair t₁ (L.prim L.p-i2f t₂))) (Ψ₁ SCx.+ᵘ Ψ₂)
  farith-ir {p = p} fa (syn r-float rt₁ d₁) (syn r-int rt₂ d₂) =
    syn r-float (r-prim p (r-pair rt₁ (r-prim L.p-i2f rt₂))) (w-arith-float-ir fa d₁ d₂)

  cmp : ∀ {n} {L : SU.Locals m n} {op p e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} → SU.Compare op (primS p)
      → Syn L e₁ LT.Int t₁ Ψ₁ → Syn L e₂ LT.Int t₂ Ψ₂ → Syn L (SX.RBinOp op e₁ e₂) (LT.Unit LT.+ LT.Unit) (L.prim p (L.pair t₁ t₂)) (Ψ₁ SCx.+ᵘ Ψ₂)
  cmp {p = p} c (syn r-int rt₁ d₁) (syn r-int rt₂ d₂) = syn (r-+ r-unit r-unit) (r-prim p (r-pair rt₁ rt₂)) (w-compare c d₁ d₂)

mutual
  fwdᵢ : ∀ {n Γn} {Γd : LC.Ctx m n} {L : SU.Locals m n} {e A Ψ} (D : C n Γn Γd ⊢ᵢ e ∶ A ⨾ Ψ)
       → LR Γn Γd L → ∀ {e′} → RX (names Γn) e e′ → Syn L e′ A (proj₁ (EV.elabᵢ V D)) Ψ
  fwdᶜ : ∀ {n Γn} {Γd : LC.Ctx m n} {L : SU.Locals m n} {e A Ψ} (D : C n Γn Γd ⊢ᶜ e ∶ A ⨾ Ψ)
       → LR Γn Γd L → ∀ {e′} → RX (names Γn) e e′ → ∀ {A′} → TyR Δ A A′ → Chk L e′ A′ (proj₁ (EV.elabᶜ V D)) Ψ
  fwdᵈ : ∀ {n Γn} {Γd : LC.Ctx m n} {L : SU.Locals m n} {e A B π Ψ} (D : C n Γn Γd ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ)
       → LR Γn Γd L → ∀ {e′} → RX (names Γn) e e′ → ∀ {A′} → TyR Δ A A′ → Dom L e′ A′ π B (proj₁ (EV.elabᵈ V D)) Ψ

  ----------------------------------------------------------------------
  -- Synthesis
  ----------------------------------------------------------------------

  fwdᵢ (t-int n) lr x-int = syn r-int (r-lit _) (w-int n)
  fwdᵢ (t-float i f l) lr x-float = syn r-float (r-lit _) (w-float i f l)
  fwdᵢ t-unit lr x-unit = syn r-unit r-unit w-unit
  fwdᵢ t-unit-var lr (x-res _) = syn r-unit r-unit w-unit-g
  fwdᵢ (t-var-local {eV = svar i} lk) lr (x-local _) =
    let (A′ , ra , mem) = lk-R lr i lk in syn ra (r-var i) (w-var mem)
  fwdᵢ {Γd = Γd} {L = L} (t-var-resolved {cn = cn} {T = T} ng wn lk k eq) lr (x-res _) = res (TView.View.declares V lk)
    where
      res : (D : VV.Declared (showCanonical cn) T) → Syn L (SX.RResolved cn) _ (proj₁ (EV.sigE {Δ = Δ} {Γ = Γd} cn wn k D eq)) SCx.zeroUsage
      res (VV.declared h mem) =
        syn (subst (TyR Δ _) (trans eq (sym (⌜declS⌝ k h))) (tyR _)) (tmR _) (w-sigop {ok = tt} ng (mem wn refl) k h)
  fwdᵢ (t-var-own _ lk eq) lr (x-res _) =
    syn-retype (sym eq) _ (refS (TView.ImportAt.entryOf (TView.View.imported V lk)) (h-imp lk) (TView.ImportAt.mono (TView.View.imported V lk)) _ _
                                (cong SC.Schema.arity (TView.ImportAt.mono (TView.View.imported V lk))))
  fwdᵢ (t-var-poly-instantiate-infer {schema = sc} {g = g} _ _ lp _ eq) lr (x-res _) =
    let ki = kinded-instance sc (ground-kinded sc g) in
    syn-retype (sym eq) _ (syn-retype (proj₂ (proj₂ ki)) _
      (refS (TView.View.entry V lp) (h-poly lp) (TView.View.entryIs V lp) (proj₁ ki) (proj₁ (proj₂ ki)) (h-ground lp g)))
  fwdᵢ (t-annot {T = T} d refl) lr (x-annot x) =
    let chk rt der = fwdᶜ d lr x (annot-R {T} _) in syn (annot-R {T} _) rt (w-annot der)
  fwdᵢ (t-pair da db) lr (x-pair xa xb) =
    let syn ra rta da′ = fwdᵢ da lr xa ; syn rb rtb db′ = fwdᵢ db lr xb in syn (r-* ra rb) (r-pair rta rtb) (w-pair da′ db′)
  fwdᵢ (t-neg d) lr (x-neg x) =
    let (_ , rt , der) = atInt (fwdᵢ d lr x) in syn r-int (r-prim L.p-neg rt) (w-neg der)
  fwdᵢ (t-neg-float i f l) lr (x-neg x-float) = syn r-float (r-lit _) (w-neg-float i f l)
  fwdᵢ (t-let {q = q} d₁ d₂) lr (x-let x₁ x₂) =
    let syn r₁ rt₁ d₁′ = fwdᵢ d₁ lr x₁ ; syn r₂ rt₂ d₂′ = fwdᵢ d₂ (lr-▸ lr r₁) x₂
    in syn r₂ (r-let rt₁ rt₂) (w-let (qS q) d₁′ d₂′)
  fwdᵢ (t-case {qL = qL} {qR} ds dl dr J) lr (x-destruct xs xl xr) = case-step (fwdᵢ ds lr xs)
    where
      case-step : Syn _ _ _ _ _ → Syn _ _ _ _ _
      case-step (syn (r-+ ra rb) rts ds′) =
        let syn rl rtl dl′ = fwdᵢ dl (lr-▸ lr ra) xl ; syn rr rtr dr′ = fwdᵢ dr (lr-▸ lr rb) xr
            (C′ , rc , J′) = join-S J rl rr
        in syn rc (r-case rts (r-coerce rl rc rtl) (r-coerce rr rc rtr)) (w-case (qS qL) (qS qR) ds′ dl′ dr′ J′)
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
    let syn ra rt der = fwdᵢ d lr x in syn ra (r-app (idᶜ-R LG.pure ra) rt) (w-id-app der)
  fwdᵢ (t-fst-app d) lr (x-app (x-res _) x) = fst-step (fwdᵢ d lr x)
    where
      fst-step : Syn _ _ _ _ _ → Syn _ _ _ _ _
      fst-step (syn (r-* ra rb) rt der) = syn ra (r-app (fstᶜ-R LG.pure ra rb) rt) (w-fst-app der)
  fwdᵢ (t-snd-app d) lr (x-app (x-res _) x) = snd-step (fwdᵢ d lr x)
    where
      snd-step : Syn _ _ _ _ _ → Syn _ _ _ _ _
      snd-step (syn (r-* ra rb) rt der) = syn rb (r-app (sndᶜ-R LG.pure ra rb) rt) (w-snd-app der)
  fwdᵢ (t-terminal-app d) lr (x-app (x-res _) x) =
    let syn ra rt der = fwdᵢ d lr x in syn r-unit (r-app (terminalᶜ-R LG.pure ra) rt) (w-terminal-app der)
  fwdᵢ (t-apply-app-infer d) lr (x-app (x-res _) x) = apply-step (fwdᵢ d lr x)
    where
      apply-step : Syn _ _ _ _ _ → Syn _ _ _ _ _
      apply-step (syn (r-* (r-⇒ {A′ = A₁} {B′ = B₁} refl ra rb) ra′) rt der) =
        syn rb (r-app (applyᶜ-R ra rb) rt)
            (w-apply-app (subst (λ Z → W⇒ _ _ ((A₁ SU.⇒⟨ SG.pure ⟩ B₁) ST.* Z) _ _) (TyR-uniqueˢ ra′ ra) der))
  fwdᵢ (t-apply-eff-app-infer {π = π} {g = g} d) lr (x-app (x-res _) x) = applyEff-step (fwdᵢ d lr x)
    where
      applyEff-step : Syn _ _ _ _ _ → Syn _ _ _ _ _
      applyEff-step (syn (r-* (r-⇒ {A′ = A₁} {B′ = B₁} refl ra rb) ra′) rt der) =
        syn (r-⇒ refl r-unit rb) (r-app (applyEffᶜ-R π ra rb) rt)
            (w-apply-eff-app (eff-S g) (subst (λ Z → W⇒ _ _ ((A₁ SU.⇒⟨ πS π ⟩ B₁) ST.* Z) _ _) (TyR-uniqueˢ ra′ ra) der))
  fwdᵢ (t-Out-app-infer wf refl d) lr (x-app (x-res _) x) = out-step (fwdᵢ d lr x)
    where
      out-step : Syn _ _ _ _ _ → Syn _ _ _ _ _
      out-step (syn (r-ν refl f) rt der) =
        syn (⟦⟧-R f (r-ν refl f)) (r-app (outᶜ-R f) rt) (w-Out-app (wf-S wf f) der)
  fwdᵢ (t-Out-eff-app-infer wf refl d) lr (x-app (x-res _) x) = out-step (fwdᵢ d lr x)
    where
      out-step : Syn _ _ _ _ _ → Syn _ _ _ _ _
      out-step (syn (r-ν refl f) rt der) =
        syn (r-⇒ refl r-unit (⟦⟧-R f (r-ν refl f))) (r-app (outActᶜ-R f) rt) (w-Out-act-app (wf-S wf f) der)
  fwdᵢ (t-app nh df dx) lr (x-app xf xx) = app-step (fwdᵢ df lr xf)
    where
      app-step : Syn _ _ _ _ _ → Syn _ _ _ _ _
      app-step (syn (r-⇒ refl ra rb) rtf df′) =
        let chk rtx dx′ = fwdᶜ dx lr xx ra in syn rb (r-app rtf rtx) (w-app (not-special nh xf) df′ dx′)
  fwdᵢ (t-effApp {π = π} {g = g} nh df dx) lr (x-app xf xx) = app-step (fwdᵢ df lr xf)
    where
      app-step : Syn _ _ _ _ _ → Syn _ _ _ _ _
      app-step (syn (r-⇒ refl ra rb) rtf df′) =
        let chk rtx dx′ = fwdᶜ dx lr xx ra
        in syn (r-⇒ refl r-unit rb) (effAppᶜ-R π rtf rtx) (w-effApp (not-special nh xf) (eff-S g) df′ dx′)
  fwdᵢ (t-app-spine nh dx df) lr (x-app xf xx) =
    let syn rx rtx dx′ = fwdᵢ dx lr xx ; dom rb rtf df′ = fwdᵈ df lr xf rx
    in syn rb (r-app rtf rtx) (w-app-spine (not-special nh xf) dx′ df′)

  ----------------------------------------------------------------------
  -- Checking
  ----------------------------------------------------------------------

  fwdᶜ (t-id-check {π = π}) lr (x-res _) (r-⇒ refl ra ra′) =
    chk (idᶜ-R π ra) (subst (λ Z → W⇐ _ _ (_ SU.⇒⟨ πS π ⟩ Z) _ _) (TyR-uniqueˢ ra ra′) w-id)
  fwdᶜ (t-fst-check {π = π}) lr (x-res _) (r-⇒ refl (r-* ra rb) ra′) =
    chk (fstᶜ-R π ra rb) (subst (λ Z → W⇐ _ _ (_ SU.⇒⟨ πS π ⟩ Z) _ _) (TyR-uniqueˢ ra ra′) w-fst)
  fwdᶜ (t-snd-check {π = π}) lr (x-res _) (r-⇒ refl (r-* ra rb) rb′) =
    chk (sndᶜ-R π ra rb) (subst (λ Z → W⇐ _ _ (_ SU.⇒⟨ πS π ⟩ Z) _ _) (TyR-uniqueˢ rb rb′) w-snd)
  fwdᶜ (t-terminal-morph-check {π = π}) lr (x-res _) (r-⇒ refl ra r-unit) = chk (terminalᶜ-R π ra) w-terminal
  fwdᶜ (t-initial-morph-check {π = π}) lr (x-res _) (r-⇒ refl r-void ra) = chk (initialᶜ-R π ra) w-initial
  fwdᶜ (t-inl-morph-check {π = π}) lr (x-res _) (r-⇒ refl ra (r-+ ra′ rb)) =
    chk (inlᶜ-R π ra rb) (subst (λ Z → W⇐ _ _ (_ SU.⇒⟨ πS π ⟩ (Z ST.+ _)) _ _) (TyR-uniqueˢ ra ra′) w-inl)
  fwdᶜ (t-inr-morph-check {π = π}) lr (x-res _) (r-⇒ refl rb (r-+ ra rb′)) =
    chk (inrᶜ-R π ra rb) (subst (λ Z → W⇐ _ _ (_ SU.⇒⟨ πS π ⟩ (_ ST.+ Z)) _ _) (TyR-uniqueˢ rb rb′) w-inr)
  fwdᶜ (t-compose-check-g {π = π} dg df) lr (x-app (x-app (x-res _) xf) xg) (r-⇒ refl ra rc) =
    let dom rb rtg dg′ = fwdᵈ dg lr xg ra ; chk rtf df′ = fwdᶜ df lr xf (r-⇒ refl rb rc)
    in chk (composeᶜ-R π ra rtf rtg) (w-compose-g dg′ df′)
  fwdᶜ (t-compose-check-f {π = π} {π′} wf p dg) lr (x-app (x-app (x-res _) xf) xg) (r-⇒ refl ra rc) = comp-step (fwdᵢ wf lr xf)
    where
      comp-step : Syn _ _ _ _ _ → Chk _ _ _ _ _
      comp-step (syn (r-⇒ refl rb rc′) rtf df′) =
        let chk rtg dg′ = fwdᶜ dg lr xg (r-⇒ refl ra rb)
        in chk (composeᶜ-R π ra (r-coerce (r-⇒ refl rb rc′) (r-⇒ refl rb rc) rtf) rtg)
               (w-compose-f df′ (sub-S p (r-⇒ refl rb rc′) (r-⇒ refl rb rc)) dg′)
  fwdᶜ (t-case-copair-check {π = π} df dg) lr (x-app (x-app (x-res _) xf) xg) (r-⇒ refl (r-+ ra rb) rc) =
    let chk rtf df′ = fwdᶜ df lr xf (r-⇒ refl ra rc) ; chk rtg dg′ = fwdᶜ dg lr xg (r-⇒ refl rb rc)
    in chk (caseᶜ-R π ra rb rtf rtg) (w-case′ df′ dg′)
  fwdᶜ (t-pair-morph-check {π = π} df dg) lr (x-app (x-app (x-res _) xf) xg) (r-⇒ refl ra (r-* rb rc)) =
    let chk rtf df′ = fwdᶜ df lr xf (r-⇒ refl ra rb) ; chk rtg dg′ = fwdᶜ dg lr xg (r-⇒ refl ra rc)
    in chk (pairᶜ-R π ra rtf rtg) (w-pair′ df′ dg′)
  fwdᶜ (t-curry-check {π₀ = π₀} {π} df) lr (x-app (x-res _) xf) (r-⇒ refl ra (r-⇒ refl rb rc)) =
    let chk rtf df′ = fwdᶜ df lr xf (r-⇒ refl (r-* ra rb) rc)
    in chk (curryᶜ-R π₀ π ra rb rtf) (w-curry df′)
  fwdᶜ (t-cata-check {π = π} wf dalg) lr (x-app (x-res _) xa) (r-⇒ refl (r-μ f) ra) =
    let chk rt dalg′ = fwdᶜ dalg lr xa (r-⇒ refl (⟦⟧-R f ra) ra)
    in chk (cataᶜ-R π f rt) (w-cata (wf-S wf f) dalg′)
  fwdᶜ (t-ana-check {π₀ = π₀} {φ = φ} {ua = ua} wf dc) lr (x-app (x-res _) xc) (r-⇒ refl ra (r-ν refl f)) =
    let chk rt dc′ = fwdᶜ dc lr xc (r-⇒ (cong (SG.mk-kind SG.Many) (πS-fin φ)) ra (⟦⟧-R f ra))
    in chk (anaᶜ-R π₀ f ra rt) (w-ana (⊑π-S ua) (wf-S wf f) dc′)
  fwdᶜ (t-loop-check dc) lr (x-app (x-res _) xc) (r-⇒ refl ra rb) =
    let chk rt dc′ = fwdᶜ dc lr xc (r-⇒ refl ra (r-+ rb ra)) in chk (loopᶜ-R ra rt) (w-loop dc′)
  fwdᶜ (t-sub d p) lr x rB =
    let syn rA rt d′ = fwdᵢ d lr x in chk (r-coerce rA rB rt) (w-sub d′ (sub-S p rA rB))
  fwdᶜ (t-lam ≤p d) lr (x-lam x) (r-⇒ refl ra rb) =
    let chk rt d′ = fwdᶜ d (lr-▸ lr ra) x rb in chk (r-lam ra rt) (w-lam ≤p d′)
  fwdᶜ (t-pair-lit-check da db) lr (x-pair xa xb) (r-* ra rb) =
    let chk rta da′ = fwdᶜ da lr xa ra ; chk rtb db′ = fwdᶜ db lr xb rb in chk (r-pair rta rtb) (w-pair-lit da′ db′)
  fwdᶜ (t-In-app-check wf d) lr (x-app (x-res _) x) (r-μ f) =
    let chk rt d′ = fwdᶜ d lr x (⟦⟧-R f (r-μ f)) in chk (r-app (inᶜ-R f) rt) (w-In-app (wf-S wf f) d′)
  fwdᶜ (t-apply-check dp) lr (x-app (x-res _) x) rB = apply-step (fwdᵢ dp lr x)
    where
      apply-step : Syn _ _ _ _ _ → Chk _ _ _ _ _
      apply-step (syn (r-* (r-⇒ {A′ = A₁} {B′ = B₁} refl ra rb) ra′) rt der) =
        subst (λ Z → Chk _ _ Z _ _) (TyR-uniqueˢ rb rB)
          (chk (r-app (applyᶜ-R ra rb) rt)
               (w-apply-app′ (subst (λ Z → W⇒ _ _ ((A₁ SU.⇒⟨ SG.pure ⟩ B₁) ST.* Z) _ _) (TyR-uniqueˢ ra′ ra) der)))
  fwdᶜ (t-inl-app-check d) lr (x-app (x-res _) x) (r-+ ra rb) =
    let chk rt d′ = fwdᶜ d lr x ra in chk (r-app (inlᶜ-R LG.pure ra rb) rt) (w-inl-app d′)
  fwdᶜ (t-inr-app-check d) lr (x-app (x-res _) x) (r-+ ra rb) =
    let chk rt d′ = fwdᶜ d lr x rb in chk (r-app (inrᶜ-R LG.pure ra rb) rt) (w-inr-app d′)
  fwdᶜ (t-initial-app-check d) lr (x-app (x-res _) x) rT =
    let chk rt d′ = fwdᶜ d lr x r-void in chk (r-app (initialᶜ-R LG.pure rT) rt) (w-initial-app d′)
  fwdᶜ (t-var-poly-instantiate {schema = sc} _ _ lp ng ins) lr (x-res _) rT =
    let ki = kinded-instance sc ins in
    subst (λ Z → Chk _ _ Z _ _) (TyR-≡ rT)
          (chk-retype (proj₂ (proj₂ ki)) _
            (refC (TView.View.entry V lp) (h-poly lp) (TView.View.entryIs V lp) (proj₁ ki) (proj₁ (proj₂ ki)) (h-open lp ng)))

  ----------------------------------------------------------------------
  -- An arrow out of a given domain
  ----------------------------------------------------------------------

  fwdᵈ (d-infer {π = π} {π′} w a g) lr x rA = infer-step (fwdᵢ w lr x)
    where
      infer-step : Syn _ _ _ _ _ → Dom _ _ _ _ _ _ _
      infer-step (syn (r-⇒ refl rA′ rb) rt der) =
        dom rb (r-coerce (r-⇒ refl rA′ rb) (r-⇒ refl rA rb) rt) (w-infer der (sub-S a rA rA′) (⊑π-S g))
  fwdᵈ (d-poly {schema = sc} _ _ lp ng arr cvd ins g) lr (x-res _) rA =
    let (X , Y , te , incl) = h-arrow lp arr cvd
        ki = kinded-instance sc ins
    in subst (λ Z → Dom _ _ Z _ _ _ _) (TyR-≡ rA)
             (refD (TView.View.entry V lp) (h-poly lp) (TView.View.entryIs V lp) (proj₁ ki) (proj₁ (proj₂ ki)) (h-open lp ng) te incl
                   (proj₂ (proj₂ ki)) g)
  fwdᵈ (d-lam d) lr (x-lam x) rA =
    let syn rb rt d′ = fwdᵢ d (lr-▸ lr rA) x in dom rb (r-lam rA rt) (w-lam↦ d′)
  fwdᵈ (d-compose {π = π} dg df) lr (x-app (x-app (x-res _) xf) xg) rA =
    let dom rm rtg dg′ = fwdᵈ dg lr xg rA ; dom rb rtf df′ = fwdᵈ df lr xf rm
    in dom rb (composeᶜ-R π rA rtf rtg) (w-compose↦ dg′ df′)
  fwdᵈ (d-id {π = π}) lr (x-res _) rA = dom rA (idᶜ-R π rA) w-id↦
  fwdᵈ (d-fst {π = π}) lr (x-res _) (r-* ra rb) = dom ra (fstᶜ-R π ra rb) w-fst↦
  fwdᵈ (d-snd {π = π}) lr (x-res _) (r-* ra rb) = dom rb (sndᶜ-R π ra rb) w-snd↦
  fwdᵈ (d-terminal {π = π}) lr (x-res _) rA = dom r-unit (terminalᶜ-R π rA) w-terminal↦
  fwdᵈ (d-initial {π = π}) lr (x-res _) r-void = dom r-void (initialᶜ-R π r-void) w-initial↦
  fwdᵈ (d-case {π = π} df dg J) lr (x-app (x-app (x-res _) xf) xg) (r-+ ra rb) =
    let dom rcf rtf df′ = fwdᵈ df lr xf ra ; dom rcg rtg dg′ = fwdᵈ dg lr xg rb
        (C′ , rc , J′) = join-S J rcf rcg
    in dom rc (caseᶜ-R π ra rb (r-coerce (r-⇒ refl ra rcf) (r-⇒ refl ra rc) rtf) (r-coerce (r-⇒ refl rb rcg) (r-⇒ refl rb rc) rtg))
           (w-case↦ df′ dg′ J′)
  fwdᵈ (d-pair {π = π} df dg) lr (x-app (x-app (x-res _) xf) xg) rA =
    let dom rb rtf df′ = fwdᵈ df lr xf rA ; dom rc rtg dg′ = fwdᵈ dg lr xg rA
    in dom (r-* rb rc) (pairᶜ-R π rA rtf rtg) (w-pair↦ df′ dg′)
  fwdᵈ (d-cata {π = π} wf dalg) lr (x-app (x-res _) xa) (r-μ f) = cata-step (fwdᵢ dalg lr xa)
    where
      cata-step : Syn _ _ _ _ _ → Dom _ _ _ _ _ _ _
      cata-step (syn (r-⇒ refl rl ra) rt der) =
        dom ra (cataᶜ-R π f rt)
            (w-cata↦ (wf-S wf f) (subst (λ Z → W⇒ _ _ (Z SU.⇒⟨ πS π ⟩ _) _ _) (TyR-uniqueˢ rl (⟦⟧-R f ra)) der))
