-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Completeness — the checker is complete for the Spec's
-- surface typing (plan 0.122 §5.6, plan 0.151).
--
-- An expression the Spec types, with its usage (`TypeCheck.Use`), at a scope's
-- Pack, is accepted by the checker at the same type and usage. By induction on
-- the usage annotation: each rule is the checker's clause for its form, the
-- generators' rows found by the table's deciders (`TableSound`), a name by
-- the lookups its annotation records (`View.InView`, the signature's), and
-- the routes the checker takes by the form (`FormSound`): a head that
-- synthesizes is applied (`s-app`), one that never does is given the
-- argument's type (`s-app-spine`), and `compose` takes `g`'s domain-given
-- route exactly when `g` has a domain-given form.
------------------------------------------------------------------------

module Once.TypeCheck.Completeness where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; ¬_; Dec)
open import Once.Spec.Name using (canonical; own)
import Once.Spec.Grade as LG
import Once.Spec.Type as ST
import Once.Spec.Context as SCx
import Once.Spec.Surface.Syntax as Raw
import Once.Spec.Surface.Type as Rawᵗ
import Once.Spec.Surface.Typing as SUT
import Once.Spec.Surface.Generators as G
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Core.Syntax using (Tm; Schema; schema; _!!_)
open Schema using (arity; kinds; type)
open import Once.TypeCheck.Scope using (NamedCtx; Binding; lookupLocal-go; lookupImport; lookupPolyPrefix;
                                        GenKindView; gk-map; gk-const; gk-comb₁; gk-comb₂; genKindView)
open Binding using (name)
open NamedCtx
import Once.TypeCheck.Scope as Classify
open import Once.Context using (svar)
import Once.TypeCheck.Scoped as Sc
open import Once.TypeCheck.SpecWitness using (Pack; OkOf; OkSOf; pack▸; shape-lo; module At; WC; WI)
open Pack
import Once.TypeCheck.Use as UMod
open import Once.TypeCheck.Elaborate
import Once.TypeCheck.Elaborate as E
open import Once.TypeCheck.ElaborateSound using (checkElabV; inferElabV; checkElab-sound; inferElab-sound)
open import Once.TypeCheck.Completeness.Refs
open import Once.TypeCheck.TableSound using (mapFrom?-complete; mapTo?-complete; mapAt?-complete)
import Once.TypeCheck.FormSound as FS
open import Once.Generators using (fromCodomain?; fromDomain?)
open import Once.Type.SubDecide using (_<:?_; _⊑π?_)
open import Once.Spec.Sub using (_<:ᶜ_)
open import Once.Spec.Core.Derived using (𝕋)
open import Once.Type.Join using (join?-complete)
open import Once.TypeCheck.DeciderComplete using (wfFun?-complete-at; isGround-complete-at; ¬Ground-isGround-inj₂)
open import Once.Core.Decl using (⌜declS⌝)
import Once.TypeCheck.View as TView
open import Once.Type.Closed using (sub0; sub0≡)
open import Once.Type.Core using (wk₀)
open import Once.Type.Instance using (KindedInstance)
open import Once.Type.Schema using (schemaOf; kinded-instance)
import Once.Type.Poly as TP
import Once.Type
open import Once.Type.Rigid using (ground-kinded)
open import Once.Adequacy.SpecFront.SchemaOf using (ground-arity; open-arity; ki-of)
open import Once.TypeCheck.Classify using (lookupPolyPrefix⇒lookupPoly)
import Once.TypeCheck.Error as Error
import Once.Adequacy.SpecFront.Inst as In
import Once.Name

-- A Spec local is the name the checker finds (the converse of
-- `Scoped.Locals.found`).
------------------------------------------------------------------------

module _ {Σ} {s : ℕ} {S} {nm : Fin s → _} {m : ℕ} where
  open Sc.Locals Σ S nm {m}
  open SUT Σ S nm using (_∋_⦂_at_; here; there)

  finds : ∀ {n x A i} {Γn} {Γd : SCx.Ctx m n} {L} → LocalsOf Γn Γd L → L ∋ x ⦂ A at i
        → lookupLocal-go x Γn Γd ≡ just (SCx.lookup Γd i , SCx.singleUse i LG.One , svar i)
  finds {x = x} (lo-▸ {b = b} lo) here with x ≟ name b
  ... | yes _ = refl
  ... | no ¬e = ⊥-elim (¬e refl)
  finds {x = x} (lo-▸ {Γn = Γn} {Γd = Γd} {b = b} lo) (there ne v) with x ≟ name b
  ... | yes e = ⊥-elim (ne e)
  ... | no _ rewrite finds {Γn = Γn} {Γd = Γd} lo v = refl

------------------------------------------------------------------------
-- The judgments at a Pack
------------------------------------------------------------------------

open UMod hiding (_⊢_⇒_↝_; _⊢_⇐_↝_; _⊢_⇐_⇒[_]↦_↝_)

module _ {m} {ctx : NamedCtx m} (P : Pack ctx) where
  Syn : Raw.Expr → ST.Ty m → Tm (S P) m (size ctx) → Set
  Syn = SUT._⊢_⇒_↝_ (Sg P) (S P) (nm P) (kinds ctx) (L P)

  Chk : Raw.Expr → ST.Ty m → Tm (S P) m (size ctx) → Set
  Chk = SUT._⊢_⇐_↝_ (Sg P) (S P) (nm P) (kinds ctx) (L P)

  Dom : Raw.Expr → ST.Ty m → LG.Purity → ST.Ty m → Tm (S P) m (size ctx) → Set
  Dom = SUT._⊢_⇐_⇒[_]↦_↝_ (Sg P) (S P) (nm P) (kinds ctx) (L P)

  U⇒ : ∀ {e A t} → Syn e A t → SCx.Usage (size ctx) → Set
  U⇒ = Use⇒ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx)

  U⇐ : ∀ {e A t} → Chk e A t → SCx.Usage (size ctx) → Set
  U⇐ = Use⇐ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx)

  U↦ : ∀ {e A π B t} → Dom e A π B t → SCx.Usage (size ctx) → Set
  U↦ = Use↦ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx)

------------------------------------------------------------------------
-- References: the entry a name's lookups found, at the checker's type
------------------------------------------------------------------------

import Once.Type.Poly as TP
import Once.Type
open import Data.Unit using (tt)

-- the answer, at an equal type
at-type : ∀ {m} (ctx : NamedCtx m) (e : Raw.Expr) {A A′ : ST.Ty m} {Ψ}
        → A ≡ A′ → (∃[ eE ] ∃[ d ] ∃[ f ] inferElab ctx e ≡ success A Ψ eE d f)
        → ∃[ eE ] ∃[ d ] ∃[ f ] inferElab ctx e ≡ success A′ Ψ eE d f
at-type ctx e refl r = r

at-name : ∀ {m} (ctx : NamedCtx m) {c c′} {A : ST.Ty m} {Ψ}
        → c ≡ c′ → (∃[ eE ] ∃[ d ] ∃[ f ] inferElab ctx (Raw.RResolved c′) ≡ success A Ψ eE d f)
        → ∃[ eE ] ∃[ d ] ∃[ f ] inferElab ctx (Raw.RResolved c) ≡ success A Ψ eE d f
at-name ctx refl r = r

lt0 : 0 < 0 → ⊥
lt0 ()

private
  -- a closed type at any instance
  mono-ty : ∀ {m} {sc T} (e : sc ≡ schema 0 ST.∅ₖ T) (τ : ST.TySub (arity sc) m) → type sc ST.⟨ τ ⟩ ≡ wk₀ T
  mono-ty {T = T} refl τ = sub0 T τ _

  -- a monomorphic entry has no type variables
  mono-arity : ∀ {sc T} → sc ≡ schema 0 ST.∅ₖ T → arity sc ≡ 0
  mono-arity refl = refl

  -- no type variables: a ground schema
  ground-of : ∀ (sc : Rawᵗ.PolyType) → arity (schemaOf sc) ≡ 0 → TP.Ground sc
  ground-of sc a with Once.Type.isGround sc in eq
  ... | inj₁ g  = g
  ... | inj₂ tt = ⊥-elim (lt0 (subst (0 <_) a (open-arity sc (isGround-inj₂→¬Ground sc eq))))

  -- a ground entry's type, at any instance
  ground-ty : ∀ {m} {Δ : ST.KCtx m} {sc′} (sc : Rawᵗ.PolyType) (e : sc′ ≡ schemaOf sc) (g : TP.Ground sc) (τ : ST.TySub (arity sc′) m)
            → type sc′ ST.⟨ τ ⟩ ≡ TP.extractGround sc g
  ground-ty {Δ = Δ} sc refl g τ =
    let K = kinded-instance sc (ground-kinded {Δ = Δ} sc g)
    in trans (sub0≡ (ground-arity sc g) (type (schemaOf sc)) τ _) (proj₂ (proj₂ K))

  -- a kinded instance of the entry's schema
  poly-inst : ∀ {m} {Δ : ST.KCtx m} {sc′} (sc : Rawᵗ.PolyType) (e : sc′ ≡ schemaOf sc) (τ : ST.TySub (arity sc′) m)
            → ST.Respects (kinds sc′) Δ τ → KindedInstance Δ sc (type sc′ ST.⟨ τ ⟩)
  poly-inst {Δ = Δ} sc refl τ r = ki-of {Δ = Δ} sc τ r

-- a checked answer, at an equal type
at-typeC : ∀ {m} (ctx : NamedCtx m) (e : Raw.Expr) {A A′ : ST.Ty m} {Ψ}
         → A ≡ A′ → (∃[ eE ] ∃[ d ] ∃[ f ] checkElab ctx e A ≡ success Ψ eE d f)
         → ∃[ eE ] ∃[ d ] ∃[ f ] checkElab ctx e A′ ≡ success Ψ eE d f
at-typeC ctx e refl r = r

at-nameC : ∀ {m} (ctx : NamedCtx m) {c c′} {A : ST.Ty m} {Ψ}
         → c ≡ c′ → (∃[ eE ] ∃[ d ] ∃[ f ] checkElab ctx (Raw.RResolved c′) A ≡ success Ψ eE d f)
         → ∃[ eE ] ∃[ d ] ∃[ f ] checkElab ctx (Raw.RResolved c) A ≡ success Ψ eE d f
at-nameC ctx refl r = r

-- a closed type, lifted
↑≡wk₀ : ∀ {Σ s S nm m} (T : ST.Type) → SUT.↑ Σ {s} S nm {m} T ≡ wk₀ T
↑≡wk₀ T = sub0 T _ _

-- the Spec's operator classes are the checker's

-- an answer at an equal usage
at-usage : ∀ {m n} {Γ : SCx.Ctx m n} {A : ST.Ty m} {r : E.CheckElabResult Γ A} {Ψ Ψ′}
         → Ψ ≡ Ψ′ → (∃[ eE ] ∃[ d ] ∃[ f ] r ≡ success Ψ eE d f) → ∃[ eE ] ∃[ d ] ∃[ f ] r ≡ success Ψ′ eE d f
at-usage refl x = x

at-nameG : ∀ {m} (ctx : NamedCtx m) {c c′} {A B : ST.Ty m} {π Ψ}
         → c ≡ c′ → (∃[ eE ] ∃[ d ] ∃[ f ] (elabGiven ctx (Raw.RResolved c′) A π) ≡ success B Ψ eE d f)
         → ∃[ eE ] ∃[ d ] ∃[ f ] (elabGiven ctx (Raw.RResolved c) A π) ≡ success B Ψ eE d f
at-nameG ctx refl r = r

head-fails : ∀ {m} {ctx : NamedCtx m} {c c′ err} → c ≡ c′ → inferElab ctx (Raw.RResolved c′) ≡ failure err
           → inferElab ctx (Raw.RResolved c) ≡ failure err
head-fails refl e = e

private
  -- a polymorphic entry is not ground
  open-of : ∀ {sch} (sc : Rawᵗ.PolyType) → sch ≡ schemaOf sc → 0 < arity sch → ¬ TP.Ground sc
  open-of sc refl pos g = lt0 (subst (0 <_) (ground-arity sc g) pos)

  -- its arrow, read in the compiler's schema
  arrow-of : ∀ {m} {Δ : ST.KCtx m} {sch} (sc : Rawᵗ.PolyType) → sch ≡ schemaOf sc
           → ∀ {sd sco π′} → type sch ≡ sd ST.⇒[ LG.mk-kind LG.Many π′ ] sco → (∀ i → ST.Occurs i sco → ST.Occurs i sd)
           → Σ[ sd₀ ∈ Rawᵗ.PolyType ] Σ[ sc₀ ∈ Rawᵗ.PolyType ] TP.ArrowSchema sc sd₀ sc₀ π′ × TP.CodVarsInDom sd₀ sc₀
  arrow-of {Δ = Δ} sc refl {π′ = π′} ty oc = In.arrow-at sc (schemaOf sc) refl ty oc π′ refl

  arr-inst : ∀ {m} {sch : Schema} (τ : ST.TySub (arity sch) m) {sd sco : ST.Ty (arity sch)} {A B : ST.Ty m} {π′}
           → type sch ≡ sd ST.⇒[ LG.mk-kind LG.Many π′ ] sco → sd ST.⟨ τ ⟩ ≡ A → sco ST.⟨ τ ⟩ ≡ B
           → type sch ST.⟨ τ ⟩ ≡ A ST.⇒[ LG.mk-kind LG.Many π′ ] B
  arr-inst τ ty ea eb = trans (cong (ST._⟨ τ ⟩) ty) (Relation.Binary.PropositionalEquality.cong₂ (λ X Y → X ST.⇒[ _ ] Y) ea eb)

-- A polymorphic definition, given its domain.
given-poly-at : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) (x : String) (sc : Rawᵗ.PolyType) {b p}
                → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing
                → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p))
                → 0 < arity (S P !! TView.View.entry (V P) lp)
                → ∀ {sd sco π′ A B π}
                → type (S P !! TView.View.entry (V P) lp) ≡ sd ST.⇒[ LG.mk-kind LG.Many π′ ] sco
                → (∀ i → ST.Occurs i sco → ST.Occurs i sd)
                → (τ : ST.TySub (arity (S P !! TView.View.entry (V P) lp)) m) → ST.Respects (kinds (S P !! TView.View.entry (V P) lp)) (kinds ctx) τ
                → sd ST.⟨ τ ⟩ ≡ A → sco ST.⟨ τ ⟩ ≡ B → π′ LG.⊑π π
                → ∃[ eE ] ∃[ d ] ∃[ f ] (elabGiven ctx (Raw.RResolved (own x)) A π) ≡ success B SCx.zeroUsage eE d f
given-poly-at {ctx = ctx} P x sc {b} {p} ns ni lp pos {A = A} {π = π} ty oc τ r ea eb o
  rewrite poly-head-fails ctx x ns ni lp (open-of sc (TView.View.entryIs (V P) lp) pos) =
    DPoly.from-lookups ctx x A π (Error.UnboundVariable x) ns ni lp (open-of sc (TView.View.entryIs (V P) lp) pos)
      (proj₁ (proj₂ (proj₂ ar))) (proj₂ (proj₂ (proj₂ ar))) (proj₁ ki) (proj₁ (proj₂ ki)) o ki
  where
    ar = arrow-of {Δ = kinds ctx} sc (TView.View.entryIs (V P) lp) ty oc
    ki = subst (KindedInstance (kinds ctx) sc) (arr-inst {sch = S P !! TView.View.entry (V P) lp} τ ty ea eb) (poly-inst {Δ = kinds ctx} sc (TView.View.entryIs (V P) lp) τ r)

------------------------------------------------------------------------
-- The routes the checker takes, by the form
------------------------------------------------------------------------

private
  const-map : ∀ {k} → G.IsConstant k → G.IsMap k → ⊥
  const-map G.is-constant ()
  const-comb : ∀ {k n} → G.IsConstant k → G.IsCombinator n k → ⊥
  const-comb G.is-constant ()
  map-comb : ∀ {k n} → G.IsMap k → G.IsCombinator n k → ⊥
  map-comb G.is-map ()
  comb-12 : ∀ {k} → G.IsCombinator 1 k → G.IsCombinator 2 k → ⊥
  comb-12 G.is-combinator ()

module _ {m} {ctx : NamedCtx m} (P : Pack ctx) where
  private
    module SU = SUT (Sg P) (S P) (nm P)
      using (CheckHead; DomainForm; OwnCheck; PartialCombinator; ch-comb₁; ch-comb₂; ch-lam; ch-map
            ; ch-poly; oc-map; oc-pair; pc-bare; pc-one; s-app; s-app-spine; s-const)
  open SU using (PartialCombinator; CheckHead; OwnCheck)

  -- `s-app`: a head that synthesizes is applied.
  app-route : ∀ {f A t} (x : Raw.Expr) → Syn P f A t → ¬ PartialCombinator f → ¬ CheckHead f
            → (∀ {c} → f ≡ Raw.RResolved c → polyKind ctx c ≡ not-poly)
            → inferElab ctx (Raw.RApp f x) ≡ appOn ctx x (inferElab ctx f)
  app-route {f = Raw.RGen g} x s pc ch hr = gen₀ s
    where
      gen₀ : ∀ {A t} → Syn P (Raw.RGen g) A t → inferElab ctx (Raw.RApp (Raw.RGen g) x) ≡ appOn ctx x (inferElab ctx (Raw.RGen g))
      gen₀ (SU.s-const G.k-unit)    = refl
      gen₀ (SU.s-const G.k-toFloat) = refl
  app-route {f = Raw.RResolved c} x s pc ch hr with polyKind ctx c | hr refl
  ... | .not-poly | refl = refl
  app-route {f = Raw.RApp (Raw.RGen g) a} x s pc ch hr = gen₁ (genKindView g)
    where
      gen₁ : (kv : GenKindView g) → inferAppGen₁ ctx (Raw.RApp (Raw.RGen g) a) g x kv ≡ appOn ctx x (inferElab ctx (Raw.RApp (Raw.RGen g) a))
      gen₁ (gk-map _)    = refl
      gen₁ (gk-const _)  = refl
      gen₁ (gk-comb₁ ic) = ⊥-elim (ch (SU.ch-comb₁ ic))
      gen₁ (gk-comb₂ ic) = ⊥-elim (pc (SU.pc-one ic))
  app-route {f = Raw.RApp (Raw.RApp (Raw.RGen g) a) b} x s pc ch hr = gen₂ (genKindView g)
    where
      gen₂ : (kv : GenKindView g) → inferAppGen₂ ctx (Raw.RApp (Raw.RApp (Raw.RGen g) a) b) g x kv ≡ appOn ctx x (inferElab ctx (Raw.RApp (Raw.RApp (Raw.RGen g) a) b))
      gen₂ (gk-map _)    = refl
      gen₂ (gk-const _)  = refl
      gen₂ (gk-comb₁ _)  = refl
      gen₂ (gk-comb₂ ic) = ⊥-elim (ch (SU.ch-comb₂ ic))
  app-route {f = Raw.RApp (Raw.RApp (Raw.RVar _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp (Raw.RQualified _ _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp (Raw.RResolved _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp (Raw.RApp _ _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp (Raw.RLam _ _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp (Raw.RLet _ _ _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp (Raw.RPair _ _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp (Raw.RDestruct _ _ _ _ _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp Raw.RUnit _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp (Raw.RInt _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp (Raw.RFloat _ _ _ _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp (Raw.RAnnot _ _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp (Raw.RBinOp _ _ _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RApp (Raw.RNeg _) _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RVar _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RQualified _ _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RResolved _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RLam _ _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RLet _ _ _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RPair _ _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RDestruct _ _ _ _ _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp Raw.RUnit _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RInt _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RFloat _ _ _ _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RAnnot _ _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RBinOp _ _ _) _} x s pc ch hr = refl
  app-route {f = Raw.RApp (Raw.RNeg _) _} x s pc ch hr = refl
  app-route {f = (Raw.RVar _)} x s pc ch hr = refl
  app-route {f = (Raw.RLet _ _ _)} x s pc ch hr = refl
  app-route {f = (Raw.RPair _ _)} x s pc ch hr = refl
  app-route {f = (Raw.RDestruct _ _ _ _ _)} x s pc ch hr = refl
  app-route {f = Raw.RUnit} x s pc ch hr = refl
  app-route {f = (Raw.RInt _)} x s pc ch hr = refl
  app-route {f = (Raw.RFloat _ _ _ _)} x s pc ch hr = refl
  app-route {f = (Raw.RAnnot _ _)} x s pc ch hr = refl
  app-route {f = (Raw.RBinOp _ _ _)} x s pc ch hr = refl
  app-route {f = (Raw.RNeg _)} x s pc ch hr = refl

  -- `s-app-spine`: a head that never synthesizes is given the argument's type.
  spine-route : ∀ {f} (x : Raw.Expr) → CheckHead f → (∀ {c} → f ≡ Raw.RResolved c → polyKind ctx c ≢ not-poly)
              → (∀ {g} → f ≢ Raw.RGen g)
              → inferElab ctx (Raw.RApp f x) ≡ inferSpine ctx f (inferElab ctx x)
  spine-route x SU.ch-lam hp ng = refl
  spine-route {f = Raw.RResolved c} x (SU.ch-poly _) hp ng with polyKind ctx c | hp refl
  ... | not-poly   | ne = ⊥-elim (ne refl)
  ... | E.poly-dom | _  = refl
  ... | poly-other | _  = refl
  spine-route x (SU.ch-map _) hp ng = ⊥-elim (ng refl)
  spine-route {f = Raw.RApp (Raw.RGen g) a} x (SU.ch-comb₁ ic) hp ng = gen₁ (genKindView g)
    where
      gen₁ : (kv : GenKindView g) → inferAppGen₁ ctx (Raw.RApp (Raw.RGen g) a) g x kv ≡ inferSpine ctx (Raw.RApp (Raw.RGen g) a) (inferElab ctx x)
      gen₁ (gk-comb₁ _)   = refl
      gen₁ (gk-map im)    = ⊥-elim (map-comb im ic)
      gen₁ (gk-const k)   = ⊥-elim (const-comb k ic)
      gen₁ (gk-comb₂ ic₂) = ⊥-elim (comb-12 ic ic₂)
  spine-route {f = Raw.RApp (Raw.RApp (Raw.RGen g) a) b} x (SU.ch-comb₂ ic) hp ng = gen₂ (genKindView g)
    where
      gen₂ : (kv : GenKindView g) → inferAppGen₂ ctx (Raw.RApp (Raw.RApp (Raw.RGen g) a) b) g x kv ≡ inferSpine ctx (Raw.RApp (Raw.RApp (Raw.RGen g) a) b) (inferElab ctx x)
      gen₂ (gk-comb₂ _)   = refl
      gen₂ (gk-map im)    = ⊥-elim (map-comb im ic)
      gen₂ (gk-const k)   = ⊥-elim (const-comb k ic)
      gen₂ (gk-comb₁ ic₁) = ⊥-elim (comb-12 ic₁ ic)

  -- `d-infer`: a synthesizing term is given its domain through its synthesis.
  private
    res-given : ∀ cn A π (r : InferElabResult (debruijn ctx)) {B Ψ eE d f} → r ≡ success B Ψ eE d f
              → given-res ctx cn A π r ≡ given-infer ctx (Raw.RResolved cn) A π r
    res-given cn A π (success _ _ _ _ _) _ = refl

  given-route : ∀ {e A′ t} (A : ST.Ty m) (π : LG.Purity) → Syn P e A′ t
              → ∀ {B Ψ eE d f} → inferElab ctx e ≡ success B Ψ eE d f
              → elabGiven ctx e A π ≡ given-infer ctx e A π (inferElab ctx e)
  given-route {e = Raw.RGen g} A π s _ = gen₀ s
    where
      gen₀ : ∀ {A′ t} → Syn P (Raw.RGen g) A′ t → elabGiven ctx (Raw.RGen g) A π ≡ given-infer ctx (Raw.RGen g) A π (inferElab ctx (Raw.RGen g))
      gen₀ (SU.s-const G.k-unit)    = refl
      gen₀ (SU.s-const G.k-toFloat) = refl
  given-route {e = Raw.RResolved cn} A π s eq = res-given cn A π (inferElab ctx (Raw.RResolved cn)) eq
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.id) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.compose) _) _} A π (SU.s-app pc _ _ _) _ = ⊥-elim (pc (SU.pc-one G.is-combinator))
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.compose) _) _} A π (SU.s-app-spine (SU.ch-comb₁ ()) _ _) _
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.fst) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.snd) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.terminal) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.pair) _) _} A π (SU.s-app pc _ _ _) _ = ⊥-elim (pc (SU.pc-one G.is-combinator))
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.pair) _) _} A π (SU.s-app-spine (SU.ch-comb₁ ()) _ _) _
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.inl) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.inr) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.initial) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.case) _) _} A π (SU.s-app pc _ _ _) _ = ⊥-elim (pc (SU.pc-one G.is-combinator))
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.case) _) _} A π (SU.s-app-spine (SU.ch-comb₁ ()) _ _) _
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.apply) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.curry) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.In) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.cata) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.Out) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.ana) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.unit) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RGen G.toFloat) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RVar _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RQualified _ _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RResolved _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RApp _ _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RLam _ _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RLet _ _ _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RPair _ _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RDestruct _ _ _ _ _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp Raw.RUnit _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RInt _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RFloat _ _ _ _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RAnnot _ _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RBinOp _ _ _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RApp (Raw.RNeg _) _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.id) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.compose) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.fst) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.snd) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.terminal) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.pair) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.inl) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.inr) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.initial) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.case) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.apply) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.curry) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.In) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.cata) _} A π (SU.s-app pc _ _ _) _ = ⊥-elim (pc (SU.pc-bare G.is-combinator))
  given-route {e = Raw.RApp (Raw.RGen G.cata) _} A π (SU.s-app-spine (SU.ch-map ()) _ _) _
  given-route {e = Raw.RApp (Raw.RGen G.Out) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.ana) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.unit) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RGen G.toFloat) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RVar _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RQualified _ _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RResolved _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RLam _ _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RLet _ _ _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RPair _ _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RDestruct _ _ _ _ _) _} A π s _ = refl
  given-route {e = Raw.RApp Raw.RUnit _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RInt _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RFloat _ _ _ _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RAnnot _ _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RBinOp _ _ _) _} A π s _ = refl
  given-route {e = Raw.RApp (Raw.RNeg _) _} A π s _ = refl
  given-route {e = (Raw.RVar _)} A π s _ = refl
  given-route {e = (Raw.RLet _ _ _)} A π s _ = refl
  given-route {e = (Raw.RPair _ _)} A π s _ = refl
  given-route {e = (Raw.RDestruct _ _ _ _ _)} A π s _ = refl
  given-route {e = Raw.RUnit} A π s _ = refl
  given-route {e = (Raw.RInt _)} A π s _ = refl
  given-route {e = (Raw.RFloat _ _ _ _)} A π s _ = refl
  given-route {e = (Raw.RAnnot _ _)} A π s _ = refl
  given-route {e = (Raw.RBinOp _ _ _)} A π s _ = refl
  given-route {e = (Raw.RNeg _)} A π s _ = refl

  -- `c-sub`: a synthesizing term, converted.
  private
    res-sub : ∀ cn T (r : InferElabResult (debruijn ctx)) {B Ψ eE d f} → r ≡ success B Ψ eE d f
            → checkElabV-RResolved-other ctx cn T r ≡ embedOrSubsume ctx (Raw.RResolved cn) T r
    res-sub cn T (success _ _ _ _ _) _ = refl

  sub-route : ∀ {e A t} (T : ST.Ty m) → Syn P e A t → ¬ OwnCheck e
            → ∀ {B Ψ eE d f} → inferElab ctx e ≡ success B Ψ eE d f
            → checkElab ctx e T ≡ embedOrSubsume ctx e T (inferElab ctx e)
  sub-route {e = Raw.RGen g} T s noc _ = gen₀ s
    where
      gen₀ : ∀ {A t} → Syn P (Raw.RGen g) A t → checkElab ctx (Raw.RGen g) T ≡ embedOrSubsume ctx (Raw.RGen g) T (inferElab ctx (Raw.RGen g))
      gen₀ (SU.s-const G.k-unit)    = refl
      gen₀ (SU.s-const G.k-toFloat) = refl
  sub-route {e = Raw.RResolved cn} T s noc eq = res-sub cn T (inferElab ctx (Raw.RResolved cn)) eq
  sub-route {e = Raw.RPair _ _} T s noc _ = ⊥-elim (noc SU.oc-pair)
  sub-route {e = Raw.RApp (Raw.RGen g) x} T s noc _ = gen′ s
    where
      gen′ : ∀ {A t} → Syn P (Raw.RApp (Raw.RGen g) x) A t → checkElab ctx (Raw.RApp (Raw.RGen g) x) T ≡ embedOrSubsume ctx (Raw.RApp (Raw.RGen g) x) T (inferElab ctx (Raw.RApp (Raw.RGen g) x))
      gen : G.IsMap (G.kind g) → (kv : GenKindView g) → checkAppGen ctx (Raw.RGen g) g x T kv ≡ checkSubApp ctx (Raw.RGen g) x T
      gen′ (SU.s-app _ _ (SU.s-const G.k-toFloat) _) = refl
      gen′ (SU.s-app-spine (SU.ch-map im) _ _) = gen im (genKindView g)
      gen im (gk-map _) with fromCodomain? (G.kind g)
      ... | yes fc = ⊥-elim (noc (SU.oc-map fc))
      ... | no _   = refl
      gen im (gk-const k)  = ⊥-elim (const-map k im)
      gen im (gk-comb₁ ic) = ⊥-elim (map-comb im ic)
      gen im (gk-comb₂ ic) = ⊥-elim (map-comb im ic)
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RGen g) a) x} T s noc _ = gen₁ (genKindView g)
    where
      no2 : ∀ {A t} → Syn P (Raw.RApp (Raw.RApp (Raw.RGen g) a) x) A t → G.IsCombinator 2 (G.kind g) → ⊥
      no2 (SU.s-app pc _ _ _) ic = pc (SU.pc-one ic)
      no2 (SU.s-app-spine (SU.ch-comb₁ ic₁) _ _) ic = comb-12 ic₁ ic
      gen₁ : (kv : GenKindView g) → checkAppGen₁ ctx (Raw.RApp (Raw.RGen g) a) g a x T kv ≡ checkSubApp ctx (Raw.RApp (Raw.RGen g) a) x T
      gen₁ (gk-map _)    = refl
      gen₁ (gk-const _)  = refl
      gen₁ (gk-comb₁ _)  = refl
      gen₁ (gk-comb₂ ic) = ⊥-elim (no2 s ic)
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RVar _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RQualified _ _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RResolved _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RApp _ _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RLam _ _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RLet _ _ _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RPair _ _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RDestruct _ _ _ _ _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp Raw.RUnit _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RInt _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RFloat _ _ _ _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RAnnot _ _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RBinOp _ _ _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RApp (Raw.RNeg _) _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RVar _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RQualified _ _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RResolved _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RLam _ _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RLet _ _ _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RPair _ _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RDestruct _ _ _ _ _) _} T s noc _ = refl
  sub-route {e = Raw.RApp Raw.RUnit _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RInt _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RFloat _ _ _ _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RAnnot _ _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RBinOp _ _ _) _} T s noc _ = refl
  sub-route {e = Raw.RApp (Raw.RNeg _) _} T s noc _ = refl
  sub-route {e = (Raw.RVar _)} T s noc _ = refl
  sub-route {e = (Raw.RLet _ _ _)} T s noc _ = refl
  sub-route {e = (Raw.RDestruct _ _ _ _ _)} T s noc _ = refl
  sub-route {e = Raw.RUnit} T s noc _ = refl
  sub-route {e = (Raw.RInt _)} T s noc _ = refl
  sub-route {e = (Raw.RFloat _ _ _ _)} T s noc _ = refl
  sub-route {e = (Raw.RAnnot _ _)} T s noc _ = refl
  sub-route {e = (Raw.RBinOp _ _ _)} T s noc _ = refl
  sub-route {e = (Raw.RNeg _)} T s noc _ = refl

  -- A synthesizing name is no polymorphic one.
  private
    sig-own : ∀ {T} ls li lp → ls ≡ just T → polyKind-own ls li lp ≡ not-poly
    sig-own .(just _) _ _ refl = refl
    imp-own : ∀ {T} ls li lp → ls ≡ nothing → li ≡ just T → polyKind-own ls li lp ≡ not-poly
    imp-own .nothing .(just _) _ refl refl = refl
    poly-own : ∀ {sc b p} ls li lp → ls ≡ nothing → li ≡ nothing → lp ≡ just (sc , b , p) → TP.Ground sc
             → polyKind-own ls li lp ≡ not-poly
    poly-own {sc = sc} .nothing .nothing .(just _) refl refl refl g with Once.Type.isGround sc | isGround-complete-at sc g
    ... | .(inj₁ g) | refl = refl

    lt0′ : 0 < 0 → ⊥
    lt0′ ()

    ground-at : ∀ {x sc b p} (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p))
              → arity (S P !! TView.View.entry (V P) lp) ≡ 0 → TP.Ground sc
    ground-at {sc = sc} lp a with Once.Type.isGround sc in eq
    ... | inj₁ g  = g
    ... | inj₂ tt = ⊥-elim (lt0′ (subst (0 <_) a (h-open P lp (isGround-inj₂→¬Ground sc eq))))

    sig-notPoly : ∀ c {T} → lookupImport (sig ctx) (Once.Name.showCanonical c) ≡ just T → polyKind ctx c ≡ not-poly
    sig-notPoly (canonical []) _ = refl
    sig-notPoly (own x) lk = sig-own _ _ _ lk
    sig-notPoly (canonical (_ ∷ _ ∷ _)) _ = refl

  name-notPoly : ∀ {c A t Ψ} {d : Syn P (Raw.RResolved c) A t} → U⇒ P d Ψ → polyKind ctx c ≡ not-poly
  name-notPoly (UMod.u-sigop {c = c} {ok = ok} _ _) = sig-notPoly c (proj₁ ok)
  name-notPoly (UMod.u-def {e = e} {ok = TView.iv-imp {x = x} ns lk refl}) =
    subst (λ c′ → polyKind ctx c′ ≡ not-poly) (trans (sym (h-imp P lk)) e) (imp-own _ _ _ ns lk)
  name-notPoly (UMod.u-def {e = e} {a = a} {ok = TView.iv-poly {x = x} ns ni lp refl}) =
    subst (λ c′ → polyKind ctx c′ ≡ not-poly) (trans (sym (h-poly P lp)) e) (poly-own _ _ _ ns ni lp (ground-at lp a))

  ----------------------------------------------------------------------
  -- The rules' last steps, their premises' results in hand
  ----------------------------------------------------------------------

  -- `s-app`, at the arrow's grade.
  app-done : ∀ (x : Raw.Expr) {A B : ST.Ty m} {q} (π : LG.Purity) {Ψ₁ Ψ₂ fE df ff xE dx fx}
           → (cr : E.CheckElabResult (debruijn ctx) A) → cr ≡ success Ψ₂ xE dx fx
           → ∃[ eE ] ∃[ d ] ∃[ f ] appAt ctx x A B q π {Ψ₁} fE df ff cr ≡ success (𝕋 π B) (Ψ₁ SCx.+ᵘ (q SCx.*ᵘ Ψ₂)) eE d f
  app-done x LG.pure _ refl = _ , _ , _ , refl
  app-done x LG.act  _ refl = _ , _ , _ , refl
  app-done x LG.eff  _ refl = _ , _ , _ , refl

  -- `s-app` whole: the head synthesized, the argument checked at its domain.
  app-step : ∀ {f x A B q π tf Ψf fE df ff Ψx xE dx fx} → Syn P f (A ST.⇒[ LG.mk-kind q π ] B) tf
           → ¬ PartialCombinator f → ¬ CheckHead f → (∀ {c} → f ≡ Raw.RResolved c → polyKind ctx c ≡ not-poly)
           → inferElab ctx f ≡ success (A ST.⇒[ LG.mk-kind q π ] B) Ψf fE df ff
           → checkElab ctx x A ≡ success Ψx xE dx fx
           → ∃[ eE ] ∃[ d ] ∃[ fr ] inferElab ctx (Raw.RApp f x) ≡ success (𝕋 π B) (Ψf SCx.+ᵘ (q SCx.*ᵘ Ψx)) eE d fr
  app-step {x = x} {A = A} {B = B} {q = q} {π = π} {Ψf = Ψf} {fE = fE} {df = df} {ff = ff} s pc ch hr eqF eqX =
    let (eE , d , fr , r) = app-done x {B = B} {q = q} π {Ψ₁ = Ψf} {fE = fE} {df = df} {ff = ff} (checkElab ctx x A) eqX
    in eE , d , fr , trans (app-route x s pc ch hr) (trans (cong (appOn ctx x) eqF) r)

  -- `s-app-spine`, the head given the argument's type.
  spine-done : ∀ (f x : Raw.Expr) {X T : ST.Ty m} {Ψx Ψf xE dx fx fE df ff}
             → inferElab ctx x ≡ success X Ψx xE dx fx → elabGiven ctx f X LG.pure ≡ success T Ψf fE df ff
             → ∃[ eE ] ∃[ d ] ∃[ fr ] inferSpine ctx f (inferElab ctx x) ≡ success T (Ψf SCx.+ᵘ (LG.Many SCx.*ᵘ Ψx)) eE d fr
  spine-done f x eqX eqG = _ , _ , _ , trans (cong (inferSpine ctx f) eqX) (cong (spineAt ctx _ _) eqG)

  -- …at a structure map: applied as a morphism.
  map-spine : ∀ {g k X T t Ψx xE dx fx} (x : Raw.Expr) → G.FromDomain (G.kind g)
            → (mo : G.Morphism {S = S P} (kinds ctx) {n = size ctx} g k X LG.pure T t)
            → (∀ {k′ B′} {t′ : Tm (S P) m (size ctx)} → G.Morphism {S = S P} (kinds ctx) {n = size ctx} g k′ X LG.pure B′ t′ → T <:ᶜ B′)
            → inferElab ctx x ≡ success X Ψx xE dx fx
            → ∃[ eE ] ∃[ d ] ∃[ f ] inferElab ctx (Raw.RApp (Raw.RGen g) x) ≡ success T (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψx)) eE d f
  map-spine {g = g} {k = im} x fd mo least eqX with genKindView g
  ... | gk-const k  = ⊥-elim (const-map k im)
  ... | gk-comb₁ ic = ⊥-elim (map-comb im ic)
  ... | gk-comb₂ ic = ⊥-elim (map-comb im ic)
  ... | gk-map _ with fromDomain? (G.kind g)
  ...   | no ¬fd = ⊥-elim (¬fd fd)
  ...   | yes _  = _ , _ , _ , trans (cong (inferMapSpine ctx g) eqX) (cong (inferMapSpine-go ctx g _ _ _) (mapFrom?-complete fd mo least))

  -- `c-map`.
  check-map : ∀ {g k A π B t} (mo : G.Morphism {S = S P} (kinds ctx) {n = size ctx} g k A π B t)
            → ∃[ eE ] ∃[ d ] ∃[ f ] checkElab ctx (Raw.RGen g) (A ST.⇒[ LG.mk-kind LG.Many π ] B) ≡ success SCx.zeroUsage eE d f
  check-map {g = g} {k = im} {A = A} {π = π} {B = B} mo with genKindView g
  ... | gk-map _    = _ , _ , _ , cong (checkMapAt-go ctx g A π B) (mapAt?-complete mo)
  ... | gk-const k  = ⊥-elim (const-map k im)
  ... | gk-comb₁ ic = ⊥-elim (map-comb im ic)
  ... | gk-comb₂ ic = ⊥-elim (map-comb im ic)

  -- `c-map-app`.
  check-map-app : ∀ {g k A B t Ψ xE dx fx} (x : Raw.Expr) → G.FromCodomain (G.kind g)
                → (mo : G.Morphism {S = S P} (kinds ctx) {n = size ctx} g k A LG.pure B t)
                → checkElab ctx x A ≡ success Ψ xE dx fx
                → ∃[ eE ] ∃[ d ] ∃[ f ] checkElab ctx (Raw.RApp (Raw.RGen g) x) B ≡ success (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) eE d f
  check-map-app {g = g} {k = im} {A = A} {B = B} x fc mo eqX with genKindView g
  ... | gk-const k  = ⊥-elim (const-map k im)
  ... | gk-comb₁ ic = ⊥-elim (map-comb im ic)
  ... | gk-comb₂ ic = ⊥-elim (map-comb im ic)
  ... | gk-map _ with fromCodomain? (G.kind g)
  ...   | no ¬fc = ⊥-elim (¬fc fc)
  ...   | yes _ rewrite mapTo?-complete fc mo with checkElab ctx x A | eqX
  ...     | _ | refl = _ , _ , _ , refl

  -- `d-map`.
  given-map : ∀ {g k A π B t} (π′ : LG.Purity) → G.FromDomain (G.kind g)
            → (mo : G.Morphism {S = S P} (kinds ctx) {n = size ctx} g k A π B t)
            → (∀ {k′ B′} {t′ : Tm (S P) m (size ctx)} → G.Morphism {S = S P} (kinds ctx) {n = size ctx} g k′ A π B′ t′ → B <:ᶜ B′)
            → π′ ≡ π
            → ∃[ eE ] ∃[ d ] ∃[ f ] elabGiven ctx (Raw.RGen g) A π′ ≡ success B SCx.zeroUsage eE d f
  given-map {g = g} {k = im} {A = A} π′ fd mo least refl with genKindView g
  ... | gk-map _    = _ , _ , _ , cong (givenMap ctx g A π′) (mapFrom?-complete fd mo least)
  ... | gk-const k  = ⊥-elim (const-map k im)
  ... | gk-comb₁ ic = ⊥-elim (map-comb im ic)
  ... | gk-comb₂ ic = ⊥-elim (map-comb im ic)

  -- `c-compose-g`: `g` has a domain-given form, so the checker takes its route.
  compose-g-done : ∀ (f g : Raw.Expr) {A B C : ST.Ty m} {π} {Ψ₁ Ψ₂ fE df ff gE dg fg}
                 → SU.DomainForm g
                 → elabGiven ctx g A π ≡ success B Ψ₂ gE dg fg
                 → checkElab ctx f (B ST.⇒[ LG.mk-kind LG.Many π ] C) ≡ success Ψ₁ fE df ff
                 → ∃[ eE ] ∃[ d ] ∃[ fr ] checkElab ctx (Raw.RApp (Raw.RApp (Raw.RGen G.compose) f) g) (A ST.⇒[ LG.mk-kind LG.Many π ] C)
                                          ≡ success (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂)) eE d fr
  compose-g-done f g {A} {B} {C} {π} dfg eqG eqF with domainForm? ctx g in eD
  ... | false = ⊥-elim (FS.domainForm-false P g eD dfg)
  ... | true with elabGiven ctx g A π | eqG
  ...   | _ | refl with checkElab ctx f (B ST.⇒[ LG.mk-kind LG.Many π ] C) | eqF
  ...     | _ | refl = _ , _ , _ , refl

  -- `c-compose-f`: `g` has none, so the checker reads the middle off `f`.
  compose-f-done : ∀ (f g : Raw.Expr) {A B C C′ : ST.Ty m} {π π′} {Ψ₁ Ψ₂ fE df ff gE dg fg} {tg}
                 → ¬ SU.DomainForm g
                 → (dgd : Chk P g (A ST.⇒[ LG.mk-kind LG.Many π ] B) tg) → U⇐ P dgd Ψ₂
                 → inferElab ctx f ≡ success (B ST.⇒[ LG.mk-kind LG.Many π′ ] C′) Ψ₁ fE df ff
                 → (B ST.⇒[ LG.mk-kind LG.Many π′ ] C′) <: (B ST.⇒[ LG.mk-kind LG.Many π ] C)
                 → checkElab ctx g (A ST.⇒[ LG.mk-kind LG.Many π ] B) ≡ success Ψ₂ gE dg fg
                 → ∃[ eE ] ∃[ d ] ∃[ fr ] checkElab ctx (Raw.RApp (Raw.RApp (Raw.RGen G.compose) f) g) (A ST.⇒[ LG.mk-kind LG.Many π ] C)
                                          ≡ success (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂)) eE d fr
  compose-f-done f g {A} {B} {C} {C′} {π} {π′} ndf dgd ug eqF p eqG with domainForm? ctx g in eD
  ... | true = ⊥-elim (ndf (FS.domainForm-true-chk P g eD dgd ug))
  ... | false with inferElab ctx f | eqF
  ...   | _ | refl with (B ST.⇒[ LG.mk-kind LG.Many π′ ] C′) <:? (B ST.⇒[ LG.mk-kind LG.Many π ] C)
  ...     | no ¬p = ⊥-elim (¬p p)
  ...     | yes _ with checkElab ctx g (A ST.⇒[ LG.mk-kind LG.Many π ] B) | eqG
  ...       | _ | refl = _ , _ , _ , refl

  -- `c-sub`: the decided conversion.
  private
    sub-dec : ∀ (e : Raw.Expr) (T : ST.Ty m) {A : ST.Ty m} {Ψ eE d f} (dc : Dec (A <: T)) → A <: T
            → ∃[ eE′ ] ∃[ d′ ] ∃[ f′ ] embedOrSubsume-dec ctx e {Ψ = Ψ} T A eE d f dc ≡ success Ψ eE′ d′ f′
    sub-dec e T (yes _) _ = _ , _ , _ , refl
    sub-dec e T (no ¬p) p = ⊥-elim (¬p p)

  sub-done : ∀ {e A t} (T : ST.Ty m) → Syn P e A t → ¬ OwnCheck e → ∀ {Ψ eE d f} → inferElab ctx e ≡ success A Ψ eE d f → A <: T
           → ∃[ eE′ ] ∃[ d′ ] ∃[ f′ ] checkElab ctx e T ≡ success Ψ eE′ d′ f′
  sub-done {e = e} {A = A} T s noc eq p with sub-route T s noc eq
  ... | er rewrite eq = let (a , b , c , r) = sub-dec e T (A <:? T) p in a , b , c , trans er r

  -- `d-cata`: the algebra synthesized, converted.
  given-cata-done : ∀ (alg : Raw.Expr) {F : ST.Fun m} {A₁ A : ST.Ty m} {π′ π} {Ψ eE d f}
                  → (w : ST.WFFun (kinds ctx) F) → ST.⟦ F ⟧F A <: A₁ → π′ LG.⊑π π
                  → inferElab ctx alg ≡ success (A₁ ST.⇒[ LG.mk-kind LG.Many π′ ] A) Ψ eE d f
                  → ∃[ eE′ ] ∃[ d′ ] ∃[ f′ ] elabGiven ctx (Raw.RApp (Raw.RGen G.cata) alg) (ST.μ F) π ≡ success A (LG.Many SCx.*ᵘ Ψ) eE′ d′ f′
  given-cata-done alg {F} {A₁} {A} {π′} {π} w p o eq rewrite wfFun?-complete-at w | eq
    with ST.⟦ F ⟧F A <:? A₁ | π′ ⊑π? π
  ... | yes _ | yes _ = _ , _ , _ , refl
  ... | no ¬p | _     = ⊥-elim (¬p p)
  ... | yes _ | no ¬o = ⊥-elim (¬o o)


------------------------------------------------------------------------
-- The induction
------------------------------------------------------------------------

-- A result equation lifts to the result paired with its soundness.
pairUp : ∀ {A : Set} {B : A → Set} {a a′ : A} (b : B a) (eq : a ≡ a′) → (a , b) ≡ (a′ , subst B eq b)
pairUp b refl = refl

mutual
  infer-completeS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e A t Ψ} {d : Syn P e A t}
                  → U⇒ P d Ψ → ∃[ eE ] ∃[ dd ] ∃[ f ] inferElab ctx e ≡ success A Ψ eE dd f
  infer-completeS P u-int = _ , _ , _ , refl
  infer-completeS P u-float = _ , _ , _ , refl
  infer-completeS P u-unit = _ , _ , _ , refl
  infer-completeS P (u-const {c = G.k-unit}) = _ , _ , _ , refl
  infer-completeS P (u-const {c = G.k-toFloat}) = _ , _ , _ , refl
  infer-completeS {ctx = ctx} P (u-var {x = x} {v = v}) =
    at-type ctx (Raw.RVar x) (UMod.lookup-shape (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) (shape-lo (lr P)) v)
            (infer-complete-RVar-local {ctx = ctx} x (finds (lr P) v))
  infer-completeS {ctx = ctx} P (u-sigop {c = c} {ok = ok} k h) =
    at-type ctx (Raw.RResolved c) (sym (⌜declS⌝ k h)) (infer-complete-RResolved {ctx = ctx} (proj₂ ok) (proj₁ ok) k)

  infer-completeS {ctx = ctx} P (u-def {c = c} {e = e} {τ = τ} {ok = TView.iv-imp ns lk refl}) =
    at-type ctx (Raw.RResolved c) (sym (mono-ty (TView.ImportAt.mono (TView.View.imported (V P) lk)) τ))
            (at-name ctx (trans (sym e) (h-imp P lk)) (infer-complete-RResolved-own {ctx = ctx} ns lk))
  infer-completeS {ctx = ctx} P (u-def {c = c} {e = e} {τ = τ} {a = a} {ok = TView.iv-poly {x = x} {sc = sc} ns ni lp refl}) =
    let g = ground-of sc (trans (cong arity (sym (TView.View.entryIs (V P) lp))) a) in
    at-type ctx (Raw.RResolved c) (sym (ground-ty {Δ = kinds ctx} sc (TView.View.entryIs (V P) lp) g τ))
            (at-name ctx (trans (sym e) (h-poly P lp))
                     (checkElab-fallback-RVar-poly-infer {ctx = ctx} x ns ni (lookupPolyPrefix⇒lookupPoly (polys ctx) x lp)
                        (isGround-complete-at sc g)))
  infer-completeS {ctx = ctx} P (u-annot {e = e} {T = T} u) =
    at-type ctx (Raw.RAnnot e T) (sym (↑≡wk₀ {Sg P} {_} {S P} {nm P} T)) (infer-complete-RAnnot {ctx = ctx} e T (proj₂ (proj₂ (proj₂ (at-typeC ctx e (↑≡wk₀ {Sg P} {_} {S P} {nm P} T) (check-completeS P u))))))
  infer-completeS P (u-pair {a = a} {b = b} ua ub) =
    let (_ , _ , _ , eq₁) = infer-completeS P ua ; (_ , _ , _ , eq₂) = infer-completeS P ub
    in infer-complete-RPair a b eq₁ eq₂
  infer-completeS P (u-neg {e = e} {A = A} {h = h} u) = let (_ , _ , _ , eq) = infer-completeS P u in infer-complete-RNeg e A h eq
  infer-completeS P (u-let {x = x} {e₁ = e₁} {e₂ = e₂} {A = A} u₁ u₂) =
    let (_ , _ , _ , eq₁) = infer-completeS P u₁ ; (_ , _ , _ , eq₂) = infer-completeS (pack▸ x A P) u₂
    in infer-complete-RLet x e₁ e₂ eq₁ eq₂
  infer-completeS P (u-case {e = sc} {xl = xl} {el = el} {xr = xr} {er = er} {A = A} {B = B} {Cl = Cl} {Cr = Cr} {C = C} {j = j} us ul ur) =
    let (_ , _ , _ , eqS) = infer-completeS P us
        (_ , _ , _ , eqL) = infer-completeS (pack▸ xl A P) ul
        (_ , _ , _ , eqR) = infer-completeS (pack▸ xr B P) ur
    in infer-complete-RDestruct sc xl el xr er Cl Cr C j eqS eqL eqR
  infer-completeS P (u-binop {op = op} {e₁ = e₁} {e₂ = e₂} {A = A} {h = h} u₁ u₂) =
    let (_ , _ , _ , eq₁) = infer-completeS P u₁ ; (_ , _ , _ , eq₂) = infer-completeS P u₂
    in infer-complete-RBinOp op A h e₁ e₂ eq₁ eq₂
  infer-completeS {ctx = ctx} P (u-app {f = f} {x = x} {A = A} {B = B} {q = q} {π = π} {pc = pc} {ch = ch} {df = df} {Ψ₁ = Ψ₁} uf ux) =
    let (fE , d₁ , f₁ , eqF) = infer-completeS P uf
        (_ , _ , _ , eqX) = check-completeS P ux
        (eE , d , fr , r) = app-done P x {B = B} {q = q} π {Ψ₁ = Ψ₁} {fE = fE} {df = d₁} {ff = f₁} (checkElab ctx x A) eqX
    in eE , d , fr , trans (app-route P x df pc ch (λ { refl → name-notPoly P uf })) (trans (cong (appOn ctx x) eqF) r)
  infer-completeS P (u-app-spine {ch = ch} ux (u-infer {d = d} w)) = ⊥-elim (At.synth-noCH P d w ch)
  infer-completeS P (u-app-spine {x = x} ux (u-map {fd = fd} {mo = mo} {least = least})) =
    map-spine P x fd mo least (proj₂ (proj₂ (proj₂ (infer-completeS P ux))))
  infer-completeS {ctx = ctx} P (u-app-spine {f = f} {x = x} {ch = ch} ux uf@(u-poly {e = e} {a = pos} {ok = ok})) =
    let (eE , d , fr , r) = spine-done P f x (proj₂ (proj₂ (proj₂ (infer-completeS P ux)))) (proj₂ (proj₂ (proj₂ (given-completeS P uf))))
    in eE , d , fr , trans (spine-route P x ch (λ { refl → FS.ok-poly P ok e pos }) (λ ())) r
  infer-completeS {ctx = ctx} P (u-app-spine {f = f} {x = x} {ch = ch} ux uf@(u-lam _)) = spine-by P f x ch ux uf (λ ()) (λ ())
  infer-completeS {ctx = ctx} P (u-app-spine {f = f} {x = x} {ch = ch} ux uf@(u-compose _ _)) = spine-by P f x ch ux uf (λ ()) (λ ())
  infer-completeS {ctx = ctx} P (u-app-spine {f = f} {x = x} {ch = ch} ux uf@(u-case _ _)) = spine-by P f x ch ux uf (λ ()) (λ ())
  infer-completeS {ctx = ctx} P (u-app-spine {f = f} {x = x} {ch = ch} ux uf@(u-pair _ _)) = spine-by P f x ch ux uf (λ ()) (λ ())
  infer-completeS {ctx = ctx} P (u-app-spine {f = f} {x = x} {ch = ch} ux uf@(u-cata _)) = spine-by P f x ch ux uf (λ ()) (λ ())

  -- the spine at a head that is neither a name nor a generator
  spine-by : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) (f x : Raw.Expr) {X T tx tf Ψx Ψf}
               {dx : Syn P x X tx} {df : Dom P f X LG.pure T tf}
           → SUT.CheckHead (Sg P) (S P) (nm P) f → U⇒ P dx Ψx → U↦ P df Ψf
           → (∀ {c} → f ≢ Raw.RResolved c) → (∀ {g} → f ≢ Raw.RGen g)
           → ∃[ eE ] ∃[ d ] ∃[ fr ] inferElab ctx (Raw.RApp f x) ≡ success T (Ψf SCx.+ᵘ (LG.Many SCx.*ᵘ Ψx)) eE d fr
  spine-by P f x ch ux uf nr ng =
    let (eE , d , fr , r) = spine-done P f x (proj₂ (proj₂ (proj₂ (infer-completeS P ux)))) (proj₂ (proj₂ (proj₂ (given-completeS P uf))))
    in eE , d , fr , trans (spine-route P x ch (λ e → ⊥-elim (nr e)) ng) r

  -- the strong view: the checker's whole answer, its result with its soundness
  check-completeVS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e A t Ψ} {d : Chk P e A t}
                   → U⇐ P d Ψ → ∃[ eE ] ∃[ dd ] ∃[ f ] Σ[ w ∈ WC ctx e A Ψ eE ] (checkElabV ctx e A ≡ (success Ψ eE dd f , w))
  check-completeVS {ctx = ctx} P {e} {A} u =
    let (eE , d′ , f , eq) = check-completeS P u in eE , d′ , f , _ , pairUp (checkElab-sound ctx e A) eq

  infer-completeVS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e A t Ψ} {d : Syn P e A t}
                   → U⇒ P d Ψ → ∃[ eE ] ∃[ dd ] ∃[ f ] Σ[ w ∈ WI ctx e A Ψ eE ] (inferElabV ctx e ≡ (success A Ψ eE dd f , w))
  infer-completeVS {ctx = ctx} P {e} u =
    let (eE , d′ , f , eq) = infer-completeS P u in eE , d′ , f , _ , pairUp (inferElab-sound ctx e) eq

  check-completeS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e A t Ψ} {d : Chk P e A t}
                  → U⇐ P d Ψ → ∃[ eE ] ∃[ dd ] ∃[ f ] checkElab ctx e A ≡ success Ψ eE dd f
  check-completeS P (u-map {mo = mo}) = check-map P mo
  check-completeS P (u-map-app {e = x} {fc = fc} {mo = mo} u) = check-map-app P x fc mo (proj₂ (proj₂ (proj₂ (check-completeS P u))))
  check-completeS P (u-compose-g {f = f} {g = g} {df′ = dfg} ug uf) =
    compose-g-done P f g dfg (proj₂ (proj₂ (proj₂ (given-completeS P ug)))) (proj₂ (proj₂ (proj₂ (check-completeS P uf))))
  check-completeS P (u-compose-f {f = f} {g = g} {ndf = ndf} {p = p} {dg = dg} uf ug) =
    compose-f-done P f g ndf dg ug (proj₂ (proj₂ (proj₂ (infer-completeS P uf)))) p (proj₂ (proj₂ (proj₂ (check-completeS P ug))))
  check-completeS {ctx = ctx} P (u-case {f = f} {g = g} {A = A} {B = B} {C = C} {π = π} uf ug)
    with checkElab ctx f (A ST.⇒[ LG.mk-kind LG.Many π ] C) | check-completeS P uf
  ... | _ | (_ , _ , _ , refl) with checkElab ctx g (B ST.⇒[ LG.mk-kind LG.Many π ] C) | check-completeS P ug
  ...   | _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  check-completeS {ctx = ctx} P (u-pair {f = f} {g = g} {A = A} {B = B} {C = C} {π = π} uf ug)
    with checkElab ctx f (A ST.⇒[ LG.mk-kind LG.Many π ] B) | check-completeS P uf
  ... | _ | (_ , _ , _ , refl) with checkElab ctx g (A ST.⇒[ LG.mk-kind LG.Many π ] C) | check-completeS P ug
  ...   | _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  check-completeS {ctx = ctx} P (u-curry {f = f} {A = A} {B = B} {C = C} {π = π} uf)
    with checkElab ctx f ((A ST.* B) ST.⇒[ LG.mk-kind LG.Many π ] C) | check-completeS P uf
  ... | _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  check-completeS {ctx = ctx} P (u-cata {alg = alg} {F = F} {A = A} {π = π} {w = w} ua)
    rewrite wfFun?-complete-at w
    with checkElab ctx alg (ST.⟦ F ⟧F A ST.⇒[ LG.mk-kind LG.Many π ] A) | check-completeS P ua
  ... | _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  check-completeS {ctx = ctx} P (u-ana {c = c} {A = A} {fi = G.final-ν {F = F} {f = φ} LG.⊑-pa w} uc)
    rewrite wfFun?-complete-at w
    with checkElab ctx c (A ST.⇒[ LG.mk-kind LG.Many (LG.fin φ) ] ST.⟦ F ⟧F A) | check-completeS P uc
  ... | _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  check-completeS {ctx = ctx} P (u-ana {c = c} {A = A} {fi = G.final-ν {F = F} {f = φ} LG.⊑-act w} uc)
    rewrite wfFun?-complete-at w
    with checkElab ctx c (A ST.⇒[ LG.mk-kind LG.Many (LG.fin φ) ] ST.⟦ F ⟧F A) | check-completeS P uc
  ... | _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  check-completeS {ctx = ctx} P (u-ana {c = c} {A = A} {X = B} {fi = G.final-T∞} uc) =
    let (_ , _ , _ , eq) = check-completeS P uc in _ , _ , _ , cong (checkLoop ctx A B) eq
  check-completeS P (u-sub {noc = noc} {d = s} {p = p} u) = sub-done P _ s noc (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) p
  check-completeS {ctx = ctx} P (u-lam {x = x} {body = body} {A = A} {B = B} {q = q} {q′ = q′} ≤p u) =
    check-complete-RLam ctx x body A q q′ B ≤p (proj₂ (proj₂ (proj₂ (check-completeS (pack▸ x A P) u))))
  check-completeS {ctx = ctx} P (u-pair-lit {a = a} {b = b} {A = A} {B = B} ua ub)
    with checkElab ctx a A | check-completeS P ua
  ... | _ | (_ , _ , _ , refl) with checkElab ctx b B | check-completeS P ub
  ...   | _ | (_ , _ , _ , refl) = _ , _ , _ , refl

  check-completeS P (u-poly {a = pos} {ok = TView.iv-imp ns lk refl}) =
    ⊥-elim (lt0 (subst (0 <_) (mono-arity (TView.ImportAt.mono (TView.View.imported (V P) lk))) pos))
  check-completeS {ctx = ctx} P (u-poly {c = c} {e = e} {a = pos} {τ = τ} {r = r} {ok = TView.iv-poly {x = x} {sc = sc} ns ni lp refl}) =
    at-nameC ctx (trans (sym e) (h-poly P lp))
      (checkElab-fallback-RVar-poly {ctx = ctx} x _ ns ni lp
         (¬Ground-isGround-inj₂ sc (λ g → lt0 (subst (0 <_) (trans (cong arity (TView.View.entryIs (V P) lp)) (ground-arity sc g)) pos)))
         (poly-inst {Δ = kinds ctx} sc (TView.View.entryIs (V P) lp) τ r))

  -- The domain-given mode is exact.
  given-completeS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e A π B t Ψ} {d : Dom P e A π B t}
                  → U↦ P d Ψ → ∃[ eE ] ∃[ dd ] ∃[ f ] (elabGiven ctx e A π) ≡ success B Ψ eE dd f
  given-completeS {ctx = ctx} P {e} {A} {π} (u-infer {d = d} {p = a} {o = g} w) =
    let (_ , _ , _ , eq) = infer-completeS P w
        (eE , dd , ff , r) = given-infer-complete {ctx = ctx} {e = e} (inferElab ctx e) eq a g
    in eE , dd , ff , trans (given-route P A π d eq) r

  given-completeS P (u-poly {a = pos} {ok = TView.iv-imp ns lk refl}) =
    ⊥-elim (lt0 (subst (0 <_) (mono-arity (TView.ImportAt.mono (TView.View.imported (V P) lk))) pos))
  given-completeS {ctx = ctx} P (u-poly {c = c} {e = e} {a = pos} {A = A} {B = B} {π = π} {ty = ty} {oc = oc} {τ = τ} {r = r} {ea = ea} {eb = eb} {o = o}
                                        {ok = TView.iv-poly {x = x} {sc = sc} ns ni lp refl}) =
    at-nameG ctx (trans (sym e) (h-poly P lp)) (given-poly-at P x sc ns ni lp pos ty oc τ r ea eb o)
  given-completeS {ctx = ctx} P (u-lam {x = x} {body = body} {A = A} u)
    with inferElab (Classify.extendNamedCtx ctx x A) body | infer-completeS (pack▸ x A P) u
  ... | success _ (_ SCx.∷ _) _ _ _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  given-completeS P {π = π} (u-map {fd = fd} {mo = mo} {least = least}) = given-map P π fd mo least refl

  given-completeS {ctx = ctx} P (u-compose {f = f} {g = g} {A = A} {M = M} {π = π} ug uf)
    with elabGiven ctx g A π | given-completeS P ug
  ... | success _ _ _ _ _  | (_ , _ , _ , refl)
      with elabGiven ctx f M π | given-completeS P uf
  ...   | success _ _ _ _ _  | (_ , _ , _ , refl) = _ , _ , _ , refl
  given-completeS {ctx = ctx} P (u-case {f = f} {g = g} {A = A} {B = B} {π = π} {j = j} uf ug)
    with elabGiven ctx f A π | given-completeS P uf
  ... | success _ _ _ _ _  | (_ , _ , _ , refl)
      with elabGiven ctx g B π | given-completeS P ug
  ...   | success _ _ _ _ _  | (_ , _ , _ , refl) =
    _ , _ , _ , cong (λ x → (E.given-case-join ctx f g A B π _ _ _ _ _ x)) (proj₂ (join?-complete j))
  given-completeS {ctx = ctx} P (u-pair {f = f} {g = g} {A = A} {π = π} uf ug)
    with elabGiven ctx f A π | given-completeS P uf
  ... | success _ _ _ _ _  | (_ , _ , _ , refl)
      with elabGiven ctx g A π | given-completeS P ug
  ...   | success _ _ _ _ _  | (_ , _ , _ , refl) = _ , _ , _ , refl
  given-completeS P (u-cata {alg = alg} {w = w} {p = p} {o = o} u) = given-cata-done P alg w p o (proj₂ (proj₂ (proj₂ (infer-completeS P u))))
