-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.CompletenessS — the checker is complete for the Spec's
-- surface typing (plan 0.122 §5.6, stage f).
--
-- An expression the Spec types, with its usage (`TypeCheck.Use`), at a scope's
-- Pack, is accepted by the checker at the same type and usage. By induction on
-- the usage annotation, each case the checker's per-rule lemma
-- (`Completeness.Rules`) at its premises' results; a reference is found by the
-- lookups its annotation records (`View.InView`, the signature's), the
-- domain-given and spine routes as the checker takes them, and two routes of
-- one composition agree in their usage by coherence (`Adequacy.CoherenceS`).
-- It replaces completeness over the compiler's judgment (`Completeness`).
------------------------------------------------------------------------

module Once.TypeCheck.CompletenessS where

open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; ¬_)
open import Once.Spec.Name using (canonical; own)
import Once.Spec.Grade as LG
import Once.Spec.Type as ST
import Once.Spec.Context as SCx
import Once.Spec.Surface.Syntax as Raw
import Once.Spec.Surface.Typing as SUT
open import Once.Internal.Typing.Scope using (NamedCtx; Binding; lookupLocal; lookupLocal-go; lookupLocal-at; lookupLocal-next)
open Binding using (name)
open NamedCtx
open import Once.Internal.Context using (svar)
import Once.TypeCheck.Scoped as Sc
open import Once.TypeCheck.SpecWitness using (Pack; OkOf; OkSOf; pack▸)
open Pack
import Once.TypeCheck.Use as UMod
open import Once.TypeCheck.Elaborate using (inferElab; checkElab; success)
open import Once.TypeCheck.Completeness.Rules

------------------------------------------------------------------------
-- A Spec local is the name the checker finds (the converse of
-- `Scoped.Locals.found`).
------------------------------------------------------------------------

module _ {Σ} {s : ℕ} {S} {nm : Fin s → _} {m : ℕ} where
  open Sc.Locals Σ S nm {m}
  open SUT Σ S nm using (Locals; _∋_⦂_at_; here; there)

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

open import Once.Spec.Core.Syntax using (Tm)
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

open import Once.Postulates using (extensionality)
open import Once.Internal.Type using (wk₀; none)
open import Once.Internal.Type.Instance using (KindedInstance; rigidOf)
open import Once.Internal.Type.Schema using (schemaOf; kinded-instance)
import Once.Internal.Type.Poly as TP
import Once.Type
open import Once.Spec.Core.Syntax using (Schema; schema; _!!_)
open Schema using (arity; kinds; type)
open import Once.Internal.Typing.Scope using (lookupImport; lookupPolyPrefix)
open import Once.TypeCheck.Classify using (lookupPolyPrefix⇒lookupPoly)
open import Once.TypeCheck.DeciderComplete using (isGround-complete-at; ¬Ground-isGround-inj₂)
open import Once.TypeCheck.Elaborate using (isGround-inj₂→¬Ground)
open import Once.Type.Rigid using (ground-kinded)
open import Once.Adequacy.SpecFront.SchemaOf using (ground-arity; open-arity; ki-of)
open import Once.TypeCheck.ElaborateProofs using (checkElab-fallback-RVar-poly; checkElab-fallback-RVar-poly-infer)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Nat using (_<_)

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
  mono-ty {T = T} refl τ = cong (T ST.⟨_⟩) (extensionality λ ())

  -- a monomorphic entry has no type variables
  mono-arity : ∀ {sc T} → sc ≡ schema 0 ST.∅ₖ T → arity sc ≡ 0
  mono-arity refl = refl

  -- no type variables: a ground schema
  ground-of : ∀ (sc : Raw.PolyType) → arity (schemaOf sc) ≡ 0 → TP.Ground sc
  ground-of sc a with Once.Type.isGround sc in eq
  ... | inj₁ g  = g
  ... | inj₂ tt = ⊥-elim (lt0 (subst (0 <_) a (open-arity sc (isGround-inj₂→¬Ground sc eq))))

  -- a ground entry's type, at any instance
  ground-ty : ∀ {m} {Δ : ST.KCtx m} {sc′} (sc : Raw.PolyType) (e : sc′ ≡ schemaOf sc) (g : TP.Ground sc) (τ : ST.TySub (arity sc′) m)
            → type sc′ ST.⟨ τ ⟩ ≡ TP.extractGround sc g
  ground-ty {Δ = Δ} sc refl g τ =
    let K = kinded-instance sc (ground-kinded {Δ = Δ} sc g)
    in trans (cong (type (schemaOf sc) ST.⟨_⟩) (extensionality λ i → ⊥-elim (fin0 (ground-arity sc g) i))) (proj₂ (proj₂ K))
    where fin0 : ∀ {n} → n ≡ 0 → Fin n → ⊥
          fin0 refl ()

  -- a kinded instance of the entry's schema
  poly-inst : ∀ {m} {Δ : ST.KCtx m} {sc′} (sc : Raw.PolyType) (e : sc′ ≡ schemaOf sc) (τ : ST.TySub (arity sc′) m)
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
↑≡wk₀ T = cong (T ST.⟨_⟩) (extensionality λ ())

-- the Spec's operator classes are the checker's
open import Once.Spec.Surface.Syntax using (BinOp)
import Once.Internal.Syntax as IS
ia-op : ∀ {Σ s S nm op p} → SUT.IntArith Σ {s} S nm op p → IS.isArithmeticOp op ≡ true
ia-op SUT.ia-add = refl
ia-op SUT.ia-sub = refl
ia-op SUT.ia-mul = refl
ia-op SUT.ia-div = refl
ia-op SUT.ia-mod = refl

fa-op : ∀ {Σ s S nm op p} → SUT.FloatArith Σ {s} S nm op p → IS.isFloatArithmeticOp op ≡ true
fa-op SUT.fa-add = refl
fa-op SUT.fa-sub = refl
fa-op SUT.fa-mul = refl
fa-op SUT.fa-div = refl

cmp-op : ∀ {Σ s S nm op p} → SUT.Compare Σ {s} S nm op p → IS.isComparisonOp op ≡ true
cmp-op SUT.cmp-lt = refl
cmp-op SUT.cmp-le = refl
cmp-op SUT.cmp-gt = refl
cmp-op SUT.cmp-ge = refl
cmp-op SUT.cmp-eq = refl
cmp-op SUT.cmp-ne = refl

-- An ordinary application's head is not one the checker takes apart.
open import Once.Internal.Typing.Scope using (AppHeadView; classifyAppHead; classifyAppHeadView; viewToPba)
import Once.Internal.Typing.Scope as LTS
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-lookup)
import Data.List
open import Data.List.Relation.Unary.Any using (here; there)

module _ {Σ} {s : ℕ} {S} {nm : Fin s → _} where
  private
    module SUX = SUT Σ S nm
    gen∈ : (k : Fin (Data.List.length SUX.specialGenerators)) → Data.List.lookup SUX.specialGenerators k ∈ SUX.specialGenerators
    gen∈ k = ∈-lookup {xs = SUX.specialGenerators} k

  special⁻ : ∀ {f} (v : AppHeadView f) → ¬ SUX.SpecialHead f → viewToPba v ≡ nothing
  special⁻ LTS.ahv-id       ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 0))))
  special⁻ LTS.ahv-fst      ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 1))))
  special⁻ LTS.ahv-snd      ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 2))))
  special⁻ LTS.ahv-terminal ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 3))))
  special⁻ LTS.ahv-inl      ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 4))))
  special⁻ LTS.ahv-inr      ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 5))))
  special⁻ LTS.ahv-initial  ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 6))))
  special⁻ LTS.ahv-curry    ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 7))))
  special⁻ LTS.ahv-apply    ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 8))))
  special⁻ LTS.ahv-In       ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 9))))
  special⁻ LTS.ahv-cata     ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 10))))
  special⁻ LTS.ahv-ana      ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 11))))
  special⁻ LTS.ahv-Out      ns = ⊥-elim (ns (SUX.sh-gen (gen∈ (Data.Fin.# 12))))
  special⁻ LTS.ahv-pair-applied    ns = ⊥-elim (ns SUX.sh-pair)
  special⁻ LTS.ahv-compose-applied ns = ⊥-elim (ns SUX.sh-compose)
  special⁻ LTS.ahv-case-applied    ns = ⊥-elim (ns SUX.sh-case)
  special⁻ LTS.ahv-other ns = refl

  ordinary : ∀ {f} → ¬ SUX.SpecialHead f → classifyAppHead f ≡ nothing
  ordinary {f = f} ns = special⁻ (classifyAppHeadView f) ns

------------------------------------------------------------------------
-- The induction
------------------------------------------------------------------------

open import Once.TypeCheck.SpecWitness using (shape-lo; ok-gen; ok-sig; ok-inj; oks-fun)
import Once.TypeCheck.View as TView
open import Once.Internal.Core.Decl using (⌜declS⌝)
open import Once.TypeCheck.Completeness
  using (pair-lit-reduce; given-infer-complete; given-cata-complete; compose-f-complete; infer-complete-RApp-spine;
         poly-head-fails; checkElab-fallback-RVar; completeness-gap-inl-app-check-eq; completeness-gap-inr-app-check-eq;
         completeness-gap-initial-app-check-eq)

open import Once.TypeCheck.Elaborate
  using (inferElabV; checkElabV; elabGivenV; given-infer; elabGivenLeaf; elabGivenApp; checkCompose-g; checkLoop; failure;
         VerifiedInferResult; VerifiedGivenResult; checkCaseGo)
import Once.TypeCheck.Elaborate as E
open import Once.TypeCheck.DualWitness using (DC; DI; dt-case-copair-check)
open import Once.TypeCheck.ElaborateProofs
  using (checkElab-fallback-RInt; checkElab-fallback-RFloat; checkElab-fallback-RUnit; checkElab-fallback-RVar-unit;
         checkElab-fallback-RVar-id; checkElab-fallback-RVar-fst; checkElab-fallback-RVar-snd; checkElab-fallback-RVar-terminal;
         checkElab-fallback-RVar-initial; checkElab-fallback-RVar-inl; checkElab-fallback-RVar-inr; checkElab-fallback-RApp-In;
         checkElab-fallback-RApp-apply; checkElab-fallback-RApp-apply-effclosure; checkElab-fallback-RApp-apply-actclosure;
         checkElab-fallback-RResolved; checkElab-fallback-RAnnot; checkElab-fallback-RLet; checkElab-fallback-RDestruct;
         checkElab-fallback-RNeg; checkElab-fallback-RBinOp; checkElab-fallback-RApp-id; checkElab-fallback-RApp-fst;
         checkElab-fallback-RApp-snd; checkElab-fallback-RApp-terminal; checkElab-fallback-RApp-Out; checkElab-fallback-RApp-generic;
         checkCataGo-J; checkCataGoV-pure-J; checkCataGo-just-success; checkAnaGoV-J; checkAnaGo-just-success; checkLoopV-J; withUnit-elim)
open import Once.TypeCheck.DeciderComplete using (wfFun?-complete-at)
open import Once.Internal.Type.Join using (join?-complete)
open import Once.Internal.Type.Sub using (pure-⊑; <:-refl; sub-prod)
open import Once.Spec.Grade using (⊑-pure; ⊑-pe; ⊑-pa)
open import Once.Spec.Sub using (_<:_; sub-int; sub-float; sub-unit; sub-*)
import Once.TypeCheck.Error as Error
import Once.Internal.Typing.Scope as Classify
open import Once.CanonicalName using (bare-NotGenerator)
open import Once.Spec.Name using (gen; NotGenerator)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
import Once.Surface.Syntax
import Once.TypeCheck.UseAgree as UAg
open import Once.TypeCheck.ShapeHet using (module _≅_)
open _≅_ using (≅-us)
import Once.Adequacy.SpecFront.Inst as In
open import Once.TypeCheck.Completeness using (module DPoly)
import Once.Type.Grade
import Data.Nat.Induction

-- an answer at an equal usage
at-usage : ∀ {m n} {Γ : SCx.Ctx m n} {A : ST.Ty m} {r : E.CheckElabResult Γ A} {Ψ Ψ′}
         → Ψ ≡ Ψ′ → (∃[ eE ] ∃[ d ] ∃[ f ] r ≡ success Ψ eE d f) → ∃[ eE ] ∃[ d ] ∃[ f ] r ≡ success Ψ′ eE d f
at-usage refl x = x

-- the given mode, at a name
at-nameG : ∀ {m} (ctx : NamedCtx m) {c c′} {A B : ST.Ty m} {π Ψ}
         → c ≡ c′ → (∃[ eE ] ∃[ d ] ∃[ f ] proj₁ (elabGivenV ctx (Raw.RResolved c′) A π) ≡ success B Ψ eE d f)
         → ∃[ eE ] ∃[ d ] ∃[ f ] proj₁ (elabGivenV ctx (Raw.RResolved c) A π) ≡ success B Ψ eE d f
at-nameG ctx refl r = r

head-fails : ∀ {m} {ctx : NamedCtx m} {c c′ err} → c ≡ c′ → inferElab ctx (Raw.RResolved c′) ≡ failure err
           → inferElab ctx (Raw.RResolved c) ≡ failure err
head-fails refl e = e

private
  -- a polymorphic entry is not ground
  open-of : ∀ {sch} (sc : Raw.PolyType) → sch ≡ schemaOf sc → 0 < arity sch → ¬ TP.Ground sc
  open-of sc refl pos g = lt0 (subst (0 <_) (ground-arity sc g) pos)

  -- its arrow, read in the compiler's schema
  arrow-of : ∀ {m} {Δ : ST.KCtx m} {sch} (sc : Raw.PolyType) → sch ≡ schemaOf sc
           → ∀ {sd sco π′} → type sch ≡ sd ST.⇒[ LG.mk-kind LG.Many π′ ] sco → (∀ i → ST.Occurs i sco → ST.Occurs i sd)
           → Σ[ sd₀ ∈ Raw.PolyType ] Σ[ sc₀ ∈ Raw.PolyType ] TP.ArrowSchema sc sd₀ sc₀ π′ × TP.CodVarsInDom sd₀ sc₀
  arrow-of {Δ = Δ} sc refl {π′ = π′} ty oc = In.arrow-at Δ sc (schemaOf sc) refl ty oc π′ refl

  arr-inst : ∀ {m} {sch : Schema} (τ : ST.TySub (arity sch) m) {sd sco : ST.Ty (arity sch)} {A B : ST.Ty m} {π′}
           → type sch ≡ sd ST.⇒[ LG.mk-kind LG.Many π′ ] sco → sd ST.⟨ τ ⟩ ≡ A → sco ST.⟨ τ ⟩ ≡ B
           → type sch ST.⟨ τ ⟩ ≡ A ST.⇒[ LG.mk-kind LG.Many π′ ] B
  arr-inst τ ty ea eb = trans (cong (ST._⟨ τ ⟩) ty) (Relation.Binary.PropositionalEquality.cong₂ (λ X Y → X ST.⇒[ _ ] Y) ea eb)

-- A polymorphic definition, given its domain.
given-poly-at : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) (x : String) (sc : Raw.PolyType) {b p}
                → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing
                → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p))
                → 0 < arity (S P !! TView.View.entry (V P) lp)
                → ∀ {sd sco π′ A B π}
                → type (S P !! TView.View.entry (V P) lp) ≡ sd ST.⇒[ LG.mk-kind LG.Many π′ ] sco
                → (∀ i → ST.Occurs i sco → ST.Occurs i sd)
                → (τ : ST.TySub (arity (S P !! TView.View.entry (V P) lp)) m) → ST.Respects (kinds (S P !! TView.View.entry (V P) lp)) (kinds ctx) τ
                → sd ST.⟨ τ ⟩ ≡ A → sco ST.⟨ τ ⟩ ≡ B → π′ LG.⊑π π
                → ∃[ eE ] ∃[ d ] ∃[ f ] proj₁ (elabGivenV ctx (Raw.RResolved (own x)) A π) ≡ success B SCx.zeroUsage eE d f
given-poly-at {ctx = ctx} P x sc {b} {p} ns ni lp pos {A = A} {π = π} ty oc τ r ea eb o
  rewrite poly-head-fails ctx x ns ni lp (open-of sc (TView.View.entryIs (V P) lp) pos) =
    DPoly.from-lookups ctx x A π (Error.UnboundVariable x) ns ni lp (open-of sc (TView.View.entryIs (V P) lp) pos)
      (proj₁ (proj₂ (proj₂ ar))) (proj₂ (proj₂ (proj₂ ar))) (proj₁ ki) (proj₁ (proj₂ ki)) o ki
  where
    ar = arrow-of {Δ = kinds ctx} sc (TView.View.entryIs (V P) lp) ty oc
    ki = subst (KindedInstance (kinds ctx) sc) (arr-inst {sch = S P !! TView.View.entry (V P) lp} τ ty ea eb) (poly-inst {Δ = kinds ctx} sc (TView.View.entryIs (V P) lp) τ r)

-- The domain-given mode takes a synthesizing term apart only through its synthesis.
private
  res-route : ∀ {m} (ctx : NamedCtx m) (cn : _) (A : ST.Ty m) (π : LG.Purity)
                (r : VerifiedInferResult ctx (Raw.RResolved cn)) {B : ST.Ty m} {Ψ eE d f}
            → proj₁ r ≡ success B Ψ eE d f
            → E.given-res ctx cn A π r ≡ given-infer ctx (Raw.RResolved cn) A π r
  res-route ctx cn A π (success _ _ _ _ _ , _) _ = refl
  res-route ctx cn A π (failure _ , _) ()

  leaf-route : ∀ {m} (ctx : NamedCtx m) (cn : _) (A : ST.Ty m) (π : LG.Purity)
                 (r : VerifiedInferResult ctx (Raw.RResolved cn))
             → NotGenerator cn → (vw : AppHeadView (Raw.RResolved cn))
             → ∀ {B : ST.Ty m} {Ψ eE d f} → proj₁ r ≡ success B Ψ eE d f
             → elabGivenLeaf ctx cn A π vw r ≡ given-infer ctx (Raw.RResolved cn) A π r
  leaf-route ctx ._ A π r (¬id ∷ᴬ _) LTS.ahv-id _ = ⊥-elim (¬id refl)
  leaf-route ctx ._ A π r (_ ∷ᴬ ¬fst ∷ᴬ _) LTS.ahv-fst _ = ⊥-elim (¬fst refl)
  leaf-route ctx ._ A π r (_ ∷ᴬ _ ∷ᴬ ¬snd ∷ᴬ _) LTS.ahv-snd _ = ⊥-elim (¬snd refl)
  leaf-route ctx ._ A π r (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ ¬t ∷ᴬ _) LTS.ahv-terminal _ = ⊥-elim (¬t refl)
  leaf-route ctx ._ A π r (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ ¬i ∷ᴬ _) LTS.ahv-initial _ = ⊥-elim (¬i refl)
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ LTS.ahv-inl ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ LTS.ahv-inr ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ LTS.ahv-curry ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ LTS.ahv-apply ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ LTS.ahv-In ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ LTS.ahv-cata ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ LTS.ahv-ana ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ LTS.ahv-Out ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx cn A π r _ LTS.ahv-other ok = res-route ctx cn A π r ok

  app-other-route : ∀ {m} (ctx : NamedCtx m) (f x : Raw.Expr) (A : ST.Ty m) (π : LG.Purity)
                      (r : VerifiedInferResult ctx (Raw.RApp f x))
                  → classifyAppHeadView f ≡ LTS.ahv-other
                  → elabGivenApp ctx f x A π (classifyAppHeadView f) r ≡ given-infer ctx (Raw.RApp f x) A π r
  app-other-route ctx f x A π r eq rewrite eq = refl

  caseGo-success : ∀ {m} {A B C : ST.Ty m} {ctx f g} {π : LG.Purity}
    {Ψf Ψg : SCx.Usage (size ctx)} {Ef : _} {Eg : _} {Wf : _} {Wg : _} {df ff dg fg : ℕ}
    → checkElabV ctx f (A ST.⇒[ LG.mk-kind LG.Many π ] C) ≡ (success Ψf Ef df ff , Wf)
    → checkElabV ctx g (B ST.⇒[ LG.mk-kind LG.Many π ] C) ≡ (success Ψg Eg dg fg , Wg)
    → Σ-syntax ℕ λ d → Σ-syntax ℕ λ fr →
        checkCaseGo ctx f g A B C π ≡ (success (Ψf SCx.+ᵘ Ψg) (Once.Surface.Syntax.copair' Ef Eg) d fr , dt-case-copair-check Wf Wg)
  caseGo-success eqf eqg rewrite eqf | eqg = _ , _ , refl

-- A synthesizing term, given a domain: through its synthesis.
given-infer-routeS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e T t Ψ} {d : Syn P e T t} → U⇒ P d Ψ → ∀ (A : ST.Ty m) (π : LG.Purity)
                   → ∃[ eE ] ∃[ dd ] ∃[ f ] proj₁ (inferElabV ctx e) ≡ success T Ψ eE dd f
                   → elabGivenV ctx e A π ≡ given-infer ctx e A π (inferElabV ctx e)
given-infer-routeS P u-int A π _ = refl
given-infer-routeS P u-float A π _ = refl
given-infer-routeS P u-unit A π _ = refl
given-infer-routeS P u-unit-g A π _ = refl
given-infer-routeS P u-var A π _ = refl
given-infer-routeS {ctx = ctx} P (u-sigop {c = c} {ng = ng} _ _) A π (_ , _ , _ , ok) =
  leaf-route ctx c A π (inferElabV ctx (Raw.RResolved c)) ng (classifyAppHeadView (Raw.RResolved c)) ok
given-infer-routeS {ctx = ctx} P (u-def {c = c} {d = d} {e = e} {ok = ok′}) A π (_ , _ , _ , ok) =
  leaf-route ctx c A π (inferElabV ctx (Raw.RResolved c)) (subst NotGenerator e (ok-gen P ok′)) (classifyAppHeadView (Raw.RResolved c)) ok
given-infer-routeS P (u-annot _) A π _ = refl
given-infer-routeS P (u-pair _ _) A π _ = refl
given-infer-routeS P (u-neg _) A π _ = refl
given-infer-routeS P u-neg-float A π _ = refl
given-infer-routeS P (u-let _ _) A π _ = refl
given-infer-routeS P (u-case _ _ _) A π _ = refl
given-infer-routeS P (u-arith _ _) A π _ = refl
given-infer-routeS P (u-arith-float _ _) A π _ = refl
given-infer-routeS P (u-arith-float-il _ _) A π _ = refl
given-infer-routeS P (u-arith-float-ir _ _) A π _ = refl
given-infer-routeS P (u-compare _ _) A π _ = refl
given-infer-routeS P (u-id-app _) A π _ = refl
given-infer-routeS P (u-fst-app _) A π _ = refl
given-infer-routeS P (u-snd-app _) A π _ = refl
given-infer-routeS P (u-terminal-app _) A π _ = refl
given-infer-routeS P (u-apply-app _) A π _ = refl
given-infer-routeS P (u-apply-eff-app _) A π _ = refl
given-infer-routeS P (u-Out-app _) A π _ = refl
given-infer-routeS P (u-Out-act-app _) A π _ = refl
given-infer-routeS {ctx = ctx} P (u-app {f = f} {x = x} {ns = ns} _ _) A π _ =
  app-other-route ctx f x A π (inferElabV ctx (Raw.RApp f x)) (Once.TypeCheck.Classify.classifyAppHead-nothing⇒view-other (ordinary ns))
given-infer-routeS {ctx = ctx} P (u-effApp {f = f} {x = x} {ns = ns} _ _) A π _ =
  app-other-route ctx f x A π (inferElabV ctx (Raw.RApp f x)) (Once.TypeCheck.Classify.classifyAppHead-nothing⇒view-other (ordinary ns))
given-infer-routeS {ctx = ctx} P (u-app-spine {f = f} {x = x} {ns = ns} _ _) A π _ =
  app-other-route ctx f x A π (inferElabV ctx (Raw.RApp f x)) (Once.TypeCheck.Classify.classifyAppHead-nothing⇒view-other (ordinary ns))

private
  -- what the checker reads off a Pack
  Ok : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) → Fin (s P) → Set
  Ok P = OkOf P

mutual
  infer-completeS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e A t Ψ} {d : Syn P e A t}
                  → U⇒ P d Ψ → ∃[ eE ] ∃[ dd ] ∃[ f ] inferElab ctx e ≡ success A Ψ eE dd f
  infer-completeS {ctx = ctx} P (u-int {i}) = infer-complete-RInt {ctx = ctx} i
  infer-completeS P u-float = _ , _ , _ , refl
  infer-completeS {ctx = ctx} P u-unit = infer-complete-RUnit {ctx = ctx}
  infer-completeS {ctx = ctx} P u-unit-g = infer-complete-RVar-unit {ctx = ctx}
  infer-completeS {ctx = ctx} P (u-var {x = x} {v = v}) =
    at-type ctx (Raw.RVar x) (UMod.lookup-shape (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) (shape-lo (lr P)) v)
            (infer-complete-RVar-local {ctx = ctx} x (finds (lr P) v))
  infer-completeS {ctx = ctx} P (u-sigop {c = c} {ng = ng} {ok = ok} k h) =
    at-type ctx (Raw.RResolved c) (sym (⌜declS⌝ k h)) (infer-complete-RResolved {ctx = ctx} ng (proj₂ ok) (proj₁ ok) k)
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
  infer-completeS P (u-neg {e = e} u) = let (_ , _ , _ , eq) = infer-completeS P u in infer-complete-RNeg e eq
  infer-completeS P u-neg-float = _ , _ , _ , refl
  infer-completeS P (u-let {x = x} {e₁ = e₁} {e₂ = e₂} {A = A} u₁ u₂) =
    let (_ , _ , _ , eq₁) = infer-completeS P u₁ ; (_ , _ , _ , eq₂) = infer-completeS (pack▸ x A P) u₂
    in infer-complete-RLet x e₁ e₂ eq₁ eq₂
  infer-completeS P (u-case {e = sc} {xl = xl} {el = el} {xr = xr} {er = er} {A = A} {B = B} {Cl = Cl} {Cr = Cr} {C = C} {j = j} us ul ur) =
    let (_ , _ , _ , eqS) = infer-completeS P us
        (_ , _ , _ , eqL) = infer-completeS (pack▸ xl A P) ul
        (_ , _ , _ , eqR) = infer-completeS (pack▸ xr B P) ur
    in infer-complete-RDestruct sc xl el xr er Cl Cr C j eqS eqL eqR
  infer-completeS P (u-arith {op = op} {e₁ = e₁} {e₂ = e₂} {o = o} u₁ u₂) =
    let (_ , _ , _ , eq₁) = infer-completeS P u₁ ; (_ , _ , _ , eq₂) = infer-completeS P u₂
    in infer-complete-RBinOp-arith op (ia-op o) e₁ e₂ eq₁ eq₂
  infer-completeS P (u-arith-float {op = op} {e₁ = e₁} {e₂ = e₂} {o = o} u₁ u₂) =
    let (_ , _ , _ , eq₁) = infer-completeS P u₁ ; (_ , _ , _ , eq₂) = infer-completeS P u₂
    in infer-complete-RBinOp-arith-float op (fa-op o) e₁ e₂ eq₁ eq₂
  infer-completeS P (u-arith-float-il {op = op} {e₁ = e₁} {e₂ = e₂} {o = o} u₁ u₂) =
    let (_ , _ , _ , eq₁) = infer-completeS P u₁ ; (_ , _ , _ , eq₂) = infer-completeS P u₂
    in infer-complete-RBinOp-arith-float-il op (fa-op o) e₁ e₂ eq₁ eq₂
  infer-completeS P (u-arith-float-ir {op = op} {e₁ = e₁} {e₂ = e₂} {o = o} u₁ u₂) =
    let (_ , _ , _ , eq₁) = infer-completeS P u₁ ; (_ , _ , _ , eq₂) = infer-completeS P u₂
    in infer-complete-RBinOp-arith-float-ir op (fa-op o) e₁ e₂ eq₁ eq₂
  infer-completeS P (u-compare {op = op} {e₁ = e₁} {e₂ = e₂} {o = o} u₁ u₂) =
    let (_ , _ , _ , eq₁) = infer-completeS P u₁ ; (_ , _ , _ , eq₂) = infer-completeS P u₂
    in infer-complete-RBinOp-cmp op (cmp-op o) e₁ e₂ eq₁ eq₂
  infer-completeS P (u-id-app {e = e} u) = let (_ , _ , _ , eq) = infer-completeS P u in infer-complete-RApp-id e eq
  infer-completeS P (u-fst-app {e = e} u) = let (_ , _ , _ , eq) = infer-completeS P u in infer-complete-RApp-fst e eq
  infer-completeS P (u-snd-app {e = e} u) = let (_ , _ , _ , eq) = infer-completeS P u in infer-complete-RApp-snd e eq
  infer-completeS P (u-terminal-app {e = e} u) = let (_ , _ , _ , eq) = infer-completeS P u in infer-complete-RApp-terminal e eq
  infer-completeS P (u-apply-app {e = e} {A = A} u) = let (_ , _ , _ , eq) = infer-completeS P u in infer-complete-RApp-apply e A eq
  infer-completeS P (u-apply-eff-app {e = e} {A = A} {g = LG.eg-eff} u) =
    let (_ , _ , _ , eq) = infer-completeS P u in infer-complete-RApp-apply-eff e A eq
  infer-completeS P (u-apply-eff-app {e = e} {A = A} {g = LG.eg-act} u) =
    let (_ , _ , _ , eq) = infer-completeS P u in infer-complete-RApp-apply-act e A eq
  infer-completeS P (u-Out-app {e = e} {w = w} u) = let (_ , _ , _ , eq) = infer-completeS P u in infer-complete-RApp-Out e w eq
  infer-completeS P (u-Out-act-app {e = e} {w = w} u) = let (_ , _ , _ , eq) = infer-completeS P u in infer-complete-RApp-Out-act e w eq
  infer-completeS P (u-app {f = f} {x = x} {A = A} {ns = ns} uf ux) =
    let (_ , _ , _ , eqF) = infer-completeS P uf ; (_ , _ , _ , eqX) = check-completeS P ux
    in infer-complete-RApp-generic f x A (ordinary ns) eqF eqX
  infer-completeS P (u-effApp {f = f} {x = x} {A = A} {ns = ns} {g = LG.eg-eff} uf ux) =
    let (_ , _ , _ , eqF) = infer-completeS P uf ; (_ , _ , _ , eqX) = check-completeS P ux
    in infer-complete-RApp-eff f x A (ordinary ns) eqF eqX
  infer-completeS P (u-effApp {f = f} {x = x} {A = A} {ns = ns} {g = LG.eg-act} uf ux) =
    let (_ , _ , _ , eqF) = infer-completeS P uf ; (_ , _ , _ , eqX) = check-completeS P ux
    in infer-complete-RApp-act f x A (ordinary ns) eqF eqX
  infer-completeS P (u-app-spine {f = f} {x = x} {ns = ns} ux uf) = spine-completeS P f x (ordinary ns) ux uf

  -- the strong view: the checker's whole answer
  check-completeVS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e A t Ψ} {d : Chk P e A t}
                   → U⇐ P d Ψ → ∃[ eE ] ∃[ dd ] ∃[ f ] Σ[ w ∈ DC ctx e A Ψ eE ] (checkElabV ctx e A ≡ (success Ψ eE dd f , w))
  check-completeVS {ctx = ctx} P {e} {A} u with checkElabV ctx e A | check-completeS P u
  ... | r , w0 | eE , d′ , f , eq rewrite eq = eE , d′ , f , w0 , refl

  infer-completeVS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e A t Ψ} {d : Syn P e A t}
                   → U⇒ P d Ψ → ∃[ eE ] ∃[ dd ] ∃[ f ] Σ[ w ∈ DI ctx e A Ψ eE ] (inferElabV ctx e ≡ (success A Ψ eE dd f , w))
  infer-completeVS {ctx = ctx} P {e} u with inferElabV ctx e | infer-completeS P u
  ... | r , w0 | eE , d′ , f , eq rewrite eq = eE , d′ , f , w0 , refl

  check-completeVS-from-infer : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e A B t Ψ} {d : Syn P e A t}
                              → U⇒ P d Ψ → A <: B → ∃[ eE ] ∃[ dd ] ∃[ f ] Σ[ w ∈ DC ctx e B Ψ eE ] (checkElabV ctx e B ≡ (success Ψ eE dd f , w))
  check-completeVS-from-infer {ctx = ctx} P {e} {B = B} u p with checkElabV ctx e B | iFromInferSubS P u p
  ... | r , w0 | eE , d′ , f , eq rewrite eq = eE , d′ , f , w0 , refl

  check-completeS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e A t Ψ} {d : Chk P e A t}
                  → U⇐ P d Ψ → ∃[ eE ] ∃[ dd ] ∃[ f ] checkElab ctx e A ≡ success Ψ eE dd f
  check-completeS P (u-sub {p = p} u) = iFromInferSubS P u p
  check-completeS {ctx = ctx} P (u-id {T = T} {π = π}) = checkElab-fallback-RVar-id {ctx = ctx} T (pure-⊑ π)
  check-completeS {ctx = ctx} P (u-fst {A = A} {B = B} {π = π}) = checkElab-fallback-RVar-fst {ctx = ctx} A B (pure-⊑ π)
  check-completeS {ctx = ctx} P (u-snd {A = A} {B = B} {π = π}) = checkElab-fallback-RVar-snd {ctx = ctx} A B (pure-⊑ π)
  check-completeS {ctx = ctx} P (u-terminal {A = A} {π = π}) = checkElab-fallback-RVar-terminal {ctx = ctx} A (pure-⊑ π)
  check-completeS {ctx = ctx} P (u-initial {A = A} {π = π}) = checkElab-fallback-RVar-initial {ctx = ctx} A (pure-⊑ π)
  check-completeS {ctx = ctx} P (u-inl {A = A} {B = B} {π = π}) = checkElab-fallback-RVar-inl {ctx = ctx} A B (pure-⊑ π)
  check-completeS {ctx = ctx} P (u-inr {A = A} {B = B} {π = π}) = checkElab-fallback-RVar-inr {ctx = ctx} A B (pure-⊑ π)
  check-completeS {ctx = ctx} P (u-compose-g {f = f} {g = g} {A = A} {B = B} {C = C} {π = π} ug uf)
    with elabGivenV ctx g A π | given-completeS P ug
  ... | success _ _ _ _ _ , _ | (_ , _ , _ , refl)
      with checkElabV ctx f (B ST.⇒[ LG.mk-kind LG.Many π ] C) | check-completeS P uf
  ...   | success _ _ _ _ , _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  check-completeS {ctx = ctx} P u@(u-compose-f {f = f} {g = g} {A = A} {B = B} {C = C} {C′ = C′} {π = π} {π′ = π′} {p = s} uf ug) =
    let (_ , _ , _ , eqF) = infer-completeS P uf
        (_ , _ , _ , eqG) = check-completeS P ug
    in compose-g-completeS P f g A B C C′ π π′ u (elabGivenV ctx g A π) eqF s eqG
  check-completeS P (u-case {π = LG.pure} uf ug) =
    let (_ , _ , _ , Wf , eqf) = check-completeVS P uf
        (_ , _ , _ , Wg , eqg) = check-completeVS P ug
        (d , fr , eqGo) = caseGo-success eqf eqg
    in _ , _ , _ , cong proj₁ eqGo
  check-completeS P (u-case {π = LG.eff} uf ug)
    with check-completeVS P uf | check-completeVS P ug
  ... | (_ , _ , _ , Wf , eqf) | (_ , _ , _ , Wg , eqg)
        with caseGo-success eqf eqg
  ...     | (d , fr , eqGo) rewrite eqGo = _ , _ , _ , refl
  check-completeS P (u-case {π = LG.act} uf ug)
    with check-completeVS P uf | check-completeVS P ug
  ... | (_ , _ , _ , Wf , eqf) | (_ , _ , _ , Wg , eqg)
        with caseGo-success eqf eqg
  ...     | (d , fr , eqGo) rewrite eqGo = _ , _ , _ , refl
  check-completeS P (u-pair uf ug)
    with check-completeVS P uf | check-completeVS P ug
  ... | (_ , _ , _ , Wf , eqf) | (_ , _ , _ , Wg , eqg)
        rewrite eqf | eqg = _ , _ , _ , refl
  check-completeS P (u-curry {π₀ = π₀} uf)
    with check-completeVS P uf
  ... | (_ , _ , _ , Wf , eqf) rewrite eqf =
    withUnit-elim _ (pure-⊑ π₀) _ (λ res → ∃[ eE ] ∃[ d ] ∃[ f ] proj₁ res ≡ success _ eE d f) (λ _ → _ , _ , _ , refl)
  check-completeS {ctx = ctx} P (u-cata {alg = alg} {F = F} {A = A} {π = LG.pure} {w = w} ua)
    with wfFun?-complete-at w
  ... | eqW
    with check-completeVS P ua
  ... | (_ , _ , _ , W , eqA)
        with checkCataGo-just-success ctx alg F A LG.pure w eqW eqA ⊑-pure
  ...     | eqGo = _ , _ , _ , cong proj₁ (trans (checkCataGoV-pure-J ctx alg F A (just w) eqW) eqGo)
  check-completeS {ctx = ctx} P (u-cata {alg = alg} {F = F} {A = A} {π = LG.eff} {w = w} ua)
    with wfFun?-complete-at w
  ... | eqW
    with check-completeVS P ua
  ... | (_ , _ , _ , W , eqA)
        with checkCataGo-just-success ctx alg F A LG.eff w eqW eqA ⊑-pe
  ...     | eqGo rewrite trans (checkCataGo-J ctx alg F A LG.eff (just w) eqW) eqGo = _ , _ , _ , refl
  check-completeS {ctx = ctx} P (u-cata {alg = alg} {F = F} {A = A} {π = LG.act} {w = w} ua)
    with wfFun?-complete-at w
  ... | eqW
    with check-completeVS P ua
  ... | (_ , _ , _ , W , eqA)
        with checkCataGo-just-success ctx alg F A LG.act w eqW eqA ⊑-pa
  ...     | eqGo rewrite trans (checkCataGo-J ctx alg F A LG.act (just w) eqW) eqGo = _ , _ , _ , refl
  check-completeS {ctx = ctx} P (u-ana {c = coalg} {F = F} {A = A} {π₀ = π₀} {f = φ} {g = ua} {w = w} uc)
    with wfFun?-complete-at w
  ... | eqW
    with check-completeVS P uc
  ... | (_ , _ , _ , W , eqA)
        with checkAnaGo-just-success ctx coalg F A π₀ φ ua w eqW eqA (pure-⊑ π₀)
  ...     | eqGo = _ , _ , _ , cong proj₁ (trans (checkAnaGoV-J ctx coalg F A π₀ φ ua (just w) eqW) eqGo)
  check-completeS {ctx = ctx} P (u-loop {c = round} {A = A} {B = B} ur)
    with check-completeVS P ur
  ... | (_ , _ , _ , W , eqR) = _ , _ , _ , cong proj₁ (trans (checkLoopV-J ctx round A B) (cong (checkLoop ctx round A B) eqR))
  check-completeS {ctx = ctx} P (u-lam {x = x} {body = body} {A = A} {B = B} {q = q} {π = π} {q′ = q′} ≤p u) =
    let (_ , _ , _ , eqB) = check-completeS (pack▸ x A P) u
    in check-complete-RLam ctx x body A q q′ B ≤p (pure-⊑ π) eqB
  check-completeS P (u-pair-lit ua ub)
    with check-completeVS P ua | check-completeVS P ub
  ... | (_ , _ , _ , _ , eqA) | (_ , _ , _ , _ , eqB) = pair-lit-reduce eqA eqB
  check-completeS P (u-In-app {e = arg} {F = F} {w = w} u) =
    let (_ , _ , _ , eqA) = check-completeS P u in checkElab-fallback-RApp-In arg F (wfFun?-complete-at w) eqA
  check-completeS P (u-apply-app {e = e} {A = A} {B = B} u) =
    let (_ , _ , _ , eq) = infer-completeS P u in checkElab-fallback-RApp-apply e A B eq (<:-refl B)
  check-completeS P (u-inl-app {e = arg} {A = A} {B = B} u) =
    let (_ , _ , _ , eqC) = check-completeS P u in completeness-gap-inl-app-check-eq arg A B eqC
  check-completeS P (u-inr-app {e = arg} {A = A} {B = B} u) =
    let (_ , _ , _ , eqC) = check-completeS P u in completeness-gap-inr-app-check-eq arg A B eqC
  check-completeS P (u-initial-app {e = arg} {T = T} u) =
    let (_ , _ , _ , eqC) = check-completeS P u in completeness-gap-initial-app-check-eq arg T eqC
  check-completeS P (u-poly {a = pos} {ok = TView.iv-imp ns lk refl}) =
    ⊥-elim (lt0 (subst (0 <_) (mono-arity (TView.ImportAt.mono (TView.View.imported (V P) lk))) pos))
  check-completeS {ctx = ctx} P (u-poly {c = c} {e = e} {a = pos} {τ = τ} {r = r} {ok = TView.iv-poly {x = x} {sc = sc} ns ni lp refl}) =
    at-nameC ctx (trans (sym e) (h-poly P lp))
      (checkElab-fallback-RVar-poly {ctx = ctx} x _ ns ni lp
         (¬Ground-isGround-inj₂ sc (λ g → lt0 (subst (0 <_) (trans (cong arity (TView.View.entryIs (V P) lp)) (ground-arity sc g)) pos)))
         (poly-inst {Δ = kinds ctx} sc (TView.View.entryIs (V P) lp) τ r))

  -- compose, the checker's order: `g`'s route first. Where it succeeds on a
  -- derivation built on `f`'s route, the two compositions agree on their usage
  -- (`UseAgree`).
  compose-g-completeS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) (f g : Raw.Expr) (A B C C′ : ST.Ty m) (π π′ : LG.Purity)
                          {t Ψ₁ Ψ₂} {dc : Chk P (Raw.RApp (Raw.RApp (Raw.RResolved (gen "compose")) f) g) (A ST.⇒[ LG.mk-kind LG.Many π ] C) t}
                      → U⇐ P dc (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂))
                      → (rG : VerifiedGivenResult ctx g A π)
                      → ∀ {fE gE} {df ff dg fg : ℕ}
                      → inferElab ctx f ≡ success (B ST.⇒[ LG.mk-kind LG.Many π′ ] C′) Ψ₁ fE df ff
                      → (B ST.⇒[ LG.mk-kind LG.Many π′ ] C′) <: (B ST.⇒[ LG.mk-kind LG.Many π ] C)
                      → checkElab ctx g (A ST.⇒[ LG.mk-kind LG.Many π ] B) ≡ success Ψ₂ gE dg fg
                      → ∃[ eE ] ∃[ d ] ∃[ fr ] proj₁ (checkCompose-g ctx f g A C π rG) ≡ success (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂)) eE d fr
  compose-g-completeS P f g A B C C′ π π′ u (failure _ , _) eqF p eqG = compose-f-complete f g A B C C′ π π′ eqF p eqG
  compose-g-completeS {ctx = ctx} P f g A B C C′ π π′ u (success B″ Ψg″ gE″ dg″ fg″ , wG) eqF p eqG
    with E.checkElabV-wf ctx (Data.Nat.Induction.<-wellFounded (Data.List.length (polys ctx))) f (B″ ST.⇒[ LG.mk-kind LG.Many π ] C)
  ... | failure _ , _ = compose-f-complete f g A B C C′ π π′ eqF p eqG
  ... | success Ψf″ fE″ df″ ff″ , wF =
    at-usage (≅-us (UA.coh⇐ (shape-lo (lr P)) (UMod.u-compose-g (proj₂ (proj₁ (proj₂ (proj₂ (proj₂ wG) P))))
                                                               (proj₂ (proj₁ (proj₂ (proj₂ (proj₂ wF) P))))) u refl))
             (_ , _ , _ , refl)
    where module UA = UAg (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (inline P) (ok-gen P) (ok-sig P) (ok-inj P) (λ {c} → oks-fun P {c}) (kinds ctx)

  spine-completeS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) (f x : Raw.Expr) {X B tx tf Ψf Ψx}
                      {dx : Syn P x X tx} {df : Dom P f X LG.pure B tf}
                  → classifyAppHead f ≡ nothing → U⇒ P dx Ψx → U↦ P df Ψf
                  → ∃[ eE ] ∃[ d ] ∃[ f′ ] inferElab ctx (Raw.RApp f x) ≡ success B (Ψf SCx.+ᵘ (LG.Many SCx.*ᵘ Ψx)) eE d f′
  spine-completeS {ctx = ctx} P f x eqAH ux uf@(u-lam _) =
    infer-complete-RApp-spine f x eqAH refl (proj₂ (proj₂ (proj₂ (infer-completeS P ux)))) (proj₂ (proj₂ (proj₂ (given-completeS P uf))))
  spine-completeS {ctx = ctx} P f x eqAH ux uf@(u-compose _ _) =
    infer-complete-RApp-spine f x eqAH refl (proj₂ (proj₂ (proj₂ (infer-completeS P ux)))) (proj₂ (proj₂ (proj₂ (given-completeS P uf))))
  spine-completeS P f x () ux u-id
  spine-completeS P f x () ux u-fst
  spine-completeS P f x () ux u-snd
  spine-completeS P f x () ux u-terminal
  spine-completeS P f x () ux u-initial
  spine-completeS {ctx = ctx} P f x eqAH ux uf@(u-case _ _) =
    infer-complete-RApp-spine f x eqAH refl (proj₂ (proj₂ (proj₂ (infer-completeS P ux)))) (proj₂ (proj₂ (proj₂ (given-completeS P uf))))
  spine-completeS {ctx = ctx} P f x eqAH ux uf@(u-pair _ _) =
    infer-complete-RApp-spine f x eqAH refl (proj₂ (proj₂ (proj₂ (infer-completeS P ux)))) (proj₂ (proj₂ (proj₂ (given-completeS P uf))))
  spine-completeS {ctx = ctx} P f x eqAH ux uf@(u-cata _) =
    infer-complete-RApp-spine f x eqAH refl (proj₂ (proj₂ (proj₂ (infer-completeS P ux)))) (proj₂ (proj₂ (proj₂ (given-completeS P uf))))
  spine-completeS {ctx = ctx} P f x eqAH ux uf@(u-poly {e = e} {a = pos} {ok = TView.iv-imp ns lk refl}) =
    ⊥-elim (lt0 (subst (0 <_) (mono-arity (TView.ImportAt.mono (TView.View.imported (V P) lk))) pos))
  spine-completeS {ctx = ctx} P f x eqAH ux uf@(u-poly {e = e} {a = pos} {ok = TView.iv-poly {x = y} {sc = sc} ns ni lp refl}) =
    infer-complete-RApp-spine f x eqAH
      (head-fails (trans (sym e) (h-poly P lp)) (cong proj₁ (poly-head-fails ctx y ns ni lp (open-of sc (TView.View.entryIs (V P) lp) pos))))
      (proj₂ (proj₂ (proj₂ (infer-completeS P ux)))) (proj₂ (proj₂ (proj₂ (given-completeS P uf))))
  spine-completeS P f x eqAH ux (u-infer {A′ = A′} {p = a} {o = ⊑-pure} w) =
    let (_ , _ , _ , eqF) = infer-completeS P w
        (_ , _ , _ , eqX) = iFromInferSubS P ux a
    in infer-complete-RApp-generic f x A′ eqAH eqF eqX

  -- The domain-given mode is exact.
  given-completeS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e A π B t Ψ} {d : Dom P e A π B t}
                  → U↦ P d Ψ → ∃[ eE ] ∃[ dd ] ∃[ f ] proj₁ (elabGivenV ctx e A π) ≡ success B Ψ eE dd f
  given-completeS {ctx = ctx} P {e} {A} {π} (u-infer {p = a} {o = g} w)
    rewrite given-infer-routeS P w A π (infer-completeS P w) =
      given-infer-complete (inferElabV ctx e) (proj₂ (proj₂ (proj₂ (infer-completeS P w)))) a g
  given-completeS P (u-poly {a = pos} {ok = TView.iv-imp ns lk refl}) =
    ⊥-elim (lt0 (subst (0 <_) (mono-arity (TView.ImportAt.mono (TView.View.imported (V P) lk))) pos))
  given-completeS {ctx = ctx} P (u-poly {c = c} {e = e} {a = pos} {A = A} {B = B} {π = π} {ty = ty} {oc = oc} {τ = τ} {r = r} {ea = ea} {eb = eb} {o = o}
                                        {ok = TView.iv-poly {x = x} {sc = sc} ns ni lp refl}) =
    at-nameG ctx (trans (sym e) (h-poly P lp)) (given-poly-at P x sc ns ni lp pos ty oc τ r ea eb o)
  given-completeS {ctx = ctx} P (u-lam {x = x} {body = body} {A = A} {π = π} {q′ = q′} u)
    with inferElabV (Classify.extendNamedCtx ctx x A) body | infer-completeS (pack▸ x A P) u
  ... | success _ (_ SCx.∷ _) _ _ _ , _ | (_ , _ , _ , refl)
      with E.decideLeq q′ LG.Many | decideLeq-just q′ LG.Many (Once.Type.Grade.≤q-Many q′)
  ...   | just _ | _ , refl = withUnit-elim _ (pure-⊑ π) _ (λ res → ∃[ eE ] ∃[ d ] ∃[ f ] proj₁ res ≡ success _ _ eE d f) (λ _ → _ , _ , _ , refl)
  given-completeS {ctx = ctx} P (u-compose {f = f} {g = g} {A = A} {M = M} {π = π} ug uf)
    with elabGivenV ctx g A π | given-completeS P ug
  ... | success _ _ _ _ _ , _ | (_ , _ , _ , refl)
      with elabGivenV ctx f M π | given-completeS P uf
  ...   | success _ _ _ _ _ , _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  given-completeS P (u-id {π = π}) = withUnit-elim _ (pure-⊑ π) _ (λ res → ∃[ eE ] ∃[ d ] ∃[ f ] proj₁ res ≡ success _ _ eE d f) (λ _ → _ , _ , _ , refl)
  given-completeS P (u-fst {π = π}) = withUnit-elim _ (pure-⊑ π) _ (λ res → ∃[ eE ] ∃[ d ] ∃[ f ] proj₁ res ≡ success _ _ eE d f) (λ _ → _ , _ , _ , refl)
  given-completeS P (u-snd {π = π}) = withUnit-elim _ (pure-⊑ π) _ (λ res → ∃[ eE ] ∃[ d ] ∃[ f ] proj₁ res ≡ success _ _ eE d f) (λ _ → _ , _ , _ , refl)
  given-completeS P (u-terminal {π = π}) = withUnit-elim _ (pure-⊑ π) _ (λ res → ∃[ eE ] ∃[ d ] ∃[ f ] proj₁ res ≡ success _ _ eE d f) (λ _ → _ , _ , _ , refl)
  given-completeS P (u-initial {π = π}) = withUnit-elim _ (pure-⊑ π) _ (λ res → ∃[ eE ] ∃[ d ] ∃[ f ] proj₁ res ≡ success _ _ eE d f) (λ _ → _ , _ , _ , refl)
  given-completeS {ctx = ctx} P (u-case {f = f} {g = g} {A = A} {B = B} {π = π} {j = j} uf ug)
    with elabGivenV ctx f A π | given-completeS P uf
  ... | success _ _ _ _ _ , _ | (_ , _ , _ , refl)
      with elabGivenV ctx g B π | given-completeS P ug
  ...   | success _ _ _ _ _ , _ | (_ , _ , _ , refl) =
    _ , _ , _ , cong (λ x → proj₁ (E.given-case-join _ _ _ _ _ _ _ _ _ _ _ _ _ x)) (proj₂ (join?-complete j))
  given-completeS {ctx = ctx} P (u-pair {f = f} {g = g} {A = A} {π = π} uf ug)
    with elabGivenV ctx f A π | given-completeS P uf
  ... | success _ _ _ _ _ , _ | (_ , _ , _ , refl)
      with elabGivenV ctx g A π | given-completeS P ug
  ...   | success _ _ _ _ _ , _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  given-completeS {ctx = ctx} P (u-cata {alg = alg} {F = F} {A = A} {π = π} {w = w} u)
    rewrite wfFun?-complete-at w =
      given-cata-complete w (pure-⊑ π) (inferElabV ctx alg) (proj₂ (proj₂ (proj₂ (infer-completeS P u))))

  -- Synthesis, then the conversion: the checker's switch.
  iFromInferSubS : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) {e A B t Ψ} {d : Syn P e A t}
                 → U⇒ P d Ψ → A <: B → ∃[ eE ] ∃[ dd ] ∃[ f ] checkElab ctx e B ≡ success Ψ eE dd f
  iFromInferSubS {ctx = ctx} P (u-int {i}) sub-int = checkElab-fallback-RInt {ctx = ctx} i
  iFromInferSubS {ctx = ctx} P (u-float {i} {f} {l}) sub-float = checkElab-fallback-RFloat {ctx = ctx} i f l
  iFromInferSubS {ctx = ctx} P u-unit sub-unit = checkElab-fallback-RUnit {ctx = ctx}
  iFromInferSubS {ctx = ctx} P u-unit-g sub-unit = checkElab-fallback-RVar-unit {ctx = ctx}
  iFromInferSubS {ctx = ctx} P u@(u-var {x = x} {A = T}) sb =
    checkElab-fallback-RVar {ctx = ctx} x T (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS {ctx = ctx} P u@(u-sigop {c = c} _ _) sb =
    checkElab-fallback-RResolved {ctx = ctx} c _ (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS {ctx = ctx} P u@(u-def {c = c}) sb =
    checkElab-fallback-RResolved {ctx = ctx} c _ (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS {ctx = ctx} P u@(u-annot {e = e} {T = T} _) sb =
    checkElab-fallback-RAnnot {ctx = ctx} e T
      (proj₂ (proj₂ (proj₂ (at-type ctx (Raw.RAnnot e T) (↑≡wk₀ {Sg P} {_} {S P} {nm P} T) (infer-completeS P u)))))
      (subst (_<: _) (↑≡wk₀ {Sg P} {_} {S P} {nm P} T) sb)
  iFromInferSubS P (u-pair ua ub) (sub-* pa pb)
    with check-completeVS-from-infer P ua pa | check-completeVS-from-infer P ub pb
  ... | (_ , _ , _ , _ , eqA) | (_ , _ , _ , _ , eqB) = pair-lit-reduce eqA eqB
  iFromInferSubS P u@(u-neg {e = e} _) sub-int = checkElab-fallback-RNeg e ST.Int (proj₂ (proj₂ (proj₂ (infer-completeS P u))))
  iFromInferSubS {ctx = ctx} P (u-neg-float {i} {f} {l}) sub-float = checkElab-fallback-RNeg {ctx = ctx} (Raw.RFloat i f l) ST.Float refl
  iFromInferSubS P u@(u-let {x = x} {e₁ = e₁} {e₂ = e₂} {B = B} _ _) sb =
    checkElab-fallback-RLet x e₁ e₂ B (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-case {e = sc} {xl = xl} {el = el} {xr = xr} {er = er} {C = C} _ _ _) sb =
    checkElab-fallback-RDestruct sc xl el xr er C (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-arith {op = op} {e₁ = e₁} {e₂ = e₂} _ _) sb =
    checkElab-fallback-RBinOp op e₁ e₂ ST.Int (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-arith-float {op = op} {e₁ = e₁} {e₂ = e₂} _ _) sb =
    checkElab-fallback-RBinOp op e₁ e₂ ST.Float (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-arith-float-il {op = op} {e₁ = e₁} {e₂ = e₂} _ _) sb =
    checkElab-fallback-RBinOp op e₁ e₂ ST.Float (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-arith-float-ir {op = op} {e₁ = e₁} {e₂ = e₂} _ _) sb =
    checkElab-fallback-RBinOp op e₁ e₂ ST.Float (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-compare {op = op} {e₁ = e₁} {e₂ = e₂} _ _) sb =
    checkElab-fallback-RBinOp op e₁ e₂ (ST.Unit ST.+ ST.Unit) (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-id-app {e = e} {T = T} _) sb = checkElab-fallback-RApp-id e T (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-fst-app {e = e} {A = A} _) sb = checkElab-fallback-RApp-fst e A (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-snd-app {e = e} {B = B} _) sb = checkElab-fallback-RApp-snd e B (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-terminal-app {e = e} _) sb = checkElab-fallback-RApp-terminal e ST.Unit (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-Out-app {e = v} {F = F} _) sb =
    checkElab-fallback-RApp-Out v (ST.⟦ F ⟧F (ST.ν F LG.pureᶠ)) (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-Out-act-app {e = v} {F = F} _) sb =
    checkElab-fallback-RApp-Out v (ST.Unit ST.⇒[ LG.mk-kind LG.Many LG.act ] ST.⟦ F ⟧F (ST.ν F LG.actᶠ)) (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P (u-apply-app {e = p} {A = A} {B = B} u) sb =
    checkElab-fallback-RApp-apply p A B (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P (u-apply-eff-app {e = p} {A = A} {B = B} {g = LG.eg-eff} u) sb =
    checkElab-fallback-RApp-apply-effclosure p A B (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P (u-apply-eff-app {e = p} {A = A} {B = B} {g = LG.eg-act} u) sb =
    checkElab-fallback-RApp-apply-actclosure p A B (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-app {f = f} {x = x} {B = B} {ns = ns} _ _) sb =
    checkElab-fallback-RApp-generic f x B (ordinary ns) (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-effApp {f = f} {x = x} {B = B} {π = π} {ns = ns} _ _) sb =
    checkElab-fallback-RApp-generic f x (ST.Unit ST.⇒[ LG.mk-kind LG.Many π ] B) (ordinary ns) (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
  iFromInferSubS P u@(u-app-spine {f = f} {x = x} {T = B} {ns = ns} _ _) sb =
    checkElab-fallback-RApp-generic f x B (ordinary ns) (proj₂ (proj₂ (proj₂ (infer-completeS P u)))) sb
