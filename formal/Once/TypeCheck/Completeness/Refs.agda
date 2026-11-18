-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Completeness.Refs — the checker on references and the
-- per-rule steps that need no generator (plan 0.122 §5.6, plan 0.151).
--
-- A name's lookups, the polymorphic chain (`DPoly`), and the composition
-- steps the induction (`TypeCheck.Completeness`) uses: each says the checker
-- succeeds on an expression once its premises do, at the rule's type and
-- usage.
------------------------------------------------------------------------

module Once.TypeCheck.Completeness.Refs where

open import Data.Bool using (Bool; true)
import Data.Bool
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
import Data.Nat
open import Data.Product using (∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Relation.Nullary using (yes; no; Dec; ¬_)

import Once.Spec.Type as T
import Once.Type.Core as T
import Once.Type as T
import Once.Spec.Surface.Syntax as T
import Once.Type.Poly as T
import Once.Spec.Grade as T
open import Once.Spec.Type using (Ty; Base; ∅ₖ; Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; _⊑π_)
open import Once.Type.Grade using (_≤qᵇ_)
import Once.Type.Grade
open import Once.Type.Core using (wk₀)
open import Once.Spec.Surface.Syntax as Raw using (RVar; RResolved; RAnnot; RPair)
import Once.Spec.Surface.Syntax as Syn
open import Once.Spec.Surface.Syntax using (PolyType)
open import Once.Spec.Name using (CanonicalName; own)
open import Once.Name using (showCanonical; WordName; wordNameB)
open import Once.Spec.Surface.Operator using (BinOp; binSym; BinSym)
open BinSym using (theory; shape)
open import Once.Spec.Theory using (NumTy; int; float; ⌜_⌝ⁿ; Has; Neg; symCod; int-neg; float-neg)
open import Once.TypeCheck.NumTable using (has?-yes)
open import Once.Surface.Numeric using (numBin)
open import Once.Spec.Sub using (_<:_; _⊔_≔_)
open import Once.Type.SubDecide using (_<:?_; _⊑π?_)
open import Once.Type.Join using (join?-complete)
open import Once.Type.Concrete using (IsConcrete; con-base; con-fun)
open import Once.Functor.Decide using (isConcrete?; isBaseType?; isConcrete?-complete; isBaseType?-complete)
open import Once.TypeCheck.DeciderComplete using (¬Ground-isGround-inj₂)
open import Once.Type.Poly
open import Once.Type using (isGround)
open import Once.Type.Instance using (KindedInstance)
open import Once.Type.Rigid using (kindedInstance?)
import Once.Context as Srf
import Once.Spec.Context as Surface
import Once.Spec.Context as SCx
open import Once.Spec.Context using (_*ᵘ_; _+ᵘ_; zeroUsage)
import Once.Context as Surface
open import Once.Surface.Syntax as Surface using () renaming (Expr to SExpr)
open import Once.TypeCheck.Scope using (NamedCtx; lookupImport; lookupLocal; lookupPolyPrefix; PolyCtx)
import Once.TypeCheck.Scope as Classify
open import Once.TypeCheck.Classify using (lookupPolyPrefix⇒lookupPoly; lookupPoly)
open import Once.TypeCheck.Error using (TypeError; UnboundVariable)
import Once.TypeCheck.Error as Error
open import Once.TypeCheck.Elaborate
import Once.TypeCheck.Elaborate as E

------------------------------------------------------------------------
-- References
------------------------------------------------------------------------

-- An own reference that is neither a declaration nor a monomorphic definition
-- reaches the telescope.
inferElabV-own-poly-bridge : ∀ {m} (ctx : NamedCtx m) (x : String)
  → (eS : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
  → (eI : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
  → inferElab ctx (Raw.RResolved (own x))
      ≡ inferElabV-RVar-poly-aux ctx x eS eI
inferElabV-own-poly-bridge ctx x eS eI = trans (sig-eq nothing eS) (imp-eq nothing eI)
  where
    sig-eq : ∀ ls (e : lookupImport (NamedCtx.sig ctx) x ≡ ls)
           → inferElabV-RResolved-aux ctx (own x) (lookupImport (NamedCtx.sig ctx) x) refl
             ≡ inferElabV-RResolved-aux ctx (own x) ls e
    sig-eq .(lookupImport (NamedCtx.sig ctx) x) refl = refl
    imp-eq : ∀ li (e : lookupImport (NamedCtx.imports ctx) x ≡ li)
           → inferElabV-RResolved-own-aux ctx x eS (lookupImport (NamedCtx.imports ctx) x) refl
             ≡ inferElabV-RResolved-own-aux ctx x eS li e
    imp-eq .(lookupImport (NamedCtx.imports ctx) x) refl = refl

-- J-style specialisation lemmas for the two remaining de-withed poly-fallback
-- stages. D136 deleted a third (`inferElabV-RVar-poly-aux-eq`): the fallback no
-- longer dispatches on `classifyBareBuiltin`, so there is no classifier answer
-- left to specialise.
inferElabV-RVar-poly-lookup-eq : ∀ {m} (ctx : NamedCtx m) (x : String) eL eI (lp : Maybe (PolyType × Syn.Expr))
    (eqLp : lookupPoly (NamedCtx.polys ctx) x ≡ lp)
  → inferElabV-RVar-poly-lookup-aux ctx x eL eI (lookupPoly (NamedCtx.polys ctx) x) refl
      ≡ inferElabV-RVar-poly-lookup-aux ctx x eL eI lp eqLp
inferElabV-RVar-poly-lookup-eq ctx x eL eI .(lookupPoly (NamedCtx.polys ctx) x) refl = refl

inferElabV-RVar-poly-ground-eq : ∀ {m} (ctx : NamedCtx m) (x : String) eL eI (schema : PolyType) (body : Syn.Expr) eqLp
    (ig : (Ground schema) ⊎ ⊤) (eqG : isGround schema ≡ ig)
  → inferElabV-RVar-poly-ground-aux ctx x eL eI schema body eqLp (isGround schema) refl
      ≡ inferElabV-RVar-poly-ground-aux ctx x eL eI schema body eqLp ig eqG
inferElabV-RVar-poly-ground-eq ctx x eL eI schema body eqLp .(isGround schema) refl = refl

-- The poly fallback FAILS when the name isn't in the telescope.
inferElabV-RVar-poly-aux-fail-nothing : ∀ {m} (ctx : NamedCtx m) (x : String) eL eI
  → lookupPoly (NamedCtx.polys ctx) x ≡ nothing
  → inferElabV-RVar-poly-aux ctx x eL eI
      ≡ (failure (UnboundVariable x))
inferElabV-RVar-poly-aux-fail-nothing ctx x eL eI eqLp =
  inferElabV-RVar-poly-lookup-eq ctx x eL eI nothing eqLp

-- The poly fallback FAILS for a NON-ground schema (check-mode-only).
inferElabV-RVar-poly-aux-fail-nonground : ∀ {m} (ctx : NamedCtx m) (x : String) eL eI {schema : PolyType} {body : Syn.Expr}
  → lookupPoly (NamedCtx.polys ctx) x ≡ just (schema , body)
  → isGround schema ≡ inj₂ tt
  → inferElabV-RVar-poly-aux ctx x eL eI
      ≡ (failure (UnboundVariable x))
inferElabV-RVar-poly-aux-fail-nonground ctx x eL eI {schema} {body} eqLp eqG =
  trans (inferElabV-RVar-poly-lookup-eq ctx x eL eI _ eqLp)
        (inferElabV-RVar-poly-ground-eq ctx x eL eI schema body eqLp (inj₂ tt) eqG)

-- The poly fallback SUCCEEDS at the declared ground type, witnessed by the
-- telescope-variable rule (plan 0.103 phase 1c).
inferElabV-RVar-poly-aux-success : ∀ {m} (ctx : NamedCtx m) (x : String) eL eI {schema : PolyType} {body : Syn.Expr}
    {g : Ground schema}
  → (eqLp : lookupPoly (NamedCtx.polys ctx) x ≡ just (schema , body))
  → isGround schema ≡ inj₁ g
  → inferElabV-RVar-poly-aux ctx x eL eI
      ≡ (success (extractGround schema g) Surface.zeroUsage
                 (Surface.poly x (extractGround schema g)) 0 0)
inferElabV-RVar-poly-aux-success ctx x eL eI {schema} {body} {g = g} eqLp eqG =
  trans (inferElabV-RVar-poly-lookup-eq ctx x eL eI _ eqLp)
        (inferElabV-RVar-poly-ground-eq ctx x eL eI schema body eqLp (inj₁ g) eqG)

-- The own reference FAILS when the telescope fallback does.
inferElabV-own-fail-bridge : ∀ {m} (ctx : NamedCtx m) (x : String)
  → (eS : lookupImport (NamedCtx.sig ctx) x ≡ nothing)
  → (eI : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
  → inferElabV-RVar-poly-aux ctx x eS eI
      ≡ (failure (UnboundVariable x))
  → inferElab ctx (Raw.RResolved (own x)) ≡ (failure (UnboundVariable x))
inferElabV-own-fail-bridge ctx x eS eI polyFail =
  trans (inferElabV-own-poly-bridge ctx x eS eI) polyFail

-- POSTULATE DELETED (Option A, 2026-04-22). Phase 1 emits a proper
-- `poly` constructor; the typechecker's behavior doesn't depend on
-- body. Existential witnesses are satisfied by the `poly x T` placeholder.
-- Plan 0.103 phase 2a: J-style specialisations of the de-withed check-mode
-- polymorphic-reference stages.
poly-check-eq : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m) (err : TypeError) ls eS li eI lp eP
  → checkElabV-RVar-poly-check-aux ctx x T err (lookupImport (NamedCtx.sig ctx) x) refl (lookupImport (NamedCtx.imports ctx) x) refl
      (lookupPolyPrefix (NamedCtx.polys ctx) x) refl
    ≡ checkElabV-RVar-poly-check-aux ctx x T err ls eS li eI lp eP
poly-check-eq ctx x T err .(lookupImport (NamedCtx.sig ctx) x) refl .(lookupImport (NamedCtx.imports ctx) x) refl
  .(lookupPolyPrefix (NamedCtx.polys ctx) x) refl = refl

poly-ground-eq : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m) (err : TypeError) (schema : PolyType)
  {body prefix} eL eI (eP : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ig eG
  → checkElabV-RVar-poly-ground-aux ctx x T err schema eL eI eP (isGround schema) refl
    ≡ checkElabV-RVar-poly-ground-aux ctx x T err schema eL eI eP ig eG
poly-ground-eq ctx x T err schema eL eI eP .(isGround schema) refl = refl

-- D243: a kinded instance makes the decided premise `yes`.
poly-inst-yes : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m) (err : TypeError) {schema : PolyType}
  {body prefix} eL eI (eP : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
  → KindedInstance (NamedCtx.kinds ctx) schema T
  → (checkElabV-RVar-poly-inst-aux ctx x T err eL eI eP ¬g (kindedInstance? (NamedCtx.kinds ctx) schema T))
    ≡ success Surface.zeroUsage (Surface.poly x T) 0 0
poly-inst-yes ctx x T err {schema} eL eI eP ¬g ki with kindedInstance? (NamedCtx.kinds ctx) schema T
... | yes _ = refl
... | no ¬k = ⊥-elim (¬k ki)

checkElab-fallback-RVar-poly : ∀ {m} {ctx : NamedCtx m} (x : String) (T : Ty m)
    {schema : PolyType} {body : Syn.Expr} {prefix : PolyCtx}
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing
  → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  -- Plan 0.58 / D071: NON-ground only — a ground schema INFERS at its declared
  -- type (`wt-var-poly-instantiate-infer`), so the check-mode fallback (poly
  -- node at arbitrary `T`) fires only when infer failed, i.e. non-ground.
  → isGround schema ≡ inj₂ tt
  → KindedInstance (NamedCtx.kinds ctx) schema T
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ fr →
      checkElab ctx (Raw.RResolved (own x)) T
        ≡ success Surface.zeroUsage eE d fr)))
-- Plan 0.103 phase 2a: each stage of the de-withed fallback reduces on its
-- decided premise; the kinded instance makes `kindedInstance?` say yes.
checkElab-fallback-RVar-poly {ctx = ctx} x T {schema = schema} eqS eqImp eqP eqG inst
  with inferElab ctx (Raw.RResolved (own x))
     | inferElabV-own-fail-bridge ctx x eqS eqImp
         (inferElabV-RVar-poly-aux-fail-nonground ctx x eqS eqImp
            (lookupPolyPrefix⇒lookupPoly (NamedCtx.polys ctx) x eqP) eqG)
... | (failure err ) | refl =
  _ , _ , _ ,
  trans ((poly-check-eq ctx x T err nothing eqS nothing eqImp (just _) eqP))
    (trans ((poly-ground-eq ctx x T err schema eqS eqImp eqP (inj₂ tt) eqG))
           (poly-inst-yes ctx x T err eqS eqImp eqP (isGround-inj₂→¬Ground schema eqG) inst))

-- Plan 0.58 / D071: the INFER-mode twin — a GROUND telescope name infers at
-- its declared type, emitting the `poly` placeholder (Phase 2 splices).
checkElab-fallback-RVar-poly-infer : ∀ {m} {ctx : NamedCtx m} (x : String)
    {schema : PolyType} {body : Syn.Expr} {g : Ground schema}
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing
  → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPoly (NamedCtx.polys ctx) x ≡ just (schema , body)
  → isGround schema ≡ inj₁ g
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ fr →
      inferElab ctx (Raw.RResolved (own x))
        ≡ success (extractGround schema g) Surface.zeroUsage eE d fr)))
checkElab-fallback-RVar-poly-infer {ctx = ctx} x eqS eqImp eqPoly eqG =
  _ , _ , _ ,
    trans (inferElabV-own-poly-bridge ctx x eqS eqImp)
          (inferElabV-RVar-poly-aux-success ctx x eqS eqImp eqPoly eqG)
module DPoly where
  open import Once.TypeCheck.Elaborate
    using (given-poly; given-poly-g; given-poly-a; given-poly-m; given-poly-π; isGround-inj₂→¬Ground)
  open import Once.Type.Match using (instantiate)
  open import Once.Type.MatchCorrect using (instantiate-complete; instantiate-sound)
  open import Once.Type.Determined using (codVarsInDom?; cod-determined; arrowSchema?)
  open import Once.Type.SubDecide using (_⊑π?_)
  open import Once.Type.Instance using (KindedInstance)
  open import Once.Type.Rigid using (kindedInstance?)
  open import Once.TypeCheck.Scope using (lookupPolyPrefix)
  open import Relation.Nullary using (yes; no)
  open import Data.String using (String)
  open import Data.Sum using (inj₂)
  open import Data.Unit using (tt)
  open import Data.Empty using (⊥-elim)

  ⇒-parts : ∀ {m} {a b c d : Ty m} {k k′} → (a T.⇒[ k ] b) ≡ (c T.⇒[ k′ ] d) → (a ≡ c) × (b ≡ d)
  ⇒-parts refl = refl , refl

  arrow-parts : ∀ {m} {s sd sc : T.PolyType} {π′} {A B : Ty m} (θ : String → Ty m)
    → T.ArrowSchema s sd sc π′ → T.substPoly θ s ≡ (A T.⇒[ T.mk-kind T.Many π′ ] B)
    → (T.substPoly θ sd ≡ A) × (T.substPoly θ sc ≡ B)
  arrow-parts θ T.as-pure e = ⇒-parts e
  arrow-parts θ T.as-eff  e = ⇒-parts e
  arrow-parts θ T.as-act  e = ⇒-parts e

  gp-eq : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : T.Purity) err ll eL li eI lp eP
    → given-poly ctx x A π err (lookupImport (Classify.NamedCtx.sig ctx) x) refl (lookupImport (Classify.NamedCtx.imports ctx) x) refl
        (lookupPolyPrefix (Classify.NamedCtx.polys ctx) x) refl
      ≡ given-poly ctx x A π err ll eL li eI lp eP
  gp-eq ctx x A π err .(lookupImport (Classify.NamedCtx.sig ctx) x) refl .(lookupImport (Classify.NamedCtx.imports ctx) x) refl
    .(lookupPolyPrefix (Classify.NamedCtx.polys ctx) x) refl = refl

  gg-eq : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : T.Purity) err schema {body prefix} eL eI
    (eP : lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ig eG
    → given-poly-g ctx x A π err schema eL eI eP (T.isGround schema) refl ≡ given-poly-g ctx x A π err schema eL eI eP ig eG
  gg-eq ctx x A π err schema eL eI eP .(T.isGround schema) refl = refl

  gm-eq : ∀ {mₜ} (ctx : NamedCtx mₜ) (x : String) (A : Ty mₜ) (π : T.Purity) err {schema sd sc π′ body prefix} eL eI
    (eP : lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc) mσ eS
    → given-poly-m ctx x A π err eL eI eP ¬g as inc (instantiate sd A) refl
      ≡ given-poly-m ctx x A π err eL eI eP ¬g as inc mσ eS
  gm-eq ctx x A π err {sd = sd} eL eI eP ¬g as inc .(instantiate sd A) refl = refl

  -- The codomain the elaborator computes IS the derivation's.
  at-π : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : T.Purity) err
    {B : Ty m} {π′ : T.Purity} {schema sd sc : T.PolyType} {body prefix} eL eI
    (eP : lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc) (θ₀ : String → Ty m) (e₀ : T.substPoly θ₀ sd ≡ A)
    → T.substPoly θ₀ sc ≡ B → π′ ⊑π π → KindedInstance (NamedCtx.kinds ctx) schema (A T.⇒[ T.mk-kind T.Many π′ ] B)
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        (given-poly-π ctx x A π err eL eI eP ¬g as inc θ₀ e₀ (π′ ⊑π? π)) ≡ success B Surface.zeroUsage eE d f
  at-π ctx x A π err {π′ = π′} {schema = schema} {sc = sc} eL eI eP ¬g as inc θ₀ e₀ refl g ki with π′ ⊑π? π
  ... | no ¬g′ = ⊥-elim (¬g′ g)
  ... | yes _ with kindedInstance? (NamedCtx.kinds ctx) schema (A T.⇒[ T.mk-kind T.Many π′ ] T.substPoly θ₀ sc)
  ...   | yes _ = _ , _ , _ , refl
  ...   | no ¬k = ⊥-elim (¬k ki)

  at-m : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : T.Purity) err
    {B : Ty m} {π′ : T.Purity} {schema sd sc : T.PolyType} {body prefix} eL eI
    (eP : lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc)
    (θ : String → Ty m) (eθ : T.substPoly θ schema ≡ (A T.⇒[ T.mk-kind T.Many π′ ] B)) (g : π′ ⊑π π) (ki : KindedInstance (NamedCtx.kinds ctx) schema (A T.⇒[ T.mk-kind T.Many π′ ] B))
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        (given-poly-m ctx x A π err eL eI eP ¬g as inc (instantiate sd A) refl) ≡ success B Surface.zeroUsage eE d f
  at-m ctx x A π err {sd = sd} {sc = sc} eL eI eP ¬g as inc θ eθ g ki =
    let (ed , ec) = arrow-parts θ as eθ
        (σ , eS)  = instantiate-complete sd A (θ , ed)
        θ₀        = proj₁ (instantiate-sound sd A eS)
        e₀        = proj₂ (instantiate-sound sd A eS)
        eB        = trans (cod-determined {sd = sd} {sc = sc} inc θ₀ θ (trans e₀ (sym ed))) ec
        (eE , d , f , r) = at-π ctx x A π err eL eI eP ¬g as inc θ₀ e₀ eB g ki
    in eE , d , f , trans ((gm-eq ctx x A π err eL eI eP ¬g as inc (just σ) eS)) r

  from-arrow : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : T.Purity) err
    {B : Ty m} {π′ : T.Purity} {schema sd sc : T.PolyType} {body prefix} eL eI
    (eP : lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc)
    (θ : String → Ty m) (eθ : T.substPoly θ schema ≡ (A T.⇒[ T.mk-kind T.Many π′ ] B)) (g : π′ ⊑π π) (ki : KindedInstance (NamedCtx.kinds ctx) schema (A T.⇒[ T.mk-kind T.Many π′ ] B))
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        (given-poly-a ctx x A π err eL eI eP ¬g (arrowSchema? schema)) ≡ success B Surface.zeroUsage eE d f
  from-arrow ctx x A π err {sd = sd} {sc = sc} eL eI eP ¬g T.as-pure inc θ eθ g ki with codVarsInDom? sd sc
  ... | yes inc′ = at-m ctx x A π err eL eI eP ¬g T.as-pure inc′ θ eθ g ki
  ... | no ¬inc = ⊥-elim (¬inc inc)
  from-arrow ctx x A π err {sd = sd} {sc = sc} eL eI eP ¬g T.as-eff inc θ eθ g ki with codVarsInDom? sd sc
  ... | yes inc′ = at-m ctx x A π err eL eI eP ¬g T.as-eff inc′ θ eθ g ki
  ... | no ¬inc = ⊥-elim (¬inc inc)
  from-arrow ctx x A π err {sd = sd} {sc = sc} eL eI eP ¬g T.as-act inc θ eθ g ki with codVarsInDom? sd sc
  ... | yes inc′ = at-m ctx x A π err eL eI eP ¬g T.as-act inc′ θ eθ g ki
  ... | no ¬inc = ⊥-elim (¬inc inc)

  -- The whole chain, from the lookups (the head's inference has failed).
  from-lookups : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : T.Purity) err
    {B : Ty m} {π′ : T.Purity} {schema sd sc : T.PolyType} {body prefix}
    (eL : lookupImport (Classify.NamedCtx.sig ctx) x ≡ nothing) (eI : lookupImport (Classify.NamedCtx.imports ctx) x ≡ nothing)
    (eP : lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) (¬g : ¬ T.Ground schema)
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc)
    (θ : String → Ty m) (eθ : T.substPoly θ schema ≡ (A T.⇒[ T.mk-kind T.Many π′ ] B)) (g : π′ ⊑π π) (ki : KindedInstance (NamedCtx.kinds ctx) schema (A T.⇒[ T.mk-kind T.Many π′ ] B))
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        (given-poly ctx x A π err (lookupImport (Classify.NamedCtx.sig ctx) x) refl (lookupImport (Classify.NamedCtx.imports ctx) x) refl
                 (lookupPolyPrefix (Classify.NamedCtx.polys ctx) x) refl) ≡ success B Surface.zeroUsage eE d f
  from-lookups ctx x A π err {schema = schema} eL eI eP ¬g as inc θ eθ g ki =
    let eG = ¬Ground-isGround-inj₂ schema ¬g
        (eE , d , f , r) = from-arrow ctx x A π err eL eI eP (isGround-inj₂→¬Ground schema eG) as inc θ eθ g ki
    in eE , d , f ,
       trans ((gp-eq ctx x A π err nothing eL nothing eI (just _) eP))
         (trans ((gg-eq ctx x A π err schema eL eI eP (inj₂ tt) eG)) r)

------------------------------------------------------------------------
-- A declaration of the signature, and an own monomorphic definition
------------------------------------------------------------------------

infer-complete-RResolved : ∀ {m} {ctx : NamedCtx m} {cn : CanonicalName} {T : Type}
  → WordName cn
  → lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ just T
  → IsConcrete T
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RResolved cn) ≡ success (wk₀ T) zeroUsage eE d f
infer-complete-RResolved {ctx = ctx} {cn = cn} {T = T} wn eq conc =
  go T conc eq
  where
    helper : ∀ (lhs : Maybe (Ty _))
           → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ lhs)
           → inferElabV-RResolved-aux ctx cn
               (lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn)) refl
             ≡ inferElabV-RResolved-aux ctx cn lhs eq'
    helper _ refl = refl
    helperArr : ∀ {A B : Ty _} {π : T.Purity}
              → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn)
                        ≡ just (A T.⇒[ T.mk-kind T.Many π ] B))
              → (mbA : Maybe (Base ∅ₖ A)) (eqb : isBaseType? A ≡ mbA)
                (mcB : Maybe (Base ∅ₖ B)) (eqc : isBaseType? B ≡ mcB)
              → inferElabV-RResolved-arrow-aux ctx cn eq' (isBaseType? A) refl (isBaseType? B) refl
                ≡ inferElabV-RResolved-arrow-aux ctx cn eq' mbA eqb mcB eqc
    helperArr _ _ refl _ refl = refl
    helperVal : ∀ {ty}
              → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ just ty)
              → (mc : Maybe (IsConcrete ty)) (eqc : isConcrete? ty ≡ mc)
              → inferElabV-RResolved-value-aux ctx cn ty eq' (isConcrete? ty) refl
                ≡ inferElabV-RResolved-value-aux ctx cn ty eq' mc eqc
    helperVal _ _ refl = refl
    helperW : ∀ (k : WordName cn → E.InferElabResult (NamedCtx.debruijn ctx)) (b : Bool) (e : wordNameB cn ≡ b)
            → E.inferElabV-RResolved-word ctx cn k (wordNameB cn) refl ≡ E.inferElabV-RResolved-word ctx cn k b e
    helperW _ _ refl = refl
    wt : wordNameB cn ≡ true
    wt = T-true (wordNameB cn) wn
      where
        T-true : ∀ b → Data.Bool.T b → b ≡ true
        T-true true _ = refl
    go : ∀ (T' : Type) → IsConcrete T'
       → (eq' : lookupImport (Classify.NamedCtx.sig ctx) (showCanonical cn) ≡ just T')
       → ∃[ eE ] ∃[ d ] ∃[ f ]
           inferElab ctx (RResolved cn) ≡ success (wk₀ T') zeroUsage eE d f
    go (A ⇒[ T.mk-kind Many π ] B) (con-fun bA cB) eq' = _ , _ , _ ,
      trans (trans (helper _ eq') (helperArr eq' _ (proj₂ (isBaseType?-complete bA)) _ (proj₂ (isBaseType?-complete cB)))) (helperW _ _ wt)
    go (A ⇒[ T.mk-kind One  π ] B) conc' eq' = _ , _ , _ ,
      trans (trans (helper _ eq') (helperVal eq' _ (proj₂ (isConcrete?-complete conc')))) (helperW _ _ wt)
    go (A ⇒[ T.mk-kind Zero π ] B) conc' eq' = _ , _ , _ ,
      trans (trans (helper _ eq') (helperVal eq' _ (proj₂ (isConcrete?-complete conc')))) (helperW _ _ wt)
    go Unit          _ eq' = _ , _ , _ , trans (helper _ eq') (helperW _ _ wt)
    go Void          _ eq' = _ , _ , _ , trans (helper _ eq') (helperW _ _ wt)
    go Int           _ eq' = _ , _ , _ , trans (helper _ eq') (helperW _ _ wt)
    go Float         _ eq' = _ , _ , _ , trans (helper _ eq') (helperW _ _ wt)
    go (A * B) conc' eq' = _ , _ , _ ,
      trans (trans (helper _ eq') (helperVal eq' _ (proj₂ (isConcrete?-complete conc')))) (helperW _ _ wt)
    go (A + B) conc' eq' = _ , _ , _ ,
      trans (trans (helper _ eq') (helperVal eq' _ (proj₂ (isConcrete?-complete conc')))) (helperW _ _ wt)
    go (T.μ F)  (con-base ()) eq'
    go (T.ν F _)  (con-base ()) eq'

infer-complete-RResolved-own : ∀ {m} {ctx : NamedCtx m} {x : String} {T : Type}
  → lookupImport (Classify.NamedCtx.sig ctx) x ≡ nothing
  → lookupImport (Classify.NamedCtx.imports ctx) x ≡ just T
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RResolved (own x)) ≡ success (wk₀ T) zeroUsage eE d f
infer-complete-RResolved-own {ctx = ctx} {x = x} {T = T} ns eq = _ , _ , _ , trans (h1 _ ns) (h2 _ eq)
  where
    h1 : ∀ (lhs : Maybe Type) (e′ : lookupImport (Classify.NamedCtx.sig ctx) x ≡ lhs)
       → inferElabV-RResolved-aux ctx (own x) (lookupImport (Classify.NamedCtx.sig ctx) x) refl
         ≡ inferElabV-RResolved-aux ctx (own x) lhs e′
    h1 _ refl = refl
    h2 : ∀ (lhs : Maybe Type) (e′ : lookupImport (Classify.NamedCtx.imports ctx) x ≡ lhs)
       → inferElabV-RResolved-own-aux ctx x ns (lookupImport (Classify.NamedCtx.imports ctx) x) refl
         ≡ inferElabV-RResolved-own-aux ctx x ns lhs e′
    h2 _ refl = refl


-- A non-ground telescope entry does not infer.
poly-head-fails : ∀ {m} (ctx : NamedCtx m) (x : String) {schema body prefix}
  → lookupImport (Classify.NamedCtx.sig ctx) x ≡ nothing → lookupImport (Classify.NamedCtx.imports ctx) x ≡ nothing
  → lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  → ¬ T.Ground schema
  → inferElab ctx (RResolved (own x)) ≡ (failure (Error.UnboundVariable x))
poly-head-fails ctx x {schema} eS eI eP ¬g =
  inferElabV-own-fail-bridge ctx x eS eI
    (inferElabV-RVar-poly-aux-fail-nonground ctx x eS eI
       (lookupPolyPrefix⇒lookupPoly (Classify.NamedCtx.polys ctx) x eP) (¬Ground-isGround-inj₂ schema ¬g))

-- `d-infer`: the inferred arrow's domain converts back, its grade up.
given-infer-complete : ∀ {m} {ctx : NamedCtx m} {e : Syn.Expr} {A A′ B : Ty m} {π π′ : T.Purity}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)} {eE : _} {d f : ℕ}
    (r : InferElabResult (Once.TypeCheck.Scope.NamedCtx.debruijn ctx))
  → r ≡ success (A′ T.⇒[ T.mk-kind T.Many π′ ] B) Ψ eE d f
  → A <: A′ → π′ ⊑π π
  → ∃[ eE′ ] ∃[ d′ ] ∃[ f′ ] (given-infer ctx e A π r) ≡ success B Ψ eE′ d′ f′
given-infer-complete {A = A} {A′ = A′} {π = π} {π′ = π′} (success _ _ _ _ _ ) refl a g
  with A <:? A′ | π′ ⊑π? π
... | yes _ | yes _ = _ , _ , _ , refl
... | no ¬a | _     = ⊥-elim (¬a a)
... | yes _ | no ¬g = ⊥-elim (¬g g)

infer-complete-RPair : ∀ {m} {ctx : NamedCtx m} (a b : Syn.Expr) {A B : Ty m}
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {aE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ A}
    {bE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ B}
    {dA dB fA fB : ℕ}
  → inferElab ctx a ≡ success A Ψ₁ aE dA fA
  → inferElab ctx b ≡ success B Ψ₂ bE dB fB
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RPair a b) ≡ success (A * B) (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RPair {ctx = ctx} a b eqA eqB
  with inferElab ctx a | eqA
... | success _ _ _ _ _  | refl
    with inferElab ctx b | eqB
...   | success _ _ _ _ _  | refl = _ , _ , _ , refl

-- `-e` at a number type with `Neg`: the elaborator's dispatch reduces on the
-- witnesses (`numView-num`, `has?-yes`).
infer-complete-RNeg : ∀ {m} {ctx : NamedCtx m} (e : Syn.Expr) (a : NumTy) (h : Has a Neg)
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE' : SExpr (Classify.NamedCtx.debruijn ctx) Ψ ⌜ a ⌝ⁿ}
    {d' f' : ℕ}
  → inferElab ctx e ≡ success ⌜ a ⌝ⁿ Ψ eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RNeg e) ≡ success ⌜ a ⌝ⁿ Ψ eE d f
infer-complete-RNeg {ctx = ctx} e int int-neg eqE with inferElab ctx e | eqE
... | _ | refl = _ , _ , _ , refl
infer-complete-RNeg {ctx = ctx} e float float-neg eqE with inferElab ctx e | eqE
... | _ | refl = _ , _ , _ , refl

infer-complete-RAnnot : ∀ {m} {ctx : NamedCtx m} (e : Syn.Expr) (T : Type)
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE' : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (wk₀ T)}
    {d' f' : ℕ}
  → checkElab ctx e (wk₀ T) ≡ success Ψ eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RAnnot e T) ≡ success (wk₀ T) Ψ eE d f
infer-complete-RAnnot {ctx = ctx} e T eqC
  with checkElab ctx e (wk₀ T) | eqC
... | success _ _ _ _  | refl = _ , _ , _ , refl

------------------------------------------------------------------------
-- Completeness notes
--
-- The full theorem `∀ (d : ctx ⊢ e ∶ A ⨾ Ψ) → e-is-not-RLam e →
-- ∃ eE d' f'. inferElab ctx e ≡ success A Ψ eE d' f'` walks the
-- derivation structurally, invoking the per-rule completeness
-- lemmas above. Each rule becomes one case of the pattern match.
-- Remaining work (mechanical, mirrors the soundness file):
--
--   * t-let, t-case, t-app, t-binop-*, t-var-local, t-var-import,
--     t-id-app, t-fst-app, t-snd-app, t-terminal-app.
--   * `check-complete-lam` for the `t-lam` rule specifically, showing
--     `checkElab ctx (RLam x body) (A ⇒[ q ] B)` succeeds.
------------------------------------------------------------------------

infer-complete-RLet : ∀ {m} {ctx : NamedCtx m} (x : String) (e₁ e₂ : Syn.Expr)
    {A B : Ty m} {q : Quantity}
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ A}
    {e₂E : SExpr (Classify.NamedCtx.debruijn (Classify.extendNamedCtx ctx x A))
                 (q SCx.∷ Ψ₂) B}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success A Ψ₁ e₁E d₁ f₁
  → inferElab (Classify.extendNamedCtx ctx x A) e₂
      ≡ success B (q SCx.∷ Ψ₂) e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RLet x e₁ e₂) ≡ success B (Ψ₂ +ᵘ (q *ᵘ Ψ₁)) eE d f
infer-complete-RLet {ctx = ctx} x e₁ e₂ {A = A} eq₁ eq₂
  with inferElab ctx e₁ | eq₁
... | success _ _ _ _ _  | refl
    with inferElab (Classify.extendNamedCtx ctx x A) e₂ | eq₂
...   | success _ (_ SCx.∷ _) _ _ _  | refl = _ , _ , _ , refl
------------------------------------------------------------------------
-- Variable lookup (local / import)
------------------------------------------------------------------------

infer-complete-RVar-local : ∀ {m} {ctx : NamedCtx m} (x : String) {A : Ty m}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE' : Srf.SVar (Classify.NamedCtx.debruijn ctx) Ψ A}
  → lookupLocal ctx x ≡ just (A , Ψ , eE')
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RVar x) ≡ success A Ψ eE d f
infer-complete-RVar-local {ctx = ctx} x {A} {Ψ} {eE'} eqLoc
  = _ , _ , _ , (helper _ eqLoc)
  where
    helper : ∀ (lhs : Maybe (∃[ A' ] ∃[ Ψ' ] (Srf.SVar (Classify.NamedCtx.debruijn ctx) Ψ' A')))
           → (eq' : lookupLocal ctx x ≡ lhs)
           → inferElabV-RVar-lookup-aux ctx x (lookupLocal ctx x) refl
             ≡ inferElabV-RVar-lookup-aux ctx x lhs eq'
    helper _ refl = refl

------------------------------------------------------------------------
-- RBinOp: one lemma over the table (plan 0.150 N10)
------------------------------------------------------------------------

-- The decision, at its witness.
has-yes : ∀ {m} (ctx : NamedCtx m) (op : BinOp) (a : NumTy) {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    (e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ ⌜ a ⌝ⁿ) (e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ ⌜ a ⌝ⁿ)
    (d fr : ℕ) (h : Has a (theory (binSym op))) (dh : Dec (Has a (theory (binSym op)))) → dh ≡ yes h
  → E.inferElabV-RBinOp-has ctx op a e₁E e₂E d fr dh ≡ success (symCod a (shape (binSym op))) (Ψ₁ +ᵘ Ψ₂) (numBin op a h e₁E e₂E) d fr
has-yes ctx op a e₁E e₂E d fr h _ refl = refl

infer-complete-RBinOp : ∀ {m} {ctx : NamedCtx m} (op : BinOp) (a : NumTy) (h : Has a (theory (binSym op)))
    (e₁ e₂ : Syn.Expr)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ ⌜ a ⌝ⁿ}
    {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ ⌜ a ⌝ⁿ}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success ⌜ a ⌝ⁿ Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success ⌜ a ⌝ⁿ Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success (symCod a (shape (binSym op))) (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp {ctx = ctx} op int h e₁ e₂ {e₁E = e₁E} {e₂E} {d₁} {d₂} {f₁} {f₂} eq₁ eq₂
  with inferElab ctx e₁ | eq₁ | inferElab ctx e₂ | eq₂
... | _ | refl | _ | refl = _ , _ , _ , has-yes ctx op int e₁E e₂E (d₁ Data.Nat.⊔ d₂) f₂ h _ (has?-yes h)
infer-complete-RBinOp {ctx = ctx} op float h e₁ e₂ {e₁E = e₁E} {e₂E} {d₁} {d₂} {f₁} {f₂} eq₁ eq₂
  with inferElab ctx e₁ | eq₁ | inferElab ctx e₂ | eq₂
... | _ | refl | _ | refl = _ , _ , _ , has-yes ctx op float e₁E e₂E (d₁ Data.Nat.⊔ d₂) f₂ h _ (has?-yes h)

------------------------------------------------------------------------
-- RLam check mode
------------------------------------------------------------------------

decideLeq-just : ∀ q' q → (q' ≤qᵇ q) ≡ true
               → ∃ λ (eq : (q' ≤qᵇ q) ≡ true)
               → E.decideLeq q' q ≡ just eq
decideLeq-just Zero Zero refl = refl , refl
decideLeq-just Zero One  refl = refl , refl
decideLeq-just Zero Many refl = refl , refl
decideLeq-just One  One  refl = refl , refl
decideLeq-just One  Many refl = refl , refl
decideLeq-just Many Many refl = refl , refl

check-complete-RLam : ∀ {m} (ctx : NamedCtx m) (x : String) (body : Syn.Expr)
    (A : Ty m) (q q' : Quantity) (B : Ty m)
    {Ψ' : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE' : SExpr (Classify.NamedCtx.debruijn (Classify.extendNamedCtx ctx x A))
                 (q' SCx.∷ Ψ') B}
    {d' f' : ℕ} {π : T.Purity}
  → (q' Once.Type.Grade.≤qᵇ q) ≡ true
  → checkElab (Classify.extendNamedCtx ctx x A) body B
      ≡ success (q' SCx.∷ Ψ') eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      checkElab ctx (Raw.RLam x body) (A T.⇒[ T.mk-kind q π ] B) ≡ success Ψ' eE d f
check-complete-RLam ctx x body A q q' B {Ψ' = Ψ'} leqEq eqC
  with checkElab (Classify.extendNamedCtx ctx x A) body B | eqC
... | success (_ SCx.∷ _) _ _ _  | refl
    with E.decideLeq q' q | decideLeq-just q' q leqEq
...   | just _ | _ , refl = _ , _ , _ , refl

------------------------------------------------------------------------
-- RDestruct (case / sum elimination)
------------------------------------------------------------------------

infer-complete-RDestruct : ∀ {m} {ctx : NamedCtx m} (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr)
    (xR : String) (eR : Syn.Expr) {A B : Ty m}
    {Ψs : Surface.Usage (Classify.NamedCtx.size ctx)}
    {scrutE : SExpr (Classify.NamedCtx.debruijn ctx) Ψs (A + B)}
    {ds fs : ℕ}
    (C₁ C₂ C : Ty m) (J : C₁ ⊔ C₂ ≔ C) {qℓ qr : Quantity}
    {Ψₗ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eLE : SExpr (Classify.NamedCtx.debruijn
                    (Classify.extendNamedCtx ctx xL A))
                 (qℓ SCx.∷ Ψₗ) C₁}
    {dL fL : ℕ}
    {Ψᵣ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eRE : SExpr (Classify.NamedCtx.debruijn
                    (Classify.extendNamedCtx ctx xR B))
                 (qr SCx.∷ Ψᵣ) C₂}
    {dR fR : ℕ}
  → inferElab ctx scrut ≡ success (A + B) Ψs scrutE ds fs
  → inferElab (Classify.extendNamedCtx ctx xL A) eL
      ≡ success C₁ (qℓ SCx.∷ Ψₗ) eLE dL fL
  → inferElab (Classify.extendNamedCtx ctx xR B) eR
      ≡ success C₂ (qr SCx.∷ Ψᵣ) eRE dR fR
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RDestruct scrut xL eL xR eR)
        ≡ success C (Ψs +ᵘ (Ψₗ Surface.⊔ᵘ Ψᵣ)) eE d f
infer-complete-RDestruct {ctx = ctx} scrut xL eL xR eR {A = A} {B = B} C₁ C₂ C J eqS eqL eqR
  with inferElab ctx scrut | eqS
... | success (_ + _) _ _ _ _  | refl
    with inferElab (Classify.extendNamedCtx ctx xL A) eL | eqL
...   | success _ (_ SCx.∷ _) _ _ _  | refl
      with inferElab (Classify.extendNamedCtx ctx xR B) eR | eqR
...     | success _ (_ SCx.∷ _) _ _ _  | refl =
  -- D322: the checker's join decision finds the derivation's join.
  _ , _ , _ , cong (λ x → (E.inferElabV-RDestruct-join ctx scrut xL eL xR eR A B _ _ _ _ _ _ _ x))
                   (proj₂ (join?-complete J))

------------------------------------------------------------------------
-- Generic RApp
------------------------------------------------------------------------

-- Plan 0.4 T1, change 1 (2026-04-30): premise on `x` is now a
-- `checkElab` success, matching the new bidirectional rule in
-- `inferElab` (it CHECKs the arg at the synthesized domain rather
-- than inferring it). Call sites that have a `t-app`-style
-- derivation already provide ⊢ᶜ for x; those that have an