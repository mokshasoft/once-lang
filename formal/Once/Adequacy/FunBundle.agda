-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.FunBundle — Plan 0.55: the per-function bundled
-- compiled+typed selector that discharges `main-extract`'s selector alignment.
--
-- D241 (plan 0.103 6c′): indexed by the module TELESCOPE walk.
--
-- ONE inductive `FunBundle` carries, per entry, the compile witnesses
-- (`rf`/`ce`/`cf`+`irFun`) as BOUND fields, so neither `resolveFunType` nor
-- `compileFun` is ever recomputed over an abstract `fi` (the old neutral). The
-- `findMain`-style selector (`bundle-find`) reads from it, with the compiler's
-- own decisions, so their agreement is definitional.
--
-- Promoted from the validated `BundlePOC.agda` blueprint. The two plumbing
-- lemmas are PROVEN here:
--   * `compileFun-ce`          — ce-returning refinement of `compileFun-sound`.
--   * `bundle→compiled≡compiled` — `caf-go-bundle` ↔ `compileAllFuns-go`.
------------------------------------------------------------------------

module Once.Adequacy.FunBundle where


open import Once.Internal.Typing.Scope using (PolyCtx)
open import Once.TypeCheck.Classify using (TopCtx; ctxWithImportsAndPolys)
open import Once.Internal.Module using (ModTele; []; ffi; mono; poly; MainIn; MonoBody)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String; _==_) renaming ()
open import Once.Spec.Name using (bare)
open import Once.CanonicalName using (_≟ᶜ_)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Function using (case_of_)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Spec.Grade using (mk-kind; Many; eff)
open import Once.Internal.Type using (Unit; Type; _⇒[_]_)
import Once.Compile as C
import Once.IR as IR
import Once.Parser as Parser
open import Once.Internal.Type.Instance using (rigidOf)
open import Once.Internal.Type.WellFormed using (RigidFree)
open import Once.Type.Rigid using (rigidFree?)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Internal.Type.Honest using (HonestFFI; honest?)
import Once.Surface.Syntax as Srf
open import Once.Internal.Context using (Usage)
open import Once.Surface.Syntax using (Expr)
open import Once.TypeCheck.Elaborate as TE
  using (checkElab)
open import Once.Internal.Typing.Scope using (NamedCtx)
open import Once.Internal.Syntax using (RawExpr)
open import Once.TypeCheck.Soundness using (check-sound; infer-soundV)
open import Once.Internal.Principal using (below)
open import Once.Adequacy.PrincipalDecide using (firstChecking-sound)
open import Once.Parser using (FunInfo)
import Once.Parser.Module as Module
import Once.Parser.Module.Core as Core
import Data.String as String
import Once.Internal.Typing
import Once.Internal.Type.DecEq
open FunInfo
import Once.Adequacy.AcceptSound as AS
open import Once.Compile using (findMain; findMain-here; mainEntry; moduleToIR; moduleToIR-aux)
open import Once.Internal.Type.Sub using (_<:_)
open import Once.Type.Sub using (_<:?_)
open import Once.Adequacy.MainIRForm using (bare-injective)
import Once.Adequacy.ModuleComplete as MC

EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

ctxC : C.CScope → NamedCtx
ctxC sc = ctxWithImportsAndPolys (C.ctop sc) (C.cpolys sc)

-- R8: a definition's elaboration succeeded in its own mode — checked at its
-- signature, or synthesized.
ElabOK : Maybe Type → (ctx : NamedCtx) → RawExpr → (ty : Type) → (Ψ : Usage (NamedCtx.size ctx))
       → Expr (NamedCtx.debruijn ctx) Ψ ty → ℕ → ℕ → Set
ElabOK (just _) ctx e ty Ψ se d f = checkElab ctx e ty ≡ TE.success Ψ se d f
ElabOK nothing  ctx e ty Ψ se d f = TE.inferElab ctx e ≡ TE.success ty Ψ se d f

-- …and so its body has a derivation in that mode.
elabOK-sound : ∀ (ft : Maybe Type) (ctx : NamedCtx) (e : RawExpr) (ty : Type) {Ψ se d f}
             → ElabOK ft ctx e ty Ψ se d f → MonoBody ft ctx e ty Ψ
elabOK-sound (just _) ctx e ty ce = check-sound ctx e ty ce
elabOK-sound nothing  ctx e ty ce = infer-soundV ctx e ce

data FunBundle : C.CScope → List Parser.Entry → Set where
  bnil  : ∀ {sc} → FunBundle sc []
  bffi  : ∀ {sc fi ty es} {c : IsConcrete ty} {h : HonestFFI ty} {g : RigidFree ty}
        → funIsPrimitive fi ≡ true → funType fi ≡ just ty
        → isConcrete? ty ≡ just c → honest? ty ≡ just h → rigidFree? ty ≡ just g
        → FunBundle (C.extendSig sc (funName fi) ty) es      -- D274: Σ grows
        → FunBundle sc (Parser.e-fun fi ∷ es)
  bcons : ∀ {sc fi es ty}
    {Ψ  : Usage (NamedCtx.size (ctxC sc))}
    {se : Expr (NamedCtx.debruijn (ctxC sc)) Ψ ty}
    {d f : ℕ}
    {irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
    (ep : funIsPrimitive fi ≡ false) →
    (rf : C.resolveFunType (C.ctop sc) (C.cpolys sc) (funType fi) (funBody fi) ≡ inj₂ ty) →
    (fc : C.firstChecking (ctxC sc) (funBody fi) (below ty) ≡ nothing) →
    {g : RigidFree ty} → (eg : rigidFree? ty ≡ just g) →
    (ce : ElabOK (funType fi) (ctxC sc) (funBody fi) ty Ψ se d f) →
    (cf : C.compileFunM (funType fi) IR.Heap false (C.ctop sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
            (funName fi) ty (funBody fi) ≡ inj₂ irFun) →
    FunBundle (C.extendScope sc (funName fi) ty) es →
    FunBundle sc (Parser.e-fun fi ∷ es)
  bpoly : ∀ {sc pfi es}
    {Ψ  : Usage (NamedCtx.size (ctxC sc))}
    {se : Expr (NamedCtx.debruijn (ctxC sc)) Ψ (rigidOf (Parser.PolyFunInfo.pfunType pfi))}
    {d f : ℕ} →
    (fc : C.firstChecking (ctxC sc) (Parser.PolyFunInfo.pfunBody pfi) (below (rigidOf (Parser.PolyFunInfo.pfunType pfi))) ≡ nothing) →
    (ce : checkElab (ctxC sc) (Parser.PolyFunInfo.pfunBody pfi) (rigidOf (Parser.PolyFunInfo.pfunType pfi)) ≡ TE.success Ψ se d f) →
    FunBundle (C.addEntry sc pfi) es →
    FunBundle sc (Parser.e-poly pfi ∷ es)

compileFunBody-ce : ∀ (doOpt : Bool) (ctx : TopCtx) (polys : PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (expr : RawExpr) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFunBody IR.Heap doOpt ctx polys impsOf name ty expr ≡ inj₂ ir →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndPolys ctx polys)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    checkElab (ctxWithImportsAndPolys ctx polys) expr ty ≡ TE.success Ψ se d f))))
compileFunBody-ce doOpt ctx polys impsOf name ty expr eq =
  AS.compileFunBody-aux-success doOpt ctx polys impsOf name ty refl
    (TE.checkElabV (ctxWithImportsAndPolys ctx polys) expr ty) eq

compileFun-main-aux-ce : ∀ (doOpt : Bool) (ctx : TopCtx) (polys : PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (expr : RawExpr) (vm : String ⊎ ⊤) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun-main-aux IR.Heap doOpt ctx polys impsOf name ty expr vm ≡ inj₂ ir →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndPolys ctx polys)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    checkElab (ctxWithImportsAndPolys ctx polys) expr ty ≡ TE.success Ψ se d f))))
compileFun-main-aux-ce doOpt ctx polys impsOf name ty expr (inj₁ err) ()
compileFun-main-aux-ce doOpt ctx polys impsOf name ty expr (inj₂ _) eq =
  compileFunBody-ce doOpt ctx polys impsOf name ty expr eq

compileFun-aux-ce : ∀ (doOpt : Bool) (ctx : TopCtx) (polys : PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (expr : RawExpr) (b : Bool) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun-aux IR.Heap doOpt ctx polys impsOf name ty expr b ≡ inj₂ ir →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndPolys ctx polys)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    checkElab (ctxWithImportsAndPolys ctx polys) expr ty ≡ TE.success Ψ se d f))))
compileFun-aux-ce doOpt ctx polys impsOf name ty expr true eq =
  compileFun-main-aux-ce doOpt ctx polys impsOf name ty expr (C.validateMain ty) eq
compileFun-aux-ce doOpt ctx polys impsOf name ty expr false eq =
  compileFunBody-ce doOpt ctx polys impsOf name ty expr eq

compileFun-ce : ∀ (polys : PolyCtx) (impsOf : String.String → TopCtx)
  (ctx : TopCtx) (ty : Type) (fi : FunInfo) (irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋) →
  C.compileFun IR.Heap false ctx polys impsOf (funName fi) ty (funBody fi) ≡ inj₂ irFun →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndPolys ctx polys)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    checkElab (ctxWithImportsAndPolys ctx polys) (funBody fi) ty
      ≡ TE.success Ψ se d f))))
compileFun-ce polys impsOf ctx ty fi irFun eq =
  compileFun-aux-ce false ctx polys impsOf (funName fi) ty (funBody fi) (funName fi == "main") eq

-- R8: a definition without a signature — its synthesis succeeded, at its type.
compileFunI-ce : ∀ (polys : PolyCtx) (impsOf : String.String → TopCtx)
  (ctx : TopCtx) (ty : Type) (fi : FunInfo) (irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋) →
  C.compileFunI IR.Heap false ctx polys impsOf (funName fi) ty (funBody fi) ≡ inj₂ irFun →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndPolys ctx polys)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    TE.inferElab (ctxWithImportsAndPolys ctx polys) (funBody fi) ≡ TE.success ty Ψ se d f))))
compileFunI-ce polys impsOf ctx ty fi irFun eq =
  aux (TE.inferElabV (ctxWithImportsAndPolys ctx polys) (funBody fi)) (body (funName fi == "main") eq)
  where
    nctx = ctxWithImportsAndPolys ctx polys
    body : (b : Bool) → C.compileFunI-aux IR.Heap false ctx polys impsOf (funName fi) ty (funBody fi) b ≡ inj₂ irFun
         → C.compileFunBodyI IR.Heap false ctx polys impsOf (funName fi) ty (funBody fi) ≡ inj₂ irFun
    body true  e = main (C.validateMain ty) e
      where
        main : (v : String ⊎ ⊤) → C.compileFunI-main-aux IR.Heap false ctx polys impsOf (funName fi) ty (funBody fi) v ≡ inj₂ irFun
             → C.compileFunBodyI IR.Heap false ctx polys impsOf (funName fi) ty (funBody fi) ≡ inj₂ irFun
        main (inj₁ _) ()
        main (inj₂ _) e′ = e′
    body false e = e
    at : ∀ {T Ψ} (w : nctx Once.Internal.Typing.⊢ᵢ funBody fi ∶ T ⨾ Ψ) (dd : Dec (T ≡ ty))
       → C.compileFunBodyI-at IR.Heap false ctx polys impsOf (funName fi) ty refl w dd ≡ inj₂ irFun → T ≡ ty
    at w (yes e) _ = e
    at w (no _) ()
    aux : (cr : TE.VerifiedInferResult nctx (funBody fi))
        → C.compileFunBodyI-aux IR.Heap false ctx polys impsOf (funName fi) ty refl cr ≡ inj₂ irFun
        → Σ-syntax (Usage (NamedCtx.size nctx)) (λ Ψ → Σ-syntax (Expr (NamedCtx.debruijn nctx) Ψ ty) (λ se →
            Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f → proj₁ cr ≡ TE.success ty Ψ se d f))))
    aux (TE.failure _ , _) ()
    aux (TE.success T Ψ se d f , w) e = fix (at w (T Once.Internal.Type.DecEq.≟T ty) e) se
      where
        fix : (eq′ : T ≡ ty) (se′ : Expr (NamedCtx.debruijn nctx) Ψ T)
            → Σ-syntax (Usage (NamedCtx.size nctx)) (λ Ψ′ → Σ-syntax (Expr (NamedCtx.debruijn nctx) Ψ′ ty) (λ se″ →
                Σ-syntax ℕ (λ d′ → Σ-syntax ℕ (λ f′ → TE.success T Ψ se′ d f ≡ TE.success ty Ψ′ se″ d′ f′))))
        fix refl se′ = Ψ , se′ , d , f , refl

compileFunM-ce : ∀ (ft : Maybe Type) (polys : PolyCtx) (impsOf : String.String → TopCtx)
  (ctx : TopCtx) (ty : Type) (fi : FunInfo) (irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋) → funType fi ≡ ft →
  C.compileFunM ft IR.Heap false ctx polys impsOf (funName fi) ty (funBody fi) ≡ inj₂ irFun →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndPolys ctx polys)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f → ElabOK ft (ctxWithImportsAndPolys ctx polys) (funBody fi) ty Ψ se d f))))
compileFunM-ce (just _) polys impsOf ctx ty fi irFun _ eq = compileFun-ce polys impsOf ctx ty fi irFun eq
compileFunM-ce nothing  polys impsOf ctx ty fi irFun _ eq = compileFunI-ce polys impsOf ctx ty fi irFun eq

------------------------------------------------------------------------
-- (2) Typing view + compiled view.
------------------------------------------------------------------------


bundle→typed : ∀ {sc es} → FunBundle sc es → ModTele (AS.scopeOf sc) es
bundle→typed bnil = []
bundle→typed (bffi {c = c} {h = h} {g = g} ep et _ _ _ rest) = ffi ep et c h g (bundle→typed rest)
bundle→typed {sc} (bcons {fi = fi} {ty = ty} ep rf fc {g} eg ce cf rest) =
  mono ep rf (firstChecking-sound (ctxC sc) (funBody fi) (below ty) fc) g (elabOK-sound (funType fi) (ctxC sc) (funBody fi) ty ce) (bundle→typed rest)
bundle→typed {sc} (bpoly {pfi = pfi} fc ce rest) =
  poly (firstChecking-sound (ctxC sc) (Parser.PolyFunInfo.pfunBody pfi) (below (rigidOf (Parser.PolyFunInfo.pfunType pfi))) fc)
       (check-sound (ctxC sc) (Parser.PolyFunInfo.pfunBody pfi) (rigidOf (Parser.PolyFunInfo.pfunType pfi)) ce) (bundle→typed rest)

bundle→compiled : ∀ {sc es} → FunBundle sc es → List C.CompiledFun
bundle→compiled bnil = []
bundle→compiled (bffi _ _ _ _ _ rest) = bundle→compiled rest
bundle→compiled (bcons {fi = fi} {ty = ty} {irFun = irFun} ep rf fc eg ce cf rest) =
  C.mkCompiledFun (bare (funName fi)) ty irFun ∷ bundle→compiled rest
bundle→compiled (bpoly fc ce rest) = bundle→compiled rest

-- A bundle for every accepted telescope, whose compiled list IS the compiler's.
CGB : C.CScope → List Parser.Entry → List C.CompiledFun → Set
CGB sc es compiled = Σ-syntax (FunBundle sc es) (λ b → bundle→compiled b ≡ compiled)

ce-bundleP : ∀ (sc : C.CScope) (es : List Parser.Entry) (compiled : List C.CompiledFun)
  → C.compileEntries IR.Heap false sc es ≡ inj₂ compiled → CGB sc es compiled
cgb-fun : ∀ (sc : C.CScope) (fi : FunInfo) (es : List Parser.Entry) (compiled : List C.CompiledFun) (b : Bool)
  → funIsPrimitive fi ≡ b → C.ce-fun IR.Heap false sc fi es b ≡ inj₂ compiled → CGB sc (Parser.e-fun fi ∷ es) compiled
cgb-prim : ∀ (sc : C.CScope) (fi : FunInfo) (es : List Parser.Entry) (compiled : List C.CompiledFun)
  → funIsPrimitive fi ≡ true → (mt : Maybe Type) → funType fi ≡ mt
  → C.ce-prim IR.Heap false sc fi es mt ≡ inj₂ compiled → CGB sc (Parser.e-fun fi ∷ es) compiled
cgb-mono : ∀ (sc : C.CScope) (fi : FunInfo) (es : List Parser.Entry) (compiled : List C.CompiledFun)
  → funIsPrimitive fi ≡ false → (rt : String ⊎ Type)
  → C.resolveFunType (C.ctop sc) (C.cpolys sc) (funType fi) (funBody fi) ≡ rt
  → C.ce-mono IR.Heap false sc fi es rt ≡ inj₂ compiled → CGB sc (Parser.e-fun fi ∷ es) compiled
cgb-poly-p : ∀ (sc : C.CScope) (pfi : Parser.PolyFunInfo) (es : List Parser.Entry) (compiled : List C.CompiledFun)
  → (mp : Maybe Type)
  → C.firstChecking (ctxC sc) (Parser.PolyFunInfo.pfunBody pfi) (below (rigidOf (Parser.PolyFunInfo.pfunType pfi))) ≡ mp
  → C.ce-poly-p IR.Heap false sc pfi es mp ≡ inj₂ compiled → CGB sc (Parser.e-poly pfi ∷ es) compiled
cgb-poly : ∀ (sc : C.CScope) (pfi : Parser.PolyFunInfo) (es : List Parser.Entry) (compiled : List C.CompiledFun)
  → C.firstChecking (ctxC sc) (Parser.PolyFunInfo.pfunBody pfi) (below (rigidOf (Parser.PolyFunInfo.pfunType pfi))) ≡ nothing
  → (r : TE.VerifiedCheckResult (ctxC sc) (Parser.PolyFunInfo.pfunBody pfi) (rigidOf (Parser.PolyFunInfo.pfunType pfi)))
  → TE.checkElabV (ctxC sc) (Parser.PolyFunInfo.pfunBody pfi) (rigidOf (Parser.PolyFunInfo.pfunType pfi)) ≡ r
  → C.ce-poly IR.Heap false sc pfi es (C.checkOK r) ≡ inj₂ compiled → CGB sc (Parser.e-poly pfi ∷ es) compiled

ce-bundleP sc [] compiled eq = bnil , inj₂-injective eq
ce-bundleP sc (Parser.e-fun fi ∷ es) compiled eq = cgb-fun sc fi es compiled (funIsPrimitive fi) refl eq
ce-bundleP sc (Parser.e-poly pfi ∷ es) compiled eq = cgb-poly-p sc pfi es compiled _ refl eq

cgb-fun sc fi es compiled true  ep eq = cgb-prim sc fi es compiled ep (funType fi) refl eq
cgb-fun sc fi es compiled false ep eq =
  cgb-mono sc fi es compiled ep (C.resolveFunType (C.ctop sc) (C.cpolys sc) (funType fi) (funBody fi)) refl eq

cgb-prim sc fi es compiled ep nothing et ()
cgb-prim sc fi es compiled ep (just ty) et eq = conc (isConcrete? ty) refl (honest? ty) refl (rigidFree? ty) refl eq
  where
    conc : (mc : Maybe (IsConcrete ty)) → isConcrete? ty ≡ mc → (mh : Maybe (HonestFFI ty)) → honest? ty ≡ mh
         → (mg : Maybe (RigidFree ty)) → rigidFree? ty ≡ mg
         → C.ce-prim-conc IR.Heap false sc fi es ty mc mh mg ≡ inj₂ compiled → CGB sc (Parser.e-fun fi ∷ es) compiled
    conc nothing _ _ _ _ _ ()
    conc (just _) _ nothing _ _ _ ()
    conc (just _) _ (just _) _ nothing _ ()
    conc (just c) ec (just h) eh (just g) eg eq′ =
      let (b , beq) = ce-bundleP (C.extendSig sc (funName fi) ty) es compiled eq′
      in bffi {c = c} {h = h} {g = g} ep et ec eh eg b , beq

cgb-mono sc fi es compiled ep (inj₁ _) er ()
cgb-mono sc fi es compiled ep (inj₂ ty) er eq
  with C.firstChecking (ctxC sc) (funBody fi) (below ty) in fc
... | just _ = case eq of λ ()
... | nothing
  with rigidFree? ty in eg
... | nothing = case eq of λ ()
... | just g
  with C.compileFunM (funType fi) IR.Heap false (C.ctop sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) (funName fi) ty (funBody fi) in cf
... | inj₁ _ = case eq of λ ()
... | inj₂ irFun
      with C.compileEntries IR.Heap false (C.extendScope sc (funName fi) ty) es in rec
...   | inj₁ _ = case eq of λ ()
...   | inj₂ rest =
        let (Ψ , se , d , f , ce) = compileFunM-ce (funType fi) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) (C.ctop sc) ty fi irFun refl cf
            (b , beq) = ce-bundleP (C.extendScope sc (funName fi) ty) es rest rec
        in bcons {Ψ = Ψ} {se = se} {d = d} {f = f} {irFun = irFun} ep er fc eg ce cf b
         , trans (cong (C.mkCompiledFun (bare (funName fi)) ty irFun ∷_) beq)
                 (inj₂-injective eq)

cgb-poly-p sc pfi es compiled (just _) _ ()
cgb-poly-p sc pfi es compiled nothing fc eq = cgb-poly sc pfi es compiled fc _ refl eq

cgb-poly sc pfi es compiled fc (TE.failure _ , _) _ ()
cgb-poly sc pfi es compiled fc (TE.success Ψ se d f , w) cv eq =
  let (b , beq) = ce-bundleP (C.addEntry sc pfi) es compiled eq
  in bpoly {Ψ = Ψ} {se = se} {d = d} {f = f} fc (cong proj₁ cv) b , beq

ce-bundle : ∀ (sc : C.CScope) (es : List Parser.Entry) {compiled : List C.CompiledFun}
  → C.compileEntries IR.Heap false sc es ≡ inj₂ compiled → FunBundle sc es
ce-bundle sc es {compiled} eq = proj₁ (ce-bundleP sc es compiled eq)

bundle→compiled≡compiled : ∀ (sc : C.CScope) (es : List Parser.Entry) (compiled : List C.CompiledFun)
  (eq : C.compileEntries IR.Heap false sc es ≡ inj₂ compiled) → bundle→compiled (ce-bundle sc es eq) ≡ compiled
bundle→compiled≡compiled sc es compiled eq = proj₂ (ce-bundleP sc es compiled eq)

BMainExists : ∀ {sc es} → FunBundle sc es → Set
BMainExists bnil = ⊥
BMainExists (bffi _ _ _ _ _ rest) = BMainExists rest
BMainExists (bcons {fi = fi} {ty = ty} _ _ _ _ _ _ rest) =
  ((funName fi ≡ "main") × (funIsPrimitive fi ≡ false) × (ty <: EffUU)) ⊎ BMainExists rest
BMainExists (bpoly _ _ rest) = BMainExists rest

-- D253: the program's `main` is the call of the entry `main : Eff Unit Unit`; the
-- bundle finds it with the compiler's own decisions (`findMain-here`).
bundle-find : ∀ {sc es} → FunBundle sc es → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
bundle-find bnil = nothing
bundle-find (bffi _ _ _ _ _ rest) = bundle-find rest
bundle-find (bcons {fi = fi} {ty = ty} {irFun = irFun} ep rf fc eg ce cf rest) =
  findMain-here (C.mkCompiledFun (bare (funName fi)) ty irFun)
    (bare (funName fi) ≟ᶜ bare "main") (ty <:? EffUU) (bundle-find rest)
bundle-find (bpoly _ _ rest) = bundle-find rest

find-agree : ∀ {sc es} (b : FunBundle sc es) → findMain (bundle→compiled b) ≡ bundle-find b
find-agree bnil = refl
find-agree (bffi _ _ _ _ _ rest) = find-agree rest
find-agree {sc} (bcons {fi = fi} {ty = ty} {irFun = irFun} ep rf fc eg ce cf rest) =
  cong (findMain-here (C.mkCompiledFun (bare (funName fi)) ty irFun)
          (bare (funName fi) ≟ᶜ bare "main") (ty <:? EffUU))
       (find-agree rest)
find-agree (bpoly _ _ rest) = find-agree rest

bme→me : ∀ {sc es} (b : FunBundle sc es) → BMainExists b → MainIn (bundle→typed b)
bme→me (bffi _ _ _ _ _ rest) w = bme→me rest w
bme→me (bcons _ _ _ _ _ _ rest) (inj₁ (p , _ , e)) = inj₁ (p , e)
bme→me (bcons _ _ _ _ _ _ rest) (inj₂ w) = inj₂ (bme→me rest w)
bme→me (bpoly _ _ rest) w = bme→me rest w

-- The program's `main` is only ever the entry's call (`mainEntry`, D315).
IsEntry : IR ⌊ Unit ⌋ ⌊ Unit ⌋ → Set
IsEntry ir = Σ-syntax Type (λ ty → Σ-syntax (ty <: EffUU) (λ p → ir ≡ mainEntry p))

private
  here-call : ∀ (cf : C.CompiledFun) (nd : Dec (C.CompiledFun.cfName cf ≡ bare "main"))
                (td : Dec (C.CompiledFun.cfType cf <: EffUU)) (cont : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)) {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋}
            → (cont ≡ just ir → IsEntry ir) → findMain-here cf nd td cont ≡ just ir → IsEntry ir
  here-call cf (yes _) (yes p) cont ih refl = _ , p , refl
  here-call cf (yes _) (no _)  cont ih eq   = ih eq
  here-call cf (no _)  _       cont ih eq   = ih eq

  here-exists : ∀ {sc es} (fi : FunInfo) {ty : Type} {irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋} (rest : FunBundle (C.extendScope sc (funName fi) ty) es)
                → funIsPrimitive fi ≡ false
                → (nd : Dec (bare (funName fi) ≡ bare "main")) (td : Dec (ty <: EffUU)) {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋}
                → (bundle-find rest ≡ just ir → BMainExists rest)
                → findMain-here (C.mkCompiledFun (bare (funName fi)) ty irFun) nd td (bundle-find rest) ≡ just ir
                → ((funName fi ≡ "main") × (funIsPrimitive fi ≡ false) × (ty <: EffUU)) ⊎ BMainExists rest
  here-exists fi rest ep (yes n) (yes e) ih eq = inj₁ (bare-injective n , ep , e)
  here-exists fi rest ep (yes _) (no _)  ih eq = inj₂ (ih eq)
  here-exists fi rest ep (no _)  _       ih eq = inj₂ (ih eq)

bundle-find-call : ∀ {sc es} (b : FunBundle sc es) {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋} → bundle-find b ≡ just ir → IsEntry ir
bundle-find-call bnil ()
bundle-find-call (bffi _ _ _ _ _ rest) eq = bundle-find-call rest eq
bundle-find-call (bpoly _ _ rest) eq = bundle-find-call rest eq
bundle-find-call (bcons {fi = fi} {ty = ty} {irFun = irFun} ep rf fc eg ce cf rest) eq =
  here-call (C.mkCompiledFun (bare (funName fi)) ty irFun)
    (bare (funName fi) ≟ᶜ bare "main") (ty <:? EffUU) (bundle-find rest) (bundle-find-call rest) eq

bundle-find-exists : ∀ {sc es} (b : FunBundle sc es) {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋}
  → bundle-find b ≡ just ir → BMainExists b
bundle-find-exists bnil ()
bundle-find-exists (bffi _ _ _ _ _ rest) eq = bundle-find-exists rest eq
bundle-find-exists (bpoly _ _ rest) eq = bundle-find-exists rest eq
bundle-find-exists (bcons {fi = fi} {ty = ty} {irFun = irFun} ep rf fc eg ce cf rest) eq =
  here-exists fi {irFun = irFun} rest ep (bare (funName fi) ≟ᶜ bare "main") (ty <:? EffUU)
    (bundle-find-exists rest) eq

------------------------------------------------------------------------
-- The compiled program, from `moduleToIR m ≡ just ir`: the entries, their
-- compile bundle, and the compile result it is.
------------------------------------------------------------------------

ProgramNode : Core.Module → Set
ProgramNode m =
  Σ-syntax (List Parser.Entry) (λ es →
  Σ-syntax (Parser.extractFunctions (Parser.extractAliases m) m ≡ inj₂ es) (λ _ →
  Σ-syntax (FunBundle C.emptyCScope es) (λ b →
    C.compileResolvedModule IR.Heap false m ≡ inj₂ (bundle→compiled b))))

private
  node-ce : ∀ (m : Core.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (es : List Parser.Entry) (cv : String ⊎ List C.CompiledFun)
          → C.compileEntries IR.Heap false C.emptyCScope es ≡ cv → moduleToIR-aux cv ≡ just ir
          → Parser.extractFunctions (Parser.extractAliases m) m ≡ inj₂ es → ProgramNode m
  node-ce m ir es (inj₁ _) ce mi ef = case mi of λ ()
  node-ce m ir es (inj₂ compiled) ce mi ef =
    es , ef , ce-bundle C.emptyCScope es ce
       , trans (cong (C.compileResolvedModule-aux IR.Heap false m) ef)
               (trans ce (cong inj₂ (sym (bundle→compiled≡compiled C.emptyCScope es compiled ce))))

  node-ef : ∀ (m : Core.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (efv : String ⊎ List Parser.Entry)
          → Parser.extractFunctions (Parser.extractAliases m) m ≡ efv
          → moduleToIR-aux (C.compileResolvedModule-aux IR.Heap false m efv) ≡ just ir → ProgramNode m
  node-ef m ir (inj₁ _)  ef mi = case mi of λ ()
  node-ef m ir (inj₂ es) ef mi = node-ce m ir es (C.compileEntries IR.Heap false C.emptyCScope es) refl mi ef

program-node : ∀ (m : Core.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR m ≡ just ir → ProgramNode m
program-node m ir mi = node-ef m ir (Parser.extractFunctions (Parser.extractAliases m) m) refl mi

