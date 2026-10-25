-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.TeleWalk.Invariant — the telescope walk's per-entry steps
-- (`Inv` and its ffi/mono/poly steps, plus the position facts about later
-- tables). Split from `Once.Adequacy.TeleWalk` for the per-module check cap;
-- that module has the walk itself and `main`'s step.
------------------------------------------------------------------------

import Once.Spec.Context as SCx
open import Once.Spec.Type using (Ty)
open import Once.TypeCheck.Classify using (TopCtx)
open import Once.Spec.Numerics using (TargetNum)

open import Once.Internal.Trace using (Interp; pureHalf)
open import Once.Spec.Signature using (Signature; WellFormed; Decl)
open import Data.List using (map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Once.Internal.Name using (showCanonical)
import Once.Spec.Observation as Obs

-- Plan 0.105: at an interpretation — the meaning and the compiled program run
-- against the same one. Plan 0.122: the program's signature is Σ, its
-- interpretation `J` (the Spec's), which the compiler reads as `ι`.
import Once.Spec.Grade
module Once.Adequacy.TeleWalk.Invariant (fmt : TargetNum) (Σ : Signature) (wf : WellFormed Σ) (J : Obs.Interp Σ)
  (uniq : Unique (map (λ d → showCanonical (Decl.name d)) Σ)) where

open import Once.Adequacy.SpecInterp using (toInterp)

-- The compiler's reading of `J`.
ι : Interp
ι = toInterp Σ wf J

-- `J`'s model: what the program's FFI values are.
mo : Obs.Model Σ
mo = Obs.Interp.model J

open import Data.Nat using (ℕ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String)
import Data.String as Str
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Type using (Type)
open import Once.Internal.Type.Instance using (KindedInstance)
open import Once.Internal.Type.Honest using (HonestFFI)
open import Once.Spec.Name using (bare)
import Once.Compile as C
import Once.IR as IR
import Once.Parser as Parser
open Parser.FunInfo using (funName; funBody; funType)
open Parser.PolyFunInfo using (pfunName; pfunType; pfunBody)
open import Once.IR using (IR)
import Once.IR
open import Once.IRTy using (⌊_⌋)
import Once.Internal.Context as Ctx
import Once.Spec.Context as Ctx
import Once.Surface.Syntax as Srf
open import Once.Internal.Typing.Scope using (Imports)
open import Once.Internal.Type.Instance using (rigidOf)
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.Program using (IRFun)
open Once.Denotation.Program.IRFun using (fname)
open import Once.Internal.Module using (ModTele; []; ffi; mono; poly; MainIn; ctxOf; ctxOfAt; MonoWit)
open import Once.Adequacy.ModuleProgram Σ using (Names; monoDef; monoBody; packOf; packOfAt; polyDef; PolyWit)
open import Once.TypeCheck.SpecWitness using (Pack; OkOf; OkSOf; ok-gen; ok-sig; ok-inj; oks-fun)
import Once.Adequacy.ScopeRefs as SR
import Once.Internal.Type
import Once.Adequacy.MeaningBridgeS
import Once.Spec.Effect Σ as SE
open import Once.Spec.Type using (KCtx; ∅ₖ; TySub; Respects)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Internal.Name using (WordName)
open import Once.Spec.Signature using (_∶_)
open import Once.Internal.Core.Decl using (declS; ⌜declS⌝)
open import Once.Spec.Core.Syntax using (Defs; _▷_; _!!_; Schema)
open import Once.Spec.Core.Program Σ using (Tele; def; noVars)
open import Once.Internal.Core.Telescope Σ using (teleSem; teleSem-model)
import Once.Spec.Core.Meaning as SM
import Once.Spec.Domain Σ as SDm
import Once.Metatheory.TermModel.TySubst as TS
import Once.Internal.Core.TySubstZero as TZ
open import Once.Spec.Type.Substitution using (⟨⟩-∘)
open import Once.Spec.Type using (_⟨_⟩)
open import Once.Functor.Translate using (Base-irrelevant)
import Once.Adequacy.SpecSig as SSg
open import Once.Denotation.DenotTrace using (CallEnv)
open import Once.Internal.Type.Schema using (schemaOf)
open import Once.Internal.Type.Instance using (kindsOf)
open import Once.Internal.Core.Translate Σ using (SigSig; s-ffi; ImpSig; TeleSig; i-def; impDefs; t-def; wkI; wkT; viewOf; monoSchema)
import Once.Internal.Core.Translate Σ as TR
open import Once.Compile using (irFunOf; tableOf-go)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.FunBundle as FB
import Once.Adequacy.MainIRForm as MIF
import Once.Adequacy.MeaningBridge as MB
import Once.Adequacy.CoreEnv as CE
import Once.Adequacy.CoreMeaningBridge as CMB
import Once.Adequacy.MonoEntry as ME
import Once.TypeCheck.View as TView
open import Once.Internal.Type using (none; noResp)
open import Once.Internal.Type.Schema using (kinded-instance)
open import Once.Postulates using (extensionality)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Function using (id)
open import Once.Internal.Trace using (FFIAnswers)

-- The interpretation's pure half: what the program's pure FFI values are.
φ : FFIAnswers
φ = pureHalf ι

-- The instance the core's values are read at: no variable (the walk's
-- definitions are ground).
σ₀ : TySub 0 0
σ₀ = noVars

open import Once.Denotation.SpecDomain Σ σ₀ using (⟦_⟧ᵛ; ⟦wk₀⟧ᵛ)
open import Once.Adequacy.GradedRelation Σ σ₀ using (RelGM; GM-D; RelGM-wk₀)
open import Once.Internal.Iterative using (T∞)
open import Once.Denotation.TraceMonadInfLaws using (RelS)
open import Once.Denotation.ValueRel using (RelD)
open import Once.Denotation.ValueRelPER using (RelS-trans; RelD-trans)
open import Once.Denotation.EvalRel using (table-self; coh-runs)
open import Once.Adequacy.TeleEnvLemmas fmt φ Σ σ₀ using (σW; σW-self; callSD-later; refs-skip; refs-head; spliceClosed; RefsAgree; envrel-transport;
  imprel-transport; calls-same)
import Once.Adequacy.TeleEntry fmt ι Σ σ₀ as TE

import Once.Adequacy.CoherenceS
import Once.Spec.Core.Typing
import Once.Adequacy.UseCommute
import Once.TypeCheck.WitnessSubst
import Once.TypeCheck.Use
import Once.TypeCheck.UseCore as UC
import Once.Denotation.RealizeS
import Once.Adequacy.CoherenceHet fmt as CH
open import Once.Adequacy.CoherenceLaws fmt using (module _≈_)
open _≈_ using (≈-out)
import Once.Adequacy.SourceFaithful as SF
import Once.Adequacy.ResolveFaithful as RF
open import Once.TypeCheck.Completeness using (check-completeS)
import Once.TypeCheck.Elaborate
import Data.Maybe
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.Denotation.ValueDomain using (cohᴰ)
open import Once.Denotation.Program using (tableEnv)
open import Once.Adequacy.TableCall fmt φ using (abiT; abi)
import Data.Fin
import Relation.Nullary
open import Data.List.Properties using (++-assoc)
open import Once.Adequacy.TelePosition

------------------------------------------------------------------------
-- Position predicates
------------------------------------------------------------------------

-- Later table entries do not shadow a name in scope.
private
  ≡ˡ : ∀ {X Y} {R : X → Y → Set} {m m′ : T∞ X} {n : T∞ Y} → m ≡ m′ → RelS R m′ n → RelS R m n
  ≡ˡ refl h = h
  ≡ʳ : ∀ {X Y} {R : X → Y → Set} {m : T∞ X} {n n′ : T∞ Y} → n ≡ n′ → RelS R m n → RelS R m n′
  ≡ʳ refl h = h

NoShadow : List IRFun → C.FunCtx → Set
NoShadow later imps = All (λ e → All (λ p → fname e ≢ bare (proj₁ p)) imps) later

-- THE INVARIANT at a position of the walk.
record Inv {s} {S : Defs s} (csc : C.CScope) (tl : Tele S) (ss : SigSig (C.CScope.csig csc))
           (is : ImpSig S (C.CScope.cimps csc))
           (ts : TeleSig S (C.telePolys (C.CScope.ctele csc))) (pre : List IRFun) : Set where
  field
    iself : IAgree (C.declImps (C.CScope.ctele csc)) (C.CScope.ctele csc)
    rel   : ∀ (later : List IRFun) → NoShadow later (C.CScope.cimps csc)
          → ∀ (I : String → TopCtx) → IAgree I (C.CScope.ctele csc) → ∀ (uf : Imports)
          → MB.MRel fmt Σ σ₀ (σW (later ++ pre) (C.cpolys csc) I uf) (ctxOf (AS.scopeOf csc))
                    (CE.envOf fmt Σ S σ₀ (teleSem fmt mo tl) ss is ts)

------------------------------------------------------------------------
-- D274: a declaration of Σ means `J`'s reading of it (`SpecSig.sig-rel`),
-- at every environment whose FFI values are `J`'s.
------------------------------------------------------------------------

sig-at : ∀ {s} (S : Defs s) (δ : SM.DefSem Σ fmt S) → SM.DefSem.model δ ≡ mo
       → (σ : SD.DefsSem) → CallEnv.ffiE (SD.DefsSem.calls σ) ≡ φ
       → ∀ {cn T} (wn : WordName cn) (k : IsConcrete T) (dc : TView.Declared Σ S (showCanonical cn) T)
       → RelGM Once.Spec.Grade.pure T (subst id (⟦wk₀⟧ᵛ T) (CMB.sigSem fmt Σ S σ₀ δ cn wn k dc)) (SD.sigOpSem T cn k fmt σ)
sig-at S δ e σ eψ {cn} {T} wn k (TView.declared h mem) =
  subst (λ md → RelGM Once.Spec.Grade.pure T
                  (subst id (⟦wk₀⟧ᵛ T) (subst (λ X → ⟦ X ⟧ᵛ) (⌜declS⌝ k h) (SM.sigopᵛ Σ fmt S σ₀ cn (declS T) (mem {cn} wn refl) md)))
                  (SD.sigOpSem T cn k fmt σ))
        (sym e) (SSg.sig-rel Σ wf J uniq fmt σ₀ S σ eψ k h (mem {cn} wn refl))

sigR : ∀ {s} {S : Defs s} (tl : Tele S) {sg} (ss : SigSig sg) (σ : SD.DefsSem) → CallEnv.ffiE (SD.DefsSem.calls σ) ≡ φ
     → MB.SigRel fmt Σ σ₀ σ sg (λ {cn} {T} → CE.sigEnv fmt Σ S σ₀ (teleSem fmt mo tl) ss {cn} {T})
sigR {S = S} tl ss σ eψ wn lk k = sig-at S (teleSem fmt mo tl) (teleSem-model fmt mo tl) σ eψ wn k (TR.sigAt ss lk)

------------------------------------------------------------------------
-- D274: an FFI declaration extends Σ — the environment's definitions are
-- unchanged, its world declares one more generator.
------------------------------------------------------------------------

private
  bare-ne : ∀ {x : String} (imps : C.FunCtx) (rest : List String) → All (x ≢_) (map proj₁ imps ++ rest)
          → All (λ p → bare x ≢ bare (proj₁ p)) imps
  bare-ne []       rest hs       = []
  bare-ne (p ∷ ps) rest (h ∷ hs) = (λ e → h (MIF.bare-injective e)) ∷ bare-ne ps rest hs

  -- A later table, seen from the scope before an entry, gains that entry.
  ns-step : ∀ (later : List IRFun) {x : String} {ty : Type} (imps : C.FunCtx) (e : IRFun) → fname e ≡ bare x
          → All (λ p → bare x ≢ bare (proj₁ p)) imps
          → NoShadow later ((x , ty) ∷ imps) → NoShadow (later ++ e ∷ []) imps
  ns-step []            imps e eq hs ns       = subst (λ n → All (λ p → n ≢ bare (proj₁ p)) imps) (sym eq) hs ∷ []
  ns-step (e′ ∷ later) imps e eq hs ((_ ∷ a) ∷ ns) = a ∷ ns-step later imps e eq hs ns

  -- D324: `main` joins the table but not the scope.
  ns-snoc : ∀ (later : List IRFun) {x : String} (imps : C.FunCtx) (e : IRFun) → fname e ≡ bare x
          → All (λ p → bare x ≢ bare (proj₁ p)) imps
          → NoShadow later imps → NoShadow (later ++ e ∷ []) imps
  ns-snoc []           imps e eq hs []       = subst (λ n → All (λ p → n ≢ bare (proj₁ p)) imps) (sym eq) hs ∷ []
  ns-snoc (e′ ∷ later) imps e eq hs (a ∷ ns) = a ∷ ns-snoc later imps e eq hs ns

  ns-head : ∀ (later : List IRFun) {x : String} {ty : Type} (imps : C.FunCtx)
          → NoShadow later ((x , ty) ∷ imps) → All (λ e → fname e ≢ bare x) later
  ns-head []           imps []             = []
  ns-head (e ∷ later) imps ((h ∷ _) ∷ ns) = h ∷ ns-head later imps ns

inv-sig : ∀ {s} {S : Defs s} {csc tl ss is ts pre} {x : String} {ty : Type}
            {k : IsConcrete ty} {h : HonestFFI ty} {m : ∀ {c} → WordName c → showCanonical c ≡ x → (c ∶ declS ty) ∈ Σ}
        → Inv {S = S} csc tl ss is ts pre
        → Inv (C.extendSig csc x ty) tl (s-ffi k h m ss) is ts pre
inv-sig {tl = tl} {ss} {k = k} {h} {m} inv = record
  { iself = Inv.iself inv
  ; rel   = λ later ns I ia uf → let old = Inv.rel inv later ns I ia uf in
              proj₁ old , proj₁ (proj₂ old) , sigR tl (s-ffi k h m ss) _ refl
  }

------------------------------------------------------------------------
-- A monomorphic entry: its call (the compiled body, read through the ABI)
-- is its core entry — the compile chain (faithful, the resolver, realize),
-- leg A in the scope's environment, leg B, and F for the read-back.
------------------------------------------------------------------------

private
  -- The splice of a telescope body is the checker's term at the instance, resolved.
  splice-form : ∀ (I : String → TopCtx) (uf : Imports) (pre : Once.Internal.Typing.Scope.PolyCtx) (y : String)
                  {Xs : TopCtx} {b : _} {A : Type} {se : _} {d f : ℕ}
                  (cr : Once.TypeCheck.Elaborate.VerifiedCheckResult (Once.TypeCheck.Classify.ctxWithImportsAndPolys Xs pre) b A)
                  (ce : proj₁ cr ≡ Once.TypeCheck.Elaborate.success SCx.[] se d f)
              → spliceClosed I uf pre y cr ≡ Srf.closed (resolveExpr pre I uf 0 se)
  splice-form I uf pre y (Once.TypeCheck.Elaborate.success _ _ _ _ , w) refl = refl

-- An earlier entry, read through the extended telescope.
refSemAt-wk : ∀ {s} {S : Defs s} {sc} {tl : Tele S} {body D} (d : Data.Fin.Fin s) {sc′ : Schema} (e : S !! d ≡ sc′)
                (τ : TySub (Schema.arity sc′) 0) {Δ : KCtx 0} (r : Respects (Schema.kinds sc′) Δ τ)
            → CMB.refSemAt fmt Σ (S ▷ sc) σ₀ (teleSem fmt mo (def tl sc body D)) (Data.Fin.suc d) e τ r
              ≡ CMB.refSemAt fmt Σ S σ₀ (teleSem fmt mo tl) d e τ r
refSemAt-wk d refl τ r = refl

impEnv-wk : ∀ {s} {S : Defs s} {sc} {tl : Tele S} {body D} {imps} (is : ImpSig S imps)
          → CE.impEnv fmt Σ (S ▷ sc) σ₀ (teleSem fmt mo (def tl sc body D)) (wkI is) ≡ CE.impEnv fmt Σ S σ₀ (teleSem fmt mo tl) is
impEnv-wk TR.[]              = refl
impEnv-wk {sc = sc} {tl} {body} {D} (TR.i-def {T = T} d e is) =
  cong₂ _,_ (cong (subst id (⟦wk₀⟧ᵛ T)) (refSemAt-wk {sc = sc} {tl = tl} {body = body} {D = D} d e none _))
            (impEnv-wk {sc = sc} {tl = tl} {body = body} {D = D} is)

defEnv-wk : ∀ {s} {S : Defs s} {sc} {tl : Tele S} {body D} {ps} (ts : TeleSig S ps)
          → CE.defEnv fmt Σ (S ▷ sc) σ₀ (teleSem fmt mo (def tl sc body D)) (wkT ts) ≡ CE.defEnv fmt Σ S σ₀ (teleSem fmt mo tl) ts
defEnv-wk TR.[]              = refl
defEnv-wk {sc = sc} {tl} {body} {D} (TR.t-def {p = p} d e ts) =
  cong₂ _,_ (cong (λ (h : (Δ : KCtx 0) (U : Type) → KindedInstance Δ (pfunType p) U → ⟦ U ⟧ᵛ) → λ {Δ} → h Δ)
                  (extensionality λ Δ → extensionality λ U → extensionality λ ki →
                     cong (subst (λ X → ⟦ X ⟧ᵛ) (proj₂ (proj₂ (kinded-instance (pfunType p) ki))))
                          (refSemAt-wk {sc = sc} {tl = tl} {body = body} {D = D} d e _ _)))
            (defEnv-wk {sc = sc} {tl = tl} {body = body} {D = D} ts)

-- A derivation's meaning depends on it only up to transports.
⟦⟧ˢ-≅ : ∀ {s} {S : Defs s} {Δ : KCtx 0} {t A} {d d′ : Once.Spec.Core.Typing._⊩_⊢[_]_∷_!_ Σ S Δ SCx.∅ SCx.[] t A Once.Spec.Grade.pure} {δ}
      → d H.≅ d′ → CMB.⟦_⟧ₛ fmt Σ S σ₀ d δ tt ≡ CMB.⟦_⟧ₛ fmt Σ S σ₀ d′ δ tt
⟦⟧ˢ-≅ H.refl = refl

-- The head of the instance telescope, read at an instance: its derivation
-- instantiated there, read at no variable (the instance of the instance is
-- the instance, `⟨⟩-0`; `Respects` is a proposition).
head-at : ∀ {s} {S : Defs s} {tl : Tele S} {sc : Schema} {body} {D} (τ : TySub (Schema.arity sc) 0) {Δ : KCtx 0}
            (r : Respects (Schema.kinds sc) Δ τ) (r′ : Respects (Schema.kinds sc) ∅ₖ τ)
        → CMB.refSemAt fmt Σ (S ▷ sc) σ₀ (teleSem fmt mo (def tl sc body D)) zero refl τ r
          ≡ CMB.⟦_⟧ₛ fmt Σ S σ₀ (TS.ty-subst-⊢ Σ S τ r′ D) (teleSem fmt mo tl) tt
head-at {S = S} {tl} {sc} {body} {D} τ r r′ =
  H.≅-to-≡ (H.trans (H.≡-subst-removable SDm.⟦_⟧ᵛ (sym (⟨⟩-∘ (Schema.type sc) τ σ₀)) _)
           (H.trans (H.≡-subst-removable SDm.⟦_⟧ᵛ (TZ.⟨⟩-0 Σ S noVars (Schema.type sc ⟨ τ∘ ⟩)) _)
                    (go τ∘ (extensionality λ i → TZ.⟨⟩-0 Σ S noVars (τ i)) _)))
  where
    τ∘ : TySub (Schema.arity sc) 0
    τ∘ i = τ i ⟨ σ₀ ⟩
    go : ∀ (τ′ : TySub (Schema.arity sc) 0) → τ′ ≡ τ → (r″ : Respects (Schema.kinds sc) ∅ₖ τ′)
       → SM.⟦_⟧ Σ fmt S (TS.ty-subst-⊢ Σ S τ′ r″ D) (teleSem fmt mo tl) noVars noResp tt
         H.≅ SM.⟦_⟧ Σ fmt S (TS.ty-subst-⊢ Σ S τ r′ D) (teleSem fmt mo tl) noVars noResp tt
    go _ refl r″ = H.≡-to-≅ (cong (λ q → SM.⟦_⟧ Σ fmt S (TS.ty-subst-⊢ Σ S τ q D) (teleSem fmt mo tl) noVars noResp tt)
                                 (extensionality λ i → extensionality λ e → Base-irrelevant _ _))

-- The compile chain of a monomorphic entry: its compiled body, read through the
-- ABI, is related to its entry's core meaning — the checker's term, the
-- realization of its witness, means what the witness's core term means
-- (`MeaningBridgeS`), at the scope's references (`ScopeRefs`).
module MonoStep {s} {S : Defs s} {csc : C.CScope} {tl : Tele S} {ss : SigSig (C.CScope.csig csc)} {is : ImpSig S (C.CScope.cimps csc)}
                {ts : TeleSig S (C.telePolys (C.CScope.ctele csc))} {pre : List IRFun}
                (N : Names S is ts) {fi : Parser.FunInfo} {ty : Type}
                (W : MonoWit (funType fi) (ctxOf (AS.scopeOf csc)) (funBody fi) ty SCx.[])
                {irFun : IR ⌊ Once.Spec.Type.Unit {0} ⌋ ⌊ ty ⌋}
                (cf : C.compileFunM (funType fi) IR.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                        (funName fi) ty (funBody fi) ≡ Data.Sum.inj₂ irFun)
                (inv : Inv {S = S} csc tl ss is ts pre) where
  x    = funName fi
  δ    = teleSem fmt mo tl
  S′   = S ▷ monoSchema ty
  tl′  = monoDef {S = S} {sc = AS.scopeOf csc} {fi = fi} {ty = ty} {Ψ = SCx.[]} tl ss is ts N W
  δ′   = teleSem fmt mo tl′
  e    = irFunOf (C.mkCompiledFun (bare x) ty irFun)
  ctx  = ctxOf (AS.scopeOf csc)
  ρ    = CE.envOf fmt Σ S σ₀ δ ss is ts
  V    = viewOf {S = S} ss is ts
  P    = packOf {S = S} {sc = AS.scopeOf csc} ss is ts N
  Dc   = proj₂ (monoBody {S = S} {sc = AS.scopeOf csc} ss is ts N (funType fi) W)
  uf : C.FunCtx
  uf   = (x , ty) ∷ C.CScope.cimps csc
  σx   = σW pre (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf
  M    = evalᴰ fmt (tableEnv fmt φ pre) irFun tt
  σx-self = σW-self pre (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf

  module MBS = Once.Adequacy.MeaningBridgeS fmt Σ S (Names.nm N) (OkOf P) (OkSOf P) (Names.inline N) σ₀ σx σx-self ∅ₖ

  -- The scope's references, related: the table's entries by name (the
  -- invariant's relation), the declarations of Σ as `J` reads them.
  refsR : MBS.Refs δ
  refsR = record
    { entry = SR.refs-entry fmt Σ σ₀ σx σx-self ctx (Names.nm N) (Names.inline N) V (OkSOf P)
                (Pack.h-imp P) (Pack.h-imp-call P) (Pack.h-poly P) (Pack.h-poly-inline P) δ ρ (CE.agree fmt Σ S σ₀ δ ss is ts)
                (Inv.rel inv [] [] (C.declImps (C.CScope.ctele csc)) (Inv.iself inv) uf)
    ; sigop = λ {c} {T} mem k h →
        SR.RelGM-≅ fmt Σ σ₀ σx σx-self {A = Once.Internal.Type.wk₀ {0} T} {B = Once.Internal.Type.wk₀ {0} T} refl
          (H.trans (H.≡-subst-removable (SE.M Once.Spec.Grade.pure) (sym (⟦wk₀⟧ᵛ T)) _) (H.≡-subst-removable id (⟦wk₀⟧ᵛ T) _))
          H.refl
          (RelGM-wk₀ {π = Once.Spec.Grade.pure} {A = T}
            (subst (λ md → RelGM Once.Spec.Grade.pure T
                             (subst id (⟦wk₀⟧ᵛ T) (subst (λ X → ⟦ X ⟧ᵛ) (⌜declS⌝ k h) (SM.sigopᵛ Σ fmt S σ₀ c (declS T) mem md)))
                             (SD.sigOpSem T c k fmt σx))
                   (sym (teleSem-model fmt mo tl)) (SSg.sig-rel Σ wf J uniq fmt σ₀ S σx refl k h mem)))
    }

  -- The compiled body's run is related to the checker's term's source meaning
  -- (faithfulness, then linking, an equation), and that term, the witness's
  -- realization, to the witness's core term (`MeaningBridgeS`).
  relC : ∀ {A} (W′ : MonoWit (Data.Maybe.just A) ctx (funBody fi) ty SCx.[])
       → C.compileFun IR.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty (funBody fi) ≡ Data.Sum.inj₂ irFun
       → RelGM Once.Spec.Grade.pure ty (CMB.⟦_⟧ₛ fmt Σ S σ₀ (proj₂ (monoBody {S = S} {sc = AS.scopeOf csc} ss is ts N (Data.Maybe.just A) W′)) δ tt)
                (subst T∞ (cohᴰ ty) (abiT ty M))
  relC (eE , d , f , w , ce) cf′ =
    TE.abi-rel ty _ M (GM-D Once.Spec.Grade.pure ty relA chain)
    where
      u = proj₁ (proj₂ (proj₂ w P))
      chain : RelS (RelD ty) (subst T∞ (cohᴰ ty) M) (SD.⟦ eE ⟧ˢ fmt σx tt)
      chain =
        ≡ˡ (cong (λ ir → subst T∞ (cohᴰ ty) (evalᴰ fmt (tableEnv fmt φ pre) ir tt))
                 (irFun-form (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty (funBody fi) cf′ (cong proj₁ ce)))
           (≡ʳ (RF.resolveExpr-faithful fmt (tableEnv fmt φ pre) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 eE tt)
               (SF.faithful∅ fmt (tableEnv fmt φ pre) (table-self fmt φ pre) (resolveExpr (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 eE)))
      relA : RelGM Once.Spec.Grade.pure ty _ (SD.⟦ eE ⟧ˢ fmt σx tt)
      relA = subst (λ t → RelGM Once.Spec.Grade.pure ty _ (SD.⟦ t ⟧ˢ fmt σx tt)) (proj₂ (proj₂ (proj₂ w P)))
                   (MBS.bridge⇐ (proj₂ u) {dγ₁ = tt} {γ = tt} {dγ₂ = tt} tt (MB.mk↾ tt) refsR)

  -- R8, without a signature: the same chain, through the synthesis.
  relI : (W′ : MonoWit Data.Maybe.nothing ctx (funBody fi) ty SCx.[])
       → C.compileFunI IR.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty (funBody fi) ≡ Data.Sum.inj₂ irFun
       → RelGM Once.Spec.Grade.pure ty (CMB.⟦_⟧ₛ fmt Σ S σ₀ (proj₂ (monoBody {S = S} {sc = AS.scopeOf csc} ss is ts N Data.Maybe.nothing W′)) δ tt)
                (subst T∞ (cohᴰ ty) (abiT ty M))
  relI (eE , d , f , w , ce) cf′ =
    TE.abi-rel ty _ M (GM-D Once.Spec.Grade.pure ty relA chain)
    where
      u = proj₁ (proj₂ (proj₂ w P))
      chain : RelS (RelD ty) (subst T∞ (cohᴰ ty) M) (SD.⟦ eE ⟧ˢ fmt σx tt)
      chain =
        ≡ˡ (cong (λ ir → subst T∞ (cohᴰ ty) (evalᴰ fmt (tableEnv fmt φ pre) ir tt))
                 (irFun-formI (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty (funBody fi) cf′ (cong proj₁ ce)))
           (≡ʳ (RF.resolveExpr-faithful fmt (tableEnv fmt φ pre) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 eE tt)
               (SF.faithful∅ fmt (tableEnv fmt φ pre) (table-self fmt φ pre) (resolveExpr (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 eE)))
      relA : RelGM Once.Spec.Grade.pure ty _ (SD.⟦ eE ⟧ˢ fmt σx tt)
      relA = subst (λ t → RelGM Once.Spec.Grade.pure ty _ (SD.⟦ t ⟧ˢ fmt σx tt)) (proj₂ (proj₂ (proj₂ w P)))
                   (MBS.bridge⇒ (proj₂ u) {dγ₁ = tt} {γ = tt} {dγ₂ = tt} tt (MB.mk↾ tt) refsR)

  relM-at : (ft : Data.Maybe.Maybe Type) (W′ : MonoWit ft ctx (funBody fi) ty SCx.[])
          → C.compileFunM ft IR.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty (funBody fi) ≡ Data.Sum.inj₂ irFun
          → RelGM Once.Spec.Grade.pure ty (CMB.⟦_⟧ₛ fmt Σ S σ₀ (proj₂ (monoBody {S = S} {sc = AS.scopeOf csc} ss is ts N ft W′)) δ tt)
                   (subst T∞ (cohᴰ ty) (abiT ty M))
  relM-at (Data.Maybe.just A) W′ cf′ = relC {A = A} W′ cf′
  relM-at Data.Maybe.nothing  W′ cf′ = relI W′ cf′

  -- The entry, read back at its (only) instance, is the body's meaning
  -- (`MonoEntry`: the instance substitutes for no variable).
  private
    r0 : Respects ∅ₖ ∅ₖ none
    r0 ()

  entry≡ : CMB.⟦_⟧ₛ fmt Σ S σ₀ Dc δ tt ≡ subst id (⟦wk₀⟧ᵛ ty) (CMB.impSem fmt Σ S′ σ₀ δ′ {∅ₖ} {x} (TView.def zero refl))
  entry≡ =
    H.≅-to-≡ (H.trans (H.trans (H.sym (H.≡-to-≅ (ME.mono-entry-sem Σ fmt S σ₀ ∅ₖ ∅ₖ none r0 Dc δ)))
                               (H.≡-subst-removable (λ X → ⟦ X ⟧ᵛ) (TZ.⟨⟩-0 Σ S none ty) _))
             (H.trans (H.≡-to-≅ (sym (head-at {tl = tl} {sc = monoSchema ty} {D = Dc} none (λ ()) r0)))
                      (H.sym (H.≡-subst-removable id (⟦wk₀⟧ᵛ ty) _))))

  relM : RelGM Once.Spec.Grade.pure ty (CMB.⟦_⟧ₛ fmt Σ S σ₀ Dc δ tt) (subst T∞ (cohᴰ ty) (abiT ty M))
  relM = relM-at (funType fi) W cf

-- D324: `main` joins the telescope and the table, not the definitions' scope.
inv-mono-at : ∀ (b : Bool) {s} {S : Defs s} {csc tl ss is ts pre} {fi : Parser.FunInfo} {ty : Type}
             {Ψ : Ctx.Usage 0} (N : Names S is ts) (W : MonoWit (funType fi) (ctxOf (AS.scopeOf csc)) (funBody fi) ty Ψ)
             {irFun : IR ⌊ Once.Spec.Type.Unit {0} ⌋ ⌊ ty ⌋}
         → C.compileFunM (funType fi) IR.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
             (funName fi) ty (funBody fi) ≡ Data.Sum.inj₂ irFun
         → Inv {S = S} csc tl ss is ts pre → All (funName fi ≢_) (scopeNames csc)
         → Inv (C.cscope (C.CScope.csig csc) (C.extendDefs-at b (C.CScope.cimps csc) (funName fi) ty) (C.CScope.ctele csc))
               (monoDef {S = S} {sc = AS.scopeOf csc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W)
               ss (impDefs b is) (wkT ts)
               (irFunOf (C.mkCompiledFun (bare (funName fi)) ty irFun) ∷ pre)

inv-mono : ∀ {s} {S : Defs s} {csc tl ss is ts pre} {fi : Parser.FunInfo} {ty : Type}
             {Ψ : Ctx.Usage 0} (N : Names S is ts) (W : MonoWit (funType fi) (ctxOf (AS.scopeOf csc)) (funBody fi) ty Ψ)
             {irFun : IR ⌊ Once.Spec.Type.Unit {0} ⌋ ⌊ ty ⌋}
         → C.compileFunM (funType fi) IR.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
             (funName fi) ty (funBody fi) ≡ Data.Sum.inj₂ irFun
         → Inv {S = S} csc tl ss is ts pre → All (funName fi ≢_) (scopeNames csc)
         → Inv (C.extendScope csc (funName fi) ty)
               (monoDef {S = S} {sc = AS.scopeOf csc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W)
               ss (impDefs (funName fi Str.== "main") is) (wkT ts)
               (irFunOf (C.mkCompiledFun (bare (funName fi)) ty irFun) ∷ pre)
inv-mono {S = S} {csc = csc} {tl = tl} {ss = ss} {is = is} {ts = ts} {pre = pre} {fi} {ty} {Ψ} N W {irFun} cf inv fr =
  inv-mono-at (funName fi Str.== "main") {S = S} {csc} {tl} {ss} {is} {ts} {pre} {fi} {ty} {Ψ} N W {irFun} cf inv fr

inv-mono-at true {S = S} {csc} {tl} {ss} {is} {ts} {pre} {fi} {ty} {SCx.[]} N W {irFun} cf inv fr = record
  { iself = Inv.iself inv
  ; rel   = rel′
  }
  where
    open MonoStep {S = S} {csc} {tl} {ss} {is} {ts} {pre} N {fi} {ty} W {irFun} cf inv
    rel′ : ∀ (later : List IRFun) → NoShadow later (C.CScope.cimps csc)
         → ∀ (I : String → TopCtx) → IAgree I (C.CScope.ctele csc) → ∀ (uf′ : Imports)
         → MB.MRel fmt Σ σ₀ (σW (later ++ e ∷ pre) (C.cpolys csc) I uf′) ctx
                   (CE.envOf fmt Σ S′ σ₀ δ′ ss (wkI is) (wkT ts))
    rel′ later ns I ia uf′ =
      subst (λ dm → MB.EnvRel fmt Σ σ₀ σ (C.cpolys csc) dm) (sym (defEnv-wk {sc = monoSchema ty} {tl = tl} ts)) (proj₁ old)
      , subst (λ im → MB.ImpRel fmt Σ σ₀ σ (C.CScope.cimps csc) im)
              (sym (impEnv-wk {sc = monoSchema ty} {tl = tl} is)) (proj₁ (proj₂ old))
      , sigR tl′ ss σ refl
      where
        σ = σW (later ++ e ∷ pre) (C.cpolys csc) I uf′
        old : MB.MRel fmt Σ σ₀ σ ctx ρ
        old = subst (λ tbl → MB.MRel fmt Σ σ₀ (σW tbl (C.cpolys csc) I uf′) ctx ρ)
                    (++-assoc later (e ∷ []) pre)
                    (Inv.rel inv (later ++ e ∷ [])
                       (ns-snoc later (C.CScope.cimps csc) e refl
                          (bare-ne (C.CScope.cimps csc) (map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc)) fr) ns)
                       I ia uf′)
inv-mono-at false {S = S} {csc} {tl} {ss} {is} {ts} {pre} {fi} {ty} {SCx.[]} N W {irFun} cf inv fr = record
  { iself = Inv.iself inv
  ; rel   = rel′
  }
  where
    open MonoStep {S = S} {csc} {tl} {ss} {is} {ts} {pre} N {fi} {ty} W {irFun} cf inv
    rel′ : ∀ (later : List IRFun) → NoShadow later ((x , ty) ∷ C.CScope.cimps csc)
         → ∀ (I : String → TopCtx) → IAgree I (C.CScope.ctele csc) → ∀ (uf′ : Imports)
         → MB.MRel fmt Σ σ₀ (σW (later ++ e ∷ pre) (C.cpolys csc) I uf′)
                   (ctxOf (AS.scopeOf (C.cscope (C.CScope.csig csc) ((x , ty) ∷ C.CScope.cimps csc) (C.CScope.ctele csc))))
                   (CE.envOf fmt Σ S′ σ₀ δ′ ss (i-def zero refl (wkI is)) (wkT ts))
    rel′ later ns I ia uf′ =
      subst (λ dm → MB.EnvRel fmt Σ σ₀ σ (C.cpolys csc) dm) (sym (defEnv-wk {sc = monoSchema ty} {tl = tl} ts)) (proj₁ old)
      , (new , subst (λ im → MB.ImpRel fmt Σ σ₀ σ (C.CScope.cimps csc) im)
                     (sym (impEnv-wk {sc = monoSchema ty} {tl = tl} is)) (proj₁ (proj₂ old)))
      , sigR tl′ ss σ refl
      where
        σ = σW (later ++ e ∷ pre) (C.cpolys csc) I uf′
        old : MB.MRel fmt Σ σ₀ σ ctx ρ
        old = subst (λ tbl → MB.MRel fmt Σ σ₀ (σW tbl (C.cpolys csc) I uf′) ctx ρ)
                    (++-assoc later (e ∷ []) pre)
                    (Inv.rel inv (later ++ e ∷ [])
                       (ns-step later (C.CScope.cimps csc) e refl
                          (bare-ne (C.CScope.cimps csc) (map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc)) fr) ns)
                       I ia uf′)
        callRel : RelS (RelD ty) (MB.callSD fmt Σ σ₀ σ x ty) (subst T∞ (cohᴰ ty) (abiT ty M))
        callRel = ≡ˡ (callSD-later later (e ∷ pre) (C.cpolys csc) I uf′ x ty (ns-head later (C.CScope.cimps csc) ns))
                     (coh-runs ty (abi ty x pre irFun))
        new : RelGM Once.Spec.Grade.pure ty (subst id (⟦wk₀⟧ᵛ ty) (CMB.impSem fmt Σ S′ σ₀ δ′ {∅ₖ} {x} (TView.def zero refl)))
                    (MB.callSD fmt Σ σ₀ σ x ty)
        new = subst (λ m → RelGM Once.Spec.Grade.pure ty m (MB.callSD fmt Σ σ₀ σ x ty)) entry≡
                    (GM-D Once.Spec.Grade.pure ty relM callRel)

------------------------------------------------------------------------
-- A telescope entry: typed once over its parameters; each reference to it is
-- the resolver's splice of its body at the instance (6e).
------------------------------------------------------------------------

-- Plan 0.122: a reference at a kinded instance splices the checker's term at
-- the instance; it means what the entry instantiated there means — the
-- witness over the parameters, instantiated (`WitnessSubst`), is typed by the
-- instantiated core typing (`UseCommute`), means its realization
-- (`MeaningBridgeS`), and that realization means what the instance's does
-- (`CoherenceS`), whose term the checker built.
inv-poly : ∀ {s} {S : Defs s} {csc tl ss is ts pre} {pfi : Parser.PolyFunInfo} {Ψ : Ctx.Usage 0}
             (N : Names S is ts)
             (W : PolyWit (AS.scopeOf csc) pfi Ψ)
         → Inv {S = S} csc tl ss is ts pre → All (pfunName pfi ≢_) (scopeNames csc)
         → Inv (C.addEntry csc pfi)
               (polyDef {S = S} {sc = AS.scopeOf csc} {pfi = pfi} {Ψ = Ψ} tl ss is ts N W)
               ss (wkI is) (t-def zero refl (wkT ts)) pre
inv-poly {S = S} {csc} {tl} {ss} {is} {ts} {pre} {pfi} {SCx.[]} N W inv fr = record
  { iself = declImps-head (pfi , C.ctop csc) (C.CScope.ctele csc) (y Str.≟ y)
            ∷ iself-step (pfi , C.ctop csc) (C.CScope.ctele csc) (C.CScope.ctele csc) frT (Inv.iself inv)
  ; rel   = rel′
  }
  where
    y     = pfunName pfi
    scT   = pfunType pfi
    S′    = S ▷ schemaOf scT
    δ     = teleSem fmt mo tl
    δ′    = teleSem fmt mo (polyDef {S = S} {sc = AS.scopeOf csc} {pfi = pfi} {Ψ = SCx.[]} tl ss is ts N W)
    ctx   = ctxOf (AS.scopeOf csc)
    ρ     = CE.envOf fmt Σ S σ₀ δ ss is ts
    V     = viewOf {S = S} ss is ts
    frT   = ++⁻ʳ (map proj₁ (C.CScope.cimps csc)) fr

    rel′ : ∀ (later : List IRFun) → NoShadow later (C.CScope.cimps csc)
         → ∀ (I : String → TopCtx) → IAgree I ((pfi , C.ctop csc) ∷ C.CScope.ctele csc) → ∀ (uf : Imports)
         → MB.MRel fmt Σ σ₀ (σW (later ++ pre) (C.cpolys (C.addEntry csc pfi)) I uf) (ctxOf (AS.scopeOf (C.addEntry csc pfi)))
                   (CE.envOf fmt Σ S′ σ₀ δ′ ss (wkI is) (t-def zero refl (wkT ts)))
    rel′ later ns I (iy ∷ ia) uf =
      ( head
      , envrel-transport σo σ (C.cpolys csc) (ra (C.CScope.ctele csc) frT)
          (subst (λ dm → MB.EnvRel fmt Σ σ₀ σo (C.cpolys csc) dm)
                 (sym (defEnv-wk {sc = schemaOf scT} {tl = tl} ts)) (proj₁ old)) )
      , subst (λ im → MB.ImpRel fmt Σ σ₀ σ (C.CScope.cimps csc) im)
              (sym (impEnv-wk {sc = schemaOf scT} {tl = tl} is))
              (imprel-transport σo σ (C.CScope.cimps csc)
                 (calls-same tbl (C.cpolys csc) (C.cpolys (C.addEntry csc pfi)) I I uf uf (C.CScope.cimps csc)) (proj₁ (proj₂ old)))
      , sigR (polyDef {S = S} {sc = AS.scopeOf csc} {pfi = pfi} {Ψ = SCx.[]} tl ss is ts N W) ss σ refl
      where
        tbl = later ++ pre
        σo  = σW tbl (C.cpolys csc) I uf
        σ   = σW tbl (C.cpolys (C.addEntry csc pfi)) I uf
        old : MB.MRel fmt Σ σ₀ σo ctx ρ
        old = Inv.rel inv later ns I ia uf

        -- the telescope's earlier entries are not the new one
        ra : ∀ (qs : List (Parser.PolyFunInfo × TopCtx)) → All (y ≢_) (map (λ q → pfunName (proj₁ q)) qs)
           → RefsAgree σo σ (C.buildPolyCtx (map proj₁ qs))
        ra []       []       = tt
        ra (q ∷ qs) (h ∷ hs) =
          (λ A → sym (refs-skip I uf (tableEnv fmt φ tbl) y {pfunType pfi} {pfunBody pfi} (C.cpolys csc) (pfunName (proj₁ q)) A h))
          , ra qs hs

        -- the scope's Pack, and over the parameters
        P  = packOf {S = S} {sc = AS.scopeOf csc} ss is ts N
        κ  = kindsOf scT
        Pκ = packOfAt κ {S = S} {sc = AS.scopeOf csc} ss is ts N
        ctxT = Once.TypeCheck.Classify.ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)

        module MBS = Once.Adequacy.MeaningBridgeS fmt Σ S (Names.nm N) (OkOf P) (OkSOf P) (Names.inline N) σ₀ σo (σW-self tbl (C.cpolys csc) I uf) ∅ₖ
        module COH = Once.Adequacy.CoherenceS fmt Σ S (Names.nm N) (OkOf P) (OkSOf P) (Names.inline N)
                       (ok-gen P) (ok-sig P) (ok-inj P) (λ {c} → oks-fun P {c}) ∅ₖ
        module RS = Once.Denotation.RealizeS Σ S (Names.nm N) (OkOf P) (OkSOf P) (Names.inline N) ∅ₖ
        module UM = Once.TypeCheck.Use Σ S (Names.nm N) (OkOf P) (OkSOf P) ∅ₖ

        -- the scope's references, related (as for a monomorphic entry)
        refsR : MBS.Refs δ
        refsR = record
          { entry = SR.refs-entry fmt Σ σ₀ σo (σW-self tbl (C.cpolys csc) I uf) ctx (Names.nm N) (Names.inline N) V (OkSOf P)
                      (Pack.h-imp P) (Pack.h-imp-call P) (Pack.h-poly P) (Pack.h-poly-inline P) δ ρ (CE.agree fmt Σ S σ₀ δ ss is ts) old
          ; sigop = λ {c} {T} mem k h →
              SR.RelGM-≅ fmt Σ σ₀ σo (σW-self tbl (C.cpolys csc) I uf) {A = Once.Internal.Type.wk₀ {0} T} {B = Once.Internal.Type.wk₀ {0} T} refl
                (H.trans (H.≡-subst-removable (SE.M Once.Spec.Grade.pure) (sym (⟦wk₀⟧ᵛ T)) _) (H.≡-subst-removable id (⟦wk₀⟧ᵛ T) _))
                H.refl
                (RelGM-wk₀ {π = Once.Spec.Grade.pure} {A = T}
                  (subst (λ md → RelGM Once.Spec.Grade.pure T
                                   (subst id (⟦wk₀⟧ᵛ T) (subst (λ X → ⟦ X ⟧ᵛ) (⌜declS⌝ k h) (SM.sigopᵛ Σ fmt S σ₀ c (declS T) mem md)))
                                   (SD.sigOpSem T c k fmt σo))
                         (sym (teleSem-model fmt mo tl)) (SSg.sig-rel Σ wf J uniq fmt σ₀ S σo refl k h mem)))
          }

        -- a related pair of terms, their meanings related, read at the instance's type
        fin : ∀ {X U : Type} {m} {a : Srf.Expr SCx.∅ SCx.[] U} {b : Srf.Expr SCx.∅ SCx.[] X} {t}
            → a CH.≅ b → RelGM Once.Spec.Grade.pure X m (SD.⟦ b ⟧ˢ fmt σo tt) → t ≡ SD.⟦ a ⟧ˢ fmt σo tt
            → ∀ {m′} → m′ H.≅ m → RelGM Once.Spec.Grade.pure U m′ t
        fin {X = X} (CH.≅i refl refl h) rg refl H.refl = GM-D Once.Spec.Grade.pure X rg (≈-out h σo (σW-self tbl (C.cpolys csc) I uf) tt)

        -- the new entry: its splice at an instance is its core instance
        head₀ : ∀ (U : Type) (ki : KindedInstance ∅ₖ scT U)
              → RelGM Once.Spec.Grade.pure U (CMB.entrySem fmt Σ S′ σ₀ δ′ zero {scT} refl ki) (SD.DefsSem.refs σ y U)
        head₀ U ki = fin hU (MBS.bridge⇐ (proj₂ su) {dγ₁ = tt} {γ = tt} {dγ₂ = tt} tt (MB.mk↾ tt) refsR) relRefs entryH
          where
            K   = kinded-instance scT ki
            τ   = proj₁ K
            r   = proj₁ (proj₂ K)
            module WS = Once.TypeCheck.WitnessSubst Σ S (Names.nm N) (OkOf P) (OkSOf P) κ ∅ₖ τ r
            module UCm = Once.Adequacy.UseCommute Σ S (Names.nm N) (OkOf P) (OkSOf P) κ ∅ₖ τ r
            -- the witness over the parameters, and at the instance
            wΔ  = proj₁ (proj₂ (proj₂ (proj₂ W)))
            uΔ  = proj₁ (proj₂ (proj₂ wΔ Pκ))
            su  = WS.subW⇐ (proj₂ uΔ)
            -- the checker at the instance: it accepts the instantiated witness
            cc  = subst (λ X → ∃[ se ] ∃[ d ] ∃[ f ] Once.TypeCheck.Elaborate.checkElab ctxT (pfunBody pfi) X
                                                      ≡ Once.TypeCheck.Elaborate.success SCx.[] se d f)
                        (proj₂ (proj₂ K)) (check-completeS P (proj₂ su))
            se  = proj₁ cc
            ce  = proj₂ (proj₂ (proj₂ cc))
            cr  = Once.TypeCheck.Elaborate.checkElabV ctxT (pfunBody pfi) U
            rU  = proj₂ (wit-of cr ce) P
            uU  = proj₁ (proj₂ rU)
            hU  = COH.coh⇐ UM.sh-∅ (proj₂ uU) (proj₂ su) (sym (proj₂ (proj₂ K)))
            -- the reference is the splice, the checker's term, the instance's realization
            relRefs : SD.DefsSem.refs σ y U ≡ SD.⟦ RS.realize⇐ UM.sh-∅ (proj₂ uU) ⟧ˢ fmt σo tt
            relRefs =
              trans (refs-head I uf (tableEnv fmt φ tbl) y {pfunType pfi} {pfunBody pfi} (C.cpolys csc) U)
                (trans (cong (λ X → SD.⟦ spliceClosed I uf (C.cpolys csc) y
                                          (Once.TypeCheck.Elaborate.checkElabV (Once.TypeCheck.Classify.ctxWithImportsAndPolys X (C.cpolys csc))
                                             (pfunBody pfi) U) ⟧ˢ fmt (RF.σ₀ fmt (tableEnv fmt φ tbl)) tt) iy)
                  (trans (cong (λ e′ → SD.⟦ e′ ⟧ˢ fmt (RF.σ₀ fmt (tableEnv fmt φ tbl)) tt) (splice-form I uf (C.cpolys csc) y cr ce))
                    (trans (RF.resolveExpr-faithful fmt (tableEnv fmt φ tbl) (C.cpolys csc) I uf 0 se tt)
                           (cong (λ e′ → SD.⟦ e′ ⟧ˢ fmt σo tt) (sym (proj₂ (proj₂ rU)))))))
            -- the entry at the instance is the instantiated witness's core meaning
            entryH : CMB.entrySem fmt Σ S′ σ₀ δ′ zero {scT} refl ki H.≅ CMB.⟦_⟧ₛ fmt Σ S σ₀ (UC.typ⇐ Σ S (Names.nm N) (OkOf P) (OkSOf P) ∅ₖ (proj₂ su)) δ tt
            entryH =
              H.trans (H.≡-subst-removable (λ X → ⟦ X ⟧ᵛ) (proj₂ (proj₂ K)) _)
                (H.≡-to-≅ (trans (head-at {tl = tl} {sc = schemaOf scT} {D = UC.typ⇐ Σ S (Names.nm N) (OkOf P) (OkSOf P) κ (proj₂ uΔ)} τ r r)
                                 (⟦⟧ˢ-≅ (H.sym (UCm.cm⇐ UM′.sh-∅ (proj₂ uΔ))))))
              where module UM′ = Once.TypeCheck.Use Σ S (Names.nm N) (OkOf P) (OkSOf P) κ

        -- …at any kinds over no variable (there is one such context).
        head : ∀ {Δ : KCtx 0} (U : Type) (ki : KindedInstance Δ scT U)
             → RelGM Once.Spec.Grade.pure U (CMB.entrySem fmt Σ S′ σ₀ δ′ zero {scT} refl ki) (SD.DefsSem.refs σ y U)
        head {Δ} U ki = go (extensionality λ ()) ki
          where
            go : ∀ {Δ′ : KCtx 0} → ∅ₖ ≡ Δ′ → (ki′ : KindedInstance Δ′ scT U)
               → RelGM Once.Spec.Grade.pure U (CMB.entrySem fmt Σ S′ σ₀ δ′ zero {scT} refl ki′) (SD.DefsSem.refs σ y U)
            go refl ki′ = head₀ U ki′

------------------------------------------------------------------------
-- The entry point among the remaining names
------------------------------------------------------------------------

-- A `main` later in the telescope has a name there.
mainIn-name : ∀ {sc es} (mt : ModTele sc es) → MainIn mt → Any ("main" ≡_) (map entryName es)
mainIn-name []                          ()
mainIn-name (ffi _ _ _ _ rest)        mi          = there (mainIn-name rest mi)
mainIn-name (poly _ _ rest)             mi          = there (mainIn-name rest mi)
mainIn-name (mono _ _ _ _ rest)     (inj₁ (p , _)) = here (sym p)
mainIn-name (mono _ _ _ _ rest)     (inj₂ mi)   = there (mainIn-name rest mi)

not-in : ∀ {x : String} {ys} → All (x ≢_) ys → Any (x ≡_) ys → ⊥
not-in (h ∷ _)  (here e)  = h e
not-in (_ ∷ hs) (there a) = not-in hs a

------------------------------------------------------------------------
-- The table past an entry: entries of the later names, which are new
------------------------------------------------------------------------

NS : C.FunCtx → IRFun → Set
NS imps e = All (λ p → fname e ≢ bare (proj₁ p)) imps

ns-of : ∀ {y : String} (imps : C.FunCtx) → All (λ p → y ≢ proj₁ p) imps → ∀ (e : IRFun) → fname e ≡ bare y → NS imps e
ns-of []       []       e eq = []
ns-of (p ∷ ps) (h ∷ hs) e eq = (λ q → h (MIF.bare-injective (trans (sym eq) q))) ∷ ns-of ps hs e eq

-- Every entry the rest of the walk adds to the table has a name new to the scope.
later-ns : ∀ {sc es} (b : FB.FunBundle sc es) (imps : C.FunCtx)
         → All (λ y → All (λ p → y ≢ proj₁ p) imps) (map entryName es)
         → ∀ (xs : List IRFun) → All (NS imps) xs → All (NS imps) (tableOf-go (FB.bundle→compiled b) xs)
later-ns FB.bnil imps _ xs a = a
later-ns (FB.bffi _ _ _ _ rest) imps (_ ∷ hs) xs a = later-ns rest imps hs xs a
later-ns (FB.bcons {fi = fi} {ty = ty} {irFun = irFun} _ _ _ _ _ rest) imps (h ∷ hs) xs a =
  later-ns rest imps hs (irFunOf (C.mkCompiledFun (bare (funName fi)) ty irFun) ∷ xs)
           (ns-of imps h (irFunOf (C.mkCompiledFun (bare (funName fi)) ty irFun)) refl ∷ a)
later-ns (FB.bpoly _ _ rest) imps (_ ∷ hs) xs a = later-ns rest imps hs xs a

