-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.TeleWalk.Invariant — the telescope walk's per-entry steps
-- (`Inv` and its ffi/mono/poly steps, plus the position facts about later
-- tables). Split from `Once.Adequacy.TeleWalk` for the per-module check cap;
-- that module has the walk itself and `main`'s step.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

open import Once.Denotation.TraceMonad using (Interp)

-- Plan 0.105: at an interpretation `ι` — the meaning and the compiled program
-- run against the same one.
module Once.Adequacy.TeleWalk.Invariant (fmt : TargetNum) (ι : Interp) where

open import Data.Nat using (ℕ)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.Type using (Type)
open import Once.Type.DecEq using (_≟T_)
open import Once.Type.Rigid using (RigidFree; KindedInstance)
open import Once.Type.Honest using (HonestFFI)
open import Once.CanonicalName using (bare)
open import Once.Functor.Translate using (IsConcrete)
import Once.Compile as C
open C.FunInfo using (funName; funBody; funType; funIsPrimitive)
open C.PolyFunInfo using (pfunName; pfunType; pfunBody)
open import Once.IR using (IR)
import Once.IR
open import Once.IRTy using (⌊_⌋)
import Once.Surface.Context as Ctx
import Once.Surface.Syntax as Srf
open import Once.TypeCheck.Classify using (Imports)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Type.Rigid using (rigidOf)
open import Once.Denotation.Realize using (realize)
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.Program using (IRFun; fname)
open import Once.Spec.Module using (ModTele; []; ffi; mono; poly; MainIn; EffUU; ctxOf)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Core.Telescope using (Tele; def; teleSem; runProgram; program; noKinds; noVars; noResp)
open import Once.Spec.Core.Schema using (schemaOf; kindsOf; kinded-instance)
open import Once.Spec.Core.Translate using (ImpSig; TeleSig; i-ffi; i-def; t-def; wkI; wkT; SigCF; toProgram; viewOf;
  monoHere; monoElab; monoBody; monoSchema; monoSg; polyElab; polyBody; polySg)
import Once.Spec.Core.Abstract as A
import Once.Spec.Core.Translate as TR
open import Once.Adequacy.SourceTrace using (irFunOf; tableOf-go; mainCall)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.FunBundle as FB
import Once.Adequacy.MainIRForm as MIF
import Once.Adequacy.MeaningBridge as MB
import Once.Adequacy.CoreEnv as CE
import Once.Adequacy.CoreMeaningBridge as CMB
import Once.Adequacy.CoreAbsSem as CAS
import Once.Spec.Elaboration as ElabM
import Once.Spec.Core.Meaning as GM
import Once.Spec.Core.PolyTyping as PT
import Once.Denotation.Meaning as MeaningM
open import Once.SigOp.Info using (FFIAnswers)

-- The interpretation's pure half: what the program's pure FFI values are.
φ : FFIAnswers
φ = Interp.pure ι

open import Once.Adequacy.GradedRelation fmt using (RelGT; RelGM; RelGT-bind)
open import Once.Denotation.TraceMonad using (T; projTrace)
open import Once.Adequacy.TeleEnvLemmas fmt φ using (σW; callSD-later; refs-skip; refs-head; spliceClosed; RefsAgree; envrel-transport;
  imprel-transport; calls-same)
import Once.Adequacy.TeleEntry fmt φ as TE

import Once.Adequacy.ElabInst as EI
open import Once.Type.Rigid using (RigidFree)
import Once.Adequacy.SourceFaithful as SF
import Once.Adequacy.ResolveFaithful as RF
open import Once.Adequacy.Coherence fmt using (realize-invariant)
import Once.TypeCheck.Completeness
import Once.TypeCheck.Elaborate
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
open import Once.Parser using (validIdentB)
open import Once.Denotation.DenotTrace using (evalᴰ; cohᴰ)
open import Once.Denotation.Program using (tableEnv)
open import Once.Adequacy.TableCall fmt φ using (abiT; abi; tableEnv-skip; tableEnv-hit; uncurry-app)
open import Once.Denotation.Trace using (SigOpEvent)
import Data.Fin
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
import Relation.Nullary
open import Once.Denotation.GradedOps using (sigOpRefᵛ)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ)
open import Once.Functor.Translate using (IsConcrete-irrelevant)
open import Data.List.Properties using (++-assoc)
open import Once.Adequacy.TelePosition
open import Once.Denotation.TraceMonad using (RelT′-events)
open import Once.Denotation.Program using (tableCalls)
open import Data.List using (take)

------------------------------------------------------------------------
-- Position predicates
------------------------------------------------------------------------

-- Later table entries do not shadow a name in scope.
NoShadow : List IRFun → C.FunCtx → Set
NoShadow later imps = All (λ e → All (λ p → fname e ≢ bare (proj₁ p)) imps) later

-- THE INVARIANT at a position of the walk.
record Inv {s} {S : Sig s} (csc : C.CScope) (tl : Tele S) (is : ImpSig S (C.CScope.cimps csc))
           (ts : TeleSig S (C.telePolys (C.CScope.ctele csc))) (pre : List IRFun) : Set where
  field
    valid : CE.DefsValid fmt S (teleSem fmt φ tl) is
    -- D243/D252: the scope's imports are ground (FFI and monomorphic types are),
    -- so instantiating a polymorphic body fixes them.
    irf   : ImportsRF (C.CScope.cimps csc)
    iself : IAgree (C.declImps (C.CScope.ctele csc)) (C.CScope.ctele csc)
    rel   : ∀ (later : List IRFun) → NoShadow later (C.CScope.cimps csc)
          → ∀ (I : String → Imports) → IAgree I (C.CScope.ctele csc) → ∀ (uf : Imports)
          → MB.MRel fmt (σW (later ++ pre) (C.cpolys csc) I uf) (ctxOf (AS.scopeOf csc))
                    (CE.envOf fmt S (teleSem fmt φ tl) is ts)

------------------------------------------------------------------------
-- An FFI entry: its call is its contract (TeleEntry.ffi-entry).
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

  ns-head : ∀ (later : List IRFun) {x : String} {ty : Type} (imps : C.FunCtx)
          → NoShadow later ((x , ty) ∷ imps) → All (λ e → fname e ≢ bare x) later
  ns-head []           imps []             = []
  ns-head (e ∷ later) imps ((h ∷ _) ∷ ns) = h ∷ ns-head later imps ns

inv-ffi : ∀ {s} {S : Sig s} {csc tl is ts pre} {fi : C.FunInfo} {ty : Type} {k c : IsConcrete ty}
            {h : HonestFFI ty} {g : RigidFree ty}
        → Inv {S = S} csc tl is ts pre → All (funName fi ≢_) (scopeNames csc)
        → Inv (C.extendScope csc (funName fi) ty) tl (i-ffi k h g is) ts (irFunOf (FB.primCF fi ty c) ∷ pre)
inv-ffi {S = S} {csc} {tl} {is} {ts} {pre} {fi} {ty} {k} {c} {h} {g} inv fr = record
  { valid = Inv.valid inv
  ; irf   = irf-cons {imps = C.CScope.cimps csc} {y = funName fi} {ty = ty} g (Inv.irf inv)
  ; iself = Inv.iself inv
  ; rel   = rel′
  }
  where
    x = funName fi
    δ = teleSem fmt φ tl
    e = irFunOf (FB.primCF fi ty c)
    rel′ : ∀ (later : List IRFun) → NoShadow later ((x , ty) ∷ C.CScope.cimps csc)
         → ∀ (I : String → Imports) → IAgree I (C.CScope.ctele csc) → ∀ (uf : Imports)
         → MB.MRel fmt (σW (later ++ e ∷ pre) (C.cpolys csc) I uf) (ctxOf (AS.scopeOf (C.extendScope csc x ty)))
                   (CE.envOf fmt S δ (i-ffi k h g is) ts)
    rel′ later ns I ia uf = proj₁ old , (new , proj₁ (proj₂ old)) , refl
      where
        old : MB.MRel fmt (σW (later ++ e ∷ pre) (C.cpolys csc) I uf) (ctxOf (AS.scopeOf csc)) (CE.envOf fmt S δ is ts)
        old = subst (λ tbl → MB.MRel fmt (σW tbl (C.cpolys csc) I uf) (ctxOf (AS.scopeOf csc)) (CE.envOf fmt S δ is ts))
                    (++-assoc later (e ∷ []) pre)
                    (Inv.rel inv (later ++ e ∷ [])
                       (ns-step later (C.CScope.cimps csc) e refl
                          (bare-ne (C.CScope.cimps csc) (map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc)) fr) ns)
                       I ia uf)
        new : RelGM Once.Type.pure ty (sigOpRefᵛ fmt φ (bare x) k) (MB.callSD fmt (σW (later ++ e ∷ pre) (C.cpolys csc) I uf) x ty)
        new = subst (λ k′ → RelGM Once.Type.pure ty (sigOpRefᵛ fmt φ (bare x) k′) (MB.callSD fmt (σW (later ++ e ∷ pre) (C.cpolys csc) I uf) x ty))
                    (IsConcrete-irrelevant c k)
                    (subst (RelGM Once.Type.pure ty (sigOpRefᵛ fmt φ (bare x) c))
                           (sym (callSD-later later (e ∷ pre) (C.cpolys csc) I uf x ty (ns-head later (C.CScope.cimps csc) ns)))
                           (TE.ffi-entry pre x ty c))

------------------------------------------------------------------------
-- A monomorphic entry: its call (the compiled body, read through the ABI)
-- is its core entry — the compile chain (faithful, the resolver, realize),
-- leg A in the scope's environment, leg B, and F for the read-back.
------------------------------------------------------------------------

-- Every name the telescope may define is an identifier (the extractor's guard).
MonoValid : C.Entry → Set
MonoValid (C.e-fun fi)   = funIsPrimitive fi ≡ false → validIdentB (funName fi) ≡ true
MonoValid (C.e-poly pfi) = ⊤

private
  does-no : ∀ {A : Set} (d : Dec A) → ¬ A → Relation.Nullary.isYes d ≡ false
  does-no (yes a) ¬a = ⊥-elim (¬a a)
  does-no (no _)  _  = refl

  -- The splice of a telescope body is its derivation's realization, resolved.
  splice-form : ∀ (I : String → Imports) (uf : Imports) (pre : Once.TypeCheck.Classify.PolyCtx) (y : String)
                  {Xs : Imports} {b : _} {A : Type} {se : _} {d f : ℕ}
                  (cr : Once.TypeCheck.Elaborate.VerifiedCheckResult (Once.TypeCheck.Classify.ctxWithImportsAndPolys Xs pre) b A)
                  (ce : proj₁ cr ≡ Once.TypeCheck.Elaborate.success Ctx.Usage.[] se d f)
              → spliceClosed I uf pre y cr ≡ Srf.closed (resolveExpr pre I uf 0 (realize (sound-of cr ce)))
  splice-form I uf pre y (Once.TypeCheck.Elaborate.success _ _ _ _ , w) refl = refl

impEnv-wk : ∀ {s} {S : Sig s} {sc} {tl : Tele S} {body : _} {D : _} {imps} (is : ImpSig S imps)
          → CE.impEnv fmt (S Once.Spec.Core.PolyTy.▷ sc) (teleSem fmt φ (def tl sc body D)) (wkI is) ≡ CE.impEnv fmt S (teleSem fmt φ tl) is
impEnv-wk TR.[]              = refl
impEnv-wk {sc = sc} {tl} {body} {D} (TR.i-ffi c h g is) = cong₂ _,_ refl (impEnv-wk {sc = sc} {tl = tl} {body = body} {D = D} is)
impEnv-wk {sc = sc} {tl} {body} {D} (TR.i-def d e is) = cong₂ _,_ refl (impEnv-wk {sc = sc} {tl = tl} {body = body} {D = D} is)

defEnv-wk : ∀ {s} {S : Sig s} {sc} {tl : Tele S} {body : _} {D : _} {ps} (ts : TeleSig S ps)
          → CE.defEnv fmt (S Once.Spec.Core.PolyTy.▷ sc) (teleSem fmt φ (def tl sc body D)) (wkT ts) ≡ CE.defEnv fmt S (teleSem fmt φ tl) ts
defEnv-wk TR.[]              = refl
defEnv-wk {sc = sc} {tl} {body} {D} (TR.t-def d e ts) = cong₂ _,_ refl (defEnv-wk {sc = sc} {tl = tl} {body = body} {D = D} ts)

valid-wk : ∀ {s} {S : Sig s} {sc} {tl : Tele S} {body : _} {D : _} {imps} (is : ImpSig S imps)
         → CE.DefsValid fmt S (teleSem fmt φ tl) is → CE.DefsValid fmt (S Once.Spec.Core.PolyTy.▷ sc) (teleSem fmt φ (def tl sc body D)) (wkI is)
valid-wk TR.[]             v        = tt
valid-wk {sc = sc} {tl} {body} {D} (TR.i-ffi c h g is) v        = valid-wk {sc = sc} {tl = tl} {body = body} {D = D} is v
valid-wk {sc = sc} {tl} {body} {D} (TR.i-def d e is) (h , v)  = h , valid-wk {sc = sc} {tl = tl} {body = body} {D = D} is v

-- The compile chain of a monomorphic entry: its compiled body, read through the
-- ABI, is related to its elaboration's core meaning.
module MonoStep {s} {S : Sig s} {csc : C.CScope} {tl : Tele S} {is : ImpSig S (C.CScope.cimps csc)}
                {ts : TeleSig S (C.telePolys (C.CScope.ctele csc))} {pre : List IRFun}
                (sg : SigCF S) {fi : C.FunInfo} {ty : Type} (g : RigidFree ty)
                (D : ctxOf (AS.scopeOf csc) ⊢ᶜ funBody fi ∶ ty ⨾ Ctx.Usage.[])
                {irFun : IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋}
                (cf : C.compileFun C.Heap false (C.CScope.cimps csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                        (funName fi) ty (funBody fi) ≡ Data.Sum.inj₂ irFun)
                (inv : Inv {S = S} csc tl is ts pre) where
  x    = funName fi
  δ    = teleSem fmt φ tl
  S′   = S Once.Spec.Core.PolyTy.▷ monoSchema ty
  bodyT = A.absTm S noKinds (proj₁ (monoElab {S = S} {sc = AS.scopeOf csc} {fi = fi} is ts D))
  bodyD = monoBody {S = S} {sc = AS.scopeOf csc} {fi = fi} is ts sg g D
  tl′  = def tl (monoSchema ty) bodyT bodyD
  δ′   = teleSem fmt φ tl′
  e    = irFunOf (C.mkCompiledFun (bare x) ty irFun false)
  ctx  = ctxOf (AS.scopeOf csc)
  ρ    = CE.envOf fmt S δ is ts
  V    = viewOf {S = S} is ts
  Dc   = proj₂ (ElabM.elabᶜ S V D)
  uf : C.FunCtx
  uf   = (x , ty) ∷ C.CScope.cimps csc
  σx   = σW pre (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf
  ccE  = Once.TypeCheck.Completeness.check-complete D
  ce   = proj₂ (proj₂ (proj₂ ccE))
  D′   = sound-of (Once.TypeCheck.Elaborate.checkElabV ctx (funBody fi) ty) ce
  M    = evalᴰ fmt (tableEnv fmt φ pre) irFun tt

  -- the compiled body means the elaboration's surface meaning (the compile chain)
  chain : subst T (cohᴰ ty) M ≡ SD.⟦ realize D ⟧ˢ fmt σx tt
  chain =
    trans (cong (λ ir → subst T (cohᴰ ty) (evalᴰ fmt (tableEnv fmt φ pre) ir tt))
                (irFun-form (C.CScope.cimps csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty (funBody fi) cf ce))
      (trans ((SF.faithful∅ fmt (tableEnv fmt φ pre) (resolveExpr (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 (realize D′))))
        (trans ((RF.resolveExpr-faithful fmt (tableEnv fmt φ pre) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 (realize D′) tt))
               (realize-invariant D′ D σx tt)))

  relA : RelGM Once.Type.pure ty (MeaningM.⟦_⟧ᶜ D fmt ρ tt) (SD.⟦ realize D ⟧ˢ fmt σx tt)
  relA = MB.bridge-c fmt σx D {dγ₁ = tt} {dγ₂ = tt} (MB.mk↾ tt)
           (Inv.rel inv [] [] (C.declImps (C.CScope.ctele csc)) (Inv.iself inv) uf)

  entry≡ : GM.⟦_⟧ S Dc fmt δ tt ≡ CMB.refSem fmt S′ δ′ {d = zero} {U = ty} (TR.mono-inst {S = S′} {d = zero} {T′ = ty} refl)
  entry≡ = sym (CAS.mono-entry-sem S noKinds _ _ sg g Dc fmt δ)

  relM : RelGM Once.Type.pure ty (GM.⟦_⟧ S Dc fmt δ tt) (subst T (cohᴰ ty) (abiT ty M))
  relM = TE.abi-rel ty (GM.⟦_⟧ S Dc fmt δ tt) M
           (subst (RelGM Once.Type.pure ty (GM.⟦_⟧ S Dc fmt δ tt)) (sym chain)
                  (subst (λ m → RelGM Once.Type.pure ty m (SD.⟦ realize D ⟧ˢ fmt σx tt))
                         (CMB.bridge-c fmt S {δ = δ} V (CE.agree fmt S δ is ts (Inv.valid inv)) D tt) relA))


inv-mono : ∀ {s} {S : Sig s} {csc tl is ts pre} (sg : SigCF S) {fi : C.FunInfo} {ty : Type} {g : RigidFree ty}
             {Ψ : Ctx.Usage 0} (D : ctxOf (AS.scopeOf csc) ⊢ᶜ funBody fi ∶ ty ⨾ Ψ)
             {irFun : IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋}
         → C.compileFun C.Heap false (C.CScope.cimps csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
             (funName fi) ty (funBody fi) ≡ Data.Sum.inj₂ irFun
         → validIdentB (funName fi) ≡ true
         → Inv {S = S} csc tl is ts pre → All (funName fi ≢_) (scopeNames csc)
         → Inv (C.extendScope csc (funName fi) ty)
               (def tl (monoSchema ty) (A.absTm S noKinds (proj₁ (monoElab {S = S} {sc = AS.scopeOf csc} {fi = fi} is ts D)))
                       (monoBody {S = S} {sc = AS.scopeOf csc} {fi = fi} is ts sg g D))
               (i-def zero refl (wkI is)) (wkT ts)
               (irFunOf (C.mkCompiledFun (bare (funName fi)) ty irFun false) ∷ pre)
inv-mono {S = S} {csc} {tl} {is} {ts} {pre} sg {fi} {ty} {g} {Ctx.Usage.[]} D {irFun} cf vx inv fr = record
  { valid = vx , valid-wk {sc = monoSchema ty} {tl = tl} {body = bodyT} {D = bodyD} is (Inv.valid inv)
  ; irf   = irf-cons {imps = C.CScope.cimps csc} {y = funName fi} {ty = ty} g (Inv.irf inv)
  ; iself = Inv.iself inv
  ; rel   = rel′
  }
  where
    open MonoStep {S = S} {csc} {tl} {is} {ts} {pre} sg {fi} {ty} g D {irFun} cf inv
    rel′ : ∀ (later : List IRFun) → NoShadow later ((x , ty) ∷ C.CScope.cimps csc)
         → ∀ (I : String → Imports) → IAgree I (C.CScope.ctele csc) → ∀ (uf′ : Imports)
         → MB.MRel fmt (σW (later ++ e ∷ pre) (C.cpolys csc) I uf′) (ctxOf (AS.scopeOf (C.extendScope csc x ty)))
                   (CE.envOf fmt S′ δ′ (i-def zero refl (wkI is)) (wkT ts))
    rel′ later ns I ia uf′ =
      subst (λ dm → MB.EnvRel fmt σ (C.cpolys csc) dm) (sym (defEnv-wk {sc = monoSchema ty} {tl = tl} {body = bodyT} {D = bodyD} ts)) (proj₁ old)
      , (new , subst (λ im → MB.ImpRel fmt σ (C.CScope.cimps csc) im)
                     (sym (impEnv-wk {sc = monoSchema ty} {tl = tl} {body = bodyT} {D = bodyD} is)) (proj₁ (proj₂ old)))
      , refl
      where
        σ = σW (later ++ e ∷ pre) (C.cpolys csc) I uf′
        old : MB.MRel fmt σ ctx ρ
        old = subst (λ tbl → MB.MRel fmt (σW tbl (C.cpolys csc) I uf′) ctx ρ)
                    (++-assoc later (e ∷ []) pre)
                    (Inv.rel inv (later ++ e ∷ [])
                       (ns-step later (C.CScope.cimps csc) e refl
                          (bare-ne (C.CScope.cimps csc) (map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc)) fr) ns)
                       I ia uf′)
        callEq : MB.callSD fmt σ x ty ≡ subst T (cohᴰ ty) (abiT ty M)
        callEq = trans (callSD-later later (e ∷ pre) (C.cpolys csc) I uf′ x ty (ns-head later (C.CScope.cimps csc) ns))
                       (cong (subst T (cohᴰ ty)) (abi ty x pre irFun))
        new : RelGM Once.Type.pure ty (CMB.refSem fmt S′ δ′ {d = zero} {U = ty} (TR.mono-inst {S = S′} {d = zero} {T′ = ty} refl)) (MB.callSD fmt σ x ty)
        new = subst (λ m → RelGM Once.Type.pure ty m (MB.callSD fmt σ x ty)) entry≡
                    (subst (RelGM Once.Type.pure ty (GM.⟦_⟧ S Dc fmt δ tt)) (sym callEq) relM)

------------------------------------------------------------------------
-- A telescope entry: typed once at its rigid schema; each reference to it is
-- the resolver's splice of its body at the instance (6e).
------------------------------------------------------------------------

-- Plan 0.104 E: the body at a kinded instance is the surface substitution
-- instance of its rigid derivation (`ElabInst.inst-at`, proved), and it means
-- the entry's abstraction instantiated there (`ElabInst.poly-instance-sem`).
inv-poly : ∀ {s} {S : Sig s} {csc tl is ts pre} (sg : SigCF S) {pfi : C.PolyFunInfo} {Ψ : Ctx.Usage 0}
             (D : ctxOf (AS.scopeOf csc) ⊢ᶜ pfunBody pfi ∶ rigidOf (pfunType pfi) ⨾ Ψ)
         → Inv {S = S} csc tl is ts pre → All (pfunName pfi ≢_) (scopeNames csc)
         → Inv (C.addEntry csc pfi)
               (def tl (schemaOf (pfunType pfi))
                       (A.absTm S (kindsOf (pfunType pfi)) (proj₁ (polyElab {S = S} {sc = AS.scopeOf csc} {pfi = pfi} {Ψ = Ψ} is ts D)))
                       (polyBody {S = S} {sc = AS.scopeOf csc} {pfi = pfi} {Ψ = Ψ} is ts sg D))
               (wkI is) (t-def zero refl (wkT ts)) pre
inv-poly {S = S} {csc} {tl} {is} {ts} {pre} sg {pfi} {Ctx.Usage.[]} D inv fr = record
  { valid = valid-wk {sc = schemaOf scT} {tl = tl} {body = bodyT} {D = bodyD} is (Inv.valid inv)
  ; irf   = Inv.irf inv
  ; iself = declImps-head (pfi , C.CScope.cimps csc) (C.CScope.ctele csc) (y ≟str y)
            ∷ iself-step (pfi , C.CScope.cimps csc) (C.CScope.ctele csc) (C.CScope.ctele csc) frT (Inv.iself inv)
  ; rel   = rel′
  }
  where
    y     = pfunName pfi
    scT   = pfunType pfi
    bodyT = A.absTm S (kindsOf scT) (proj₁ (polyElab {S = S} {sc = AS.scopeOf csc} {pfi = pfi} {Ψ = Ctx.Usage.[]} is ts D))
    bodyD = polyBody {S = S} {sc = AS.scopeOf csc} {pfi = pfi} {Ψ = Ctx.Usage.[]} is ts sg D
    S′    = S Once.Spec.Core.PolyTy.▷ schemaOf scT
    δ     = teleSem fmt φ tl
    δ′    = teleSem fmt φ (def tl (schemaOf scT) bodyT bodyD)
    ctx   = ctxOf (AS.scopeOf csc)
    ρ     = CE.envOf fmt S δ is ts
    V     = viewOf {S = S} is ts
    Dc    = proj₂ (ElabM.elabᶜ S V D)
    frT   = ++⁻ʳ (map proj₁ (C.CScope.cimps csc)) fr

    rel′ : ∀ (later : List IRFun) → NoShadow later (C.CScope.cimps csc)
         → ∀ (I : String → Imports) → IAgree I ((pfi , C.CScope.cimps csc) ∷ C.CScope.ctele csc) → ∀ (uf : Imports)
         → MB.MRel fmt (σW (later ++ pre) (C.cpolys (C.addEntry csc pfi)) I uf) (ctxOf (AS.scopeOf (C.addEntry csc pfi)))
                   (CE.envOf fmt S′ δ′ (wkI is) (t-def zero refl (wkT ts)))
    rel′ later ns I (iy ∷ ia) uf =
      ( head
      , envrel-transport σo σ (C.cpolys csc) (ra (C.CScope.ctele csc) frT)
          (subst (λ dm → MB.EnvRel fmt σo (C.cpolys csc) dm)
                 (sym (defEnv-wk {sc = schemaOf scT} {tl = tl} {body = bodyT} {D = bodyD} ts)) (proj₁ old)) )
      , subst (λ im → MB.ImpRel fmt σ (C.CScope.cimps csc) im)
              (sym (impEnv-wk {sc = schemaOf scT} {tl = tl} {body = bodyT} {D = bodyD} is))
              (imprel-transport σo σ (C.CScope.cimps csc)
                 (calls-same tbl (C.cpolys csc) (C.cpolys (C.addEntry csc pfi)) I I uf uf (C.CScope.cimps csc)) (proj₁ (proj₂ old)))
      , refl
      where
        tbl = later ++ pre
        σo  = σW tbl (C.cpolys csc) I uf
        σ   = σW tbl (C.cpolys (C.addEntry csc pfi)) I uf
        old : MB.MRel fmt σo ctx ρ
        old = Inv.rel inv later ns I ia uf

        -- the telescope's earlier entries are not the new one
        ra : ∀ (qs : List (C.PolyFunInfo × C.FunCtx)) → All (y ≢_) (map (λ q → pfunName (proj₁ q)) qs)
           → RefsAgree σo σ (C.buildPolyCtx (map proj₁ qs))
        ra []       []       = tt
        ra (q ∷ qs) (h ∷ hs) =
          (λ A → sym (refs-skip I uf (tableEnv fmt φ tbl) y {pfunType pfi} {pfunBody pfi} (C.cpolys csc) (pfunName (proj₁ q)) A h))
          , ra qs hs

        -- the new entry: its splice at an instance is its core instance (6e)
        head : ∀ (U : Type) (ki : KindedInstance scT U)
             → RelGM Once.Type.pure U (CMB.refSem fmt S′ δ′ {d = zero} {U = U} (TR.poly-inst {S = S′} {d = zero} {sc = scT} refl ki))
                      (SD.refs σ y U)
        head U ki =
          subst (λ m → RelGM Once.Type.pure U m (SD.refs σ y U))
                (trans (CMB.bridge-c fmt S {δ = δ} V (CE.agree fmt S δ is ts (Inv.valid inv)) D-U tt)
                       (EI.poly-instance-sem S (viewOf {S = S} is ts) sg fmt δ scT
                         (λ ki′ → EI.viewOf-natural S (kindsOf scT) _ _ is ts) (Inv.irf inv) D ki))
                (subst (RelGM Once.Type.pure U (MeaningM.⟦_⟧ᶜ D-U fmt ρ tt)) (sym eqSD)
                       (MB.bridge-c fmt σo D-U {dγ₁ = tt} {dγ₂ = tt} (MB.mk↾ tt) old))
          where
            D-U = EI.inst-at S scT (Inv.irf inv) D ki
            ccU = Once.TypeCheck.Completeness.check-complete D-U
            ce  = proj₂ (proj₂ (proj₂ ccU))
            cr  = Once.TypeCheck.Elaborate.checkElabV (Once.TypeCheck.Classify.ctxWithImportsAndPolys (C.CScope.cimps csc) (C.cpolys csc)) (pfunBody pfi) U
            D′  = sound-of cr ce
            eqSD : SD.refs σ y U ≡ SD.⟦ realize D-U ⟧ˢ fmt σo tt
            eqSD =
              trans (refs-head I uf (tableEnv fmt φ tbl) y {pfunType pfi} {pfunBody pfi} (C.cpolys csc) U)
                (trans (cong (λ X → SD.⟦ spliceClosed I uf (C.cpolys csc) y
                                          (Once.TypeCheck.Elaborate.checkElabV (Once.TypeCheck.Classify.ctxWithImportsAndPolys X (C.cpolys csc))
                                             (pfunBody pfi) U) ⟧ˢ fmt (RF.σ₀ fmt (tableEnv fmt φ tbl)) tt) iy)
                  (trans (cong (λ e′ → SD.⟦ e′ ⟧ˢ fmt (RF.σ₀ fmt (tableEnv fmt φ tbl)) tt) (splice-form I uf (C.cpolys csc) y cr ce))
                    (trans ((RF.resolveExpr-faithful fmt (tableEnv fmt φ tbl) (C.cpolys csc) I uf 0 (realize D′) tt))
                           (realize-invariant D′ D-U σo tt))))

------------------------------------------------------------------------
-- The entry point among the remaining names
------------------------------------------------------------------------

-- A `main` later in the telescope has a name there.
mainIn-name : ∀ {sc es} (mt : ModTele sc es) → MainIn mt → Any ("main" ≡_) (map entryName es)
mainIn-name []                          ()
mainIn-name (ffi _ _ _ _ _ rest)        mi          = there (mainIn-name rest mi)
mainIn-name (poly _ rest)               mi          = there (mainIn-name rest mi)
mainIn-name (mono _ _ _ _ rest)         (inj₁ (p , _)) = here (sym p)
mainIn-name (mono _ _ _ _ rest)         (inj₂ mi)   = there (mainIn-name rest mi)

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

names-imps : ∀ {y : String} (imps : C.FunCtx) (rest : List String) → All (y ≢_) (map proj₁ imps ++ rest)
           → All (λ p → y ≢ proj₁ p) imps
names-imps []       rest hs       = []
names-imps (p ∷ ps) rest (h ∷ hs) = h ∷ names-imps ps rest hs

-- Every entry the rest of the walk adds to the table has a name new to the scope.
later-ns : ∀ {sc es} (b : FB.FunBundle sc es) (imps : C.FunCtx)
         → All (λ y → All (λ p → y ≢ proj₁ p) imps) (map entryName es)
         → ∀ (xs : List IRFun) → All (NS imps) xs → All (NS imps) (tableOf-go (FB.bundle→compiled b) xs)
later-ns FB.bnil imps _ xs a = a
later-ns (FB.bffi {fi = fi} {ty = ty} {c = c} _ _ _ _ _ rest) imps (h ∷ hs) xs a =
  later-ns rest imps hs (irFunOf (FB.primCF fi ty c) ∷ xs) (ns-of imps h (irFunOf (FB.primCF fi ty c)) refl ∷ a)
later-ns (FB.bcons {fi = fi} {ty = ty} {irFun = irFun} _ _ _ _ _ rest) imps (h ∷ hs) xs a =
  later-ns rest imps hs (irFunOf (C.mkCompiledFun (bare (funName fi)) ty irFun (funIsPrimitive fi)) ∷ xs)
           (ns-of imps h (irFunOf (C.mkCompiledFun (bare (funName fi)) ty irFun (funIsPrimitive fi))) refl ∷ a)
later-ns (FB.bpoly _ rest) imps (_ ∷ hs) xs a = later-ns rest imps hs xs a

-- …so, after an entry, the table does not shadow the scope before it.
later-noshadow : ∀ {csc sc′ e es} (b : FB.FunBundle sc′ es) → Fresh csc (e ∷ es)
               → NoShadow (tableOf-go (FB.bundle→compiled b) []) (C.CScope.cimps csc)
later-noshadow {csc} b (_ , (_ ∷ hs)) =
  later-ns b (C.CScope.cimps csc)
    (All.map (names-imps (C.CScope.cimps csc) (map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc))) hs) [] []

