-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.TeleWalk — plan 0.103 6b, leg C.6: THE TELESCOPE WALK.
--
-- `realize-core` is proved by one walk over the module's entries, in lockstep
-- over three views of it:
--   * the typed telescope `mt` (`ModTele`), which `toProgram` turns into the
--     core program and `mainRealized-go` searches for `main`;
--   * the compile bundle `b` (`FunBundle`), which carries each entry's compiled
--     IR and so the function table, and `main`'s compile scope;
--   * the core telescope built so far (`tl`, with its signature data).
--
-- The invariant (`Inv`) at each position is leg A's environment relation
-- between the scope's surface environment, built from the core's (`CoreEnv`),
-- and the compiled program's environment (`σW`: calls of the table, splices
-- of the resolver), at EVERY later table that does not shadow the scope's
-- names and every declaration-import map that agrees on the scope's entries.
-- At `main`, legs A (MeaningBridge), B (CoreMeaningBridge) and F (CoreAbsSem)
-- turn it into the equation of the two runs.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.TeleWalk (fmt : TargetNum) where

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
open import Once.IRTy using (⌊_⌋)
import Once.Surface.Context as Ctx
open import Once.TypeCheck.Classify using (Imports)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Type.Rigid using (rigidOf)
open import Once.Denotation.Realize using (realize)
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.Program using (IRFun; fname)
open import Once.Spec.Module using (ModTele; []; ffi; mono; poly; MainIn; EffUU; ctxOf)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Core.Telescope using (Tele; def; teleSem; runProgram; noKinds; noVars)
open import Once.Spec.Core.Schema using (schemaOf; kindsOf; kinded-instance)
open import Once.Spec.Core.Translate using (ImpSig; TeleSig; i-ffi; i-def; t-def; wkI; wkT; SigCF; toProgram; viewOf;
  monoHere; monoElab; monoBody; monoSchema; monoSg; polyElab; polyBody; polySg)
import Once.Spec.Core.Abstract as A
import Once.Spec.Core.Translate as TR
open import Once.Adequacy.SourceTrace using (irFunOf; tableOf-go; isMain; tbl-keep)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.FunBundle as FB
import Once.Adequacy.MainIRForm as MIF
import Once.Adequacy.ModuleComplete as MC
import Once.Adequacy.MainExtract fmt as ME
import Once.Adequacy.MeaningBridge as MB
import Once.Adequacy.CoreEnv as CE
import Once.Adequacy.CoreMeaningBridge as CMB
import Once.Adequacy.CoreAbsSem as CAS
import Once.Spec.Elaboration as ElabM
import Once.Spec.Core.Meaning as GM
import Once.Spec.Core.PolyTyping as PT
import Once.Denotation.Meaning as MeaningM
open import Once.Adequacy.GradedRelation fmt using (RelGT; RelGM; RelGT-bind)
open import Once.Denotation.TraceMonad using (T; projTrace)
open import Once.Adequacy.TeleEnvLemmas fmt using (σW; callSD-later; refs-skip; refs-head; spliceClosed; RefsAgree; envrel-transport;
  imprel-transport; calls-same)
import Once.Adequacy.TeleEntry fmt as TE

import Once.Adequacy.ElabInst as EI
open import Once.Type.Rigid using (RigidFree)
import Once.Adequacy.SourceFaithful as SF
import Once.Adequacy.FaithfulLemmas as FLm
import Once.Adequacy.ResolveFaithful as RF
import Once.Adequacy.RealizeBridge as RB
open import Once.Adequacy.RealizeInvariant fmt using (realize-invariant)
import Once.TypeCheck.Completeness
import Once.TypeCheck.Soundness
import Once.TypeCheck.Elaborate
import Once.Spec.Core.Typing as GTM
import Once.Spec.Core.Syntax
open import Once.Surface.Elaborate using (elaborateFull)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
open import Once.Parser using (validIdentB)
import Once.Parser
open import Once.Denotation.DenotTrace using (evalᴰ; cohᴰ)
open import Once.Denotation.Program using (tableEnv)
open import Once.Adequacy.TableCall fmt using (abiT; abi)
import Data.Maybe
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
import Relation.Nullary
open import Once.Functor.Decide using (isConcrete?)
open import Once.Denotation.GradedOps using (sigOpRefᵛ)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ)
open import Once.Functor.Translate using (IsConcrete-irrelevant)
open import Data.List.Properties using (++-assoc)

------------------------------------------------------------------------
-- Position predicates
------------------------------------------------------------------------

-- Later table entries do not shadow a name in scope.
NoShadow : List IRFun → C.FunCtx → Set
NoShadow later imps = All (λ e → All (λ p → fname e ≢ bare (proj₁ p)) imps) later

-- A declaration-import map that agrees with the scope's telescope entries.
IAgree : (String → Imports) → List (C.PolyFunInfo × C.FunCtx) → Set
IAgree I tele = All (λ q → I (pfunName (proj₁ q)) ≡ proj₂ q) tele

-- The scope's imports are rigid-free.
ImportsRF : Imports → Set
ImportsRF imps = ∀ {x T} → Once.TypeCheck.Classify.lookupImport imps x ≡ just T → RigidFree T

irf-cons : ∀ {imps : Imports} {y : String} {ty : Type} → RigidFree ty → ImportsRF imps → ImportsRF ((y , ty) ∷ imps)
irf-cons {y = y} g old {x} lk with y ≟str x
... | yes _ = subst RigidFree (just-injective lk) g
... | no _  = old lk

-- THE INVARIANT at a position of the walk.
record Inv {s} {S : Sig s} (csc : C.CScope) (tl : Tele S) (is : ImpSig S (C.CScope.cimps csc))
           (ts : TeleSig S (C.telePolys (C.CScope.ctele csc))) (pre : List IRFun) : Set where
  field
    valid : CE.DefsValid fmt S (teleSem fmt tl) is
    -- D243/D252: the scope's imports are ground (FFI and monomorphic types are),
    -- so instantiating a polymorphic body fixes them.
    irf   : ImportsRF (C.CScope.cimps csc)
    iself : IAgree (C.declImps (C.CScope.ctele csc)) (C.CScope.ctele csc)
    rel   : ∀ (later : List IRFun) → NoShadow later (C.CScope.cimps csc)
          → ∀ (I : String → Imports) → IAgree I (C.CScope.ctele csc) → ∀ (uf : Imports)
          → MB.MRel fmt (σW (later ++ pre) (C.cpolys csc) I uf) (ctxOf (AS.scopeOf csc))
                    (CE.envOf fmt S (teleSem fmt tl) is ts)

-- The remaining entries' names: distinct, and new to the scope.
entryName : C.Entry → String
entryName = Once.Parser.entryNameOf

scopeNames : C.CScope → List String
scopeNames csc = map proj₁ (C.CScope.cimps csc) ++ map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc)

Fresh : C.CScope → List C.Entry → Set
Fresh csc es = AllPairs _≢_ (map entryName es) × All (λ x → All (x ≢_) (scopeNames csc)) (map entryName es)

-- The compiled program's environment at `main`: its whole table, and `main`'s
-- compile scope (what `MainRealizeAgrees.σTp` reads).
σMain : ∀ {csc es} (b : FB.FunBundle csc es) → FB.BMainExists b → List IRFun → SD.DefsSem
σMain b bme pre =
  σW (tableOf-go (FB.bundle→compiled b) pre)
     (C.cpolys (proj₁ (FB.bundle-main-node b bme)))
     (C.declImps (C.CScope.ctele (proj₁ (FB.bundle-main-node b bme))))
     (("main" , EffUU) ∷ C.CScope.cimps (proj₁ (FB.bundle-main-node b bme)))

------------------------------------------------------------------------
-- SCAFFOLD (plan 0.103 C): the steps, discharged next.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- `main`: legs A (SD ~ surface), B (surface = core of the elaboration) and F
-- (the core entry read back = the elaboration), at the run of `IO Unit`.
------------------------------------------------------------------------

main-step : ∀ {s} {S : Sig s} {csc tl is ts pre} (sg : SigCF S) {fi : C.FunInfo} {Ψ : Ctx.Usage 0}
              (D : ctxOf (AS.scopeOf csc) ⊢ᶜ funBody fi ∶ EffUU ⨾ Ψ)
          → Inv {S = S} csc tl is ts pre
          → (later : List IRFun) → NoShadow later (C.CScope.cimps csc)
          → ∀ n → ME.runMainˢ (σW (later ++ pre) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                                   (("main" , EffUU) ∷ C.CScope.cimps csc)) (realize D) n
                ≡ runProgram fmt (monoHere {S = S} {sc = AS.scopeOf csc} {fi = fi} {Ψ = Ψ} tl is ts sg D refl) n
main-step {S = S} {csc} {tl} {is} {ts} {pre} sg {fi} {Ctx.Usage.[]} D inv later ns n =
  sym (proj₁ (RelGT-bind {EffUU} {Once.Type.Unit} relAF (λ rv → rv {tt} {tt} tt) n))
  where
    σ  = σW (later ++ pre) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) (("main" , EffUU) ∷ C.CScope.cimps csc)
    δ  = teleSem fmt tl
    V  = viewOf {S = S} is ts
    Dc = proj₂ (ElabM.elabᶜ S V D)
    relA : RelGM Once.Type.pure EffUU (MeaningM.⟦_⟧ᶜ D fmt (CE.envOf fmt S δ is ts) tt) (SD.⟦ realize D ⟧ˢ fmt σ tt)
    relA = MB.bridge-c fmt σ D {dγ₁ = tt} {dγ₂ = tt} (MB.mk↾ tt)
             (Inv.rel inv later ns (C.declImps (C.CScope.ctele csc)) (Inv.iself inv) (("main" , EffUU) ∷ C.CScope.cimps csc))
    eqB : MeaningM.⟦_⟧ᶜ D fmt (CE.envOf fmt S δ is ts) tt ≡ GM.⟦_⟧ S Dc fmt δ tt
    eqB = CMB.bridge-c fmt S {δ = δ} V (CE.agree fmt S δ is ts (Inv.valid inv)) D tt
    relAF : RelGM Once.Type.pure EffUU (GM.⟦_⟧ S (PT.instantiate S noVars _ (A.abs-⊢ S noKinds sg Dc)) fmt δ tt) (SD.⟦ realize D ⟧ˢ fmt σ tt)
    relAF = subst (λ m → RelGM Once.Type.pure EffUU m (SD.⟦ realize D ⟧ˢ fmt σ tt))
                  (trans eqB (CAS.rt-sem S noKinds noVars _ sg Dc fmt δ)) relA

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
    δ = teleSem fmt tl
    e = irFunOf (FB.primCF fi ty c)
    rel′ : ∀ (later : List IRFun) → NoShadow later ((x , ty) ∷ C.CScope.cimps csc)
         → ∀ (I : String → Imports) → IAgree I (C.CScope.ctele csc) → ∀ (uf : Imports)
         → MB.MRel fmt (σW (later ++ e ∷ pre) (C.cpolys csc) I uf) (ctxOf (AS.scopeOf (C.extendScope csc x ty)))
                   (CE.envOf fmt S δ (i-ffi k h g is) ts)
    rel′ later ns I ia uf = proj₁ old , (new , proj₂ old)
      where
        old : MB.MRel fmt (σW (later ++ e ∷ pre) (C.cpolys csc) I uf) (ctxOf (AS.scopeOf csc)) (CE.envOf fmt S δ is ts)
        old = subst (λ tbl → MB.MRel fmt (σW tbl (C.cpolys csc) I uf) (ctxOf (AS.scopeOf csc)) (CE.envOf fmt S δ is ts))
                    (++-assoc later (e ∷ []) pre)
                    (Inv.rel inv (later ++ e ∷ [])
                       (ns-step later (C.CScope.cimps csc) e refl
                          (bare-ne (C.CScope.cimps csc) (map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc)) fr) ns)
                       I ia uf)
        new : RelGM Once.Type.pure ty (sigOpRefᵛ fmt (bare x) k) (MB.callSD fmt (σW (later ++ e ∷ pre) (C.cpolys csc) I uf) x ty)
        new = subst (λ k′ → RelGM Once.Type.pure ty (sigOpRefᵛ fmt (bare x) k′) (MB.callSD fmt (σW (later ++ e ∷ pre) (C.cpolys csc) I uf) x ty))
                    (IsConcrete-irrelevant c k)
                    (subst (RelGM Once.Type.pure ty (sigOpRefᵛ fmt (bare x) c))
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

  -- A non-`main` definition compiles to its resolved body's elaboration.
  irFun-form : ∀ (ctx : C.FunCtx) (polys : Once.TypeCheck.Classify.PolyCtx) (impsOf : String → C.FunCtx)
                 (x : String) (ty : Type) (body : _) {irFun : IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋}
                 {se : _} {d f : ℕ}
             → C.compileFun C.Heap false ctx polys impsOf x ty body ≡ inj₂ irFun → x ≢ "main"
             → Once.TypeCheck.Elaborate.checkElab (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body ty
                 ≡ Once.TypeCheck.Elaborate.success Ctx.Usage.[] se d f
             → irFun ≡ elaborateFull C.Heap (resolveExpr polys impsOf ((x , ty) ∷ ctx) 0 se)
  irFun-form ctx polys impsOf x ty body cf ne ce =
    inj₂-injective (trans (sym cf)
      (trans (cong (C.compileFun-aux C.Heap false ctx polys impsOf x ty body) (does-no (x ≟str "main") ne))
             (cong (C.compileFunBody-aux C.Heap false ctx polys impsOf x ty refl) ce)))


impEnv-wk : ∀ {s} {S : Sig s} {sc} {tl : Tele S} {body : _} {D : _} {imps} (is : ImpSig S imps)
          → CE.impEnv fmt (S Once.Spec.Core.PolyTy.▷ sc) (teleSem fmt (def tl sc body D)) (wkI is) ≡ CE.impEnv fmt S (teleSem fmt tl) is
impEnv-wk TR.[]              = refl
impEnv-wk {sc = sc} {tl} {body} {D} (TR.i-ffi c h g is) = cong₂ _,_ refl (impEnv-wk {sc = sc} {tl = tl} {body = body} {D = D} is)
impEnv-wk {sc = sc} {tl} {body} {D} (TR.i-def d e is) = cong₂ _,_ refl (impEnv-wk {sc = sc} {tl = tl} {body = body} {D = D} is)

defEnv-wk : ∀ {s} {S : Sig s} {sc} {tl : Tele S} {body : _} {D : _} {ps} (ts : TeleSig S ps)
          → CE.defEnv fmt (S Once.Spec.Core.PolyTy.▷ sc) (teleSem fmt (def tl sc body D)) (wkT ts) ≡ CE.defEnv fmt S (teleSem fmt tl) ts
defEnv-wk TR.[]              = refl
defEnv-wk {sc = sc} {tl} {body} {D} (TR.t-def d e ts) = cong₂ _,_ refl (defEnv-wk {sc = sc} {tl = tl} {body = body} {D = D} ts)

valid-wk : ∀ {s} {S : Sig s} {sc} {tl : Tele S} {body : _} {D : _} {imps} (is : ImpSig S imps)
         → CE.DefsValid fmt S (teleSem fmt tl) is → CE.DefsValid fmt (S Once.Spec.Core.PolyTy.▷ sc) (teleSem fmt (def tl sc body D)) (wkI is)
valid-wk TR.[]             v        = tt
valid-wk {sc = sc} {tl} {body} {D} (TR.i-ffi c h g is) v        = valid-wk {sc = sc} {tl = tl} {body = body} {D = D} is v
valid-wk {sc = sc} {tl} {body} {D} (TR.i-def d e is) (h , v)  = h , valid-wk {sc = sc} {tl = tl} {body = body} {D = D} is v

inv-mono : ∀ {s} {S : Sig s} {csc tl is ts pre} (sg : SigCF S) {fi : C.FunInfo} {ty : Type} {g : RigidFree ty}
             {Ψ : Ctx.Usage 0} (D : ctxOf (AS.scopeOf csc) ⊢ᶜ funBody fi ∶ ty ⨾ Ψ)
             {irFun : IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋}
         → C.compileFun C.Heap false (C.CScope.cimps csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
             (funName fi) ty (funBody fi) ≡ Data.Sum.inj₂ irFun
         → funName fi ≢ "main" → validIdentB (funName fi) ≡ true
         → Inv {S = S} csc tl is ts pre → All (funName fi ≢_) (scopeNames csc)
         → Inv (C.extendScope csc (funName fi) ty)
               (def tl (monoSchema ty) (A.absTm S noKinds (proj₁ (monoElab {S = S} {sc = AS.scopeOf csc} {fi = fi} is ts D)))
                       (monoBody {S = S} {sc = AS.scopeOf csc} {fi = fi} is ts sg g D))
               (i-def zero refl (wkI is)) (wkT ts)
               (irFunOf (C.mkCompiledFun (bare (funName fi)) ty irFun false) ∷ pre)
inv-mono {S = S} {csc} {tl} {is} {ts} {pre} sg {fi} {ty} {g} {Ctx.Usage.[]} D {irFun} cf ne vx inv fr = record
  { valid = vx , valid-wk {sc = monoSchema ty} {tl = tl} {body = bodyT} {D = bodyD} is (Inv.valid inv)
  ; irf   = irf-cons {imps = C.CScope.cimps csc} {y = funName fi} {ty = ty} g (Inv.irf inv)
  ; iself = Inv.iself inv
  ; rel   = rel′
  }
  where
    x    = funName fi
    δ    = teleSem fmt tl
    S′   = S Once.Spec.Core.PolyTy.▷ monoSchema ty
    bodyT = A.absTm S noKinds (proj₁ (monoElab {S = S} {sc = AS.scopeOf csc} {fi = fi} is ts D))
    bodyD = monoBody {S = S} {sc = AS.scopeOf csc} {fi = fi} is ts sg g D
    tl′  = def tl (monoSchema ty) bodyT bodyD
    δ′   = teleSem fmt tl′
    e    = irFunOf (C.mkCompiledFun (bare x) ty irFun false)
    ctx  = ctxOf (AS.scopeOf csc)
    ρ    = CE.envOf fmt S δ is ts
    V    = viewOf {S = S} is ts
    Dc   = proj₂ (ElabM.elabᶜ S V D)
    uf   = (x , ty) ∷ C.CScope.cimps csc
    σx   = σW pre (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf
    ccE  = Once.TypeCheck.Completeness.check-complete D
    eE   = proj₁ ccE
    ce   = proj₂ (proj₂ (proj₂ ccE))
    M    = evalᴰ fmt (tableEnv fmt pre) irFun tt

    -- the compiled body means the elaboration's surface meaning (the compile chain)
    chain : subst T (cohᴰ ty) M ≡ SD.⟦ realize D ⟧ˢ fmt σx tt
    chain =
      trans (cong (λ ir → subst T (cohᴰ ty) (evalᴰ fmt (tableEnv fmt pre) ir tt))
                  (irFun-form (C.CScope.cimps csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty (funBody fi) cf ne ce))
        (trans (FLm.T-ext-at fmt (tableEnv fmt pre) (SF.faithful∅ fmt (tableEnv fmt pre) (resolveExpr (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 eE)))
          (trans (FLm.T-ext-at fmt (tableEnv fmt pre)
                   (RF.resolveExpr-faithful fmt (tableEnv fmt pre) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 eE tt))
            (trans (RB.realize-agrees fmt σx ctx (funBody fi) ty ce tt)
                   (realize-invariant (Once.TypeCheck.Soundness.check-sound ctx (funBody fi) ty ce) D σx tt))))

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

    rel′ : ∀ (later : List IRFun) → NoShadow later ((x , ty) ∷ C.CScope.cimps csc)
         → ∀ (I : String → Imports) → IAgree I (C.CScope.ctele csc) → ∀ (uf′ : Imports)
         → MB.MRel fmt (σW (later ++ e ∷ pre) (C.cpolys csc) I uf′) (ctxOf (AS.scopeOf (C.extendScope csc x ty)))
                   (CE.envOf fmt S′ δ′ (i-def zero refl (wkI is)) (wkT ts))
    rel′ later ns I ia uf′ =
      subst (λ dm → MB.EnvRel fmt σ (C.cpolys csc) dm) (sym (defEnv-wk {sc = monoSchema ty} {tl = tl} {body = bodyT} {D = bodyD} ts)) (proj₁ old)
      , (new , subst (λ im → MB.ImpRel fmt σ (C.CScope.cimps csc) im)
                     (sym (impEnv-wk {sc = monoSchema ty} {tl = tl} {body = bodyT} {D = bodyD} is)) (proj₂ old))
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
private
  declImps-head : ∀ (e : C.PolyFunInfo × C.FunCtx) (es : List (C.PolyFunInfo × C.FunCtx))
                    (d : Dec (pfunName (proj₁ e) ≡ pfunName (proj₁ e)))
                → C.declImps-aux e es (pfunName (proj₁ e)) d ≡ proj₂ e
  declImps-head e es (yes _) = refl
  declImps-head e es (no ¬p) = ⊥-elim (¬p refl)

  declImps-skip : ∀ (e : C.PolyFunInfo × C.FunCtx) (es : List (C.PolyFunInfo × C.FunCtx)) (x : String)
                    (d : Dec (pfunName (proj₁ e) ≡ x)) → pfunName (proj₁ e) ≢ x
                → C.declImps-aux e es x d ≡ C.declImps es x
  declImps-skip e es x (yes p) ne = ⊥-elim (ne p)
  declImps-skip e es x (no _)  ne = refl

  iself-step : ∀ (e : C.PolyFunInfo × C.FunCtx) (tele : List (C.PolyFunInfo × C.FunCtx)) (qs : List (C.PolyFunInfo × C.FunCtx))
             → All (pfunName (proj₁ e) ≢_) (map (λ q → pfunName (proj₁ q)) qs)
             → IAgree (C.declImps tele) qs → IAgree (C.declImps (e ∷ tele)) qs
  iself-step e tele []       []       []       = []
  iself-step e tele (q ∷ qs) (h ∷ hs) (a ∷ as) =
    trans (declImps-skip e tele (pfunName (proj₁ q)) (pfunName (proj₁ e) ≟str pfunName (proj₁ q)) h) a ∷ iself-step e tele qs hs as

  ++⁻ʳ : ∀ {x : String} (as : List String) {bs : List String} → All (x ≢_) (as ++ bs) → All (x ≢_) bs
  ++⁻ʳ []       a        = a
  ++⁻ʳ (_ ∷ as) (_ ∷ a) = ++⁻ʳ as a

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
    δ     = teleSem fmt tl
    δ′    = teleSem fmt (def tl (schemaOf scT) bodyT bodyD)
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
                 (calls-same tbl (C.cpolys csc) (C.cpolys (C.addEntry csc pfi)) I I uf uf (C.CScope.cimps csc)) (proj₂ old))
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
          (λ A → sym (refs-skip I uf (tableEnv fmt tbl) y {pfunType pfi} {pfunBody pfi} (C.cpolys csc) (pfunName (proj₁ q)) A h))
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
            eE  = proj₁ ccU
            ce  = proj₂ (proj₂ (proj₂ ccU))
            eqSD : SD.refs σ y U ≡ SD.⟦ realize D-U ⟧ˢ fmt σo tt
            eqSD =
              trans (refs-head I uf (tableEnv fmt tbl) y {pfunType pfi} {pfunBody pfi} (C.cpolys csc) U)
                (trans (cong (λ X → SD.⟦ spliceClosed I uf (C.cpolys csc) y
                                          (Once.TypeCheck.Elaborate.checkElab (Once.TypeCheck.Classify.ctxWithImportsAndPolys X (C.cpolys csc))
                                             (pfunBody pfi) U) ⟧ˢ fmt (RF.σ₀ fmt (tableEnv fmt tbl)) tt) iy)
                  (trans (cong (λ r → SD.⟦ spliceClosed I uf (C.cpolys csc) y r ⟧ˢ fmt (RF.σ₀ fmt (tableEnv fmt tbl)) tt) ce)
                    (trans (FLm.T-ext-at fmt (tableEnv fmt tbl)
                             (RF.resolveExpr-faithful fmt (tableEnv fmt tbl) (C.cpolys csc) I uf 0 eE tt))
                      (trans (RB.realize-agrees fmt σo ctx (pfunBody pfi) U ce tt)
                             (realize-invariant (Once.TypeCheck.Soundness.check-sound ctx (pfunBody pfi) U ce) D-U σo tt)))))

------------------------------------------------------------------------
-- Freshness along the walk
------------------------------------------------------------------------

private
  insert-ne : ∀ (as bs : List String) {y x : String} → y ≢ x → All (y ≢_) (as ++ bs) → All (y ≢_) (as ++ x ∷ bs)
  insert-ne []       bs ne hs       = ne ∷ hs
  insert-ne (a ∷ as) bs ne (h ∷ hs) = h ∷ insert-ne as bs ne hs

  insert-all : ∀ (as bs : List String) {x : String} (ys : List String) → All (x ≢_) ys
             → All (λ y → All (y ≢_) (as ++ bs)) ys → All (λ y → All (y ≢_) (as ++ x ∷ bs)) ys
  insert-all as bs []       []         []         = []
  insert-all as bs (y ∷ ys) (ne ∷ nes) (h ∷ hs) = insert-ne as bs (λ e → ne (sym e)) h ∷ insert-all as bs ys nes hs

fresh-head : ∀ {csc e es} → Fresh csc (e ∷ es) → All (entryName e ≢_) (scopeNames csc)
fresh-head (_ , (h ∷ _)) = h

fresh-fun : ∀ {csc fi ty es} → Fresh csc (C.e-fun fi ∷ es) → Fresh (C.extendScope csc (funName fi) ty) es
fresh-fun {csc} {es = es} ((hd ∷ tl) , (_ ∷ hs)) = tl , insert-all [] (scopeNames csc) (map entryName es) hd hs

fresh-poly : ∀ {csc pfi es} → Fresh csc (C.e-poly pfi ∷ es) → Fresh (C.addEntry csc pfi) es
fresh-poly {csc} {es = es} ((hd ∷ tl) , (_ ∷ hs)) =
  tl , insert-all (map proj₁ (C.CScope.cimps csc)) (map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc))
                  (map entryName es) hd hs

-- A `main` later in the telescope has a name there.
mainIn-name : ∀ {sc es} (mt : ModTele sc es) → MainIn mt → Any ("main" ≡_) (map entryName es)
mainIn-name []                          ()
mainIn-name (ffi _ _ _ _ _ rest)        mi          = there (mainIn-name rest mi)
mainIn-name (poly _ rest)               mi          = there (mainIn-name rest mi)
mainIn-name (mono _ _ _ _ rest)         (inj₁ (p , _)) = here (sym p)
mainIn-name (mono _ _ _ _ rest)         (inj₂ mi)   = there (mainIn-name rest mi)

private
  not-in : ∀ {x : String} {ys} → All (x ≢_) ys → Any (x ≡_) ys → ⊥
  not-in (h ∷ _)  (here e)  = h e
  not-in (_ ∷ hs) (there a) = not-in hs a

------------------------------------------------------------------------
-- The table after `main`: entries of the later names, which are new
------------------------------------------------------------------------

tableOf-go-++ : ∀ (cfs : List C.CompiledFun) (xs pre : List IRFun) → tableOf-go cfs (xs ++ pre) ≡ tableOf-go cfs xs ++ pre
tableOf-go-++ []         xs pre = refl
tableOf-go-++ (cf ∷ cfs) xs pre with isMain cf
... | true  = tableOf-go-++ cfs xs pre
... | false = tableOf-go-++ cfs (irFunOf cf ∷ xs) pre

-- A monomorphic entry's compiled function, as the compile walk emits it.
cfOf : (fi : C.FunInfo) (ty : Type) → IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋ → C.CompiledFun
cfOf fi ty irFun = C.mkCompiledFun (bare (funName fi)) (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
                                   (proj₂ (C.maybeWrapMain (funName fi) ty irFun)) (funIsPrimitive fi)

private
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
later-ns (FB.bcons {fi = fi} {ty = ty} {irFun = irFun} _ _ _ _ _ rest) imps (h ∷ hs) xs a
  with isMain (cfOf fi ty irFun)
... | true  = later-ns rest imps hs xs a
... | false = later-ns rest imps hs (irFunOf (cfOf fi ty irFun) ∷ xs) (ns-of imps h (irFunOf (cfOf fi ty irFun)) refl ∷ a)
later-ns (FB.bpoly _ rest) imps (_ ∷ hs) xs a = later-ns rest imps hs xs a

-- …so, after an entry, the table does not shadow the scope before it.
later-noshadow : ∀ {csc sc′ e es} (b : FB.FunBundle sc′ es) → Fresh csc (e ∷ es)
               → NoShadow (tableOf-go (FB.bundle→compiled b) []) (C.CScope.cimps csc)
later-noshadow {csc} b (_ , (_ ∷ hs)) =
  later-ns b (C.CScope.cimps csc)
    (All.map (names-imps (C.CScope.cimps csc) (map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc))) hs) [] []

------------------------------------------------------------------------
-- A non-`main` entry is compiled as itself, and kept in the table
------------------------------------------------------------------------

mwm-other : ∀ (x : String) (ty : Type) (ir : IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋) → x ≢ "main"
          → C.maybeWrapMain x ty ir ≡ (ty , ir)
mwm-other x ty ir ne with x ≟str "main" | ty ≟T EffUU
... | yes p | _        = ⊥-elim (ne p)
... | no _  | yes refl = refl
... | no _  | no _     = refl

isMain-other : ∀ (x : String) (ty : Type) (ir : IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋) → x ≢ "main"
             → isMain (C.mkCompiledFun (bare x) ty ir false) ≡ false
isMain-other x ty ir ne with bare x Once.CanonicalName.≟ᶜ bare "main"
... | yes p = ⊥-elim (ne (MIF.bare-injective p))
... | no _  = refl

cfOf-other : ∀ x ft bd (ty : Type) (ir : IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋) → x ≢ "main"
           → cfOf (C.mkFunInfo x ft bd false) ty ir ≡ C.mkCompiledFun (bare x) ty ir false
cfOf-other x ft bd ty ir ne =
  cong (λ w → C.mkCompiledFun (bare x) (proj₁ w) (proj₂ w) false) (mwm-other x ty ir ne)

table-other : ∀ x ft bd (ty : Type) (ir : IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋) (cfs : List C.CompiledFun) (pre : List IRFun)
            → x ≢ "main"
            → tableOf-go (cfOf (C.mkFunInfo x ft bd false) ty ir ∷ cfs) pre
              ≡ tableOf-go cfs (irFunOf (C.mkCompiledFun (bare x) ty ir false) ∷ pre)
table-other x ft bd ty ir cfs pre ne =
  trans (cong (λ cf → tableOf-go cfs (tbl-keep (isMain cf) cf pre)) (cfOf-other x ft bd ty ir ne))
        (cong (λ b → tableOf-go cfs (tbl-keep b (C.mkCompiledFun (bare x) ty ir false) pre)) (isMain-other x ty ir ne))

------------------------------------------------------------------------
-- `main`'s compile scope, and the table around it
------------------------------------------------------------------------

module _ {csc : C.CScope} {es : List C.Entry} {ft bd} where

  private
    fiM : String → C.FunInfo
    fiM x = C.mkFunInfo x ft bd false

  msc-next : ∀ {x : String} {ty : Type} {Ψ se d f irFun}
               {ce : _} {cf : _} (rest-b : FB.FunBundle (C.extendScope csc x ty) es) (w : FB.BMainExists rest-b)
               (nd : Dec (x ≡ "main")) (td : Dec (ty ≡ EffUU))
           → x ≢ "main"
           → proj₁ (FB.bmn-dispatch {sc = csc} {es = es} {ty = ty} (fiM x) {Ψ = Ψ} {se = se} {d = d} {f = f} {irFun = irFun}
                                     ce cf refl rest-b w nd td)
             ≡ proj₁ (FB.bundle-main-node rest-b w)
  msc-next rest-b w (yes p) td ne = ⊥-elim (ne p)
  msc-next rest-b w (no _)  td ne = refl

  msc-here : ∀ {Ψ se d f irFun} {rf} {g} {eg} {ce : _} {cf : _}
               (rest-b : FB.FunBundle (C.extendScope csc "main" EffUU) es) bme
           → proj₁ (FB.bundle-main-node (FB.bcons {sc = csc} {fi = fiM "main"} {es = es} {ty = EffUU} {Ψ = Ψ} {se = se} {d = d} {f = f}
                                          {irFun = irFun} refl rf {g} eg ce cf rest-b) bme)
             ≡ csc
  msc-here rest-b (inj₁ (refl , refl , refl)) with "main" ≟str "main" | EffUU ≟T EffUU
  ... | yes refl | yes refl = refl
  ... | yes _    | no ¬q    = ⊥-elim (¬q refl)
  ... | no ¬r    | _        = ⊥-elim (¬r refl)
  msc-here rest-b (inj₂ w) with "main" ≟str "main" | EffUU ≟T EffUU
  ... | yes refl | yes refl = refl
  ... | yes _    | no ¬q    = ⊥-elim (¬q refl)
  ... | no ¬r    | _        = ⊥-elim (¬r refl)

  table-here : ∀ (ir : IR ⌊ Once.Type.Unit ⌋ ⌊ EffUU ⌋) (cfs : List C.CompiledFun) (pre : List IRFun)
             → tableOf-go (cfOf (fiM "main") EffUU ir ∷ cfs) pre ≡ tableOf-go cfs pre
  table-here ir cfs pre with "main" ≟str "main" | EffUU ≟T EffUU | bare "main" Once.CanonicalName.≟ᶜ bare "main"
  ... | yes refl | yes refl | yes _ = refl
  ... | yes _    | yes _    | no ¬c = ⊥-elim (¬c refl)
  ... | yes _    | no ¬q    | _     = ⊥-elim (¬q refl)
  ... | no ¬r    | _        | _     = ⊥-elim (¬r refl)

------------------------------------------------------------------------
-- THE WALK
------------------------------------------------------------------------

private
  σ-at : ∀ {tbl tbl′ : List IRFun} {msc msc′ : C.CScope} → tbl ≡ tbl′ → msc ≡ msc′
       → σW tbl (C.cpolys msc) (C.declImps (C.CScope.ctele msc)) (("main" , EffUU) ∷ C.CScope.cimps msc)
         ≡ σW tbl′ (C.cpolys msc′) (C.declImps (C.CScope.ctele msc′)) (("main" , EffUU) ∷ C.CScope.cimps msc′)
  σ-at refl refl = refl

  run-at : ∀ {σ σ′ : SD.DefsSem} {Ψ : Ctx.Usage 0} (se : _) (n : ℕ) → σ ≡ σ′
         → ME.runMainˢ {Ψ} σ se n ≡ ME.runMainˢ σ′ se n
  run-at se n refl = refl

-- `main` here: the whole table past it does not shadow its scope.
here-main : ∀ {s} {S : Sig s} {csc es tl is ts pre} (sg : SigCF S) {fi : C.FunInfo} {Ψ : Ctx.Usage 0}
              (D : ctxOf (AS.scopeOf csc) ⊢ᶜ funBody fi ∶ EffUU ⨾ Ψ) (cfs : List C.CompiledFun)
              (tbl : List IRFun) → tbl ≡ tableOf-go cfs pre
          → (b : FB.FunBundle (C.extendScope csc (funName fi) EffUU) es) → cfs ≡ FB.bundle→compiled b
          → Inv {S = S} csc tl is ts pre → Fresh csc (C.e-fun fi ∷ es)
          → ∀ n → ME.runMainˢ (σW tbl (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                                   (("main" , EffUU) ∷ C.CScope.cimps csc)) (realize D) n
                ≡ runProgram fmt (monoHere {S = S} {sc = AS.scopeOf csc} {fi = fi} {Ψ = Ψ} tl is ts sg D refl) n
here-main {csc = csc} {es = es} {pre = pre} sg {fi} D cfs tbl refl b refl inv fr n =
  trans (run-at (realize D) n (σ-at {msc = csc} (tableOf-go-++ (FB.bundle→compiled b) [] pre) refl))
        (main-step sg {fi = fi} D inv (tableOf-go (FB.bundle→compiled b) []) (later-noshadow {csc = csc} {e = C.e-fun fi} {es = es} b fr) n)

mutual
  walk : ∀ {csc es} (mt : ModTele (AS.scopeOf csc) es) (b : FB.FunBundle csc es) (mi : MainIn mt) (bme : FB.BMainExists b)
           {s} {S : Sig s} (tl : Tele S) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
           (sg : SigCF S) (pre : List IRFun) → Inv csc tl is ts pre → Fresh csc es → All MonoValid es
       → ∀ n → ME.runMainˢ (σMain b bme pre) (proj₂ (MC.mainRealized-go mt mi)) n ≡ runProgram fmt (toProgram tl is ts sg mt mi) n
  walk [] FB.bnil () bme tl is ts sg pre inv fr vd n
  walk {csc} {C.e-fun fi ∷ es} (ffi {fi = fi} {ty = ty} ep et c h g rest) (FB.bffi {ty = ty′} {c = c′} ep′ et′ ec eh eg rest-b) mi bme tl is ts sg pre inv fr (_ ∷ vd) n
    with just-injective (trans (sym et) et′)
  ... | refl = walk rest rest-b mi bme tl (i-ffi c h g is) ts sg (irFunOf (FB.primCF fi ty c′) ∷ pre)
                 (inv-ffi {fi = fi} {ty = ty} {k = c} {c = c′} {h = h} {g = g} inv (fresh-head {csc = csc} {e = C.e-fun fi} {es = es} fr))
                 (fresh-fun {csc = csc} {fi = fi} {ty = ty} {es = es} fr) vd n
  walk (ffi {fi = C.mkFunInfo x ft bd prim} refl et c h g rest) (FB.bcons () rf eg ce cf rest-b) mi bme tl is ts sg pre inv fr vd n
  walk {csc} {C.e-poly pfi ∷ es} (poly {pfi = pfi} {Ψ = Ctx.Usage.[]} D rest) (FB.bpoly ce rest-b) mi bme tl is ts sg pre inv fr (_ ∷ vd) n =
    walk rest rest-b mi bme _ (wkI is) (t-def zero refl (wkT ts)) (polySg sg pfi) pre
         (inv-poly sg D inv (fresh-head {csc = csc} {e = C.e-poly pfi} {es = es} fr))
         (fresh-poly {csc = csc} {pfi = pfi} {es = es} fr) vd n
  walk (mono {fi = C.mkFunInfo x ft bd prim} {ty = ty} {Ψ = Ctx.Usage.[]} refl er g D rest)
       (FB.bcons {ty = ty′} {Ψ = Ctx.Usage.[]} {irFun = irFun} refl rf eg ce cf rest-b) mi bme tl is ts sg pre inv fr (v ∷ vd) n
    with inj₂-injective (trans (sym er) rf)
  ... | refl = walk-mono er g D rest rf eg ce cf rest-b mi bme tl is ts sg pre inv fr (v refl) vd n

  walk-mono : ∀ {csc es x ft bd ty} (er : C.resolveFunType (C.CScope.cimps csc) (C.cpolys csc) ft bd ≡ inj₂ ty)
                (g : RigidFree ty) (D : ctxOf (AS.scopeOf csc) ⊢ᶜ bd ∶ ty ⨾ Ctx.Usage.[])
                (rest : ModTele (AS.scopeOf (C.extendScope csc x ty)) es)
                (rf : C.resolveFunType (C.CScope.cimps csc) (C.cpolys csc) ft bd ≡ inj₂ ty) {g′ : RigidFree ty} eg
                {se d f} ce {irFun} cf (rest-b : FB.FunBundle (C.extendScope csc x ty) es)
                (mi : ((x ≡ "main") × (ty ≡ EffUU)) ⊎ MainIn rest)
                (bme : ((x ≡ "main") × (false ≡ false) × (ty ≡ EffUU)) ⊎ FB.BMainExists rest-b)
                {s} {S : Sig s} (tl : Tele S) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
                (sg : SigCF S) (pre : List IRFun) → Inv csc tl is ts pre → Fresh csc (C.e-fun (C.mkFunInfo x ft bd false) ∷ es)
            → validIdentB x ≡ true → All MonoValid es
            → ∀ n → ME.runMainˢ (σMain (FB.bcons {fi = C.mkFunInfo x ft bd false} {Ψ = Ctx.Usage.[]} {se = se} {d = d} {f = f}
                                          {irFun = irFun} refl rf {g′} eg ce cf rest-b) bme pre)
                                 (proj₂ (MC.mainRealized-go (mono {fi = C.mkFunInfo x ft bd false} {Ψ = Ctx.Usage.[]} refl er g D rest) mi)) n
                  ≡ runProgram fmt (toProgram tl is ts sg (mono {fi = C.mkFunInfo x ft bd false} {Ψ = Ctx.Usage.[]} refl er g D rest) mi) n
  walk-mono {csc} {es} {ft = ft} {bd} er g D rest rf {g′} eg {se} {d} {f} ce {irFun} cf rest-b (inj₁ (refl , refl)) bme tl is ts sg pre inv fr vx vd n =
    trans (run-at (realize D) n (σ-at (table-here {csc = csc} {es = es} {ft = ft} {bd = bd} irFun (FB.bundle→compiled rest-b) pre)
                                      (msc-here {csc = csc} {es = es} {ft = ft} {bd = bd} {se = se} {d = d} {f = f} {irFun = irFun}
                                                {rf = rf} {g = g′} {eg = eg} {ce = ce} {cf = cf} rest-b bme)))
          (here-main sg {fi = C.mkFunInfo "main" ft bd false} D (FB.bundle→compiled rest-b) _ refl rest-b refl inv fr n)
  walk-mono {csc} {es} {x} {ft} {bd} {ty} er g D rest rf eg ce cf rest-b (inj₂ mi′) bme tl is ts sg pre inv fr vx vd n =
    walk-mono-d er g D rest rf eg ce cf rest-b mi′ bme tl is ts sg pre inv fr vx vd (x ≟str "main") (ty ≟T EffUU) n

  walk-mono-d : ∀ {csc es x ft bd ty} (er : C.resolveFunType (C.CScope.cimps csc) (C.cpolys csc) ft bd ≡ inj₂ ty)
                (g : RigidFree ty) (D : ctxOf (AS.scopeOf csc) ⊢ᶜ bd ∶ ty ⨾ Ctx.Usage.[])
                (rest : ModTele (AS.scopeOf (C.extendScope csc x ty)) es)
                (rf : C.resolveFunType (C.CScope.cimps csc) (C.cpolys csc) ft bd ≡ inj₂ ty) {g′ : RigidFree ty} eg
                {se d f} ce {irFun} cf (rest-b : FB.FunBundle (C.extendScope csc x ty) es)
                (mi′ : MainIn rest)
                (bme : ((x ≡ "main") × (false ≡ false) × (ty ≡ EffUU)) ⊎ FB.BMainExists rest-b)
                {s} {S : Sig s} (tl : Tele S) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
                (sg : SigCF S) (pre : List IRFun) → Inv csc tl is ts pre → Fresh csc (C.e-fun (C.mkFunInfo x ft bd false) ∷ es)
              → validIdentB x ≡ true → All MonoValid es
              → (nd : Dec (x ≡ "main")) (td : Dec (ty ≡ EffUU))
              → ∀ n → ME.runMainˢ (σMain (FB.bcons {fi = C.mkFunInfo x ft bd false} {Ψ = Ctx.Usage.[]} {se = se} {d = d} {f = f}
                                            {irFun = irFun} refl rf {g′} eg ce cf rest-b) bme pre)
                                   (proj₂ (MC.mrg-dispatch {sc = AS.scopeOf csc} {fi = C.mkFunInfo x ft bd false} {es = es} D {rest} mi′ nd td)) n
                    ≡ runProgram fmt (Once.Spec.Core.Translate.monoDispatch {S = S} {sc = AS.scopeOf csc} {fi = C.mkFunInfo x ft bd false}
                                        {ty = ty} {Ψ = Ctx.Usage.[]} tl is ts sg g D rest mi′ nd td) n
  -- `main`, found by the bundle's own witness
  walk-mono-d {csc} {es} {ft = ft} {bd} er g D rest rf {g′} eg {se} {d} {f} ce {irFun} cf rest-b mi′ (inj₁ (refl , refl , refl)) tl is ts sg pre inv fr vx vd (yes refl) (yes refl) n =
    trans (run-at (realize D) n (σ-at (table-here {csc = csc} {es = es} {ft = ft} {bd = bd} irFun (FB.bundle→compiled rest-b) pre)
                                      (msc-here {csc = csc} {es = es} {ft = ft} {bd = bd} {se = se} {d = d} {f = f} {irFun = irFun}
                                                {rf = rf} {g = g′} {eg = eg} {ce = ce} {cf = cf} rest-b (inj₁ (refl , refl , refl)))))
          (here-main sg {fi = C.mkFunInfo "main" ft bd false} D (FB.bundle→compiled rest-b) _ refl rest-b refl inv fr n)
  walk-mono-d er g D rest rf eg ce cf rest-b mi′ (inj₁ (p , _ , e)) tl is ts sg pre inv fr vx vd (yes _) (no ¬t) n = ⊥-elim (¬t e)
  walk-mono-d er g D rest rf eg ce cf rest-b mi′ (inj₁ (p , _ , e)) tl is ts sg pre inv fr vx vd (no ¬q) td n = ⊥-elim (¬q p)
  -- `main`, found by the dispatch
  walk-mono-d {csc} {es} {ft = ft} {bd} er g D rest rf {g′} eg {se} {d} {f} ce {irFun} cf rest-b mi′ (inj₂ w) tl is ts sg pre inv fr vx vd (yes refl) (yes refl) n =
    trans (run-at (realize D) n (σ-at (table-here {csc = csc} {es = es} {ft = ft} {bd = bd} irFun (FB.bundle→compiled rest-b) pre)
                                      (msc-here {csc = csc} {es = es} {ft = ft} {bd = bd} {se = se} {d = d} {f = f} {irFun = irFun}
                                                {rf = rf} {g = g′} {eg = eg} {ce = ce} {cf = cf} rest-b (inj₂ w))))
          (here-main sg {fi = C.mkFunInfo "main" ft bd false} D (FB.bundle→compiled rest-b) _ refl rest-b refl inv fr n)
  -- a second `main` would have the first one's name
  walk-mono-d er g D rest rf eg ce cf rest-b mi′ (inj₂ w) tl is ts sg pre inv ((hd ∷ _) , _) vx vd (yes refl) (no _) n =
    ⊥-elim (not-in hd (mainIn-name rest mi′))
  -- not `main`: the entry joins the table and the telescope
  walk-mono-d {csc} {es} {x} {ft} {bd} {ty} er g D rest rf eg ce {irFun} cf rest-b mi′ (inj₂ w) tl is ts sg pre inv fr vx vd (no ¬q) td n =
    trans (run-at (proj₂ (MC.mainRealized-go rest mi′)) n
             (σ-at′ (table-other x ft bd ty irFun (FB.bundle→compiled rest-b) pre ¬q)
                    (msc-next {csc = csc} {es = es} {ft = ft} {bd = bd} rest-b w (x ≟str "main") (ty ≟T EffUU) ¬q)))
          (walk rest rest-b mi′ w _ (i-def zero refl (wkI is)) (wkT ts) (monoSg sg g)
                (irFunOf (C.mkCompiledFun (bare x) ty irFun false) ∷ pre)
                (inv-mono sg {fi = C.mkFunInfo x ft bd false} {ty = ty} {g = g} D {irFun = irFun} cf ¬q vx inv (fresh-head {csc = csc} {e = C.e-fun (C.mkFunInfo x ft bd false)} {es = es} fr))
                (fresh-fun {csc = csc} {fi = C.mkFunInfo x ft bd false} {ty = ty} {es = es} fr) vd n)
    where
      σ-at′ : ∀ {tbl tbl′ : List IRFun} {msc msc′ : C.CScope} → tbl ≡ tbl′ → msc ≡ msc′
            → σW tbl (C.cpolys msc) (C.declImps (C.CScope.ctele msc)) (("main" , EffUU) ∷ C.CScope.cimps msc)
              ≡ σW tbl′ (C.cpolys msc′) (C.declImps (C.CScope.ctele msc′)) (("main" , EffUU) ∷ C.CScope.cimps msc′)
      σ-at′ refl refl = refl
