-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.TeleWalk — plan 0.103 6b, leg C.6: THE TELESCOPE WALK.
--
-- `CoreBridge.program-core` is proved by one walk over the module's entries,
-- in lockstep over three views of it:
--   * the typed telescope `mt` (`ModTele`), which `toProgram` turns into the
--     core program;
--   * the compile bundle `b` (`FunBundle`), which carries each entry's compiled
--     IR and so the function table;
--   * the core telescope built so far (`tl`, with its signature data).
--
-- The invariant (`Inv`) at each position is leg A's environment relation
-- between the scope's surface environment, built from the core's (`CoreEnv`),
-- and the compiled program's environment (`σW`: calls of the table, splices
-- of the resolver), at EVERY later table that does not shadow the scope's
-- names and every declaration-import map that agrees on the scope's entries.
-- Each entry's step is legs A (MeaningBridge), B (CoreMeaningBridge) and F
-- (CoreAbsSem) over its compile chain. `main` is an entry like any other
-- (D253): the compiled program calls it, and its step is the equation of the
-- two runs.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

open import Once.Lang.Trace using (Interp; pureHalf; interp)
open import Once.Lang.Contract using (ISig; Impl)

-- Plan 0.105: at an interpretation `ι` — the meaning and the compiled program
-- run against the same one.
module Once.Adequacy.TeleWalk (fmt : TargetNum) (Fs : ISig) (Ip : Impl Fs) where

-- The world: the program's signatures with the implementation `Ip`.
ι : Interp
ι = interp Fs Ip

open import Data.Nat using (ℕ)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Product using (_×_; _,_; proj₁)
import Data.String as Str
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (false)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)

open import Once.Lang.Type using (Type)
open import Once.Lang.Type.DecEq using (_≟T_)
open import Once.Lang.Type.WellFormed using (RigidFree)
open import Once.Spec.Name using (bare)
import Once.Compile as C
import Once.IR as IR
import Once.Parser as Parser
open Parser.FunInfo using (funName)
open import Once.IR using (IR)
import Once.IR
open import Once.IRTy using (⌊_⌋)
import Once.Lang.Context as Ctx
import Once.Surface.Syntax as Srf
open import Once.Lang.Typing using (_⊢ᶜ_∶_⨾_)
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.Program using (IRFun)
open Once.Denotation.Program.IRFun using (fname)
open import Once.Lang.Module using (ModTele; []; ffi; mono; poly; MainIn; EffUU; ctxOf)
open import Once.Lang.Core.PolyTy using (Sig)
open import Once.Lang.Core.Telescope using (Tele; Program; runCore; program; noKinds; noVars; noResp)
open import Once.Lang.Iterative using (T∞)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Lang.Core.Translate using (SigSig; s-ffi; ImpSig; TeleSig; i-def; t-def; wkI; wkT; SigCF; SigIn; toProgram; monoHere; monoSchema; monoSg; polySg)
import Once.Lang.Core.Abstract as A
import Once.Lang.Core.Translate as TR
open import Once.Compile using (irFunOf; tableOf-go; mainCall)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.FunBundle as FB
import Once.Adequacy.MainIRForm as MIF
import Once.Adequacy.MeaningBridge as MB
import Once.Adequacy.CoreEnv as CE
import Once.Adequacy.CoreMeaningBridge as CMB
import Once.Adequacy.CoreAbsSem as CAS
import Once.Lang.Elaboration as ElabM
import Once.Lang.Core.Meaning as GM
import Once.Lang.Core.PolyTyping as PT
import Once.Denotation.Meaning as MeaningM
open import Once.Lang.Trace using (FFIAnswers)

-- The interpretation's pure half: what the program's pure FFI values are.
φ : FFIAnswers
φ = pureHalf ι

open import Once.Adequacy.GradedRelation fmt using (RelGV; GM-D)
open import Once.Lang.Iterative using (T∞; force; return∞)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret)
open RelS using (forceS)
open import Once.Denotation.ValueRel using (retargetˡ)
open import Once.Denotation.EvalRel using (eval-rel; table-self)
open import Once.Lang.Type.Grade using (eff)
open import Once.Lang.Trace using (projTrace)
import Once.Adequacy.TeleEntry fmt ι as TE

import Once.Adequacy.ElabInst as EI
import Once.Adequacy.SourceFaithful as SF
import Once.Adequacy.ResolveFaithful as RF
import Once.TypeCheck.Completeness
import Once.TypeCheck.Elaborate
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.Denotation.Program using (tableEnv)
open import Once.Adequacy.TableCall fmt φ using (tableEnv-skip; tableEnv-hit; uncurry-app)
open import Once.Lang.Event using (SigOpEvent)
import Data.Fin
import Relation.Nullary
open import Once.Lang.Graded using (⟦_⟧ᵛ)
open import Once.Adequacy.TelePosition
open import Once.Lang.Trace using ()
open import Once.Denotation.TraceMonadLaws using (RelT′-events)
open import Once.Denotation.Program using (tableCalls)
open import Data.List using (take)

open import Once.Adequacy.TeleWalk.Invariant fmt Fs Ip hiding (φ; ι)

------------------------------------------------------------------------
-- `main` (D253): an entry like any other. The compiled program runs the CALL
-- of it, which the table answers with its compiled body read through the ABI;
-- the core program runs the entry. The entry's compile chain
-- (`MonoStep.relM`) relates the two, at the run of `Eff Unit Unit`.
------------------------------------------------------------------------

-- D320 / plan 0.119 D5: the compiled program's run at a table and the core
-- program's run are RELATED, step for step — which gives their traces
-- (`TraceTr.RelS-tr`).
Agree : List IRFun → Program Fs → Set
Agree tbl P = RelS (RelGV Once.Lang.Type.Unit) (runCore fmt P Ip) (evalᴰ fmt (tableEnv fmt φ tbl) mainCall tt)

private
  -- A run related to a returned value, against a returned value.
  ret-inv : ∀ {X Y} {R : X → Y → Set} {a b} → RelS R (return∞ a) (return∞ b) → R a b
  ret-inv h = inv (forceS h)
    where inv : ∀ {X Y} {R : X → Y → Set} {a b} → RelSB R (Once.Lang.Trace.ret (inj₁ a)) (Once.Lang.Trace.ret (inj₁ b)) → R a b
          inv (s-ret r) = r

  K-subst : ∀ {A : Type} (P : Type → Set) (p : A ≡ A) (x : P A) → subst P p x ≡ x
  K-subst P refl x = refl

  -- Past the entries after `main`, the table's call of `main` is its entry's.
  skip-later : ∀ (later es : List IRFun) {A B} (a : _) → All (λ e → fname e ≢ bare "main") later
             → tableCalls fmt φ (later ++ es) (bare "main") A B a ≡ tableCalls fmt φ es (bare "main") A B a
  skip-later []          es a []       = refl
  skip-later (e ∷ later) es a (h ∷ hs) = trans (tableEnv-skip e (later ++ es) h a) (skip-later later es a hs)

  -- …and the later entries are not named `main` (D249).
  later-not-main : ∀ {sc es} (b : FB.FunBundle sc es) → All ("main" ≢_) (map entryName es)
                 → All (λ e → fname e ≢ bare "main") (tableOf-go (FB.bundle→compiled b) [])
  later-not-main b hs = un (tableOf-go (FB.bundle→compiled b) [])
                           (later-ns b mainImps (All.map (λ h → (λ e → h (sym e)) ∷ []) hs) [] [])
    where
      mainImps : C.FunCtx
      mainImps = ("main" , EffUU) ∷ []
      un : ∀ (es : List IRFun) → All (NS mainImps) es → All (λ e → fname e ≢ bare "main") es
      un []       []              = []
      un (_ ∷ es) ((h ∷ []) ∷ hs) = h ∷ un es hs

-- The entries after `main` extend the telescope; the program still names `main`.
from-sem : ∀ {s} {S : Sig Fs s} {sc es} (tl : Tele S) (ss : SigSig Fs (Once.Lang.Module.Scope.sig sc)) (is : ImpSig S (Once.Lang.Module.Scope.imps sc))
             (ts : TeleSig S (Once.Lang.Module.Scope.tele sc)) (sg : SigCF S)
             (d : Data.Fin.Fin s) (e : S Once.Lang.Core.PolyTy.!! d ≡ monoSchema EffUU) (rest : ModTele sc es) (u : SigIn rest S)
         → runCore fmt (TR.toProgramFrom tl ss is ts sg d e rest u) Ip ≡ runCore fmt (program tl d e) Ip
from-sem tl ss is ts sg d e [] u = refl
from-sem tl ss is ts sg d e (ffi _ _ c h g rest) u = from-sem tl (s-ffi h g (u (here refl)) ss) is ts sg d e rest (λ m → u (there m))
from-sem {S = S} {sc} tl ss is ts sg d e (poly {pfi = pfi} {Ψ = Ψ} D rest) u =
  from-sem (TR.polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts sg D) ss (wkI is) (t-def zero refl (wkT ts)) (polySg sg pfi) (suc d) e rest u
from-sem {S = S} {sc} tl ss is ts sg d e (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er g D rest) u =
  from-sem (TR.monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sg g D) ss (i-def zero refl (wkI is)) (wkT ts) (monoSg sg g) (suc d) e rest u

here-main : ∀ {s} {S : Sig Fs s} {csc tl ss is ts pre} (sg : SigCF S) {ft bd} (g : RigidFree EffUU)
              (D : ctxOf (AS.scopeOf csc) ⊢ᶜ bd ∶ EffUU ⨾ Ctx.Usage.[]) {irFun : IR ⌊ Once.Lang.Type.Unit ⌋ ⌊ EffUU ⌋}
              (cf : C.compileFun IR.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                      "main" EffUU bd ≡ Data.Sum.inj₂ irFun)
              {es} (rest : ModTele (AS.scopeOf (C.extendScope csc "main" EffUU)) es)
              (rest-b : FB.FunBundle (C.extendScope csc "main" EffUU) es)
          → Inv {S = S} csc tl ss is ts pre → (u : SigIn rest S) → All ("main" ≢_) (map entryName es)
          → Agree (tableOf-go (FB.bundle→compiled rest-b) (irFunOf (C.mkCompiledFun (bare "main") EffUU irFun) ∷ pre))
                  (monoHere {S = S} {sc = AS.scopeOf csc} {fi = Parser.mkFunInfo "main" ft bd false} {ty = EffUU}
                            {Ψ = Ctx.Usage.[]} tl ss is ts sg g D rest refl u)
here-main {S = S} {csc} {tl} {ss} {is} {ts} {pre} sg {ft} {bd} g D {irFun} cf {es} rest rest-b inv u hs =
  -- Plan 0.105 / D320: the entry's compile chain relates the core entry to the
  -- compiled call (`relM`); the compiled program's tree IS that call, and the
  -- core program's run IS that entry.
  subst (λ c → RelS (RelGV Once.Lang.Type.Unit) c _) core-eq
    (GM-D eff Once.Lang.Type.Unit (proj₁ (ret-inv relM) {tt} {tt} tt)
      (retargetˡ ir-tree
        (uncurry-app (tableEnv fmt φ pre) irFun (eval-rel fmt (table-self fmt φ pre) irFun {tt} {tt} tt) {tt} {tt} tt)))
  where
    open MonoStep {S = S} {csc} {tl} {ss} {is} {ts} {pre} sg {Parser.mkFunInfo "main" ft bd false} {EffUU} g D {irFun} cf inv
    later = tableOf-go (FB.bundle→compiled rest-b) []

    -- the compiled program calls `main`, which the table answers with its
    -- direct-call form (`uncurry-app` relates that to the body's closure)
    ir-tree : force (evalᴰ fmt (tableEnv fmt φ (tableOf-go (FB.bundle→compiled rest-b) (e ∷ pre))) mainCall tt)
              ≡ force (evalᴰ fmt (tableEnv fmt φ pre) (Once.IR.apply Once.IR.∘ Once.IR.⟨ irFun Once.IR.∘ Once.IR.terminal , Once.IR.id ⟩) tt)
    ir-tree =
      cong force
        (trans (cong (λ tbl → evalᴰ fmt (tableEnv fmt φ tbl) mainCall tt) (tableOf-go-++ (FB.bundle→compiled rest-b) [] (e ∷ pre)))
          (trans (skip-later later (e ∷ pre) tt (later-not-main rest-b hs))
                 (tableEnv-hit (bare "main") ⌊ Once.Lang.Type.Unit ⌋ ⌊ Once.Lang.Type.Unit ⌋
                    (Once.IR.apply Once.IR.∘ Once.IR.⟨ irFun Once.IR.∘ Once.IR.terminal , Once.IR.id ⟩) pre tt)))

    -- the core program's entry, read back at its only instance, is the elaboration's meaning
    core≡ : GM.⟦_⟧ S (PT.instantiate S noVars noResp bodyD) fmt δ tt ≡ GM.⟦_⟧ S Dc fmt δ tt
    core≡ = trans (sym (K-subst {A = EffUU} (λ X → ⟦ X ⟧ᵛ) _ _)) (CAS.mono-entry-sem S noKinds noVars noResp sg g Dc fmt δ)

    core-eq : GM.⟦_⟧ S Dc fmt δ tt tt
            ≡ runCore fmt (monoHere {S = S} {sc = AS.scopeOf csc} {fi = Parser.mkFunInfo "main" ft bd false} {ty = EffUU}
                                    {Ψ = Ctx.Usage.[]} tl ss is ts sg g D rest refl u) Ip
    core-eq = trans (cong (λ (v : ⟦ EffUU ⟧ᵛ) → v tt) (sym core≡))
                    (sym (from-sem tl′ ss (i-def zero refl (wkI is)) (wkT ts) (monoSg sg g) zero refl rest u))

mutual
  walk : ∀ {csc es} (mt : ModTele (AS.scopeOf csc) es) (b : FB.FunBundle csc es) (mi : MainIn mt)
           {s} {S : Sig Fs s} (tl : Tele S) (ss : SigSig Fs (C.CScope.csig csc)) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
           (sg : SigCF S) (pre : List IRFun) → Inv csc tl ss is ts pre → (u : SigIn mt S) → Fresh csc es
       → Agree (tableOf-go (FB.bundle→compiled b) pre) (toProgram tl ss is ts sg mt mi u)
  walk [] FB.bnil () tl ss is ts sg pre inv u fr
  -- D274: an FFI declaration extends Σ; the table is unchanged.
  walk {csc} {Parser.e-fun fi ∷ es} (ffi {fi = fi} {ty = ty} ep et c h g rest) (FB.bffi {ty = ty′} ep′ et′ ec eh eg rest-b) mi tl ss is ts sg pre inv u fr
    with just-injective (trans (sym et) et′)
  ... | refl = walk rest rest-b mi tl (s-ffi h g (u (here refl)) ss) is ts sg pre
                 (inv-sig {x = funName fi} {ty = ty} {h = h} {g = g} {m = u (here refl)} inv)
                 (λ m → u (there m)) (fresh-sig {csc = csc} {fi = fi} {ty = ty} {es = es} fr)
  walk (ffi {fi = Parser.mkFunInfo x ft bd prim} refl et c h g rest) (FB.bcons () rf eg ce cf rest-b) mi tl ss is ts sg pre inv u fr
  walk {csc} {Parser.e-poly pfi ∷ es} (poly {pfi = pfi} {Ψ = Ctx.Usage.[]} D rest) (FB.bpoly ce rest-b) mi tl ss is ts sg pre inv u fr =
    walk rest rest-b mi _ ss (wkI is) (t-def zero refl (wkT ts)) (polySg sg pfi) pre
         (inv-poly sg D inv (fresh-head {csc = csc} {e = Parser.e-poly pfi} {es = es} fr)) u
         (fresh-poly {csc = csc} {pfi = pfi} {es = es} fr)
  walk (mono {fi = Parser.mkFunInfo x ft bd prim} {ty = ty} {Ψ = Ctx.Usage.[]} refl er g D rest)
       (FB.bcons {ty = ty′} {Ψ = Ctx.Usage.[]} {irFun = irFun} refl rf eg ce cf rest-b) mi tl ss is ts sg pre inv u fr
    with inj₂-injective (trans (sym er) rf)
  ... | refl = walk-mono er g D rest cf rest-b mi tl ss is ts sg pre inv u fr

  walk-mono : ∀ {csc es x ft bd ty} (er : C.resolveFunType (C.ctop csc) (C.cpolys csc) ft bd ≡ inj₂ ty)
                (g : RigidFree ty) (D : ctxOf (AS.scopeOf csc) ⊢ᶜ bd ∶ ty ⨾ Ctx.Usage.[])
                (rest : ModTele (AS.scopeOf (C.extendScope csc x ty)) es)
                {irFun} (cf : C.compileFun IR.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                                x ty bd ≡ Data.Sum.inj₂ irFun)
                (rest-b : FB.FunBundle (C.extendScope csc x ty) es)
                (mi : ((x ≡ "main") × (ty ≡ EffUU)) ⊎ MainIn rest)
                {s} {S : Sig Fs s} (tl : Tele S) (ss : SigSig Fs (C.CScope.csig csc)) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
                (sg : SigCF S) (pre : List IRFun) → Inv csc tl ss is ts pre → (u : SigIn rest S) → Fresh csc (Parser.e-fun (Parser.mkFunInfo x ft bd false) ∷ es)
            → Agree (tableOf-go (FB.bundle→compiled rest-b) (irFunOf (C.mkCompiledFun (bare x) ty irFun) ∷ pre))
                    (toProgram tl ss is ts sg (mono {fi = Parser.mkFunInfo x ft bd false} {Ψ = Ctx.Usage.[]} refl er g D rest) mi u)
  walk-mono {csc} {es} {ft = ft} {bd} er g D rest cf rest-b (inj₁ (refl , refl)) {S = S} tl ss is ts sg pre inv u ((hd ∷ _) , _) =
    here-main {S = S} {csc} {tl} {ss} {is} {ts} {pre} sg {ft} {bd} g D cf {es} rest rest-b inv u hd
  walk-mono {x = x} {ty = ty} er g D rest cf rest-b (inj₂ mi′) tl ss is ts sg pre inv u fr =
    walk-mono-d er g D rest cf rest-b mi′ tl ss is ts sg pre inv u fr (x Str.≟ "main") (ty ≟T EffUU)

  walk-mono-d : ∀ {csc es x ft bd ty} (er : C.resolveFunType (C.ctop csc) (C.cpolys csc) ft bd ≡ inj₂ ty)
                (g : RigidFree ty) (D : ctxOf (AS.scopeOf csc) ⊢ᶜ bd ∶ ty ⨾ Ctx.Usage.[])
                (rest : ModTele (AS.scopeOf (C.extendScope csc x ty)) es)
                {irFun} (cf : C.compileFun IR.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                                x ty bd ≡ Data.Sum.inj₂ irFun)
                (rest-b : FB.FunBundle (C.extendScope csc x ty) es)
                (mi′ : MainIn rest)
                {s} {S : Sig Fs s} (tl : Tele S) (ss : SigSig Fs (C.CScope.csig csc)) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
                (sg : SigCF S) (pre : List IRFun) → Inv csc tl ss is ts pre → (u : SigIn rest S) → Fresh csc (Parser.e-fun (Parser.mkFunInfo x ft bd false) ∷ es)
                → (nd : Dec (x ≡ "main")) (td : Dec (ty ≡ EffUU))
              → Agree (tableOf-go (FB.bundle→compiled rest-b) (irFunOf (C.mkCompiledFun (bare x) ty irFun) ∷ pre))
                      (Once.Lang.Core.Translate.monoDispatch {S = S} {sc = AS.scopeOf csc} {fi = Parser.mkFunInfo x ft bd false}
                                        {ty = ty} {Ψ = Ctx.Usage.[]} tl ss is ts sg g D rest mi′ nd td u)
  -- `main`, found by the dispatch
  walk-mono-d {csc} {es} {ft = ft} {bd} er g D rest cf rest-b mi′ {S = S} tl ss is ts sg pre inv u ((hd ∷ _) , _) (yes refl) (yes refl) =
    here-main {S = S} {csc} {tl} {ss} {is} {ts} {pre} sg {ft} {bd} g D cf {es} rest rest-b inv u hd
  -- a second `main` would have the first one's name
  walk-mono-d er g D rest cf rest-b mi′ tl ss is ts sg pre inv u ((hd ∷ _) , _) (yes refl) (no _) =
    ⊥-elim (not-in hd (mainIn-name rest mi′))
  -- not `main`: the entry joins the table and the telescope
  {-# CATCHALL #-}
  walk-mono-d {csc} {es} {x} {ft} {bd} {ty} er g D rest {irFun} cf rest-b mi′ tl ss is ts sg pre inv u fr (no ¬q) td =
    walk rest rest-b mi′ _ ss (i-def zero refl (wkI is)) (wkT ts) (monoSg sg g)
         (irFunOf (C.mkCompiledFun (bare x) ty irFun) ∷ pre)
         (inv-mono sg {fi = Parser.mkFunInfo x ft bd false} {ty = ty} {g = g} D {irFun = irFun} cf inv
                   (fresh-head {csc = csc} {e = Parser.e-fun (Parser.mkFunInfo x ft bd false)} {es = es} fr)) u
         (fresh-fun {csc = csc} {fi = Parser.mkFunInfo x ft bd false} {ty = ty} {es = es} fr)
