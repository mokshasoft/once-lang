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

open import Once.Target.Arch using (TargetNum)

open import Once.Denotation.TraceMonad using (Interp; pureHalf; interp)
open import Once.Spec.Contract using (ISig; Impl)

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
open import Data.Product using (_×_; _,_)
open import Data.String using () renaming (_≟_ to _≟str_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (false)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.Type using (Type)
open import Once.Type.DecEq using (_≟T_)
open import Once.Type.Rigid using (RigidFree)
open import Once.CanonicalName using (bare)
import Once.Compile as C
open C.FunInfo using (funName)
open import Once.IR using (IR)
import Once.IR
open import Once.IRTy using (⌊_⌋)
import Once.Surface.Context as Ctx
import Once.Surface.Syntax as Srf
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.Program using (IRFun)
open Once.Denotation.Program.IRFun using (fname)
open import Once.Spec.Module using (ModTele; []; ffi; mono; poly; MainIn; EffUU; ctxOf)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Core.Telescope using (Tele; runProgram; program; noKinds; noVars; noResp)
open import Once.Spec.Core.Translate using (SigSig; s-ffi; ImpSig; TeleSig; i-def; t-def; wkI; wkT; SigCF; SigIn; toProgram; monoHere; monoSchema; monoSg; polySg)
import Once.Spec.Core.Abstract as A
import Once.Spec.Core.Translate as TR
open import Once.Compile using (irFunOf; tableOf-go; mainCall)
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
φ = pureHalf ι

open import Once.Adequacy.GradedRelation fmt using (RelGT-bind)
open import Once.Denotation.TraceMonad using (projTrace)
import Once.Adequacy.TeleEntry fmt ι as TE

import Once.Adequacy.ElabInst as EI
open import Once.Type.Rigid using (RigidFree)
import Once.Adequacy.SourceFaithful as SF
import Once.Adequacy.ResolveFaithful as RF
import Once.TypeCheck.Completeness
import Once.TypeCheck.Elaborate
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.Denotation.Program using (tableEnv)
open import Once.Adequacy.TableCall fmt φ using (tableEnv-skip; tableEnv-hit; uncurry-app)
open import Once.Denotation.Trace using (SigOpEvent)
import Data.Fin
import Relation.Nullary
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ)
open import Once.Adequacy.TelePosition
open import Data.List.Relation.Unary.Any using (here; there)
open import Once.Denotation.TraceMonad using (RelT′-events)
open import Once.Denotation.Program using (tableCalls)
open import Data.List using (take)

open import Once.Adequacy.TeleWalk.Invariant fmt Fs Ip hiding (φ; ι)

------------------------------------------------------------------------
-- `main` (D253): an entry like any other. The compiled program runs the CALL
-- of it, which the table answers with its compiled body read through the ABI;
-- the core program runs the entry. The entry's compile chain
-- (`MonoStep.relM`) relates the two, at the run of `IO Unit`.
------------------------------------------------------------------------

-- The run of the compiled program at a table.
RunAt : List IRFun → ℕ → List SigOpEvent
RunAt tbl n = projTrace ι (evalᴰ fmt (tableEnv fmt φ tbl) mainCall tt) n

private
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
from-sem : ∀ {s} {S : Sig Fs s} {sc es} (tl : Tele S) (ss : SigSig Fs (Once.Spec.Module.Scope.sig sc)) (is : ImpSig S (Once.Spec.Module.Scope.imps sc))
             (ts : TeleSig S (Once.Spec.Module.Scope.tele sc)) (sg : SigCF S)
             (d : Data.Fin.Fin s) (e : S Once.Spec.Core.PolyTy.!! d ≡ monoSchema EffUU) (rest : ModTele sc es) (u : SigIn rest S) (n : ℕ)
         → runProgram fmt (TR.toProgramFrom tl ss is ts sg d e rest u) Ip n ≡ runProgram fmt (program tl d e) Ip n
from-sem tl ss is ts sg d e [] u n = refl
from-sem tl ss is ts sg d e (ffi _ _ c h g rest) u n = from-sem tl (s-ffi h g (u (here refl)) ss) is ts sg d e rest (λ m → u (there m)) n
from-sem {S = S} {sc} tl ss is ts sg d e (poly {pfi = pfi} {Ψ = Ψ} D rest) u n =
  from-sem (TR.polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts sg D) ss (wkI is) (t-def zero refl (wkT ts)) (polySg sg pfi) (suc d) e rest u n
from-sem {S = S} {sc} tl ss is ts sg d e (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er g D rest) u n =
  from-sem (TR.monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sg g D) ss (i-def zero refl (wkI is)) (wkT ts) (monoSg sg g) (suc d) e rest u n

here-main : ∀ {s} {S : Sig Fs s} {csc tl ss is ts pre} (sg : SigCF S) {ft bd} (g : RigidFree EffUU)
              (D : ctxOf (AS.scopeOf csc) ⊢ᶜ bd ∶ EffUU ⨾ Ctx.Usage.[]) {irFun : IR ⌊ Once.Type.Unit ⌋ ⌊ EffUU ⌋}
              (cf : C.compileFun C.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                      "main" EffUU bd ≡ Data.Sum.inj₂ irFun)
              {es} (rest : ModTele (AS.scopeOf (C.extendScope csc "main" EffUU)) es)
              (rest-b : FB.FunBundle (C.extendScope csc "main" EffUU) es)
          → Inv {S = S} csc tl ss is ts pre → (u : SigIn rest S) → All ("main" ≢_) (map entryName es)
          → ∀ n → RunAt (tableOf-go (FB.bundle→compiled rest-b) (irFunOf (C.mkCompiledFun (bare "main") EffUU irFun) ∷ pre)) n
                ≡ runProgram fmt (monoHere {S = S} {sc = AS.scopeOf csc} {fi = C.mkFunInfo "main" ft bd false} {ty = EffUU}
                                    {Ψ = Ctx.Usage.[]} tl ss is ts sg g D rest refl u) Ip n
here-main {S = S} {csc} {tl} {ss} {is} {ts} {pre} sg {ft} {bd} g D {irFun} cf {es} rest rest-b inv u hs n =
  -- Plan 0.105: related computations make the same calls under any
  -- interpretation (`RelT′-events`), so their first `n` events agree.
  trans ir-side (trans (sym (cong (take n) (RelT′-events ι [] (RelGT-bind {EffUU} {Once.Type.Unit} relM (λ rv → rv {tt} {tt} tt)))))
                       (trans (cong (λ (v : ⟦ EffUU ⟧ᵛ) → projTrace ι (v tt) n) (sym core≡))
                              (sym (from-sem tl′ ss (i-def zero refl (wkI is)) (wkT ts) (monoSg sg g) zero refl rest u n))))
  where
    open MonoStep {S = S} {csc} {tl} {ss} {is} {ts} {pre} sg {C.mkFunInfo "main" ft bd false} {EffUU} g D {irFun} cf inv
    later = tableOf-go (FB.bundle→compiled rest-b) []

    ir-side : RunAt (tableOf-go (FB.bundle→compiled rest-b) (e ∷ pre)) n ≡ projTrace ι (M Once.Denotation.TraceMonad.>>=T λ c → c tt) n
    ir-side =
      trans (cong (λ tbl → RunAt tbl n) (tableOf-go-++ (FB.bundle→compiled rest-b) [] (e ∷ pre)))
        (cong (λ t → projTrace ι t n)
          (trans (skip-later later (e ∷ pre) tt (later-not-main rest-b hs))
            (trans (tableEnv-hit (bare "main") ⌊ Once.Type.Unit ⌋ ⌊ Once.Type.Unit ⌋
                      (Once.IR.apply Once.IR.∘ Once.IR.⟨ irFun Once.IR.∘ Once.IR.terminal , Once.IR.id ⟩) pre tt)
                   (uncurry-app (tableEnv fmt φ pre) irFun tt))))

    -- the core program's entry, read back at its only instance, is the elaboration's meaning
    core≡ : GM.⟦_⟧ S (PT.instantiate S noVars noResp bodyD) fmt δ tt ≡ GM.⟦_⟧ S Dc fmt δ tt
    core≡ = trans (sym (K-subst {A = EffUU} (λ X → ⟦ X ⟧ᵛ) _ _)) (CAS.mono-entry-sem S noKinds noVars noResp sg g Dc fmt δ)

mutual
  walk : ∀ {csc es} (mt : ModTele (AS.scopeOf csc) es) (b : FB.FunBundle csc es) (mi : MainIn mt)
           {s} {S : Sig Fs s} (tl : Tele S) (ss : SigSig Fs (C.CScope.csig csc)) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
           (sg : SigCF S) (pre : List IRFun) → Inv csc tl ss is ts pre → (u : SigIn mt S) → Fresh csc es
       → ∀ n → RunAt (tableOf-go (FB.bundle→compiled b) pre) n ≡ runProgram fmt (toProgram tl ss is ts sg mt mi u) Ip n
  walk [] FB.bnil () tl ss is ts sg pre inv u fr n
  -- D274: an FFI declaration extends Σ; the table is unchanged.
  walk {csc} {C.e-fun fi ∷ es} (ffi {fi = fi} {ty = ty} ep et c h g rest) (FB.bffi {ty = ty′} ep′ et′ ec eh eg rest-b) mi tl ss is ts sg pre inv u fr n
    with just-injective (trans (sym et) et′)
  ... | refl = walk rest rest-b mi tl (s-ffi h g (u (here refl)) ss) is ts sg pre
                 (inv-sig {x = funName fi} {ty = ty} {h = h} {g = g} {m = u (here refl)} inv)
                 (λ m → u (there m)) (fresh-sig {csc = csc} {fi = fi} {ty = ty} {es = es} fr) n
  walk (ffi {fi = C.mkFunInfo x ft bd prim} refl et c h g rest) (FB.bcons () rf eg ce cf rest-b) mi tl ss is ts sg pre inv u fr n
  walk {csc} {C.e-poly pfi ∷ es} (poly {pfi = pfi} {Ψ = Ctx.Usage.[]} D rest) (FB.bpoly ce rest-b) mi tl ss is ts sg pre inv u fr n =
    walk rest rest-b mi _ ss (wkI is) (t-def zero refl (wkT ts)) (polySg sg pfi) pre
         (inv-poly sg D inv (fresh-head {csc = csc} {e = C.e-poly pfi} {es = es} fr)) u
         (fresh-poly {csc = csc} {pfi = pfi} {es = es} fr) n
  walk (mono {fi = C.mkFunInfo x ft bd prim} {ty = ty} {Ψ = Ctx.Usage.[]} refl er g D rest)
       (FB.bcons {ty = ty′} {Ψ = Ctx.Usage.[]} {irFun = irFun} refl rf eg ce cf rest-b) mi tl ss is ts sg pre inv u fr n
    with inj₂-injective (trans (sym er) rf)
  ... | refl = walk-mono er g D rest cf rest-b mi tl ss is ts sg pre inv u fr n

  walk-mono : ∀ {csc es x ft bd ty} (er : C.resolveFunType (C.ctop csc) (C.cpolys csc) ft bd ≡ inj₂ ty)
                (g : RigidFree ty) (D : ctxOf (AS.scopeOf csc) ⊢ᶜ bd ∶ ty ⨾ Ctx.Usage.[])
                (rest : ModTele (AS.scopeOf (C.extendScope csc x ty)) es)
                {irFun} (cf : C.compileFun C.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                                x ty bd ≡ Data.Sum.inj₂ irFun)
                (rest-b : FB.FunBundle (C.extendScope csc x ty) es)
                (mi : ((x ≡ "main") × (ty ≡ EffUU)) ⊎ MainIn rest)
                {s} {S : Sig Fs s} (tl : Tele S) (ss : SigSig Fs (C.CScope.csig csc)) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
                (sg : SigCF S) (pre : List IRFun) → Inv csc tl ss is ts pre → (u : SigIn rest S) → Fresh csc (C.e-fun (C.mkFunInfo x ft bd false) ∷ es)
            → ∀ n → RunAt (tableOf-go (FB.bundle→compiled rest-b) (irFunOf (C.mkCompiledFun (bare x) ty irFun) ∷ pre)) n
                  ≡ runProgram fmt (toProgram tl ss is ts sg (mono {fi = C.mkFunInfo x ft bd false} {Ψ = Ctx.Usage.[]} refl er g D rest) mi u) Ip n
  walk-mono {csc} {es} {ft = ft} {bd} er g D rest cf rest-b (inj₁ (refl , refl)) {S = S} tl ss is ts sg pre inv u ((hd ∷ _) , _) n =
    here-main {S = S} {csc} {tl} {ss} {is} {ts} {pre} sg {ft} {bd} g D cf {es} rest rest-b inv u hd n
  walk-mono {x = x} {ty = ty} er g D rest cf rest-b (inj₂ mi′) tl ss is ts sg pre inv u fr n =
    walk-mono-d er g D rest cf rest-b mi′ tl ss is ts sg pre inv u fr (x ≟str "main") (ty ≟T EffUU) n

  walk-mono-d : ∀ {csc es x ft bd ty} (er : C.resolveFunType (C.ctop csc) (C.cpolys csc) ft bd ≡ inj₂ ty)
                (g : RigidFree ty) (D : ctxOf (AS.scopeOf csc) ⊢ᶜ bd ∶ ty ⨾ Ctx.Usage.[])
                (rest : ModTele (AS.scopeOf (C.extendScope csc x ty)) es)
                {irFun} (cf : C.compileFun C.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                                x ty bd ≡ Data.Sum.inj₂ irFun)
                (rest-b : FB.FunBundle (C.extendScope csc x ty) es)
                (mi′ : MainIn rest)
                {s} {S : Sig Fs s} (tl : Tele S) (ss : SigSig Fs (C.CScope.csig csc)) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
                (sg : SigCF S) (pre : List IRFun) → Inv csc tl ss is ts pre → (u : SigIn rest S) → Fresh csc (C.e-fun (C.mkFunInfo x ft bd false) ∷ es)
                → (nd : Dec (x ≡ "main")) (td : Dec (ty ≡ EffUU))
              → ∀ n → RunAt (tableOf-go (FB.bundle→compiled rest-b) (irFunOf (C.mkCompiledFun (bare x) ty irFun) ∷ pre)) n
                    ≡ runProgram fmt (Once.Spec.Core.Translate.monoDispatch {S = S} {sc = AS.scopeOf csc} {fi = C.mkFunInfo x ft bd false}
                                        {ty = ty} {Ψ = Ctx.Usage.[]} tl ss is ts sg g D rest mi′ nd td u) Ip n
  -- `main`, found by the dispatch
  walk-mono-d {csc} {es} {ft = ft} {bd} er g D rest cf rest-b mi′ {S = S} tl ss is ts sg pre inv u ((hd ∷ _) , _) (yes refl) (yes refl) n =
    here-main {S = S} {csc} {tl} {ss} {is} {ts} {pre} sg {ft} {bd} g D cf {es} rest rest-b inv u hd n
  -- a second `main` would have the first one's name
  walk-mono-d er g D rest cf rest-b mi′ tl ss is ts sg pre inv u ((hd ∷ _) , _) (yes refl) (no _) n =
    ⊥-elim (not-in hd (mainIn-name rest mi′))
  -- not `main`: the entry joins the table and the telescope
  {-# CATCHALL #-}
  walk-mono-d {csc} {es} {x} {ft} {bd} {ty} er g D rest {irFun} cf rest-b mi′ tl ss is ts sg pre inv u fr (no ¬q) td n =
    walk rest rest-b mi′ _ ss (i-def zero refl (wkI is)) (wkT ts) (monoSg sg g)
         (irFunOf (C.mkCompiledFun (bare x) ty irFun) ∷ pre)
         (inv-mono sg {fi = C.mkFunInfo x ft bd false} {ty = ty} {g = g} D {irFun = irFun} cf inv
                   (fresh-head {csc = csc} {e = C.e-fun (C.mkFunInfo x ft bd false)} {es = es} fr)) u
         (fresh-fun {csc = csc} {fi = C.mkFunInfo x ft bd false} {ty = ty} {es = es} fr) n
