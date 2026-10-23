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

import Once.Spec.Context as SCx
open import Once.Spec.Type using (Ty)
open import Once.Spec.Numerics using (TargetNum)

open import Once.Spec.Signature using (Signature; WellFormed; Decl)
open import Data.List using (map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Once.Internal.Name using (showCanonical)
import Once.Spec.Observation as Obs

-- Plan 0.105: at an interpretation — the meaning and the compiled program run
-- against the same one. Plan 0.122: the Spec's interpretation `J` of Σ.
module Once.Adequacy.TeleWalk (fmt : TargetNum) (Σ : Signature) (wf : WellFormed Σ) (J : Obs.Interp Σ)
  (uniq : Unique (map (λ d → showCanonical (Decl.name d)) Σ)) where

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
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (false)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Once.Spec.Type using (Type; _⟨_⟩)
open import Once.Internal.Type.DecEq using (_≟T_)
open import Once.Spec.Name using (bare)
import Once.Compile as C
import Once.IR as IR
import Once.Parser as Parser
open Parser.FunInfo using (funName)
open import Once.IR using (IR)
import Once.IR
open import Once.IRTy using (⌊_⌋)
import Once.Internal.Context as Ctx
import Once.Surface.Syntax as Srf
open import Once.Internal.Typing using (_⊢ᶜ_∶_⨾_)
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.Program using (IRFun)
open Once.Denotation.Program.IRFun using (fname)
open import Once.Internal.Module using (ModTele; []; ffi; mono; poly; MainIn; EffUU; ctxOf; MonoBody; MonoWit)
open import Once.Internal.Principal using (PrincipalAt)
open import Once.Spec.Core.Syntax using (Defs; _!!_)
open import Once.Spec.Core.Program Σ using (Tele; Entry; noVars)
open import Once.Internal.Core.Telescope Σ using (Program; runCore; program)
open import Once.Spec.Sub using (_<:_; sub-void; sub-unit; sub-arr)
open import Once.Spec.Grade using (_⊑π_; ⊑-eff; ⊑-pe; ⊑-ae)
open import Once.Type.Sub using (_<:?_)
import Once.Spec.Domain Σ as SDm
import Once.Spec.Effect Σ as SE
import Once.Internal.Core.TySubstZero as TZ
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Once.CanonicalName using (_≟ᶜ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Once.Denotation.ValueDomain using (cohᴰ)
open import Once.Internal.Iterative using (_>>=∞_)
open import Once.Internal.Iterative using (T∞)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Internal.Core.Translate Σ using (impDefs; SigSig; s-ffi; ImpSig; TeleSig; i-def; t-def; wkI; wkT; SigIn; toProgram; monoHere; monoSchema)
import Once.Internal.Core.Translate Σ as TR
open import Once.Compile using (irFunOf; tableOf-go)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.FunBundle as FB
import Once.Adequacy.MainIRForm as MIF
import Once.Adequacy.MeaningBridge as MB
import Once.Adequacy.CoreEnv as CE
import Once.Adequacy.CoreMeaningBridge as CMB
import Once.Adequacy.MonoEntry as ME
import Once.Internal.Elaboration as ElabM

open import Once.Adequacy.TeleWalk.Invariant fmt Σ wf J uniq

open import Once.Adequacy.GradedRelation Σ σ₀ using (RelGV; RelGM; GM-D)
open import Once.Denotation.SpecDomain Σ σ₀ using (⟦_⟧ᵛ)
open import Once.Adequacy.SpecRun Σ using (RunR; BlockR; SumR; ret; left; forceR; fmapˡ-R; embed-mapˡ-R; bind∞-R; embed-bind-R)
open import Once.Internal.Iterative using (T∞; return∞)
open T∞ using (force)
open import Once.Denotation.ValueRel using (retargetˡ)
open import Once.Denotation.EvalRel using (eval-rel; table-self)
open import Once.Spec.Grade using (eff)
open import Once.Internal.Trace using (projTrace)

import Once.Adequacy.ElabInst as EI
import Once.Adequacy.SourceFaithful as SF
import Once.Adequacy.ResolveFaithful as RF
import Once.TypeCheck.Completeness
import Once.TypeCheck.Elaborate
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.Denotation.Program using (tableEnv)
open import Once.Adequacy.TableCall fmt φ using (tableEnv-skip; tableEnv-hit; uncurry-app; abiT)
open import Once.Internal.Event using (SigOpEvent)
import Data.Fin
import Relation.Nullary
open import Once.Adequacy.TelePosition
open import Once.Internal.Trace using ()
open import Once.Denotation.TraceMonadLaws using (RelT′-events)
open import Once.Denotation.Program using (tableCalls)
open import Data.List using (take)

------------------------------------------------------------------------
-- `main` (D253): an entry like any other. The compiled program runs the CALL
-- of it, which the table answers with its compiled body read through the ABI;
-- the core program runs the entry. The entry's compile chain
-- (`MonoStep.relM`) relates the two, at the run of `Eff Unit Unit`.
------------------------------------------------------------------------

-- D320 / plan 0.119 D5: the compiled program's run at a table and the core
-- program's run are RELATED, step for step — which gives their traces
-- (`TraceTr.RelS-tr`). The compiled program runs its entry `ir` (`mainEntry`:
-- the call of `main`, converted to `Eff Unit Unit`, D315).
Agree : List IRFun → IR ⌊ (Once.Spec.Type.Unit {0}) ⌋ ⌊ (Once.Spec.Type.Unit {0}) ⌋ → Program → Set
Agree tbl ir P = RunR (RelGV (Once.Spec.Type.Unit {0})) (runCore fmt P mo) (evalᴰ fmt (tableEnv fmt φ tbl) ir tt)

-- …at the entry the bundle finds, if any.
AgreeM : List IRFun → Maybe (IR ⌊ (Once.Spec.Type.Unit {0}) ⌋ ⌊ (Once.Spec.Type.Unit {0}) ⌋) → Program → Set
AgreeM tbl (just ir) P = Agree tbl ir P
AgreeM tbl nothing   P = ⊥

private
  -- A run related to a returned value, against a returned value.
  ret-inv : ∀ {X Y} {R : X → Y → Set} {a b} → RunR R (SE.return∞ a) (return∞ b) → R a b
  ret-inv h = inv (forceR h)
    where inv : ∀ {X Y} {R : X → Y → Set} {a b}
              → BlockR (SumR R (RunR R)) (SE.roll (SE.done (inj₁ a))) (Once.Internal.Trace.ret (inj₁ b)) → R a b
          inv (ret (left r)) = r

  -- `main`'s result, converted to `Unit` at grade `eff`: the run is unchanged…
  conv-unit : ∀ {π} (g : π ⊑π eff) {m : SE.M π ⊤} {t}
            → RelGM π (Once.Spec.Type.Unit {0}) m t
            → RunR (RelGV (Once.Spec.Type.Unit {0})) (SE.sub g (SE.fmap π (SDm.conv σ₀ (sub-unit {m = 0})) m)) t
  conv-unit ⊑-eff     r = fmapˡ-R (λ _ → tt) r
  conv-unit ⊑-pe      r = r
  conv-unit ⊑-ae  {m} r = embed-mapˡ-R (λ _ → tt) m r

  -- …and a run that never returns (`Void`) is related to any continuation of
  -- a run it is related to.
  conv-void : ∀ {π} (g : π ⊑π eff) {m : SE.M π ⊥} {t} {Y} {k : ⟦ (Once.Spec.Type.Void {0}) ⟧ᴰ → T∞ Y}
              {R : ⊤ → Y → Set}
            → RelGM π (Once.Spec.Type.Void {0}) m t
            → RunR R (SE.sub g (SE.fmap π (SDm.conv σ₀ (sub-void {B = Once.Spec.Type.Unit {0}})) m)) (t >>=∞ k)
  conv-void ⊑-eff      r = bind∞-R (λ {a} _ → ⊥-elim a) r
  conv-void ⊑-pe  {()} r
  conv-void ⊑-ae  {m}  r = embed-bind-R (λ {a} _ → ⊥-elim a) m r

  -- `main`'s run, converted (D315), against the compiled entry: the call of
  -- `main`, which the table answers with its entry's direct-call form.
  main-run : ∀ {ty} (p : ty <: EffUU) (pre tbl : List IRFun) {irFun : IR ⌊ (Once.Spec.Type.Unit {0}) ⌋ ⌊ ty ⌋} {v : ⟦ ty ⟧ᵛ}
           → (∀ A B a → tableCalls fmt φ tbl (bare "main") A B a
                        ≡ tableCalls fmt φ (irFunOf (C.mkCompiledFun (bare "main") ty irFun) ∷ pre) (bare "main") A B a)
           → RelGM Once.Spec.Grade.pure ty v (subst T∞ (cohᴰ ty) (abiT ty (evalᴰ fmt (tableEnv fmt φ pre) irFun tt)))
           → RunR (RelGV (Once.Spec.Type.Unit {0})) (SDm.conv σ₀ p v tt) (evalᴰ fmt (tableEnv fmt φ tbl) (C.mainEntry p) tt)
  main-run sub-void pre tbl {v = ()} sk r
  main-run (sub-arr {π = π} sub-unit sub-unit g) pre tbl {irFun} {v} sk r =
    conv-unit g {m = v tt} (GM-D π (Once.Spec.Type.Unit {0}) (proj₁ (ret-inv r) {tt} {tt} tt)
      (retargetˡ (cong force (trans (sk ⌊ (Once.Spec.Type.Unit {0}) ⌋ ⌊ (Once.Spec.Type.Unit {0}) ⌋ tt)
                                    (tableEnv-hit (bare "main") ⌊ (Once.Spec.Type.Unit {0}) ⌋ ⌊ (Once.Spec.Type.Unit {0}) ⌋ (Once.IR.apply Once.IR.∘ Once.IR.⟨ irFun Once.IR.∘ Once.IR.terminal , Once.IR.id ⟩) pre tt)))
        (uncurry-app (tableEnv fmt φ pre) irFun (eval-rel fmt (table-self fmt φ pre) irFun {tt} {tt} tt) {tt} {tt} tt)))
  main-run (sub-arr {π = π} sub-unit sub-void g) pre tbl {irFun} {v} sk r =
    conv-void g {m = v tt} (GM-D π (Once.Spec.Type.Void {0}) (proj₁ (ret-inv r) {tt} {tt} tt)
      (retargetˡ (cong force (trans (sk ⌊ (Once.Spec.Type.Unit {0}) ⌋ ⌊ (Once.Spec.Type.Void {0}) ⌋ tt)
                                    (tableEnv-hit (bare "main") ⌊ (Once.Spec.Type.Unit {0}) ⌋ ⌊ (Once.Spec.Type.Void {0}) ⌋ (Once.IR.apply Once.IR.∘ Once.IR.⟨ irFun Once.IR.∘ Once.IR.terminal , Once.IR.id ⟩) pre tt)))
        (uncurry-app (tableEnv fmt φ pre) irFun (eval-rel fmt (table-self fmt φ pre) irFun {tt} {tt} tt) {tt} {tt} tt)))

  -- Any two proofs that `main` is usable as `Eff Unit Unit` give one entry.
  entry-irr : ∀ {ty} (p q : ty <: EffUU) → C.mainEntry p ≡ C.mainEntry q
  entry-irr (sub-arr sub-unit sub-unit _) (sub-arr sub-unit sub-unit _) = refl
  entry-irr (sub-arr sub-unit sub-void _) (sub-arr sub-unit sub-void _) = refl
  entry-irr sub-void sub-void = refl

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
from-sem : ∀ {s} {S : Defs s} {sc es} (tl : Tele S) (ss : SigSig (Once.Internal.Module.Scope.sig sc)) (is : ImpSig S (Once.Internal.Module.Scope.imps sc))
             (ts : TeleSig S (Once.Internal.Module.Scope.tele sc))
             (d : Data.Fin.Fin s) (e : Entry (S !! d)) (rest : ModTele sc es) (u : SigIn rest)
         → runCore fmt (TR.toProgramFrom tl ss is ts d e rest u) mo ≡ runCore fmt (program tl d e) mo
from-sem tl ss is ts d e [] u = refl
from-sem tl ss is ts d e (ffi _ _ c h rest) u = from-sem tl (s-ffi c h (u (here refl)) ss) is ts d e rest (λ m → u (there m))
from-sem {S = S} {sc} tl ss is ts d e (poly {pfi = pfi} {Ψ = Ψ} pr D _ rest) u =
  from-sem (TR.polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts D) ss (wkI is) (t-def zero refl (wkT ts)) (suc d) e rest u
from-sem {S = S} {sc} tl ss is ts d e (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr D _ rest) u =
  from-sem (TR.monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D) ss (impDefs (funName fi Str.== "main") is) (wkT ts) (suc d) e rest u

-- `main` (D315): its run at its own type, converted, against the compiled
-- entry the bundle finds — whichever proofs of the conversion each side holds.
here-main : ∀ {s} {S : Defs s} {csc tl ss is ts pre} {ft bd ty} (p : ty <: EffUU)
              (D : MonoBody ft (ctxOf (AS.scopeOf csc)) bd ty SCx.[]) {irFun : IR ⌊ (Once.Spec.Type.Unit {0}) ⌋ ⌊ ty ⌋}
              (cf : C.compileFunM ft IR.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                      "main" ty bd ≡ Data.Sum.inj₂ irFun)
              {es} (rest : ModTele (AS.scopeOf (C.extendScope csc "main" ty)) es)
              (rest-b : FB.FunBundle (C.extendScope csc "main" ty) es)
          → Inv {S = S} csc tl ss is ts pre → (u : SigIn rest) → All ("main" ≢_) (map entryName es)
          → (nd : Dec (bare "main" ≡ bare "main")) (td : Dec (ty <: EffUU))
          → AgreeM (tableOf-go (FB.bundle→compiled rest-b) (irFunOf (C.mkCompiledFun (bare "main") ty irFun) ∷ pre))
                   (C.findMain-here (C.mkCompiledFun (bare "main") ty irFun) nd td (FB.bundle-find rest-b))
                   (monoHere {S = S} {sc = AS.scopeOf csc} {fi = Parser.mkFunInfo "main" ft bd false} {ty = ty}
                             {Ψ = SCx.[]} tl ss is ts D rest p u)
here-main p D cf rest rest-b inv u hs (no ¬e) td = ⊥-elim (¬e refl)
here-main p D cf rest rest-b inv u hs (yes _) (no ¬p) = ⊥-elim (¬p p)
here-main {S = S} {csc} {tl} {ss} {is} {ts} {pre} {ft} {bd} {ty} p D {irFun} cf {es} rest rest-b inv u hs (yes _) (yes q) =
  -- Plan 0.105 / D320: the entry's compile chain relates the core entry to the
  -- compiled call (`relM`); the compiled program's tree IS that call,
  -- converted, and the core program's run IS that entry, converted.
  subst₂ (λ c ir → RunR (RelGV (Once.Spec.Type.Unit {0})) c (evalᴰ fmt (tableEnv fmt φ tbl) ir tt))
         (sym core-eq) (entry-irr p q)
         (main-run p pre tbl
            (λ A B a → trans (cong (λ t → tableCalls fmt φ t (bare "main") A B a) (tableOf-go-++ (FB.bundle→compiled rest-b) [] (e ∷ pre)))
                             (skip-later later (e ∷ pre) a (later-not-main rest-b hs)))
            relM)
  where
    open MonoStep {S = S} {csc} {tl} {ss} {is} {ts} {pre} {Parser.mkFunInfo "main" ft bd false} {ty} D {irFun} cf inv
    later = tableOf-go (FB.bundle→compiled rest-b) []
    tbl   = tableOf-go (FB.bundle→compiled rest-b) (e ∷ pre)

    -- the core program's run: its entry, read back at its only instance (the
    -- elaboration's meaning), converted
    core-eq : runCore fmt (monoHere {S = S} {sc = AS.scopeOf csc} {fi = Parser.mkFunInfo "main" ft bd false} {ty = ty}
                                    {Ψ = SCx.[]} tl ss is ts D rest p u) mo
            ≡ SDm.conv σ₀ p (CMB.⟦_⟧ₛ fmt Σ S σ₀ Dc δ tt) tt
    core-eq =
      trans (from-sem tl′ ss (impDefs ("main" Str.== "main") {x = "main"} {T = ty} is) (wkT ts) zero (TR.mainEntry p) rest u)
            (cong (λ v → SDm.conv σ₀ p v tt) entry-v)
      where
        -- the entry at no variable: the instance's meaning is the body's
        entry-v = H.≅-to-≡ (H.trans (H.≡-subst-removable SDm.⟦_⟧ᵛ (TZ.⟨⟩-0 Σ S noVars (ty ⟨ noVars ⟩)) _)
                           (H.trans (H.sym (H.≡-subst-removable (λ X → SDm.⟦ X ⟨ σ₀ ⟩ ⟧ᵛ) (TZ.⟨⟩-0 Σ S noVars ty) _))
                                    (H.≡-to-≅ (ME.mono-entry-sem Σ fmt S σ₀ _ _ noVars _ Dc δ))))

mutual
  walk : ∀ {csc es} (mt : ModTele (AS.scopeOf csc) es) (b : FB.FunBundle csc es) (mi : MainIn mt)
           {s} {S : Defs s} (tl : Tele S) (ss : SigSig (C.CScope.csig csc)) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
           (pre : List IRFun) → Inv csc tl ss is ts pre → (u : SigIn mt) → Fresh csc es
       → AgreeM (tableOf-go (FB.bundle→compiled b) pre) (FB.bundle-find b) (toProgram tl ss is ts mt mi u)
  walk [] FB.bnil () tl ss is ts pre inv u fr
  -- D274: an FFI declaration extends Σ; the table is unchanged.
  walk {csc} {Parser.e-fun fi ∷ es} (ffi {fi = fi} {ty = ty} ep et c h rest) (FB.bffi {ty = ty′} ep′ et′ ec eh rest-b) mi tl ss is ts pre inv u fr
    with just-injective (trans (sym et) et′)
  ... | refl = walk rest rest-b mi tl (s-ffi c h (u (here refl)) ss) is ts pre
                 (inv-sig {x = funName fi} {ty = ty} {k = c} {h = h} {m = u (here refl)} inv)
                 (λ m → u (there m)) (fresh-sig {csc = csc} {fi = fi} {ty = ty} {es = es} fr)
  walk (ffi {fi = Parser.mkFunInfo x ft bd prim} refl et c h rest) (FB.bcons () rf fc ce cf rest-b) mi tl ss is ts pre inv u fr
  walk {csc} {Parser.e-poly pfi ∷ es} (poly {pfi = pfi} {Ψ = SCx.[]} pr D _ rest) (FB.bpoly fc ce rest-b) mi tl ss is ts pre inv u fr =
    walk rest rest-b mi _ ss (wkI is) (t-def zero refl (wkT ts)) pre
         (inv-poly D inv (fresh-head {csc = csc} {e = Parser.e-poly pfi} {es = es} fr)) u
         (fresh-poly {csc = csc} {pfi = pfi} {es = es} fr)
  walk (mono {fi = Parser.mkFunInfo x ft bd prim} {ty = ty} {Ψ = SCx.[]} refl er pr D W rest)
       (FB.bcons {ty = ty′} {Ψ = SCx.[]} {irFun = irFun} refl rf fc ce cf rest-b) mi tl ss is ts pre inv u fr
    with inj₂-injective (trans (sym er) rf)
  ... | refl = walk-mono er pr D W rest cf rest-b mi tl ss is ts pre inv u fr
                 (bare x ≟ᶜ bare "main") (ty <:? EffUU)

  walk-mono : ∀ {csc es x ft bd ty} (er : C.resolveFunType (C.ctop csc) (C.cpolys csc) ft bd ≡ inj₂ ty)
                (pr : PrincipalAt (ctxOf (AS.scopeOf csc)) bd ty)
                (D : MonoBody ft (ctxOf (AS.scopeOf csc)) bd ty SCx.[])
                (W : MonoWit ft (ctxOf (AS.scopeOf csc)) bd ty SCx.[])
                (rest : ModTele (AS.scopeOf (C.extendScope csc x ty)) es)
                {irFun} (cf : C.compileFunM ft IR.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                                x ty bd ≡ Data.Sum.inj₂ irFun)
                (rest-b : FB.FunBundle (C.extendScope csc x ty) es)
                (mi : ((x ≡ "main") × (ty <: EffUU)) ⊎ MainIn rest)
                {s} {S : Defs s} (tl : Tele S) (ss : SigSig (C.CScope.csig csc)) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
                (pre : List IRFun) → Inv csc tl ss is ts pre → (u : SigIn rest) → Fresh csc (Parser.e-fun (Parser.mkFunInfo x ft bd false) ∷ es)
                → (nd′ : Dec (bare x ≡ bare "main")) (td : Dec (ty <: EffUU))
            → AgreeM (tableOf-go (FB.bundle→compiled rest-b) (irFunOf (C.mkCompiledFun (bare x) ty irFun) ∷ pre))
                     (C.findMain-here (C.mkCompiledFun (bare x) ty irFun) nd′ td (FB.bundle-find rest-b))
                     (toProgram tl ss is ts (mono {fi = Parser.mkFunInfo x ft bd false} {Ψ = SCx.[]} refl er pr D W rest) mi u)
  walk-mono {csc} {es} {ft = ft} {bd} er pr D W rest cf rest-b (inj₁ (refl , p)) {S = S} tl ss is ts pre inv u ((hd ∷ _) , _) nd′ td =
    here-main {S = S} {csc} {tl} {ss} {is} {ts} {pre} {ft} {bd} p D cf {es} rest rest-b inv u hd nd′ td
  walk-mono {x = x} {ty = ty} er pr D W rest cf rest-b (inj₂ mi′) tl ss is ts pre inv u fr nd′ td =
    walk-mono-d D rest cf rest-b mi′ tl ss is ts pre inv u fr (x Str.≟ "main") (ty <:? EffUU) nd′ td

  walk-mono-d : ∀ {csc es x ft bd ty}
                (D : MonoBody ft (ctxOf (AS.scopeOf csc)) bd ty SCx.[])
                (rest : ModTele (AS.scopeOf (C.extendScope csc x ty)) es)
                {irFun} (cf : C.compileFunM ft IR.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                                x ty bd ≡ Data.Sum.inj₂ irFun)
                (rest-b : FB.FunBundle (C.extendScope csc x ty) es)
                (mi′ : MainIn rest)
                {s} {S : Defs s} (tl : Tele S) (ss : SigSig (C.CScope.csig csc)) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
                (pre : List IRFun) → Inv csc tl ss is ts pre → (u : SigIn rest) → Fresh csc (Parser.e-fun (Parser.mkFunInfo x ft bd false) ∷ es)
                → (nd : Dec (x ≡ "main")) (tc : Dec (ty <: EffUU)) (nd′ : Dec (bare x ≡ bare "main")) (td : Dec (ty <: EffUU))
              → AgreeM (tableOf-go (FB.bundle→compiled rest-b) (irFunOf (C.mkCompiledFun (bare x) ty irFun) ∷ pre))
                       (C.findMain-here (C.mkCompiledFun (bare x) ty irFun) nd′ td (FB.bundle-find rest-b))
                       (TR.monoDispatch {S = S} {sc = AS.scopeOf csc} {fi = Parser.mkFunInfo x ft bd false}
                                        {ty = ty} {Ψ = SCx.[]} tl ss is ts D rest mi′ nd tc u)
  -- `main`, found by the dispatch
  walk-mono-d {csc} {es} {ft = ft} {bd} D rest cf rest-b mi′ {S = S} tl ss is ts pre inv u ((hd ∷ _) , _) (yes refl) (yes p) nd′ td =
    here-main {S = S} {csc} {tl} {ss} {is} {ts} {pre} {ft} {bd} p D cf {es} rest rest-b inv u hd nd′ td
  -- a second `main` would have the first one's name
  walk-mono-d D rest cf rest-b mi′ tl ss is ts pre inv u ((hd ∷ _) , _) (yes refl) (no _) nd′ td =
    ⊥-elim (not-in hd (mainIn-name rest mi′))
  -- not `main`: the entry joins the table and the telescope
  {-# CATCHALL #-}
  walk-mono-d D rest cf rest-b mi′ tl ss is ts pre inv u fr (no ¬q) tc (yes e) td =
    ⊥-elim (¬q (MIF.bare-injective e))
  {-# CATCHALL #-}
  walk-mono-d {csc} {es} {x} {ft} {bd} {ty} D rest {irFun} cf rest-b mi′ tl ss is ts pre inv u fr (no ¬q) tc (no _) td =
    walk rest rest-b mi′ _ ss (impDefs (x Str.== "main") is) (wkT ts)
         (irFunOf (C.mkCompiledFun (bare x) ty irFun) ∷ pre)
         (inv-mono {fi = Parser.mkFunInfo x ft bd false} {ty = ty} D {irFun = irFun} cf inv
                   (fresh-head {csc = csc} {e = Parser.e-fun (Parser.mkFunInfo x ft bd false)} {es = es} fr)) u
         (fresh-fun {csc = csc} {fi = Parser.mkFunInfo x ft bd false} {ty = ty} {es = es} fr)
