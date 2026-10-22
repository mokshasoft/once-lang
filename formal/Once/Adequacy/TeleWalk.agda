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

open import Once.Internal.Trace using (Interp; pureHalf; interp)
open import Once.Internal.Contract using (Impl)
open import Once.Spec.Signature using (Signature)
open import Once.Internal.Core.Decl using (toISig)

-- Plan 0.105: at an interpretation `ι` — the meaning and the compiled program
-- run against the same one. Plan 0.122: the program's signature is Σ.
module Once.Adequacy.TeleWalk (fmt : TargetNum) (Σ : Signature) (Ip : Impl (toISig Σ)) where

-- The world: the program's signature with the implementation `Ip`.
ι : Interp
ι = interp (toISig Σ) Ip

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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Once.Spec.Type using (Type)
open import Once.Internal.Type.DecEq using (_≟T_)
open import Once.Internal.Type.WellFormed using (RigidFree)
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
open import Once.Internal.Module using (ModTele; []; ffi; mono; poly; MainIn; EffUU; ctxOf; MonoBody)
open import Once.Internal.Principal using (PrincipalAt)
open import Once.Spec.Core.Syntax using (Defs; _!!_)
open import Once.Spec.Core.Program Σ using (Tele; Entry; noVars)
open import Once.Internal.Core.Telescope Σ using (Program; runCore; program)
open import Once.Internal.Core.TySubstZero using (⟨⟩-0)
open import Once.Metatheory.TermModel.TySubst using (<:-⟨⟩)
open import Once.Spec.Sub using (_<:_; sub-void; sub-unit; sub-int; sub-float; sub-arr; sub-μ; sub-ν)
open import Once.Internal.Type.Sub using (sub-prod; sub-sum; sub-rigid)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Type.Sub using (_<:?_)
open import Once.Internal.GradedOps using (⟦_⟧<:ᵛ; fmapM)
open import Once.Internal.Graded using (M; subM)
open import Once.CanonicalName using (_≟ᶜ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Once.Denotation.ValueDomain using (cohᴰ)
open import Once.Denotation.ValueRel using (RelS-fmapˡ)
open import Once.Denotation.TraceMonadInfLaws using (RelS-bind; RelS-≈ˡ; embed-bind)
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
import Once.Internal.Core.Meaning as GM
import Once.Denotation.Meaning as MeaningM
open import Once.Internal.Trace using (FFIAnswers)

-- The interpretation's pure half: what the program's pure FFI values are.
φ : FFIAnswers
φ = pureHalf ι

open import Once.Adequacy.GradedRelation fmt using (RelGV; RelGM; GM-D; RelS-embed-fmap)
open import Once.Internal.Iterative using (T∞; return∞)
open T∞ using (force)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret)
open RelS using (forceS)
open import Once.Denotation.ValueRel using (retargetˡ)
open import Once.Denotation.EvalRel using (eval-rel; table-self)
open import Once.Spec.Grade using (eff)
open import Once.Internal.Trace using (projTrace)
import Once.Adequacy.TeleEntry fmt ι as TE

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
open import Once.Internal.Graded using (⟦_⟧ᵛ)
open import Once.Adequacy.TelePosition
open import Once.Internal.Trace using ()
open import Once.Denotation.TraceMonadLaws using (RelT′-events)
open import Once.Denotation.Program using (tableCalls)
open import Data.List using (take)

open import Once.Adequacy.TeleWalk.Invariant fmt Σ Ip hiding (φ; ι)

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
Agree tbl ir P = RelS (RelGV (Once.Spec.Type.Unit {0})) (runCore fmt P Ip) (evalᴰ fmt (tableEnv fmt φ tbl) ir tt)

-- …at the entry the bundle finds, if any.
AgreeM : List IRFun → Maybe (IR ⌊ (Once.Spec.Type.Unit {0}) ⌋ ⌊ (Once.Spec.Type.Unit {0}) ⌋) → Program → Set
AgreeM tbl (just ir) P = Agree tbl ir P
AgreeM tbl nothing   P = ⊥

private
  -- A run related to a returned value, against a returned value.
  ret-inv : ∀ {X Y} {R : X → Y → Set} {a b} → RelS R (return∞ a) (return∞ b) → R a b
  ret-inv h = inv (forceS h)
    where inv : ∀ {X Y} {R : X → Y → Set} {a b} → RelSB R (Once.Internal.Trace.ret (inj₁ a)) (Once.Internal.Trace.ret (inj₁ b)) → R a b
          inv (s-ret r) = r

  -- A subtyping has one proof.
  ⊑π-irr : ∀ {π π′} (g g′ : π ⊑π π′) → g ≡ g′
  ⊑π-irr ⊑-pure ⊑-pure = refl
  ⊑π-irr ⊑-eff  ⊑-eff  = refl
  ⊑π-irr ⊑-pe   ⊑-pe   = refl
  ⊑π-irr ⊑-act  ⊑-act  = refl
  ⊑π-irr ⊑-pa   ⊑-pa   = refl
  ⊑π-irr ⊑-ae   ⊑-ae   = refl

  <:-irr : ∀ {m} {A B : Ty m} (p q : A <: B) → p ≡ q
  <:-irr sub-void          sub-void             = refl
  <:-irr sub-unit          sub-unit             = refl
  <:-irr sub-int           sub-int              = refl
  <:-irr sub-float         sub-float            = refl
  <:-irr (sub-arr a b g)   (sub-arr a′ b′ g′)   =
    trans (cong (λ x → sub-arr x b g) (<:-irr a a′))
          (trans (cong (λ x → sub-arr a′ x g) (<:-irr b b′)) (cong (sub-arr a′ b′) (⊑π-irr g g′)))
  <:-irr (sub-prod a b)    (sub-prod a′ b′)     = cong₂ sub-prod (<:-irr a a′) (<:-irr b b′)
  <:-irr (sub-sum a b)     (sub-sum a′ b′)      = cong₂ sub-sum (<:-irr a a′) (<:-irr b b′)
  <:-irr sub-μ             sub-μ                = refl
  <:-irr (sub-ν g)         (sub-ν g′)           = cong sub-ν (⊑π-irr g g′)
  <:-irr sub-rigid         sub-rigid            = refl

  -- The entry's conversion, read across the schema's round trip.
  conv-subst : ∀ {X ty : Type} (e : X ≡ ty) (q : X <: EffUU) (p : ty <: EffUU) (x : ⟦ X ⟧ᵛ)
             → ⟦ q ⟧<:ᵛ x ≡ ⟦ p ⟧<:ᵛ (subst (λ Y → ⟦ Y ⟧ᵛ) e x)
  conv-subst refl q p x = cong (λ r → ⟦ r ⟧<:ᵛ x) (<:-irr q p)

  -- `main`'s result, converted to `Unit` at grade `eff`: the run is unchanged…
  conv-unit : ∀ {π} (g : π ⊑π eff) {m : M π ⟦ (Once.Spec.Type.Unit {0}) ⟧ᵛ} {t}
            → RelGM π (Once.Spec.Type.Unit {0}) m t
            → RelS (RelGV (Once.Spec.Type.Unit {0})) (subM g (fmapM π ⟦ sub-unit {m = 0} ⟧<:ᵛ m)) t
  conv-unit ⊑-eff r     = RelS-fmapˡ r (λ _ → tt)
  conv-unit ⊑-pe  r     = r
  conv-unit ⊑-ae  {m} r = RelS-embed-fmap m r

  -- …and a run that never returns (`Void`) is related to any continuation of
  -- a run it is related to.
  conv-void : ∀ {π} (g : π ⊑π eff) {m : M π ⟦ (Once.Spec.Type.Void {0}) ⟧ᵛ} {t} {Y} {k : ⟦ (Once.Spec.Type.Void {0}) ⟧ᴰ → T∞ Y}
              {R : ⟦ (Once.Spec.Type.Unit {0}) ⟧ᵛ → Y → Set}
            → RelGM π (Once.Spec.Type.Void {0}) m t
            → RelS R (subM g (fmapM π ⟦ sub-void {B = (Once.Spec.Type.Unit {0})} ⟧<:ᵛ m)) (t >>=∞ k)
  conv-void ⊑-eff      r = RelS-bind r (λ {a} _ → ⊥-elim a)
  conv-void ⊑-pe  {()} r
  conv-void ⊑-ae  {m}  r = RelS-≈ˡ (embed-bind m (λ l → Once.Internal.Trace.ret (⟦ sub-void {B = (Once.Spec.Type.Unit {0})} ⟧<:ᵛ l))) (RelS-bind r (λ {a} _ → ⊥-elim a))

  -- `main`'s run, converted (D315), against the compiled entry: the call of
  -- `main`, which the table answers with its entry's direct-call form.
  main-run : ∀ {ty} (p : ty <: EffUU) (pre tbl : List IRFun) {irFun : IR ⌊ (Once.Spec.Type.Unit {0}) ⌋ ⌊ ty ⌋} {v : ⟦ ty ⟧ᵛ}
           → (∀ A B a → tableCalls fmt φ tbl (bare "main") A B a
                        ≡ tableCalls fmt φ (irFunOf (C.mkCompiledFun (bare "main") ty irFun) ∷ pre) (bare "main") A B a)
           → RelGM Once.Spec.Grade.pure ty v (subst T∞ (cohᴰ ty) (abiT ty (evalᴰ fmt (tableEnv fmt φ pre) irFun tt)))
           → RelS (RelGV (Once.Spec.Type.Unit {0})) (⟦ p ⟧<:ᵛ v tt) (evalᴰ fmt (tableEnv fmt φ tbl) (C.mainEntry p) tt)
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
         → runCore fmt (TR.toProgramFrom tl ss is ts d e rest u) Ip ≡ runCore fmt (program tl d e) Ip
from-sem tl ss is ts d e [] u = refl
from-sem tl ss is ts d e (ffi _ _ c h g rest) u = from-sem tl (s-ffi c h (u (here refl)) ss) is ts d e rest (λ m → u (there m))
from-sem {S = S} {sc} tl ss is ts d e (poly {pfi = pfi} {Ψ = Ψ} pr D rest) u =
  from-sem (TR.polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts D) ss (wkI is) (t-def zero refl (wkT ts)) (suc d) e rest u
from-sem {S = S} {sc} tl ss is ts d e (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr g D rest) u =
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
  subst₂ (λ c ir → RelS (RelGV (Once.Spec.Type.Unit {0})) c (evalᴰ fmt (tableEnv fmt φ tbl) ir tt))
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
                                    {Ψ = SCx.[]} tl ss is ts D rest p u) Ip
            ≡ ⟦ p ⟧<:ᵛ (GM.⟦_⟧ Σ S Dc fmt δ tt) tt
    core-eq =
      trans (from-sem tl′ ss (impDefs ("main" Str.== "main") {x = "main"} {T = ty} is) (wkT ts) zero (TR.mainEntry p) rest u)
        (trans (cong (λ f → f tt) (conv-subst (⟨⟩-0 Σ S noVars ty) (<:-⟨⟩ Σ S noVars p) p _))
               (cong (λ v → ⟦ p ⟧<:ᵛ v tt) (ME.mono-entry-sem Σ S _ _ noVars _ Dc fmt δ)))

mutual
  walk : ∀ {csc es} (mt : ModTele (AS.scopeOf csc) es) (b : FB.FunBundle csc es) (mi : MainIn mt)
           {s} {S : Defs s} (tl : Tele S) (ss : SigSig (C.CScope.csig csc)) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
           (pre : List IRFun) → Inv csc tl ss is ts pre → (u : SigIn mt) → Fresh csc es
       → AgreeM (tableOf-go (FB.bundle→compiled b) pre) (FB.bundle-find b) (toProgram tl ss is ts mt mi u)
  walk [] FB.bnil () tl ss is ts pre inv u fr
  -- D274: an FFI declaration extends Σ; the table is unchanged.
  walk {csc} {Parser.e-fun fi ∷ es} (ffi {fi = fi} {ty = ty} ep et c h g rest) (FB.bffi {ty = ty′} ep′ et′ ec eh eg rest-b) mi tl ss is ts pre inv u fr
    with just-injective (trans (sym et) et′)
  ... | refl = walk rest rest-b mi tl (s-ffi c h (u (here refl)) ss) is ts pre
                 (inv-sig {x = funName fi} {ty = ty} {k = c} {h = h} {m = u (here refl)} inv)
                 (λ m → u (there m)) (fresh-sig {csc = csc} {fi = fi} {ty = ty} {es = es} fr)
  walk (ffi {fi = Parser.mkFunInfo x ft bd prim} refl et c h g rest) (FB.bcons () rf fc eg ce cf rest-b) mi tl ss is ts pre inv u fr
  walk {csc} {Parser.e-poly pfi ∷ es} (poly {pfi = pfi} {Ψ = SCx.[]} pr D rest) (FB.bpoly fc ce rest-b) mi tl ss is ts pre inv u fr =
    walk rest rest-b mi _ ss (wkI is) (t-def zero refl (wkT ts)) pre
         (inv-poly D inv (fresh-head {csc = csc} {e = Parser.e-poly pfi} {es = es} fr)) u
         (fresh-poly {csc = csc} {pfi = pfi} {es = es} fr)
  walk (mono {fi = Parser.mkFunInfo x ft bd prim} {ty = ty} {Ψ = SCx.[]} refl er pr g D rest)
       (FB.bcons {ty = ty′} {Ψ = SCx.[]} {irFun = irFun} refl rf fc eg ce cf rest-b) mi tl ss is ts pre inv u fr
    with inj₂-injective (trans (sym er) rf)
  ... | refl = walk-mono er pr g D rest cf rest-b mi tl ss is ts pre inv u fr
                 (bare x ≟ᶜ bare "main") (ty <:? EffUU)

  walk-mono : ∀ {csc es x ft bd ty} (er : C.resolveFunType (C.ctop csc) (C.cpolys csc) ft bd ≡ inj₂ ty)
                (pr : PrincipalAt (ctxOf (AS.scopeOf csc)) bd ty)
                (g : RigidFree ty) (D : MonoBody ft (ctxOf (AS.scopeOf csc)) bd ty SCx.[])
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
                     (toProgram tl ss is ts (mono {fi = Parser.mkFunInfo x ft bd false} {Ψ = SCx.[]} refl er pr g D rest) mi u)
  walk-mono {csc} {es} {ft = ft} {bd} er pr g D rest cf rest-b (inj₁ (refl , p)) {S = S} tl ss is ts pre inv u ((hd ∷ _) , _) nd′ td =
    here-main {S = S} {csc} {tl} {ss} {is} {ts} {pre} {ft} {bd} p D cf {es} rest rest-b inv u hd nd′ td
  walk-mono {x = x} {ty = ty} er pr g D rest cf rest-b (inj₂ mi′) tl ss is ts pre inv u fr nd′ td =
    walk-mono-d g D rest cf rest-b mi′ tl ss is ts pre inv u fr (x Str.≟ "main") (ty <:? EffUU) nd′ td

  walk-mono-d : ∀ {csc es x ft bd ty}
                (g : RigidFree ty) (D : MonoBody ft (ctxOf (AS.scopeOf csc)) bd ty SCx.[])
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
  walk-mono-d {csc} {es} {ft = ft} {bd} g D rest cf rest-b mi′ {S = S} tl ss is ts pre inv u ((hd ∷ _) , _) (yes refl) (yes p) nd′ td =
    here-main {S = S} {csc} {tl} {ss} {is} {ts} {pre} {ft} {bd} p D cf {es} rest rest-b inv u hd nd′ td
  -- a second `main` would have the first one's name
  walk-mono-d g D rest cf rest-b mi′ tl ss is ts pre inv u ((hd ∷ _) , _) (yes refl) (no _) nd′ td =
    ⊥-elim (not-in hd (mainIn-name rest mi′))
  -- not `main`: the entry joins the table and the telescope
  {-# CATCHALL #-}
  walk-mono-d g D rest cf rest-b mi′ tl ss is ts pre inv u fr (no ¬q) tc (yes e) td =
    ⊥-elim (¬q (MIF.bare-injective e))
  {-# CATCHALL #-}
  walk-mono-d {csc} {es} {x} {ft} {bd} {ty} g D rest {irFun} cf rest-b mi′ tl ss is ts pre inv u fr (no ¬q) tc (no _) td =
    walk rest rest-b mi′ _ ss (impDefs (x Str.== "main") is) (wkT ts)
         (irFunOf (C.mkCompiledFun (bare x) ty irFun) ∷ pre)
         (inv-mono {fi = Parser.mkFunInfo x ft bd false} {ty = ty} D {irFun = irFun} cf inv
                   (fresh-head {csc = csc} {e = Parser.e-fun (Parser.mkFunInfo x ft bd false)} {es = es} fr)) u
         (fresh-fun {csc = csc} {fi = Parser.mkFunInfo x ft bd false} {ty = ty} {es = es} fr)
