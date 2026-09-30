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
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.Type using (Type)
open import Once.Type.DecEq using (_≟T_)
open import Once.Type.Rigid using (RigidFree)
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
open import Once.Spec.Core.Schema using (schemaOf; kindsOf)
open import Once.Spec.Core.Translate using (ImpSig; TeleSig; i-ffi; i-def; t-def; wkI; wkT; SigCF; toProgram; viewOf;
  monoHere; monoElab; monoBody; monoSchema; monoSg; polyElab; polyBody; polySg)
import Once.Spec.Core.Abstract as A
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
open import Once.Adequacy.MeaningRelation fmt using (RelT; RelT-bind)
open import Once.Denotation.TraceMonad using (T; projTrace)
open import Once.Adequacy.TeleEnvLemmas fmt using (σW)

------------------------------------------------------------------------
-- Position predicates
------------------------------------------------------------------------

-- Later table entries do not shadow a name in scope.
NoShadow : List IRFun → C.FunCtx → Set
NoShadow later imps = All (λ e → All (λ p → fname e ≢ bare (proj₁ p)) imps) later

-- A declaration-import map that agrees with the scope's telescope entries.
IAgree : (String → Imports) → List (C.PolyFunInfo × C.FunCtx) → Set
IAgree I tele = All (λ q → I (pfunName (proj₁ q)) ≡ proj₂ q) tele

-- THE INVARIANT at a position of the walk.
record Inv {s} {S : Sig s} (csc : C.CScope) (tl : Tele S) (is : ImpSig S (C.CScope.cimps csc))
           (ts : TeleSig S (C.telePolys (C.CScope.ctele csc))) (pre : List IRFun) : Set where
  field
    valid : CE.DefsValid fmt S (teleSem fmt tl) is
    iself : IAgree (C.declImps (C.CScope.ctele csc)) (C.CScope.ctele csc)
    rel   : ∀ (later : List IRFun) → NoShadow later (C.CScope.cimps csc)
          → ∀ (I : String → Imports) → IAgree I (C.CScope.ctele csc) → ∀ (uf : Imports)
          → MB.MRel fmt (σW (later ++ pre) (C.cpolys csc) I uf) (ctxOf (AS.scopeOf csc))
                    (CE.envOf fmt S (teleSem fmt tl) is ts)

-- The remaining entries' names: distinct, and new to the scope.
entryName : C.Entry → String
entryName (C.e-fun fi)   = funName fi
entryName (C.e-poly pfi) = pfunName pfi

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

postulate
  inv-ffi : ∀ {s} {S : Sig s} {csc tl is ts pre} {fi : C.FunInfo} {ty : Type} {c : IsConcrete ty}
              {h : HonestFFI ty} {g : RigidFree ty}
          → Inv {S = S} csc tl is ts pre → All (funName fi ≢_) (scopeNames csc)
          → Inv (C.extendScope csc (funName fi) ty) tl (i-ffi h g is) ts (irFunOf (FB.primCF fi ty c) ∷ pre)

  inv-poly : ∀ {s} {S : Sig s} {csc tl is ts pre} (sg : SigCF S) {pfi : C.PolyFunInfo} {Ψ : Ctx.Usage 0}
               (D : ctxOf (AS.scopeOf csc) ⊢ᶜ pfunBody pfi ∶ rigidOf (pfunType pfi) ⨾ Ψ)
           → Inv {S = S} csc tl is ts pre → All (pfunName pfi ≢_) (scopeNames csc)
           → Inv (C.addEntry csc pfi)
                 (def tl (schemaOf (pfunType pfi))
                         (A.absTm S (kindsOf (pfunType pfi)) (proj₁ (polyElab {S = S} {sc = AS.scopeOf csc} {pfi = pfi} {Ψ = Ψ} is ts D)))
                         (polyBody {S = S} {sc = AS.scopeOf csc} {pfi = pfi} {Ψ = Ψ} is ts sg D))
                 (wkI is) (t-def zero refl (wkT ts)) pre

  inv-mono : ∀ {s} {S : Sig s} {csc tl is ts pre} (sg : SigCF S) {fi : C.FunInfo} {ty : Type} {g : RigidFree ty}
               {Ψ : Ctx.Usage 0} (D : ctxOf (AS.scopeOf csc) ⊢ᶜ funBody fi ∶ ty ⨾ Ψ)
               {irFun : IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋}
           → C.compileFun C.Heap false (C.CScope.cimps csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
               (funName fi) ty (funBody fi) ≡ Data.Sum.inj₂ irFun
           → funName fi ≢ "main"
           → Inv {S = S} csc tl is ts pre → All (funName fi ≢_) (scopeNames csc)
           → Inv (C.extendScope csc (funName fi) ty)
                 (def tl (monoSchema ty) (A.absTm S noKinds (proj₁ (monoElab {S = S} {sc = AS.scopeOf csc} {fi = fi} is ts D)))
                         (monoBody {S = S} {sc = AS.scopeOf csc} {fi = fi} is ts sg g D))
                 (i-def zero refl (wkI is)) (wkT ts)
                 (irFunOf (C.mkCompiledFun (bare (funName fi)) ty irFun false) ∷ pre)

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
  sym (proj₁ (RelT-bind {EffUU} {Once.Type.Unit} relAF (λ rv → rv {tt} {tt} tt) n))
  where
    σ  = σW (later ++ pre) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) (("main" , EffUU) ∷ C.CScope.cimps csc)
    δ  = teleSem fmt tl
    V  = viewOf {S = S} is ts
    Dc = proj₂ (ElabM.elabᶜ S V D)
    relA : RelT EffUU (MeaningM.⟦_⟧ᶜ D fmt (CE.envOf fmt S δ is ts) tt) (SD.⟦ realize D ⟧ˢ fmt σ tt)
    relA = MB.bridge-c fmt σ D {dγ₁ = tt} {dγ₂ = tt} (MB.mk↾ tt)
             (Inv.rel inv later ns (C.declImps (C.CScope.ctele csc)) (Inv.iself inv) (("main" , EffUU) ∷ C.CScope.cimps csc))
    eqB : MeaningM.⟦_⟧ᶜ D fmt (CE.envOf fmt S δ is ts) tt ≡ GM.⟦_⟧ S Dc fmt δ tt
    eqB = CMB.bridge-c fmt S {δ = δ} V (CE.agree fmt S δ is ts (Inv.valid inv)) D tt
    relAF : RelT EffUU (GM.⟦_⟧ S (PT.instantiate S noVars _ (A.abs-⊢ S noKinds sg Dc)) fmt δ tt) (SD.⟦ realize D ⟧ˢ fmt σ tt)
    relAF = subst (λ m → RelT EffUU m (SD.⟦ realize D ⟧ˢ fmt σ tt))
                  (trans eqB (CAS.rt-sem S noKinds noVars _ sg Dc fmt δ)) relA

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
           (sg : SigCF S) (pre : List IRFun) → Inv csc tl is ts pre → Fresh csc es
       → ∀ n → ME.runMainˢ (σMain b bme pre) (proj₂ (MC.mainRealized-go mt mi)) n ≡ runProgram fmt (toProgram tl is ts sg mt mi) n
  walk [] FB.bnil () bme tl is ts sg pre inv fr n
  walk {csc} {C.e-fun fi ∷ es} (ffi {fi = fi} {ty = ty} ep et c h g rest) (FB.bffi {ty = ty′} {c = c′} ep′ et′ ec eh eg rest-b) mi bme tl is ts sg pre inv fr n
    with just-injective (trans (sym et) et′)
  ... | refl = walk rest rest-b mi bme tl (i-ffi h g is) ts sg (irFunOf (FB.primCF fi ty c′) ∷ pre)
                 (inv-ffi {fi = fi} {ty = ty} {c = c′} {h = h} {g = g} inv (fresh-head {csc = csc} {e = C.e-fun fi} {es = es} fr))
                 (fresh-fun {csc = csc} {fi = fi} {ty = ty} {es = es} fr) n
  walk (ffi {fi = C.mkFunInfo x ft bd prim} refl et c h g rest) (FB.bcons () rf eg ce cf rest-b) mi bme tl is ts sg pre inv fr n
  walk {csc} {C.e-poly pfi ∷ es} (poly {pfi = pfi} {Ψ = Ctx.Usage.[]} D rest) (FB.bpoly ce rest-b) mi bme tl is ts sg pre inv fr n =
    walk rest rest-b mi bme _ (wkI is) (t-def zero refl (wkT ts)) (polySg sg pfi) pre
         (inv-poly sg D inv (fresh-head {csc = csc} {e = C.e-poly pfi} {es = es} fr))
         (fresh-poly {csc = csc} {pfi = pfi} {es = es} fr) n
  walk (mono {fi = C.mkFunInfo x ft bd prim} {ty = ty} {Ψ = Ctx.Usage.[]} refl er g D rest)
       (FB.bcons {ty = ty′} {Ψ = Ctx.Usage.[]} {irFun = irFun} refl rf eg ce cf rest-b) mi bme tl is ts sg pre inv fr n
    with inj₂-injective (trans (sym er) rf)
  ... | refl = walk-mono er g D rest rf eg ce cf rest-b mi bme tl is ts sg pre inv fr n

  walk-mono : ∀ {csc es x ft bd ty} (er : C.resolveFunType (C.CScope.cimps csc) (C.cpolys csc) ft bd ≡ inj₂ ty)
                (g : RigidFree ty) (D : ctxOf (AS.scopeOf csc) ⊢ᶜ bd ∶ ty ⨾ Ctx.Usage.[])
                (rest : ModTele (AS.scopeOf (C.extendScope csc x ty)) es)
                (rf : C.resolveFunType (C.CScope.cimps csc) (C.cpolys csc) ft bd ≡ inj₂ ty) {g′ : RigidFree ty} eg
                {se d f} ce {irFun} cf (rest-b : FB.FunBundle (C.extendScope csc x ty) es)
                (mi : ((x ≡ "main") × (ty ≡ EffUU)) ⊎ MainIn rest)
                (bme : ((x ≡ "main") × (false ≡ false) × (ty ≡ EffUU)) ⊎ FB.BMainExists rest-b)
                {s} {S : Sig s} (tl : Tele S) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
                (sg : SigCF S) (pre : List IRFun) → Inv csc tl is ts pre → Fresh csc (C.e-fun (C.mkFunInfo x ft bd false) ∷ es)
            → ∀ n → ME.runMainˢ (σMain (FB.bcons {fi = C.mkFunInfo x ft bd false} {Ψ = Ctx.Usage.[]} {se = se} {d = d} {f = f}
                                          {irFun = irFun} refl rf {g′} eg ce cf rest-b) bme pre)
                                 (proj₂ (MC.mainRealized-go (mono {fi = C.mkFunInfo x ft bd false} {Ψ = Ctx.Usage.[]} refl er g D rest) mi)) n
                  ≡ runProgram fmt (toProgram tl is ts sg (mono {fi = C.mkFunInfo x ft bd false} {Ψ = Ctx.Usage.[]} refl er g D rest) mi) n
  walk-mono {csc} {es} {ft = ft} {bd} er g D rest rf {g′} eg {se} {d} {f} ce {irFun} cf rest-b (inj₁ (refl , refl)) bme tl is ts sg pre inv fr n =
    trans (run-at (realize D) n (σ-at (table-here {csc = csc} {es = es} {ft = ft} {bd = bd} irFun (FB.bundle→compiled rest-b) pre)
                                      (msc-here {csc = csc} {es = es} {ft = ft} {bd = bd} {se = se} {d = d} {f = f} {irFun = irFun}
                                                {rf = rf} {g = g′} {eg = eg} {ce = ce} {cf = cf} rest-b bme)))
          (here-main sg {fi = C.mkFunInfo "main" ft bd false} D (FB.bundle→compiled rest-b) _ refl rest-b refl inv fr n)
  walk-mono {csc} {es} {x} {ft} {bd} {ty} er g D rest rf eg ce cf rest-b (inj₂ mi′) bme tl is ts sg pre inv fr n =
    walk-mono-d er g D rest rf eg ce cf rest-b mi′ bme tl is ts sg pre inv fr (x ≟str "main") (ty ≟T EffUU) n

  walk-mono-d : ∀ {csc es x ft bd ty} (er : C.resolveFunType (C.CScope.cimps csc) (C.cpolys csc) ft bd ≡ inj₂ ty)
                (g : RigidFree ty) (D : ctxOf (AS.scopeOf csc) ⊢ᶜ bd ∶ ty ⨾ Ctx.Usage.[])
                (rest : ModTele (AS.scopeOf (C.extendScope csc x ty)) es)
                (rf : C.resolveFunType (C.CScope.cimps csc) (C.cpolys csc) ft bd ≡ inj₂ ty) {g′ : RigidFree ty} eg
                {se d f} ce {irFun} cf (rest-b : FB.FunBundle (C.extendScope csc x ty) es)
                (mi′ : MainIn rest)
                (bme : ((x ≡ "main") × (false ≡ false) × (ty ≡ EffUU)) ⊎ FB.BMainExists rest-b)
                {s} {S : Sig s} (tl : Tele S) (is : ImpSig S (C.CScope.cimps csc)) (ts : TeleSig S (C.telePolys (C.CScope.ctele csc)))
                (sg : SigCF S) (pre : List IRFun) → Inv csc tl is ts pre → Fresh csc (C.e-fun (C.mkFunInfo x ft bd false) ∷ es)
              → (nd : Dec (x ≡ "main")) (td : Dec (ty ≡ EffUU))
              → ∀ n → ME.runMainˢ (σMain (FB.bcons {fi = C.mkFunInfo x ft bd false} {Ψ = Ctx.Usage.[]} {se = se} {d = d} {f = f}
                                            {irFun = irFun} refl rf {g′} eg ce cf rest-b) bme pre)
                                   (proj₂ (MC.mrg-dispatch {sc = AS.scopeOf csc} {fi = C.mkFunInfo x ft bd false} {es = es} D {rest} mi′ nd td)) n
                    ≡ runProgram fmt (Once.Spec.Core.Translate.monoDispatch {S = S} {sc = AS.scopeOf csc} {fi = C.mkFunInfo x ft bd false}
                                        {ty = ty} {Ψ = Ctx.Usage.[]} tl is ts sg g D rest mi′ nd td) n
  -- `main`, found by the bundle's own witness
  walk-mono-d {csc} {es} {ft = ft} {bd} er g D rest rf {g′} eg {se} {d} {f} ce {irFun} cf rest-b mi′ (inj₁ (refl , refl , refl)) tl is ts sg pre inv fr (yes refl) (yes refl) n =
    trans (run-at (realize D) n (σ-at (table-here {csc = csc} {es = es} {ft = ft} {bd = bd} irFun (FB.bundle→compiled rest-b) pre)
                                      (msc-here {csc = csc} {es = es} {ft = ft} {bd = bd} {se = se} {d = d} {f = f} {irFun = irFun}
                                                {rf = rf} {g = g′} {eg = eg} {ce = ce} {cf = cf} rest-b (inj₁ (refl , refl , refl)))))
          (here-main sg {fi = C.mkFunInfo "main" ft bd false} D (FB.bundle→compiled rest-b) _ refl rest-b refl inv fr n)
  walk-mono-d er g D rest rf eg ce cf rest-b mi′ (inj₁ (p , _ , e)) tl is ts sg pre inv fr (yes _) (no ¬t) n = ⊥-elim (¬t e)
  walk-mono-d er g D rest rf eg ce cf rest-b mi′ (inj₁ (p , _ , e)) tl is ts sg pre inv fr (no ¬q) td n = ⊥-elim (¬q p)
  -- `main`, found by the dispatch
  walk-mono-d {csc} {es} {ft = ft} {bd} er g D rest rf {g′} eg {se} {d} {f} ce {irFun} cf rest-b mi′ (inj₂ w) tl is ts sg pre inv fr (yes refl) (yes refl) n =
    trans (run-at (realize D) n (σ-at (table-here {csc = csc} {es = es} {ft = ft} {bd = bd} irFun (FB.bundle→compiled rest-b) pre)
                                      (msc-here {csc = csc} {es = es} {ft = ft} {bd = bd} {se = se} {d = d} {f = f} {irFun = irFun}
                                                {rf = rf} {g = g′} {eg = eg} {ce = ce} {cf = cf} rest-b (inj₂ w))))
          (here-main sg {fi = C.mkFunInfo "main" ft bd false} D (FB.bundle→compiled rest-b) _ refl rest-b refl inv fr n)
  -- a second `main` would have the first one's name
  walk-mono-d er g D rest rf eg ce cf rest-b mi′ (inj₂ w) tl is ts sg pre inv ((hd ∷ _) , _) (yes refl) (no _) n =
    ⊥-elim (not-in hd (mainIn-name rest mi′))
  -- not `main`: the entry joins the table and the telescope
  walk-mono-d {csc} {es} {x} {ft} {bd} {ty} er g D rest rf eg ce {irFun} cf rest-b mi′ (inj₂ w) tl is ts sg pre inv fr (no ¬q) td n =
    trans (run-at (proj₂ (MC.mainRealized-go rest mi′)) n
             (σ-at′ (table-other x ft bd ty irFun (FB.bundle→compiled rest-b) pre ¬q)
                    (msc-next {csc = csc} {es = es} {ft = ft} {bd = bd} rest-b w (x ≟str "main") (ty ≟T EffUU) ¬q)))
          (walk rest rest-b mi′ w _ (i-def zero refl (wkI is)) (wkT ts) (monoSg sg g)
                (irFunOf (C.mkCompiledFun (bare x) ty irFun false) ∷ pre)
                (inv-mono sg {fi = C.mkFunInfo x ft bd false} {ty = ty} {g = g} D {irFun = irFun} cf ¬q inv (fresh-head {csc = csc} {e = C.e-fun (C.mkFunInfo x ft bd false)} {es = es} fr))
                (fresh-fun {csc = csc} {fi = C.mkFunInfo x ft bd false} {ty = ty} {es = es} fr) n)
    where
      σ-at′ : ∀ {tbl tbl′ : List IRFun} {msc msc′ : C.CScope} → tbl ≡ tbl′ → msc ≡ msc′
            → σW tbl (C.cpolys msc) (C.declImps (C.CScope.ctele msc)) (("main" , EffUU) ∷ C.CScope.cimps msc)
              ≡ σW tbl′ (C.cpolys msc′) (C.declImps (C.CScope.ctele msc′)) (("main" , EffUU) ∷ C.CScope.cimps msc′)
      σ-at′ refl refl = refl
