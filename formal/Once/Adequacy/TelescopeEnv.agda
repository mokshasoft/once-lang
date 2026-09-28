-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.TelescopeEnv — plan 0.103 phase 1c: THE TELESCOPE LEMMA.
--
-- The specification's telescope environment (each ground entry's meaning,
-- from its declaration-time derivation, `MainMeaning.defMeanings`) is related
-- entry by entry to the environment of the linked references' surface
-- meanings (`ResolveFaithful.σR`) — the premise `EnvRelTop` of the main
-- bridge.
--
-- By recursion on the telescope. A linked reference means the linked body of
-- the entry `lookupPolyPrefix` finds, elaborated in that entry's declaration
-- context (`resolveExpr` links there), so it depends on the telescope only
-- through the lookup (`σR-lookup`). The head entry's linked body is related to
-- its meaning by the substitution lemma, the agreement of elaboration with the
-- reference elaboration, derivation independence, and the bridge on the
-- entry's own derivation in its tail's environments (the recursion). The
-- tail's entries are not the head (names are distinct, `guardDistinct`), so
-- the head does not change what they link to.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.TelescopeEnv where

open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Unit using (⊤; tt)
import Data.Sum
open import Data.Empty using (⊥-elim)
open import Data.String using (String)
import Data.String.Properties as StrProp
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Induction.WellFounded using (Acc; acc)

open import Once.Postulates using (extensionality)
open import Once.Type using (Type; PolyType; Ground; extractGround)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
import Once.Surface.Syntax as Srf
import Once.Denotation.SourceDenote as SD
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (PolyCtx; lookupPolyPrefix; ctxWithImportsAndPolys)
open import Once.TypeCheck.Elaborate using (CheckElabResult; success; failure; checkElab)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr; resolveExprWF; resolvePolyCase; applySplice; Imports)
open import Once.TypeCheck.Completeness using (check-complete)
open import Once.TypeCheck.Soundness using (check-sound)
open import Once.Denotation.Realize using (realize)
open import Once.Denotation.Meaning using (DefMeanings; ⟦_⟧ᶜ)
import Once.Compile as C
open C.PolyFunInfo using (pfunName; pfunType; pfunBody; pfunAfter)
import Once.Parser.Module.Core as P
open import Once.Spec.Module using (ModuleTyped; HasValidMain-decl; PolysTyped; PolysTyped-ef; EntriesTyped)
import Once.Adequacy.ModuleComplete as MC
import Once.Adequacy.MainRealizeAgrees as MRA
import Once.Adequacy.MainMeaningBridge as MMB
import Once.Adequacy.MainForm as MF
import Once.Adequacy.MeaningBridge as MB
import Once.Adequacy.RealizeAgrees as RA
import Once.Adequacy.ResolveFaithful as RF
import Once.Adequacy.RealizeInvariant as RI
open import Once.Adequacy.NameClash using (guard-polys)
import Once.Denotation.MainMeaning as MM
open import Once.Adequacy.MeaningRelation using (RelT)

------------------------------------------------------------------------
-- The resolver does not depend on its termination witness.
------------------------------------------------------------------------

acc-irrel : ∀ {n : ℕ} (a b : Acc _<_ n) → a ≡ b
acc-irrel (acc f) (acc g) =
  cong acc (cong (λ H {y} → H y) (extensionality λ y → extensionality λ p → acc-irrel (f {y} p) (g {y} p)))

------------------------------------------------------------------------
-- A linked reference, as a function of the lookup's answer only.
------------------------------------------------------------------------

module _ (impsOf : String → Imports) (userFns : Imports) where

  spliceClosed : ∀ {A} (pre : PolyCtx) (x : String) → CheckElabResult Srf.∅ A → Srf.Expr Srf.∅ Srf.zeroUsage A
  spliceClosed {A} pre x (failure _)               = Srf.poly x A
  spliceClosed     pre x (success Srf.[] eE _ _)   = Srf.closed (resolveExpr pre impsOf userFns 0 eE)

  polyVal : (x : String) (A : Type) → Maybe (PolyType × RawExpr × PolyCtx) → Srf.Expr Srf.∅ Srf.zeroUsage A
  polyVal x A nothing                  = Srf.poly x A
  polyVal x A (just (_ , body , pre))  = spliceClosed pre x (checkElab (ctxWithImportsAndPolys (impsOf x) pre) body A)

  splice-val : ∀ (L : PolyCtx) (a : Acc _<_ (length L)) (x : String) (A : Type) {s b pre}
    (eq : lookupPolyPrefix L x ≡ just (s , b , pre)) (r : CheckElabResult Srf.∅ A)
    → applySplice {Γ = Srf.∅} L a impsOf userFns 0 x A eq r ≡ spliceClosed pre x r
  splice-val L a x A eq (failure _) = refl
  splice-val L (acc rec) x A {pre = pre} eq (success Srf.[] eE _ _) =
    cong (λ z → Srf.closed (resolveExprWF pre z impsOf userFns 0 eE)) (acc-irrel _ _)

  case-val : ∀ (L : PolyCtx) (a : Acc _<_ (length L)) (x : String) (A : Type)
    (look : Maybe _) (eq : lookupPolyPrefix L x ≡ look)
    → resolvePolyCase {Γ = Srf.∅} L a impsOf userFns 0 x A look eq ≡ polyVal x A look
  case-val L a x A nothing eq = refl
  case-val L a x A (just (s , body , pre)) eq =
    splice-val L a x A eq (checkElab (ctxWithImportsAndPolys (impsOf x) pre) body A)

module _ (fmt : TargetNum) (impsOf : String → Imports) (userFns : Imports) where

  σR-lookup : ∀ (L : PolyCtx) (x : String) (A : Type)
    → RF.σR fmt L impsOf userFns 0 x A ≡ SD.⟦ polyVal impsOf userFns x A (lookupPolyPrefix L x) ⟧ˢ fmt (RF.σ₀ fmt) tt
  σR-lookup L x A = cong (λ e → SD.⟦ e ⟧ˢ fmt (RF.σ₀ fmt) tt)
                         (case-val impsOf userFns L (<-wellFounded (length L)) x A (lookupPolyPrefix L x) refl)

  lookup-skip : ∀ (n : String) {s b} (L : PolyCtx) (y : String) → n ≢ y
    → lookupPolyPrefix ((n , s , b) ∷ L) y ≡ lookupPolyPrefix L y
  lookup-skip n L y n≢y with n StrProp.≟ y
  ... | yes p = ⊥-elim (n≢y p)
  ... | no _  = refl

  lookup-head : ∀ (n : String) {s b} (L : PolyCtx)
    → lookupPolyPrefix ((n , s , b) ∷ L) n ≡ just (s , b , L)
  lookup-head n L with n StrProp.≟ n
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  σR-skip : ∀ (n : String) {s b} (L : PolyCtx) (y : String) (A : Type) → n ≢ y
    → RF.σR fmt ((n , s , b) ∷ L) impsOf userFns 0 y A ≡ RF.σR fmt L impsOf userFns 0 y A
  σR-skip n {s} {b} L y A n≢y =
    trans (σR-lookup ((n , s , b) ∷ L) y A)
          (trans (cong (λ l → SD.⟦ polyVal impsOf userFns y A l ⟧ˢ fmt (RF.σ₀ fmt) tt) (lookup-skip n L y n≢y))
                 (sym (σR-lookup L y A)))

  --------------------------------------------------------------------
  -- Transporting the environment relation between surface environments
  -- that agree on the telescope's names.
  --------------------------------------------------------------------

  AgreeOn : SD.DefsSem → SD.DefsSem → List C.PolyFunInfo → Set
  AgreeOn σ₁ σ₂ pfis = All (λ q → ∀ A → σ₁ (pfunName q) A ≡ σ₂ (pfunName q) A) pfis

  envrel-transport : ∀ (σ₁ σ₂ : SD.DefsSem) (pfis : List C.PolyFunInfo) {ρ : DefMeanings (C.buildPolyCtx pfis)}
    → AgreeOn σ₁ σ₂ pfis → MB.EnvRel fmt σ₁ (C.buildPolyCtx pfis) ρ → MB.EnvRel fmt σ₂ (C.buildPolyCtx pfis) ρ
  envrel-transport σ₁ σ₂ []           _          _        = tt
  envrel-transport σ₁ σ₂ (q ∷ pfis) {ρ = e , ρ} (h ∷ hs) (r , rs) =
    (λ g → subst (RelT fmt (extractGround (pfunType q) g) (e g)) (h (extractGround (pfunType q) g)) (r g))
    , envrel-transport σ₁ σ₂ pfis hs rs

  skip-all : ∀ (q : C.PolyFunInfo) (pfis : List C.PolyFunInfo)
    → All (λ p → pfunName q ≢ pfunName p) pfis
    → AgreeOn (RF.σR fmt (C.buildPolyCtx (q ∷ pfis)) impsOf userFns 0) (RF.σR fmt (C.buildPolyCtx pfis) impsOf userFns 0) pfis
  skip-all q []           []         = []
  skip-all q (p ∷ pfis) (n≢ ∷ n≢s) =
    (λ A → σR-skip (pfunName q) (C.buildPolyCtx (p ∷ pfis)) (pfunName p) A n≢)
    ∷ skip-all′ pfis n≢s
    where
      skip-all′ : ∀ (ps : List C.PolyFunInfo) → All (λ p′ → pfunName q ≢ pfunName p′) ps
        → All (λ r → ∀ A → RF.σR fmt (C.buildPolyCtx (q ∷ p ∷ pfis)) impsOf userFns 0 (pfunName r) A
                          ≡ RF.σR fmt (C.buildPolyCtx (p ∷ pfis)) impsOf userFns 0 (pfunName r) A) ps
      skip-all′ []       []         = []
      skip-all′ (r ∷ rs) (n≢r ∷ ns) =
        (λ A → σR-skip (pfunName q) (C.buildPolyCtx (p ∷ pfis)) (pfunName r) A n≢r) ∷ skip-all′ rs ns

  --------------------------------------------------------------------
  -- The recursion.
  --------------------------------------------------------------------

  module _ (at : ℕ → C.FunCtx) where

    σS : List C.PolyFunInfo → SD.DefsSem
    σS pfis = RF.σR fmt (C.buildPolyCtx pfis) impsOf userFns 0

    -- Each entry's declaration imports are what linking uses for its name.
    DeclImps : List C.PolyFunInfo → Set
    DeclImps pfis = All (λ q → impsOf (pfunName q) ≡ at (pfunAfter q)) pfis

    head-rel : ∀ (q : C.PolyFunInfo) (pfis : List C.PolyFunInfo)
      (t : (g : Ground (pfunType q)) →
           ctxWithImportsAndPolys (at (pfunAfter q)) (C.buildPolyCtx pfis) ⊢ᶜ pfunBody q
             ∶ extractGround (pfunType q) g ⨾ Srf.zeroUsage)
      (ts : EntriesTyped at pfis)
      → impsOf (pfunName q) ≡ at (pfunAfter q)
      → MB.EnvRel fmt (σS pfis) (C.buildPolyCtx pfis) (MM.defMeanings fmt at pfis ts)
      → ∀ (g : Ground (pfunType q))
      → RelT fmt (extractGround (pfunType q) g)
             (⟦ t g ⟧ᶜ fmt (MM.defMeanings fmt at pfis ts) tt)
             (σS (q ∷ pfis) (pfunName q) (extractGround (pfunType q) g))
    head-rel q pfis t ts ieq er g
      with check-complete (t g)
    ... | eE , d , f , ce =
      subst (RelT fmt Tg (⟦ t g ⟧ᶜ fmt ρT tt)) (sym chain)
        (MB.bridge-c fmt (σS pfis) (t g) {dγ₁ = tt} {dγ₂ = tt} (MB.mk↾ tt) er)
      where
        Tg   = extractGround (pfunType q) g
        ρT   = MM.defMeanings fmt at pfis ts
        ctx  = ctxWithImportsAndPolys (at (pfunAfter q)) (C.buildPolyCtx pfis)
        -- the linked reference is the entry's declaration-context elaboration
        linked : σS (q ∷ pfis) (pfunName q) Tg
               ≡ SD.⟦ resolveExpr (C.buildPolyCtx pfis) impsOf userFns 0 eE ⟧ˢ fmt (RF.σ₀ fmt) tt
        linked =
          trans (σR-lookup (C.buildPolyCtx (q ∷ pfis)) (pfunName q) Tg)
            (trans (cong (λ l → SD.⟦ polyVal impsOf userFns (pfunName q) Tg l ⟧ˢ fmt (RF.σ₀ fmt) tt)
                         (lookup-head (pfunName q) (C.buildPolyCtx pfis)))
                   (cong (λ r → SD.⟦ spliceClosed impsOf userFns (C.buildPolyCtx pfis) (pfunName q) r ⟧ˢ fmt (RF.σ₀ fmt) tt)
                         (trans (cong (λ im → checkElab (ctxWithImportsAndPolys im (C.buildPolyCtx pfis)) (pfunBody q) Tg) ieq)
                                ce)))
        chain : σS (q ∷ pfis) (pfunName q) Tg ≡ SD.⟦ realize (t g) ⟧ˢ fmt (σS pfis) tt
        chain =
          trans linked
            (trans (RF.T-ext-at fmt (RF.resolveExpr-faithful fmt (C.buildPolyCtx pfis) impsOf userFns 0 eE tt))
              (trans (RA.realize-agrees fmt (σS pfis) ctx (pfunBody q) Tg ce tt)
                     (RI.realize-invariant fmt (check-sound ctx (pfunBody q) Tg ce) (t g) (σS pfis) tt)))

    tele : ∀ (pfis : List C.PolyFunInfo) (ts : EntriesTyped at pfis)
      → AllPairs _≢_ (map pfunName pfis) → DeclImps pfis
      → MB.EnvRel fmt (σS pfis) (C.buildPolyCtx pfis) (MM.defMeanings fmt at pfis ts)
    tele []           _        _            _          = tt
    tele (q ∷ pfis) (t , ts) (hd≢ ∷ dn) (ih ∷ ihs) =
      head-rel q pfis t ts ih erT
      , envrel-transport (σS pfis) (σS (q ∷ pfis)) pfis (sym-agree (skip-all q pfis (names≢ pfis hd≢))) erT
      where
        erT = tele pfis ts dn ihs
        names≢ : ∀ (ps : List C.PolyFunInfo) → All (pfunName q ≢_) (map pfunName ps) → All (λ p → pfunName q ≢ pfunName p) ps
        names≢ []       []       = []
        names≢ (p ∷ ps) (h ∷ hs) = h ∷ names≢ ps hs
        sym-agree : ∀ {σ₁ σ₂ ps} → AgreeOn σ₁ σ₂ ps → AgreeOn σ₂ σ₁ ps
        sym-agree []       = []
        sym-agree (h ∷ hs) = (λ A → sym (h A)) ∷ sym-agree hs

------------------------------------------------------------------------
-- Every entry's name links with its own declaration imports.
------------------------------------------------------------------------

afterOf-head : ∀ (q : C.PolyFunInfo) (ps : List C.PolyFunInfo) → C.afterOf (q ∷ ps) (pfunName q) ≡ pfunAfter q
afterOf-head q ps with pfunName q StrProp.≟ pfunName q
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

afterOf-skip : ∀ (q : C.PolyFunInfo) (ps : List C.PolyFunInfo) (y : String) → pfunName q ≢ y
  → C.afterOf (q ∷ ps) y ≡ C.afterOf ps y
afterOf-skip q ps y q≢y with pfunName q StrProp.≟ y
... | yes p = ⊥-elim (q≢y p)
... | no _  = refl

afterOf-own : ∀ (F : List C.PolyFunInfo) → AllPairs _≢_ (map pfunName F)
  → All (λ q → C.afterOf F (pfunName q) ≡ pfunAfter q) F
afterOf-own []       _          = []
afterOf-own (q ∷ F) (hd≢ ∷ dn) = afterOf-head q F ∷ shift F hd≢ (afterOf-own F dn)
  where
    shift : ∀ (ps : List C.PolyFunInfo) → All (pfunName q ≢_) (map pfunName ps)
      → All (λ r → C.afterOf F (pfunName r) ≡ pfunAfter r) ps
      → All (λ r → C.afterOf (q ∷ F) (pfunName r) ≡ pfunAfter r) ps
    shift []       []       []       = []
    shift (r ∷ ps) (h ∷ hs) (e ∷ es) = trans (afterOf-skip q F (pfunName r) h) e ∷ shift ps hs es

------------------------------------------------------------------------
-- The lemma at the apex.
------------------------------------------------------------------------

tele-ef : ∀ (fmt : TargetNum) (ef : String Data.Sum.⊎ (List C.FunInfo × List C.PolyFunInfo)) (pts : PolysTyped-ef ef)
  (funs : List C.FunInfo) (polys : List C.PolyFunInfo) (e : ef ≡ Data.Sum.inj₂ (funs , polys))
  (userFns : Imports) → AllPairs _≢_ (map pfunName polys)
  → MMB.EnvRelTop-ef fmt (RF.σR fmt (C.buildPolyCtx polys) (C.entryImps funs polys) userFns 0) ef pts
tele-ef fmt .(Data.Sum.inj₂ (funs , polys)) pts funs polys refl userFns dn =
  tele fmt (C.entryImps funs polys) userFns (C.funCtxAt funs C.emptyFunCtx (C.buildPolyCtx polys)) polys pts dn
    (imps (afterOf-own polys dn))
  where
    imps : ∀ {ps} → All (λ q → C.afterOf polys (pfunName q) ≡ pfunAfter q) ps
      → All (λ q → C.entryImps funs polys (pfunName q) ≡ C.funCtxAt funs C.emptyFunCtx (C.buildPolyCtx polys) (pfunAfter q)) ps
    imps []       = []
    imps (e ∷ es) = cong (C.funCtxAt funs C.emptyFunCtx (C.buildPolyCtx polys)) e ∷ imps es

telescope-envrel : ∀ (fmt : TargetNum) (m : P.Module) (mt : ModuleTyped m)
  (hvm : HasValidMain-decl m mt) (pts : PolysTyped m)
  → MMB.EnvRelTop fmt
      (MRA.σTp fmt m (proj₁ (MC.moduleToIR-complete m mt hvm pts)) (proj₂ (MC.moduleToIR-complete m mt hvm pts)))
      m pts
telescope-envrel fmt (P.mkModule ds) mt hvm pts =
  tele-ef fmt (C.extractFunctions (C.extractAliases (P.mkModule ds)) (P.mkModule ds)) pts funs polys ef-eq
    (("main" , _) ∷ mctx)
    (guard-polys (C.extractFunctions-go (C.extractAliases (P.mkModule ds)) ds nothing) ef-eq)
  where
    node  = MF.main-node-of fmt (P.mkModule ds) (proj₁ (MC.moduleToIR-complete (P.mkModule ds) mt hvm pts))
                                                (proj₂ (MC.moduleToIR-complete (P.mkModule ds) mt hvm pts))
    funs  = proj₁ node
    polys = proj₁ (proj₂ node)
    ef-eq = proj₁ (proj₂ (proj₂ node))
    mctx  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ node)))))
