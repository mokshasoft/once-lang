-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.FormSound — the checker's reading of an expression's form
-- is the Spec's classes (plan 0.151).
--
-- The checker decides a resolved name's kind (`polyKind`: an own polymorphic
-- definition, and whether its domain fixes its instance) and the forms that
-- give a domain-given type (`synthForm?`, `domainForm?`) from the scope's
-- lookups. At a scope's Pack they are the Spec's `PolyName`,
-- `PolyFromDomain`, `SynthForm` and `DomainForm`: an answer `true` with the
-- expression's derivation in hand, an answer `false` outright. A name's
-- negative facts come from the names' distinctness (`Pack.nm-inj`).
------------------------------------------------------------------------

module Once.TypeCheck.FormSound where

open import Data.Bool using (true; false; _∧_; _∨_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_<_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Once.Spec.Name using (canonical; own)
import Once.Spec.Surface.Syntax as Raw
import Once.Spec.Surface.Generators as G
import Once.Spec.Surface.Typing as SUT
import Once.Spec.Core.Syntax as SC
import Once.Spec.Type as ST
import Once.Type.Poly as TP
import Once.Type
open import Once.Type.Determined using (arrowSchema?; codVarsInDom?)
open import Once.Generators using (fromDomain?; fromCodomain?)
open import Once.TypeCheck.Scope
  using (NamedCtx; lookupImport; lookupPolyPrefix; headView; gk-map; gk-const; gk-comb₁; gk-comb₂; genKindView)
open NamedCtx
open import Once.TypeCheck.Elaborate
  using (not-poly; poly-other; polyKind; polyKind-own; polyKind-a;
         synthForm?; domainForm?; synthApp?; domainApp?; constB; isYesB;
         notPolyB; domPolyB; isGround-inj₂→¬Ground)
import Once.TypeCheck.Elaborate as E
open import Once.TypeCheck.SpecWitness using (Pack; module At; OkOf; OkSOf)
import Once.TypeCheck.Use as UM
import Once.Type.Determined
open Pack
import Once.TypeCheck.View as TView
import Once.Adequacy.SpecFront.Inst as In
import Once.Metatheory.Surface.Basics

------------------------------------------------------------------------
-- Booleans
------------------------------------------------------------------------

private
  ∧-true : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-true {true} {true} _ = refl , refl
  ∧-true {true} {false} ()
  ∧-true {false} ()

  ∧-false : ∀ {a b} → a ∧ b ≡ false → a ≡ false ⊎ b ≡ false
  ∧-false {false} _ = inj₁ refl
  ∧-false {true} e = inj₂ e

  ∨-true : ∀ {a b} → a ∨ b ≡ true → a ≡ true ⊎ b ≡ true
  ∨-true {true} _ = inj₁ refl
  ∨-true {false} e = inj₂ e

  ∨-false : ∀ {a b} → a ∨ b ≡ false → a ≡ false × b ≡ false
  ∨-false {false} {false} _ = refl , refl
  ∨-false {true} ()
  ∨-false {false} {true} ()

  not-yes : ∀ {Q : Set} (d : Dec Q) → Q → not (isYesB d) ≡ true → ⊥
  not-yes (yes _) _ ()
  not-yes (no ¬q) q _ = ¬q q

  isYes-of : ∀ {P : Set} (d : Dec P) → P → isYesB d ≡ true
  isYes-of (yes _) _ = refl
  isYes-of (no ¬p) p = ⊥-elim (¬p p)

  t≢f : true ≢ false
  t≢f ()

  const-map : ∀ {k} → G.IsConstant k → G.IsMap k → ⊥
  const-map G.is-constant ()
  const-comb : ∀ {k n} → G.IsConstant k → G.IsCombinator n k → ⊥
  const-comb G.is-constant ()
  map-comb : ∀ {k n} → G.IsMap k → G.IsCombinator n k → ⊥
  map-comb G.is-map ()
  comb-12 : ∀ {k} → G.IsCombinator 1 k → G.IsCombinator 2 k → ⊥
  comb-12 G.is-combinator ()
  fc-map : ∀ {k} → G.FromCodomain k → G.IsMap k
  fc-map G.fc-codomain = G.is-map
  fc-map G.fc-both     = G.is-map

  -- An arrow schema is the one `arrowSchema?` finds.
  arrow-dec : ∀ {sc sd sco π} (as : TP.ArrowSchema sc sd sco π) → arrowSchema? sc ≡ just (sd , sco , π , as)
  arrow-dec TP.as-pure = refl
  arrow-dec TP.as-eff  = refl
  arrow-dec TP.as-act  = refl

  dom-kind : ∀ {sc sd sco π} → TP.ArrowSchema sc sd sco π → TP.CodVarsInDom sd sco → polyKind-a (arrowSchema? sc) ≡ E.poly-dom
  dom-kind {sd = sd} {sco} as inc rewrite arrow-dec as with codVarsInDom? sd sco
  ... | yes _  = refl
  ... | no ¬i  = ⊥-elim (¬i inc)

------------------------------------------------------------------------
-- At a scope's Pack
------------------------------------------------------------------------

module _ {m} {ctx : NamedCtx m} (P : Pack ctx) where
  module SU = SUT (Sg P) (S P) (nm P)
    using (CheckHead; DomainForm; Locals; OwnCheck; PartialCombinator; PolyFromDomain; PolyName
          ; SynthForm; _⊢_⇐_↝_; _⊢_⇐_⇒[_]↦_↝_; _⊢_⇒_↝_; c-ana; c-case; c-cata; c-compose-f
          ; c-compose-g; c-curry; c-lam; c-map-app; c-pair; c-pair-lit; c-poly; c-sub; ch-comb₁
          ; ch-map; ch-poly; d-case; d-cata; d-compose; d-infer; d-lam; d-map; d-pair; d-poly
          ; df-case; df-cata; df-compose; df-lam; df-map; df-pair; df-poly; df-synth; oc-map
          ; oc-pair; pc-bare; pc-one; poly; poly-dom; s-app; s-app-spine; s-const; s-pair; sf-annot
          ; sf-app; sf-binop; sf-const; sf-destruct; sf-float; sf-int; sf-let; sf-name; sf-neg
          ; sf-pair; sf-unit; sf-var; module CheckHead; module DomainForm; module OwnCheck
          ; module PartialCombinator; module SynthForm)
  open SU using (Locals; PolyName; poly; PolyFromDomain; poly-dom; SynthForm; DomainForm; OwnCheck; PartialCombinator; CheckHead)
  open SU.SynthForm
  open SU.DomainForm
  open SU.OwnCheck
  open SU.PartialCombinator
  open SU.CheckHead
  open At P using (synth-noCH)
  private
    module B = Once.Metatheory.Surface.Basics (Sg P) (S P) (nm P)
      using (module Modes)
    module BM = B.Modes (kinds ctx)
      using (noSyn-comb₁; noSyn-comb₂)
    Syn = SU._⊢_⇒_↝_ (kinds ctx)
    Dom = SU._⊢_⇐_⇒[_]↦_↝_ (kinds ctx)
    US = UM.Use⇒ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx)
    UD = UM.Use↦ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx)

  ----------------------------------------------------------------------
  -- Names
  ----------------------------------------------------------------------

  private
    name-at : ∀ {x sc b p} → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing
            → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p)) → ¬ TP.Ground sc → PolyName (own x)
    name-at ns ni lp ng = poly (TView.View.entry (V P) lp) (h-poly P lp) (h-open P lp ng)

    own-name : ∀ {x} ls → lookupImport (sig ctx) x ≡ ls → ∀ li → lookupImport (imports ctx) x ≡ li
             → ∀ lp → lookupPolyPrefix (polys ctx) x ≡ lp → polyKind-own ls li lp ≢ not-poly → PolyName (own x)
    own-name nothing ns nothing ni nothing lp ne = ⊥-elim (ne refl)
    own-name nothing ns nothing ni (just (sc , b , p)) lp ne with Once.Type.isGround sc in eG
    ... | inj₁ _  = ⊥-elim (ne refl)
    ... | inj₂ tt = name-at ns ni lp (isGround-inj₂→¬Ground sc eG)
    own-name (just _) ns _ ni _ lp ne = ⊥-elim (ne refl)
    own-name nothing ns (just _) ni _ lp ne = ⊥-elim (ne refl)

  -- A name the scope reads as polymorphic is one.
  name-of : ∀ cn → polyKind ctx cn ≢ not-poly → PolyName cn
  name-of (canonical [])          ne = ⊥-elim (ne refl)
  name-of (own x)                 ne = own-name _ refl _ refl _ refl ne
  name-of (canonical (_ ∷ _ ∷ _)) ne = ⊥-elim (ne refl)

  private
    own-dom : ∀ {x} ls → lookupImport (sig ctx) x ≡ ls → ∀ li → lookupImport (imports ctx) x ≡ li
            → ∀ lp → lookupPolyPrefix (polys ctx) x ≡ lp → polyKind-own ls li lp ≡ E.poly-dom → PolyFromDomain (own x)
    own-dom nothing ns nothing ni (just (sc , b , p)) lp e with Once.Type.isGround sc in eG
    own-dom nothing ns nothing ni (just (sc , b , p)) lp () | inj₁ _
    ... | inj₂ tt with arrowSchema? sc
    own-dom nothing ns nothing ni (just (sc , b , p)) lp () | inj₂ tt | nothing
    ... | just (sd , sco , π′ , as) with codVarsInDom? sd sco
    ...   | yes inc =
            let (X , Y , te , incl) = h-arrow P lp as inc
                ng = isGround-inj₂→¬Ground sc eG
            in poly-dom (TView.View.entry (V P) lp) (h-poly P lp) (h-open P lp ng) te incl
    own-dom nothing ns nothing ni (just (sc , b , p)) lp () | inj₂ tt | just _ | no _
    own-dom nothing ns nothing ni nothing lp ()
    own-dom (just _) ns _ ni _ lp ()
    own-dom nothing ns (just _) ni _ lp ()

    own-notdom : ∀ {x} ls → lookupImport (sig ctx) x ≡ ls → ∀ li → lookupImport (imports ctx) x ≡ li
               → ∀ lp → lookupPolyPrefix (polys ctx) x ≡ lp → polyKind-own ls li lp ≡ poly-other → ¬ PolyFromDomain (own x)
    own-notdom nothing ns nothing ni (just (sc , b , p)) lp e (SU.poly-dom d′ e′ lt′ te′ occ′)
      with P .nm-inj (trans e′ (sym (h-poly P lp)))
    ... | refl with Once.Type.isGround sc in eG
    ...   | inj₁ _  = t≢f′ e
      where t≢f′ : not-poly ≡ poly-other → ⊥
            t≢f′ ()
    ...   | inj₂ tt =
            let (sd₀ , sc₀ , as₀ , inc₀) = In.arrow-at sc _ (TView.View.entryIs (V P) lp) te′ occ′ _ refl
            in other≢dom (trans (sym e) (dom-kind as₀ inc₀))
      where other≢dom : poly-other ≡ E.poly-dom → ⊥
            other≢dom ()
    own-notdom nothing ns nothing ni nothing lp () _
    own-notdom (just _) ns _ ni _ lp () _
    own-notdom nothing ns (just _) ni _ lp () _

  dom-of : ∀ cn → polyKind ctx cn ≡ E.poly-dom → PolyFromDomain cn
  dom-of (canonical [])          ()
  dom-of (own x)                 e = own-dom _ refl _ refl _ refl e
  dom-of (canonical (_ ∷ _ ∷ _)) ()

  notdom-of : ∀ cn → polyKind ctx cn ≡ poly-other → ¬ PolyFromDomain cn
  notdom-of (canonical [])          ()
  notdom-of (own x)                 e = own-notdom _ refl _ refl _ refl e
  notdom-of (canonical (_ ∷ _ ∷ _)) ()

  -- A name that synthesizes is no polymorphic definition.
  synth-notPoly : ∀ {n} {L′ : Locals m n} {cn T t Ψ} (s : Syn L′ (Raw.RResolved cn) T t) → US s Ψ → ¬ PolyName cn
  synth-notPoly s u pn = synth-noCH s u (ch-poly pn)

  private
    notPoly-of : ∀ cn → notPolyB (polyKind ctx cn) ≡ false → polyKind ctx cn ≢ not-poly
    notPoly-of cn e ne = t≢f (trans (sym (cong notPolyB ne)) e)

    domPoly-other : ∀ cn → domPolyB (polyKind ctx cn) ≡ false → polyKind ctx cn ≡ poly-other
    domPoly-other cn e with polyKind ctx cn
    ... | not-poly   = ⊥-elim (t≢f e)
    ... | E.poly-dom = ⊥-elim (t≢f e)
    ... | poly-other = refl

    ch-pc : ∀ {f} → CheckHead f → ¬ PartialCombinator f
    ch-pc (ch-map im) (pc-bare ic)     = map-comb im ic
    ch-pc (ch-comb₁ ic) (pc-one ic′)   = comb-12 ic ic′

  ----------------------------------------------------------------------
  -- Synthesizing forms
  ----------------------------------------------------------------------

  -- An application the decider calls synthesizing is no codomain-fixed map applied.
  private
    app-noOC : ∀ f x → synthApp? f (headView f) ≡ true → ¬ OwnCheck (Raw.RApp f x)
    app-noOC _ x e (oc-map {g = g} fc) with genKindView g
    ... | gk-map _    = not-yes (fromCodomain? (G.kind g)) fc e
    ... | gk-const ic = const-map ic (fc-map fc)
    ... | gk-comb₁ ic = map-comb (fc-map fc) ic
    ... | gk-comb₂ ic = map-comb (fc-map fc) ic

    syn-noPC : ∀ {n} {L′ : Locals m n} {f x T t} → Syn L′ (Raw.RApp f x) T t → ¬ PartialCombinator f
    syn-noPC (SU.s-app pc _ _ _) = pc
    syn-noPC (SU.s-app-spine ch _ _) = ch-pc ch

  synthForm-true : ∀ {n} {L′ : Locals m n} e {T t Ψ} → synthForm? ctx e ≡ true → (s : Syn L′ e T t) → US s Ψ → SynthForm e
  synthForm-true (Raw.RInt _) _ _ _             = sf-int
  synthForm-true (Raw.RFloat _ _ _ _) _ _ _     = sf-float
  synthForm-true Raw.RUnit _ _ _                = sf-unit
  synthForm-true (Raw.RVar _) _ _ _             = sf-var
  synthForm-true (Raw.RResolved cn) _ s u       = sf-name (synth-notPoly s u)
  synthForm-true (Raw.RGen g) _ (SU.s-const {k = k} _) _ = sf-const k
  synthForm-true (Raw.RAnnot _ _) _ _ _         = sf-annot
  synthForm-true (Raw.RPair a b) e (SU.s-pair da db) (UM.u-pair ua ub) =
    let (ea , eb) = ∧-true e in sf-pair (synthForm-true a ea da ua) (synthForm-true b eb db ub)
  synthForm-true (Raw.RNeg _) _ _ _             = sf-neg
  synthForm-true (Raw.RBinOp _ _ _) _ _ _       = sf-binop
  synthForm-true (Raw.RLet _ _ _) _ _ _         = sf-let
  synthForm-true (Raw.RDestruct _ _ _ _ _) _ _ _ = sf-destruct
  synthForm-true (Raw.RApp f x) e s _           = sf-app (syn-noPC s) (app-noOC f x e)
  synthForm-true (Raw.RQualified _ _) () _ _
  synthForm-true (Raw.RLam _ _) () _ _

  private
    app-false : ∀ f x → synthApp? f (headView f) ≡ false → ¬ PartialCombinator f → ¬ OwnCheck (Raw.RApp f x) → ⊥
    app-false (Raw.RGen g) x e npc noc with genKindView g
    ... | gk-map _    = noc (oc-map (from-no (fromCodomain? (G.kind g)) e))
      where from-no : ∀ {Q : Set} (d : Dec Q) → not (isYesB d) ≡ false → Q
            from-no (yes q) _ = q
            from-no (no _) ()
    ... | gk-const _  = t≢f e
    ... | gk-comb₁ ic = npc (pc-bare ic)
    ... | gk-comb₂ ic = npc (pc-bare ic)
    app-false (Raw.RApp (Raw.RGen g) a) x e npc noc with genKindView g
    ... | gk-comb₂ ic = npc (pc-one ic)
    ... | gk-map _    = t≢f e
    ... | gk-const _  = t≢f e
    ... | gk-comb₁ _  = t≢f e
    app-false (Raw.RVar _) x () npc noc
    app-false (Raw.RQualified _ _) x () npc noc
    app-false (Raw.RResolved _) x () npc noc
    app-false (Raw.RLam _ _) x () npc noc
    app-false (Raw.RLet _ _ _) x () npc noc
    app-false (Raw.RPair _ _) x () npc noc
    app-false (Raw.RDestruct _ _ _ _ _) x () npc noc
    app-false Raw.RUnit x () npc noc
    app-false (Raw.RInt _) x () npc noc
    app-false (Raw.RFloat _ _ _ _) x () npc noc
    app-false (Raw.RAnnot _ _) x () npc noc
    app-false (Raw.RBinOp _ _ _) x () npc noc
    app-false (Raw.RNeg _) x () npc noc
    app-false (Raw.RApp (Raw.RVar _) _) x () npc noc
    app-false (Raw.RApp (Raw.RQualified _ _) _) x () npc noc
    app-false (Raw.RApp (Raw.RResolved _) _) x () npc noc
    app-false (Raw.RApp (Raw.RLam _ _) _) x () npc noc
    app-false (Raw.RApp (Raw.RLet _ _ _) _) x () npc noc
    app-false (Raw.RApp (Raw.RPair _ _) _) x () npc noc
    app-false (Raw.RApp (Raw.RDestruct _ _ _ _ _) _) x () npc noc
    app-false (Raw.RApp Raw.RUnit _) x () npc noc
    app-false (Raw.RApp (Raw.RInt _) _) x () npc noc
    app-false (Raw.RApp (Raw.RFloat _ _ _ _) _) x () npc noc
    app-false (Raw.RApp (Raw.RAnnot _ _) _) x () npc noc
    app-false (Raw.RApp (Raw.RBinOp _ _ _) _) x () npc noc
    app-false (Raw.RApp (Raw.RNeg _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RGen _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RVar _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RQualified _ _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RResolved _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RLam _ _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RLet _ _ _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RPair _ _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RDestruct _ _ _ _ _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp Raw.RUnit _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RInt _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RFloat _ _ _ _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RAnnot _ _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RBinOp _ _ _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RNeg _) _) _) x () npc noc
    app-false (Raw.RApp (Raw.RApp (Raw.RApp _ _) _) _) x () npc noc

  synthForm-false : ∀ e → synthForm? ctx e ≡ false → ¬ SynthForm e
  synthForm-false (Raw.RResolved cn) e (sf-name ¬pn) = ¬pn (name-of cn (notPoly-of cn e))
  synthForm-false (Raw.RGen g) e (sf-const ic) with genKindView g
  ... | gk-const _  = t≢f e
  ... | gk-map im   = const-map ic im
  ... | gk-comb₁ ic′ = const-comb ic ic′
  ... | gk-comb₂ ic′ = const-comb ic ic′
  synthForm-false (Raw.RPair a b) e (sf-pair sa sb) with ∧-false {synthForm? ctx a} e
  ... | inj₁ ea = synthForm-false a ea sa
  ... | inj₂ eb = synthForm-false b eb sb
  synthForm-false (Raw.RApp f x) e (sf-app npc noc) = app-false f x e npc noc
  synthForm-false (Raw.RInt _) () _
  synthForm-false (Raw.RFloat _ _ _ _) () _
  synthForm-false Raw.RUnit () _
  synthForm-false (Raw.RVar _) () _
  synthForm-false (Raw.RAnnot _ _) () _
  synthForm-false (Raw.RNeg _) () _
  synthForm-false (Raw.RBinOp _ _ _) () _
  synthForm-false (Raw.RLet _ _ _) () _
  synthForm-false (Raw.RDestruct _ _ _ _ _) () _

  ----------------------------------------------------------------------
  -- Domain-given forms
  ----------------------------------------------------------------------

  private
    -- A combinator given its arms that the decider reads as domain-given
    -- does not synthesize.
    domApp-noSyn : ∀ {n} {L′ : Locals m n} f a {T t} → domainApp? ctx f a ≡ true → ¬ Syn L′ (Raw.RApp f a) T t
    domApp-noSyn (Raw.RApp (Raw.RGen G.compose) f′) a e s = BM.noSyn-comb₂ G.is-combinator s
    domApp-noSyn (Raw.RApp (Raw.RGen G.case) f′) a e s    = BM.noSyn-comb₂ G.is-combinator s
    domApp-noSyn (Raw.RApp (Raw.RGen G.pair) f′) a e s    = BM.noSyn-comb₂ G.is-combinator s
    domApp-noSyn (Raw.RGen G.cata) a e s                   = BM.noSyn-comb₁ G.is-combinator s
    domApp-noSyn (Raw.RGen G.id) a () s
    domApp-noSyn (Raw.RGen G.compose) a () s
    domApp-noSyn (Raw.RGen G.fst) a () s
    domApp-noSyn (Raw.RGen G.snd) a () s
    domApp-noSyn (Raw.RGen G.terminal) a () s
    domApp-noSyn (Raw.RGen G.pair) a () s
    domApp-noSyn (Raw.RGen G.inl) a () s
    domApp-noSyn (Raw.RGen G.inr) a () s
    domApp-noSyn (Raw.RGen G.initial) a () s
    domApp-noSyn (Raw.RGen G.case) a () s
    domApp-noSyn (Raw.RGen G.apply) a () s
    domApp-noSyn (Raw.RGen G.curry) a () s
    domApp-noSyn (Raw.RGen G.In) a () s
    domApp-noSyn (Raw.RGen G.Out) a () s
    domApp-noSyn (Raw.RGen G.ana) a () s
    domApp-noSyn (Raw.RGen G.unit) a () s
    domApp-noSyn (Raw.RGen G.toFloat) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.id) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.fst) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.snd) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.terminal) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.inl) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.inr) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.initial) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.apply) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.curry) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.In) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.cata) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.Out) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.ana) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.unit) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RGen G.toFloat) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RVar _) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RQualified _ _) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RResolved _) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RLam _ _) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RLet _ _ _) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RPair _ _) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RDestruct _ _ _ _ _) _) a () s
    domApp-noSyn (Raw.RApp Raw.RUnit _) a () s
    domApp-noSyn (Raw.RApp (Raw.RInt _) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RFloat _ _ _ _) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RAnnot _ _) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RBinOp _ _ _) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RNeg _) _) a () s
    domApp-noSyn (Raw.RApp (Raw.RApp _ _) _) a () s
    domApp-noSyn (Raw.RVar _) a () s
    domApp-noSyn (Raw.RQualified _ _) a () s
    domApp-noSyn (Raw.RResolved _) a () s
    domApp-noSyn (Raw.RLam _ _) a () s
    domApp-noSyn (Raw.RLet _ _ _) a () s
    domApp-noSyn (Raw.RPair _ _) a () s
    domApp-noSyn (Raw.RDestruct _ _ _ _ _) a () s
    domApp-noSyn Raw.RUnit a () s
    domApp-noSyn (Raw.RInt _) a () s
    domApp-noSyn (Raw.RFloat _ _ _ _) a () s
    domApp-noSyn (Raw.RAnnot _ _) a () s
    domApp-noSyn (Raw.RBinOp _ _ _) a () s
    domApp-noSyn (Raw.RNeg _) a () s

  domainForm-true : ∀ {n} {L′ : Locals m n} e {A π B t Ψ} → domainForm? ctx e ≡ true → (d : Dom L′ e A π B t) → UD d Ψ → DomainForm e
  domainForm-true (Raw.RLam x b) e (SU.d-lam db) (UM.u-lam ub) = df-lam (synthForm-true b e db ub)
  domainForm-true (Raw.RLam x b) e (SU.d-infer () _ _) _
  domainForm-true (Raw.RResolved cn) _ (SU.d-infer s _ _) (UM.u-infer w) = df-synth (sf-name (synth-notPoly s w))
  domainForm-true (Raw.RResolved cn) _ (SU.d-poly d e lt ty oc _ _ _ _ _) _ = df-poly (poly-dom d e lt ty oc)
  domainForm-true (Raw.RGen g) _ (SU.d-map fd _ _) _ = df-map fd
  domainForm-true (Raw.RGen g) _ (SU.d-infer (SU.s-const {k = k} _) _ _) _ = df-synth (sf-const k)
  domainForm-true (Raw.RApp f a) e (SU.d-infer s _ _) (UM.u-infer w) with ∨-true {synthForm? ctx (Raw.RApp f a)} e
  ... | inj₁ es = df-synth (synthForm-true (Raw.RApp f a) es s w)
  ... | inj₂ ed = ⊥-elim (domApp-noSyn f a ed s)
  domainForm-true (Raw.RApp (Raw.RApp (Raw.RGen G.compose) f) g) e (SU.d-compose dg df) (UM.u-compose ug uf) =
    let (ef , eg) = ∧-true e in df-compose (domainForm-true f ef df uf) (domainForm-true g eg dg ug)
  domainForm-true (Raw.RApp (Raw.RApp (Raw.RGen G.case) f) g) e (SU.d-case df dg _) (UM.u-case uf ug) =
    let (ef , eg) = ∧-true e in df-case (domainForm-true f ef df uf) (domainForm-true g eg dg ug)
  domainForm-true (Raw.RApp (Raw.RApp (Raw.RGen G.pair) f) g) e (SU.d-pair df dg) (UM.u-pair uf ug) =
    let (ef , eg) = ∧-true e in df-pair (domainForm-true f ef df uf) (domainForm-true g eg dg ug)
  domainForm-true (Raw.RApp (Raw.RGen G.cata) a) e (SU.d-cata _ da _ _) (UM.u-cata ua) = df-cata (synthForm-true a e da ua)
  domainForm-true (Raw.RInt _) e (SU.d-infer s _ _) (UM.u-infer w) = df-synth (synthForm-true _ e s w)
  domainForm-true (Raw.RFloat _ _ _ _) e (SU.d-infer s _ _) (UM.u-infer w) = df-synth (synthForm-true _ e s w)
  domainForm-true Raw.RUnit e (SU.d-infer s _ _) (UM.u-infer w) = df-synth (synthForm-true _ e s w)
  domainForm-true (Raw.RVar _) e (SU.d-infer s _ _) (UM.u-infer w) = df-synth (synthForm-true _ e s w)
  domainForm-true (Raw.RAnnot _ _) e (SU.d-infer s _ _) (UM.u-infer w) = df-synth (synthForm-true _ e s w)
  domainForm-true (Raw.RPair _ _) e (SU.d-infer s _ _) (UM.u-infer w) = df-synth (synthForm-true _ e s w)
  domainForm-true (Raw.RNeg _) e (SU.d-infer s _ _) (UM.u-infer w) = df-synth (synthForm-true _ e s w)
  domainForm-true (Raw.RBinOp _ _ _) e (SU.d-infer s _ _) (UM.u-infer w) = df-synth (synthForm-true _ e s w)
  domainForm-true (Raw.RLet _ _ _) e (SU.d-infer s _ _) (UM.u-infer w) = df-synth (synthForm-true _ e s w)
  domainForm-true (Raw.RDestruct _ _ _ _ _) e (SU.d-infer s _ _) (UM.u-infer w) = df-synth (synthForm-true _ e s w)
  domainForm-true (Raw.RQualified _ _) e (SU.d-infer () _ _) _

  domainForm-false : ∀ e → domainForm? ctx e ≡ false → ¬ DomainForm e
  domainForm-false (Raw.RLam x b) e (df-lam sb) = synthForm-false b e sb
  domainForm-false (Raw.RLam x b) e (df-synth ())
  domainForm-false (Raw.RResolved cn) e (df-synth (sf-name ¬pn)) =
    ¬pn (name-of cn (λ np → t≢f (trans (sym (cong domPolyB np)) e)))
  domainForm-false (Raw.RResolved cn) e (df-poly pfd) = notdom-of cn (domPoly-other cn e) pfd
  domainForm-false (Raw.RGen g) e (df-synth sf) = synthForm-false (Raw.RGen g) (proj₁ (∨-false e)) sf
  domainForm-false (Raw.RGen g) e (df-map fd) = t≢f (trans (sym (isYes-of (fromDomain? (G.kind g)) fd)) (proj₂ (∨-false {constB (genKindView g)} e)))
  domainForm-false (Raw.RApp f a) e (df-synth sf) = synthForm-false (Raw.RApp f a) (proj₁ (∨-false e)) sf
  domainForm-false (Raw.RApp (Raw.RApp (Raw.RGen G.compose) f) g) e (df-compose df dg) with ∧-false {domainForm? ctx f} (proj₂ (∨-false {synthForm? ctx (Raw.RApp (Raw.RApp (Raw.RGen G.compose) f) g)} e))
  ... | inj₁ ef = domainForm-false f ef df
  ... | inj₂ eg = domainForm-false g eg dg
  domainForm-false (Raw.RApp (Raw.RApp (Raw.RGen G.case) f) g) e (df-case df dg) with ∧-false {domainForm? ctx f} (proj₂ (∨-false {synthForm? ctx (Raw.RApp (Raw.RApp (Raw.RGen G.case) f) g)} e))
  ... | inj₁ ef = domainForm-false f ef df
  ... | inj₂ eg = domainForm-false g eg dg
  domainForm-false (Raw.RApp (Raw.RApp (Raw.RGen G.pair) f) g) e (df-pair df dg) with ∧-false {domainForm? ctx f} (proj₂ (∨-false {synthForm? ctx (Raw.RApp (Raw.RApp (Raw.RGen G.pair) f) g)} e))
  ... | inj₁ ef = domainForm-false f ef df
  ... | inj₂ eg = domainForm-false g eg dg
  domainForm-false (Raw.RApp (Raw.RGen G.cata) a) e (df-cata sa) = synthForm-false a (proj₂ (∨-false {synthForm? ctx (Raw.RApp (Raw.RGen G.cata) a)} e)) sa
  domainForm-false (Raw.RInt _) e (df-synth sf)             = synthForm-false _ e sf
  domainForm-false (Raw.RFloat _ _ _ _) e (df-synth sf)     = synthForm-false _ e sf
  domainForm-false Raw.RUnit e (df-synth sf)                = synthForm-false _ e sf
  domainForm-false (Raw.RVar _) e (df-synth sf)             = synthForm-false _ e sf
  domainForm-false (Raw.RAnnot _ _) e (df-synth sf)         = synthForm-false _ e sf
  domainForm-false (Raw.RPair _ _) e (df-synth sf)          = synthForm-false _ e sf
  domainForm-false (Raw.RNeg _) e (df-synth sf)             = synthForm-false _ e sf
  domainForm-false (Raw.RBinOp _ _ _) e (df-synth sf)       = synthForm-false _ e sf
  domainForm-false (Raw.RLet _ _ _) e (df-synth sf)         = synthForm-false _ e sf
  domainForm-false (Raw.RDestruct _ _ _ _ _) e (df-synth sf) = synthForm-false _ e sf
  domainForm-false (Raw.RQualified _ _) e (df-synth ())

  ----------------------------------------------------------------------
  -- A checked expression: the classes from its derivation and its usage,
  -- which records the entry each name reaches (for completeness)
  ----------------------------------------------------------------------

  private
    UC = UM.Use⇐ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx)
    Chk = SU._⊢_⇐_↝_ (kinds ctx)

    polyKind-a-not : ∀ {sc} (v : Maybe (Once.Type.Determined.ArrowView sc)) → polyKind-a v ≢ not-poly
    polyKind-a-not nothing ()
    polyKind-a-not (just (sd , sco , π′ , _)) e with codVarsInDom? sd sco
    polyKind-a-not (just _) () | yes _
    polyKind-a-not (just _) () | no _

    lt0 : 0 < 0 → ⊥
    lt0 ()

    np-true : ∀ k → notPolyB k ≡ true → k ≡ not-poly
    np-true not-poly _ = refl
    np-true E.poly-dom ()
    np-true poly-other ()

  -- An entry the checker's lookups reach, with type variables, is read as polymorphic.
  ok-poly : ∀ {d c} → OkOf P d → nm P d ≡ c → 0 < SC.Schema.arity (S P SC.!! d) → polyKind ctx c ≢ not-poly
  ok-poly (TView.iv-imp ns lk refl) e pos np =
    lt0 (subst (0 <_) (cong SC.Schema.arity (TView.ImportAt.mono (TView.View.imported (V P) lk))) pos)
  ok-poly {c = c} (TView.iv-poly {x = x} {sc = sc} ns ni lp refl) e pos np
    with trans (sym e) (h-poly P lp)
  ... | refl = kind-not _ _ _ ns ni lp (λ g → lt0 (subst (0 <_) (h-ground P lp g) pos)) np
    where
      kind-not : ∀ {sc′ b p} ls li lp′ → ls ≡ nothing → li ≡ nothing → lp′ ≡ just (sc′ , b , p) → ¬ TP.Ground sc′
               → polyKind-own ls li lp′ ≢ not-poly
      kind-not {sc′ = sc′} .nothing .nothing .(just _) refl refl refl ng with Once.Type.isGround sc′
      ... | inj₁ g  = ⊥-elim (ng g)
      ... | inj₂ tt = polyKind-a-not (arrowSchema? sc′)

  synthForm-true-chk : ∀ {n} {L′ : Locals m n} e {A t Ψ} → synthForm? ctx e ≡ true → (d : Chk L′ e A t) → UC d Ψ → SynthForm e
  synthForm-true-chk (Raw.RResolved cn) _ (SU.c-sub _ s _) (UM.u-sub w) = sf-name (synth-notPoly s w)
  synthForm-true-chk (Raw.RResolved cn) e (SU.c-poly d en lt τ r) (UM.u-poly {ok = ok}) =
    ⊥-elim (ok-poly ok en lt (np-true (polyKind ctx cn) e))
  synthForm-true-chk (Raw.RGen g) e _ _ with genKindView g
  ... | gk-const ic = sf-const ic
  synthForm-true-chk (Raw.RGen g) () _ _ | gk-map _
  synthForm-true-chk (Raw.RGen g) () _ _ | gk-comb₁ _
  synthForm-true-chk (Raw.RGen g) () _ _ | gk-comb₂ _
  synthForm-true-chk (Raw.RPair a b) e (SU.c-pair-lit da db) (UM.u-pair-lit ua ub) =
    let (ea , eb) = ∧-true e in sf-pair (synthForm-true-chk a ea da ua) (synthForm-true-chk b eb db ub)
  synthForm-true-chk (Raw.RPair a b) e (SU.c-sub noc _ _) _ = ⊥-elim (noc oc-pair)
  synthForm-true-chk (Raw.RApp f x) e (SU.c-sub _ s _) _ = sf-app (syn-noPC s) (app-noOC f x e)
  synthForm-true-chk (Raw.RApp f x) e (SU.c-map-app fc _ _) _ = ⊥-elim (app-noOC f x e (oc-map fc))
  synthForm-true-chk (Raw.RApp _ x) () (SU.c-curry _) _
  synthForm-true-chk (Raw.RApp _ x) () (SU.c-cata _ _) _
  synthForm-true-chk (Raw.RApp _ x) () (SU.c-ana _ _) _
  synthForm-true-chk (Raw.RApp _ x) () (SU.c-compose-g _ _ _) _
  synthForm-true-chk (Raw.RApp _ x) () (SU.c-compose-f _ _ _ _) _
  synthForm-true-chk (Raw.RApp _ x) () (SU.c-case _ _) _
  synthForm-true-chk (Raw.RApp _ x) () (SU.c-pair _ _) _
  synthForm-true-chk (Raw.RInt _) _ _ _             = sf-int
  synthForm-true-chk (Raw.RFloat _ _ _ _) _ _ _     = sf-float
  synthForm-true-chk Raw.RUnit _ _ _                = sf-unit
  synthForm-true-chk (Raw.RVar _) _ _ _             = sf-var
  synthForm-true-chk (Raw.RAnnot _ _) _ _ _         = sf-annot
  synthForm-true-chk (Raw.RNeg _) _ _ _             = sf-neg
  synthForm-true-chk (Raw.RBinOp _ _ _) _ _ _       = sf-binop
  synthForm-true-chk (Raw.RLet _ _ _) _ _ _         = sf-let
  synthForm-true-chk (Raw.RDestruct _ _ _ _ _) _ _ _ = sf-destruct
  synthForm-true-chk (Raw.RQualified _ _) () _ _
  synthForm-true-chk (Raw.RLam _ _) () _ _

  domainForm-true-syn : ∀ {n} {L′ : Locals m n} e {T t Ψ} → domainForm? ctx e ≡ true → (s : Syn L′ e T t) → US s Ψ → DomainForm e
  domainForm-true-syn (Raw.RResolved cn) _ s u = df-synth (sf-name (synth-notPoly s u))
  domainForm-true-syn (Raw.RGen g) _ (SU.s-const {k = k} _) _ = df-synth (sf-const k)
  domainForm-true-syn (Raw.RApp f a) e s u with ∨-true {synthForm? ctx (Raw.RApp f a)} e
  ... | inj₁ es = df-synth (synthForm-true (Raw.RApp f a) es s u)
  ... | inj₂ ed = ⊥-elim (domApp-noSyn f a ed s)
  domainForm-true-syn (Raw.RLam _ _) _ () _
  domainForm-true-syn (Raw.RQualified _ _) _ () _
  domainForm-true-syn e@(Raw.RInt _) ed s u = df-synth (synthForm-true e ed s u)
  domainForm-true-syn e@(Raw.RFloat _ _ _ _) ed s u = df-synth (synthForm-true e ed s u)
  domainForm-true-syn e@Raw.RUnit ed s u = df-synth (synthForm-true e ed s u)
  domainForm-true-syn e@(Raw.RVar _) ed s u = df-synth (synthForm-true e ed s u)
  domainForm-true-syn e@(Raw.RAnnot _ _) ed s u = df-synth (synthForm-true e ed s u)
  domainForm-true-syn e@(Raw.RPair _ _) ed s u = df-synth (synthForm-true e ed s u)
  domainForm-true-syn e@(Raw.RNeg _) ed s u = df-synth (synthForm-true e ed s u)
  domainForm-true-syn e@(Raw.RBinOp _ _ _) ed s u = df-synth (synthForm-true e ed s u)
  domainForm-true-syn e@(Raw.RLet _ _ _) ed s u = df-synth (synthForm-true e ed s u)
  domainForm-true-syn e@(Raw.RDestruct _ _ _ _ _) ed s u = df-synth (synthForm-true e ed s u)

  domainForm-true-chk : ∀ {n} {L′ : Locals m n} e {A t Ψ} → domainForm? ctx e ≡ true → (d : Chk L′ e A t) → UC d Ψ → DomainForm e
  domainForm-true-chk (Raw.RResolved cn) _ (SU.c-sub _ s _) (UM.u-sub w) = df-synth (sf-name (synth-notPoly s w))
  domainForm-true-chk (Raw.RResolved cn) e (SU.c-poly d en lt τ r) (UM.u-poly {ok = ok}) with polyKind ctx cn in ek
  ... | not-poly   = ⊥-elim (ok-poly ok en lt ek)
  ... | E.poly-dom = df-poly (dom-of cn ek)
  domainForm-true-chk (Raw.RResolved cn) () (SU.c-poly _ _ _ _ _) _ | poly-other
  domainForm-true-chk (Raw.RLam x b) e (SU.c-lam db) (UM.u-lam _ ub) = df-lam (synthForm-true-chk b e db ub)
  domainForm-true-chk (Raw.RGen g) e _ _ with ∨-true {constB (genKindView g)} e
  ... | inj₂ ed = df-map (yes-of (fromDomain? (G.kind g)) ed)
    where yes-of : ∀ {Q : Set} (dq : Dec Q) → isYesB dq ≡ true → Q
          yes-of (yes q) _ = q
          yes-of (no _) ()
  ... | inj₁ ec with genKindView g
  ...   | gk-const ic = df-synth (sf-const ic)
  domainForm-true-chk (Raw.RGen g) e _ _ | inj₁ () | gk-map _
  domainForm-true-chk (Raw.RGen g) e _ _ | inj₁ () | gk-comb₁ _
  domainForm-true-chk (Raw.RGen g) e _ _ | inj₁ () | gk-comb₂ _
  domainForm-true-chk (Raw.RApp f a) e d u with ∨-true {synthForm? ctx (Raw.RApp f a)} e
  ... | inj₁ es = df-synth (synthForm-true-chk (Raw.RApp f a) es d u)
  domainForm-true-chk (Raw.RApp f a) e (SU.c-sub _ s _) _ | inj₂ ed = ⊥-elim (domApp-noSyn f a ed s)
  domainForm-true-chk (Raw.RApp (Raw.RApp (Raw.RGen G.compose) f) g) e (SU.c-compose-g dg _ df) (UM.u-compose-g _ uf) | inj₂ ed =
    df-compose (domainForm-true-chk f (proj₁ (∧-true ed)) df uf) dg
  domainForm-true-chk (Raw.RApp (Raw.RApp (Raw.RGen G.compose) f) g) e (SU.c-compose-f _ df _ dg) (UM.u-compose-f uf ug) | inj₂ ed =
    let (ef , eg) = ∧-true ed in df-compose (domainForm-true-syn f ef df uf) (domainForm-true-chk g eg dg ug)
  domainForm-true-chk (Raw.RApp (Raw.RApp (Raw.RGen G.case) f) g) e (SU.c-case df dg) (UM.u-case uf ug) | inj₂ ed =
    let (ef , eg) = ∧-true ed in df-case (domainForm-true-chk f ef df uf) (domainForm-true-chk g eg dg ug)
  domainForm-true-chk (Raw.RApp (Raw.RApp (Raw.RGen G.pair) f) g) e (SU.c-pair df dg) (UM.u-pair uf ug) | inj₂ ed =
    let (ef , eg) = ∧-true ed in df-pair (domainForm-true-chk f ef df uf) (domainForm-true-chk g eg dg ug)
  domainForm-true-chk (Raw.RApp (Raw.RGen G.cata) a) e (SU.c-cata _ da) (UM.u-cata ua) | inj₂ ed =
    df-cata (synthForm-true-chk a ed da ua)
  domainForm-true-chk (Raw.RApp (Raw.RGen G.id) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.compose) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.fst) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.snd) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.terminal) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.pair) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.inl) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.inr) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.initial) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.case) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.apply) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.curry) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.In) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.Out) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.ana) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.unit) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.toFloat) _) e (SU.c-map-app _ _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp (Raw.RGen G.cata) _) e (SU.c-map-app () _ _) _ | inj₂ _
  domainForm-true-chk (Raw.RApp _ _) e (SU.c-curry _) _ | inj₂ ()
  domainForm-true-chk (Raw.RApp _ _) e (SU.c-ana _ _) _ | inj₂ ()
  domainForm-true-chk (Raw.RQualified _ _) () _ _
  domainForm-true-chk e@(Raw.RInt _) ed d u            = df-synth (synthForm-true-chk e ed d u)
  domainForm-true-chk e@(Raw.RFloat _ _ _ _) ed d u    = df-synth (synthForm-true-chk e ed d u)
  domainForm-true-chk e@Raw.RUnit ed d u               = df-synth (synthForm-true-chk e ed d u)
  domainForm-true-chk e@(Raw.RVar _) ed d u            = df-synth (synthForm-true-chk e ed d u)
  domainForm-true-chk e@(Raw.RAnnot _ _) ed d u        = df-synth (synthForm-true-chk e ed d u)
  domainForm-true-chk e@(Raw.RPair _ _) ed d u         = df-synth (synthForm-true-chk e ed d u)
  domainForm-true-chk e@(Raw.RNeg _) ed d u            = df-synth (synthForm-true-chk e ed d u)
  domainForm-true-chk e@(Raw.RBinOp _ _ _) ed d u      = df-synth (synthForm-true-chk e ed d u)
  domainForm-true-chk e@(Raw.RLet _ _ _) ed d u        = df-synth (synthForm-true-chk e ed d u)
  domainForm-true-chk e@(Raw.RDestruct _ _ _ _ _) ed d u = df-synth (synthForm-true-chk e ed d u)
