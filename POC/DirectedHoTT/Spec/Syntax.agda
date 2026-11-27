-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 20 — THE EXPERIMENT: dependent Π/Σ over a de Bruijn
--                            base, with substitution STRICTLY stable
--
-- The load-bearing test of the design decision (HANDOFF §1). The directed
-- functor-category CwF was RULED OUT as the kernel because its Π is only
-- LAX-stable — `(Π A B)[σ] ≢ Π (A[σ]) (B[σ↑])`, the failure of Beck–Chevalley
-- (`NbEPDirPiSub`, dHoTT-12e). The design's bet is that a STRICT SYNTACTIC
-- presentation fixes this by construction. This module runs the experiment.
--
-- A genuinely DEPENDENT raw syntax (well-scoped de Bruijn, base an arbitrary
-- context depth `Cx`): types `RTy` and terms `RTm` are MUTUAL, and `El`
-- injects a term into a type — so a type can mention a term VARIABLE
-- (`Π base (El (var vz))` is `(x : base) → El x`, a real dependency).
-- Substitution acts on both, defined structurally.
--
--   * `Π-stable`/`Σ-stable`/`El-stable` — substitution-stability is
--     DEFINITIONAL (`refl`): `(Π A B)[σ] ≡ Π (A[σ]) (B[σ↑])`. The lax
--     comparison map of the semantic CwF is here an EQUALITY, for free — the
--     syntactic presentation structurally has no Beck–Chevalley obstruction.
--   * `[id]ᵀ`/`[∘]ᵀ` — and it is a COHERENT strict substitution calculus:
--     type substitution satisfies the identity and COMPOSITION laws (the four
--     mutual fusion lemmas, funext-free via pointwise `*-cong`, exactly the
--     `NbEPDirDB` technique doubled for types+terms). `[∘]ᵀ` is the one that
--     matters for Beck–Chevalley: Π commutes STRICTLY with COMPOSED
--     substitutions, `subTy τ (subTy σ (Π A B)) ≡ subTy (τ ∘ₛ σ) (Π A B)` with
--     the Π structure preserved on the nose.
--
-- VERDICT: the experiment PASSES — dependent Π/Σ substitution-stability, the
-- exact thing that was only lax semantically, is definitional syntactically,
-- and sits inside a proven strict substitution calculus. Honest ceiling: this
-- is RAW syntax (scoping enforced, typing not) — enough to settle the
-- stability question; intrinsic typing + conversion is the next slice.
-- `--safe`, ZERO axioms (funext-free).
--
-- ★ GENERIC SYNTAX (SPIKE-GENERIC-SYNTAX, branch spike-generic-syntax,
--   2026-11-27): `RTy`/`RTm` are the two sorts of ONE binding signature,
--   `KSig` below, over `Spec/Bind`'s generic scoped syntax. Every former is a
--   pattern synonym (implicit `{Γ}` included), so the API is unchanged.
--   Renaming and substitution are the generic traversal at two kits, and
--   the congruence, fusion and identity lemmas below are corollaries of the
--   generic ones, with their old statements.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.Syntax where
open import DirectedHoTT.Prelude
  using ( _≡_; refl; sym; trans; cong; cong₂; ¬_; Dec; yes; no )
-- ★ INDUCTIVE-TYPES AXIS: a metalanguage ℕ, used only as a CONSTRUCTOR
--   TAG.  It is not the object-language `Nat`.
open import Agda.Builtin.Nat using ( zero; suc; _==_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Scope public
import DirectedHoTT.Spec.Bind as G
open G using ( fld; fnat )

-- ⚠ LOCAL: `normalizer.Syntax.Types` exports `cong₂` but not `cong₃`, and
--   `Lib/Wk`'s copy is downstream of this module.  Three lines beats an
--   import cycle.
cong₃ : {A B C D : Set} (f : A → B → C → D) {a a' : A} {b b' : B} {c c' : C} →
        a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

cong₄ : {A B C D E : Set} (f : A → B → C → D → E) {a a' : A} {b b' : B} {c c' : C} {d d' : D} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → f a b c d ≡ f a' b' c' d'
cong₄ f refl refl refl refl = refl

------------------------------------------------------------------------
-- The MUTUAL dependent raw syntax: types and terms, with `El` bringing a
-- term into a type. `Π A B` / `Σ' A B` bind one variable in `B`.
--
-- ★ ONE BINDING SIGNATURE: two sorts, the constructors of each, and each
--   constructor's fields (`fld s k`: a subterm of sort `s` under `k` new
--   binders; `fnat`: a meta natural). Variables live at the term sort.
-- ★★ LEVITATION (PLAN-LEVITATION, D490–D492): descriptions are TERMS
--   of the large type `Desc I`, so there is no separate description
--   syntax — and renaming/substitution traverse them like any term.
------------------------------------------------------------------------

data Srt : Set where
  ty tm : Srt

data KCon : Srt → Set where
  `base `U `Π `Σ' `El `Hom `Unit `Nat `Id `IMu `Desc `DIh `Fin : KCon ty
  `lam `app `pair `absurd `ordtr `fst `snd `⌜base⌝ `⌜Π⌝ `⌜Σ⌝ `⌜Hom⌝ `hrefl `tr `ap
    `⌜Id⌝ `idrefl `jsub `unit `nzero `nsuc `natrec `con `ielim `dι `dσ `dρ `dpay `dih
    `fzero `fsuc `fcase `fcase0 `psplit `⌜Nat⌝ `⌜IMu⌝ `⌜Fin⌝ `⌜Unit⌝ `ref : KCon tm

kfields : ∀ {s} → KCon s → List (G.Field Srt)
kfields `base   = []
kfields `U      = []
kfields `Π      = fld ty 0 ∷ fld ty 1 ∷ []
kfields `Σ'     = fld ty 0 ∷ fld ty 1 ∷ []
kfields `El     = fld tm 0 ∷ []
kfields `Hom    = fld ty 0 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `Unit   = []
kfields `Nat    = []
kfields `Id     = fld ty 0 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `IMu    = fld tm 0 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `Desc   = fld tm 0 ∷ []
kfields `DIh    = fld tm 0 ∷ fld ty 2 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `Fin    = fld tm 0 ∷ []
kfields `lam    = fld tm 1 ∷ []
kfields `app    = fld tm 0 ∷ fld tm 0 ∷ []
kfields `pair   = fld tm 0 ∷ fld tm 0 ∷ []
kfields `absurd = fld tm 0 ∷ fld tm 0 ∷ []
kfields `ordtr  = fld tm 0 ∷ fld tm 0 ∷ fld tm 0 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `fst    = fld tm 0 ∷ []
kfields `snd    = fld tm 0 ∷ []
kfields `⌜base⌝ = []
kfields `⌜Π⌝    = fld tm 0 ∷ fld tm 1 ∷ []
kfields `⌜Σ⌝    = fld tm 0 ∷ fld tm 1 ∷ []
kfields `⌜Hom⌝  = fld tm 0 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `hrefl  = fld tm 0 ∷ fld tm 0 ∷ []
kfields `tr     = fld tm 1 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `ap     = fld tm 0 ∷ fld tm 1 ∷ fld tm 0 ∷ []
kfields `⌜Id⌝   = fld tm 0 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `idrefl = fld tm 0 ∷ fld tm 0 ∷ []
kfields `jsub   = fld tm 1 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `unit   = []
kfields `nzero  = []
kfields `nsuc   = fld tm 0 ∷ []
kfields `natrec = fld tm 0 ∷ fld tm 2 ∷ fld tm 0 ∷ []
kfields `con    = fld tm 0 ∷ []
kfields `ielim  = fld tm 0 ∷ fld tm 0 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `dι     = []
kfields `dσ     = fld tm 0 ∷ fld tm 0 ∷ []
kfields `dρ     = fld tm 0 ∷ fld tm 0 ∷ []
kfields `dpay   = fld tm 0 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `dih    = fld tm 0 ∷ fld tm 0 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `fzero  = []
kfields `fsuc   = fld tm 0 ∷ []
kfields `fcase  = fld tm 0 ∷ fld tm 0 ∷ fld tm 1 ∷ []
kfields `fcase0 = fld tm 0 ∷ []
kfields `psplit = fld tm 2 ∷ fld tm 0 ∷ []
kfields `⌜Nat⌝  = []
kfields `⌜IMu⌝  = fld tm 0 ∷ fld tm 0 ∷ fld tm 0 ∷ []
kfields `⌜Fin⌝  = fld tm 0 ∷ []
kfields `⌜Unit⌝ = []
kfields `ref    = fnat ∷ []

KSig : G.BSig
KSig = record { Sort = Srt ; vsort = tm ; Con = KCon ; fields = kfields }

RTy RTm : Cx → Set
RTy = G.Tm KSig ty
RTm = G.Tm KSig tm

-- ★ the formers, as pattern synonyms (they read, match and apply as the
--   old constructors did, implicit scope included)
infixr 5 _,ᵃ_
pattern _,ᵃ_ a as = a G.∷ᵃ as
pattern ∎ᵃ = G.[]ᵃ

pattern base {Γ}          = G.node {Γ = Γ} `base ∎ᵃ
pattern U {Γ}             = G.node {Γ = Γ} `U ∎ᵃ
pattern Π {Γ} A B         = G.node {Γ = Γ} `Π (A ,ᵃ B ,ᵃ ∎ᵃ)
pattern Σ' {Γ} A B        = G.node {Γ = Γ} `Σ' (A ,ᵃ B ,ᵃ ∎ᵃ)
pattern El {Γ} t          = G.node {Γ = Γ} `El (t ,ᵃ ∎ᵃ)
pattern Hom {Γ} A t u     = G.node {Γ = Γ} `Hom (A ,ᵃ t ,ᵃ u ,ᵃ ∎ᵃ)
pattern Unit {Γ}          = G.node {Γ = Γ} `Unit ∎ᵃ
pattern Nat {Γ}           = G.node {Γ = Γ} `Nat ∎ᵃ
pattern Id {Γ} A t u      = G.node {Γ = Γ} `Id (A ,ᵃ t ,ᵃ u ,ᵃ ∎ᵃ)
pattern IMu {Γ} I D i     = G.node {Γ = Γ} `IMu (I ,ᵃ D ,ᵃ i ,ᵃ ∎ᵃ)
pattern Desc {Γ} I        = G.node {Γ = Γ} `Desc (I ,ᵃ ∎ᵃ)
pattern DIh {Γ} D M C p   = G.node {Γ = Γ} `DIh (D ,ᵃ M ,ᵃ C ,ᵃ p ,ᵃ ∎ᵃ)
pattern Fin {Γ} n         = G.node {Γ = Γ} `Fin (n ,ᵃ ∎ᵃ)
pattern var {Γ} x         = G.var {Γ = Γ} x
pattern lam {Γ} t         = G.node {Γ = Γ} `lam (t ,ᵃ ∎ᵃ)
pattern app {Γ} t u       = G.node {Γ = Γ} `app (t ,ᵃ u ,ᵃ ∎ᵃ)
pattern pair {Γ} a b      = G.node {Γ = Γ} `pair (a ,ᵃ b ,ᵃ ∎ᵃ)
pattern absurd {Γ} c e    = G.node {Γ = Γ} `absurd (c ,ᵃ e ,ᵃ ∎ᵃ)
pattern ordtr {Γ} a t u p q = G.node {Γ = Γ} `ordtr (a ,ᵃ t ,ᵃ u ,ᵃ p ,ᵃ q ,ᵃ ∎ᵃ)
pattern fst {Γ} p         = G.node {Γ = Γ} `fst (p ,ᵃ ∎ᵃ)
pattern snd {Γ} p         = G.node {Γ = Γ} `snd (p ,ᵃ ∎ᵃ)
pattern ⌜base⌝ {Γ}        = G.node {Γ = Γ} `⌜base⌝ ∎ᵃ
pattern ⌜Π⌝ {Γ} c d       = G.node {Γ = Γ} `⌜Π⌝ (c ,ᵃ d ,ᵃ ∎ᵃ)
pattern ⌜Σ⌝ {Γ} c d       = G.node {Γ = Γ} `⌜Σ⌝ (c ,ᵃ d ,ᵃ ∎ᵃ)
pattern ⌜Hom⌝ {Γ} c a b   = G.node {Γ = Γ} `⌜Hom⌝ (c ,ᵃ a ,ᵃ b ,ᵃ ∎ᵃ)
pattern hrefl {Γ} c t     = G.node {Γ = Γ} `hrefl (c ,ᵃ t ,ᵃ ∎ᵃ)
pattern tr {Γ} d p e      = G.node {Γ = Γ} `tr (d ,ᵃ p ,ᵃ e ,ᵃ ∎ᵃ)
pattern ap {Γ} c b p      = G.node {Γ = Γ} `ap (c ,ᵃ b ,ᵃ p ,ᵃ ∎ᵃ)
pattern ⌜Id⌝ {Γ} c a b    = G.node {Γ = Γ} `⌜Id⌝ (c ,ᵃ a ,ᵃ b ,ᵃ ∎ᵃ)
pattern idrefl {Γ} c t    = G.node {Γ = Γ} `idrefl (c ,ᵃ t ,ᵃ ∎ᵃ)
pattern jsub {Γ} d p e    = G.node {Γ = Γ} `jsub (d ,ᵃ p ,ᵃ e ,ᵃ ∎ᵃ)
pattern unit {Γ}          = G.node {Γ = Γ} `unit ∎ᵃ
pattern nzero {Γ}         = G.node {Γ = Γ} `nzero ∎ᵃ
pattern nsuc {Γ} n        = G.node {Γ = Γ} `nsuc (n ,ᵃ ∎ᵃ)
pattern natrec {Γ} z s n  = G.node {Γ = Γ} `natrec (z ,ᵃ s ,ᵃ n ,ᵃ ∎ᵃ)
pattern con {Γ} p         = G.node {Γ = Γ} `con (p ,ᵃ ∎ᵃ)
pattern ielim {Γ} D i e t = G.node {Γ = Γ} `ielim (D ,ᵃ i ,ᵃ e ,ᵃ t ,ᵃ ∎ᵃ)
pattern dι {Γ}            = G.node {Γ = Γ} `dι ∎ᵃ
pattern dσ {Γ} S f        = G.node {Γ = Γ} `dσ (S ,ᵃ f ,ᵃ ∎ᵃ)
pattern dρ {Γ} j C        = G.node {Γ = Γ} `dρ (j ,ᵃ C ,ᵃ ∎ᵃ)
pattern dpay {Γ} I D C    = G.node {Γ = Γ} `dpay (I ,ᵃ D ,ᵃ C ,ᵃ ∎ᵃ)
pattern dih {Γ} D e C p   = G.node {Γ = Γ} `dih (D ,ᵃ e ,ᵃ C ,ᵃ p ,ᵃ ∎ᵃ)
pattern fzero {Γ}         = G.node {Γ = Γ} `fzero ∎ᵃ
pattern fsuc {Γ} t        = G.node {Γ = Γ} `fsuc (t ,ᵃ ∎ᵃ)
pattern fcase {Γ} t a b   = G.node {Γ = Γ} `fcase (t ,ᵃ a ,ᵃ b ,ᵃ ∎ᵃ)
pattern fcase0 {Γ} t      = G.node {Γ = Γ} `fcase0 (t ,ᵃ ∎ᵃ)
pattern psplit {Γ} b q    = G.node {Γ = Γ} `psplit (b ,ᵃ q ,ᵃ ∎ᵃ)
pattern ⌜Nat⌝ {Γ}         = G.node {Γ = Γ} `⌜Nat⌝ ∎ᵃ
pattern ⌜IMu⌝ {Γ} I D i   = G.node {Γ = Γ} `⌜IMu⌝ (I ,ᵃ D ,ᵃ i ,ᵃ ∎ᵃ)
pattern ⌜Fin⌝ {Γ} n       = G.node {Γ = Γ} `⌜Fin⌝ (n ,ᵃ ∎ᵃ)
pattern ⌜Unit⌝ {Γ}        = G.node {Γ = Γ} `⌜Unit⌝ ∎ᵃ
pattern ref {Γ} d         = G.node {Γ = Γ} `ref (d G.∷ⁿ ∎ᵃ)

-- ★ `RTy.Fin`: the old datatype's module, where downstream code
--   disambiguates `Fin` from the Lib's (a datatype came with one)
module RTy where
  pattern Fin {Γ} n = G.node {Γ = Γ} `Fin (n ,ᵃ ∎ᵃ)

-- the generic traversal, instantiated ONCE, here
module KT = G.Trav KSig

private
  variable
    Γ Δ Θ : Cx

------------------------------------------------------------------------
-- Renamings (variable-for-variable) and their action on types + terms.
------------------------------------------------------------------------

Ren : Cx → Cx → Set
Ren Γ Δ = Var Γ → Var Δ

extR : Ren Γ Δ → Ren (Γ ∙) (Δ ∙)
extR = KT.ext KT.renK

-- ★ A THINNING — an order-preserving embedding, as FIRST-ORDER data.
--   Where a renaming is any function on variables, a thinning can only
--   KEEP a variable or DROP (skip) one of the target's, in order — so
--   it is exactly a WEAKENING.  A-math's constructor telescopes are the
--   customer: the constructor's own scope embeds into the telescope
--   omitting the abstract family, and that embedding is a thinning, not
--   an arbitrary renaming.  First-order is what lets the Knot reify it.
data Thin : Cx → Cx → Set where
  done : Thin ε ε
  keep : Thin Γ Δ → Thin (Γ ∙) (Δ ∙)
  drop : Thin Γ Δ → Thin Γ (Δ ∙)

-- its action on variables.  ⚠ `thinR (keep θ)` IS `extR (thinR θ)`
--   clause by clause, so a walk that extends by `keep` needs no lemma.
thinR : Thin Γ Δ → Ren Γ Δ
thinR (keep θ) vz     = vz
thinR (keep θ) (vs x) = vs (thinR θ x)
thinR (drop θ) x      = vs (thinR θ x)

renTy : Ren Γ Δ → RTy Γ → RTy Δ
renTy = KT.ren
renTm : Ren Γ Δ → RTm Γ → RTm Δ
renTm = KT.ren

------------------------------------------------------------------------
-- Parallel substitutions (variable-for-term) and their action.
------------------------------------------------------------------------

Sub : Cx → Cx → Set
Sub Γ Δ = Var Γ → RTm Δ

extS : Sub Γ Δ → Sub (Γ ∙) (Δ ∙)
extS = KT.ext KT.subK

subTy : Sub Γ Δ → RTy Γ → RTy Δ
subTy = KT.sub
subTm : Sub Γ Δ → RTm Γ → RTm Δ
subTm = KT.sub

-- Identity and the four composition operators (explicit-index, genuine
-- Ren/Sub — same shape as NbEPDirDB).
idₛ : Sub Γ Γ
idₛ x = var x

infixr 8 _∘ᵣ_ _ₛ∘ᵣ_ _ᵣ∘ₛ_ _∘ₛ_
_∘ᵣ_ : Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
(ρ' ∘ᵣ ρ) x = ρ' (ρ x)

_ₛ∘ᵣ_ : Sub Δ Θ → Ren Γ Δ → Sub Γ Θ
(σ ₛ∘ᵣ ρ) x = σ (ρ x)

_ᵣ∘ₛ_ : Ren Δ Θ → Sub Γ Δ → Sub Γ Θ
(ρ ᵣ∘ₛ σ) x = renTm ρ (σ x)

_∘ₛ_ : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
(τ ∘ₛ σ) x = subTm τ (σ x)

------------------------------------------------------------------------
-- ★ THE HEADLINE: substitution-stability of the dependent formers is
--   DEFINITIONAL. This is the lax comparison map of the semantic CwF,
--   here an EQUALITY for free — no Beck–Chevalley obstruction.
------------------------------------------------------------------------

Π-stable : (σ : Sub Γ Δ) (A : RTy Γ) (B : RTy (Γ ∙)) →
           subTy σ (Π A B) ≡ Π (subTy σ A) (subTy (extS σ) B)
Π-stable σ A B = refl

Σ-stable : (σ : Sub Γ Δ) (A : RTy Γ) (B : RTy (Γ ∙)) →
           subTy σ (Σ' A B) ≡ Σ' (subTy σ A) (subTy (extS σ) B)
Σ-stable σ A B = refl

-- Dependency substitutes coherently: `El` follows its term.
El-stable : (σ : Sub Γ Δ) (t : RTm Γ) → subTy σ (El t) ≡ El (subTm σ t)
El-stable σ t = refl

-- `Hom` is substitution-stable definitionally too — the former adds no
-- Beck–Chevalley debt.
Hom-stable : (σ : Sub Γ Δ) (A : RTy Γ) (t u : RTm Γ) →
             subTy σ (Hom A t u) ≡ Hom (subTy σ A) (subTm σ t) (subTm σ u)
Hom-stable σ A t u = refl

-- three-argument congruence, for the `Hom` clauses of the calculus below
Hom-cong₃ : {A A' : RTy Γ} {t t' u u' : RTm Γ} →
            A ≡ A' → t ≡ t' → u ≡ u' → Hom A t u ≡ Hom A' t' u'
Hom-cong₃ refl refl refl = refl

-- ★ WF-axis: ordtr is 5-ary, so it gets its own congruence, in the
-- house style of `Hom-cong₃`.
ordtr-cong₅ : {a a' t t' u u' p p' q q' : RTm Γ} →
              a ≡ a' → t ≡ t' → u ≡ u' → p ≡ p' → q ≡ q' →
              ordtr a t u p q ≡ ordtr a' t' u' p' q'
ordtr-cong₅ refl refl refl refl refl = refl

Id-cong₃ : {A A' : RTy Γ} {t t' u u' : RTm Γ} →
           A ≡ A' → t ≡ t' → u ≡ u' → Id A t u ≡ Id A' t' u'
Id-cong₃ refl refl refl = refl

-- …and its term-level mirrors for the three W2 formers
⌜Hom⌝-cong₃ : {c c' a a' b b' : RTm Γ} →
              c ≡ c' → a ≡ a' → b ≡ b' → ⌜Hom⌝ c a b ≡ ⌜Hom⌝ c' a' b'
⌜Hom⌝-cong₃ refl refl refl = refl

tr-cong₃ : {d d' : RTm (Γ ∙)} {p p' e e' : RTm Γ} →
           d ≡ d' → p ≡ p' → e ≡ e' → tr d p e ≡ tr d' p' e'
tr-cong₃ refl refl refl = refl

ap-cong₃ : {c c' : RTm Γ} {b b' : RTm (Γ ∙)} {p p' : RTm Γ} →
           c ≡ c' → b ≡ b' → p ≡ p' → ap c b p ≡ ap c' b' p'
ap-cong₃ refl refl refl = refl

⌜Id⌝-cong₃ : {c c' a a' b b' : RTm Γ} →
             c ≡ c' → a ≡ a' → b ≡ b' → ⌜Id⌝ c a b ≡ ⌜Id⌝ c' a' b'
⌜Id⌝-cong₃ refl refl refl = refl

jsub-cong₃ : {d d' : RTm (Γ ∙)} {p p' e e' : RTm Γ} →
             d ≡ d' → p ≡ p' → e ≡ e' → jsub d p e ≡ jsub d' p' e'
jsub-cong₃ refl refl refl = refl

natrec-cong₃ : {z z' : RTm Γ} {s s' : RTm ((Γ ∙) ∙)} {n n' : RTm Γ} →
               z ≡ z' → s ≡ s' → n ≡ n' → natrec z s n ≡ natrec z' s' n'
natrec-cong₃ refl refl refl = refl

-- A concrete dependent type and its substitution: `(x : base) → El x`.
Πdep : RTy Γ
Πdep = Π base (El (var vz))

_ : (σ : Sub Γ Δ) → subTy σ Πdep ≡ Π base (El (var vz))
_ = λ σ → refl

------------------------------------------------------------------------
-- ...and it is a COHERENT strict calculus: the mutual substitution laws.
-- ★ GENERIC (SPIKE-GENERIC-SYNTAX): each is a corollary of `Spec/Bind`'s
--   congruence, fusion and identity, proved once for every signature; the
--   statements are the hand-written calculus's.
------------------------------------------------------------------------

extR-cong : {ρ ρ' : Ren Γ Δ} → (∀ (x : Var Γ) → ρ x ≡ ρ' x) →
            ∀ (x : Var (Γ ∙)) → extR ρ x ≡ extR ρ' x
extR-cong h vz     = refl
extR-cong h (vs x) = cong vs (h x)

renTy-cong : {ρ ρ' : Ren Γ Δ} → (∀ (x : Var Γ) → ρ x ≡ ρ' x) →
             (A : RTy Γ) → renTy ρ A ≡ renTy ρ' A
renTy-cong = KT.Cong.trav-cong KT.renK
renTm-cong : {ρ ρ' : Ren Γ Δ} → (∀ (x : Var Γ) → ρ x ≡ ρ' x) →
             (t : RTm Γ) → renTm ρ t ≡ renTm ρ' t
renTm-cong = KT.Cong.trav-cong KT.renK

extS-cong : {σ σ' : Sub Γ Δ} → (∀ (x : Var Γ) → σ x ≡ σ' x) →
            ∀ (x : Var (Γ ∙)) → extS σ x ≡ extS σ' x
extS-cong h vz     = refl
extS-cong h (vs x) = cong (renTm vs) (h x)

subTy-cong : {σ σ' : Sub Γ Δ} → (∀ (x : Var Γ) → σ x ≡ σ' x) →
             (A : RTy Γ) → subTy σ A ≡ subTy σ' A
subTy-cong = KT.Cong.trav-cong KT.subK
subTm-cong : {σ σ' : Sub Γ Δ} → (∀ (x : Var Γ) → σ x ≡ σ' x) →
             (t : RTm Γ) → subTm σ t ≡ subTm σ' t
subTm-cong = KT.Cong.trav-cong KT.subK

-- ren ∘ ren.
extr-extr : (ρ' : Ren Δ Θ) (ρ : Ren Γ Δ) (x : Var (Γ ∙)) →
            (extR ρ' ∘ᵣ extR ρ) x ≡ extR (ρ' ∘ᵣ ρ) x
extr-extr ρ' ρ vz     = refl
extr-extr ρ' ρ (vs x) = refl

renTy-renTy : {ρ' : Ren Δ Θ} {ρ : Ren Γ Δ} (A : RTy Γ) →
              renTy ρ' (renTy ρ A) ≡ renTy (ρ' ∘ᵣ ρ) A
renTy-renTy {ρ' = ρ'} {ρ} = KT.ren-ren ρ ρ'
renTm-renTm : {ρ' : Ren Δ Θ} {ρ : Ren Γ Δ} (t : RTm Γ) →
              renTm ρ' (renTm ρ t) ≡ renTm (ρ' ∘ᵣ ρ) t
renTm-renTm {ρ' = ρ'} {ρ} = KT.ren-ren ρ ρ'

-- sub ∘ ren.
exts-extr : (σ : Sub Δ Θ) (ρ : Ren Γ Δ) (x : Var (Γ ∙)) →
            (extS σ ₛ∘ᵣ extR ρ) x ≡ extS (σ ₛ∘ᵣ ρ) x
exts-extr σ ρ vz     = refl
exts-extr σ ρ (vs x) = refl

subTy-renTy : {σ : Sub Δ Θ} {ρ : Ren Γ Δ} (A : RTy Γ) →
              subTy σ (renTy ρ A) ≡ subTy (σ ₛ∘ᵣ ρ) A
subTy-renTy {σ = σ} {ρ} = KT.sub-ren ρ σ
subTm-renTm : {σ : Sub Δ Θ} {ρ : Ren Γ Δ} (t : RTm Γ) →
              subTm σ (renTm ρ t) ≡ subTm (σ ₛ∘ᵣ ρ) t
subTm-renTm {σ = σ} {ρ} = KT.sub-ren ρ σ

-- ren ∘ sub.
extr-exts : (ρ : Ren Δ Θ) (σ : Sub Γ Δ) (x : Var (Γ ∙)) →
            (extR ρ ᵣ∘ₛ extS σ) x ≡ extS (ρ ᵣ∘ₛ σ) x
extr-exts ρ σ vz     = refl
extr-exts ρ σ (vs x) = trans (KT.ren-ren vs (extR ρ) (σ x)) (sym (KT.ren-ren ρ vs (σ x)))

renTy-subTy : {ρ : Ren Δ Θ} {σ : Sub Γ Δ} (A : RTy Γ) →
              renTy ρ (subTy σ A) ≡ subTy (ρ ᵣ∘ₛ σ) A
renTy-subTy {ρ = ρ} {σ} = KT.ren-sub σ ρ
renTm-subTm : {ρ : Ren Δ Θ} {σ : Sub Γ Δ} (t : RTm Γ) →
              renTm ρ (subTm σ t) ≡ subTm (ρ ᵣ∘ₛ σ) t
renTm-subTm {ρ = ρ} {σ} = KT.ren-sub σ ρ

-- sub ∘ sub.
exts-exts : (τ : Sub Δ Θ) (σ : Sub Γ Δ) (x : Var (Γ ∙)) →
            (extS τ ∘ₛ extS σ) x ≡ extS (τ ∘ₛ σ) x
exts-exts τ σ vz     = refl
exts-exts τ σ (vs x) = trans (KT.sub-ren vs (extS τ) (σ x)) (sym (KT.ren-sub τ vs (σ x)))

subTy-subTy : {τ : Sub Δ Θ} {σ : Sub Γ Δ} (A : RTy Γ) →
              subTy τ (subTy σ A) ≡ subTy (τ ∘ₛ σ) A
subTy-subTy {τ = τ} {σ} = KT.sub-sub σ τ
subTm-subTm : {τ : Sub Δ Θ} {σ : Sub Γ Δ} (t : RTm Γ) →
              subTm τ (subTm σ t) ≡ subTm (τ ∘ₛ σ) t
subTm-subTm {τ = τ} {σ} = KT.sub-sub σ τ

-- Identity: `exts` preserves `idₛ`, hence `subTy idₛ = id`.
exts-id : (x : Var (Γ ∙)) → extS idₛ x ≡ idₛ x
exts-id vz     = refl
exts-id (vs x) = refl

subTy-id : (A : RTy Γ) → subTy idₛ A ≡ A
subTy-id = KT.sub-id
subTm-id : (t : RTm Γ) → subTm idₛ t ≡ t
subTm-id = KT.sub-id



------------------------------------------------------------------------
-- ★ closed things weakened into any scope (the unique substitution out of
--   the empty context).
------------------------------------------------------------------------

εsub : Sub ε Γ
εsub ()

εwkTy : RTy ε → RTy Γ
εwkTy = subTy εsub

εwk-ren : (ρ : Ren Γ Δ) (A : RTy ε) → renTy ρ (εwkTy A) ≡ εwkTy A
εwk-ren ρ A = trans (renTy-subTy A) (subTy-cong (λ ()) A)

εwk-sub : (σ : Sub Γ Δ) (A : RTy ε) → subTy σ (εwkTy A) ≡ εwkTy A
εwk-sub σ A = trans (subTy-subTy A) (subTy-cong (λ ()) A)

εwkTm : RTm ε → RTm Γ
εwkTm = subTm εsub

εwkTm-ren : (ρ : Ren Γ Δ) (t : RTm ε) → renTm ρ (εwkTm t) ≡ εwkTm t
εwkTm-ren ρ t = trans (renTm-subTm t) (subTm-cong (λ ()) t)

εwkTm-sub : (σ : Sub Γ Δ) (t : RTm ε) → subTm σ (εwkTm t) ≡ εwkTm t
εwkTm-sub σ t = trans (subTm-subTm t) (subTm-cong (λ ()) t)

------------------------------------------------------------------------
-- ★ THE CATEGORY-OF-CONTEXTS LAWS ON TYPES — the coherence that makes the
--   definitional Π-stability NON-vacuous. `[∘]ᵀ` is the Beck–Chevalley-
--   relevant law: type substitution commutes with COMPOSITION, so Π commutes
--   STRICTLY with composed substitutions (combine with `Π-stable`).
------------------------------------------------------------------------

[id]ᵀ : (A : RTy Γ) → subTy idₛ A ≡ A
[id]ᵀ = subTy-id

[∘]ᵀ : {τ : Sub Δ Θ} {σ : Sub Γ Δ} (A : RTy Γ) →
       subTy τ (subTy σ A) ≡ subTy (τ ∘ₛ σ) A
[∘]ᵀ = subTy-subTy

-- Π commutes with composed substitution, on the nose (Beck–Chevalley,
-- strictly): both routes land at the same Π with no comparison map.
Π-BeckChevalley : {τ : Sub Δ Θ} {σ : Sub Γ Δ} (A : RTy Γ) (B : RTy (Γ ∙)) →
                  subTy τ (subTy σ (Π A B)) ≡ subTy (τ ∘ₛ σ) (Π A B)
Π-BeckChevalley A B = subTy-subTy (Π A B)

------------------------------------------------------------------------
-- ★ THE KERNEL SIGNATURE (PLAN-REF, D501): the definition context.  A
--   telescope of closed entries — a declared type and a body — read by
--   projection (`ref d`).  Entry d is meant to be typed over the entries
--   before it (`Spec/Typing`'s `WfSig`); the length is cached, so a lookup
--   is one walk down the telescope.
------------------------------------------------------------------------

record Def : Set where
  constructor ⟨_∣_⟩
  field
    kType : RTy ε
    kBody : RTm ε
open Def public

data DefTele : Set where
  ∅   : DefTele
  _▸_ : DefTele → Def → DefTele
infixl 5 _▸_

-- entry d of a telescope of length n (entries counted from the first);
-- beyond the length, a junk entry that no well-formed use reaches
pickK : Bool → Def → Def → Def
pickK true  x y = x
pickK false x y = y

lookupK : ℕ → DefTele → ℕ → Def
lookupK (suc n) (T ▸ e) d = pickK (d == n) e (lookupK n T d)
lookupK zero    _       d = ⟨ Unit ∣ unit ⟩
lookupK (suc n) ∅       d = ⟨ Unit ∣ unit ⟩

record Defs : Set where
  constructor mkK
  field
    len  : ℕ
    tele : DefTele
  size : ℕ
  size = len
  type : ℕ → RTy ε
  type d = kType (lookupK len tele d)
  body : ℕ → RTm ε
  body d = kBody (lookupK len tele d)

∅ᴷ : Defs
∅ᴷ = mkK 0 ∅

_▸ᴷ_ : Defs → Def → Defs
mkK n T ▸ᴷ e = mkK (suc n) (T ▸ e)
infixl 5 _▸ᴷ_

-- the names below a bound
infix 4 _<ˢ_
data _<ˢ_ : ℕ → ℕ → Set where
  <-here  : ∀ {n} → n <ˢ suc n
  <-there : ∀ {d n} → d <ˢ n → d <ˢ suc n

<ˢ-zero : ∀ {d} → ¬ (d <ˢ zero)
<ˢ-zero ()

-- is name d among the first n?  (δ fires exactly on the names in the
-- signature, so the development and the evaluators decide it)
private
  ≟ℕ : (a b : ℕ) → Dec (a ≡ b)
  ≟ℕ zero    zero    = yes refl
  ≟ℕ zero    (suc b) = no λ ()
  ≟ℕ (suc a) zero    = no λ ()
  ≟ℕ (suc a) (suc b) = suc≟ (≟ℕ a b)
    where
    suc≟ : Dec (a ≡ b) → Dec (suc a ≡ suc b)
    suc≟ (yes refl) = yes refl
    suc≟ (no ne)    = no λ { refl → ne refl }

  <ˢ-suc : ∀ {d n} → Dec (d ≡ n) → Dec (d <ˢ n) → Dec (d <ˢ suc n)
  <ˢ-suc (yes refl) _       = yes <-here
  <ˢ-suc (no ne)    (yes p) = yes (<-there p)
  <ˢ-suc (no ne)    (no ¬p) = no λ { <-here → ne refl ; (<-there p) → ¬p p }

_<ˢ?_ : (d n : ℕ) → Dec (d <ˢ n)
d <ˢ? zero  = no <ˢ-zero
d <ˢ? suc n = <ˢ-suc (≟ℕ d n) (d <ˢ? n)

<ˢ-down : ∀ {d n} → suc d <ˢ n → d <ˢ n
<ˢ-down <-here      = <-there <-here
<ˢ-down (<-there p) = <-there (<ˢ-down p)

<ˢ-pred : ∀ {d n} → suc d <ˢ suc n → d <ˢ n
<ˢ-pred <-here      = <-here
<ˢ-pred (<-there p) = <ˢ-down p

-- a name below n is not n
<ˢ→≠ : ∀ {d n} → d <ˢ n → (d == n) ≡ false
<ˢ→≠ {_}     {zero}  ()
<ˢ→≠ {zero}  {suc n} _ = refl
<ˢ→≠ {suc d} {suc n} p = <ˢ→≠ (<ˢ-pred p)

-- so a lookup below the newest entry skips it (signature extension)
pickK-false : ∀ {b x y} → b ≡ false → pickK b x y ≡ y
pickK-false refl = refl

lookupK-▸ : ∀ {n T e d} → d <ˢ n → lookupK (suc n) (T ▸ e) d ≡ lookupK n T d
lookupK-▸ p = pickK-false (<ˢ→≠ p)
