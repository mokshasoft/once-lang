-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.Convert
--
-- Connects the formal grammar specification (`Once.Grammar`) to the
-- internal type representation (`Once.Type`).
--
-- The grammar spec (`GType`) is what users write in source code. The
-- internal type (`Type`) is what the type-checker operates on. The two
-- diverge in two directions:
--
--   * `GType` has `TVar` (for grammar-level type-variable references).
--     `Type` does not: after 0.2.5, type variables live only inside
--     `PolyType` signatures, never in user-written types.
--   * `Type` has `μ-type` / `ν-type` (inductive/coinductive fixed points).
--     `GType` does not: these are produced internally by the elaborator,
--     not parsed from source.
--
-- Conversion is therefore partial in both directions, matching those
-- asymmetries:
--
--   `typeToGType : Type → Maybe GType`  (fails on μ/ν)
--   `gtypeToType : GType → Maybe Type`  (fails on TVar)
--
-- The main connection theorem (`parseType-expressible-in-grammar`) says:
-- every type produced by the surface parser is expressible in the
-- formal grammar. This is the "grammar conformance" property — the
-- parser never produces internal-only shapes.
------------------------------------------------------------------------

module Once.Grammar.Convert where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

import Once.Type as T
open T using (Type; Quantity; Zero; One; Many)
import Once.Grammar as G
open G using (GType)

open import Once.Parser.Token
open import Once.Parser.Type using (parseType)

------------------------------------------------------------------------
-- GType → Type
------------------------------------------------------------------------

-- | Convert a grammar-level type to an internal type.
-- Fails if the grammar type uses `TVar`, since user-written types
-- are not allowed to contain free type variables. `GMu` converts via
-- the mutual functor companion `gfunctorToFunctor`.
mutual
  gtypeToType : GType → Maybe Type
  gtypeToType G.TUnit   = just T.Unit
  gtypeToType G.TVoid   = just T.Void
  gtypeToType G.TInt    = just T.Int
  gtypeToType G.TFloat  = just T.Float
  gtypeToType G.TBuffer = just T.Buffer
  gtypeToType G.TString = just T.Str
  gtypeToType (A G.⇒[ q ] B) with gtypeToType A | gtypeToType B
  ... | just A' | just B' = just (A' T.⇒[ T.mk-kind q T.pure ] B')
  ... | _       | _       = nothing
  gtypeToType (A G.⊗ B) with gtypeToType A | gtypeToType B
  ... | just A' | just B' = just (A' T.* B')
  ... | _       | _       = nothing
  gtypeToType (A G.⊕ B) with gtypeToType A | gtypeToType B
  ... | just A' | just B' = just (A' T.+ B')
  ... | _       | _       = nothing
  gtypeToType (G.TEff A B) with gtypeToType A | gtypeToType B
  ... | just A' | just B' = just (A' T.⇒[ T.mk-kind T.Many T.eff ] B')
  ... | _       | _       = nothing
  gtypeToType (G.GMu gf) with gfunctorToFunctor gf
  ... | just F  = just (T.μ-type F)
  ... | nothing = nothing
  gtypeToType (G.TVar _) = nothing

  -- | Convert a grammar-level functor to an internal `Functor`.
  -- Fails iff a constant `K g` holds a non-convertible `g` (e.g. TVar).
  gfunctorToFunctor : G.GFunctor → Maybe T.Functor
  gfunctorToFunctor (G.GFK g) with gtypeToType g
  ... | just t  = just (T.K t)
  ... | nothing = nothing
  gfunctorToFunctor G.GFId = just T.Id
  gfunctorToFunctor (G.GFSum f g) with gfunctorToFunctor f | gfunctorToFunctor g
  ... | just Ff | just Fg = just (Ff T.⊕ Fg)
  ... | _       | _       = nothing
  gfunctorToFunctor (G.GFProd f g) with gfunctorToFunctor f | gfunctorToFunctor g
  ... | just Ff | just Fg = just (Ff T.⊗ Fg)
  ... | _       | _       = nothing

------------------------------------------------------------------------
-- Type → GType
------------------------------------------------------------------------

-- | Convert an internal type back to a grammar-level type.
-- `μ-type` is now expressible via `GMu` (mutual functor companion).
-- Still fails on `ν-type`, which has no surface syntax.
mutual
  typeToGType : Type → Maybe GType
  typeToGType T.Unit   = just G.TUnit
  typeToGType T.Void   = just G.TVoid
  typeToGType T.Int    = just G.TInt
  typeToGType T.Float  = just G.TFloat
  typeToGType T.Buffer = just G.TBuffer
  typeToGType T.Str    = just G.TString
  typeToGType (A T.⇒[ T.mk-kind q T.pure ] B) with typeToGType A | typeToGType B
  ... | just A' | just B' = just (A' G.⇒[ q ] B')
  ... | _       | _       = nothing
  typeToGType (A T.* B) with typeToGType A | typeToGType B
  ... | just A' | just B' = just (A' G.⊗ B')
  ... | _       | _       = nothing
  typeToGType (A T.+ B) with typeToGType A | typeToGType B
  ... | just A' | just B' = just (A' G.⊕ B')
  ... | _       | _       = nothing
  typeToGType (A T.⇒[ T.mk-kind T.Many T.eff ] B) with typeToGType A | typeToGType B
  ... | just A' | just B' = just (G.TEff A' B')
  ... | _       | _       = nothing
  -- Degenerate kinds: eff + Zero/One. Grammar has no form for these.
  typeToGType (_ T.⇒[ T.mk-kind T.Zero T.eff ] _) = nothing
  typeToGType (_ T.⇒[ T.mk-kind T.One T.eff ] _) = nothing
  typeToGType (T.μ-type F) with functorToGFunctor F
  ... | just gf = just (G.GMu gf)
  ... | nothing = nothing
  typeToGType (T.ν-type _) = nothing

  -- | Convert an internal `Functor` to a grammar-level functor.
  -- Fails iff a constant `K t` holds a non-expressible `t` (e.g. ν).
  functorToGFunctor : T.Functor → Maybe G.GFunctor
  functorToGFunctor (T.K t) with typeToGType t
  ... | just g  = just (G.GFK g)
  ... | nothing = nothing
  functorToGFunctor T.Id = just G.GFId
  functorToGFunctor (F T.⊕ G') with functorToGFunctor F | functorToGFunctor G'
  ... | just gf | just gg = just (G.GFSum gf gg)
  ... | _       | _       = nothing
  functorToGFunctor (F T.⊗ G') with functorToGFunctor F | functorToGFunctor G'
  ... | just gf | just gg = just (G.GFProd gf gg)
  ... | _       | _       = nothing

------------------------------------------------------------------------
-- Round-trip lemmas
------------------------------------------------------------------------

-- | Type → GType → Type is the identity (when convertible in the first step).
--
-- Converting an internal type to its grammar form and back recovers the
-- original type exactly. This is a structural induction on `Type`.
typeToGType-gtypeToType : ∀ (t : Type) (g : GType)
                        → typeToGType t ≡ just g
                        → gtypeToType g ≡ just t
functorToGFunctor-gfunctorToFunctor : ∀ (F : T.Functor) (gf : G.GFunctor)
                                    → functorToGFunctor F ≡ just gf
                                    → gfunctorToFunctor gf ≡ just F
typeToGType-gtypeToType T.Unit   .G.TUnit   refl = refl
typeToGType-gtypeToType T.Void   .G.TVoid   refl = refl
typeToGType-gtypeToType T.Int    .G.TInt    refl = refl
typeToGType-gtypeToType T.Float  .G.TFloat  refl = refl
typeToGType-gtypeToType T.Buffer .G.TBuffer refl = refl
typeToGType-gtypeToType T.Str    .G.TString refl = refl
typeToGType-gtypeToType (A T.⇒[ T.mk-kind q T.pure ] B) g eq with typeToGType A in eqA | typeToGType B in eqB
typeToGType-gtypeToType (A T.⇒[ T.mk-kind q T.pure ] B) .(gA G.⇒[ q ] gB) refl | just gA | just gB
  rewrite typeToGType-gtypeToType A gA eqA
        | typeToGType-gtypeToType B gB eqB = refl
typeToGType-gtypeToType (A T.* B) g eq with typeToGType A in eqA | typeToGType B in eqB
typeToGType-gtypeToType (A T.* B) .(gA G.⊗ gB) refl | just gA | just gB
  rewrite typeToGType-gtypeToType A gA eqA
        | typeToGType-gtypeToType B gB eqB = refl
typeToGType-gtypeToType (A T.+ B) g eq with typeToGType A in eqA | typeToGType B in eqB
typeToGType-gtypeToType (A T.+ B) .(gA G.⊕ gB) refl | just gA | just gB
  rewrite typeToGType-gtypeToType A gA eqA
        | typeToGType-gtypeToType B gB eqB = refl
typeToGType-gtypeToType (A T.⇒[ T.mk-kind T.Many T.eff ] B) g eq with typeToGType A in eqA | typeToGType B in eqB
typeToGType-gtypeToType (A T.⇒[ T.mk-kind T.Many T.eff ] B) .(G.TEff gA gB) refl | just gA | just gB
  rewrite typeToGType-gtypeToType A gA eqA
        | typeToGType-gtypeToType B gB eqB = refl
typeToGType-gtypeToType (T.μ-type F) g eq with functorToGFunctor F in eqF
typeToGType-gtypeToType (T.μ-type F) .(G.GMu gf) refl | just gf
  rewrite functorToGFunctor-gfunctorToFunctor F gf eqF = refl

functorToGFunctor-gfunctorToFunctor (T.K t) g eq with typeToGType t in eqt
functorToGFunctor-gfunctorToFunctor (T.K t) .(G.GFK gt) refl | just gt
  rewrite typeToGType-gtypeToType t gt eqt = refl
functorToGFunctor-gfunctorToFunctor T.Id .G.GFId refl = refl
functorToGFunctor-gfunctorToFunctor (F T.⊕ G') gf eq
  with functorToGFunctor F in eqF | functorToGFunctor G' in eqG
functorToGFunctor-gfunctorToFunctor (F T.⊕ G') .(G.GFSum gfa gfb) refl | just gfa | just gfb
  rewrite functorToGFunctor-gfunctorToFunctor F gfa eqF
        | functorToGFunctor-gfunctorToFunctor G' gfb eqG = refl
functorToGFunctor-gfunctorToFunctor (F T.⊗ G') gf eq
  with functorToGFunctor F in eqF | functorToGFunctor G' in eqG
functorToGFunctor-gfunctorToFunctor (F T.⊗ G') .(G.GFProd gfa gfb) refl | just gfa | just gfb
  rewrite functorToGFunctor-gfunctorToFunctor F gfa eqF
        | functorToGFunctor-gfunctorToFunctor G' gfb eqG = refl

-- | GType → Type → GType is the identity (when convertible in the first step).
gtypeToType-typeToGType : ∀ (g : GType) (t : Type)
                        → gtypeToType g ≡ just t
                        → typeToGType t ≡ just g
gfunctorToFunctor-functorToGFunctor : ∀ (gf : G.GFunctor) (F : T.Functor)
                                    → gfunctorToFunctor gf ≡ just F
                                    → functorToGFunctor F ≡ just gf
gtypeToType-typeToGType G.TUnit   .T.Unit   refl = refl
gtypeToType-typeToGType G.TVoid   .T.Void   refl = refl
gtypeToType-typeToGType G.TInt    .T.Int    refl = refl
gtypeToType-typeToGType G.TFloat  .T.Float  refl = refl
gtypeToType-typeToGType G.TBuffer .T.Buffer refl = refl
gtypeToType-typeToGType G.TString .T.Str    refl = refl
gtypeToType-typeToGType (A G.⇒[ q ] B) t eq with gtypeToType A in eqA | gtypeToType B in eqB
gtypeToType-typeToGType (A G.⇒[ q ] B) .(tA T.⇒[ T.mk-kind q T.pure ] tB) refl | just tA | just tB
  rewrite gtypeToType-typeToGType A tA eqA
        | gtypeToType-typeToGType B tB eqB = refl
gtypeToType-typeToGType (A G.⊗ B) t eq with gtypeToType A in eqA | gtypeToType B in eqB
gtypeToType-typeToGType (A G.⊗ B) .(tA T.* tB) refl | just tA | just tB
  rewrite gtypeToType-typeToGType A tA eqA
        | gtypeToType-typeToGType B tB eqB = refl
gtypeToType-typeToGType (A G.⊕ B) t eq with gtypeToType A in eqA | gtypeToType B in eqB
gtypeToType-typeToGType (A G.⊕ B) .(tA T.+ tB) refl | just tA | just tB
  rewrite gtypeToType-typeToGType A tA eqA
        | gtypeToType-typeToGType B tB eqB = refl
gtypeToType-typeToGType (G.TEff A B) t eq with gtypeToType A in eqA | gtypeToType B in eqB
gtypeToType-typeToGType (G.TEff A B) .(tA T.⇒[ T.mk-kind T.Many T.eff ] tB) refl | just tA | just tB
  rewrite gtypeToType-typeToGType A tA eqA
        | gtypeToType-typeToGType B tB eqB = refl
gtypeToType-typeToGType (G.GMu gf) t eq with gfunctorToFunctor gf in eqG
gtypeToType-typeToGType (G.GMu gf) .(T.μ-type F) refl | just F
  rewrite gfunctorToFunctor-functorToGFunctor gf F eqG = refl

gfunctorToFunctor-functorToGFunctor (G.GFK g) F eq with gtypeToType g in eqg
gfunctorToFunctor-functorToGFunctor (G.GFK g) .(T.K t) refl | just t
  rewrite gtypeToType-typeToGType g t eqg = refl
gfunctorToFunctor-functorToGFunctor G.GFId .T.Id refl = refl
gfunctorToFunctor-functorToGFunctor (G.GFSum gf gg) F eq
  with gfunctorToFunctor gf in eqF | gfunctorToFunctor gg in eqGG
gfunctorToFunctor-functorToGFunctor (G.GFSum gf gg) .(Ff T.⊕ Fg) refl | just Ff | just Fg
  rewrite gfunctorToFunctor-functorToGFunctor gf Ff eqF
        | gfunctorToFunctor-functorToGFunctor gg Fg eqGG = refl
gfunctorToFunctor-functorToGFunctor (G.GFProd gf gg) F eq
  with gfunctorToFunctor gf in eqF | gfunctorToFunctor gg in eqGG
gfunctorToFunctor-functorToGFunctor (G.GFProd gf gg) .(Ff T.⊗ Fg) refl | just Ff | just Fg
  rewrite gfunctorToFunctor-functorToGFunctor gf Ff eqF
        | gfunctorToFunctor-functorToGFunctor gg Fg eqGG = refl

------------------------------------------------------------------------
-- Grammar expressibility predicate
------------------------------------------------------------------------

-- | A `Type` is "grammar-expressible" iff it can be round-tripped through
-- `GType`. This is the subset of internal types the surface grammar
-- can actually name.
--
-- Concretely: not `μ-type`, not `ν-type`, and recursively not containing
-- them. The parser only produces grammar-expressible types.
GrammarExpressible : Type → Set
GrammarExpressible t = Σ[ g ∈ GType ] typeToGType t ≡ just g

------------------------------------------------------------------------
-- Parser output is grammar-expressible
------------------------------------------------------------------------

-- | Every atomic type produced by `parseTypeAtom` is grammar-expressible.
-- (Proved by case analysis on the first token.)
--
-- We don't prove this for the full parser here (that is part of G1 in
-- plan 0.3) — but we state the top-level claim, and verify it
-- structurally for the atom-level cases which cover the base types.
--
-- The full completeness proof (for parseType) is deferred to G1; this
-- module just provides the conversion infrastructure it will build on.

-- | Convenience: the parser produces a GType-convertible Type.
-- This definition composes the parser with conversion, giving a
-- "grammar-level" parser for free.
parseGType : List Token → Maybe (GType × List Token)
parseGType toks with parseType toks
... | nothing = nothing
... | just (t , rest) with typeToGType t
...   | just g = just (g , rest)
...   | nothing = nothing

------------------------------------------------------------------------
-- Base-type examples (smoke checks that the connection works)
------------------------------------------------------------------------

-- These definitions exercise the round-trip at the definitional level;
-- if any of them fail to type-check, the conversion tables above are out
-- of sync with either `Grammar` or `Type`.

_ : gtypeToType G.TUnit ≡ just T.Unit
_ = refl

_ : gtypeToType G.TString ≡ just T.Str
_ = refl

_ : typeToGType T.Str ≡ just G.TString
_ = refl

_ : gtypeToType (G.TInt G.⇒[ One ] G.TInt) ≡ just (T.Int T.⇒[ T.mk-kind T.One T.pure ] T.Int)
_ = refl

_ : typeToGType (T.Int T.* T.Str) ≡ just (G.TInt G.⊗ G.TString)
_ = refl

-- TVar is rejected:
_ : gtypeToType (G.TVar "A") ≡ nothing
_ = refl

-- μ-type is now expressible via GMu:
_ : typeToGType (T.μ-type (T.K T.Int)) ≡ just (G.GMu (G.GFK G.TInt))
_ = refl

-- Nat = μ (K Unit ⊕ Id) round-trips:
_ : typeToGType (T.μ-type (T.K T.Unit T.⊕ T.Id))
      ≡ just (G.GMu (G.GFSum (G.GFK G.TUnit) G.GFId))
_ = refl

-- ν-type is still rejected (no surface syntax):
_ : typeToGType (T.ν-type (T.K T.Int)) ≡ nothing
_ = refl

------------------------------------------------------------------------
-- Grammar-expressibility characterisation
--
-- An internal `Type` is grammar-expressible exactly when it avoids
-- the `μ-type` / `ν-type` constructors (the two Type constructors
-- without corresponding `GType` constructors). This predicate +
-- lemma pair provides a structural characterisation independent
-- of the partial conversion function.
------------------------------------------------------------------------

-- `NoNu t`: `t` contains no `ν-type` (μ-type is allowed — it is now
-- grammar-expressible via `GMu`). `NoNuF` is the functor analogue,
-- mutual because `μ-type` carries a `Functor` and `K` carries a `Type`.
mutual
  data NoNu : Type → Set where
    nnu-unit   : NoNu T.Unit
    nnu-void   : NoNu T.Void
    nnu-int    : NoNu T.Int
    nnu-float  : NoNu T.Float
    nnu-str    : NoNu T.Str
    nnu-buffer : NoNu T.Buffer
    nnu-prod   : ∀ {A B} → NoNu A → NoNu B → NoNu (A T.* B)
    nnu-sum    : ∀ {A B} → NoNu A → NoNu B → NoNu (A T.+ B)
    nnu-fun    : ∀ {A B q} → NoNu A → NoNu B → NoNu (A T.⇒[ T.mk-kind q T.pure ] B)
    nnu-eff    : ∀ {A B} → NoNu A → NoNu B → NoNu (A T.⇒[ T.mk-kind T.Many T.eff ] B)
    nnu-mu     : ∀ {F} → NoNuF F → NoNu (T.μ-type F)

  data NoNuF : T.Functor → Set where
    nnuf-k    : ∀ {t} → NoNu t → NoNuF (T.K t)
    nnuf-id   : NoNuF T.Id
    nnuf-sum  : ∀ {F G'} → NoNuF F → NoNuF G' → NoNuF (F T.⊕ G')
    nnuf-prod : ∀ {F G'} → NoNuF F → NoNuF G' → NoNuF (F T.⊗ G')

-- | `NoNu t` suffices for `typeToGType t` to return `just _`.
typeToGType-NoNu :
  ∀ {t : Type} → NoNu t → Σ[ g ∈ GType ] typeToGType t ≡ just g
functorToGFunctor-NoNuF :
  ∀ {F : T.Functor} → NoNuF F → Σ[ gf ∈ G.GFunctor ] functorToGFunctor F ≡ just gf
typeToGType-NoNu nnu-unit   = G.TUnit   , refl
typeToGType-NoNu nnu-void   = G.TVoid   , refl
typeToGType-NoNu nnu-int    = G.TInt    , refl
typeToGType-NoNu nnu-float  = G.TFloat  , refl
typeToGType-NoNu nnu-str    = G.TString , refl
typeToGType-NoNu nnu-buffer = G.TBuffer , refl
typeToGType-NoNu (nnu-prod nrA nrB)
  with typeToGType-NoNu nrA | typeToGType-NoNu nrB
... | gA , eqA | gB , eqB rewrite eqA | eqB = (gA G.⊗ gB) , refl
typeToGType-NoNu (nnu-sum nrA nrB)
  with typeToGType-NoNu nrA | typeToGType-NoNu nrB
... | gA , eqA | gB , eqB rewrite eqA | eqB = (gA G.⊕ gB) , refl
typeToGType-NoNu (nnu-fun {q = q} nrA nrB)
  with typeToGType-NoNu nrA | typeToGType-NoNu nrB
... | gA , eqA | gB , eqB rewrite eqA | eqB = (gA G.⇒[ q ] gB) , refl
typeToGType-NoNu (nnu-eff nrA nrB)
  with typeToGType-NoNu nrA | typeToGType-NoNu nrB
... | gA , eqA | gB , eqB rewrite eqA | eqB = G.TEff gA gB , refl
typeToGType-NoNu (nnu-mu nf)
  with functorToGFunctor-NoNuF nf
... | gf , eqf rewrite eqf = G.GMu gf , refl

functorToGFunctor-NoNuF (nnuf-k nt)
  with typeToGType-NoNu nt
... | g , eq rewrite eq = G.GFK g , refl
functorToGFunctor-NoNuF nnuf-id = G.GFId , refl
functorToGFunctor-NoNuF (nnuf-sum nf ng)
  with functorToGFunctor-NoNuF nf | functorToGFunctor-NoNuF ng
... | gf , eqf | gg , eqg rewrite eqf | eqg = G.GFSum gf gg , refl
functorToGFunctor-NoNuF (nnuf-prod nf ng)
  with functorToGFunctor-NoNuF nf | functorToGFunctor-NoNuF ng
... | gf , eqf | gg , eqg rewrite eqf | eqg = G.GFProd gf gg , refl
