-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Type — the compiler's types as the Spec's (plan
-- 0.121, the core bridge).
--
-- `TyR Δ A A′`: the compiler's type `A` is the Spec's `A′ : Ty m`. Plan
-- 0.122: the two are one grammar, the relation the identity's graph
-- (`TyR-≡`), kept by its constructors for the front-end bridge.
------------------------------------------------------------------------

import Once.Spec.Grade
module Once.Adequacy.SpecCore.Type where


open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

import Once.Spec.Grade as LG
import Once.Spec.Grade as SG
import Once.Spec.Type as ST
import Once.Spec.Sub as SS
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS; kS)

------------------------------------------------------------------------
-- Grades
------------------------------------------------------------------------

qS-injective : ∀ {q q′} → qS q ≡ qS q′ → q ≡ q′
qS-injective {LG.Zero} {LG.Zero} _ = refl
qS-injective {LG.One}  {LG.One}  _ = refl
qS-injective {LG.Many} {LG.Many} _ = refl
qS-injective {LG.Zero} {LG.One}  ()
qS-injective {LG.Zero} {LG.Many} ()
qS-injective {LG.One}  {LG.Zero} ()
qS-injective {LG.One}  {LG.Many} ()
qS-injective {LG.Many} {LG.Zero} ()
qS-injective {LG.Many} {LG.One}  ()

φS-injective : ∀ {φ φ′} → φS φ ≡ φS φ′ → φ ≡ φ′
φS-injective {LG.pureᶠ} {LG.pureᶠ} _ = refl
φS-injective {LG.actᶠ}  {LG.actᶠ}  _ = refl
φS-injective {LG.pureᶠ} {LG.actᶠ}  ()
φS-injective {LG.actᶠ}  {LG.pureᶠ} ()

πS-injective : ∀ {π π′} → πS π ≡ πS π′ → π ≡ π′
πS-injective {LG.pure} {LG.pure} _ = refl
πS-injective {LG.act}  {LG.act}  _ = refl
πS-injective {LG.eff}  {LG.eff}  _ = refl
πS-injective {LG.pure} {LG.act}  ()
πS-injective {LG.pure} {LG.eff}  ()
πS-injective {LG.act}  {LG.pure} ()
πS-injective {LG.act}  {LG.eff}  ()
πS-injective {LG.eff}  {LG.pure} ()
πS-injective {LG.eff}  {LG.act}  ()

kS-injective : ∀ {k k′} → kS k ≡ kS k′ → k ≡ k′
kS-injective {LG.mk-kind q π} {LG.mk-kind q′ π′} e =
  mk (qS-injective (cong SG.ArrowKind.quantity e)) (πS-injective (cong SG.ArrowKind.purity e))
  where
    mk : q ≡ q′ → π ≡ π′ → LG.mk-kind q π ≡ LG.mk-kind q′ π′
    mk refl refl = refl

πS-fin : ∀ φ → πS (LG.fin φ) ≡ SG.fin (φS φ)
πS-fin LG.pureᶠ = refl
πS-fin LG.actᶠ  = refl

⊑π-S : ∀ {π π′} → π Once.Spec.Grade.⊑π π′ → πS π SG.⊑π πS π′
⊑π-S Once.Spec.Grade.⊑-pure = SG.⊑-pure
⊑π-S Once.Spec.Grade.⊑-eff  = SG.⊑-eff
⊑π-S Once.Spec.Grade.⊑-pe   = SG.⊑-pe
⊑π-S Once.Spec.Grade.⊑-act  = SG.⊑-act
⊑π-S Once.Spec.Grade.⊑-pa   = SG.⊑-pa
⊑π-S Once.Spec.Grade.⊑-ae   = SG.⊑-ae

⊑π-L : ∀ π π′ → πS π SG.⊑π πS π′ → π Once.Spec.Grade.⊑π π′
⊑π-L LG.pure LG.pure _ = Once.Spec.Grade.⊑-pure
⊑π-L LG.pure LG.act  _ = Once.Spec.Grade.⊑-pa
⊑π-L LG.pure LG.eff  _ = Once.Spec.Grade.⊑-pe
⊑π-L LG.act  LG.act  _ = Once.Spec.Grade.⊑-act
⊑π-L LG.act  LG.eff  _ = Once.Spec.Grade.⊑-ae
⊑π-L LG.eff  LG.eff  _ = Once.Spec.Grade.⊑-eff
⊑π-L LG.act  LG.pure ()
⊑π-L LG.eff  LG.pure ()
⊑π-L LG.eff  LG.act  ()

-- a stream's grade, compared as a grade
⊑φ-S : ∀ φ φ′ → LG.fin φ Once.Spec.Grade.⊑π LG.fin φ′ → SG.fin (φS φ) SG.⊑π SG.fin (φS φ′)
⊑φ-S LG.pureᶠ LG.pureᶠ _ = SG.⊑-pure
⊑φ-S LG.pureᶠ LG.actᶠ  _ = SG.⊑-pa
⊑φ-S LG.actᶠ  LG.actᶠ  _ = SG.⊑-act
⊑φ-S LG.actᶠ  LG.pureᶠ ()

⊑φ-L : ∀ φ φ′ → SG.fin (φS φ) SG.⊑π SG.fin (φS φ′) → LG.fin φ Once.Spec.Grade.⊑π LG.fin φ′
⊑φ-L LG.pureᶠ LG.pureᶠ _ = Once.Spec.Grade.⊑-pure
⊑φ-L LG.pureᶠ LG.actᶠ  _ = Once.Spec.Grade.⊑-pa
⊑φ-L LG.actᶠ  LG.actᶠ  _ = Once.Spec.Grade.⊑-act
⊑φ-L LG.actᶠ  LG.pureᶠ ()

·p-S : ∀ π π′ → πS (π LG.·p π′) ≡ πS π SG.·p πS π′
·p-S LG.pure π′      = refl
·p-S LG.act  LG.pure = refl
·p-S LG.act  LG.act  = refl
·p-S LG.act  LG.eff  = refl
·p-S LG.eff  π′      = refl

positionGrade-S : ∀ q π → πS (LG.positionGrade q π) ≡ SG.positionGrade (qS q) (πS π)
positionGrade-S LG.Zero π = refl
positionGrade-S LG.One  π = refl
positionGrade-S LG.Many π = refl

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- Plan 0.122: the compiler's types ARE the Spec's (a polymorphic body is
-- checked over its parameters, `var j`); `TyR` is the identity's graph, kept
-- by its constructors for the front-end bridge's case analyses.
mutual
  data TyR {m} (Δ : ST.KCtx m) : ST.Ty m → ST.Ty m → Set where
    r-unit  : TyR Δ ST.Unit ST.Unit
    r-void  : TyR Δ ST.Void ST.Void
    r-int   : TyR Δ ST.Int ST.Int
    r-float : TyR Δ ST.Float ST.Float
    r-*     : ∀ {A A′ B B′} → TyR Δ A A′ → TyR Δ B B′ → TyR Δ (A ST.* B) (A′ ST.* B′)
    r-+     : ∀ {A A′ B B′} → TyR Δ A A′ → TyR Δ B B′ → TyR Δ (A ST.+ B) (A′ ST.+ B′)
    -- (the Spec's grades as equations, so that a derivation at a given
    -- Spec type can be taken apart)
    r-⇒     : ∀ {A A′ B B′ k k′} → kS k ≡ k′ → TyR Δ A A′ → TyR Δ B B′
            → TyR Δ (A ST.⇒[ k ] B) (A′ ST.⇒[ k′ ] B′)
    r-μ     : ∀ {F F′} → FunR Δ F F′ → TyR Δ (ST.μ F) (ST.μ F′)
    r-ν     : ∀ {F F′ φ f} → φS φ ≡ f → FunR Δ F F′ → TyR Δ (ST.ν F φ) (ST.ν F′ f)
    -- a parameter
    r-var   : ∀ (j : Fin m) → TyR Δ (ST.var j) (ST.var j)

  data FunR {m} (Δ : ST.KCtx m) : ST.Fun m → ST.Fun m → Set where
    r-K  : ∀ {A A′} → TyR Δ A A′ → FunR Δ (ST.K A) (ST.K A′)
    r-Id : FunR Δ ST.Id ST.Id
    r-⊕  : ∀ {F F′ G G′} → FunR Δ F F′ → FunR Δ G G′ → FunR Δ (F ST.⊕ G) (F′ ST.⊕ G′)
    r-⊗  : ∀ {F F′ G G′} → FunR Δ F F′ → FunR Δ G G′ → FunR Δ (F ST.⊗ G) (F′ ST.⊗ G′)

module _ {m} {Δ : ST.KCtx m} where

  -- (the graph's canonical proof)
  mutual
    tyR : ∀ (A : ST.Ty m) → TyR Δ A A
    tyR (ST.var j) = r-var j
    tyR ST.Unit    = r-unit
    tyR ST.Void    = r-void
    tyR ST.Int     = r-int
    tyR ST.Float   = r-float
    tyR (A ST.* B) = r-* (tyR A) (tyR B)
    tyR (A ST.+ B) = r-+ (tyR A) (tyR B)
    tyR (A ST.⇒[ LG.mk-kind q π ] B) = r-⇒ (kS-id q π) (tyR A) (tyR B)
      where
        kS-id : ∀ q π → kS (LG.mk-kind q π) ≡ LG.mk-kind q π
        kS-id LG.Zero LG.pure = refl
        kS-id LG.Zero LG.act  = refl
        kS-id LG.Zero LG.eff  = refl
        kS-id LG.One  LG.pure = refl
        kS-id LG.One  LG.act  = refl
        kS-id LG.One  LG.eff  = refl
        kS-id LG.Many LG.pure = refl
        kS-id LG.Many LG.act  = refl
        kS-id LG.Many LG.eff  = refl
    tyR (ST.μ F)   = r-μ (funR F)
    tyR (ST.ν F φ) = r-ν (φS-id φ) (funR F)
      where
        φS-id : ∀ φ → φS φ ≡ φ
        φS-id LG.pureᶠ = refl
        φS-id LG.actᶠ  = refl

    funR : ∀ (F : ST.Fun m) → FunR Δ F F
    funR (ST.K A)   = r-K (tyR A)
    funR ST.Id      = r-Id
    funR (F ST.⊕ G) = r-⊕ (funR F) (funR G)
    funR (F ST.⊗ G) = r-⊗ (funR F) (funR G)

  mutual
    TyR-uniqueˢ : ∀ {A A′ A″} → TyR Δ A A′ → TyR Δ A A″ → A′ ≡ A″
    TyR-uniqueˢ r-unit    r-unit      = refl
    TyR-uniqueˢ r-void    r-void      = refl
    TyR-uniqueˢ r-int     r-int       = refl
    TyR-uniqueˢ r-float   r-float     = refl
    TyR-uniqueˢ (r-* a b) (r-* a′ b′) = cong₂ ST._*_ (TyR-uniqueˢ a a′) (TyR-uniqueˢ b b′)
    TyR-uniqueˢ (r-+ a b) (r-+ a′ b′) = cong₂ ST._+_ (TyR-uniqueˢ a a′) (TyR-uniqueˢ b b′)
    TyR-uniqueˢ (r-⇒ refl a b) (r-⇒ refl a′ b′) = cong₂ (λ x y → x ST.⇒[ _ ] y) (TyR-uniqueˢ a a′) (TyR-uniqueˢ b b′)
    TyR-uniqueˢ (r-μ f)   (r-μ f′)    = cong ST.μ (FunR-uniqueˢ f f′)
    TyR-uniqueˢ (r-ν refl f) (r-ν refl f′) = cong (λ G → ST.ν G _) (FunR-uniqueˢ f f′)
    TyR-uniqueˢ (r-var j) (r-var .j)  = refl

    FunR-uniqueˢ : ∀ {F F′ F″} → FunR Δ F F′ → FunR Δ F F″ → F′ ≡ F″
    FunR-uniqueˢ (r-K a)   (r-K a′)    = cong ST.K (TyR-uniqueˢ a a′)
    FunR-uniqueˢ r-Id      r-Id        = refl
    FunR-uniqueˢ (r-⊕ f g) (r-⊕ f′ g′) = cong₂ ST._⊕_ (FunR-uniqueˢ f f′) (FunR-uniqueˢ g g′)
    FunR-uniqueˢ (r-⊗ f g) (r-⊗ f′ g′) = cong₂ ST._⊗_ (FunR-uniqueˢ f f′) (FunR-uniqueˢ g g′)

  mutual
    TyR-uniqueˡ : ∀ {A B A′} → TyR Δ A A′ → TyR Δ B A′ → A ≡ B
    TyR-uniqueˡ r-unit    r-unit      = refl
    TyR-uniqueˡ r-void    r-void      = refl
    TyR-uniqueˡ r-int     r-int       = refl
    TyR-uniqueˡ r-float   r-float     = refl
    TyR-uniqueˡ (r-* a b) (r-* a′ b′) = cong₂ ST._*_ (TyR-uniqueˡ a a′) (TyR-uniqueˡ b b′)
    TyR-uniqueˡ (r-+ a b) (r-+ a′ b′) = cong₂ ST._+_ (TyR-uniqueˡ a a′) (TyR-uniqueˡ b b′)
    TyR-uniqueˡ (r-⇒ e a b) (r-⇒ e′ a′ b′) =
      arr (kS-injective (trans e (sym e′))) (TyR-uniqueˡ a a′) (TyR-uniqueˡ b b′)
      where
        arr : ∀ {k k′ A B C D} → k ≡ k′ → A ≡ C → B ≡ D → (A ST.⇒[ k ] B) ≡ (C ST.⇒[ k′ ] D)
        arr refl refl refl = refl
    TyR-uniqueˡ (r-μ f)   (r-μ f′)    = cong ST.μ (FunR-uniqueˡ f f′)
    TyR-uniqueˡ (r-ν e f) (r-ν e′ f′) = ν-eq (φS-injective (trans e (sym e′))) (FunR-uniqueˡ f f′)
      where
        ν-eq : ∀ {φ φ′ F G} → φ ≡ φ′ → F ≡ G → ST.ν F φ ≡ ST.ν G φ′
        ν-eq refl refl = refl
    TyR-uniqueˡ (r-var j) (r-var .j)  = refl

    FunR-uniqueˡ : ∀ {F G F′} → FunR Δ F F′ → FunR Δ G F′ → F ≡ G
    FunR-uniqueˡ (r-K a)   (r-K a′)    = cong ST.K (TyR-uniqueˡ a a′)
    FunR-uniqueˡ r-Id      r-Id        = refl
    FunR-uniqueˡ (r-⊕ f g) (r-⊕ f′ g′) = cong₂ ST._⊕_ (FunR-uniqueˡ f f′) (FunR-uniqueˡ g g′)
    FunR-uniqueˡ (r-⊗ f g) (r-⊗ f′ g′) = cong₂ ST._⊗_ (FunR-uniqueˡ f f′) (FunR-uniqueˡ g g′)

  -- The graph is the identity.
  TyR-≡ : ∀ {A A′} → TyR Δ A A′ → A ≡ A′
  TyR-≡ {A} r = TyR-uniqueˢ (tyR A) r

  FunR-≡ : ∀ {F F′} → FunR Δ F F′ → F ≡ F′
  FunR-≡ {F} f = FunR-uniqueˢ (funR F) f

  -- Functor application commutes.
  TyR-⟦⟧ : ∀ {F F′ A A′} → FunR Δ F F′ → TyR Δ A A′ → TyR Δ (ST.⟦ F ⟧F A) (ST.⟦ F′ ⟧F A′)
  TyR-⟦⟧ (r-K b)   a = b
  TyR-⟦⟧ r-Id      a = a
  TyR-⟦⟧ (r-⊕ f g) a = r-+ (TyR-⟦⟧ f a) (TyR-⟦⟧ g a)
  TyR-⟦⟧ (r-⊗ f g) a = r-* (TyR-⟦⟧ f a) (TyR-⟦⟧ g a)

  ------------------------------------------------------------------------
  -- Base types and well-formed functors: the Spec's, at the kinds

  base-S : ∀ {A A′} → ST.Base Δ A → TyR Δ A A′ → ST.Base Δ A′
  base-S b r = subst (ST.Base Δ) (TyR-≡ r) b

  base-L : ∀ {A A′} → ST.Base Δ A′ → TyR Δ A A′ → ST.Base Δ A
  base-L b r = subst (ST.Base Δ) (sym (TyR-≡ r)) b

  wf-S : ∀ {F F′} → ST.WFFun Δ F → FunR Δ F F′ → ST.WFFun Δ F′
  wf-S w f = subst (ST.WFFun Δ) (FunR-≡ f) w

  wf-L : ∀ {F F′} → ST.WFFun Δ F′ → FunR Δ F F′ → ST.WFFun Δ F
  wf-L w f = subst (ST.WFFun Δ) (sym (FunR-≡ f)) w

  ------------------------------------------------------------------------
  -- Subtyping, both ways (one order)

  sub-S : ∀ {A B A′ B′} → A SS.<: B → TyR Δ A A′ → TyR Δ B B′ → A′ SS.<: B′
  sub-S p ra rb = subst₂ SS._<:_ (TyR-≡ ra) (TyR-≡ rb) p

  sub-L : ∀ {A B A′ B′} → A′ SS.<: B′ → TyR Δ A A′ → TyR Δ B B′ → A SS.<: B
  sub-L p ra rb = subst₂ SS._<:_ (sym (TyR-≡ ra)) (sym (TyR-≡ rb)) p
