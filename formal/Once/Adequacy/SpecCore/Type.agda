-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Type — the compiler's types as the Spec's (plan
-- 0.121, the core bridge).
--
-- `TyR Δ A A′`: the compiler's type `A` is the Spec's `A′ : Ty m`. The two
-- grammars are the same but for type parameters: inside a polymorphic body
-- the compiler writes the `i`-th one as the constant `rigid k i`, the Spec as
-- the variable `var j` of the kinding context `Δ`, at `toℕ j ≡ i` and of the
-- same kind. The relation is a bijection (`TyR-uniqueˢ`, `TyR-uniqueˡ`), and
-- it carries the grades, the subtyping order, functor application and base
-- types both ways — what the core judgments are built from.
------------------------------------------------------------------------

import Once.Spec.Grade
module Once.Adequacy.SpecCore.Type where


open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

import Once.Spec.Grade as LG
import Once.Spec.Grade as SG
import Once.Internal.Type as LT
import Once.Internal.Type.Sub as LS
import Once.Internal.Type.WellFormed as LW
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

kindS : LT.TKind → ST.Kind
kindS LT.k-base = ST.base
kindS LT.k-any  = ST.any

kindS-injective : ∀ {k k′} → kindS k ≡ kindS k′ → k ≡ k′
kindS-injective {LT.k-base} {LT.k-base} _ = refl
kindS-injective {LT.k-any}  {LT.k-any}  _ = refl
kindS-injective {LT.k-base} {LT.k-any}  ()
kindS-injective {LT.k-any}  {LT.k-base} ()

mutual
  data TyR {m} (Δ : ST.KCtx m) : LT.Type → ST.Ty m → Set where
    r-unit  : TyR Δ LT.Unit ST.Unit
    r-void  : TyR Δ LT.Void ST.Void
    r-int   : TyR Δ LT.Int ST.Int
    r-float : TyR Δ LT.Float ST.Float
    r-*     : ∀ {A A′ B B′} → TyR Δ A A′ → TyR Δ B B′ → TyR Δ (A LT.* B) (A′ ST.* B′)
    r-+     : ∀ {A A′ B B′} → TyR Δ A A′ → TyR Δ B B′ → TyR Δ (A LT.+ B) (A′ ST.+ B′)
    -- (the Spec's grades as equations, so that a derivation at a given
    -- Spec type can be taken apart)
    r-⇒     : ∀ {A A′ B B′ k k′} → kS k ≡ k′ → TyR Δ A A′ → TyR Δ B B′
            → TyR Δ (A LT.⇒[ k ] B) (A′ ST.⇒[ k′ ] B′)
    r-μ     : ∀ {F F′} → FunR Δ F F′ → TyR Δ (LT.μ-type F) (ST.μ F′)
    r-ν     : ∀ {F F′ φ f} → φS φ ≡ f → FunR Δ F F′ → TyR Δ (LT.ν-type F φ) (ST.ν F′ f)
    -- the `i`-th parameter, of its kind
    r-rigid : ∀ {k i} (j : Fin m) → toℕ j ≡ i → Δ j ≡ kindS k → TyR Δ (LT.rigid k i) (ST.var j)

  data FunR {m} (Δ : ST.KCtx m) : LT.Functor → ST.Fun m → Set where
    r-K  : ∀ {A A′} → TyR Δ A A′ → FunR Δ (LT.K A) (ST.K A′)
    r-Id : FunR Δ LT.Id ST.Id
    r-⊕  : ∀ {F F′ G G′} → FunR Δ F F′ → FunR Δ G G′ → FunR Δ (F LT.⊕ G) (F′ ST.⊕ G′)
    r-⊗  : ∀ {F F′ G G′} → FunR Δ F F′ → FunR Δ G G′ → FunR Δ (F LT.⊗ G) (F′ ST.⊗ G′)

module _ {m} {Δ : ST.KCtx m} where

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
    TyR-uniqueˢ (r-rigid j e _) (r-rigid j′ e′ _) = cong ST.var (toℕ-injective (trans e (sym e′)))

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
    TyR-uniqueˡ (r-* a b) (r-* a′ b′) = cong₂ LT._*_ (TyR-uniqueˡ a a′) (TyR-uniqueˡ b b′)
    TyR-uniqueˡ (r-+ a b) (r-+ a′ b′) = cong₂ LT._+_ (TyR-uniqueˡ a a′) (TyR-uniqueˡ b b′)
    TyR-uniqueˡ (r-⇒ e a b) (r-⇒ e′ a′ b′) =
      arr (kS-injective (trans e (sym e′))) (TyR-uniqueˡ a a′) (TyR-uniqueˡ b b′)
      where
        arr : ∀ {k k′ A B C D} → k ≡ k′ → A ≡ C → B ≡ D → (A LT.⇒[ k ] B) ≡ (C LT.⇒[ k′ ] D)
        arr refl refl refl = refl
    TyR-uniqueˡ (r-μ f)   (r-μ f′)    = cong LT.μ-type (FunR-uniqueˡ f f′)
    TyR-uniqueˡ (r-ν e f) (r-ν e′ f′) = ν-eq (φS-injective (trans e (sym e′))) (FunR-uniqueˡ f f′)
      where
        ν-eq : ∀ {φ φ′ F G} → φ ≡ φ′ → F ≡ G → LT.ν-type F φ ≡ LT.ν-type G φ′
        ν-eq refl refl = refl
    TyR-uniqueˡ (r-rigid j e k) (r-rigid .j e′ k′) = rig (trans (sym e) e′) (kindS-injective (trans (sym k) k′))
      where
        rig : ∀ {i i′ κ κ′} → i ≡ i′ → κ ≡ κ′ → LT.rigid κ i ≡ LT.rigid κ′ i′
        rig refl refl = refl

    FunR-uniqueˡ : ∀ {F G F′} → FunR Δ F F′ → FunR Δ G F′ → F ≡ G
    FunR-uniqueˡ (r-K a)   (r-K a′)    = cong LT.K (TyR-uniqueˡ a a′)
    FunR-uniqueˡ r-Id      r-Id        = refl
    FunR-uniqueˡ (r-⊕ f g) (r-⊕ f′ g′) = cong₂ LT._⊕_ (FunR-uniqueˡ f f′) (FunR-uniqueˡ g g′)
    FunR-uniqueˡ (r-⊗ f g) (r-⊗ f′ g′) = cong₂ LT._⊗_ (FunR-uniqueˡ f f′) (FunR-uniqueˡ g g′)

  -- Functor application commutes.
  TyR-⟦⟧ : ∀ {F F′ A A′} → FunR Δ F F′ → TyR Δ A A′ → TyR Δ (LT.⟦ F ⟧T A) (ST.⟦ F′ ⟧F A′)
  TyR-⟦⟧ (r-K b)   a = b
  TyR-⟦⟧ r-Id      a = a
  TyR-⟦⟧ (r-⊕ f g) a = r-+ (TyR-⟦⟧ f a) (TyR-⟦⟧ g a)
  TyR-⟦⟧ (r-⊗ f g) a = r-* (TyR-⟦⟧ f a) (TyR-⟦⟧ g a)

  ------------------------------------------------------------------------
  -- Base types and well-formed functors

  base-S : ∀ {A A′} → LW.IsBaseType A → TyR Δ A A′ → ST.Base Δ A′
  base-S LW.base-Unit   r-unit    = ST.b-Unit
  base-S LW.base-Void   r-void    = ST.b-Void
  base-S LW.base-Int    r-int     = ST.b-Int
  base-S LW.base-Float  r-float   = ST.b-Float
  base-S (LW.base-Prod a b) (r-* ra rb) = ST.b-* (base-S a ra) (base-S b rb)
  base-S (LW.base-Sum a b)  (r-+ ra rb) = ST.b-+ (base-S a ra) (base-S b rb)
  base-S LW.base-rigid  (r-rigid j _ k) = ST.b-var k

  base-L : ∀ {A A′} → ST.Base Δ A′ → TyR Δ A A′ → LW.IsBaseType A
  base-L ST.b-Unit   r-unit    = LW.base-Unit
  base-L ST.b-Void   r-void    = LW.base-Void
  base-L ST.b-Int    r-int     = LW.base-Int
  base-L ST.b-Float  r-float   = LW.base-Float
  base-L (ST.b-* a b) (r-* ra rb) = LW.base-Prod (base-L a ra) (base-L b rb)
  base-L (ST.b-+ a b) (r-+ ra rb) = LW.base-Sum (base-L a ra) (base-L b rb)
  base-L (ST.b-var e) (r-rigid {k = k} j _ k′) = rigid-base k (kindS-injective (trans (sym k′) e))
    where
      rigid-base : ∀ {i} κ → κ ≡ LT.k-base → LW.IsBaseType (LT.rigid κ i)
      rigid-base .LT.k-base refl = LW.base-rigid

  wf-S : ∀ {F F′} → LW.WellFormedF F → FunR Δ F F′ → ST.WFFun Δ F′
  wf-S (LW.wf-K b)      (r-K a)   = ST.wf-K (base-S b a)
  wf-S LW.wf-Id         r-Id      = ST.wf-Id
  wf-S (LW.wf-Sum f g)  (r-⊕ a b) = ST.wf-⊕ (wf-S f a) (wf-S g b)
  wf-S (LW.wf-Prod f g) (r-⊗ a b) = ST.wf-⊗ (wf-S f a) (wf-S g b)

  wf-L : ∀ {F F′} → ST.WFFun Δ F′ → FunR Δ F F′ → LW.WellFormedF F
  wf-L (ST.wf-K b) (r-K a)   = LW.wf-K (base-L b a)
  wf-L ST.wf-Id    r-Id      = LW.wf-Id
  wf-L (ST.wf-⊕ f g) (r-⊕ a b) = LW.wf-Sum (wf-L f a) (wf-L g b)
  wf-L (ST.wf-⊗ f g) (r-⊗ a b) = LW.wf-Prod (wf-L f a) (wf-L g b)

  ------------------------------------------------------------------------
  -- Subtyping, both ways

  sub-S : ∀ {A B A′ B′} → A LS.<: B → TyR Δ A A′ → TyR Δ B B′ → A′ SS.<: B′
  sub-S LS.sub-void r-void _ = SS.sub-void
  sub-S LS.sub-unit r-unit r-unit = SS.sub-unit
  sub-S LS.sub-int r-int r-int = SS.sub-int
  sub-S LS.sub-float r-float r-float = SS.sub-float
  sub-S (LS.sub-arr a b p) (r-⇒ refl ra rb) (r-⇒ refl ra′ rb′) = SS.sub-arr (sub-S a ra′ ra) (sub-S b rb rb′) (⊑π-S p)
  sub-S (LS.sub-prod a b) (r-* ra rb) (r-* ra′ rb′) = SS.sub-* (sub-S a ra ra′) (sub-S b rb rb′)
  sub-S (LS.sub-sum a b) (r-+ ra rb) (r-+ ra′ rb′) = SS.sub-+ (sub-S a ra ra′) (sub-S b rb rb′)
  sub-S LS.sub-μ (r-μ f) (r-μ f′) = subst (λ G → ST.μ _ SS.<: ST.μ G) (FunR-uniqueˢ f f′) SS.sub-μ
  sub-S (LS.sub-ν {φ = φ} {φ′} p) (r-ν refl f) (r-ν refl f′) =
    subst (λ G → ST.ν _ _ SS.<: ST.ν G _) (FunR-uniqueˢ f f′) (SS.sub-ν (⊑φ-S φ φ′ p))
  sub-S LS.sub-rigid r@(r-rigid _ _ _) r′ = subst (λ X → ST.var _ SS.<: X) (TyR-uniqueˢ r r′) SS.sub-var

  -- The Spec's order, read back.
  sub-L : ∀ {A B A′ B′} → A′ SS.<: B′ → TyR Δ A A′ → TyR Δ B B′ → A LS.<: B
  sub-L SS.sub-void r-void _ = LS.sub-void
  sub-L SS.sub-var r@(r-rigid _ _ _) r′ = subst (λ X → _ LS.<: X) (TyR-uniqueˡ r r′) LS.sub-rigid
  sub-L SS.sub-unit r-unit r-unit = LS.sub-unit
  sub-L SS.sub-int r-int r-int = LS.sub-int
  sub-L SS.sub-float r-float r-float = LS.sub-float
  sub-L (SS.sub-arr a b p) (r-⇒ {k = LG.mk-kind q π} e ra rb) (r-⇒ {k = LG.mk-kind q′ π′} e′ ra′ rb′) =
    arr (qS-injective (trans (cong SG.ArrowKind.quantity e) (sym (cong SG.ArrowKind.quantity e′))))
        (⊑π-L π π′ (grade (cong SG.ArrowKind.purity e) (cong SG.ArrowKind.purity e′) p))
        (sub-L a ra′ ra) (sub-L b rb rb′)
    where
      grade : ∀ {x y x′ y′} → x ≡ x′ → y ≡ y′ → x′ SG.⊑π y′ → x SG.⊑π y
      grade refl refl p = p
      arr : ∀ {A A′ B B′} → q ≡ q′ → π Once.Spec.Grade.⊑π π′ → A′ LS.<: A → B LS.<: B′
          → (A LT.⇒[ LG.mk-kind q π ] B) LS.<: (A′ LT.⇒[ LG.mk-kind q′ π′ ] B′)
      arr refl p a b = LS.sub-arr a b p
  sub-L (SS.sub-*  a b) (r-* ra rb) (r-* ra′ rb′) = LS.sub-prod (sub-L a ra ra′) (sub-L b rb rb′)
  sub-L (SS.sub-+  a b) (r-+ ra rb) (r-+ ra′ rb′) = LS.sub-sum (sub-L a ra ra′) (sub-L b rb rb′)
  sub-L SS.sub-μ (r-μ f) (r-μ f′) = subst (λ G → LT.μ-type _ LS.<: LT.μ-type G) (FunR-uniqueˡ f f′) LS.sub-μ
  sub-L (SS.sub-ν p) (r-ν {φ = φ} e f) (r-ν {φ = φ′} e′ f′) =
    subst (λ G → LT.ν-type _ φ LS.<: LT.ν-type G φ′) (FunR-uniqueˡ f f′) (LS.sub-ν (⊑φ-L φ φ′ (grade e e′ p)))
    where
      grade : ∀ {x y x′ y′} → x ≡ x′ → y ≡ y′ → SG.fin x′ SG.⊑π SG.fin y′ → SG.fin x SG.⊑π SG.fin y
      grade refl refl p = p
