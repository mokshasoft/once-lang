------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 8 — the DIRECTED DEPENDENT SUM `Σ⁺`
--
-- The first DEPENDENT directed type former: `Σ⁺ A B : Ty⁺ Γ` for `A : Ty⁺ Γ`
-- and `B : Ty⁺ (Γ ▷ A)` — a covariant type whose fibre over `x` is
-- `Σ (a : A x) → B (x , a)`. Unlike the non-dependent formers, its functor
-- action must move the second component `b : B (x,a)` into the fibre over
-- `A.act f a`, and the LAWS then compare across DIFFERENT fibres — the
-- transport that dependent type theory always pays.
--
-- The two ingredients that tame it, both `J`/`K` facts (no new axiom):
--   * `subst-act` — moving `B.act (m , refl)` along a fibre equality `e` is
--     `B.act (m , e)` (path induction on `e`); this converts every transport
--     into a `B.act` at a matched morphism;
--   * `uip` — the `▷`-morphisms carry an equality PROOF, and any two proofs of
--     a `Set`-equality agree, so `B.act` cannot tell them apart.
-- With those, `actid` lands on `B.actid` and `act⨾` on `B.act⨾` — the fibre
-- laws of `B`, exactly as a Grothendieck construction should.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirSig where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; subst; Σ; _,_ )
open Σ
open import poc.OCP0009.NbEPDirCwF using ( Ctx; Ty⁺; _▷_ )

-- Uniqueness of identity proofs (available: the codebase is `--with-K`).
uip : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

-- Σ-equality from a base equality and a transported fibre equality.
Σ≡ : ∀ {A : Set} {C : A → Set} {a₁ a₂ : A} {b₁ : C a₁} {b₂ : C a₂}
     (p : a₁ ≡ a₂) → subst C p b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
Σ≡ refl q = cong (_ ,_) q

------------------------------------------------------------------------
-- The directed dependent sum.
------------------------------------------------------------------------

module _ {Γ : Ctx} (A : Ty⁺ Γ) (B : Ty⁺ (Γ ▷ A)) where
  private
    module Γ  = Ctx Γ
    module A  = Ty⁺ A
    module B  = Ty⁺ B
  open Γ using ( Ob; _⇒_; idₒ; _⨾_ )
  open Ctx (Γ ▷ A) using () renaming ( _⨾_ to _⨾▷_ )

  -- Moving `B.act (m , refl)` along a fibre equality is `B.act (m , e)`.
  subst-act : ∀ {x z a v} (m : x ⇒ z) (e : A.act m a ≡ v) (b : B.fam (x , a)) →
              subst (λ w → B.fam (z , w)) e (B.act (m , refl) b) ≡ B.act (m , e) b
  subst-act m refl b = refl

  Σ⁺ : Ty⁺ Γ
  Σ⁺ = record
    { fam   = λ x → Σ (A.fam x) (λ a → B.fam (x , a))
    ; act   = λ f p → (A.act f (fst p) , B.act (f , refl) (snd p))
    ; actid = λ p →
        Σ≡ (A.actid (fst p))
           (trans (subst-act idₒ (A.actid (fst p)) (snd p)) (B.actid (snd p)))
    ; act⨾  = λ f g p →
        Σ≡ (A.act⨾ f g (fst p))
           (trans (subst-act (f ⨾ g) (A.act⨾ f g (fst p)) (snd p))
           (trans (cong (λ e → B.act ((f ⨾ g) , e) (snd p))
                        (uip (A.act⨾ f g (fst p))
                             (snd ((f , refl) ⨾▷ (g , refl)))))
                  (B.act⨾ (f , refl) (g , refl) (snd p)))) }
