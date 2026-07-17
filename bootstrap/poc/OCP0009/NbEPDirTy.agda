------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 7 — DIRECTED TYPE FORMERS (variance-annotated)
--
-- The heart of a DIRECTED type theory: the type formers carry VARIANCE. Over
-- the directed CwF (`NbEPDirCwF`), a type is a functor `Γ → Set` — covariant
-- (`Ty⁺`) or contravariant (`Ty⁻`). The formers must respect that, and the
-- ONE that reveals the discipline is the function type: it is COVARIANT in its
-- codomain but CONTRAVARIANT in its domain, so a covariant `A ⇒ B` is only
-- well-formed with a CONTRAVARIANT domain `A : Ty⁻`. This is `NbEPDirV`'s
-- `⇒→`-contravariance, now as a CwF type former.
--
--   * `_×⁺_` / `_+⁺_` — covariant product / sum (both `Ty⁺ → Ty⁺ → Ty⁺`),
--                       structural, no `funext`;
--   * `_⇒⁺_`          — the directed function type `Ty⁻ Γ → Ty⁺ Γ → Ty⁺ Γ`:
--                       covariant, its action pre-composes the CONTRAVARIANT
--                       domain action and post-composes the codomain's. Its
--                       functor laws need `funext` (they compare functions),
--                       threaded as a hypothesis — stays `--safe`.
--
-- Variance is not decoration: `_⇒⁺_` simply does not typecheck with a
-- covariant domain — you cannot turn a forward `A.act f` into the backward
-- map the contravariant position needs. The directed exponential FORCES the
-- domain contravariant, which is the whole content of "directed".
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirTy where

open import normalizer.Syntax.Types
  using ( _≡_; refl; cong; cong₂; trans
        ; Σ; _,_; _×_; _⊎_; inj₁; inj₂ )
open Σ
open import poc.OCP0009.NbEPDirCwF using ( Ctx; Ty⁺; Ty⁻ )

------------------------------------------------------------------------
-- Covariant product and sum — structural, `funext`-free.
------------------------------------------------------------------------

_×⁺_ : ∀ {Γ} → Ty⁺ Γ → Ty⁺ Γ → Ty⁺ Γ
_×⁺_ {Γ} A B = record
  { fam   = λ x → A.fam x × B.fam x
  ; act   = λ f p → (A.act f (fst p) , B.act f (snd p))
  ; actid = λ p → cong₂ _,_ (A.actid (fst p)) (B.actid (snd p))
  ; act⨾  = λ f g p → cong₂ _,_ (A.act⨾ f g (fst p)) (B.act⨾ f g (snd p)) }
  where module A = Ty⁺ A ; module B = Ty⁺ B

_+⁺_ : ∀ {Γ} → Ty⁺ Γ → Ty⁺ Γ → Ty⁺ Γ
_+⁺_ {Γ} A B = record
  { fam   = λ x → A.fam x ⊎ B.fam x
  ; act   = act
  ; actid = actid
  ; act⨾  = act⨾ }
  where
  module A = Ty⁺ A ; module B = Ty⁺ B
  open Ctx Γ
  act : ∀ {x y} → x ⇒ y → A.fam x ⊎ B.fam x → A.fam y ⊎ B.fam y
  act f (inj₁ a) = inj₁ (A.act f a)
  act f (inj₂ b) = inj₂ (B.act f b)
  actid : ∀ {x} (s : A.fam x ⊎ B.fam x) → act idₒ s ≡ s
  actid (inj₁ a) = cong inj₁ (A.actid a)
  actid (inj₂ b) = cong inj₂ (B.actid b)
  act⨾ : ∀ {x y z} (f : x ⇒ y) (g : y ⇒ z) (s : A.fam x ⊎ B.fam x) →
         act (f ⨾ g) s ≡ act g (act f s)
  act⨾ f g (inj₁ a) = cong inj₁ (A.act⨾ f g a)
  act⨾ f g (inj₂ b) = cong inj₂ (B.act⨾ f g b)

------------------------------------------------------------------------
-- The directed function type — CONTRAVARIANT domain, covariant codomain.
-- Laws need `funext` (function equalities), threaded so we stay `--safe`.
------------------------------------------------------------------------

module _ (funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
                   (∀ x → f x ≡ g x) → f ≡ g) where

  _⇒⁺_ : ∀ {Γ} → Ty⁻ Γ → Ty⁺ Γ → Ty⁺ Γ
  _⇒⁺_ {Γ} A B = record
    { fam   = λ x → A.fam x → B.fam x
    ; act   = λ f g a → B.act f (g (A.act f a))
    ; actid = λ g → funext (λ a →
                trans (B.actid _) (cong g (A.actid a)))
    ; act⨾  = λ f g' gg → funext (λ a →
                trans (B.act⨾ f g' _)
                      (cong (λ z → B.act g' (B.act f (gg z))) (A.act⨾ f g' a))) }
    where module A = Ty⁻ A ; module B = Ty⁺ B
