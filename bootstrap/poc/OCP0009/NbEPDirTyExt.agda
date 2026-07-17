------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 12a — a `Ty⁺` EXTENSIONALITY principle
--
-- The tool that unblocks the CwF stability laws. Two `Ty⁺` with equal `fam`
-- and equal `act` (AS FUNCTIONS) are equal — even when the `act` fields are
-- not definitionally equal (`+⁺`/`Σ⁺`/`Π⁺`). The obstruction was Agda's
-- `MetaCannotDependOn`: reconstructing a `Ty⁺` with a bound implicit-argument
-- `act`. The fix is a wrapper `Ty⁺ᵉ` whose `act` has EXPLICIT indices — then
--   * building the record (`actᵉ = a`) needs no implicit meta, and
--   * the proof-field props close by plain `funext` (no `funextᵢ`);
-- and `toTy⁺ (fromTy⁺ T) ≡ T` holds DEFINITIONALLY by η, so a `Ty⁺ᵉ` equality
-- transports back to a `Ty⁺` equality by `cong₁`. `funext` threaded.
--
--   * `Ty⁺-ext` : `(λ x y → act T₁) ≡ (λ x y → act T₂) → T₁ ≡₁ T₂`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirTyExt where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import poc.OCP0009.NbEPDirCwF using ( Ctx; Ty⁺ )
open import poc.OCP0009.NbEPDirCwFL using ( _≡₁_; refl₁; cong₂₁ )
open import poc.OCP0009.NbEPDirSig using ( uip )

-- Congruence at the `Set₁` equality.
cong₁ : {A B : Set₁} (f : A → B) {x y : A} → x ≡₁ y → f x ≡₁ f y
cong₁ f refl₁ = refl₁

module W
  (funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
            (∀ x → f x ≡ g x) → f ≡ g)
  (Δ : Ctx)
  where
  open Ctx Δ

  -- The explicit-index wrapper.
  record Ty⁺ᵉ : Set₁ where
    field
      famᵉ   : Ob → Set
      actᵉ   : (x y : Ob) → x ⇒ y → famᵉ x → famᵉ y
      actidᵉ : (x : Ob) (a : famᵉ x) → actᵉ x x idₒ a ≡ a
      act⨾ᵉ  : (x y z : Ob) (f : x ⇒ y) (g : y ⇒ z) (a : famᵉ x) →
               actᵉ x z (f ⨾ g) a ≡ actᵉ y z g (actᵉ x y f a)

  ActTᵉ : (Ob → Set) → Set
  ActTᵉ fam = (x y : Ob) → x ⇒ y → fam x → fam y

  IdTᵉ : (fam : Ob → Set) → ActTᵉ fam → Set
  IdTᵉ fam a = (x : Ob) (p : fam x) → a x x idₒ p ≡ p

  CompTᵉ : (fam : Ob → Set) → ActTᵉ fam → Set
  CompTᵉ fam a = (x y z : Ob) (f : x ⇒ y) (g : y ⇒ z) (p : fam x) →
                 a x z (f ⨾ g) p ≡ a y z g (a x y f p)

  mkᵉ : (fam : Ob → Set) (a : ActTᵉ fam) → IdTᵉ fam a → CompTᵉ fam a → Ty⁺ᵉ
  mkᵉ fam a i c =
    record { famᵉ = fam ; actᵉ = a ; actidᵉ = i ; act⨾ᵉ = c }

  -- The proof fields are propositions (plain `funext`, all explicit).
  IdTᵉ-prop : ∀ {fam a} (u v : IdTᵉ fam a) → u ≡ v
  IdTᵉ-prop u v = funext (λ x → funext (λ p → uip (u x p) (v x p)))

  CompTᵉ-prop : ∀ {fam a} (u v : CompTᵉ fam a) → u ≡ v
  CompTᵉ-prop u v =
    funext (λ x → funext (λ y → funext (λ z → funext (λ f → funext (λ g →
      funext (λ p → uip (u x y z f g p) (v x y z f g p)))))))

  -- Wrapper equality from equal `fam` + equal (explicit) `act`.
  Ty⁺ᵉ-≡ : (fam : Ob → Set) (a₁ a₂ : ActTᵉ fam)
           (i₁ : IdTᵉ fam a₁) (i₂ : IdTᵉ fam a₂)
           (c₁ : CompTᵉ fam a₁) (c₂ : CompTᵉ fam a₂) →
           a₁ ≡ a₂ → mkᵉ fam a₁ i₁ c₁ ≡₁ mkᵉ fam a₂ i₂ c₂
  Ty⁺ᵉ-≡ fam a₁ .a₁ i₁ i₂ c₁ c₂ refl =
    cong₂₁ (mkᵉ fam a₁) (IdTᵉ-prop {fam} {a₁} i₁ i₂) (CompTᵉ-prop {fam} {a₁} c₁ c₂)

  -- Unwrap. `toTy⁺ (mkᵉ (fam T)(λ x y → act T)…) ≡ T` DEFINITIONALLY (η), so
  -- a `Ty⁺ᵉ`-equality of two wrappers built from `T₁`/`T₂` (with `fam T₁`
  -- and `fam T₂` definitionally equal — the case for the stability laws)
  -- transports by `cong₁ toTy⁺` to `T₁ ≡₁ T₂`.
  toTy⁺ : Ty⁺ᵉ → Ty⁺ Δ
  toTy⁺ E = record { fam = famᵉ ; act = λ {x} {y} → actᵉ x y
                   ; actid = λ {x} → actidᵉ x ; act⨾ = λ {x} {y} {z} → act⨾ᵉ x y z }
    where open Ty⁺ᵉ E
