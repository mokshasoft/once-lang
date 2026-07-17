------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 13c — a SMALL dependent universe (syntactic, Σ/Π)
--
-- Closing item 2: a genuinely SMALL universe (`U : Set`, so `𝒰.fam` lands in
-- `Set`) that is CLOSED under dependent `Σ`/`Π`, by INDUCTION–RECURSION
-- (`U`/`El` mutual — `--safe`; the family is a real `El a → U`, so the
-- dependency is genuine, not a large code carrying types).
--
--   * `U` / `El`    — the universe and its decoding, closed under `⊤/⊥/Σ/Π`;
--   * `disc`        — a set as a DISCRETE directed type (`Ty⁺`, trivial action);
--   * `El-dir`      — the directed decoding `U → Ty⁺ Γ` (`disc ∘ El`);
--   * `Fib`/`Σ⁺-code` — the `` `Σ `` code's directed decoding IS a `Σ⁺`: the
--     fibre `Fib a b` over `Γ ▷ disc(El a)` (its action is a `subst` along the
--     comprehension proof), and `El-dir (`Σ a b) ≡₁ Σ⁺ (disc (El a)) (Fib a b)`.
--
-- Directedness is trivialised by `disc` (the discrete embedding) — a fully
-- VARIANT small universe (Hofmann–Streicher, codes carrying variance) is the
-- deeper object. But the closure under `Σ`/`Π` and the decoding to `Σ⁺` are
-- genuine and small.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirUnivS where

open import normalizer.Syntax.Types
  using ( _≡_; refl; trans; cong; subst; ⊤; tt; ⊥; Σ; _,_ )
open Σ
open import poc.OCP0009.NbEPDirCwF using ( Ctx; Ty⁺; _▷_ )
open import poc.OCP0009.NbEPDirSig using ( Σ⁺; uip )
open import poc.OCP0009.NbEPDirCwFL using ( _≡₁_ )
open import poc.OCP0009.NbEPDirTyExt using ( cong₁; module W )

------------------------------------------------------------------------
-- The small universe, closed under Σ/Π (induction–recursion).
------------------------------------------------------------------------

mutual
  data U : Set where
    `⊤ `⊥ : U
    `Σ `Π : (a : U) → (El a → U) → U

  El : U → Set
  El `⊤       = ⊤
  El `⊥       = ⊥
  El (`Σ a b) = Σ (El a) (λ x → El (b x))
  El (`Π a b) = (x : El a) → El (b x)

------------------------------------------------------------------------
-- The discrete embedding of a set into the directed types.
------------------------------------------------------------------------

disc : ∀ {Γ} → Set → Ty⁺ Γ
disc S = record { fam = λ _ → S ; act = λ _ s → s
                ; actid = λ _ → refl ; act⨾ = λ _ _ _ → refl }

El-dir : ∀ {Γ} → U → Ty⁺ Γ
El-dir u = disc (El u)

------------------------------------------------------------------------
-- The `` `Σ `` code's directed decoding — the dependent fibre as a `Ty⁺`
-- over the comprehension, its action a `subst` along the fibre proof.
------------------------------------------------------------------------

subst-trans : ∀ {A : Set} {P : A → Set} {x y z} (p : x ≡ y) (q : y ≡ z) (w : P x) →
              subst P (trans p q) w ≡ subst P q (subst P p w)
subst-trans refl refl w = refl

module _ {Γ : Ctx} (a : U) (b : El a → U) where
  open Ctx (Γ ▷ disc (El a)) using () renaming ( _⨾_ to _⨾▷_ )

  Fib : Ty⁺ (Γ ▷ disc (El a))
  Fib = record
    { fam = λ p → El (b (snd p))
    ; act = λ m w → subst (λ v → El (b v)) (snd m) w
    ; actid = λ w → refl
    ; act⨾ = λ f g w →
        trans (cong (λ e → subst (λ v → El (b v)) e w)
                    (uip (snd (f ⨾▷ g)) (trans (snd f) (snd g))))
              (subst-trans (snd f) (snd g) w) }

------------------------------------------------------------------------
-- The `` `Σ `` code decodes to the directed dependent sum. `fam`/`act` are
-- definitionally equal (`Σ` η + `subst _ refl = id`); only the proof fields
-- differ, closed by `funext` + `uip`.
------------------------------------------------------------------------

module _
  (funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
            (∀ x → f x ≡ g x) → f ≡ g)
  where

  -- `El-dir`'s and `Σ⁺`'s actions are defeq (`Σ` η + `subst _ refl = id`), but
  -- Agda won't unify them under a reconstruction, so go via the extensionality
  -- wrapper (`ae = refl`, the acts being definitionally equal as functions).
  Σ⁺-code : ∀ {Γ} (a : U) (b : El a → U) →
            El-dir {Γ} (`Σ a b) ≡₁ Σ⁺ (disc (El a)) (Fib {Γ} a b)
  Σ⁺-code {Γ} a b =
    cong₁ toTy⁺
      (Ty⁺ᵉ-≡ (Ty⁺.fam LHS)
              (λ x y → Ty⁺.act LHS {x} {y}) (λ x y → Ty⁺.act RHS {x} {y})
              (λ x → Ty⁺.actid LHS {x}) (λ x → Ty⁺.actid RHS {x})
              (λ x y z → Ty⁺.act⨾ LHS {x} {y} {z}) (λ x y z → Ty⁺.act⨾ RHS {x} {y} {z})
              refl)
    where
    LHS = El-dir {Γ} (`Σ a b)
    RHS = Σ⁺ (disc (El a)) (Fib {Γ} a b)
    open W funext Γ
