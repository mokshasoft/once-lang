------------------------------------------------------------------------
-- Theory.Models.StrongCCL3.Typed.Faithful
--
-- Faithfulness theorems for the Phase 2 coded typed encoding.
--
--   1. encode-func-faithful : encode-func φ ≡ encode-func ψ → φ ≡ ψ
--   2. encode-tyc-faithful  : encode-tyc T ≡ encode-tyc U → T ≡ U
--   3. encode-typed-c-faithful (bundled) : if two typed encodings agree,
--      then their source types agree, their target types agree, and
--      their erased term encodings agree.
--
-- (1) and (2) are proved by mutual structural induction over the
-- universes Func / TyClosed. Off-diagonal cases (different head
-- constructors) collapse via Agda's absurd pattern () because the
-- distinct tag prefixes make the two terms structurally distinct
-- already at the outer In/inr/inl spine. Diagonal cases peel the
-- prefix via repeated _∘_ injectivity, then use ⟨_,_⟩ injectivity
-- (for binary tags) and the recursive faithfulness witnesses.
--
-- (3) follows by ⟨_,_⟩ injectivity on the typed carrier
-- (TyCode × TyCode × Code) plus (2) for the type components. The
-- erased term agreement is the third projection unchanged.
--
-- Note: encode-typed-c-faithful does NOT promise t₁ ≡ t₂ at the term
-- level — that needs the erased layer's encode-faithful, which lives
-- elsewhere (and is itself an open obligation). What is delivered here
-- is the part the typed layer actually contributes: full type
-- recovery (impossible at the erased layer) plus deferral of the
-- term part to encode.
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

module Theory.Models.StrongCCL3.Typed.Faithful where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)
open import Data.Product using (_×_; _,_)

import Theory.Syntax.StrongCCL.CCT3 as Syn
open Syn using (Term; _∘_; ⟨_,_⟩)

open import Theory.Models.StrongCCL3.Typed.Func using (TyClosed; Func; lift)
import Theory.Models.StrongCCL3.Typed.Func as F
open import Theory.Models.StrongCCL3.Typed.Coded
  using (CodedCode; encode-tyc; encode-func)
open import Theory.Models.StrongCCL3.Encoding using (Code; encode)
open import Theory.Models.StrongCCL3.Typed.EncodingCoded
  using (TypedCodeC; encode-typed-c)

------------------------------------------------------------------------
-- Constructor injectivity helpers.
--
-- _∘_ is a constructor of Term, so its arguments are propositionally
-- recoverable from the equation on the composition.  Same for ⟨_,_⟩.
------------------------------------------------------------------------

∘-inj-r : ∀ {A B C} {g g' : Term B C} {h h' : Term A B} →
          (g ∘ h) ≡ (g' ∘ h') → h ≡ h'
∘-inj-r refl = refl

⟨,⟩-inj-l : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
            ⟨ f , g ⟩ ≡ ⟨ f' , g' ⟩ → f ≡ f'
⟨,⟩-inj-l refl = refl

⟨,⟩-inj-r : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
            ⟨ f , g ⟩ ≡ ⟨ f' , g' ⟩ → g ≡ g'
⟨,⟩-inj-r refl = refl

------------------------------------------------------------------------
-- Mutually recursive faithfulness for encode-tyc and encode-func.
------------------------------------------------------------------------

mutual

  encode-tyc-faithful : ∀ T U → encode-tyc T ≡ encode-tyc U → T ≡ U

  -- TyClosed.Unit ──────────────────────────────────────────────────────
  encode-tyc-faithful F.Unit       F.Unit       _ = refl
  encode-tyc-faithful F.Unit       F.Void       ()
  encode-tyc-faithful F.Unit       (F.Mu _)     ()
  encode-tyc-faithful F.Unit       (_ F.× _)    ()
  encode-tyc-faithful F.Unit       (_ F.⊎ _)    ()
  encode-tyc-faithful F.Unit       (_ F.⇒ _)    ()

  -- TyClosed.Void ──────────────────────────────────────────────────────
  encode-tyc-faithful F.Void       F.Unit       ()
  encode-tyc-faithful F.Void       F.Void       _ = refl
  encode-tyc-faithful F.Void       (F.Mu _)     ()
  encode-tyc-faithful F.Void       (_ F.× _)    ()
  encode-tyc-faithful F.Void       (_ F.⊎ _)    ()
  encode-tyc-faithful F.Void       (_ F.⇒ _)    ()

  -- TyClosed.Mu (payload at depth 4) ───────────────────────────────────
  encode-tyc-faithful (F.Mu _)     F.Unit       ()
  encode-tyc-faithful (F.Mu _)     F.Void       ()
  encode-tyc-faithful (F.Mu φ)     (F.Mu ψ)     eq =
    cong F.Mu (encode-func-faithful φ ψ
                (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r eq)))))
  encode-tyc-faithful (F.Mu _)     (_ F.× _)    ()
  encode-tyc-faithful (F.Mu _)     (_ F.⊎ _)    ()
  encode-tyc-faithful (F.Mu _)     (_ F.⇒ _)    ()

  -- TyClosed._×_ (pair payload at depth 5) ─────────────────────────────
  encode-tyc-faithful (_ F.× _)    F.Unit       ()
  encode-tyc-faithful (_ F.× _)    F.Void       ()
  encode-tyc-faithful (_ F.× _)    (F.Mu _)     ()
  encode-tyc-faithful (a F.× b)    (c F.× d)    eq =
    let pair-eq = ∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r eq))))
    in cong₂ F._×_ (encode-tyc-faithful a c (⟨,⟩-inj-l pair-eq))
                   (encode-tyc-faithful b d (⟨,⟩-inj-r pair-eq))
  encode-tyc-faithful (_ F.× _)    (_ F.⊎ _)    ()
  encode-tyc-faithful (_ F.× _)    (_ F.⇒ _)    ()

  -- TyClosed._⊎_ (pair payload at depth 6) ─────────────────────────────
  encode-tyc-faithful (_ F.⊎ _)    F.Unit       ()
  encode-tyc-faithful (_ F.⊎ _)    F.Void       ()
  encode-tyc-faithful (_ F.⊎ _)    (F.Mu _)     ()
  encode-tyc-faithful (_ F.⊎ _)    (_ F.× _)    ()
  encode-tyc-faithful (a F.⊎ b)    (c F.⊎ d)    eq =
    let pair-eq = ∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r eq)))))
    in cong₂ F._⊎_ (encode-tyc-faithful a c (⟨,⟩-inj-l pair-eq))
                   (encode-tyc-faithful b d (⟨,⟩-inj-r pair-eq))
  encode-tyc-faithful (_ F.⊎ _)    (_ F.⇒ _)    ()

  -- TyClosed._⇒_ (pair payload at depth 7) ─────────────────────────────
  encode-tyc-faithful (_ F.⇒ _)    F.Unit       ()
  encode-tyc-faithful (_ F.⇒ _)    F.Void       ()
  encode-tyc-faithful (_ F.⇒ _)    (F.Mu _)     ()
  encode-tyc-faithful (_ F.⇒ _)    (_ F.× _)    ()
  encode-tyc-faithful (_ F.⇒ _)    (_ F.⊎ _)    ()
  encode-tyc-faithful (a F.⇒ b)    (c F.⇒ d)    eq =
    let pair-eq = ∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r eq))))))
    in cong₂ F._⇒_ (encode-tyc-faithful a c (⟨,⟩-inj-l pair-eq))
                   (encode-tyc-faithful b d (⟨,⟩-inj-r pair-eq))

  encode-func-faithful : ∀ φ ψ → encode-func φ ≡ encode-func ψ → φ ≡ ψ

  -- Func.K (TyClosed payload at depth 8) ───────────────────────────────
  encode-func-faithful (F.K T)     (F.K U)      eq =
    cong F.K (encode-tyc-faithful T U
               (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r
                 (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r eq)))))))))
  encode-func-faithful (F.K _)     F.Id         ()
  encode-func-faithful (F.K _)     (_ F.⊕ _)    ()
  encode-func-faithful (F.K _)     (_ F.⊗ _)    ()

  -- Func.Id ────────────────────────────────────────────────────────────
  encode-func-faithful F.Id        (F.K _)      ()
  encode-func-faithful F.Id        F.Id         _ = refl
  encode-func-faithful F.Id        (_ F.⊕ _)    ()
  encode-func-faithful F.Id        (_ F.⊗ _)    ()

  -- Func._⊕_ (pair payload at depth 10) ────────────────────────────────
  encode-func-faithful (_ F.⊕ _)   (F.K _)      ()
  encode-func-faithful (_ F.⊕ _)   F.Id         ()
  encode-func-faithful (φ F.⊕ ψ)   (φ' F.⊕ ψ')  eq =
    let pair-eq = ∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r
                  (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r eq)))))))))
    in cong₂ F._⊕_ (encode-func-faithful φ φ' (⟨,⟩-inj-l pair-eq))
                   (encode-func-faithful ψ ψ' (⟨,⟩-inj-r pair-eq))
  encode-func-faithful (_ F.⊕ _)   (_ F.⊗ _)    ()

  -- Func._⊗_ (pair payload at depth 10, last alternative — no inl) ─────
  encode-func-faithful (_ F.⊗ _)   (F.K _)      ()
  encode-func-faithful (_ F.⊗ _)   F.Id         ()
  encode-func-faithful (_ F.⊗ _)   (_ F.⊕ _)    ()
  encode-func-faithful (φ F.⊗ ψ)   (φ' F.⊗ ψ')  eq =
    let pair-eq = ∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r
                  (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r (∘-inj-r eq)))))))))
    in cong₂ F._⊗_ (encode-func-faithful φ φ' (⟨,⟩-inj-l pair-eq))
                   (encode-func-faithful ψ ψ' (⟨,⟩-inj-r pair-eq))

------------------------------------------------------------------------
-- Theorem 3: bundled faithfulness of the typed encoding.
--
-- For t₁, t₂ at potentially different types, agreement of their typed
-- encodings forces:
--   - source-type agreement   (A₁ ≡ A₂)
--   - target-type agreement   (B₁ ≡ B₂)
--   - erased-term agreement   (encode t₁ ≡ encode t₂)
--
-- This is the principled gain over Phase 1: the typed encoding
-- recovers full type information, which the erased encoding cannot.
-- The remaining "term agreement up to ≡" depends on encode-faithful
-- at the erased layer (separate obligation).
------------------------------------------------------------------------

encode-typed-c-faithful :
  ∀ {A₁ B₁ A₂ B₂ : TyClosed}
    (t₁ : Term (lift A₁) (lift B₁)) (t₂ : Term (lift A₂) (lift B₂)) →
  encode-typed-c t₁ ≡ encode-typed-c t₂ →
  (A₁ ≡ A₂) × (B₁ ≡ B₂) × (encode t₁ ≡ encode t₂)
encode-typed-c-faithful {A₁} {B₁} {A₂} {B₂} t₁ t₂ eq =
  let -- eq : ⟨ encode-tyc A₁ , ⟨ encode-tyc B₁ , encode t₁ ⟩ ⟩
      --   ≡ ⟨ encode-tyc A₂ , ⟨ encode-tyc B₂ , encode t₂ ⟩ ⟩
      src-tag-eq  = ⟨,⟩-inj-l eq
      tail-eq     = ⟨,⟩-inj-r eq
      tgt-tag-eq  = ⟨,⟩-inj-l tail-eq
      term-tag-eq = ⟨,⟩-inj-r tail-eq
  in encode-tyc-faithful A₁ A₂ src-tag-eq
   , encode-tyc-faithful B₁ B₂ tgt-tag-eq
   , term-tag-eq
