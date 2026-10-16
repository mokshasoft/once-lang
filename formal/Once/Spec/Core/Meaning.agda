{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Meaning — the meaning of a core derivation.
--
-- At every closed instance `σ` of its type variables that respects their
-- kinds, a derivation of `Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π` means
--
--     ⟦ Γ ↾ Ψ ⟧ → M π ⟦ A ⟧
--
-- call by value, over the values of the variables the term USES: a variable
-- used zero times has no value (an erased binder binds nothing). One clause
-- per rule. Sub-usage forgets values; sub-effect is the monad morphism. A
-- polymorphic definition means the family of its instances.
--
-- Relative to the target's numbers (`TargetNum`), the meanings of the
-- earlier definitions, and an Interpretation of the signature.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)
open import Data.Nat using (ℕ)

module Once.Spec.Core.Meaning (Σ : Signature) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Bool using (not)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; pure; act; eff; mk-kind; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type using (Ty; KCtx; ∅ₖ; TySub; _⟨_⟩; _⟨_⟩F; Respects; respects-∘; ⟨⟩-∘; μ; ν)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Signature
  using (DeclType; constant; arrow; _∶_; Op; op; Effectful; e-act; e-eff; Layer; call; ⌜_⌝)
open import Once.Spec.Context
  using (Ctx; ∅; _▸_; lookup; Usage; []; _∷_; _⊑ᵘ_; _⊑∷_; _+ᵘ_; _*ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
open import Once.Spec.Numerics using (module TargetNum)
open TargetNum fmt using (int-bits; float-format)
import Once.Spec.Word as Word
open import Once.Spec.Float.Decimal using (round)
import Once.Spec.Float.Arith as FA
open import Once.Spec.Bool using (truth)
open import Once.Spec.Effect Σ using (M; bind; fmap; bindᵍ; sub; T; T∞; returnT; return∞; loop; performT; perform; module νM)
open νM using (outν)
open import Once.Spec.Observation Σ using (Interp; module Interp)
open Interp using (value)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toB; fromB; toL; fromL; foldM; anaM; conv)
open import Once.Spec.Polynomial using (inS)
open import Once.Spec.Core.Syntax
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Typing Σ S

------------------------------------------------------------------------
-- What a term may name besides its variables
------------------------------------------------------------------------

record DefSem : Set where
  field
    -- each earlier definition, at each instance of its schema
    defs   : (d : Fin s) (τ : TySub (arity (S !! d)) 0) → Respects (kinds (S !! d)) ∅ₖ τ
           → ⟦ type (S !! d) ⟨ τ ⟩ ⟧ᵛ
    -- the world: an Interpretation of the signature
    interp : Interp
open DefSem

------------------------------------------------------------------------
-- The environment: the values of the variables used
------------------------------------------------------------------------

Slot : Quantity → Set → Set
Slot Zero X = ⊤
Slot One  X = X
Slot Many X = X

slot : ∀ q {X} → X → Slot q X
slot Zero x = tt
slot One  x = x
slot Many x = x

module _ {m : ℕ} (σ : TySub m 0) where

  Env : ∀ {n} → Ctx m n → Usage n → Set
  Env ∅       []      = ⊤
  Env (Γ ▸ A) (q ∷ Ψ) = Env Γ Ψ × Slot q ⟦ A ⟨ σ ⟩ ⟧ᵛ

  -- Forget the values a part of the term does not use.
  restrict : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} → Ψ ⊑ᵘ Ψ′ → Env Γ Ψ′ → Env Γ Ψ
  restrict {Γ = ∅}     []         tt      = tt
  restrict {Γ = Γ ▸ A} (0≤q ⊑∷ ps) (ρ , v) = restrict ps ρ , tt
  restrict {Γ = Γ ▸ A} (1≤1 ⊑∷ ps) (ρ , v) = restrict ps ρ , v
  restrict {Γ = Γ ▸ A} (1≤ω ⊑∷ ps) (ρ , v) = restrict ps ρ , v
  restrict {Γ = Γ ▸ A} (ω≤ω ⊑∷ ps) (ρ , v) = restrict ps ρ , v

  lookupᵛ : ∀ {n} (Γ : Ctx m n) (i : Fin n) → Env Γ (Once.Spec.Context.singleUse i One) → ⟦ lookup Γ i ⟨ σ ⟩ ⟧ᵛ
  lookupᵛ (Γ ▸ A) zero    (ρ , v) = v
  lookupᵛ (Γ ▸ A) (suc i) (ρ , _) = lookupᵛ Γ i ρ

  ----------------------------------------------------------------------
  -- A reference to the signature: a value the world provides, or an
  -- operation — one call, read at its grade
  ----------------------------------------------------------------------

  sigopᵛ : ∀ (c : CanonicalName) (t : DeclType) → (c ∶ t) ∈ Σ → Interp → ⟦ Once.Spec.Signature.⌜_⌝ᵈ t ⟨ σ ⟩ ⟧ᵛ
  sigopᵛ c (constant b) m ι = fromB σ b (value ι m tt)
  sigopᵛ c (arrow a (mk-kind Zero pure) b) m ι = λ _ → fromB σ b (value ι m tt tt)
  sigopᵛ c (arrow a (mk-kind One  pure) b) m ι = λ x → fromB σ b (value ι m tt (toB σ a x))
  sigopᵛ c (arrow a (mk-kind Many pure) b) m ι = λ x → fromB σ b (value ι m tt (toB σ a x))
  sigopᵛ c (arrow a (mk-kind Zero act) b)  m ι = λ _ → performT (call (op m e-act) tt (fromB σ b))
  sigopᵛ c (arrow a (mk-kind One  act) b)  m ι = λ x → performT (call (op m e-act) (toB σ a x) (fromB σ b))
  sigopᵛ c (arrow a (mk-kind Many act) b)  m ι = λ x → performT (call (op m e-act) (toB σ a x) (fromB σ b))
  sigopᵛ c (arrow a (mk-kind Zero eff) b)  m ι = λ _ → perform (call (op m e-eff) tt (fromB σ b))
  sigopᵛ c (arrow a (mk-kind One  eff) b)  m ι = λ x → perform (call (op m e-eff) (toB σ a x) (fromB σ b))
  sigopᵛ c (arrow a (mk-kind Many eff) b)  m ι = λ x → perform (call (op m e-eff) (toB σ a x) (fromB σ b))

  -- The arithmetic is the target's: words of its width (`+`, `-`, `*` wrap;
  -- `/`, `%` total; comparisons signed), floats of its format, correctly
  -- rounded.
  primᵛ : ∀ (p : Prim) → ⟦ primDom p ⟨ σ ⟩ ⟧ᵛ → ⟦ primCod p ⟨ σ ⟩ ⟧ᵛ
  primᵛ p-add  (a , b) = Word.Width._⊕_  int-bits a b
  primᵛ p-sub  (a , b) = Word.Width._⊖_  int-bits a b
  primᵛ p-mul  (a , b) = Word.Width._⊗_  int-bits a b
  primᵛ p-div  (a , b) = Word.Width._/ˢ_ int-bits a b
  primᵛ p-mod  (a , b) = Word.Width._%ˢ_ int-bits a b
  primᵛ p-neg  a       = Word.Width.⊝_   int-bits a
  primᵛ p-lt   (a , b) = truth (Word.Width._<ˢ_ int-bits a b)
  primᵛ p-le   (a , b) = truth (not (Word.Width._<ˢ_ int-bits b a))
  primᵛ p-gt   (a , b) = truth (Word.Width._<ˢ_ int-bits b a)
  primᵛ p-ge   (a , b) = truth (not (Word.Width._<ˢ_ int-bits a b))
  primᵛ p-eq   (a , b) = truth (Word.Width._≡ʷ_ int-bits a b)
  primᵛ p-ne   (a , b) = truth (not (Word.Width._≡ʷ_ int-bits a b))
  primᵛ p-fadd (a , b) = FA.fadd float-format a b
  primᵛ p-fsub (a , b) = FA.fsub float-format a b
  primᵛ p-fmul (a , b) = FA.fmul float-format a b
  primᵛ p-fdiv (a , b) = FA.fdiv float-format a b
  primᵛ p-i2f  a       = FA.i2f float-format (Word.Width.toℤ int-bits a)

------------------------------------------------------------------------
-- The meaning
------------------------------------------------------------------------

⟦_⟧ : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ t A π} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π
    → DefSem → (σ : TySub m 0) → Respects Δ ∅ₖ σ → Env σ Γ Ψ → M π ⟦ A ⟨ σ ⟩ ⟧ᵛ

⟦ ⊢var {Γ = Γ} i ⟧ ρ σ r γ = lookupᵛ σ Γ i γ

-- A λ is a value. An erased argument is not passed.
⟦ ⊢lam {q = Zero} 0≤q d ⟧ ρ σ r γ = λ _ → ⟦ d ⟧ ρ σ r (γ , tt)
⟦ ⊢lam {q = One}  0≤q d ⟧ ρ σ r γ = λ _ → ⟦ d ⟧ ρ σ r (γ , tt)
⟦ ⊢lam {q = Many} 0≤q d ⟧ ρ σ r γ = λ _ → ⟦ d ⟧ ρ σ r (γ , tt)
⟦ ⊢lam 1≤1 d ⟧ ρ σ r γ = λ a → ⟦ d ⟧ ρ σ r (γ , a)
⟦ ⊢lam 1≤ω d ⟧ ρ σ r γ = λ a → ⟦ d ⟧ ρ σ r (γ , a)
⟦ ⊢lam ω≤ω d ⟧ ρ σ r γ = λ a → ⟦ d ⟧ ρ σ r (γ , a)

-- The function, then the argument, then the call.
⟦ ⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = Zero} {π} {π₁} df dx ⟧ ρ σ r γ =
  bindᵍ π₁ π (⟦ df ⟧ ρ σ r (restrict σ (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) γ)) λ f → f tt
⟦ ⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = One} {π} {π₁} {π₂} df dx ⟧ ρ σ r γ =
  bindᵍ π₁ _ (⟦ df ⟧ ρ σ r (restrict σ (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)) γ)) λ f →
  bindᵍ π₂ π (⟦ dx ⟧ ρ σ r (restrict σ (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) γ)) λ x → f x
⟦ ⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = Many} {π} {π₁} {π₂} df dx ⟧ ρ σ r γ =
  bindᵍ π₁ _ (⟦ df ⟧ ρ σ r (restrict σ (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) γ)) λ f →
  bindᵍ π₂ π (⟦ dx ⟧ ρ σ r (restrict σ (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) γ)) λ x → f x

-- An erased right-hand side is not evaluated.
⟦ ⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = Zero} d₁ d₂ ⟧ ρ σ r γ =
  ⟦ d₂ ⟧ ρ σ r (restrict σ (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) γ , tt)
⟦ ⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = One} {π₁} {π₂} d₁ d₂ ⟧ ρ σ r γ =
  bindᵍ π₁ π₂ (⟦ d₁ ⟧ ρ σ r (restrict σ (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) γ)) λ v →
  ⟦ d₂ ⟧ ρ σ r (restrict σ (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) γ , v)
⟦ ⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = Many} {π₁} {π₂} d₁ d₂ ⟧ ρ σ r γ =
  bindᵍ π₁ π₂ (⟦ d₁ ⟧ ρ σ r (restrict σ (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) γ)) λ v →
  ⟦ d₂ ⟧ ρ σ r (restrict σ (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) γ , v)

⟦ ⊢unit ⟧ ρ σ r γ = tt

⟦ ⊢pair {Ψ₁ = Ψ₁} {Ψ₂} {π₁} {π₂} da db ⟧ ρ σ r γ =
  bindᵍ π₁ π₂ (⟦ da ⟧ ρ σ r (restrict σ (⊑ᵘ-+ˡ Ψ₁ Ψ₂) γ)) λ a →
  fmap π₂ (λ b → a , b) (⟦ db ⟧ ρ σ r (restrict σ (⊑ᵘ-+ʳ Ψ₁ Ψ₂) γ))
⟦ ⊢fst {π = π} d ⟧ ρ σ r γ = fmap π proj₁ (⟦ d ⟧ ρ σ r γ)
⟦ ⊢snd {π = π} d ⟧ ρ σ r γ = fmap π proj₂ (⟦ d ⟧ ρ σ r γ)

⟦ ⊢inl {π = π} d ⟧ ρ σ r γ = fmap π inj₁ (⟦ d ⟧ ρ σ r γ)
⟦ ⊢inr {π = π} d ⟧ ρ σ r γ = fmap π inj₂ (⟦ d ⟧ ρ σ r γ)
⟦ ⊢case {Ψs = Ψs} {Ψ} {qℓ} {qr} {π₁} {π₂} ds dl dr ⟧ ρ σ r γ =
  bindᵍ π₁ π₂ (⟦ ds ⟧ ρ σ r (restrict σ (⊑ᵘ-+ˡ Ψs Ψ) γ))
    [ (λ a → ⟦ dl ⟧ ρ σ r (restrict σ (⊑ᵘ-+ʳ Ψs Ψ) γ , slot qℓ a))
    , (λ b → ⟦ dr ⟧ ρ σ r (restrict σ (⊑ᵘ-+ʳ Ψs Ψ) γ , slot qr b)) ]′

⟦ ⊢absurd {π = π} d ⟧ ρ σ r γ = bind π (⟦ d ⟧ ρ σ r γ) ⊥-elim

⟦ ⊢roll {π = π} {F = F} wf d ⟧ ρ σ r γ = fmap π (λ l → inS (toL σ F (μ F) l)) (⟦ d ⟧ ρ σ r γ)
⟦ ⊢fold {Ψa = Ψa} {Ψt} {π} {π₁} {π₂} {F} {A} wf da dt ⟧ ρ σ r γ =
  bindᵍ π₁ _ (⟦ da ⟧ ρ σ r (restrict σ (⊑ᵘ-trans (⊑ᵘ-*Many Ψa) (⊑ᵘ-+ˡ (Many *ᵘ Ψa) Ψt)) γ)) λ alg →
  bindᵍ π₂ π (⟦ dt ⟧ ρ σ r (restrict σ (⊑ᵘ-+ʳ (Many *ᵘ Ψa) Ψt) γ)) λ v →
  foldM π (code (F ⟨ σ ⟩F)) (λ l → alg (fromL σ F A l)) v

⟦ ⊢unfold {Ψc = Ψc} {Ψs} {π} {π₁} {π₂} {F} {A} g wf dc da ⟧ ρ σ r γ =
  bindᵍ π₁ π₂ (⟦ dc ⟧ ρ σ r (restrict σ (⊑ᵘ-trans (⊑ᵘ-*Many Ψc) (⊑ᵘ-+ˡ (Many *ᵘ Ψc) Ψs)) γ)) λ c →
  fmap π₂ (anaM g (code (F ⟨ σ ⟩F)) (λ x → fmap π (toL σ F A) (c x)))
          (⟦ da ⟧ ρ σ r (restrict σ (⊑ᵘ-+ʳ (Many *ᵘ Ψc) Ψs) γ))
⟦ ⊢out {π = π} {π₁} {F} wf d ⟧ ρ σ r γ =
  bindᵍ π₁ π (⟦ d ⟧ ρ σ r γ) λ v → fmap π (fromL σ F (ν F π)) (outν v)

-- The server: the round is evaluated once, then the seed; the loop is the
-- anamorphism over the round.
⟦ ⊢iter {Ψf = Ψf} {Ψs} {π₁} {π₂} d ds ⟧ ρ σ r γ =
  bindᵍ π₁ _ (⟦ d ⟧ ρ σ r (restrict σ (⊑ᵘ-trans (⊑ᵘ-*Many Ψf) (⊑ᵘ-+ˡ (Many *ᵘ Ψf) Ψs)) γ)) λ f →
  bindᵍ π₂ eff (⟦ ds ⟧ ρ σ r (restrict σ (⊑ᵘ-+ʳ (Many *ᵘ Ψf) Ψs) γ)) λ a →
  loop f a

⟦ ⊢coerce {π = π} p d ⟧ ρ σ r γ = fmap π (conv σ p) (⟦ d ⟧ ρ σ r γ)

⟦ ⊢lit-int {i = i} ⟧   ρ σ r γ = Word.Width.fromℤ int-bits i
⟦ ⊢lit-float {d = d} ⟧ ρ σ r γ = round float-format d

⟦ ⊢prim {π = π} p d ⟧ ρ σ r γ = fmap π (primᵛ σ p) (⟦ d ⟧ ρ σ r γ)

⟦ ⊢sigop {c = c} {t} m ⟧ ρ σ r γ = sigopᵛ σ c t m (interp ρ)

⟦ ⊢ref d τ rd ⟧ ρ σ r γ =
  subst ⟦_⟧ᵛ (sym (⟨⟩-∘ (type (S !! d)) τ σ)) (defs ρ d (λ i → τ i ⟨ σ ⟩) (respects-∘ rd r))

⟦ ⊢sub-use p d ⟧ ρ σ r γ = ⟦ d ⟧ ρ σ r (restrict σ p γ)
⟦ ⊢sub-eff g d ⟧ ρ σ r γ = sub g (⟦ d ⟧ ρ σ r γ)
