------------------------------------------------------------------------
-- normalizer.Theory.Eval.StepTransparency
--
-- The ASSEMBLY step of the transparency kernel: wire the per-constructor
-- handler facts (HandlerCorrectness) into the recursive structure of
-- `normalize = cata TermF normalize-step`.
--
-- The crux is the cata-UNFOLDING lemma `normalize-unfold`: in the model,
-- `eval normalize` on a one-layer code `fix x` equals `normalize-step`
-- applied to the layer whose recursive children have ALREADY been
-- normalized (`fmap-Set TermF (eval normalize)`). This holds definitionally
-- — it is just the computation rule of `cata-Set`, modulo η for `eval`.
--
-- Specialised to the composition position it says
--
--     eval normalize (comp-code c₁ c₂)
--       ≡ eval handle-comp (eval normalize c₁ , eval normalize c₂)
--
-- and combining with the HandlerCorrectness probe gives the first
-- transparency result on a redex with ARBITRARY (not necessarily already-
-- normal) subterms:
--
--     eval normalize (comp-code (id-code A) c₂) ≡ eval normalize c₂
--
-- i.e. `normalize` collapses `id ∘ h` to `normalize h` for any h — genuine
-- forward progress past the NoRedex class (RealNormalizerFixpoint only had
-- already-normal inputs).
--
-- Trust: NO axioms, NO postulates. Everything is computation in the model.
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/StepTransparency.agda
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module normalizer.Theory.Eval.StepTransparency where

open import normalizer.Syntax.Types
  using (_≡_; refl; trans; cong; ⊤; tt; μ_; _×_; _,_; _⊎_; inj₁; inj₂)
open import normalizer.Encoding.Encoding using (TyFuncCode; TermCode'; TermF)
open import normalizer.Testing.Evaluator
  using (⟦_⟧T; ⟦_⟧FS; Fix; fix; eval; fmap-Set; coherence⁻¹)
open import normalizer.TCB0.Normalizer.Handlers
  using (normalize; normalize-step; handle-comp)
open import normalizer.TCB0.Normalizer.Dispatch using (is-id)
open import normalizer.Theory.Eval.HandlerCorrectness
  using (handle-comp-id-left; handle-comp-trichotomy)

------------------------------------------------------------------------
-- Value-level code constructors (the data `eval ∘ encode` produces).
------------------------------------------------------------------------

-- TermF position 0: id (carrying a type code).
id-code : ⟦ TyFuncCode ⟧T → Fix TermF
id-code A = fix (inj₁ A)

-- TermF position 1: composition of two child codes.
comp-code : Fix TermF → Fix TermF → Fix TermF
comp-code c₁ c₂ = fix (inj₂ (inj₁ (c₁ , c₂)))

-- TermF position 2: fst (carrying two type codes — a non-recursive leaf).
fst-code : ⟦ TyFuncCode ⟧T → ⟦ TyFuncCode ⟧T → Fix TermF
fst-code a b = fix (inj₂ (inj₂ (inj₁ (a , b))))

-- TermF position 4: pair of two child codes.
pair-code : Fix TermF → Fix TermF → Fix TermF
pair-code c₁ c₂ = fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (c₁ , c₂))))))

-- TermF position 7: case of two child (branch) codes.
case-code : Fix TermF → Fix TermF → Fix TermF
case-code c₁ c₂ =
  fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (c₁ , c₂)))))))))

------------------------------------------------------------------------
-- Specialisation to the composition position.
------------------------------------------------------------------------

normalize-comp :
  ∀ (c₁ c₂ : Fix TermF) →
  eval normalize (comp-code c₁ c₂)
    ≡ eval handle-comp (eval normalize c₁ , eval normalize c₂)
normalize-comp c₁ c₂ = refl

------------------------------------------------------------------------
-- Transparency on the `id ∘ h` redex, for ARBITRARY h.
--
-- `normalize` on an `id`-headed composition collapses to `normalize` of
-- the right child — the genuine `id ∘ h ⟶ h` rewrite carried through the
-- model on non-normal subterms. (`eval normalize (id-code A)` is itself
-- `id-code A`: id is a rebuild/non-redex, so the left child normalizes to
-- an `id` code, firing `handle-comp-id-left`.)
------------------------------------------------------------------------

normalize-id-left :
  ∀ (A : ⟦ TyFuncCode ⟧T) (c₂ : Fix TermF) →
  eval normalize (comp-code (id-code A) c₂) ≡ eval normalize c₂
normalize-id-left A c₂ =
  handle-comp-id-left A (eval normalize c₂)

------------------------------------------------------------------------
-- The rebuild-handler sweep.
--
-- Every handler other than `handle-comp` (and the deferred eta cases) just
-- rebuilds its constructor with `In`. Denotationally that makes `normalize`
-- a CONGRUENCE there: it recurses into the children and reassembles the
-- same tag. All hold by `refl` via `normalize-unfold` — the sweep over the
-- remaining 12 rebuild positions is this same one-liner shape.
--
-- Leaf constructor (no recursive children): `normalize` fixes it. `fst`
-- stores two type codes (a `K ⊗ K` payload `fmap` leaves untouched), so a
-- fst-code is a denotational fixpoint of `normalize`. Same shape for snd,
-- inl, inr, terminal, initial, In, Out, apply.
------------------------------------------------------------------------

normalize-fst :
  ∀ (a b : ⟦ TyFuncCode ⟧T) →
  eval normalize (fst-code a b) ≡ fst-code a b
normalize-fst a b = refl

-- Recursive constructors: `normalize` pushes through into the children.
-- These are the reusable inductive-step (congruence) lemmas for a future
-- structural transparency induction.

normalize-pair :
  ∀ (c₁ c₂ : Fix TermF) →
  eval normalize (pair-code c₁ c₂)
    ≡ pair-code (eval normalize c₁) (eval normalize c₂)
normalize-pair c₁ c₂ = refl

normalize-case :
  ∀ (c₁ c₂ : Fix TermF) →
  eval normalize (case-code c₁ c₂)
    ≡ case-code (eval normalize c₁) (eval normalize c₂)
normalize-case c₁ c₂ = refl

------------------------------------------------------------------------
-- COMPLETE characterization of `normalize` on a composition, with NO
-- hypotheses — the comp case of transparency, fully resolved.
--
-- Combining `normalize-comp` (peel to the handler on normalized children)
-- with the handler spec and the `is-id` decision lemma, `normalize` on a
-- comp-code always lands in exactly one of three shapes:
--
--   1. left child normalizes to `id`  → `normalize` of the right child;
--   2. else right child normalizes to `id` → `normalize` of the left child;
--   3. else → the rebuilt composition of the normalized children.
--
-- Both identity laws `id ∘ h ⟶ h` and `f ∘ id ⟶ f` are now carried through
-- the model on ARBITRARY subterms (the `f ∘ id` case was the piece the
-- previous round could not reach), and case 3 confirms `normalize` is a
-- congruence when no identity redex is present.
------------------------------------------------------------------------

-- The lift is a top-level `private` helper (elaborated once) that simply
-- PATTERN-MATCHES the small ⊎ result of `handle-comp-trichotomy` and
-- rewrites each disjunct's LHS through `normalize-comp`. No `with`, so the
-- giant `eval normalize (comp-code c₁ c₂)` term is never re-expanded across
-- the goal — the memory-cheap form.
private
  ncc-lift :
    ∀ (c₁ c₂ : Fix TermF) →
      (eval handle-comp (eval normalize c₁ , eval normalize c₂) ≡ eval normalize c₂)
    ⊎ ((eval handle-comp (eval normalize c₁ , eval normalize c₂) ≡ eval normalize c₁)
    ⊎ (eval handle-comp (eval normalize c₁ , eval normalize c₂)
         ≡ comp-code (eval normalize c₁) (eval normalize c₂))) →
      (eval normalize (comp-code c₁ c₂) ≡ eval normalize c₂)
    ⊎ ((eval normalize (comp-code c₁ c₂) ≡ eval normalize c₁)
    ⊎ (eval normalize (comp-code c₁ c₂)
         ≡ comp-code (eval normalize c₁) (eval normalize c₂)))
  ncc-lift c₁ c₂ (inj₁ d)        = inj₁ (trans (normalize-comp c₁ c₂) d)
  ncc-lift c₁ c₂ (inj₂ (inj₁ d)) = inj₂ (inj₁ (trans (normalize-comp c₁ c₂) d))
  ncc-lift c₁ c₂ (inj₂ (inj₂ d)) = inj₂ (inj₂ (trans (normalize-comp c₁ c₂) d))

normalize-comp-complete :
  ∀ (c₁ c₂ : Fix TermF) →
    (eval normalize (comp-code c₁ c₂) ≡ eval normalize c₂)
  ⊎ ((eval normalize (comp-code c₁ c₂) ≡ eval normalize c₁)
  ⊎ (eval normalize (comp-code c₁ c₂)
       ≡ comp-code (eval normalize c₁) (eval normalize c₂)))
normalize-comp-complete c₁ c₂ =
  ncc-lift c₁ c₂ (handle-comp-trichotomy (eval normalize c₁) (eval normalize c₂))
