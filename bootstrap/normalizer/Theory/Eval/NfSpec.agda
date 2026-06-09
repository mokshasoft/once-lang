------------------------------------------------------------------------
-- normalizer.Theory.Eval.NfSpec
--
-- The SPEC normal form `nf : Term A B → Term A B` for the evaluator-route
-- transparency obligation (`RanzowFixpoint.EvalFullCorrectness.Correct`,
-- which needs a concrete `spec : Hom A B → Hom A B`).
--
-- `nf` is STRUCTURAL id-elimination: a congruence at every constructor, with
-- the SOLE rewrite being identity-composition collapse (`id ∘ g → g`,
-- `f ∘ id → f`) via `comp-nf`. It mirrors the bootstrap normalizer's
-- `normalize-step` EXACTLY — `handle-comp` does id-elimination, every other
-- handler is a plain rebuild (congruence). It is NOT the full reduction
-- system `_⟶_`: the product/coproduct/exponential β-rules (`fst ∘ ⟨f,g⟩ → f`,
-- …) are deliberately excluded.
--
-- SCOPE / compiler link (origin/heap-only-pivot-2, Plan 0.39): Once's real
-- correctness is SigOp-TRACE correctness, and value-level correctness is
-- blind to effects — but ONLY the "drop" rewrites (which delete subterms,
-- e.g. `fst ∘ ⟨f,g⟩ → f`, `terminal ∘ f → terminal`) can drop a SigOp and
-- thus need a trace-aware spec. `nf` performs NONE of those: id-elimination
-- is trace-transparent (`id ∘ f = f`, `g ∘ id = g` preserve `obs` by
-- construction). The bootstrap purpose needs only id-elimination (a correct
-- total normalizer with the Ranzow fixpoint; not an optimizer), so a
-- value-level spec is sound here and value-correctness ⟹ trace-correctness.
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/NfSpec.agda
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module normalizer.Theory.Eval.NfSpec where

open import normalizer.Syntax.Types using (_≡_; refl; trans; cong)
open import normalizer.Syntax.CCC
  using (Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_];
         terminal; initial; curry; apply; In; Out; cata)

------------------------------------------------------------------------
-- id-eliminating composition — the only non-congruence rule (mirrors
-- handle-comp). Detecting `id` directly in a `comp-nf` argument trips
-- Agda's coverage unification on the rich Term indices (Out/cata/…), so we
-- route the decision through a value-level `IsId?` detector (matched as a
-- value, no `with`, no 2-D Term split).
------------------------------------------------------------------------

-- Decision-with-proof: `yes-id` carries the index refinement `t = id`.
data IsId? : ∀ {A B} → Term A B → Set where
  yes-id : ∀ {A} → IsId? (id {A})
  no-id  : ∀ {A B} {t : Term A B} → IsId? t

isId? : ∀ {A B} (t : Term A B) → IsId? t
isId? id          = yes-id
isId? (f ∘ g)     = no-id
isId? fst         = no-id
isId? snd         = no-id
isId? ⟨ f , g ⟩   = no-id
isId? inl         = no-id
isId? inr         = no-id
isId? [ f , g ]   = no-id
isId? terminal    = no-id
isId? initial     = no-id
isId? (curry f)   = no-id
isId? apply       = no-id
isId? In          = no-id
isId? Out         = no-id
isId? (cata F alg) = no-id

-- PUBLIC (used by Adequacy's comp bridge). `yes-id` on f forces B = C
-- (id ∘ g → g); `yes-id` on g forces A = B (f ∘ id → f); else rebuild.
comp-elim : ∀ {A B C} (f : Term B C) (g : Term A B) → IsId? f → IsId? g → Term A C
comp-elim f g yes-id _      = g
comp-elim f g no-id  yes-id = f
comp-elim f g no-id  no-id  = f ∘ g

comp-nf : ∀ {A B C} → Term B C → Term A B → Term A C
comp-nf f g = comp-elim f g (isId? f) (isId? g)

------------------------------------------------------------------------
-- The spec normal form: structural id-elimination.
------------------------------------------------------------------------

nf : ∀ {A B} → Term A B → Term A B
nf id          = id
nf (f ∘ g)     = comp-nf (nf f) (nf g)
nf fst         = fst
nf snd         = snd
nf ⟨ f , g ⟩   = ⟨ nf f , nf g ⟩
nf inl         = inl
nf inr         = inr
nf [ f , g ]   = [ nf f , nf g ]
nf terminal    = terminal
nf initial     = initial
nf (curry f)   = curry (nf f)
nf apply       = apply
nf In          = In
nf Out         = Out
nf (cata F alg) = cata F (nf alg)
