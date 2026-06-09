------------------------------------------------------------------------
-- normalizer.Theory.Eval.HandlerCorrectness
--
-- FEASIBILITY PROBE for the transparency kernel (the one remaining deep
-- obligation: full correctness on ALL inputs, spec = nf).
--
-- `normalize = cata TermF normalize-step`, so transparency reduces to the
-- DENOTATIONAL correctness of the algebra `normalize-step`, one term
-- constructor at a time. This module discharges that for the single
-- NON-TRIVIAL constructor — the composition position `handle-comp`, which
-- is the only handler that actually rewrites rather than rebuilding — on
-- the implemented redex
--
--     id ∘ g  ⟶  g            (`id-left`)
--
-- We show that, IN THE DENOTATIONAL MODEL, the comp handler applied to a
-- layer whose left child is (the value of) an `id` code returns exactly
-- the right child unchanged. Both the schematic version (any type-code A
-- and any child value g) and the version on genuine `encode`-images are
-- proved; both hold definitionally (`refl`), so the handler's case
-- analysis — `is-id` dispatch through `Out`, `distrib`, `caseWithCtx` —
-- all computes in the model with no stuck redex.
--
-- This mirrors how totality was de-risked (one structural `cata` case
-- before the general theorem): it confirms `eval` of a `normalize-step`
-- branch "does the right thing on that tag" before committing to all
-- fifteen constructors.
--
-- Trust: NO axioms, NO postulates — pure computation in the model. (Even
-- funext, the lone axiom of EvalSound, is not needed here.)
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/HandlerCorrectness.agda
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module normalizer.Theory.Eval.HandlerCorrectness where

open import normalizer.Syntax.Types
  using (_≡_; refl; sym; trans; cong; ⊤; tt; _×_; _,_; _⊎_; inj₁; inj₂)
open import normalizer.Syntax.CCC using (Term; _∘_; id; fst; _*_)
open import normalizer.Encoding.Encoding using (TyFuncCode; TermCode'; TermF; encode)
open import normalizer.Testing.Evaluator using (⟦_⟧T; Fix; fix; eval)
open import normalizer.TCB0.Normalizer.Handlers
  using (handle-comp; comp-f-is-id; check-g-handler; comp-g-is-id; comp-fallback)
open import normalizer.TCB0.Normalizer.Dispatch using (is-id)
open import normalizer.Combinators.Chain using (caseWithCtx)

------------------------------------------------------------------------
-- Schematic version.
--
-- `fix (inj₁ A) : Fix TermF` is the value of the code at TermF position 0
-- (the `id` constructor, carrying a type code A). Feeding the comp handler
-- the layer ⟨ that , g ⟩ — i.e. the redex `id ∘ g` with an already-
-- normalized right child g — the handler returns g.
--
-- The whole `is-id`/`distrib`/`caseWithCtx` cascade computes, so this is
-- `refl`: in particular `eval Out (fix (inj₁ A))` peels the coproduct via
-- coherence⁻¹, the position-0 dispatch hits the `ret-yes` branch, and the
-- `caseWithCtx` selects `comp-f-is-id = fst`, projecting g back out.
------------------------------------------------------------------------

handle-comp-id-left :
  ∀ (A : ⟦ TyFuncCode ⟧T) (g : Fix TermF) →
  eval handle-comp (fix (inj₁ A) , g) ≡ g
handle-comp-id-left A g = refl

------------------------------------------------------------------------
-- On genuine encodings.
--
-- The schematic value `fix (inj₁ A)` is exactly `eval (encode (id {B})) tt`
-- (encode of `id` is `In ∘ inl ∘ ⌜ B ⌝Ty`, which evaluates to
-- `fix (inj₁ ⟦B⟧)`). So the handler, given the ENCODED `id` and the
-- ENCODED already-normal child `g`, returns the encoded `g` — the
-- per-constructor transparency content for the `id ∘ g` redex.
------------------------------------------------------------------------

handle-comp-correct-on-id-left :
  ∀ {A B} (g : Term A B) →
  eval handle-comp (eval (encode (id {B})) tt , eval (encode g) tt)
    ≡ eval (encode g) tt
handle-comp-correct-on-id-left g = refl

------------------------------------------------------------------------
-- The second redex of the comp handler: `f ∘ id ⟶ f` (`id-right`).
--
-- This exercises the SECOND dispatch tier (`check-g-handler`): the first
-- `is-id` test on the left child must FALL THROUGH (f is not `id`), then
-- the `is-id` test on the right child fires and the handler returns f.
-- Unlike `id-left`, the left child here must be a CONCRETE non-`id` code
-- so the position dispatch can reduce — we use `encode (fst {A} {B})`
-- (TermF position 2). The type codes A, B stay abstract: they only flow
-- through `K`-payloads, never matched. Still `refl`.
------------------------------------------------------------------------

handle-comp-correct-on-id-right :
  ∀ {A B} →
  eval handle-comp
       (eval (encode (fst {A} {B})) tt , eval (encode (id {A * B})) tt)
    ≡ eval (encode (fst {A} {B})) tt
handle-comp-correct-on-id-right = refl

------------------------------------------------------------------------
-- COMPLETE denotational specification of handle-comp, parametrised by the
-- `is-id` decision on each child.
--
-- `handle-comp` is `caseWithCtx comp-f-is-id check-g-handler ∘
-- prep-check-f-id`, a two-tier cascade driven entirely by `is-id`. Once we
-- KNOW each child's `is-id` result, the `distrib`/`caseWithCtx` plumbing
-- computes (case on inj₁/inj₂), so each branch is a `rewrite`-then-`refl`.
-- Together these three lemmas pin down the handler on every input, with NO
-- 15-way structural enumeration — the redex decision is delegated to
-- `eval is-id`. This is the reusable core for the comp case of any
-- structural transparency / idempotence proof.
--
--   1. left child is `id`   → return right child         (id-left)
--   2. left ≠ id, right = id → return (rebuilt) left      (id-right)
--   3. left ≠ id, right ≠ id → rebuild as a composition   (rebuild)
--
-- (`w₁`/`w₂` are the `is-id` "no" payloads; the separate reconstruction
-- fact `eval is-id v ≡ inj₂ v` for non-id v makes them literally v.)
------------------------------------------------------------------------

-- The handler factors through `is-id`: `eval handle-comp (v₁ , v₂)` is
-- definitionally `eval (caseWithCtx comp-f-is-id check-g-handler)
-- (v₂ , eval is-id v₁)`, and the inner `check-g-handler` likewise factors
-- through `eval is-id v₂`. So each branch is `cong` over the `is-id`
-- equation(s): substituting the known `inj₁ tt` / `inj₂ w` unblocks the
-- `distrib`/`caseWithCtx` case analysis, which then computes.

handle-comp-spec-id-left :
  ∀ (v₁ v₂ : Fix TermF) →
  eval is-id v₁ ≡ inj₁ tt →
  eval handle-comp (v₁ , v₂) ≡ v₂
handle-comp-spec-id-left v₁ v₂ e₁ =
  cong (λ s → eval (caseWithCtx comp-f-is-id check-g-handler) (v₂ , s)) e₁

handle-comp-spec-id-right :
  ∀ (v₁ v₂ w₁ : Fix TermF) →
  eval is-id v₁ ≡ inj₂ w₁ →
  eval is-id v₂ ≡ inj₁ tt →
  eval handle-comp (v₁ , v₂) ≡ w₁
handle-comp-spec-id-right v₁ v₂ w₁ e₁ e₂ =
  trans (cong (λ s → eval (caseWithCtx comp-f-is-id check-g-handler) (v₂ , s)) e₁)
        (cong (λ s → eval (caseWithCtx comp-g-is-id comp-fallback) (w₁ , s)) e₂)

handle-comp-spec-rebuild :
  ∀ (v₁ v₂ w₁ w₂ : Fix TermF) →
  eval is-id v₁ ≡ inj₂ w₁ →
  eval is-id v₂ ≡ inj₂ w₂ →
  eval handle-comp (v₁ , v₂) ≡ fix (inj₂ (inj₁ (w₁ , w₂)))
handle-comp-spec-rebuild v₁ v₂ w₁ w₂ e₁ e₂ =
  trans (cong (λ s → eval (caseWithCtx comp-f-is-id check-g-handler) (v₂ , s)) e₁)
        (cong (λ s → eval (caseWithCtx comp-g-is-id comp-fallback) (w₁ , s)) e₂)

------------------------------------------------------------------------
-- The `is-id` decision lemma — discharges the hypotheses above for ANY
-- value, with no extra assumptions.
--
-- `is-id` is TOTAL and FAITHFUL: on every code it returns either `inj₁ tt`
-- ("yes, id-headed") or `inj₂ v` ("no", reconstructing the SAME code v —
-- the dispatch's `rebuild-k` is identity-on-codes at every position). One
-- `refl` clause per TermF position (15); position 0 is the only "yes".
--
-- With this, the handle-comp spec is fully concrete: feeding the two
-- disjuncts into the three branch lemmas pins down `handle-comp` on every
-- pair of inputs.
------------------------------------------------------------------------

is-id-correct :
  ∀ (v : Fix TermF) →
  (eval is-id v ≡ inj₁ tt) ⊎ (eval is-id v ≡ inj₂ v)
is-id-correct (fix (inj₁ _)) = inj₁ refl
is-id-correct (fix (inj₂ (inj₁ _))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₁ _)))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₂ (inj₁ _))))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _)))))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _))))))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _)))))))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _))))))))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _)))))))))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _))))))))))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _)))))))))))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _))))))))))))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _)))))))))))))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _))))))))))))))) = inj₂ refl
is-id-correct (fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (_)))))))))))))))) = inj₂ refl

------------------------------------------------------------------------
-- TRICHOTOMY: the complete case analysis of `handle-comp` on an arbitrary
-- pair of values, with the `is-id` decisions discharged INTERNALLY.
--
-- This is the value-level core, elaborated ONCE over abstract `v₁ v₂`.
-- The normalize-level assembly (StepTransparency.normalize-comp-complete)
-- can then case-split on this single small ⊎ result instead of running a
-- nested `with is-id-correct (eval normalize cᵢ)` — the latter generalises
-- the giant `eval normalize …` subterms across a goal that already names
-- the heavy comp term three times, which is what exhausted memory. Here
-- the `with`s scrutinise `is-id` of plain variables, so the abstraction
-- stays tiny.
--
--   1. left = id          → right child v₂              (id-left)
--   2. left ≠ id, right=id → left child  v₁              (id-right)
--   3. left ≠ id, right≠id → rebuilt comp `fix (inj₂ (inj₁ (v₁ , v₂)))`
------------------------------------------------------------------------

private
  -- Abstract the (huge-normal-form) handler application `eval handle-comp
  -- (v₁ , v₂)` behind a fresh variable `r` carrying a `refl` witness, then
  -- PATTERN-MATCH (not `with`) on the two small `is-id` decisions. Because
  -- the result type is phrased over `r` — a variable — instead of the giant
  -- term, the case analysis never makes agda re-expand that term across the
  -- goal. That goal-normalisation under `with` is exactly what ballooned
  -- memory past 7 GB; phrased this way the proof stays tiny.
  tri-aux :
    ∀ (v₁ v₂ r : Fix TermF) →
    eval handle-comp (v₁ , v₂) ≡ r →
    (eval is-id v₁ ≡ inj₁ tt) ⊎ (eval is-id v₁ ≡ inj₂ v₁) →
    (eval is-id v₂ ≡ inj₁ tt) ⊎ (eval is-id v₂ ≡ inj₂ v₂) →
    (r ≡ v₂) ⊎ ((r ≡ v₁) ⊎ (r ≡ fix (inj₂ (inj₁ (v₁ , v₂)))))
  tri-aux v₁ v₂ r eq (inj₁ y₁) _ =
    inj₁ (trans (sym eq) (handle-comp-spec-id-left v₁ v₂ y₁))
  tri-aux v₁ v₂ r eq (inj₂ n₁) (inj₁ y₂) =
    inj₂ (inj₁ (trans (sym eq) (handle-comp-spec-id-right v₁ v₂ v₁ n₁ y₂)))
  tri-aux v₁ v₂ r eq (inj₂ n₁) (inj₂ n₂) =
    inj₂ (inj₂ (trans (sym eq) (handle-comp-spec-rebuild v₁ v₂ v₁ v₂ n₁ n₂)))

handle-comp-trichotomy :
  ∀ (v₁ v₂ : Fix TermF) →
    (eval handle-comp (v₁ , v₂) ≡ v₂)
  ⊎ ((eval handle-comp (v₁ , v₂) ≡ v₁)
  ⊎ (eval handle-comp (v₁ , v₂) ≡ fix (inj₂ (inj₁ (v₁ , v₂)))))
handle-comp-trichotomy v₁ v₂ =
  tri-aux v₁ v₂ (eval handle-comp (v₁ , v₂)) refl
          (is-id-correct v₁) (is-id-correct v₂)
