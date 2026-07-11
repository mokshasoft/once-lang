------------------------------------------------------------------------
-- OCP-0009 · The neutrals frontier — what conversion should even DECIDE
--
-- Before building residualizing NbE for `μ`-domain (open) terms, one fact
-- must be pinned down, because it reframes the whole frontier and corrects a
-- tempting overclaim ("NbE decides `≋` on open terms" — it does NOT, and
-- cannot):
--
--   On OPEN terms, observational equality `_≋_` (= ∀ x. eval t x ≡ eval u x)
--   STRICTLY EXCEEDS definitional equality. `_≋_` on an infinite domain is
--   the full first-order theory of the model — it contains every inductive
--   theorem (`n+0 = n`, commutativity, …) and is therefore UNDECIDABLE.
--
-- A type-checker's conversion is the DEFINITIONAL fragment (what reduces),
-- a proper subset of `_≋_`; NbE decides that subset. The residual (`n+0=n`
-- and friends) is PROPOSITIONAL — proven by the user with induction / `J`,
-- deliberately NOT by conversion.
--
-- This module PROVES the split on the smallest witness:
--   * `0 + n ≋ n`  is DEFINITIONAL  — proved by `λ n → refl` (an open
--       conversion evaluation already decides: recursion is on the 1st arg).
--   * `n + 0 = n`  is PROPOSITIONAL — proved by induction (`+F-runit`); it
--       is NOT `refl`, so conversion / NbE does not and should not decide it.
--
-- So evaluation genuinely reaches *some* open conversions (first result),
-- and the boundary of the decidable (definitional) target is exactly the
-- reduce-vs-induct line (second result). The NbE ENGINE that decides the
-- definitional subset for open terms is the remaining engineering; this
-- fixes its correct TARGET.
------------------------------------------------------------------------

module poc.OCP0009.Open where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Testing.Evaluator hiding (fst; snd)
open import poc.OCP0009.Sound using (_≋_)
open import poc.OCP0009.Dependent using (Nat; NatF; zero; suc; add)

------------------------------------------------------------------------
-- Result 1 — an OPEN conversion that evaluation DECIDES (definitional).
--
--   plus0 = λ n. 0 + n.   Since `+` recurses on its FIRST argument,
--   `add 0` reduces to the identity function, so `0 + n` computes to `n`
--   with no induction — hence `plus0 ≋ id` holds pointwise by `refl`.
------------------------------------------------------------------------

plus0 : Term Nat Nat
plus0 = apply ∘ ⟨ add ∘ (zero ∘ terminal) , id ⟩

0+n≋n : plus0 ≋ id
0+n≋n n = refl

------------------------------------------------------------------------
-- Result 2 — the PROPOSITIONAL residual: `n + 0 = n` needs induction.
--
-- Peano addition on the model's `Nat = Fix NatF`, and the right-unit law,
-- proved by structural induction. This is the archetype of an equation that
-- is TRUE in the model (so it is a valid `_≋_`) but is NOT definitional —
-- it is not `refl`, so no conversion checker / NbE decides it.
------------------------------------------------------------------------

zeroF : Fix NatF
zeroF = fix (inj₁ tt)

sucF : Fix NatF → Fix NatF
sucF n = fix (inj₂ n)

infixl 30 _+F_
_+F_ : Fix NatF → Fix NatF → Fix NatF
fix (inj₁ tt) +F m = m
fix (inj₂ n)  +F m = sucF (n +F m)

-- Left unit is definitional (computes): `0 +F m = m` by `refl`.
+F-lunit : ∀ m → zeroF +F m ≡ m
+F-lunit m = refl

-- Right unit is propositional: needs induction on the first argument.
+F-runit : ∀ n → n +F zeroF ≡ n
+F-runit (fix (inj₁ tt)) = refl
+F-runit (fix (inj₂ n))  = cong sucF (+F-runit n)

------------------------------------------------------------------------
-- The split, side by side:
--
--   0 + n ≋ n   :  `λ n → refl`         (definitional — conversion decides)
--   n + 0 = n   :  induction (+F-runit) (propositional — J/induction only)
--
-- Both are true equalities of the model. Only the first is definitional, so
-- only the first is in a checker's conversion / NbE target. `_≋_` on the
-- infinite `Nat` domain contains BOTH (and all of Peano arithmetic), hence
-- is undecidable — which is *why* the checker targets the definitional
-- subset, not `_≋_` itself.
------------------------------------------------------------------------
