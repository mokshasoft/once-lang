------------------------------------------------------------------------
-- ⚠⚠⚠ PARKED — A **NEGATIVE RESULT**.  THIS MODULE TYPECHECKS AND IS
--     NOT USED.  It is the spike that answered "should a judgement
--     row's `IConWf` be COMPUTED, the way `Lib/IWk` computes weakening
--     methods?"  ⇒ **NO — GENERATE IT.**  Kept because the measurement
--     is not re-derivable from the code that replaced it.
--
-- ★★★ IT WORKS.  `jsWf` really does replace `Examples/Knot/Lookup`'s
--   fifteen hand-written per-field lemmas (`W₁ … W₆`, `V₁ … V₉`) with
--   ONE induction, and the split below is a real fix.  It is simply far
--   more expensive than emitting the same rows as named definitions.
--
-- ⚠⚠ MEASURED, `_∋_∷_`'s `here` row:
--
--     hand-written `Knot/Lookup`   17 fields (BOTH rows)      3s
--       — plus the descriptions, the Wf proofs and an inhabitant
--     computed, first design        5 fields   ✗ killed at 106s
--     computed, shape/proof split   5 fields      20.6s / 2.1 GB
--     computed, split + named codes 7 fields      45.2s / 4.1 GB
--
--   ⇒ ~40× worse PER FIELD than the hand-written form, after BOTH fixes.
--
-- ★★★ AND THE MECHANISM, which is the part worth keeping.  A judgement
--   row's ford codes are INTRINSICALLY LARGE — a ford's third component
--   is the rule's own conclusion, transported through `jsub`/`symN`
--   (`Ctx-extK`, `Var-vsK`, `wkK`).  `JShape`'s index is a `Ctx` that
--   grows by one `El <code>` per field, so EVERY LATER FIELD'S TYPE
--   RE-EMBEDS ALL THE EARLIER CODES: quadratic in elaborated term size.
--
--   The hand-written form never pays it, because each `Θᵢ` and each `κᵢ`
--   is a `Def`: the index is a NAME and the body elaborates once behind
--   it.  Naming the codes here moved the cliff from 5 fields to 7 —
--   confirming the mechanism — but a datatype index cannot be given the
--   sharing that a definition gets for free.
--
-- ⇒ ★ GENERATION IS RIGHT FOR A PRINCIPLED REASON, not just empirically:
--   emitting a row as named `Θ`/`κ` definitions is exactly what keeps
--   elaborated term size LINEAR.  This is
--   `agda-cost-is-elaborated-term-size` applying at the level of a
--   DATATYPE INDEX rather than a function body.
--
-- ⚠ AND `jsWf` WOULD NOT HAVE PAID EVEN IF IT WERE FAST.  Per field it
--   is `jw-ford dc da db`; the emitted alternative is
--   `iwf-κ κᵢ (icw-ford _ _ _) (⊢⌜Id⌝ dc da db) Wᵢ₊₁` — the same three
--   derivations either way.  The hand-written `W` lemmas are scaffolding
--   around content that no scheme can compute, so there was less to win
--   here than the `Lib/IWk` analogy suggested.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- OCP-0009 · LIB — ⬜ SPIKE: ★★★ IS A JUDGEMENT ROW'S `IConWf`
-- **COMPUTABLE**?
--
-- `Examples/Knot/Lookup` proves `_∋_∷_`'s two `IConWf`s BY HAND —
-- `W₁ … W₆` and `V₁ … V₉`, one lemma per field. `PLAN-JUDGEMENT` step 3
-- is ~166 rows with more bookkeeping each, so the question is whether
-- that chain can be COMPUTED from a description of the row, the way
-- `Lib/IWk` computes weakening methods and `Lib/IFold` computes fold
-- methods.
--
-- ★ THE SPIKE'S ONE QUESTION: what does a row have to be TOLD, and what
--   can be worked out?
--
-- ⚠ THE ANSWER IS NOT "EVERYTHING".  A field's code is built from
--   variables and projections — computable — but a FORD's right-hand
--   side is the rule's actual content: `Ctx-extK`, `Var-vsK`, `wkK`,
--   each an ordinary function with its own typing lemma.  Nothing
--   generic can derive those, and pretending otherwise would just move
--   the work.
--
-- ⇒ so the split this file tests is: **the row supplies the derivations
--   that ARE its content; everything else is one induction.**
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.IJudge where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; RTy; IDesc; ICon; iι; iρ; iκ
        ; IMu; El; U; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; εwkTy; εwkTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; _⊢_∷_; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; ICodeWf; icw-clo; icw-ford; icw-imu; IDescWf )

------------------------------------------------------------------------
-- 1. ★★★ THE SHAPE — **CODES ONLY, NO DERIVATIONS**.
--
-- ⚠⚠ MEASURED, AND THIS SPLIT IS THE WHOLE DESIGN.  The first version
--   put a field's derivations in the same constructor as its code, so
--   the tail's TYPE was `JRow D I (jfExt f)` with `f` carrying three
--   `⊢jsub`-sized proofs.  `jfExt` discards them, but the index still
--   mentions `f`, so every later field re-embeds them:
--
--       3 binders                        3.2s
--       + the depth ford                 3.7s
--       + ONE transported ford      ✗ killed at 106s
--       + two                       ✗ killed at 233s
--
--   Nothing was wrong with the derivations — `Examples/Knot/Lookup`
--   proves the same things and checks in seconds.  They were wrong to
--   be in an INDEX (`agda-cost-is-elaborated-term-size`).
--
-- ⇒ the shape's index chain mentions only CODES, which are exactly the
--   terms the hand-written `κ`s are.  Same split `Lib/IWk` makes between
--   classifying a row and typing it.
------------------------------------------------------------------------

data JShape (D : IDesc) (I : RTy ε) : Ctx → Set where
  js-nil  : {Θ : Ctx} → JShape D I Θ

  -- a `Nat` binder — a CLOSED code
  js-nat  : {Θ : Ctx} → JShape D I (Θ ▹ El ⌜Nat⌝) → JShape D I Θ

  -- a binder at a NESTED indexed family: `Γ : Ctx m`, `A : RTy m`, …
  js-mu   : {Θ : Ctx} (E : IDesc) (J : RTy ε) (ix : RTm ⌊ Θ ⌋) →
            JShape D I (Θ ▹ El (⌜IMu⌝ E J ix)) → JShape D I Θ

  -- a FORDING constraint
  js-ford : {Θ : Ctx} (c a b : RTm ⌊ Θ ⌋) →
            JShape D I (Θ ▹ El (⌜Id⌝ c a b)) → JShape D I Θ

  -- ⚠ a RECURSIVE premise extends by `IMu D I j`, NOT by `El` — the one
  --   place the description being DEFINED appears, and why a row cannot
  --   be written before its own description exists.
  js-rec  : {Θ : Ctx} (j : RTm ⌊ Θ ⌋) →
            JShape D I (Θ ▹ IMu D I j) → JShape D I Θ

jsCon : {D : IDesc} {I : RTy ε} {Θ : Ctx} → JShape D I Θ → ICon ⌊ Θ ⌋
jsCon js-nil            = iι
jsCon (js-nat s)        = iκ ⌜Nat⌝ (jsCon s)
jsCon (js-mu E J ix s)  = iκ (⌜IMu⌝ E J ix) (jsCon s)
jsCon (js-ford c a b s) = iκ (⌜Id⌝ c a b) (jsCon s)
jsCon (js-rec j s)      = iρ j (jsCon s)

------------------------------------------------------------------------
-- 2. THE PROOFS, INDEXED BY THE SHAPE.
--
-- ★ Each constructor carries exactly the premises of the `iwf-κ`/`iwf-ρ`
--   it becomes — no more.  `ICodeWf` and `Θ ⊢ κ ∷ U` are DERIVED.
--
-- ⚠ A FORD'S THIRD DERIVATION IS THE RULE'S OWN CONTENT — the `b` side
--   is where `Ctx-extK`, `Var-vsK`, `wkK` live.  Nothing generic can
--   produce it, and pretending otherwise would only move the work.  What
--   this file removes is the scaffolding AROUND it.
------------------------------------------------------------------------

data JWf (D : IDesc) (I : RTy ε) : {Θ : Ctx} → JShape D I Θ → Set where
  jw-nil  : {Θ : Ctx} → JWf D I (js-nil {Θ = Θ})
  jw-nat  : {Θ : Ctx} {s : JShape D I (Θ ▹ El ⌜Nat⌝)} →
            JWf D I s → JWf D I (js-nat s)
  jw-mu   : {Θ : Ctx} {E : IDesc} {J : RTy ε} {ix : RTm ⌊ Θ ⌋}
            {s : JShape D I (Θ ▹ El (⌜IMu⌝ E J ix))} →
            IDescWf J E → Θ ⊢ ix ∷ εwkTy J →
            JWf D I s → JWf D I (js-mu E J ix s)
  jw-ford : {Θ : Ctx} {c a b : RTm ⌊ Θ ⌋}
            {s : JShape D I (Θ ▹ El (⌜Id⌝ c a b))} →
            Θ ⊢ c ∷ U → Θ ⊢ a ∷ El c → Θ ⊢ b ∷ El c →
            JWf D I s → JWf D I (js-ford c a b s)
  jw-rec  : {Θ : Ctx} {j : RTm ⌊ Θ ⌋} {s : JShape D I (Θ ▹ IMu D I j)} →
            Θ ⊢ j ∷ εwkTy I → JWf D I s → JWf D I (js-rec j s)

------------------------------------------------------------------------
-- 3. ★★★ AND THE WELL-FORMEDNESS IS **ONE INDUCTION**.
--
--    `W₁ … W₆` and `V₁ … V₉` — fifteen hand-written lemmas, one per
--    field — become this.
------------------------------------------------------------------------

jsWf : {D : IDesc} {I : RTy ε} {Θ : Ctx} {s : JShape D I Θ} →
       JWf D I s → IConWf D I Θ (jsCon s)
jsWf jw-nil = iwf-ι
jsWf (jw-nat w) =
  iwf-κ ⌜Nat⌝ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝ (jsWf w)
jsWf (jw-mu {E = E} {J = J} {ix = ix} d dx w) =
  iwf-κ (⌜IMu⌝ E J ix) (icw-imu ix d) (⊢⌜IMu⌝ d dx) (jsWf w)
jsWf (jw-ford {c = c} {a = a} {b = b} dc da db w) =
  iwf-κ (⌜Id⌝ c a b) (icw-ford c a b) (⊢⌜Id⌝ dc da db) (jsWf w)
jsWf (jw-rec {j = j} d w) =
  iwf-ρ j d (jsWf w)
