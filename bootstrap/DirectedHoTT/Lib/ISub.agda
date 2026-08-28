------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ SUBSTITUTION METHODS, COMPUTED FROM THE
-- DESCRIPTION.  The FOURTH customer of the method-tuple shape.
--
-- ⚠⚠ WHY COMPUTED AND NOT GENERATED, and it is MEASURED, not taste.
--   `Examples/Knot/Sz`'s header records the experiment: 53 methods, 53
--   method `⊢ty`s and 53 tuple rungs, GENERATED, cost **147s**, and two
--   attempts to speed the enumerated form up made it worse.  Computed
--   from the description the same thing is **5s** — ~30×.  Generating
--   `subTm`'s 53 methods would rebuild exactly the artifact that
--   measurement retired.
--
--   ⚠ NOT the same call as `Examples/Knot/SzAgree`, which IS generated:
--   those 30 clauses are `⟶*` CHAINS at concrete rows.  53 TYPING
--   DERIVATIONS at concrete rows are the expensive thing.
--
-- ★★★ AND THE CLASSIFICATION IS ALREADY BUILT.  `Lib/IWk`'s `WkCon` /
--   `WkIx` / `IsSucs` say exactly what substitution needs to know:
--
--     `rides s _ p`  — the field's index RIDES the ambient depth, and
--                      `depthOf p` is how many binders deeper it sits.
--                      ⇒ apply its IH at `nsuc^k n` and `ext^k σ`.
--     `pinned`       — the index is CLOSED, so substitution cannot move
--                      it.  ⇒ take the ORIGINAL field.
--
--   Measured over `KnotD`: 66 fields ride at depth 0, 10 at depth 1, one
--   at depth 2, four are pinned.  ⇒ FOUR shapes, and `Lib/IWk` already
--   distinguishes all four.  ★ That the weakening classification serves
--   substitution unchanged is the evidence that the two share a library.
--
-- ⚠ THE EXTENSION IS A PARAMETER, and it has to be: `extS` is built over
--   the KNOT (`Examples/Knot/SubMot`), and `Lib` may not import
--   `Examples`.  Which is also the right generic shape — the action is
--   the only thing that differs between customers.
--
-- ⬜⬜ AND THE TUPLE CANNOT USE `Lib/IMeths`' PREFIX HATCH.  Three rows
--   are NOT a payload rebuild — they APPLY `σ` instead:
--
--     `cTm-var`  — `subTm σ (var x) = σ x`.  ⚠ Not computable as a
--                  rebuild: the method's result would be `icon tagTm-var
--                  (pair <a Tm> …)`, i.e. `var` applied to a TERM.
--     `cVar-vz`, `cVar-vs` — at sort `sVar` the motive is `Tm n`
--                  (`sortMap sVar ⟶* sTm`), so these are the lookup too.
--
--   ⚠⚠ MEASURED: they sit at rows 11, 51 and 52 of 53 — NOT a
--   contiguous suffix.  `Lib/IMeths`' `cdTake` computes a PREFIX, so it
--   does not fit; `extS` only fitted because its two exceptions happened
--   to be last.
--
--   ⚠ AND TWO TEMPTING FIXES DO NOT WORK:
--     * moving `cTm-var` to the end of `KNOT` would displace
--       `cVar-vz`/`cVar-vs` from the suffix, breaking `Lib/IWk`'s hatch
--       — which needs exactly those two last (`wkdRest … ≡ cVar-vz ◂
--       cVar-vs ◂ inil`).  One problem traded for another.
--     * teaching `isubPay` a "lookup" field case does not help either:
--       `cTm-var`'s whole METHOD has a different shape, not one field.
--
--   ⇒ the walk `subTm` needs is a per-row MASK (computed | given), which
--   is a genuine generalisation of the prefix hatch — and the first one
--   the fourth customer has forced rather than suggested.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.ISub where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; Var; ICon; IDesc; _◂_; inil
        ; app; lam; pair; fst; snd; unit; nsuc; icon; var; vz; vs )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )
open import DirectedHoTT.Lib.IWk
  using ( WkCon; wk-ι; wk-ρ; wk-κ; WkIx; rides; pinned; IsSucs; depthOf
        ; Maybe; just; nothing; decCon )

module Sub
  -- ★ the ONE thing that differs from weakening: how a substitution is
  --   pushed under a binder.  Given the target depth `n` and the
  --   substitution `σ`, produce the pair one binder deeper.
  -- ⚠ IT TAKES THE SOURCE DEPTH TOO.  `extS` is an `ielim` at index
  --   `pair sVar (nsuc d)`, so building `σ⁺` needs `d`, not just the
  --   target `n` — the parameter cannot be `n σ ↦ σ⁺`.
  (extN : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ)   -- d n σ ↦ σ⁺
  where

  -- `nsuc^k`
  sucsN : {Γ : Cx} → ℕ → RTm Γ → RTm Γ
  sucsN zero    n = n
  sucsN (suc k) n = nsuc (sucsN k n)

  -- `ext^k`, threading the depth: the j-th extension is taken at the
  -- depth the j-1 previous ones produced.
  extsN : {Γ : Cx} → ℕ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  extsN zero    d n σ = σ
  extsN (suc k) d n σ = extN (sucsN k d) (sucsN k n) (extsN k d n σ)

  ------------------------------------------------------------------------
  -- ONE FIELD.
  --
  -- ⚠ A `pinned` field takes the ORIGINAL, exactly as in `Lib/IWk` — and
  --   for the same reason one step over: its index is closed, so the
  --   substitution has nothing to act on.  ⚠ Its IH still EXISTS (every
  --   `iρ` gets one); it is simply not used.
  ------------------------------------------------------------------------

  sPick : {Γ Δ : Cx} {a : Var Δ} {j : RTm Δ} →
          WkIx a j → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  sPick (rides _ _ p) d n σ q ih =
    app (app ih (sucsN (depthOf p) n)) (extsN (depthOf p) d n σ)
  sPick (pinned _ _)  d n σ q ih = q

  ------------------------------------------------------------------------
  -- THE PAYLOAD, REBUILT.  ⚠ The two tuples are walked TOGETHER, as in
  -- `Lib/IWk.iwkPay`: `q` has a slot per FIELD and `ih` one per
  -- RECURSIVE field, so only the `ρ` case advances both.
  ------------------------------------------------------------------------

  isubPay : {Γ Δ : Cx} {a : Var Δ} {C : ICon Δ} →
            WkCon a C → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  isubPay wk-ι           d n σ q ih = unit
  isubPay (wk-ρ ix w)    d n σ q ih =
    pair (sPick ix d n σ (fst q) (fst ih)) (isubPay w d n σ (snd q) (snd ih))
  isubPay (wk-κ _ w)     d n σ q ih = pair (fst q) (isubPay w d n σ (snd q) ih)

  ------------------------------------------------------------------------
  -- ★★★ THE METHOD.
  --
  -- Binder layout: `imethTy` binds the index, the payload and the IH
  -- tuple; the motive adds `n` and `σ`.  Five in all:
  --
  --     σ = vz · n = vs vz · ih = vs² vz · p = vs³ vz · i = vs⁴ vz
  --
  -- ⚠ `C` STAYS ABSTRACT.  The row is consulted only through its
  --   CLASSIFICATION, exactly as `Lib/IFold` consults it only through the
  --   `ICon` — which is what keeps this one proof rather than 53.
  ------------------------------------------------------------------------

  isubMethod : {Γ Δ : Cx} {a : Var Δ} {C : ICon Δ} →
               ℕ → WkCon a C → RTm Γ
  isubMethod k w =
    lam (lam (lam (lam (lam
      (icon k (isubPay w (snd (var (vs (vs (vs (vs vz)))))) -- d = snd ⟨i⟩
                         (var (vs vz))                     -- n
                         (var vz)                          -- σ
                         (var (vs (vs (vs vz))))           -- the payload
                         (var (vs (vs vz)))))))))          -- the IH tuple

  ------------------------------------------------------------------------
  -- ★★★ THE MASK: PER ROW, COMPUTED **OR** GIVEN.
  --
  -- ⚠⚠ WHY NOT `Lib/IMeths`' PREFIX HATCH — MEASURED, see the header:
  --   `subTm`'s three σ-applying rows sit at 11, 51 and 52 of 53, so the
  --   exceptions are not a suffix and a prefix walk cannot express them.
  --
  -- ★ AND THE MASK IS NOT MERELY A LENGTH: a computed row carries its
  --   CLASSIFICATION, exactly as `Lib/IWk`'s `wkd-cons` does.  That is
  --   the difference between this and `Lib/IMeths`, and it is why the
  --   mask lives here rather than there.
  ------------------------------------------------------------------------

  data SubDesc : IDesc → Set where
    sd-nil  : SubDesc inil
    sd-comp : {C : ICon (ε ∙)} {E : IDesc} →
              WkCon vz C → SubDesc E → SubDesc (C ◂ E)
    sd-give : {C : ICon (ε ∙)} {E : IDesc} → SubDesc E → SubDesc (C ◂ E)

  -- ★ THE MASK IS COMPUTED, from a predicate naming the LOOKUP rows.
  --
  -- ⚠ AND IT IS TOTAL IN BOTH DIRECTIONS.  A row the caller does not
  --   flag is still only computed if `Lib/IWk`'s decider classifies it;
  --   otherwise it falls back to GIVEN.  So an unclassifiable row can
  --   never block the walk — it just lands in the caller's lap, which is
  --   the same contract `decDesc` has.
  decSub : (give? : ℕ → 𝔹) → ℕ → (E : IDesc) → SubDesc E
  decSub give? j inil    = sd-nil
  decSub give? j (C ◂ E) with give? j
  ... | true  = sd-give (decSub give? (suc j) E)
  ... | false with decCon vz C
  ...   | just w  = sd-comp w (decSub give? (suc j) E)
  ...   | nothing = sd-give (decSub give? (suc j) E)

  ------------------------------------------------------------------------
  -- THE TUPLE.  ⚠ Right-nested, like every other method tuple here.
  ------------------------------------------------------------------------

  isubMeths : {Γ : Cx} → ((k : ℕ) → RTm Γ) → ℕ → {E : IDesc} → SubDesc E → RTm Γ
  isubMeths give j sd-nil        = unit
  isubMeths give j (sd-comp w W) = pair (isubMethod j w) (isubMeths give (suc j) W)
  isubMeths give j (sd-give W)   = pair (give j)         (isubMeths give (suc j) W)

  -- how many rows the caller must supply, and where they are
  sdGiven : {E : IDesc} → SubDesc E → ℕ
  sdGiven sd-nil        = zero
  sdGiven (sd-comp _ W) = sdGiven W
  sdGiven (sd-give W)   = suc (sdGiven W)
