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
-- ⚠⚠ CORRECTION (2026-08-29): "`Lib/IWk`'s classification serves
--   substitution UNCHANGED" is true of the TERM and FALSE of the TYPING.
--   Recorded here because it was asserted twice and the mask's
--   `sdGiven … ≡ 3` control appeared to confirm it — that control checks
--   which rows CLASSIFY, which is a term-level property.
--
--   ★ THE GAP: a `rides s cs p` field's method applies the IH, which
--     lands at `K (pair (sortMap s) …)`, while the payload slot wants
--     `K (pair s …)`.  Those agree only if `sortMap s ⟶* s`, and
--     `WkIx` records only that `s` is CLOSED.  ⚠ Weakening never needed
--     it because weakening does not touch the SORT — it bumps the depth.
--
--   ✅ AND THE PREMISE HOLDS, measured over `KnotD`: the 50 computed
--     rows' recursive fields use six sorts — `sTy` 9, `sTm` 57,
--     `sDesc` 4, `sDCon` 3, `sIDesc` 4, `sICon` 3 — and NEVER `sVar`,
--     which is the one sort `sortMap` moves.  `sVar` occurs only in the
--     three LOOKUP rows, which are given.
--
--   ⇒ so `Lib/ISub` needs its own index classification: `WkIx`'s, plus
--     a witness `sortMap s ⟶* s`.  ⚠ Decidable — `s` is a numeral, so
--     `pred⁵ s ≡ 0` decides it and the chain is built by recursion —
--     but it is DATA the weakening classifier does not carry.
--
-- ★★★ WHAT `Lib/IWk` DOES STILL GIVE, unchanged:
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
open import normalizer.Syntax.Types using ( _≡_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; Var; ICon; IDesc; _◂_; inil; iι; iρ; iκ
        ; app; lam; pair; fst; snd; unit; nsuc; icon; var; vz; vs )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; occTm )
open import DirectedHoTT.Spec.Typing using ( _⟶*_ )
open import DirectedHoTT.Lib.IWk
  using ( WkCon; wk-ι; wk-ρ; wk-κ; WkIx; rides; pinned; IsSucs; depthOf
        ; Maybe; just; nothing; decCon; decSucs; decClosed; WkKa; decKa )

module Sub
  -- ★ the ONE thing that differs from weakening: how a substitution is
  --   pushed under a binder.  Given the target depth `n` and the
  --   substitution `σ`, produce the pair one binder deeper.
  -- ⚠ IT TAKES THE SOURCE DEPTH TOO.  `extS` is an `ielim` at index
  --   `pair sVar (nsuc d)`, so building `σ⁺` needs `d`, not just the
  --   target `n` — the parameter cannot be `n σ ↦ σ⁺`.
  (extN : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ)   -- d n σ ↦ σ⁺
  -- ★ THE SORT MAP, and a decision procedure for the ONE property the
  --   typing needs of it.  ⚠ Both are parameters for the same reason
  --   `extN` is: `sortMap` is built over the KNOT and `Lib` may not
  --   import `Examples`.
  (smap : {Γ : Cx} → RTm Γ → RTm Γ)
  (decStable : {Δ : Cx} (s : RTm Δ) → Maybe (smap s ⟶* s))
  where

  ------------------------------------------------------------------------
  -- ★★★ THE REFINED INDEX CLASSIFICATION.
  --
  -- ⚠ `Lib/IWk`'s `WkIx` is NOT enough for the typing, though it is for
  --   the term — see this module's header.  A `rides` field's method
  --   applies the IH, which lands at `K (pair (smap s) …)` where the
  --   payload slot wants `K (pair s …)`; those agree only if
  --   `smap s ⟶* s`, and `WkIx` records only that `s` is CLOSED.
  --
  -- ★ So `SubIx` is `WkIx` plus exactly that witness.  Everything else —
  --   `IsSucs`, `depthOf`, the `pinned` case — is `Lib/IWk`'s, unchanged.
  ------------------------------------------------------------------------

  data SubIx {Δ : Cx} (a : Var Δ) : RTm Δ → Set where
    s-rides  : (s : RTm Δ) → ((x : Var Δ) → occTm x s ≡ false) →
               {d : RTm Δ} → IsSucs a d →
               smap s ⟶* s →
               SubIx a (pair s d)
    s-pinned : (j : RTm Δ) → ((x : Var Δ) → occTm x j ≡ false) → SubIx a j

  -- ⚠ THE DEPTH IS READ OFF THE `IsSucs`, exactly as in `Lib/IWk`: it is
  --   how many binders deeper the field sits, hence how many times `σ`
  --   must be extended.
  sDepth : {Δ : Cx} {a : Var Δ} {j : RTm Δ} → SubIx a j → ℕ
  sDepth (s-rides _ _ p _) = depthOf p
  sDepth (s-pinned _ _)    = zero

  ------------------------------------------------------------------------
  -- THE ROW, and its decider.
  --
  -- ⚠⚠ THE κ FIELDS ARE **NOT** SETTLED BY `Lib/IWk`'s `WkKa` EITHER,
  --   and this is the second place weakening and substitution part
  --   company.  `ka-fst` says a TAG FORD's witness "still serves"
  --   because `fst (sh ⟨i⟩) ⟶ fst ⟨i⟩` — the shift leaves the sort
  --   alone.  Substitution MAPS the sort, so at the new index the ford
  --   reads `smap (fst ⟨i⟩) ≡ s` and the old witness does not serve.
  --   ★ That gap is exactly what `Knot/SubMot`'s `sortConv` closes, so
  --   the classification can keep `WkKa` and let the TYPING pay — but it
  --   is worth knowing that `WkKa` is reused for its SHAPE here, not
  --   because its justification carries over.
  ------------------------------------------------------------------------

  data SubCon {Δ : Cx} (a : Var Δ) : ICon Δ → Set where
    sc-ι : SubCon a iι
    sc-ρ : {j : RTm Δ} {C : ICon (Δ ∙)} →
           SubIx a j → SubCon (vs a) C → SubCon a (iρ j C)
    sc-κ : {κ : RTm Δ} {C : ICon (Δ ∙)} →
           WkKa a κ → SubCon (vs a) C → SubCon a (iκ κ C)

  decSubIx : {Δ : Cx} (a : Var Δ) (j : RTm Δ) → Maybe (SubIx a j)
  decSubIx a (pair s d) with decSucs a d | decClosed s | decStable s
  ... | just p  | just cs | just st = just (s-rides s cs p st)
  ... | _       | _       | _       = decSPin a (pair s d)
    where
      decSPin : {Δ' : Cx} (b : Var Δ') (k : RTm Δ') → Maybe (SubIx b k)
      decSPin b k with decClosed k
      ... | just o  = just (s-pinned k o)
      ... | nothing = nothing
  decSubIx a j with decClosed j
  ... | just o  = just (s-pinned j o)
  ... | nothing = nothing

  decSubCon : {Δ : Cx} (a : Var Δ) (C : ICon Δ) → Maybe (SubCon a C)
  decSubCon a iι = just sc-ι
  decSubCon a (iρ j C) with decSubIx a j
  ... | nothing = nothing
  ... | just p with decSubCon (vs a) C
  ...   | just w  = just (sc-ρ p w)
  ...   | nothing = nothing
  decSubCon a (iκ κ C) with decKa a κ
  ... | nothing = nothing
  ... | just p with decSubCon (vs a) C
  ...   | just w  = just (sc-κ p w)
  ...   | nothing = nothing

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
          SubIx a j → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  sPick (s-rides _ _ p _) d n σ q ih =
    app (app ih (sucsN (depthOf p) n)) (extsN (depthOf p) d n σ)
  sPick (s-pinned _ _)    d n σ q ih = q

  ------------------------------------------------------------------------
  -- THE PAYLOAD, REBUILT.  ⚠ The two tuples are walked TOGETHER, as in
  -- `Lib/IWk.iwkPay`: `q` has a slot per FIELD and `ih` one per
  -- RECURSIVE field, so only the `ρ` case advances both.
  ------------------------------------------------------------------------

  isubPay : {Γ Δ : Cx} {a : Var Δ} {C : ICon Δ} →
            SubCon a C → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  isubPay sc-ι           d n σ q ih = unit
  isubPay (sc-ρ ix w)    d n σ q ih =
    pair (sPick ix d n σ (fst q) (fst ih)) (isubPay w d n σ (snd q) (snd ih))
  isubPay (sc-κ _ w)     d n σ q ih = pair (fst q) (isubPay w d n σ (snd q) ih)

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
               ℕ → SubCon a C → RTm Γ
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
              SubCon vz C → SubDesc E → SubDesc (C ◂ E)
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
  ... | false with decSubCon vz C
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

