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
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; Var; ICon; IDesc; _◂_; inil; iι; iρ; iκ
        ; app; lam; pair; fst; snd; unit; nzero; nsuc; icon; var; vz; vs; ⌜Id⌝; ⌜Nat⌝
        ; Sub; subTm; RTy; IMu; Nat; El; extS; ipayTy; sel 
        -- ★ for the promoted `isubMethod-red` block:
        ; subTm-subTm; extS; _∘ₛ_ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; occTm )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; csymᵀ; Ctx; ⌊_⌋; _⊢_∷_; ⊢app; ⊢conv; ⊢nsuc; iinst
        ; ⊢pair; ⊢unit; ⊢fst; ⊢snd
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ; IDescWf; iihTy; wk-single; βfst; βsnd ; single 
        -- ★ for the promoted `isubMethod-red` block:
        ; single; wk-single; β; step; done )
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢-cast; Sub⊢; Sub⊢-ext; iext-Sub⊢ )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy; w; _∙^_; w^; sub-w; extS^; pw^ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-⌜Id⌝ˡ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-IMu; ⟶ᵀ*-El )
-- ★ for the promoted `isubMethod-red` block:
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-appˡ )
open import DirectedHoTT.Lib.NatNum using ( num; num-sub )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ )
open import DirectedHoTT.Lib.IMeths using ( selCong )

-- ★ the two-element pair `InSD?` decides into.  ⚠ Local: `Lib/IWk`'s are
--   inside its own scope and this module sits beside it, not under it.
data ⊤sd : Set where
  ttsd : ⊤sd

data ⊥sd : Set where
open import DirectedHoTT.Lib.IWk
  using ( WkCon; wk-ι; wk-ρ; wk-κ; WkIx; rides; pinned; IsSucs; depthOf; sucs
        ; Maybe; just; nothing; decCon; decSucs; decClosed; decVar
        ; pinned-stable; isSucs-sub; payStep; sucs-red; sucs-sub )

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
  -- ⚠ INDEXED BY THE NUMERAL'S **VALUE**, not by a term, and the
  --   witness is Γ-GENERIC.  See `IsNum` below: the typing needs this
  --   proof AFTER a substitution has been applied, and only a value can
  --   cross the context boundary.
  (decStable : (k : ℕ) → Maybe ({Δ : Cx} → smap {Δ} (num k) ⟶* num k))
  -- ★★★ AND THE SORT FORD'S **ACTION**.  ⚠⚠ WEAKENING COPIES A κ FIELD
  --   AND SUBSTITUTION MAY NOT — the third place the two part company,
  --   and the one that changes the TERM rather than just the proof.
  --
  --   `Lib/IWk`'s `⊢kaComp` copies a tag ford because `fst (sh ⟨i⟩) ⟶
  --   fst ⟨i⟩`: the two ford types are CONVERTIBLE, so the same witness
  --   inhabits both.  Under substitution the output index reads
  --   `smap (fst ⟨i⟩)`, which does NOT reduce to `fst ⟨i⟩` — mapping the
  --   sort is the whole point of `smap`.  ⇒ the witness must be ACTED
  --   ON: given the row's tag `b` and a proof of `fst ⟨i⟩ ≡ b`, produce
  --   one of `smap (fst ⟨i⟩) ≡ b`.  An object-level congruence, so it is
  --   the customer's (over the knot: `jsub` along the ford).
  -- ⚠ IT TAKES THE AMBIENT SORT `fst ⟨i⟩` TOO.  The action is a
  --   SYMMETRIC transport — the base case is at the TAG and the goal is
  --   at the ambient — and `symN` names its source explicitly.  ⇒ so
  --   `isubPay` threads `fst ⟨i⟩` beside the depth; the sort was never
  --   needed while a κ field was a copy.
  (fordMap : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ)   -- fi, tag, witness
  where

  ------------------------------------------------------------------------
  -- ★★★ AND THE SORT IS A **NUMERAL** — which is DATA, not a side
  -- condition.  ⚠⚠ THIS IS THE SECOND HALF OF THE 2026-08-29 CORRECTION
  -- in this module's header, and it was found by trying to state
  -- `⊢sPick`.
  --
  -- ⚠ CLOSEDNESS CANNOT CROSS A SUBSTITUTION.  `⊢sPick`'s result lands
  --   at `IMu D I (pair (smap (subTm σ s)) …)` and the payload slot
  --   wants `subTm τ s`, so the witness is needed of `subTm σ s`, not of
  --   `s`.  But `s : RTm Δ` and `subTm σ s : RTm Γ` are in DIFFERENT
  --   CONTEXTS, so `subTm σ s ≡ s` is not even well-typed — closedness
  --   gives `pinned-stable`, which relates two substitutions and never
  --   strips one.  ★ No amount of care with `occTm` fixes this; the
  --   classification has to carry more.
  --
  -- ★ AND IT CAN, because every riding field's sort over `KnotD` is a
  --   literal TAG.  Recorded as `IsNum`, the sort has a VALUE in `ℕ`,
  --   which crosses contexts freely: `subTm σ s ≡ num (numOf p)` is a
  --   two-line induction, and closedness drops out as a COROLLARY
  --   (`isNum-occ`) instead of being assumed.  ⇒ the same Fording move the
  --   knot's indices use, one level up.
  ------------------------------------------------------------------------

  data IsNum {Δ : Cx} : RTm Δ → Set where
    n-zero : IsNum nzero
    n-suc  : {t : RTm Δ} → IsNum t → IsNum (nsuc t)

  numOf : {Δ : Cx} {s : RTm Δ} → IsNum s → ℕ
  numOf n-zero    = zero
  numOf (n-suc p) = suc (numOf p)

  -- ★ the value crosses the context boundary; the term does not.
  -- ⚠ NOT `Lib/NatNum.num-sub`, which is the statement about `num k`
  --   ITSELF.  This one starts from an arbitrary term KNOWN to be a
  --   numeral, which is the only form the classifier can hand over.
  isNum-sub : {Δ Γ : Cx} {s : RTm Δ} (p : IsNum s) (σ : Sub Δ Γ) →
            subTm σ s ≡ num (numOf p)
  isNum-sub n-zero    σ = refl
  isNum-sub (n-suc p) σ = cong nsuc (isNum-sub p σ)

  -- ⚠ AND CLOSEDNESS IS DERIVED, so `s-rides` need not carry it.
  isNum-occ : {Δ : Cx} {s : RTm Δ} → IsNum s → (x : Var Δ) → occTm x s ≡ false
  isNum-occ n-zero    x = refl
  isNum-occ (n-suc p) x = isNum-occ p x

  decNum : {Δ : Cx} (s : RTm Δ) → Maybe (IsNum s)
  decNum nzero    = just n-zero
  decNum (nsuc t) with decNum t
  ... | just p  = just (n-suc p)
  ... | nothing = nothing
  decNum _        = nothing

  ------------------------------------------------------------------------
  -- ★★★ AND THE κ CLASSIFICATION IS REFINED THE SAME WAY.  `Lib/IWk`'s
  -- `WkKa` records a tag ford's tag as CLOSED; the ACTION needs it as a
  -- NUMERAL, for the same reason `SubIx` does — `fordMap` is applied in
  -- `Γ` to data named in `Δ`, and only a value crosses that boundary.
  --
  -- ⚠ AND IT CARRIES THE STABILITY WITNESS TOO.  `fordMap`'s base case
  --   is `smap b ≡ b`, so the tag must be a sort `smap` fixes.  ★ That
  --   is not an extra assumption over the knot — it is the same premise
  --   `s-rides` already makes, and the mask's `sdGiven … ≡ 3` control
  --   reports immediately if any computed row fails it.
  ------------------------------------------------------------------------

  data SubKa {Δ : Cx} (a : Var Δ) : RTm Δ → Set where
    sk-clo : (κ : RTm Δ) → ((x : Var Δ) → occTm x κ ≡ false) → SubKa a κ
    -- ⚠ THE CODE IS PINNED TO `⌜Nat⌝`, not left abstract.  A tag ford's
    --   code is `⌜Nat⌝` because an index's components ARE naturals, and
    --   `fordMap`'s customer has to name a motive — over an abstract
    --   closed `c` there is no motive to name.  ★ Nothing is lost: a row
    --   whose ford has another code simply falls through to `sk-clo` or
    --   to GIVEN, and the mask's count reports it.
    sk-fst : {b : RTm Δ} (qb : IsNum b) →
             ({Γ : Cx} → smap {Γ} (num (numOf qb)) ⟶* num (numOf qb)) →
             SubKa a (⌜Id⌝ ⌜Nat⌝ (fst (var a)) b)

  decSKClo : {Δ : Cx} (a : Var Δ) (κ : RTm Δ) → Maybe (SubKa a κ)
  decSKClo a κ with decClosed κ
  ... | just o  = just (sk-clo κ o)
  ... | nothing = nothing

  decSKFord : {Δ : Cx} (a : Var Δ) (e : RTm Δ) →
              Maybe (SubKa a (⌜Id⌝ ⌜Nat⌝ (fst (var a)) e))
  decSKFord a e with decNum e
  ... | just qb = pickK (decStable (numOf qb))
    where
      pickK : Maybe ({Γ : Cx} → smap {Γ} (num (numOf qb)) ⟶* num (numOf qb)) →
              Maybe (SubKa a (⌜Id⌝ ⌜Nat⌝ (fst (var a)) e))
      pickK (just st) = just (sk-fst qb st)
      pickK nothing   = decSKClo a (⌜Id⌝ ⌜Nat⌝ (fst (var a)) e)
  ... | nothing = decSKClo a (⌜Id⌝ ⌜Nat⌝ (fst (var a)) e)

  decSubKa : {Δ : Cx} (a : Var Δ) (κ : RTm Δ) → Maybe (SubKa a κ)
  decSubKa a (⌜Id⌝ ⌜Nat⌝ (fst (var b)) e) with decVar b a
  ... | just refl = decSKFord a e
  ... | nothing   = decSKClo a (⌜Id⌝ ⌜Nat⌝ (fst (var b)) e)
  decSubKa a κ = decSKClo a κ

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
    s-rides  : {s : RTm Δ} (q : IsNum s) →
               {d : RTm Δ} → IsSucs a d →
               ({Γ : Cx} → smap {Γ} (num (numOf q)) ⟶* num (numOf q)) →
               SubIx a (pair s d)
    s-pinned : (j : RTm Δ) → ((x : Var Δ) → occTm x j ≡ false) → SubIx a j

  -- ⚠ THE DEPTH IS READ OFF THE `IsSucs`, exactly as in `Lib/IWk`: it is
  --   how many binders deeper the field sits, hence how many times `σ`
  --   must be extended.
  sDepth : {Δ : Cx} {a : Var Δ} {j : RTm Δ} → SubIx a j → ℕ
  sDepth (s-rides _ p _) = depthOf p
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
           SubKa a κ → SubCon (vs a) C → SubCon a (iκ κ C)

  decSPin : {Δ : Cx} (b : Var Δ) (k : RTm Δ) → Maybe (SubIx b k)
  decSPin b k with decClosed k
  ... | just o  = just (s-pinned k o)
  ... | nothing = nothing

  decSubIx : {Δ : Cx} (a : Var Δ) (j : RTm Δ) → Maybe (SubIx a j)
  decSubIx a (pair s d) with decSucs a d | decNum s
  ... | just p  | just q  = pick (decStable (numOf q))
    where
      pick : Maybe ({Γ : Cx} → smap {Γ} (num (numOf q)) ⟶* num (numOf q)) →
             Maybe (SubIx a (pair s d))
      pick (just st) = just (s-rides q p st)
      pick nothing   = decSPin a (pair s d)
  ... | _       | _       = decSPin a (pair s d)
  decSubIx a j = decSPin a j

  decSubCon : {Δ : Cx} (a : Var Δ) (C : ICon Δ) → Maybe (SubCon a C)
  decSubCon a iι = just sc-ι
  decSubCon a (iρ j C) with decSubIx a j
  ... | nothing = nothing
  ... | just p with decSubCon (vs a) C
  ...   | just w  = just (sc-ρ p w)
  ...   | nothing = nothing
  decSubCon a (iκ κ C) with decSubKa a κ
  ... | nothing = nothing
  ... | just p with decSubCon (vs a) C
  ...   | just w  = just (sc-κ p w)
  ...   | nothing = nothing

  -- ⚠ `nsuc^k` IS `Lib/IWk`'s `sucs`, IMPORTED rather than repeated.
  --   A local copy compiled fine and was WRONG to keep: `isSucs-sub`
  --   states the depth in terms of `sucs`, so a duplicate would have
  --   made every use of that lemma pay a rewrite between two identical
  --   definitions.
  -- `ext^k`, threading the depth: the j-th extension is taken at the
  -- depth the j-1 previous ones produced.
  extsN : {Γ : Cx} → ℕ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  extsN zero    d n σ = σ
  extsN (suc k) d n σ = extN (sucs k d) (sucs k n) (extsN k d n σ)

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
  sPick (s-rides _ p _) d n σ q ih =
    app (app ih (sucs (depthOf p) n)) (extsN (depthOf p) d n σ)
  sPick (s-pinned _ _)    d n σ q ih = q

  -- ★ AND THE κ FIELD IS NOT ALWAYS A COPY.  ⚠ A closed code is — its
  --   type does not mention the ambient, so both substitutions leave it
  --   alone.  A TAG FORD is not: see `fordMap`'s note above.
  kaPick : {Γ Δ : Cx} {a : Var Δ} {κ : RTm Δ} →
           SubKa a κ → RTm Γ → RTm Γ → RTm Γ
  kaPick (sk-clo _ _)  fi p = p
  kaPick (sk-fst qb _) fi p = fordMap fi (num (numOf qb)) p

  ------------------------------------------------------------------------
  -- THE PAYLOAD, REBUILT.  ⚠ The two tuples are walked TOGETHER, as in
  -- `Lib/IWk.iwkPay`: `q` has a slot per FIELD and `ih` one per
  -- RECURSIVE field, so only the `ρ` case advances both.
  ------------------------------------------------------------------------

  isubPay : {Γ Δ : Cx} {a : Var Δ} {C : ICon Δ} →
            SubCon a C → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  isubPay sc-ι           fi d n σ q ih = unit
  isubPay (sc-ρ ix w)    fi d n σ q ih =
    pair (sPick ix d n σ (fst q) (fst ih)) (isubPay w fi d n σ (snd q) (snd ih))
  isubPay (sc-κ ka w)    fi d n σ q ih =
    pair (kaPick ka fi (fst q)) (isubPay w fi d n σ (snd q) ih)

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
      (icon k (isubPay w (fst (var (vs (vs (vs (vs vz)))))) -- fi = fst ⟨i⟩
                         (snd (var (vs (vs (vs (vs vz)))))) -- d  = snd ⟨i⟩
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

  ------------------------------------------------------------------------
  -- ★★★ SELECTING A METHOD OUT OF THE TUPLE — the first reduction lemma
  -- this library has ever shipped, and the reason `sz` was the only
  -- agreement in the development.
  --
  -- ⚠⚠ `Lib/ISzRed` ships four such lemmas for the FOLD's methods, which
  --   is exactly why `Knot/SzAgree` can be generated at all.  `Lib/ISub`
  --   shipped NONE: every `⟶*` in it was a hypothesis it CONSUMES
  --   (`decStable`, `smap` stability), never a lemma it proves.  So
  --   nothing could reduce through `isubMeths`, and no agreement over
  --   `subTm` was statable.  `FUTURE.md` D′, third layer.
  --
  -- ★ AND IT BELONGS **HERE**, inside `Sub`, not factored out.  The
  --   corrected rule (`PLAN-RENAMING.md` §16.3) is *state each lemma
  --   over the smallest carrier that determines it* — and `isubMeths`
  --   mentions `isubMethod`, whose behaviour IS this module's
  --   parameters.  `Lib/ISzRed` is written against `IFold`'s parameters
  --   for the same correct reason.  ⇒ the earlier "parameterised modules
  --   are the trap" reading was wrong; what was wrong about
  --   `ifMeths-sel` is that SELECTION does not depend on the algebra.
  ------------------------------------------------------------------------

  -- ★ the k-th method of the walk, as a FUNCTION — computed, so a caller
  --   never names a position.
  sdMeth : {Γ : Cx} → ((k : ℕ) → RTm Γ) → ℕ → {E : IDesc} → SubDesc E → ℕ → RTm Γ
  sdMeth give j sd-nil          k       = unit
  sdMeth give j (sd-comp w W)   zero    = isubMethod j w
  sdMeth give j (sd-give W)     zero    = give j
  sdMeth give j (sd-comp w W)   (suc k) = sdMeth give (suc j) W k
  sdMeth give j (sd-give W)     (suc k) = sdMeth give (suc j) W k

  -- ★ "row k of the walk exists", DECIDED — `Lib/IMeths.InCD?`'s twin.
  InSD? : {E : IDesc} → SubDesc E → ℕ → Set
  InSD? sd-nil        k       = ⊥sd
  InSD? (sd-comp _ W) zero    = ⊤sd
  InSD? (sd-give W)   zero    = ⊤sd
  InSD? (sd-comp _ W) (suc k) = InSD? W k
  InSD? (sd-give W)   (suc k) = InSD? W k

  isubMeths-sel : {Γ : Cx} {give : (k : ℕ) → RTm Γ} {E : IDesc}
                  (W : SubDesc E) (j k : ℕ) → InSD? W k →
                  sel k (isubMeths give j W) ⟶* sdMeth give j W k
  isubMeths-sel (sd-comp w W) j zero    p = step (βfst _ _) done
  isubMeths-sel (sd-give W)   j zero    p = step (βfst _ _) done
  isubMeths-sel (sd-comp w W) j (suc k) p =
    step (selCong k (βsnd _ _)) (isubMeths-sel W (suc j) k p)
  isubMeths-sel (sd-give W)   j (suc k) p =
    step (selCong k (βsnd _ _)) (isubMeths-sel W (suc j) k p)

  -- how many rows the caller must supply, and where they are
  sdGiven : {E : IDesc} → SubDesc E → ℕ
  sdGiven sd-nil        = zero
  sdGiven (sd-comp _ W) = sdGiven W
  sdGiven (sd-give W)   = suc (sdGiven W)


  ------------------------------------------------------------------------
  -- ★★★ THE TYPING.
  --
  -- ⚠ FOUR PARAMETERS, and every one of them is here because `Lib` may
  --   not import `Examples` — exactly the reason `extN` is a parameter
  --   of the enclosing module.  ★ Which is also the right generic shape:
  --   what a customer supplies is its ACTION and its MOTIVE, and nothing
  --   below mentions a sort tag or the knot.
  --
  -- ⚠⚠ `⊢motApp` HANDS OVER THE IH **ELIMINATED**, not the motive.  The
  --   alternative — pass the motive and apply it here — needs `iinst`'s
  --   de Bruijn layout to unfold, which is precisely the knot-specific
  --   computation `Lib` cannot do.  ★ And the index is taken APART into
  --   `pair s dd` at the interface: a field's index IS a pair, and left
  --   whole every use would owe a `βsnd` that only the customer can
  --   discharge.  ⇒ state the equation at the shape it HAS.
  ------------------------------------------------------------------------

  module Typing
    (D : IDesc) (I : RTy ε)
    -- the SUBSTITUTION's own type: source depth `d`, target depth `n`
    (STy : {Γ : Cx} → RTm Γ → RTm Γ → RTy Γ)
    -- the motive, in the two slots `iihTy` binds: index, then element
    (M : {Γ : Cx} → RTy ((Γ ∙) ∙))
    (⊢ext : {Γ : Ctx} {d n σ : RTm ⌊ Γ ⌋} →
            Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ σ ∷ STy d n →
            Γ ⊢ extN d n σ ∷ STy (nsuc d) (nsuc n))
    (⊢motApp : {Γ : Ctx} {s dd u h m sb : RTm ⌊ Γ ⌋} →
               Γ ⊢ h ∷ iinst (pair s dd) u M → Γ ⊢ m ∷ Nat →
               Γ ⊢ sb ∷ STy dd m →
               Γ ⊢ app (app h m) sb ∷ IMu D I (pair (smap s) m))
    -- ★ and the ford action's typing.  ⚠ IT TAKES THE STABILITY CHAIN
    --   AS AN ARGUMENT: `sk-fst` carries it precisely so this can, and
    --   it is what the action's BASE CASE needs.
    (⊢fordMap : {Γ : Ctx} {fi t : RTm ⌊ Γ ⌋} (k : ℕ) →
                ({Δ : Cx} → smap {Δ} (num k) ⟶* num k) →
                Γ ⊢ fi ∷ Nat →
                Γ ⊢ t ∷ El (⌜Id⌝ ⌜Nat⌝ fi (num k)) →
                Γ ⊢ fordMap fi (num k) t ∷ El (⌜Id⌝ ⌜Nat⌝ (smap fi) (num k)))
    where

    -- ⚠ `⟶*-castₗ` now comes from `Lib/ICast`, beside the `⟶*-castᵣ`
    --   that `Knot/SubMot` had written independently three days later.

    sucs-red* : {Γ : Cx} (k : ℕ) {x y : RTm Γ} → x ⟶* y → sucs k x ⟶* sucs k y
    sucs-red* k done       = done
    sucs-red* k (step r q) = step (sucs-red k r) (sucs-red* k q)

    ⊢sucs : {Γ : Ctx} (k : ℕ) {n : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ Nat → Γ ⊢ sucs k n ∷ Nat
    ⊢sucs zero    dn = dn
    ⊢sucs (suc k) dn = ⊢nsuc (⊢sucs k dn)

    -- ★ `⊢extNK`, ITERATED — which is the whole reason step 1 came
    --   first.  ⚠ No cast: `extsN (suc k)` extends at `sucs k d`, and
    --   `⊢ext` lands at `nsuc (sucs k d) = sucs (suc k) d`, so the two
    --   sides MEET definitionally.  That is what threading the depth
    --   through `extsN` bought.
    ⊢extsN : {Γ : Ctx} (k : ℕ) {d n σ : RTm ⌊ Γ ⌋} →
             Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ σ ∷ STy d n →
             Γ ⊢ extsN k d n σ ∷ STy (sucs k d) (sucs k n)
    ⊢extsN zero    dd dn dσ = dσ
    ⊢extsN (suc k) dd dn dσ =
      ⊢ext (⊢sucs k dd) (⊢sucs k dn) (⊢extsN k dd dn dσ)

    ------------------------------------------------------------------------
    -- ★★★ ONE FIELD, TYPED.  The twin of `Lib/IWk`'s `⊢ixComp`, and it
    -- splits the same two ways — but the `rides` half is a DIFFERENT
    -- proof, because substitution moves the SORT and weakening does not.
    --
    -- ⚠ THE TWO HYPOTHESES ARE ABOUT `snd (σ a)` AND `snd (τ a)`, not
    --   about `σ a` and `τ a`.  A row's ambient index is a PAIR and only
    --   its DEPTH is what the field's index rides; `isSucs-sub` already
    --   states it that way, so this is the shape that composes.
    ------------------------------------------------------------------------

    ⊢sPick : {Γ Θ : Ctx} {σ τ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋} {a : Var ⌊ Θ ⌋}
             {j : RTm ⌊ Θ ⌋} {d n sb q ih : RTm ⌊ Γ ⌋}
             (ix : SubIx a j) →
             -- ⚠⚠ σ's HYPOTHESIS IS AN `≡` AND τ's IS A `⟶*`, and the
             --   asymmetry is forced by the CUSTOMER.  `σ` is
             --   `isingle ⟨i⟩` with `⟨i⟩` a VARIABLE, so `snd (σ a)` is
             --   the ambient depth on the nose.  `τ` is `isingle (pair
             --   (smap ⟨s⟩) n)` — a literal pair — so `snd (τ a)` is a
             --   STUCK PROJECTION and only `βsnd` moves it.
             --   ⇒ state each at the shape its own side has.
             snd (σ a) ≡ d → snd (τ a) ⟶* n →
             Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ sb ∷ STy d n →
             Γ ⊢ q  ∷ IMu D I (subTm σ j) →
             Γ ⊢ ih ∷ iinst (subTm σ j) q M →
             Γ ⊢ sPick ix d n sb q ih ∷ IMu D I (subTm τ j)
    -- ⚠ THE PINNED CASE IS `Lib/IWk`'s, VERBATIM: a closed index is not
    --   moved by either substitution, so the ORIGINAL field serves.
    ⊢sPick {σ = σ} {τ = τ} (s-pinned j o) hσ hτ dd dn dsb dq dih =
      ⊢-cast (cong (IMu D I) (pinned-stable j σ τ o)) dq
    -- ★ AND THE RIDING CASE IS THE ONE THE NUMERAL WAS FOR.  Three moves,
    --   in the order the goal presents them:
    --     · the IH lands at `smap (subTm σ s)`;
    --     · `isNum-sub` replaces that by `smap (num N)` — the ONLY step
    --       that crosses the context boundary, and the reason `IsNum`
    --       exists;
    --     · `st` reduces it to `num N`, which is `subTm τ s` again.
    ⊢sPick {Γ = Γ} {σ = σ} {τ = τ} {n = n} (s-rides {s = s} qn p st)
           hσ hτ dd dn dsb dq dih =
      -- ⚠ AND THE TWO ENDPOINTS ARE PAID IN DIFFERENT CURRENCIES: the
      --   SORT closes by an `≡` (`isNum-sub`), the DEPTH by a `⟶*` run
      --   BACKWARDS (`csymᵀ`).  One `⊢-cast` then one `⊢conv`, never a
      --   single step doing both.
      ⊢conv (⊢-cast (cong (λ z → IMu D I (pair z (sucs k n)))
                          (sym (isNum-sub qn τ)))
              (⊢conv (⊢-cast (cong (λ z → IMu D I (pair (smap z) (sucs k n)))
                                   (isNum-sub qn σ))
                       (⊢motApp dih (⊢sucs k dn)
                         (⊢-cast (cong (λ z → STy z (sucs k n)) (sym eqσ))
                                 (⊢extsN k dd dn dsb))))
                     (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairˡ st)))))
            (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairʳ redτ))))
      where
        k    = depthOf p
        eqσ  = trans (isSucs-sub p σ) (cong (sucs k) hσ)
        redτ = ⟶*-castₗ (isSucs-sub p τ) (sucs-red* k hτ)

    ------------------------------------------------------------------------
    -- ★★★ ONE κ FIELD, TYPED — and the two halves are not the same kind
    -- of step.  A CLOSED code is retyped by a cast, exactly as in
    -- `Lib/IWk`.  A TAG FORD is not retyped at all: its witness was
    -- REPLACED at the term level, and this is where that replacement is
    -- justified.
    ------------------------------------------------------------------------

    ⊢kaPick : {Γ Θ : Ctx} {σ τ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋} {a : Var ⌊ Θ ⌋}
              {κ : RTm ⌊ Θ ⌋} {fi t : RTm ⌊ Γ ⌋} (ka : SubKa a κ) →
              -- ⚠ same asymmetry as `⊢sPick`, same reason.
              fst (σ a) ≡ fi → fst (τ a) ⟶* smap fi → Γ ⊢ fi ∷ Nat →
              Γ ⊢ t ∷ El (subTm σ κ) →
              Γ ⊢ kaPick ka fi t ∷ El (subTm τ κ)
    ⊢kaPick {σ = σ} {τ = τ} (sk-clo κ o) hσ hτ dfi dt =
      ⊢-cast (cong El (pinned-stable κ σ τ o)) dt
    ⊢kaPick {σ = σ} {τ = τ} {fi = fi} (sk-fst qb st) hσ hτ dfi dt =
      ⊢conv (⊢-cast (cong (λ y → El (⌜Id⌝ ⌜Nat⌝ (smap fi) y))
                          (sym (isNum-sub qb τ)))
        (⊢fordMap (numOf qb) st dfi
          (⊢-cast (cong₂ (λ z y → El (⌜Id⌝ ⌜Nat⌝ z y))
                         hσ (isNum-sub qb σ))
                  dt)))
            (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-⌜Id⌝ˡ hτ))))

    ------------------------------------------------------------------------
    -- ★★★ THE PAYLOAD, REBUILT AND TYPED.  The twin of `Lib/IWk`'s
    -- `⊢iwkPay`, and structurally identical to it: the two tuples are
    -- walked together, only the `ρ` case advances both, and each field's
    -- component lemma decides what its slot owes.
    --
    -- ⚠ THE FOUR INDEX HYPOTHESES THREAD UNCHANGED through the recursive
    --   calls, because `iext σ u (vs x) = σ x` — extending the SOURCE
    --   context with a value does not touch what the ambient maps to.
    --   ⇒ no `cong`, no re-derivation per depth.
    --
    -- ★ AND THE IH SLOT NEEDS NO CAST, unlike `Lib/IWk`'s.  There the
    --   motive is `Mot D I`, whose instantiation leaves a `wk-single`
    --   round trip; here `⊢sPick` takes its hypothesis at `iinst` —
    --   which is the shape `iihTy` HANDS OVER.
    ------------------------------------------------------------------------

    ⊢isubPay : {Γ Θ : Ctx} {σ τ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋} {a : Var ⌊ Θ ⌋}
               {C : ICon ⌊ Θ ⌋} {fi d n sb : RTm ⌊ Γ ⌋}
               (w : SubCon a C) → IConWf D I Θ C → IDescWf I D →
               Sub⊢ Θ Γ σ → Sub⊢ Θ Γ τ →
               fst (σ a) ≡ fi → fst (τ a) ⟶* smap fi →
               snd (σ a) ≡ d → snd (τ a) ⟶* n →
               Γ ⊢ fi ∷ Nat → Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat →
               Γ ⊢ sb ∷ STy d n →
               (q ih : RTm ⌊ Γ ⌋) →
               Γ ⊢ q  ∷ ipayTy D I σ C →
               Γ ⊢ ih ∷ iihTy D I σ C q M →
               Γ ⊢ isubPay w fi d n sb q ih ∷ ipayTy D I τ C
    ⊢isubPay sc-ι iwf-ι wD hσ hτ fσ fτ sσ sτ dfi dd dn dsb q ih dq dih = ⊢unit
    ⊢isubPay {σ = σ} {τ = τ} (sc-ρ ix w) (iwf-ρ j dj wC) wD hσ hτ fσ fτ sσ sτ
             dfi dd dn dsb q ih dq dih =
      ⊢pair (ipayTy-wf D I (extS τ) _ wD wC (Sub⊢-ext hτ))
            c₀
            (⊢-cast (sym (payStep D I τ _ _))
              (⊢isubPay w wC wD (iext-Sub⊢ hσ (⊢fst dq)) (iext-Sub⊢ hτ c₀)
                        fσ fτ sσ sτ dfi dd dn dsb (snd q) (snd ih)
                        (⊢-cast (payStep D I σ (fst q) _) (⊢snd dq))
                        (⊢-cast (wk-singleTy {v = fst ih} _) (⊢snd dih))))
      where
        c₀ = ⊢sPick ix sσ sτ dd dn dsb (⊢fst dq) (⊢fst dih)
    ⊢isubPay {σ = σ} {τ = τ} (sc-κ {C = C'} ka w) (iwf-κ κ _ dc wC) wD hσ hτ fσ fτ sσ sτ
             dfi dd dn dsb q ih dq dih =
      ⊢pair (ipayTy-wf D I (extS τ) C' wD wC (Sub⊢-ext hτ))
            c₀
            (⊢-cast (sym (payStep D I τ (kaPick ka _ (fst q)) C'))
              (⊢isubPay w wC wD (iext-Sub⊢ hσ (⊢fst dq)) (iext-Sub⊢ hτ c₀)
                        fσ fτ sσ sτ dfi dd dn dsb (snd q) ih
                        (⊢-cast (payStep D I σ (fst q) C') (⊢snd dq))
                        dih))
      where
        c₀ = ⊢kaPick ka fσ fτ dfi (⊢fst dq)

  ------------------------------------------------------------------------
  -- ★★★ REDUCTION **THROUGH** A COMPUTED METHOD — the second half of what
  -- `PLAN-RENAMING.md` §16.2 said this library owed.
  --
  -- ⚠⚠ `Lib/ISzRed` ships four such lemmas for the FOLD's methods, which is
  --   why `Knot/SzAgree` can be generated at all.  `Lib/ISub` shipped NONE:
  --   every `⟶*` in it was a hypothesis it CONSUMES, never a lemma it
  --   proves.  `isubMeths-sel` (above) was half 1 — SELECTING a method.
  --   This is half 2 — REDUCING THROUGH one.
  --
  -- ★ AND THE β SPINE WAS NEVER THE PROBLEM.  Five βs peel `isubMethod`'s
  --   `lam⁵` on the first try (peeling `4·3·2·1·0` `appˡ`s — see
  --   `PLAN-RENAMING.md` §15.3, the count is not local to any one line).
  --   What blocks is that `isubPay` recurses on the `SubCon`, so with `w`
  --   abstract it is a NEUTRAL call and `subTm` cannot compute through it.
  --   ⇒ the content is naturality, and the βs are the easy part.
  --
  -- ⚠⚠ AND THE TWO PARAMETER FACTS ARE **HYPOTHESES, NOT LEMMAS**.  `extN`
  --   and `fordMap` are this module's parameters; how they behave under
  --   substitution is not knowable here, exactly as `decStable` is a
  --   parameter rather than a proof.  They are EXPLICIT ARGUMENTS rather
  --   than new module parameters, so the existing instantiations
  --   (`Knot/SubMot`, `Knot/RenTm`) are untouched and only a caller of
  --   these lemmas owes them.
  --
  -- ⚠ NON-VACUITY IS CONTROLLED at `Examples/Knot/ISubRedControl`, which
  --   discharges both hypotheses at a trivial instantiation.  A lemma whose
  --   hypotheses cannot be met proves nothing — that is exactly how
  --   `subTI` made `consistency` vacuous (`PLAN-INDEXED`).
  ------------------------------------------------------------------------

  -- the two hypotheses, named once
  ExtNSub : Set
  ExtNSub = {Γ Δ : Cx} (τ : Sub Γ Δ) (d n σ : RTm Γ) →
            subTm τ (extN d n σ) ≡ extN (subTm τ d) (subTm τ n) (subTm τ σ)

  FordMapSub : Set
  FordMapSub = {Γ Δ : Cx} (τ : Sub Γ Δ) (fi b p : RTm Γ) →
               subTm τ (fordMap fi b p) ≡ fordMap (subTm τ fi) (subTm τ b) (subTm τ p)

  ------------------------------------------------------------------------
  -- ★ THE CASCADE.  `isubPay` is built from `sPick` and `kaPick`, which
  --   are built from `extsN`/`sucs` and `fordMap`.  Each layer's
  --   naturality is one induction, and the two parameter facts enter
  --   ONLY where the parameter itself does.
  ------------------------------------------------------------------------

  -- ⚠ `cong₃` by hand: three-argument congruence is not in the prelude,
  --   and pattern-matching all three to `refl` is shorter than nesting
  --   `cong₂`.
  extN-cong₃ : {Γ : Cx} {a a' b b' c c' : RTm Γ} →
               a ≡ a' → b ≡ b' → c ≡ c' → extN a b c ≡ extN a' b' c'
  extN-cong₃ refl refl refl = refl

  extsN-sub : ExtNSub → {Γ Δ : Cx} (k : ℕ) (τ : Sub Γ Δ) (d n σ : RTm Γ) →
              subTm τ (extsN k d n σ) ≡ extsN k (subTm τ d) (subTm τ n) (subTm τ σ)
  extsN-sub hE zero    τ d n σ = refl
  extsN-sub hE (suc k) τ d n σ =
    trans (hE τ (sucs k d) (sucs k n) (extsN k d n σ))
          (extN-cong₃ (sucs-sub k τ d) (sucs-sub k τ n) (extsN-sub hE k τ d n σ))

  sPick-sub : ExtNSub → {Δ₀ : Cx} {a : Var Δ₀} {j : RTm Δ₀} (ix : SubIx a j) →
              {Γ Δ : Cx} (τ : Sub Γ Δ) (d n σ q ih : RTm Γ) →
              subTm τ (sPick ix d n σ q ih)
              ≡ sPick ix (subTm τ d) (subTm τ n) (subTm τ σ) (subTm τ q) (subTm τ ih)
  sPick-sub hE (s-rides _ p _) τ d n σ q ih =
    cong₂ (λ x y → app (app (subTm τ ih) x) y)
          (sucs-sub (depthOf p) τ n) (extsN-sub hE (depthOf p) τ d n σ)
  sPick-sub hE (s-pinned _ _)  τ d n σ q ih = refl

  kaPick-sub : FordMapSub → {Δ₀ : Cx} {a : Var Δ₀} {κ : RTm Δ₀} (ka : SubKa a κ) →
               {Γ Δ : Cx} (τ : Sub Γ Δ) (fi p : RTm Γ) →
               subTm τ (kaPick ka fi p) ≡ kaPick ka (subTm τ fi) (subTm τ p)
  kaPick-sub hF (sk-clo _ _)  τ fi p = refl
  kaPick-sub hF (sk-fst qb _) τ fi p =
    trans (hF τ fi (num (numOf qb)) p)
          (cong (λ z → fordMap (subTm τ fi) z (subTm τ p)) (num-sub τ (numOf qb)))

  ------------------------------------------------------------------------
  -- ★★★ THE LEMMA HALF 2 EXISTS FOR.
  ------------------------------------------------------------------------
  isubPay-sub : ExtNSub → FordMapSub →
                {Δ₀ : Cx} {a : Var Δ₀} {C : ICon Δ₀} (w : SubCon a C) →
                {Γ Δ : Cx} (τ : Sub Γ Δ) (fi d n σ q ih : RTm Γ) →
                subTm τ (isubPay w fi d n σ q ih)
                ≡ isubPay w (subTm τ fi) (subTm τ d) (subTm τ n)
                            (subTm τ σ) (subTm τ q) (subTm τ ih)
  isubPay-sub hE hF sc-ι        τ fi d n σ q ih = refl
  isubPay-sub hE hF (sc-ρ ix w) τ fi d n σ q ih =
    cong₂ pair (sPick-sub hE ix τ d n σ (fst q) (fst ih))
               (isubPay-sub hE hF w τ fi d n σ (snd q) (snd ih))
  isubPay-sub hE hF (sc-κ ka w) τ fi d n σ q ih =
    cong₂ pair (kaPick-sub hF ka τ fi (fst q))
               (isubPay-sub hE hF w τ fi d n σ (snd q) ih)

  isubPay-cong₆ : {Δ₀ : Cx} {a : Var Δ₀} {C : ICon Δ₀} (w : SubCon a C) →
                  {Γ : Cx} {fi fi' d d' n n' σ σ' q q' ih ih' : RTm Γ} →
                  fi ≡ fi' → d ≡ d' → n ≡ n' → σ ≡ σ' → q ≡ q' → ih ≡ ih' →
                  isubPay w fi d n σ q ih ≡ isubPay w fi' d' n' σ' q' ih'
  isubPay-cong₆ w refl refl refl refl refl refl = refl

  ------------------------------------------------------------------------
  -- ★★★ HALF 2, ASSEMBLED.  The five βs peel the spine (§15.3's
  --   `4·3·2·1·0`); then FOUR `subTm-subTm`s collapse the five nested
  --   single-substitutions into one composite, and `isubPay-sub` fires
  --   ONCE against it.
  --
  -- ⚠ COLLAPSE FIRST, PUSH ONCE.  Pushing `isubPay-sub` through the five
  --   substitutions one at a time needs a `cong (subTm …)` wrapper per
  --   layer and leaves four intermediate forms to name.  Composing them
  --   first means the naturality lemma is used exactly once, and the six
  --   argument slots then COMPUTE — `subTm` on a variable is `σ x`.
  ------------------------------------------------------------------------
  -- ⚠ THE `SubCon` BINDER IS `sw`, NOT `w`.  `Lib/Wk.w` is weakening, and
  --   naming the description `w` shadows it inside the `where` block —
  --   `w (w (w i))` then parses as the SubCon applied to arguments.
  isubMethod-red : ExtNSub → FordMapSub →
                   {Δ₀ : Cx} {a : Var Δ₀} {C : ICon Δ₀} (sw : SubCon a C) (k : ℕ)
                   {Γ : Cx} (i p ih n σ : RTm Γ) →
                   app (app (app (app (app (isubMethod k sw) i) p) ih) n) σ
                   ⟶* icon k (isubPay sw (fst i) (snd i) n σ p ih)
  isubMethod-red hE hF sw k {Γ} i p ih n σ =
    ⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
   (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
   (⟶*-trans (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
   (⟶*-trans (⟶*-appˡ (step (β _ _) done))
   (⟶*-trans (step (β _ _) done)
             (subst (λ z → z ⟶* icon k (isubPay sw (fst i) (snd i) n σ p ih))
                    (sym eq) done)))))
    where
      -- ⚠⚠ EVERY SUBSTITUTION IS PINNED.  With `_` for `subTm-subTm`'s
      --   two implicits the constraints block on the composite and NONE
      --   of the six argument slots solve — `meta-standing-for-a-computation`
      --   exactly: a meta here stands for a computation Agda must re-run,
      --   and it has nothing to run it against until the chain is named.
      S₁ = extS (extS (extS (extS (single i))))
      S₂ = extS (extS (extS (single p)))
      S₃ = extS (extS (single ih))
      S₄ = extS (single n)
      S₅ = single σ
      -- ★ FOUR OF THE SIX SLOTS NEED A TOWER, AT FOUR DIFFERENT DEPTHS.
      --   A slot bound at binder `j` arrives under `4-j` weakenings, so
      --   `i` (outermost) owes four, `p` three, `ih` two, `n` one, and
      --   `σ` (innermost) owes none.  Every one of them is `pw^` counted
      --   down — which is the whole reason to index it.
      --
      -- ⚠ `unc` UN-COLLAPSES FIRST.  `isubPay-sub` fired against the
      --   composite, so the slots come back as `subTm (…∘ₛ…) V`; the
      --   towers are stated on the NESTED form, where `pw^` applies with
      --   no rearrangement.  One helper, used six times.
      -- ★ the method's BODY, named once.  ⚠ every `subTm-subTm` below
      --   needs its term argument explicitly; with `_` the composite is
      --   what blocks, and nothing downstream solves.
      B : RTm (((((Γ ∙) ∙) ∙) ∙) ∙)
      B = isubPay sw (fst (var (vs (vs (vs (vs vz))))))
                     (snd (var (vs (vs (vs (vs vz))))))
                     (var (vs vz)) (var vz)
                     (var (vs (vs (vs vz)))) (var (vs (vs vz)))

      unc : (X : RTm (((((Γ ∙) ∙) ∙) ∙) ∙)) →
            subTm ((((S₅ ∘ₛ S₄) ∘ₛ S₃) ∘ₛ S₂) ∘ₛ S₁) X
            ≡ subTm S₅ (subTm S₄ (subTm S₃ (subTm S₂ (subTm S₁ X))))
      unc X = sym
        (trans (subTm-subTm {τ = S₅} {σ = S₄} (subTm S₃ (subTm S₂ (subTm S₁ X))))
        (trans (subTm-subTm {τ = S₅ ∘ₛ S₄} {σ = S₃} (subTm S₂ (subTm S₁ X)))
        (trans (subTm-subTm {τ = (S₅ ∘ₛ S₄) ∘ₛ S₃} {σ = S₂} (subTm S₁ X))
               (subTm-subTm {τ = ((S₅ ∘ₛ S₄) ∘ₛ S₃) ∘ₛ S₂} {σ = S₁} X))))

      eq-i : subTm ((((S₅ ∘ₛ S₄) ∘ₛ S₃) ∘ₛ S₂) ∘ₛ S₁) (var (vs (vs (vs (vs vz))))) ≡ i
      eq-i = trans (unc (var (vs (vs (vs (vs vz))))))
             (trans (cong (λ z → subTm S₅ (subTm S₄ (subTm S₃ z))) (pw^ {u = p}  3 i))
             (trans (cong (λ z → subTm S₅ (subTm S₄ z))            (pw^ {u = ih} 2 i))
             (trans (cong (subTm S₅)                               (pw^ {u = n}  1 i))
                                                                   (pw^ {u = σ}  0 i))))

      eq-p : subTm ((((S₅ ∘ₛ S₄) ∘ₛ S₃) ∘ₛ S₂) ∘ₛ S₁) (var (vs (vs (vs vz)))) ≡ p
      eq-p = trans (unc (var (vs (vs (vs vz)))))
             (trans (cong (λ z → subTm S₅ (subTm S₄ z)) (pw^ {u = ih} 2 p))
             (trans (cong (subTm S₅)                    (pw^ {u = n}  1 p))
                                                        (pw^ {u = σ}  0 p)))

      eq-ih : subTm ((((S₅ ∘ₛ S₄) ∘ₛ S₃) ∘ₛ S₂) ∘ₛ S₁) (var (vs (vs vz))) ≡ ih
      eq-ih = trans (unc (var (vs (vs vz))))
              (trans (cong (subTm S₅) (pw^ {u = n} 1 ih))
                                      (pw^ {u = σ} 0 ih))

      eq-n : subTm ((((S₅ ∘ₛ S₄) ∘ₛ S₃) ∘ₛ S₂) ∘ₛ S₁) (var (vs vz)) ≡ n
      eq-n = trans (unc (var (vs vz))) (pw^ {u = σ} 0 n)

      eq-σ : subTm ((((S₅ ∘ₛ S₄) ∘ₛ S₃) ∘ₛ S₂) ∘ₛ S₁) (var vz) ≡ σ
      eq-σ = trans (unc (var vz)) refl

      eq = cong (icon k)
             (trans (subTm-subTm {τ = S₅} {σ = S₄} (subTm S₃ (subTm S₂ (subTm S₁ B))))
             (trans (subTm-subTm {τ = S₅ ∘ₛ S₄} {σ = S₃} (subTm S₂ (subTm S₁ B)))
             (trans (subTm-subTm {τ = (S₅ ∘ₛ S₄) ∘ₛ S₃} {σ = S₂} (subTm S₁ B))
             (trans (subTm-subTm {τ = ((S₅ ∘ₛ S₄) ∘ₛ S₃) ∘ₛ S₂} {σ = S₁} B)
             (trans (isubPay-sub hE hF sw
                       ((((S₅ ∘ₛ S₄) ∘ₛ S₃) ∘ₛ S₂) ∘ₛ S₁)
                       (fst (var (vs (vs (vs (vs vz))))))
                       (snd (var (vs (vs (vs (vs vz))))))
                       (var (vs vz))
                       (var vz)
                       (var (vs (vs (vs vz))))
                       (var (vs (vs vz))))
                    (isubPay-cong₆ sw (cong fst eq-i) (cong snd eq-i)
                                      eq-n eq-σ eq-p eq-ih))))))

  ------------------------------------------------------------------------
  -- ★ ONE METHOD.  `isubMethod j w = lam⁵ (icon j (isubPay w <the five
  --   bound variables>))`, so a substitution reaching it must cross five
  --   binders — and `extS⁵ τ` fixes every one of those variables.  ⇒ the
  --   whole method is INVARIANT, and the only real content is
  --   `isubPay-sub`, which `Lib/ISub` already has.
  ------------------------------------------------------------------------

  isubMethod-sub : ExtNSub → FordMapSub →
                   {Δ₀ : Cx} {a : Var Δ₀} {C : ICon Δ₀} (w : SubCon a C) (j : ℕ) →
                   {Γ Δ : Cx} (τ : Sub Γ Δ) →
                   subTm τ (isubMethod j w) ≡ isubMethod j w
  isubMethod-sub hE hF w j τ =
    cong (λ z → lam (lam (lam (lam (lam (icon j z))))))
         (isubPay-sub hE hF w (extS (extS (extS (extS (extS τ)))))
            _ _ _ _ _ _)

  ------------------------------------------------------------------------
  -- ★★★ THE TUPLE.  Induction on the walk; the `sd-comp` slots are
  --   `isubMethod-sub` above, and the `sd-give` slots are the caller's
  --   business — hence the hypothesis.
  --
  -- ⚠ `give` MUST BE Γ-GENERIC (`{Γ : Cx} → ℕ → RTm Γ`).  `isubMeths` takes
  --   it at a FIXED `Γ`, but invariance relates `give {Γ}` to `give {Δ}`,
  --   which cannot even be WRITTEN for a Γ-fixed function.  `renGiveK` and
  --   `giveK` are both already generic, so nothing at the call sites moves.
  ------------------------------------------------------------------------

  GiveSub : ({Γ : Cx} → ℕ → RTm Γ) → Set
  GiveSub give = {Γ Δ : Cx} (τ : Sub Γ Δ) (k : ℕ) → subTm τ (give {Γ} k) ≡ give {Δ} k

  isubMeths-sub : ExtNSub → FordMapSub →
                  {give : {Γ : Cx} → ℕ → RTm Γ} → GiveSub give →
                  {Γ Δ : Cx} (τ : Sub Γ Δ) {E : IDesc} (W : SubDesc E) (j : ℕ) →
                  subTm τ (isubMeths (give {Γ}) j W) ≡ isubMeths (give {Δ}) j W
  isubMeths-sub hE hF hg τ sd-nil        j = refl
  isubMeths-sub hE hF hg τ (sd-comp w W) j =
    cong₂ pair (isubMethod-sub hE hF w j τ) (isubMeths-sub hE hF hg τ W (suc j))
  isubMeths-sub hE hF hg τ (sd-give W)   j =
    cong₂ pair (hg τ j) (isubMeths-sub hE hF hg τ W (suc j))
