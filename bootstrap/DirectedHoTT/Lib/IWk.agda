------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ OBJECT-LEVEL WEAKENING OVER AN INDEXED
-- DESCRIPTION, computed from the description.
--
--     iwkMeths D  :  the method tuple for `ielim D _ iwkMeths _`
--                    at the SHIFTING motive
--                        M(i,t) = IMu D I (sh ⟨i⟩)
--
-- `Examples/Knot/WkRows` is the hand-written control: four rows, one per
-- shape, and the generic method here must agree with it.
--
-- ★★ WHY THIS IS NOT `Lib/IFold` WITH A DIFFERENT ALGEBRA.  `IFold`
--   folds into the CONSTANT motive `Nat`, so it can take the IH at every
--   `iρ`.  A weakening cannot: a field PINNED at a literal index has its
--   IH at the shifted depth and the rebuilt row still wants the literal
--   one, so that field must take the ORIGINAL FIELD out of the payload.
--   Two `iρ` fields of `dκ` need opposite treatments.  That is the whole
--   reason this module exists and `IFold`'s shape does not reach it.
--
-- ★★★ SO THE DESCRIPTION MUST SAY WHICH, AND `WkIx` IS THAT.  ⚠ It is
--   DATA, not a proof: the classification is DECIDED from the raw index
--   expression (§2), and the generic method then inducts over it.  That
--   keeps the description a VARIABLE at the use site, which is the
--   condition `half-generalization-is-worst` says a generic lemma has to
--   meet — the classification is COMPUTED, never enumerated.
--
-- ⚠⚠ SCOPE, AND IT IS A REAL RESTRICTION.  `WkIx` covers a field whose
--   index either RIDES the ambient depth (`pair s (sucᵏ (snd ⟨i⟩))`) or
--   is PINNED (mentions the ambient nowhere).  It does NOT cover a
--   DEPTH-FORDED row, whose κ constrains `snd ⟨i⟩` and so needs the
--   witness re-proved under `nsuc` — `Examples/Knot/WkRows` §5 shows
--   that costs one `congS`.  In `KnotD` those are `cVar-vz`/`cVar-vs`,
--   2 rows of 53, and they are hand-written exactly as their smart
--   constructors already are in `Knot/Build`.
--
-- ⚠⚠ WHAT IS AND IS NOT BUILT HERE, STATED FIRST.
--
--     §1–§4  the classification, and the METHOD and TUPLE computed from
--            it — term level.                                   ✅ BUILT
--     §5     the classification DECIDED from a raw description.  ✅ BUILT
--            (`Examples/Knot/WkProbe` runs it on the knot: 12 row shapes
--            classify, and the two DEPTH-FORDED rows are REFUSED rather
--            than mis-classified.)
--     §6     the lemma the `pinned` case cashes out into.        ✅ BUILT
--     ⬜     `⊢iwkMethod` / `⊢iwkMeths` — THE TYPING.            NOT BUILT
--     ⬜     the per-row ESCAPE HATCH the probe showed is needed. NOT BUILT
--
--   ⇒ `iwkMeths` produces a TERM and nothing yet says it inhabits
--     `imethsTy`.  Do not read this module as a finished eliminator.
--     §7 names the three obligations that remain and what each rests on.
--
-- ★ THE ONE COLLAPSE THAT MAKES THE RIDING CASE UNIFORM.  A riding index
--   is `pair s (sucᵏ (snd ⟨i⟩))`, and
--
--       j[amb := sh i]  ⟶   pair s (sucᵏ (nsuc (snd i)))      (βsnd)
--       sh (j[amb := i]) ⟶* pair s (nsuc (sucᵏ (snd i)))      (βfst, βsnd)
--
--   and `sucᵏ (nsuc x)` IS `nsuc (sucᵏ x)` — both are `nsucᵏ⁺¹ x`,
--   definitionally.  So the two sides meet at ONE normal form by a chain
--   whose length does not depend on `k`, and the conversion is uniform.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.IWk where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; var; Var
        ; RTy; RTm; Unit; Σ'; El; IMu; Nat
        ; lam; pair; fst; snd; unit; nzero; nsuc; icon; ⌜Id⌝
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_
        ; Sub; extS; subTm; isingle; iext )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; occTm; subTm-occ )

------------------------------------------------------------------------
-- 1. THE SHIFT, and the two facts about it a method uses.
------------------------------------------------------------------------

-- `sh (pair a b) = pair a (nsuc b)`, written on the INDEX rather than on
-- its components so that it applies to an abstract `⟨i⟩`.
sh : {Γ : Cx} → RTm Γ → RTm Γ
sh i = pair (fst i) (nsuc (snd i))

-- ⚠ NATURALITY IS `refl`, and that is worth having rather than assuming:
--   `sh` is built from term FORMERS, so substitution walks straight
--   through it.  Every index chain below rests on this.
sh-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) (i : RTm Γ) → subTm σ (sh i) ≡ sh (subTm σ i)
sh-sub σ i = refl

------------------------------------------------------------------------
-- 2. ★★★ THE PER-FIELD CLASSIFICATION.
--
-- ⚠ INDEXED BY THE AMBIENT'S `Var`, not by a context.  As the telescope
--   grows the ambient moves out by one per field, so the classification
--   of a LATER field is against a LATER variable — and a `Var Δ` is the
--   only thing that tracks that.
------------------------------------------------------------------------

sucs : {Γ : Cx} → ℕ → RTm Γ → RTm Γ
sucs zero    t = t
sucs (suc k) t = nsuc (sucs k t)

-- ★ …and the collapse §0 promised, as a one-line induction.
sucs-nsuc : {Γ : Cx} (k : ℕ) (t : RTm Γ) → sucs k (nsuc t) ≡ nsuc (sucs k t)
sucs-nsuc zero    t = refl
sucs-nsuc (suc k) t = cong nsuc (sucs-nsuc k t)

-- `d` is `sucᵏ (snd ⟨i⟩)` for SOME k.  ⚠ As a DATATYPE rather than a
-- `Σ ℕ (λ k → d ≡ …)`: indexed by `d`, matching on it recovers the shape
-- definitionally, where a Forded equation would have to be transported
-- through every step of the typing lemma.
data IsSucs {Δ : Cx} (a : Var Δ) : RTm Δ → Set where
  is-snd : IsSucs a (snd (var a))
  is-suc : {d : RTm Δ} → IsSucs a d → IsSucs a (nsuc d)

depthOf : {Δ : Cx} {a : Var Δ} {d : RTm Δ} → IsSucs a d → ℕ
depthOf is-snd      = zero
depthOf (is-suc p)  = suc (depthOf p)

isSucs-eq : {Δ : Cx} {a : Var Δ} {d : RTm Δ} (p : IsSucs a d) →
            d ≡ sucs (depthOf p) (snd (var a))
isSucs-eq is-snd     = refl
isSucs-eq (is-suc p) = cong nsuc (isSucs-eq p)

data WkIx {Δ : Cx} (a : Var Δ) : RTm Δ → Set where
  -- the index RIDES the ambient depth: take the IH.
  rides  : (s : RTm Δ) {d : RTm Δ} → IsSucs a d → WkIx a (pair s d)
  -- the index does not mention the ambient at all: take the ORIGINAL
  -- FIELD.  ⚠ Its IH exists and is at the shifted depth; it is simply
  -- unusable, and the generic method never names it.
  pinned : (j : RTm Δ) → occTm a j ≡ false → WkIx a j

-- the κ fields a weakening can pass through unchanged
data WkKa {Δ : Cx} (a : Var Δ) : RTm Δ → Set where
  -- a CLOSED code — its type is untouched by the shift
  ka-clo : (κ : RTm Δ) → occTm a κ ≡ false → WkKa a κ
  -- ★ a TAG FORD.  `fst (sh ⟨i⟩) ⟶ fst ⟨i⟩` by `βfst`, so the witness
  --   the method was handed still serves.  ⚠ The right endpoint must not
  --   mention the ambient — that is what makes this the TAG ford and not
  --   the DEPTH one, which is out of scope (see the header).
  ka-fst : (c b : RTm Δ) → occTm a c ≡ false → occTm a b ≡ false →
           WkKa a (⌜Id⌝ c (fst (var a)) b)

-- a constructor a weakening can be computed for
data WkCon {Δ : Cx} (a : Var Δ) : ICon Δ → Set where
  wk-ι : WkCon a iι
  wk-ρ : {j : RTm Δ} {C : ICon (Δ ∙)} →
         WkIx a j → WkCon (vs a) C → WkCon a (iρ j C)
  wk-κ : {κ : RTm Δ} {C : ICon (Δ ∙)} →
         WkKa a κ → WkCon (vs a) C → WkCon a (iκ κ C)

-- ★★★ THE ESCAPE HATCH, AND IT IS STRUCTURAL.  `wkd-stop E` says
--   "classify no further; the methods for `E` are SUPPLIED".  ⚠ Note
--   what it is NOT: a parallel bookkeeping structure listing which rows
--   are hand-written, which would have to be kept in sync with the
--   description by hand.  The method tuple is RIGHT-NESTED, so
--   "classified rows, then given rows" is just where the nest stops —
--   and `WkDesc`'s own index says where.
--
-- ⇒ THE COST IS A CONDITION ON THE TABLE: the rows a weakening cannot
--   classify must be a SUFFIX of the description.  `KnotD` satisfies it
--   — `cVar-vz`/`cVar-vs` are rows 52–53 — and the generator already
--   appends exceptional rows last for an unrelated reason (`∈ID`
--   positions must not move).  This makes that convention LOAD-BEARING,
--   which is worth knowing before anyone reorders the table.
data WkDesc : IDesc → Set where
  wkd-stop : (E : IDesc) → WkDesc E
  wkd-cons : {C : ICon (ε ∙)} {E : IDesc} →
             WkCon vz C → WkDesc E → WkDesc (C ◂ E)

-- how many rows got classified — ★ OBSERVABLE, so a caller can ASSERT it
--   and a row that silently stops being classifiable is caught.
wkdLen : {E : IDesc} → WkDesc E → ℕ
wkdLen (wkd-stop _)   = zero
wkdLen (wkd-cons _ W) = suc (wkdLen W)

-- …and WHICH rows are left.  ⚠ The partner of `wkdLen`, and the reason
--   both exist: together they say exactly what the caller's tail must
--   inhabit — `imethsTyFrom D I M (j + wkdLen W) (wkdRest W)`.  That is
--   the escape hatch's contract, statable without mentioning a row.
wkdRest : {E : IDesc} → WkDesc E → IDesc
wkdRest (wkd-stop E)  = E
wkdRest (wkd-cons _ W) = wkdRest W

------------------------------------------------------------------------
-- 3. THE PAYLOAD, REBUILT.  ⚠ The two tuples are walked TOGETHER: `q` is
--    the original payload and `ih` the IH tuple, and `iihTy` skips κ
--    fields, so only an `iρ` advances `ih`.
------------------------------------------------------------------------

iwkPay : {Γ Δ : Cx} {a : Var Δ} {C : ICon Δ} →
         WkCon a C → RTm Γ → RTm Γ → RTm Γ
iwkPay wk-ι           q ih = unit
-- ★ RIDES ⇒ the IH.        ★ PINNED ⇒ the ORIGINAL FIELD.
iwkPay (wk-ρ (rides s p) w)  q ih = pair (fst ih) (iwkPay w (snd q) (snd ih))
iwkPay (wk-ρ (pinned j o) w) q ih = pair (fst q)  (iwkPay w (snd q) ih)
-- a κ field is passed through either way; what differs is the CONVERSION
-- its type needs, which is in the typing lemma and not here.
iwkPay (wk-κ _ w)     q ih = pair (fst q) (iwkPay w (snd q) ih)

------------------------------------------------------------------------
-- 4. THE METHOD, AND THE TUPLE — both computed, neither per-row.
--
-- ⚠ The method's three binders are the ELIMINATOR's, in `imethTy`'s
--   order: index, payload, IH tuple.  `Lib/IFold.ifMethod` has the same
--   shape; what differs is that its body folds to a `Nat` and this one
--   REBUILDS the constructor.
------------------------------------------------------------------------

iwkMethod : {Γ Δ : Cx} {a : Var Δ} {C : ICon Δ} → ℕ → WkCon a C → RTm Γ
iwkMethod k w = lam (lam (lam (icon k (iwkPay w (var (vs vz)) (var vz)))))

-- ⚠ THE TUPLE TAKES A TAIL, and that is the whole escape hatch at the
--   term level.  `wkd-stop` hands the tail straight back, so a caller
--   with no exceptional rows passes `unit` and gets the old behaviour.
iwkMethsFrom : {Γ : Cx} → ℕ → {E : IDesc} → WkDesc E → RTm Γ → RTm Γ
iwkMethsFrom k (wkd-stop _)   tl = tl
iwkMethsFrom k (wkd-cons w W) tl = pair (iwkMethod k w) (iwkMethsFrom (suc k) W tl)

iwkMeths : {Γ : Cx} {E : IDesc} → WkDesc E → RTm Γ → RTm Γ
iwkMeths W tl = iwkMethsFrom zero W tl

------------------------------------------------------------------------
-- 5. ★★★ THE CLASSIFICATION IS **DECIDED**, NOT SUPPLIED.
--
-- ⚠⚠ THIS SECTION IS WHY THE MODULE IS GENERIC AT ALL.  If a caller had
--   to write a `WkCon` per row, the enumeration would have moved into the
--   CONSUMER — measured the worst of the three options
--   (`half-generalization-is-worst`).  Here `WkKnot = get (decDesc
--   KnotD)`: one call, the description a variable, and the 53 rows are
--   classified by a structural recursion Agda runs.
------------------------------------------------------------------------

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

data ⊥ : Set where

-- ⚠ `Chk` COMPUTES.  At a concrete description `decDesc D` reduces to a
--   `just`, so `Chk` reduces to the unit type and the witness is `tt` —
--   which is what lets the caller write `get (decDesc D) tt` and never
--   name a row.  If a row were unclassifiable it would reduce to `⊥` and
--   the caller would not type-check: a LOUD failure, not a silent one.
record ⊤ : Set where
  constructor tt

Chk : {A : Set} → Maybe A → Set
Chk nothing  = ⊥
Chk (just _) = ⊤

get : {A : Set} (m : Maybe A) → Chk m → A
get (just x) _ = x
get nothing  ()

-- decidable `Var` equality, returning the EQUATION rather than a `𝔹`
decVar : {Δ : Cx} (a b : Var Δ) → Maybe (a ≡ b)
decVar vz     vz     = just refl
decVar (vs a) (vs b) with decVar a b
... | just e  = just (cong vs e)
... | nothing = nothing
decVar vz     (vs _) = nothing
decVar (vs _) vz     = nothing

-- ⚠ `occTm a t` must be OBSERVED, not scrutinised: a plain `with` throws
--   the equation away.  Indexing the helper by the result keeps it —
--   `natrec-branch-has-no-scrutinee-evidence`, the same encoding.
decOcc : {Δ : Cx} (a : Var Δ) (t : RTm Δ) → Maybe (occTm a t ≡ false)
decOcc a t = go (occTm a t) refl
  where
    go : (b : 𝔹) → occTm a t ≡ b → Maybe (occTm a t ≡ false)
    go false e = just e
    go true  e = nothing

decSucs : {Δ : Cx} (a : Var Δ) (d : RTm Δ) → Maybe (IsSucs a d)
decSucs a (snd (var b)) with decVar b a
... | just refl = just is-snd
... | nothing   = nothing
decSucs a (nsuc d) with decSucs a d
... | just p  = just (is-suc p)
... | nothing = nothing
decSucs a _ = nothing

-- ⚠ FLAT, WITH NAMED HELPERS, NOT NESTED `with`s.  A nested `with` whose
--   branches are laid out by `...` alignment silently loses a case and
--   Agda reports it as a coverage gap in a generated `with-NNN` — one
--   sighting was enough.
decPin : {Δ : Cx} (a : Var Δ) (j : RTm Δ) → Maybe (WkIx a j)
decPin a j with decOcc a j
... | just o  = just (pinned j o)
... | nothing = nothing

decIx : {Δ : Cx} (a : Var Δ) (j : RTm Δ) → Maybe (WkIx a j)
decIx a (pair s d) with decSucs a d
... | just p  = just (rides s p)
... | nothing = decPin a (pair s d)
decIx a j = decPin a j

decKaFord : {Δ : Cx} (a : Var Δ) (c e : RTm Δ) →
            Maybe (WkKa a (⌜Id⌝ c (fst (var a)) e))
decKaFord a c e with decOcc a c | decOcc a e
... | just oc | just oe = just (ka-fst c e oc oe)
... | just _  | nothing = nothing
... | nothing | _       = nothing

decKaClo : {Δ : Cx} (a : Var Δ) (κ : RTm Δ) → Maybe (WkKa a κ)
decKaClo a κ with decOcc a κ
... | just o  = just (ka-clo κ o)
... | nothing = nothing

decKa : {Δ : Cx} (a : Var Δ) (κ : RTm Δ) → Maybe (WkKa a κ)
decKa a (⌜Id⌝ c (fst (var b)) e) with decVar b a
... | just refl = decKaFord a c e
... | nothing   = decKaClo a (⌜Id⌝ c (fst (var b)) e)
decKa a κ = decKaClo a κ

decCon : {Δ : Cx} (a : Var Δ) (C : ICon Δ) → Maybe (WkCon a C)
decCon a iι = just wk-ι
decCon a (iρ j C) with decIx a j
... | nothing = nothing
... | just p with decCon (vs a) C
...   | just w  = just (wk-ρ p w)
...   | nothing = nothing
decCon a (iκ κ C) with decKa a κ
... | nothing = nothing
... | just p with decCon (vs a) C
...   | just w  = just (wk-κ p w)
...   | nothing = nothing

-- ★★★ AND SO `decDesc` IS **TOTAL**.  It classifies as far as it can and
--   stops — no `Maybe`, no `get`, no way for a caller to be blocked.
--
-- ⚠ AND IT STILL FAILS LOUDLY.  Stopping early does not silently drop
--   rows: it makes the TAIL bigger, and the caller has to inhabit
--   `imethsTyFrom D I M k E'` for whatever `E'` is left.  A row that
--   stops being classifiable turns into methods someone must write, not
--   into a wrong answer.  `wkdLen` makes it assertable on top of that.
decDesc : (E : IDesc) → WkDesc E
decDesc inil = wkd-stop inil
decDesc (C ◂ E) with decCon vz C
... | just w  = wkd-cons w (decDesc E)
... | nothing = wkd-stop (C ◂ E)

------------------------------------------------------------------------
-- 6. ★★ THE LEMMA THE `pinned` CASE RESTS ON.
--
-- A pinned field's index does not mention the ambient, so REPLACING the
-- ambient cannot move it — which is exactly why the ORIGINAL FIELD still
-- has the right type in the rebuilt row.  ⚠ Proved rather than asserted,
-- because it is the one step where the classification has to CASH OUT
-- into an equation the typing lemma can use.
--
-- `Spec/Variance.subTm-occ` does the work: it needs the two environments
-- to agree on every variable the term OCCURS IN, and non-occurrence of
-- `a` is precisely what rules `a` out of that set.
------------------------------------------------------------------------

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- `true ≢ false`, at the one place it is needed
tf : {A : Set} → true ≡ false → A
tf ()

pinned-stable : {Δ Γ : Cx} {a : Var Δ} {j : RTm Δ} {σ τ : Sub Δ Γ} →
                occTm a j ≡ false →
                ((y : Var Δ) → (a ≡ y → ⊥) → σ y ≡ τ y) →
                subTm σ j ≡ subTm τ j
pinned-stable {a = a} {j = j} o h = subTm-occ j agree
  where
    agree : (x : Var _) → occTm x j ≡ true → _
    agree x oc =
      h x (λ e → tf (trans (sym oc)
                           (trans (sym (cong (λ z → occTm z j) e)) o)))

------------------------------------------------------------------------
-- 7. ⬜ WHAT THE TYPING LEMMA STILL OWES, named so the next session does
--    not re-derive it.
--
-- `⊢iwkPay` has to show the rebuilt payload inhabits
-- `ipayTy D I (isingle (sh ⟨i⟩)) C`, walking `WkCon` and discharging one
-- obligation per field.  All three are identified, and one is done:
--
--   `pinned`   ⇒ ✅ §6.  `pinned-stable` says the field's index is FIXED
--                by replacing the ambient, so the ORIGINAL FIELD already
--                has the type the rebuilt row wants.  No conversion.
--
--   `rides`    ⇒ ⬜ the IH's index and the row's meet at ONE normal form,
--                by the collapse in the header (`sucs-nsuc`).  The chain
--                is, per field and INDEPENDENT of `k`:
--                  IH   `pair (fst (pair s dₖ)) (nsuc (snd (pair s dₖ)))`
--                        ⟶ βfst ⟶ βsnd ⟶   `pair s (nsuc dₖ)`
--                  row  `pair s (sucs k (snd (sh ⟨i⟩)))`
--                        ⟶ βsnd ⟶           `pair s (sucs k (nsuc (snd ⟨i⟩)))`
--                        ≡ `sucs-nsuc` ≡     `pair s (nsuc dₖ)`
--                `Examples/Knot/WkRows` does exactly this by hand at
--                `cTm-lam`, `cDCon-kap` and `cVar-vs` — three `ixFwd`
--                /`ixBack` steps — so the shape is known to work.  What
--                is open is stating it ONCE over an abstract `IsSucs`.
--
--   `ka-clo` / `ka-fst` ⇒ ⬜ `ka-clo` is `pinned-stable` again, on the
--                CODE rather than on an index.  `ka-fst` is one
--                conversion, `ξ-El (ξ-⌜Id⌝ˡ (βfst …))` — `WkRows.unFst`.
--
-- ✅ AND THE ESCAPE HATCH IS SETTLED (§2/§4): `wkd-stop` plus a TAIL
--   argument.  Its contract is statable without naming a row, which is
--   what makes the typing lemma's signature writable:
--
--     ⊢iwkMethsFrom :
--       (D : IDesc) (I : RTy ε) (M : RTy ((Γ ∙) ∙)) (j : ℕ)
--       {E : IDesc} (W : WkDesc E) (tl : RTm ⌊ Γ ⌋) →
--       Γ ⊢ tl ∷ imethsTyFrom D I M (j + wkdLen W) (wkdRest W) →
--       Γ ⊢ iwkMethsFrom j W tl ∷ imethsTyFrom D I M j E
--
--   ⇒ the caller supplies ONE tail and its ONE derivation.  No parallel
--     structure to keep in sync with the description, and a caller with
--     nothing exceptional passes `unit`/`⊢unit`.
------------------------------------------------------------------------
