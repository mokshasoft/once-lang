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
-- ⚠ WHAT IS BUILT.
--
--     §1–§4  the classification, and the METHOD and TUPLE computed from
--            it — term level.
--     §5     the classification DECIDED from a raw description.
--     §6     `pinned-stable`, the lemma the `pinned` case cashes out to.
--     §8–§9  ★ THE TYPING: `⊢iwkPay`, `⊢iwkMethod`, `⊢iwkMethsFrom`.
--
--   ⇒ `iwkMeths` produces a term AND a derivation that it inhabits
--     `imethsTyFrom`.  Validated at the real table in
--     `Examples/Knot/WkProbe`: 51 of the knot's 53 rows classify, the
--     computed methods are `refl`-equal to `Examples/Knot/WkRows`'
--     hand-written ones, and they type against the real `IConWf`s.
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
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; var; Var
        ; RTy; RTm; Unit; Σ'; El; IMu; Nat
        ; lam; pair; fst; snd; unit; nzero; nsuc; icon; ⌜Id⌝; ⌜Nat⌝
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_
        ; Sub; extS; subTm; subTy; isingle; iext; renTy; extR
        ; ipayTy; ipayTy-sub; ipayTy-cong; ipayTy-ren
        ; _∈ID_; hereID; thereID; ilookupD; εwkTy; εwk-ren )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; wk-single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢pair; ⊢fst; ⊢snd; ⊢unit; ⊢conv
        ; ty-El; ty-Unit; ty-Σ; ty-Π; ty-IMu
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; IDescWf; IDescWfFrom; idwf-nil; idwf-cons
        ; iihTy; imethTy; imethsTyFrom; ⊢lam; ⊢icon
        ; _≅ᵀ_; csymᵀ; credᵀ; ξ-El; ξ-⌜Id⌝ˡ; ξ-IMu
        ; _⟶_; βfst; βsnd; ξ-pairˡ; ξ-pairʳ; ξ-nsuc )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢-cast; Sub⊢; Sub⊢-ext; iext-Sub⊢; isingle-Sub⊢; ren-ty
        ; iihTy-wf; iihTy-ren; iihTy-cong )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf; imethsTyFromNat-wf )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; _∨_; ∨-false; occTm; subTm-occ )

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

-- ★ …and the same under a substitution, which is the form the typing
--   lemma actually consumes: `snd (var a)` becomes `snd (σ a)`, and the
--   `nsuc`s ride along untouched.
isSucs-sub : {Δ Γ : Cx} {a : Var Δ} {d : RTm Δ} (p : IsSucs a d)
             (σ : Sub Δ Γ) → subTm σ d ≡ sucs (depthOf p) (snd (σ a))
isSucs-sub is-snd     σ = refl
isSucs-sub (is-suc p) σ = cong nsuc (isSucs-sub p σ)

-- a reduction under `sucᵏ` — the congruence the `rides` chain needs, and
-- the reason its length does not grow with `k`: ONE step, wrapped.
sucs-red : {Γ : Cx} (k : ℕ) {x y : RTm Γ} → x ⟶ y → sucs k x ⟶ sucs k y
sucs-red zero    r = r
sucs-red (suc k) r = ξ-nsuc (sucs-red k r)

data WkIx {Δ : Cx} (a : Var Δ) : RTm Δ → Set where
  -- the index RIDES the ambient depth: take the IH.
  --
  -- ⚠ THE SORT COMPONENT MUST BE CLOSED TOO, for `pinned`'s reason one
  --   step over: the `rides` case needs `subTm τ (pair s d)` to converge
  --   with `sh (subTm σ (pair s d))`, and an `s` that moved between the
  --   two environments would break that before the depth chain even
  --   starts.  In `KnotD` every `s` is a sort NUMERAL, so this costs
  --   nothing there — which is exactly why it had to be checked rather
  --   than assumed.
  rides  : (s : RTm Δ) → ((x : Var Δ) → occTm x s ≡ false) →
           {d : RTm Δ} → IsSucs a d → WkIx a (pair s d)
  -- the index is CLOSED: take the ORIGINAL FIELD.  ⚠ Its IH exists and
  -- is at the shifted depth; it is simply unusable, and the generic
  -- method never names it.
  --
  -- ⚠⚠ CLOSED, NOT MERELY "DOES NOT MENTION THE AMBIENT" — and the
  --   difference is a SOUNDNESS one, found by tracing the typing lemma's
  --   `pinned` case before writing it.  That case needs the field's index
  --   to be FIXED by the rebuild, and the rebuild changes two things: the
  --   ambient, AND every `rides` field's value (its slot holds the IH
  --   now, not the original field).  An index avoiding only the ambient
  --   could still mention an earlier `rides` slot and move.
  --
  --   ⇒ non-occurrence of the ambient is too weak.  It happens to be
  --     sound on `KnotD` — every pinned index there is a closed pair of
  --     numerals — which is exactly how a hole like this survives into a
  --     library that then claims to be generic.
  pinned : (j : RTm Δ) → ((x : Var Δ) → occTm x j ≡ false) → WkIx a j

-- the κ fields a weakening can pass through unchanged
data WkKa {Δ : Cx} (a : Var Δ) : RTm Δ → Set where
  -- a CLOSED code — its type is untouched by the shift.  ⚠ Same
  -- strengthening as `pinned`, for the same reason.
  ka-clo : (κ : RTm Δ) → ((x : Var Δ) → occTm x κ ≡ false) → WkKa a κ
  -- ★ a TAG FORD.  `fst (sh ⟨i⟩) ⟶ fst ⟨i⟩` by `βfst`, so the witness
  --   the method was handed still serves.  ⚠ The right endpoint must not
  --   mention the ambient — that is what makes this the TAG ford and not
  --   the DEPTH one, which is out of scope (see the header).
  ka-fst : (c b : RTm Δ) →
           ((x : Var Δ) → occTm x c ≡ false) →
           ((x : Var Δ) → occTm x b ≡ false) →
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
-- ⚠ AND WHAT IT COSTS IS COVERAGE, **NOT** A RESTRICTION ON WHAT MAY BE
--   WRITTEN.  Nothing is forbidden: whatever `decDesc` stops at, the
--   caller supplies the leftover, and any description works.  What
--   ordering affects is HOW MUCH gets computed — `decDesc` stops at the
--   FIRST row it cannot classify, so a classifiable row sitting after an
--   unclassifiable one is simply not computed and lands in the caller's
--   tail instead.
--
--   ⇒ that is invisible unless measured, so `wkdLen`/`wkdRest` measure
--     it and `Examples/Knot/WkProbe` PINS both: 51 rows computed, and
--     the leftover is exactly `cVar-vz ◂ cVar-vs ◂ inil`.  For `KnotD`
--     the stop costs nothing, because the generator already appends
--     exceptional rows last (so `∈ID` positions do not move).
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

-- ★ RIDES ⇒ the IH.  ★ PINNED ⇒ the ORIGINAL FIELD.  One picker, so the
--   term level and the typing lemma cannot disagree about which.
ixPick : {Γ Δ : Cx} {a : Var Δ} {j : RTm Δ} → WkIx a j → RTm Γ → RTm Γ → RTm Γ
ixPick (rides _ _ _) q ih = ih
ixPick (pinned _ _)  q ih = q

iwkPay : {Γ Δ : Cx} {a : Var Δ} {C : ICon Δ} →
         WkCon a C → RTm Γ → RTm Γ → RTm Γ
iwkPay wk-ι           q ih = unit
iwkPay (wk-ρ ix w)    q ih = pair (ixPick ix (fst q) (fst ih))
                                 (iwkPay w (snd q) (snd ih))
-- a κ field is passed through either way; what differs is the CONVERSION
-- its type needs, which is in the typing lemma and not here.
-- ⚠ AND BOTH ρ CASES ADVANCE THE IH TUPLE, even `pinned`, which does not
--   USE its IH: `iihTy` has one entry per `iρ` regardless, so not
--   stepping would read the NEXT field's IH at this field's position.
--   ⚠ The `pinned` clause said `ih` until the typing lemma was written —
--   the term level type-checks either way, which is the hazard.
--   A κ field contributes NO entry, so it does not advance.
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
-- ★ CLOSEDNESS, DECIDED STRUCTURALLY — and note it needs no enumeration
--   of `Var Δ`, which is what made the stronger condition look expensive.
--   `occTm x nzero` is `false` for EVERY `x` definitionally, so the leaf
--   case is `λ _ → refl` and the rest is `∨-false`.
--   ⚠ Conservative by construction: an unrecognised shape is `nothing`,
--   so it costs COVERAGE, never soundness.
decClosed : {Δ : Cx} (j : RTm Δ) → Maybe ((x : Var Δ) → occTm x j ≡ false)
-- ⚠ EVERY PATTERN CONSTRUCTOR BELOW MUST BE IMPORTED.  `⌜Nat⌝` was not,
--   and Agda turned it into a pattern VARIABLE — a catch-all matching
--   every term, whose `refl` then failed to type.  It warns
--   (`PatternShadowsConstructor`) but the error it produces points at the
--   body, not the import list.  `agda-unimported-constructor-trap`.
decClosed nzero   = just (λ _ → refl)
decClosed ⌜Nat⌝   = just (λ _ → refl)
decClosed unit    = just (λ _ → refl)
decClosed (nsuc t) with decClosed t
... | just h  = just h
... | nothing = nothing
decClosed (fst t) with decClosed t
... | just h  = just h
... | nothing = nothing
decClosed (snd t) with decClosed t
... | just h  = just h
... | nothing = nothing
decClosed (pair u v) with decClosed u | decClosed v
... | just hu | just hv = just (λ x → ∨-false (hu x) (hv x))
... | just _  | nothing = nothing
... | nothing | _       = nothing
decClosed (⌜Id⌝ c u v) with decClosed c | decClosed u | decClosed v
... | just hc | just hu | just hv =
      just (λ x → ∨-false (hc x) (∨-false (hu x) (hv x)))
... | _ | _ | _ = nothing
decClosed _ = nothing

decPin : {Δ : Cx} (a : Var Δ) (j : RTm Δ) → Maybe (WkIx a j)
decPin a j with decClosed j
... | just o  = just (pinned j o)
... | nothing = nothing

decIx : {Δ : Cx} (a : Var Δ) (j : RTm Δ) → Maybe (WkIx a j)
decIx a (pair s d) with decSucs a d | decClosed s
... | just p  | just cs = just (rides s cs p)
... | just _  | nothing = decPin a (pair s d)
... | nothing | _       = decPin a (pair s d)
decIx a j = decPin a j

decKaFord : {Δ : Cx} (a : Var Δ) (c e : RTm Δ) →
            Maybe (WkKa a (⌜Id⌝ c (fst (var a)) e))
decKaFord a c e with decClosed c | decClosed e
... | just oc | just oe = just (ka-fst c e oc oe)
... | just _  | nothing = nothing
... | nothing | _       = nothing

decKaClo : {Δ : Cx} (a : Var Δ) (κ : RTm Δ) → Maybe (WkKa a κ)
decKaClo a κ with decClosed κ
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

-- ⚠ NOW IT TAKES CLOSEDNESS AND NEEDS NO HYPOTHESIS ON THE ENVIRONMENTS
--   AT ALL.  A closed index is fixed by ANY substitution, so the two may
--   differ wherever they like — which is exactly what the rebuild does to
--   the `rides` slots, and why the weaker version could not have served.
-- ⚠ `j`, `σ` AND `τ` ARE EXPLICIT, and that is forced.  The conclusion
--   is `subTm σ j ≡ subTm τ j` and `subTm` is a DEFINED function, hence
--   not injective — left implicit, all three go unsolved at EVERY call
--   site (`pin-implicits-on-defined-set-types`; this module is another
--   sighting, and the error names `subTm _σ _j = subTm σ j (blocked)`).
pinned-stable : {Δ Γ : Cx} (j : RTm Δ) (σ τ : Sub Δ Γ) →
                ((x : Var Δ) → occTm x j ≡ false) →
                subTm σ j ≡ subTm τ j
pinned-stable j σ τ o = subTm-occ j (λ x oc → tf (trans (sym oc) (o x)))

------------------------------------------------------------------------
-- 7. ✅ WHAT THE TYPING NEEDED, AND WHERE EACH PIECE WENT.
--
--   `pinned`   ⇒ §6.  `pinned-stable`: a CLOSED index is fixed by any
--                substitution, so the ORIGINAL FIELD already has the type
--                the rebuilt row wants.  No conversion.
--
--   `rides`    ⇒ §8's `ridesConv`.  The IH's index and the row's meet at
--                ONE normal form, by a chain whose length does NOT depend
--                on `k` — `sucs-nsuc` is what makes them meet rather than
--                needing a chain per `k`.
--
--   `ka-clo` / `ka-fst` ⇒ §8's `⊢kaComp`.  `ka-clo` is `pinned-stable`
--                again, on the CODE rather than an index; `ka-fst` is one
--                conversion, `ξ-El (ξ-⌜Id⌝ˡ (βfst …))`.
--
-- ⚠ AND TWO THINGS THE FOLD DID NOT NEED, both found by writing it:
--
--   · `IConWf` THREADED THROUGH THE RECURSION.  Every `⊢pair` wants the
--     tail's `⊢ty`, and `Lib/IPay.ipayTy-wf` supplies it only from an
--     `IConWf`.  `Lib/IFold` never needed one because a fold's `⊢op`
--     takes no `⊢ty`.
--
--   · `Split D j E` (§9) — "E is D from position j".  `⊢icon` asks for
--     `k ∈ID D` AND for the payload at `ilookupD D k`; neither follows
--     from the other, and a fold needs neither because it never BUILDS
--     an `icon`.  One relation yields both, derived on the way past —
--     where `Knot/Tags` enumerates the memberships at O(n²).
------------------------------------------------------------------------

-- a three-way cast on a Fording constraint's parts.  ⚠ A named lemma,
-- not `subst` with an underscored motive: written inline the context
-- becomes a meta INSIDE the lambda and never solves (`Knot/Build`'s
-- `tyCast` records the same sighting).
fordCast : {Γ : Ctx} {c c' u u' b b' t : RTm ⌊ Γ ⌋} →
           c ≡ c' → u ≡ u' → b ≡ b' →
           Γ ⊢ t ∷ El (⌜Id⌝ c (fst u) b) → Γ ⊢ t ∷ El (⌜Id⌝ c' (fst u') b')
fordCast refl refl refl d = d

-- the shifting motive, as `iihTy`/`imethTy` want it: two slots, the
-- INDEX one at `var (vs vz)`.
Mot : {Γ : Cx} → IDesc → RTy ε → RTy ((Γ ∙) ∙)
Mot D I = IMu D I (sh (var (vs vz)))

-- ★ one payload step: `⊢pair`'s tail type, with the binder discharged.
--   ⚠ `wk-single` is the only propositional step, and it is the one
--   `Lib/IFold` also pays (`wk-singleTy`).
payStep : {Γ Δ : Cx} (D : IDesc) (I : RTy ε) (σ : Sub Δ Γ) (v : RTm Γ)
          (C : ICon (Δ ∙)) →
          subTy (single v) (ipayTy D I (extS σ) C) ≡ ipayTy D I (iext σ v) C
payStep D I σ v C =
  trans (ipayTy-sub (single v) D I (extS σ) C)
        (ipayTy-cong D I C (λ { vz → refl ; (vs x) → wk-single (σ x) }))

-- ★ a κ field passes through, and WHICH conversion it needs is the only
--   thing its classification decides.
⊢kaComp : {Γ Θ : Ctx} {σ τ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋} {a : Var ⌊ Θ ⌋}
          {κ : RTm ⌊ Θ ⌋} {t : RTm ⌊ Γ ⌋} →
          WkKa a κ → τ a ≡ sh (σ a) →
          Γ ⊢ t ∷ El (subTm σ κ) → Γ ⊢ t ∷ El (subTm τ κ)
⊢kaComp {σ = σ} {τ = τ} (ka-clo κ o) sq d =
  ⊢-cast (cong El (pinned-stable κ σ τ o)) d
-- ⚠ THE TAG FORD.  At the shifted index the constraint reads
--   `fst (sh ⟨i⟩) ≡ s`, and `βfst` takes that to `fst ⟨i⟩ ≡ s` — the
--   witness the method was handed.  One conversion, no transport.
⊢kaComp {σ = σ} {τ = τ} (ka-fst c b oc ob) sq d =
  fordCast (pinned-stable c σ τ oc) (sym sq) (pinned-stable b σ τ ob)
           (⊢conv d (csymᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ˡ (βfst _ _))))))

--
--     sh (pair sσ dσ) ⟶βfst⟶βsnd  pair sσ (nsuc dσ)
--     subTm τ (pair s d) ≡ pair sσ (sucs k (snd (sh (σ a))))
--                        ⟶βsnd    pair sσ (sucs k (nsuc (snd (σ a))))
--                        ≡        pair sσ (nsuc dσ)         (`sucs-nsuc`)
--
--   ⚠ The last line is where `sucs k (nsuc x) ≡ nsuc (sucs k x)` earns
--     its keep: both are `nsucᵏ⁺¹ x`, so the two sides MEET rather than
--     needing a chain per `k`.
ridesConv : {Γ Θ : Ctx} {σ τ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋} {a : Var ⌊ Θ ⌋}
            {s d : RTm ⌊ Θ ⌋} {t : RTm ⌊ Γ ⌋} (D : IDesc) (I : RTy ε) →
            ((x : Var ⌊ Θ ⌋) → occTm x s ≡ false) →
            (p : IsSucs a d) → τ a ≡ sh (σ a) →
            Γ ⊢ t ∷ IMu D I (sh (subTm σ (pair s d))) →
            Γ ⊢ t ∷ IMu D I (subTm τ (pair s d))
ridesConv {σ = σ} {τ = τ} {a = a} {s = s} {d = d} D I cs p sq dt =
  imuCast (cong₂ pair (pinned-stable s σ τ cs) (sym (isSucs-sub p τ)))
   (imuCast (cong (λ z → pair (subTm σ s) (sucs k (snd z))) (sym sq))
    (imuBack (ξ-pairʳ (sucs-red k (βsnd (fst (σ a)) (nsuc (snd (σ a))))))
     (imuCast (cong (pair (subTm σ s)) (sym (sucs-nsuc k (snd (σ a)))))
      (imuCast (cong (λ z → pair (subTm σ s) (nsuc z)) (isSucs-sub p σ))
       (imuFwd (ξ-pairʳ (ξ-nsuc (βsnd (subTm σ s) (subTm σ d))))
        (imuFwd (ξ-pairˡ (βfst (subTm σ s) (subTm σ d))) dt))))))
  where
    k = depthOf p
    imuFwd : {i i' t' : RTm ⌊ _ ⌋} → i ⟶ i' →
             _ ⊢ t' ∷ IMu D I i → _ ⊢ t' ∷ IMu D I i'
    imuFwd r e = ⊢conv e (credᵀ (ξ-IMu r))
    imuBack : {i i' t' : RTm ⌊ _ ⌋} → i ⟶ i' →
              _ ⊢ t' ∷ IMu D I i' → _ ⊢ t' ∷ IMu D I i
    imuBack r e = ⊢conv e (csymᵀ (credᵀ (ξ-IMu r)))
    imuCast : {i i' t' : RTm ⌊ _ ⌋} → i ≡ i' →
              _ ⊢ t' ∷ IMu D I i → _ ⊢ t' ∷ IMu D I i'
    imuCast refl e = e

-- ★ and the ρ component: the IH when the index RIDES, the ORIGINAL FIELD
--   when it is pinned.  ⚠ `ixPick` makes the choice in BOTH places, so
--   the term level and the proof cannot drift apart about which.
⊢ixComp : {Γ Θ : Ctx} {σ τ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋} {a : Var ⌊ Θ ⌋}
          {j : RTm ⌊ Θ ⌋} {u v : RTm ⌊ Γ ⌋} (D : IDesc) (I : RTy ε)
          (ix : WkIx a j) → τ a ≡ sh (σ a) →
          Γ ⊢ u ∷ IMu D I (subTm σ j) →
          Γ ⊢ v ∷ IMu D I (sh (subTm σ j)) →
          Γ ⊢ ixPick ix u v ∷ IMu D I (subTm τ j)
-- ⚠ `{s = s}` PINNED, same reason as `pinned-stable`'s explicit args:
--   `ridesConv`'s conclusion mentions `s` only under `subTm`.
⊢ixComp D I (rides s cs p) sq du dv = ridesConv {s = s} D I cs p sq dv
⊢ixComp {σ = σ} {τ = τ} D I (pinned j o) sq du dv =
  ⊢-cast (cong (IMu D I) (pinned-stable j σ τ o)) du

⊢iwkPay : {Γ Θ : Ctx} (D : IDesc) (I : RTy ε)
          {σ τ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋} {a : Var ⌊ Θ ⌋} {C : ICon ⌊ Θ ⌋}
          (w : WkCon a C) → IConWf D I Θ C → IDescWf I D →
          Sub⊢ Θ Γ σ → Sub⊢ Θ Γ τ → τ a ≡ sh (σ a) →
          (q ih : RTm ⌊ Γ ⌋) →
          Γ ⊢ q ∷ ipayTy D I σ C →
          Γ ⊢ ih ∷ iihTy D I σ C q (Mot D I) →
          Γ ⊢ iwkPay w q ih ∷ ipayTy D I τ C
⊢iwkPay D I wk-ι iwf-ι wD hσ hτ sq q ih dq dih = ⊢unit
⊢iwkPay {Γ = Γ} D I {σ = σ} {τ = τ} (wk-ρ ix w) (iwf-ρ j dj wC)
        wD hσ hτ sq q ih dq dih =
  ⊢pair (ipayTy-wf D I (extS τ) _ wD wC (Sub⊢-ext hτ))
        c₀
        (⊢-cast (sym (payStep D I τ _ _))
          (⊢iwkPay D I w wC wD
                   (iext-Sub⊢ hσ (⊢fst dq)) (iext-Sub⊢ hτ c₀) sq
                   (snd q) (snd ih)
                   (⊢-cast (payStep D I σ (fst q) _) (⊢snd dq))
                   (⊢-cast (wk-singleTy {v = fst ih} _) (⊢snd dih))))
  where
    c₀ = ⊢ixComp D I ix sq (⊢fst dq)
           (⊢-cast (cong (λ z → IMu D I (sh z)) (wk-single (subTm σ j)))
                   (⊢fst dih))
⊢iwkPay {Γ = Γ} D I {σ = σ} {τ = τ} (wk-κ {κ = κ} {C = C'} ka w)
        (iwf-κ .κ _ dc wC) wD hσ hτ sq q ih dq dih =
  ⊢pair (ipayTy-wf D I (extS τ) C' wD wC (Sub⊢-ext hτ))
        c₀
        (⊢-cast (sym (payStep D I τ (fst q) C'))
          (⊢iwkPay D I w wC wD
                   (iext-Sub⊢ hσ (⊢fst dq)) (iext-Sub⊢ hτ c₀) sq
                   (snd q) ih
                   (⊢-cast (payStep D I σ (fst q) C') (⊢snd dq))
                   dih))
  where
    c₀ = ⊢kaComp {σ = σ} {τ = τ} ka sq (⊢fst dq)

------------------------------------------------------------------------
-- 9. THE METHOD, AND THE TUPLE.
--
-- ⚠ ONE HYPOTHESIS THE FOLD DID NOT NEED: `⊢sh`.  `Lib/IFold`'s motive is
--   `Nat`, so its result index is whatever the eliminator hands it.  Here
--   the result sits at `sh ⟨i⟩`, and `⊢icon` must TYPE that index — which
--   is only possible if `I` is a type `sh` preserves.  ⇒ the shift's
--   typing is a parameter, discharged by the caller (`⊢ixP ⊢fst ⊢nsuc-⊢snd`
--   at `I = Σ' Nat Nat`).  A description whose index type is not a pair
--   simply has no `sh`, and says so here rather than deeper in.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★ "E IS D FROM POSITION j", as a relation — and it is what `⊢icon`
--    turned out to need.
--
-- ⚠ `⊢icon` asks for `k ∈ID D` AND for the payload at
--   `ilookupD D k` — i.e. that this row IS the k-th one.  Neither follows
--   from the other, and `Lib/IFold` needed neither, because a fold never
--   BUILDS an `icon`.
--
-- ★ ONE relation yields both, by induction, and its zero case is
--   `spl-nil : Split D 0 D` — so the top-level caller says nothing.
--   `Knot/Tags` pays O(n²) to enumerate the memberships; this derives
--   each one on the way past instead.
data Split : IDesc → ℕ → IDesc → Set where
  spl-nil  : {E : IDesc} → Split E zero E
  spl-cons : {D : IDesc} {j : ℕ} {E : IDesc} {C : ICon (ε ∙)} →
             Split D j E → Split (C ◂ D) (suc j) E

spl-mem : {D : IDesc} {j : ℕ} {C : ICon (ε ∙)} {E : IDesc} →
          Split D j (C ◂ E) → j ∈ID D
spl-mem spl-nil      = hereID
spl-mem (spl-cons s) = thereID (spl-mem s)

spl-look : {D : IDesc} {j : ℕ} {C : ICon (ε ∙)} {E : IDesc} →
           Split D j (C ◂ E) → ilookupD D j ≡ C
spl-look spl-nil      = refl
spl-look (spl-cons s) = spl-look s

spl-step : {D : IDesc} {j : ℕ} {C : ICon (ε ∙)} {E : IDesc} →
           Split D j (C ◂ E) → Split D (suc j) E
spl-step spl-nil      = spl-cons spl-nil
spl-step (spl-cons s) = spl-cons (spl-step s)

-- where the tuple's walk ENDS.  ⚠ Defined by the same recursion the walk
--   takes, so `posOf (wkd-cons w W) j` is `posOf W (suc j)` DEFINITIONALLY
--   — which removes every `j + n` arithmetic lemma from the typing below.
posOf : {E : IDesc} → WkDesc E → ℕ → ℕ
posOf (wkd-stop _)   j = j
posOf (wkd-cons _ W) j = posOf W (suc j)

⊢iwkMethod : {Γ : Ctx} (D : IDesc) (I : RTy ε) (k : ℕ) {C : ICon (ε ∙)}
             (w : WkCon vz C) → IDescWf I D → IConWf D I (◇ ▹ εwkTy I) C →
             k ∈ID D → ilookupD D k ≡ C →
             ({Δ : Ctx} → Δ ⊢ty εwkTy I) →
             ({Δ : Ctx} {i : RTm ⌊ Δ ⌋} → Δ ⊢ i ∷ εwkTy I → Δ ⊢ sh i ∷ εwkTy I) →
             Γ ⊢ iwkMethod k w ∷ imethTy D I k C (Mot D I)
-- ⚠ EVERY CAST IS INLINE, not `where`-bound.  A `where` binding without a
--   type signature leaves the CONTEXT a meta, and these live at three
--   different depths — `Lib/IFold.⊢ifMethod` inlines for the same reason.
⊢iwkMethod {Γ = Γ} D I k {C = C} w wD wC mem look tI ⊢sh =
  ⊢lam tI
    (⊢lam (ipayTy-wf {Γ = Γ ▹ εwkTy I} D I (isingle (var vz)) C
                     wD wC (isingle-Sub⊢ (⊢-cast (εwk-ren vs I) (⊢var here))))
      (⊢lam (iihTy-wf {Γ = (Γ ▹ εwkTy I) ▹ ipayTy D I (isingle (var vz)) C}
                      D I (Mot D I) (isingle (var (vs vz))) C (var vz) wC
                      (isingle-Sub⊢
                        (⊢-cast (trans (cong (renTy vs) (εwk-ren vs I))
                                       (εwk-ren vs I))
                                (⊢var (there here))))
                      (ty-IMu wD
                        (⊢sh (⊢-cast (trans (cong (renTy vs) (εwk-ren vs I))
                                            (εwk-ren vs I))
                                     (⊢var (there here)))))
                      (⊢-cast (trans (ipayTy-ren vs D I (isingle (var vz)) C)
                                     (ipayTy-cong D I C
                                        (λ { vz → refl ; (vs ()) })))
                              (⊢var here)))
        -- ★ the result sits at `sh ⟨i⟩` — which is why `⊢sh` has to be a
        --   hypothesis: `⊢icon` must TYPE that index, and only an index
        --   type the shift preserves admits one.
        (⊢icon wD mem
               (⊢sh (⊢-cast (trans (cong (renTy vs)
                                     (trans (cong (renTy vs) (εwk-ren vs I))
                                            (εwk-ren vs I)))
                                   (εwk-ren vs I))
                            (⊢var (there (there here)))))
               -- ⚠ `⊢icon` wants the payload at `ilookupD D k`, not at
               --   `C`.  They are the same row, and `spl-look` is what
               --   says so; this is where that is cashed.
               (⊢-cast (cong (ipayTy D I (isingle (sh (var (vs (vs vz)))))) (sym look))
                (⊢iwkPay D I w wC wD
                        (isingle-Sub⊢
                          (⊢-cast (trans (cong (renTy vs)
                                           (trans (cong (renTy vs) (εwk-ren vs I))
                                                  (εwk-ren vs I)))
                                         (εwk-ren vs I))
                                  (⊢var (there (there here)))))
                        (isingle-Sub⊢
                          (⊢sh (⊢-cast (trans (cong (renTy vs)
                                                (trans (cong (renTy vs) (εwk-ren vs I))
                                                       (εwk-ren vs I)))
                                              (εwk-ren vs I))
                                       (⊢var (there (there here))))))
                        refl (var (vs vz)) (var vz)
                        -- ⚠ TWO renamings, not one: the payload's domain
                        --   is declared two binders out and is weakened
                        --   past BOTH the payload and the IH binder.
                        (⊢-cast (trans (cong (renTy vs)
                                         (trans (ipayTy-ren vs D I (isingle (var vz)) C)
                                                (ipayTy-cong D I C
                                                   (λ { vz → refl ; (vs ()) }))))
                                       (trans (ipayTy-ren vs D I (isingle (var (vs vz))) C)
                                              (ipayTy-cong D I C
                                                 (λ { vz → refl ; (vs ()) }))))
                                (⊢var (there here)))
                        (⊢-cast (trans (iihTy-ren vs D I (isingle (var (vs vz))) C
                                                  (var vz) (Mot D I))
                                       (iihTy-cong D I C (var (vs vz)) (Mot D I)
                                          (λ { vz → refl ; (vs ()) })))
                                (⊢var here)))))))

-- ★ the method type's own well-formedness, at the SHIFTING motive.
--   ⚠ `Lib/IPay`'s pair is `Nat`-specific (`imethTyNat-wf`), because
--   `Lib/IFold` never needed another motive.  These two are that pair
--   with `Nat` replaced by `Mot D I` — the only changes are the two
--   places the motive's own `⊢ty` is required, and both are `⊢sh`.
imethTyMot-wf : {Γ : Ctx} (D : IDesc) (I : RTy ε) (k : ℕ) (C : ICon (ε ∙)) →
                IDescWf I D → IConWf D I (◇ ▹ εwkTy I) C →
                ({Δ : Ctx} → Δ ⊢ty εwkTy I) →
                ({Δ : Ctx} {i : RTm ⌊ Δ ⌋} → Δ ⊢ i ∷ εwkTy I → Δ ⊢ sh i ∷ εwkTy I) →
                Γ ⊢ty imethTy D I k C (Mot D I)
imethTyMot-wf {Γ = Γ} D I k C wD wC tI ⊢sh =
  ty-Π tI
    (ty-Π (ipayTy-wf {Γ = Γ ▹ εwkTy I} D I (isingle (var vz)) C
                     wD wC (isingle-Sub⊢ (⊢-cast (εwk-ren vs I) (⊢var here))))
      (ty-Π (iihTy-wf {Γ = (Γ ▹ εwkTy I) ▹ ipayTy D I (isingle (var vz)) C}
                      D I (Mot D I) (isingle (var (vs vz))) C (var vz) wC
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs I))
                                                   (εwk-ren vs I))
                                            (⊢var (there here))))
                      (ty-IMu wD
                        (⊢sh (⊢-cast (trans (cong (renTy vs) (εwk-ren vs I))
                                            (εwk-ren vs I))
                                     (⊢var (there here)))))
                      (⊢-cast (trans (ipayTy-ren vs D I (isingle (var vz)) C)
                                     (ipayTy-cong D I C
                                       (λ { vz → refl ; (vs ()) })))
                              (⊢var here)))
            (ty-IMu wD
              (⊢sh (⊢-cast (trans (cong (renTy vs)
                                    (trans (cong (renTy vs) (εwk-ren vs I))
                                           (εwk-ren vs I)))
                                  (εwk-ren vs I))
                           (⊢var (there (there here))))))))

imethsTyFromMot-wf : {Γ : Ctx} (D : IDesc) (I : RTy ε) (j : ℕ) (E : IDesc) →
                     IDescWf I D → IDescWfFrom D I E →
                     ({Δ : Ctx} → Δ ⊢ty εwkTy I) →
                     ({Δ : Ctx} {i : RTm ⌊ Δ ⌋} →
                       Δ ⊢ i ∷ εwkTy I → Δ ⊢ sh i ∷ εwkTy I) →
                     Γ ⊢ty imethsTyFrom D I (Mot D I) j E
imethsTyFromMot-wf D I j inil    wD idwf-nil          tI ⊢sh = ty-Unit
imethsTyFromMot-wf D I j (C ◂ E) wD (idwf-cons wC wE) tI ⊢sh =
  ty-Σ (imethTyMot-wf D I j C wD wC tI ⊢sh)
       (ren-ty (imethsTyFromMot-wf D I (suc j) E wD wE tI ⊢sh) there)

-- ★★★ THE TUPLE.  ⚠ `Split D j E` is what lets each row hand `⊢icon` its
--   MEMBERSHIP and its LOOKUP, derived on the way past rather than
--   enumerated; and `posOf` is defined by the same recursion as the walk,
--   so the tail's position needs no `j + n` arithmetic at all.
⊢iwkMethsFrom : {Γ : Ctx} (D : IDesc) (I : RTy ε) {j : ℕ}
                {E : IDesc} (W : WkDesc E) → Split D j E →
                IDescWf I D → IDescWfFrom D I E →
                ({Δ : Ctx} → Δ ⊢ty εwkTy I) →
                ({Δ : Ctx} {i : RTm ⌊ Δ ⌋} →
                  Δ ⊢ i ∷ εwkTy I → Δ ⊢ sh i ∷ εwkTy I) →
                (tl : RTm ⌊ Γ ⌋) →
                Γ ⊢ tl ∷ imethsTyFrom D I (Mot D I) (posOf W j) (wkdRest W) →
                Γ ⊢ iwkMethsFrom j W tl ∷ imethsTyFrom D I (Mot D I) j E
⊢iwkMethsFrom D I (wkd-stop E) sp wD wE tI ⊢sh tl dtl = dtl
⊢iwkMethsFrom D I {j = j} (wkd-cons w W) sp wD (idwf-cons wC wE) tI ⊢sh tl dtl =
  ⊢pair (ren-ty (imethsTyFromMot-wf D I (suc j) _ wD wE tI ⊢sh) there)
        (⊢iwkMethod D I j w wD wC (spl-mem sp) (spl-look sp) tI ⊢sh)
        (⊢-cast (sym (wk-singleTy {v = iwkMethod j w} _))
                (⊢iwkMethsFrom D I W (spl-step sp) wD wE tI ⊢sh tl dtl))
