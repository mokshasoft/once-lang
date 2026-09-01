------------------------------------------------------------------------
-- DirectedHoTT · ★★★ FORMER COVERAGE, AS A **TYPE-CHECKED** OBLIGATION.
--
-- ⚠⚠ THE BUG THIS EXISTS FOR IS THE ONE `FUTURE.md` NAMES:
--   *"a DATATYPE DECLARATION carries no totality obligation"*.  Agda's
--   coverage checker checks FUNCTIONS, not DATATYPES.  Adding a former
--   to `RTm` and forgetting its row in the SN layer is a perfectly
--   well-formed omission: the module compiles, the sweep is green, and
--   nothing is obliged to notice until `fund` is finally asked to build
--   one — several modules and many minutes downstream, as a unification
--   error rather than "you forgot a case".
--
--   It has happened TWICE: `ordtr` (2026-08-05 → 06) and
--   `icon`/`ielim`/`⌜IMu⌝` (2026-08-22).  Both times the only thing that
--   caught it was an out-of-band shell script grepping the source.
--
-- ★★★ IT DOES NOT HAVE TO BE OUT OF BAND.  `Agda.Builtin.Reflection`
--   works under `--safe` (measured 2026-09-01), and `getDefinition` on a
--   `data-type` yields its CONSTRUCTOR LIST at type-check time.  So
--   "every `RTm` former is homed in ≥1 of `SNe`/`SN`/`SNRed`" is an
--   ordinary proposition, checked in the sweep, that NAMES the orphans
--   when it fails.
--
-- ⚠ WHAT THIS IS NOT.  It checks that a former is MENTIONED, not that
--   the row it appears in says the right thing — the same gap
--   `Knot/Census` has against `enDeriv`.  Mentioning is the cheap shadow
--   of coverage, and it is exactly the shadow the shell script cast.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.FormerCensus where
open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import DirectedHoTT.Spec.Syntax using ( RTm )
open import DirectedHoTT.Metatheory.LogicalRelation
  using ( SNe; SN; SNRed; Ne; spine?; stablecd? )

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- ⚠ no `if_then_else_` in `Agda.Builtin.Bool`; match instead.
_∈?_ : Name → List Name → Bool
n ∈? []       = false
n ∈? (m ∷ ms) with primQNameEquality n m
... | true  = true
... | false = n ∈? ms

------------------------------------------------------------------------
-- ★ every `Name` a term mentions.  ⚠ Constructor types are `pi`/`def`/
--   `con` spines; `pat-lam` cannot occur in one, so its bodies are not
--   walked and nothing is lost.
------------------------------------------------------------------------

mutual
  names  : Term → List Name
  names (var _ as)               = namesA as
  names (con c as)               = c ∷ namesA as
  names (def f as)               = f ∷ namesA as
  names (lam _ (abs _ t))        = names t
  names (pat-lam _ as)           = namesA as
  names (pi (arg _ a) (abs _ b)) = names a ++ names b
  names (agda-sort _)            = []
  names (lit _)                  = []
  names (meta _ as)              = namesA as
  names unknown                  = []

  namesA : List (Arg Term) → List Name
  namesA []              = []
  namesA (arg _ t ∷ as)  = names t ++ namesA as

consOf : Name → TC (List Name)
consOf n = bindTC (getDefinition n) λ where
  (data-type _ cs) → returnTC cs
  _                → returnTC []

-- every name mentioned in any constructor type of any listed datatype
mentionedIn : List Name → TC (List Name)
mentionedIn []       = returnTC []
mentionedIn (d ∷ ds) =
  bindTC (consOf d)        λ cs →
  bindTC (fromCons cs)     λ here →
  bindTC (mentionedIn ds)  λ rest →
  returnTC (here ++ rest)
  where
    fromCons : List Name → TC (List Name)
    fromCons []       = returnTC []
    fromCons (c ∷ cs) = bindTC (getType c)     λ t →
                        bindTC (fromCons cs)   λ r →
                        returnTC (names t ++ r)

orphans : List Name → List Name → List Name
orphans []       _  = []
orphans (c ∷ cs) ms with c ∈? ms
... | true  = orphans cs ms
... | false = c ∷ orphans cs ms

errs : List Name → List ErrorPart
errs []       = []
errs (n ∷ ns) = nameErr n ∷ errs ns

------------------------------------------------------------------------
-- ★★★ GATE 1 — every `RTm` former is homed in the SN layer.
------------------------------------------------------------------------

macro
  snCoversRTm : Term → TC ⊤
  snCoversRTm hole =
    bindTC (consOf (quote RTm)) λ cs →
    bindTC (mentionedIn (quote SNe ∷ quote SN ∷ quote SNRed ∷ quote Ne ∷ [])) λ ms →
    check (orphans cs ms)
    where
      check : List Name → TC ⊤
      check []       = unify hole (con (quote tt) [])
      check os@(_ ∷ _) =
        typeError (strErr "RTm former(s) with NO row in SNe/SN/SNRed/Ne:"
                     ∷ errs os)

_ : ⊤
_ = snCoversRTm

------------------------------------------------------------------------
-- ★★★ GATE 3, AS AN OBLIGATION — PINNING A CATCH-ALL'S **EXTENT**.
--
-- ⚠⚠ THE BUG (`25602107`): `spine?` and `stablecd?` had explicit
--   `con`/`elim` rows and inherited `_ = false` for `icon`/`ielim`.
--   THREE silently wrong answers; `--safe`, zero warnings, Agda's
--   coverage checker perfectly happy — a catch-all IS total.
--
-- ★ THE FIX IS NOT "BAN CATCH-ALLS".  Most are right: `spine?` genuinely
--   answers `false` for most formers.  The fix is to make the catch-all's
--   EXTENT a number that cannot move quietly — add a former to `RTm` and
--   it silently joins the catch-all, the count changes, and THIS FAILS.
--   Bumping it is then a deliberate act taken with the list in view,
--   which is precisely the decision that was skipped.
------------------------------------------------------------------------

patHeads : Pattern → List Name
patNames : List (Arg Pattern) → List Name

patHeads (con c ps) = c ∷ patNames ps
patHeads _          = []

patNames []             = []
patNames (arg _ p ∷ ps) = patHeads p ++ patNames ps

clauseNames : List Clause → List Name
clauseNames []                        = []
clauseNames (clause _ ps _ ∷ cs)      = patNames ps ++ clauseNames cs
clauseNames (absurd-clause _ ps ∷ cs) = patNames ps ++ clauseNames cs

matchedBy : Name → TC (List Name)
matchedBy f = bindTC (getDefinition f) λ where
  (function cs) → returnTC (clauseNames cs)
  _             → returnTC []

count : List Name → Nat
count []       = 0
count (_ ∷ ns) = suc (count ns)

macro
  -- how many constructors of `T` reach `f` ONLY through its catch-all
  catchAllN : Name → Name → Term → TC ⊤
  catchAllN f T hole =
    bindTC (consOf T)    λ cs →
    bindTC (matchedBy f) λ ms →
    unify hole (lit (nat (count (orphans cs ms))))

  -- …the same, but NAMING them, for when the number moves
  catchAllList : Name → Name → Term → TC ⊤
  catchAllList f T _ =
    bindTC (consOf T)    λ cs →
    bindTC (matchedBy f) λ ms →
    typeError (strErr "reached only by the catch-all:" ∷ errs (orphans cs ms))

-- ⚠ THESE NUMBERS ARE A DECISION, NOT AN OBSERVATION.  Each asserts
--   "every other `RTm` former was considered, and `false` is right".
--   ⇒ if one moves, do NOT just bump it — swap in `catchAllList`, read
--     the names, decide, and put the number back.
_ : catchAllN spine? RTm ≡ 12
_ = refl

_ : catchAllN stablecd? RTm ≡ 7
_ = refl
