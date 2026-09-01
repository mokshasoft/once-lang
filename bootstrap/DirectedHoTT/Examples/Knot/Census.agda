------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE CENSUS, AS A **TYPE-CHECKED** INVARIANT.
--
-- ⚠⚠ THIS EXISTS BECAUSE `JUDGEMENT-ATTEMPTS` §13 SAID SOMETHING TOO
--   STRONG.  It observed that four of nine real defects were invisible to
--   Agda and concluded a type checker "cannot see" the correspondence
--   between `Spec/Typing.agda` and the emitted rows.  ★ THE SECOND HALF
--   OF THAT IS FALSE: Agda cannot see a correspondence NOBODY WROTE
--   DOWN.  Written down, it checks it — and the two halves of this
--   module are the proof.
--
--   ① HOW MANY RULES THE SOURCE HAS is readable at type-check time, by
--     REFLECTION, under `--safe`.  `getDefinition` on a `data-type`
--     yields its constructor list; its length is a `Nat` the type
--     checker computes.  Nothing here is a script.
--
--   ② HOW MANY ROWS THE ENCODING HAS is ordinary Agda: `IDesc` is a
--     first-order list, so `ilen` is four lines and `refl` decides it.
--
--   ⇒ and then the two are RELATED by an equation, which is the thing
--     the Python ratchet could only assert.
--
-- ★★★ WHAT THIS CATCHES THAT THE RATCHET DID NOT.  On 2026-09-01 the row
--   count went 51 → 49 → 51 while fixing depth bugs.  `_FLOOR` was 34, so
--   it saw nothing: A FLOOR ONLY CATCHES A FALL BELOW ITSELF.  Here the
--   number is EXACT and any drift is a type error, in the sweep, for
--   free.
--
-- ⚠ WHAT IT DOES **NOT** CATCH, and this must be said plainly: a row that
--   is well-formed but encodes the WRONG RULE — `dwf-cons` emitting
--   `DescWf C` for `DescWf (C ◃ E)` — is still invisible here.  Counting
--   is the CHEAP SHADOW of the correspondence, not the correspondence.
--   The tier that closes that is an adequacy map (`enDeriv`), §13.4.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Census where
open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat renaming ( Nat to ℕ )
open import Agda.Builtin.Equality
open import DirectedHoTT.Spec.Syntax using ( IDesc; inil; _◂_ )
open import DirectedHoTT.Spec.Typing
  using ( _⊢_∷_; _⊢ty_; DConWf; DescWf; IConWf; ICodeWf; IDescWfFrom
        ; _⟶_; _⟶ᵀ_; _≅ᵀ_ )
open import DirectedHoTT.Spec.Variance using ( NoNatC )
open import DirectedHoTT.Examples.Knot.JudgeRows  using ( JudgeD )
open import DirectedHoTT.Examples.Knot.RedRows    using ( RedD )
open import DirectedHoTT.Examples.Knot.TyRedRows  using ( TyRedD )
open import DirectedHoTT.Examples.Knot.ConvRows   using ( ConvD )
open import DirectedHoTT.Examples.Knot.NoNatCRows using ( NoNatCD )

------------------------------------------------------------------------
-- ① the SOURCE side — by reflection, at type-check time
------------------------------------------------------------------------

len : {A : Set} → List A → ℕ
len []       = 0
len (_ ∷ xs) = suc (len xs)

conList : Name → TC (List Name)
conList n = bindTC (getDefinition n) λ where
  (data-type _ cs) → returnTC cs
  _                → returnTC []

macro
  -- ★ the number of constructors of a datatype, as a literal
  rules : Name → Term → TC ⊤
  rules n hole = bindTC (conList n) λ cs → unify hole (lit (nat (len cs)))

------------------------------------------------------------------------
-- ② the ENCODING side — ordinary Agda, `IDesc` being a first-order list
------------------------------------------------------------------------

ilen : IDesc → ℕ
ilen inil      = 0
ilen (_ ◂ D)   = suc (ilen D)

------------------------------------------------------------------------
-- ③ …AND THE TWO, RELATED.  ⚠ Each `skipped` is a rule NAMED in its
--   module's `NOT EMITTED` header; the equation is what stops that list
--   from growing silently.
------------------------------------------------------------------------

-- the merged block: seven judgements, ONE description
srcJudge : ℕ
srcJudge = rules _⊢ty_ + rules _⊢_∷_ + rules DConWf + rules DescWf
         + rules IConWf + rules ICodeWf + rules IDescWfFrom

_ : srcJudge ≡ 56
_ = refl

_ : ilen JudgeD ≡ 51
_ = refl

-- ⊢tr · ⊢con · ⊢elim · ⊢icon · ⊢ielim
_ : ilen JudgeD + 5 ≡ srcJudge
_ = refl

-- the four self-contained families
_ : rules _⟶_ ≡ 73
_ = refl

-- ι-elim · ι-ielim
_ : ilen RedD + 2 ≡ rules _⟶_
_ = refl

_ : ilen TyRedD ≡ rules _⟶ᵀ_
_ = refl

_ : ilen ConvD ≡ rules _≅ᵀ_
_ = refl

_ : ilen NoNatCD ≡ rules NoNatC
_ = refl
