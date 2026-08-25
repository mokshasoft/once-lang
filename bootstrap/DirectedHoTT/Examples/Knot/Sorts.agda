------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — THE KNOT'S INDEX: (SORT, DEPTH).
--
-- PLAN-INDEXED §5 item 7, step 2.  The whole `RTm`/`RTy` mutual knot —
-- 7 families, 53 constructors — is ONE indexed description over
-- `I = Σ' Nat Nat`: the first component is a SORT TAG, the second a
-- CONTEXT DEPTH.
--
-- ★ THIS FILE IS HAND-WRITTEN; `Desc`/`Wf` are GENERATED.  What lives
--   here is exactly what a generator should not own: the sort numbering,
--   the two `El ⌜Nat⌝` ↔ `Nat` conversions every Ford eats, and the
--   pair-introduction lemma every recursive field's index needs.
--
-- ⚠ THE SORT ORDER IS LOAD-BEARING and must not be permuted casually:
--   `Desc.KnotD` lists the constructors in it, and `⊢icon`'s `k ∈ID D`
--   premise counts positions in that list.  The order below groups by
--   family so the two coincide.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Sorts where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; RTm; Σ'; Nat; El; U
        ; var; pair; fst; snd; nzero; nsuc; ⌜Nat⌝ )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢conv; ⊢nzero; ⊢nsuc; ⊢pair; ⊢fst; ⊢snd; ⊢var; here
        ; _⊢ty_; ty-Nat; ty-Σ
        ; _≅ᵀ_; csymᵀ; credᵀ; El-⌜Nat⌝ )

------------------------------------------------------------------------
-- 1. THE INDEX TYPE.  ⚠ `Σ' Nat Nat`, a raw TYPE and not `El` of a code
--    — there is no `⌜Σ⌝` on this path, and `ty-IMu`/`⌜IMu⌝` never ask
--    for one (PLAN-INDEXED §14).
------------------------------------------------------------------------

IPair : RTy ε
IPair = Σ' Nat Nat

⊢IPair : {Γ : Ctx} → Γ ⊢ty Σ' Nat Nat
⊢IPair = ty-Σ ty-Nat ty-Nat

------------------------------------------------------------------------
-- 2. THE SEVEN SORT TAGS.
--
--     0 RTy   1 RTm   2 Desc   3 DCon   4 IDesc   5 ICon   6 Var
--
-- ⚠ KEPT AS `Def`s, not inlined numerals.  Every one of the 53 Fording
--   constraints mentions its tag, and a folded `sVar` is one symbol
--   where `nsuc (nsuc (nsuc (nsuc (nsuc (nsuc nzero)))))` is thirteen —
--   `agda-cost-is-elaborated-term-size` applied to the one thing this
--   encoding has 53 copies of.
------------------------------------------------------------------------

sTy sTm sDesc sDCon sIDesc sICon sVar : {Γ : Cx} → RTm Γ
sTy    = nzero
sTm    = nsuc sTy
sDesc  = nsuc sTm
sDCon  = nsuc sDesc
sIDesc = nsuc sDCon
sICon  = nsuc sIDesc
sVar   = nsuc sICon

⊢sTy : {Γ : Ctx} → Γ ⊢ sTy ∷ Nat
⊢sTy = ⊢nzero

⊢sTm : {Γ : Ctx} → Γ ⊢ sTm ∷ Nat
⊢sTm = ⊢nsuc ⊢sTy

⊢sDesc : {Γ : Ctx} → Γ ⊢ sDesc ∷ Nat
⊢sDesc = ⊢nsuc ⊢sTm

⊢sDCon : {Γ : Ctx} → Γ ⊢ sDCon ∷ Nat
⊢sDCon = ⊢nsuc ⊢sDesc

⊢sIDesc : {Γ : Ctx} → Γ ⊢ sIDesc ∷ Nat
⊢sIDesc = ⊢nsuc ⊢sDCon

⊢sICon : {Γ : Ctx} → Γ ⊢ sICon ∷ Nat
⊢sICon = ⊢nsuc ⊢sIDesc

⊢sVar : {Γ : Ctx} → Γ ⊢ sVar ∷ Nat
⊢sVar = ⊢nsuc ⊢sICon

------------------------------------------------------------------------
-- 3. THE TWO CONVERSIONS AND THE PAIR LEMMA.
--
-- `⌜Id⌝`'s endpoints are typed at `El ⌜Nat⌝` (it is CODE-indexed) while
-- `⊢fst`/`⊢snd` and `⊢pair` speak of `Nat`.  Everything the generator
-- emits crosses that boundary in one of these three ways and no other.
------------------------------------------------------------------------

toI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
toI d = ⊢conv d (csymᵀ (credᵀ El-⌜Nat⌝))

fromI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Nat
fromI d = ⊢conv d (credᵀ El-⌜Nat⌝)

⊢ixP : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
       Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ pair a b ∷ Σ' Nat Nat
⊢ixP da db = ⊢pair ty-Nat da db

-- the ambient index's two components, at the telescope's innermost slot
⊢fstIx : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ fst i ∷ Nat
⊢fstIx = ⊢fst

⊢sndIx : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ snd i ∷ Nat
⊢sndIx = ⊢snd
