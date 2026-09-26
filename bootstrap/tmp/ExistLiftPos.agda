------------------------------------------------------------------------
-- SPIKE · POSITIVITY of the EXISTENTIAL `ILift`.
--
-- Question: `iki-κ`'s σ-FAMILY exists only so `ILift`'s κ node has a
-- predicate.  If instead `ILift` stores the interpretation EXISTENTIALLY
-- beside the membership —
--
--     ILift (iκ κ C) P σ t = SN t × Σ (⊩₀ (El (subTm σ κ)))
--                                     (λ r → r ⊩₀∋ fst t) × …
--
-- — then `IKPred`/`IDPred`/`ikpredsOf`/`ipredsOf`/`ilookupP` and the
-- whole `ICodeWf` apparatus become unnecessary, and `Vec A n` needs no
-- new row at all.
--
-- ⚠ BUT it creates a NEW CYCLE: `IMuMem`'s constructor now mentions
--   `_⊩₀∋_`, which is defined by recursion on `⊩₀`, whose `IMu` clause
--   returns `IMuMem`.  Datatype → defined function → back to the
--   datatype.  Agda's positivity checker must do POLARITY analysis of
--   `_⊩₀∋_` to accept it.  THAT is what this file tests, in miniature,
--   with the real cycle's shape and nothing else.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
-- ⚠ the stand-ins are MODULE PARAMETERS, not postulates: `--safe` bans
--   postulates, and parameters are strictly more conservative for a
--   positivity test — the checker cannot unfold them either way.
module tmp.ExistLiftPos
  (RTm RTy : Set)
  (SN : RTm → Set)
  (IMu Unit : RTy)
  (ap fst' snd' : RTm → RTm)
  where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Sigma using ( Σ; _,_ )

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

data ICon : Set where
  iι : ICon
  iρ : ICon → ICon
  iκ : RTy → ICon → ICon          -- the field's TYPE, in place of `El κ`

------------------------------------------------------------------------
-- THE MUTUAL BLOCK — same shape as `Metatheory/LogicalRelation`.
------------------------------------------------------------------------

data ⊩₀_ : RTy → Set
_⊩₀∋_ : {A : RTy} → ⊩₀ A → RTm → Set
data IMuMem : RTm → Set
ILift : ICon → RTm → Set

data ⊩₀_ where
  ⊩₀Unit : ⊩₀ Unit
  -- ★ the clause that closes the cycle: membership at `IMu` IS `IMuMem`.
  --   ⚠ and NOTE WHAT IS GONE — no `IDInterp` argument.
  ⊩₀IMu  : ⊩₀ IMu

⊩₀Unit ⊩₀∋ t = SN t
⊩₀IMu  ⊩₀∋ t = SN t × IMuMem t

-- ⚠⚠ `C` IS QUANTIFIED, so `ILift C p` is STUCK — exactly as the real
--   `imm-icon` is stuck at `ILift (ilookupD D k) …` for a VARIABLE `D`.
--   With a CONCRETE `iι` here the checker unfolds to `SN p` and never
--   looks at the `iκ` case at all, which would make this file pass
--   while testing nothing.
data IMuMem where
  imm-ne   : {t : RTm} → SN t → IMuMem t
  imm-icon : (C : ICon) {p : RTm} → ILift C p → IMuMem (ap p)

-- ★★★ THE EXISTENTIAL.  `ILift` no longer takes an `IKPred`, and no
--   longer takes a `P` — the recursive slot is `IMuMem` directly.
ILift iι       t = SN t
ILift (iρ C)   t = SN t × ((SN (fst' t) × IMuMem (fst' t)) × ILift C (snd' t))
ILift (iκ A C) t = SN t × (Σ (⊩₀ A) (λ r → r ⊩₀∋ fst' t) × ILift C (snd' t))
