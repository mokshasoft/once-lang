------------------------------------------------------------------------
-- Normalize.Rebuild: Reconstruction helpers for the normalizer
--
-- This module contains:
-- - rebuild-N: reconstruct TermCode' from position data via In ∘ inj-N
-- - ret-yes: signals match with inl ∘ terminal
-- - ret-no-N: rebuild and return inr for "not matched" case
------------------------------------------------------------------------

module normalizer.Implementation.Normalize.Rebuild where

open import normalizer.Foundations.Types public
open import normalizer.Foundations.CCC public
open import normalizer.Foundations.Encoding public
open import normalizer.Implementation.NoRedex hiding (is-id) public

------------------------------------------------------------------------
-- Rebuild helpers: reconstruct a TermCode' from position data
--
-- rebuild-N takes data at position N and produces TermCode' via In ∘ inj-N
------------------------------------------------------------------------

rebuild-0 : Term TyFuncCode TermCode'
rebuild-0 = In ∘ inl  -- position 0: id

rebuild-1 : Term (TermCode' * TermCode') TermCode'
rebuild-1 = In ∘ inr ∘ inl  -- position 1: comp

rebuild-2 : Term (TyFuncCode * TyFuncCode) TermCode'
rebuild-2 = In ∘ inr ∘ inr ∘ inl  -- position 2: fst

rebuild-3 : Term (TyFuncCode * TyFuncCode) TermCode'
rebuild-3 = In ∘ inr ∘ inr ∘ inr ∘ inl  -- position 3: snd

rebuild-4 : Term (TermCode' * TermCode') TermCode'
rebuild-4 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 4: pair

rebuild-5 : Term (TyFuncCode * TyFuncCode) TermCode'
rebuild-5 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 5: inl

rebuild-6 : Term (TyFuncCode * TyFuncCode) TermCode'
rebuild-6 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 6: inr

rebuild-7 : Term (TermCode' * TermCode') TermCode'
rebuild-7 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 7: case

rebuild-8 : Term TyFuncCode TermCode'
rebuild-8 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 8: terminal

rebuild-9 : Term TyFuncCode TermCode'
rebuild-9 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 9: initial

rebuild-10 : Term TyFuncCode TermCode'
rebuild-10 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 10: In

rebuild-11 : Term TyFuncCode TermCode'
rebuild-11 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 11: Out

rebuild-12 : Term (TyFuncCode * TermCode') TermCode'
rebuild-12 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 12: cata

rebuild-13 : Term ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode')) TermCode'
rebuild-13 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl  -- position 13: curry

rebuild-14 : Term (TyFuncCode * TyFuncCode) TermCode'
rebuild-14 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr  -- position 14: apply (last position, no inl)

------------------------------------------------------------------------
-- "Return yes" helper: signals match with inl ∘ terminal
------------------------------------------------------------------------

ret-yes : ∀ {A} → Term A (Unit + TermCode')
ret-yes = inl ∘ terminal

------------------------------------------------------------------------
-- "Return no" helpers: rebuild and return inr
--
-- These use the rebuild-N helpers composed with inr
------------------------------------------------------------------------

ret-no-0 : Term TyFuncCode (Unit + TermCode')
ret-no-0 = inr ∘ rebuild-0

ret-no-1 : Term (TermCode' * TermCode') (Unit + TermCode')
ret-no-1 = inr ∘ rebuild-1

ret-no-2 : Term (TyFuncCode * TyFuncCode) (Unit + TermCode')
ret-no-2 = inr ∘ rebuild-2

ret-no-3 : Term (TyFuncCode * TyFuncCode) (Unit + TermCode')
ret-no-3 = inr ∘ rebuild-3

ret-no-4 : Term (TermCode' * TermCode') (Unit + TermCode')
ret-no-4 = inr ∘ rebuild-4

ret-no-5 : Term (TyFuncCode * TyFuncCode) (Unit + TermCode')
ret-no-5 = inr ∘ rebuild-5

ret-no-6 : Term (TyFuncCode * TyFuncCode) (Unit + TermCode')
ret-no-6 = inr ∘ rebuild-6

ret-no-7 : Term (TermCode' * TermCode') (Unit + TermCode')
ret-no-7 = inr ∘ rebuild-7

ret-no-8 : Term TyFuncCode (Unit + TermCode')
ret-no-8 = inr ∘ rebuild-8

ret-no-9 : Term TyFuncCode (Unit + TermCode')
ret-no-9 = inr ∘ rebuild-9

ret-no-10 : Term TyFuncCode (Unit + TermCode')
ret-no-10 = inr ∘ rebuild-10

ret-no-11 : Term TyFuncCode (Unit + TermCode')
ret-no-11 = inr ∘ rebuild-11

ret-no-12 : Term (TyFuncCode * TermCode') (Unit + TermCode')
ret-no-12 = inr ∘ rebuild-12

ret-no-13 : Term ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode')) (Unit + TermCode')
ret-no-13 = inr ∘ rebuild-13

ret-no-14 : Term (TyFuncCode * TyFuncCode) (Unit + TermCode')
ret-no-14 = inr ∘ rebuild-14

------------------------------------------------------------------------
-- Specialized "return no" variants for is-pair and is-case dispatchers
--
-- Return type: (TermCode' * TermCode') + TermCode'
------------------------------------------------------------------------

ret-no-pair-0 : Term TyFuncCode ((TermCode' * TermCode') + TermCode')
ret-no-pair-0 = inr ∘ rebuild-0

ret-no-pair-1 : Term (TermCode' * TermCode') ((TermCode' * TermCode') + TermCode')
ret-no-pair-1 = inr ∘ rebuild-1

ret-no-pair-2 : Term (TyFuncCode * TyFuncCode) ((TermCode' * TermCode') + TermCode')
ret-no-pair-2 = inr ∘ rebuild-2

ret-no-pair-3 : Term (TyFuncCode * TyFuncCode) ((TermCode' * TermCode') + TermCode')
ret-no-pair-3 = inr ∘ rebuild-3

ret-no-pair-4 : Term (TermCode' * TermCode') ((TermCode' * TermCode') + TermCode')
ret-no-pair-4 = inr ∘ rebuild-4

ret-no-pair-5 : Term (TyFuncCode * TyFuncCode) ((TermCode' * TermCode') + TermCode')
ret-no-pair-5 = inr ∘ rebuild-5

ret-no-pair-6 : Term (TyFuncCode * TyFuncCode) ((TermCode' * TermCode') + TermCode')
ret-no-pair-6 = inr ∘ rebuild-6

ret-no-pair-7 : Term (TermCode' * TermCode') ((TermCode' * TermCode') + TermCode')
ret-no-pair-7 = inr ∘ rebuild-7

ret-no-pair-8 : Term TyFuncCode ((TermCode' * TermCode') + TermCode')
ret-no-pair-8 = inr ∘ rebuild-8

ret-no-pair-9 : Term TyFuncCode ((TermCode' * TermCode') + TermCode')
ret-no-pair-9 = inr ∘ rebuild-9

ret-no-pair-10 : Term TyFuncCode ((TermCode' * TermCode') + TermCode')
ret-no-pair-10 = inr ∘ rebuild-10

ret-no-pair-11 : Term TyFuncCode ((TermCode' * TermCode') + TermCode')
ret-no-pair-11 = inr ∘ rebuild-11

ret-no-pair-12 : Term (TyFuncCode * TermCode') ((TermCode' * TermCode') + TermCode')
ret-no-pair-12 = inr ∘ rebuild-12

ret-no-pair-13 : Term ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode')) ((TermCode' * TermCode') + TermCode')
ret-no-pair-13 = inr ∘ rebuild-13

ret-no-pair-14 : Term (TyFuncCode * TyFuncCode) ((TermCode' * TermCode') + TermCode')
ret-no-pair-14 = inr ∘ rebuild-14

------------------------------------------------------------------------
-- Specialized "return no" variants for is-cata dispatcher
--
-- Return type: (TyFuncCode * TermCode') + TermCode'
------------------------------------------------------------------------

ret-no-cata-0 : Term TyFuncCode ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-0 = inr ∘ rebuild-0

ret-no-cata-1 : Term (TermCode' * TermCode') ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-1 = inr ∘ rebuild-1

ret-no-cata-2 : Term (TyFuncCode * TyFuncCode) ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-2 = inr ∘ rebuild-2

ret-no-cata-3 : Term (TyFuncCode * TyFuncCode) ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-3 = inr ∘ rebuild-3

ret-no-cata-4 : Term (TermCode' * TermCode') ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-4 = inr ∘ rebuild-4

ret-no-cata-5 : Term (TyFuncCode * TyFuncCode) ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-5 = inr ∘ rebuild-5

ret-no-cata-6 : Term (TyFuncCode * TyFuncCode) ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-6 = inr ∘ rebuild-6

ret-no-cata-7 : Term (TermCode' * TermCode') ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-7 = inr ∘ rebuild-7

ret-no-cata-8 : Term TyFuncCode ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-8 = inr ∘ rebuild-8

ret-no-cata-9 : Term TyFuncCode ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-9 = inr ∘ rebuild-9

ret-no-cata-10 : Term TyFuncCode ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-10 = inr ∘ rebuild-10

ret-no-cata-11 : Term TyFuncCode ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-11 = inr ∘ rebuild-11

-- Skip ret-no-cata-12 since position 12 is cata itself (the dispatcher's target position)

ret-no-cata-13 : Term ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode')) ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-13 = inr ∘ rebuild-13

ret-no-cata-14 : Term (TyFuncCode * TyFuncCode) ((TyFuncCode * TermCode') + TermCode')
ret-no-cata-14 = inr ∘ rebuild-14

------------------------------------------------------------------------
-- Encoded id term (for eta reductions)
------------------------------------------------------------------------

encoded-id : Term Unit TermCode'
encoded-id = In ∘ inl ∘ ⌜ Unit ⌝Ty
