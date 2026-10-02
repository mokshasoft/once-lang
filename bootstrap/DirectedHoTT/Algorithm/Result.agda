-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — a RESULT with a reason: `ok`, or `err` saying why.
--                      (PLAN-BIDI S6 — what the elaborator returns)
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.Result where
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import Agda.Builtin.String using ( String; primStringAppend )

data R (A : Set) : Set where
  ok  : A → R A
  err : String → R A

infixl 1 _>>=_
_>>=_ : {A B : Set} → R A → (A → R B) → R B
ok a  >>= f = f a
err w >>= f = err w

-- try the first, else the second (whose reason is reported)
infixl 3 _<|>_
_<|>_ : {A : Set} → R A → R A → R A
ok a  <|> _ = ok a
err _ <|> m = m

-- a view that must succeed
need : {A : Set} → String → Maybe A → R A
need w (just a) = ok a
need w nothing  = err w

opt : {A : Set} → R A → Maybe A
opt (ok a)  = just a
opt (err _) = nothing

-- prefix a reason with where it arose
at : {A : Set} → String → R A → R A
at w (ok a)   = ok a
at w (err w') = err (primStringAppend w (primStringAppend " › " w'))

-- the reason, or "ok" — for reading a failure off a type error
why : {A : Set} → R A → String
why (ok _)  = "ok"
why (err w) = w
