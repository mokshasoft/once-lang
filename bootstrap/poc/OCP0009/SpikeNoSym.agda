------------------------------------------------------------------------
-- OCP-0009 · W2 eliminator step — `no-sym` INTERNAL: `sym` is FALSE at `U`,
--                                  not merely underivable.
--
-- W2's done-when includes re-proving `no-sym` internally: "if internalizing
-- the former makes `sym` derivable, the former is wrong."  Before designing
-- the eliminator, fix the STRENGTH of the target: is `sym` something the
-- eliminator must merely FAIL to derive, or something FALSE that no sound
-- eliminator could derive?
--
-- ★ ANSWER: FALSE, by the same two-code universe as `SpikeHomNatU`.
-- `Hom U c d = El c ⇒ El d` (the decided clause, now a kernel computation
-- rule).  On the codes `{⊥, ⊤}`: `Hom U ⌜⊥⌝ ⌜⊤⌝` is INHABITED (the vacuous
-- map) and `Hom U ⌜⊤⌝ ⌜⊥⌝` is EMPTY (a map `⊤ ⇒ ⊥` yields `⊥`).  So a
-- `sym` at `U` would manufacture an inhabitant of an empty type.
--
-- Consequences for the eliminator design, in order of strength:
--
--   1. NO eliminator validated by the intended semantics derives
--      `sym : Hom A x y → Hom A y x` — same strength as `SpikeHomNatU`'s
--      naturality result: the STATEMENT fails, so soundness alone protects
--      `no-sym`.  The syntactic mechanism that enforces it (the variance
--      premise on `tr`'s motive — `NbEPDirDBVar`) is guarding a genuine
--      semantic boundary, not a stylistic one.
--   2. The internal `no-sym` check on the future `tr` is therefore a
--      SOUNDNESS regression test, and `NbEPDirDBVar`'s negative control
--      (`sym`'s motive is not `Pos` — it is `Neg`) is its syntactic half.
--
-- `--safe`, zero postulates, zero holes, zero imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeNoSym where

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

infix 3 ¬_
¬_ : Set → Set
¬ P = P → ⊥

data Code : Set where
  c⊥ c⊤ : Code

El : Code → Set
El c⊥ = ⊥
El c⊤ = ⊤

-- the decided `U` clause: a path between codes is a map between decodings
HomU : Code → Code → Set
HomU c d = El c → El d

-- one direction is inhabited...
arrow : HomU c⊥ c⊤
arrow ()

-- ...and the other is EMPTY.
no-arrow-back : ¬ HomU c⊤ c⊥
no-arrow-back h = h tt

-- ★★ THE RESULT: `sym` at `U` is FALSE.  Any term of type
-- `Hom U c d → Hom U d c` instantiates, at `{⌜⊥⌝, ⌜⊤⌝}`, to a function
-- producing a member of an empty type from `arrow`.
no-sym-U : ¬ (HomU c⊥ c⊤ → HomU c⊤ c⊥)
no-sym-U s = (s arrow) tt
