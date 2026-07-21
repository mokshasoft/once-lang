------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 42 (M1) — SOUNDNESS OF dHoTT (project): the meta
--            DIRECTED universe, directed identity `Hom`, directed J, `no-sym`.
--
-- dHoTT's novelty is that the identity type is DIRECTED: `Hom a b := a ⟶* b`,
-- with a COVARIANT eliminator and NO symmetry.  So a model of dHoTT is NOT the
-- standard set model (where `Id a b = a ≡ b` is symmetric) — a type must carry a
-- DIRECTED hom-structure, `Hom` is its reflexive-transitive closure, directed J
-- is covariant transport, and `no-sym` must genuinely hold.
--
-- This milestone: the meta DIRECTED Tarski universe by induction-recursion.  A
-- code decodes to a SET (`Êl`) together with a BASE one-step directed relation
-- (`Stp`); the directed identity `Hom` is the reflexive-transitive closure of
-- `Stp`, so:
--   * `transp` — DIRECTED (covariant) transport / the directed J: it consumes a
--     MONOTONICITY (functorial-action) witness, i.e. you may transport only
--     COVARIANTLY along the reduction — exactly dHoTT's `transport⟶`;
--   * ★ `no-sym` — the identity is genuinely directed: an arrow `t0 ⟶ t1` exists
--     but `t1 ⟶ t0` does NOT (`Hom ι̂ t1 t0 → Empty`).
--
-- Codes: `⊥̂` (empty), `ι̂` (a base type with an asymmetric arrow — the `no-sym`
-- witness), `π̂` (dependent functions, DISCRETE directed structure for now — the
-- covariant/natural-transformation function hom is an M2 refinement).
-- `--safe`, zero axioms (IR is safe).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDHoTT where

open import Agda.Builtin.Sigma using ( Σ; _,_; fst; snd )

data Empty : Set where

record ⊤ : Set where
  constructor tt

-- a two-object base with a single, asymmetric arrow.
data Two : Set where
  t0 t1 : Two

data StpTwo : Two → Two → Set where
  arr : StpTwo t0 t1

------------------------------------------------------------------------
-- The meta DIRECTED Tarski universe (induction-recursion): a code decodes to a
-- SET `Êl` plus a BASE one-step directed relation `Stp`.
------------------------------------------------------------------------

data Û : Set
Êl  : Û → Set
Stp : (a : Û) → Êl a → Êl a → Set

data Û where
  ⊥̂ : Û
  ι̂ : Û
  π̂ : (a : Û) → (Êl a → Û) → Û

Êl ⊥̂       = Empty
Êl ι̂       = Two
Êl (π̂ a b) = (x : Êl a) → Êl (b x)

Stp ⊥̂       _ _ = Empty
Stp ι̂       x y = StpTwo x y
Stp (π̂ a b) _ _ = Empty          -- functions discrete (M2: covariant hom)

------------------------------------------------------------------------
-- The DIRECTED IDENTITY: `Hom` = reflexive-transitive closure of `Stp`.
------------------------------------------------------------------------

infixr 5 _◃_
data Hom (a : Û) : Êl a → Êl a → Set where
  rfl : ∀ {x}     → Hom a x x
  _◃_ : ∀ {x y z} → Stp a x y → Hom a y z → Hom a x z

-- `Hom` is reflexive-TRANSITIVE (composition of directed paths).
_⊙_ : ∀ {a} {x y z : Êl a} → Hom a x y → Hom a y z → Hom a x z
rfl     ⊙ q = q
(s ◃ p) ⊙ q = s ◃ (p ⊙ q)

------------------------------------------------------------------------
-- DIRECTED transport / directed J — COVARIANT only (needs the functorial
-- action).  This is dHoTT's `transport⟶`: no symmetry is available.
------------------------------------------------------------------------

transp : (a : Û) (P : Êl a → Set) → (∀ {x y} → Stp a x y → P x → P y) →
         ∀ {x y} → Hom a x y → P x → P y
transp a P mono rfl     px = px
transp a P mono (s ◃ h) px = transp a P mono h (mono s px)

------------------------------------------------------------------------
-- ★ NO-SYM — the identity is genuinely DIRECTED.
------------------------------------------------------------------------

hom01 : Hom ι̂ t0 t1
hom01 = arr ◃ rfl

no-sym : Hom ι̂ t1 t0 → Empty
no-sym (() ◃ _)

-- and the base is not discrete: there IS a nontrivial directed path.
non-discrete : Hom ι̂ t0 t1
non-discrete = hom01
