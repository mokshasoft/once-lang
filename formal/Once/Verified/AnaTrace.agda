-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.AnaTrace — the PRODUCTIVE simulation for `ana` (Plan 0.46).
--
-- The corecursive counterpart of the finite bridge: the denotational
-- `evalᴰ`-trace of an anamorphism (`ana-events`, depth-bounded unfold) agrees,
-- EVENT-PREFIX-wise, with the operational `SS.eval` unfold (`anaUnfold`) at SOME
-- fuel. Genuine `∀k → ∃s`: the trace GROWS with the observation depth `k`,
-- matched by a larger operational fuel. Discharges the `ana` case of
-- `elaborate-trace-correct`.
--
-- WHY TAKE-BASED, NOT FULL EQUALITY (lesson, 2026-06-15): an earlier draft tried
-- to decompose the step via a `functor-walk` claiming `mapAnaF`'s trace equals
-- `events-F` FULLY (∀ fuel). That is FALSE: at an `Id` position `mapAnaF s` is
-- `anaUnfold s`, whose trace GROWS with the fuel `s`, while `events-F` is the
-- fixed depth-`k` trace. The operational fuel ≠ the denotational depth, so the
-- two agree only on the OBSERVED PREFIX (`take`). Hence the relation is
-- `∃ s, take k … ≡ take k …`, and the inductive step is a genuine prefix
-- simulation (the hard core, kept as ONE honest postulate below — NOT a
-- full-equality functor-walk).
--
-- It also needs the coalgebra+seed CORRESPONDENCE (`CoalgSeedCorr`): for
-- UNRELATED `coalgD`/`coalgV` or `a`/`av` the unfolds are unrelated, so the
-- statement is false without it. `CoalgSeedCorr` is abstract here; its concrete
-- definition is the bridge's value-sim at the coalgebra `A → F(A)` together with
-- the seed value-sim (to be supplied when wiring into `elaborate-trace-correct`).
------------------------------------------------------------------------

module Once.Verified.AnaTrace where

open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; _⊔_)
open import Data.List using (List; []; _∷_; _++_; take; length)
open import Data.Nat using (z≤n; s≤s)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Data.Nat.Properties using (0∸n≡0)
open import Data.List.Properties using (∷-injective; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)

-- `take n (p ++ x) = take n p ++ take (n ∸ |p|) x` (no stdlib lemma). The list
-- glue for the prefix simulation: the coalgebra-trace prefix `p` is consumed,
-- leaving a `(n ∸ |p|)`-budget on the functor-recursion tail.
take-++ : ∀ {ℓ} {X : Set ℓ} (n : ℕ) (p x : List X)
        → take n (p ++ x) ≡ take n p ++ take (n ∸ length p) x
take-++ zero    p        x rewrite 0∸n≡0 (length p) = refl
take-++ (suc n) []       x = refl
take-++ (suc n) (y ∷ p)  x = cong (y ∷_) (take-++ n p x)

-- If the tails agree up to the leftover budget, the full prefixes agree.
take-++-cong : ∀ {ℓ} {X : Set ℓ} (n : ℕ) (p x y : List X)
             → take (n ∸ length p) x ≡ take (n ∸ length p) y
             → take n (p ++ x) ≡ take n (p ++ y)
take-++-cong n p x y eq =
  trans (take-++ n p x) (trans (cong (take n p ++_) eq) (sym (take-++ n p y)))

-- A SHORTER prefix follows from a longer one. This is how the depth IH discharges
-- a functor `Id` position: the recursion's IH gives `take k`, and the leftover
-- budget there is `d ≤ k` (because the coalgebra already consumed ≥ 1 event), so
-- `take d` follows. (`take d xs = take d (take k xs)` for `d ≤ k`.)
take-mono : ∀ {ℓ} {X : Set ℓ} (d k : ℕ) (xs ys : List X)
          → d ≤ k → take k xs ≡ take k ys → take d xs ≡ take d ys
take-mono zero    k       xs       ys       _       _  = refl
take-mono (suc d) (suc k) []       []       _       _  = refl
take-mono (suc d) (suc k) []       (y ∷ ys) (s≤s _) ()
take-mono (suc d) (suc k) (x ∷ xs) []       (s≤s _) ()
take-mono (suc d) (suc k) (x ∷ xs) (y ∷ ys) (s≤s le) eq =
  cong₂ _∷_ (proj₁ (∷-injective eq)) (take-mono d k xs ys le (proj₂ (∷-injective eq)))

-- Equal `take d` prefixes ⇒ equal leftover budgets `d ∸ length`. This is what
-- aligns the split point in the functor `⊗` case: `take d (A ++ B) ≡ take d (C ++ D)`
-- from sub-prefix matches needs the offsets `d ∸ |A|` and `d ∸ |C|` to coincide,
-- which they do precisely because the `take d` prefixes match (both ≥ d, or both
-- full with equal length).
take-len : ∀ {ℓ} {X : Set ℓ} (d : ℕ) (A C : List X)
         → take d A ≡ take d C → d ∸ length A ≡ d ∸ length C
take-len zero    A        C        _  = trans (0∸n≡0 (length A)) (sym (0∸n≡0 (length C)))
take-len (suc d) []       []       _  = refl
take-len (suc d) []       (c ∷ C)  ()
take-len (suc d) (a ∷ A)  []       ()
take-len (suc d) (a ∷ A)  (c ∷ C)  eq = take-len d A C (proj₂ (∷-injective eq))

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Once.Type using (Type; Functor; ⟦_⟧T; K; Id; _⊕_; _⊗_)
open import Once.CCC.IR using (IR)
open import Once.CCC.Eval as Val using ()
open import Once.Semantics.Machine using (⟦_⟧F)
open import Once.Verified.Trace using (SigOpEvent)
open import Once.Verified.DenotTrace using (ana-events; evalᴰ; inject)
open import Once.Verified.SourceSemantics
  using (Value; Vint; Vstr; Vunit; Vpair; Vinl; Vinr; Vin; Vclos; Vbuiltin; Vsigop; Vana
        ; Defs; Result; runTraceEval; anaUnfold; mapAnaF; apply; _>>=ᵣ_)
open import Once.Verified.TraceDenote using (events-F)
import Once.Verified.ElaborateTrace as ET

-- `>>=ᵣ`-ing with a PURE `just (g x , [])` preserves the trace: the functor `⊕`
-- walk wraps each sub-walk's result in `Vinl`/`Vinr` and emits no events of its
-- own, so its trace is exactly the sub-walk's trace (modulo `e ++ [] ≡ e`).
rte-mapj : (g : Value → Value) (m : Result)
         → runTraceEval (m >>=ᵣ λ x → just (g x , [])) ≡ runTraceEval m
rte-mapj g nothing        = refl
rte-mapj g (just (v , e)) = ++-identityʳ e

-- The per-layer correspondence, by recursion on the functor. A layer `⟦F⟧F A`
-- (denotational) corresponds to a `Value` (operational) when their seeds at the
-- `Id` positions are `R`-related; constant (`K`) data carries no seeds (hence no
-- trace), so it is unconstrained. This is what the functor-recursive unfold walk
-- consumes: at each `Id` it pulls an `R`-related sub-seed to recurse on.
LayerRel : ∀ {A : Type} (R : Val.⟦ A ⟧ → Value → Set)
           (F : Functor) → ⟦ F ⟧F Val.⟦ A ⟧ → Value → Set
LayerRel R (K T)     d         v             = ⊤
LayerRel R Id        d         v             = R d v
LayerRel R (F₁ ⊕ F₂) (inj₁ d)  (Vinl v)      = LayerRel R F₁ d v
LayerRel R (F₁ ⊕ F₂) (inj₂ d)  (Vinr v)      = LayerRel R F₂ d v
LayerRel R (F₁ ⊕ F₂) _         _             = ⊥
LayerRel R (F₁ ⊗ F₂) (d₁ , d₂) (Vpair v₁ v₂) = LayerRel R F₁ d₁ v₁ × LayerRel R F₂ d₂ v₂
LayerRel R (F₁ ⊗ F₂) _         _             = ⊥

module _ (defs : Defs) where

  -- The coalgebra + seed correspondence, CONCRETE: the coalgebra `A → F(A)` is a
  -- FINITE morphism, so its correspondence is exactly the finite bridge's CompSim
  -- at the coalgebra — `evalᴰ coalgD` (denotationally, from the seed) simulates
  -- `apply coalgV` (operationally). Its value-sim component sits at `⟦F⟧T A`, which
  -- IS the per-layer correspondence the unfold recursion consumes (it recurses the
  -- type structure of `F`, relating seeds at the `Id`/`A` positions). The seed
  -- relation is folded in via the closed coalgebra applied to `inject a` / `av`.
  CoalgSeedCorr :
    ∀ {F : Functor} {A : Type} → IR A (⟦ F ⟧T A) → Value → Val.⟦ A ⟧ → Value → Set
  CoalgSeedCorr {F} {A} coalgD coalgV a av =
    ET.CompSim defs (⟦ F ⟧T A) (evalᴰ coalgD (inject a)) (λ s → apply s defs coalgV av)

  -- The functor-recursive unfold walk: ONE layer `⟦G⟧F A` is walked structurally,
  -- recursing the OUTER unfold (`coalgD`/`coalgV` at depth `k`) at each `Id`. The
  -- depth IH (`IH`) and the coalgebra-uniformity (`coalgU`, turning an `R`-related
  -- seed into the seed's correspondence) are fixed as module parameters; the walk
  -- is structural on `G`. Proves K / Id / ⊕ outright; the genuine productivity
  -- core is isolated to the ⊗ case (`functor-walk-pair`).
  module FunctorWalk
    {F : Functor} {A : Type}
    (coalgD : IR A (⟦ F ⟧T A)) (coalgV : Value) (k : ℕ)
    (R : Val.⟦ A ⟧ → Value → Set)
    (coalgU : ∀ a' av' → R a' av' → CoalgSeedCorr {F} {A} coalgD coalgV a' av')
    (IH : ∀ a' av' → CoalgSeedCorr {F} {A} coalgD coalgV a' av'
         → ∃[ s ] take k (ana-events {F} {A} coalgD a' k)
                    ≡ take k (runTraceEval (anaUnfold s defs F coalgV av')))
    where

    postulate
      -- THE PRODUCTIVE CORE (⊗). The two sub-walks run at a COMMON operational
      -- fuel, so combining their per-sub-walk ∃-fuels needs fuel-stabilization
      -- (more fuel → the same observed prefix, once stabilized); the split itself
      -- is `take-++-cong` + `take-len`. This is the genuine corecursion content
      -- and the last honest hole of the structural walk. [open]
      functor-walk-pair :
        ∀ (G₁ G₂ : Functor) (d : ℕ) → d ≤ k
        → (ld₁ : ⟦ G₁ ⟧F Val.⟦ A ⟧) (ld₂ : ⟦ G₂ ⟧F Val.⟦ A ⟧) (lv₁ lv₂ : Value)
        → LayerRel R G₁ ld₁ lv₁ → LayerRel R G₂ ld₂ lv₂
        → ∃[ s ] take d (events-F (G₁ ⊗ G₂) (λ seed → ana-events {F} {A} coalgD seed k) (ld₁ , ld₂))
                   ≡ take d (runTraceEval (mapAnaF s defs F (G₁ ⊗ G₂) coalgV (Vpair lv₁ lv₂)))

    functor-walk : (G : Functor) (d : ℕ) → d ≤ k
                 → (ld : ⟦ G ⟧F Val.⟦ A ⟧) (lv : Value)
                 → LayerRel R G ld lv
                 → ∃[ s ] take d (events-F G (λ seed → ana-events {F} {A} coalgD seed k) ld)
                            ≡ take d (runTraceEval (mapAnaF s defs F G coalgV lv))
    -- K: constant data — no events on either side.
    functor-walk (K T) d d≤k ld lv lr = zero , refl
    -- Id: this position IS a sub-seed; recurse the OUTER unfold via the depth IH,
    -- and shrink the prefix from `take k` to `take d` (d ≤ k by density) via take-mono.
    functor-walk Id d d≤k ld lv lr =
      let (s , eq) = IH ld lv (coalgU ld lv lr)
      in s , take-mono d k _ _ d≤k eq
    -- ⊕: the operational walk wraps the sub-walk in Vinl/Vinr (no events of its
    -- own), so its trace = the sub-walk's trace (rte-mapj). Recurse.
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₁ ld) (Vinl lv) lr =
      let (s , eq) = functor-walk G₁ d d≤k ld lv lr
      in s , trans eq (sym (cong (take d) (rte-mapj Vinl (mapAnaF s defs F G₁ coalgV lv))))
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₂ ld) (Vinr lv) lr =
      let (s , eq) = functor-walk G₂ d d≤k ld lv lr
      in s , trans eq (sym (cong (take d) (rte-mapj Vinr (mapAnaF s defs F G₂ coalgV lv))))
    -- ⊗: the productive core.
    functor-walk (G₁ ⊗ G₂) d d≤k (ld₁ , ld₂) (Vpair lv₁ lv₂) (lr₁ , lr₂) =
      functor-walk-pair G₁ G₂ d d≤k ld₁ ld₂ lv₁ lv₂ lr₁ lr₂
    -- ⊕/⊗ shape mismatches: LayerRel = ⊥.
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₁ ld) (Vint _)     ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₁ ld) (Vstr _)     ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₁ ld) Vunit        ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₁ ld) (Vpair _ _)  ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₁ ld) (Vinr _)     ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₁ ld) (Vin _)      ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₁ ld) (Vclos _ _ _) ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₁ ld) (Vbuiltin _ _) ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₁ ld) (Vsigop _ _) ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₁ ld) (Vana _ _)   ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₂ ld) (Vint _)     ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₂ ld) (Vstr _)     ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₂ ld) Vunit        ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₂ ld) (Vpair _ _)  ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₂ ld) (Vinl _)     ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₂ ld) (Vin _)      ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₂ ld) (Vclos _ _ _) ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₂ ld) (Vbuiltin _ _) ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₂ ld) (Vsigop _ _) ()
    functor-walk (G₁ ⊕ G₂) d d≤k (inj₂ ld) (Vana _ _)   ()
    functor-walk (G₁ ⊗ G₂) d d≤k (ld₁ , ld₂) (Vint _)     ()
    functor-walk (G₁ ⊗ G₂) d d≤k (ld₁ , ld₂) (Vstr _)     ()
    functor-walk (G₁ ⊗ G₂) d d≤k (ld₁ , ld₂) Vunit        ()
    functor-walk (G₁ ⊗ G₂) d d≤k (ld₁ , ld₂) (Vinl _)     ()
    functor-walk (G₁ ⊗ G₂) d d≤k (ld₁ , ld₂) (Vinr _)     ()
    functor-walk (G₁ ⊗ G₂) d d≤k (ld₁ , ld₂) (Vin _)      ()
    functor-walk (G₁ ⊗ G₂) d d≤k (ld₁ , ld₂) (Vclos _ _ _) ()
    functor-walk (G₁ ⊗ G₂) d d≤k (ld₁ , ld₂) (Vbuiltin _ _) ()
    functor-walk (G₁ ⊗ G₂) d d≤k (ld₁ , ld₂) (Vsigop _ _) ()
    functor-walk (G₁ ⊗ G₂) d d≤k (ld₁ , ld₂) (Vana _ _)   ()

  postulate
    -- THE PRODUCTIVE INDUCTIVE STEP — the genuine hard core. Given the operands
    -- correspond, at depth `suc k` the take-`(suc k)` event prefixes agree at SOME
    -- operational fuel `s`. TAKE-based (the operational fuel ≠ the denotational
    -- depth; the traces agree only on the observed prefix). Proof = a prefix
    -- simulation threading `take` through one unfold layer (coalgebra step +
    -- functor-recursive unfolds) and the depth IH — still open.
    ana-trace-step :
      ∀ {F : Functor} {A : Type} (coalgD : IR A (⟦ F ⟧T A)) (coalgV : Value)
        (a : Val.⟦ A ⟧) (av : Value) (k : ℕ)
      → CoalgSeedCorr {F} {A} coalgD coalgV a av
      → ∃[ s ] take (suc k) (ana-events {F} {A} coalgD a (suc k))
                 ≡ take (suc k) (runTraceEval (anaUnfold s defs F coalgV av))

  -- THE PRODUCTIVE CORRESPONDENCE. `∀k∃s`, conditional on the correspondence.
  -- Base (k=0): both prefixes are `take 0 _ = []`. Step: `ana-trace-step`.
  ana-trace-correct :
    ∀ {F : Functor} {A : Type} (coalgD : IR A (⟦ F ⟧T A)) (coalgV : Value)
      (a : Val.⟦ A ⟧) (av : Value) (k : ℕ)
    → CoalgSeedCorr {F} {A} coalgD coalgV a av
    → ∃[ s ] take k (ana-events {F} {A} coalgD a k)
               ≡ take k (runTraceEval (anaUnfold s defs F coalgV av))
  ana-trace-correct coalgD coalgV a av zero    cc = zero , refl
  ana-trace-correct coalgD coalgV a av (suc k) cc = ana-trace-step coalgD coalgV a av k cc
