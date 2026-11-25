-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Table — the checker's reading of the generator table
-- (`Spec.Surface.Generators`, plan 0.151).
--
-- A structure map has one rule per mode over the table (`c-map`, `c-map-app`,
-- `d-map`). The checker decides the table at the types it has: at a given
-- arrow (`mapAt?`), from a given domain at its least codomain (`mapFrom?`),
-- and, for a map its codomain fixes, from a given codomain (`mapTo?`). Each
-- answers with the IR morphism the map compiles to (`morphIR`, the
-- realization's: `Denotation.RealizeS`). Plain code; that the answers are the
-- table's is `TypeCheck.TableSound`.
------------------------------------------------------------------------

module Once.TypeCheck.Table where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (yes; no)

open import Once.Spec.Grade using (Purity; pure; act; eff; Finite; fin; pureᶠ; actᶠ; Many; mk-kind)
open import Once.Spec.Type using (Ty; KCtx; Fun; Unit; Void; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F; WFFun)
open import Once.Spec.Core.Syntax using (Defs; Tm)
open import Once.Spec.Core.Derived using (𝕋)
open import Once.Spec.Surface.Generators
open import Once.Type.DecEq using (_≟T_)
open import Once.Functor.Decide using (wfFun?)
open import Once.IR as IR using (IR)
open import Once.Surface.Map using (Map; mp-id; mp-fst; mp-snd; mp-terminal; mp-inl; mp-inr; mp-initial; mp-apply; mp-In; mp-Out; mp-toFloat)
open import Once.Arith.SigOp.Builders using (i2f-info)
open import Once.IRTy using (⌊_⌋; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)

------------------------------------------------------------------------
-- What a structure map compiles to
------------------------------------------------------------------------

-- The IR `In`, `Out` at a functor's layer.
inIR : ∀ {m} {Δ : KCtx m} (F : Fun m) → WFFun Δ F → IR ⌊ ⟦ F ⟧F (μ F) ⌋ ⌊ μ F ⌋
inIR F w = subst (λ o → IR o ⌊ μ F ⌋) (sym (⌊⟧T-commute F (μ F))) (IR.In (wf-⌊⌋ w))

outIR : ∀ {m} {Δ : KCtx m} (F : Fun m) (f : Finite) → WFFun Δ F → IR ⌊ ν F f ⌋ ⌊ ⟦ F ⟧F (ν F f) ⌋
outIR F f w = subst (λ o → IR ⌊ ν F f ⌋ o) (sym (⌊⟧T-commute F (ν F f))) (IR.Out (wf-⌊⌋ w))

-- `apply` at a closure of grade `ρ`: pure, the call; effectful, the
-- suspension of the call (D222).
applyIR : ∀ {m} (A B : Ty m) (ρ : Purity) → IR ⌊ (A ⇒[ mk-kind Many ρ ] B) * A ⌋ ⌊ 𝕋 ρ B ⌋
applyIR A B pure = IR.apply
applyIR A B act  = IR.curry (IR.apply IR.∘ IR.fst)
applyIR A B eff  = IR.curry (IR.apply IR.∘ IR.fst)

-- `Out` at a stream of grade `f`: pure, the force; acting, its suspension (D233).
outTIR : ∀ {m} {Δ : KCtx m} (F : Fun m) (f : Finite) → WFFun Δ F → IR ⌊ ν F f ⌋ ⌊ 𝕋 (fin f) (⟦ F ⟧F (ν F f)) ⌋
outTIR F pureᶠ w = outIR F pureᶠ w
outTIR F actᶠ  w = IR.curry (outIR F actᶠ w IR.∘ IR.fst)

-- ★ D461: a structure map's IR, a function of its table entry
mapIR : ∀ {m} {A B : Ty m} → Map A B → IR ⌊ A ⌋ ⌊ B ⌋
mapIR mp-id             = IR.id
mapIR mp-fst            = IR.fst
mapIR mp-snd            = IR.snd
mapIR mp-terminal       = IR.terminal
mapIR mp-inl            = IR.inl
mapIR mp-inr            = IR.inr
mapIR mp-initial        = IR.initial
mapIR (mp-apply A B ρ)  = applyIR A B ρ
mapIR (mp-In F w)       = inIR F w
mapIR (mp-Out F f w)    = outTIR F f w
mapIR mp-toFloat        = IR.SigOp i2f-info

-- the entry the Spec's row names
morphMap : ∀ {m} {Δ : KCtx m} {s} {S : Defs s} {n} {g k A π B} {t : Tm S m n}
         → Morphism Δ g k A π B t → Map A B
morphMap m-id                         = mp-id
morphMap m-fst                        = mp-fst
morphMap m-snd                        = mp-snd
morphMap m-terminal                   = mp-terminal
morphMap m-inl                        = mp-inl
morphMap m-inr                        = mp-inr
morphMap m-initial                    = mp-initial
morphMap (m-apply {A = A} {B} {ρ})    = mp-apply A B ρ
morphMap (m-In {F = F} w)             = mp-In F w
morphMap (m-Out {F = F} {f} w)        = mp-Out F f w

morphIR : ∀ {m} {Δ : KCtx m} {s} {S : Defs s} {n} {g k A π B} {t : Tm S m n}
        → Morphism Δ g k A π B t → IR ⌊ A ⌋ ⌊ B ⌋
morphIR mo = mapIR (morphMap mo)

------------------------------------------------------------------------
-- Type views the deciders read
------------------------------------------------------------------------

module _ where
  data SumV {m} : Ty m → Set where
    sum-at    : ∀ A B → SumV (A + B)
    sum-other : ∀ {T} → SumV T

  sumV : ∀ {m} (T : Ty m) → SumV T
  sumV (A + B) = sum-at A B
  {-# CATCHALL #-}
  sumV _ = sum-other

  data ProdV {m} : Ty m → Set where
    prod-at    : ∀ A B → ProdV (A * B)
    prod-other : ∀ {T} → ProdV T

  prodV : ∀ {m} (T : Ty m) → ProdV T
  prodV (A * B) = prod-at A B
  {-# CATCHALL #-}
  prodV _ = prod-other

  data ApplyV {m} : Ty m → Set where
    apply-at    : ∀ A ρ B A′ → ApplyV ((A ⇒[ mk-kind Many ρ ] B) * A′)
    apply-other : ∀ {T} → ApplyV T

  applyV : ∀ {m} (T : Ty m) → ApplyV T
  applyV ((A ⇒[ mk-kind Many ρ ] B) * A′) = apply-at A ρ B A′
  {-# CATCHALL #-}
  applyV _ = apply-other

  data MuV {m} : Ty m → Set where
    mu-at    : ∀ F → MuV (μ F)
    mu-other : ∀ {T} → MuV T

  muV : ∀ {m} (T : Ty m) → MuV T
  muV (μ F) = mu-at F
  {-# CATCHALL #-}
  muV _ = mu-other

  data NuV {m} : Ty m → Set where
    nu-at    : ∀ F f → NuV (ν F f)
    nu-other : ∀ {T} → NuV T

  nuV : ∀ {m} (T : Ty m) → NuV T
  nuV (ν F f) = nu-at F f
  {-# CATCHALL #-}
  nuV _ = nu-other

------------------------------------------------------------------------
-- From a given domain, at the least codomain (`d-map`)
------------------------------------------------------------------------

-- The least codomain and the morphism; `nothing` for a map its domain does
-- not fix, or a domain the map has no instance at.
mapFrom? : ∀ {m} (Δ : KCtx m) (g : Gen) (A : Ty m) → Maybe (Σ[ B ∈ Ty m ] Map A B)
mapFrom?-fst      : ∀ {m} {A : Ty m} → ProdV A → Maybe (Σ[ B ∈ Ty m ] Map A B)
mapFrom?-snd      : ∀ {m} {A : Ty m} → ProdV A → Maybe (Σ[ B ∈ Ty m ] Map A B)
mapFrom?-apply    : ∀ {m} {A : Ty m} → ApplyV A → Maybe (Σ[ B ∈ Ty m ] Map A B)
mapFrom?-apply-at : ∀ {m} (A : Ty m) ρ B {A′ : Ty m} → Relation.Nullary.Dec (A ≡ A′)
                  → Maybe (Σ[ C ∈ Ty m ] Map ((A ⇒[ mk-kind Many ρ ] B) * A′) C)
mapFrom?-initial  : ∀ {m} (A : Ty m) → Relation.Nullary.Dec (A ≡ Void) → Maybe (Σ[ B ∈ Ty m ] Map A B)
mapFrom?-Out      : ∀ {m} (Δ : KCtx m) {A : Ty m} → NuV A → Maybe (Σ[ B ∈ Ty m ] Map A B)
mapFrom?-Out-wf   : ∀ {m} {Δ : KCtx m} (F : Fun m) (f : Finite) → Maybe (WFFun Δ F)
                  → Maybe (Σ[ B ∈ Ty m ] Map (ν F f) B)

mapFrom? Δ id       A = just (A , mp-id)
mapFrom? Δ fst      A = mapFrom?-fst (prodV A)
mapFrom? Δ snd      A = mapFrom?-snd (prodV A)
mapFrom? Δ terminal A = just (Unit , mp-terminal)
mapFrom? Δ initial  A = mapFrom?-initial A (A ≟T Void)
mapFrom? Δ apply    A = mapFrom?-apply (applyV A)
mapFrom? Δ Out      A = mapFrom?-Out Δ (nuV A)
mapFrom? Δ compose  A = nothing
mapFrom? Δ pair     A = nothing
mapFrom? Δ inl      A = nothing
mapFrom? Δ inr      A = nothing
mapFrom? Δ case     A = nothing
mapFrom? Δ curry    A = nothing
mapFrom? Δ In       A = nothing
mapFrom? Δ cata     A = nothing
mapFrom? Δ ana      A = nothing
mapFrom? Δ unit     A = nothing
mapFrom? Δ toFloat  A = nothing

mapFrom?-fst (prod-at A B) = just (A , mp-fst)
mapFrom?-fst prod-other    = nothing
mapFrom?-snd (prod-at A B) = just (B , mp-snd)
mapFrom?-snd prod-other    = nothing
mapFrom?-initial .Void (yes refl) = just (Void , mp-initial)
mapFrom?-initial A     (no _)     = nothing
mapFrom?-apply (apply-at A ρ B A′) = mapFrom?-apply-at A ρ B (A ≟T A′)
mapFrom?-apply apply-other         = nothing
mapFrom?-apply-at A ρ B (yes refl) = just (𝕋 ρ B , mp-apply A B ρ)
mapFrom?-apply-at A ρ B (no _)     = nothing
mapFrom?-Out Δ (nu-at F f) = mapFrom?-Out-wf {Δ = Δ} F f (wfFun? Δ F)
mapFrom?-Out Δ nu-other    = nothing
mapFrom?-Out-wf F f (just w) = just (𝕋 (fin f) (⟦ F ⟧F (ν F f)) , mp-Out F f w)
mapFrom?-Out-wf F f nothing  = nothing

------------------------------------------------------------------------
-- From a given codomain, at pure, for a map its codomain fixes (`c-map-app`)
------------------------------------------------------------------------

mapTo? : ∀ {m} (Δ : KCtx m) (g : Gen) (B : Ty m) → Maybe (Σ[ A ∈ Ty m ] Map A B)
mapTo?-inl   : ∀ {m} {B : Ty m} → SumV B → Maybe (Σ[ A ∈ Ty m ] Map A B)
mapTo?-inr   : ∀ {m} {B : Ty m} → SumV B → Maybe (Σ[ A ∈ Ty m ] Map A B)
mapTo?-In    : ∀ {m} (Δ : KCtx m) {B : Ty m} → MuV B → Maybe (Σ[ A ∈ Ty m ] Map A B)
mapTo?-In-wf : ∀ {m} {Δ : KCtx m} (F : Fun m) → Maybe (WFFun Δ F) → Maybe (Σ[ A ∈ Ty m ] Map A (μ F))

mapTo? Δ id       B = just (B , mp-id)
mapTo? Δ inl      B = mapTo?-inl (sumV B)
mapTo? Δ inr      B = mapTo?-inr (sumV B)
mapTo? Δ initial  B = just (Void , mp-initial)
mapTo? Δ In       B = mapTo?-In Δ (muV B)
mapTo? Δ compose  B = nothing
mapTo? Δ fst      B = nothing
mapTo? Δ snd      B = nothing
mapTo? Δ terminal B = nothing
mapTo? Δ pair     B = nothing
mapTo? Δ case     B = nothing
mapTo? Δ apply    B = nothing
mapTo? Δ curry    B = nothing
mapTo? Δ cata     B = nothing
mapTo? Δ Out      B = nothing
mapTo? Δ ana      B = nothing
mapTo? Δ unit     B = nothing
mapTo? Δ toFloat  B = nothing

mapTo?-inl (sum-at A B) = just (A , mp-inl)
mapTo?-inl sum-other    = nothing
mapTo?-inr (sum-at A B) = just (B , mp-inr)
mapTo?-inr sum-other    = nothing
mapTo?-In Δ (mu-at F) = mapTo?-In-wf {Δ = Δ} F (wfFun? Δ F)
mapTo?-In Δ mu-other  = nothing
mapTo?-In-wf F (just w) = just (⟦ F ⟧F (μ F) , mp-In F w)
mapTo?-In-wf F nothing  = nothing

------------------------------------------------------------------------
-- At a given arrow (`c-map`)
------------------------------------------------------------------------

-- A structure map's instances at `A ⇒⟨ π ⟩ B` are its instances from the
-- domain whose codomain is `B`, but for `initial` (any codomain) and the
-- maps only the codomain fixes.
mapAt? : ∀ {m} (Δ : KCtx m) (g : Gen) (A : Ty m) (B : Ty m) → Maybe (Map A B)
mapAt?-by-dom : ∀ {m} {A : Ty m} (B : Ty m) → Maybe (Σ[ B′ ∈ Ty m ] Map A B′) → Maybe (Map A B)
mapAt?-by-dom-eq : ∀ {m} {A : Ty m} (B B′ : Ty m) → Map A B′ → Relation.Nullary.Dec (B′ ≡ B) → Maybe (Map A B)
mapAt?-by-cod : ∀ {m} (A : Ty m) {B : Ty m} → Maybe (Σ[ A′ ∈ Ty m ] Map A′ B) → Maybe (Map A B)
mapAt?-by-cod-eq : ∀ {m} (A A′ : Ty m) {B : Ty m} → Map A′ B → Relation.Nullary.Dec (A′ ≡ A) → Maybe (Map A B)
mapAt?-initial : ∀ {m} (A : Ty m) {B : Ty m} → Relation.Nullary.Dec (A ≡ Void) → Maybe (Map A B)

mapAt? Δ initial  A B = mapAt?-initial A {B = B} (A ≟T Void)
mapAt? Δ inl      A B = mapAt?-by-cod A {B = B} (mapTo? Δ inl B)
mapAt? Δ inr      A B = mapAt?-by-cod A {B = B} (mapTo? Δ inr B)
mapAt? Δ In       A B = mapAt?-by-cod A {B = B} (mapTo? Δ In B)
mapAt? Δ id       A B = mapAt?-by-dom {A = A} B (mapFrom? Δ id A)
mapAt? Δ fst      A B = mapAt?-by-dom {A = A} B (mapFrom? Δ fst A)
mapAt? Δ snd      A B = mapAt?-by-dom {A = A} B (mapFrom? Δ snd A)
mapAt? Δ terminal A B = mapAt?-by-dom {A = A} B (mapFrom? Δ terminal A)
mapAt? Δ apply    A B = mapAt?-by-dom {A = A} B (mapFrom? Δ apply A)
mapAt? Δ Out      A B = mapAt?-by-dom {A = A} B (mapFrom? Δ Out A)
mapAt? Δ compose  A B = nothing
mapAt? Δ pair     A B = nothing
mapAt? Δ case     A B = nothing
mapAt? Δ curry    A B = nothing
mapAt? Δ cata     A B = nothing
mapAt? Δ ana      A B = nothing
mapAt? Δ unit     A B = nothing
mapAt? Δ toFloat  A B = nothing

mapAt?-by-dom B nothing          = nothing
mapAt?-by-dom {A = A} B (just (B′ , m′)) = mapAt?-by-dom-eq {A = A} B B′ m′ (B′ ≟T B)
mapAt?-by-dom-eq B .B m′ (yes refl) = just m′
mapAt?-by-dom-eq B B′ m′ (no _)     = nothing
mapAt?-by-cod A nothing          = nothing
mapAt?-by-cod A {B} (just (A′ , m′)) = mapAt?-by-cod-eq A A′ {B = B} m′ (A′ ≟T A)
mapAt?-by-cod-eq A .A m′ (yes refl) = just m′
mapAt?-by-cod-eq A A′ m′ (no _)     = nothing
mapAt?-initial .Void (yes refl) = just mp-initial
mapAt?-initial A     (no _)     = nothing
