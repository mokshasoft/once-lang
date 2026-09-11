-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.ValueDomain — the IR-FREE monadic value domain.
--
-- Extracted from `Once.Denotation.DenotTrace` (Plan 0.58, OCP-0006): the value
-- domain `⟦_⟧ᴰ`, the `forget`/`inject` coercions, and the SigOp emission
-- `emit-D` use only `Once.Type` / `Val` / the trace monad / `SigOp.Info` — NO
-- `Once.IR` (IR enters only at `evalᴰ`, which STAYS in `DenotTrace`). This is
-- the semantic-domain vocabulary the IR-free reference meaning `⟦_⟧ᵈ` lands in.
--
-- `DenotTrace` re-exports this (`open … public`), so consumers are unchanged.
------------------------------------------------------------------------

module Once.Denotation.ValueDomain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; sym; subst)

open import Once.Type
open import Once.IRTy using (IRTy; ⌈_⌉; ⌊_⌋)
open import Once.CCC.Eval as Val using ()
open import Once.SigOp.Info
open import Once.Denotation.Trace using (SigOpEvent; mkEvent)
open import Once.Denotation.TraceMonad using (T; returnT; valueT; projTrace; fmapT; _>>=T_)
open import Once.Semantics.Machine using (⟦_⟧F; coh; tF-coh)
open import Once.Word using (Carrier)
open import Once.Semantics.Functor using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; νS; unfoldS)
open import Once.Functor.Translate using (translateF)
open import Once.Semantics.Machine using (coerce-ν-in)

------------------------------------------------------------------------
-- The effectful greatest fixed point.
--
-- `νS`'s layer is a value; `νᵈ`'s is a COMPUTATION. That single `T` is the
-- whole difference, and it is what lets an anamorphism over an effectful
-- coalgebra be a value at all.
--
-- D062's rule applies to everything below: a corecursive call must sit
-- STRUCTURALLY under the guard, never be passed to a defined function. So the
-- functor maps are inlined (never `sfmap`) and the bind is unfolded by hand
-- (never `_>>=T_`). Both were checked against negative controls; each one
-- fails the termination checker when written the convenient way.
------------------------------------------------------------------------

record νᵈ (F : SFunctor) : Set where
  coinductive
  field
    forceᵈ : T (⟦ F ⟧SF (νᵈ F))

open νᵈ public

-- `forget` at an arrow runs the closure at depth `0` and drops its trace.
-- This is the same thing, one layer at a time.
mutual
  forgetν : ∀ {F} → νᵈ F → νS F
  unfoldS (forgetν {F} v) = mapForgetν F F (valueT (forceᵈ v) zero)

  mapForgetν : ∀ (F H : SFunctor) → ⟦ H ⟧SF (νᵈ F) → ⟦ H ⟧SF (νS F)
  mapForgetν F (SK B)   x        = x
  mapForgetν F SId      x        = forgetν x
  mapForgetν F (H S⊕ J) (inj₁ x) = inj₁ (mapForgetν F H x)
  mapForgetν F (H S⊕ J) (inj₂ y) = inj₂ (mapForgetν F J y)
  mapForgetν F (H S⊗ J) (x , y)  = (mapForgetν F H x , mapForgetν F J y)

-- `inject` at an arrow lifts a pure function to a trace-free closure. This is
-- the same thing: every layer emits nothing.
mutual
  injectν : ∀ {F} → νS F → νᵈ F
  forceᵈ (injectν {F} x) = λ _ → ([] , mapInjectν F F (unfoldS x))

  mapInjectν : ∀ (F H : SFunctor) → ⟦ H ⟧SF (νS F) → ⟦ H ⟧SF (νᵈ F)
  mapInjectν F (SK B)   x        = x
  mapInjectν F SId      x        = injectν x
  mapInjectν F (H S⊕ J) (inj₁ x) = inj₁ (mapInjectν F H x)
  mapInjectν F (H S⊕ J) (inj₂ y) = inj₂ (mapInjectν F J y)
  mapInjectν F (H S⊗ J) (x , y)  = (mapInjectν F H x , mapInjectν F J y)

-- `injectν` commutes with a transport along the functor index. While `inject`
-- at ν was the identity and `cohᴰ` borrowed `coh`, the corresponding naturality
-- square was `refl`; now that both sides name their own constructor it has to
-- be proved, which is one `refl` after generalising the equation.
forgetν-coh : ∀ {F G : SFunctor} (eq : F ≡ G) (v : νᵈ G)
            → subst (λ z → z) (cong νS eq) (forgetν (subst (λ z → z) (sym (cong νᵈ eq)) v))
              ≡ forgetν v
forgetν-coh refl v = refl

injectν-coh : ∀ {F G : SFunctor} (eq : F ≡ G) (v : νS G)
            → injectν (subst (λ z → z) (sym (cong νS eq)) v)
              ≡ subst (λ z → z) (sym (cong νᵈ eq)) (injectν v)
injectν-coh refl v = refl

-- Sequence a functor layer of COMPUTATIONS into a computation of a layer.
--
-- This is what lets a `Cata` share ONE budget across a layer instead of
-- handing every child the full `n` and concatenating: the threading is
-- `_>>=T_`'s, so `bounded` holds by construction rather than by a bespoke
-- argument. Same reason `events-Fᵇ` replaced `events-F` on the ana side —
-- except here the layer is already monadic, so the traversal IS the fix.
seqF : ∀ (G : Functor) {X : Set} → ⟦ G ⟧F (T X) → T (⟦ G ⟧F X)
seqF (K A)   x        = returnT x
seqF Id      m        = m
seqF (G ⊕ H) (inj₁ x) = fmapT inj₁ (seqF G x)
seqF (G ⊕ H) (inj₂ y) = fmapT inj₂ (seqF H y)
seqF (G ⊗ H) (x , y)  = seqF G x >>=T λ u → seqF H y >>=T λ v → returnT (u , v)

-- The effectful anamorphism: `sem-ana` with the coalgebra's step made a
-- COMPUTATION. Forcing a layer runs the coalgebra once and emits exactly that
-- layer's events; the children are suspensions and emit nothing until they are
-- forced in turn. So the trace order is the order the program FORCES layers —
-- there is no traversal chosen here, which is the whole point.
mutual
  anaᵈ : ∀ (H : SFunctor) {A : Set} → (A → T (⟦ H ⟧SF A)) → A → νᵈ H
  forceᵈ (anaᵈ H coalg a) = λ k →
    ( projTrace (coalg a) k , mapAnaᵈ H H coalg (valueT (coalg a) k) )

  mapAnaᵈ : ∀ (H G : SFunctor) {A : Set}
          → (A → T (⟦ H ⟧SF A)) → ⟦ G ⟧SF A → ⟦ G ⟧SF (νᵈ H)
  mapAnaᵈ H (SK B)     coalg x        = x
  mapAnaᵈ H SId        coalg a        = anaᵈ H coalg a
  mapAnaᵈ H (G₁ S⊕ G₂) coalg (inj₁ x) = inj₁ (mapAnaᵈ H G₁ coalg x)
  mapAnaᵈ H (G₁ S⊕ G₂) coalg (inj₂ y) = inj₂ (mapAnaᵈ H G₂ coalg y)
  mapAnaᵈ H (G₁ S⊗ G₂) coalg (x , y)  = (mapAnaᵈ H G₁ coalg x , mapAnaᵈ H G₂ coalg y)

-- Transport across the functor index. Because `anaᵈ` is indexed by the
-- SFunctor and the `⟦_⟧F → ⟦_⟧SF` coercion happens OUTSIDE it, this is a
-- match-to-refl. `sem-ana` bakes `coerce-ν-in` in, which is exactly why its
-- erasure round-trip has to go through the `sem-ana-anaS` bisimulation and
-- the `bisimS-to-eq` axiom; keeping the coercion at the boundary means the
-- effectful side needs neither.
anaᵈ-subst-nat : ∀ {H₁ H₂ : SFunctor} (eq : H₁ ≡ H₂) {A : Set}
                 (c : A → T (⟦ H₁ ⟧SF A)) (a : A)
               → subst νᵈ eq (anaᵈ H₁ c a)
                 ≡ anaᵈ H₂ (subst (λ H → A → T (⟦ H ⟧SF A)) eq c) a
anaᵈ-subst-nat refl c a = refl

-- Erasure round-trip, functor index only. Matching `heq` to `refl` reduces it
-- to "the two coalgebras are the same function" — which is what the coalgebra
-- IH gives. No bisimulation and no axiom, because `anaᵈ` is indexed by the
-- SFunctor and the `⟦_⟧F → ⟦_⟧SF` coercion sits outside it.
anaᵈ-erase : ∀ {H₁ H₂ : SFunctor} (heq : H₁ ≡ H₂) {A : Set}
             (c₁ : A → T (⟦ H₁ ⟧SF A)) (c₂ : A → T (⟦ H₂ ⟧SF A)) (a : A)
           → subst (λ H → A → T (⟦ H ⟧SF A)) heq c₁ ≡ c₂
           → subst νᵈ heq (anaᵈ H₁ c₁ a) ≡ anaᵈ H₂ c₂ a
anaᵈ-erase refl c₁ c₂ a eq = cong (λ c → anaᵈ _ c a) eq

-- Carrier equality folded in, exactly as `sem-ana-erase-full` does for the
-- pure side, so consumers never hand-thread the carrier transport.
anaᵈ-erase-full : ∀ {H₁ H₂ : SFunctor} (heq : H₁ ≡ H₂) {A₁ A₂ : Set} (ceq : A₁ ≡ A₂)
    (c₁ : A₁ → T (⟦ H₁ ⟧SF A₁)) (c₂ : A₂ → T (⟦ H₂ ⟧SF A₂)) (a : A₁)
  → subst (λ H → A₂ → T (⟦ H ⟧SF A₂)) heq
      (λ x → subst (λ Z → T (⟦ H₁ ⟧SF Z)) ceq (c₁ (subst (λ z → z) (sym ceq) x)))
    ≡ c₂
  → subst νᵈ heq (anaᵈ H₁ c₁ a) ≡ anaᵈ H₂ c₂ (subst (λ z → z) ceq a)
anaᵈ-erase-full heq refl c₁ c₂ a eq = anaᵈ-erase heq c₁ c₂ a eq

-- `subst` along a `cong`ed equation is `subst` along the equation (mirrors
-- `subst-νS-cong`). `cohᴰ (ν-type F)` is `cong νᵈ (tF-coh F)`, so consumers
-- need this to reach `anaᵈ-erase`.
subst-νᵈ-cong : ∀ {H₁ H₂ : SFunctor} (eq : H₁ ≡ H₂) (v : νᵈ H₁)
              → subst (λ z → z) (cong νᵈ eq) v ≡ subst νᵈ eq v
subst-νᵈ-cong refl v = refl

-- The Functor-level form the IR and surface clauses actually call: coerce the
-- layer at the boundary, then unfold.
anaFᵈ : ∀ (F : Functor) {A : Set}
      → (A → T (⟦ F ⟧F A)) → A → νᵈ (translateF Carrier Carrier F)
anaFᵈ F {A} coalg = anaᵈ (translateF Carrier Carrier F) (λ a → fmapT (coerce-ν-in F A) (coalg a))

------------------------------------------------------------------------
-- The monadic value domain. Mirrors `Val.⟦_⟧` EXCEPT at the arrow, which
-- becomes the Kleisli arrow into `T`.
------------------------------------------------------------------------

⟦_⟧ᴰ : Type → Set
⟦ Unit ⟧ᴰ       = ⊤
⟦ Void ⟧ᴰ       = ⊥
⟦ A * B ⟧ᴰ      = ⟦ A ⟧ᴰ × ⟦ B ⟧ᴰ
⟦ A + B ⟧ᴰ      = ⟦ A ⟧ᴰ ⊎ ⟦ B ⟧ᴰ
-- D143: the arrow's meaning is GRADE-AWARE at the quantity. A `Zero`-graded
-- argument is ERASED — it has no runtime existence — so the erased arrow's
-- meaning takes NO argument. Purity is still ignored: a pure and an effectful
-- arrow over the same A, B mean the same thing (that is what plan 0.52 M2
-- established, and it stays).
--
-- WHY THIS BELONGS IN THE SPEC. Erasure is a SEMANTIC claim. While the meaning
-- was grade-blind, "a Zero-graded argument is not represented at runtime" was a
-- promise no specification made, so no compiler could be obliged to keep it —
-- and `⌊_⌋` erasing became incoherent with `coh` (the full→runtime direction
-- has no canonical inhabitant when only ONE side forgets the argument). Making
-- both sides forget it together is what restores coherence.
⟦ A ⇒[ mk-kind Zero π ] B ⟧ᴰ = ⊤ → T ⟦ B ⟧ᴰ   -- erased: no argument
⟦ A ⇒[ mk-kind One  π ] B ⟧ᴰ = ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
⟦ A ⇒[ mk-kind Many π ] B ⟧ᴰ = ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
⟦ μ-type F ⟧ᴰ   = Val.⟦ μ-type F ⟧            -- first-order data: reuse pure
-- ν is the OTHER type that suspends computation, so like the arrow it is
-- Kleisli: forcing a layer IS a `T`-computation. A ν built by an EFFECTFUL
-- coalgebra cannot be a pure value — while it was one, `Ana` had to read its
-- coalgebra at budget `0` (discarding the effects) and the effects had to be
-- re-invented by a separate eager left-to-right unfold, which ordered events
-- the anamorphism does not order. Here the order is the order the program
-- FORCES layers, which is the order the machine runs them in.
⟦ ν-type F ⟧ᴰ   = νᵈ (translateF Carrier Carrier F)
⟦ Int ⟧ᴰ        = Val.⟦ Int ⟧
⟦ Float ⟧ᴰ      = Val.⟦ Float ⟧
⟦ Str ⟧ᴰ        = Val.⟦ Str ⟧
⟦ Buffer ⟧ᴰ     = Val.⟦ Buffer ⟧

------------------------------------------------------------------------
-- Plan 0.52 M2: the monadic value domain over the UNGRADED IR objects
-- (`⟦_⟧ᴰᴵ := ⟦_⟧ᴰ ∘ ⌈_⌉`), used to denote IR morphisms (evalᴰ/realize) now
-- that IR objects are `IRTy`. `cohᴰ` is the transport `⟦ ⌊T⌋ ⟧ᴰᴵ ≡ ⟦ T ⟧ᴰ`
-- (μ/ν reuse the pure-domain `coh`; the arrow is grade-blind Kleisli).

⟦_⟧ᴰᴵ : IRTy → Set
⟦ A ⟧ᴰᴵ = ⟦ ⌈ A ⌉ ⟧ᴰ

cohᴰ : ∀ (T' : Type) → ⟦ ⌊ T' ⌋ ⟧ᴰᴵ ≡ ⟦ T' ⟧ᴰ
cohᴰ Unit         = refl
cohᴰ Void         = refl
cohᴰ (A * B)      = cong₂ _×_ (cohᴰ A) (cohᴰ B)
cohᴰ (A + B)      = cong₂ _⊎_ (cohᴰ A) (cohᴰ B)
-- D143: split on the quantity. At `Zero` BOTH sides forget the argument
-- (`⌊_⌋` gives `Unit ⇛ ⌊B⌋`, `⟦_⟧ᴰ` gives `⊤ → T ⟦B⟧ᴰ`), so only the codomain
-- has to be transported — which is exactly what makes erasure coherent.
cohᴰ (A ⇒[ mk-kind Zero π ] B) = cong  (λ y → ⊤ → T y) (cohᴰ B)
cohᴰ (A ⇒[ mk-kind One  π ] B) = cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B)
cohᴰ (A ⇒[ mk-kind Many π ] B) = cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B)
cohᴰ (μ-type F)   = coh (μ-type F)
-- ν's monadic meaning is no longer its pure one, so this transport stops
-- borrowing `coh` and names its own constructor. Structurally identical.
cohᴰ (ν-type F)   = cong νᵈ (tF-coh F)
cohᴰ Int          = refl
cohᴰ Float        = refl
cohᴰ Str          = refl
cohᴰ Buffer       = refl

------------------------------------------------------------------------
-- Forgetful coercions between the monadic and the pure value domains.
-- They are the identity on every type EXCEPT the arrow: `forget` runs a
-- closure and drops its trace; `inject` lifts a pure function to a
-- trace-less (pure) closure. Closure runs use observation depth `zero` —
-- a closure is a TOTAL function, so its value is depth-independent.
-- Needed to interface with the pure `semM`/`eval` for base operations.
------------------------------------------------------------------------

mutual
  forget : ∀ {A} → ⟦ A ⟧ᴰ → Val.⟦ A ⟧
  forget {Unit}       x        = x
  forget {Void}       ()
  forget {A * B}      (a , b)  = (forget a , forget b)
  forget {A + B}      (inj₁ a) = inj₁ (forget a)
  forget {A + B}      (inj₂ b) = inj₂ (forget b)
  -- D143: split on the quantity. At `Zero` BOTH domains take `⟦Unit⟧`, so the
  -- argument is passed through untouched rather than injected — there is no
  -- argument of type `A` on either side to convert.
  forget {A ⇒[ mk-kind Zero π ] B} clo = λ u  → forget (valueT (clo u) zero)
  forget {A ⇒[ mk-kind One  π ] B} clo = λ va → forget (valueT (clo (inject va)) zero)
  forget {A ⇒[ mk-kind Many π ] B} clo = λ va → forget (valueT (clo (inject va)) zero)
  forget {μ-type F}   x        = x
  forget {ν-type F}   v        = forgetν v
  forget {Int}        x        = x
  forget {Float}      x        = x
  forget {Str}        x        = x
  forget {Buffer}     x        = x

  inject : ∀ {A} → Val.⟦ A ⟧ → ⟦ A ⟧ᴰ
  inject {Unit}       x        = x
  inject {Void}       ()
  inject {A * B}      (a , b)  = (inject a , inject b)
  inject {A + B}      (inj₁ a) = inj₁ (inject a)
  inject {A + B}      (inj₂ b) = inj₂ (inject b)
  inject {A ⇒[ mk-kind Zero π ] B} pf = λ u  → returnT (inject (pf u))
  inject {A ⇒[ mk-kind One  π ] B} pf = λ da → returnT (inject (pf (forget da)))
  inject {A ⇒[ mk-kind Many π ] B} pf = λ da → returnT (inject (pf (forget da)))
  inject {μ-type F}   x        = x
  inject {ν-type F}   x        = injectν x
  inject {Int}        x        = x
  inject {Float}      x        = x
  inject {Str}        x        = x
  inject {Buffer}     x        = x

------------------------------------------------------------------------
-- The effectful-SigOp emission (unconditional: the budget is consumed by
-- `Ana`, not by individual SigOps; the first-`n` prefix is taken at the
-- top). Pure SigOps emit nothing, in lockstep with the machine.
------------------------------------------------------------------------

emit-D : ∀ {A B} → SigOpInfo A B → Val.⟦ A ⟧ → List SigOpEvent
emit-D si x with effect si
... | Pure    = []
... | Emits _ = mkEvent si x ∷ []
... | Halts _ = mkEvent si x ∷ []

-- The BUDGET-AWARE emitter. `take n (emit-D si x)` is the wrong cap: `take`
-- matches its BUDGET first, so `take n []` is stuck while `n` is abstract —
-- which breaks every proof that knows only `emit-D si x ≡ []` (the whole
-- Pure/arith family). `capN` matches the LIST first, so an empty emission is
-- silent at every budget definitionally.
sig1ᴰ : ℕ → SigOpEvent → List SigOpEvent
sig1ᴰ zero    _ = []
sig1ᴰ (suc _) e = e ∷ []

capN : ℕ → List SigOpEvent → List SigOpEvent
capN n []       = []
capN n (e ∷ es) = sig1ᴰ n e

-- Budget LAST, mirroring the `take n (emit-D si x)` it replaces.
emit-Dᵇ : ∀ {A B} → SigOpInfo A B → Val.⟦ A ⟧ → ℕ → List SigOpEvent
emit-Dᵇ si x n = capN n (emit-D si x)

-- A Pure SigOp stays silent at every budget — one `cong`, because `capN n []`
-- reduces without knowing `n`.
emit-Dᵇ-[] : ∀ {A B} (si : SigOpInfo A B) (x : Val.⟦ A ⟧) (n : ℕ)
           → emit-D si x ≡ [] → emit-Dᵇ si x n ≡ []
emit-Dᵇ-[] si x n eq = cong (capN n) eq


------------------------------------------------------------------------
-- Plan 0.58: the `⟦_⟧ᴰ`-level functor coercion — the trace-preserving mirror
-- of `coerce-functor⁻¹`. The recursion-scheme fold must carry `⟦C⟧ᴰ` (NOT the
-- forgotten `Val.⟦C⟧`) so an EFFECTFUL-arrow carrier keeps its apply-time
-- effects (the `Val`-fold's `forget`-per-layer silently dropped them). Purely
-- structural: `Id`→carrier, `⊕`/`⊗`→structural, `K A`→`inject` (a `K` value is
-- `Val.⟦A⟧`; `inject` lifts it to `⟦A⟧ᴰ`, the identity at the base types `K`
-- holds for a `WellFormedF`).
-- The FORWARD direction, the mirror of `coerce-functor` at the `ᴰ` level.
-- `Ana` needs it to hand its coalgebra to `anaᵈ`. At `K` it forgets, exactly
-- as the inverse injects — and `WellFormedF` puts `K` only at base types,
-- where `forget` is the identity.
coerce-functor-D : ∀ F C → ⟦ ⟦ F ⟧T C ⟧ᴰ → ⟦ F ⟧F ⟦ C ⟧ᴰ
coerce-functor-D (K A)    C x        = forget x
coerce-functor-D Id       C x        = x
coerce-functor-D (F ⊕ G)  C (inj₁ x) = inj₁ (coerce-functor-D F C x)
coerce-functor-D (F ⊕ G)  C (inj₂ y) = inj₂ (coerce-functor-D G C y)
coerce-functor-D (F ⊗ G)  C (x , y)  = (coerce-functor-D F C x , coerce-functor-D G C y)

coerce-functor⁻¹-D : ∀ F C → ⟦ F ⟧F ⟦ C ⟧ᴰ → ⟦ ⟦ F ⟧T C ⟧ᴰ
coerce-functor⁻¹-D (K A)    C x        = inject x
coerce-functor⁻¹-D Id       C x        = x
coerce-functor⁻¹-D (F ⊕ G)  C (inj₁ x) = inj₁ (coerce-functor⁻¹-D F C x)
coerce-functor⁻¹-D (F ⊕ G)  C (inj₂ y) = inj₂ (coerce-functor⁻¹-D G C y)
coerce-functor⁻¹-D (F ⊗ G)  C (x , y)  = (coerce-functor⁻¹-D F C x , coerce-functor⁻¹-D G C y)
