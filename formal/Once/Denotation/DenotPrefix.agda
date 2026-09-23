-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.DenotPrefix — `evalᴰ` produces legitimate `Behavior`s.
--
-- `Behavior` (spec) demands `extends`/`bounded`/`saturates` of its `at`.
-- `TraceMonad.PrefixFamily` packages those for a `T`-computation and is closed
-- under `returnT`, `tell` and `_>>=T_`. What is missing is that `evalᴰ` lands
-- in that class — and that cannot be a plain induction on the IR, because
--
--     evalᴰ fmt apply p = proj₁ p (proj₂ p)
--
-- RUNS a closure that came out of the value domain. Nothing constrains it
-- unless the domain itself carries the predicate. So this is a LOGICAL
-- RELATION over `Type`, and `curry`/`apply` is the pair that forces it to
-- exist: `curry` puts a closure in, `apply` takes one out.
--
-- ν is coinductive here, and for the same reason it is Kleisli in the value
-- domain: a suspension is good exactly when FORCING it yields a prefix family
-- whose layer is again good. That is `Out`'s obligation, stated.
------------------------------------------------------------------------

module Once.Denotation.DenotPrefix where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; z≤n)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Once.Type
open import Once.Word using (Carrier)
open import Once.Semantics.Functor using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Denotation.TraceMonad using (T; mkT; valueT; PrefixFamily; prefixFamily; returnT; returnT-pf)
open import Data.Bool using (false)
open import Once.Denotation.ValueDomain
  using (⟦_⟧ᴰ; νᵈ; forceᵈ; inject; forget; injectν; mapInjectν)
open import Once.Semantics.Functor using (νS; unfoldS)
import Once.Semantics.Machine as Val
open import Once.IR using (IR)
open import Once.IRTy using (IRTy; ⌈_⌉; ⌊_⌋)
import Once.IRTy as IT
open import Once.IRTy using (WellFormedFI; FitsInRegI)
open import Once.IR using (NatTr)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.Float.Decimal using (Decimal)
open import Data.Integer using (ℤ)
open import Once.Target.Arch using (TargetNum)
open import Once.Denotation.DenotTrace using (evalᴰ; ⟦_⟧ᴰᴵ)
open import Once.Denotation.TraceMonad using (_>>=T_; >>=T-pf)
open Once.IR.IR

------------------------------------------------------------------------
-- The relation.
------------------------------------------------------------------------

-- A suspension is good when each forced layer is a prefix family whose
-- contents are good. Coinductive: the layer holds more suspensions.
mutual
  record Goodν {H : SFunctor} (v : νᵈ H) : Set where
    coinductive
    field
      force-pf   : PrefixFamily (forceᵈ v)
      force-good : ∀ k → GoodLayer H H (valueT (forceᵈ v) k)

  -- `SK` holds a Set of BASE data (`WellFormedF` puts `K` only at base
  -- types), which carries no closures and no suspensions — so the layer
  -- predicate only has to say something at `SId`.
  GoodLayer : ∀ (H G : SFunctor) → ⟦ G ⟧SF (νᵈ H) → Set
  GoodLayer H (SK B)     x        = ⊤
  GoodLayer H SId        v        = Goodν v
  GoodLayer H (G₁ S⊕ G₂) (inj₁ x) = GoodLayer H G₁ x
  GoodLayer H (G₁ S⊕ G₂) (inj₂ y) = GoodLayer H G₂ y
  GoodLayer H (G₁ S⊗ G₂) (x , y)  = GoodLayer H G₁ x × GoodLayer H G₂ y

open Goodν public

Good  : ∀ (A : Type) → ⟦ A ⟧ᴰ → Set
GoodT : ∀ (B : Type) → T ⟦ B ⟧ᴰ → Set

Good Unit        _        = ⊤
Good Void        ()
Good (A * B)     (a , b)  = Good A a × Good B b
Good (A + B)     (inj₁ a) = Good A a
Good (A + B)     (inj₂ b) = Good B b
-- The arrow is the whole point: a closure is good when it maps good
-- arguments to good computations. At `Zero` there is no argument.
Good (A ⇒[ mk-kind Zero π ] B) f = ∀ u → GoodT B (f u)
Good (A ⇒[ mk-kind One  π ] B) f = ∀ a → Good A a → GoodT B (f a)
Good (A ⇒[ mk-kind Many π ] B) f = ∀ a → Good A a → GoodT B (f a)
Good (μ-type F)  _        = ⊤     -- finite first-order data: no suspension
Good (ν-type F)  v        = Goodν v
Good Int         _        = ⊤
Good Float       _        = ⊤
Good Str         _        = ⊤
Good Buffer      _        = ⊤

-- A good computation: a prefix family whose value is good at every budget.
GoodT B m = PrefixFamily m × (∀ k → Good B (valueT m k))

------------------------------------------------------------------------
-- A PURE value is good.
--
-- `inject` lifts `Val.⟦A⟧` into the monadic domain, and everything it builds
-- is effect-free: closures return `returnT`, and a ν emits `[]` at every
-- layer. Needed by every leaf whose value comes from the pure semantics
-- (`SigOp`'s `semM`, and the whole `eval`-backed tail of `evalᴰ`).
------------------------------------------------------------------------

mutual
  -- `forceᵈ (injectν v)` IS `returnT (mapInjectν …)`, so the prefix-family
  -- half is `returnT-pf`; the layer half recurses. Corecursive, so the map is
  -- inlined (D062) rather than routed through a defined function.
  injectν-Good : ∀ {F : SFunctor} (v : νS F) → Goodν (injectν v)
  force-pf   (injectν-Good v)     = returnT-pf _
  force-good (injectν-Good {F} v) k = injectν-layer F F (unfoldS v)

  injectν-layer : ∀ (F G : SFunctor) (x : ⟦ G ⟧SF (νS F))
                → GoodLayer F G (mapInjectν F G x)
  injectν-layer F (SK B)     x        = tt
  injectν-layer F SId        v        = injectν-Good v
  injectν-layer F (G₁ S⊕ G₂) (inj₁ x) = injectν-layer F G₁ x
  injectν-layer F (G₁ S⊕ G₂) (inj₂ y) = injectν-layer F G₂ y
  injectν-layer F (G₁ S⊗ G₂) (x , y)  = (injectν-layer F G₁ x , injectν-layer F G₂ y)

-- A computation whose trace is CONSTANTLY EMPTY is a prefix family, and all
-- three conditions are immediate: `length [] ≤ k` is `z≤n`, saturation compares
-- two identical pairs, and coherence extends `[]` by `[]`.
--
-- This is the shape of `evalᴰ`'s `eval`-backed fallback
-- (DenotTrace.agda:202) at every constructor whose `rec-trace-D` is `[]` —
-- `In`, `out-μ` and `const` (:206, :208, :230).
const-empty-pf : ∀ {X : Set} (v : X) → PrefixFamily {X} (mkT (λ _ → []) false v)
const-empty-pf v = prefixFamily (λ k → z≤n) (λ k _ → refl) (λ k → ([] , refl))

inject-Good : ∀ (A : Type) (v : Val.⟦ A ⟧) → Good A (inject {A} v)
inject-Good Unit        v        = tt
inject-Good Void        ()
inject-Good (A * B)     (a , b)  = (inject-Good A a , inject-Good B b)
inject-Good (A + B)     (inj₁ a) = inject-Good A a
inject-Good (A + B)     (inj₂ b) = inject-Good B b
inject-Good (A ⇒[ mk-kind Zero π ] B) pf = λ u  → (returnT-pf _ , λ k → inject-Good B _)
inject-Good (A ⇒[ mk-kind One  π ] B) pf = λ a _ → (returnT-pf _ , λ k → inject-Good B _)
inject-Good (A ⇒[ mk-kind Many π ] B) pf = λ a _ → (returnT-pf _ , λ k → inject-Good B _)
inject-Good (μ-type F)  v        = tt
inject-Good (ν-type F)  v        = injectν-Good v
inject-Good Int         v        = tt
inject-Good Float       v        = tt
inject-Good Str         v        = tt
inject-Good Buffer      v        = tt

------------------------------------------------------------------------
-- THE theorem: `evalᴰ` lands in the prefix-family class.
--
-- Induction on the IR, with `Good` carrying the hypothesis through closures.
-- The `returnT`-shaped constructors are `returnT-pf`; `_∘_` and `⟨_,_⟩` are
-- `>>=T-pf`; `curry`/`apply` are where the arrow clause of `Good` is used,
-- one to establish it and one to consume it.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- THE REMAINING OBLIGATIONS, ONE NAME EACH.
--
-- This block used to be a SINGLE postulate:
--
--     postulate evalᴰ-good-schemes : ∀ {X : Set} → X
--
-- A postulate inhabiting EVERY type is not a scaffold. It is `⊥` under another
-- name, and `evalᴰ-good` fell through to it for every recursion scheme, so
-- `FlatFromObs` (which imports `evalᴰ-good` and applies it) carried it into the
-- apex cone. Machine-checked with two probes: `boom : ⊥ = evalᴰ-good-schemes`
-- typechecked, and so did the same ⊥ alongside an import of `Once.Certified`.
-- Every proof under the apex was vacuous while it stood.
--
-- Each obligation below is now its own NAMED statement at its own constructor.
-- A named postulate can still be FALSE — that is what the emptiness probes are
-- for — but it can only prove the one thing it says, so a false one falsifies
-- its own clause instead of the entire development.
--
-- `Cata` is known to FAIL `bounded` as written: its trace algebra hands every
-- layer the full budget and concatenates (`cata-ev-algᴰ`), the same defect
-- `events-Fᵇ` fixed on the ana side. Naming it separately is what lets that be
-- true of `Cata` alone.
--
-- (`free-heap` was in this list and is gone — the constructor was removed.)
------------------------------------------------------------------------

postulate


  evalᴰ-good-Cata : ∀ (fmt : TargetNum) {F} (wf : WellFormedFI F) {E A}
                    (alg : IR (E IT.* IT.⟦ F ⟧TI A) A) (a : ⟦ E IT.* IT.μ-type F ⟧ᴰᴵ)
                  → Good ⌈ E IT.* IT.μ-type F ⌉ a
                  → GoodT ⌈ A ⌉ (evalᴰ fmt (Cata wf alg) a)

  evalᴰ-good-Para : ∀ (fmt : TargetNum) {F} (wf : WellFormedFI F) {A}
                    (alg : IR (IT.⟦ F ⟧TI (IT.μ-type F IT.* A)) A) (a : ⟦ IT.μ-type F ⟧ᴰᴵ)
                  → Good ⌈ IT.μ-type F ⌉ a
                  → GoodT ⌈ A ⌉ (evalᴰ fmt (Para wf alg) a)

  evalᴰ-good-Out : ∀ (fmt : TargetNum) {F} (wf : WellFormedFI F)
                   (a : ⟦ IT.ν-type F ⟧ᴰᴵ)
                 → Good ⌈ IT.ν-type F ⌉ a
                 → GoodT ⌈ (IT.⟦ F ⟧TI (IT.ν-type F)) ⌉ (evalᴰ fmt (Out wf) a)

  evalᴰ-good-in-ν : ∀ (fmt : TargetNum) {F} (wf : WellFormedFI F)
                    (a : ⟦ (IT.⟦ F ⟧TI (IT.ν-type F)) ⟧ᴰᴵ)
                  → Good ⌈ (IT.⟦ F ⟧TI (IT.ν-type F)) ⌉ a
                  → GoodT ⌈ IT.ν-type F ⌉ (evalᴰ fmt (in-ν wf) a)

  evalᴰ-good-Ana : ∀ (fmt : TargetNum) {F} (wf : WellFormedFI F) {A}
                   (coalg : IR A (IT.⟦ F ⟧TI A)) (a : ⟦ A ⟧ᴰᴵ)
                 → Good ⌈ A ⌉ a
                 → GoodT ⌈ IT.ν-type F ⌉ (evalᴰ fmt (Ana wf coalg) a)

  evalᴰ-good-Hylo : ∀ (fmt : TargetNum) {F G} (wfF : WellFormedFI F) (wfG : WellFormedFI G) {B}
                    (alg : IR (IT.⟦ F ⟧TI B) B) (t : NatTr G F) (a : ⟦ IT.μ-type G ⟧ᴰᴵ)
                  → Good ⌈ IT.μ-type G ⌉ a
                  → GoodT ⌈ B ⌉ (evalᴰ fmt (Hylo wfF wfG alg t) a)

  evalᴰ-good-Fuse : ∀ (fmt : TargetNum) {F G} (wfF : WellFormedFI F) (wfG : WellFormedFI G) {B}
                    (alg : IR (IT.⟦ F ⟧TI B) B) (t : NatTr G F) (a : ⟦ IT.μ-type G ⟧ᴰᴵ)
                  → Good ⌈ IT.μ-type G ⌉ a
                  → GoodT ⌈ B ⌉ (evalᴰ fmt (Fuse wfF wfG alg t) a)


  evalᴰ-good-SigOp : ∀ (fmt : TargetNum) {A B : Type} (si : SigOpInfo A B)
                     (a : ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                   → Good ⌈ ⌊ A ⌋ ⌉ a
                   → GoodT ⌈ ⌊ B ⌋ ⌉ (evalᴰ fmt (SigOp si) a)

evalᴰ-good : ∀ (fmt : TargetNum) {A B : IRTy} (ir : IR A B) (a : ⟦ A ⟧ᴰᴵ)
           → Good ⌈ A ⌉ a → GoodT ⌈ B ⌉ (evalᴰ fmt ir a)
evalᴰ-good fmt id        a ga = (returnT-pf a , λ k → ga)
evalᴰ-good fmt fst       p ga = (returnT-pf _ , λ k → proj₁ ga)
evalᴰ-good fmt snd       p ga = (returnT-pf _ , λ k → proj₂ ga)
evalᴰ-good fmt inl       a ga = (returnT-pf _ , λ k → ga)
evalᴰ-good fmt inr       b gb = (returnT-pf _ , λ k → gb)
evalᴰ-good fmt terminal  _ _  = (returnT-pf _ , λ k → tt)
evalᴰ-good fmt initial   ()
-- `case` dispatches to a sub-morphism; the payload's goodness comes straight
-- from the scrutinee's.
evalᴰ-good fmt (case f g) (inj₁ a) ga = evalᴰ-good fmt f a ga
evalᴰ-good fmt (case f g) (inj₂ b) gb = evalᴰ-good fmt g b gb
-- `curry` ESTABLISHES the arrow clause: the closure is good because the body
-- is, for every good argument.
evalᴰ-good fmt (curry f) a ga =
  (returnT-pf _ , λ k b gb → evalᴰ-good fmt f (a , b) (ga , gb))
-- `apply` CONSUMES it: the pair carries a good closure and a good argument.
evalᴰ-good fmt apply p ga = proj₁ ga (proj₂ p) (proj₂ ga)
-- Composition: `>>=T-pf` with the continuation hypothesis at exactly the
-- values `f` produces — which is why that hypothesis had to be weakened.
evalᴰ-good fmt (_∘_ {A} {B} {C} g f) a ga =
  -- plan 0.97: the budget on the right is now FREE — `valueT` ignores it —
  -- so it has to be named rather than inferred.
  ( >>=T-pf (evalᴰ fmt f a) (evalᴰ fmt g) (proj₁ ihf) (λ k → proj₁ (ihg k))
  , λ k → proj₂ (ihg k) 0 )
  where
    ihf : GoodT ⌈ B ⌉ (evalᴰ fmt f a)
    ihf = evalᴰ-good fmt f a ga

    ihg : ∀ k → GoodT ⌈ C ⌉ (evalᴰ fmt g (valueT (evalᴰ fmt f a) k))
    ihg k = evalᴰ-good fmt g (valueT (evalᴰ fmt f a) k) (proj₂ ihf k)

-- Pairing: two nested binds over the SAME argument, closed by `returnT`.
evalᴰ-good fmt (⟨_,_⟩ {A} {B} {C} f g) a ga =
  ( >>=T-pf (evalᴰ fmt f a)
      (λ b → evalᴰ fmt g a >>=T λ c → returnT (b , c)) (proj₁ ihf)
      (λ k → >>=T-pf (evalᴰ fmt g a)
               (λ c → returnT (valueT (evalᴰ fmt f a) k , c)) (proj₁ ihg)
               (λ j → returnT-pf _))
  , λ k → (proj₂ ihf 0 , proj₂ ihg 0) )
  where
    ihf : GoodT ⌈ B ⌉ (evalᴰ fmt f a)
    ihf = evalᴰ-good fmt f a ga

    ihg : GoodT ⌈ C ⌉ (evalᴰ fmt g a)
    ihg = evalᴰ-good fmt g a ga

evalᴰ-good fmt (In {F} wf) a ga = (const-empty-pf _ , λ k → inject-Good ⌈ IT.μ-type F ⌉ (eval fmt (In wf) (forget a)))
evalᴰ-good fmt (out-μ {F} wf) a ga = (const-empty-pf _ , λ k → inject-Good ⌈ (IT.⟦ F ⟧TI (IT.μ-type F)) ⌉ (eval fmt (out-μ wf) (forget a)))
evalᴰ-good fmt (Cata wf alg)       a ga = evalᴰ-good-Cata  fmt wf alg a ga
evalᴰ-good fmt (Para wf alg)       a ga = evalᴰ-good-Para  fmt wf alg a ga
evalᴰ-good fmt (Out wf)            a ga = evalᴰ-good-Out   fmt wf a ga
evalᴰ-good fmt (in-ν wf)           a ga = evalᴰ-good-in-ν  fmt wf a ga
evalᴰ-good fmt (Ana wf coalg)      a ga = evalᴰ-good-Ana   fmt wf coalg a ga
evalᴰ-good fmt (Hylo wfF wfG alg t) a ga = evalᴰ-good-Hylo fmt wfF wfG alg t a ga
evalᴰ-good fmt (Fuse wfF wfG alg t) a ga = evalᴰ-good-Fuse fmt wfF wfG alg t a ga
evalᴰ-good fmt (const {A} fits v) a ga = (const-empty-pf _ , λ k → inject-Good ⌈ A ⌉ (eval fmt (const fits v) (forget a)))
evalᴰ-good fmt (SigOp si)          a ga = evalᴰ-good-SigOp fmt si a ga
