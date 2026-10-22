-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Iterative — SPEC. The computation domain of a program that
-- may RUN FOREVER: the coinductive RESUMPTION monad over the finite trees
-- (D317, `Spec.Effect`'s `T∞`).
--
-- `T` (`TraceMonad`) is the INITIAL algebra of `Y ↦ X + Σ Y` — finite trees,
-- an effectful computation that returns (a BLOCK). `T∞ X = νY. T (X + Y)`: a
-- run is a block that ends with the result or with the rest of the run. The
-- end of a block is a SILENT step — what a loop's round that calls nothing
-- is — so a run may go on forever without another call, and `T∞` has no
-- total "first n events" observable: a run's observation is its TRACE
-- (`Once.Denotation.TraceTr`), compared by weak bisimilarity (D317).
--
-- Equality of `T∞` runs is BISIMILARITY (`TreeEq∞`), never `≡` (D201: no
-- bisimulation-to-equality axiom).
------------------------------------------------------------------------

module Once.Internal.Iterative where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Once.Spec.Word using (Carrier)
import Once.Internal.Value Carrier Carrier as V
open import Once.Internal.Event using (SigOpEvent)
open import Once.Internal.Trace
  using (T; ret; call; halt; CallOp; HaltOp; Interp; callAnswer; callEvent; haltEvent; unlinkedOp)
open CallOp using (cdom; ccod)
open HaltOp using (hdom)

------------------------------------------------------------------------
-- The run
------------------------------------------------------------------------

record T∞ (X : Set) : Set where
  coinductive
  field force : T (X ⊎ T∞ X)
open T∞

------------------------------------------------------------------------
-- The monad
------------------------------------------------------------------------

return∞ : ∀ {X} → X → T∞ X
force (return∞ x) = ret (inj₁ x)

infixl 1 _>>=∞_
_>>=∞_    : ∀ {X Y} → T∞ X → (X → T∞ Y) → T∞ Y
bindBlock : ∀ {X Y} → T (X ⊎ T∞ X) → (X → T∞ Y) → T (Y ⊎ T∞ Y)
force (m >>=∞ k) = bindBlock (force m) k
bindBlock (ret (inj₁ x)) k = force (k x)
bindBlock (ret (inj₂ m)) k = ret (inj₂ (m >>=∞ k))
bindBlock (call o a c)   k = call o a (λ b → bindBlock (c b) k)
bindBlock (halt o a)     k = halt o a

------------------------------------------------------------------------
-- Every finite tree is one block: `T ↪ T∞`, a monad morphism (up to `≈∞`).
------------------------------------------------------------------------

embedBlock : ∀ {X Y} → T X → T (X ⊎ Y)
embedBlock (ret x)      = ret (inj₁ x)
embedBlock (call o a k) = call o a (λ b → embedBlock (k b))
embedBlock (halt o a)   = halt o a

embed : ∀ {X} → T X → T∞ X
force (embed m) = embedBlock m

------------------------------------------------------------------------
-- THE LOOP (D317): a round is a block that ends with the result or the next
-- state; the loop is the anamorphism into `T∞`.
------------------------------------------------------------------------

loop      : ∀ {A B : Set} → (A → T (B ⊎ A)) → A → T∞ B
loopBlock : ∀ {A B : Set} → (A → T (B ⊎ A)) → T (B ⊎ A) → T (B ⊎ T∞ B)
force (loop c a) = loopBlock c (c a)
loopBlock c (ret (inj₁ b)) = ret (inj₁ b)
loopBlock c (ret (inj₂ a)) = ret (inj₂ (loop c a))
loopBlock c (call o x k)   = call o x (λ v → loopBlock c (k v))
loopBlock c (halt o x)     = halt o x

------------------------------------------------------------------------
-- A run that returns AT ONCE (its first block is `ret`: a constructor, a
-- destructor, a suspension), and its value — read without an Interpretation.
------------------------------------------------------------------------

NowB : ∀ {X} → T (X ⊎ T∞ X) → Set
NowB (ret (inj₁ _)) = ⊤
NowB (ret (inj₂ _)) = ⊥
NowB (call _ _ _)   = ⊥
NowB (halt _ _)     = ⊥

nowB : ∀ {X} (b : T (X ⊎ T∞ X)) → {NowB b} → X
nowB (ret (inj₁ x)) = x

Now : ∀ {X} → T∞ X → Set
Now m = NowB (force m)

valueNow : ∀ {X} (m : T∞ X) → {Now m} → X
valueNow m {p} = nowB (force m) {p}

------------------------------------------------------------------------
-- ITERATION over rounds that need not stop (the IR's loop, plan 0.119 D5):
-- the IR is ungraded, so a round is a `T∞` computation; a round's end that
-- continues is a silent step. `loop` is the instance at a finite round
-- (`iter∞ (embed ∘ c)` has the same blocks).
------------------------------------------------------------------------

iterRun   : ∀ {A B : Set} → (A → T∞ (B ⊎ A)) → T∞ (B ⊎ A) → T∞ B
iterBlock : ∀ {A B : Set} → (A → T∞ (B ⊎ A)) → T ((B ⊎ A) ⊎ T∞ (B ⊎ A)) → T (B ⊎ T∞ B)
force (iterRun f m) = iterBlock f (force m)
iterBlock f (ret (inj₁ (inj₁ b))) = ret (inj₁ b)
iterBlock f (ret (inj₁ (inj₂ a))) = ret (inj₂ (iterRun f (f a)))
iterBlock f (ret (inj₂ m))        = ret (inj₂ (iterRun f m))
iterBlock f (call o x k)          = call o x (λ v → iterBlock f (k v))
iterBlock f (halt o x)            = halt o x

iter∞ : ∀ {A B : Set} → (A → T∞ (B ⊎ A)) → A → T∞ B
iter∞ f a = iterRun f (f a)

------------------------------------------------------------------------
-- Bisimilarity: the same blocks, step by step, forever; the results related
-- by `R`.
------------------------------------------------------------------------

data BlockEq {Z : Set} (R : Z → Z → Set) : T Z → T Z → Set where
  ret≈  : ∀ {z z′} → R z z′ → BlockEq R (ret z) (ret z′)
  call≈ : ∀ {o a k k′} → (∀ b → BlockEq R (k b) (k′ b)) → BlockEq R (call o a k) (call o a k′)
  halt≈ : ∀ {o a} → BlockEq R (halt o a) (halt o a)

data StepEq {X Y : Set} (Rx : X → X → Set) (Ry : Y → Y → Set) : X ⊎ Y → X ⊎ Y → Set where
  done≈ : ∀ {x x′} → Rx x x′ → StepEq Rx Ry (inj₁ x) (inj₁ x′)
  next≈ : ∀ {y y′} → Ry y y′ → StepEq Rx Ry (inj₂ y) (inj₂ y′)

record TreeEq∞ {X : Set} (Rx : X → X → Set) (m m′ : T∞ X) : Set where
  coinductive
  field force≈ : BlockEq (StepEq Rx (TreeEq∞ Rx)) (force m) (force m′)
open TreeEq∞

------------------------------------------------------------------------
-- The functor action, and sequencing a layer of computations (`seqF`'s twin).
------------------------------------------------------------------------

open import Once.Spec.Type using (K; Id; _⊕_; _⊗_)

open import Once.Internal.Type using (Functor)
open import Once.Internal.Value Carrier Carrier using (⟦_⟧F)

fmap∞ : ∀ {X Y} → (X → Y) → T∞ X → T∞ Y
fmap∞ f m = m >>=∞ λ x → return∞ (f x)

seqF∞ : ∀ (G : Functor) {X : Set} → ⟦ G ⟧F (T∞ X) → T∞ (⟦ G ⟧F X)
seqF∞ (K A)   x        = return∞ x
seqF∞ Id      m        = m
seqF∞ (G ⊕ H) (inj₁ x) = fmap∞ inj₁ (seqF∞ G x)
seqF∞ (G ⊕ H) (inj₂ y) = fmap∞ inj₂ (seqF∞ H y)
seqF∞ (G ⊗ H) (x , y)  = seqF∞ G x >>=∞ λ u → seqF∞ H y >>=∞ λ v → return∞ (u , v)
