-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Iterative — SPEC. The computation domain of a program that
-- may RUN FOREVER (D311, plan 0.117 C1): the free COMPLETELY ITERATIVE monad
-- on the call/halt signature (Aczel–Adámek–Milius–Velebil).
--
-- `T` (`TraceMonad`) is the INITIAL algebra of `Y ↦ X + Σ Y` — finite trees,
-- an effectful computation that returns. `T∞` is the FINAL coalgebra of the
-- SAME functor: the same three nodes (`ret`, `call`, `halt`), possibly
-- infinitely deep. There is NO silent step (no `Tau`): every node is either
-- the end or an observable event, so every `T∞` tree is PRODUCTIVE by the
-- shape of its functor, and its first `n` events are computed by a total
-- function of `n` (`events∞`, D058's observable).
--
-- Equality of `T∞` trees is BISIMILARITY (`TreeEq∞`), never `≡` (D201: no
-- bisimulation-to-equality axiom).
------------------------------------------------------------------------

module Once.Spec.Iterative where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)

open import Once.Spec.Word using (Carrier)
import Once.Spec.Value Carrier Carrier as V
open import Once.Spec.Event using (SigOpEvent)
open import Once.Denotation.TraceMonad
  using (T; ret; call; halt; CallOp; HaltOp; Interp; callAnswer; callEvent; haltEvent; unlinkedOp)
open CallOp using (cdom; ccod)
open HaltOp using (hdom)

------------------------------------------------------------------------
-- One layer, and the tree
------------------------------------------------------------------------

-- A layer of the tree with the rest at `R`: the three nodes of `T`.
data T∞F (X R : Set) : Set where
  ret∞  : X → T∞F X R
  call∞ : (o : CallOp) → V.⟦ cdom o ⟧ → (V.⟦ ccod o ⟧ → R) → T∞F X R
  halt∞ : (o : HaltOp) → V.⟦ hdom o ⟧ → T∞F X R

record T∞ (X : Set) : Set where
  coinductive
  field force : T∞F X (T∞ X)
open T∞

------------------------------------------------------------------------
-- The monad
------------------------------------------------------------------------

return∞ : ∀ {X} → X → T∞ X
force (return∞ x) = ret∞ x

infixl 1 _>>=∞_
_>>=∞_ : ∀ {X Y} → T∞ X → (X → T∞ Y) → T∞ Y
bind∞F : ∀ {X Y} → T∞F X (T∞ X) → (X → T∞ Y) → T∞F Y (T∞ Y)
force (m >>=∞ k) = bind∞F (force m) k
bind∞F (ret∞ x)      k = force (k x)
bind∞F (call∞ o a c) k = call∞ o a (λ b → c b >>=∞ k)
bind∞F (halt∞ o a)   k = halt∞ o a

------------------------------------------------------------------------
-- Every finite tree is one: `T ↪ T∞`, a monad morphism (up to `≈∞`).
------------------------------------------------------------------------

embed : ∀ {X} → T X → T∞ X
force (embed (ret x))      = ret∞ x
force (embed (call o a k)) = call∞ o a (λ b → embed (k b))
force (embed (halt o a))   = halt∞ o a

------------------------------------------------------------------------
-- Bisimilarity: the same nodes, layer by layer, forever; the values at the
-- leaves related by `R`.
------------------------------------------------------------------------

data NodeEq {X R R′ : Set} (Rx : X → X → Set) (Rr : R → R′ → Set) : T∞F X R → T∞F X R′ → Set where
  ret≈∞  : ∀ {x y} → Rx x y → NodeEq Rx Rr (ret∞ x) (ret∞ y)
  call≈∞ : ∀ {o a k k′} → (∀ b → Rr (k b) (k′ b)) → NodeEq Rx Rr (call∞ o a k) (call∞ o a k′)
  halt≈∞ : ∀ {o a} → NodeEq Rx Rr (halt∞ o a) (halt∞ o a)

record TreeEq∞ {X : Set} (Rx : X → X → Set) (m m′ : T∞ X) : Set where
  coinductive
  field force≈ : NodeEq Rx (TreeEq∞ Rx) (force m) (force m′)
open TreeEq∞

------------------------------------------------------------------------
-- THE OBSERVABLE (D058): the first `n` events of a run against an
-- interpretation, from a history. Total in `n`: each event costs one, and
-- every node is an event or the end — there is nothing to wait on.
------------------------------------------------------------------------

events∞  : ∀ {X} → Interp → List SigOpEvent → T∞ X → ℕ → List SigOpEvent
eventsF  : ∀ {X} → Interp → List SigOpEvent → T∞F X (T∞ X) → ℕ → List SigOpEvent
eventsC  : ∀ {X} → Interp → List SigOpEvent → (o : CallOp) → V.⟦ cdom o ⟧ → (V.⟦ ccod o ⟧ → T∞ X)
         → Maybe V.⟦ ccod o ⟧ → ℕ → List SigOpEvent
events∞ ι h m zero    = []
events∞ ι h m (suc n) = eventsF ι h (force m) n
eventsF ι h (ret∞ x)      n = []
eventsF ι h (halt∞ o a)   n = [ haltEvent o a ]
eventsF ι h (call∞ o a k) n = eventsC ι h o a k (callAnswer ι h o a) n
eventsC ι h o a k (just b) n = callEvent o a ∷ events∞ ι (h ++ [ callEvent o a ]) (k b) n
eventsC ι h o a k nothing  n = [ haltEvent unlinkedOp tt ]

------------------------------------------------------------------------
-- Streams whose layers may take forever to arrive (`ν-type F prod`): a
-- layer is a `T∞` computation — every event of it observable, none silent.
-- Mirrors `νᵈ` (`ValueDomain`), with `T∞` for `T`; D062's rule holds: the
-- maps are written by hand so each corecursive call sits under a copattern.
------------------------------------------------------------------------

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)

record ν∞ (H : SFunctor) : Set where
  coinductive
  field force∞ : T∞ (⟦ H ⟧SF (ν∞ H))
open ν∞

ana∞     : ∀ (H : SFunctor) {A : Set} → (A → T∞ (⟦ H ⟧SF A)) → A → ν∞ H
anaTree∞ : ∀ (H : SFunctor) {A : Set} → (A → T∞ (⟦ H ⟧SF A)) → T∞ (⟦ H ⟧SF A) → T∞ (⟦ H ⟧SF (ν∞ H))
anaLayer∞ : ∀ (H : SFunctor) {A : Set} → (A → T∞ (⟦ H ⟧SF A))
          → T∞F (⟦ H ⟧SF A) (T∞ (⟦ H ⟧SF A)) → T∞F (⟦ H ⟧SF (ν∞ H)) (T∞ (⟦ H ⟧SF (ν∞ H)))
mapAna∞  : ∀ (H G : SFunctor) {A : Set} → (A → T∞ (⟦ H ⟧SF A)) → ⟦ G ⟧SF A → ⟦ G ⟧SF (ν∞ H)
force∞ (ana∞ H c a) = anaTree∞ H c (c a)
force (anaTree∞ H c m) = anaLayer∞ H c (force m)
anaLayer∞ H c (ret∞ l)      = ret∞ (mapAna∞ H H c l)
anaLayer∞ H c (call∞ o a k) = call∞ o a (λ b → anaTree∞ H c (k b))
anaLayer∞ H c (halt∞ o a)   = halt∞ o a
mapAna∞ H (SK B)     c x        = x
mapAna∞ H SId        c a        = ana∞ H c a
mapAna∞ H (G₁ S⊕ G₂) c (inj₁ x) = inj₁ (mapAna∞ H G₁ c x)
mapAna∞ H (G₁ S⊕ G₂) c (inj₂ y) = inj₂ (mapAna∞ H G₂ c y)
mapAna∞ H (G₁ S⊗ G₂) c (x , y)  = mapAna∞ H G₁ c x , mapAna∞ H G₂ c y

------------------------------------------------------------------------
-- The functor action, and sequencing a layer of computations (`seqF`'s twin).
------------------------------------------------------------------------

open import Once.Spec.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.Semantics.Machine using (⟦_⟧F)

fmap∞ : ∀ {X Y} → (X → Y) → T∞ X → T∞ Y
fmap∞ f m = m >>=∞ λ x → return∞ (f x)

seqF∞ : ∀ (G : Functor) {X : Set} → ⟦ G ⟧F (T∞ X) → T∞ (⟦ G ⟧F X)
seqF∞ (K A)   x        = return∞ x
seqF∞ Id      m        = m
seqF∞ (G ⊕ H) (inj₁ x) = fmap∞ inj₁ (seqF∞ G x)
seqF∞ (G ⊕ H) (inj₂ y) = fmap∞ inj₂ (seqF∞ H y)
seqF∞ (G ⊗ H) (x , y)  = seqF∞ G x >>=∞ λ u → seqF∞ H y >>=∞ λ v → return∞ (u , v)
