-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Guarded — SPEC. The computations whose FIRST node is an event
-- (D311, plan 0.117 C2): the grade `eff⁺`, the guard of guarded iteration.
--
-- `T⁺ X` is the IDEAL of the completely iterative monad `T∞` (D312): the
-- trees whose root is a call or a halt, never a bare result. It has no unit
-- (a value performs no event); `T∞` acts on it from the right (run a `T⁺`,
-- then any `T∞`: still an event first) and from the left into it (run any
-- `T∞`, then a `T⁺`: an event comes before the result, whichever path — a
-- tree of `T∞` has no silent node). It embeds into `T∞` (`forget⁺`). A
-- foreign operation's call, `call⁺ o a return∞`, is the generic effect — the
-- prototypical `T⁺` computation.
------------------------------------------------------------------------

module Once.Spec.Guarded where

open import Data.Unit using (tt)

open import Once.Spec.Word using (Carrier)
import Once.Spec.Value Carrier Carrier as V
open import Once.Spec.Trace using (CallOp; HaltOp)
open import Once.Spec.Iterative
  using (T∞; T∞F; ret∞; call∞; halt∞; return∞; _>>=∞_; module T∞)
open T∞ using (force)
open CallOp using (cdom; ccod)
open HaltOp using (hdom)

data T⁺ (X : Set) : Set where
  call⁺ : (o : CallOp) → V.⟦ cdom o ⟧ → (V.⟦ ccod o ⟧ → T∞ X) → T⁺ X
  halt⁺ : (o : HaltOp) → V.⟦ hdom o ⟧ → T⁺ X

-- The root of a guarded tree: an event.
root⁺ : ∀ {X} → T⁺ X → T∞F X (T∞ X)
root⁺ (call⁺ o a k) = call∞ o a k
root⁺ (halt⁺ o a)   = halt∞ o a

-- Every guarded tree is a tree.
forget⁺ : ∀ {X} → T⁺ X → T∞ X
force (forget⁺ m) = root⁺ m

-- `T∞` acting on the right: an event first, then anything.
infixl 1 _>>=⁺_
_>>=⁺_ : ∀ {X Y} → T⁺ X → (X → T∞ Y) → T⁺ Y
call⁺ o a k >>=⁺ f = call⁺ o a (λ b → k b >>=∞ f)
halt⁺ o a   >>=⁺ f = halt⁺ o a

-- …and on the left: anything, then an event first — so an event comes before
-- every result.
infixl 1 _⁺=<<_
bindF⁺ : ∀ {X Y} → T∞F X (T∞ X) → (X → T⁺ Y) → T⁺ Y
bindF⁺ (ret∞ x)      f = f x
bindF⁺ (call∞ o a k) f = call⁺ o a (λ b → k b >>=∞ λ x → forget⁺ (f x))
bindF⁺ (halt∞ o a)   f = halt⁺ o a

_⁺=<<_ : ∀ {X Y} → T∞ X → (X → T⁺ Y) → T⁺ Y
m ⁺=<< f = bindF⁺ (force m) f

fmap⁺ : ∀ {X Y} → (X → Y) → T⁺ X → T⁺ Y
fmap⁺ g m = m >>=⁺ λ x → return∞ (g x)

------------------------------------------------------------------------
-- Streams whose every forced layer begins with an event (`ν-type F eff⁺`):
-- `ν∞` with `T⁺` for `T∞` at each layer's root (D062's rule: the maps
-- written by hand).
------------------------------------------------------------------------

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)

record ν⁺ (H : SFunctor) : Set where
  coinductive
  field force⁺ : T⁺ (⟦ H ⟧SF (ν⁺ H))
open ν⁺

ana⁺      : ∀ (H : SFunctor) {A : Set} → (A → T⁺ (⟦ H ⟧SF A)) → A → ν⁺ H
anaRoot⁺  : ∀ (H : SFunctor) {A : Set} → (A → T⁺ (⟦ H ⟧SF A)) → T⁺ (⟦ H ⟧SF A) → T⁺ (⟦ H ⟧SF (ν⁺ H))
anaTree⁺  : ∀ (H : SFunctor) {A : Set} → (A → T⁺ (⟦ H ⟧SF A)) → T∞ (⟦ H ⟧SF A) → T∞ (⟦ H ⟧SF (ν⁺ H))
anaLayer⁺ : ∀ (H : SFunctor) {A : Set} → (A → T⁺ (⟦ H ⟧SF A))
          → T∞F (⟦ H ⟧SF A) (T∞ (⟦ H ⟧SF A)) → T∞F (⟦ H ⟧SF (ν⁺ H)) (T∞ (⟦ H ⟧SF (ν⁺ H)))
mapAna⁺   : ∀ (H G : SFunctor) {A : Set} → (A → T⁺ (⟦ H ⟧SF A)) → ⟦ G ⟧SF A → ⟦ G ⟧SF (ν⁺ H)
force⁺ (ana⁺ H c a) = anaRoot⁺ H c (c a)
anaRoot⁺ H c (call⁺ o a k) = call⁺ o a (λ b → anaTree⁺ H c (k b))
anaRoot⁺ H c (halt⁺ o a)   = halt⁺ o a
force (anaTree⁺ H c m) = anaLayer⁺ H c (force m)
anaLayer⁺ H c (ret∞ l)      = ret∞ (mapAna⁺ H H c l)
anaLayer⁺ H c (call∞ o a k) = call∞ o a (λ b → anaTree⁺ H c (k b))
anaLayer⁺ H c (halt∞ o a)   = halt∞ o a
mapAna⁺ H (SK B)     c x        = x
mapAna⁺ H SId        c a        = ana⁺ H c a
mapAna⁺ H (G₁ S⊕ G₂) c (inj₁ x) = inj₁ (mapAna⁺ H G₁ c x)
mapAna⁺ H (G₁ S⊕ G₂) c (inj₂ y) = inj₂ (mapAna⁺ H G₂ c y)
mapAna⁺ H (G₁ S⊗ G₂) c (x , y)  = mapAna⁺ H G₁ c x , mapAna⁺ H G₂ c y

------------------------------------------------------------------------
-- GUARDED ITERATION (D311 §3): a step that performs an event before it
-- answers, iterated — the loop of a server. `iter∞ f a` runs `f a`; its first
-- node is an event, so the tree grows by at least one node before the next
-- round, and the iteration is a productive `T∞` tree however long it runs. A
-- `inj₁ b` ends the loop with `b`; an `inj₂ a′` runs the next round from `a′`.
------------------------------------------------------------------------

open import Data.Sum using (_⊎_)

iter∞      : ∀ {A B : Set} → (A → T⁺ (B ⊎ A)) → A → T∞ B
iterRoot∞  : ∀ {A B : Set} → (A → T⁺ (B ⊎ A)) → T⁺ (B ⊎ A) → T∞F B (T∞ B)
iterTree∞  : ∀ {A B : Set} → (A → T⁺ (B ⊎ A)) → T∞ (B ⊎ A) → T∞ B
iterLayer∞ : ∀ {A B : Set} → (A → T⁺ (B ⊎ A)) → T∞F (B ⊎ A) (T∞ (B ⊎ A)) → T∞F B (T∞ B)
force (iter∞ f a) = iterRoot∞ f (f a)
iterRoot∞ f (call⁺ o x k) = call∞ o x (λ r → iterTree∞ f (k r))
iterRoot∞ f (halt⁺ o x)   = halt∞ o x
force (iterTree∞ f m) = iterLayer∞ f (force m)
iterLayer∞ f (ret∞ (inj₁ b)) = ret∞ b
iterLayer∞ f (ret∞ (inj₂ a)) = iterRoot∞ f (f a)
iterLayer∞ f (call∞ o x k)   = call∞ o x (λ r → iterTree∞ f (k r))
iterLayer∞ f (halt∞ o x)     = halt∞ o x
