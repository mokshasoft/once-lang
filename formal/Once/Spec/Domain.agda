{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Domain — what a value of each type is.
--
-- One value domain. A pure arrow is a total function, an effectful one a
-- function into its grade's monad (`Spec.Effect`); an erased arrow takes no
-- argument. `μ F` is the initial algebra of `F`'s polynomial functor, `ν F π`
-- the final coalgebra of `M π ∘ F`.
--
-- With it: the fold and the unfold on the polynomial functors (the fold runs
-- a product layer left first), the action of `ν` on the monad morphisms, and
-- the conversion each subtyping derivation means. Everything is stated at a
-- closed instance `σ` of the type variables.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Spec.Domain (Σ : Signature) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Once.Spec.Grade using (Purity; pure; act; eff⁺; eff; mk-kind; Zero; One; Many; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-g; ⊑-ge; ⊑-eff)
open import Once.Spec.Type
  using (Ty; Type; Fun; var; Unit; Void; _*_; _+_; _⇒[_]_; μ; ν; Int; Float; K; Id; _⊕_; _⊗_; ⟦_⟧F; TySub; _⟨_⟩; _⟨_⟩F)
open import Once.Spec.Sub
open import Once.Spec.Word using (Carrier)
open import Once.Spec.Signature using (BTy; unit; void; int; float; ⌜_⌝; ⟦_⟧ᵇ; Layer; call)
import Once.Spec.Signature as S
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; inS)
open import Once.Spec.Effect Σ
  using (M; return; bind; fmap; sub; T; roll; done; node; returnT; T∞; embed;
         T⁺; call⁺; forget⁺; νM; Step; module T∞; module νM)
open T∞ using (force)
open νM using (outν)

------------------------------------------------------------------------
-- The value domain
------------------------------------------------------------------------

⟦_⟧ᵛ : Type → Set
code : Fun 0 → SFunctor
⟦ var () ⟧ᵛ
⟦ Unit ⟧ᵛ  = ⊤
⟦ Void ⟧ᵛ  = ⊥
⟦ A * B ⟧ᵛ = ⟦ A ⟧ᵛ × ⟦ B ⟧ᵛ
⟦ A + B ⟧ᵛ = ⟦ A ⟧ᵛ ⊎ ⟦ B ⟧ᵛ
⟦ A ⇒[ mk-kind Zero π ] B ⟧ᵛ = ⊤ → M π ⟦ B ⟧ᵛ
⟦ A ⇒[ mk-kind One  π ] B ⟧ᵛ = ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ
⟦ A ⇒[ mk-kind Many π ] B ⟧ᵛ = ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ
⟦ μ F ⟧ᵛ   = μS (code F)
⟦ ν F π ⟧ᵛ = νM π (code F)
⟦ Int ⟧ᵛ   = Carrier
⟦ Float ⟧ᵛ = Carrier
code (K A)   = SK ⟦ A ⟧ᵛ
code Id      = SId
code (F ⊕ G) = code F S⊕ code G
code (F ⊗ G) = code F S⊗ code G

------------------------------------------------------------------------
-- A base type's values are its values as a type; a functor applied to a type
-- is the polynomial functor applied to its values
------------------------------------------------------------------------

module _ {m : ℕ} (σ : TySub m 0) where

  toB   : ∀ b → ⟦ ⌜ b ⌝ ⟨ σ ⟩ ⟧ᵛ → ⟦ b ⟧ᵇ
  fromB : ∀ b → ⟦ b ⟧ᵇ → ⟦ ⌜ b ⌝ ⟨ σ ⟩ ⟧ᵛ
  toB unit  x = x
  toB void  x = x
  toB int   x = x
  toB float x = x
  toB (a S.* b) (x , y)  = toB a x , toB b y
  toB (a S.+ b) (inj₁ x) = inj₁ (toB a x)
  toB (a S.+ b) (inj₂ y) = inj₂ (toB b y)
  fromB unit  x = x
  fromB void  x = x
  fromB int   x = x
  fromB float x = x
  fromB (a S.* b) (x , y)  = fromB a x , fromB b y
  fromB (a S.+ b) (inj₁ x) = inj₁ (fromB a x)
  fromB (a S.+ b) (inj₂ y) = inj₂ (fromB b y)

  toL   : ∀ (F : Fun m) (X : Ty m) → ⟦ ⟦ F ⟧F X ⟨ σ ⟩ ⟧ᵛ → ⟦ code (F ⟨ σ ⟩F) ⟧SF ⟦ X ⟨ σ ⟩ ⟧ᵛ
  fromL : ∀ (F : Fun m) (X : Ty m) → ⟦ code (F ⟨ σ ⟩F) ⟧SF ⟦ X ⟨ σ ⟩ ⟧ᵛ → ⟦ ⟦ F ⟧F X ⟨ σ ⟩ ⟧ᵛ
  toL (K A)   X x        = x
  toL Id      X x        = x
  toL (F ⊕ G) X (inj₁ x) = inj₁ (toL F X x)
  toL (F ⊕ G) X (inj₂ y) = inj₂ (toL G X y)
  toL (F ⊗ G) X (x , y)  = toL F X x , toL G X y
  fromL (K A)   X x        = x
  fromL Id      X x        = x
  fromL (F ⊕ G) X (inj₁ x) = inj₁ (fromL F X x)
  fromL (F ⊕ G) X (inj₂ y) = inj₂ (fromL G X y)
  fromL (F ⊗ G) X (x , y)  = fromL F X x , fromL G X y

------------------------------------------------------------------------
-- The fold: the algebra at each layer, the layer's recursive positions first,
-- left to right
------------------------------------------------------------------------

-- The algebra's grade has a unit (`pure ⊑π π`): a layer with no recursive
-- position runs nothing.
foldM  : ∀ π → pure ⊑π π → (G : SFunctor) {X : Set} → (⟦ G ⟧SF X → M π X) → μS G → M π X
layerM : ∀ π → pure ⊑π π → (G : SFunctor) (H : SFunctor) {X : Set} → (⟦ G ⟧SF X → M π X) → ⟦ H ⟧SF (μS G) → M π (⟦ H ⟧SF X)
foldM π e G alg (inS x) = bind π (layerM π e G G alg x) alg
layerM π e G (SK B)     alg x        = return e x
layerM π e G SId        alg x        = foldM π e G alg x
layerM π e G (H₁ S⊕ H₂) alg (inj₁ x) = fmap π inj₁ (layerM π e G H₁ alg x)
layerM π e G (H₁ S⊕ H₂) alg (inj₂ y) = fmap π inj₂ (layerM π e G H₂ alg y)
layerM π e G (H₁ S⊗ H₂) alg (x , y)  =
  bind π (layerM π e G H₁ alg x) λ u → bind π (layerM π e G H₂ alg y) λ v → return e (u , v)

------------------------------------------------------------------------
-- The unfold: each forced layer runs the coalgebra at its grade
------------------------------------------------------------------------

anaP   : ∀ (G : SFunctor) {X : Set} → (X → ⟦ G ⟧SF X) → X → νM pure G
mapP   : ∀ (G H : SFunctor) {X : Set} → (X → ⟦ G ⟧SF X) → ⟦ H ⟧SF X → ⟦ H ⟧SF (νM pure G)
outν (anaP G c x) = mapP G G c (c x)
mapP G (SK B)     c x        = x
mapP G SId        c x        = anaP G c x
mapP G (H₁ S⊕ H₂) c (inj₁ x) = inj₁ (mapP G H₁ c x)
mapP G (H₁ S⊕ H₂) c (inj₂ y) = inj₂ (mapP G H₂ c y)
mapP G (H₁ S⊗ H₂) c (x , y)  = mapP G H₁ c x , mapP G H₂ c y

anaA   : ∀ (G : SFunctor) {X : Set} → (X → T (⟦ G ⟧SF X)) → X → νM act G
treeA  : ∀ (G : SFunctor) {X : Set} → (X → T (⟦ G ⟧SF X)) → T (⟦ G ⟧SF X) → T (⟦ G ⟧SF (νM act G))
mapA   : ∀ (G H : SFunctor) {X : Set} → (X → T (⟦ G ⟧SF X)) → ⟦ H ⟧SF X → ⟦ H ⟧SF (νM act G)
outν (anaA G c x) = treeA G c (c x)
treeA G c (roll (done l))            = roll (done (mapA G G c l))
treeA G c (roll (node (call o a k))) = roll (node (call o a (λ b → treeA G c (k b))))
mapA G (SK B)     c x        = x
mapA G SId        c x        = anaA G c x
mapA G (H₁ S⊕ H₂) c (inj₁ x) = inj₁ (mapA G H₁ c x)
mapA G (H₁ S⊕ H₂) c (inj₂ y) = inj₂ (mapA G H₂ c y)
mapA G (H₁ S⊗ H₂) c (x , y)  = mapA G H₁ c x , mapA G H₂ c y

anaE   : ∀ (G : SFunctor) {X : Set} → (X → T∞ (⟦ G ⟧SF X)) → X → νM eff G
treeE  : ∀ (G : SFunctor) {X : Set} → (X → T∞ (⟦ G ⟧SF X)) → T∞ (⟦ G ⟧SF X) → T∞ (⟦ G ⟧SF (νM eff G))
stepE  : ∀ (G : SFunctor) {X : Set} → (X → T∞ (⟦ G ⟧SF X)) → Step (⟦ G ⟧SF X) (T∞ (⟦ G ⟧SF X)) → Step (⟦ G ⟧SF (νM eff G)) (T∞ (⟦ G ⟧SF (νM eff G)))
mapE   : ∀ (G H : SFunctor) {X : Set} → (X → T∞ (⟦ G ⟧SF X)) → ⟦ H ⟧SF X → ⟦ H ⟧SF (νM eff G)
outν (anaE G c x) = treeE G c (c x)
force (treeE G c m) = stepE G c (force m)
stepE G c (done l)            = done (mapE G G c l)
stepE G c (node (call o a k)) = node (call o a (λ b → treeE G c (k b)))
mapE G (SK B)     c x        = x
mapE G SId        c x        = anaE G c x
mapE G (H₁ S⊕ H₂) c (inj₁ x) = inj₁ (mapE G H₁ c x)
mapE G (H₁ S⊕ H₂) c (inj₂ y) = inj₂ (mapE G H₂ c y)
mapE G (H₁ S⊗ H₂) c (x , y)  = mapE G H₁ c x , mapE G H₂ c y

anaG   : ∀ (G : SFunctor) {X : Set} → (X → T⁺ (⟦ G ⟧SF X)) → X → νM eff⁺ G
rootG  : ∀ (G : SFunctor) {X : Set} → (X → T⁺ (⟦ G ⟧SF X)) → T⁺ (⟦ G ⟧SF X) → T⁺ (⟦ G ⟧SF (νM eff⁺ G))
treeG  : ∀ (G : SFunctor) {X : Set} → (X → T⁺ (⟦ G ⟧SF X)) → T∞ (⟦ G ⟧SF X) → T∞ (⟦ G ⟧SF (νM eff⁺ G))
stepG  : ∀ (G : SFunctor) {X : Set} → (X → T⁺ (⟦ G ⟧SF X)) → Step (⟦ G ⟧SF X) (T∞ (⟦ G ⟧SF X)) → Step (⟦ G ⟧SF (νM eff⁺ G)) (T∞ (⟦ G ⟧SF (νM eff⁺ G)))
mapG   : ∀ (G H : SFunctor) {X : Set} → (X → T⁺ (⟦ G ⟧SF X)) → ⟦ H ⟧SF X → ⟦ H ⟧SF (νM eff⁺ G)
outν (anaG G c x) = rootG G c (c x)
rootG G c (call⁺ (call o a k)) = call⁺ (call o a (λ b → treeG G c (k b)))
force (treeG G c m) = stepG G c (force m)
stepG G c (done l)            = done (mapG G G c l)
stepG G c (node (call o a k)) = node (call o a (λ b → treeG G c (k b)))
mapG G (SK B)     c x        = x
mapG G SId        c x        = anaG G c x
mapG G (H₁ S⊕ H₂) c (inj₁ x) = inj₁ (mapG G H₁ c x)
mapG G (H₁ S⊕ H₂) c (inj₂ y) = inj₂ (mapG G H₂ c y)
mapG G (H₁ S⊗ H₂) c (x , y)  = mapG G H₁ c x , mapG G H₂ c y

anaM : ∀ π (G : SFunctor) {X : Set} → (X → M π (⟦ G ⟧SF X)) → X → νM π G
anaM pure = anaP
anaM act  = anaA
anaM eff⁺ = anaG
anaM eff  = anaE

------------------------------------------------------------------------
-- ν on the monad morphisms: every layer converted
------------------------------------------------------------------------

νpa  : ∀ (G : SFunctor) → νM pure G → νM act G
lpa  : ∀ (G H : SFunctor) → ⟦ H ⟧SF (νM pure G) → ⟦ H ⟧SF (νM act G)
outν (νpa G v) = roll (done (lpa G G (outν v)))
lpa G (SK B)     x        = x
lpa G SId        v        = νpa G v
lpa G (H₁ S⊕ H₂) (inj₁ x) = inj₁ (lpa G H₁ x)
lpa G (H₁ S⊕ H₂) (inj₂ y) = inj₂ (lpa G H₂ y)
lpa G (H₁ S⊗ H₂) (x , y)  = lpa G H₁ x , lpa G H₂ y

νpe  : ∀ (G : SFunctor) → νM pure G → νM eff G
tpe  : ∀ (G : SFunctor) → ⟦ G ⟧SF (νM pure G) → T∞ (⟦ G ⟧SF (νM eff G))
lpe  : ∀ (G H : SFunctor) → ⟦ H ⟧SF (νM pure G) → ⟦ H ⟧SF (νM eff G)
outν (νpe G v) = tpe G (outν v)
force (tpe G l) = done (lpe G G l)
lpe G (SK B)     x        = x
lpe G SId        v        = νpe G v
lpe G (H₁ S⊕ H₂) (inj₁ x) = inj₁ (lpe G H₁ x)
lpe G (H₁ S⊕ H₂) (inj₂ y) = inj₂ (lpe G H₂ y)
lpe G (H₁ S⊗ H₂) (x , y)  = lpe G H₁ x , lpe G H₂ y

νae  : ∀ (G : SFunctor) → νM act G → νM eff G
tae  : ∀ (G : SFunctor) → T (⟦ G ⟧SF (νM act G)) → T∞ (⟦ G ⟧SF (νM eff G))
lae  : ∀ (G H : SFunctor) → ⟦ H ⟧SF (νM act G) → ⟦ H ⟧SF (νM eff G)
outν (νae G v) = tae G (outν v)
force (tae G (roll (done l)))            = done (lae G G l)
force (tae G (roll (node (call o a k)))) = node (call o a (λ b → tae G (k b)))
lae G (SK B)     x        = x
lae G SId        v        = νae G v
lae G (H₁ S⊕ H₂) (inj₁ x) = inj₁ (lae G H₁ x)
lae G (H₁ S⊕ H₂) (inj₂ y) = inj₂ (lae G H₂ y)
lae G (H₁ S⊗ H₂) (x , y)  = lae G H₁ x , lae G H₂ y

νge  : ∀ (G : SFunctor) → νM eff⁺ G → νM eff G
rge  : ∀ (G : SFunctor) → T⁺ (⟦ G ⟧SF (νM eff⁺ G)) → T∞ (⟦ G ⟧SF (νM eff G))
tge  : ∀ (G : SFunctor) → T∞ (⟦ G ⟧SF (νM eff⁺ G)) → T∞ (⟦ G ⟧SF (νM eff G))
sge  : ∀ (G : SFunctor) → Step (⟦ G ⟧SF (νM eff⁺ G)) (T∞ (⟦ G ⟧SF (νM eff⁺ G))) → Step (⟦ G ⟧SF (νM eff G)) (T∞ (⟦ G ⟧SF (νM eff G)))
lge  : ∀ (G H : SFunctor) → ⟦ H ⟧SF (νM eff⁺ G) → ⟦ H ⟧SF (νM eff G)
outν (νge G v) = rge G (outν v)
force (rge G (call⁺ (call o a k))) = node (call o a (λ b → tge G (k b)))
force (tge G m) = sge G (force m)
sge G (done l)            = done (lge G G l)
sge G (node (call o a k)) = node (call o a (λ b → tge G (k b)))
lge G (SK B)     x        = x
lge G SId        v        = νge G v
lge G (H₁ S⊕ H₂) (inj₁ x) = inj₁ (lge G H₁ x)
lge G (H₁ S⊕ H₂) (inj₂ y) = inj₂ (lge G H₂ y)
lge G (H₁ S⊗ H₂) (x , y)  = lge G H₁ x , lge G H₂ y

subν : ∀ {π π′} → π ⊑π π′ → ∀ (G : SFunctor) → νM π G → νM π′ G
subν ⊑-pure G v = v
subν ⊑-pa   G v = νpa G v
subν ⊑-pe   G v = νpe G v
subν ⊑-act  G v = v
subν ⊑-ae   G v = νae G v
subν ⊑-g    G v = v
subν ⊑-ge   G v = νge G v
subν ⊑-eff  G v = v

------------------------------------------------------------------------
-- What a subtyping derivation means: its conversion
------------------------------------------------------------------------

conv : ∀ {m} (σ : TySub m 0) {A B : Ty m} → A <: B → ⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ B ⟨ σ ⟩ ⟧ᵛ
conv σ sub-void  x = ⊥-elim x
conv σ sub-var   x = x
conv σ sub-unit  x = x
conv σ sub-int   x = x
conv σ sub-float x = x
conv σ (sub-arr {q = Zero} {π = π} a b g) f = λ u → sub g (fmap π (conv σ b) (f u))
conv σ (sub-arr {q = One}  {π = π} a b g) f = λ x → sub g (fmap π (conv σ b) (f (conv σ a x)))
conv σ (sub-arr {q = Many} {π = π} a b g) f = λ x → sub g (fmap π (conv σ b) (f (conv σ a x)))
conv σ (sub-* a b) (x , y)  = conv σ a x , conv σ b y
conv σ (sub-+ a b) (inj₁ x) = inj₁ (conv σ a x)
conv σ (sub-+ a b) (inj₂ y) = inj₂ (conv σ b y)
conv σ sub-μ x = x
conv σ (sub-ν {F = F} g) v = subν g (code (F ⟨ σ ⟩F)) v

------------------------------------------------------------------------
-- A function run at each recursive position of a layer, left to right: what
-- the fold's laws are stated with
------------------------------------------------------------------------

traverseM : ∀ π → pure ⊑π π → (H : SFunctor) {X Y : Set} → (X → M π Y) → ⟦ H ⟧SF X → M π (⟦ H ⟧SF Y)
traverseM π e (SK B)     f x        = return e x
traverseM π e SId        f x        = f x
traverseM π e (H₁ S⊕ H₂) f (inj₁ x) = fmap π inj₁ (traverseM π e H₁ f x)
traverseM π e (H₁ S⊕ H₂) f (inj₂ y) = fmap π inj₂ (traverseM π e H₂ f y)
traverseM π e (H₁ S⊗ H₂) f (x , y)  =
  bind π (traverseM π e H₁ f x) λ u → bind π (traverseM π e H₂ f y) λ v → return e (u , v)
