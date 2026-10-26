{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecRun — a Spec computation against an implementation run
-- (plan 0.122 §5.5, M1).
--
-- The Spec's computations are trees of Σ's calls (`Spec.Effect`); the
-- implementation's (the IR's, `IR.Semantics.Trace`/`Iterative`) are trees of calls
-- named by their declarations, with a halt for a call that does not answer. A
-- Spec block and an implementation block are related step for step: the same
-- end, related values; a call of Σ's declaration against the implementation's
-- call of the same name at the declaration's types (`CallR`), related
-- arguments, and related answers going on alike; a call into `void` against a
-- halt (`HaltR`). A run is the coinductive closure: blocks whose ends are
-- related values or related runs (`RunR`).
--
-- The operations of both monads preserve the relation: the binds, the
-- embedding of blocks, the maps, the loop and the iteration.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecRun (Σ : Signature) where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Empty using (⊥; ⊥-elim)

open import Once.Spec.Word using (Carrier)
open import Once.Spec.Signature using (⟦_⟧ᵇ; Op; op; _∶_; operation; NotEmpty; argAt; arg; void)
import Once.Spec.Signature as SSig
import Once.IR.Semantics.Value Carrier Carrier as V
import Once.IR.Semantics.Trace as LTr
import Once.IR.Semantics.Iterative as LI
import Once.Spec.Effect Σ as SE
import Once.Spec.Polynomial as SPoly
import Once.Adequacy.SpecInterp as SI

------------------------------------------------------------------------
-- Calls
------------------------------------------------------------------------

-- Σ's operation against the implementation's call of its name, at the
-- declaration's types (an argument used zero times is `unit`, `argAt`); the
-- argument and the answer cross by the base conversions.
data CallR : Op Σ → LTr.CallOp → Set where
  cr : ∀ {cn a q b bA} (m : (cn ∶ operation a q b) ∈ Σ) → NotEmpty b
     → CallR (op m) (LTr.callOp cn SI.⌞ argAt q a ⌟ bA SI.⌞ b ⌟)

argR : ∀ {o o′} → CallR o o′ → ⟦ arg o ⟧ᵇ → V.⟦ LTr.CallOp.cdom o′ ⟧ → Set
argR (cr {a = a} {q} m _) y x = SI.toB (argAt q a) x ≡ y

ansR : ∀ {o o′} → CallR o o′ → ⟦ Op.ans o ⟧ᵇ → V.⟦ LTr.CallOp.ccod o′ ⟧ → Set
ansR (cr {b = b} m _) y x = x ≡ SI.fromB b y

-- A call of a declaration answering `void` against a halt.
data HaltR : Op Σ → LTr.HaltOp → Set where
  hr : ∀ {cn a q bA} (m : (cn ∶ operation a q void) ∈ Σ) → HaltR (op m) (LTr.haltOp cn SI.⌞ argAt q a ⌟ bA)

hargR : ∀ {o o′} → HaltR o o′ → ⟦ arg o ⟧ᵇ → V.⟦ LTr.HaltOp.hdom o′ ⟧ → Set
hargR (hr {a = a} {q} m) y x = SI.toB (argAt q a) x ≡ y

------------------------------------------------------------------------
-- Blocks and runs
------------------------------------------------------------------------

data BlockR {X Y : Set} (R : X → Y → Set) : SE.T X → LTr.T Y → Set where
  ret  : ∀ {x y} → R x y → BlockR R (SE.roll (SE.done x)) (LTr.ret y)
  call : ∀ {o o′ a a′ k k′} (c : CallR o o′) → argR c a a′
       → (∀ {b b′} → ansR c b b′ → BlockR R (k b) (k′ b′))
       → BlockR R (SE.roll (SE.node (SSig.call o a k))) (LTr.call o′ a′ k′)
  halt : ∀ {o o′ a a′ k} (h : HaltR o o′) → hargR h a a′
       → BlockR R (SE.roll (SE.node (SSig.call o a k))) (LTr.halt o′ a′)

data SumR {X X′ Y Y′ : Set} (R : X → Y → Set) (S : X′ → Y′ → Set) : X ⊎ X′ → Y ⊎ Y′ → Set where
  left  : ∀ {x y} → R x y → SumR R S (inj₁ x) (inj₁ y)
  right : ∀ {x y} → S x y → SumR R S (inj₂ x) (inj₂ y)

record RunR {X Y : Set} (R : X → Y → Set) (m : SE.T∞ X) (n : LI.T∞ Y) : Set where
  coinductive
  field forceR : BlockR (SumR R (RunR R)) (SE.force m) (LI.T∞.force n)
open RunR

------------------------------------------------------------------------
-- Blocks: the bind and the map
------------------------------------------------------------------------

module _ {X X′ Y Y′ : Set} {R : X → Y → Set} {S : X′ → Y′ → Set} where

  bindT-R : ∀ {t u} {k : X → SE.T X′} {g : Y → LTr.T Y′}
          → BlockR R t u → (∀ {x y} → R x y → BlockR S (k x) (g y)) → BlockR S (t SE.>>=T k) (u LTr.>>=T g)
  bindT-R (ret r)      h = h r
  bindT-R (call c a k) h = call c a (λ b → bindT-R (k b) h)
  bindT-R (halt x a)   h = halt x a

  mapT-R : ∀ {t u} {f : X → X′} {g : Y → Y′}
         → BlockR R t u → (∀ {x y} → R x y → S (f x) (g y)) → BlockR S (SE.mapT f t) (LTr.fmapT g u)
  mapT-R r h = bindT-R r (λ x → ret (h x))

module _ {X Y : Set} {R S : X → Y → Set} (rs : ∀ {x y} → R x y → S x y) where

  BlockR-mono : ∀ {t u} → BlockR R t u → BlockR S t u
  BlockR-mono (ret r)      = ret (rs r)
  BlockR-mono (call c a k) = call c a (λ b → BlockR-mono (k b))
  BlockR-mono (halt x a)   = halt x a

module _ {X Y : Set} {R S : X → Y → Set} (rs : ∀ {x y} → R x y → S x y) where

  RunR-mono  : ∀ {m n} → RunR R m n → RunR S m n
  RunRB-mono : ∀ {b b′} → BlockR (SumR R (RunR R)) b b′ → BlockR (SumR S (RunR S)) b b′
  forceR (RunR-mono r) = RunRB-mono (forceR r)
  RunRB-mono (ret (left r))  = ret (left (rs r))
  RunRB-mono (ret (right r)) = ret (right (RunR-mono r))
  RunRB-mono (call c a k)    = call c a (λ b → RunRB-mono (k b))
  RunRB-mono (halt x a)      = halt x a

------------------------------------------------------------------------
-- Runs: the unit, the embedding of a block, the bind
------------------------------------------------------------------------

return∞-R : ∀ {X Y : Set} {R : X → Y → Set} {x y} → R x y → RunR R (SE.return∞ x) (LI.return∞ y)
forceR (return∞-R r) = ret (left r)

module _ {X Y : Set} {R : X → Y → Set} where

  embed-R  : ∀ {t u} → BlockR R t u → RunR R (SE.embed t) (LI.embed u)
  embedB-R : ∀ {t u} → BlockR R t u → BlockR (SumR R (RunR R)) (SE.mapT inj₁ t) (LI.embedBlock u)
  forceR (embed-R r) = embedB-R r
  embedB-R (ret r)      = ret (left r)
  embedB-R (call c a k) = call c a (λ b → embedB-R (k b))
  embedB-R (halt x a)   = halt x a

module _ {X X′ Y Y′ : Set} {R : X → Y → Set} {S : X′ → Y′ → Set}
         {k : X → SE.T∞ X′} {g : Y → LI.T∞ Y′}
         (h : ∀ {x y} → R x y → RunR S (k x) (g y)) where

  bind∞-R : ∀ {m n} → RunR R m n → RunR S (m SE.>>=∞ k) (n LI.>>=∞ g)
  bindB-R : ∀ {b b′} → BlockR (SumR R (RunR R)) b b′ → BlockR (SumR S (RunR S)) (SE.bindBlock b k) (LI.bindBlock b′ g)
  forceR (bind∞-R r) = bindB-R (forceR r)
  bindB-R (ret (left r))  = forceR (h r)
  bindB-R (ret (right r)) = ret (right (bind∞-R r))
  bindB-R (call c a k₀)   = call c a (λ b → bindB-R (k₀ b))
  bindB-R (halt x a)      = halt x a

-- A block's bind, embedded, against the implementation's bind of a run
-- related to the block's embedding: the block's calls first, then the
-- continuation's run.
module _ {X X′ Y Y′ : Set} {R : X → Y → Set} {S : X′ → Y′ → Set}
         {k : X → SE.T X′} {g : Y → LI.T∞ Y′}
         (h : ∀ {x y} → R x y → RunR S (SE.embed (k x)) (g y)) where

  embed-bind-R  : ∀ t {n} → RunR R (SE.embed t) n → RunR S (SE.embed (t SE.>>=T k)) (n LI.>>=∞ g)
  embed-bindB-R : ∀ t {b} → BlockR (SumR R (RunR R)) (SE.mapT inj₁ t) b
                → BlockR (SumR S (RunR S)) (SE.mapT inj₁ (t SE.>>=T k)) (LI.bindBlock b g)
  forceR (embed-bind-R t r) = embed-bindB-R t (forceR r)
  embed-bindB-R (SE.roll (SE.done x)) (ret (left r)) = forceR (h r)
  embed-bindB-R (SE.roll (SE.node (SSig.call o a k₀))) (call c ar kr) = call c ar (λ b → embed-bindB-R (k₀ _) (kr b))
  embed-bindB-R (SE.roll (SE.node (SSig.call o a k₀))) (halt x ar)    = halt x ar

------------------------------------------------------------------------
-- The loop: related rounds give related loops
------------------------------------------------------------------------

module _ {A A′ B B′ : Set} {RA : A → A′ → Set} {RB : B → B′ → Set}
         {c : A → SE.T (B ⊎ A)} {c′ : A′ → LTr.T (B′ ⊎ A′)}
         (h : ∀ {a a′} → RA a a′ → BlockR (SumR RB RA) (c a) (c′ a′)) where

  loop-R  : ∀ {a a′} → RA a a′ → RunR RB (SE.loop c a) (LI.loop c′ a′)
  loopB-R : ∀ {t t′} → BlockR (SumR RB RA) t t′
          → BlockR (SumR RB (RunR RB)) (SE.treeA (SPoly.SK B SPoly.S⊕ SPoly.SId) c t) (LI.loopBlock c′ t′)
  forceR (loop-R r) = loopB-R (h r)
  loopB-R (ret (left rb))  = ret (left rb)
  loopB-R (ret (right ra)) = ret (right (loop-R ra))
  loopB-R (call o ra k)    = call o ra (λ rb → loopB-R (k rb))
  loopB-R (halt x a)       = halt x a

-- …and against the implementation's iteration over runs: a round that is a
-- finite block, related to the implementation's round run.
module _ {A A′ B B′ : Set} {RB : B → B′ → Set} {S : (B ⊎ A) → (B′ ⊎ A′) → Set}
         {c : A → SE.T (B ⊎ A)} {f′ : A′ → LI.T∞ (B′ ⊎ A′)}
         (s-inl : ∀ {b b′} → S (inj₁ b) (inj₁ b′) → RB b b′)
         (s-inr : ∀ {a a′} → S (inj₂ a) (inj₂ a′) → RunR S (SE.embed (c a)) (f′ a′))
         (s-lr  : ∀ {b a′} → S (inj₁ b) (inj₂ a′) → ⊥)
         (s-rl  : ∀ {a b′} → S (inj₂ a) (inj₁ b′) → ⊥) where

  loop-iter-R : ∀ {a a′} → S (inj₂ a) (inj₂ a′) → RunR RB (SE.loop c a) (LI.iter∞ f′ a′)
  loopB-iter  : ∀ t {l′} → BlockR (SumR S (RunR S)) (SE.mapT inj₁ t) l′
              → BlockR (SumR RB (RunR RB)) (SE.treeA (SPoly.SK B SPoly.S⊕ SPoly.SId) c t) (LI.iterBlock f′ l′)
  forceR (loop-iter-R {a} r) = loopB-iter (c a) (forceR (s-inr r))
  loopB-iter (SE.roll (SE.done (inj₁ b))) (ret (left {y = inj₁ b′} r)) = ret (left (s-inl r))
  loopB-iter (SE.roll (SE.done (inj₁ b))) (ret (left {y = inj₂ a′} r)) = ⊥-elim (s-lr r)
  loopB-iter (SE.roll (SE.done (inj₂ a))) (ret (left {y = inj₂ a′} r)) = ret (right (loop-iter-R r))
  loopB-iter (SE.roll (SE.done (inj₂ a))) (ret (left {y = inj₁ b′} r)) = ⊥-elim (s-rl r)
  loopB-iter (SE.roll (SE.node (SSig.call o a k))) (call cc ar kr) = call cc ar (λ e → loopB-iter (k _) (kr e))
  loopB-iter (SE.roll (SE.node (SSig.call o a k))) (halt x ar)    = halt x ar

------------------------------------------------------------------------
-- Restating a run on either side
------------------------------------------------------------------------

module _ {X Y : Set} {R : X → Y → Set} where

  ≡ʳ-R : ∀ {m n n′} → n ≡ n′ → RunR R m n′ → RunR R m n
  ≡ʳ-R refl h = h

  -- the implementation's run, along an equation of its first block
  retargetʳ-R : ∀ {m n n′} → LI.T∞.force n ≡ LI.T∞.force n′ → RunR R m n′ → RunR R m n
  forceR (retargetʳ-R {m} e h) = subst (BlockR (SumR R (RunR R)) (SE.force m)) (Relation.Binary.PropositionalEquality.sym e) (forceR h)
    where import Relation.Binary.PropositionalEquality

  -- the Spec's run, along an equation of its first block
  retargetˡ-R : ∀ {m m′ n} → SE.force m ≡ SE.force m′ → RunR R m′ n → RunR R m n
  forceR (retargetˡ-R {n = n} e h) = subst (λ b → BlockR (SumR R (RunR R)) b (LI.T∞.force n)) (Relation.Binary.PropositionalEquality.sym e) (forceR h)
    where import Relation.Binary.PropositionalEquality

-- The implementation's run, mapped.
module _ {X Y Y′ : Set} {R : X → Y → Set} {S : X → Y′ → Set} {g : Y → Y′} (h : ∀ {x y} → R x y → S x (g y)) where

  fmapʳ-R  : ∀ {m n} → RunR R m n → RunR S m (LI.fmap∞ g n)
  fmapBʳ-R : ∀ {b b′} → BlockR (SumR R (RunR R)) b b′
           → BlockR (SumR S (RunR S)) b (LI.bindBlock b′ (λ y → LI.return∞ (g y)))
  forceR (fmapʳ-R r) = fmapBʳ-R (forceR r)
  fmapBʳ-R (ret (left r))  = ret (left (h r))
  fmapBʳ-R (ret (right r)) = ret (right (fmapʳ-R r))
  fmapBʳ-R (call c a k)    = call c a (λ e → fmapBʳ-R (k e))
  fmapBʳ-R (halt x a)      = halt x a

-- The Spec's run, mapped…
module _ {X X′ Y : Set} {R : X → Y → Set} {S : X′ → Y → Set} {f : X → X′} (h : ∀ {x y} → R x y → S (f x) y) where

  fmapˡ-R  : ∀ {m n} → RunR R m n → RunR S (m SE.>>=∞ λ x → SE.return∞ (f x)) n
  fmapBˡ-R : ∀ {b b′} → BlockR (SumR R (RunR R)) b b′
           → BlockR (SumR S (RunR S)) (SE.bindBlock b (λ x → SE.return∞ (f x))) b′
  forceR (fmapˡ-R r) = fmapBˡ-R (forceR r)
  fmapBˡ-R (ret (left r))  = ret (left (h r))
  fmapBˡ-R (ret (right r)) = ret (right (fmapˡ-R r))
  fmapBˡ-R (call c a k)    = call c a (λ e → fmapBˡ-R (k e))
  fmapBˡ-R (halt x a)      = halt x a

  -- …and a block's map, embedded.
  embed-mapˡ-R  : ∀ t {n} → RunR R (SE.embed t) n → RunR S (SE.embed (SE.mapT f t)) n
  embed-mapBˡ-R : ∀ t {b} → BlockR (SumR R (RunR R)) (SE.mapT inj₁ t) b
                → BlockR (SumR S (RunR S)) (SE.mapT inj₁ (SE.mapT f t)) b
  forceR (embed-mapˡ-R t r) = embed-mapBˡ-R t (forceR r)
  embed-mapBˡ-R (SE.roll (SE.done x)) (ret (left r)) = ret (left (h r))
  embed-mapBˡ-R (SE.roll (SE.node (SSig.call o a k₀))) (call c ar kr) = call c ar (λ b → embed-mapBˡ-R (k₀ _) (kr b))
  embed-mapBˡ-R (SE.roll (SE.node (SSig.call o a k₀))) (halt x ar)    = halt x ar
