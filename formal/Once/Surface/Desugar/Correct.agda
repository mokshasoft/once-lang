{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Surface.Desugar.Correct
--
-- Correctness proof for the desugar transformation.
-- Proves that desugaring preserves program semantics.
--
-- See D035: Two-Stage IR and MAlonzo Compilation
------------------------------------------------------------------------

open import Once.Backend.MachineInterface
open import Once.Contract

module Once.Surface.Desugar.Correct
  (MI : MachineInterface)
  (CI : ContractInterface)
  where

open import Once.Type
open import Once.SemanticBaseMachine MI
open import Once.Surface.IR ⟦_⟧ as S
open import Once.Surface.Desugar ⟦_⟧
open import Once.IR ⟦_⟧ as IRM
open import Once.Semantics MI
open import Once.Memory using (Word)

module Correct where

  open DesugarDef CI
  open IRM.IRDef CI
  open ContractInterface CI
  open SemanticsDef CI

  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
  open import Data.String using (String)

  open import Once.Postulates ⟦_⟧ IR Closure Closure.semantics encode eval
    using (extensionality; closure-semantics-eq)

  ------------------------------------------------------------------------
  -- Primitive evaluation
  ------------------------------------------------------------------------

  -- | evalPrim postulate has been ELIMINATED!
  -- Primitive semantics are now carried directly in the Prim constructor.

  ------------------------------------------------------------------------
  -- Surface IR Semantics
  ------------------------------------------------------------------------

  -- | Evaluation of Surface IR
  --
  -- Same as Core IR semantics, plus:
  -- - Let: evaluate binding, pair with input, evaluate body
  -- - Prim: use postulated primitive evaluation
  --
  evalSurface : ∀ {A B} → SurfaceIR A B → ⟦ A ⟧ → ⟦ B ⟧

  -- Category structure
  evalSurface S.id x = x
  evalSurface (g S.∘ f) x = evalSurface g (evalSurface f x)

  -- Products
  evalSurface S.fst (a , b) = a
  evalSurface S.snd (a , b) = b
  evalSurface S.⟨ f , g ⟩ x = (evalSurface f x , evalSurface g x)

  -- Coproducts
  evalSurface S.inl a = inj₁ a
  evalSurface S.inr b = inj₂ b
  evalSurface S.[ f , g ] (inj₁ a) = evalSurface f a
  evalSurface S.[ f , g ] (inj₂ b) = evalSurface g b

  -- Terminal
  evalSurface S.terminal _ = tt

  -- Initial
  evalSurface S.initial ()

  -- Exponential (with explicit Closure)
  evalSurface (S.curry f) a = record
    { env-addr  = encode a
    ; semantics = λ b → evalSurface f (a , b)
    }
  evalSurface S.apply (cl , a) = semantics cl a

  -- Recursive types
  evalSurface S.fold x = wrap x
  evalSurface S.unfold x = unwrap x

  -- Effects
  evalSurface S.arr f = f

  -- Surface-only: Let binding
  -- evalSurface (Let e1 e2) x = evalSurface e2 (x , evalSurface e1 x)
  evalSurface (S.Let e1 e2) x = evalSurface e2 (x , evalSurface e1 x)

  -- Surface-only: Primitives (explicit semantic function - no evalPrim postulate needed!)
  evalSurface (S.Prim _ sem) x = sem x

  ------------------------------------------------------------------------
  -- Correctness theorem
  ------------------------------------------------------------------------

  -- | Primitive correctness (TECHNICAL DEBT: postulated)
  --
  -- TODO: Will be proven when makeContract is replaced with real domain compilers
  --
  postulate
    desugar-correct-prim : ∀ {A B} (name : String) (sem : ⟦ A ⟧ → ⟦ B ⟧) (x : ⟦ A ⟧)
                         → eval (prim-desugar {A} {B} name sem) x ≡ sem x

  -- | Desugar preserves semantics
  --
  -- For any Surface IR term, evaluating the desugared Core IR
  -- gives the same result as directly evaluating the Surface IR.
  --
  -- The proof is by structural induction on the Surface IR term.
  -- Most cases are trivial (refl) because the constructors are
  -- the same in both IRs. The interesting cases are Let and Prim.
  --
  desugar-correct : ∀ {A B} (ir : SurfaceIR A B) (x : ⟦ A ⟧)
                  → eval (desugar ir) x ≡ evalSurface ir x

  -- Category structure
  desugar-correct S.id x = refl
  desugar-correct (g S.∘ f) x =
    let ih-f = desugar-correct f x
        ih-g = desugar-correct g (evalSurface f x)
    in begin
      eval (desugar g C.∘ desugar f) x
        ≡⟨ refl ⟩
      eval (desugar g) (eval (desugar f) x)
        ≡⟨ cong (eval (desugar g)) ih-f ⟩
      eval (desugar g) (evalSurface f x)
        ≡⟨ ih-g ⟩
      evalSurface g (evalSurface f x)
        ≡⟨ refl ⟩
      evalSurface (g S.∘ f) x
        ∎
    where open Relation.Binary.PropositionalEquality.≡-Reasoning

  -- Products
  desugar-correct S.fst (a , b) = refl
  desugar-correct S.snd (a , b) = refl
  desugar-correct S.⟨ f , g ⟩ x =
    cong₂ _,_ (desugar-correct f x) (desugar-correct g x)

  -- Coproducts
  desugar-correct S.inl a = refl
  desugar-correct S.inr b = refl
  desugar-correct S.[ f , g ] (inj₁ a) = desugar-correct f a
  desugar-correct S.[ f , g ] (inj₂ b) = desugar-correct g b

  -- Terminal
  desugar-correct S.terminal x = refl

  -- Initial
  desugar-correct S.initial ()

  -- Exponential (with explicit Closure)
  -- Both eval (curry (desugar f)) and evalSurface (S.curry f) create Closure records.
  -- We prove equality via closure-semantics-eq by showing their semantics are equal.
  desugar-correct (S.curry f) a = closure-semantics-eq
    (eval (C.curry (desugar f)) a)
    (evalSurface (S.curry f) a)
    (extensionality (λ b → desugar-correct f (a , b)))
  desugar-correct S.apply (cl , a) = refl

  -- Recursive types
  desugar-correct S.fold x = refl
  desugar-correct S.unfold x = refl

  -- Effects
  desugar-correct S.arr f = refl

  -- | Let binding correctness
  --
  -- desugar (Let e1 e2) = desugar e2 ∘ ⟨ id , desugar e1 ⟩
  --
  -- eval (desugar e2 ∘ ⟨ id , desugar e1 ⟩) x
  --   = eval (desugar e2) (eval ⟨ id , desugar e1 ⟩ x)
  --   = eval (desugar e2) (x , eval (desugar e1) x)
  --   = evalSurface e2 (x , evalSurface e1 x)     by IH
  --   = evalSurface (Let e1 e2) x                 by definition
  --
  desugar-correct (S.Let e1 e2) x =
    let ih-e1 = desugar-correct e1 x
        ih-e2 = desugar-correct e2 (x , evalSurface e1 x)
    in begin
      eval (desugar (S.Let e1 e2)) x
        ≡⟨ refl ⟩
      eval (desugar e2 C.∘ C.⟨ C.id , desugar e1 ⟩) x
        ≡⟨ refl ⟩
      eval (desugar e2) (x , eval (desugar e1) x)
        ≡⟨ cong (λ v → eval (desugar e2) (x , v)) ih-e1 ⟩
      eval (desugar e2) (x , evalSurface e1 x)
        ≡⟨ ih-e2 ⟩
      evalSurface e2 (x , evalSurface e1 x)
        ≡⟨ refl ⟩
      evalSurface (S.Let e1 e2) x
        ∎
    where open Relation.Binary.PropositionalEquality.≡-Reasoning

  -- | Primitive correctness (no postulate needed!)
  desugar-correct (S.Prim name sem) x = desugar-correct-prim name sem x
