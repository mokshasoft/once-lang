-- Evidence for plan 0.119 §7 A″ (plans/0.119-A2.patch); checked against the Spec at ef91bbbd3,
-- not part of the build. Check: copy into formal/POC/, `make agda MODULE=POC/<file>`.
{-# OPTIONS --safe #-}
-- POC (not committed): `Spec.Metatheory.Recursion.fold-fusion` is false at
-- an effectful grade. Over binary trees, fusion moves the second child's
-- fold before the first child's `f`: `a a b b` becomes `a b a b`.
module POC.FusionFalse where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Once.Spec.Name using (gen)
open import Once.Spec.Grade using (mk-kind; Many; act; ⊑-pa)
open import Once.Spec.Signature using (Signature; _∶_; arrow; unit; Op; op; e-act; call)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; inS)
import Once.Spec.Effect as E
import Once.Spec.Domain as D
open import Once.Spec.Metatheory using (Recursion)

abΣ : Signature
abΣ = (gen "a" ∶ arrow unit (mk-kind Many act) unit) ∷ (gen "b" ∶ arrow unit (mk-kind Many act) unit) ∷ []

open E abΣ
open D abΣ using (foldM; traverseM)

opA opB : Op abΣ
opA = op (here refl) e-act
opB = op (there (here refl)) e-act

emitA emitB : T ⊤
emitA = performT (call opA tt (λ b → b))
emitB = performT (call opB tt (λ b → b))

G : SFunctor
G = SK ⊤ S⊕ (SId S⊗ SId)

leaf : μS G
leaf = inS (inj₁ tt)

node2 : μS G → μS G → μS G
node2 u v = inS (inj₂ (u , v))

f : Bool → T ⊤
f true  = emitB
f false = returnT tt

alg : ⟦ G ⟧SF Bool → T Bool
alg (inj₁ tt)        = emitA >>=T λ _ → returnT true
alg (inj₂ (r₁ , r₂)) = f r₁ >>=T λ _ → f r₂ >>=T λ _ → returnT false

alg′ : ⟦ G ⟧SF ⊤ → T ⊤
alg′ (inj₁ tt) = emitA >>=T λ _ → emitB
alg′ (inj₂ _)  = returnT tt

hyp : ∀ l → (alg l >>=T f) ≡ (traverseM act ⊑-pa G f l >>=T alg′)
hyp (inj₁ tt)              = refl
hyp (inj₂ (true  , true))  = refl
hyp (inj₂ (true  , false)) = refl
hyp (inj₂ (false , true))  = refl
hyp (inj₂ (false , false)) = refl

-- The operations a run calls, in order (every answer here is `tt`).
walk : ∀ {X} → T X → List ℕ
walk (roll (done x)) = []
walk (roll (node (call (op (here refl) e-act) a k)))         = 0 ∷ walk (k tt)
walk (roll (node (call (op (there (here refl)) e-act) a k))) = 1 ∷ walk (k tt)
walk (roll (node (call (op (there (there ())) _) a k)))

fused-differs : ¬ ((foldM act ⊑-pa G alg (node2 leaf leaf) >>=T f) ≡ foldM act ⊑-pa G alg′ (node2 leaf leaf))
fused-differs e with cong walk e
... | ()

fusion-false : ¬ Recursion abΣ
fusion-false R = fused-differs (Recursion.fold-fusion R act ⊑-pa G alg alg′ f hyp (node2 leaf leaf))
