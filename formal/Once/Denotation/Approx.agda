-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.Approx — a run that need not stop, observed at a ROUND
-- BUDGET (plan 0.119 D5, option (a)).
--
-- `approx r m` follows the run `m : T∞ X` through at most `r` silent steps
-- (the ends of blocks that continue); at the next one it is CUT. The result is
-- a finite tree: what the run does before its `r+1`-th silent step, and how
-- much budget is left if it returns. This is a proof technique of the
-- backend, not a meaning: the machine is related to `approx r` of the meaning
-- at every budget, and agreement at every budget is weak bisimilarity of the
-- traces.
------------------------------------------------------------------------

module Once.Denotation.Approx where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Once.Internal.Trace using (T; ret; call; halt)
open import Once.Internal.Iterative using (T∞)
open T∞ using (force)

-- What a budgeted observation ends with: a result and the budget left, or a
-- cut.
data Ap (X : Set) : Set where
  done : X → ℕ → Ap X
  cut  : Ap X

approx      : ∀ {X} → ℕ → T∞ X → T (Ap X)
approxBlock : ∀ {X} → ℕ → T (X ⊎ T∞ X) → T (Ap X)
approx r m = approxBlock r (force m)
approxBlock r       (ret (inj₁ x)) = ret (done x r)
approxBlock zero    (ret (inj₂ m)) = ret cut
approxBlock (suc r) (ret (inj₂ m)) = approx r m
approxBlock r       (call o a k)   = call o a (λ b → approxBlock r (k b))
approxBlock r       (halt o a)     = halt o a

------------------------------------------------------------------------
-- How a budgeted run ended, as the backend's obligations read it.
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Once.Res using (Res; stopped; returns)

-- The run was not cut: it stopped, or returned.
NotCut : ∀ {X} → Res (Ap X) → Set
NotCut stopped              = ⊤
NotCut (returns (done _ _)) = ⊤
NotCut (returns cut)        = ⊥

-- The budget left when the run ended (a stopped run consumed none that
-- matters; a cut one consumed it all).
budgetLeft : ∀ {X} → ℕ → Res (Ap X) → ℕ
budgetLeft r stopped              = r
budgetLeft r (returns (done _ r′)) = r′
budgetLeft r (returns cut)        = 0

------------------------------------------------------------------------
-- A finite block embedded in `T∞` consumes no budget: its budgeted run is
-- its own run, every result tagged with the budget it was given. (Stated on
-- runs, so no function extensionality: a run applies a continuation only to
-- the answer the Interpretation gives.)
------------------------------------------------------------------------

open import Data.List using (List; _++_; [_])
open import Data.Product using (proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Res using (mapRes; is-stopped)
open import Once.Internal.Event using (SigOpEvent)
open import Once.Internal.Iterative using (embed; embedBlock)
open import Once.Internal.Trace using (Interp; Run; run; run-call; consE; callAnswer; callEvent; haltEvent; unlinkedOp; CallOp)
open import Once.Internal.Trace using (module CallOp)
open CallOp using (cdom; ccod)
import Once.Semantics.Machine as M

tagRun : ∀ {X} → ℕ → Run X → Run (Ap X)
tagRun r ρ = proj₁ ρ , mapRes (λ x → done x r) (proj₂ ρ)

run-approx-embedB : ∀ {X} (ι : Interp) (h : List SigOpEvent) (r : ℕ) (t : T X)
                  → run ι h (approxBlock r (embedBlock t)) ≡ tagRun r (run ι h t)
run-approx-call   : ∀ {X} (ι : Interp) (h : List SigOpEvent) (r : ℕ) (o : CallOp) (a : M.⟦ cdom o ⟧)
                      (k : M.⟦ ccod o ⟧ → T X) (ans : Maybe M.⟦ ccod o ⟧)
                  → run-call ι h o a (λ b → approxBlock r (embedBlock (k b))) ans
                    ≡ tagRun r (run-call ι h o a k ans)
run-approx-embedB ι h r (ret x)      = refl
run-approx-embedB ι h r (halt o a)   = refl
run-approx-embedB ι h r (call o a k) = run-approx-call ι h r o a k (callAnswer ι h o a)
run-approx-call ι h r o a k (just b) = cong (consE (callEvent o a)) (run-approx-embedB ι (h ++ [ callEvent o a ]) r (k b))
run-approx-call ι h r o a k nothing  = refl

run-approx-embed : ∀ {X} (ι : Interp) (h : List SigOpEvent) (r : ℕ) (t : T X)
                 → run ι h (approx r (embed t)) ≡ tagRun r (run ι h t)
run-approx-embed ι h r t = run-approx-embedB ι h r t

-- Reading a tagged result.
is-stopped-tag : ∀ {X} (r : ℕ) (ρ : Res X) → is-stopped (mapRes (λ x → done x r) ρ) ≡ is-stopped ρ
is-stopped-tag r stopped     = refl
is-stopped-tag r (returns _) = refl

budgetLeft-tag : ∀ {X} (r : ℕ) (ρ : Res X) → budgetLeft r (mapRes (λ x → done x r) ρ) ≡ r
budgetLeft-tag r stopped     = refl
budgetLeft-tag r (returns _) = refl

notCut-tag : ∀ {X} (r : ℕ) (ρ : Res X) → NotCut (mapRes (λ x → done x r) ρ)
notCut-tag r stopped     = tt
notCut-tag r (returns _) = tt

done-tag : ∀ {X} {r r′ : ℕ} {v : X} (ρ : Res X) → mapRes (λ x → done x r) ρ ≡ returns (done v r′) → ρ ≡ returns v
done-tag (returns x) refl = refl

------------------------------------------------------------------------
-- THE BUDGETED RUN OF A BIND is the budgeted runs of its parts: the first
-- part's run, then — if it returned with budget `r′` left — the second part's
-- run at `r′`, the history threaded. A stopped or cut first part ends the
-- whole.
------------------------------------------------------------------------

open import Data.List using (_∷_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Once.Internal.Iterative using (_>>=∞_; bindBlock)
open import Once.Internal.Trace using (appE)

thenAp : ∀ {X Y} → Interp → List SigOpEvent → List SigOpEvent → Res (Ap X) → (X → T∞ Y) → Run (Ap Y)
thenAp ι h es stopped              f = es , stopped
thenAp ι h es (returns cut)        f = es , returns cut
thenAp ι h es (returns (done x r)) f = appE es (run ι (h ++ es) (approx r (f x)))

mutual
  run-approx-bindB : ∀ {X Y} (ι : Interp) (h : List SigOpEvent) (r : ℕ) (b : T (X ⊎ T∞ X)) (f : X → T∞ Y)
                   → run ι h (approxBlock r (bindBlock b f))
                     ≡ thenAp ι h (proj₁ (run ι h (approxBlock r b))) (proj₂ (run ι h (approxBlock r b))) f
  run-approx-bindB ι h r       (ret (inj₁ x)) f = cong (λ hh → run ι hh (approx r (f x))) (sym (++-identityʳ h))
  run-approx-bindB ι h zero    (ret (inj₂ m)) f = refl
  run-approx-bindB ι h (suc r) (ret (inj₂ m)) f = run-approx-bindB ι h r (force m) f
  run-approx-bindB ι h r       (call o a k)   f = run-approx-bind-call ι h r o a k f (callAnswer ι h o a)
  run-approx-bindB ι h r       (halt o a)     f = refl

  run-approx-bind-call : ∀ {X Y} (ι : Interp) (h : List SigOpEvent) (r : ℕ) (o : CallOp) (a : M.⟦ cdom o ⟧)
                           (k : M.⟦ ccod o ⟧ → T (X ⊎ T∞ X)) (f : X → T∞ Y) (mb : Maybe M.⟦ ccod o ⟧)
                       → run-call ι h o a (λ b → approxBlock r (bindBlock (k b) f)) mb
                         ≡ thenAp ι h (proj₁ (run-call ι h o a (λ b → approxBlock r (k b)) mb))
                                      (proj₂ (run-call ι h o a (λ b → approxBlock r (k b)) mb)) f
  run-approx-bind-call ι h r o a k f (just b) =
    trans (cong (consE (callEvent o a)) (run-approx-bindB ι (h ++ [ callEvent o a ]) r (k b) f))
          (cons-thenAp ι h (callEvent o a)
             (proj₁ (run ι (h ++ [ callEvent o a ]) (approxBlock r (k b))))
             (proj₂ (run ι (h ++ [ callEvent o a ]) (approxBlock r (k b)))) f)
  run-approx-bind-call ι h r o a k f nothing = refl

  cons-thenAp : ∀ {X Y} ι h e es (ρ : Res (Ap X)) (f : X → T∞ Y)
              → consE e (thenAp ι (h ++ [ e ]) es ρ f) ≡ thenAp ι h (e ∷ es) ρ f
  cons-thenAp ι h e es stopped              f = refl
  cons-thenAp ι h e es (returns cut)        f = refl
  cons-thenAp ι h e es (returns (done x r)) f =
    cong (λ hh → appE (e ∷ es) (run ι hh (approx r (f x)))) (++-assoc h [ e ] es)

run-approx-bind : ∀ {X Y} (ι : Interp) (h : List SigOpEvent) (r : ℕ) (m : T∞ X) (f : X → T∞ Y)
                → run ι h (approx r (m >>=∞ f))
                  ≡ thenAp ι h (proj₁ (run ι h (approx r m))) (proj₂ (run ι h (approx r m))) f
run-approx-bind ι h r m f = run-approx-bindB ι h r (force m) f

------------------------------------------------------------------------
-- THE LOOP at a budget: a budgeted run of `iterRun f m` is the budgeted run of
-- the round `m`, then — on `inr a` with budget left — one silent step (one
-- unit of budget) and the loop from the next round `f a`.
------------------------------------------------------------------------

open import Once.Internal.Iterative using (iterRun; iterBlock)

thenIter : ∀ {A B} → Interp → List SigOpEvent → List SigOpEvent → Res (Ap (B ⊎ A))
         → (A → T∞ (B ⊎ A)) → Run (Ap B)
thenIter ι h es stopped                            f = es , stopped
thenIter ι h es (returns cut)                      f = es , returns cut
thenIter ι h es (returns (done (inj₁ b) r))        f = es , returns (done b r)
thenIter ι h es (returns (done (inj₂ a) zero))     f = es , returns cut
thenIter ι h es (returns (done (inj₂ a) (suc r)))  f = appE es (run ι (h ++ es) (approx r (iterRun f (f a))))

mutual
  run-approx-iterB : ∀ {A B} (ι : Interp) (h : List SigOpEvent) (r : ℕ)
                       (b : T ((B ⊎ A) ⊎ T∞ (B ⊎ A))) (f : A → T∞ (B ⊎ A))
                   → run ι h (approxBlock r (iterBlock f b))
                     ≡ thenIter ι h (proj₁ (run ι h (approxBlock r b))) (proj₂ (run ι h (approxBlock r b))) f
  run-approx-iterB ι h r       (ret (inj₁ (inj₁ b))) f = refl
  run-approx-iterB ι h zero    (ret (inj₁ (inj₂ a))) f = refl
  run-approx-iterB ι h (suc r) (ret (inj₁ (inj₂ a))) f =
    cong (λ hh → run ι hh (approx r (iterRun f (f a)))) (sym (++-identityʳ h))
  run-approx-iterB ι h zero    (ret (inj₂ m))        f = refl
  run-approx-iterB ι h (suc r) (ret (inj₂ m))        f = run-approx-iterB ι h r (force m) f
  run-approx-iterB ι h r       (call o a k)          f = run-approx-iter-call ι h r o a k f (callAnswer ι h o a)
  run-approx-iterB ι h r       (halt o a)            f = refl

  run-approx-iter-call : ∀ {A B} (ι : Interp) (h : List SigOpEvent) (r : ℕ) (o : CallOp) (a : M.⟦ cdom o ⟧)
                           (k : M.⟦ ccod o ⟧ → T ((B ⊎ A) ⊎ T∞ (B ⊎ A))) (f : A → T∞ (B ⊎ A))
                           (mb : Maybe M.⟦ ccod o ⟧)
                       → run-call ι h o a (λ b → approxBlock r (iterBlock f (k b))) mb
                         ≡ thenIter ι h (proj₁ (run-call ι h o a (λ b → approxBlock r (k b)) mb))
                                        (proj₂ (run-call ι h o a (λ b → approxBlock r (k b)) mb)) f
  run-approx-iter-call ι h r o a k f (just b) =
    trans (cong (consE (callEvent o a)) (run-approx-iterB ι (h ++ [ callEvent o a ]) r (k b) f))
          (cons-thenIter ι h (callEvent o a)
             (proj₁ (run ι (h ++ [ callEvent o a ]) (approxBlock r (k b))))
             (proj₂ (run ι (h ++ [ callEvent o a ]) (approxBlock r (k b)))) f)
  run-approx-iter-call ι h r o a k f nothing = refl

  cons-thenIter : ∀ {A B} ι h e es (ρ : Res (Ap (B ⊎ A))) (f : A → T∞ (B ⊎ A))
                → consE e (thenIter ι (h ++ [ e ]) es ρ f) ≡ thenIter ι h (e ∷ es) ρ f
  cons-thenIter ι h e es stopped                           f = refl
  cons-thenIter ι h e es (returns cut)                     f = refl
  cons-thenIter ι h e es (returns (done (inj₁ b) r))       f = refl
  cons-thenIter ι h e es (returns (done (inj₂ a) zero))    f = refl
  cons-thenIter ι h e es (returns (done (inj₂ a) (suc r))) f =
    cong (λ hh → appE (e ∷ es) (run ι hh (approx r (iterRun f (f a))))) (++-assoc h [ e ] es)

run-approx-iter : ∀ {A B} (ι : Interp) (h : List SigOpEvent) (r : ℕ) (m : T∞ (B ⊎ A)) (f : A → T∞ (B ⊎ A))
                → run ι h (approx r (iterRun f m))
                  ≡ thenIter ι h (proj₁ (run ι h (approx r m))) (proj₂ (run ι h (approx r m))) f
run-approx-iter ι h r m f = run-approx-iterB ι h r (force m) f

-- The value a budgeted run returned.
done-value : ∀ {X} {v v′ : X} {r r′ : ℕ} → returns (done v r) ≡ returns (done v′ r′) → v ≡ v′
done-value refl = refl

-- How a budgeted run is OBSERVED to end: returned, halted, or — cut — not
-- (yet): the run goes on past the budget.
open import Once.Spec.Trace using (End; returned; halted)

endAp : ∀ {X} → Res (Ap X) → Maybe (End ⊤)
endAp (returns (done _ _)) = just (returned tt)
endAp stopped              = just halted
endAp (returns cut)        = nothing

------------------------------------------------------------------------
-- A budgeted run never GAINS budget: what is left when it returns is at
-- most what it was given (each silent step spends one unit).
------------------------------------------------------------------------

open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n)

mutual
  done-≤B : ∀ {X} (ι : Interp) (h : List SigOpEvent) (r : ℕ) (b : T (X ⊎ T∞ X)) {v : X} {r′ : ℕ}
          → proj₂ (run ι h (approxBlock r b)) ≡ returns (done v r′) → r′ ≤ r
  done-≤B ι h r       (ret (inj₁ x)) refl = ≤-refl
  done-≤B ι h zero    (ret (inj₂ m)) ()
  done-≤B ι h (suc r) (ret (inj₂ m)) e    = m≤n⇒m≤1+n (done-≤B ι h r (force m) e)
  done-≤B ι h r       (call o a k)   e    = done-≤-call ι h r o a k (callAnswer ι h o a) e
  done-≤B ι h r       (halt o a)     ()

  done-≤-call : ∀ {X} (ι : Interp) (h : List SigOpEvent) (r : ℕ) (o : CallOp) (a : M.⟦ cdom o ⟧)
                  (k : M.⟦ ccod o ⟧ → T (X ⊎ T∞ X)) (mb : Maybe M.⟦ ccod o ⟧) {v : X} {r′ : ℕ}
              → proj₂ (run-call ι h o a (λ b → approxBlock r (k b)) mb) ≡ returns (done v r′) → r′ ≤ r
  done-≤-call ι h r o a k (just b) e = done-≤B ι (h ++ [ callEvent o a ]) r (k b) e
  done-≤-call ι h r o a k nothing  ()

done-≤ : ∀ {X} (ι : Interp) (h : List SigOpEvent) (r : ℕ) (m : T∞ X) {v : X} {r′ : ℕ}
       → proj₂ (run ι h (approx r m)) ≡ returns (done v r′) → r′ ≤ r
done-≤ ι h r m = done-≤B ι h r (force m)
