-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Witness.Echo — a server is typed, and it runs forever:
-- at every depth `n` its observation has exactly `n` events
-- (`Spec.Metatheory.Totality`, D311, plan 0.117 E2).
--
-- The server is `Spec.Totality.echoServer`, `iter step ()` with
-- `step = λ _ → inr (λ _ → inr (write (read ())))`. Each round is two calls; a `Unit`
-- call is answered by the protocol and `read` by the implementation, so
-- under ANY implementation every call is answered and the run never stops.
------------------------------------------------------------------------

module Once.Metatheory.Witness.Echo where

open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Type.Grade using (pure; eff⁺; eff; Zero; Many)
open import Once.Spec.Type using (Unit; Void; _⇒[_]_; _+_)
open import Once.Spec.Type.Grade using (mk-kind)
open import Once.Spec.Type.WellFormed using (con-fun; base-Int; base-Unit; rf-Int; rf-Unit; rf-⇒)
open import Once.Spec.Context using (∅; []; _,_^_)
open import Once.Spec.Totality using (echoDefs; readN; writeN; echoStep; echoServer)
open import Once.Spec.Core.Typing echoDefs

step-typed : ∅ ⊢[ [] ] echoStep ∷ Unit ⇒[ mk-kind Many pure ] (Void + (Unit ⇒[ mk-kind Many eff⁺ ] (Void + Unit))) ! pure
step-typed =
  ⊢lam {q' = Zero} refl
    (⊢inr (⊢lam {q' = Zero} refl
      (⊢inr (⊢app (⊢sigop writeN (con-fun base-Int base-Unit) tt (rf-⇒ rf-Int rf-Unit) (there (here refl)))
                  (⊢app (⊢sigop readN (con-fun base-Unit base-Int) tt (rf-⇒ rf-Unit rf-Int) (here refl)) ⊢unit)))))

server-typed : ∅ ⊢[ [] ] echoServer ∷ Void ! eff
server-typed = ⊢iter step-typed ⊢unit

------------------------------------------------------------------------
-- A step that always loops and whose every call is answered: its iteration
-- observes exactly `n` events at depth `n`, from any history.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
import Data.List
open import Data.List using (List; length; _++_; [_])
open import Data.Maybe using (Maybe; just)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Once.Spec.Event using (SigOpEvent)
open import Once.Spec.Trace using (Interp; CallOp; callAnswer; callEvent)
open import Once.Spec.Guarded using (T⁺; call⁺; halt⁺; iter∞; iterStart∞; iterRoot∞; iterTree∞; iterLayer∞)
open import Once.Spec.Iterative using (T∞; T∞F; ret∞; events∞; eventsF; eventsC; call∞; module T∞)
open T∞ using (force)

module Forever (ι : Interp) where
  -- A call the world answers, whatever happened before.
  Answered : (o : CallOp) → _ → Set
  Answered o x = ∀ (h : List SigOpEvent) → ∃[ b ] (callAnswer ι h o x ≡ just b)

  -- The rest of a round, node by node: answered calls, then a loop.
  data Loops {A : Set} : T∞F (⊥ ⊎ A) (T∞ (⊥ ⊎ A)) → Set where
    loops : ∀ a → Loops (ret∞ (inj₂ a))
    calls : ∀ {o x k} → Answered o x → (∀ b → Loops (force (k b))) → Loops (call∞ o x k)

  -- A round: an answered call first (the guard), then the rest.
  Round : ∀ {A : Set} → T⁺ (⊥ ⊎ A) → Set
  Round (call⁺ o x k) = Answered o x × (∀ b → Loops (force (k b)))
  Round (halt⁺ o x)   = ⊥

  -- A step that never takes the pure exit (there is no `⊥` to exit with).
  Step : ∀ {A : Set} → ⊥ ⊎ T⁺ (⊥ ⊎ A) → Set
  Step (inj₁ ())
  Step (inj₂ m) = Round m

  module _ {A : Set} (f : A → ⊥ ⊎ T⁺ (⊥ ⊎ A)) (rf : ∀ a → Step (f a)) where
    eventsC-just : ∀ {X} h o x (k : _ → T∞ X) (r : Maybe _) b → r ≡ just b → ∀ n
                 → length (eventsC ι h o x k r n) ≡ suc (length (events∞ ι (h ++ [ callEvent o x ]) (k b) n))
    eventsC-just h o x k .(just b) b refl n = refl

    runs-start : ∀ (s : ⊥ ⊎ T⁺ (⊥ ⊎ A)) → Step s → ∀ h n → length (eventsF ι h (iterStart∞ f s) n) ≡ suc n
    runs-root  : ∀ (m : T⁺ (⊥ ⊎ A)) → Round m → ∀ h n → length (eventsF ι h (iterRoot∞ f m) n) ≡ suc n
    runs-tree  : ∀ (t : T∞ (⊥ ⊎ A)) → Loops (force t) → ∀ h n → length (events∞ ι h (iterTree∞ f t) n) ≡ n
    runs-layer : ∀ (l : T∞F (⊥ ⊎ A) (T∞ (⊥ ⊎ A))) → Loops l → ∀ h n → length (eventsF ι h (iterLayer∞ f l) n) ≡ suc n
    runs-start (inj₁ ()) r h n
    runs-start (inj₂ m)  r h n = runs-root m r h n
    runs-root (call⁺ o x k) (ans , lk) h n =
      trans (eventsC-just h o x _ (callAnswer ι h o x) (proj₁ (ans h)) (proj₂ (ans h)) n)
            (cong suc (runs-tree (k (proj₁ (ans h))) (lk _) _ n))
    runs-tree t l h zero    = refl
    runs-tree t l h (suc n) = runs-layer (force t) l h n
    runs-layer (ret∞ (inj₂ a)) (loops .a) h n = runs-start (f a) (rf a) h n
    runs-layer (call∞ o x k) (calls ans lk) h n =
      trans (eventsC-just h o x _ (callAnswer ι h o x) (proj₁ (ans h)) (proj₂ (ans h)) n)
            (cong suc (runs-tree (k (proj₁ (ans h))) (lk _) _ n))

    runs : ∀ a h n → length (events∞ ι h (iter∞ f a) n) ≡ n
    runs a h zero    = refl
    runs a h (suc n) = runs-start (f a) (rf a) h n

------------------------------------------------------------------------
-- The echo server runs forever, under every implementation.
------------------------------------------------------------------------

open import Once.Spec.Core.Meaning echoDefs
open import Once.Spec.Totality using (echoSig)
open import Once.Spec.Trace using (interp)
open import Once.Spec.Graded using (_>>=ᵖ_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

module _ fmt (ds : DefSem) where
  private
    ι = interp echoSig (impl ds)
    open Forever ι
    -- the step's meaning, its round run (as `⟦ ⊢iter ⟧` reads it)
    step : ⊤ → ⊥ ⊎ T⁺ (⊥ ⊎ ⊤)
    step a = map₂ (λ th → th tt) (⟦ step-typed ⟧ fmt ds tt a)

  opaque
    unfolding _>>=ᵖ_
    server≡ : ⟦ server-typed ⟧ fmt ds tt ≡ iter∞ step tt
    server≡ = refl

    round : ∀ a → Step (step a)
    round a = (λ h → _ , refl) , λ b → calls (λ h → _ , refl) (λ _ → loops _)

  server-runs : ∀ n → length (events∞ ι Data.List.[] (⟦ server-typed ⟧ fmt ds tt) n) ≡ n
  server-runs n = subst (λ m → length (events∞ ι Data.List.[] m n) ≡ n) (sym server≡)
                        (runs step round tt Data.List.[] n)
