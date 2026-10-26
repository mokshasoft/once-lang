{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecObserve — related computations are observed the same
-- (plan 0.121 §3.5; plan 0.122 §5.5: a Spec computation against an
-- implementation run, `SpecRun`).
--
-- The compiler observes a computation as its trace machine's run against an
-- interpretation (`TraceTr.trT∞`), the Spec as its trace in a world
-- (`Observation.trace`). On related trees the two go in lockstep: the end of a
-- block is a silent step on both sides, a call shows the same event and goes
-- on with related answers, a halt shows its call and ends. So the traces are
-- the same (`observe-R`), given that the interpretation and the world agree on
-- every related call (`Agree`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecObserve (Σ : Signature) where

open import Data.Empty using (⊥-elim)
import Data.Empty
open import Data.List using (List; []; _∷_; _++_; [_]; map)
open import Data.List.Properties using (map-++)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Spec.Word using (Carrier)
import Once.IR.Semantics.Value Carrier Carrier as V
open import Once.IR.Semantics.Event using (SigOpEvent; toEvent)
import Once.IR.Semantics.Trace as LTr
import Once.IR.Semantics.Iterative as LI
open import Once.Denotation.TraceTr using (trT∞; δ∞; Conf)
import Once.Denotation.TraceTr as TT
open import Once.Adequacy.MachineTrace using (module Machine; listTr)
open import Once.Spec.Signature using (Op; module Op; arg; NotEmpty; notEmpty?; Event; eventOf; ⟦_⟧ᵇ; call)
open Op using (ans)
open import Once.Spec.Delay using (Delay; module Delay; now; _⇓_; now⇓; later⇓; _≈⟨_⟩_)
open Delay using (step)
open import Once.Spec.Trace using (Tr; module Tr; End; returned; halted; EndRel; returned≈; halted≈; StepRel; _≈ᵗ⟨_⟩_; module _≈ᵗ⟨_⟩_)
open Tr using (next)
open _≈ᵗ⟨_⟩_ using (same)
open import Once.Spec.Observation Σ using (World; module World; trace; blockD; after)
import Once.Spec.Effect Σ as SE
open import Once.Adequacy.SpecRun Σ
open RunR using (forceR)

------------------------------------------------------------------------
-- The interpretation and the world agree on related calls
------------------------------------------------------------------------

record Agree (ι : LTr.Interp) (w : World) : Set where
  field
    -- a related call has an answer, and is answered by the related one: the
    -- world's at the inhabitant its answer type is decided to have
    answered : ∀ {o o′} (c : CallR o o′) {a a′} → argR c a a′ → ∀ h
             → NotEmpty (ans o)
               × (∀ p → notEmpty? (ans o) ≡ yes p
                  → Σ[ b ∈ V.⟦ LTr.CallOp.ccod o′ ⟧ ] (LTr.callAnswer ι h o′ a′ ≡ just b)
                      × ansR c (World.answer w o (map toEvent h) a p) b)
    -- and shows the same event
    call-event : ∀ {o o′} (c : CallR o o′) {a a′} → argR c a a′ → toEvent (LTr.callEvent o′ a′) ≡ eventOf o a
    -- a halt shows its call, and the Spec's call answers nothing
    halt-event : ∀ {o o′} (h : HaltR o o′) {a a′} → hargR h a a′ → toEvent (LTr.haltEvent o′ a′) ≡ eventOf o a
    halt-void  : ∀ {o o′} → HaltR o o′ → ¬ NotEmpty (ans o)

------------------------------------------------------------------------
-- Two traces in lockstep
------------------------------------------------------------------------

private
  S′ : Set
  S′ = End ⊤ ⊎ (Event × Tr ⊤)

  SR : S′ → S′ → Set
  SR = StepRel _≡_ (λ u u′ → u ≈ᵗ⟨ _≡_ ⟩ u′)

mutual
  -- the two traces take their steps together
  record TLS (t t′ : Tr ⊤) : Set where
    coinductive
    field tls : LS (next t) (next t′)

  record LS (d d′ : Delay S′) : Set where
    coinductive
    field ls : StepLS (step d) (step d′)

  data StepLS : S′ ⊎ Delay S′ → S′ ⊎ Delay S′ → Set where
    nowEnd  : ∀ {e e′} → EndRel _≡_ e e′ → StepLS (inj₁ (inj₁ e)) (inj₁ (inj₁ e′))
    nowCall : ∀ {v v′ t t′} → v ≡ v′ → TLS t t′ → StepLS (inj₁ (inj₂ (v , t))) (inj₁ (inj₂ (v′ , t′)))
    laterLS : ∀ {d d′} → LS d d′ → StepLS (inj₂ d) (inj₂ d′)
open TLS
open LS

-- In lockstep, two traces are the same. (The convergence on the other side
-- is threaded as a continuation, so that every recursive call is in tail
-- position and the corecursive one sits directly under the pairs.)
TLS⇒≈ : ∀ {t t′} → TLS t t′ → t ≈ᵗ⟨ _≡_ ⟩ t′
private
  fwd : ∀ {d d′ d″} → LS d d′ → (∀ {b} → d′ ⇓ b → d″ ⇓ b) → ∀ a → d ⇓ a → ∃[ b ] (d″ ⇓ b × SR a b)
  fwd-now : ∀ {d′ d″ a x} → x ≡ step d′ → (∀ {b} → d′ ⇓ b → d″ ⇓ b) → StepLS (inj₁ a) x → ∃[ b ] (d″ ⇓ b × SR a b)
  fwd-later : ∀ {d′ d″ d₁ a x} → x ≡ step d′ → (∀ {b} → d′ ⇓ b → d″ ⇓ b) → StepLS (inj₂ d₁) x → d₁ ⇓ a
            → ∃[ b ] (d″ ⇓ b × SR a b)
  bwd : ∀ {d d′ d″} → LS d d′ → (∀ {a} → d ⇓ a → d″ ⇓ a) → ∀ b → d′ ⇓ b → ∃[ a ] (d″ ⇓ a × SR a b)
  bwd-now : ∀ {d d″ b x} → x ≡ step d → (∀ {a} → d ⇓ a → d″ ⇓ a) → StepLS x (inj₁ b) → ∃[ a ] (d″ ⇓ a × SR a b)
  bwd-later : ∀ {d d″ d₁′ b x} → x ≡ step d → (∀ {a} → d ⇓ a → d″ ⇓ a) → StepLS x (inj₂ d₁′) → d₁′ ⇓ b
            → ∃[ a ] (d″ ⇓ a × SR a b)

same (TLS⇒≈ r) = (λ a p → fwd (tls r) (λ q → q) a p) , (λ b p → bwd (tls r) (λ q → q) b p)

fwd {d} {d′} r k a (now⇓ q)     = fwd-now refl k (subst (λ s → StepLS s (step d′)) q (ls r))
fwd {d} {d′} r k a (later⇓ q x) = fwd-later refl k (subst (λ s → StepLS s (step d′)) q (ls r)) x
fwd-now e k (nowEnd x)     = _ , k (now⇓ (sym e)) , x
fwd-now e k (nowCall v tl) = _ , k (now⇓ (sym e)) , v , TLS⇒≈ tl
fwd-later e k (laterLS r₁) x = fwd r₁ (λ q → k (later⇓ (sym e) q)) _ x

bwd {d} {d′} r k b (now⇓ q)     = bwd-now refl k (subst (λ s → StepLS (step d) s) q (ls r))
bwd {d} {d′} r k b (later⇓ q x) = bwd-later refl k (subst (λ s → StepLS (step d) s) q (ls r)) x
bwd-now e k (nowEnd x)     = _ , k (now⇓ (sym e)) , x
bwd-now e k (nowCall v tl) = _ , k (now⇓ (sym e)) , v , TLS⇒≈ tl
bwd-later e k (laterLS r₁) x = bwd r₁ (λ q → k (later⇓ (sym e) q)) _ x

------------------------------------------------------------------------
-- Related computations, observed
------------------------------------------------------------------------

module _ (ι : LTr.Interp) (w : World) (ag : Agree ι w) {X : Set} {R : ⊤ → X → Set} where
  open Agree ag
  private
    module M = Machine (δ∞ ι {X})

    haltLS : TLS (listTr [] halted) (record { next = now (inj₁ halted) })
    ls (tls haltLS) = nowEnd halted≈

    hist : ∀ {h h′} (e : map toEvent h ≡ h′) (ce : SigOpEvent) {v} → toEvent ce ≡ v
         → map toEvent (h ++ [ ce ]) ≡ h′ ++ [ v ]
    hist {h} refl ce refl = map-++ toEvent h [ ce ]

    just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
    just-inj refl = refl

  -- (`b` the Spec's block, `b′` the implementation's)
  blockLS : ∀ {h h′ b b′} → map toEvent h ≡ h′ → BlockR (SumR R (RunR R)) b b′
          → LS (M.go (δ∞ ι (h , b′))) (blockD w h′ b)
  callStep : ∀ {h h′ o o′ a a′ k k′} (c : CallR o o′) → map toEvent h ≡ h′ → (ra : argR c a a′)
           → (∀ {b b′} → ansR c b b′ → BlockR (SumR R (RunR R)) (k b) (k′ b′))
           → ∀ mb → LTr.callAnswer ι h o′ a′ ≡ mb
           → StepLS (step (M.go (TT.answer ι h o′ a′ k′ mb)))
                    (inj₁ (inj₂ (eventOf o a , after w h′ o a k (notEmpty? (ans o)))))
  afterR  : ∀ {h h′ o o′ a a′ k k′ b′} (c : CallR o o′) → map toEvent h ≡ h′ → argR c a a′
          → (∀ {b b′} → ansR c b b′ → BlockR (SumR R (RunR R)) (k b) (k′ b′))
          → NotEmpty (ans o) → (∀ p → notEmpty? (ans o) ≡ yes p → ansR c (World.answer w o h′ a p) b′)
          → ∀ dec → notEmpty? (ans o) ≡ dec → TLS (M.tr [] (h ++ [ LTr.callEvent o′ a′ ] , k′ b′)) (after w h′ o a k dec)
  haltR   : ∀ {h′ o o′ a a′ k} (hh : HaltR o o′) → hargR hh a a′
          → ∀ dec → TLS (listTr [] halted) (after w h′ o a k dec)

  ls (blockLS e (ret (left r)))  = nowEnd (returned≈ refl)
  ls (blockLS e (ret (right r))) = laterLS (blockLS e (forceR r))
  ls (blockLS {h} e (call {o′ = o′} {a′ = a′} c ra k)) = callStep c e ra k (LTr.callAnswer ι h o′ a′) refl
  ls (blockLS e (halt hh ra)) = nowCall (halt-event hh ra) (haltR hh ra (notEmpty? _))

  callStep {h} {k = kk} {k′ = kk′} c e ra k (just b′) q =
    nowCall (call-event c ra) (afterR {k = kk} {k′ = kk′} c e ra k (proj₁ (answered c ra h)) ans₀ (notEmpty? _) refl)
    where
      ans₀ : ∀ p → notEmpty? _ ≡ yes p → ansR c (World.answer w _ _ _ p) b′
      ans₀ p d = from (proj₂ (answered c ra h) p d)
        where
          from : _ → _
          from (b , eq , r) = subst (λ x → ansR c (World.answer w _ _ _ p) x) (just-inj (trans (sym eq) q))
                                    (subst (λ hh → ansR c (World.answer w _ hh _ p) b) e r)
  callStep {h} {h′} {o} {o′} {a} {a′} {kk} {kk′} c e ra k nothing q = no-answer (notEmpty? (ans o)) refl
    where
      just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → Data.Empty.⊥
      just≢nothing ()
      no-answer : ∀ dec → notEmpty? (ans o) ≡ dec
                → StepLS (step (M.go (TT.answer ι h o′ a′ kk′ nothing)))
                         (inj₁ (inj₂ (eventOf o a , after w h′ o a kk (notEmpty? (ans o)))))
      no-answer (yes p) d = ⊥-elim (just≢nothing (trans (sym (proj₁ (proj₂ (proj₂ (answered c ra h) p d)))) q))
      no-answer (no ¬p) d = ⊥-elim (¬p (proj₁ (answered c ra h)))

  tls (afterR {o′ = o′} {a′ = a′} c e ra k ne hans (yes p) d) = blockLS (hist e (LTr.callEvent o′ a′) (call-event c ra)) (k (hans p d))
  afterR c e ra k ne hans (no ¬p) d = ⊥-elim (¬p ne)

  haltR hh ra (yes p) = ⊥-elim (halt-void hh p)
  tls (haltR hh ra (no _)) = tls haltLS

  observeLS : ∀ {h m m′} → RunR R m m′ → TLS (trT∞ ι h m′) (trace w (map toEvent h) m)
  tls (observeLS r) = blockLS refl (forceR r)

  -- Related computations have the same trace.
  observe-R : ∀ {h m m′} → RunR R m m′ → trT∞ ι h m′ ≈ᵗ⟨ _≡_ ⟩ trace w (map toEvent h) m
  observe-R r = TLS⇒≈ (observeLS r)
