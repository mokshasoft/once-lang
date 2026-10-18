{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Run — a run to a depth, as an inductive relation.
--
-- `Run w h m n d e`: in the world `w`, which has seen `h`, the computation
-- `m` observed to `n` visible steps makes the calls `d` and ends `e` (`just`
-- an end, `nothing` cut at the depth). It is exactly the trace's depth-`n`
-- observation (`run-sound`, `run-complete`), with the silent steps unrolled
-- into the derivation: a block's end is a step of the derivation
-- (`rb-next`), so a silent loop has no run past depth zero. Stated
-- inductively, runs compose by plain induction (`Once.Metatheory.RunLaws`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Run (Σ : Signature) where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Spec.Signature using (Event; eventOf; Op; module Op; arg; ⟦_⟧ᵇ; NotEmpty; notEmpty?)
open Op using (ans)
open import Once.Spec.Effect Σ
open import Once.Spec.Observation Σ using (World; module World; History; trace; blockD; after)
open import Once.Spec.Trace using (End; returned; halted; Tr; module Tr; Calls; none)
import Once.Spec.Trace
open import Once.Spec.Delay using (Delay; module Delay; now; _⇓_; now⇓; later⇓)
open import Once.Metatheory.Trace Σ using (Obs; pre; preStep; bindD; bind⇓; bind⇓⁻; nowInv)

open Delay using (step)
open Tr using (next)

module _ (w : World) where
  open World w using (answer)

  data RunB {X : Set} : History → T (X ⊎ T∞ X) → ℕ → History → Maybe (End X) → Set
  data RunA {X : Set} (h : History) (o : Op Σ) (a : ⟦ arg o ⟧ᵇ) (k : ⟦ ans o ⟧ᵇ → T (X ⊎ T∞ X))
       : Dec (NotEmpty (ans o)) → ℕ → History → Maybe (End X) → Set

  data RunB {X} where
    rb-cut  : ∀ {h t} → RunB h t zero [] nothing
    rb-ret  : ∀ {h x n} → RunB h (roll (done (inj₁ x))) (suc n) [] (just (returned x))
    rb-next : ∀ {h m n d e} → RunB h (force m) (suc n) d e → RunB h (roll (done (inj₂ m))) (suc n) d e
    rb-call : ∀ {h o a k n d e}
            → RunA h o a k (notEmpty? (ans o)) n d e
            → RunB h (roll (node (call o a k))) (suc n) (eventOf o a ∷ d) e

  data RunA {X} h o a k where
    ra-go   : ∀ {p n d e} → RunB (h ++ [ eventOf o a ]) (k (answer o h a p)) n d e → RunA h o a k (yes p) n d e
    ra-halt : ∀ {¬p n} → RunA h o a k (no ¬p) (suc n) [] (just halted)
    ra-cut  : ∀ {¬p} → RunA h o a k (no ¬p) zero [] nothing

  -- A run of the computation itself (so `m` is known from the type).
  record Run {X : Set} (h : History) (m : T∞ X) (n : ℕ) (d : History) (e : Maybe (End X)) : Set where
    constructor run
    field unrun : RunB h (force m) n d e

  ----------------------------------------------------------------------
  -- A run is the trace's observation to its depth
  ----------------------------------------------------------------------

  -- The trace of a block.
  blk : ∀ {X} → History → T (X ⊎ T∞ X) → Tr X
  next (blk h t) = blockD w h t

  private
    preTrace : ∀ {X} h (m : T∞ X) n → pre n (trace w h m) ≡ pre n (blk h (force m))
    preTrace h m zero    = refl
    preTrace h m (suc n) = refl

    preAfter : ∀ {X} h (o : Op Σ) a (k : ⟦ ans o ⟧ᵇ → T (X ⊎ T∞ X)) p n
             → pre n (after w h o a k (yes p)) ≡ pre n (blk (h ++ [ eventOf o a ]) (k (answer o h a p)))
    preAfter h o a k p zero    = refl
    preAfter h o a k p (suc n) = refl

  runB-sound : ∀ {X h t n d} {e : Maybe (End X)} → RunB h t n d e → pre n (blk h t) ⇓ (d , e)
  runA-sound : ∀ {X h o a k D n d} {e : Maybe (End X)} → RunA h o a k D n d e → pre n (after w h o a k D) ⇓ (d , e)
  runB-sound rb-cut = now⇓ refl
  runB-sound rb-ret = bind⇓ (now⇓ refl) (now⇓ refl)
  runB-sound {h = h} {n = suc n} (rb-next {m = m} r) = go (bind⇓⁻ (blockD w h (force m)) (preStep n) (runB-sound r))
    where go : ∀ {o} → ∃[ s ] (blockD w h (force m) ⇓ s × preStep n s ⇓ o) → bindD (blockD w h (roll (done (inj₂ m)))) (preStep n) ⇓ o
          go (s , a , p) = bind⇓ (later⇓ refl a) p
  runB-sound (rb-call r) = bind⇓ (now⇓ refl) (bind⇓ (runA-sound r) (now⇓ refl))
  runA-sound {h = h} {o} {a} {k} {n = n} (ra-go {p} r) = subst (_⇓ _) (sym (preAfter h o a k p n)) (runB-sound r)
  runA-sound ra-halt = bind⇓ (now⇓ refl) (now⇓ refl)
  runA-sound ra-cut  = now⇓ refl

  run-sound : ∀ {X h} {m : T∞ X} {n d e} → Run h m n d e → pre n (trace w h m) ⇓ (d , e)
  run-sound {h = h} {m} {n} (run r) = subst (_⇓ _) (sym (preTrace h m n)) (runB-sound r)

  -- What the observation arrives at is a run.
  MadeB : ∀ {X} → History → T (X ⊎ T∞ X) → ℕ → Obs X → Set
  MadeB h t n o = ∃[ d ] ∃[ e ] (o ≡ (d , e) × RunB h t n d e)

  private
    MadeA : ∀ {X} → History → (o : Op Σ) → ⟦ arg o ⟧ᵇ → (⟦ ans o ⟧ᵇ → T (X ⊎ T∞ X)) → Dec (NotEmpty (ans o)) → ℕ → Obs X → Set
    MadeA h o a k D n ob = ∃[ d ] ∃[ e ] (ob ≡ (d , e) × RunA h o a k D n d e)

  completeB : ∀ {X} h (t : T (X ⊎ T∞ X)) n {ob} → pre n (blk h t) ⇓ ob → MadeB h t n ob
  completeS : ∀ {X} h (t : T (X ⊎ T∞ X)) n {s ob} → blockD w h t ⇓ s → preStep n s ⇓ ob → MadeB h t (suc n) ob
  completeA : ∀ {X} h (o : Op Σ) a (k : ⟦ ans o ⟧ᵇ → T (X ⊎ T∞ X)) (D : Dec (NotEmpty (ans o))) n {ob}
            → pre n (after w h o a k D) ⇓ ob → MadeA h o a k D n ob
  completeB h t zero    p = [] , nothing , sym (nowInv p) , rb-cut
  completeB h t (suc n) p = split (bind⇓⁻ (blockD w h t) (preStep n) p)
    where split : ∀ {ob} → ∃[ s ] (blockD w h t ⇓ s × preStep n s ⇓ ob) → MadeB h t (suc n) ob
          split (s , a , ps) = completeS h t n a ps
  completeS h (roll (done (inj₁ x))) n (now⇓ refl) ps = [] , just (returned x) , sym (nowInv ps) , rb-ret
  completeS h (roll (done (inj₁ x))) n (later⇓ () _) ps
  completeS h (roll (done (inj₂ m))) n (now⇓ ()) ps
  completeS h (roll (done (inj₂ m))) n (later⇓ refl a) ps = wrap (completeS h (force m) n a ps)
    where wrap : ∀ {ob} → MadeB h (force m) (suc n) ob → MadeB h (roll (done (inj₂ m))) (suc n) ob
          wrap (d , e , eq , r) = d , e , eq , rb-next r
  completeS h (roll (node (call o a k))) n (now⇓ refl) ps = wrap (bind⇓⁻ (pre n (after w h o a k (notEmpty? (ans o)))) _ ps)
    where
      wrap : ∀ {ob} → ∃[ o₁ ] (pre n (after w h o a k (notEmpty? (ans o))) ⇓ o₁ × now (eventOf o a ∷ proj₁ o₁ , proj₂ o₁) ⇓ ob)
           → MadeB h (roll (node (call o a k))) (suc n) ob
      wrap (o₁ , o₁⇓ , q) = fin (nowInv q) (completeA h o a k (notEmpty? (ans o)) n o₁⇓)
        where fin : ∀ {ob} → (eventOf o a ∷ proj₁ o₁ , proj₂ o₁) ≡ ob → MadeA h o a k (notEmpty? (ans o)) n o₁
                  → MadeB h (roll (node (call o a k))) (suc n) ob
              fin refl (d , e , refl , r) = eventOf o a ∷ d , e , refl , rb-call r
  completeS h (roll (node (call o a k))) n (later⇓ () _) ps
  completeA h o a k (yes p) n q = wrap (completeB (h ++ [ eventOf o a ]) (k (answer o h a p)) n (subst (_⇓ _) (preAfter h o a k p n) q))
    where wrap : ∀ {ob} → MadeB (h ++ [ eventOf o a ]) (k (answer o h a p)) n ob → MadeA h o a k (yes p) n ob
          wrap (d , e , eq , r) = d , e , eq , ra-go r
  completeA h o a k (no ¬p) zero    q = [] , nothing , sym (nowInv q) , ra-cut
  completeA h o a k (no ¬p) (suc n) q = fin (bind⇓⁻ (now (inj₁ halted)) (preStep n) q)
    where fin : ∀ {ob} → ∃[ s ] (now (inj₁ halted) ⇓ s × preStep n s ⇓ ob) → MadeA h o a k (no ¬p) (suc n) ob
          fin (s , s⇓ , ps) = at (nowInv s⇓) ps
            where at : ∀ {s ob} → inj₁ halted ≡ s → preStep n s ⇓ ob → MadeA h o a k (no ¬p) (suc n) ob
                  at refl ps′ = [] , just halted , sym (nowInv ps′) , ra-halt

  -- What the trace's observation arrives at is a run, and the calls it made.
  Made : ∀ {X} → History → T∞ X → ℕ → Obs X → Set
  Made h m n ob = ∃[ d ] ∃[ e ] (ob ≡ (d , e) × Run h m n d e)

  run-complete : ∀ {X} h (m : T∞ X) n {ob} → pre n (trace w h m) ⇓ ob → Made h m n ob
  run-complete h m n p = wrap (completeB h (force m) n (subst (_⇓ _) (preTrace h m n) p))
    where wrap : ∀ {ob} → MadeB h (force m) n ob → Made h m n ob
          wrap (d , e , eq , r) = d , e , eq , run r

  ----------------------------------------------------------------------
  -- A run's calls are calls the trace makes
  ----------------------------------------------------------------------

  private
    -- The calls a delayed step makes first.
    data CallsD {X : Set} : Delay (End X ⊎ (Event × Tr X)) → List Event → Set where
      noneD : ∀ {D} → CallsD D []
      callD : ∀ {D v t′ vs} → D ⇓ inj₂ (v , t′) → Calls t′ vs → CallsD D (v ∷ vs)

    toCalls : ∀ {X} {t : Tr X} {vs} → CallsD (next t) vs → Calls t vs
    toCalls noneD       = none
    toCalls (callD p c) = Once.Spec.Trace.call p c

    callsB : ∀ {X h t n d} {e : Maybe (End X)} → RunB h t n d e → CallsD (blockD w h t) d
    callsA : ∀ {X h o a k D n d} {e : Maybe (End X)} → RunA h o a k D n d e → Calls (after w h o a k D) d
    callsB rb-cut      = noneD
    callsB rb-ret      = noneD
    callsB (rb-next r) = later refl (callsB r)
      where later : ∀ {X} {D D′ : Delay (End X ⊎ (Event × Tr X))} {vs} → step D ≡ inj₂ D′ → CallsD D′ vs → CallsD D vs
            later q noneD       = noneD
            later q (callD p c) = callD (later⇓ q p) c
    callsB (rb-call r) = callD (now⇓ refl) (callsA r)
    callsA (ra-go r) = toCalls (callsB r)
    callsA ra-halt   = none
    callsA ra-cut    = none

  run-calls : ∀ {X h} {m : T∞ X} {n d e} → Run h m n d e → Calls (trace w h m) d
  run-calls (run r) = toCalls (callsB r)
