-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Denotation.FaithfulLemmas — reusable coherence lemmas for the
-- `faithful` proof's recursion-scheme cases (`cata`/`ana`).
--
-- Extracted from `SourceFaithful` (per the extract-proofs-from-where
-- discipline) so each lemma's typecheck cost stays bounded and so the
-- pieces are independently reusable:
--
--   * `forget-inject`     — `forget ∘ inject ≡ id` (round-trip; the
--                           monadic/pure value domains agree on injected
--                           values). Induction on the type.
------------------------------------------------------------------------

module Once.Denotation.FaithfulLemmas where

open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

open import Once.Type using (Type; Unit; Void; Int; Str; Float; Buffer;
                              _*_; _+_; _⇒[_]_; μ-type; ν-type; Functor; ⟦_⟧T;
                              Purity; mk-kind; Many)
open import Once.CCC.Eval as Val using ()
open import Once.CCC.IR using (IR; _∘_; ⟨_,_⟩; apply; curry; terminal; id; snd; Cata; Ana)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Semantics.Machine using (sem-cata; sem-ana; coerce-functor; coerce-functor⁻¹; sem-fmap)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; ∅; zeroUsage; ⟦_⟧ᶜ)
open import Once.Surface.Elaborate using (elaborate)
import Once.Compile as C
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceMonad using (T; returnT; valueT; projTrace; _>>=T_)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; evalᴰ; cata-ev-algᴰ; ana-events; forget; inject)
open import Once.Denotation.TraceDenote using (events-F)
import Once.Denotation.SourceDenote as SD
open import Once.Postulates using (extensionality)

open Once.Surface.Syntax.Expr

------------------------------------------------------------------------
-- `forget ∘ inject ≡ id`. At every first-order type `inject`/`forget`
-- are the identity, so `refl`. At the arrow, `inject` wraps the pure
-- function as a trace-less closure and `forget` runs it at depth `zero`
-- and drops the (empty) trace — the round-trip collapses to the original
-- function by extensionality, using the round-trips at the smaller
-- domain/codomain types (`A`, `B`).
------------------------------------------------------------------------

forget-inject : ∀ {A} (v : Val.⟦ A ⟧) → forget {A} (inject {A} v) ≡ v
forget-inject {Unit}   v        = refl
forget-inject {Void}   ()
forget-inject {Int}    v        = refl
forget-inject {Float}  v        = refl
forget-inject {Str}    v        = refl
forget-inject {Buffer} v        = refl
forget-inject {μ-type F} v      = refl
forget-inject {ν-type F} v      = refl
forget-inject {A * B}  (a , b)  = cong₂ _,_ (forget-inject {A} a) (forget-inject {B} b)
forget-inject {A + B}  (inj₁ a) = cong inj₁ (forget-inject {A} a)
forget-inject {A + B}  (inj₂ b) = cong inj₂ (forget-inject {B} b)
forget-inject {A ⇒[ k ] B} pf   =
  extensionality (λ va →
    trans (cong (λ z → forget (inject (pf z))) (forget-inject {A} va))
          (forget-inject {B} (pf va)))

------------------------------------------------------------------------
-- Closure-bridge — replaces the retired `build-pure`. The elaborated
-- closed-morphism IR (`apply ∘ ⟨ elab morph ∘ terminal , id ⟩`) applied to
-- `w` equals BINDING the source morphism computation `⟦morph⟧ˢ tt` and
-- applying it to `w`. Pure monad reduction (the `returnT`/`terminal`
-- left-identities are definitional; the only residual is `++ []`, i.e.
-- `++-identityʳ`), given the morphism IH. NO purity assumption — the
-- algebra's build trace is THREADED, not discarded. This is exactly what
-- lets `cata`/`ana` drop `build-pure` once `⟦_⟧ˢ` threads the algebra
-- computation per layer (matching `evalᴰ`'s per-layer `evalᴰ alg`).
------------------------------------------------------------------------

morph-app-bridge : ∀ {D E kk} (morph : Expr ∅ zeroUsage (D ⇒[ kk ] E))
                     (ih : ∀ j → evalᴰ (elaborate C.Heap morph) tt j ≡ SD.⟦ morph ⟧ˢ tt j)
                     (w : ⟦ D ⟧ᴰ) (n : ℕ)
                   → evalᴰ (apply ∘ ⟨ elaborate C.Heap morph ∘ terminal , id ⟩ C.Heap) w n
                     ≡ (SD.⟦ morph ⟧ˢ tt >>=T (λ clo → clo w)) n
morph-app-bridge morph ih w n rewrite ih n =
  cong₂ _,_
    (cong (_++ proj₁ (proj₂ (SD.⟦ morph ⟧ˢ tt n) w n))
          (++-identityʳ (proj₁ (SD.⟦ morph ⟧ˢ tt n))))
    refl

-- … and its function form (equal as `T`-values, ∀ depth).
morph-app-bridge-fun : ∀ {D E kk} (morph : Expr ∅ zeroUsage (D ⇒[ kk ] E))
                         (ih : ∀ j → evalᴰ (elaborate C.Heap morph) tt j ≡ SD.⟦ morph ⟧ˢ tt j)
                         (w : ⟦ D ⟧ᴰ)
                       → evalᴰ (apply ∘ ⟨ elaborate C.Heap morph ∘ terminal , id ⟩ C.Heap) w
                         ≡ (SD.⟦ morph ⟧ˢ tt >>=T (λ clo → clo w))
morph-app-bridge-fun morph ih w = extensionality (morph-app-bridge morph ih w)

------------------------------------------------------------------------
-- `cata`-faithfulness. Both sides fold with `sem-cata` over a per-layer
-- algebra; after the `⟦_⟧ˢ` threading restructure, `cata-ev-algᴰ n algIR`
-- and `cata-ev-algˢ n (⟦alg⟧ˢ tt)` agree per layer by the closure-bridge —
-- the case reduces to the algebra IH + monad reduction, NO `build-pure`.
------------------------------------------------------------------------

cata-body : ∀ {m} {Γ : Ctx m} {F : Functor} {A} {π : Purity}
              (wf : WellFormedF F)
              (alg : Expr ∅ zeroUsage (⟦ F ⟧T A ⇒[ mk-kind Many π ] A))
              (ih : ∀ j → evalᴰ (elaborate C.Heap alg) tt j ≡ SD.⟦ alg ⟧ˢ tt j)
              (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
            → evalᴰ (elaborate C.Heap (cata {Γ = Γ} wf alg)) dγ k
              ≡ SD.⟦ cata {Γ = Γ} wf alg ⟧ˢ dγ k
cata-body {Γ = Γ} {F = F} {A = A} wf alg ih dγ k =
  cong (_,_ []) (extensionality (λ b → extensionality (λ n →
    cong (λ r → (proj₁ r , inject (proj₂ r)))
      (cong (λ a → sem-cata wf a b) (alg-eq n)))))
  where
    algIR : IR (⟦ F ⟧T A) A
    algIR = apply ∘ ⟨ elaborate C.Heap alg ∘ terminal , id ⟩ C.Heap

    -- Per layer, the two algebras' `step`s agree by the closure-bridge.
    alg-eq : ∀ (n : ℕ)
           → cata-ev-algᴰ {F} {A} n algIR
             ≡ SD.cata-ev-algˢ {F} {A} n (SD.⟦ alg ⟧ˢ tt)
    alg-eq n = extensionality (λ fc →
      cong (λ s → (events-F F proj₁ fc ++ projTrace s n , forget (valueT s n)))
           (morph-app-bridge-fun alg ih (inject (coerce-functor⁻¹ F A (sem-fmap F proj₂ fc)))))

------------------------------------------------------------------------
-- `ana`-faithfulness. Dual of `cata`. The TRACE side bridges
-- `ana-events` (IR coalgebra, `DenotTrace`) to the threaded `ana-eventsˢ`
-- (`⟦coalg⟧ˢ tt`, `SourceDenote`) by induction on the unfold depth, using
-- the per-layer closure-bridge; the VALUE side (`sem-ana`) matches because
-- `valueT … 0` of the threaded `step` reduces to the once-built closure
-- value. NO `build-pure`.
------------------------------------------------------------------------

ana-ev-bridge : ∀ {F A kk} (coalg : Expr ∅ zeroUsage (A ⇒[ kk ] ⟦ F ⟧T A))
                  (ih : ∀ j → evalᴰ (elaborate C.Heap coalg) tt j ≡ SD.⟦ coalg ⟧ˢ tt j)
                  (a : Val.⟦ A ⟧) (m : ℕ)
              → ana-events {F} {A} (apply ∘ ⟨ elaborate C.Heap coalg ∘ terminal , id ⟩ C.Heap) a m
                ≡ SD.ana-eventsˢ {F} {A} (SD.⟦ coalg ⟧ˢ tt) a m
ana-ev-bridge coalg ih a zero        = refl
ana-ev-bridge {F} {A} coalg ih a (suc m) =
  cong₂ _++_
    (cong (λ s → projTrace s m) step-eq)
    (trans (cong (λ s → events-F F (λ seed → ana-events {F} {A} coalgIR seed m)
                          (coerce-functor F A (forget (valueT s m)))) step-eq)
           (cong (λ g → events-F F g (coerce-functor F A (forget (valueT stepˢ m))))
                 (extensionality (λ seed → ana-ev-bridge coalg ih seed m))))
  where
    coalgIR : IR A (⟦ F ⟧T A)
    coalgIR = apply ∘ ⟨ elaborate C.Heap coalg ∘ terminal , id ⟩ C.Heap
    stepˢ : T ⟦ ⟦ F ⟧T A ⟧ᴰ
    stepˢ = SD.⟦ coalg ⟧ˢ tt >>=T (λ clo → clo (inject a))
    step-eq : evalᴰ coalgIR (inject a) ≡ stepˢ
    step-eq = morph-app-bridge-fun coalg ih (inject a)

ana-body : ∀ {mm} {Γ : Ctx mm} {F : Functor} {A} {π : Purity}
             (wf : WellFormedF F)
             (coalg : Expr ∅ zeroUsage (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A))
             (ih : ∀ j → evalᴰ (elaborate C.Heap coalg) tt j ≡ SD.⟦ coalg ⟧ˢ tt j)
             (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
           → evalᴰ (elaborate C.Heap (ana {Γ = Γ} wf coalg)) dγ k
             ≡ SD.⟦ ana {Γ = Γ} wf coalg ⟧ˢ dγ k
ana-body {Γ = Γ} {F = F} {A = A} wf coalg ih dγ k =
  cong (_,_ []) (extensionality (λ a → extensionality (λ n →
    cong₂ _,_
      (ana-ev-bridge coalg ih (forget a) n)
      (cong (λ f → inject (sem-ana F f (forget a)))
            (extensionality (λ a' →
              cong (λ s → coerce-functor F A (forget (valueT s zero)))
                   (morph-app-bridge-fun coalg ih (inject a'))))))))
