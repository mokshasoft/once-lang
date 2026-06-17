-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.FaithfulLemmas — reusable coherence lemmas for the
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

module Once.Verified.FaithfulLemmas where

open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

open import Once.Type using (Type; Unit; Void; Int; Str; Float; Buffer;
                              _*_; _+_; _⇒[_]_; μ-type; ν-type; Functor; ⟦_⟧T;
                              Purity; mk-kind; Many)
open import Once.CCC.Eval as Val using ()
open import Once.CCC.IR using (IR; _∘_; ⟨_,_⟩; apply; curry; terminal; id; snd; Cata; Ana)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Semantics.Machine using (sem-cata; sem-ana; coerce-functor)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; ∅; zeroUsage)
open import Once.Surface.Elaborate using (elaborate; ⟦_⟧ᶜ)
import Once.Compile as C
open import Once.Verified.Trace using (SigOpEvent)
open import Once.Verified.TraceMonad using (T; returnT; valueT; projTrace)
open import Once.Verified.DenotTrace using (⟦_⟧ᴰ; evalᴰ; cata-ev-algᴰ; ana-events; forget; inject)
open import Once.Verified.TraceDenote using (events-F)
import Once.Verified.SourceDenote as SD
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
-- Construction-purity (`build-pure`). Building a function VALUE is pure
-- and depth-independent: a closed (∅) arrow-typed expression denotes
-- `returnT <closure>` — it emits NOTHING and its value does not depend on
-- the observation depth. Effects are DEFERRED into the closure body (the
-- D018 suspended-Eff design) and fire only when the closure is APPLIED
-- (captured inside the fold's trace), never at build time. UNIFORM over
-- π = pure and π = eff. (TODO: discharge by purity-soundness induction on
-- the closed expression — the one remaining obligation under `cata`/`ana`.)
------------------------------------------------------------------------

postulate
  build-pure : ∀ {A B kk} (e : Expr ∅ zeroUsage (A ⇒[ kk ] B)) (n : ℕ)
             → SD.⟦ e ⟧ˢ tt n ≡ ([] , proj₂ (SD.⟦ e ⟧ˢ tt zero))

------------------------------------------------------------------------
-- `cata`-faithfulness, shared body (takes the algebra IH as an argument,
-- mirroring `app-body`). After the `⟦_⟧ᴰ` value-model fix, `cata-ev-algᴰ
-- n algIR` is DEFINITIONALLY `cata-ev-algˢ n (evalᴰ algIR)`, so the whole
-- case reduces to the closure-bridge `evalᴰ algIR ≡ valueT (⟦alg⟧ˢ tt) 0`
-- — and that follows from the IH + `build-pure` (the closure built per
-- fold-layer by the IR equals the source's once-built closure).
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

    -- The closure-bridge, pointwise in the fold input `w` and depth `n`.
    cb : ∀ (w : ⟦ ⟦ F ⟧T A ⟧ᴰ) (n : ℕ)
       → evalᴰ algIR w n ≡ valueT (SD.⟦ alg ⟧ˢ tt) zero w n
    cb w n rewrite ih n | build-pure alg n = refl

    -- Lift to the algebra equality used by both the trace and the value.
    alg-eq : ∀ (n : ℕ)
           → cata-ev-algᴰ {F} {A} n algIR
             ≡ SD.cata-ev-algˢ {F} {A} n (valueT (SD.⟦ alg ⟧ˢ tt) zero)
    alg-eq n = cong (SD.cata-ev-algˢ {F} {A} n)
                    (extensionality (λ w → extensionality (λ n′ → cb w n′)))

------------------------------------------------------------------------
-- `ana`-faithfulness. Dual of `cata`; the value-model fix makes `evalᴰ`'s
-- `Ana` value `sem-ana` over the coalgebra's OWN trace-value, mirroring
-- `⟦_⟧ˢ`. Needs one extra structural lemma (`ana-ev-bridge`) because the
-- trace `ana-events` recurses on the IR coalgebra while the source's
-- `ana-eventsˢ` recurses on the closure — they agree by induction on the
-- unfold depth, then the closure-bridge ties IR-closure to source-closure.
------------------------------------------------------------------------

-- `ana-events` on an IR coalgebra equals `ana-eventsˢ` on its `evalᴰ`
-- closure — both unfold identically; induction on the depth `m`.
ana-ev-bridge : ∀ {F A} (ir : IR A (⟦ F ⟧T A)) (a : Val.⟦ A ⟧) (m : ℕ)
              → ana-events {F} {A} ir a m ≡ SD.ana-eventsˢ {F} {A} (evalᴰ ir) a m
ana-ev-bridge ir a zero        = refl
ana-ev-bridge {F} {A} ir a (suc m) =
  cong (projTrace (evalᴰ ir (inject a)) m ++_)
       (cong (λ g → events-F F g (coerce-functor F A (forget (valueT (evalᴰ ir (inject a)) m))))
             (extensionality (λ seed → ana-ev-bridge ir seed m)))

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
      (trans (ana-ev-bridge coalgIR (forget a) n)
             (cong (λ c → SD.ana-eventsˢ {F} {A} c (forget a) n) cb-fun))
      (cong (λ f → inject (sem-ana F f (forget a)))
            (extensionality (λ a' →
              cong (λ c → coerce-functor F A (forget (valueT (c (inject a')) zero))) cb-fun))))))
  where
    coalgIR : IR A (⟦ F ⟧T A)
    coalgIR = apply ∘ ⟨ elaborate C.Heap coalg ∘ terminal , id ⟩ C.Heap
    cb : ∀ (w : ⟦ A ⟧ᴰ) (n : ℕ) → evalᴰ coalgIR w n ≡ valueT (SD.⟦ coalg ⟧ˢ tt) zero w n
    cb w n rewrite ih n | build-pure coalg n = refl
    cb-fun : evalᴰ coalgIR ≡ valueT (SD.⟦ coalg ⟧ˢ tt) zero
    cb-fun = extensionality (λ w → extensionality (λ n → cb w n))
