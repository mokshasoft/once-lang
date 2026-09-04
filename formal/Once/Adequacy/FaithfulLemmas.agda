-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.FaithfulLemmas — reusable coherence lemmas for the
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

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.FaithfulLemmas (fmt : TargetNum) where

open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst; subst-sym-subst)

open import Once.Type using (Type; Unit; Void; Int; Str; Float; Buffer;
                              _*_; _+_; _⇒[_]_; μ-type; ν-type; Functor; ⟦_⟧T;
                              Purity; mk-kind; Zero; One; Many)
open import Once.CCC.Eval as Val using ()
open import Once.IR using (IR; _∘_; ⟨_,_⟩; apply; curry; terminal; id; snd; Cata; Ana; ⌊_⌋)
open import Once.Functor.Translate using (WellFormedF)
open import Once.IRTy using (⌊⟧T-commute; ⌈⟧TI-commute; eraseF; ⌈_⌉F; ⌈_⌉)
import Once.IRTy as II
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Denotation.Meaning using (cata-sem; cata-ev-algᴰ-D)
open import Once.Adequacy.CataErased fmt using (evalᴰ-Cata-erased; subst-T-apply; subst-T-projTrace; pairᴰ-subst⁻)
open import Once.Adequacy.LiftFnReduce fmt using (liftFn-apply; liftFn-∘; liftFn-terminal)
open import Once.Adequacy.AnaErased fmt using
  (events-F-erase; coerce-SFRel; coh-to-TRel; inject-coh-nat; forget-coh-gen;
   TRel; SFRel; sem-ana-erase-coh′; sem-ana-erase-full; coerce-νin-erase)
open import Once.Semantics.Machine using
  (sem-cata; sem-ana; coerce-functor; coerce-functor⁻¹; sem-fmap; coh; coerce-ν-in; tF-coh; ⟦_⟧F)
open import Once.Semantics.Functor using (νS; ⟦_⟧SF; SFunctor)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; ∅; zeroUsage; ⟦_⟧ᶜ; _↾_)
open import Once.Surface.Elaborate using (elaborate; cataM)
import Once.Compile as C
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceMonad using (T; returnT; valueT; projTrace; _>>=T_)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; evalᴰ; cata-ev-algᴰ; ana-events; forget; inject; coerce-functor⁻¹-D; liftFn; cohᴰ)
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
-- D143: at an ERASED arrow neither side carries an argument of type `A`, so
-- there is no round-trip on the domain — only the codomain's IH is used.
forget-inject {A ⇒[ mk-kind Zero π ] B} pf =
  extensionality (λ u → forget-inject {B} (pf u))
forget-inject {A ⇒[ mk-kind One π ] B} pf =
  extensionality (λ va →
    trans (cong (λ z → forget (inject (pf z))) (forget-inject {A} va))
          (forget-inject {B} (pf va)))
forget-inject {A ⇒[ mk-kind Many π ] B} pf =
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

-- Transport commutes with closure application + bind (all by `refl`): applying a
-- `cohᴰ`-transported closure `T`-value to a `cohᴰ`-back-transported argument, then
-- transporting the result, equals the untransported apply-bind.
transport-apply-bind : ∀ {DI DT EI ET : Set} (pD : DI ≡ DT) (pE : EI ≡ ET)
    (h : T (DT → T ET)) (w : DT)
  → subst T pE ((subst T (sym (cong₂ (λ x y → x → T y) pD pE)) h)
                  >>=T (λ vf → vf (subst (λ z → z) (sym pD) w)))
    ≡ (h >>=T (λ clo → clo w))
transport-apply-bind refl refl h w = refl

-- Transport through `returnT` / through an arrow closure (both `refl`).
subst-T-returnT : ∀ {X Y : Set} (eq : X ≡ Y) (g : X)
  → subst T eq (returnT g) ≡ returnT (subst (λ z → z) eq g)
subst-T-returnT refl g = refl

subst-arrow : ∀ {DI DT EI ET : Set} (pD : DI ≡ DT) (pE : EI ≡ ET) (g : DI → T EI)
  → subst (λ z → z) (cong₂ (λ x y → x → T y) pD pE) g
    ≡ (λ x → subst T pE (g (subst (λ z → z) (sym pD) x)))
subst-arrow refl refl g = refl

-- D143: `apply ∘ ⟨ … ⟩` requires `⌊D ⇒[kk] E⌋ ≡ ⌊D⌋ ⇛ ⌊E⌋`, which holds only
-- at a NON-erased arrow — `⌊_⌋` sends a `Zero`-graded one to `Unit ⇛ ⌊E⌋`.
-- `Many` is what every consumer (the `ana` coalgebra) instantiates.
morph-app-bridge : ∀ {D E π} (morph : Expr ∅ zeroUsage (D ⇒[ mk-kind Many π ] E))
                     (ih : ∀ j → liftFn fmt {⟦ ∅ ⟧ᶜ} {D ⇒[ mk-kind Many π ] E} (elaborate C.Heap morph) tt j ≡ SD.⟦ morph ⟧ˢ fmt tt j)
                     (w : ⟦ D ⟧ᴰ) (n : ℕ)
                   → liftFn fmt {D} {E} (apply ∘ ⟨ elaborate C.Heap morph ∘ terminal , id ⟩ C.Heap) w n
                     ≡ (SD.⟦ morph ⟧ˢ fmt tt >>=T (λ clo → clo w)) n
morph-app-bridge {D} {E} morph ih w n =
  trans (cong (λ X → subst T (cohᴰ E) X n) app-⟨⟩-clean)
    (trans (cong (λ h → subst T (cohᴰ E) (h >>=T (λ vf → vf w')) n) ih-evalᴰ)
           (cong (λ t → t n) (transport-apply-bind (cohᴰ D) (cohᴰ E) (SD.⟦ morph ⟧ˢ fmt tt) w)))
  where
    w' = subst (λ z → z) (sym (cohᴰ D)) w
    -- The elaborated closed-morphism `apply ∘ ⟨ morph ∘ terminal , id ⟩` applied to `w'`
    -- monad-reduces (`terminal`/`id` = `returnT`) to `evalᴰ morph tt >>=T (λ vf → vf w')`;
    -- the only residual is the pair-build's empty trace (`++ []`, `++-identityʳ`).
    app-⟨⟩-clean : evalᴰ fmt (apply ∘ ⟨ elaborate C.Heap morph ∘ terminal , id ⟩ C.Heap) w'
                   ≡ (evalᴰ fmt (elaborate C.Heap morph) tt >>=T (λ vf → vf w'))
    app-⟨⟩-clean = extensionality (λ j →
      cong₂ _,_
        (cong (_++ proj₁ (proj₂ (evalᴰ fmt (elaborate C.Heap morph) tt j) w' j))
              (++-identityʳ (proj₁ (evalᴰ fmt (elaborate C.Heap morph) tt j))))
        refl)
    -- `ih` in `evalᴰ`-form: `evalᴰ (elaborate morph) tt ≡ subst T (sym cohᴰ(D⇒E)) (SD.⟦morph⟧ˢ tt)`.
    ih-evalᴰ : evalᴰ fmt (elaborate C.Heap morph) tt
               ≡ subst T (sym (cong₂ (λ x y → x → T y) (cohᴰ D) (cohᴰ E))) (SD.⟦ morph ⟧ˢ fmt tt)
    ih-evalᴰ = trans (sym (subst-sym-subst (cong₂ (λ x y → x → T y) (cohᴰ D) (cohᴰ E))))
                     (cong (subst T (sym (cong₂ (λ x y → x → T y) (cohᴰ D) (cohᴰ E)))) (extensionality ih))

-- … and its function form (equal as `T`-values, ∀ depth).
morph-app-bridge-fun : ∀ {D E π} (morph : Expr ∅ zeroUsage (D ⇒[ mk-kind Many π ] E))
                         (ih : ∀ j → liftFn fmt {⟦ ∅ ⟧ᶜ} {D ⇒[ mk-kind Many π ] E} (elaborate C.Heap morph) tt j ≡ SD.⟦ morph ⟧ˢ fmt tt j)
                         (w : ⟦ D ⟧ᴰ)
                       → liftFn fmt {D} {E} (apply ∘ ⟨ elaborate C.Heap morph ∘ terminal , id ⟩ C.Heap) w
                         ≡ (SD.⟦ morph ⟧ˢ fmt tt >>=T (λ clo → clo w))
morph-app-bridge-fun morph ih w = extensionality (morph-app-bridge morph ih w)

------------------------------------------------------------------------
-- `cata`-faithfulness. Both sides fold with `sem-cata` over a per-layer
-- algebra; after the `⟦_⟧ˢ` threading restructure, `cata-ev-algᴰ n algIR`
-- and `cata-ev-algˢ n (⟦alg⟧ˢ tt)` agree per layer by the closure-bridge —
-- the case reduces to the algebra IH + monad reduction, NO `build-pure`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- D131: what `cataM` MEANS applied to an obtained algebra closure.
--
-- `cataM wf m = curry (Cata (wf-⌊⌋ wf) (subst … (apply ∘ ⟨ fst , snd ⟩)))`, so
-- applying it to a closure `c` gives the fold whose per-layer algebra is
-- "apply `c`". That is the whole content of the parameterized fold: the
-- closure is obtained ONCE, by the caller, and the fold carries it. Same
-- transport shape as the old `elab-cata-reduce`, with the closure as the
-- environment instead of the algebra being inlined.
------------------------------------------------------------------------
cataM-fold : ∀ {F : Functor} {A : Type} {π : Purity} (wfF : WellFormedF F)
               (c : ⟦ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ⟧ᴰ)
           → liftFn fmt {⟦ F ⟧T A ⇒[ mk-kind Many π ] A} {μ-type F ⇒[ mk-kind Many π ] A}
                    (cataM {F} {A} wfF C.Heap) c
             ≡ returnT (cata-sem wfF c)
cataM-fold {F} {A} {π} wfF c =
  trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ (μ-type F)) (cohᴰ A))
                         (λ b → evalᴰ fmt (innerCata) (c' , b)))
        (cong returnT
          (trans (subst-arrow (cohᴰ (μ-type F)) (cohᴰ A) (λ b → evalᴰ fmt innerCata (c' , b)))
                 (extensionality (λ x →
                    trans (trans (cong (λ W → subst T (cohᴰ A) (evalᴰ fmt innerCata W))
                                       (sym (pairᴰ-subst⁻ (cohᴰ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A))
                                                          (cohᴰ (μ-type F)) c x)))
                                 (evalᴰ-Cata-erased {A} {F} {⟦ F ⟧T A ⇒[ mk-kind Many π ] A} wfF applyIR c x))
                          (cong (λ g → cata-sem wfF g x)
                                (extensionality apply-closure))))))
  where
    c' = subst (λ z → z) (sym (cohᴰ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A))) c
    applyIR : IR (⌊ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ⌋ C.* ⌊ ⟦ F ⟧T A ⌋) ⌊ A ⌋
    applyIR = C.apply C.∘ C.⟨ C.fst , C.snd ⟩ C.Heap
    -- Applying the carried closure IS the algebra: `⟨fst,snd⟩` is pair-η and
    -- `liftFn apply` is application, so the fold's per-layer algebra is `c`.
    apply-closure : ∀ (z : ⟦ ⟦ F ⟧T A ⟧ᴰ)
                  → liftFn fmt {(⟦ F ⟧T A ⇒[ mk-kind Many π ] A) Once.Type.* (⟦ F ⟧T A)} {A}
                           applyIR (c , z)
                    ≡ c z
    apply-closure z = cong (λ h → h (c , z)) (liftFn-apply {⟦ F ⟧T A} {A} {π})
    innerCata = C.Cata (wf-⌊⌋ wfF)
                     (subst (λ o → IR (⌊ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ⌋ C.* o) ⌊ A ⌋)
                            (⌊⟧T-commute F A) applyIR)

-- D131: the elaboration is `cataM ∘ (ealg ∘ terminal)` and BOTH sides now bind
-- the algebra once, so this is a bind-congruence over a shared computation
-- plus one per-closure fold equality — structurally simpler than the old
-- proof, which had to bridge a per-layer REBUILD against a bound closure.
cata-body : ∀ {m} {Γ : Ctx m} {F : Functor} {A} {π : Purity}
              (wf : WellFormedF F)
              (alg : Expr ∅ zeroUsage (⟦ F ⟧T A ⇒[ mk-kind Many π ] A))
              (ih : ∀ j → liftFn fmt {⟦ ∅ ⟧ᶜ} {⟦ F ⟧T A ⇒[ mk-kind Many π ] A} (elaborate C.Heap alg) tt j ≡ SD.⟦ alg ⟧ˢ fmt tt j)
              (dγ : ⟦ ⟦ Γ ↾ zeroUsage ⟧ᶜ ⟧ᴰ) (k : ℕ)
            → liftFn fmt {⟦ Γ ↾ zeroUsage ⟧ᶜ} {μ-type F ⇒[ mk-kind Many π ] A}
                (elaborate C.Heap (cata {Γ = Γ} wf alg)) dγ k
              ≡ SD.⟦ cata {Γ = Γ} wf alg ⟧ˢ fmt dγ k
cata-body {Γ = Γ} {F = F} {A = A} {π = π} wf alg ih dγ k =
  trans (cong (λ t → t k) split) (cong (λ t → t k) fold-step)
  where
    ealg   = elaborate C.Heap alg
    cataM' = cataM {F} {A} wf C.Heap
    -- `liftFn`'s surface implicits cannot be inferred through `⌊_⌋`, so pin
    -- them once here rather than at each of the four occurrences.
    liftCataM = liftFn fmt {⟦ F ⟧T A ⇒[ mk-kind Many π ] A}
                           {μ-type F ⇒[ mk-kind Many π ] A} cataM'
    liftEalg  = liftFn fmt {⟦ ∅ ⟧ᶜ} {⟦ F ⟧T A ⇒[ mk-kind Many π ] A} ealg

    -- The composition splits and `∘ terminal` feeds the algebra the empty
    -- environment, so the left factor is the algebra's own denotation and the
    -- IH applies to it directly.
    split : liftFn fmt {⟦ Γ ↾ zeroUsage ⟧ᶜ} {μ-type F ⇒[ mk-kind Many π ] A}
                   (elaborate C.Heap (cata {Γ = Γ} wf alg)) dγ
          ≡ (SD.⟦ alg ⟧ˢ fmt tt >>=T liftCataM)
    split = trans (cong (λ h → h dγ) (liftFn-∘ {B = ⟦ F ⟧T A ⇒[ mk-kind Many π ] A} {C = μ-type F ⇒[ mk-kind Many π ] A} {A = ⟦ Γ ↾ zeroUsage ⟧ᶜ} cataM' (ealg C.∘ C.terminal)))
                  (cong (λ t → t >>=T liftCataM)
                        (trans (cong (λ h → h dγ) (liftFn-∘ {B = ⟦ ∅ ⟧ᶜ} {C = ⟦ F ⟧T A ⇒[ mk-kind Many π ] A} {A = ⟦ Γ ↾ zeroUsage ⟧ᶜ} ealg C.terminal))
                               (trans (cong (λ t → t >>=T liftEalg)
                                            (cong (λ h → h dγ) (liftFn-terminal {⟦ Γ ↾ zeroUsage ⟧ᶜ})))
                                      (extensionality ih))))

    -- Per obtained closure the fold agrees — `cataM-fold`.
    fold-step : (SD.⟦ alg ⟧ˢ fmt tt >>=T liftCataM)
              ≡ SD.⟦ cata {Γ = Γ} wf alg ⟧ˢ fmt dγ
    fold-step = cong (λ g → SD.⟦ alg ⟧ˢ fmt tt >>=T g)
                     (extensionality (λ c → cataM-fold {F} {A} {π} wf c))

------------------------------------------------------------------------
-- `ana`-faithfulness. Dual of `cata`. The TRACE side bridges
-- `ana-events` (IR coalgebra, `DenotTrace`) to the threaded `ana-eventsˢ`
-- (`⟦coalg⟧ˢ tt`, `SourceDenote`) by induction on the unfold depth, using
-- the per-layer closure-bridge; the VALUE side (`sem-ana`) matches because
-- `valueT … 0` of the threaded `step` reduces to the once-built closure
-- value. NO `build-pure`.
------------------------------------------------------------------------

-- `evalᴰ` of a codomain-`subst`ed IR transports the result (dual of
-- `CataErased.evalᴰ-subst-dom`). `valueT`/`projTrace` of a value-`subst`ed
-- `T` split trace (unchanged) from value (transported).
evalᴰ-subst-cod : ∀ {X o₁ o₂ : II.IRTy} (eq : o₁ ≡ o₂) (ir : IR X o₁) (v : ⟦ X ⟧ᴰᴵ)
  → evalᴰ fmt (subst (λ o → IR X o) eq ir) v ≡ subst T (cong ⟦_⟧ᴰᴵ eq) (evalᴰ fmt ir v)
evalᴰ-subst-cod refl ir v = refl

valueT-subst : ∀ {X Y : Set} (eq : X ≡ Y) (h : T X) (m : ℕ)
  → valueT (subst T eq h) m ≡ subst (λ z → z) eq (valueT h m)
valueT-subst refl h m = refl

-- D143: same restriction as `morph-app-bridge` — the coalgebra is applied
-- through `apply`, so its arrow must be NON-erased.
ana-ev-bridge : ∀ {F A π} (coalg : Expr ∅ zeroUsage (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A))
                  (ih : ∀ j → liftFn fmt {⟦ ∅ ⟧ᶜ} {A ⇒[ mk-kind Many π ] ⟦ F ⟧T A} (elaborate C.Heap coalg) tt j ≡ SD.⟦ coalg ⟧ˢ fmt tt j)
                  (s : Val.⟦ A ⟧) (m : ℕ)
              → ana-events fmt {eraseF F} {⌊ A ⌋}
                  (subst (λ o → IR ⌊ A ⌋ o) (⌊⟧T-commute F A)
                         (apply ∘ ⟨ elaborate C.Heap coalg ∘ terminal , id ⟩ C.Heap))
                  (subst (λ z → z) (sym (coh A)) s) m
                ≡ SD.ana-eventsˢ {F} {A} (SD.⟦ coalg ⟧ˢ fmt tt) s m
ana-ev-bridge coalg ih s zero = refl
ana-ev-bridge {F} {A} coalg ih s (suc m) =
  cong₂ _++_ trace-eq events-eq
  where
    p : IR ⌊ A ⌋ ⌊ ⟦ F ⟧T A ⌋
    p = apply ∘ ⟨ elaborate C.Heap coalg ∘ terminal , id ⟩ C.Heap
    seed-e = subst (λ z → z) (sym (coh A)) s
    v0T = evalᴰ fmt p (inject seed-e)
    v0 = valueT v0T m
    eE = cong ⟦_⟧ᴰᴵ (⌊⟧T-commute F A)
    eS = cohᴰ (⟦ F ⟧T A)

    step-e-eq : evalᴰ fmt (subst (λ o → IR ⌊ A ⌋ o) (⌊⟧T-commute F A) p) (inject seed-e)
                ≡ subst T eE v0T
    step-e-eq = evalᴰ-subst-cod (⌊⟧T-commute F A) p (inject seed-e)

    step-s-eq : (SD.⟦ coalg ⟧ˢ fmt tt >>=T (λ clo → clo (inject s))) ≡ subst T eS v0T
    step-s-eq = trans (sym (morph-app-bridge-fun coalg ih (inject s)))
                      (cong (λ w → subst T eS (evalᴰ fmt p w)) (sym (inject-coh-nat A s)))

    trace-eq : projTrace (evalᴰ fmt (subst (λ o → IR ⌊ A ⌋ o) (⌊⟧T-commute F A) p) (inject seed-e)) m
               ≡ projTrace (SD.⟦ coalg ⟧ˢ fmt tt >>=T (λ clo → clo (inject s))) m
    trace-eq = trans (cong (λ t → projTrace t m) step-e-eq)
                 (trans (subst-T-projTrace eE v0T m)
                   (trans (sym (subst-T-projTrace eS v0T m))
                          (cong (λ t → projTrace t m) (sym step-s-eq))))

    R : Val.⟦ ⌈ ⌊ A ⌋ ⌉ ⟧ → Val.⟦ A ⟧ → Set
    R xe xs = subst (λ z → z) (coh A) xe ≡ xs

    child-e = λ seed → ana-events fmt {eraseF F} {⌊ A ⌋}
                (subst (λ o → IR ⌊ A ⌋ o) (⌊⟧T-commute F A) p) seed m
    child-s = λ seed → SD.ana-eventsˢ {F} {A} ((SD.⟦ coalg ⟧ˢ fmt) tt) seed m

    child-R : ∀ {xe xs} → R xe xs → child-e xe ≡ child-s xs
    child-R {xe} {xs} req =
      trans (cong (λ z → child-e z)
                  (trans (sym (subst-sym-subst (coh A))) (cong (subst (λ z → z) (sym (coh A))) req)))
            (ana-ev-bridge coalg ih xs m)

    ve-eq : valueT (evalᴰ fmt (subst (λ o → IR ⌊ A ⌋ o) (⌊⟧T-commute F A) p) (inject seed-e)) m
            ≡ subst (λ z → z) eE v0
    ve-eq = trans (cong (λ t → valueT t m) step-e-eq) (valueT-subst eE v0T m)

    vs-eq : valueT (SD.⟦ coalg ⟧ˢ fmt tt >>=T (λ clo → clo (inject s))) m
            ≡ subst (λ z → z) eS v0
    vs-eq = trans (cong (λ t → valueT t m) step-s-eq) (valueT-subst eS v0T m)

    events-eq : events-F ⌈ eraseF F ⌉F child-e
                  (coerce-functor ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉
                    (subst (λ Ty → Val.⟦ Ty ⟧) (⌈⟧TI-commute (eraseF F) ⌊ A ⌋)
                      (forget (valueT (evalᴰ fmt (subst (λ o → IR ⌊ A ⌋ o) (⌊⟧T-commute F A) p) (inject seed-e)) m))))
                ≡ events-F F child-s (coerce-functor F A (forget (valueT (SD.⟦ coalg ⟧ˢ fmt tt >>=T (λ clo → clo (inject s))) m)))
    events-eq =
      trans (cong (λ X → events-F ⌈ eraseF F ⌉F child-e
                    (coerce-functor ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉
                      (subst (λ Ty → Val.⟦ Ty ⟧) (⌈⟧TI-commute (eraseF F) ⌊ A ⌋) (forget X)))) ve-eq)
        (trans (events-F-erase F R child-e child-s child-R _ _
                  (coerce-SFRel F _ _ (coh-to-TRel F A v0)))
               (cong (λ X → events-F F child-s (coerce-functor F A (forget X))) (sym vs-eq)))

ana-body : ∀ {mm} {Γ : Ctx mm} {F : Functor} {A} {π : Purity}
             (wf : WellFormedF F)
             (coalg : Expr ∅ zeroUsage (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A))
             (ih : ∀ j → liftFn fmt {⟦ ∅ ⟧ᶜ} {A ⇒[ mk-kind Many π ] ⟦ F ⟧T A} (elaborate C.Heap coalg) tt j ≡ SD.⟦ coalg ⟧ˢ fmt tt j)
             (dγ : ⟦ ⟦ Γ ↾ zeroUsage ⟧ᶜ ⟧ᴰ) (k : ℕ)
           → liftFn fmt {⟦ Γ ↾ zeroUsage ⟧ᶜ} {A ⇒[ mk-kind Many π ] ν-type F} (elaborate C.Heap (ana {Γ = Γ} wf coalg)) dγ k
             ≡ SD.⟦ ana {Γ = Γ} wf coalg ⟧ˢ fmt dγ k
ana-body {Γ = Γ} {F = F} {A = A} {π = π} wf coalg ih dγ k =
  trans elab-ana-reduce (cong (_,_ []) per-a)
  where
    coalgIR : IR ⌊ A ⌋ ⌊ ⟦ F ⟧T A ⌋
    coalgIR = apply ∘ ⟨ elaborate C.Heap coalg ∘ terminal , id ⟩ C.Heap
    coalg' = subst (λ o → IR ⌊ A ⌋ o) (⌊⟧T-commute F A) coalgIR
    Ana-IR : IR ⌊ A ⌋ ⌊ ν-type F ⌋
    Ana-IR = Ana (wf-⌊⌋ wf) coalg'

    elab-ana-reduce : liftFn fmt {⟦ Γ ↾ zeroUsage ⟧ᶜ} {A ⇒[ mk-kind Many π ] ν-type F} (elaborate C.Heap (ana {Γ = Γ} wf coalg)) dγ k
                      ≡ returnT (λ a → liftFn fmt {A} {ν-type F} Ana-IR a) k
    elab-ana-reduce = cong (λ t → t k)
      (trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ (ν-type F))) (λ a → evalᴰ fmt Ana-IR a))
             (cong returnT (subst-arrow (cohᴰ A) (cohᴰ (ν-type F)) (λ a → evalᴰ fmt Ana-IR a))))

    cL-e : Val.⟦ ⌈ ⌊ A ⌋ ⌉ ⟧ → ⟦ ⌈ eraseF F ⌉F ⟧F Val.⟦ ⌈ ⌊ A ⌋ ⌉ ⟧
    cL-e = λ a'' → coerce-functor ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉
                     (subst (λ Ty → Val.⟦ Ty ⟧) (⌈⟧TI-commute (eraseF F) ⌊ A ⌋)
                            (forget (valueT (evalᴰ fmt coalg' (inject a'')) 0)))

    cR : Val.⟦ A ⟧ → ⟦ F ⟧F Val.⟦ A ⟧
    cR = λ a'' → coerce-functor F A (forget (valueT (valueT ((SD.⟦ coalg ⟧ˢ fmt) tt) 0 (inject a'')) 0))

    subst-νS-cong : ∀ {H₁ H₂ : SFunctor} (eq : H₁ ≡ H₂) (v : νS H₁)
                  → subst (λ z → z) (cong νS eq) v ≡ subst νS eq v
    subst-νS-cong refl v = refl

    seed-eq : ∀ (a : ⟦ A ⟧ᴰ)
            → forget (subst (λ z → z) (sym (cohᴰ A)) a) ≡ subst (λ z → z) (sym (coh A)) (forget a)
    seed-eq a = trans (sym (subst-sym-subst (coh A)))
                      (cong (subst (λ z → z) (sym (coh A))) (forget-coh-gen A a))

    trace-at : ∀ (a : ⟦ A ⟧ᴰ) (n : ℕ)
             → ana-events fmt {eraseF F} {⌊ A ⌋} coalg' (forget (subst (λ z → z) (sym (cohᴰ A)) a)) n
               ≡ SD.ana-eventsˢ {F} {A} (SD.⟦ coalg ⟧ˢ fmt tt) (forget a) n
    trace-at a n = trans (cong (λ z → ana-events fmt {eraseF F} {⌊ A ⌋} coalg' z n) (seed-eq a))
                         (ana-ev-bridge coalg ih (forget a) n)

    subst-fn-cod : ∀ {H₁ H₂ : SFunctor} (eq : H₁ ≡ H₂) (f : Val.⟦ A ⟧ → ⟦ H₁ ⟧SF Val.⟦ A ⟧)
                 → subst (λ H → Val.⟦ A ⟧ → ⟦ H ⟧SF Val.⟦ A ⟧) eq f
                   ≡ (λ x → subst (λ H → ⟦ H ⟧SF Val.⟦ A ⟧) eq (f x))
    subst-fn-cod refl f = refl

    v0 : Val.⟦ A ⟧ → ⟦ ⌊ ⟦ F ⟧T A ⌋ ⟧ᴰᴵ
    v0 x = valueT (evalᴰ fmt coalgIR (inject (subst (λ z → z) (sym (coh A)) x))) 0

    erased-eq : ∀ (x : Val.⟦ A ⟧)
              → subst (λ Ty → Val.⟦ Ty ⟧) (⌈⟧TI-commute (eraseF F) ⌊ A ⌋)
                  (forget (valueT (evalᴰ fmt coalg' (inject (subst (λ z → z) (sym (coh A)) x))) 0))
                ≡ subst (λ Ty → Val.⟦ Ty ⟧) (⌈⟧TI-commute (eraseF F) ⌊ A ⌋)
                    (forget (subst (λ z → z) (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute F A)) (v0 x)))
    erased-eq x = cong (λ w → subst (λ Ty → Val.⟦ Ty ⟧) (⌈⟧TI-commute (eraseF F) ⌊ A ⌋) (forget w))
      (trans (cong (λ t → valueT t 0) (evalᴰ-subst-cod (⌊⟧T-commute F A) coalgIR (inject (subst (λ z → z) (sym (coh A)) x))))
             (valueT-subst (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute F A)) (evalᴰ fmt coalgIR (inject (subst (λ z → z) (sym (coh A)) x))) 0))

    step-s-eq : ∀ (x : Val.⟦ A ⟧)
              → (SD.⟦ coalg ⟧ˢ fmt tt >>=T (λ clo → clo (inject x)))
                ≡ subst T (cohᴰ (⟦ F ⟧T A)) (evalᴰ fmt coalgIR (inject (subst (λ z → z) (sym (coh A)) x)))
    step-s-eq x = trans (sym (morph-app-bridge-fun coalg ih (inject x)))
                        (cong (λ w → subst T (cohᴰ (⟦ F ⟧T A)) (evalᴰ fmt coalgIR w)) (sym (inject-coh-nat A x)))

    surface-eq : ∀ (x : Val.⟦ A ⟧)
               → forget (valueT (valueT (SD.⟦ coalg ⟧ˢ fmt tt) 0 (inject x)) 0)
                 ≡ forget (subst (λ z → z) (cohᴰ (⟦ F ⟧T A)) (v0 x))
    surface-eq x = cong forget
      (trans (cong (λ t → valueT t 0) (step-s-eq x))
             (valueT-subst (cohᴰ (⟦ F ⟧T A)) (evalᴰ fmt coalgIR (inject (subst (λ z → z) (sym (coh A)) x))) 0))

    ceq : ∀ (a : ⟦ A ⟧ᴰ)
        → subst (λ H → Val.⟦ A ⟧ → ⟦ H ⟧SF Val.⟦ A ⟧) (tF-coh F)
             (λ x → coerce-ν-in ⌈ eraseF F ⌉F Val.⟦ A ⟧
                      (subst (λ Z → ⟦ ⌈ eraseF F ⌉F ⟧F Z) (coh A) (cL-e (subst (λ z → z) (sym (coh A)) x))))
          ≡ (λ x → coerce-ν-in F Val.⟦ A ⟧ (cR x))
    ceq a = trans
      (subst-fn-cod (tF-coh F)
        (λ x → coerce-ν-in ⌈ eraseF F ⌉F Val.⟦ A ⟧
                 (subst (λ Z → ⟦ ⌈ eraseF F ⌉F ⟧F Z) (coh A) (cL-e (subst (λ z → z) (sym (coh A)) x)))))
      (extensionality (λ x →
        trans (cong (λ w → subst (λ H → ⟦ H ⟧SF Val.⟦ A ⟧) (tF-coh F)
                      (coerce-ν-in ⌈ eraseF F ⌉F Val.⟦ A ⟧
                        (subst (λ Z → ⟦ ⌈ eraseF F ⌉F ⟧F Z) (coh A)
                          (coerce-functor ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉ w))))
                    (erased-eq x))
          (trans (coerce-νin-erase F A (v0 x))
                 (cong (λ w → coerce-ν-in F Val.⟦ A ⟧ (coerce-functor F A w)) (sym (surface-eq x))))))

    value-at : ∀ (a : ⟦ A ⟧ᴰ)
             → subst (λ z → z) (cohᴰ (ν-type F)) (inject (sem-ana ⌈ eraseF F ⌉F cL-e (forget (subst (λ z → z) (sym (cohᴰ A)) a))))
               ≡ inject (sem-ana F cR (forget a))
    value-at a = trans (subst-νS-cong (tF-coh F) (sem-ana ⌈ eraseF F ⌉F cL-e (forget (subst (λ z → z) (sym (cohᴰ A)) a))))
                   (trans (sem-ana-erase-full (coh A) cL-e cR (forget (subst (λ z → z) (sym (cohᴰ A)) a)) (ceq a))
                          (cong (sem-ana F cR) (forget-coh-gen A a)))

    per-a : (λ a → liftFn fmt {A} {ν-type F} Ana-IR a)
            ≡ (λ a → λ n → ( SD.ana-eventsˢ {F} {A} (SD.⟦ coalg ⟧ˢ fmt tt) (forget a) n
                           , inject (sem-ana F cR (forget a)) ))
    per-a = extensionality (λ a → extensionality (λ n →
      trans (subst-T-apply (cohᴰ (ν-type F)) (evalᴰ fmt Ana-IR (subst (λ z → z) (sym (cohᴰ A)) a)) n)
            (cong₂ _,_ (trace-at a n) (value-at a))))
