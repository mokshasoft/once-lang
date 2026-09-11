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
open import Data.List using (List; []; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Nat.Properties using (0∸n≡0)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst; subst-sym-subst; subst-subst-sym)

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
  (coerce-SFRel; coh-to-TRel; inject-coh-nat; forget-coh-gen;
   TRel; SFRel; coerce-νin-erase; forgetν-injectν; VE0ᴰ; coerce-νin-erase-D)
open import Once.Semantics.Machine using
  (sem-cata; sem-ana; coerce-functor; coerce-functor⁻¹; sem-fmap; coh; coerce-ν-in; tF-coh; ⟦_⟧F)
open import Once.Semantics.Functor using (νS; ⟦_⟧SF; SFunctor)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; ∅; zeroUsage; ⟦_⟧ᶜ; _↾_)
open import Once.Surface.Elaborate using (elaborate; cataM)
import Once.Compile as C
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceMonad using (T; returnT; valueT; projTrace; _>>=T_; bindAt; fmapT)
open import Once.Functor.Translate using (translateF)
open import Once.Word using (Carrier)
open import Once.Semantics.Functor using (SFunctor; ⟦_⟧SF)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; evalᴰ; cata-ev-algᴰ; forget; inject; coerce-functor⁻¹-D; coerce-functor-D; liftFn; cohᴰ; anaFᵈ; anaᵈ-erase-full; subst-νᵈ-cong; νᵈ)
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
-- D179: no longer definitional — the round trip rebuilds every layer, so it
-- is coinductive (discharged via the existing `bisimS-to-eq`).
forget-inject {ν-type F} v      = forgetν-injectν v
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
                   → liftFn fmt {D} {E} (apply ∘ ⟨ elaborate C.Heap morph ∘ terminal , id ⟩) w n
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
    -- `_>>=T_` threads the budget, so the pair-build's `++ []` sits inside the
    -- continuation's budget as well as inside the trace. Rewriting the WHOLE
    -- pair (`bindAt`, which reads the head exactly once) carries both; a
    -- `cong` on the trace alone would leave the budget un-rewritten.
    app-⟨⟩-clean : evalᴰ fmt (apply ∘ ⟨ elaborate C.Heap morph ∘ terminal , id ⟩) w'
                   ≡ (evalᴰ fmt (elaborate C.Heap morph) tt >>=T (λ vf → vf w'))
    app-⟨⟩-clean = extensionality (λ j → cong (bindAt (evalᴰ fmt (apply {⌊ D ⌋} {⌊ E ⌋})) j) (pair-eq j))
      where
        mc = evalᴰ fmt (elaborate C.Heap morph) tt

        pair-eq : ∀ j → evalᴰ fmt ⟨ elaborate C.Heap morph ∘ terminal {⌊ D ⌋} , id {⌊ D ⌋} ⟩ w' j
                        ≡ (proj₁ (mc j) , (proj₂ (mc j) , w'))
        pair-eq j = cong (_, (proj₂ (mc j) , w')) (++-identityʳ (proj₁ (mc j)))
    -- `ih` in `evalᴰ`-form: `evalᴰ (elaborate morph) tt ≡ subst T (sym cohᴰ(D⇒E)) (SD.⟦morph⟧ˢ tt)`.
    ih-evalᴰ : evalᴰ fmt (elaborate C.Heap morph) tt
               ≡ subst T (sym (cong₂ (λ x y → x → T y) (cohᴰ D) (cohᴰ E))) (SD.⟦ morph ⟧ˢ fmt tt)
    ih-evalᴰ = trans (sym (subst-sym-subst (cong₂ (λ x y → x → T y) (cohᴰ D) (cohᴰ E))))
                     (cong (subst T (sym (cong₂ (λ x y → x → T y) (cohᴰ D) (cohᴰ E)))) (extensionality ih))

-- … and its function form (equal as `T`-values, ∀ depth).
morph-app-bridge-fun : ∀ {D E π} (morph : Expr ∅ zeroUsage (D ⇒[ mk-kind Many π ] E))
                         (ih : ∀ j → liftFn fmt {⟦ ∅ ⟧ᶜ} {D ⇒[ mk-kind Many π ] E} (elaborate C.Heap morph) tt j ≡ SD.⟦ morph ⟧ˢ fmt tt j)
                         (w : ⟦ D ⟧ᴰ)
                       → liftFn fmt {D} {E} (apply ∘ ⟨ elaborate C.Heap morph ∘ terminal , id ⟩) w
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
    applyIR = C.apply C.∘ C.⟨ C.fst , C.snd ⟩
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

-- A `subst` on a `T` moves only the VALUE; the trace is untouched.
subst-T-trace : ∀ {X Y : Set} (eq : X ≡ Y) (h : T X) (k : ℕ)
  → projTrace (subst T eq h) k ≡ projTrace h k
subst-T-trace refl h k = refl

-- `subst` along a `cong`ed equation is `subst` along the equation itself.
subst-id-cong : ∀ {W : Set₁} (P : W → Set) {w w' : W} (eq : w ≡ w') (v : P w)
  → subst (λ z → z) (cong P eq) v ≡ subst P eq v
subst-id-cong P refl v = refl

-- `coerce-ν-in` is natural in the carrier, so a carrier transport passes
-- through it.
coerce-ν-in-subst : ∀ (G : Functor) {X Y : Set} (eq : X ≡ Y) (v : ⟦ G ⟧F X)
  → subst (λ Z → ⟦ translateF Carrier Carrier G ⟧SF Z) eq (coerce-ν-in G X v)
    ≡ coerce-ν-in G Y (subst (λ Z → ⟦ G ⟧F Z) eq v)
coerce-ν-in-subst G refl v = refl

-- A family-form `subst` over `T` is a `subst T` along the `cong`ed equation.
subst-fam-T : ∀ {W : Set₁} (P : W → Set) {w w' : W} (eq : w ≡ w') (m : T (P w))
  → subst (λ Z → T (P Z)) eq m ≡ subst T (cong P eq) m
subst-fam-T P refl m = refl

valueT-subst : ∀ {X Y : Set} (eq : X ≡ Y) (h : T X) (m : ℕ)
  → valueT (subst T eq h) m ≡ subst (λ z → z) eq (valueT h m)
valueT-subst refl h m = refl
-- D179: `ana`-faithfulness is now ONE claim. Both sides denote `anaᵈ` over
-- their own coalgebra and emit nothing, so the old split — an `ana-events`
-- trace bridge PLUS a `sem-ana` value bridge, reconciled by hand — is gone.
-- It existed only because a pure ν could not carry the coalgebra's effects,
-- which forced the trace to be rebuilt beside the value.
--
-- D143: same restriction as `morph-app-bridge` — the coalgebra is applied
-- through `apply`, so its arrow must be NON-erased.
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
    coalgIR = apply ∘ ⟨ elaborate C.Heap coalg ∘ terminal , id ⟩
    coalg' = subst (λ o → IR ⌊ A ⌋ o) (⌊⟧T-commute F A) coalgIR
    Ana-IR : IR ⌊ A ⌋ ⌊ ν-type F ⌋
    Ana-IR = Ana (wf-⌊⌋ wf) coalg'

    elab-ana-reduce : liftFn fmt {⟦ Γ ↾ zeroUsage ⟧ᶜ} {A ⇒[ mk-kind Many π ] ν-type F} (elaborate C.Heap (ana {Γ = Γ} wf coalg)) dγ k
                      ≡ returnT (λ a → liftFn fmt {A} {ν-type F} Ana-IR a) k
    elab-ana-reduce = cong (λ t → t k)
      (trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ (ν-type F))) (λ a → evalᴰ fmt Ana-IR a))
             (cong returnT (subst-arrow (cohᴰ A) (cohᴰ (ν-type F)) (λ a → evalᴰ fmt Ana-IR a))))

    -- The IR-side coalgebra, as `anaFᵈ` receives it.
    cE : ⟦ ⌊ A ⌋ ⟧ᴰᴵ → T (⟦ ⌈ eraseF F ⌉F ⟧F ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
    cE = λ a' → fmapT (λ x → coerce-functor-D ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉
                               (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute (eraseF F) ⌊ A ⌋) x))
                      (evalᴰ fmt coalg' a')

    -- The surface-side coalgebra.
    cS : ⟦ A ⟧ᴰ → T (⟦ F ⟧F ⟦ A ⟧ᴰ)
    cS = λ a' → fmapT (coerce-functor-D F A) (SD.⟦ coalg ⟧ˢ fmt tt >>=T λ clo → clo a')

    -- THE content of `ana`-faithfulness, now that both sides are `anaᵈ`: the
    -- two coalgebras agree after the erasure transports. Everything else is
    -- `anaᵈ-erase-full`, which is a `refl` once both equations are matched.
    coalg-agree :
        subst (λ H → ⟦ A ⟧ᴰ → T (⟦ H ⟧SF ⟦ A ⟧ᴰ)) (tF-coh F)
          (λ x → subst (λ Z → T (⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z)) (cohᴰ A)
                   ((λ y → fmapT (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ) (cE y))
                      (subst (λ z → z) (sym (cohᴰ A)) x)))
        ≡ (λ y → fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (cS y))
    -- Push the functor-index transport into the function's codomain.
    push-subst-fn : ∀ {H₁ H₂ : SFunctor} (eq : H₁ ≡ H₂)
                      (f : ⟦ A ⟧ᴰ → T (⟦ H₁ ⟧SF ⟦ A ⟧ᴰ))
                  → subst (λ H → ⟦ A ⟧ᴰ → T (⟦ H ⟧SF ⟦ A ⟧ᴰ)) eq f
                    ≡ (λ x → subst (λ H → T (⟦ H ⟧SF ⟦ A ⟧ᴰ)) eq (f x))
    push-subst-fn refl f = refl

    -- THE content, pointwise in the seed. Both sides are a `fmapT` over the
    -- SAME underlying computation (`morph-app-bridge-fun` identifies them);
    -- what differs is the coercion chain on the value, which is exactly
    -- `coerce-νin-erase-D`.
    -- The seed, transported to the IR's erased carrier.
    seedOf : ⟦ A ⟧ᴰ → ⟦ ⌊ A ⌋ ⟧ᴰᴵ
    seedOf x = subst (λ z → z) (sym (cohᴰ A)) x

    -- `v0`: the coalgebra's value, read off the SHARED underlying computation
    -- `evalᴰ fmt coalgIR`. Both sides are a `fmapT` over this one thing.
    v0 : ⟦ A ⟧ᴰ → ℕ → ⟦ ⌊ ⟦ F ⟧T A ⌋ ⟧ᴰᴵ
    v0 x k = valueT (evalᴰ fmt coalgIR (seedOf x)) k

    -- The IR side's computation IS the shared one, up to `coalg'`'s codomain
    -- transport.
    e-eq : ∀ (x : ⟦ A ⟧ᴰ)
         → evalᴰ fmt coalg' (seedOf x)
           ≡ subst T (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute F A)) (evalᴰ fmt coalgIR (seedOf x))
    e-eq x = evalᴰ-subst-cod (⌊⟧T-commute F A) coalgIR (seedOf x)

    -- The surface side's computation is the shared one too — that is the IH.
    s-eq : ∀ (x : ⟦ A ⟧ᴰ)
         → (SD.⟦ coalg ⟧ˢ fmt tt >>=T (λ clo → clo x))
           ≡ subst T (cohᴰ (⟦ F ⟧T A)) (evalᴰ fmt coalgIR (seedOf x))
    s-eq x = sym (morph-app-bridge-fun coalg ih x)

    per-x-D179 : ∀ (x : ⟦ A ⟧ᴰ)
      → subst (λ H → T (⟦ H ⟧SF ⟦ A ⟧ᴰ)) (tF-coh F)
          (subst (λ Z → T (⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z)) (cohᴰ A)
            (fmapT (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ) (cE (seedOf x))))
        ≡ fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (cS x)
    per-x-D179 x = extensionality (λ k → cong₂ _,_ (tr k) (vl k))
      where
        -- Traces: neither `subst` nor `fmapT` touches a trace, so both sides
        -- reduce to the trace of the SHARED `evalᴰ fmt coalgIR` computation.
        LHSm : T (⟦ translateF Carrier Carrier F ⟧SF ⟦ A ⟧ᴰ)
        LHSm = subst (λ H → T (⟦ H ⟧SF ⟦ A ⟧ᴰ)) (tF-coh F)
                 (subst (λ Z → T (⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z)) (cohᴰ A)
                   (fmapT (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ) (cE (seedOf x))))

        tr : ∀ k → projTrace LHSm k ≡ projTrace (fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (cS x)) k
        tr k = t1 ⟨t⟩ t2 ⟨t⟩ t3 ⟨t⟩ t4 ⟨t⟩ t5 ⟨t⟩ t6 ⟨t⟩ t7 ⟨t⟩ t8
          where
            infixr 5 _⟨t⟩_
            _⟨t⟩_ : ∀ {X : Set} {a b c : X} → a ≡ b → b ≡ c → a ≡ c
            _⟨t⟩_ = trans

            t1 = cong (λ m → projTrace m k) (subst-fam-T (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F) _)
            t2 = subst-T-trace (cong (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F)) _ k
            t3 = cong (λ m → projTrace m k)
                   (subst-fam-T (λ Z → ⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z) (cohᴰ A) _)
            t4 = subst-T-trace
                   (cong (λ Z → ⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z) (cohᴰ A)) _ k
            t5 = cong (λ m → projTrace m k) (e-eq x)
            t6 = subst-T-trace (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute F A)) _ k
            t7 = sym (subst-T-trace (cohᴰ (⟦ F ⟧T A)) _ k)
            t8 = cong (λ m → projTrace m k) (sym (s-eq x))

        -- Values: push both `subst`s through `valueT`, and what is left on the
        -- left is EXACTLY `coerce-νin-erase-D`'s statement at the coalgebra's
        -- value `v0 x k`, with the right-hand side reached through the IH.
        infixr 5 _⟨v⟩_
        _⟨v⟩_ : ∀ {X : Set} {a b c : X} → a ≡ b → b ≡ c → a ≡ c
        _⟨v⟩_ = trans

        lhs-shape : ∀ k
          → valueT LHSm k
            ≡ subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F)
                (coerce-ν-in ⌈ eraseF F ⌉F ⟦ A ⟧ᴰ
                  (subst (λ Z → ⟦ ⌈ eraseF F ⌉F ⟧F Z) (cohᴰ A)
                    (coerce-functor-D ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ F A (v0 x k)))))
        lhs-shape k =
            cong (λ m → valueT m k) (subst-fam-T (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F) _)
          ⟨v⟩ valueT-subst (cong (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F)) _ k
          ⟨v⟩ subst-id-cong (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F) _
          ⟨v⟩ cong (subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F))
                (  cong (λ m → valueT m k)
                     (subst-fam-T (λ Z → ⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z) (cohᴰ A) _)
                 ⟨v⟩ valueT-subst
                       (cong (λ Z → ⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z) (cohᴰ A)) _ k
                 ⟨v⟩ subst-id-cong (λ Z → ⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z) (cohᴰ A) _
                 ⟨v⟩ coerce-ν-in-subst ⌈ eraseF F ⌉F (cohᴰ A) _
                 ⟨v⟩ cong (λ w → coerce-ν-in ⌈ eraseF F ⌉F ⟦ A ⟧ᴰ
                             (subst (λ Z → ⟦ ⌈ eraseF F ⌉F ⟧F Z) (cohᴰ A)
                               (coerce-functor-D ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉
                                 (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute (eraseF F) ⌊ A ⌋) w))))
                        (  cong (λ m → valueT m k) (e-eq x)
                         ⟨v⟩ valueT-subst (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute F A)) _ k))

        rhs-shape : ∀ k
          → valueT (fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (cS x)) k
            ≡ coerce-ν-in F ⟦ A ⟧ᴰ
                (coerce-functor-D F A (subst (λ z → z) (cohᴰ (⟦ F ⟧T A)) (v0 x k)))
        rhs-shape k =
          cong (λ w → coerce-ν-in F ⟦ A ⟧ᴰ (coerce-functor-D F A w))
            (  cong (λ m → valueT m k) (s-eq x)
             ⟨v⟩ valueT-subst (cohᴰ (⟦ F ⟧T A)) _ k)

        vl : ∀ k → valueT LHSm k ≡ valueT (fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (cS x)) k
        vl k = lhs-shape k ⟨v⟩ coerce-νin-erase-D F A (v0 x k) ⟨v⟩ sym (rhs-shape k)
    coalg-agree =
      trans (push-subst-fn (tF-coh F)
              (λ x → subst (λ Z → T (⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z)) (cohᴰ A)
                       (fmapT (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                              (cE (subst (λ z → z) (sym (cohᴰ A)) x)))))
            (extensionality per-x-D179)

    ana-agree : ∀ (a : ⟦ A ⟧ᴰ)
              → subst (λ z → z) (cohᴰ (ν-type F))
                  (anaFᵈ ⌈ eraseF F ⌉F cE (subst (λ z → z) (sym (cohᴰ A)) a))
                ≡ anaFᵈ F cS a
    ana-agree a =
      trans (subst-νᵈ-cong (tF-coh F) (anaFᵈ ⌈ eraseF F ⌉F cE (subst (λ z → z) (sym (cohᴰ A)) a)))
        (trans (anaᵈ-erase-full (tF-coh F) (cohᴰ A)
                  (λ y → fmapT (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ) (cE y))
                  (λ y → fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (cS y))
                  (subst (λ z → z) (sym (cohᴰ A)) a)
                  coalg-agree)
               (cong (anaFᵈ F cS) (subst-subst-sym (cohᴰ A))))

    per-a : (λ a → liftFn fmt {A} {ν-type F} Ana-IR a)
            ≡ proj₂ (SD.⟦ ana {Γ = Γ} wf coalg ⟧ˢ fmt dγ k)
    per-a = extensionality (λ a →
      trans (subst-T-returnT (cohᴰ (ν-type F))
               (anaFᵈ ⌈ eraseF F ⌉F cE (subst (λ z → z) (sym (cohᴰ A)) a)))
            (cong returnT (ana-agree a)))
