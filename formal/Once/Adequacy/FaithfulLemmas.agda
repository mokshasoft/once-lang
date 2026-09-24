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
import Once.Semantics.Machine as Val
open import Once.IR using (IR; _∘_; ⟨_,_⟩; apply; curry; terminal; id; snd; Cata; Ana; ⌊_⌋)
open import Once.Functor.Translate using (WellFormedF)
open import Once.IRTy using (⌊⟧T-commute; ⌈⟧TI-commute; eraseF; ⌈_⌉F; ⌈_⌉)
import Once.IRTy as II
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Denotation.Meaning using (cata-sem; cata-ev-algᴰ-D)
open import Once.Adequacy.CataErased fmt using (evalᴰ-Cata-erased; subst-T-projTrace; pairᴰ-subst⁻; T-ext; subst-T-resT)
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
open import Once.Res using (Res; stopped; returns; mapRes; mapRes-id; mapRes-∘; mapRes-cong)
open import Once.Denotation.TraceMonad using (T; returnT; valueT; projTrace; stoppedT; atT; _>>=T_; bindAt; fmapT; bindRes-mapʳ; >>=T-mapʳ; bindRes; bindResAt; >>=T-at)
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
-- plan 0.98: the round trip happens UNDER `mapRes`. `inject` at an arrow is
-- `resT-lift ∘ mapRes inject` and `forget` is `mapRes forget ∘ T.resT`, so the
-- two maps fuse and the codomain's IH applies pointwise inside.
forget-inject {A ⇒[ mk-kind Zero π ] B} pf =
  extensionality (λ u →
    trans (mapRes-∘ forget inject (pf u))
    (trans (mapRes-cong (λ z → forget-inject {B} z) (pf u))
           (mapRes-id (pf u))))
forget-inject {A ⇒[ mk-kind One π ] B} pf =
  extensionality (λ va →
    trans (cong (λ z → mapRes forget (mapRes inject (pf z))) (forget-inject {A} va))
    (trans (mapRes-∘ forget inject (pf va))
    (trans (mapRes-cong (λ z → forget-inject {B} z) (pf va))
           (mapRes-id (pf va)))))
forget-inject {A ⇒[ mk-kind Many π ] B} pf =
  extensionality (λ va →
    trans (cong (λ z → mapRes forget (mapRes inject (pf z))) (forget-inject {A} va))
    (trans (mapRes-∘ forget inject (pf va))
    (trans (mapRes-cong (λ z → forget-inject {B} z) (pf va))
           (mapRes-id (pf va)))))

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

-- plan 0.97: record eta from the BUDGET VIEW. Several proofs here are
-- naturally pointwise in the budget (they go through `bindAt`), and `atT`
-- bundles the three fields at one budget — so this is the bridge from that
-- shape to the equation of computations the statements now want.
-- A bind reads the head's result ONCE, so mapping the result before binding
-- is the same as composing the map into the continuation.
bindResAt-mapRes : ∀ {X Y Z : Set} (f : Y → T Z) (g : X → Y) (n : ℕ)
                     (es : List SigOpEvent) (r : Res X)
                 → bindResAt f n es (mapRes g r) ≡ bindResAt (λ x → f (g x)) n es r
bindResAt-mapRes f g n es stopped     = refl
bindResAt-mapRes f g n es (returns x) = refl

-- plan 0.98: the budget view is a PAIR, so this is two `cong`s, not three.
T-ext-at : ∀ {X : Set} {l r : T X} → (∀ n → atT l n ≡ atT r n) → l ≡ r
T-ext-at h = T-ext (λ n → cong proj₁ (h n)) (cong proj₂ (h 0))

-- D143: `apply ∘ ⟨ … ⟩` requires `⌊D ⇒[kk] E⌋ ≡ ⌊D⌋ ⇛ ⌊E⌋`, which holds only
-- at a NON-erased arrow — `⌊_⌋` sends a `Zero`-graded one to `Unit ⇛ ⌊E⌋`.
-- `Many` is what every consumer (the `ana` coalgebra) instantiates.
-- plan 0.97: ONE equation of computations. The budget-indexed form and the
-- `-fun` wrapper that recovered this from it are both gone — with `T` a
-- record, equal-at-every-budget IS equality, so the index was carrying
-- nothing.
morph-app-bridge : ∀ {D E π} (morph : Expr ∅ zeroUsage (D ⇒[ mk-kind Many π ] E))
                     (ih : liftFn fmt {⟦ ∅ ⟧ᶜ} {D ⇒[ mk-kind Many π ] E} (elaborate C.Heap morph) tt ≡ SD.⟦ morph ⟧ˢ fmt tt)
                     (w : ⟦ D ⟧ᴰ)
                   → liftFn fmt {D} {E} (apply ∘ ⟨ elaborate C.Heap morph ∘ terminal , id ⟩) w
                     ≡ (SD.⟦ morph ⟧ˢ fmt tt >>=T (λ clo → clo w))
morph-app-bridge {D} {E} {π} morph ih w =
  trans (cong (λ X → subst T (cohᴰ E) X) app-⟨⟩-clean)
    (trans (cong (λ h → subst T (cohᴰ E) (h >>=T (λ vf → vf w'))) ih-evalᴰ)
           (transport-apply-bind (cohᴰ D) (cohᴰ E) (SD.⟦ morph ⟧ˢ fmt tt) w))
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
    -- plan 0.98: the pair-build's residual is a `mapRes` on the RESULT, and a
    -- bind reads that result once — so the two binds differ only by which
    -- function they apply to the value, which is `bindResAt-mapRes`.
    app-⟨⟩-clean = T-ext-at (λ j →
      trans (>>=T-at (evalᴰ fmt ⟨ elaborate C.Heap morph ∘ terminal {⌊ D ⌋} , id {⌊ D ⌋} ⟩ w')
                     (evalᴰ fmt (apply {⌊ D ⌋} {⌊ E ⌋})) j)
      (trans (cong (bindAt (evalᴰ fmt (apply {⌊ D ⌋} {⌊ E ⌋})) j) (pair-eq j))
      (trans (bindResAt-mapRes (evalᴰ fmt (apply {⌊ D ⌋} {⌊ E ⌋})) (λ v → (v , w'))
                               j (projTrace mc j) (T.resT mc))
             (sym (>>=T-at mc (λ vf → vf w') j)))))
      where
        mc = evalᴰ fmt (elaborate C.Heap morph) tt

        -- plan 0.98: the pair-build's residual is ONE lemma now. 0.97 had to
        -- fix up the trace and the flag separately (`join-es-idʳ` /
        -- `join-st-idʳ`) because the budget view was a triple; the pair-build
        -- is just `mc` with its value paired against `w'`, i.e. a `fmapT`, and
        -- its stopped branch has no `++ []` to remove because no sequel was
        -- ever built.
        -- Split on `mc`'s RESULT: stopped leaves the head's own trace with no
        -- sequel built, and returning leaves the pair-build's `++ []`.
        pair-eq-of : ∀ (r : Res ⟦ ⌊ D ⇒[ mk-kind Many π ] E ⌋ ⟧ᴰᴵ) (j : ℕ)
                   → atT (bindRes (λ n → T.trT mc n) r
                            (λ b → evalᴰ fmt (id {⌊ D ⌋}) w' >>=T (λ c → returnT (b , c)))) j
                     ≡ (projTrace mc j , mapRes (λ v → (v , w')) r)
        pair-eq-of stopped     j = refl
        pair-eq-of (returns v) j = cong (_, returns (v , w')) (++-identityʳ (T.trT mc j))

        pair-eq : ∀ j → atT (evalᴰ fmt ⟨ elaborate C.Heap morph ∘ terminal {⌊ D ⌋} , id {⌊ D ⌋} ⟩ w') j
                        ≡ (projTrace mc j , mapRes (λ v → (v , w')) (T.resT mc))
        pair-eq j = pair-eq-of (T.resT mc) j
    -- `ih` in `evalᴰ`-form: `evalᴰ (elaborate morph) tt ≡ subst T (sym cohᴰ(D⇒E)) (SD.⟦morph⟧ˢ tt)`.
    ih-evalᴰ : evalᴰ fmt (elaborate C.Heap morph) tt
               ≡ subst T (sym (cong₂ (λ x y → x → T y) (cohᴰ D) (cohᴰ E))) (SD.⟦ morph ⟧ˢ fmt tt)
    ih-evalᴰ = trans (sym (subst-sym-subst (cong₂ (λ x y → x → T y) (cohᴰ D) (cohᴰ E))))
                     (cong (subst T (sym (cong₂ (λ x y → x → T y) (cohᴰ D) (cohᴰ E)))) ih)

-- (`morph-app-bridge-fun` is retired: it recovered the computation equation
-- from the budget-indexed one, and the budget-indexed one no longer exists.)
morph-app-bridge-fun = morph-app-bridge

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
              (ih : liftFn fmt {⟦ ∅ ⟧ᶜ} {⟦ F ⟧T A ⇒[ mk-kind Many π ] A} (elaborate C.Heap alg) tt ≡ SD.⟦ alg ⟧ˢ fmt tt)
              (dγ : ⟦ ⟦ Γ ↾ zeroUsage ⟧ᶜ ⟧ᴰ)
            → liftFn fmt {⟦ Γ ↾ zeroUsage ⟧ᶜ} {μ-type F ⇒[ mk-kind Many π ] A}
                (elaborate C.Heap (cata {Γ = Γ} wf alg)) dγ
              ≡ SD.⟦ cata {Γ = Γ} wf alg ⟧ˢ fmt dγ
cata-body {Γ = Γ} {F = F} {A = A} {π = π} wf alg ih dγ =
  trans split fold-step
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
                                      ih)))

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

-- plan 0.98: the `valueT`-transport lemma is GONE. A transport moves the
-- RESULT, not a value — `subst-T-resT` (CataErased) is its replacement, and it
-- needs no "there is a value" side condition because `mapRes` has none.
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
             (ih : liftFn fmt {⟦ ∅ ⟧ᶜ} {A ⇒[ mk-kind Many π ] ⟦ F ⟧T A} (elaborate C.Heap coalg) tt ≡ SD.⟦ coalg ⟧ˢ fmt tt)
             (dγ : ⟦ ⟦ Γ ↾ zeroUsage ⟧ᶜ ⟧ᴰ)
           → liftFn fmt {⟦ Γ ↾ zeroUsage ⟧ᶜ} {A ⇒[ mk-kind Many π ] ν-type F} (elaborate C.Heap (ana {Γ = Γ} wf coalg)) dγ
             ≡ SD.⟦ ana {Γ = Γ} wf coalg ⟧ˢ fmt dγ
ana-body {Γ = Γ} {F = F} {A = A} {π = π} wf coalg ih dγ =
  trans elab-ana-reduce (cong returnT per-a)
  where
    coalgIR : IR ⌊ A ⌋ ⌊ ⟦ F ⟧T A ⌋
    coalgIR = apply ∘ ⟨ elaborate C.Heap coalg ∘ terminal , id ⟩
    coalg' = subst (λ o → IR ⌊ A ⌋ o) (⌊⟧T-commute F A) coalgIR
    Ana-IR : IR ⌊ A ⌋ ⌊ ν-type F ⌋
    Ana-IR = Ana (wf-⌊⌋ wf) coalg'

    elab-ana-reduce : liftFn fmt {⟦ Γ ↾ zeroUsage ⟧ᶜ} {A ⇒[ mk-kind Many π ] ν-type F} (elaborate C.Heap (ana {Γ = Γ} wf coalg)) dγ
                      ≡ returnT (λ a → liftFn fmt {A} {ν-type F} Ana-IR a)
    elab-ana-reduce =
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
    s-eq x = sym (morph-app-bridge coalg ih x)

    per-x-D179 : ∀ (x : ⟦ A ⟧ᴰ)
      → subst (λ H → T (⟦ H ⟧SF ⟦ A ⟧ᴰ)) (tF-coh F)
          (subst (λ Z → T (⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z)) (cohᴰ A)
            (fmapT (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ) (cE (seedOf x))))
        ≡ fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (cS x)
    -- plan 0.98: TWO obligations became ONE. 0.97 proved the stop flag and the
    -- value separately (`st` by eight `subst-T-stop` steps, `vl` by the
    -- `coerce-νin-erase-D` chain) and `T-ext` consumed both. With the value
    -- inside `Res` there is a single result field, and the coercion chain that
    -- acted on the value now acts UNDER `mapRes` — so the flag half comes for
    -- free: `mapRes` cannot turn a `stopped` into a `returns`.
    per-x-D179 x = T-ext tr res-eq
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

        -- plan 0.98: `R0` replaces 0.97's `v0`. `v0` read a VALUE at a budget;
        -- the result does not depend on the budget (only the trace does), so
        -- the index went with the value.
        R0 : Res ⟦ ⌊ ⟦ F ⟧T A ⌋ ⟧ᴰᴵ
        R0 = T.resT (evalᴰ fmt coalgIR (seedOf x))

        infixr 5 _⟨v⟩_
        _⟨v⟩_ : ∀ {X : Set} {a b c : X} → a ≡ b → b ≡ c → a ≡ c
        _⟨v⟩_ = trans

        -- The two coercion chains, read as functions of the coalgebra's
        -- RESULT. They are exactly the two sides of `coerce-νin-erase-D`, and
        -- each side's result is its chain `mapRes`ed over the shared `R0`.
        fM : ⟦ ⌊ ⟦ F ⟧T A ⌋ ⟧ᴰᴵ → ⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ
        fM w = coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ
                 (coerce-functor-D ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ F A w))

        fI : ⟦ ⌊ ⟦ F ⟧T A ⌋ ⟧ᴰᴵ → ⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF ⟦ A ⟧ᴰ
        fI w = coerce-ν-in ⌈ eraseF F ⌉F ⟦ A ⟧ᴰ
                 (subst (λ Z → ⟦ ⌈ eraseF F ⌉F ⟧F Z) (cohᴰ A)
                   (coerce-functor-D ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ F A w)))

        fL : ⟦ ⌊ ⟦ F ⟧T A ⌋ ⟧ᴰᴵ → ⟦ translateF Carrier Carrier F ⟧SF ⟦ A ⟧ᴰ
        fL w = subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F) (fI w)

        fR : ⟦ ⌊ ⟦ F ⟧T A ⌋ ⟧ᴰᴵ → ⟦ translateF Carrier Carrier F ⟧SF ⟦ A ⟧ᴰ
        fR w = coerce-ν-in F ⟦ A ⟧ᴰ
                 (coerce-functor-D F A (subst (λ z → z) (cohᴰ (⟦ F ⟧T A)) w))

        -- The IR side, innermost first: the coalgebra's own computation IS the
        -- shared one (`e-eq`), a transport moves a result by `mapRes`
        -- (`subst-T-resT`), and `fmapT` IS `mapRes` on the result — so the
        -- three maps fuse into `fM`.
        m2-shape : T.resT (fmapT (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ) (cE (seedOf x)))
                 ≡ mapRes fM R0
        m2-shape =
            cong (λ mm → T.resT (fmapT (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                           (fmapT (λ y → coerce-functor-D ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉
                                           (subst (λ Ty → ⟦ Ty ⟧ᴰ)
                                                  (⌈⟧TI-commute (eraseF F) ⌊ A ⌋) y))
                                  mm)))
                 (e-eq x)
          ⟨v⟩ cong (λ r → mapRes (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                            (mapRes (λ y → coerce-functor-D ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉
                                             (subst (λ Ty → ⟦ Ty ⟧ᴰ)
                                                    (⌈⟧TI-commute (eraseF F) ⌊ A ⌋) y)) r))
                   (subst-T-resT (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute F A)) (evalᴰ fmt coalgIR (seedOf x)))
          ⟨v⟩ cong (mapRes (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ))
                   (mapRes-∘ (λ y → coerce-functor-D ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉
                                      (subst (λ Ty → ⟦ Ty ⟧ᴰ)
                                             (⌈⟧TI-commute (eraseF F) ⌊ A ⌋) y))
                             (subst (λ z → z) (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute F A)))
                             R0)
          ⟨v⟩ mapRes-∘ (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                       (λ w → coerce-functor-D ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ F A w))
                       R0

        -- …then the carrier transport, which passes through `coerce-ν-in`
        -- (`coerce-ν-in-subst`) once it is on the value side of the `mapRes`.
        inner-shape : T.resT (subst (λ Z → T (⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z)) (cohᴰ A)
                               (fmapT (coerce-ν-in ⌈ eraseF F ⌉F ⟦ ⌊ A ⌋ ⟧ᴰᴵ) (cE (seedOf x))))
                    ≡ mapRes fI R0
        inner-shape =
            cong T.resT (subst-fam-T (λ Z → ⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z) (cohᴰ A) _)
          ⟨v⟩ subst-T-resT (cong (λ Z → ⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z) (cohᴰ A)) _
          ⟨v⟩ mapRes-cong (subst-id-cong (λ Z → ⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z) (cohᴰ A)) _
          ⟨v⟩ cong (mapRes (subst (λ Z → ⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z) (cohᴰ A))) m2-shape
          ⟨v⟩ mapRes-∘ (subst (λ Z → ⟦ translateF Carrier Carrier ⌈ eraseF F ⌉F ⟧SF Z) (cohᴰ A)) fM R0
          ⟨v⟩ mapRes-cong (λ w → coerce-ν-in-subst ⌈ eraseF F ⌉F (cohᴰ A)
                                   (coerce-functor-D ⌈ eraseF F ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ F A w))) R0

        -- …and finally the functor transport.
        lhs-shape : T.resT LHSm ≡ mapRes fL R0
        lhs-shape =
            cong T.resT (subst-fam-T (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F) _)
          ⟨v⟩ subst-T-resT (cong (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F)) _
          ⟨v⟩ mapRes-cong (subst-id-cong (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F)) _
          ⟨v⟩ cong (mapRes (subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F))) inner-shape
          ⟨v⟩ mapRes-∘ (subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh F)) fI R0

        -- The surface side, the same way: its computation is the shared one
        -- too (that is the IH, via `s-eq`), so its result is `fR` over `R0`.
        rhs-shape : T.resT (fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (cS x)) ≡ mapRes fR R0
        rhs-shape =
            cong (λ mm → T.resT (fmapT (coerce-ν-in F ⟦ A ⟧ᴰ)
                           (fmapT (coerce-functor-D F A) mm)))
                 (s-eq x)
          ⟨v⟩ cong (λ r → mapRes (coerce-ν-in F ⟦ A ⟧ᴰ) (mapRes (coerce-functor-D F A) r))
                   (subst-T-resT (cohᴰ (⟦ F ⟧T A)) (evalᴰ fmt coalgIR (seedOf x)))
          ⟨v⟩ cong (mapRes (coerce-ν-in F ⟦ A ⟧ᴰ))
                   (mapRes-∘ (coerce-functor-D F A) (subst (λ z → z) (cohᴰ (⟦ F ⟧T A))) R0)
          ⟨v⟩ mapRes-∘ (coerce-ν-in F ⟦ A ⟧ᴰ)
                       (λ w → coerce-functor-D F A (subst (λ z → z) (cohᴰ (⟦ F ⟧T A)) w))
                       R0

        -- Both sides are the SAME result mapped by the two chains, and the two
        -- chains agree pointwise — that is `coerce-νin-erase-D`, unchanged.
        res-eq : T.resT LHSm ≡ T.resT (fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (cS x))
        res-eq = lhs-shape
          ⟨v⟩ mapRes-cong (coerce-νin-erase-D F A) R0
          ⟨v⟩ sym rhs-shape
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
            ≡ valueT (SD.⟦ ana {Γ = Γ} wf coalg ⟧ˢ fmt dγ) 0
    per-a = extensionality (λ a →
      trans (subst-T-returnT (cohᴰ (ν-type F))
               (anaFᵈ ⌈ eraseF F ⌉F cE (subst (λ z → z) (sym (cohᴰ A)) a)))
            (cong returnT (ana-agree a)))
