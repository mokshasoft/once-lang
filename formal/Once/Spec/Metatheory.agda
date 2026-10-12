-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Metatheory — WHAT THE LANGUAGE PROMISES ABOUT ITSELF (D304).
--
-- A metatheorem is a claim about the Spec ALONE: it mentions no compiler. If
-- one cannot be proved, the LANGUAGE is wrong, not the compiler — D276 made
-- the grades affine precisely so that substitution is typed. So the
-- statements are part of the Spec, read with the definition they constrain;
-- the proofs are not (D140): they live under `Once.Metatheory`, which may
-- import only the Spec and its semantic domain, never the compiler
-- (`scripts/metatheory-gate.sh`). `Once.Certified` carries the proofs, so
-- each statement is on the apex and goes red when the Spec moves.
--
-- Seven parts:
--   * `term-model` — for every signature of definitions `S`, the core's TERM
--     MODEL (`Once.Spec.Core.TermModel`): substitution of terms is typed
--     (`subst-⊢`), a pure `let` means its substitution (`let-β`, referential
--     transparency), and substitution of types is typed (`ty-subst-⊢`, D303).
--   * `type-system` — the surface typing judgment (D305): subtyping and the
--     purity order are partial orders whose derivations are unique (so a
--     coercion has one meaning), and a term's usage is a property of the term,
--     not of the mode that typed it — synthesis is unique, checking agrees
--     with it, the domain-given mode is exact.
--   * `effects` — the meaning's effect structure (plan 0.112 E, C4): each
--     grade's `M π` is a monad, subeffecting `subM` and the erasure `toT` to
--     the interaction tree are monad morphisms, and the observation `run`
--     respects return and bind (`then` threads the history).
--   * `coherence` — the core meaning is a function of the JUDGMENT, not of the
--     derivation chosen for it (plan 0.116; `Spec.Core.Coherence`).
--   * `freyd` — effects form a Freyd category (plan 0.116): a computation is
--     central (commutes with every other) exactly when it is pure, and only a
--     pure computation may be skipped. So `pure` (D250: referential
--     transparency) is the categorical notion, and a meaning that drops or
--     moves an effectful computation is unsound.
--   * `recursion` — the fold is the unique algebra morphism out of `μ`, and
--     fusion holds (plan 0.112 D3). STATED, NOT YET PROVED: `Once.Metatheory`
--     postulates both (`Once.Metatheory.Recursion`).
--   * `totality` — Once is total and productive (D311): an effectful
--     computation that returns is a finite tree, and every layer of every
--     stream comes after finite work (`Spec.Totality`).
--
-- No type-safety theorem is needed in this setting: the meaning is a TOTAL
-- function on derivations, so every well-typed program means something by
-- construction.
------------------------------------------------------------------------

module Once.Spec.Metatheory where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Contract using (ISig)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Core.TermModel using (TermModel) public
open import Once.Spec.Core.Coherence using (Coherence)
open import Once.Spec.Type.Grade using (Purity; pure; mk-kind; Many)
open import Once.Spec.Type using (Type; _⇒[_]_; μ-type; ν-type; ⟦_⟧T)
open import Once.Spec.Totality using (FiniteT; FiniteM; selfRef; forwardRef; defF; tickDefs; ticker)
open import Once.Spec.Module using (ModTele; emptyScope)
open import Once.Spec.Context using (∅)
open import Once.Spec.Type.WellFormed using (wf-Id)
open import Once.Spec.Type.Grade using (eff)
open import Once.Spec.Type using (Id)
open import Once.Spec.Type.Sub using (⊑-pe)
open import Data.List using (_∷_; [])
open import Data.Unit using (tt)
open import Data.Product using (∃-syntax)
open import Relation.Nullary using (¬_)
open import Once.Denotation.TraceMonad using (call)
import Once.Spec.Core.Typing
import Once.Spec.Core.Meaning
open import Once.Spec.Type.Sub using (_<:_; _⊑π_)
open import Once.Spec.Type.WellFormed using (WellFormedF)
open import Once.Spec.Meaning
  using ( T ; returnT ; _>>=T_ ; Interp ; run ; then ; SigOpEvent
        ; M ; ⟦_⟧ᵛ ; returnM ; bindM ; subM ; toT
        ; in-valueᵛ ; cata-semᵛ ; mapLayerᵛ ; ana-semᵛ ; out-semᵛ )
open import Once.Spec.Syntax using (RawExpr)
open import Once.Spec.Typing.Scope using (NamedCtx)
open import Once.Spec.Typing using (_⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_; _⊢ᵈ_∶_⇒[_]↦_⨾_)
import Once.Spec.Context as Surface

-- The surface typing judgment's laws (D305).
record TypeSystem : Set where
  field
    -- subtyping is a preorder with unique derivations (D226: one judgment)
    <:-refl   : ∀ A → A <: A
    <:-trans  : ∀ {A B C} → A <: B → B <: C → A <: C
    <:-unique : ∀ {A B} (p q : A <: B) → p ≡ q
    -- …and so is the purity order
    ⊑π-refl   : ∀ π → π ⊑π π
    ⊑π-trans  : ∀ {π₁ π₂ π₃} → π₁ ⊑π π₂ → π₂ ⊑π π₃ → π₁ ⊑π π₃
    ⊑π-unique : ∀ {π π′} (g h : π ⊑π π′) → g ≡ h

    -- synthesis is unique
    synth-unique : ∀ {ctx : NamedCtx} {e : RawExpr} {A A′ : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                 → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᵢ e ∶ A′ ⨾ Ψ′ → A ≡ A′ × Ψ ≡ Ψ′
    -- checking at one type gives one usage
    check-usage-unique : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                       → ctx ⊢ᶜ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ A ⨾ Ψ′ → Ψ ≡ Ψ′
    -- checking agrees with synthesis on usage
    check-agrees-synth : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                       → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ B ⨾ Ψ′ → Ψ ≡ Ψ′
    -- the domain-given mode agrees with checking at an arrow from its domain
    domain-agrees-check : ∀ {ctx : NamedCtx} {e : RawExpr} {A B B′ : Type} {π : Purity}
                            {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                        → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᶜ e ∶ (A ⇒[ mk-kind Many π ] B′) ⨾ Ψ′ → Ψ ≡ Ψ′
    -- a term that synthesizes is domain-given only through its synthesized arrow
    domain-agrees-synth : ∀ {ctx : NamedCtx} {e : RawExpr} {A B S : Type} {π : Purity}
                            {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                        → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᵢ e ∶ S ⨾ Ψ′
                        → Σ[ A′ ∈ Type ] Σ[ π′ ∈ Purity ] (S ≡ (A′ ⇒[ mk-kind Many π′ ] B)) × π′ ⊑π π × Ψ ≡ Ψ′
    -- the domain-given mode is exact: its output is determined by its input
    domain-exact : ∀ {ctx : NamedCtx} {e : RawExpr} {A B B′ : Type} {π : Purity}
                     {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                 → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B′ ⨾ Ψ′ → B ≡ B′ × Ψ ≡ Ψ′

-- The meaning's effect structure (plan 0.112 E, C4).
record Effects : Set₁ where
  field
    -- each grade's `M π` is a monad
    M-identityˡ : ∀ π {X Y : Set} (x : X) (k : X → M π Y) → bindM π (returnM π x) k ≡ k x
    M-identityʳ : ∀ π {X : Set} (m : M π X) → bindM π m (returnM π) ≡ m
    M-assoc     : ∀ π {X Y Z : Set} (m : M π X) (f : X → M π Y) (g : Y → M π Z)
                → bindM π (bindM π m f) g ≡ bindM π m (λ x → bindM π (f x) g)
    -- subeffecting is a monad morphism `M π → M π′`
    subM-return : ∀ {π π′} (g : π ⊑π π′) {X : Set} (x : X) → subM g (returnM π x) ≡ returnM π′ x
    subM-bind   : ∀ {π π′} (g : π ⊑π π′) {X Y : Set} (m : M π X) (k : X → M π Y)
                → subM g (bindM π m k) ≡ bindM π′ (subM g m) (λ x → subM g (k x))
    -- so is the erasure of a grade to the interaction tree
    toT-return  : ∀ π {X : Set} (x : X) → toT π (returnM π x) ≡ returnT x
    toT-bind    : ∀ π {X Y : Set} (m : M π X) (k : X → M π Y)
                → toT π (bindM π m k) ≡ (toT π m >>=T λ x → toT π (k x))
    -- the observation respects return and bind
    run-return  : ∀ (ι : Interp) (h : List SigOpEvent) {X Y : Set} (x : X) (f : X → T Y)
                → then ι h (run ι h (returnT x)) f ≡ run ι h (f x)
    run-bind    : ∀ (ι : Interp) (h : List SigOpEvent) {X Y : Set} (m : T X) (f : X → T Y)
                → run ι h (m >>=T f) ≡ then ι h (run ι h m) f

-- The fold's universal property (plan 0.112 D3) and unfold's computation law
-- (plan 0.116 E).
record Recursion : Set₁ where
  field
    -- `fold alg` is the only `h` that commutes with the constructor
    fold-unique : ∀ π {F A} (wf : WellFormedF F) (alg : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ)
                    (h : ⟦ μ-type F ⟧ᵛ → M π ⟦ A ⟧ᵛ)
                → (∀ x → h (in-valueᵛ wf x) ≡ bindM π (mapLayerᵛ π wf h x) alg)
                → ∀ v → h v ≡ cata-semᵛ π wf alg v
    -- fusion: a map that commutes with the algebras commutes with the folds
    fold-fusion : ∀ π {F A B} (wf : WellFormedF F)
                    (alg : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ) (alg′ : ⟦ ⟦ F ⟧T B ⟧ᵛ → M π ⟦ B ⟧ᵛ)
                    (f : ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ)
                → (∀ y → bindM π (alg y) f ≡ bindM π (mapLayerᵛ π wf f y) alg′)
                → ∀ v → bindM π (cata-semᵛ π wf alg v) f ≡ cata-semᵛ π wf alg′ v
    -- unfold's computation law (plan 0.116 E): forcing `unfold c s` runs the
    -- coalgebra FUNCTION on the seed (once per forced layer; its term was
    -- evaluated once, when the stream was built — D273) and puts `unfold c` at
    -- the recursive positions. An effectful coalgebra is a server (D233). With
    -- it, every observation of a stream is determined; uniqueness holds up to
    -- bisimilarity (the final T∘F-coalgebra).
    unfold-out  : ∀ π {F A} (wf : WellFormedF F) (clo : ⟦ A ⟧ᵛ → M π ⟦ ⟦ F ⟧T A ⟧ᵛ) (a : ⟦ A ⟧ᵛ)
                → out-semᵛ π wf (ana-semᵛ π pure wf clo a)
                  ≡ bindM π (clo a) (mapLayerᵛ π wf (λ a′ → returnM π (ana-semᵛ π pure wf clo a′)))

-- Effects form a Freyd category (plan 0.116). Values and pure maps are the
-- category C, computations `X → T Y` the premonoidal category K = Kleisli(T),
-- and subeffecting `returnT` (D250, `subM ⊑-pe`) the embedding J : C → K.
-- A computation is CENTRAL when it commutes with every computation: running it
-- before or after another gives the same tree.
Central : ∀ {Y : Set} → T Y → Set₁
Central {Y} m = ∀ {W : Set} (n : T W)
              → (m >>=T λ y → n >>=T λ w → returnT (y , w)) ≡ (n >>=T λ w → m >>=T λ y → returnT (y , w))

record Freyd : Set₁ where
  field
    -- J's image is central: a pure computation commutes with every computation
    pure-central : ∀ {Y : Set} (y : Y) → Central (returnT y)
    -- and only it: a central computation is pure (`T` is free over call/halt)
    central-pure : ∀ {Y : Set} (m : T Y) → Central m → Σ[ y ∈ Y ] m ≡ returnT y
    -- only a pure computation may be skipped: one whose run can be dropped
    -- before every continuation is a value
    discard-pure : ∀ {Y : Set} (m : T Y) → (∀ {W : Set} (k : T W) → (m >>=T λ _ → k) ≡ k)
                 → Σ[ y ∈ Y ] m ≡ returnT y

-- Once is TOTAL and PRODUCTIVE (D311, plan 0.117 A; `Spec.Totality`). An
-- effectful computation that returns ends, on every path, after finitely many
-- events; so does each layer of every stream, effectful or not. With an
-- inductive `T` these hold by construction, and that is their job here: a
-- silent step in `T`, or a coinductive `T` without a guard — what general
-- recursion would need (OCP-0003) — makes them false.
--
-- And what it does NOT give up (`Spec.Totality` names the programs): a
-- definition cannot name itself or a later definition — there is no general
-- recursion to be partial with — while a stream whose every layer performs an
-- effect, the shape of every server, is typed, and its first layer does
-- perform one.
module TickTyping  = Once.Spec.Core.Typing tickDefs
module TickMeaning = Once.Spec.Core.Meaning tickDefs

record Totality : Set₁ where
  field
    finite     : ∀ {X : Set} (m : T X) → FiniteT m
    productive : ∀ π {F} (wf : WellFormedF F) (v : ⟦ ν-type F π ⟧ᵛ) → FiniteM π (out-semᵛ π wf v)
    no-self-reference    : ¬ ModTele emptyScope (selfRef ∷ [])
    no-forward-reference : ¬ ModTele emptyScope (forwardRef ∷ defF ∷ [])
    stream-typed : TickTyping._⊢[_]_∷_!_ ∅ Surface.[] ticker (ν-type Id eff) pure
    stream-emits : ∀ fmt (ds : TickMeaning.DefSem)
                 → ∃[ o ] ∃[ a ] ∃[ k ]
                   TickMeaning.⟦ TickTyping.⊢out wf-Id (TickTyping.⊢sub-eff ⊑-pe stream-typed) ⟧ fmt ds tt
                   ≡ call o a k

record Metatheory : Set₁ where
  field
    term-model  : ∀ {Fs : ISig} {s : ℕ} (S : Sig Fs s) → TermModel S
    type-system : TypeSystem
    effects     : Effects
    coherence   : ∀ {Fs : ISig} {s : ℕ} (S : Sig Fs s) → Coherence S
    freyd       : Freyd
    recursion   : Recursion
    totality    : Totality
