{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- SPIKE 9 (§4.2¹³) — THE ERASED-CARRIER MODEL.  A route that is NOT on the
-- §4.2‴…§4.2¹² list, and that does not have the blocking edge at all.
--
-- OBSERVATION THAT UNLOCKS IT.  `NbEPDirDTTCh`'s typing has SIX rules —
-- ⊢vz ⊢vs ⊢tt ⊢ff ⊢lam ⊢app — and *no conversion rule* and *no 𝕀 eliminator*.
-- So a syntactic type NEVER has to compute for a derivation to exist.  The
-- interpretation therefore does NOT have to be a function of an environment:
-- the carrier of a type can be read off the type SYNTAX alone.
--
-- CONSEQUENCE.  Split the model in two:
--   Layer 1 (here, CLOSED)  ⟦_⟧T : Ty Γ → Set          -- term-BLIND carrier
--                           ⟦_⟧M : Δ ⊢ t ∷ A → ⟦Δ⟧C → ⟦A⟧T
--   Layer 2 (here, DEFINED) ⟨_⟩T : Δ ⊨ A → ⟦Δ⟧C → ⟦A⟧T → Set
--                                                      -- the honest dependency
--
-- Every obstruction the fuel design fought lives in Layer 1's coherence lemmas
-- (`ren-⟦⟧`, `sub-⟦⟧`) — and BOTH are 4-case structural inductions on the TYPE,
-- because ⟦_⟧T ignores terms.  There is no environment in their statements, so:
--   · no `CI`, no `envO`, no `CIwf`, no `nat-MI`, no OPE naturality;
--   · no `Û`/`Êl` universe  ⇒ no strict positivity, no large elimination;
--   · no fuel, no bounds, no `--prop`, no `TERMINATING`;
--   · `MI ⊢app` needs NO soundness invariant (`⟦subTy (single u) B⟧T ≡ ⟦B⟧T`
--     is term-blind) ⇒ **the `MI → MI-ty` back-edge of §4.2¹² does not exist.**
--
-- ⚠ HONEST SCOPE.  Layer 1 alone proves `consistency` for the raw calculus but
-- it ERASES the dependency (⟦𝕀 t A B⟧T does not look at t).  Layer 2 is what
-- restores it, and it is a PREDICATE over an already-fixed carrier, not a
-- second carrier — so it can never feed back into Layer 1.  Layer 2's
-- fundamental theorem is NOT attempted here (see the closing note).
------------------------------------------------------------------------
module poc.OCP0009.SpikeErase where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma    using ( Σ; _,_; fst; snd )
open import poc.OCP0009.NbEPDirDTTCh

data Empty : Set where
record ⊤ : Set where
  constructor ⋆
data 𝟚 : Set where 0₂ 1₂ : 𝟚
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

coe : {A B : Set} → A ≡ B → A → B
coe refl a = a

------------------------------------------------------------------------
-- LAYER 1a — the erased carrier.  Structural on `Ty`; BLIND to `Tm`.
--
-- 𝕀's carrier is the DISJOINT UNION of the two branches: big enough to hold a
-- value of either branch, so Layer 2 can still pin down which one — but the
-- CHOICE is not made here, which is exactly why this layer needs no semantics
-- of the condition and hence no environment.
------------------------------------------------------------------------

⟦_⟧T : ∀ {Γ} → Ty Γ → Set
⟦ 𝔹       ⟧T = 𝟚
⟦ ⊥̇       ⟧T = Empty
⟦ 𝕀 t A B ⟧T = ⟦ A ⟧T ⊎ ⟦ B ⟧T
⟦ Π̇ A B   ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

-- THE TWO COHERENCE LEMMAS.  Compare §4.2‴/§4.2⁹: these are the `wkTI`/`subTI`
-- of this model, and both are 4 lines.  No environment, no OPE, no fuel.
ren-⟦⟧ : ∀ {Γ Δ}(ρ : Ren Γ Δ)(A : Ty Γ) → ⟦ renTy ρ A ⟧T ≡ ⟦ A ⟧T
ren-⟦⟧ ρ 𝔹         = refl
ren-⟦⟧ ρ ⊥̇         = refl
ren-⟦⟧ ρ (𝕀 t A B) = cong₂ _⊎_ (ren-⟦⟧ ρ A) (ren-⟦⟧ ρ B)
ren-⟦⟧ ρ (Π̇ A B)   = cong₂ (λ X Y → X → Y) (ren-⟦⟧ ρ A) (ren-⟦⟧ (extR ρ) B)

sub-⟦⟧ : ∀ {Γ Δ}(σ : Sub Γ Δ)(A : Ty Γ) → ⟦ subTy σ A ⟧T ≡ ⟦ A ⟧T
sub-⟦⟧ σ 𝔹         = refl
sub-⟦⟧ σ ⊥̇         = refl
sub-⟦⟧ σ (𝕀 t A B) = cong₂ _⊎_ (sub-⟦⟧ σ A) (sub-⟦⟧ σ B)
sub-⟦⟧ σ (Π̇ A B)   = cong₂ (λ X Y → X → Y) (sub-⟦⟧ σ A) (sub-⟦⟧ (extS σ) B)

------------------------------------------------------------------------
-- LAYER 1b — environments and the term interpretation.
-- `⟦_⟧C` recurses on `Con` alone; it never calls `_⊨_`.  `⟦_⟧M` recurses on the
-- `⊢` derivation alone and DISCARDS every carried well-formedness proof.
------------------------------------------------------------------------

⟦_⟧C : ∀ {Γ} → Con Γ → Set
⟦ ε              ⟧C = ⊤
⟦ _▷_ Δ {A} wA   ⟧C = Σ ⟦ Δ ⟧C (λ _ → ⟦ A ⟧T)

⟦_⟧M : ∀ {Γ}{Δ : Con Γ}{t A} → Δ ⊢ t ∷ A → ⟦ Δ ⟧C → ⟦ A ⟧T
⟦ ⊢vz {A = A} wR       ⟧M (γ , a) = coe (sym (ren-⟦⟧ vs A)) a
⟦ ⊢vs {A = A} wA wR td ⟧M (γ , _) = coe (sym (ren-⟦⟧ vs A)) (⟦ td ⟧M γ)
⟦ ⊢tt                  ⟧M γ       = 1₂
⟦ ⊢ff                  ⟧M γ       = 0₂
⟦ ⊢lam wA td           ⟧M γ       = λ a → ⟦ td ⟧M (γ , a)
⟦ ⊢app {B = B} {u = u} wΠ tf tu ⟧M γ =
  coe (sym (sub-⟦⟧ (single u) B)) (⟦ tf ⟧M γ (⟦ tu ⟧M γ))

------------------------------------------------------------------------
-- ★ CONSISTENCY for the RAW calculus.  --safe, zero postulates, zero holes,
--   zero TERMINATING, zero fuel.
------------------------------------------------------------------------

consistency : ∀ {t} → ε ⊢ t ∷ ⊥̇ → Empty
consistency td = ⟦ td ⟧M ⋆

------------------------------------------------------------------------
-- CONTROLS — `consistency` must not be vacuous through a degenerate ⟦_⟧M.
-- Real derivations, real computation, checked by `refl`.
------------------------------------------------------------------------

-- ε ⊢ lam 𝔹 (var vz) ∷ Π̇ 𝔹 𝔹, applied to tt.
idB : ε ⊢ lam 𝔹 (var vz) ∷ Π̇ 𝔹 𝔹
idB = ⊢lam ⊨𝔹 (⊢vz ⊨𝔹)

ctrl-id : ⟦ idB ⟧M ⋆ 1₂ ≡ 1₂
ctrl-id = refl

ctrl-app : ⟦ ⊢app (⊨Π ⊨𝔹 ⊨𝔹) idB ⊢ff ⟧M ⋆ ≡ 0₂
ctrl-app = refl

-- a variable whose type is a genuinely dependent 𝕀, and a Π over it: the
-- erasure carrier is the sum, so the context is NOT collapsed to a point.
depCon : Con (ε ∙)
depCon = ε ▷ ⊨𝕀 ⊢tt ⊨𝔹 ⊨𝔹 ⊨⊥

ctrl-dep : ⟦ depCon ⟧C ≡ Σ ⊤ (λ _ → 𝟚 ⊎ Empty)
ctrl-dep = refl

------------------------------------------------------------------------
-- LAYER 2 — the honest dependency, as a PREDICATE over the fixed carrier.
--
-- This is where `𝕀` stops being erased: the predicate at `⊨𝕀` says the injection
-- tag AGREES with the interpreted condition, i.e. a well-formed inhabitant of
-- `𝕀 t A B` really is an `A` when `t ⇓ tt` and a `B` when `t ⇓ ff`.
--
-- ⚠ THE STRUCTURAL POINT: `⟨_⟩T` recurses on the ⊨-derivation and CALLS Layer 1
-- (`⟦ tb ⟧M`), but Layer 1 never calls `⟨_⟩T`.  The dependency is one-way, so no
-- cycle can form — this is the stratification §4.2¹² wanted, obtained by
-- construction rather than by fighting the termination checker.
------------------------------------------------------------------------

⟨_⟩T : ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A)(γ : ⟦ Δ ⟧C) → ⟦ A ⟧T → Set
⟨ ⊨𝔹                ⟩T γ b       = ⊤
⟨ ⊨⊥                ⟩T γ e       = ⊤
⟨ ⊨𝕀 tb w𝔹 wA wB    ⟩T γ (inl a) = Σ (⟦ tb ⟧M γ ≡ 1₂) (λ _ → ⟨ wA ⟩T γ a)
⟨ ⊨𝕀 tb w𝔹 wA wB    ⟩T γ (inr b) = Σ (⟦ tb ⟧M γ ≡ 0₂) (λ _ → ⟨ wB ⟩T γ b)
⟨ ⊨Π wA wB          ⟩T γ f       = (a : _) → ⟨ wA ⟩T γ a → ⟨ wB ⟩T (γ , a) (f a)

-- environment-wise lifting of the predicate.
data ⟨_⟩C : ∀ {Γ}(Δ : Con Γ) → ⟦ Δ ⟧C → Set where
  ⟨⟩  : ⟨ ε ⟩C ⋆
  _∷_ : ∀ {Γ}{Δ : Con Γ}{A}{wA : Δ ⊨ A}{γ : ⟦ Δ ⟧C}{a : ⟦ A ⟧T}
        → ⟨ Δ ⟩C γ → ⟨ wA ⟩T γ a → ⟨ _▷_ Δ {A} wA ⟩C (γ , a)

------------------------------------------------------------------------
-- WHAT IS LEFT (deliberately NOT attempted here, so the file stays --safe):
--
--   fundamental : (td : Δ ⊢ t ∷ A)(wA : Δ ⊨ A)(γ : ⟦Δ⟧C) → ⟨ Δ ⟩C γ
--               → ⟨ wA ⟩T γ (coe … (⟦ td ⟧M γ))
--
-- Its ⊢vz case needs a weakening lemma and its ⊢app case a substitution lemma
-- FOR ⟨_⟩T.  Those are the honest `wkTI`/`subTI` — but they are now implications
-- between PREDICATES over carriers that are already fixed by Layer 1.  If they
-- turn out to need a measure (§4.2⁷'s type↓/OPE↑ situation), that measure sits on
-- a proof and cannot propagate into any other statement — which is precisely the
-- P1 property §4.2⁸/§4.2⁹ tried and failed to obtain by Acc-plumbing.
------------------------------------------------------------------------
