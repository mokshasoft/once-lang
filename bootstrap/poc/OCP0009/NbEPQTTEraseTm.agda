------------------------------------------------------------------------
-- OCP-0009 · QTT — the ERASING TERM elaboration (the documented "Next")
--
-- `NbEPQTTJ` gave the FULL elaboration `⟦_⟧` (keeps every argument) and the
-- erased TYPE elaboration `⌊_⌋ᵗ` (`⌊A ⇒[𝟘] B⌋ = ⌊B⌋`). This module gives the
-- missing piece: the erasing TERM elaboration `⌊_⌋`, which drops `𝟘`-graded
-- arguments and `𝟘`-bound variables from the runtime term.
--
-- THE TRICK — the promised "`𝟘`-usage strengthening lemma" is DEFINITIONAL:
-- index the runtime context by the usage vector, dropping the `𝟘` slots
-- (`⌊ Γ , A ∣ ρ ∷ 𝟘 ⌋ᶜ = ⌊ Γ ∣ ρ ⌋ᶜ`). Then
--   * a `𝟘`-bound `lam` elaborates its body IN THE SAME runtime context —
--     no strengthening needed, the slot was never there;
--   * a `𝟘`-graded `app` is the function alone (`𝟘 ·ᵘ ρa` contributes no
--     slots, so the context projection is just a walk);
--   * `var (vs x)` over an erased slot is `var x` — erased slots are
--     invisible to variable lookup.
-- What remains is bookkeeping: usage-vector SPLITTING projections for `app`/
-- `pair` (`prjˡ`/`prjʳ` : the `ρ +ᵘ σ` context projects to each summand's)
-- and SCALING projections (`prj¹`/`prjω`), all small vector recursions over
-- the `Mult` semiring's definitional equations.
--
-- Headline examples:
--   * `⌊ K ⌋ ≡ curry snd ≡ ⌊ idₗ ⌋` — the constant function (erased 2nd
--     argument) and the linear identity erase to the SAME one-argument
--     runtime term, while their FULL elaborations differ.
--   * The SEMANTIC check (this is why the full-fragment NbE `NbEPF` was
--     needed): applying full `K` to a kept argument `x` and an ERASED
--     argument `y` — with `x`, `y` genuine OPEN context variables, i.e.
--     neutrals — is decided EQUAL to applying erased `K` to `x` alone:
--     `nf t-full ≡ nf t-erased`, by `refl`. Erased-argument irrelevance on
--     open terms, decided by normalization.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPQTTEraseTm where

open import normalizer.Syntax.Types
  using ( Ty; Unit; _*_; _⇒_; _≡_; refl )
open import normalizer.Syntax.CCC as C using ()
open import poc.OCP0009.NbEPQTT
  using ( Mult; 𝟘; 𝟙; ω )
open import poc.OCP0009.NbEPQTTJ
  using ( Tyq; ι; _×q_; _⇒[_]_
        ; Con; ∅; _,_; Use; []; _∷_; 0ᵘ; _+ᵘ_; _·ᵘ_
        ; _∋_; vz; vs; useVar
        ; _⊢[_]_; var; lam; app; pair
        ; ⌊_⌋ᵗ; ιT; idₗ; K; ⟦_⟧ )
open import poc.OCP0009.NbEPF as F using ()

------------------------------------------------------------------------
-- The RUNTIME context: usage-masked — `𝟘` slots are dropped.
------------------------------------------------------------------------

⌊_∣_⌋ᶜ : (Γ : Con) → Use Γ → Ty
⌊ ∅     ∣ []    ⌋ᶜ = Unit
⌊ Γ , A ∣ ρ ∷ 𝟘 ⌋ᶜ = ⌊ Γ ∣ ρ ⌋ᶜ
⌊ Γ , A ∣ ρ ∷ 𝟙 ⌋ᶜ = ⌊ Γ ∣ ρ ⌋ᶜ * ⌊ A ⌋ᵗ
⌊ Γ , A ∣ ρ ∷ ω ⌋ᶜ = ⌊ Γ ∣ ρ ⌋ᶜ * ⌊ A ⌋ᵗ

------------------------------------------------------------------------
-- Context projections: splitting a sum of usages, and un-scaling.
------------------------------------------------------------------------

prjˡ : ∀ {Γ} (ρ σ : Use Γ) → C.Term ⌊ Γ ∣ ρ +ᵘ σ ⌋ᶜ ⌊ Γ ∣ ρ ⌋ᶜ
prjˡ []      []      = C.id
prjˡ (ρ ∷ 𝟘) (σ ∷ 𝟘) = prjˡ ρ σ
prjˡ (ρ ∷ 𝟘) (σ ∷ 𝟙) = prjˡ ρ σ C.∘ C.fst
prjˡ (ρ ∷ 𝟘) (σ ∷ ω) = prjˡ ρ σ C.∘ C.fst
prjˡ (ρ ∷ 𝟙) (σ ∷ 𝟘) = C.⟨ prjˡ ρ σ C.∘ C.fst , C.snd ⟩
prjˡ (ρ ∷ 𝟙) (σ ∷ 𝟙) = C.⟨ prjˡ ρ σ C.∘ C.fst , C.snd ⟩
prjˡ (ρ ∷ 𝟙) (σ ∷ ω) = C.⟨ prjˡ ρ σ C.∘ C.fst , C.snd ⟩
prjˡ (ρ ∷ ω) (σ ∷ n) = C.⟨ prjˡ ρ σ C.∘ C.fst , C.snd ⟩

prjʳ : ∀ {Γ} (ρ σ : Use Γ) → C.Term ⌊ Γ ∣ ρ +ᵘ σ ⌋ᶜ ⌊ Γ ∣ σ ⌋ᶜ
prjʳ []      []      = C.id
prjʳ (ρ ∷ 𝟘) (σ ∷ 𝟘) = prjʳ ρ σ
prjʳ (ρ ∷ 𝟘) (σ ∷ 𝟙) = C.⟨ prjʳ ρ σ C.∘ C.fst , C.snd ⟩
prjʳ (ρ ∷ 𝟘) (σ ∷ ω) = C.⟨ prjʳ ρ σ C.∘ C.fst , C.snd ⟩
prjʳ (ρ ∷ 𝟙) (σ ∷ 𝟘) = prjʳ ρ σ C.∘ C.fst
prjʳ (ρ ∷ 𝟙) (σ ∷ 𝟙) = C.⟨ prjʳ ρ σ C.∘ C.fst , C.snd ⟩
prjʳ (ρ ∷ 𝟙) (σ ∷ ω) = C.⟨ prjʳ ρ σ C.∘ C.fst , C.snd ⟩
prjʳ (ρ ∷ ω) (σ ∷ 𝟘) = prjʳ ρ σ C.∘ C.fst
prjʳ (ρ ∷ ω) (σ ∷ 𝟙) = C.⟨ prjʳ ρ σ C.∘ C.fst , C.snd ⟩
prjʳ (ρ ∷ ω) (σ ∷ ω) = C.⟨ prjʳ ρ σ C.∘ C.fst , C.snd ⟩

-- Un-scaling: `𝟙 ·ᵘ ρ` and `ω ·ᵘ ρ` keep exactly `ρ`'s slots.
prj¹ : ∀ {Γ} (ρ : Use Γ) → C.Term ⌊ Γ ∣ 𝟙 ·ᵘ ρ ⌋ᶜ ⌊ Γ ∣ ρ ⌋ᶜ
prj¹ []      = C.id
prj¹ (ρ ∷ 𝟘) = prj¹ ρ
prj¹ (ρ ∷ 𝟙) = C.⟨ prj¹ ρ C.∘ C.fst , C.snd ⟩
prj¹ (ρ ∷ ω) = C.⟨ prj¹ ρ C.∘ C.fst , C.snd ⟩

prjω : ∀ {Γ} (ρ : Use Γ) → C.Term ⌊ Γ ∣ ω ·ᵘ ρ ⌋ᶜ ⌊ Γ ∣ ρ ⌋ᶜ
prjω []      = C.id
prjω (ρ ∷ 𝟘) = prjω ρ
prjω (ρ ∷ 𝟙) = C.⟨ prjω ρ C.∘ C.fst , C.snd ⟩
prjω (ρ ∷ ω) = C.⟨ prjω ρ C.∘ C.fst , C.snd ⟩

------------------------------------------------------------------------
-- The erasing TERM elaboration.
------------------------------------------------------------------------

-- A variable's own slot is `𝟙` (kept, rightmost of its masked context);
-- every erased slot above it is invisible.
⌊var_⌋ : ∀ {Γ A} (x : Γ ∋ A) → C.Term ⌊ Γ ∣ useVar x ⌋ᶜ ⌊ A ⌋ᵗ
⌊var vz ⌋   = C.snd
⌊var vs x ⌋ = ⌊var x ⌋

⌊_⌋ : ∀ {Γ ρ A} → Γ ⊢[ ρ ] A → C.Term ⌊ Γ ∣ ρ ⌋ᶜ ⌊ A ⌋ᵗ
⌊ var x ⌋           = ⌊var x ⌋
⌊ lam {π = 𝟘} t ⌋   = ⌊ t ⌋                 -- erased binder: body already
                                            -- lives in the smaller context
⌊ lam {π = 𝟙} t ⌋   = C.curry ⌊ t ⌋
⌊ lam {π = ω} t ⌋   = C.curry ⌊ t ⌋
⌊ app {π = 𝟘} {ρf = ρf} {ρa = ρa} f a ⌋ =   -- erased argument: DROPPED
  ⌊ f ⌋ C.∘ prjˡ ρf (𝟘 ·ᵘ ρa)
⌊ app {π = 𝟙} {ρf = ρf} {ρa = ρa} f a ⌋ =
  C.apply C.∘ C.⟨ ⌊ f ⌋ C.∘ prjˡ ρf (𝟙 ·ᵘ ρa)
                , (⌊ a ⌋ C.∘ prj¹ ρa) C.∘ prjʳ ρf (𝟙 ·ᵘ ρa) ⟩
⌊ app {π = ω} {ρf = ρf} {ρa = ρa} f a ⌋ =
  C.apply C.∘ C.⟨ ⌊ f ⌋ C.∘ prjˡ ρf (ω ·ᵘ ρa)
                , (⌊ a ⌋ C.∘ prjω ρa) C.∘ prjʳ ρf (ω ·ᵘ ρa) ⟩
⌊ pair {ρa = ρa} {ρb = ρb} a b ⌋ =
  C.⟨ ⌊ a ⌋ C.∘ prjˡ ρa ρb , ⌊ b ⌋ C.∘ prjʳ ρa ρb ⟩

------------------------------------------------------------------------
-- Elaboration examples — computed by `refl`.
------------------------------------------------------------------------

-- The linear identity: erasure changes nothing (nothing is erased).
_ : ⌊ idₗ ⌋ ≡ C.curry C.snd
_ = refl

-- The constant function `K : ι ⇒[𝟙] (ι ⇒[𝟘] ι)`: the `𝟘`-bound second
-- argument VANISHES from the runtime term — a one-argument function.
_ : ⌊ K ⌋ ≡ C.curry C.snd
_ = refl

-- ... which makes erased-K and the linear identity the SAME runtime term,
-- while their full elaborations differ (two-argument vs one-argument).
_ : ⌊ K ⌋ ≡ ⌊ idₗ ⌋
_ = refl

_ : ⟦ K ⟧ ≡ C.curry (C.curry (C.snd C.∘ C.fst))
_ = refl

------------------------------------------------------------------------
-- THE SEMANTIC CHECK (needs the full-fragment NbE `NbEPF`): applying the
-- FULL `K` to a kept argument `x` and an erased argument `y` — both genuine
-- OPEN context variables (neutrals) — equals applying the ERASED `K` to `x`
-- alone. Decided by `nf`, by `refl`: the erased argument is irrelevant on
-- open terms, not just on closed instances.
------------------------------------------------------------------------

-- Full K and erased K, as full-fragment terms (`⌊K⌋ = curry snd` above).
KF : F.Tm Unit (ιT ⇒ (ιT ⇒ ιT))
KF = F.curryT (F.curryT (F.sndT F.⊙ F.fstT))

KE : F.Tm Unit (ιT ⇒ ιT)
KE = F.curryT F.sndT

-- Over the open context `ιT * ιT`: `x = fst`, `y = snd` (both neutral).
t-full : F.Tm (ιT * ιT) ιT
t-full = F.appT F.⊙ F.pair (F.appT F.⊙ F.pair (KF F.⊙ F.termT) F.fstT) F.sndT

t-erased : F.Tm (ιT * ιT) ιT
t-erased = F.appT F.⊙ F.pair (KE F.⊙ F.termT) F.fstT

_ : F.nf t-full ≡ F.nf t-erased
_ = refl
