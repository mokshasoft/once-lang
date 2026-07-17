------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 13 — a DIRECTED UNIVERSE (Ty⁺ reflected as a type)
--
-- A Tarski universe over the directed CwF: a type `𝒰 : Ty⁺ Γ` whose TERMS are
-- CODES, together with a decoding `El : Code → Ty⁺ Γ` that eliminates a code
-- into a (directed) TYPE — LARGE ELIMINATION. This reflects `Ty⁺` (types) at
-- the term level: a directed type has a name inside the theory.
--
--   * `⊤⁺` / `⊥⁺` — the directed unit / void (the base types);
--   * `Code`       — the small directed types as a datatype (`1`/`0`/`×`/`+`);
--   * `El`         — decodes a code to a `Ty⁺ Γ`, by RECURSION on the code
--                    (into `⊤⁺`/`⊥⁺`/`×⁺`/`+⁺`) — large elimination;
--   * `𝒰`          — the universe: `fam _ = Code`, a discrete (constant) type;
--   * `⌜_⌝`        — codes AS TERMS (`Code → Tm Γ 𝒰`) — the reflection;
--   * `El∘⌜⌝`      — `El` of a reflected code is the type it names (`refl`).
--
-- Codes are the NON-dependent formers here (`1`/`0`/`×`/`+`); dependent codes
-- (`Σ`/`Π`, whose second field is a code FAMILY) are the natural extension,
-- decoding to `Σ⁺`/`Π⁺`. `𝒰` being discrete is the honest small-universe
-- choice — a genuinely *variant* universe (à la Hofmann–Streicher) is larger.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirUniv where

open import normalizer.Syntax.Types using ( _≡_; refl; ⊤; tt; ⊥ )
open import poc.OCP0009.NbEPDirCwF using ( Ctx; Ty⁺; Tm )
open import poc.OCP0009.NbEPDirTy  using ( _×⁺_; _+⁺_ )

------------------------------------------------------------------------
-- The base types: directed unit and void.
------------------------------------------------------------------------

⊤⁺ : ∀ {Γ} → Ty⁺ Γ
⊤⁺ = record { fam = λ _ → ⊤ ; act = λ _ _ → tt
            ; actid = λ _ → refl ; act⨾ = λ _ _ _ → refl }

⊥⁺ : ∀ {Γ} → Ty⁺ Γ
⊥⁺ = record { fam = λ _ → ⊥ ; act = λ _ a → a
            ; actid = λ _ → refl ; act⨾ = λ _ _ _ → refl }

------------------------------------------------------------------------
-- The codes and their decoding — LARGE ELIMINATION (a code → a type).
------------------------------------------------------------------------

data Code : Set where
  `1 `0 : Code
  _`×_ _`+_ : Code → Code → Code

El : ∀ {Γ} → Code → Ty⁺ Γ
El `1       = ⊤⁺
El `0       = ⊥⁺
El (c `× d) = El c ×⁺ El d
El (c `+ d) = El c +⁺ El d

------------------------------------------------------------------------
-- The universe as a (discrete) type, and codes as its terms.
------------------------------------------------------------------------

𝒰 : ∀ {Γ} → Ty⁺ Γ
𝒰 = record { fam = λ _ → Code ; act = λ _ c → c
           ; actid = λ _ → refl ; act⨾ = λ _ _ _ → refl }

-- A code names a type: it is a (constant, hence natural) term of `𝒰`.
⌜_⌝ : ∀ {Γ} → Code → Tm Γ 𝒰
⌜ c ⌝ = record { tm = λ _ → c ; nat = λ _ → refl }

-- Coherence: a reflected code reads back to itself (so `El` of it is `El c`).
⌜⌝-tm : ∀ {Γ} (c : Code) (x : Ctx.Ob Γ) → Tm.tm (⌜_⌝ {Γ} c) x ≡ c
⌜⌝-tm c x = refl
