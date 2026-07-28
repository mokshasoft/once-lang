{-# OPTIONS --prop #-}
-- SPIKE 8 (CI REDESIGN) — can the `MI → wkTI` edge be REMOVED?
--
-- §4.2⁹ established that every measure re-plumbing fails and that ONE edge is the whole problem:
-- `MI`'s ⊢vz/⊢vs need a semantic weakening lemma, because the value was STORED at the small
-- context's type (`Êl (TI wA ρ)`) while `MI` must PRODUCE it at the big context's type
-- (`Êl (TI wA' (ρ ∷ᴱ v))`, wA' a wf of `renTy vs A`).  Kill that mismatch and the naturality
-- layer separates into its own downstream module, which is what §4.2⁵/⁶/⁷ all asked for.
--
-- TWO redesigns are testable.  Both are here.  Neither has been tried before.
--
--   V1  "store the value already at the WEAKENED wf", so ⊢vz is a projection.
--   V2  "make MI TYPE-AGNOSTIC" — MI returns an untyped semantic pair `Σ Û Êl` instead of
--       `Êl (TI wA ρ)`, so its type never mentions TI, ⊢vz/⊢vs become projections, and the
--       type-agreement invariant becomes a DOWNSTREAM lemma (`MI-sound`) that may carry wkTI
--       without dragging MI along.
--
-- V1 IS REFUTED ON PAPER — recorded here so nobody re-derives it.  The slot would need type
-- `Êl (TI wR (ρ ∷ᴱ v))` where `wR : (Δ ▷ wA) ⊨ renTy vs A` — i.e. the constructor's own field
-- type mentions the constructor's own RESULT.  That is not induction-recursion (whose later
-- fields may mention EARLIER fields and the recursive function, never the result being built);
-- it is genuine self-reference.  Storing the weakening EQUATION as a field fails identically:
-- the equation `TI wR (ρ ∷ᴱ v) ≡ TI wA ρ` mentions `ρ ∷ᴱ v` too.  So V1 is not a redesign that
-- exists.  ⇒ V2 is the only live one, and is what this file actually checks.
--
-- WIN CONDITION for V2: the core block below (CI/TI/MI) type-checks, terminates, and does NOT
-- mention wkTI/nat-TI/envO anywhere.  Then naturality moves downstream and subTI is unblocked.
-- LOSS CONDITION: some MI clause cannot be written without the soundness invariant, which drags
-- wkTI back into the block — the edge survives and V2 dies with V1.
module poc.OCP0009.SpikeCIR where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma    using ( Σ; _,_; fst; snd )
open import poc.OCP0009.NbEPDirDTTCh

data Empty : Set where
record ⊤ : Set where
  constructor ⋆
data 𝟚 : Set where 0₂ 1₂ : 𝟚

-- Û gains a UNIT — V2 needs a junk inhabitant, and `Êl ⊥̂ = Empty` has none.
data Û : Set
Êl : Û → Set
data Û where
  ⊥̂  : Û
  ⊤̂  : Û
  𝔹̂  : Û
  π̂  : (a : Û) → (Êl a → Û) → Û
Êl ⊥̂       = Empty
Êl ⊤̂       = ⊤
Êl 𝔹̂       = 𝟚
Êl (π̂ a b) = (x : Êl a) → Êl (b x)

Ifᵁ : 𝟚 → Û → Û → Û
Ifᵁ 1₂ c d = c
Ifᵁ 0₂ c d = d

Val : Set
Val = Σ Û Êl

junk : Val
junk = ⊤̂ , ⋆

-- Reading a boolean out of an untyped value WITHOUT any soundness lemma: match the
-- carrier, default on mismatch.  This is what frees TI from depending on MI's typing.
asBool : Val → 𝟚
asBool (𝔹̂ , b) = b
asBool _        = 0₂

------------------------------------------------------------------------
-- V2 CORE.  MI's type does NOT mention TI.  No wkTI anywhere — that is the point.
------------------------------------------------------------------------
data CI : ∀ {Γ} → Con Γ → Set where
  ⟨⟩   : CI ε
  _∷ᴱ_ : ∀ {Γ}{Δ : Con Γ}{A}{wA : Δ ⊨ A} → CI Δ → Val → CI (Δ ▷ wA)

TI : ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A) → CI Δ → Û
MI : ∀ {Γ}{Δ : Con Γ}{t A}(td : Δ ⊢ t ∷ A) → CI Δ → Val

TI ⊨𝔹               ρ = 𝔹̂
TI ⊨⊥               ρ = ⊥̂
TI (⊨𝕀 tb w𝔹 wA wB) ρ = Ifᵁ (asBool (MI tb ρ)) (TI wA ρ) (TI wB ρ)
TI (⊨Π wA wB)       ρ = π̂ (TI wA ρ) (λ x → TI wB (ρ ∷ᴱ (TI wA ρ , x)))

-- ⊢vz / ⊢vs are now PURE PROJECTIONS.  No coercion, no wkTI.  THIS IS THE EDGE, GONE.
MI (⊢vz wR)       (ρ ∷ᴱ v) = v
MI (⊢vs wA wR td) (ρ ∷ᴱ v) = MI td ρ
MI ⊢tt ρ = 𝔹̂ , 1₂
MI ⊢ff ρ = 𝔹̂ , 0₂
-- ⊢lam: the carrier and the element are built from the SAME recursive call, so they agree
-- definitionally — no soundness lemma needed.  (This is the clause that made V2 look viable.)
MI (⊢lam {B = B} wA td) ρ =
  π̂ (TI wA ρ) (λ x → fst (MI td (ρ ∷ᴱ (TI wA ρ , x)))) ,
  (λ x → snd (MI td (ρ ∷ᴱ (TI wA ρ , x))))
-- ⊢app: THE TEST.  We hold `MI tf ρ : Val` and `MI tu ρ : Val` and must apply one to the other.
-- Matching the function's carrier as `π̂ a b` gives `snd (MI tf ρ) : (x : Êl a) → Êl (b x)`,
-- but the argument is at `Êl (fst (MI tu ρ))` — so this needs `fst (MI tu ρ) ≡ a`, i.e. exactly
-- the soundness invariant, i.e. wkTI back inside the block.  Junk-defaulting instead would make
-- MI DEFINITIONALLY junk on every application (Û has a function field, so no decidable equality
-- can distinguish the good case) — which makes soundness FALSE rather than merely unproven.
MI (⊢app wΠ tf tu) ρ with MI tf ρ
... | (π̂ a b , f) = {! the argument is at Êl (fst (MI tu ρ)), not Êl a !}
... | _            = junk

------------------------------------------------------------------------
-- THE PAYOFF, and the real reason V2 matters.  Because `CI` is now a PLAIN datatype
-- (it stores untyped `Val`s, so its constructor never mentions TI), `envO` is a pure
-- list operation: the `keep` clause just re-stores the value.  In the live file that
-- clause must coerce the stored value along `nat-TI`, which is the `envO → nat-TI`
-- edge that made the §4.2⁶ cycle `MI → wkTI → envO → TI → MI` close.  Here that edge
-- DOES NOT EXIST, and envO/nat-TI/wkTI all sit strictly BELOW the core.
------------------------------------------------------------------------
envO : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc) → CI Θc → CI Δc
envO done       ⟨⟩       = ⟨⟩
envO (keep r wA) (δ ∷ᴱ x) = envO r δ ∷ᴱ x     -- ← no nat-TI coercion.  THE EDGE IS GONE.
envO (skip r wB) (δ ∷ᴱ x) = envO r δ

-- and nat-TI is now statable and provable DOWNSTREAM of a finished core: it mentions only
-- TI and envO, both already defined above, and is not mutual with either.
nat-TI : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)
         (δ : CI Θc) → TI (ren⊨ r wA) δ ≡ TI wA (envO r δ)
nat-TI r ⊨𝔹 δ = refl
nat-TI r ⊨⊥ δ = refl
nat-TI r (⊨𝕀 tb w𝔹 wA wB) δ = {! naturality of MI at the condition + the two branches !}
nat-TI r (⊨Π wA wB)       δ = {! π̂-cong + the codomain under keep !}
