{-# OPTIONS --prop #-}
-- SPIKE 8a (ROUTE (a) of §4.2¹⁰) — close `MI ⊢app` with a mutual soundness lemma.
--
-- §4.2¹⁰ (SpikeCIR) got the core to check and terminate with MI type-agnostic, leaving exactly
-- one clause: ⊢app cannot apply two untyped `Val`s.  Route (a) closes it by coercing along a
-- mutual `MI-ty : fst (MI td ρ w) ≡ TI wA ρ w`.
--
-- DESIGN NOTE (why it is shaped like this).  MI-ty's ⊢vz case reads a value out of the
-- environment, so it needs the environment to be WELL-FORMED — an arbitrary `Val` in a slot has
-- no relation to the slot's type.  Two ways to supply that, and the choice is load-bearing:
--
--   ✗ Bake the proof into CI (`_∷ᴱ_[_] : (ρ : CI Δ)(v : Val) → fst v ≡ TI wA ρ → CI (Δ ▷ wA)`).
--     REJECTED: `envO`'s keep clause would then have to produce `fst x ≡ TI wA (envO r δ)` from
--     `fst x ≡ TI (ren⊨ r wA) δ` — i.e. **nat-TI** — resurrecting the exact `envO → nat-TI` edge
--     that §4.2¹⁰ removed.  That would throw away the whole result.
--
--   ✓ Keep CI PLAIN and carry well-formedness SEPARATELY as `CIwf`.  `envO : CI Θc → CI Δc`
--     stays a pure list operation; transporting the wf across it becomes a downstream lemma
--     (`CIwf δ → CIwf (envO r δ)`) which may use nat-TI freely without being in this block.
--
-- `wkTI` is POSTULATED here — bound-free, which it now CAN be.  That is deliberate: this file
-- tests whether {TI, MI, MI-ty} + CIwf is ORDERABLE AT ALL.  If it is not, route (a) is dead and
-- no amount of work on wkTI's proof matters.  If it is, the follow-up question is whether the
-- real wkTI/nat-TI can be added back (Test B).
--
-- ⚠ CONTROL (§4.2⁴): `bad` must be flagged, or this file proves nothing.
module poc.OCP0009.SpikeCIRa where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma    using ( Σ; _,_; fst; snd )
open import Agda.Builtin.Nat      using ( Nat; zero; suc )
open import poc.OCP0009.NbEPDirDTTCh

data Empty : Set where
record ⊤ : Set where
  constructor ⋆
data 𝟚 : Set where 0₂ 1₂ : 𝟚

trans' : ∀ {a}{A : Set a}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' refl q = q
sym'   : ∀ {a}{A : Set a}{x y : A} → x ≡ y → y ≡ x
sym'   refl = refl

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

coe : {A B : Set} → A ≡ B → A → B
coe refl a = a
congÊl : ∀ {c d} → c ≡ d → Êl c ≡ Êl d
congÊl refl = refl

Val : Set
Val = Σ Û Êl

asBool : Val → 𝟚
asBool (𝔹̂ , b) = b
asBool _        = 0₂

force : ∀ {a}{A : Set a}{B : Set} → A → B → B
force _ b = b

------------------------------------------------------------------------
-- CI stays PLAIN (untyped slots) so that envO remains a pure list operation.
------------------------------------------------------------------------
data CI : ∀ {Γ} → Con Γ → Set where
  ⟨⟩   : CI ε
  _∷ᴱ_ : ∀ {Γ}{Δ : Con Γ}{A}{wA : Δ ⊨ A} → CI Δ → Val → CI (Δ ▷ wA)

-- well-formedness of an environment, carried SEPARATELY from CI
data CIwf : ∀ {Γ}{Δ : Con Γ} → CI Δ → Set

TI    : ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A)(ρ : CI Δ) → CIwf ρ → Û
MI    : ∀ {Γ}{Δ : Con Γ}{t A}(td : Δ ⊢ t ∷ A)(ρ : CI Δ) → CIwf ρ → Val
MI-ty : ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A)(td : Δ ⊢ t ∷ A)(ρ : CI Δ)(w : CIwf ρ)
        → fst (MI td ρ w) ≡ TI wA ρ w

data CIwf where
  ⟨⟩w  : CIwf ⟨⟩
  _∷w_ : ∀ {Γ}{Δ : Con Γ}{A}{wA : Δ ⊨ A}{ρ : CI Δ}{v : Val}
         (w : CIwf ρ) → fst v ≡ TI wA ρ w → CIwf (_∷ᴱ_ {wA = wA} ρ v)

-- bound-free, and only POSTULATED — see the header.
postulate
  wkTI : ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){A}(wA₀ : Δc ⊨ A)
         (wA : (Δc ▷ wC) ⊨ renTy vs A)(ρ : CI Δc)(w : CIwf ρ)(v : Val)
         (p : fst v ≡ TI wC ρ w)
         → TI wA (_∷ᴱ_ {wA = wC} ρ v) (w ∷w p) ≡ TI wA₀ ρ w

TI ⊨𝔹               ρ w = 𝔹̂
TI ⊨⊥               ρ w = ⊥̂
TI (⊨𝕀 tb w𝔹 wA wB) ρ w = Ifᵁ (asBool (MI tb ρ w)) (TI wA ρ w) (TI wB ρ w)
TI (⊨Π wA wB)       ρ w = π̂ (TI wA ρ w) (λ x → TI wB (ρ ∷ᴱ (TI wA ρ w , x)) (w ∷w refl))

-- ⊢vz / ⊢vs remain PURE PROJECTIONS — the §4.2¹⁰ win is preserved.
MI (⊢vz wR)       (ρ ∷ᴱ v) (w ∷w p) = v
MI (⊢vs wA wR td) (ρ ∷ᴱ v) (w ∷w p) = MI td ρ w
MI ⊢tt ρ w = 𝔹̂ , 1₂
MI ⊢ff ρ w = 𝔹̂ , 0₂
MI (⊢lam wA td) ρ w =
  π̂ (TI wA ρ w) (λ x → fst (MI td (ρ ∷ᴱ (TI wA ρ w , x)) (w ∷w refl))) ,
  (λ x → snd (MI td (ρ ∷ᴱ (TI wA ρ w , x)) (w ∷w refl)))
-- ⊢app, closed by coercion along MI-ty.  Note the result carrier is computed from the SEMANTIC
-- argument `ex`, not from `subTy (single u) B` — so no subTI appears here.
-- ⚠ `ex`/`ef` are INLINE, not `where`-bound: a where-bound value whose TYPE is a function type
-- becomes an auxiliary definition, and applying it (`ef ex`) counts as a CALL with no descent.
-- The live file carries the same warning ("VALUE bindings stay inline: they call MI/MI-irr/…").
MI (⊢app (⊨Π wA wB) tf tu) ρ w =
  TI wB (ρ ∷ᴱ (TI wA ρ w , coe (congÊl (MI-ty wA tu ρ w)) (snd (MI tu ρ w)))) (w ∷w refl) ,
  coe (congÊl (MI-ty (⊨Π wA wB) tf ρ w)) (snd (MI tf ρ w))
    (coe (congÊl (MI-ty wA tu ρ w)) (snd (MI tu ρ w)))

-- MI-ty: only the ⊢vz case is written out (it is the one that consumes wkTI); the rest are
-- holes with their recursive calls routed through `force` so the checker still sees them.
MI-ty wA' (⊢vz {wA = wA} wR) (ρ ∷ᴱ v) (w ∷w p) =
  trans' p (sym' (wkTI wA wA wA' ρ w v p))
MI-ty wA' (⊢vs wA wR td) (ρ ∷ᴱ v) (w ∷w p) = force (MI-ty wA td ρ w) {!!}
MI-ty wA' ⊢tt ρ w = {!!}
MI-ty wA' ⊢ff ρ w = {!!}
MI-ty wA' (⊢lam wA td) ρ w =
  force (λ x → MI-ty {!!} td (ρ ∷ᴱ (TI wA ρ w , x)) (w ∷w refl)) {!!}
MI-ty wA' (⊢app (⊨Π wA wB) tf tu) ρ w =
  force (MI-ty (⊨Π wA wB) tf ρ w) (force (MI-ty wA tu ρ w) {!!})

------------------------------------------------------------------------
-- envO is STILL a pure list operation — CI stayed plain, so §4.2¹⁰'s win survives route (a).
------------------------------------------------------------------------
envO : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc) → CI Θc → CI Δc
envO done        ⟨⟩       = ⟨⟩
envO (keep r wA) (δ ∷ᴱ x) = envO r δ ∷ᴱ x
envO (skip r wB) (δ ∷ᴱ x) = envO r δ

------------------------------------------------------------------------
-- CONTROL — must be flagged.
------------------------------------------------------------------------
bad : Nat → Nat
bad n = force (bad n) zero
