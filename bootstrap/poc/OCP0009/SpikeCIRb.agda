{-# OPTIONS --prop #-}
-- SPIKE 8b (TEST B of §4.2¹¹) — put the REAL wkTI/nat-TI back.
--
-- §4.2¹¹ verified {TI, MI, MI-ty} + CIwf orders with `wkTI` POSTULATED.  wkTI is consumed by
-- MI-ty's ⊢vz case, so it is genuinely mutual with that block; deriving it needs nat-TI, which
-- needs envO-wf (transport of well-formedness across envO), whose keep case needs nat-TI back.
-- So Test B asks: does {TI, MI, MI-ty, envO-wf, nat-TI, nat-MI, wkTI} order?
--
-- WHAT IS DIFFERENT FROM §4.2⁶ (where this exact shape failed).  `CI` is PLAIN and `envO` is a
-- PURE list operation, so `envO` itself carries no proof obligation and is not in the cycle.
-- The cycle now runs only through the PROOFS.  Even if it needs a numeric measure (§4.2⁷ argued
-- one is necessary for the (type ↓, OPE ↑) situation), that measure would sit on PROOFS —
-- equations between already-defined terms — not on `TI`'s type.  That is the whole P1 win: a
-- bound on a proof does not propagate into every statement the way a bound on `TI` did.
--
-- ⚠ CONTROL: `bad` must be flagged.
module poc.OCP0009.SpikeCIRb where

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
-- CI PLAIN; envO a PURE list operation (defined up front, outside every cycle).
------------------------------------------------------------------------
data CI : ∀ {Γ} → Con Γ → Set where
  ⟨⟩   : CI ε
  _∷ᴱ_ : ∀ {Γ}{Δ : Con Γ}{A}{wA : Δ ⊨ A} → CI Δ → Val → CI (Δ ▷ wA)

envO : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc) → CI Θc → CI Δc
envO done        ⟨⟩       = ⟨⟩
envO (keep r wA) (δ ∷ᴱ x) = envO r δ ∷ᴱ x
envO (skip r wB) (δ ∷ᴱ x) = envO r δ

------------------------------------------------------------------------
-- THE FULL BLOCK.
------------------------------------------------------------------------
data CIwf : ∀ {Γ}{Δ : Con Γ} → CI Δ → Set

TI    : ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A)(ρ : CI Δ) → CIwf ρ → Û
MI    : ∀ {Γ}{Δ : Con Γ}{t A}(td : Δ ⊢ t ∷ A)(ρ : CI Δ) → CIwf ρ → Val
MI-ty : ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A)(td : Δ ⊢ t ∷ A)(ρ : CI Δ)(w : CIwf ρ)
        → fst (MI td ρ w) ≡ TI wA ρ w

envO-wf : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc)(δ : CI Θc)
          → CIwf δ → CIwf (envO r δ)
nat-TI  : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)
          (δ : CI Θc)(w : CIwf δ)
          → TI (ren⊨ r wA) δ w ≡ TI wA (envO r δ) (envO-wf r δ w)
nat-MI  : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){t A}(td : Δc ⊢ t ∷ A)
          (δ : CI Θc)(w : CIwf δ)
          → MI (ren⊢ r td) δ w ≡ MI td (envO r δ) (envO-wf r δ w)

data CIwf where
  ⟨⟩w  : CIwf ⟨⟩
  _∷w_ : ∀ {Γ}{Δ : Con Γ}{A}{wA : Δ ⊨ A}{ρ : CI Δ}{v : Val}
         (w : CIwf ρ) → fst v ≡ TI wA ρ w → CIwf (_∷ᴱ_ {wA = wA} ρ v)

-- wkTI is now DERIVED, not postulated — this is the whole point of Test B.
wkTI : ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){A}(wA₀ : Δc ⊨ A)
       (wA : (Δc ▷ wC) ⊨ renTy vs A)(ρ : CI Δc)(w : CIwf ρ)(v : Val)
       (p : fst v ≡ TI wC ρ w)
       → TI wA (_∷ᴱ_ {wA = wC} ρ v) (w ∷w p) ≡ TI wA₀ ρ w

TI ⊨𝔹               ρ w = 𝔹̂
TI ⊨⊥               ρ w = ⊥̂
TI (⊨𝕀 tb w𝔹 wA wB) ρ w = Ifᵁ (asBool (MI tb ρ w)) (TI wA ρ w) (TI wB ρ w)
TI (⊨Π wA wB)       ρ w = π̂ (TI wA ρ w) (λ x → TI wB (ρ ∷ᴱ (TI wA ρ w , x)) (w ∷w refl))

MI (⊢vz wR)       (ρ ∷ᴱ v) (w ∷w p) = v
MI (⊢vs wA wR td) (ρ ∷ᴱ v) (w ∷w p) = MI td ρ w
MI ⊢tt ρ w = 𝔹̂ , 1₂
MI ⊢ff ρ w = 𝔹̂ , 0₂
MI (⊢lam wA td) ρ w =
  π̂ (TI wA ρ w) (λ x → fst (MI td (ρ ∷ᴱ (TI wA ρ w , x)) (w ∷w refl))) ,
  (λ x → snd (MI td (ρ ∷ᴱ (TI wA ρ w , x)) (w ∷w refl)))
-- ⚠ ex/ef INLINE (see §4.2¹¹ trap 1)
MI (⊢app (⊨Π wA wB) tf tu) ρ w =
  TI wB (ρ ∷ᴱ (TI wA ρ w , coe (congÊl (MI-ty wA tu ρ w)) (snd (MI tu ρ w)))) (w ∷w refl) ,
  coe (congÊl (MI-ty (⊨Π wA wB) tf ρ w)) (snd (MI tf ρ w))
    (coe (congÊl (MI-ty wA tu ρ w)) (snd (MI tu ρ w)))

MI-ty wA' (⊢vz {wA = wC} wR) (ρ ∷ᴱ v) (w ∷w p) =
  trans' p (sym' (wkTI wC wC wA' ρ w v p))
MI-ty wA' (⊢vs wA wR td) (ρ ∷ᴱ v) (w ∷w p) = force (MI-ty wA td ρ w) {!!}
MI-ty wA' ⊢tt ρ w = {!!}
MI-ty wA' ⊢ff ρ w = {!!}
MI-ty wA' (⊢lam wA td) ρ w =
  force (λ x → MI-ty {!!} td (ρ ∷ᴱ (TI wA ρ w , x)) (w ∷w refl)) {!!}
MI-ty wA' (⊢app (⊨Π wA wB) tf tu) ρ w =
  force (MI-ty (⊨Π wA wB) tf ρ w) (force (MI-ty wA tu ρ w) {!!})

-- envO-wf's keep case is where nat-TI is consumed: it must turn
--   p : fst x ≡ TI (ren⊨ r wA) δ w      into      fst x ≡ TI wA (envO r δ) (envO-wf r δ w)
envO-wf done        ⟨⟩       ⟨⟩w       = ⟨⟩w
envO-wf (keep r wA) (δ ∷ᴱ x) (w ∷w p) = envO-wf r δ w ∷w trans' p (nat-TI r wA δ w)
envO-wf (skip r wB) (δ ∷ᴱ x) (w ∷w p) = envO-wf r δ w

nat-TI r ⊨𝔹 δ w = refl
nat-TI r ⊨⊥ δ w = refl
nat-TI r (⊨𝕀 tb w𝔹 wA wB) δ w =
  force (nat-MI r tb δ w) (force (nat-TI r wA δ w) (force (nat-TI r wB δ w) {!!}))
nat-TI r (⊨Π wA wB) δ w =
  force (nat-TI r wA δ w) (force (λ x → nat-TI (keep r wA) wB (δ ∷ᴱ x) {!!}) {!!})

-- ⊢vz/⊢vs need the keep/skip OPE analysis (the real file's nat-var-vz/nat-var-vs, both already
-- PROVEN there).  Not what Test B is about — holed.  nat-MI's recursion is still exercised by
-- the ⊢lam and ⊢app clauses below.
nat-MI r (⊢vz wR)       δ w = {!!}
nat-MI r (⊢vs wA wR td) δ w = {!!}
nat-MI r ⊢tt δ w = {!!}
nat-MI r ⊢ff δ w = {!!}
nat-MI r (⊢lam wA td) δ w = force (λ x → nat-MI (keep r wA) td (δ ∷ᴱ x) {!!}) {!!}
nat-MI r (⊢app wΠ tf tu) δ w =
  force (nat-MI r tf δ w) (force (nat-MI r tu δ w) {!!})

-- wkTI at wk⊑ = skip (id⊑ Δc) wC.  envO (wk⊑ Δc wC) (ρ ∷ᴱ v) = envO (id⊑ Δc) ρ, so this also
-- wants an `envO-id` coherence; hole it here — the question under test is the CALL GRAPH.
wkTI wC wA₀ wA ρ w v p = force (nat-TI (wk⊑ _ wC) wA₀ (ρ ∷ᴱ v) (w ∷w p)) {!!}

------------------------------------------------------------------------
-- CONTROL
------------------------------------------------------------------------
bad : Nat → Nat
bad n = force (bad n) zero
