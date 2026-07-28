{-# OPTIONS --prop #-}
-- SPIKE 7 (OPTION 1, SCALED) — the gating test for the Acc transform of NbEPDirDTTChMF.
--
-- SpikeAcc (§4.2⁸) put Acc on `nat-TI` ONLY, and failed with the §4.2⁶ cycle.  The handoff's
-- recommendation was that the FULL transform puts Acc on the WHOLE cycle (CI/TI/MI/envO/wkTI/
-- nat-TI), which is what P2 needs.  THAT IS UNTESTED.  This file tests it, before committing to
-- a ~1400-line rewrite.
--
-- DESIGN UNDER TEST.  Each function takes an `Acc` on ITS OWN measure (computed from its own
-- arguments — szT/dsz/szCon, exactly the real file's), and every call passes `h m' proof`
-- from the caller's `acc h`.  A BOUND-FREE wrapper (`TI wA ρ = TIa wA ρ (wfAcc _)`) is what all
-- STATEMENTS mention, so no type carries a bound ⇒ subTI becomes stateable (that is P1).
--
-- TWO QUESTIONS, both answered by this one file:
--
--  Q1 (call graph).  Does Agda's termination checker accept the Acc threaded around the whole
--      MI → wkTI → envO → TI → MI cycle?  If NO, Option 1 is dead and we descope.
--
--  Q2 (the risk the handoff underplays).  The current file gets bound-irrelevance
--      DEFINITIONALLY: bounds are `--prop`, so `TI n wA ρ b1` and `TI n wA ρ b2` are the same
--      term.  Acc CANNOT be Prop (SplitInProp — you may not pattern-match a Prop into Set), so
--      that definitional equality is LOST and every place relying on it needs an `accIrr`
--      transport.  §4.2⁸ costed those as "a one-line accIrr cong ... bounded, mechanical".
--      But `cong (TIa wA ρ) (accIrr …)` is a PARTIAL APPLICATION OF TIa — i.e. a CALL to the
--      function being defined, at an UNCHANGED measure.  If the termination checker counts it,
--      every bridge is itself a non-decreasing recursive call and the transform cannot close.
--      Irrelevance (`.(h : Acc _)`) does not rescue it: you cannot split on an irrelevant arg.
--      The TI-Π clause below exercises exactly this bridge.
--
-- ⚠ SCOPE / HONESTY.  This is a CALL-GRAPH test, not a proof.  The descent inequalities are
--   supplied by `oracle` (postulated).  That is deliberate: it isolates Q1/Q2 from the
--   arithmetic.  The arithmetic is a SEPARATE and also-unsettled question — with per-function
--   measures, cross-function calls need genuine inequalities BETWEEN DIFFERENT measures
--   (e.g. MI's `dsz td + szCon Δ` vs wkTI's `szT wA₀ + szCon Δc`), which the fuel design never
--   needed because a single global `n` bounded each independently.  Hand-check for MI/⊢vs:
--     need  szT wA + szCon Δc  <  suc (dsz td) + szT wB + szCon Δc,  i.e.  szT wA ≤ dsz td + szT wB
--   and `dsz (⊢vz wR) = 1` regardless of how large that variable's type is — so this is NOT
--   obviously true and is Stage B.  Do NOT read a green Q1 as "Option 1 works".
--
-- ⚠ METHOD (§4.2⁴): Agda does not termination-check `where`-bindings the body never uses.
--   All recursive calls are routed through `force` so the body genuinely uses them, and
--   `CONTROL` below is a deliberate non-decreasing self-call that MUST be flagged — if the
--   checker stays silent about CONTROL, this file proves nothing.
module poc.OCP0009.SpikeAcc2 where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma    using ( Σ; _,_; fst; snd )
open import Agda.Builtin.Nat      using ( Nat; zero; suc; _+_ )
open import poc.OCP0009.NbEPDirDTTCh

postulate funext : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

cong' : ∀ {a b}{A : Set a}{B : Set b}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong' f refl = refl
sym' : ∀ {a}{A : Set a}{x y : A} → x ≡ y → y ≡ x
sym' refl = refl

------------------------------------------------------------------------
-- Accessibility.  SET-valued order (Prop would hit SplitInProp).
------------------------------------------------------------------------
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n}   → zero  ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
_<'_ : Nat → Nat → Set
m <' n = suc m ≤ n
≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

data Acc (n : Nat) : Set where
  acc : (∀ m → m <' n → Acc m) → Acc n

wfAcc : ∀ n → Acc n                      -- top clause does NOT match n ⇒ reduces on open terms
wfAcc n = acc (go n)
  where go : ∀ n m → m <' n → Acc m
        go (suc n) zero    _       = acc (λ _ ())
        go (suc n) (suc m) (s≤s p) = acc (λ k q → go n k (≤-trans q p))

accIrr : ∀ {n}(a b : Acc n) → a ≡ b
accIrr (acc p) (acc q) = cong' acc (funext (λ m → funext (λ r → accIrr (p m r) (q m r))))

-- ⚠ THE ORACLE.  Stands in for the real descent arithmetic (Stage B).  Call-graph test only.
postulate oracle : ∀ {m n} → m <' n

------------------------------------------------------------------------
-- Measures — identical to the real file's szT / dsz / szCon.
------------------------------------------------------------------------
szT   : ∀ {Γ}{Δ : Con Γ}{A} → Δ ⊨ A → Nat
dsz   : ∀ {Γ}{Δ : Con Γ}{t A} → Δ ⊢ t ∷ A → Nat
szT ⊨𝔹              = suc zero
szT ⊨⊥              = suc zero
szT (⊨𝕀 tb w𝔹 wA wB) = suc (dsz tb + (szT wA + szT wB))
szT (⊨Π wA wB)      = suc (szT wA + szT wB)
dsz (⊢vz wR)        = suc zero
dsz (⊢vs wA wR td)  = suc (dsz td)
dsz ⊢tt             = suc zero
dsz ⊢ff             = suc zero
dsz (⊢lam wA td)    = suc (dsz td)
dsz (⊢app wΠ tf tu) = suc (dsz tf + dsz tu)

szCon : ∀ {Γ} → Con Γ → Nat
szCon ε        = zero
szCon (Δ ▷ wA) = szT wA + szCon Δ

------------------------------------------------------------------------
-- Semantic universe (IR), as in the real file.
------------------------------------------------------------------------
data Empty : Set where
data 𝟚 : Set where 0₂ 1₂ : 𝟚

data Û : Set
Êl : Û → Set
data Û where
  ⊥̂  : Û
  𝔹̂  : Û
  π̂  : (a : Û) → (Êl a → Û) → Û
Êl ⊥̂       = Empty
Êl 𝔹̂       = 𝟚
Êl (π̂ a b) = (x : Êl a) → Êl (b x)

Ifᵁ : 𝟚 → Û → Û → Û
Ifᵁ 1₂ c d = c
Ifᵁ 0₂ c d = d

coe : {A B : Set} → A ≡ B → A → B
coe refl a = a
congÊl : ∀ {c d} → c ≡ d → Êl c ≡ Êl d
congÊl refl = refl

force : ∀ {a}{A : Set a}{B : Set} → A → B → B
force _ b = b

------------------------------------------------------------------------
-- THE WHOLE CYCLE, Acc-threaded, with BOUND-FREE wrappers.
------------------------------------------------------------------------
-- CI must be an IR DATATYPE, not a function (SpikeWF finding #1): as a function,
-- CI (Δ ▷ wA) calls TI wA at CI's own measure szCon (Δ ▷ wA) — no decrease.
data CI : ∀ {Γ} → Con Γ → Set

-- wrappers (what every STATEMENT mentions — NO bounds anywhere)
TI    : ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A) → CI Δ → Û

-- constructors must land before any signature that mentions `_∷ᴱ_`
data CI where
  ⟨⟩   : CI ε
  _∷ᴱ_ : ∀ {Γ}{Δ : Con Γ}{A}{wA : Δ ⊨ A}(ρ : CI Δ) → Êl (TI wA ρ) → CI (Δ ▷ wA)

MI    : ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A)(td : Δ ⊢ t ∷ A)(ρ : CI Δ) → Êl (TI wA ρ)
envO  : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc) → CI Θc → CI Δc
nat-TI : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)
         (wA' : Θc ⊨ renTy ⌜ o ⌝ A)(δ : CI Θc) → TI wA' δ ≡ TI wA (envO r δ)
wkTI  : ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){A}(wA₀ : Δc ⊨ A)
        (wA : (Δc ▷ wC) ⊨ renTy vs A)(ρ : CI Δc)(v : Êl (TI wC ρ))
        → TI wA (ρ ∷ᴱ v) ≡ TI wA₀ ρ

-- aux forms — the measure lives HERE and nowhere else
TIa    : ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A)(ρ : CI Δ) → Acc (szT wA + szCon Δ) → Û
MIa    : ∀ {Γ}{Δ : Con Γ}{t A}(wA : Δ ⊨ A)(td : Δ ⊢ t ∷ A)(ρ : CI Δ)
         → Acc (dsz td + szCon Δ) → Êl (TI wA ρ)
envOa  : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc)(δ : CI Θc)
         → Acc (szCon Θc) → CI Δc
nat-TIa : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A)
          (wA' : Θc ⊨ renTy ⌜ o ⌝ A)(δ : CI Θc) → Acc (szT wA + szCon Θc)
          → TI wA' δ ≡ TI wA (envO r δ)
wkTIa  : ∀ {Γ}{Δc : Con Γ}{C}(wC : Δc ⊨ C){A}(wA₀ : Δc ⊨ A)
         (wA : (Δc ▷ wC) ⊨ renTy vs A)(ρ : CI Δc)(v : Êl (TI wC ρ))
         → Acc (szT wA₀ + szCon Δc) → TI wA (ρ ∷ᴱ v) ≡ TI wA₀ ρ

-- Δ ⊨ 𝔹 has ⊨𝔹 as its only constructor, but must be MUTUAL with TI (SpikeWF finding #2).
TI-𝔹 : ∀ {Γ}{Δ : Con Γ}(w : Δ ⊨ 𝔹)(ρ : CI Δ) → TI w ρ ≡ 𝔹̂

-- the bound-free wrappers
TI     wA ρ            = TIa    wA ρ            (wfAcc _)
MI     wA td ρ         = MIa    wA td ρ         (wfAcc _)
envO   r δ             = envOa  r δ             (wfAcc _)
nat-TI r wA wA' δ      = nat-TIa r wA wA' δ     (wfAcc _)
wkTI   wC wA₀ wA ρ v   = wkTIa  wC wA₀ wA ρ v   (wfAcc _)

-- ⚠ Q2 LIVES HERE.  `x` is bound at `Êl (TIa wA ρ h')` but `_∷ᴱ_` demands `Êl (TI wA ρ)`.
-- With --prop bounds that mismatch does not exist (definitional irrelevance).  With Acc it
-- must be bridged by accIrr — and `cong' (TIa wA ρ)` is a PARTIAL APPLICATION OF TIa, i.e. a
-- call to a function of this very mutual block at an UNCHANGED measure.
bridge : ∀ {Γ}{Δ : Con Γ}{A}(wA : Δ ⊨ A)(ρ : CI Δ)(h : Acc (szT wA + szCon Δ))
         → TIa wA ρ h ≡ TI wA ρ
bridge wA ρ h = cong' (TIa wA ρ) (accIrr h (wfAcc _))

-- ...and the SAME bridge is needed for envO, because nat-TI's CONCLUSION mentions the
-- WRAPPER `envO r δ` while envOa's own recursive call produces `envOa r δ (g _ oracle)`.
-- Under --prop those are the same term; under Acc they are only propositionally equal.
envO-bridge : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc)(δ : CI Θc)
              (h : Acc (szCon Θc)) → envOa r δ h ≡ envO r δ
envO-bridge r δ h = cong' (envOa r δ) (accIrr h (wfAcc _))

TIa ⊨𝔹              ρ h       = 𝔹̂
TIa ⊨⊥              ρ h       = ⊥̂
TIa (⊨𝕀 tb w𝔹 wA wB) ρ (acc g) =
  Ifᵁ (coe (congÊl (TI-𝔹 w𝔹 ρ)) (MI w𝔹 tb ρ))
      (TIa wA ρ (g _ oracle)) (TIa wB ρ (g _ oracle))
TIa (⊨Π wA wB)      ρ (acc g) =
  π̂ (TIa wA ρ (g _ oracle))
    (λ x → TIa wB (ρ ∷ᴱ coe (congÊl (bridge wA ρ (g _ oracle))) x) (g _ oracle))

TI-𝔹 ⊨𝔹 ρ = refl

MIa wA' (⊢vz {wA = wA} wR)       (ρ ∷ᴱ v) (acc g) =
  coe (congÊl (sym' (wkTIa wA wA wA' ρ v (g _ oracle)))) v
MIa wA' (⊢vs {wB = wB} wA wR td) (ρ ∷ᴱ v) (acc g) =
  coe (congÊl (sym' (wkTIa wB wA wA' ρ v (g _ oracle)))) (MIa wA td ρ (g _ oracle))
MIa ⊨𝔹  ⊢tt ρ h = 1₂
MIa ⊨𝔹  ⊢ff ρ h = 0₂
-- ⊢lam: MATCH ⊨-unique, do not transport (SpikeWF finding #3).
MIa (⊨Π wA wB) (⊢lam wA' td) ρ (acc g) with ⊨-unique wA' wA
... | refl = λ x → force (MIa wB td (ρ ∷ᴱ {!!}) (g _ oracle)) {!!}
MIa wS (⊢app (⊨Π wA' wB) tf tu) ρ (acc g) =
  force (MIa (⊨Π wA' wB) tf ρ (g _ oracle)) (force (MIa wA' tu ρ (g _ oracle)) {!!})

envOa done        ⟨⟩       h       = ⟨⟩
envOa (keep r wA) (δ ∷ᴱ x) (acc g) =
  envOa r δ (g _ oracle) ∷ᴱ
    coe (congÊl (cong' (TI wA) (sym' (envO-bridge r δ (g _ oracle)))))
        (coe (congÊl (nat-TIa r wA (ren⊨ r wA) δ (g _ oracle))) x)
envOa (skip r wB) (δ ∷ᴱ x) (acc g) = envOa r δ (g _ oracle)

nat-TIa r ⊨𝔹 wA'               δ h       = {!!}
nat-TIa r ⊨⊥ wA'               δ h       = {!!}
nat-TIa r (⊨𝕀 tb w𝔹 wA wB) wA' δ (acc g) =
  force (nat-TIa r wA {!!} δ (g _ oracle)) (force (nat-TIa r wB {!!} δ (g _ oracle)) {!!})
nat-TIa r (⊨Π wA wB) wA'       δ (acc g) =
  force (nat-TIa r wA {!!} δ (g _ oracle)) {!!}

-- the real MI → wkTI → nat-TI edge (this is what SpikeAcc could not close)
wkTIa wC wA₀ wA ρ v (acc g) =
  force (nat-TIa (wk⊑ _ wC) wA₀ {!!} (ρ ∷ᴱ v) (g _ oracle)) {!!}

------------------------------------------------------------------------
-- CONTROL (§4.2⁴).  A deliberate NON-decreasing self-call.  The termination checker
-- MUST flag `bad`.  If it does not, this file's green result is meaningless — the
-- checker is not looking where we think it is.
------------------------------------------------------------------------
bad : Nat → Nat
bad n = force (bad n) zero
