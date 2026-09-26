{-# OPTIONS --safe #-}
-- SPIKE-LEVITATION S1 — NEUTRAL descriptions, in a CONCRETE calculus.
--
-- Descriptions are TERMS (`dnil`/`dcons`), so a description can be a
-- VARIABLE.  The formers that compute on descriptions — `ielim` (ι),
-- `lkp` (ilookupD), `ihs` (iihs) — are given with their real shapes, and the
-- rule DESIGN under test is:
--
--   ★ a description operator computes only on a CANONICAL description
--     (head `dnil`/`dcons`), exactly as `natrec` computes only on numerals.
--
-- The calculus is ONE module parameterised by the ι rule's side condition
-- `Guard`.  `Levitated` instantiates it with `Canon` and proves the
-- neutral-description cases of `fund`; `Control` instantiates it with `⊤`
-- (ι fires at ANY description) and PROVES the same lemma FALSE.
module tmp.LevS1 where

open import Agda.Builtin.Nat  using ( Nat; zero; suc )
open import Agda.Builtin.Unit using ( ⊤; tt )

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

¬_ : Set → Set
¬ A = A → ⊥

data Fin : Nat → Set where
  fz : {n : Nat} → Fin (suc n)
  fs : {n : Nat} → Fin n → Fin (suc n)

-- ═══ syntax ═══════════════════════════════════════════════════════════════
data Tm (n : Nat) : Set where
  var   : Fin n → Tm n
  lam   : Tm (suc n) → Tm n
  app   : Tm n → Tm n → Tm n
  dnil  : Tm n                         -- descriptions are terms
  dcons : Tm n → Tm n → Tm n
  icon  : Nat → Tm n → Tm n            -- icon k payload
  ielim : Tm n → Tm n → Tm n → Tm n    -- ielim D methods scrutinee
  lkp   : Tm n → Nat → Tm n            -- ilookupD D k
  ihs   : Tm n → Tm n → Tm n → Tm n    -- iihs D methods payload
  mnil  : Tm n                         -- method tuples
  mcons : Tm n → Tm n → Tm n
  sel   : Nat → Tm n → Tm n            -- the k-th method

variable
  m n     : Nat
  k       : Nat
  b       : Tm (suc n)
  a c c' d d' ms ms' t t' u u' p p' e e' : Tm n

ext : (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
ext ρ fz     = fz
ext ρ (fs i) = fs (ρ i)

ren : (Fin m → Fin n) → Tm m → Tm n
ren ρ (var i)       = var (ρ i)
ren ρ (lam b)       = lam (ren (ext ρ) b)
ren ρ (app t u)     = app (ren ρ t) (ren ρ u)
ren ρ dnil          = dnil
ren ρ (dcons c d)   = dcons (ren ρ c) (ren ρ d)
ren ρ (icon k p)    = icon k (ren ρ p)
ren ρ (ielim d e t) = ielim (ren ρ d) (ren ρ e) (ren ρ t)
ren ρ (lkp d k)     = lkp (ren ρ d) k
ren ρ (ihs d e p)   = ihs (ren ρ d) (ren ρ e) (ren ρ p)
ren ρ mnil          = mnil
ren ρ (mcons a e)   = mcons (ren ρ a) (ren ρ e)
ren ρ (sel k e)     = sel k (ren ρ e)

exts : (Fin m → Tm n) → Fin (suc m) → Tm (suc n)
exts σ fz     = var fz
exts σ (fs i) = ren fs (σ i)

sub : (Fin m → Tm n) → Tm m → Tm n
sub σ (var i)       = σ i
sub σ (lam b)       = lam (sub (exts σ) b)
sub σ (app t u)     = app (sub σ t) (sub σ u)
sub σ dnil          = dnil
sub σ (dcons c d)   = dcons (sub σ c) (sub σ d)
sub σ (icon k p)    = icon k (sub σ p)
sub σ (ielim d e t) = ielim (sub σ d) (sub σ e) (sub σ t)
sub σ (lkp d k)     = lkp (sub σ d) k
sub σ (ihs d e p)   = ihs (sub σ d) (sub σ e) (sub σ p)
sub σ mnil          = mnil
sub σ (mcons a e)   = mcons (sub σ a) (sub σ e)
sub σ (sel k e)     = sel k (sub σ e)

sg : Tm n → Fin (suc n) → Tm n
sg u fz     = u
sg u (fs i) = var i

_[_] : Tm (suc n) → Tm n → Tm n
b [ u ] = sub (sg u) b

-- A CANONICAL description: its head is a description constructor.
data Canon {n : Nat} : Tm n → Set where
  c-nil  : Canon dnil
  c-cons : Canon (dcons c d)

-- NEUTRAL terms: a variable under eliminators — INCLUDING the description
-- operators applied to a neutral description (the new SNe forms).
data Ne {n : Nat} : Tm n → Set where
  ne-var   : {i : Fin n} → Ne (var i)
  ne-app   : Ne t → Ne (app t u)
  ne-sel   : Ne e → Ne (sel k e)
  ne-ielim : Ne d → Ne (ielim d e t)   -- ★ elimination over a neutral D
  ne-lkp   : Ne d → Ne (lkp d k)       -- ★ a stuck constructor lookup
  ne-ihs   : Ne d → Ne (ihs d e p)     -- ★ stuck recursive hypotheses

ne-canon : Ne d → Canon d → ⊥
ne-canon (ne-app _)   ()
ne-canon (ne-sel _)   ()
ne-canon (ne-ielim _) ()
ne-canon (ne-lkp _)   ()
ne-canon (ne-ihs _)   ()

-- ═══ the calculus, parameterised by ι's side condition ═══════════════════
module Calc (Guard : {n : Nat} → Tm n → Set) where

  infix 4 _⟶_
  data _⟶_ {n : Nat} : Tm n → Tm n → Set where
    β      : app (lam b) u ⟶ b [ u ]
    -- ι: the method gets the payload and the recursive hypotheses
    ι      : Guard d → ielim d e (icon k p) ⟶ app (app (sel k e) p) (ihs d e p)
    lkp-z  : lkp (dcons c d) zero ⟶ c
    lkp-s  : lkp (dcons c d) (suc k) ⟶ lkp d k
    ihs-c  : Canon d → ihs d e p ⟶ ielim d e p
    sel-z  : sel zero (mcons a e) ⟶ a
    sel-s  : sel (suc k) (mcons a e) ⟶ sel k e
    -- full congruence
    lam-c  : {b b' : Tm (suc n)} → b ⟶ b' → lam b ⟶ lam b'
    appl   : t ⟶ t' → app t u ⟶ app t' u
    appr   : u ⟶ u' → app t u ⟶ app t u'
    dconsl : c ⟶ c' → dcons c d ⟶ dcons c' d
    dconsr : d ⟶ d' → dcons c d ⟶ dcons c d'
    icon-c : p ⟶ p' → icon k p ⟶ icon k p'
    ielim₁ : d ⟶ d' → ielim d e t ⟶ ielim d' e t
    ielim₂ : e ⟶ e' → ielim d e t ⟶ ielim d e' t
    ielim₃ : t ⟶ t' → ielim d e t ⟶ ielim d e t'
    lkp-c  : d ⟶ d' → lkp d k ⟶ lkp d' k
    ihs₁   : d ⟶ d' → ihs d e p ⟶ ihs d' e p
    ihs₂   : e ⟶ e' → ihs d e p ⟶ ihs d e' p
    ihs₃   : p ⟶ p' → ihs d e p ⟶ ihs d e p'
    mconsl : a ⟶ c → mcons a e ⟶ mcons c e
    mconsr : e ⟶ e' → mcons a e ⟶ mcons a e'
    sel-c  : e ⟶ e' → sel k e ⟶ sel k e'

  data SN {n : Nat} (t : Tm n) : Set where
    sn : (∀ {t'} → t ⟶ t' → SN t') → SN t

  sn-step : SN t → t ⟶ t' → SN t'
  sn-step (sn h) s = h s

-- ═══ the LEVITATED design: ι only at a canonical description ═════════════
module Levitated where
  open Calc Canon public

  -- neutrality is preserved by reduction — the fact that FAILS under `Control`
  ne-pres : Ne t → t ⟶ t' → Ne t'
  ne-pres (ne-app ())   β
  ne-pres (ne-app n)    (appl s)   = ne-app (ne-pres n s)
  ne-pres (ne-app n)    (appr _)   = ne-app n
  ne-pres (ne-sel ())   sel-z
  ne-pres (ne-sel ())   sel-s
  ne-pres (ne-sel n)    (sel-c s)  = ne-sel (ne-pres n s)
  ne-pres (ne-ielim n)  (ι g)      = ⊥-elim (ne-canon n g)
  ne-pres (ne-ielim n)  (ielim₁ s) = ne-ielim (ne-pres n s)
  ne-pres (ne-ielim n)  (ielim₂ _) = ne-ielim n
  ne-pres (ne-ielim n)  (ielim₃ _) = ne-ielim n
  ne-pres (ne-lkp ())   lkp-z
  ne-pres (ne-lkp ())   lkp-s
  ne-pres (ne-lkp n)    (lkp-c s)  = ne-lkp (ne-pres n s)
  ne-pres (ne-ihs n)    (ihs-c g)  = ⊥-elim (ne-canon n g)
  ne-pres (ne-ihs n)    (ihs₁ s)   = ne-ihs (ne-pres n s)
  ne-pres (ne-ihs n)    (ihs₂ _)   = ne-ihs n
  ne-pres (ne-ihs n)    (ihs₃ _)   = ne-ihs n

  -- ★ the new SNe forms are SN from SN parts: ONLY congruence steps exist
  sn-ielim : Ne d → SN d → SN e → SN t → SN (ielim d e t)
  sn-ielim nd sd@(sn hd) se@(sn he) st@(sn ht) = sn λ where
    (ι g)      → ⊥-elim (ne-canon nd g)
    (ielim₁ s) → sn-ielim (ne-pres nd s) (hd s) se st
    (ielim₂ s) → sn-ielim nd sd (he s) st
    (ielim₃ s) → sn-ielim nd sd se (ht s)

  sn-ihs : Ne d → SN d → SN e → SN p → SN (ihs d e p)
  sn-ihs nd sd@(sn hd) se@(sn he) sp@(sn hp) = sn λ where
    (ihs-c g) → ⊥-elim (ne-canon nd g)
    (ihs₁ s)  → sn-ihs (ne-pres nd s) (hd s) se sp
    (ihs₂ s)  → sn-ihs nd sd (he s) sp
    (ihs₃ s)  → sn-ihs nd sd se (hp s)

  sn-lkp : Ne d → SN d → SN (lkp d k)
  sn-lkp (ne-app n)   (sn hd) = sn λ { (lkp-c s) → sn-lkp (ne-pres (ne-app n) s) (hd s) }
  sn-lkp (ne-sel n)   (sn hd) = sn λ { (lkp-c s) → sn-lkp (ne-pres (ne-sel n) s) (hd s) }
  sn-lkp (ne-ielim n) (sn hd) = sn λ { (lkp-c s) → sn-lkp (ne-pres (ne-ielim n) s) (hd s) }
  sn-lkp (ne-lkp n)   (sn hd) = sn λ { (lkp-c s) → sn-lkp (ne-pres (ne-lkp n) s) (hd s) }
  sn-lkp (ne-ihs n)   (sn hd) = sn λ { (lkp-c s) → sn-lkp (ne-pres (ne-ihs n) s) (hd s) }
  sn-lkp ne-var       (sn hd) = sn λ { (lkp-c ()) }

  sn-icon : SN p → SN (icon k p)
  sn-icon (sn hp) = sn λ { (icon-c s) → sn-icon (hp s) }

  -- A candidate: what ⊩₀ interprets a type as.  CR3 (neutral SN terms are
  -- members) is the only closure property the neutral cases use.
  record Cand (n : Nat) : Set₁ where
    field
      _∋_ : Tm n → Set
      cr3 : ∀ {t} → Ne t → SN t → _∋_ t
  open Cand

  -- ⊩₀IMuNe / a stuck operator TYPE (`ipayTy D …`, `imethsTy D …` at a
  -- neutral D): the SN candidate.  It IS a candidate.
  snCand : Cand n
  snCand ._∋_       = SN
  snCand .cr3 _ s   = s

  -- ★ fund, `⊢icon` at a neutral D: the payload's type is stuck, so the
  --   payload is known only SN — which is all ⊩₀IMuNe asks.
  fund-icon-ne : SN p → snCand ∋ icon k p
  fund-icon-ne = sn-icon

  -- ★ fund, `⊢ielim` at a neutral D: ANY motive candidate, methods known
  --   only SN (their type `imethsTy D M` is stuck), scrutinee in ⊩₀IMuNe.
  --   The result is NEUTRAL, so it is in the motive — no case on the
  --   scrutinee, no use of the methods.
  fund-ielim-ne : (Mot : Cand n) → Ne d → SN d → SN e → snCand ∋ t →
                  Mot ∋ ielim d e t
  fund-ielim-ne Mot nd sd se st = cr3 Mot (ne-ielim nd) (sn-ielim nd sd se st)

  -- ⚠ CONTROL 2 — the WRONG CANDIDATE: at a neutral D, demand a canonical
  --   payload (`icon k p` with `p` a value).  `⊢icon`'s case would need every
  --   SN payload to be a value; a variable is SN and is not.
  data Val {n : Nat} : Tm n → Set where
    v-lam  : Val (lam b)
    v-icon : Val (icon k p)
    v-dnil : Val (dnil {n})
    v-dcons : Val (dcons c d)
    v-mnil : Val (mnil {n})
    v-mcons : Val (mcons a e)

  wrong-cand-refuted : ¬ (∀ {p : Tm 1} → SN p → Val p)
  wrong-cand-refuted claim with claim {var fz} (sn λ ())
  ... | ()

-- ═══ CONTROL 1: ι at ANY description — the neutral lemma is FALSE ═══════
module Control where
  open Calc (λ _ → ⊤)

  ω : Tm n
  ω = lam (app (var fz) (var fz))

  ω-nf : ¬ (ω {n} ⟶ t)
  ω-nf (lam-c (appl ()))
  ω-nf (lam-c (appr ()))

  no-Ω : ¬ SN (app (app (ω {n}) ω) u)
  no-Ω (sn h) = no-Ω (h (appl β))

  -- d = a VARIABLE (neutral, SN), methods = (ω , ·) (SN — all a stuck
  -- `imethsTy` promises), scrutinee = icon 0 ω (SN).  ι fires, `sel` picks
  -- ω, and the reduct contains Ω.
  refuted : ¬ (∀ {n} {d e t : Tm n} → Ne d → SN d → SN e → SN t →
               SN (ielim d e t))
  refuted claim =
    no-Ω (sn-step (sn-step s (ι tt)) (appl (appl sel-z)))
    where
    s = claim {1} {var fz} {mcons ω mnil} {icon 0 ω} ne-var
          (sn λ ())
          (sn λ { (mconsl x) → ⊥-elim (ω-nf x) ; (mconsr ()) })
          (sn λ { (icon-c x) → ⊥-elim (ω-nf x) })
