-- SPIKE (untracked): a kernel-shaped fragment over `tmp.GenSyn` (SPIKE-GENERIC-SYNTAX S2).
-- Two sorts (terms with variables, types without), binders of depth 1 and 2,
-- pattern synonyms so the syntax reads as the hand-written one, and the
-- definitional equalities the metatheory relies on, by `refl`.

{-# OPTIONS --safe #-}
module tmp.GenSynFrag where
open import DirectedHoTT.Prelude using ( _≡_; refl )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import Agda.Builtin.Nat using ( zero; suc )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; Var; vz; vs )
open import tmp.GenSyn

data Srt : Set where tm ty : Srt

data KCon : Srt → Set where
  -- terms
  `lam `app `pair `natrec `nzero `nsuc `ref : KCon tm
  `⌜Π⌝ : KCon tm
  -- types
  `Π `Σ `U `El `Nat : KCon ty

kfields : ∀ {s} → KCon s → List (Field Srt)
kfields `lam    = rec tm 1 ∷ []
kfields `app    = rec tm 0 ∷ rec tm 0 ∷ []
kfields `pair   = rec tm 0 ∷ rec tm 0 ∷ []
kfields `natrec = rec tm 0 ∷ rec tm 2 ∷ rec tm 0 ∷ []      -- z, s under (n, ih), scrutinee
kfields `nzero  = []
kfields `nsuc   = rec tm 0 ∷ []
kfields `ref    = nat ∷ []
kfields `⌜Π⌝    = rec tm 0 ∷ rec tm 1 ∷ []
kfields `Π      = rec ty 0 ∷ rec ty 1 ∷ []
kfields `Σ      = rec ty 0 ∷ rec ty 1 ∷ []
kfields `U      = []
kfields `El     = rec tm 0 ∷ []
kfields `Nat    = []

K : Sig
K = record { Sort = Srt ; vsort = tm ; Con = KCon ; fields = kfields }

RTm RTy : Cx → Set
RTm = Tm K tm
RTy = Tm K ty

-- the hand-written look
pattern lam t        = con `lam (t ∷ʳ [])
pattern app t u      = con `app (t ∷ʳ u ∷ʳ [])
pattern natrec z s n = con `natrec (z ∷ʳ s ∷ʳ n ∷ʳ [])
pattern ref d        = con `ref (d ∷ⁿ [])
pattern Π A B        = con `Π (A ∷ʳ B ∷ʳ [])
pattern El c         = con `El (c ∷ʳ [])
pattern U            = con `U []

open Trav K

-- ★ the equalities the metatheory needs DEFINITIONALLY
Π-stable : ∀ {Γ Δ} (σ : Var Γ → T Δ) (A : RTy Γ) (B : RTy (Γ ∙))
         → sub σ (Π A B) ≡ Π (sub σ A) (sub (ext subK σ) B)
Π-stable σ A B = refl

lam-ren : ∀ {Γ Δ} (ρ : Var Γ → Var Δ) (t : RTm (Γ ∙)) → ren ρ (lam t) ≡ lam (ren (ext renK ρ) t)
lam-ren ρ t = refl

natrec-sub : ∀ {Γ Δ} (σ : Var Γ → T Δ) z s n
           → sub σ (natrec z s n) ≡ natrec (sub σ z) (sub (ext subK (ext subK σ)) s) (sub σ n)
natrec-sub σ z s n = refl

ref-sub : ∀ {Γ Δ} (σ : Var Γ → T Δ) d → sub σ (ref d) ≡ ref d
ref-sub σ d = refl

var-sub : ∀ {Γ Δ} (σ : Var Γ → T Δ) x → sub σ (var x) ≡ σ x
var-sub σ x = refl

-- β's substitution, on a concrete term: (λ. app v0 v1)[v0 := U-code] at depth 1
ex : sub {Γ = ε ∙ ∙} (λ { vz → ref 7 ; (vs x) → var x }) (app (var vz) (var (vs vz)))
     ≡ app (ref 7) (var vz)
ex = refl
