-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE EVALUATOR: full normal forms, CERTIFIED.
--                      (PLAN-BIDI S7a; PLAN-NF Phase 1)
--
-- ★ WHAT IT RETURNS.  For a term (type) `t`, either its normal form `u`
--   with a chain `t ⟶* u` AND a witness `Nf u`, or — fuel exhausted —
--   the term reached and its chain.  Every step it takes IS a `_⟶_`
--   constructor, so the evaluator cannot take a step the kernel does not
--   have.
--
-- ★ WHY IT STAYS IN SYNC WITH THE RULES.
--   · `head` is the one place that knows the computation rules, as a
--     function: a head redex gives `just` its step, anything else
--     `nothing`.  `Nf` asks every congruence position to be normal and
--     the head to give `nothing`.
--   · `nf-irr : Nf t → t ⟶ v → ⊥` is proved by case on the STEP, so
--     Agda's coverage check makes it handle EVERY rule of `_⟶_`/`_⟶ᵀ_`.
--     A rule `head` forgets is a computation clause of `nf-irr` that
--     cannot close; a new rule is a clause `nf-irr` lacks.  Either way:
--     a compile error, never a silent slowdown.
--   · the evaluator builds `Nf` only from `head … ≡ nothing`, so it
--     cannot stop at a redex.
--
-- ★ WHAT IT IS FOR.  Normal forms are unique (`nf-irr` + Church–Rosser),
--   so conversion of two types that normalise within the fuel is DECIDED
--   by comparing normal forms: `decConvFast`.  The checker
--   (`Algorithm/CheckA`) tries it first, before the derivation-driven
--   procedure — and the evaluator is the missing function behind the
--   Knot's hand-built reduction chains (`kernel-has-no-evaluator`).
--
-- ★ GUARDED RULES (`pw?`, `stkA?`, `stkC?`) are decided by passing the
--   Boolean together with its equation (`…G b e`), so both the step and
--   its refutation see the guard's evidence — no `inspect`.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.Eval where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; Σ; _,_; ⊥; ⊥-elim )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; pw?; stkA?; stkC? )
open import DirectedHoTT.Metatheory.RedCong using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶*-trans; ⟶ᵀ*-trans; red→≅ᵀ )
open import DirectedHoTT.Metatheory.Injectivity using ( church-rosserᵀ )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no; _≟Ty_ )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- 1. ★ ONE STEP AT THE HEAD — the computation rules, as a function.
------------------------------------------------------------------------

Step : RTm Γ → Set
Step {Γ} t = Σ (RTm Γ) (λ v → t ⟶ v)

Stepᵀ : RTy Γ → Set
Stepᵀ {Γ} A = Σ (RTy Γ) (λ B → A ⟶ᵀ B)

-- the guarded rules: the Boolean, with its equation
-- ★ F6: off the pw-able codes, the ORDER's reflexivity computes on its
--   argument (`hrefl-Nat-z/s`; `pw? ⌜Nat⌝` is false, so no overlap)
hreflN : (C s : RTm Γ) → Maybe (Step (hrefl C s))
hreflN ⌜Nat⌝ nzero    = just (_ , hrefl-Nat-z)
hreflN ⌜Nat⌝ (nsuc m) = just (_ , hrefl-Nat-s m)
hreflN _     _        = nothing

hreflG : (C s : RTm Γ) (b : 𝔹) → pw? C ≡ b → Maybe (Step (hrefl C s))
hreflG C s true  e = just (_ , hrefl-pw C s e)
hreflG C s false e = hreflN C s

trHomG : (c a m : RTm (Γ ∙)) (c₁ a₁ b₁ s e : RTm Γ) (b : 𝔹) → stkA? c₁ ≡ b →
         Maybe (Step (tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e))
trHomG c a m c₁ a₁ b₁ s e true  h = just (_ , tr-J-Hom c a m c₁ a₁ b₁ s e h)
trHomG c a m c₁ a₁ b₁ s e false h = nothing

trPwG : (c a f : RTm (Γ ∙)) (e : RTm Γ) (b : 𝔹) → pw? c ≡ b →
        Maybe (Step (tr (⌜Hom⌝ c a (var vz)) (lam f) e))
trPwG c a f e true  h = just (_ , tr-pw c a f e h)
trPwG c a f e false h = nothing

apG : (cB : RTm Γ) (b : RTm (Γ ∙)) (c₁ s : RTm Γ) (x : 𝔹) → stkC? c₁ ≡ x →
      Maybe (Step (ap cB b (hrefl c₁ s)))
apG cB b c₁ s true  h = just (_ , ap-J cB b c₁ s h)
apG cB b c₁ s false h = nothing

head : (t : RTm Γ) → Maybe (Step t)
head (app (lam b) u)                       = just (_ , β b u)
head (fst (pair a b))                      = just (_ , βfst a b)
head (snd (pair a b))                      = just (_ , βsnd a b)
head (ordtr nzero t u p q)                 = just (_ , ordtr-z t u p q)
head (ordtr (nsuc a) nzero nzero p q)      = just (_ , ordtr-szz a p q)
head (ordtr (nsuc a) (nsuc t) nzero p q)   = just (_ , ordtr-ssz a t p q)
head (ordtr (nsuc a) nzero (nsuc u) p q)   = just (_ , ordtr-szs a u p q)
head (ordtr (nsuc a) (nsuc t) (nsuc u) p q) = just (_ , ordtr-sss a t u p q)
head (tr (⌜Hom⌝ c a m) (hrefl ⌜base⌝ s) e)          = just (_ , tr-J-base c a m s e)
head (tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e)     = just (_ , tr-J-Σ c a m c₁ c₂ s e)
head (tr (⌜Hom⌝ c a m) (hrefl ⌜Unit⌝ s) e)          = just (_ , tr-J-Unit c a m s e)
head (tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e) = just (_ , tr-J-Id c a m c₁ a₁ b₁ s e)
head (tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ I D i) s) e)   = just (_ , tr-J-IMu c a m s e)
head (tr (⌜Hom⌝ c a m) (hrefl (⌜Fin⌝ n) s) e)       = just (_ , tr-J-Fin c a m s e)
head (tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e) =
  trHomG c a m c₁ a₁ b₁ s e (stkA? c₁) refl
head (tr (⌜Hom⌝ c a (var vz)) (lam f) e)   = trPwG c a f e (pw? c) refl
head (tr (var vz) (lam f) e)               = just (_ , tr-taut f e)
head (hrefl C s)                           = hreflG C s (pw? C) refl
head (ap cB b (hrefl c₁ s))                = apG cB b c₁ s (stkC? c₁) refl
head (jsub d (idrefl c s) e)               = just (_ , jsub-refl d c s e)
head (natrec z s nzero)                    = just (_ , natrec-zero z s)
head (natrec z s (nsuc n))                 = just (_ , natrec-suc z s n)
head (ielim D i e (con p))                 = just (_ , ι D i e p)
head (dpay I D dι)                         = just (_ , dpay-ι I D)
head (dpay I D (dσ S f))                   = just (_ , dpay-σ I D S f)
head (dpay I D (dρ j C))                   = just (_ , dpay-ρ I D j C)
head (dih D e dι p)                        = just (_ , dih-ι D e p)
head (dih D e (dσ S f) p)                  = just (_ , dih-σ D e S f p)
head (dih D e (dρ j C) p)                  = just (_ , dih-ρ D e j C p)
head (fcase fzero a b)                     = just (_ , fcase-z a b)
head (fcase (fsuc t) a b)                  = just (_ , fcase-s t a b)
head (psplit b (pair x y))                 = just (_ , psplit-β b x y)
head (ref n b)                             = just (_ , δref n b)
head _                                     = nothing

headᵀ : (A : RTy Γ) → Maybe (Stepᵀ A)
headᵀ (El ⌜base⌝)        = just (_ , El-⌜base⌝)
headᵀ (El (⌜Π⌝ c d))     = just (_ , El-⌜Π⌝ c d)
headᵀ (El (⌜Σ⌝ c d))     = just (_ , El-⌜Σ⌝ c d)
headᵀ (El (⌜Hom⌝ c a b)) = just (_ , El-⌜Hom⌝ c a b)
headᵀ (El (⌜Id⌝ c a b))  = just (_ , El-⌜Id⌝ c a b)
headᵀ (El ⌜Nat⌝)         = just (_ , El-⌜Nat⌝)
headᵀ (El (⌜IMu⌝ I D i)) = just (_ , El-⌜IMu⌝)
headᵀ (El (⌜Fin⌝ n))     = just (_ , El-⌜Fin⌝)
headᵀ (El ⌜Unit⌝)        = just (_ , El-⌜Unit⌝)
headᵀ (DIh D M dι p)       = just (_ , DIh-ι D M p)
headᵀ (DIh D M (dσ S f) p) = just (_ , DIh-σ D M S f p)
headᵀ (DIh D M (dρ j C) p) = just (_ , DIh-ρ D M j C p)
headᵀ (Hom Nat nzero n)           = just (_ , Hom-Nat-z n)
headᵀ (Hom Nat (nsuc m) nzero)    = just (_ , Hom-Nat-sz m)
headᵀ (Hom Nat (nsuc m) (nsuc n)) = just (_ , Hom-Nat-ss m n)
headᵀ (Hom U c d)                 = just (_ , Hom-U c d)
headᵀ (Hom (Π A B) f g)           = just (_ , Hom-Π A B f g)
headᵀ _                           = nothing

------------------------------------------------------------------------
-- 2. ★ NORMAL FORMS: every congruence position normal, the head stuck.
------------------------------------------------------------------------

data Nf : RTm Γ → Set
data Nfᵀ : RTy Γ → Set

data Nf where
  nf-var    : {x : Var Γ} → Nf (var x)
  nf-lam    : {t : RTm (Γ ∙)} → Nf t → Nf (lam t)
  nf-app    : {f u : RTm Γ} → Nf f → Nf u → head (app f u) ≡ nothing → Nf (app f u)
  nf-pair   : {a b : RTm Γ} → Nf a → Nf b → Nf (pair a b)
  nf-absurd : {c e : RTm Γ} → Nf c → Nf e → Nf (absurd c e)
  nf-ordtr  : {a t u p q : RTm Γ} → Nf a → Nf t → Nf u → Nf p → Nf q →
              head (ordtr a t u p q) ≡ nothing → Nf (ordtr a t u p q)
  nf-fst    : {p : RTm Γ} → Nf p → head (fst p) ≡ nothing → Nf (fst p)
  nf-snd    : {p : RTm Γ} → Nf p → head (snd p) ≡ nothing → Nf (snd p)
  nf-⌜base⌝ : Nf (⌜base⌝ {Γ})
  nf-⌜Π⌝    : {c : RTm Γ} {d : RTm (Γ ∙)} → Nf c → Nf d → Nf (⌜Π⌝ c d)
  nf-⌜Σ⌝    : {c : RTm Γ} {d : RTm (Γ ∙)} → Nf c → Nf d → Nf (⌜Σ⌝ c d)
  nf-⌜Hom⌝  : {c a b : RTm Γ} → Nf c → Nf a → Nf b → Nf (⌜Hom⌝ c a b)
  nf-⌜Id⌝   : {c a b : RTm Γ} → Nf c → Nf a → Nf b → Nf (⌜Id⌝ c a b)
  nf-hrefl  : {c t : RTm Γ} → Nf c → Nf t → head (hrefl c t) ≡ nothing → Nf (hrefl c t)
  nf-idrefl : {c t : RTm Γ} → Nf c → Nf t → Nf (idrefl c t)
  nf-tr     : {d : RTm (Γ ∙)} {p e : RTm Γ} → Nf d → Nf p → Nf e →
              head (tr d p e) ≡ nothing → Nf (tr d p e)
  nf-ap     : {c p : RTm Γ} {b : RTm (Γ ∙)} → Nf c → Nf b → Nf p →
              head (ap c b p) ≡ nothing → Nf (ap c b p)
  nf-jsub   : {d : RTm (Γ ∙)} {p e : RTm Γ} → Nf d → Nf p → Nf e →
              head (jsub d p e) ≡ nothing → Nf (jsub d p e)
  nf-unit   : Nf (unit {Γ})
  nf-nzero  : Nf (nzero {Γ})
  nf-nsuc   : {n : RTm Γ} → Nf n → Nf (nsuc n)
  nf-natrec : {z n : RTm Γ} {s : RTm ((Γ ∙) ∙)} → Nf z → Nf s → Nf n →
              head (natrec z s n) ≡ nothing → Nf (natrec z s n)
  nf-⌜Nat⌝  : Nf (⌜Nat⌝ {Γ})
  nf-⌜Unit⌝ : Nf (⌜Unit⌝ {Γ})
  nf-⌜IMu⌝  : {I D i : RTm Γ} → Nf I → Nf D → Nf i → Nf (⌜IMu⌝ I D i)
  nf-⌜Fin⌝  : {n : RTm Γ} → Nf n → Nf (⌜Fin⌝ n)
  nf-con    : {p : RTm Γ} → Nf p → Nf (con p)
  nf-ielim  : {D i e t : RTm Γ} → Nf D → Nf i → Nf e → Nf t →
              head (ielim D i e t) ≡ nothing → Nf (ielim D i e t)
  nf-dι     : Nf (dι {Γ})
  nf-dσ     : {S f : RTm Γ} → Nf S → Nf f → Nf (dσ S f)
  nf-dρ     : {j C : RTm Γ} → Nf j → Nf C → Nf (dρ j C)
  nf-dpay   : {I D C : RTm Γ} → Nf I → Nf D → Nf C →
              head (dpay I D C) ≡ nothing → Nf (dpay I D C)
  nf-dih    : {D e C p : RTm Γ} → Nf D → Nf e → Nf C → Nf p →
              head (dih D e C p) ≡ nothing → Nf (dih D e C p)
  nf-fzero  : Nf (fzero {Γ})
  nf-fsuc   : {t : RTm Γ} → Nf t → Nf (fsuc t)
  nf-fcase  : {t a : RTm Γ} {b : RTm (Γ ∙)} → Nf t → Nf a → Nf b →
              head (fcase t a b) ≡ nothing → Nf (fcase t a b)
  nf-fcase0 : {t : RTm Γ} → Nf t → Nf (fcase0 t)
  nf-psplit : {b : RTm ((Γ ∙) ∙)} {q : RTm Γ} → Nf b → Nf q →
              head (psplit b q) ≡ nothing → Nf (psplit b q)

data Nfᵀ where
  nf-base : Nfᵀ (base {Γ})
  nf-U    : Nfᵀ (U {Γ})
  nf-Π    : {A : RTy Γ} {B : RTy (Γ ∙)} → Nfᵀ A → Nfᵀ B → Nfᵀ (Π A B)
  nf-Σ    : {A : RTy Γ} {B : RTy (Γ ∙)} → Nfᵀ A → Nfᵀ B → Nfᵀ (Σ' A B)
  nf-El   : {c : RTm Γ} → Nf c → headᵀ (El c) ≡ nothing → Nfᵀ (El c)
  nf-Hom  : {A : RTy Γ} {t u : RTm Γ} → Nfᵀ A → Nf t → Nf u →
            headᵀ (Hom A t u) ≡ nothing → Nfᵀ (Hom A t u)
  nf-Unit : Nfᵀ (Unit {Γ})
  nf-Nat  : Nfᵀ (Nat {Γ})
  nf-Id   : {A : RTy Γ} {t u : RTm Γ} → Nfᵀ A → Nf t → Nf u → Nfᵀ (Id A t u)
  nf-IMu  : {I D i : RTm Γ} → Nf I → Nf D → Nf i → Nfᵀ (IMu I D i)
  nf-Desc : {I : RTm Γ} → Nf I → Nfᵀ (Desc I)
  nf-DIh  : {D C p : RTm Γ} {M : RTy ((Γ ∙) ∙)} → Nf D → Nfᵀ M → Nf C → Nf p →
            headᵀ (DIh D M C p) ≡ nothing → Nfᵀ (DIh D M C p)
  nf-Fin  : {n : RTm Γ} → Nf n → Nfᵀ (Fin n)

------------------------------------------------------------------------
-- 3. ★ A NORMAL FORM DOES NOT STEP — by case on the STEP: every rule.
------------------------------------------------------------------------

private
  -- a guarded rule's step contradicts a stuck head
  hreflG-no : {C s : RTm Γ} (b : 𝔹) (e : pw? C ≡ b) → b ≡ true → hreflG C s b e ≡ nothing → ⊥
  hreflG-no true e h ()
  hreflG-no false e () q

  trHomG-no : {c a m : RTm (Γ ∙)} {c₁ a₁ b₁ s e : RTm Γ} (b : 𝔹) (h : stkA? c₁ ≡ b) →
              b ≡ true → trHomG c a m c₁ a₁ b₁ s e b h ≡ nothing → ⊥
  trHomG-no true h q ()
  trHomG-no false h () q

  trPwG-no : {c a f : RTm (Γ ∙)} {e : RTm Γ} (b : 𝔹) (h : pw? c ≡ b) →
             b ≡ true → trPwG c a f e b h ≡ nothing → ⊥
  trPwG-no true h q ()
  trPwG-no false h () q

  apG-no : {cB c₁ s : RTm Γ} {b : RTm (Γ ∙)} (x : 𝔹) (h : stkC? c₁ ≡ x) →
           x ≡ true → apG cB b c₁ s x h ≡ nothing → ⊥
  apG-no true h q ()
  apG-no false h () q

nf-irr  : {t v : RTm Γ} → Nf t → t ⟶ v → ⊥
nf-irrᵀ : {A B : RTy Γ} → Nfᵀ A → A ⟶ᵀ B → ⊥

nf-irr (nf-app _ _ ()) (β _ _)
nf-irr (nf-fst _ ()) (βfst _ _)
nf-irr (nf-snd _ ()) (βsnd _ _)
nf-irr (nf-lam n) (ξ-lam s) = nf-irr n s
nf-irr (nf-app n _ _) (ξ-appˡ s) = nf-irr n s
nf-irr (nf-app _ n _) (ξ-appʳ s) = nf-irr n s
nf-irr (nf-pair n _) (ξ-pairˡ s) = nf-irr n s
nf-irr (nf-pair _ n) (ξ-pairʳ s) = nf-irr n s
nf-irr (nf-ordtr _ _ _ _ _ ()) (ordtr-z _ _ _ _)
nf-irr (nf-ordtr _ _ _ _ _ ()) (ordtr-szz _ _ _)
nf-irr (nf-ordtr _ _ _ _ _ ()) (ordtr-ssz _ _ _ _)
nf-irr (nf-ordtr _ _ _ _ _ ()) (ordtr-szs _ _ _ _)
nf-irr (nf-ordtr _ _ _ _ _ ()) (ordtr-sss _ _ _ _ _)
nf-irr (nf-ordtr n _ _ _ _ _) (ξ-ordtrᵃ s) = nf-irr n s
nf-irr (nf-ordtr _ n _ _ _ _) (ξ-ordtrᵗ s) = nf-irr n s
nf-irr (nf-ordtr _ _ n _ _ _) (ξ-ordtrᵘ s) = nf-irr n s
nf-irr (nf-ordtr _ _ _ n _ _) (ξ-ordtrᵖ s) = nf-irr n s
nf-irr (nf-ordtr _ _ _ _ n _) (ξ-ordtrq s) = nf-irr n s
nf-irr (nf-absurd n _) (ξ-absurdᶜ s) = nf-irr n s
nf-irr (nf-absurd _ n) (ξ-absurdᵉ s) = nf-irr n s
nf-irr (nf-fst n _) (ξ-fst s) = nf-irr n s
nf-irr (nf-snd n _) (ξ-snd s) = nf-irr n s
nf-irr (nf-⌜Π⌝ n _) (ξ-⌜Π⌝ˡ s) = nf-irr n s
nf-irr (nf-⌜Π⌝ _ n) (ξ-⌜Π⌝ʳ s) = nf-irr n s
nf-irr (nf-⌜Σ⌝ n _) (ξ-⌜Σ⌝ˡ s) = nf-irr n s
nf-irr (nf-⌜Σ⌝ _ n) (ξ-⌜Σ⌝ʳ s) = nf-irr n s
nf-irr (nf-tr _ _ _ ()) (tr-J-base _ _ _ _ _)
nf-irr (nf-tr _ _ _ ()) (tr-J-Σ _ _ _ _ _ _ _)
nf-irr (nf-tr _ _ _ ()) (tr-J-Unit _ _ _ _ _)
nf-irr (nf-tr _ _ _ ()) (tr-J-Id _ _ _ _ _ _ _ _)
nf-irr (nf-tr _ _ _ ()) (tr-J-IMu _ _ _ _ _)
nf-irr (nf-tr _ _ _ ()) (tr-J-Fin _ _ _ _ _)
nf-irr (nf-tr _ _ _ ()) (tr-taut _ _)
nf-irr (nf-hrefl {c = C} _ _ q) (hrefl-pw _ _ h) = hreflG-no (pw? C) refl h q
nf-irr (nf-tr _ _ _ q) (tr-J-Hom _ _ _ c₁ _ _ _ _ h) = trHomG-no (stkA? c₁) refl h q
nf-irr (nf-tr _ _ _ q) (tr-pw c _ _ _ h) = trPwG-no (pw? c) refl h q
nf-irr (nf-⌜Hom⌝ n _ _) (ξ-⌜Hom⌝ᶜ s) = nf-irr n s
nf-irr (nf-⌜Hom⌝ _ n _) (ξ-⌜Hom⌝ˡ s) = nf-irr n s
nf-irr (nf-⌜Hom⌝ _ _ n) (ξ-⌜Hom⌝ʳ s) = nf-irr n s
nf-irr (nf-hrefl _ _ ()) hrefl-Nat-z
nf-irr (nf-hrefl _ _ ()) (hrefl-Nat-s _)
nf-irr (nf-hrefl n _ _) (ξ-hreflᶜ s) = nf-irr n s
nf-irr (nf-hrefl _ n _) (ξ-hreflᵃ s) = nf-irr n s
nf-irr (nf-tr n _ _ _) (ξ-trᵈ s) = nf-irr n s
nf-irr (nf-tr _ n _ _) (ξ-trᵖ s) = nf-irr n s
nf-irr (nf-tr _ _ n _) (ξ-trᵉ s) = nf-irr n s
nf-irr (nf-ap _ _ _ q) (ap-J _ _ c₁ _ h) = apG-no (stkC? c₁) refl h q
nf-irr (nf-ap n _ _ _) (ξ-apᶜ s) = nf-irr n s
nf-irr (nf-ap _ n _ _) (ξ-apᵇ s) = nf-irr n s
nf-irr (nf-ap _ _ n _) (ξ-apᵖ s) = nf-irr n s
nf-irr (nf-jsub _ _ _ ()) (jsub-refl _ _ _ _)
nf-irr (nf-⌜Id⌝ n _ _) (ξ-⌜Id⌝ᶜ s) = nf-irr n s
nf-irr (nf-⌜Id⌝ _ n _) (ξ-⌜Id⌝ˡ s) = nf-irr n s
nf-irr (nf-⌜Id⌝ _ _ n) (ξ-⌜Id⌝ʳ s) = nf-irr n s
nf-irr (nf-idrefl n _) (ξ-idreflᶜ s) = nf-irr n s
nf-irr (nf-idrefl _ n) (ξ-idreflᵃ s) = nf-irr n s
nf-irr (nf-jsub n _ _ _) (ξ-jsubᵈ s) = nf-irr n s
nf-irr (nf-jsub _ n _ _) (ξ-jsubᵖ s) = nf-irr n s
nf-irr (nf-jsub _ _ n _) (ξ-jsubᵉ s) = nf-irr n s
nf-irr (nf-natrec _ _ _ ()) (natrec-zero _ _)
nf-irr (nf-natrec _ _ _ ()) (natrec-suc _ _ _)
nf-irr (nf-nsuc n) (ξ-nsuc s) = nf-irr n s
nf-irr (nf-⌜Fin⌝ n) (ξ-⌜Fin⌝ s) = nf-irr n s
nf-irr (nf-natrec n _ _ _) (ξ-natrecᶻ s) = nf-irr n s
nf-irr (nf-natrec _ n _ _) (ξ-natrecˢ s) = nf-irr n s
nf-irr (nf-natrec _ _ n _) (ξ-natrecⁿ s) = nf-irr n s
nf-irr (nf-ielim _ _ _ _ ()) (ι _ _ _ _)
nf-irr (nf-dpay _ _ _ ()) (dpay-ι _ _)
nf-irr (nf-dpay _ _ _ ()) (dpay-σ _ _ _ _)
nf-irr (nf-dpay _ _ _ ()) (dpay-ρ _ _ _ _)
nf-irr (nf-dih _ _ _ _ ()) (dih-ι _ _ _)
nf-irr (nf-dih _ _ _ _ ()) (dih-σ _ _ _ _ _)
nf-irr (nf-dih _ _ _ _ ()) (dih-ρ _ _ _ _ _)
nf-irr (nf-fcase _ _ _ ()) (fcase-z _ _)
nf-irr (nf-fcase _ _ _ ()) (fcase-s _ _ _)
nf-irr (nf-psplit _ _ ()) (psplit-β _ _ _)
nf-irr (nf-⌜IMu⌝ n _ _) (ξ-⌜IMu⌝ᴵ s) = nf-irr n s
nf-irr (nf-⌜IMu⌝ _ n _) (ξ-⌜IMu⌝ᴰ s) = nf-irr n s
nf-irr (nf-⌜IMu⌝ _ _ n) (ξ-⌜IMu⌝ⁱ s) = nf-irr n s
nf-irr (nf-con n) (ξ-con s) = nf-irr n s
nf-irr (nf-ielim n _ _ _ _) (ξ-ielimᴰ s) = nf-irr n s
nf-irr (nf-ielim _ n _ _ _) (ξ-ielimⁱ s) = nf-irr n s
nf-irr (nf-ielim _ _ n _ _) (ξ-ielimᵉ s) = nf-irr n s
nf-irr (nf-ielim _ _ _ n _) (ξ-ielimᵗ s) = nf-irr n s
nf-irr (nf-dσ n _) (ξ-dσˢ s) = nf-irr n s
nf-irr (nf-dσ _ n) (ξ-dσᶠ s) = nf-irr n s
nf-irr (nf-dρ n _) (ξ-dρʲ s) = nf-irr n s
nf-irr (nf-dρ _ n) (ξ-dρᶜ s) = nf-irr n s
nf-irr (nf-dpay n _ _ _) (ξ-dpayᴵ s) = nf-irr n s
nf-irr (nf-dpay _ n _ _) (ξ-dpayᴰ s) = nf-irr n s
nf-irr (nf-dpay _ _ n _) (ξ-dpayᶜ s) = nf-irr n s
nf-irr (nf-dih n _ _ _ _) (ξ-dihᴰ s) = nf-irr n s
nf-irr (nf-dih _ n _ _ _) (ξ-dihᵉ s) = nf-irr n s
nf-irr (nf-dih _ _ n _ _) (ξ-dihᶜ s) = nf-irr n s
nf-irr (nf-dih _ _ _ n _) (ξ-dihᵖ s) = nf-irr n s
nf-irr (nf-fsuc n) (ξ-fsuc s) = nf-irr n s
nf-irr (nf-fcase n _ _ _) (ξ-fcaseᵗ s) = nf-irr n s
nf-irr (nf-fcase _ n _ _) (ξ-fcaseᵃ s) = nf-irr n s
nf-irr (nf-fcase _ _ n _) (ξ-fcaseᵇ s) = nf-irr n s
nf-irr (nf-fcase0 n) (ξ-fcase0 s) = nf-irr n s
nf-irr (nf-psplit n _ _) (ξ-psplitᵇ s) = nf-irr n s
nf-irr (nf-psplit _ n _) (ξ-psplitᵍ s) = nf-irr n s

nf-irrᵀ (nf-El _ ()) El-⌜base⌝
nf-irrᵀ (nf-El _ ()) (El-⌜Π⌝ _ _)
nf-irrᵀ (nf-El _ ()) (El-⌜Σ⌝ _ _)
nf-irrᵀ (nf-El _ ()) (El-⌜Hom⌝ _ _ _)
nf-irrᵀ (nf-El _ ()) (El-⌜Id⌝ _ _ _)
nf-irrᵀ (nf-El _ ()) El-⌜Nat⌝
nf-irrᵀ (nf-El _ ()) El-⌜IMu⌝
nf-irrᵀ (nf-El _ ()) El-⌜Fin⌝
nf-irrᵀ (nf-El _ ()) El-⌜Unit⌝
nf-irrᵀ (nf-DIh _ _ _ _ ()) (DIh-ι _ _ _)
nf-irrᵀ (nf-DIh _ _ _ _ ()) (DIh-σ _ _ _ _ _)
nf-irrᵀ (nf-DIh _ _ _ _ ()) (DIh-ρ _ _ _ _ _)
nf-irrᵀ (nf-El n _) (ξ-El s) = nf-irr n s
nf-irrᵀ (nf-Π n _) (ξ-Πˡ s) = nf-irrᵀ n s
nf-irrᵀ (nf-Π _ n) (ξ-Πʳ s) = nf-irrᵀ n s
nf-irrᵀ (nf-Σ n _) (ξ-Σˡ s) = nf-irrᵀ n s
nf-irrᵀ (nf-Σ _ n) (ξ-Σʳ s) = nf-irrᵀ n s
nf-irrᵀ (nf-Hom _ _ _ ()) (Hom-Nat-z _)
nf-irrᵀ (nf-Hom _ _ _ ()) (Hom-Nat-sz _)
nf-irrᵀ (nf-Hom _ _ _ ()) (Hom-Nat-ss _ _)
nf-irrᵀ (nf-Hom _ _ _ ()) (Hom-U _ _)
nf-irrᵀ (nf-Hom _ _ _ ()) (Hom-Π _ _ _ _)
nf-irrᵀ (nf-Hom n _ _ _) (ξ-Homᵀ s) = nf-irrᵀ n s
nf-irrᵀ (nf-Hom _ n _ _) (ξ-Homˡ s) = nf-irr n s
nf-irrᵀ (nf-Hom _ _ n _) (ξ-Homʳ s) = nf-irr n s
nf-irrᵀ (nf-Id n _ _) (ξ-Idᵀ s) = nf-irrᵀ n s
nf-irrᵀ (nf-Id _ n _) (ξ-Idˡ s) = nf-irr n s
nf-irrᵀ (nf-Id _ _ n) (ξ-Idʳ s) = nf-irr n s
nf-irrᵀ (nf-IMu n _ _) (ξ-IMuᴵ s) = nf-irr n s
nf-irrᵀ (nf-IMu _ n _) (ξ-IMuᴰ s) = nf-irr n s
nf-irrᵀ (nf-IMu _ _ n) (ξ-IMuⁱ s) = nf-irr n s
nf-irrᵀ (nf-Desc n) (ξ-Desc s) = nf-irr n s
nf-irrᵀ (nf-Fin n) (ξ-Fin s) = nf-irr n s
nf-irrᵀ (nf-DIh n _ _ _ _) (ξ-DIhᴰ s) = nf-irr n s
nf-irrᵀ (nf-DIh _ n _ _ _) (ξ-DIhᴹ s) = nf-irrᵀ n s
nf-irrᵀ (nf-DIh _ _ n _ _) (ξ-DIhᶜ s) = nf-irr n s
nf-irrᵀ (nf-DIh _ _ _ n _) (ξ-DIhᵖ s) = nf-irr n s

------------------------------------------------------------------------
-- 4. ★ THE EVALUATOR — innermost: the fields first, then the head; a
--    contraction spends one unit of fuel.  Its result carries the chain.
------------------------------------------------------------------------

data Ev {Γ : Cx} (t : RTm Γ) : Set where
  nfd : (u : RTm Γ) → t ⟶* u → Nf u → Ev t
  out : (u : RTm Γ) → t ⟶* u → Ev t        -- fuel exhausted

data Evᵀ {Γ : Cx} (A : RTy Γ) : Set where
  nfdᵀ : (B : RTy Γ) → A ⟶ᵀ* B → Nfᵀ B → Evᵀ A
  outᵀ : (B : RTy Γ) → A ⟶ᵀ* B → Evᵀ A

private
  variable
    Δ : Cx

  -- a chain, through a congruence
  map* : {a b : RTm Δ} (f : RTm Δ → RTm Γ) → (∀ {x y} → x ⟶ y → f x ⟶ f y) →
         a ⟶* b → f a ⟶* f b
  map* f ξ done       = done
  map* f ξ (step r p) = step (ξ r) (map* f ξ p)

  map*ᵗ : {a b : RTm Δ} (f : RTm Δ → RTy Γ) → (∀ {x y} → x ⟶ y → f x ⟶ᵀ f y) →
          a ⟶* b → f a ⟶ᵀ* f b
  map*ᵗ f ξ done       = doneᵀ
  map*ᵗ f ξ (step r p) = stepᵀ (ξ r) (map*ᵗ f ξ p)

  map*ᵀ : {A B : RTy Δ} (f : RTy Δ → RTy Γ) → (∀ {X Y} → X ⟶ᵀ Y → f X ⟶ᵀ f Y) →
          A ⟶ᵀ* B → f A ⟶ᵀ* f B
  map*ᵀ f ξ doneᵀ       = doneᵀ
  map*ᵀ f ξ (stepᵀ r p) = stepᵀ (ξ r) (map*ᵀ f ξ p)

  -- ★ one FIELD: evaluate it, extend the chain through the congruence,
  --   and continue with its normal form — or stop, fuel exhausted
  fld : {t : RTm Γ} {a : RTm Δ} (f : RTm Δ → RTm Γ) → (∀ {x y} → x ⟶ y → f x ⟶ f y) →
        t ⟶* f a → Ev a → ({a' : RTm Δ} → Nf a' → t ⟶* f a' → Ev t) → Ev t
  fld f ξ ch (nfd a' c n) k = k n (⟶*-trans ch (map* f ξ c))
  fld f ξ ch (out a' c)   k = out (f a') (⟶*-trans ch (map* f ξ c))

  fldᵗ : {A : RTy Γ} {a : RTm Δ} (f : RTm Δ → RTy Γ) → (∀ {x y} → x ⟶ y → f x ⟶ᵀ f y) →
         A ⟶ᵀ* f a → Ev a → ({a' : RTm Δ} → Nf a' → A ⟶ᵀ* f a' → Evᵀ A) → Evᵀ A
  fldᵗ f ξ ch (nfd a' c n) k = k n (⟶ᵀ*-trans ch (map*ᵗ f ξ c))
  fldᵗ f ξ ch (out a' c)   k = outᵀ (f a') (⟶ᵀ*-trans ch (map*ᵗ f ξ c))

  fldᵀ : {A : RTy Γ} {X : RTy Δ} (f : RTy Δ → RTy Γ) → (∀ {x y} → x ⟶ᵀ y → f x ⟶ᵀ f y) →
         A ⟶ᵀ* f X → Evᵀ X → ({X' : RTy Δ} → Nfᵀ X' → A ⟶ᵀ* f X' → Evᵀ A) → Evᵀ A
  fldᵀ f ξ ch (nfdᵀ X' c n) k = k n (⟶ᵀ*-trans ch (map*ᵀ f ξ c))
  fldᵀ f ξ ch (outᵀ X' c)   k = outᵀ (f X') (⟶ᵀ*-trans ch (map*ᵀ f ξ c))

  -- continue from a reduct
  thenᵉ : {t u : RTm Γ} → t ⟶* u → Ev u → Ev t
  thenᵉ ch (nfd v c n) = nfd v (⟶*-trans ch c) n
  thenᵉ ch (out v c)   = out v (⟶*-trans ch c)

  thenᵀ : {A B : RTy Γ} → A ⟶ᵀ* B → Evᵀ B → Evᵀ A
  thenᵀ ch (nfdᵀ C c n) = nfdᵀ C (⟶ᵀ*-trans ch c) n
  thenᵀ ch (outᵀ C c)   = outᵀ C (⟶ᵀ*-trans ch c)

eval  : ℕ → (t : RTm Γ) → Ev t
evalᵀ : ℕ → (A : RTy Γ) → Evᵀ A

private
  -- ★ the HEAD, once the fields are normal: stuck ⇒ normal; else contract
  contract : ℕ → {t u : RTm Γ} → t ⟶* u → Step u → Ev t
  contract zero    ch (v , r) = out v (⟶*-trans ch (step r done))
  contract (suc k) ch (v , r) = thenᵉ (⟶*-trans ch (step r done)) (eval k v)

  finG : ℕ → {t : RTm Γ} (u : RTm Γ) → t ⟶* u → (head u ≡ nothing → Nf u) →
         (m : Maybe (Step u)) → head u ≡ m → Ev t
  finG k u ch mk (just st) _ = contract k ch st
  finG k u ch mk nothing   e = nfd u ch (mk e)

  fin : ℕ → {t : RTm Γ} (u : RTm Γ) → t ⟶* u → (head u ≡ nothing → Nf u) → Ev t
  fin k u ch mk = finG k u ch mk (head u) refl

  contractᵀ : ℕ → {A B : RTy Γ} → A ⟶ᵀ* B → Stepᵀ B → Evᵀ A
  contractᵀ zero    ch (C , r) = outᵀ C (⟶ᵀ*-trans ch (stepᵀ r doneᵀ))
  contractᵀ (suc k) ch (C , r) = thenᵀ (⟶ᵀ*-trans ch (stepᵀ r doneᵀ)) (evalᵀ k C)

  finGᵀ : ℕ → {A : RTy Γ} (B : RTy Γ) → A ⟶ᵀ* B → (headᵀ B ≡ nothing → Nfᵀ B) →
          (m : Maybe (Stepᵀ B)) → headᵀ B ≡ m → Evᵀ A
  finGᵀ k B ch mk (just st) _ = contractᵀ k ch st
  finGᵀ k B ch mk nothing   e = nfdᵀ B ch (mk e)

  finᵀ : ℕ → {A : RTy Γ} (B : RTy Γ) → A ⟶ᵀ* B → (headᵀ B ≡ nothing → Nfᵀ B) → Evᵀ A
  finᵀ k B ch mk = finGᵀ k B ch mk (headᵀ B) refl

eval k (var x) = nfd _ done nf-var
eval k (lam t) =
  fld lam ξ-lam done (eval k t) λ n ch → nfd _ ch (nf-lam n)
eval k (app f u) =
  fld (λ x → app x u) ξ-appˡ done (eval k f) λ {f'} nf ch →
  fld (app f') ξ-appʳ ch (eval k u) λ {u'} nu ch' →
  fin k (app f' u') ch' (nf-app nf nu)
eval k (pair a b) =
  fld (λ x → pair x b) ξ-pairˡ done (eval k a) λ {a'} na ch →
  fld (pair a') ξ-pairʳ ch (eval k b) λ nb ch' → nfd _ ch' (nf-pair na nb)
eval k (absurd c e) =
  fld (λ x → absurd x e) ξ-absurdᶜ done (eval k c) λ {c'} nc ch →
  fld (absurd c') ξ-absurdᵉ ch (eval k e) λ ne ch' → nfd _ ch' (nf-absurd nc ne)
eval k (ordtr a t u p q) =
  fld (λ x → ordtr x t u p q) ξ-ordtrᵃ done (eval k a) λ {a'} na c1 →
  fld (λ x → ordtr a' x u p q) ξ-ordtrᵗ c1 (eval k t) λ {t'} nt c2 →
  fld (λ x → ordtr a' t' x p q) ξ-ordtrᵘ c2 (eval k u) λ {u'} nu c3 →
  fld (λ x → ordtr a' t' u' x q) ξ-ordtrᵖ c3 (eval k p) λ {p'} np c4 →
  fld (ordtr a' t' u' p') ξ-ordtrq c4 (eval k q) λ {q'} nq c5 →
  fin k (ordtr a' t' u' p' q') c5 (nf-ordtr na nt nu np nq)
eval k (fst p) = fld fst ξ-fst done (eval k p) λ {p'} n ch → fin k (fst p') ch (nf-fst n)
eval k (snd p) = fld snd ξ-snd done (eval k p) λ {p'} n ch → fin k (snd p') ch (nf-snd n)
eval k ⌜base⌝ = nfd _ done nf-⌜base⌝
eval k (⌜Π⌝ c d) =
  fld (λ x → ⌜Π⌝ x d) ξ-⌜Π⌝ˡ done (eval k c) λ {c'} nc ch →
  fld (⌜Π⌝ c') ξ-⌜Π⌝ʳ ch (eval k d) λ nd ch' → nfd _ ch' (nf-⌜Π⌝ nc nd)
eval k (⌜Σ⌝ c d) =
  fld (λ x → ⌜Σ⌝ x d) ξ-⌜Σ⌝ˡ done (eval k c) λ {c'} nc ch →
  fld (⌜Σ⌝ c') ξ-⌜Σ⌝ʳ ch (eval k d) λ nd ch' → nfd _ ch' (nf-⌜Σ⌝ nc nd)
eval k (⌜Hom⌝ c a b) =
  fld (λ x → ⌜Hom⌝ x a b) ξ-⌜Hom⌝ᶜ done (eval k c) λ {c'} nc c1 →
  fld (λ x → ⌜Hom⌝ c' x b) ξ-⌜Hom⌝ˡ c1 (eval k a) λ {a'} na c2 →
  fld (⌜Hom⌝ c' a') ξ-⌜Hom⌝ʳ c2 (eval k b) λ nb c3 → nfd _ c3 (nf-⌜Hom⌝ nc na nb)
eval k (⌜Id⌝ c a b) =
  fld (λ x → ⌜Id⌝ x a b) ξ-⌜Id⌝ᶜ done (eval k c) λ {c'} nc c1 →
  fld (λ x → ⌜Id⌝ c' x b) ξ-⌜Id⌝ˡ c1 (eval k a) λ {a'} na c2 →
  fld (⌜Id⌝ c' a') ξ-⌜Id⌝ʳ c2 (eval k b) λ nb c3 → nfd _ c3 (nf-⌜Id⌝ nc na nb)
eval k (hrefl c t) =
  fld (λ x → hrefl x t) ξ-hreflᶜ done (eval k c) λ {c'} nc ch →
  fld (hrefl c') ξ-hreflᵃ ch (eval k t) λ {t'} nt ch' → fin k (hrefl c' t') ch' (nf-hrefl nc nt)
eval k (idrefl c t) =
  fld (λ x → idrefl x t) ξ-idreflᶜ done (eval k c) λ {c'} nc ch →
  fld (idrefl c') ξ-idreflᵃ ch (eval k t) λ nt ch' → nfd _ ch' (nf-idrefl nc nt)
eval k (tr d p e) =
  fld (λ x → tr x p e) ξ-trᵈ done (eval k d) λ {d'} nd c1 →
  fld (λ x → tr d' x e) ξ-trᵖ c1 (eval k p) λ {p'} np c2 →
  fld (tr d' p') ξ-trᵉ c2 (eval k e) λ {e'} ne c3 → fin k (tr d' p' e') c3 (nf-tr nd np ne)
eval k (ap c b p) =
  fld (λ x → ap x b p) ξ-apᶜ done (eval k c) λ {c'} nc c1 →
  fld (λ x → ap c' x p) ξ-apᵇ c1 (eval k b) λ {b'} nb c2 →
  fld (ap c' b') ξ-apᵖ c2 (eval k p) λ {p'} np c3 → fin k (ap c' b' p') c3 (nf-ap nc nb np)
eval k (jsub d p e) =
  fld (λ x → jsub x p e) ξ-jsubᵈ done (eval k d) λ {d'} nd c1 →
  fld (λ x → jsub d' x e) ξ-jsubᵖ c1 (eval k p) λ {p'} np c2 →
  fld (jsub d' p') ξ-jsubᵉ c2 (eval k e) λ {e'} ne c3 → fin k (jsub d' p' e') c3 (nf-jsub nd np ne)
eval k unit = nfd _ done nf-unit
eval k nzero = nfd _ done nf-nzero
eval k (nsuc n) = fld nsuc ξ-nsuc done (eval k n) λ nn ch → nfd _ ch (nf-nsuc nn)
eval k (natrec z s n) =
  fld (λ x → natrec x s n) ξ-natrecᶻ done (eval k z) λ {z'} nz c1 →
  fld (λ x → natrec z' x n) ξ-natrecˢ c1 (eval k s) λ {s'} ns c2 →
  fld (natrec z' s') ξ-natrecⁿ c2 (eval k n) λ {n'} nn c3 → fin k (natrec z' s' n') c3 (nf-natrec nz ns nn)
eval k ⌜Nat⌝ = nfd _ done nf-⌜Nat⌝
eval k ⌜Unit⌝ = nfd _ done nf-⌜Unit⌝
eval k (⌜IMu⌝ I D i) =
  fld (λ x → ⌜IMu⌝ x D i) ξ-⌜IMu⌝ᴵ done (eval k I) λ {I'} nI c1 →
  fld (λ x → ⌜IMu⌝ I' x i) ξ-⌜IMu⌝ᴰ c1 (eval k D) λ {D'} nD c2 →
  fld (⌜IMu⌝ I' D') ξ-⌜IMu⌝ⁱ c2 (eval k i) λ ni c3 → nfd _ c3 (nf-⌜IMu⌝ nI nD ni)
eval k (⌜Fin⌝ n) = fld ⌜Fin⌝ ξ-⌜Fin⌝ done (eval k n) λ nn ch → nfd _ ch (nf-⌜Fin⌝ nn)
eval k (con p) = fld con ξ-con done (eval k p) λ np ch → nfd _ ch (nf-con np)
eval k (ielim D i e t) =
  fld (λ x → ielim x i e t) ξ-ielimᴰ done (eval k D) λ {D'} nD c1 →
  fld (λ x → ielim D' x e t) ξ-ielimⁱ c1 (eval k i) λ {i'} ni c2 →
  fld (λ x → ielim D' i' x t) ξ-ielimᵉ c2 (eval k e) λ {e'} ne c3 →
  fld (ielim D' i' e') ξ-ielimᵗ c3 (eval k t) λ {t'} nt c4 →
  fin k (ielim D' i' e' t') c4 (nf-ielim nD ni ne nt)
eval k dι = nfd _ done nf-dι
eval k (dσ S f) =
  fld (λ x → dσ x f) ξ-dσˢ done (eval k S) λ {S'} nS ch →
  fld (dσ S') ξ-dσᶠ ch (eval k f) λ nf ch' → nfd _ ch' (nf-dσ nS nf)
eval k (dρ j C) =
  fld (λ x → dρ x C) ξ-dρʲ done (eval k j) λ {j'} nj ch →
  fld (dρ j') ξ-dρᶜ ch (eval k C) λ nC ch' → nfd _ ch' (nf-dρ nj nC)
eval k (dpay I D C) =
  fld (λ x → dpay x D C) ξ-dpayᴵ done (eval k I) λ {I'} nI c1 →
  fld (λ x → dpay I' x C) ξ-dpayᴰ c1 (eval k D) λ {D'} nD c2 →
  fld (dpay I' D') ξ-dpayᶜ c2 (eval k C) λ {C'} nC c3 → fin k (dpay I' D' C') c3 (nf-dpay nI nD nC)
eval k (dih D e C p) =
  fld (λ x → dih x e C p) ξ-dihᴰ done (eval k D) λ {D'} nD c1 →
  fld (λ x → dih D' x C p) ξ-dihᵉ c1 (eval k e) λ {e'} ne c2 →
  fld (λ x → dih D' e' x p) ξ-dihᶜ c2 (eval k C) λ {C'} nC c3 →
  fld (dih D' e' C') ξ-dihᵖ c3 (eval k p) λ {p'} np c4 →
  fin k (dih D' e' C' p') c4 (nf-dih nD ne nC np)
eval k fzero = nfd _ done nf-fzero
-- a definition always unfolds: its head is never stuck
eval k (ref n b) = fin k (ref n b) done (λ ())
eval k (fsuc t) = fld fsuc ξ-fsuc done (eval k t) λ nt ch → nfd _ ch (nf-fsuc nt)
eval k (fcase t a b) =
  fld (λ x → fcase x a b) ξ-fcaseᵗ done (eval k t) λ {t'} nt c1 →
  fld (λ x → fcase t' x b) ξ-fcaseᵃ c1 (eval k a) λ {a'} na c2 →
  fld (fcase t' a') ξ-fcaseᵇ c2 (eval k b) λ {b'} nb c3 → fin k (fcase t' a' b') c3 (nf-fcase nt na nb)
eval k (fcase0 t) = fld fcase0 ξ-fcase0 done (eval k t) λ nt ch → nfd _ ch (nf-fcase0 nt)
eval k (psplit b q) =
  fld (λ x → psplit x q) ξ-psplitᵇ done (eval k b) λ {b'} nb ch →
  fld (psplit b') ξ-psplitᵍ ch (eval k q) λ {q'} nq ch' → fin k (psplit b' q') ch' (nf-psplit nb nq)

evalᵀ k base = nfdᵀ _ doneᵀ nf-base
evalᵀ k U    = nfdᵀ _ doneᵀ nf-U
evalᵀ k Unit = nfdᵀ _ doneᵀ nf-Unit
evalᵀ k Nat  = nfdᵀ _ doneᵀ nf-Nat
evalᵀ k (Fin n) = fldᵗ Fin ξ-Fin doneᵀ (eval k n) λ nn ch → nfdᵀ _ ch (nf-Fin nn)
evalᵀ k (Π A B) =
  fldᵀ (λ X → Π X B) ξ-Πˡ doneᵀ (evalᵀ k A) λ {A'} nA ch →
  fldᵀ (Π A') ξ-Πʳ ch (evalᵀ k B) λ nB ch' → nfdᵀ _ ch' (nf-Π nA nB)
evalᵀ k (Σ' A B) =
  fldᵀ (λ X → Σ' X B) ξ-Σˡ doneᵀ (evalᵀ k A) λ {A'} nA ch →
  fldᵀ (Σ' A') ξ-Σʳ ch (evalᵀ k B) λ nB ch' → nfdᵀ _ ch' (nf-Σ nA nB)
evalᵀ k (El c) = fldᵗ El ξ-El doneᵀ (eval k c) λ {c'} nc ch → finᵀ k (El c') ch (nf-El nc)
evalᵀ k (Hom A t u) =
  fldᵀ (λ X → Hom X t u) ξ-Homᵀ doneᵀ (evalᵀ k A) λ {A'} nA c1 →
  fldᵗ (λ x → Hom A' x u) ξ-Homˡ c1 (eval k t) λ {t'} nt c2 →
  fldᵗ (Hom A' t') ξ-Homʳ c2 (eval k u) λ {u'} nu c3 → finᵀ k (Hom A' t' u') c3 (nf-Hom nA nt nu)
evalᵀ k (Id A t u) =
  fldᵀ (λ X → Id X t u) ξ-Idᵀ doneᵀ (evalᵀ k A) λ {A'} nA c1 →
  fldᵗ (λ x → Id A' x u) ξ-Idˡ c1 (eval k t) λ {t'} nt c2 →
  fldᵗ (Id A' t') ξ-Idʳ c2 (eval k u) λ nu c3 → nfdᵀ _ c3 (nf-Id nA nt nu)
evalᵀ k (IMu I D i) =
  fldᵗ (λ x → IMu x D i) ξ-IMuᴵ doneᵀ (eval k I) λ {I'} nI c1 →
  fldᵗ (λ x → IMu I' x i) ξ-IMuᴰ c1 (eval k D) λ {D'} nD c2 →
  fldᵗ (IMu I' D') ξ-IMuⁱ c2 (eval k i) λ ni c3 → nfdᵀ _ c3 (nf-IMu nI nD ni)
evalᵀ k (Desc I) = fldᵗ Desc ξ-Desc doneᵀ (eval k I) λ nI ch → nfdᵀ _ ch (nf-Desc nI)
evalᵀ k (DIh D M C p) =
  fldᵗ (λ x → DIh x M C p) ξ-DIhᴰ doneᵀ (eval k D) λ {D'} nD c1 →
  fldᵀ (λ X → DIh D' X C p) ξ-DIhᴹ c1 (evalᵀ k M) λ {M'} nM c2 →
  fldᵗ (λ x → DIh D' M' x p) ξ-DIhᶜ c2 (eval k C) λ {C'} nC c3 →
  fldᵗ (DIh D' M' C') ξ-DIhᵖ c3 (eval k p) λ {p'} np c4 →
  finᵀ k (DIh D' M' C' p') c4 (nf-DIh nD nM nC np)

------------------------------------------------------------------------
-- 5. ★ NORMAL FORMS ARE UNIQUE ⇒ conversion is DECIDED by them.
------------------------------------------------------------------------

-- a normal type reduces only to itself
nf-stuckᵀ : {N C : RTy Γ} → Nfᵀ N → N ⟶ᵀ* C → N ≡ C
nf-stuckᵀ n doneᵀ          = refl
nf-stuckᵀ n (stepᵀ r rest) = ⊥-elim (nf-irrᵀ n r)

-- two convertible types have the SAME normal form (Church–Rosser)
nf-uniqueᵀ : {A B A' B' : RTy Γ} → Nfᵀ A' → Nfᵀ B' → A ⟶ᵀ* A' → B ⟶ᵀ* B' → A ≅ᵀ B → A' ≡ B'
nf-uniqueᵀ nA nB rA rB c
  with church-rosserᵀ (ctrnᵀ (csymᵀ (red→≅ᵀ rA)) (ctrnᵀ c (red→≅ᵀ rB)))
... | C , (r₁ , r₂) = trans (nf-stuckᵀ nA r₁) (sym (nf-stuckᵀ nB r₂))

-- ★ conversion, decided by evaluation — `nothing` only if the fuel runs out
decConvFast : ℕ → (A B : RTy Γ) → Maybe (Dec (A ≅ᵀ B))
decConvFast k A B with evalᵀ k A | evalᵀ k B
... | nfdᵀ A' rA nA | nfdᵀ B' rB nB with A' ≟Ty B'
...   | yes refl = just (yes (ctrnᵀ (red→≅ᵀ rA) (csymᵀ (red→≅ᵀ rB))))
...   | no ne    = just (no (λ c → ne (nf-uniqueᵀ nA nB rA rB c)))
decConvFast k A B | _ | _ = nothing
