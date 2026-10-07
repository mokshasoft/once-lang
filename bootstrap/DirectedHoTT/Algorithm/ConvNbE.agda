-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ CONVERSION DECIDED BY THE ENVIRONMENT EVALUATOR
-- (PLAN-EVAL E3, the checker's side).
--
-- `Algorithm/NbE` computes a candidate normal form; `nbe-sound`/`nbeᵀ-sound`
-- make it CONVERTIBLE with its input.  Whether it is NORMAL is not a
-- theorem about the evaluator (fuel can run out; a rule can be left stuck)
-- but it is DECIDABLE on the output: `Algorithm/Eval`'s certificate
-- `Nf`/`Nfᵀ` is syntactic — every field normal, no redex at the head
-- (`head`) — so `nf?`/`nfᵀ?` CHECK it in one pass, evaluating nothing.
--
-- With both: a certified normal form of a type, and conversion DECIDED —
--   · yes: equal normal forms (`A ≅ᵀ N ≡ M ≅ᵀ B`);
--   · no : two normal forms that are convertible are EQUAL (Church–Rosser,
--          a normal form does not step), so distinct ones refute.
-- `nothing` only where a readback is not certified normal; the checker
-- then falls back to its other procedures.
--
-- `--safe`, ZERO postulates.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; _<ˢ?_ )
open import DirectedHoTT.Algorithm.NbE.Value using ( Tbl )
import DirectedHoTT.Algorithm.NbE.TblOK as TO
module DirectedHoTT.Algorithm.ConvNbE (𝒮 : KSig) (tbl : Tbl) (tok : TO.TblOK 𝒮 tbl) where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; Σ; _,_; _×_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Reduction 𝒮 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.Injectivity 𝒮 using ( church-rosserᵀ )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no; _≟Ty_ )
import DirectedHoTT.Algorithm.Eval 𝒮 as ᴵEval
open ᴵEval using ( Step; Stepᵀ; head; headᵀ; Nf; Nfᵀ; nf-stuckᵀ )
open ᴵEval
open import DirectedHoTT.Algorithm.NbE tbl using ( nbeᵀ )
open import DirectedHoTT.Algorithm.NbESoundTy 𝒮 tbl tok using ( nbeᵀ-sound )

private
  variable
    Γ : Cx

  infixl 1 _>>=_
  _>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  just a  >>= f = f a
  nothing >>= f = nothing

  -- no redex at the head, decided (the evidence `head` returns, read back)
  hd : (t : RTm Γ) → Maybe (head t ≡ nothing)
  hd t = go (head t) refl
    where
    go : (m : Maybe (Step t)) → head t ≡ m → Maybe (head t ≡ nothing)
    go nothing  e = just e
    go (just _) _ = nothing

  hdᵀ : (A : RTy Γ) → Maybe (headᵀ A ≡ nothing)
  hdᵀ A = go (headᵀ A) refl
    where
    go : (m : Maybe (Stepᵀ A)) → headᵀ A ≡ m → Maybe (headᵀ A ≡ nothing)
    go nothing  e = just e
    go (just _) _ = nothing

------------------------------------------------------------------------
-- 1. Normality, CHECKED (one clause per `Nf` constructor; `ref` is a
--    δ-redex, so never normal).
------------------------------------------------------------------------

-- a reference is normal exactly when it names no entry (PLAN-REF)
refNf : {Γ : Cx} (d : ℕ) (q : Dec (d <ˢ KSig.size 𝒮)) → (d <ˢ? KSig.size 𝒮) ≡ q → Maybe (Nf (ref {Γ} d))
refNf d (yes _) _ = nothing
refNf d (no _)  e = just (nf-ref (cong (refHead d) e))

nf?  : (t : RTm Γ) → Maybe (Nf t)
nfᵀ? : (A : RTy Γ) → Maybe (Nfᵀ A)

nf? (var x)          = just nf-var
nf? (lam t)          = nf? t >>= λ n → just (nf-lam n)
nf? (app f u)        = nf? f >>= λ a → nf? u >>= λ b → hd (app f u) >>= λ h → just (nf-app a b h)
nf? (pair a b)       = nf? a >>= λ x → nf? b >>= λ y → just (nf-pair x y)
nf? (absurd c e)     = nf? c >>= λ x → nf? e >>= λ y → just (nf-absurd x y)
nf? (ordtr a t u p q) =
  nf? a >>= λ na → nf? t >>= λ nt → nf? u >>= λ nu → nf? p >>= λ np → nf? q >>= λ nq →
  hd (ordtr a t u p q) >>= λ h → just (nf-ordtr na nt nu np nq h)
nf? (fst p)          = nf? p >>= λ n → hd (fst p) >>= λ h → just (nf-fst n h)
nf? (snd p)          = nf? p >>= λ n → hd (snd p) >>= λ h → just (nf-snd n h)
nf? ⌜base⌝           = just nf-⌜base⌝
nf? (⌜Π⌝ c d)        = nf? c >>= λ x → nf? d >>= λ y → just (nf-⌜Π⌝ x y)
nf? (⌜Σ⌝ c d)        = nf? c >>= λ x → nf? d >>= λ y → just (nf-⌜Σ⌝ x y)
nf? (⌜Hom⌝ c a b)    = nf? c >>= λ x → nf? a >>= λ y → nf? b >>= λ z → just (nf-⌜Hom⌝ x y z)
nf? (⌜Id⌝ c a b)     = nf? c >>= λ x → nf? a >>= λ y → nf? b >>= λ z → just (nf-⌜Id⌝ x y z)
nf? (hrefl c t)      = nf? c >>= λ x → nf? t >>= λ y → hd (hrefl c t) >>= λ h → just (nf-hrefl x y h)
nf? (idrefl c t)     = nf? c >>= λ x → nf? t >>= λ y → just (nf-idrefl x y)
nf? (tr d p e)       = nf? d >>= λ x → nf? p >>= λ y → nf? e >>= λ z → hd (tr d p e) >>= λ h → just (nf-tr x y z h)
nf? (ap c b p)       = nf? c >>= λ x → nf? b >>= λ y → nf? p >>= λ z → hd (ap c b p) >>= λ h → just (nf-ap x y z h)
nf? (jsub d p e)     = nf? d >>= λ x → nf? p >>= λ y → nf? e >>= λ z → hd (jsub d p e) >>= λ h → just (nf-jsub x y z h)
nf? unit             = just nf-unit
nf? nzero            = just nf-nzero
nf? (nsuc n)         = nf? n >>= λ x → just (nf-nsuc x)
nf? (natrec z s n)   = nf? z >>= λ x → nf? s >>= λ y → nf? n >>= λ w → hd (natrec z s n) >>= λ h → just (nf-natrec x y w h)
nf? ⌜Nat⌝            = just nf-⌜Nat⌝
nf? ⌜Unit⌝           = just nf-⌜Unit⌝
nf? (⌜IMu⌝ I D i)    = nf? I >>= λ x → nf? D >>= λ y → nf? i >>= λ z → just (nf-⌜IMu⌝ x y z)
nf? (⌜Fin⌝ n)        = nf? n >>= λ x → just (nf-⌜Fin⌝ x)
nf? (con p)          = nf? p >>= λ x → just (nf-con x)
nf? (ielim D i e t)  =
  nf? D >>= λ a → nf? i >>= λ b → nf? e >>= λ c → nf? t >>= λ d → hd (ielim D i e t) >>= λ h → just (nf-ielim a b c d h)
nf? dι               = just nf-dι
nf? (dσ S f)         = nf? S >>= λ x → nf? f >>= λ y → just (nf-dσ x y)
nf? (dρ j C)         = nf? j >>= λ x → nf? C >>= λ y → just (nf-dρ x y)
nf? (dpay I D C)     = nf? I >>= λ x → nf? D >>= λ y → nf? C >>= λ z → hd (dpay I D C) >>= λ h → just (nf-dpay x y z h)
nf? (dih D e C p)    =
  nf? D >>= λ a → nf? e >>= λ b → nf? C >>= λ c → nf? p >>= λ d → hd (dih D e C p) >>= λ h → just (nf-dih a b c d h)
nf? fzero            = just nf-fzero
nf? (fsuc t)         = nf? t >>= λ x → just (nf-fsuc x)
nf? (fcase t a b)    = nf? t >>= λ x → nf? a >>= λ y → nf? b >>= λ z → hd (fcase t a b) >>= λ h → just (nf-fcase x y z h)
nf? (fcase0 t)       = nf? t >>= λ x → just (nf-fcase0 x)
nf? (psplit b q)     = nf? b >>= λ x → nf? q >>= λ y → hd (psplit b q) >>= λ h → just (nf-psplit x y h)
nf? (ref d)          = refNf d (d <ˢ? KSig.size 𝒮) refl

nfᵀ? base          = just nf-base
nfᵀ? U             = just nf-U
nfᵀ? (Π A B)       = nfᵀ? A >>= λ x → nfᵀ? B >>= λ y → just (nf-Π x y)
nfᵀ? (Σ' A B)      = nfᵀ? A >>= λ x → nfᵀ? B >>= λ y → just (nf-Σ x y)
nfᵀ? (El c)        = nf? c >>= λ x → hdᵀ (El c) >>= λ h → just (nf-El x h)
nfᵀ? (Hom A t u)   = nfᵀ? A >>= λ x → nf? t >>= λ y → nf? u >>= λ z → hdᵀ (Hom A t u) >>= λ h → just (nf-Hom x y z h)
nfᵀ? Unit          = just nf-Unit
nfᵀ? Nat           = just nf-Nat
nfᵀ? (Id A t u)    = nfᵀ? A >>= λ x → nf? t >>= λ y → nf? u >>= λ z → just (nf-Id x y z)
nfᵀ? (IMu I D i)   = nf? I >>= λ x → nf? D >>= λ y → nf? i >>= λ z → just (nf-IMu x y z)
nfᵀ? (Desc I)      = nf? I >>= λ x → just (nf-Desc x)
nfᵀ? (DIh D M C p) =
  nf? D >>= λ a → nfᵀ? M >>= λ b → nf? C >>= λ c → nf? p >>= λ d → hdᵀ (DIh D M C p) >>= λ h → just (nf-DIh a b c d h)
nfᵀ? (Fin n)       = nf? n >>= λ x → just (nf-Fin x)

------------------------------------------------------------------------
-- 2. ★ A certified normal form of a type, and conversion decided.
------------------------------------------------------------------------

nbeFuel : ℕ
nbeFuel = 100000

-- a normal form CONVERTIBLE with A and CERTIFIED normal
record NfOf {Γ : Cx} (A : RTy Γ) : Set where
  constructor nbeNfv
  field
    N   : RTy Γ
    cnv : A ≅ᵀ N
    nrm : Nfᵀ N

nbeNf : (A : RTy Γ) → Maybe (NfOf A)
nbeNf A = at (nbeᵀ nbeFuel A) refl
  where
  -- the readback computed ONCE (an argument: an expression written twice
  -- is evaluated twice)
  at : (N : RTy _) → nbeᵀ nbeFuel A ≡ N → Maybe (NfOf A)
  at N e = nfᵀ? N >>= λ n → just (nbeNfv N (cnv e) n)
    where cnv : nbeᵀ nbeFuel A ≡ N → A ≅ᵀ N
          cnv refl = nbeᵀ-sound nbeFuel A

-- ★ two normal forms that are convertible are EQUAL
nf-convᵀ : {N M : RTy Γ} → Nfᵀ N → Nfᵀ M → N ≅ᵀ M → N ≡ M
nf-convᵀ nN nM c with church-rosserᵀ c
... | C , (r₁ , r₂) = trans (nf-stuckᵀ nN r₁) (sym (nf-stuckᵀ nM r₂))

private
  ≡→≅ᵀ : {A B : RTy Γ} → A ≡ B → A ≅ᵀ B
  ≡→≅ᵀ refl = crflᵀ

  decide : {A B : RTy Γ} (a : NfOf A) (b : NfOf B) → Dec (NfOf.N a ≡ NfOf.N b) → Dec (A ≅ᵀ B)
  decide (nbeNfv N ca na) (nbeNfv M cb nb) (yes e) = yes (ctrnᵀ ca (ctrnᵀ (≡→≅ᵀ e) (csymᵀ cb)))
  decide (nbeNfv N ca na) (nbeNfv M cb nb) (no ne) = no (λ c → ne (nf-convᵀ na nb (ctrnᵀ (csymᵀ ca) (ctrnᵀ c cb))))

  both : {A B : RTy Γ} → Maybe (NfOf A) → Maybe (NfOf B) → Maybe (Dec (A ≅ᵀ B))
  both (just a) (just b) = just (decide a b (NfOf.N a ≟Ty NfOf.N b))
  both _        _        = nothing

-- ★ conversion of types, DECIDED by NbE — or nothing (not certified normal)
decConvNbE : (A B : RTy Γ) → Maybe (Dec (A ≅ᵀ B))
decConvNbE A B = both (nbeNf A) (nbeNf B)
