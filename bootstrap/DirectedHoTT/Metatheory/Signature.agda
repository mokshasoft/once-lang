-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ A WELL-FORMED SIGNATURE, and CONSERVATIVITY.
--                      (PLAN-BIDI §2-bis, S5 — design (ii), route B)
--
-- ★ `WfSig S`: the signature is a TELESCOPE and well-formedness is context
--   formation — each entry has an ANNOTATED body, typed at its declared
--   type in the empty context over the entries BEFORE it, whose erasure is
--   the stored body.  Typing over the earlier entries is what makes the
--   signature acyclic: a body refers only to earlier entries.
--
-- ★ `wf→ok`: a well-formed signature satisfies `SigOK`, the hypothesis of
--   δ-elimination (`Metatheory/Erasure`).  By induction on the entries:
--   entry `n` is erased by `Erasure` over the telescope before it, whose
--   `SigOK` is the induction hypothesis; its references lie below `n`, so
--   its erasure is the same over the extended telescope (`era-agree`).  No new metatheory: the kernel's proofs are
--   reused as they are.
--
-- ★ CONSERVATIVITY, the payoff: every kernel theorem holds over every
--   well-formed signature.  Consistency is below, one line.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Signature where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; cong; subst; Σ; _,_; _×_; ⊤; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc; _==_; _<_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Metatheory.SigBelow using ( below; belowᵀ; Agree; era-agreeᵀ; mono-belowᵀ; up-suc; lt-suc )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing using ( ◇; _⊢_∷_ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.Signature
import DirectedHoTT.Spec.TypingA as TA
import DirectedHoTT.Metatheory.Erasure as Er

-- ★ CONTEXT FORMATION.  An entry is well-formed over the signature BEFORE
--   it: an annotated body typed at the declared type, whose erasure is the
--   stored body, and whose references (body and type) lie below — the
--   bound as CHECKED DATA (`Metatheory/SigBelow`), so that erasure over any
--   extension of the signature agrees with erasure over this one.
EntryWf : Sig → Entry → Set
EntryWf S e =
  Σ (ATm ε) λ b →
    TA._⊢ᴬ_∷_ S TA.◇ᴬ b (eType e)
  × ((Era.⌈_⌉ (Sig.body S) b ≡ eBody e)
  × ((below (len S) b ≡ true) × (belowᵀ (len S) (eType e) ≡ true)))

-- a telescope of length n, every entry well-formed over the ones before
WfTele : ℕ → Tele → Set
WfTele zero    ∅       = ⊤
WfTele (suc n) (T ▸ e) = WfTele n T × EntryWf (mkSig n T) e
WfTele zero    (T ▸ e) = ⊥
WfTele (suc n) ∅       = ⊥

-- ★ extending a well-formed signature is ONE more entry: `WfSig (S ▸ˢ e)`
--   is `WfSig S × EntryWf S e` definitionally, so a signature checked in one
--   module is extended in another without re-checking it.
WfSig : Sig → Set
WfSig S = WfTele (len S) (tele S)

------------------------------------------------------------------------
-- Lookups in an extended telescope.
------------------------------------------------------------------------

private
  ==-refl : (n : ℕ) → (n == n) ≡ true
  ==-refl zero    = refl
  ==-refl (suc n) = ==-refl n

  <→≠ : (d n : ℕ) → (d < n) ≡ true → (d == n) ≡ false
  <→≠ zero    zero    ()
  <→≠ zero    (suc n) e = refl
  <→≠ (suc d) zero    ()
  <→≠ (suc d) (suc n) e = <→≠ d n e

  <ˢ→< : {d n : ℕ} → d <ˢ n → (d < n) ≡ true
  <ˢ→< {d} {suc d} <-here = lt-refl d
    where
    lt-refl : (d : ℕ) → (d < suc d) ≡ true
    lt-refl zero    = refl
    lt-refl (suc d) = lt-refl d
  <ˢ→< {d} {suc n} (<-there p) = lt-suc d n (<ˢ→< p)

lookup-here : (n : ℕ) (T : Tele) (e : Entry) → lookupE (suc n) (T ▸ e) n ≡ e
lookup-here n T e = subst (λ b → pickE b e (lookupE n T n) ≡ e) (sym (==-refl n)) refl

lookup-there : (n : ℕ) (T : Tele) (e : Entry) (d : ℕ) → (d < n) ≡ true → lookupE (suc n) (T ▸ e) d ≡ lookupE n T d
lookup-there n T e d p = subst (λ b → pickE b e (lookupE n T d) ≡ lookupE n T d) (sym (<→≠ d n p)) refl

-- the extended body table agrees with the old one below n
agree-ext : (n : ℕ) (T : Tele) (e : Entry) →
            Agree n (Sig.body (mkSig (suc n) (T ▸ e))) (Sig.body (mkSig n T))
agree-ext n T e d p = cong eBody (lookup-there n T e d p)

-- every declared type of a well-formed telescope lies below its length
belowTy : (n : ℕ) (T : Tele) → WfTele n T → {d : ℕ} → d <ˢ n → belowᵀ n (Sig.type (mkSig n T) d) ≡ true
belowTy (suc n) (T ▸ e) (w , (b , (db , (eq , (bb , bt))))) {d} <-here =
  subst (λ x → belowᵀ (suc n) (eType x) ≡ true) (sym (lookup-here n T e)) (mono-belowᵀ {n = n} {m = suc n} (up-suc n) (eType e) bt)
belowTy (suc n) (T ▸ e) (w , _) {d} (<-there p) =
  subst (λ x → belowᵀ (suc n) (eType x) ≡ true) (sym (lookup-there n T e d (<ˢ→< p)))
        (mono-belowᵀ {n = n} {m = suc n} (up-suc n) (eType (lookupE n T d)) (belowTy n T w p))

------------------------------------------------------------------------
-- ★ `wf→ok`: every entry erases to a closed kernel term of its type.
------------------------------------------------------------------------

okTele : (n : ℕ) (T : Tele) → WfTele n T → SigOK (mkSig n T)
okTele (suc n) (T ▸ e) (w , (b , (db , (eq , (bb , bt))))) {d} <-here =
  subst (λ x → ◇ ⊢ eBody x ∷ Era.⌈_⌉ᵀ (Sig.body S') (eType x)) (sym (lookup-here n T e))
    (subst (λ A → ◇ ⊢ eBody e ∷ A) (sym (era-agreeᵀ n (agree-ext n T e) (eType e) bt))
      (subst (λ t → ◇ ⊢ t ∷ Era.⌈_⌉ᵀ (Sig.body S₀) (eType e)) eq
        (Er.erase S₀ (okTele n T w) db)))
  where
  S₀ = mkSig n T
  S' = mkSig (suc n) (T ▸ e)
okTele (suc n) (T ▸ e) (w , _) {d} (<-there p) =
  subst (λ x → ◇ ⊢ eBody x ∷ Era.⌈_⌉ᵀ (Sig.body S') (eType x)) (sym (lookup-there n T e d (<ˢ→< p)))
    (subst (λ A → ◇ ⊢ Sig.body S₀ d ∷ A) (sym (era-agreeᵀ n (agree-ext n T e) _ (belowTy n T w p)))
      (okTele n T w p))
  where
  S₀ = mkSig n T
  S' = mkSig (suc n) (T ▸ e)

wf→ok : (S : Sig) → WfSig S → SigOK S
wf→ok S w = okTele (len S) (tele S) w

------------------------------------------------------------------------
-- ★ Conservativity: the kernel's consistency, over any signature.
------------------------------------------------------------------------

consistencyˢ : (S : Sig) → WfSig S → {t : ATm ε} →
               TA._⊢ᴬ_∷_ S TA.◇ᴬ t base → ⊥
consistencyˢ S w = Er.consistencyᴬ S (wf→ok S w)
