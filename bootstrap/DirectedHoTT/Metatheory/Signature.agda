-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ A WELL-FORMED SIGNATURE (the checker's), and what
--                      it means for the KERNEL (PLAN-REF, D082).
--
-- ★ `WfSig S`: the signature is a TELESCOPE and well-formedness is context
--   formation — each entry has an ANNOTATED body, typed at its declared
--   type (itself well-formed) in the empty context over the entries
--   BEFORE it, and erasing to the stored body.  Typing over the earlier
--   entries is what makes the signature acyclic: `⊢ᴬref` only reaches the
--   names before it, so a body refers only to earlier entries.
--
-- ★ `wf→K`: it is the KERNEL's context formation (`Spec/SigWf.WfK`) of
--   the erased signature.  Entry n is erased over its prefix
--   (`Metatheory/Erasure`), then moved to the whole signature along the
--   extension (`Metatheory/SigExt`): the prefix agrees with the whole on
--   every name below n.
--
-- ★ CONSERVATIVITY: every kernel theorem holds over a well-formed
--   signature; consistency is the last line.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Signature where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst; Σ; _,_; _×_; ⊤; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc; _==_; _<_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.Signature
open import DirectedHoTT.Spec.SigWf using ( WfUpTo; WfK )
import DirectedHoTT.Spec.Typing as Ty
open import DirectedHoTT.Spec.Base using ( ◇ )
import DirectedHoTT.Spec.TypingA as TA
import DirectedHoTT.Metatheory.Erasure as Er
import DirectedHoTT.Metatheory.SigExt as SigExt

-- ★ CONTEXT FORMATION.  An entry is well-formed over the signature BEFORE
--   it: its declared type well-formed, an annotated body typed at it, and
--   that body erasing to the stored one.
EntryWf : Sig → Entry → Set
EntryWf S e =
  Σ (ATm ε) λ b →
    TA._⊢tyᴬ_ S TA.◇ᴬ (eType e)
  × (TA._⊢ᴬ_∷_ S TA.◇ᴬ b (eType e)
  × (⌈ b ⌉ ≡ eBody e))

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

  lt-suc : (d n : ℕ) → (d < n) ≡ true → (d < suc n) ≡ true
  lt-suc zero    n       e = refl
  lt-suc (suc d) zero    ()
  lt-suc (suc d) (suc n) e = lt-suc d n e

  <ˢ→< : {d n : ℕ} → d <ˢ n → (d < n) ≡ true
  <ˢ→< {d} {suc d} <-here = lt-refl d
    where
    lt-refl : (d : ℕ) → (d < suc d) ≡ true
    lt-refl zero    = refl
    lt-refl (suc d) = lt-refl d
  <ˢ→< {d} {suc n} (<-there p) = lt-suc d n (<ˢ→< p)

lookup-here : (n : ℕ) (T : Tele) (e : Entry) → lookupE (suc n) (T ▸ e) n ≡ e
lookup-here n T e = subst (λ b → pickE b e (lookupE n T n) ≡ e) (sym (==-refl n)) refl

lookup-there : (n : ℕ) (T : Tele) (e : Entry) {d : ℕ} → d <ˢ n → lookupE (suc n) (T ▸ e) d ≡ lookupE n T d
lookup-there n T e {d} p = subst (λ b → pickE b e (lookupE n T d) ≡ lookupE n T d) (sym (<→≠ d n (<ˢ→< p))) refl

------------------------------------------------------------------------
-- ★ `wf→K`: the kernel's context formation.
------------------------------------------------------------------------

-- the telescope (n , T) is a PREFIX of S: S has its names, with its entries
record Prefix (n : ℕ) (T : Tele) (S : Sig) : Set where
  constructor prefix
  field
    pinc   : ∀ {d} → d <ˢ n → d <ˢ Sig.size S
    pagree : ∀ {d} → d <ˢ n → lookupE n T d ≡ lookupE (len S) (tele S) d
open Prefix

-- the prefix of a prefix
shrink : {n : ℕ} {T : Tele} {e : Entry} {S : Sig} → Prefix (suc n) (T ▸ e) S → Prefix n T S
shrink {n} {T} {e} (prefix i a) =
  prefix (λ p → i (<-there p)) (λ {d} p → trans (sym (lookup-there n T e p)) (a (<-there p)))

private
  module Step (n : ℕ) (T : Tele) (S : Sig) (pre : Prefix n T S) where
    S₀ = mkSig n T

    body≡ : ∀ {d} → d <ˢ n → KSig.body (kernel S₀) d ≡ KSig.body (kernel S) d
    body≡ {d} p = trans (kernel-body S₀ d) (trans (cong eBody (pagree pre p)) (sym (kernel-body S d)))

    type≡ : ∀ {d} → d <ˢ n → KSig.type (kernel S₀) d ≡ KSig.type (kernel S) d
    type≡ {d} p = trans (kernel-type S₀ d) (trans (cong (λ x → ⌈ eType x ⌉ᵀ) (pagree pre p)) (sym (kernel-type S d)))

    open SigExt (kernel S₀) (kernel S) (pinc pre) body≡
    open Typed n type≡ public

-- entry n of S, from its annotated derivations over the prefix
entryK : (n : ℕ) (T : Tele) (e : Entry) (S : Sig) → Prefix (suc n) (T ▸ e) S →
         EntryWf (mkSig n T) e → Ty.EntryOK (kernel S) n n
entryK n T e S pre (b , (dA , (db , eq))) =
  Ty.entryOK (subst (λ A → Ty._⊢ty_ (kernel S) n ◇ A) (sym tyS) (ext⊢ty {Γ = ◇} {T = ⌈ eType e ⌉ᵀ} (Er.erase-ty S₀ dA)))
             (subst₂ (λ t A → Ty._⊢_∷_ (kernel S) n ◇ t A) (trans eq (sym bodyS)) (sym tyS) (ext⊢ {Γ = ◇} {t = ⌈ b ⌉} {T = ⌈ eType e ⌉ᵀ} (Er.erase S₀ db)))
  where
  open Step n T S (shrink pre) using ( S₀; ext⊢; ext⊢ty )
  here≡ : lookupE (len S) (tele S) n ≡ e
  here≡ = trans (sym (pagree pre <-here)) (lookup-here n T e)
  tyS : KSig.type (kernel S) n ≡ ⌈ eType e ⌉ᵀ
  tyS = trans (kernel-type S n) (cong (λ x → ⌈ eType x ⌉ᵀ) here≡)
  bodyS : KSig.body (kernel S) n ≡ eBody e
  bodyS = trans (kernel-body S n) (cong eBody here≡)
  subst₂ : {A B : Set} (P : A → B → Set) {a a' : A} {x x' : B} → a ≡ a' → x ≡ x' → P a x → P a' x'
  subst₂ P refl refl h = h

toK : (n : ℕ) (T : Tele) (S : Sig) → Prefix n T S → WfTele n T → WfUpTo (kernel S) n
toK zero    ∅       S pre _              = _
toK (suc n) (T ▸ e) S pre (w , ew) = toK n T S (shrink pre) w , entryK n T e S pre ew

wf→K : (S : Sig) → WfSig S → WfK (kernel S)
wf→K S w = toK (len S) (tele S) S (prefix (λ p → p) (λ p → refl)) w

------------------------------------------------------------------------
-- ★ Conservativity: the kernel's consistency, over any signature.
------------------------------------------------------------------------

consistencyˢ : (S : Sig) → WfSig S → {t : ATm ε} →
               TA._⊢ᴬ_∷_ S TA.◇ᴬ t base → ⊥
consistencyˢ S w = Er.consistencyᴬ S (wf→K S w)
