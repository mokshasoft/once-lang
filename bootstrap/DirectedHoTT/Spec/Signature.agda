-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE SIGNATURE, as the CHECKER sees it.
--
-- ★ WHAT IT IS.  Entries `0 … size-1`, each a closed body of a declared
--   closed type.  The declared types are ANNOTATED (`ATy`): the checker
--   types `ref d` by them (`Spec/TypingA.⊢ᴬref`).  The bodies are kernel
--   terms.
--
-- ★ THE KERNEL'S VIEW (PLAN-REF, D082).  `kernel S` erases the declared
--   types: it is the definition context the kernel reduces and types
--   under (`Spec/Reduction`, `Spec/Typing`).  A reference is a projection
--   from it, in both layers.
--
-- ★ A TELESCOPE (D081): entry n is checked over the entries before it;
--   extending a signature is context extension, so a signature built in
--   one module is extended in another without re-checking it
--   (`Metatheory/Signature.WfSig` is the context-formation rule).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.Signature where
open import normalizer.Syntax.Types using ( _≡_; refl; cong; ¬_ )
open import Agda.Builtin.Nat using ( zero; suc; _==_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.Syntax public using ( _<ˢ_; <-here; <-there; <ˢ-zero; _<ˢ?_ )

record Entry : Set where
  constructor ⟨_∣_⟩
  field
    eType : ATy ε
    eBody : RTm ε
open Entry public

data Tele : Set where
  ∅   : Tele
  _▸_ : Tele → Entry → Tele
infixl 5 _▸_

-- entry d of a telescope of length n (entries counted from the first)
pickE : Bool → Entry → Entry → Entry
pickE true  x y = x
pickE false x y = y

lookupE : ℕ → Tele → ℕ → Entry
lookupE (suc n) (T ▸ e) d = pickE (d == n) e (lookupE n T d)
lookupE zero    _       d = ⟨ Unit ∣ unit ⟩
lookupE (suc n) ∅       d = ⟨ Unit ∣ unit ⟩

record Sig : Set where
  constructor mkSig
  field
    len  : ℕ
    tele : Tele
  -- what the checker consults (`open Sig S`)
  size : ℕ
  size = len
  type : ℕ → ATy ε
  type d = eType (lookupE len tele d)
  body : ℕ → RTm ε
  body d = eBody (lookupE len tele d)
open Sig public using ( len; tele )

∅ˢ : Sig
∅ˢ = mkSig 0 ∅

-- extend by one entry
_▸ˢ_ : Sig → Entry → Sig
S ▸ˢ e = mkSig (suc (len S)) (tele S ▸ e)
infixl 5 _▸ˢ_


------------------------------------------------------------------------
-- ★ The kernel's signature: the declared types erased.
------------------------------------------------------------------------

kEntry : Entry → KEntry
kEntry e = ⟨ ⌈ eType e ⌉ᵀ ∣ eBody e ⟩

kTele : Tele → KTele
kTele ∅       = ∅
kTele (T ▸ e) = kTele T ▸ kEntry e

kernel : Sig → KSig
kernel S = mkK (len S) (kTele (tele S))

-- a lookup in the kernel's view is the erased lookup
private
  pick-k : (b : Bool) (x y : Entry) → pickK b (kEntry x) (kEntry y) ≡ kEntry (pickE b x y)
  pick-k true  x y = refl
  pick-k false x y = refl

  lookup-k : (n : ℕ) (T : Tele) (d : ℕ) → lookupK n (kTele T) d ≡ kEntry (lookupE n T d)
  lookup-k (suc n) (T ▸ e) d with lookupK n (kTele T) d | lookup-k n T d
  ... | _ | refl = pick-k (d == n) e (lookupE n T d)
  lookup-k zero    ∅       d = refl
  lookup-k zero    (T ▸ e) d = refl
  lookup-k (suc n) ∅       d = refl

kernel-type : (S : Sig) (d : ℕ) → KSig.type (kernel S) d ≡ ⌈ Sig.type S d ⌉ᵀ
kernel-type S d = cong kType (lookup-k (len S) (tele S) d)

kernel-body : (S : Sig) (d : ℕ) → KSig.body (kernel S) d ≡ Sig.body S d
kernel-body S d = cong kBody (lookup-k (len S) (tele S) d)
