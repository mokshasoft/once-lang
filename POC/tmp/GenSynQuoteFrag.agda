-- SPIKE: the fragment's ENUMERATION (all a signature writes, three lines per
-- former), and the generic quotation at it: `refl` tests with a negative
-- control, and injectivity as an instance (SPIKE-GENERIC-SYNTAX S5).

{-# OPTIONS --safe #-}
open import DirectedHoTT.Prelude using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Scope using ( Cx; ε; _∙; Var; vz; vs )
import DirectedHoTT.Spec.Syntax as S
open import tmp.GenSyn
open import tmp.GenSynFrag
open import tmp.GenSynQuote
module tmp.GenSynQuoteFrag where

-- tags: the variable is 0 at the term sort, constructors follow
ixK : ∀ {s} → KCon s → ℕ
ixK `lam = 1 ; ixK `app = 2 ; ixK `pair = 3 ; ixK `natrec = 4 ; ixK `nzero = 5
ixK `nsuc = 6 ; ixK `ref = 7 ; ixK `⌜Π⌝ = 8
ixK `Π = 0 ; ixK `Σ = 1 ; ixK `U = 2 ; ixK `El = 3 ; ixK `Nat = 4

cxK : ∀ s → ℕ → Maybe (KCon s)
cxK tm 1 = just `lam ; cxK tm 2 = just `app ; cxK tm 3 = just `pair ; cxK tm 4 = just `natrec
cxK tm 5 = just `nzero ; cxK tm 6 = just `nsuc ; cxK tm 7 = just `ref ; cxK tm 8 = just `⌜Π⌝
cxK ty 0 = just `Π ; cxK ty 1 = just `Σ ; cxK ty 2 = just `U ; cxK ty 3 = just `El ; cxK ty 4 = just `Nat
cxK _ _ = nothing

rtK : ∀ {s} (c : KCon s) → cxK s (ixK c) ≡ just c
rtK `lam = refl ; rtK `app = refl ; rtK `pair = refl ; rtK `natrec = refl ; rtK `nzero = refl
rtK `nsuc = refl ; rtK `ref = refl ; rtK `⌜Π⌝ = refl
rtK `Π = refl ; rtK `Σ = refl ; rtK `U = refl ; rtK `El = refl ; rtK `Nat = refl

EK : Enum K
EK = record { ix = ixK ; cx = cxK ; rt = rtK ; vix = 0 ; vfresh = refl }

open Quote EK

-- closed quotations at the empty scope (pattern synonyms take no implicits)
qTm : RTm ε → S.RTm ε
qTm t = ⌜ t ⌝
qTy : RTy ε → S.RTm ε
qTy A = ⌜ A ⌝

-- the quotation is the Knot's encoding (`Lib/SynUnq`'s), by `refl`
q-lam : qTm (lam (var vz))
      ≡ conₗ 1 (S.pair (conₗ 0 (S.pair S.fzero S.unit)) S.unit)
q-lam = refl

q-Π : qTy (Π U (El (var vz)))
    ≡ conₗ 0 (S.pair (conₗ 2 S.unit) (S.pair (conₗ 3 (S.pair (conₗ 0 (S.pair S.fzero S.unit)) S.unit)) S.unit))
q-Π = refl

q-ref : qTm (ref 2) ≡ conₗ 7 (S.pair (num 2) S.unit)
q-ref = refl

-- injectivity, an instance of the one generic proof
q-inj : ∀ {Γ} (t u : RTm Γ) → ⌜ t ⌝ {Θ = ε} ≡ ⌜ u ⌝ → t ≡ u
q-inj = ⌜⌝-inj
