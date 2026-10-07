-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ UNQUOTE, generic in the signature (PLAN-FAITHFUL
-- F6.2, the Lib half).
--
-- A signature's syntax as an AGDA datatype, `STm sg s d` (sort `s`,
-- depth `d`), quoted exactly the way the Knot's constructors build
-- terms (`conₗ k (field , … , unit)`, numerals `num`, variables
-- tags `fzero`/`fsuc`):
--
--     ⌜_⌝ˢ      : STm sg s d → RTm Θ
--     ⌜⌝ˢ-inj   : ⌜ x ⌝ˢ ≡ ⌜ y ⌝ˢ → x ≡ y                 (structural)
--     syn-unquote : ◇ ⊢ t ∷ SK sg s (num d) → IsNormal t →
--                 Σ x. t ≡ ⌜ x ⌝ˢ                       (typed, by fuel)
--
-- So a CLOSED NORMAL term of a syntax is the quotation of a unique tree.
-- A concrete syntax (the Knot) only bridges its own Agda datatype to
-- `STm` — structurally, with no typing.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; _<ˢ?_ )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Lib.SynUnq (𝒮 : KSig) (wf : WfK 𝒮) where

-- ★ PLAN-REF: at a well-formed signature, all its names
private
  𝓃 = KSig.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_; ⊥; ⊥-elim; _⊎_; inj₁; inj₂ )
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( ⟶ᵀ*-El; red→≅ᵀ; ⟶*-dpayᶜ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢-cast )
open import DirectedHoTT.Metatheory.SubjectReduction 𝒮 𝓃 ok using ( gen-nsuc )
open import DirectedHoTT.Metatheory.LogicalRelation 𝒮 using ( IsNormal )
open import DirectedHoTT.Metatheory.Canonicity 𝒮 wf
  using ( canNat; NatShape; ns-zero; ns-suc; sz; _≤_; ≤-refl )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( tag; conₗ; Lt; lt-z; lt-s; selF-β; nth-sub; subC; selF; Nth; [] )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok using ( ⌜_⌝ᵗ; ⌜_⌝ₛ; nth-⌜⌝; nthᵗ-z; nthᵗ-s )
open import DirectedHoTT.Lib.NatNum 𝒮 𝓃 using ( num )
open import DirectedHoTT.Lib.NatFib 𝒮 𝓃 ok using ( fibN-z; fibN-s )
open import DirectedHoTT.Lib.NatCode 𝒮 𝓃 using ( toI; fromI )
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Lib.Decode 𝒮 wf
open import DirectedHoTT.Lib.SynDecode 𝒮 wf
open import DirectedHoTT.Lib.Size 𝒮 wf using ( szp; szˡ; szʳ )

private
  variable
    Θ : Cx
    n c k s d : ℕ

------------------------------------------------------------------------
-- 1. THE TREES, and their quotation.
------------------------------------------------------------------------

data STm (sg : Sig n) : ℕ → ℕ → Set
data SArgs (sg : Sig n) (d : ℕ) : Shape → Set

data STm sg where
  node : {s d c k : ℕ} {shs : Shapes c} {sh : Shape} →
         NthG sg s shs → NthSh shs k sh → SArgs sg d sh → STm sg s d

data SArgs sg d where
  s[]   : SArgs sg d []ʰ
  s-rec : {s k : ℕ} {sh : Shape} → STm sg s (k + d) → SArgs sg d sh → SArgs sg d (rec s k ∷ʰ sh)
  s-nat : {sh : Shape} → ℕ → SArgs sg d sh → SArgs sg d (nat ∷ʰ sh)
  s-cls : {s : ℕ} {sh : Shape} → STm sg s zero → SArgs sg d sh → SArgs sg d (cls s ∷ʰ sh)
  s-v   : (i : ℕ) → Lt i d → SArgs sg d vʰ

⌜_⌝ˢ : {sg : Sig n} → STm sg s d → {Θ : Cx} → RTm Θ
⌜_⌝ᵃ : {sg : Sig n} {sh : Shape} → SArgs sg d sh → {Θ : Cx} → RTm Θ
⌜ node {k = k} _ _ as ⌝ˢ = conₗ k ⌜ as ⌝ᵃ
⌜ s[] ⌝ᵃ        = unit
⌜ s-rec t as ⌝ᵃ = pair ⌜ t ⌝ˢ ⌜ as ⌝ᵃ
⌜ s-nat m as ⌝ᵃ = pair (num m) ⌜ as ⌝ᵃ
⌜ s-cls t as ⌝ᵃ = pair ⌜ t ⌝ˢ ⌜ as ⌝ᵃ
⌜ s-v i _ ⌝ᵃ    = pair (tag i) unit

------------------------------------------------------------------------
-- 2. ★ QUOTATION IS INJECTIVE — structurally.
------------------------------------------------------------------------

private
  con-inj : {a b : RTm Θ} → con a ≡ con b → a ≡ b
  con-inj refl = refl
  pairˡ : {a b a' b' : RTm Θ} → pair a b ≡ pair a' b' → a ≡ a'
  pairˡ refl = refl
  pairʳ : {a b a' b' : RTm Θ} → pair a b ≡ pair a' b' → b ≡ b'
  pairʳ refl = refl
  fsuc-inj : {a b : RTm Θ} → fsuc a ≡ fsuc b → a ≡ b
  fsuc-inj refl = refl
  nsuc-inj : {a b : RTm Θ} → nsuc a ≡ nsuc b → a ≡ b
  nsuc-inj refl = refl

tag-inj : (k k' : ℕ) → tag {Θ} k ≡ tag k' → k ≡ k'
tag-inj zero    zero     _ = refl
tag-inj zero    (suc k') ()
tag-inj (suc k) zero     ()
tag-inj (suc k) (suc k') e = cong suc (tag-inj k k' (fsuc-inj e))

num-inj : (m m' : ℕ) → num {Θ} m ≡ num m' → m ≡ m'
num-inj zero    zero     _ = refl
num-inj zero    (suc m') ()
num-inj (suc m) zero     ()
num-inj (suc m) (suc m') e = cong suc (num-inj m m' (nsuc-inj e))

lt-uniq : {i d : ℕ} (p q : Lt i d) → p ≡ q
lt-uniq lt-z     lt-z     = refl
lt-uniq (lt-s p) (lt-s q) = cong lt-s (lt-uniq p q)

-- the positions are unique (and so are their witnesses)
nthG-uniq : {sg : Sig n} {c c' : ℕ} {shs : Shapes c} {shs' : Shapes c'} (a : NthG sg s shs) (b : NthG sg s shs') →
            _≡_ {A = Σ ℕ (λ c₀ → Σ (Shapes c₀) (NthG sg s))} (c , (shs , a)) (c' , (shs' , b))
nthG-uniq nthᵍ-z     nthᵍ-z     = refl
nthG-uniq (nthᵍ-s a) (nthᵍ-s b) with nthG-uniq a b
... | refl = refl

nthSh-uniq : {shs : Shapes c} {sh sh' : Shape} (a : NthSh shs k sh) (b : NthSh shs k sh') →
             _≡_ {A = Σ Shape (NthSh shs k)} (sh , a) (sh' , b)
nthSh-uniq nthʰ-z     nthʰ-z     = refl
nthSh-uniq (nthʰ-s a) (nthʰ-s b) with nthSh-uniq a b
... | refl = refl

⌜⌝ˢ-inj : {sg : Sig n} (x y : STm sg s d) → ⌜ x ⌝ˢ {Θ} ≡ ⌜ y ⌝ˢ → x ≡ y
⌜⌝ᵃ-inj : {sg : Sig n} {sh : Shape} (as bs : SArgs sg d sh) → ⌜ as ⌝ᵃ {Θ} ≡ ⌜ bs ⌝ᵃ → as ≡ bs
⌜⌝ˢ-inj {Θ = Θ} (node {k = k} ng nh as) (node {k = k'} ng' nh' bs) e
  with tag-inj {Θ} k k' (pairˡ (con-inj e)) | nthG-uniq ng ng'
... | refl | refl with nthSh-uniq nh nh'
...   | refl = cong (node ng nh) (⌜⌝ᵃ-inj as bs (pairʳ (con-inj e)))
⌜⌝ᵃ-inj s[] s[] _ = refl
⌜⌝ᵃ-inj (s-rec t as) (s-rec u bs) e = cong₂ s-rec (⌜⌝ˢ-inj t u (pairˡ e)) (⌜⌝ᵃ-inj as bs (pairʳ e))
⌜⌝ᵃ-inj {Θ = Θ} (s-nat m as) (s-nat m' bs) e = cong₂ s-nat (num-inj {Θ} m m' (pairˡ e)) (⌜⌝ᵃ-inj as bs (pairʳ e))
⌜⌝ᵃ-inj (s-cls t as) (s-cls u bs) e = cong₂ s-cls (⌜⌝ˢ-inj t u (pairˡ e)) (⌜⌝ᵃ-inj as bs (pairʳ e))
⌜⌝ᵃ-inj {Θ = Θ} (s-v i l) (s-v j l') e with tag-inj {Θ} i j (pairˡ e)
... | refl with lt-uniq l l'
...   | refl = refl

------------------------------------------------------------------------
-- 3. Numerals and variables, decoded.
------------------------------------------------------------------------

-- a closed normal natural IS a numeral
nat-unq : {t : RTm ε} → ◇ ⊢ t ∷ El ⌜Nat⌝ → IsNormal t → Σ ℕ (λ m → t ≡ num m)
nat-unq d nrm with canNat (fromI d) (canon (fromI d) nrm)
nat-unq d nrm | ns-zero = zero , refl
nat-unq {t = nsuc t'} d nrm | ns-suc .t' with gen-nsuc (fromI d)
... | (dt , _) with nat-unq (toI dt) (λ r → nrm (ξ-nsuc r))
...   | m , eq = suc m , cong nsuc eq

------------------------------------------------------------------------
-- 4. ★ A CLOSED NORMAL TERM OF A SYNTAX IS A QUOTED TREE.
--    By fuel: the fields are smaller than the node (`sz`).
------------------------------------------------------------------------

-- every sort in range has its constructor list
nthG-of : (sg : Sig k) → Lt s k → Σ ℕ (λ c₀ → Σ (Shapes c₀) (NthG sg s))
nthG-of (shs ∷ᵍ sg) lt-z     = _ , (shs , nthᵍ-z)
nthG-of (_ ∷ᵍ sg)   (lt-s l) with nthG-of sg l
... | c₀ , (shs , ng) = c₀ , (shs , nthᵍ-s ng)

nsucs-num : (k d : ℕ) → nsucs {ε} k (num d) ≡ num (k + d)
nsucs-num zero    d = refl
nsucs-num (suc k) d = cong nsuc (nsucs-num k d)

syn-unq : {sg : Sig n} → SigOK n sg → (f : ℕ) {s d : ℕ} {shs : Shapes c} {t : RTm ε} →
          NthG sg s shs → sz t ≤ f → ◇ ⊢ t ∷ SK sg s (num d) → IsNormal t →
          Σ (STm sg s d) (λ x → t ≡ ⌜ x ⌝ˢ)
args-unq : {sg : Sig n} → SigOK n sg → (f : ℕ) {d : ℕ} {sh : Shape} {p : RTm ε} →
           ShOK n sh → sz p ≤ f → DArgs sg (num d) sh p →
           Σ (SArgs sg d sh) (λ as → p ≡ ⌜ as ⌝ᵃ)

syn-unq ok zero ng () dt nrm
syn-unq ok (suc f) {d = d} ng h dt nrm with syn-dec {d = num d} ng dt nrm
... | k , (sh , (p , (nh , (refl , args))))
  with args-unq ok f (nthSh-ok (nthG-ok ok ng) nh) (szp k p h) args
...   | as , refl = node ng nh as , refl

args-unq ok zero sok () args
args-unq ok (suc f) sok h d[] = s[] , refl
args-unq {n = n} {sg = sg} ok (suc f) {d = d} {sh = rec s k ∷ʰ _} (fᵒʰ (ok-rec lt ∷ᶠ fok)) h (d-rec {a = a} {p = r} da na rest)
  with nthG-of sg lt
... | _ , (_ , ng)
  with syn-unq ok f {d = k + d} ng (szˡ a r h) (⊢-cast (cong (SK sg s) (nsucs-num k d)) da) na
     | args-unq ok f (fᵒʰ fok) (szʳ a r h) rest
...   | x , refl | as , refl = s-rec x as , refl
args-unq ok (suc f) (fᵒʰ (ok-nat ∷ᶠ fok)) h (d-nat {a = a} {p = r} da na rest)
  with nat-unq da na | args-unq ok f (fᵒʰ fok) (szʳ a r h) rest
... | m , refl | as , refl = s-nat m as , refl
args-unq {sg = sg} ok (suc f) (fᵒʰ (ok-cls lt ∷ᶠ fok)) h (d-cls {a = a} {p = r} da na rest)
  with nthG-of sg lt
... | _ , (_ , ng)
  with syn-unq ok f {d = zero} ng (szˡ a r h) da na | args-unq ok f (fᵒʰ fok) (szʳ a r h) rest
...   | x , refl | as , refl = s-cls x as , refl
args-unq ok (suc f) {d = d} vᵒʰ h (d-v da na) with tag-dec da na
... | i , (l , refl) = s-v i l , refl
args-unq ok (suc f) (fᵒʰ ()) h (d-v da na)

-- ★ the theorem, fuel discharged
syn-unquote : {sg : Sig n} → SigOK n sg → {s d : ℕ} {shs : Shapes c} {t : RTm ε} →
          NthG sg s shs → ◇ ⊢ t ∷ SK sg s (num d) → IsNormal t →
          Σ (STm sg s d) (λ x → t ≡ ⌜ x ⌝ˢ)
syn-unquote ok {d = d} {t = t} ng dt nrm = syn-unq ok (sz t) {d = d} ng ≤-refl dt nrm

------------------------------------------------------------------------
-- 5. ★ Quotes are NORMAL: built from introduction forms only.
------------------------------------------------------------------------

tag-normal : (k : ℕ) → IsNormal (tag {Θ} k)
tag-normal zero    ()
tag-normal (suc k) (ξ-fsuc r) = tag-normal k r

num-normal : (m : ℕ) → IsNormal (num {Θ} m)
num-normal zero    ()
num-normal (suc m) (ξ-nsuc r) = num-normal m r

⌜⌝ˢ-normal : {sg : Sig n} (x : STm sg s d) → IsNormal (⌜ x ⌝ˢ {Θ})
⌜⌝ᵃ-normal : {sg : Sig n} {sh : Shape} (as : SArgs sg d sh) → IsNormal (⌜ as ⌝ᵃ {Θ})
⌜⌝ˢ-normal (node {k = k} _ _ as) (ξ-con (ξ-pairˡ r)) = tag-normal k r
⌜⌝ˢ-normal (node _ _ as) (ξ-con (ξ-pairʳ r)) = ⌜⌝ᵃ-normal as r
⌜⌝ᵃ-normal s[] ()
⌜⌝ᵃ-normal (s-rec t as) (ξ-pairˡ r) = ⌜⌝ˢ-normal t r
⌜⌝ᵃ-normal (s-rec t as) (ξ-pairʳ r) = ⌜⌝ᵃ-normal as r
⌜⌝ᵃ-normal (s-nat m as) (ξ-pairˡ r) = num-normal m r
⌜⌝ᵃ-normal (s-nat m as) (ξ-pairʳ r) = ⌜⌝ᵃ-normal as r
⌜⌝ᵃ-normal (s-cls t as) (ξ-pairˡ r) = ⌜⌝ˢ-normal t r
⌜⌝ᵃ-normal (s-cls t as) (ξ-pairʳ r) = ⌜⌝ᵃ-normal as r
⌜⌝ᵃ-normal (s-v i l) (ξ-pairˡ r) = tag-normal i r
⌜⌝ᵃ-normal (s-v i l) (ξ-pairʳ ())
