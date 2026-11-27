-- SPIKE: the fragment's renaming agreement as ONE application of the generic
-- theorem (SPIKE-GENERIC-SYNTAX S5, part 2). What the signature writes: its
-- object signature (each shape is `toShape` of the constructor's own fields,
-- in tag order), the position table (`atᵍ`/`atʰ`), and nothing else. Its
-- well-formedness is computed from the fields by one generic function.

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Spec.Base hiding ( _,,_; _×_ )
module tmp.GenSynAgreeFrag (𝒮 : Defs) (wf : WfK 𝒮) where
open import DirectedHoTT.Prelude using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.SynRen 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( varsAt )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( Lt; lt-z; lt-s )
import tmp.GenSyn as G
open import tmp.GenSynFrag using ( K; KCon; Srt; tm; ty; kfields
  ; `lam; `app; `pair; `natrec; `nzero; `nsuc; `ref; `⌜Π⌝; `Π; `Σ; `U; `El; `Nat )
open import tmp.GenSynQuoteFrag using ( ixK )
open import tmp.GenSynAgree 𝒮 wf

sIxK : Srt → ℕ
sIxK ty = 0
sIxK tm = 1

open Agree K sIxK

-- the object signature: each shape is the constructor's fields, in tag order
tyShs : Shapes 5
tyShs = toShape (kfields `Π) ∷ˢʰ toShape (kfields `Σ) ∷ˢʰ toShape (kfields `U)
     ∷ˢʰ toShape (kfields `El) ∷ˢʰ toShape (kfields `Nat) ∷ˢʰ []ˢʰ

tmShs : Shapes 9
tmShs = vʰ ∷ˢʰ toShape (kfields `lam) ∷ˢʰ toShape (kfields `app) ∷ˢʰ toShape (kfields `pair)
     ∷ˢʰ toShape (kfields `natrec) ∷ˢʰ toShape (kfields `nzero) ∷ˢʰ toShape (kfields `nsuc)
     ∷ˢʰ toShape (kfields `ref) ∷ˢʰ toShape (kfields `⌜Π⌝) ∷ˢʰ []ˢʰ

osgK : Sig 2
osgK = tyShs ∷ᵍ tmShs ∷ᵍ []ᵍ

-- well-formedness, from the fields (generic in the field list)
ltS : ∀ s → Lt (sIxK s) 2
ltS ty = lt-z
ltS tm = lt-s lt-z

fok : (fs : List (G.Field Srt)) → FOK 2 (toShape fs)
fok []               = []ᶠ
fok (G.rec s k ∷ fs) = ok-rec (ltS s) ∷ᶠ fok fs
fok (G.nat ∷ fs)     = ok-nat ∷ᶠ fok fs

sok : ∀ {s} (c : KCon s) → ShOK 2 (toShape (kfields c))
sok c = fᵒʰ (fok (kfields c))

okK : SigOK 2 osgK
okK = (sok `Π ∷ᵒˢ sok `Σ ∷ᵒˢ sok `U ∷ᵒˢ sok `El ∷ᵒˢ sok `Nat ∷ᵒˢ []ᵒˢ)
   ∷ᵒᵍ (vᵒʰ ∷ᵒˢ sok `lam ∷ᵒˢ sok `app ∷ᵒˢ sok `pair ∷ᵒˢ sok `natrec ∷ᵒˢ sok `nzero
        ∷ᵒˢ sok `nsuc ∷ᵒˢ sok `ref ∷ᵒˢ sok `⌜Π⌝ ∷ᵒˢ []ᵒˢ)
   ∷ᵒᵍ []ᵒᵍ

-- the position table
cnumK : Srt → ℕ
cnumK ty = 5
cnumK tm = 9

shsK : (s : Srt) → Shapes (cnumK s)
shsK ty = tyShs
shsK tm = tmShs

nGK : (s : Srt) → NthG osgK (sIxK s) (shsK s)
nGK ty = atᵍ 0
nGK tm = atᵍ 1

nShK : ∀ {s} (c : KCon s) → NthSh (shsK s) (ixK c) (toShape (kfields c))
nShK `lam = atʰ 1 ; nShK `app = atʰ 2 ; nShK `pair = atʰ 3 ; nShK `natrec = atʰ 4
nShK `nzero = atʰ 5 ; nShK `nsuc = atʰ 6 ; nShK `ref = atʰ 7 ; nShK `⌜Π⌝ = atʰ 8
nShK `Π = atʰ 0 ; nShK `Σ = atʰ 1 ; nShK `U = atʰ 2 ; nShK `El = atʰ 3 ; nShK `Nat = atʰ 4

OK : ObjSig
OK = record { ix = ixK ; vix = 0 ; nS = 2 ; osg = osgK ; ok = okK ; cnum = cnumK ; shs = shsK
            ; nG = nGK ; nSh = nShK ; nV = atʰ 0 ; vok = varsAt osgK 1 refl }

-- ★ the fragment's renaming agreement: the generic theorem, applied
module RA = Agreeing OK (λ σ → refl) (λ σ → refl) (λ σ → refl) (λ σ → refl)

renAgreeK = RA.agree
