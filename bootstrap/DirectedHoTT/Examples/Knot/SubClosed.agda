------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ SUBSTITUTION IS THE IDENTITY ON THE CLOSED SORTS.
-- `Knot/RenClosed`'s twin, and the SAME seven rows.
--
-- ⚠ THE ONLY DIFFERENCE BETWEEN THE TWO FILES IS THE **FORD** CHAIN.
--   `kaPick` is the identity at the renaming instantiation
--   (`renFordMap fi b p = p`), so a ford is one projection there; here it
--   is a `fordMapK` jsub and TWO `jsub-refl`s fire, because `symN` is
--   itself a `jsub`.  Every recursive and pinned slot is character-for-
--   character the same.
--
-- ★ AND IT IS STILL SEVEN ROWS, for the same reason: `cDCon-kap`'s `RTy ε`
--   and `cIDesc-cons`'s `ICon (ε ∙)` sit at CLOSED indices (`lit(0)`,
--   `lit(1)`), so `decSubIx` pins them and neither substitution nor
--   renaming ever descends into an `RTy`, an `RTm` or an `ICon` from here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SubClosed where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; RTy; Desc; dnil; _◃_; DCon; dι; dρ; dκ
        ; IDesc; inil; _◂_; ICon; app; pair; icon; idrefl; ⌜Nat⌝; unit )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; βfst; βsnd; jsub-refl )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst; ⟶*-snd
        ; ⟶*-ielimᵗ; ⟶*-ielimⁱ; ⟶*-jsubᵖ )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.ISub using ( ttsd )
open import DirectedHoTT.Examples.Knot.Map using ( enDesc; enDCon; enTy; enIDesc; enICon )
open import DirectedHoTT.Examples.Knot.Sorts using ( num; sDesc; sDCon; sIDesc )
open import DirectedHoTT.Examples.Knot.SubApp using ( subAtK )
open import DirectedHoTT.Examples.Knot.SubRed using ( sub-head-red )

infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
done       » q = q
(step r p) » q = step r (p » q)

id-dnil : {Θ : Cx} (n m : ℕ) (σ : RTm Θ) → 
          subAtK sDesc (num n) (num m) σ (enDesc dnil) ⟶* enDesc {Θ} dnil
id-dnil n m σ  =
  sub-head-red 41 ttsd ttsd refl
               sDesc (num n) (num m) σ (pair (idrefl ⌜Nat⌝ sDesc) unit) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-fst done » step (βfst _ _) done)) »
     ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
     step (jsub-refl _ _ _ _) done))

id-cons : {Θ : Cx} (n m : ℕ) (σ : RTm Θ) → (c : DCon) (d : Desc) →
          ({m' : ℕ} {σ' : RTm Θ} →
             subAtK sDCon (num n) (num m') σ' (enDCon c) ⟶* enDCon {Θ} c) →
          ({m' : ℕ} {σ' : RTm Θ} →
             subAtK sDesc (num n) (num m') σ' (enDesc d) ⟶* enDesc {Θ} d) →
          subAtK sDesc (num n) (num m) σ (enDesc (c ◃ d)) ⟶* enDesc {Θ} (c ◃ d)
id-cons n m σ c d ihc ihd =
  sub-head-red 42 ttsd ttsd refl
               sDesc (num n) (num m) σ (pair (enDCon c) (pair (enDesc d) (pair (idrefl ⌜Nat⌝ sDesc) unit))) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst done » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst done » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihc)) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihd))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
     step (jsub-refl _ _ _ _) done))))

id-dι : {Θ : Cx} (n m : ℕ) (σ : RTm Θ) → 
          subAtK sDCon (num n) (num m) σ (enDCon dι) ⟶* enDCon {Θ} dι
id-dι n m σ  =
  sub-head-red 43 ttsd ttsd refl
               sDCon (num n) (num m) σ (pair (idrefl ⌜Nat⌝ sDCon) unit) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-fst done » step (βfst _ _) done)) »
     ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
     step (jsub-refl _ _ _ _) done))

id-dρ : {Θ : Cx} (n m : ℕ) (σ : RTm Θ) → (c : DCon) →
          ({m' : ℕ} {σ' : RTm Θ} →
             subAtK sDCon (num n) (num m') σ' (enDCon c) ⟶* enDCon {Θ} c) →
          subAtK sDCon (num n) (num m) σ (enDCon (dρ c)) ⟶* enDCon {Θ} (dρ c)
id-dρ n m σ c ihc =
  sub-head-red 44 ttsd ttsd refl
               sDCon (num n) (num m) σ (pair (enDCon c) (pair (idrefl ⌜Nat⌝ sDCon) unit)) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst done » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst done » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihc)) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
     step (jsub-refl _ _ _ _) done)))

id-dκ : {Θ : Cx} (n m : ℕ) (σ : RTm Θ) → (A : RTy ε) (c : DCon) →
          ({m' : ℕ} {σ' : RTm Θ} →
             subAtK sDCon (num n) (num m') σ' (enDCon c) ⟶* enDCon {Θ} c) →
          subAtK sDCon (num n) (num m) σ (enDCon (dκ A c)) ⟶* enDCon {Θ} (dκ A c)
id-dκ n m σ A c ihc =
  sub-head-red 45 ttsd ttsd refl
               sDCon (num n) (num m) σ (pair (enTy A) (pair (enDCon c) (pair (idrefl ⌜Nat⌝ sDCon) unit))) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-fst done » step (βfst _ _) done)) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihc))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
     step (jsub-refl _ _ _ _) done))))

id-inil : {Θ : Cx} (n m : ℕ) (σ : RTm Θ) → 
          subAtK sIDesc (num n) (num m) σ (enIDesc inil) ⟶* enIDesc {Θ} inil
id-inil n m σ  =
  sub-head-red 46 ttsd ttsd refl
               sIDesc (num n) (num m) σ (pair (idrefl ⌜Nat⌝ sIDesc) unit) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-fst done » step (βfst _ _) done)) »
     ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
     step (jsub-refl _ _ _ _) done))

id-icons : {Θ : Cx} (n m : ℕ) (σ : RTm Θ) → (C : ICon (ε ∙)) (E : IDesc) →
          ({m' : ℕ} {σ' : RTm Θ} →
             subAtK sIDesc (num n) (num m') σ' (enIDesc E) ⟶* enIDesc {Θ} E) →
          subAtK sIDesc (num n) (num m) σ (enIDesc (C ◂ E)) ⟶* enIDesc {Θ} (C ◂ E)
id-icons n m σ C E ihE =
  sub-head-red 47 ttsd ttsd refl
               sIDesc (num n) (num m) σ (pair (enICon C) (pair (enIDesc E) (pair (idrefl ⌜Nat⌝ sIDesc) unit))) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-fst done » step (βfst _ _) done)) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihE))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
     step (jsub-refl _ _ _ _) done))))

------------------------------------------------------------------------
-- ★ THE KNOT TIED — `Knot/RenClosed`'s shape exactly.  ⚠ The only
--   difference between the two files is the FORD chain: `kaPick` is the
--   identity at the renaming instance and a `fordMapK` jsub here.
------------------------------------------------------------------------

mutual
  sub-Desc-id : {Θ : Cx} (n m : ℕ) (σ : RTm Θ) (D : Desc) →
                subAtK sDesc (num n) (num m) σ (enDesc D) ⟶* enDesc {Θ} D
  sub-Desc-id n m σ dnil    = id-dnil n m σ
  sub-Desc-id n m σ (c ◃ d) =
    id-cons n m σ c d (λ {m'} {σ'} → sub-DCon-id n m' σ' c)
                      (λ {m'} {σ'} → sub-Desc-id n m' σ' d)

  sub-DCon-id : {Θ : Cx} (n m : ℕ) (σ : RTm Θ) (c : DCon) →
                subAtK sDCon (num n) (num m) σ (enDCon c) ⟶* enDCon {Θ} c
  sub-DCon-id n m σ dι       = id-dι n m σ
  sub-DCon-id n m σ (dρ c)   = id-dρ n m σ c (λ {m'} {σ'} → sub-DCon-id n m' σ' c)
  sub-DCon-id n m σ (dκ A c) = id-dκ n m σ A c (λ {m'} {σ'} → sub-DCon-id n m' σ' c)

sub-IDesc-id : {Θ : Cx} (n m : ℕ) (σ : RTm Θ) (E : IDesc) →
               subAtK sIDesc (num n) (num m) σ (enIDesc E) ⟶* enIDesc {Θ} E
sub-IDesc-id n m σ inil    = id-inil n m σ
sub-IDesc-id n m σ (C ◂ E) = id-icons n m σ C E (λ {m'} {σ'} → sub-IDesc-id n m' σ' E)
