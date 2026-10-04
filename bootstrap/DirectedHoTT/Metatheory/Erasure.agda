-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ ERASURE IS SOUND: the annotated kernel means the
--                      unannotated one.  (PLAN-BIDI §3d)
--
--       erase : Γ ⊢ᴬ t ∷ A → ⌈ Γ ⌉ᶜ ⊢ ⌈ t ⌉ ∷ ⌈ A ⌉ᵀ
--
-- ★ Over a signature: an annotated `ref d` erases to the kernel's
--   `ref d (body d)`, typed by `⊢ref` from the body's derivation.  The
--   hypothesis `SigOK` (each erased body has its erased declared type)
--   comes from `Metatheory/Signature`'s `WfSig`.
--
-- ★ THIS IS THE WHOLE BRIDGE.  Every metatheorem of `RTm` now applies to
--   the annotated kernel through it — consistency is below, one line.
--   Conversion needs no bridge at all: `⊢ᴬconv` IS `⊢conv` on erasures.
--
-- ★ The only content is substitution: a rule whose conclusion substitutes
--   into an `ATy` erases to the `⊢` rule whose conclusion substitutes into
--   the erasure — `era-subTy`/`era-subTm`, stated against a pointwise-equal
--   `RTm` substitution, close each such case with one cast.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst; ⊥ )
open import Agda.Builtin.Nat using ( zero )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.Signature using ( Sig; SigOK )
open import DirectedHoTT.Metatheory.TySub using ( sub-lemma )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢-cast )
open import DirectedHoTT.Metatheory.Canonicity using ( consistency )
module DirectedHoTT.Metatheory.Erasure (S : Sig) (ok : SigOK S) where
open Sig S
open Era body
open import DirectedHoTT.Spec.AnnotatedDesc body
open import DirectedHoTT.Spec.TypingA S

private
  variable
    Γ : ACtx

erase-∋ : {x : Var ⌊ Γ ⌋ᴬ} {A : ATy ⌊ Γ ⌋ᴬ} → Γ ∋ᴬ x ∷ A → ⌈ Γ ⌉ᶜ ∋ x ∷ ⌈ A ⌉ᵀ
erase-∋ {Γ = Γ ▹ᴬ A} (hereᴬ {A = A}) =
  subst (λ Z → ⌈ Γ ▹ᴬ A ⌉ᶜ ∋ vz ∷ Z) (sym (era-renTy vs A)) (here {A = ⌈ A ⌉ᵀ})
erase-∋ {Γ = Γ ▹ᴬ B} (thereᴬ {A = A} {x = x} v) =
  subst (λ Z → ⌈ Γ ▹ᴬ B ⌉ᶜ ∋ vs x ∷ Z) (sym (era-renTy vs A))
        (there {A = ⌈ A ⌉ᵀ} {B = ⌈ B ⌉ᵀ} (erase-∋ v))

erase    : {t : ATm ⌊ Γ ⌋ᴬ} {A : ATy ⌊ Γ ⌋ᴬ} → Γ ⊢ᴬ t ∷ A → ⌈ Γ ⌉ᶜ ⊢ ⌈ t ⌉ ∷ ⌈ A ⌉ᵀ
erase-ty : {A : ATy ⌊ Γ ⌋ᴬ} → Γ ⊢tyᴬ A → ⌈ Γ ⌉ᶜ ⊢ty ⌈ A ⌉ᵀ
-- ★ the motive context erases to `motCtx` up to the two weakenings
motCtx-era : {Γ : ACtx} {I D : ATm ⌊ Γ ⌋ᴬ} {M : RTy ((⌊ Γ ⌋ᴬ ∙) ∙)} →
             ⌈ motCtxᴬ Γ I D ⌉ᶜ ⊢ty M → motCtx ⌈ Γ ⌉ᶜ ⌈ I ⌉ ⌈ D ⌉ ⊢ty M
motCtx-era {Γ} {I} {D} {M} d =
  subst (λ Z → ((⌈ Γ ⌉ᶜ ▹ El ⌈ I ⌉) ▹ Z) ⊢ty M)
        (cong₂' (era-renTm vs I) (era-renTm vs D)) d
  where
  cong₂' : ∀ {a a' b b'} → a ≡ a' → b ≡ b' → IMu a b (var vz) ≡ IMu a' b' (var vz)
  cong₂' refl refl = refl

erase (⊢ᴬvar v) = ⊢var (erase-∋ v)
erase (⊢ᴬlam dA d) = ⊢lam (erase-ty dA) (erase d)
erase (⊢ᴬapp {B = B} {u = u} d₁ d₂) =
  ⊢-cast (sym (sub1 u B)) (⊢app (erase d₁) (erase d₂))
erase (⊢ᴬpair {B = B} {a = a} _ dB da db) =
  ⊢pair (erase-ty dB) (erase da) (⊢-cast (sub1 a B) (erase db))
erase (⊢ᴬabsurd dc de) = ⊢absurd (erase dc) (erase de)
erase (⊢ᴬordtr da dt du dp dq) =
  ⊢ordtr (erase da) (erase dt) (erase du) (erase dp) (erase dq)
erase (⊢ᴬfst d) = ⊢fst (erase d)
erase (⊢ᴬsnd {B = B} {p = p} d) = ⊢-cast (sym (sub1 (fst p) B)) (⊢snd (erase d))
erase ⊢ᴬ⌜base⌝ = ⊢⌜base⌝
erase (⊢ᴬ⌜Π⌝ dc dd) = ⊢⌜Π⌝ (erase dc) (erase dd)
erase (⊢ᴬ⌜Σ⌝ dc dd) = ⊢⌜Σ⌝ (erase dc) (erase dd)
erase (⊢ᴬ⌜Hom⌝ dc da db) = ⊢⌜Hom⌝ (erase dc) (erase da) (erase db)
erase (⊢ᴬhrefl dc dt) = ⊢hrefl (erase dc) (erase dt)
erase (⊢ᴬtrU dt du dp de) = ⊢trU (erase dt) (erase du) (erase dp) (erase de)
erase (⊢ᴬtr {c = c} {a = a} {t = t} {u = u} dA dc da dvz nn o₁ o₂ dt du dp de) =
  ⊢-cast (cong El (sym (sub1ᵗ u (⌜Hom⌝ c a (var vz)))))
    (⊢tr (erase dc) (erase da) (erase dvz) nn o₁ o₂ (erase dt) (erase du) (erase dp)
         (⊢-cast (cong El (sub1ᵗ t (⌜Hom⌝ c a (var vz)))) (erase de)))
erase (⊢ᴬap {cB = cB} {b = b} {t = t} {u = u} dcA fl dcB db dt du dp) =
  ⊢-cast (cong₂' (sym (sub1ᵗ t b)) (sym (sub1ᵗ u b)))
    (⊢ap (erase dcA) fl (erase dcB)
         (⊢-cast (cong El (era-renTm vs cB)) (erase db))
         (erase dt) (erase du) (erase dp))
  where
  cong₂' : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → Hom (El ⌈ cB ⌉) x y ≡ Hom (El ⌈ cB ⌉) x' y'
  cong₂' refl refl = refl
erase (⊢ᴬ⌜Id⌝ dc da db) = ⊢⌜Id⌝ (erase dc) (erase da) (erase db)
erase ⊢ᴬ⌜Nat⌝ = ⊢⌜Nat⌝
erase (⊢ᴬ⌜IMu⌝ {I = I} dI dD di) = ⊢⌜IMu⌝ (erase dI) (⊢-cast (era-DescF I) (erase dD)) (erase di)
erase (⊢ᴬ⌜Fin⌝ dn) = ⊢⌜Fin⌝ (erase dn)
erase (⊢ᴬdι dI) = ⊢dι (erase dI)
erase (⊢ᴬdσ {I = I} {S = S} dI dS df) =
  ⊢dσ (erase dI) (erase dS)
      (⊢-cast (cong (λ z → Π (El ⌈ S ⌉) (Desc z)) (era-renTm vs I)) (erase df))
erase (⊢ᴬdρ dI dj dC) = ⊢dρ (erase dI) (erase dj) (erase dC)
erase (⊢ᴬdpay {I = I} dI dD dC) = ⊢dpay (erase dI) (⊢-cast (era-DescF I) (erase dD)) (erase dC)
erase (⊢ᴬcon {I = I} dI dD di dp) = ⊢con (erase dI) (⊢-cast (era-DescF I) (erase dD)) (erase di) (erase dp)
erase (⊢ᴬdih {I = I} {D = D} {M = M} dI dD dM de dC dp) =
  ⊢dih (erase dI) (⊢-cast (era-DescF I) (erase dD)) (motCtx-era {I = I} {D = D} (erase-ty dM)) (⊢-cast (era-MethTy I D M) (erase de))
       (erase dC) (erase dp)
erase (⊢ᴬielim {I = I} {D = D} {M = M} {i = i} {t = t} dI dD dM de di dt) =
  ⊢-cast (sym (era-iinst i t M))
    (⊢ielim (erase dI) (⊢-cast (era-DescF I) (erase dD)) (motCtx-era {I = I} {D = D} (erase-ty dM)) (⊢-cast (era-MethTy I D M) (erase de))
            (erase di) (erase dt))
erase (⊢ᴬfzero dn) = ⊢fzero (erase dn)
erase (⊢ᴬfsuc _ d) = ⊢fsuc (erase d)
erase (⊢ᴬfcase {n = n} {P = P} {t = t} _ dP dt da db) =
  ⊢-cast (sym (sub1 t P))
    (⊢fcase (erase-ty dP) (erase dt) (⊢-cast (sub1 (fzero n) P) (erase da))
            (⊢-cast (era-subTy (fsucSᴬ n) fsucS (era-fsucS n) P) (erase db)))
erase (⊢ᴬfcase0 {P = P} {t = t} dP dt) =
  ⊢-cast (sym (sub1 t P)) (⊢fcase0 (erase-ty dP) (erase dt))
erase (⊢ᴬpsplit {A = A} {B = B} {P = P} {q = q} dA dB dP dq db) =
  ⊢-cast (sym (sub1 q P))
    (⊢psplit (erase-ty dA) (erase-ty dB) (erase-ty dP) (erase dq)
             (⊢-cast (era-subTy (pairSᴬ A B) pairS (era-pairS A B) P) (erase db)))
erase ⊢ᴬ⌜Unit⌝ = ⊢⌜Unit⌝
erase (⊢ᴬidrefl dc dt) = ⊢idrefl (erase dc) (erase dt)
erase (⊢ᴬjsub {d = d} {t = t} {u = u} dA dd dt du dp de) =
  ⊢-cast (cong El (sym (sub1ᵗ u d)))
    (⊢jsub (erase dd) (erase dt) (erase du) (erase dp)
           (⊢-cast (cong El (sub1ᵗ t d)) (erase de)))
erase ⊢ᴬunit = ⊢unit
erase ⊢ᴬnzero = ⊢nzero
erase (⊢ᴬnsuc d) = ⊢nsuc (erase d)
erase (⊢ᴬnatrec {M = M} {n = n} dM dz ds dn) =
  ⊢-cast (sym (sub1 n M))
    (⊢natrec (erase-ty dM)
             (⊢-cast (sub1 nzero M) (erase dz))
             (⊢-cast (era-subTy nrsᴬ nrs nrs-era M) (erase ds))
             (erase dn))
-- ★ a reference erases to the kernel's reference WITH the signature's
--   body, typed by that body's derivation (`SigOK`)
erase (⊢ᴬref {d = d} p) = ⊢-cast (sym (era-εwkTy (type d))) (⊢ref (ok p))
erase (⊢ᴬconv d c) = ⊢conv (erase d) c

erase-ty tyᴬ-base = ty-base
erase-ty tyᴬ-U    = ty-U
erase-ty (tyᴬ-Π dA dB) = ty-Π (erase-ty dA) (erase-ty dB)
erase-ty (tyᴬ-Σ dA dB) = ty-Σ (erase-ty dA) (erase-ty dB)
erase-ty (tyᴬ-El dc) = ty-El (erase dc)
erase-ty (tyᴬ-Id dA dt du) = ty-Id (erase-ty dA) (erase dt) (erase du)
erase-ty tyᴬ-Unit = ty-Unit
erase-ty tyᴬ-Nat  = ty-Nat
erase-ty (tyᴬ-IMu {I = I} dI dD di) = ty-IMu (erase dI) (⊢-cast (era-DescF I) (erase dD)) (erase di)
erase-ty (tyᴬ-Desc dI) = ty-Desc (erase dI)
erase-ty (tyᴬ-DIh {I = I} {D = D} dI dD dM dC dp) =
  ty-DIh (erase dI) (⊢-cast (era-DescF I) (erase dD)) (motCtx-era {I = I} {D = D} (erase-ty dM)) (erase dC) (erase dp)
erase-ty (tyᴬ-Fin dn) = ty-Fin (erase dn)
erase-ty (tyᴬ-Hom dA dt du) = ty-Hom (erase-ty dA) (erase dt) (erase du)

------------------------------------------------------------------------
-- ★ The first transferred theorem: the annotated kernel is CONSISTENT.
------------------------------------------------------------------------

consistencyᴬ : {t : ATm ε} → ◇ᴬ ⊢ᴬ t ∷ base → ⊥
consistencyᴬ d = consistency (erase d)
