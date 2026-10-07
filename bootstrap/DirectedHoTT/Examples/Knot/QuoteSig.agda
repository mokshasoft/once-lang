-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ QUOTING A SIGNATURE (PLAN-REF K2): `quoteDefs 𝒯`,
-- an inhabitant of `⌜QSig⌝` (`Knot/QSig`), and its lookups.
--
--   quoteDefs 𝒯 = (size , λd. sel types d , λd. sel bodies d)
--
-- `sel f e r x` selects among `r` closed entries by a chain of `natrec`s,
-- each one SHIFTING the entry function (`f ∘ suc`), so a lookup is one
-- induction on the name:
--
--   typesQ  (quoteDefs 𝒯) (num d) ⟶* quoteTy (type 𝒯 d)     (every d)
--   bodiesQ (quoteDefs 𝒯) (num d) ⟶* quoteTm (body 𝒯 d)
--
-- beyond the size both sides are the kernel's default entry `⟨Unit∣unit⟩`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.QuoteSig (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _⊎_; inj₁; inj₂ )
open import Agda.Builtin.Nat using ( zero; suc; _+_; _==_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( ⟶*-trans; ⟶*-appˡ )
open import DirectedHoTT.Lib.NatCode 𝒮 𝓃 using ( toI; fromI )
open import DirectedHoTT.Lib.NatNum 𝒮 𝓃 using ( num; num-sub; ⊢num )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( Lt; lt-z; lt-s )
open import DirectedHoTT.Lib.SynUnq 𝒮 wf using ( ⌜⌝ˢ-sub )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf using ( K )
open import DirectedHoTT.Examples.Knot.Terms 𝒮 wf using ( quoteTy; quoteTm; ⊢quoteTy; ⊢quoteTm )
open import DirectedHoTT.Examples.Knot.Unquote 𝒮 wf using ( toTy; toTm; quote-toTy; quote-toTm )
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf

private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- 1. A quotation is CLOSED.
------------------------------------------------------------------------

quoteTy-sub : {Γ : Cx} (σ : Sub Δ Θ) (A : RTy Γ) → subTm σ (quoteTy A {Δ}) ≡ quoteTy A
quoteTy-sub σ A = trans (cong (subTm σ) (sym (quote-toTy A))) (trans (⌜⌝ˢ-sub σ (toTy A)) (quote-toTy A))

quoteTm-sub : {Γ : Cx} (σ : Sub Δ Θ) (t : RTm Γ) → subTm σ (quoteTm t {Δ}) ≡ quoteTm t
quoteTm-sub σ t = trans (cong (subTm σ) (sym (quote-toTm t))) (trans (⌜⌝ˢ-sub σ (toTm t)) (quote-toTm t))

------------------------------------------------------------------------
-- 2. SELECTION by a natural.
------------------------------------------------------------------------

Entry : Set
Entry = {Θ : Cx} → RTm Θ

Closed : Entry → Set
Closed e = ∀ {Δ Θ} (σ : Sub Δ Θ) → subTm σ (e {Δ}) ≡ e

sel : (ℕ → Entry) → Entry → ℕ → RTm Δ → RTm Δ
sel f e zero    x = e
sel f e (suc r) x = natrec (f 0) (sel (λ i → f (suc i)) e r (var (vs vz))) x

private
  ⟶*-≡ : {t u v : RTm Δ} → t ⟶* u → u ≡ v → t ⟶* v
  ⟶*-≡ p refl = p

module _ (e : Entry) (ec : Closed e) where

  sel-sub : (f : ℕ → Entry) → (∀ i → Closed (f i)) → (r : ℕ) (σ : Sub Δ Θ) (x : RTm Δ) →
            subTm σ (sel f e r x) ≡ sel f e r (subTm σ x)
  sel-sub f fc zero    σ x = ec σ
  sel-sub f fc (suc r) σ x =
    cong₂ (λ z s → natrec z s (subTm σ x)) (fc 0 σ)
          (sel-sub (λ i → f (suc i)) (λ i → fc (suc i)) r (extS (extS σ)) (var (vs vz)))

  -- one step of the chain: the successor branch is the SHIFTED chain
  sel-suc : (f : ℕ → Entry) → (∀ i → Closed (f i)) → (r : ℕ) (m : RTm Δ) →
            sel f e (suc r) (nsuc m) ⟶ sel (λ i → f (suc i)) e r m
  sel-suc f fc r m =
    subst (λ z → sel f e (suc r) (nsuc m) ⟶ z)
          (trans (cong (subTm (single (natrec (f 0) S m))) (sel-sub f' fc' r (extS (single m)) (var (vs vz))))
          (trans (sel-sub f' fc' r (single (natrec (f 0) S m)) (renTm vs m))
                 (cong (sel f' e r) (wk-cancel-tm (natrec (f 0) S m) m))))
          (natrec-suc (f 0) S m)
    where
      f' : ℕ → Entry
      f' i = f (suc i)
      fc' : ∀ i → Closed (f' i)
      fc' i = fc (suc i)
      S = sel f' e r (var (vs vz))

  -- a name below the count selects its entry…
  sel-hit : (f : ℕ → Entry) → (∀ i → Closed (f i)) → {r d : ℕ} → Lt d r → sel f e r (num d) ⟶* f d {Δ}
  sel-hit f fc lt-z         = step (natrec-zero (f 0) _) done
  sel-hit f fc {suc r} (lt-s {k = d} p) =
    step (sel-suc f fc r (num d)) (sel-hit (λ i → f (suc i)) (λ i → fc (suc i)) p)

  -- …one at or past it, the default
  sel-miss : (f : ℕ → Entry) → (∀ i → Closed (f i)) → (r k : ℕ) → sel f e r (num (r + k)) ⟶* e {Δ}
  sel-miss f fc zero    k = done
  sel-miss f fc (suc r) k = step (sel-suc f fc r (num (r + k))) (sel-miss (λ i → f (suc i)) (λ i → fc (suc i)) r k)

------------------------------------------------------------------------
-- 3. The kernel's lookup past the size is the default entry.
------------------------------------------------------------------------

lt-or-ge : (d n : ℕ) → Lt d n ⊎ Σ ℕ (λ k → d ≡ (n + k))
lt-or-ge d       zero    = inj₂ (d , refl)
lt-or-ge zero    (suc n) = inj₁ lt-z
lt-or-ge (suc d) (suc n) with lt-or-ge d n
... | inj₁ p       = inj₁ (lt-s p)
... | inj₂ (k , e) = inj₂ (k , cong suc e)

private
  lt-self : (n : ℕ) → Lt n (suc n)
  lt-self zero    = lt-z
  lt-self (suc n) = lt-s (lt-self n)

  lt-up : {i n : ℕ} → Lt i n → Lt i (suc n)
  lt-up lt-z     = lt-z
  lt-up (lt-s p) = lt-s (lt-up p)

  past : {i n : ℕ} (k : ℕ) → Lt i n → ((n + k) == i) ≡ false
  past k lt-z     = refl
  past k (lt-s p) = past k p

  miss : (n : ℕ) (T : DefTele) (d : ℕ) → (∀ {i} → Lt i n → (d == i) ≡ false) → lookupK n T d ≡ ⟨ Unit ∣ unit ⟩
  miss zero    T       d h = refl
  miss (suc n) ∅       d h = refl
  miss (suc n) (T ▸ x) d h with d == n | h (lt-self n)
  ... | false | refl = miss n T d (λ p → h (lt-up p))

lookupK-past : (n : ℕ) (T : DefTele) (k : ℕ) → lookupK n T (n + k) ≡ ⟨ Unit ∣ unit ⟩
lookupK-past n T k = miss n T (n + k) (past k)

------------------------------------------------------------------------
-- 4. ★ THE QUOTED SIGNATURE.
------------------------------------------------------------------------

module _ (𝒯 : Defs) where
  open Defs 𝒯 using ( len; tele; size; type; body )

  tyE bdE : ℕ → Entry
  tyE i = quoteTy (type i)
  bdE i = quoteTm (body i)

  private
    tyE-c : ∀ i → Closed (tyE i)
    tyE-c i σ = quoteTy-sub σ (type i)
    bdE-c : ∀ i → Closed (bdE i)
    bdE-c i σ = quoteTm-sub σ (body i)
    ty₀ tm₀ : Entry
    ty₀ = quoteTy {ε} Unit
    tm₀ = quoteTm {ε} unit
    ty₀-c : Closed ty₀
    ty₀-c σ = quoteTy-sub σ (Unit {ε})
    tm₀-c : Closed tm₀
    tm₀-c σ = quoteTm-sub σ (unit {ε})

  ⌜types⌝ ⌜bodies⌝ : RTm Δ
  ⌜types⌝  = lam (sel tyE ty₀ size (var vz))
  ⌜bodies⌝ = lam (sel bdE tm₀ size (var vz))

  quoteDefs : RTm Δ
  quoteDefs = pair (num size) (pair ⌜types⌝ ⌜bodies⌝)

  quoteDefs-sub : (σ : Sub Δ Θ) → subTm σ (quoteDefs {Δ}) ≡ quoteDefs
  quoteDefs-sub σ =
    cong₂ (λ n p → pair n p) (num-sub σ size)
          (cong₂ (λ a b → pair (lam a) (lam b))
                 (sel-sub ty₀ ty₀-c tyE tyE-c size (extS σ) (var vz))
                 (sel-sub tm₀ tm₀-c bdE bdE-c size (extS σ) (var vz)))

  -- ★ the lookups COMPUTE to the quoted entries — at every name
  sizeQ-at : sizeQ (quoteDefs {Δ}) ⟶* num size
  sizeQ-at = step (βfst _ _) done

  typesQ-at : (d : ℕ) → typesQ (quoteDefs {Δ}) (num d) ⟶* quoteTy (type d)
  typesQ-at d =
    ⟶*-trans (⟶*-appˡ (step (ξ-fst (βsnd _ _)) (step (βfst _ _) done)))
    (step (β _ _)
    (subst (λ z → z ⟶* quoteTy (type d)) (sym (sel-sub ty₀ ty₀-c tyE tyE-c size (single (num d)) (var vz))) (pick (lt-or-ge d size))))
    where
      pick : Lt d size ⊎ Σ ℕ (λ k → d ≡ (size + k)) → sel tyE ty₀ size (num d) ⟶* quoteTy (type d)
      pick (inj₁ p)        = sel-hit ty₀ ty₀-c tyE tyE-c p
      pick (inj₂ (k , refl)) =
        ⟶*-≡ (sel-miss ty₀ ty₀-c tyE tyE-c size k) (cong (λ x → quoteTy (Def.kType x)) (sym (lookupK-past len tele k)))

  bodiesQ-at : (d : ℕ) → bodiesQ (quoteDefs {Δ}) (num d) ⟶* quoteTm (body d)
  bodiesQ-at d =
    ⟶*-trans (⟶*-appˡ (step (ξ-snd (βsnd _ _)) (step (βsnd _ _) done)))
    (step (β _ _)
    (subst (λ z → z ⟶* quoteTm (body d)) (sym (sel-sub tm₀ tm₀-c bdE bdE-c size (single (num d)) (var vz))) (pick (lt-or-ge d size))))
    where
      pick : Lt d size ⊎ Σ ℕ (λ k → d ≡ (size + k)) → sel bdE tm₀ size (num d) ⟶* quoteTm (body d)
      pick (inj₁ p)        = sel-hit tm₀ tm₀-c bdE bdE-c p
      pick (inj₂ (k , refl)) =
        ⟶*-≡ (sel-miss tm₀ tm₀-c bdE bdE-c size k) (cong (λ x → quoteTm (Def.kBody x)) (sym (lookupK-past len tele k)))

------------------------------------------------------------------------
-- 5. Its typing.
------------------------------------------------------------------------

module _ (C : Entry) (Cc : Closed C) (⊢C : {Γ : Ctx} → Γ ⊢ C ∷ U) (e : Entry) (ec : Closed e)
         (⊢e : {Γ : Ctx} → Γ ⊢ e ∷ El C) where

  ⊢sel : (f : ℕ → Entry) → (∀ i → Closed (f i)) → (∀ i {Γ : Ctx} → Γ ⊢ f i ∷ El C) →
         (r : ℕ) {Γ : Ctx} {x : RTm ⌊ Γ ⌋} → Γ ⊢ x ∷ Nat → Γ ⊢ sel f e r x ∷ El C
  ⊢sel f fc ⊢f zero    dx = ⊢e
  ⊢sel f fc ⊢f (suc r) {Γ} {x} dx =
    ⊢-cast (cong El (Cc (single x)))
      (⊢natrec {M = El C} (ty-El ⊢C)
               (⊢-cast (sym (cong El (Cc (single nzero)))) (⊢f 0))
               (⊢-cast (sym (cong El (Cc nrs)))
                       (⊢sel (λ i → f (suc i)) (λ i → fc (suc i)) (λ i → ⊢f (suc i)) r (⊢var (there here))))
               dx)

module _ (𝒯 : Defs) where
  open Defs 𝒯 using ( size; type; body )

  private
    ⊢ty : {Γ : Ctx} (A : RTy ε) → Γ ⊢ quoteTy A ∷ El ⌜Ty⌝₀
    ⊢ty A = ⊢conv (⊢quoteTy A) (csymᵀ (credᵀ El-⌜Ty⌝₀))
    ⊢tm : {Γ : Ctx} (t : RTm ε) → Γ ⊢ quoteTm t ∷ El ⌜Tm⌝₀
    ⊢tm t = ⊢conv (⊢quoteTm t) (csymᵀ (credᵀ El-⌜Tm⌝₀))

  ⊢quoteDefs : {Ξ : Ctx} → Ξ ⊢ quoteDefs 𝒯 ∷ El ⌜QSig⌝
  ⊢quoteDefs {Ξ} =
    ⊢conv (⊢pair (ty-El ⊢⌜Tabs⌝) (toI (⊢num size))
                 (⊢-cast (sym (cong El (⌜Tabs⌝-sub (single (num size))))) dtabs))
          (csymᵀ (credᵀ (El-⌜Σ⌝ ⌜Nat⌝ ⌜Tabs⌝)))
    where
      dL : Ξ ⊢ ⌜types⌝ 𝒯 ∷ El ⌜Tys⌝
      dL = ⊢conv (⊢lam (ty-El ⊢⌜Nat⌝)
                       (⊢sel ⌜Ty⌝₀ ⌜Ty⌝₀-sub ⊢⌜Ty⌝₀ (quoteTy {ε} Unit) (λ σ → quoteTy-sub σ (Unit {ε})) (⊢ty Unit)
                             (tyE 𝒯) (λ i σ → quoteTy-sub σ (type i)) (λ i → ⊢ty (type i)) size (fromI (⊢var here))))
                 (csymᵀ (credᵀ (El-⌜Π⌝ ⌜Nat⌝ ⌜Ty⌝₀)))
      dB : Ξ ⊢ ⌜bodies⌝ 𝒯 ∷ El ⌜Bds⌝
      dB = ⊢conv (⊢lam (ty-El ⊢⌜Nat⌝)
                       (⊢sel ⌜Tm⌝₀ ⌜Tm⌝₀-sub ⊢⌜Tm⌝₀ (quoteTm {ε} unit) (λ σ → quoteTm-sub σ (unit {ε})) (⊢tm unit)
                             (bdE 𝒯) (λ i σ → quoteTm-sub σ (body i)) (λ i → ⊢tm (body i)) size (fromI (⊢var here))))
                 (csymᵀ (credᵀ (El-⌜Π⌝ ⌜Nat⌝ ⌜Tm⌝₀)))
      dtabs : Ξ ⊢ pair (⌜types⌝ 𝒯) (⌜bodies⌝ 𝒯) ∷ El ⌜Tabs⌝
      dtabs = ⊢conv (⊢pair (ty-El ⊢⌜Bds⌝) dL (⊢-cast (sym (cong El (⌜Bds⌝-sub (single (⌜types⌝ 𝒯))))) dB))
                    (csymᵀ (credᵀ (El-⌜Σ⌝ ⌜Tys⌝ ⌜Bds⌝)))
