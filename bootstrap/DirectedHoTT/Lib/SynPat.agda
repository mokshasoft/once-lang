-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — ★★ A NESTED PATTERN: a `Desc`-valued case on a
-- syntax term that has ONE live row (D077).
--
-- A judgement's rule whose conclusion has a constructor PATTERN in a
-- non-subject position (`⊢lam`'s type `Π A B`) is a nested case: the
-- outer fibre (on the subject) cases on that component, and exactly one
-- head — the pattern's — has a row; every other head is empty.  The
-- pattern's variables are the scrutinee's payload: no existential, no
-- Ford (D077 "Where the target is a constructor pattern, the fibre is
-- computed by unification, i.e. by case").
--
--     CASE j a c  =  app (ielim D (tag s₀ , j) PATM a) c
--     case-β   :  CASE j (conₗ h q) c  ⟶*  R j q c
--
-- It is `Lib/SynFib`'s `Fib` at the row table `rowAt s₀ h r` (the row at
-- one position, `noRow` elsewhere), typed ONCE here from the one row's
-- typing — instances cost only their row.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; _<ˢ?_ )
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
import DirectedHoTT.Spec.Typing as Ty
module DirectedHoTT.Lib.SynPat (𝒮 : KSig) (𝓃 : ℕ) (ok : Ty.EntriesOK 𝒮 𝓃) where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( ⟶*-trans; ⟶*-appˡ; ⟶*-appʳ; ⟶*-ielimᵗ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( Cons; []; selF; tag; conₗ; Lt; ⊢selF; []ᵈ )
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynView 𝒮 𝓃 ok using ( PayV )
open import DirectedHoTT.Lib.SynFib 𝒮 𝓃 ok

private
  variable
    Δ Θ : Cx
    n m c : ℕ

------------------------------------------------------------------------
-- 1. The shape at a position, and the one-row table.
------------------------------------------------------------------------

lookShs : Shapes c → ℕ → Shape
lookShs []ˢʰ         k       = []ʰ
lookShs (sh ∷ˢʰ shs) zero    = sh
lookShs (sh ∷ˢʰ shs) (suc k) = lookShs shs k

lookSh : Sig m → ℕ → ℕ → Shape
lookSh []ᵍ          s       k = []ʰ
lookSh (shs ∷ᵍ sg)  zero    k = lookShs shs k
lookSh (shs ∷ᵍ sg)  (suc s) k = lookSh sg s k

look-nthSh : {shs : Shapes c} {k : ℕ} {sh : Shape} → NthSh shs k sh → lookShs shs k ≡ sh
look-nthSh nthʰ-z      = refl
look-nthSh (nthʰ-s nh) = look-nthSh nh

look-nth : {sg : Sig m} {s k : ℕ} {shs : Shapes c} {sh : Shape} → NthG sg s shs → NthSh shs k sh → lookSh sg s k ≡ sh
look-nth nthᵍ-z      nh = look-nthSh nh
look-nth (nthᵍ-s ng) nh = look-nth ng nh

-- the empty fibre
noRow : Row
noRow = record { R = λ j p c → dσ (⌜Fin⌝ nzero) (selF []) ; R-sub = λ σ j p c → refl }

-- the row `r` at (s₀ , h), none elsewhere
rowAt : ℕ → ℕ → Row → ℕ → ℕ → Row
rowAt zero     zero    r zero    zero    = r
rowAt zero     zero    r zero    (suc k) = noRow
rowAt zero     (suc h) r zero    zero    = noRow
rowAt zero     (suc h) r zero    (suc k) = rowAt zero h r zero k
rowAt zero     zero    r (suc s) k       = noRow
rowAt zero     (suc h) r (suc s) k       = noRow
rowAt (suc s₀) h       r zero    k       = noRow
rowAt (suc s₀) h       r (suc s) k       = rowAt s₀ h r s k

rowAt-elim : (P : Row → Set) (s₀ h s k : ℕ) {r : Row} → (s ≡ s₀ → k ≡ h → P r) → P noRow → P (rowAt s₀ h r s k)
rowAt-elim P zero     zero    zero    zero    f n = f refl refl
rowAt-elim P zero     zero    zero    (suc k) f n = n
rowAt-elim P zero     (suc h) zero    zero    f n = n
rowAt-elim P zero     (suc h) zero    (suc k) f n = rowAt-elim P zero h zero k (λ e1 e2 → f e1 (cong suc e2)) n
rowAt-elim P zero     zero    (suc s) k       f n = n
rowAt-elim P zero     (suc h) (suc s) k       f n = n
rowAt-elim P (suc s₀) h       zero    k       f n = n
rowAt-elim P (suc s₀) h       (suc s) k       f n = rowAt-elim P s₀ h s k (λ e1 e2 → f (cong suc e1) e2) n

rowAt-hit : (P : Row → Set) (s₀ h : ℕ) {r : Row} → P (rowAt s₀ h r s₀ h) → P r
rowAt-hit P zero     zero    x = x
rowAt-hit P zero     (suc h) x = rowAt-hit P zero h x
rowAt-hit P (suc s₀) h       x = rowAt-hit P s₀ h x

------------------------------------------------------------------------
-- 2. ★ THE CASE.
------------------------------------------------------------------------

module Pat {sg : Sig n} (ok : SigOK n sg)
           (J : {Δ : Cx} → RTm Δ) (J-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (J {Δ}) ≡ J)
           (⊢J : {Γ : Ctx} → Γ ⊢ J ∷ U)
           (C : {Δ : Cx} → RTm (Δ ∙)) (C-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm (extS σ) (C {Δ}) ≡ C)
           (⊢C : {Γ : Ctx} → (Γ ▹ El (SI n)) ⊢ C ∷ U)
           (s₀ h : ℕ) (r : Row) where

  open Row
  open Fib ok J J-sub ⊢J C C-sub ⊢C (rowAt s₀ h r) public

  private
    okNo : {s : ℕ} {sh : Shape} → RowOK s sh noRow
    okNo dj dp dc = ⊢dσ ⊢J (⊢⌜Fin⌝ ⊢nzero) (⊢selF ⊢J []ᵈ)

    okHit : {s k c' : ℕ} {shs : Shapes c'} {sh : Shape} → NthG sg s shs → NthSh shs k sh →
            RowOK s₀ (lookSh sg s₀ h) r → s ≡ s₀ → k ≡ h → RowOK s sh r
    okHit ng nh rok refl refl = subst (λ z → RowOK s₀ z r) (look-nth ng nh) rok

  -- ★ the case's method, typed from its ONE row
  ⊢PATM : {Γ : Ctx} → RowOK s₀ (lookSh sg s₀ h) r → Γ ⊢ FIBM ∷ MethTy (SI n) (SD sg) FM
  ⊢PATM rok = ⊢FIBM (λ {s} {c'} {k} {shs} {sh} ng nh →
                       rowAt-elim (RowOK s sh) s₀ h s k (okHit ng nh rok) (okNo {s} {sh}))

  -- ★ OPAQUE: the case carries the whole fibre method (every row), and a
  --   transparent one is compared by normalisation wherever two syntactic
  --   forms of one context meet (`context-form-mismatch-opaque`)
  opaque
    CASE : RTm Δ → RTm Δ → RTm Δ → RTm Δ
    CASE j a c = app (ielim (SD sg) (pair (tag s₀) j) FIBM a) c

    CASE-sub : (σ : Sub Δ Θ) (j a c : RTm Δ) → subTm σ (CASE j a c) ≡ CASE (subTm σ j) (subTm σ a) (subTm σ c)
    CASE-sub σ j a c =
      cong₃' (SD-sub σ sg) (tag-sub σ s₀) (FIBM-sub σ)
      where
        cong₃' : {D D' T T' M M' : RTm _} → D ≡ D' → T ≡ T' → M ≡ M' →
                 app (ielim D (pair T (subTm σ j)) M (subTm σ a)) (subTm σ c) ≡ app (ielim D' (pair T' (subTm σ j)) M' (subTm σ a)) (subTm σ c)
        cong₃' refl refl refl = refl

    -- ★ typed: at any depth, scrutinee of sort s₀, and convoy
    ⊢CASE : {Ξ : Ctx} {j a c : RTm ⌊ Ξ ⌋} → RowOK s₀ (lookSh sg s₀ h) r → Lt s₀ n →
            Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ a ∷ SK sg s₀ j → Ξ ⊢ c ∷ El (Cat (pair (tag s₀) j)) → Ξ ⊢ CASE j a c ∷ Desc J
    ⊢CASE {Ξ} {j} {a} {c} rok lt dj da dc =
      ⊢-cast {Ξ} {CASE j a c} {subTy (single c) (Desc J)} {Desc J} (cong Desc (J-sub (single c)))
        (⊢app {Ξ} {El (Cat i)} {Desc J} {ielim (SD sg) i FIBM a} {c}
              (⊢-cast {Ξ} {ielim (SD sg) i FIBM a} {iinst i a FM} {Π (El (Cat i)) (Desc J)} eI dI) dc)
      where
        i : RTm ⌊ Ξ ⌋
        i = pair (tag s₀) j
        dI : Ξ ⊢ ielim (SD sg) i FIBM a ∷ iinst i a FM
        dI = ⊢ielim {Ξ} {SI n} {SD sg} {FM} {FIBM} {i} {a} ⊢SI (⊢SD ok) ⊢FM (⊢PATM rok) (⊢ix lt dj) (⊢SK→IMu {sg = sg} {s = s₀} {d = j} da)
        eI : iinst i a FM ≡ Π (El (Cat i)) (Desc J)
        eI = trans {x = iinst i a FM} {y = subTy (single a ∘ₛ extS (single i)) FM} {z = Π (El (Cat i)) (Desc J)}
                   (subTy-subTy {τ = single a} {σ = extS (single i)} FM)
                   (trans (FM-sub (single a ∘ₛ extS (single i)))
                          (cong (λ z → Π (El (Cat z)) (Desc J)) {x = subTm (single a) (renTm vs i)} {y = i}
                                (wk-cancel-tm a i)))

    -- reduction in the scrutinee and in the convoy
    CASE-⟶ᵃ : {j a a' c : RTm Δ} → a ⟶* a' → CASE j a c ⟶* CASE j a' c
    CASE-⟶ᵃ r = ⟶*-appˡ (⟶*-ielimᵗ r)

    CASE-⟶ᶜ : {j a c c' : RTm Δ} → c ⟶* c' → CASE j a c ⟶* CASE j a c'
    CASE-⟶ᶜ r = ⟶*-appʳ r

    -- ★ at ANY head: the row the table holds there (the pattern's, or
    --   `noRow`) — what a decoder (PLAN-FAITHFUL F6) reads a CASE with
    case-any : {c' k : ℕ} {shs : Shapes c'} {sh : Shape} {j q c : RTm Δ} → NthG sg s₀ shs → NthSh shs k sh →
               CASE j (conₗ k q) c ⟶* R (rowAt s₀ h r s₀ k) j q c
    case-any {j = j} {q} {c} ng nh = fib-β {D = SD sg} {j = j} {p = q} {c₀ = c} ng nh

    -- ★ at the pattern's head, the case IS the row
    case-β : {c' : ℕ} {shs : Shapes c'} {sh : Shape} {j q c : RTm Δ} → NthG sg s₀ shs → NthSh shs h sh →
             CASE j (conₗ h q) c ⟶* R r j q c
    case-β {j = j} {q} {c} ng nh =
      rowAt-hit (λ ρ → CASE j (conₗ h q) c ⟶* R ρ j q c) s₀ h (fib-β {D = SD sg} {j = j} {p = q} {c₀ = c} ng nh)
