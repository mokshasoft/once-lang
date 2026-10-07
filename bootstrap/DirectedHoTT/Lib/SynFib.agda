-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — ★★★ A FAMILY FIBRED BY CASE ON A SYNTAX TERM (D077),
-- generic in the signature.
--
-- A judgement over a syntax is presented by its fibres: the rows a term
-- of head `k` (sort `s`) admits.  The fibre function eliminates the
-- subject with a `Desc`-valued motive, carrying the index's other
-- components as a CONVOY `c`:
--
--     FM(i, t)  =  El C(i) → Desc J
--     FIBM      =  one method per constructor:  λ p h c. R_{s,k} j p c
--
-- ★ Each row is a NATURAL family `R j p c` (a function of the method's
--   index, payload and convoy, with its substitution law).  So the
--   computation rule is proven ONCE, here, with the rows abstract:
--
--     fib-β :  app (ielim D (tag s , j) FIBM (conₗ k p)) c  ⟶*  R_{s,k} j p c
--
--   and every β is cast to its clean reduct, so no substitution tower forms
--   (memory: beta-chains-cast-each-step).  A row is typed at ARBITRARY
--   terms against the payload's normal form `PayV`; the method's awkward
--   context is this module's business.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; _<ˢ?_ )
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
import DirectedHoTT.Spec.Typing as Ty
module DirectedHoTT.Lib.SynFib (𝒮 : KSig) (𝓃 : ℕ) (ok : Ty.EntriesOK 𝒮 𝓃) where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _×_; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( ⟶*-trans; ⟶*-appˡ; red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢wk; ⊢-cast; wk-cancel-tm; sub-lemma; ⊢single )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using ( wk-sub )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic 𝒮 using ( ⟨_⟩ᵣ; subTm-var )
open import DirectedHoTT.Metatheory.Premises 𝒮 𝓃 using ( mot-ren; ⊢wkD )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( Cons; []; _∷_; Nth; nth-z; nth-s; nth-lt; selF; subC; tag; conₗ; tag-ren; Lt; lt-z; ⊢selF; selF-β; ⊢tag; ⊢pay-σ; ⊢con-fib; AllD; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok
open import DirectedHoTT.Lib.TelAt 𝒮 𝓃 ok using ( HypAt; entₛ; nth-⌜⌝ₛₛ; allSD )
open import DirectedHoTT.Lib.MethAt 𝒮 𝓃 ok
open import DirectedHoTT.Lib.Sorted 𝒮 𝓃 ok using ( σₛ; ιₛ; ⊢ιₛ; PerS; []ₚ; _∷ₚ_; ⊢sortMeth; ⊢methₛ; SortT; ιₛ-red )
open import DirectedHoTT.Lib.NatNum 𝒮 𝓃 using ( num )
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynView 𝒮 𝓃 ok using ( PayV; payV-red; ren-tel )
open import DirectedHoTT.Lib.SynTravM 𝒮 𝓃 ok using ( _+'_; +'-zero )

private
  variable
    Γ Δ Θ : Cx
    n : ℕ

------------------------------------------------------------------------
-- 1. A ROW: a natural family in the method's index, payload and convoy.
------------------------------------------------------------------------

record Row : Set₁ where
  field
    R     : {Δ : Cx} → RTm Δ → RTm Δ → RTm Δ → RTm Δ
    R-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) (j p c : RTm Δ) → subTm σ (R j p c) ≡ R (subTm σ j) (subTm σ p) (subTm σ c)

-- the weakenings the β-walk passes through, and their cancellation
W1 W2 W3 : RTm Δ → RTm _
W1 t = renTm vs t
W2 t = renTm vs (W1 t)
W3 t = renTm vs (W2 t)

private
  k0 : (u t : RTm Δ) → subTm (single u) (W1 t) ≡ t
  k0 u t = wk-cancel-tm u t

  k1 : (u t : RTm Δ) → subTm (extS (single u)) (W2 t) ≡ W1 t
  k1 u t = trans (wk-sub (single u) (W1 t)) (cong (renTm vs) (k0 u t))

  k2 : (u t : RTm Δ) → subTm (extS (extS (single u))) (W3 t) ≡ W2 t
  k2 u t = trans (wk-sub (extS (single u)) (W2 t)) (cong (renTm vs) (k1 u t))

  -- one β, cast to its clean reduct
  βcast : (t : RTm (Δ ∙)) (u v : RTm Δ) → subTm (single u) t ≡ v → app (lam t) u ⟶* v
  βcast t u v e = step (β t u) (subst (λ z → z ⟶* v) (sym e) done)

------------------------------------------------------------------------
-- 2. ★ THE FIBRE METHOD over a signature.
------------------------------------------------------------------------

-- the family's index and convoy, before any row (so rows can be TYPED
-- in modules of their own)
module Fib₀ {sg : Sig n} (ok : SigOK n sg)
           (J : {Δ : Cx} → RTm Δ) (J-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (J {Δ}) ≡ J)
           (⊢J : {Γ : Ctx} → Γ ⊢ J ∷ U)
           (C : {Δ : Cx} → RTm (Δ ∙)) (C-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm (extS σ) (C {Δ}) ≡ C)
           (⊢C : {Γ : Ctx} → (Γ ▹ El (SI n)) ⊢ C ∷ U) where

  open Row

  -- the convoy's code at an index
  Cat : RTm Δ → RTm Δ
  Cat i = subTm (single i) C

  -- ★ C depends on nothing but its index
  C-inst : (τ : Sub (Δ ∙) Θ) → subTm τ C ≡ Cat (τ vz)
  C-inst τ = trans (subTm-cong pt C) (trans (sym (subTm-subTm C)) (cong (subTm (single (τ vz))) (C-sub (τ ₛ∘ᵣ vs))))
    where
      pt : ∀ x → τ x ≡ (single (τ vz) ∘ₛ extS (τ ₛ∘ᵣ vs)) x
      pt vz     = refl
      pt (vs x) = sym (wk-cancel-tm (τ vz) (τ (vs x)))

  ⊢Cat : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El (SI n) → Γ ⊢ Cat i ∷ U
  ⊢Cat di = sub-lemma ⊢C (⊢single di)

  -- the case's motive
  FM : RTy ((Δ ∙) ∙)
  FM = Π (El (renTm vs C)) (Desc J)

  FM-sub : (τ : Sub ((Δ ∙) ∙) Θ) → subTy τ FM ≡ Π (El (Cat (τ (vs vz)))) (Desc J)
  FM-sub τ = cong₂ Π (cong El (trans (subTm-renTm C) (C-inst (τ ₛ∘ᵣ vs)))) (cong Desc (J-sub (extS τ)))

  ⊢FM : {Γ : Ctx} → motCtx Γ (SI n) (SD sg) ⊢ty FM
  ⊢FM = ty-Π (ty-El (⊢wk ⊢C)) (ty-Desc ⊢J)

  -- a row, typed: at ANY index, payload and convoy
  RowOK : ℕ → Shape → Row → Set
  RowOK s sh r = {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ →
                 Ξ ⊢ p ∷ PayV sh (pair (tag s) j) (SI n) (SD sg) → Ξ ⊢ c ∷ El (Cat (pair (tag s) j)) →
                 Ξ ⊢ R r j p c ∷ Desc J

  -- ★ a family's rows WITH their typings, one entry per constructor, in
  --   the signature's order — what a family is, read off as a table.  The
  --   dispatch by position (`NthG`/`NthSh`) is `rowIn`/`okIn`, once, here;
  --   the sort index is the table's, so an entry is checked against
  --   `RowOK s sh r` at the sort the table was written at.
  infixr 5 ⟨_∣_⟩∷_ ⟨_∣∀_⟩∷_ _∷ᴳ_
  data RowsOK (s : ℕ) : {c : ℕ} → Shapes c → Set₁ where
    []ᴿ    : RowsOK s []ˢʰ
    ⟨_∣_⟩∷_ : {c : ℕ} {sh : Shape} {shs : Shapes c} (r : Row) → RowOK s sh r → RowsOK s shs → RowsOK s (sh ∷ˢʰ shs)
    -- a row typed at EVERY sort and shape (a family's "no rule here"):
    --   the table supplies the shape, so nothing is left to infer
    ⟨_∣∀_⟩∷_ : {c : ℕ} {sh : Shape} {shs : Shapes c} (r : Row) → ((s' : ℕ) (sh' : Shape) → RowOK s' sh' r) →
               RowsOK s shs → RowsOK s (sh ∷ˢʰ shs)

  data RowsOKG (s₀ : ℕ) : {m : ℕ} → Sig m → Set₁ where
    []ᴳ  : RowsOKG s₀ []ᵍ
    _∷ᴳ_ : {c m : ℕ} {shs : Shapes c} {sg' : Sig m} → RowsOK s₀ shs → RowsOKG (suc s₀) sg' → RowsOKG s₀ (shs ∷ᵍ sg')

  -- past the end of a table (never typed, never reached)
  pastRow : Row
  pastRow = record { R = λ j p c → j ; R-sub = λ σ j p c → refl }

  rowInSh : {s c : ℕ} {shs : Shapes c} → RowsOK s shs → ℕ → Row
  rowInSh []ᴿ               k       = pastRow
  rowInSh (⟨ r ∣ _ ⟩∷ rs)  zero    = r
  rowInSh (⟨ r ∣ _ ⟩∷ rs)  (suc k) = rowInSh rs k
  rowInSh (⟨ r ∣∀ _ ⟩∷ rs) zero    = r
  rowInSh (⟨ r ∣∀ _ ⟩∷ rs) (suc k) = rowInSh rs k

  rowIn : {s₀ m : ℕ} {sg' : Sig m} → RowsOKG s₀ sg' → ℕ → ℕ → Row
  rowIn []ᴳ         s       k = pastRow
  rowIn (t ∷ᴳ ts)  zero    k = rowInSh t k
  rowIn (t ∷ᴳ ts)  (suc s) k = rowIn ts s k

  okInSh : {s c k : ℕ} {shs : Shapes c} {sh : Shape} (t : RowsOK s shs) → NthSh shs k sh → RowOK s sh (rowInSh t k)
  okInSh (⟨ r ∣ o ⟩∷ rs) nthʰ-z      = o
  okInSh (⟨ r ∣ o ⟩∷ rs) (nthʰ-s nh) = okInSh rs nh
  okInSh {s = s} {sh = sh} (⟨ r ∣∀ o ⟩∷ rs) nthʰ-z = o s sh
  okInSh (⟨ r ∣∀ o ⟩∷ rs) (nthʰ-s nh) = okInSh rs nh

  okIn : {s₀ m s c k : ℕ} {sg' : Sig m} {shs : Shapes c} {sh : Shape} (t : RowsOKG s₀ sg') →
         NthG sg' s shs → NthSh shs k sh → RowOK (s +' s₀) sh (rowIn t s k)
  okIn (t ∷ᴳ ts) nthᵍ-z      nh = okInSh t nh
  okIn (t ∷ᴳ ts) (nthᵍ-s ng) nh = okIn ts ng nh

  -- …the form `Fib` takes: a whole signature's table, every row typed
  okOf : {s c k : ℕ} {shs : Shapes c} {sh : Shape} (t : RowsOKG zero sg) →
         NthG sg s shs → NthSh shs k sh → RowOK s sh (rowIn t s k)
  okOf {s = s} {k = k} {sh = sh} t ng nh = subst (λ m → RowOK m sh (rowIn t s k)) (+'-zero s) (okIn t ng nh)

module Fib {sg : Sig n} (ok : SigOK n sg)
           (J : {Δ : Cx} → RTm Δ) (J-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (J {Δ}) ≡ J)
           (⊢J : {Γ : Ctx} → Γ ⊢ J ∷ U)
           (C : {Δ : Cx} → RTm (Δ ∙)) (C-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm (extS σ) (C {Δ}) ≡ C)
           (⊢C : {Γ : Ctx} → (Γ ▹ El (SI n)) ⊢ C ∷ U)
           (row : ℕ → ℕ → Row) where

  open Row
  open Fib₀ ok J J-sub ⊢J C C-sub ⊢C public

  -- the methods
  mF : Row → RTm (Δ ∙)
  mF r = lam (lam (lam (R r (var (vs (vs (vs vz)))) (var (vs (vs vz))) (var vz))))

  mFs : {c : ℕ} → ℕ → Shapes c → ℕ → Cons (Δ ∙) c
  mFs s []ˢʰ         k = []
  mFs s (sh ∷ˢʰ shs) k = mF (row s k) ∷ mFs s shs (suc k)

  sortMsF : {m : ℕ} → Sig m → ℕ → Cons Δ m
  sortMsF []ᵍ          s = []
  sortMsF (shs ∷ᵍ sg') s = lam (methAt (mFs s shs zero)) ∷ sortMsF sg' (suc s)

  FIBM : RTm Δ
  FIBM = methAt (sortMsF sg zero)

  ----------------------------------------------------------------------
  -- 3. ★ TYPED.
  ----------------------------------------------------------------------

  private
    -- the motive at constructor `k` of sort `s`
    FM-at : (s k : ℕ) → subTy (atS (ιₛ {Δ = Δ} s) (conₗ k (var (vs vz)))) (wk1M FM)
                        ≡ Π (El (Cat (W2 (ιₛ s)))) (Desc J)
    FM-at s k = trans (subTy-renTy FM) (FM-sub (atS (ιₛ s) (conₗ k (var (vs vz))) ₛ∘ᵣ extR (extR vs)))

    W3ι : (s : ℕ) → W3 (ιₛ {Δ = Δ} s) ≡ pair (tag s) (var (vs (vs (vs vz))))
    W3ι s = cong (λ z → pair z (var (vs (vs (vs vz)))))
                 (trans (cong (renTm vs) (trans (cong (renTm vs) (tag-ren vs s)) (tag-ren vs s))) (tag-ren vs s))

    -- ★ one constructor's method, from its row's typing
    ⊢mF : {Γ : Ctx} {s k c : ℕ} {shs : Shapes c} {sh : Shape} → NthG sg s shs → NthSh shs k sh →
          RowOK s sh (row s k) →
          HypAt (Γ ▹ El ⌜Nat⌝) (renTm vs (SI n)) (renTm vs (SD sg)) (wk1M FM) (σₛ s) (tel sh (var vz))
            ⊢ lam (R (row s k) (var (vs (vs (vs vz)))) (var (vs (vs vz))) (var vz))
            ∷ subTy (atS (ιₛ s) (conₗ k (var (vs vz)))) (wk1M FM)
    ⊢mF {Γ = Γ} {s = s} {k = k} {sh = sh} ng nh rok =
      ⊢-cast (sym (FM-at s k)) (⊢lam (ty-El dCs) dR)
      where
        H = HypAt (Γ ▹ El ⌜Nat⌝) (renTm vs (SI n)) (renTm vs (SD sg)) (wk1M FM) (σₛ s) (tel sh (var vz))
        ι₂ = W2 (ιₛ {Δ = ⌊ Γ ⌋} s)
        ι₃ : RTm (⌊ H ⌋ ∙)
        ι₃ = pair (tag s) (var (vs (vs (vs vz))))
        dιₛ : (Γ ▹ El ⌜Nat⌝) ⊢ ιₛ s ∷ El (renTm vs (SI n))
        dιₛ = ⊢ιₛ ⊢⌜Nat⌝ (nthG-lt ng)
        dCs : H ⊢ Cat ι₂ ∷ U
        dCs = ⊢Cat (⊢wkSI (⊢wkSI (⊢-cast (cong El (SI-ren vs n)) dιₛ)))
        H₃ = H ▹ El (Cat ι₂)
        dj : H₃ ⊢ var (vs (vs (vs vz))) ∷ El ⌜Nat⌝
        dj = ⊢var (there (there (there here)))
        eC : renTm vs (Cat ι₂) ≡ Cat ι₃
        eC = trans (renTm-subTm C) (trans (C-inst (vs ᵣ∘ₛ single ι₂)) (cong Cat (W3ι s)))
        dc : H₃ ⊢ var vz ∷ El (Cat ι₃)
        dc = ⊢-cast (cong El eC) (⊢var here)
        eP : renTm vs (renTm vs (renTm vs (subTm (σₛ s) ⌜ tel sh (var vz) ⌝ᵗ))) ≡ ⌜ tel sh ι₃ ⌝ᵗ
        eP = trans (cong (λ z → renTm vs (renTm vs (renTm vs z))) (sub-tel (σₛ s) sh (var vz)))
             (trans (cong (λ z → renTm vs (renTm vs z)) (ren-tel vs sh (ιₛ s)))
             (trans (cong (renTm vs) (ren-tel vs sh (W1 (ιₛ s))))
             (trans (ren-tel vs sh (W2 (ιₛ s))) (cong (λ z → ⌜ tel sh z ⌝ᵗ) (W3ι s)))))
        eD : renTm vs (renTm vs (renTm vs (renTm vs (SD {Δ = ⌊ Γ ⌋} sg)))) ≡ SD sg
        eD = trans (cong (λ z → renTm vs (renTm vs (renTm vs z))) (SD-ren vs))
             (trans (cong (λ z → renTm vs (renTm vs z)) (SD-ren vs)) (trans (cong (renTm vs) (SD-ren vs)) (SD-ren vs)))
        dp : H₃ ⊢ var (vs (vs vz)) ∷ PayV sh ι₃ (SI n) (SD sg)
        dp = ⊢conv (⊢-cast (cong₃ (λ I D X → El (dpay I D X)) (SI-wks 4) eD eP) (⊢var (there (there here))))
                   (red→≅ᵀ (payV-red sh ι₃ (SI n) (SD sg)))
        dR : H₃ ⊢ R (row s k) (var (vs (vs (vs vz)))) (var (vs (vs vz))) (var vz) ∷ Desc J
        dR = rok dj dp dc

    perT : {Γ : Ctx} {s c c' k : ℕ} {shsAll : Shapes c} {shs : Shapes c'} →
           NthG sg s shsAll → ShsOK n shs →
           ({j : ℕ} {sh : Shape} → NthSh shs j sh → NthSh shsAll (j +' k) sh) →
           ({j : ℕ} {sh : Shape} → NthSh shs j sh → RowOK s sh (row s (j +' k))) →
           PerKAt (Γ ▹ El ⌜Nat⌝) (renTm vs (SI n)) (renTm vs (SD sg)) (wk1M FM) (ιₛ s)
                  (selF (subC (σₛ s) ⌜ tels shsAll ⌝ₛ)) k (mFs s shs k)
    perT ng []ᵒˢ look oks = []ₐ
    perT {s = s} ng (shok ∷ᵒˢ shoks) look oks =
      entₛ ⊢⌜Nat⌝ (sigOK ok) ⊢FM (nth-stels ng) (nth-tels (look nthʰ-z)) (⊢mF ng (look nthʰ-z) (oks nthʰ-z))
      ∷ₐ perT ng shoks (λ n' → look (nthʰ-s n')) (λ n' → oks (nthʰ-s n'))

    perS : {Γ : Ctx} {m s₀ : ℕ} {sg' : Sig m} →
           SigOK n sg' → ({j c : ℕ} {shs : Shapes c} → NthG sg' j shs → NthG sg (j +' s₀) shs) →
           ({j c k : ℕ} {shs : Shapes c} {sh : Shape} → NthG sg' j shs → NthSh shs k sh → RowOK (j +' s₀) sh (row (j +' s₀) k)) →
           PerS Γ (SortT (SI n) (SD sg) FM ⌜Nat⌝) s₀ (sortMsF sg' s₀)
    perS []ᵒᵍ look oks = []ₚ
    perS {Γ = Γ} (shoks ∷ᵒᵍ okss) look oks =
      ⊢sortMeth ⊢⌜Nat⌝ (allSD ⊢SI (sigOK ok)) ⊢FM (nth-⌜⌝ₛₛ (nth-stels (look nthᵍ-z)))
                (perT (look nthᵍ-z) shoks (λ {j} n' → subst (λ m → NthSh _ m _) (sym (+'-zero j)) n')
                      (λ {j} n' → subst (λ m → RowOK _ _ (row _ m)) (sym (+'-zero j)) (oks nthᵍ-z n')))
      ∷ₚ perS okss (λ n' → look (nthᵍ-s n')) (λ n' → oks (nthᵍ-s n'))

  -- ★ THE FIBRE METHOD, typed from every row's typing
  ⊢FIBM : {Γ : Ctx} → ({s c k : ℕ} {shs : Shapes c} {sh : Shape} → NthG sg s shs → NthSh shs k sh → RowOK s sh (row s k)) →
          Γ ⊢ FIBM ∷ MethTy (SI n) (SD sg) FM
  ⊢FIBM oks =
    ⊢methₛ ⊢⌜Nat⌝ (⊢SD ok) ⊢FM
      (perS ok (λ {j} n' → subst (λ m → NthG _ m _) (sym (+'-zero j)) n')
               (λ {j} ng nh → subst (λ m → RowOK m _ (row m _)) (sym (+'-zero j)) (oks ng nh)))

  ----------------------------------------------------------------------
  -- 4. ★ IT COMPUTES: at constructor `k` of sort `s`, the fibre IS the row.
  ----------------------------------------------------------------------

  private
    nth-mFs : {c k₀ k : ℕ} (s : ℕ) {shs : Shapes c} {sh : Shape} → NthSh shs k sh →
              Nth (mFs {Δ = Δ} s shs k₀) k (mF (row s (k +' k₀)))
    nth-mFs s nthʰ-z      = nth-z
    nth-mFs s (nthʰ-s nt) = nth-s (nth-mFs s nt)

    nth-sortMsF : {m s₀ s c : ℕ} {sg' : Sig m} {shs : Shapes c} → NthG sg' s shs →
                  Nth (sortMsF {Δ = Δ} sg' s₀) s (lam (methAt (mFs (s +' s₀) shs zero)))
    nth-sortMsF nthᵍ-z      = nth-z
    nth-sortMsF (nthᵍ-s nt) = nth-s (nth-sortMsF nt)

  fib-β : {s c k : ℕ} {shs : Shapes c} {sh : Shape} {D j p c₀ : RTm Δ} → NthG sg s shs → NthSh shs k sh →
          app (ielim D (pair (tag s) j) FIBM (conₗ k p)) c₀ ⟶* R (row s k) j p c₀
  fib-β {Δ = Δ} {s = s} {k = k} {shs = shs} {D = D} {j} {p} {c₀} ng nh =
    ⟶*-trans (⟶*-appˡ (ιₛ-red nE nm))
      (subst (λ z → app (app (app z p) h) c₀ ⟶* R r j p c₀) (sym e0)
        (⟶*-trans (⟶*-appˡ (⟶*-appˡ (βcast t0 p (lam t1) e1)))
        (⟶*-trans (⟶*-appˡ (βcast t1 h (lam t2) e2))
                  (βcast t2 c₀ (R r j p c₀) e3))))
    where
      r = row s k
      nE : Nth (sortMsF {Δ = Δ} sg zero) s (lam (methAt (mFs s shs zero)))
      nE = subst (λ m → Nth (sortMsF sg zero) s (lam (methAt (mFs m shs zero)))) (+'-zero s) (nth-sortMsF ng)
      nm : Nth (mFs {Δ = Δ} s shs zero) k (mF r)
      nm = subst (λ m → Nth (mFs s shs zero) k (mF (row s m))) (+'-zero k) (nth-mFs s nh)
      h = dih D FIBM (app D (pair (tag s) j)) (pair (tag k) p)
      t0 : RTm (Δ ∙)
      t0 = lam (lam (R r (W3 j) (var (vs (vs vz))) (var vz)))
      t1 : RTm (Δ ∙)
      t1 = lam (R r (W2 j) (W2 p) (var vz))
      t2 : RTm (Δ ∙)
      t2 = R r (W1 j) (W1 p) (var vz)
      e0 : subTm (single j) (mF r) ≡ lam t0
      e0 = cong (λ X → lam (lam (lam X)))
                {x = subTm (extS (extS (extS (single j)))) (R r (var (vs (vs (vs vz)))) (var (vs (vs vz))) (var vz))}
                {y = R r (W3 j) (var (vs (vs vz))) (var vz)}
                (R-sub r (extS (extS (extS (single j)))) (var (vs (vs (vs vz)))) (var (vs (vs vz))) (var vz))
      e1 : subTm (single p) t0 ≡ lam t1
      e1 = cong (λ X → lam (lam X))
                {x = subTm (extS (extS (single p))) (R r (W3 j) (var (vs (vs vz))) (var vz))}
                {y = R r (W2 j) (W2 p) (var vz)}
                (trans (R-sub r (extS (extS (single p))) (W3 j) (var (vs (vs vz))) (var vz))
                       (cong (λ z → R r z (W2 p) (var vz)) {x = subTm (extS (extS (single p))) (W3 j)} {y = W2 j} (k2 p j)))
      e2 : subTm (single h) t1 ≡ lam t2
      e2 = cong lam
                {x = subTm (extS (single h)) (R r (W2 j) (W2 p) (var vz))}
                {y = R r (W1 j) (W1 p) (var vz)}
                (trans (R-sub r (extS (single h)) (W2 j) (W2 p) (var vz))
                       (cong₂ (λ a b → R r a b (var vz))
                              {x = subTm (extS (single h)) (W2 j)} {x' = W1 j} {y = subTm (extS (single h)) (W2 p)} {y' = W1 p}
                              (k1 h j) (k1 h p)))
      e3 : subTm (single c₀) t2 ≡ R r j p c₀
      e3 = trans (R-sub r (single c₀) (W1 j) (W1 p) (var vz))
                 (cong₂ (λ a b → R r a b c₀) {x = subTm (single c₀) (W1 j)} {x' = j} {y = subTm (single c₀) (W1 p)} {y' = p}
                        (k0 c₀ j) (k0 c₀ p))

  ----------------------------------------------------------------------
  -- 5. ★ CLOSED: the fibre method commutes with every substitution.
  ----------------------------------------------------------------------

  mF-sub : (σ : Sub Δ Θ) (r : Row) → subTm (extS σ) (mF {Δ} r) ≡ mF r
  mF-sub σ r = cong (λ X → lam (lam (lam X)))
                    {x = subTm (extS (extS (extS (extS σ)))) (R r (var (vs (vs (vs vz)))) (var (vs (vs vz))) (var vz))}
                    {y = R r (var (vs (vs (vs vz)))) (var (vs (vs vz))) (var vz)}
                    (R-sub r (extS (extS (extS (extS σ)))) (var (vs (vs (vs vz)))) (var (vs (vs vz))) (var vz))

  mFs-sub : {c : ℕ} (σ : Sub Δ Θ) (s : ℕ) (shs : Shapes c) (k : ℕ) → subC (extS σ) (mFs {Δ = Δ} s shs k) ≡ mFs s shs k
  mFs-sub σ s []ˢʰ         k = refl
  mFs-sub σ s (sh ∷ˢʰ shs) k = cong₂ _∷_ (mF-sub σ (row s k)) (mFs-sub σ s shs (suc k))

  sortMsF-sub : {m : ℕ} (σ : Sub Δ Θ) (sg' : Sig m) (s : ℕ) → subC σ (sortMsF {Δ = Δ} sg' s) ≡ sortMsF sg' s
  sortMsF-sub σ []ᵍ          s = refl
  sortMsF-sub σ (shs ∷ᵍ sg') s =
    cong₂ _∷_ (cong lam (trans {x = subTm (extS σ) (methAt (mFs s shs zero))}
                               {y = methAt (subC (extS σ) (mFs s shs zero))} {z = methAt (mFs s shs zero)}
                               (methAt-sub (extS σ) (mFs s shs zero))
                               (cong methAt {x = subC (extS σ) (mFs s shs zero)} {y = mFs s shs zero} (mFs-sub σ s shs zero))))
              (sortMsF-sub σ sg' (suc s))

  FIBM-sub : (σ : Sub Δ Θ) → subTm σ (FIBM {Δ}) ≡ FIBM
  FIBM-sub σ = trans {x = subTm σ (FIBM {_})} {y = methAt (subC σ (sortMsF sg zero))} {z = FIBM}
                     (methAt-sub σ (sortMsF sg zero))
                     (cong methAt {x = subC σ (sortMsF sg zero)} {y = sortMsF sg zero} (sortMsF-sub σ sg zero))

------------------------------------------------------------------------
-- 6. ★ A CONSTRUCTOR OF A ONE-ROW FIBRE: tag 0, then the row's payload.
------------------------------------------------------------------------

-- a constructor of a one-row fibre
⊢conRow : {Ξ : Ctx} {I D i C p : RTm ⌊ Ξ ⌋} → Ξ ⊢ I ∷ U → Ξ ⊢ D ∷ DescF I → Ξ ⊢ i ∷ El I →
          app D i ⟶* dσ (⌜Fin⌝ (num 1)) (selF (C ∷ [])) → Ξ ⊢ C ∷ Desc I → Ξ ⊢ p ∷ El (dpay I D C) → Ξ ⊢ conₗ 0 p ∷ IMu I D i
⊢conRow {Ξ} {I} {D} {i} {C} {p} dI dD di r dC dp =
  ⊢con-fib dI dD di r
    (⊢pay-σ dI dD (⊢selF dI (dC ∷ᵈ []ᵈ)) (⊢conv (⊢tag lt-z) (csymᵀ (credᵀ El-⌜Fin⌝)))
            (⊢conv dp (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (selF-β {Cs = C ∷ []} nth-z)))))))


-- ★ …and of an n-row fibre, at row `k`
⊢conRowₖ : {Ξ : Ctx} {c k : ℕ} {I D i C p : RTm ⌊ Ξ ⌋} {Cs : Cons ⌊ Ξ ⌋ c} → Nth Cs k C →
           Ξ ⊢ I ∷ U → Ξ ⊢ D ∷ DescF I → Ξ ⊢ i ∷ El I →
           app D i ⟶* dσ (⌜Fin⌝ (num c)) (selF Cs) → AllD Ξ I Cs → Ξ ⊢ p ∷ El (dpay I D C) → Ξ ⊢ conₗ k p ∷ IMu I D i
⊢conRowₖ {Ξ} {c} {k} {I} {D} {i} {C} {p} {Cs} nt dI dD di r ds dp =
  ⊢con-fib dI dD di r
    (⊢pay-σ dI dD (⊢selF dI ds) (⊢conv (⊢tag (nth-lt nt)) (csymᵀ (credᵀ El-⌜Fin⌝)))
            (⊢conv dp (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (selF-β {Cs = Cs} nt)))))))
