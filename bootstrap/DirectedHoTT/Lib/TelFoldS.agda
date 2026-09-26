------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ THE FOLD OF A SORTED FAMILY (`Lib/TelFold` over
-- `Lib/Sorted`).
--
-- Same algebra, same per-node fold `foldK`; the method is assembled
-- sort by sort (`⊢methₛ`), each sort's constructors at the index
-- `pair (tag s) j` (`⊢sortMeth`).  The fold never looks at the index, so
-- a mutual family folds exactly like a flat one.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.TelFoldS where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Metatheory.Premises using () renaming ( ⊢wkD to ⊢wkD' )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; Nth; nth-z; nth-s; tag; selF; selF-β; nth-sub; subC; conₗ; AllD; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.TelFold
  using ( Alg; module Alg; IhK; IhN-K; IhK-ren; K-ren; foldK; foldK-sub; ⊢foldK )
open import DirectedHoTT.Lib.MethAt
open import DirectedHoTT.Lib.Sorted
open import DirectedHoTT.Lib.TelAt

private
  variable
    Γ Δ : Cx
    c k n s : ℕ

-- `j +' k` counts `j` on from `k`, head case definitional (as `Lib/TelFold`)
infixl 30 _+'_
_+'_ : ℕ → ℕ → ℕ
zero  +' k = k
suc j +' k = j +' suc k

+'-suc : (j k : ℕ) → j +' suc k ≡ suc (j +' k)
+'-suc zero    k = refl
+'-suc (suc j) k = +'-suc j (suc k)

+'-zero : (j : ℕ) → j +' zero ≡ j
+'-zero zero    = refl
+'-zero (suc j) = trans (+'-suc j zero) (cong suc (+'-zero j))

module _ (A : Alg) where
  open Alg A

  -- constructor `k`'s method at an index: the node's fold
  mfoldAt : Tel Δ → RTm Γ
  mfoldAt T = lam (lam (nd (foldK A T (var vz))))

  foldMsAt : Tels Δ c → Cons Γ c
  foldMsAt []ᵗ       = []
  foldMsAt (T ∷ᵗ Ts) = mfoldAt T ∷ foldMsAt Ts

  -- one method per sort
  sortFolds : STels Δ n → Cons Γ n
  sortFolds []ˢᵗ        = []
  sortFolds (Ts ∷ˢᵗ Tss) = lam (methAt (foldMsAt Ts)) ∷ sortFolds Tss

  ⊢mfoldAt : {Γ : Ctx} {I D i : RTm ⌊ Γ ⌋} {σ : Sub Δ ⌊ Γ ⌋} {T : Tel Δ} {s : RTm ((⌊ Γ ⌋ ∙) ∙)} →
             Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → Γ ⊢ subTm σ ⌜ T ⌝ᵗ ∷ Desc I →
             Γ ⊢ mfoldAt T ∷ MethAt I D K i (subTm σ ⌜ T ⌝ᵗ) s
  ⊢mfoldAt {D = D} {i = i} {σ = σ} {T = T} {s = s} dI dD dC =
    ⊢methTσ {σ = σ} {T = T} dI dD ⊢K dC
      (⊢-cast (sym (K-sub (atS i s))) (⊢nd (⊢foldK A T (⊢-cast eq (⊢var here)))))
    where
      eq : renTy vs (IhN (vs ᵣ∘ₛ σ) T (renTm vs D) (wk1M K) (var vz)) ≡ IhK A T
      eq = trans (cong (renTy vs)
                   (trans (cong (λ M → IhN (vs ᵣ∘ₛ σ) T (renTm vs D) M (var vz)) (K-ren A _))
                          (IhN-K A (vs ᵣ∘ₛ σ) T (renTm vs D) (var vz))))
                 (IhK-ren A vs T)

  -- one list's methods at an index, each typed, with its lookup
  perAt : {Γ : Ctx} {I D i f : RTm ⌊ Γ ⌋} {σ : Sub Δ ⌊ Γ ⌋} {Ts : Tels Δ c} →
          Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → AllD Γ I (subC σ ⌜ Ts ⌝ₛ) →
          ({j : ℕ} {C : RTm Δ} → Nth ⌜ Ts ⌝ₛ j C → app f (tag (j +' k)) ⟶* subTm σ C) →
          PerKAt Γ I D K i f k (foldMsAt Ts)
  perAt {Ts = []ᵗ}     dI dD []ᵈ        look = []ₐ
  perAt {σ = σ} {Ts = T ∷ᵗ Ts} dI dD (dC ∷ᵈ ds) look =
    (look nth-z , ⊢mfoldAt {σ = σ} {T = T} dI dD dC) ∷ₐ perAt dI dD ds (λ n → look (nth-s n))

  private
    nth-AllSOK : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Tss : STels (⌊ Γ ⌋ ∙) n} {Ts : Tels (⌊ Γ ⌋ ∙) c} →
                 AllSOK Γ I Tss → NthST Tss s Ts → AllOK (Γ ▹ El I) (renTm vs I) Ts
    nth-AllSOK (ok ∷ˢᵒ _)   nthˢᵗ-z     = ok
    nth-AllSOK (_ ∷ˢᵒ oks) (nthˢᵗ-s n) = nth-AllSOK oks n

    perS : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {Tss : STels (⌊ Γ ⌋ ∙) n} {Tss' : STels (⌊ Γ ⌋ ∙) k} {s₀ : ℕ} →
           (Γ ▹ El (⌜Fin⌝ n)) ⊢ J ∷ U → AllSOK Γ (SortI J n) Tss →
           ({j c : ℕ} {Ts : Tels (⌊ Γ ⌋ ∙) c} → NthST Tss' j Ts → NthST Tss (j +' s₀) Ts) →
           PerS Γ (SortT (SortI J n) (Dₛₜ Tss) K J) s₀ (sortFolds Tss')
    perS {Tss' = []ˢᵗ} dJ oks lookS = []ₚ
    perS {Γ = Γ} {J = J} {Tss = Tss} {Tss' = Ts ∷ˢᵗ Tss'} {s₀ = s₀} dJ oks lookS =
      ⊢sortMeth dJ dss ⊢K (nth-⌜⌝ₛₛ ns)
        (subst (λ M → PerKAt _ _ _ M _ _ zero (foldMsAt Ts)) (sym (K-ren A (extR (extR vs))))
          (perAt (⊢wk dI) (⊢wkD' dD) (subAllDₛ s₀ dix (allD (⊢wk dI) (nth-AllSOK oks ns)))
                 (λ {j} n → subst (λ m → app (selF (subC (σₛ s₀) ⌜ Ts ⌝ₛ)) (tag m) ⟶* _)
                                  (sym (+'-zero j)) (selF-β (nth-sub (σₛ s₀) n)))))
      ∷ₚ perS dJ oks (λ n → lookS (nthˢᵗ-s n))
      where
        ns = lookS nthˢᵗ-z
        dI = ⊢SortI dJ
        dss = allSD dI oks
        dD = ⊢Dₛ dI dss
        dix = ⊢ιₛ dJ (nthS-lt (nth-⌜⌝ₛₛ ns))

  -- ★ the fold's one method
  ⊢foldₛ : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {Tss : STels (⌊ Γ ⌋ ∙) n} →
           (Γ ▹ El (⌜Fin⌝ n)) ⊢ J ∷ U → AllSOK Γ (SortI J n) Tss →
           Γ ⊢ methAt (sortFolds Tss) ∷ MethTy (SortI J n) (Dₛₜ Tss) K
  ⊢foldₛ dJ oks = ⊢methₛ dJ (⊢Dₛₜ dJ oks) ⊢K (perS dJ oks (λ {j} n → subst (λ m → NthST _ m _) (sym (+'-zero j)) n))

  -- ★ …AND IT COMPUTES: ι, two β, the body's substitution through the fold
  nth-foldMsAt : {Ts : Tels Δ c} {T : Tel Δ} → NthT Ts k T → Nth (foldMsAt {Γ = Γ} Ts) k (mfoldAt T)
  nth-foldMsAt nthᵗ-z     = nth-z
  nth-foldMsAt (nthᵗ-s n) = nth-s (nth-foldMsAt n)

  nth-sortFolds : {Tss : STels Δ n} {Ts : Tels Δ c} → NthST Tss s Ts →
                  Nth (sortFolds {Γ = Γ} Tss) s (lam (methAt (foldMsAt Ts)))
  nth-sortFolds nthˢᵗ-z     = nth-z
  nth-sortFolds (nthˢᵗ-s n) = nth-s (nth-sortFolds n)

  fold-ιₛ : {Tss : STels (Δ ∙) n} {Ts : Tels (Δ ∙) c} {T : Tel (Δ ∙)} {j p : RTm Δ} →
            NthST Tss s Ts → NthT Ts k T →
            ielim (Dₛₜ Tss) (pair (tag s) j) (methAt (sortFolds Tss)) (conₗ k p)
              ⟶* nd (foldK A T (dihN (single (pair (tag s) j)) T (Dₛₜ Tss) (methAt (sortFolds Tss)) p))
  fold-ιₛ {s = s} {Tss = Tss} {T = T} {j} {p} ns nt =
    ⟶*-trans (ιₛT ns nt (nth-sortFolds ns) (nth-foldMsAt nt))
      (step (ξ-appˡ (β _ p))
      (step (β _ h)
        (subst (λ t → t ⟶* nd (foldK A T h)) (sym body) done)))
    where
      h = dihN (single (pair (tag s) j)) T (Dₛₜ Tss) (methAt (sortFolds Tss)) p
      σ₁ = extS (extS (single j))
      σ₂ = extS (single p)
      body : subTm (single h) (subTm σ₂ (subTm σ₁ (nd (foldK A T (var vz))))) ≡ nd (foldK A T h)
      body = trans (cong (λ t → subTm (single h) (subTm σ₂ t))
                         (trans (nd-sub σ₁ _) (cong nd (foldK-sub A σ₁ T (var vz)))))
             (trans (cong (subTm (single h))
                          (trans (nd-sub σ₂ _) (cong nd (foldK-sub A σ₂ T (var vz)))))
             (trans (nd-sub (single h) _) (cong nd (foldK-sub A (single h) T (var vz)))))
