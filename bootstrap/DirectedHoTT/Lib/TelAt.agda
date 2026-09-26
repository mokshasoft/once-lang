------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ TELESCOPES AT AN INDEX TERM, and SORTED
-- TELESCOPES.
--
-- `Lib/Tel` reads a constructor's method along its telescope with the
-- index a BINDER (`⊢methT`).  Here the index is a TERM `i` and the
-- telescope carries a PENDING SUBSTITUTION `σ` (its index variable
-- instantiated) — the per-constructor method `Lib/MethAt` and
-- `Lib/Sorted` want, written against the hypotheses' and payload's
-- normal forms (`IhN`, `PayN`).
--
-- Then the sorted surface: one `Tels` per sort (`STels`), constructors
-- (`⊢conₛₜ`) and the computation rule with the hypotheses walked
-- (`ιₛT`).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.TelAt where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _×_; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-appʳ; ⟶*-dihᶜ; red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; conv-ctx; sub-lemma )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( subTm-var )
open import DirectedHoTT.Metatheory.Premises using ( mot-ren; ⊢wkD )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; Nth; nth-z; nth-s; tag; selF; selF-β; nth-sub; subC; conₗ; AllD )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.MethAt
open import DirectedHoTT.Lib.Sorted

private
  variable
    Γ Δ : Cx
    c k n s : ℕ

------------------------------------------------------------------------
-- 1. ★ ONE CONSTRUCTOR'S METHOD AT `i`, along its telescope.
------------------------------------------------------------------------

-- the method's context: the payload of the telescope under `σ`, the
--   hypotheses in normal form
HypAt : (Γ : Ctx) → RTm ⌊ Γ ⌋ → RTm ⌊ Γ ⌋ → RTy ((⌊ Γ ⌋ ∙) ∙) → Sub Δ ⌊ Γ ⌋ → Tel Δ → Ctx
HypAt Γ I D M σ T =
  (Γ ▹ El (dpay I D (subTm σ ⌜ T ⌝ᵗ))) ▹ IhN (vs ᵣ∘ₛ σ) T (renTm vs D) (wk1M M) (var vz)

hypsAt≅ : (σ : Sub Δ Γ) (T : Tel Δ) (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
          DIh (renTm vs D) (wk1M M) (renTm vs (subTm σ ⌜ T ⌝ᵗ)) (var vz)
            ≅ᵀ IhN (vs ᵣ∘ₛ σ) T (renTm vs D) (wk1M M) (var vz)
hypsAt≅ σ T D M =
  red→≅ᵀ (subst (λ C → DIh (renTm vs D) (wk1M M) C (var vz) ⟶ᵀ* IhN (vs ᵣ∘ₛ σ) T (renTm vs D) (wk1M M) (var vz))
                (sym (renTm-subTm ⌜ T ⌝ᵗ))
                (ihN-red (vs ᵣ∘ₛ σ) T (renTm vs D) (wk1M M) (var vz)))

-- ★ the per-constructor method at `i`
⊢methTσ : {Γ : Ctx} {I D i : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {σ : Sub Δ ⌊ Γ ⌋} {T : Tel Δ}
          {s b : RTm ((⌊ Γ ⌋ ∙) ∙)} →
          Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → motCtx Γ I D ⊢ty M → Γ ⊢ subTm σ ⌜ T ⌝ᵗ ∷ Desc I →
          HypAt Γ I D M σ T ⊢ b ∷ subTy (atS i s) M →
          Γ ⊢ lam (lam b) ∷ MethAt I D M i (subTm σ ⌜ T ⌝ᵗ) s
⊢methTσ {D = D} {M = M} {σ = σ} {T = T} dI dD dM dC db =
  ⊢lam (ty-El (⊢dpay dI dD dC)) (⊢lam dH (conv-ctx (csymᵀ (hypsAt≅ σ T D M)) db))
  where dH = ty-DIh (⊢wk dI) (⊢wkD dD) (mot-ren there dM) (⊢wk dC) (⊢var here)

-- ★ the method's PAYLOAD variable, at its normal form
⊢payAt : {Γ : Ctx} {I D : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {σ : Sub Δ ⌊ Γ ⌋} {T : Tel Δ} →
         HypAt Γ I D M σ T ⊢ var (vs vz) ∷
           PayN (vs ᵣ∘ₛ (vs ᵣ∘ₛ σ)) T (renTm vs (renTm vs I)) (renTm vs (renTm vs D))
⊢payAt {Γ = Γ} {I} {D} {M} {σ} {T} =
  ⊢conv (subst (λ C → HypAt Γ I D M σ T ⊢ var (vs vz) ∷ El (dpay I₂ D₂ C))
               (trans (cong (renTm vs) (renTm-subTm ⌜ T ⌝ᵗ)) (renTm-subTm ⌜ T ⌝ᵗ))
               (⊢var (there here)))
        (red→≅ᵀ (payN-red (vs ᵣ∘ₛ (vs ᵣ∘ₛ σ)) T I₂ D₂))
  where I₂ = renTm vs (renTm vs I)
        D₂ = renTm vs (renTm vs D)

------------------------------------------------------------------------
-- 2. ★ SORTED TELESCOPES.
------------------------------------------------------------------------

infixr 5 _∷ˢᵗ_ _∷ˢᵒ_
data STels (Δ : Cx) : ℕ → Set where
  []ˢᵗ  : STels Δ zero
  _∷ˢᵗ_ : Tels Δ c → STels Δ n → STels Δ (suc n)

⌜_⌝ₛₛ : STels Δ n → SCons Δ n
⌜ []ˢᵗ ⌝ₛₛ      = []ˢ
⌜ Ts ∷ˢᵗ Tss ⌝ₛₛ = ⌜ Ts ⌝ₛ ∷ˢ ⌜ Tss ⌝ₛₛ

data NthST : STels Δ n → ℕ → Tels Δ c → Set where
  nthˢᵗ-z : {Ts : Tels Δ c} {Tss : STels Δ n} → NthST (Ts ∷ˢᵗ Tss) zero Ts
  nthˢᵗ-s : {Ts : Tels Δ c} {Ts' : Tels Δ k} {Tss : STels Δ n} →
            NthST Tss s Ts → NthST (Ts' ∷ˢᵗ Tss) (suc s) Ts

nth-⌜⌝ₛₛ : {Tss : STels Δ n} {Ts : Tels Δ c} → NthST Tss s Ts → NthS ⌜ Tss ⌝ₛₛ s ⌜ Ts ⌝ₛ
nth-⌜⌝ₛₛ nthˢᵗ-z     = nthˢ-z
nth-⌜⌝ₛₛ (nthˢᵗ-s n) = nthˢ-s (nth-⌜⌝ₛₛ n)

data AllSOK (Γ : Ctx) (I : RTm ⌊ Γ ⌋) : STels (⌊ Γ ⌋ ∙) n → Set where
  []ˢᵒ  : AllSOK Γ I []ˢᵗ
  _∷ˢᵒ_ : {Ts : Tels (⌊ Γ ⌋ ∙) c} {Tss : STels (⌊ Γ ⌋ ∙) n} →
          AllOK (Γ ▹ El I) (renTm vs I) Ts → AllSOK Γ I Tss → AllSOK Γ I (Ts ∷ˢᵗ Tss)

allSD : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Tss : STels (⌊ Γ ⌋ ∙) n} →
        Γ ⊢ I ∷ U → AllSOK Γ I Tss → AllSD Γ I ⌜ Tss ⌝ₛₛ
allSD dI []ˢᵒ         = []ᵃ
allSD dI (ok ∷ˢᵒ oks) = allD (⊢wk dI) ok ∷ᵃ allSD dI oks

-- the family of a sorted telescope list
Dₛₜ : STels (Δ ∙) n → RTm Δ
Dₛₜ Tss = Dₛ ⌜ Tss ⌝ₛₛ

⊢Dₛₜ : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {Tss : STels (⌊ Γ ⌋ ∙) n} →
       (Γ ▹ El (⌜Fin⌝ n)) ⊢ J ∷ U → AllSOK Γ (SortI J n) Tss → Γ ⊢ Dₛₜ Tss ∷ DescF (SortI J n)
⊢Dₛₜ dJ oks = ⊢Dₛ (⊢SortI dJ) (allSD (⊢SortI dJ) oks)

-- ★ constructor `k` of sort `s`, its payload read along the telescope
⊢conₛₜ : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {Tss : STels (⌊ Γ ⌋ ∙) n} {Ts : Tels (⌊ Γ ⌋ ∙) c}
         {T : Tel (⌊ Γ ⌋ ∙)} {j p : RTm ⌊ Γ ⌋} →
         (Γ ▹ El (⌜Fin⌝ n)) ⊢ J ∷ U → AllSOK Γ (SortI J n) Tss → NthST Tss s Ts → NthT Ts k T →
         Γ ⊢ j ∷ El (subTm (single (tag s)) J) →
         Γ ⊢ p ∷ El (dpay (SortI J n) (Dₛₜ Tss) (subTm (single (pair (tag s) j)) ⌜ T ⌝ᵗ)) →
         Γ ⊢ conₗ k p ∷ IMu (SortI J n) (Dₛₜ Tss) (pair (tag s) j)
⊢conₛₜ dJ oks ns nt dj dp = ⊢conₛ dJ (allSD (⊢SortI dJ) oks) (nth-⌜⌝ₛₛ ns) (nth-⌜⌝ nt) dj dp

------------------------------------------------------------------------
-- 3. ★ …AND IT COMPUTES, the hypotheses walked (`dihN`).
------------------------------------------------------------------------

-- the fibre at a sorted index, then the tag layer, peeled
dihₛ : {Css : SCons (Δ ∙) n} {Cs : Cons (Δ ∙) c} {C : RTm (Δ ∙)} {e j p : RTm Δ} →
       NthS Css s Cs → Nth Cs k C →
       dih (Dₛ Css) e (app (Dₛ Css) (pair (tag s) j)) (pair (tag k) p)
         ⟶* dih (Dₛ Css) e (subTm (single (pair (tag s) j)) C) p
dihₛ {s = s} {k = k} {Cs = Cs} {j = j} {p = p} ns nt =
  ⟶*-trans (⟶*-dihᶜ (fibₛ-β j ns))
   (step (dih-σ _ _ _ _ _)
   (step (ξ-dihᶜ (ξ-appʳ (βfst _ _)))
   (step (ξ-dihᵖ (βsnd _ _))
     (⟶*-dihᶜ (selF-β (nth-sub (single (pair (tag s) j)) nt))))))

ιₛT : {Tss : STels (Δ ∙) n} {Ts : Tels (Δ ∙) c} {T : Tel (Δ ∙)} {Es : Cons Δ n} {ms : Cons (Δ ∙) c}
      {m : RTm (Δ ∙)} {j p : RTm Δ} →
      NthST Tss s Ts → NthT Ts k T → Nth Es s (lam (methAt ms)) → Nth ms k m →
      ielim (Dₛₜ Tss) (pair (tag s) j) (methAt Es) (conₗ k p)
        ⟶* app (app (subTm (single j) m) p)
               (dihN (single (pair (tag s) j)) T (Dₛₜ Tss) (methAt Es) p)
ιₛT {s = s} {Tss = Tss} {T = T} {Es = Es} {j = j} {p = p} ns nt nE nm =
  ⟶*-trans (ιₛ-red nE nm)
    (⟶*-appʳ (⟶*-trans (dihₛ (nth-⌜⌝ₛₛ ns) (nth-⌜⌝ nt))
                        (dihN-red (single (pair (tag s) j)) T (Dₛₜ Tss) (methAt Es) p)))

------------------------------------------------------------------------
-- 4. ★ ONE METHOD ENTRY of a sorted family: constructor `k` of sort `s`,
--    its body against the normal forms at `ιₛ s` (`HypAt`), with its
--    lookup — what `⊢sortMeth`'s `PerKAt` list is built from.
------------------------------------------------------------------------

nth-AllSOK : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Tss : STels (⌊ Γ ⌋ ∙) n} {Ts : Tels (⌊ Γ ⌋ ∙) c} →
             AllSOK Γ I Tss → NthST Tss s Ts → AllOK (Γ ▹ El I) (renTm vs I) Ts
nth-AllSOK (ok ∷ˢᵒ _)   nthˢᵗ-z     = ok
nth-AllSOK (_ ∷ˢᵒ oks) (nthˢᵗ-s n) = nth-AllSOK oks n

nth-OK : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Ts : Tels ⌊ Γ ⌋ c} {T : Tel ⌊ Γ ⌋} →
         AllOK Γ I Ts → NthT Ts k T → TelOK Γ I T
nth-OK (ok ∷ᵒ _)   nthᵗ-z     = ok
nth-OK (_ ∷ᵒ oks) (nthᵗ-s n) = nth-OK oks n

entₛ : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {Tss : STels (⌊ Γ ⌋ ∙) n} {Ts : Tels (⌊ Γ ⌋ ∙) c}
       {T : Tel (⌊ Γ ⌋ ∙)} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {b : RTm (((⌊ Γ ⌋ ∙) ∙) ∙)} →
       (Γ ▹ El (⌜Fin⌝ n)) ⊢ J ∷ U → AllSOK Γ (SortI J n) Tss → motCtx Γ (SortI J n) (Dₛₜ Tss) ⊢ty M →
       NthST Tss s Ts → NthT Ts k T →
       HypAt (Γ ▹ El (subTm (single (tag s)) J)) (renTm vs (SortI J n)) (renTm vs (Dₛₜ Tss)) (wk1M M) (σₛ s) T
         ⊢ b ∷ subTy (atS (ιₛ s) (conₗ k (var (vs vz)))) (wk1M M) →
       (app (selF (subC (σₛ s) ⌜ Ts ⌝ₛ)) (tag k) ⟶* subTm (σₛ s) ⌜ T ⌝ᵗ)
       × ((Γ ▹ El (subTm (single (tag s)) J))
            ⊢ lam (lam b) ∷ MethKAt (renTm vs (SortI J n)) (renTm vs (Dₛₜ Tss)) (wk1M M) (ιₛ s) (subTm (σₛ s) ⌜ T ⌝ᵗ) k)
entₛ {n = n} {s = s} {Γ = Γ} {J = J} {Tss} {Ts} {T} {M} dJ oks dM ns nt db =
  selF-β (nth-sub (σₛ s) (nth-⌜⌝ nt)) ,
  ⊢methTσ {σ = σₛ s} {T = T} (⊢wk dI) (⊢wkD (⊢Dₛₜ dJ oks)) (mot-ren there dM) dC db
  where
    dI = ⊢SortI dJ
    dix = ⊢ιₛ dJ (nthS-lt (nth-⌜⌝ₛₛ ns))
    dC = ⊢-cast (cong Desc (fl-σₛ' s (SortI J n)))
                (sub-lemma (⊢tel (⊢wk dI) (nth-OK (nth-AllSOK oks ns) nt)) (hσₛ s dix))
      where
        fl-σₛ' : (s : ℕ) (t : RTm ⌊ Γ ⌋) → subTm (σₛ s) (renTm vs t) ≡ renTm vs t
        fl-σₛ' s t = trans (subTm-renTm t) (subTm-var vs t)
