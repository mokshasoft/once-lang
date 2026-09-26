------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ SORTED FAMILIES: a family presented BY FIBRES OVER
-- A SORT.
--
-- A mutual family (the Knot's `RTy`/`RTm`, `Examples/Mutual`) is one
-- family over `I = Σ (s : Fin ns) (J s)`, and its fibre over `(s , j)` is
-- the constructors OF SORT `s` (D074: fibres of the target map are the
-- definition — no sort Ford, no Id-vs-Hom commitment on the tag):
--
--   Dₛ Css = λ i. sel [Dσ Cs₀, …, Dσ Cs_{ns-1}] (fst i)
--
-- with each `Csₛ` a constructor list over the index (`Lib/Sugar`).
--
-- ★ THE METHODS PATTERN-MATCH ON THE INDEX.  At an abstract index the
--   fibre is stuck on `fst i`, so the one method splits the index
--   (`psplit`), selects by sort, and hands each sort's method the index
--   `pair (tag s) j` — where the fibre computes (`fibₛ-β`), and
--   `Lib/MethAt`'s method-at-an-index-term does the rest.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Sorted where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _×_; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-dpayᶜ; ⟶ᵀ*-El; red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶*-ren; ⟶*-appˡ; ⟶ᵀ*-Σˡ )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var; subTm-var )
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢wk; ⊢-cast; wk-cancel-tm; ren-ty; sub-ty; Ren⊢-ext; ren-lemma; Ren⊢; ∋-cast
        ; conv-ctxᵀ; conv-ctx; sub-lemma; Sub⊢ )
open import DirectedHoTT.Metatheory.Premises using ( mot-ren; ⊢wkD; MethTy-wf; pairS⊢ )
open import DirectedHoTT.Metatheory.Validity using ( wk-app-vz )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; wkC; subC; Nth; nth-z; nth-s; tag; sel; selF; Dσ; conₗ
        ; sel-sub; sel-β; selF-β; selF-sub; nth-sub; subC-wkC
        ; AllD; []ᵈ; _∷ᵈ_; ⊢sel; ⊢selF; ⊢Dσ; subAllD; ⊢con-fib; ⊢pay-σ; ⊢tag; nth-lt; Lt; lt-z; lt-s
        ; selM; tag-ren; AllQ; []q; _∷q_; castQ; ⊢selG; fsucsS; fsucsS-zero; fsucsS-suc; fsucsS-head; wk-single-tag )
open import DirectedHoTT.Lib.MethAt

private
  variable
    Γ Δ Θ : Cx
    c k n s : ℕ

------------------------------------------------------------------------
-- 1. THE FAMILY.
------------------------------------------------------------------------

-- one constructor list per sort (each with its own length)
infixr 5 _∷ˢ_
data SCons (Δ : Cx) : ℕ → Set where
  []ˢ  : SCons Δ zero
  _∷ˢ_ : Cons Δ c → SCons Δ n → SCons Δ (suc n)

-- sort `s`'s list
data NthS : SCons Δ n → ℕ → Cons Δ c → Set where
  nthˢ-z : {Cs : Cons Δ c} {Css : SCons Δ n} → NthS (Cs ∷ˢ Css) zero Cs
  nthˢ-s : {Cs : Cons Δ c} {Cs' : Cons Δ k} {Css : SCons Δ n} →
           NthS Css s Cs → NthS (Cs' ∷ˢ Css) (suc s) Cs

-- the per-sort fibres, as one list of descriptions
SDs : SCons (Δ ∙) n → Cons (Δ ∙) n
SDs []ˢ         = []
SDs (Cs ∷ˢ Css) = Dσ Cs ∷ SDs Css

nth-SDs : {Css : SCons (Δ ∙) n} {Cs : Cons (Δ ∙) c} → NthS Css s Cs → Nth (SDs Css) s (Dσ Cs)
nth-SDs nthˢ-z      = nth-z
nth-SDs (nthˢ-s nt) = nth-s (nth-SDs nt)

-- ★ THE FAMILY: the fibre over `i` is sort `fst i`'s constructors
Dₛ : SCons (Δ ∙) n → RTm Δ
Dₛ Css = lam (sel (SDs Css) (fst (var vz)))

-- every sort's entries are descriptions over `I` (over the index)
infixr 5 _∷ᵃ_
data AllSD (Γ : Ctx) (I : RTm ⌊ Γ ⌋) : SCons (⌊ Γ ⌋ ∙) n → Set where
  []ᵃ  : AllSD Γ I []ˢ
  _∷ᵃ_ : {Cs : Cons (⌊ Γ ⌋ ∙) c} {Css : SCons (⌊ Γ ⌋ ∙) n} →
         AllD (Γ ▹ El I) (renTm vs I) Cs → AllSD Γ I Css → AllSD Γ I (Cs ∷ˢ Css)

nth-AllSD : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Css : SCons (⌊ Γ ⌋ ∙) n} {Cs : Cons (⌊ Γ ⌋ ∙) c} →
            AllSD Γ I Css → NthS Css s Cs → AllD (Γ ▹ El I) (renTm vs I) Cs
nth-AllSD (ds ∷ᵃ _)  nthˢ-z      = ds
nth-AllSD (_ ∷ᵃ dss) (nthˢ-s nt) = nth-AllSD dss nt

private
  allSDs : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Css : SCons (⌊ Γ ⌋ ∙) n} →
           Γ ⊢ I ∷ U → AllSD Γ I Css → AllD (Γ ▹ El I) (renTm vs I) (SDs Css)
  allSDs dI []ᵃ         = []ᵈ
  allSDs dI (ds ∷ᵃ dss) = ⊢Dσ dI ds ∷ᵈ allSDs dI dss

-- the index code `Σ (s : Fin ns) J` decodes to a `Σ'`
SortI : RTm (Δ ∙) → ℕ → RTm Δ
SortI J n = ⌜Σ⌝ (⌜Fin⌝ n) J

unSortI : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {i : RTm ⌊ Γ ⌋} →
          Γ ⊢ i ∷ El (SortI J n) → Γ ⊢ i ∷ Σ' (El (⌜Fin⌝ n)) (El J)
unSortI d = ⊢conv d (credᵀ (El-⌜Σ⌝ _ _))

-- the sort of an index
⊢sortOf : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {i : RTm ⌊ Γ ⌋} →
          Γ ⊢ i ∷ El (SortI J n) → Γ ⊢ fst i ∷ Fin n
⊢sortOf d = ⊢conv (⊢fst (unSortI d)) (credᵀ El-⌜Fin⌝)

-- ★ (a) the family types
⊢Dₛ : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {Css : SCons (⌊ Γ ⌋ ∙) n} →
      Γ ⊢ SortI J n ∷ U → AllSD Γ (SortI J n) Css → Γ ⊢ Dₛ Css ∷ DescF (SortI J n)
⊢Dₛ dI dss = ⊢lam (ty-El dI) (⊢sel (⊢wk dI) (allSDs dI dss) (⊢sortOf (⊢var here)))

------------------------------------------------------------------------
-- 2. ★ THE FIBRE COMPUTES AT A SORTED INDEX.
------------------------------------------------------------------------

-- the selection's scrutinee steps under it
sel-fst : (Cs : Cons Δ c) (a b : RTm Δ) → sel Cs (fst (pair a b)) ⟶* sel Cs a
sel-fst []       a b = step (ξ-fcase0 (βfst a b)) done
sel-fst (C ∷ Cs) a b = step (ξ-fcaseᵗ (βfst a b)) done

-- the fibre under ANY substitution that puts a sorted pair at the index
fibₛ-sub : {Css : SCons (Δ ∙) n} {Cs : Cons (Δ ∙) c} (σ : Sub (Δ ∙) Θ) (j : RTm Θ) →
           NthS Css s Cs → σ vz ≡ pair (tag s) j →
           subTm σ (sel (SDs Css) (fst (var vz))) ⟶* dσ (⌜Fin⌝ c) (selF (subC σ Cs))
fibₛ-sub {c = c} {s = s} {Css = Css} {Cs = Cs} σ j nt e =
  subst (λ X → X ⟶* R) (sym (sel-sub σ (SDs Css) (fst (var vz))))
    (subst (λ z → sel (subC σ (SDs Css)) (fst z) ⟶* R) (sym e)
      (⟶*-trans (sel-fst (subC σ (SDs Css)) (tag s) j)
        (subst (λ X → sel (subC σ (SDs Css)) (tag s) ⟶* dσ (⌜Fin⌝ c) X) (selF-sub σ Cs)
               (sel-β (nth-sub σ (nth-SDs nt))))))
  where R = dσ (⌜Fin⌝ c) (selF (subC σ Cs))

-- ★ the fibre over `(tag s , j)` is sort `s`'s constructors, at the index
fibₛ-β : {Css : SCons (Δ ∙) n} {Cs : Cons (Δ ∙) c} (j : RTm Δ) → NthS Css s Cs →
         app (Dₛ Css) (pair (tag s) j) ⟶* dσ (⌜Fin⌝ c) (selF (subC (single (pair (tag s) j)) Cs))
fibₛ-β {s = s} {Css = Css} j nt =
  step (β _ _) (fibₛ-sub (single (pair (tag s) j)) j nt refl)

-- …and the same for the family WEAKENED (a method's own binder in scope)
fibₛ-wk : {Css : SCons (Δ ∙) n} {Cs : Cons (Δ ∙) c} (j : RTm (Δ ∙)) → NthS Css s Cs →
          app (renTm vs (Dₛ Css)) (pair (tag s) j)
            ⟶* dσ (⌜Fin⌝ c) (selF (subC (single (pair (tag s) j) ₛ∘ᵣ extR vs) Cs))
fibₛ-wk {s = s} {Css = Css} j nt =
  step (β _ _)
    (subst (λ X → X ⟶* _) (sym (subTm-renTm (sel (SDs Css) (fst (var vz)))))
           (fibₛ-sub (single (pair (tag s) j) ₛ∘ᵣ extR vs) j nt refl))

------------------------------------------------------------------------
-- 3. ★ (b) CONSTRUCTOR `k` OF SORT `s`, at `(tag s , j)`.
------------------------------------------------------------------------

⊢ixₛ : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {j : RTm ⌊ Γ ⌋} {s n : ℕ} →
       (Γ ▹ El (⌜Fin⌝ n)) ⊢ J ∷ U → Lt s n → Γ ⊢ j ∷ El (subTm (single (tag s)) J) →
       Γ ⊢ pair (tag s) j ∷ El (SortI J n)
⊢ixₛ dJ lt dj =
  ⊢conv (⊢pair (ty-El dJ) (⊢conv (⊢tag lt) (csymᵀ (credᵀ El-⌜Fin⌝))) dj) (csymᵀ (credᵀ (El-⌜Σ⌝ _ _)))

⊢SortI : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} → (Γ ▹ El (⌜Fin⌝ n)) ⊢ J ∷ U → Γ ⊢ SortI J n ∷ U
⊢SortI dJ = ⊢⌜Σ⌝ ⊢⌜Fin⌝ dJ

nthS-lt : {Css : SCons Δ n} {Cs : Cons Δ c} → NthS Css s Cs → Lt s n
nthS-lt nthˢ-z      = lt-z
nthS-lt (nthˢ-s nt) = lt-s (nthS-lt nt)

-- ★ constructor `k` of sort `s`: a payload of its telescope AT THE INDEX
⊢conₛ : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {Css : SCons (⌊ Γ ⌋ ∙) n} {Cs : Cons (⌊ Γ ⌋ ∙) c}
        {C : RTm (⌊ Γ ⌋ ∙)} {j p : RTm ⌊ Γ ⌋} →
        (Γ ▹ El (⌜Fin⌝ n)) ⊢ J ∷ U → AllSD Γ (SortI J n) Css → NthS Css s Cs → Nth Cs k C →
        Γ ⊢ j ∷ El (subTm (single (tag s)) J) →
        Γ ⊢ p ∷ El (dpay (SortI J n) (Dₛ Css) (subTm (single (pair (tag s) j)) C)) →
        Γ ⊢ conₗ k p ∷ IMu (SortI J n) (Dₛ Css) (pair (tag s) j)
⊢conₛ {s = s} {j = j} dJ dss nts nt dj dp =
  ⊢con-fib dI dD dix (fibₛ-β j nts)
    (⊢pay-σ dI dD (⊢selF dI (subAllD (nth-AllSD dss nts) dix))
            (⊢conv (⊢tag (nth-lt nt)) (csymᵀ (credᵀ El-⌜Fin⌝)))
            (⊢conv dp (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (selF-β (nth-sub (single (pair (tag s) j)) nt))))))))
  where
    dI = ⊢SortI dJ
    dD = ⊢Dₛ dI dss
    dix = ⊢ixₛ dJ (nthS-lt nts) dj

------------------------------------------------------------------------
-- 4. ★★ THE ONE METHOD: split the index, select by sort.
--
--   The kernel's method body `T₀` (the method at the index VARIABLE,
--   `MethTy-At`) re-based at the split index is `subTy pairS T₀`; over
--   the sort it is `SortT`, and sort `s`'s method inhabits its instance at
--   `tag s`.  The one method is `methAt` again — split, select, apply —
--   now splitting the INDEX.
------------------------------------------------------------------------

T₀ : RTm Δ → RTm Δ → RTy ((Δ ∙) ∙) → RTy (Δ ∙)
T₀ I D M = MethAt (renTm vs I) (renTm vs D) (wk1M M) (var vz) (app (renTm vs D) (var vz)) (con (var (vs vz)))

SortT : RTm Δ → RTm Δ → RTy ((Δ ∙) ∙) → RTm (Δ ∙) → RTy (Δ ∙)
SortT I D M J = Π (El J) (subTy pairS (T₀ I D M))

private
  Π-cod : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {B : RTy (⌊ Γ ⌋ ∙)} → Γ ⊢ty Π A B → (Γ ▹ A) ⊢ty B
  Π-cod (ty-Π _ d) = d

  w3 : Ren Δ (((Δ ∙) ∙) ∙)
  w3 x = vs (vs (vs x))

  ren3ᵀ : (A : RTy Δ) → renTy vs (renTy vs (renTy vs A)) ≡ renTy w3 A
  ren3ᵀ A = trans (cong (renTy vs) (renTy-renTy A)) (renTy-renTy A)

  sr-flat : {Θ Ξ Ω : Cx} (σ : Sub Θ Ξ) (ρ : Ren Ω Θ) (ρ' : Ren Ω Ξ) →
            (∀ x → σ (ρ x) ≡ var (ρ' x)) → (t : RTm Ω) → subTm σ (renTm ρ t) ≡ renTm ρ' t
  sr-flat σ ρ ρ' h t = trans (subTm-renTm t) (trans (subTm-cong h t) (subTm-var ρ' t))

⊢T₀ : {Γ : Ctx} {I D : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} →
      Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → motCtx Γ I D ⊢ty M → (Γ ▹ El I) ⊢ty T₀ I D M
⊢T₀ {Γ} {I} {D} {M} dI dD dM = Π-cod (subst (λ X → Γ ⊢ty X) (MethTy-At I D M) (MethTy-wf dI dD dM))

-- the index decodes to the split's `Σ'`
elSortI : {J : RTm (Δ ∙)} → El (SortI J n) ≅ᵀ Σ' (Fin n) (El J)
elSortI = red→≅ᵀ (stepᵀ (El-⌜Σ⌝ _ _) (⟶ᵀ*-Σˡ (stepᵀ El-⌜Fin⌝ doneᵀ)))

⊢SortT : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {D : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} →
         (Γ ▹ El (⌜Fin⌝ n)) ⊢ J ∷ U → Γ ⊢ D ∷ DescF (SortI J n) → motCtx Γ (SortI J n) D ⊢ty M →
         (Γ ▹ Fin n) ⊢ty SortT (SortI J n) D M J
⊢SortT dJ dD dM =
  ty-Π (ty-El dJ') (sub-ty (conv-ctxᵀ elSortI (⊢T₀ (⊢SortI dJ) dD dM)) (pairS⊢ (ty-El dJ')))
  where dJ' = conv-ctx (credᵀ El-⌜Fin⌝) dJ

-- one method PER SORT, each at its instance of the sort-generic type
infixr 5 _∷ₚ_
data PerS (Γ : Ctx) (Q : RTy (⌊ Γ ⌋ ∙)) : ℕ → {n : ℕ} → Cons ⌊ Γ ⌋ n → Set where
  []ₚ  : {k : ℕ} → PerS Γ Q k []
  _∷ₚ_ : {k n : ℕ} {E : RTm ⌊ Γ ⌋} {Es : Cons ⌊ Γ ⌋ n} →
         Γ ⊢ E ∷ subTy (single (tag k)) Q → PerS Γ Q (suc k) Es → PerS Γ Q k (E ∷ Es)

private
  mkAllQS : {Γ : Ctx} {Q : RTy (⌊ Γ ⌋ ∙)} {B : RTy ⌊ Γ ⌋} {k n : ℕ} {Es : Cons ⌊ Γ ⌋ n} →
            PerS Γ Q k Es → AllQ (Γ ▹ B) (subTy (fsucsS k) (renTy (extR vs) Q)) (wkC Es)
  mkAllQS []ₚ = []q
  mkAllQS {Q = Q} {k = k} (dE ∷ₚ ps) =
    ⊢-cast (sym (trans (fsucsS-head k (renTy (extR vs) Q)) (wk-single-tag k Q))) (⊢wk dE)
    ∷q castQ (sym (fsucsS-suc k (renTy (extR vs) Q))) (mkAllQS ps)

-- ★ a selector over ANY motive: entry `k` at `Q[tag k]`
⊢selQ : {Γ : Ctx} {Q : RTy (⌊ Γ ⌋ ∙)} {Es : Cons ⌊ Γ ⌋ n} →
        (Γ ▹ Fin n) ⊢ty Q → PerS Γ Q zero Es → Γ ⊢ selM Es ∷ Π (El (⌜Fin⌝ n)) Q
⊢selQ {Q = Q} dQ ps =
  ⊢lam (ty-El ⊢⌜Fin⌝)
       (⊢-cast (wk-app-vz Q)
               (⊢selG (ren-ty dQ (Ren⊢-ext there))
                      (castQ (fsucsS-zero (renTy (extR vs) Q)) (mkAllQS ps))
                      (⊢conv (⊢var here) (credᵀ El-⌜Fin⌝))))

-- ★★ THE ONE METHOD of a sorted family: split the index, select the sort
⊢methₛ : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {D : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {Es : Cons ⌊ Γ ⌋ n} →
         (Γ ▹ El (⌜Fin⌝ n)) ⊢ J ∷ U → Γ ⊢ D ∷ DescF (SortI J n) → motCtx Γ (SortI J n) D ⊢ty M →
         PerS Γ (SortT (SortI J n) D M J) zero Es →
         Γ ⊢ methAt Es ∷ MethTy (SortI J n) D M
⊢methₛ {n = n} {Γ = Γ} {J = J} {D} {M} {Es} dJ dD dM ps =
  subst (λ X → Γ ⊢ methAt Es ∷ X) (sym (MethTy-At I D M))
    (⊢lam (ty-El dI) (⊢-cast eqP (⊢psplit dA dB dP dq db)))
  where
    I = SortI J n
    dI = ⊢SortI dJ
    T = T₀ I D M
    Γ₁ = Γ ▹ El I
    dT : Γ₁ ⊢ty T
    dT = ⊢T₀ dI dD dM
    A = El (⌜Fin⌝ {⌊ Γ₁ ⌋} n)
    B = El (renTm (extR vs) J)
    cvq : renTy vs (El I) ≅ᵀ Σ' A B
    cvq = credᵀ (El-⌜Σ⌝ _ _)
    dq = ⊢conv (⊢var here) cvq
    dA = ty-El (⊢⌜Fin⌝ {n = n})
    dB : (Γ₁ ▹ A) ⊢ty B
    dB = ty-El (ren-lemma dJ (Ren⊢-ext there))
    ρP : Ren ⌊ Γ₁ ⌋ (⌊ Γ₁ ⌋ ∙)
    ρP vz     = vz
    ρP (vs y) = vs (vs y)
    hρP : Ren⊢ Γ₁ (Γ₁ ▹ renTy vs (El I)) ρP
    hρP here = ∋-cast (trans (renTy-renTy (El I)) (sym (renTy-renTy (El I)))) here
    hρP (there {A = A₀} v) = ∋-cast (trans (renTy-renTy A₀) (sym (renTy-renTy A₀))) (there (there v))
    dP : (Γ₁ ▹ Σ' A B) ⊢ty renTy ρP T
    dP = conv-ctxᵀ cvq (ren-ty dT hρP)
    eqP : subTy (single (var vz)) (renTy ρP T) ≡ T
    eqP = trans (subTy-renTy T) (trans (subTy-cong pt T) (subTy-id T))
      where
        pt : ∀ x → (single (var vz) ₛ∘ᵣ ρP) x ≡ idₛ x
        pt vz     = refl
        pt (vs y) = refl
    -- ── the branch: the sort's method at `j` ──
    Γ₃ = (Γ₁ ▹ A) ▹ B
    x j : RTm ⌊ Γ₃ ⌋
    x = var (vs vz)
    j = var vz
    Q = SortT I D M J
    h3 : Ren⊢ Γ Γ₃ w3
    h3 {A = A₀} v = ∋-cast (ren3ᵀ A₀) (there (there (there v)))
    dSel : Γ₃ ⊢ renTm w3 (selM Es) ∷ Π (El (⌜Fin⌝ n)) (renTy (extR w3) Q)
    dSel = ren-lemma (⊢selQ (⊢SortT dJ dD dM) ps) h3
    d1 = ⊢app dSel (⊢var (there here))
    eJ : renTm vs (renTm (extR vs) J) ≡ subTm (single x) (renTm (extR w3) J)
    ρx : Ren (⌊ Γ ⌋ ∙) ⌊ Γ₃ ⌋
    ρx vz     = vs vz
    ρx (vs y) = vs (vs (vs y))
    eJ = trans (renTm-renTm J)
           (trans (renTm-cong (λ { vz → refl ; (vs y) → refl }) J)
                  (sym (sr-flat (single x) (extR w3) ρx (λ { vz → refl ; (vs y) → refl }) J)))
    dj : Γ₃ ⊢ j ∷ El (subTm (single x) (renTm (extR w3) J))
    dj = ⊢-cast (cong El eJ) (⊢var here)
    d2 = ⊢app d1 dj
    eB : subTy (single j) (subTy (extS (single x)) (renTy (extR (extR w3)) (subTy pairS T)))
         ≡ subTy pairS (renTy ρP T)
    eB = trans (cong (λ z → subTy (single j) (subTy (extS (single x)) z)) (renTy-subTy T))
           (trans (cong (subTy (single j)) (subTy-subTy T))
             (trans (subTy-subTy T) (trans (subTy-cong pt T) (sym (subTy-renTy T)))))
      where
        pt : ∀ y → (single j ∘ₛ (extS (single x) ∘ₛ (extR (extR w3) ᵣ∘ₛ pairS))) y ≡ (pairS ₛ∘ᵣ ρP) y
        pt vz     = refl
        pt (vs y) = refl
    db = ⊢-cast eB d2

------------------------------------------------------------------------
-- 5. ★ SORT `s`'s METHOD, from one method per constructor at the index
--    `pair (tag s) j` (`Lib/MethAt`) — where the fibre computes.
------------------------------------------------------------------------

-- the index of sort `s`, over `j`
ιₛ : ℕ → RTm (Δ ∙)
ιₛ s = pair (tag s) (var vz)

-- the family's index variable instantiated at it
σₛ : ℕ → Sub (Δ ∙) (Δ ∙)
σₛ s = single (ιₛ s) ₛ∘ᵣ extR vs

private
  fl-σₛ : (s : ℕ) (t : RTm Δ) → subTm (σₛ s) (renTm vs t) ≡ renTm vs t
  fl-σₛ s t = sr-flat (σₛ s) vs vs (λ y → refl) t

  M-σₛ : (s : ℕ) (M : RTy ((Δ ∙) ∙)) → subTy (extS (extS (σₛ s))) (wk1M M) ≡ wk1M M
  M-σₛ s M = trans (subTy-renTy M) (trans (subTy-cong pt M) (subTy-var (extR (extR vs)) M))
    where
      pt : ∀ x → (extS (extS (σₛ s)) ₛ∘ᵣ extR (extR vs)) x ≡ ⟨ extR (extR vs) ⟩ᵣ x
      pt vz          = refl
      pt (vs vz)     = refl
      pt (vs (vs x)) = refl

  cong₆ : {A B C D E F G : Set} (g : A → B → C → D → E → F → G)
          {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} {f f' : F} →
          a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f ≡ f' → g a b c d e f ≡ g a' b' c' d' e' f'
  cong₆ g refl refl refl refl refl refl = refl

-- ★ the sort-generic type at `tag s` IS the method at `ιₛ s`
SortT-inst : (I D : RTm Δ) (M : RTy ((Δ ∙) ∙)) (J : RTm (Δ ∙)) (s : ℕ) →
             subTy (single (tag s)) (SortT I D M J)
             ≡ Π (El (subTm (single (tag s)) J))
                 (MethAt (renTm vs I) (renTm vs D) (wk1M M) (ιₛ s) (app (renTm vs D) (ιₛ s)) (con (var (vs vz))))
SortT-inst I D M J s =
  cong (Π (El (subTm (single (tag s)) J)))
    (trans (subTy-subTy (T₀ I D M))
      (trans (subTy-cong pt (T₀ I D M))
        (trans (MethAt-sub (σₛ s) (renTm vs I) (renTm vs D) (wk1M M) (var vz)
                           (app (renTm vs D) (var vz)) (con (var (vs vz))))
               (cong₆ MethAt (fl-σₛ s I) (fl-σₛ s D) (M-σₛ s M) refl
                             (cong₂ app (fl-σₛ s D) refl) refl))))
  where
    pt : ∀ x → (extS (single (tag s)) ∘ₛ pairS) x ≡ σₛ s x
    pt vz     = cong (λ z → pair z (var vz)) (tag-ren vs s)
    pt (vs x) = refl

-- the constructor lists at the index, typed
hσₛ : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {B : RTy ⌊ Γ ⌋} (s : ℕ) →
      (Γ ▹ B) ⊢ ιₛ s ∷ El (renTm vs I) → Sub⊢ (Γ ▹ El I) (Γ ▹ B) (σₛ s)
hσₛ {I = I} s dx here = ⊢-cast (cong El (sym (fl-σₛ s I))) dx
hσₛ s dx (there {A = A₀} v) =
  ⊢-cast (sym (trans (subTy-renTy A₀) (subTy-var vs A₀))) (⊢var (there v))

subAllDₛ : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {B : RTy ⌊ Γ ⌋} {Cs : Cons (⌊ Γ ⌋ ∙) c} (s : ℕ) →
           (Γ ▹ B) ⊢ ιₛ s ∷ El (renTm vs I) → AllD (Γ ▹ El I) (renTm vs I) Cs →
           AllD (Γ ▹ B) (renTm vs I) (subC (σₛ s) Cs)
subAllDₛ s dx []ᵈ = []ᵈ
subAllDₛ {I = I} s dx (d ∷ᵈ ds) =
  ⊢-cast (cong Desc (fl-σₛ s I)) (sub-lemma d (hσₛ s dx)) ∷ᵈ subAllDₛ s dx ds

-- sort `s`'s index is well-typed over its `j`
⊢ιₛ : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} → (Γ ▹ El (⌜Fin⌝ n)) ⊢ J ∷ U → Lt s n →
      (Γ ▹ El (subTm (single (tag s)) J)) ⊢ ιₛ s ∷ El (renTm vs (SortI J n))
⊢ιₛ {s = s} {J = J} dJ lt =
  ⊢ixₛ (ren-lemma dJ (Ren⊢-ext there)) lt (⊢-cast (cong El eq) (⊢var here))
  where
    eq : renTm vs (subTm (single (tag s)) J) ≡ subTm (single (tag s)) (renTm (extR vs) J)
    eq = trans (renTm-subTm J)
           (trans (subTm-cong (λ { vz → tag-ren vs s ; (vs y) → refl }) J)
                  (sym (subTm-renTm J)))

-- ★ sort `s`'s method, from its constructors' methods at `ιₛ s`
⊢sortMeth : {Γ : Ctx} {J : RTm (⌊ Γ ⌋ ∙)} {Css : SCons (⌊ Γ ⌋ ∙) n} {Cs : Cons (⌊ Γ ⌋ ∙) c}
            {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {ms : Cons (⌊ Γ ⌋ ∙) c} →
            (Γ ▹ El (⌜Fin⌝ n)) ⊢ J ∷ U → AllSD Γ (SortI J n) Css → motCtx Γ (SortI J n) (Dₛ Css) ⊢ty M →
            NthS Css s Cs →
            PerKAt (Γ ▹ El (subTm (single (tag s)) J)) (renTm vs (SortI J n)) (renTm vs (Dₛ Css)) (wk1M M)
                   (ιₛ s) (selF (subC (σₛ s) Cs)) zero ms →
            Γ ⊢ lam (methAt ms) ∷ subTy (single (tag s)) (SortT (SortI J n) (Dₛ Css) M J)
⊢sortMeth {n = n} {s = s} {Γ = Γ} {J = J} {Css} {Cs} {M} {ms} dJ dss dM nts ps =
  ⊢-cast (sym (SortT-inst I D M J s))
    (⊢lam (ty-El dJs)
      (⊢conv (⊢methAt (⊢wk dI) (⊢wkD dD) (mot-ren there dM) dix df fib ps)
             (csymᵀ (red→≅ᵀ (MethAt-monoᶜ fib)))))
  where
    I = SortI J n
    D = Dₛ Css
    dI = ⊢SortI dJ
    dD = ⊢Dₛ dI dss
    dJs : Γ ⊢ subTm (single (tag s)) J ∷ U
    dJs = sub-lemma dJ hs
      where
        hs : Sub⊢ (Γ ▹ El (⌜Fin⌝ n)) Γ (single (tag s))
        hs here = ⊢conv (⊢tag (nthS-lt nts)) (csymᵀ (credᵀ El-⌜Fin⌝))
        hs (there {A = A₀} v) = ⊢-cast (sym (wk-cancelᵀ A₀)) (⊢var v)
          where
            wk-cancelᵀ : (A : RTy ⌊ Γ ⌋) → subTy (single (tag s)) (renTy vs A) ≡ A
            wk-cancelᵀ A = trans (subTy-renTy A) (trans (subTy-cong (λ _ → refl) A) (subTy-id A))
    dix = ⊢ιₛ dJ (nthS-lt nts)
    df = ⊢selF (⊢wk dI) (subAllDₛ s dix (nth-AllSD dss nts))
    fib = fibₛ-wk (var vz) nts

------------------------------------------------------------------------
-- 6. ★ …AND IT COMPUTES: at constructor `k` of sort `s`, the one method
--    is that constructor's method at `j` — ι, the index split and sort
--    selection (`methAt-β`), one β, the payload split and tag selection.
------------------------------------------------------------------------

ιₛ-red : {D j p : RTm Δ} {m : RTm (Δ ∙)} {Es : Cons Δ n} {ms : Cons (Δ ∙) c} →
         Nth Es s (lam (methAt ms)) → Nth ms k m →
         ielim D (pair (tag s) j) (methAt Es) (conₗ k p)
           ⟶* app (app (subTm (single j) m) p)
                  (dih D (methAt Es) (app D (pair (tag s) j)) (pair (tag k) p))
ιₛ-red {s = s} {k = k} {D = D} {j} {p} {m} {Es = Es} {ms} nE nm =
  step (ι D ix e q)
   (⟶*-trans (⟶*-appˡ (methAt-β {m = lam (methAt ms)} {p = j} {h = q} nE))
    (step (ξ-appˡ (ξ-appˡ (β (methAt ms) j)))
     (subst (λ X → app (app X q) h ⟶* app (app (subTm (single j) m) p) h) (sym (methAt-sub (single j) ms))
            (methAt-β (nth-sub (single j) nm)))))
  where
    ix = pair (tag s) j
    e = methAt Es
    q = pair (tag k) p
    h = dih D e (app D ix) q
