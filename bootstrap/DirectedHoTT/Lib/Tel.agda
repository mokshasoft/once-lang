------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ THE TELESCOPE VIEW: a description term READ as
-- the constructor telescope it is, so that everything an eliminator's
-- method sees — the hypotheses' TYPE and the hypotheses THEMSELVES — is
-- computed by ONE structural induction, with the telescope a VARIABLE.
--
--     Tel Δ            tι j | tσ S T | tρ j T          (meta level)
--     ⌜ T ⌝ᵗ           dι j | dσ S (lam ⌜T⌝) | dρ j ⌜T⌝  (the term)
--
-- ★ WHY A VIEW, AND WHY IT IS NOT THE OLD `ICon` COMING BACK.  The kernel
--   has ONE datatype former; descriptions are ordinary terms (D072).  A
--   `Tel` is not a second kind of description: it is a way of WRITING a
--   description term, and `⌜_⌝ᵗ` says which.  Nothing here is trusted —
--   `TelOK` is typing of the term by the ordinary rules (`⊢tel`), and
--   every reduction lemma is a chain of kernel steps.
--   What the view buys is the thing a raw term cannot give a generic
--   lemma: a STRUCTURAL recursion.  `DIh`'s σ-step reduces through
--   `app f (fst p)`, so on terms the tail is a β-REDUCT, not a subterm.
--   On a `Tel` it is the subterm `T`, carried under a PENDING
--   SUBSTITUTION `σ` (the pointwise-motive lesson: index by the ambient
--   substitution, peel once).
--
-- ★ THE TWO NORMAL FORMS.
--     IhN σ T D M p    the hypotheses' type: `Unit` / a `Σ'` per `dρ`
--     dihN σ T D e p   the hypotheses: `unit` / a `pair` of `ielim`s
--   and `ihN-red`/`dihN-red` reduce `DIh`/`dih` at `subTm σ ⌜T⌝` to them.
--   At a concrete `T` and `σ = var` both are what the old per-example
--   step chains wrote out by hand (`Examples/Vec`'s `hyps`/`walk`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Tel where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-pairʳ; ⟶*-appʳ; ⟶*-dihᶜ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-Σʳ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-trans
        ; red→≅ᵀ )
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢wk; Ren⊢; ∋-cast; conv-ctx )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic
  using ( _,ₛ_; subTm-var; ⟨_⟩ᵣ )
open import DirectedHoTT.Metatheory.Premises
  using ( MethG; methSg; mot-ren; ⊢wkD )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; Nth; nth-z; nth-s; tag; Dₗ; conₗ; selF-β; methₗ; ιₗ
        ; MethK; AllD; []ᵈ; _∷ᵈ_; ⊢Dₗ; ⊢conₗ; ⊢pay-ι; ⊢pay-σλ; ⊢pay-ρ; Dσ
        ; selF-sub; nth-sub; vz-cancel )

private
  variable
    Γ Δ : Cx
    c k : ℕ

------------------------------------------------------------------------
-- 1. THE VIEW.
------------------------------------------------------------------------

data Tel (Δ : Cx) : Set where
  tι : Tel Δ                         -- the end (D074: the index is the fibre's)
  tσ : RTm Δ → Tel (Δ ∙) → Tel Δ     -- a non-recursive field (a code), BOUND
  tρ : RTm Δ → Tel Δ → Tel Δ         -- a recursive field at an index, NOT bound

⌜_⌝ᵗ : Tel Δ → RTm Δ
⌜ tι ⌝ᵗ     = dι
⌜ tσ S T ⌝ᵗ = dσ S (lam ⌜ T ⌝ᵗ)
⌜ tρ j T ⌝ᵗ = dρ j ⌜ T ⌝ᵗ

------------------------------------------------------------------------
-- 2. TYPING — the ordinary rules, read along the view.
------------------------------------------------------------------------

data TelOK (Γ : Ctx) (I : RTm ⌊ Γ ⌋) : Tel ⌊ Γ ⌋ → Set where
  ok-ι : TelOK Γ I tι
  ok-σ : {S : RTm ⌊ Γ ⌋} {T : Tel (⌊ Γ ⌋ ∙)} →
         Γ ⊢ S ∷ U → TelOK (Γ ▹ El S) (renTm vs I) T → TelOK Γ I (tσ S T)
  ok-ρ : {j : RTm ⌊ Γ ⌋} {T : Tel ⌊ Γ ⌋} →
         Γ ⊢ j ∷ El I → TelOK Γ I T → TelOK Γ I (tρ j T)

⊢tel : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {T : Tel ⌊ Γ ⌋} →
       Γ ⊢ I ∷ U → TelOK Γ I T → Γ ⊢ ⌜ T ⌝ᵗ ∷ Desc I
⊢tel dI ok-ι         = ⊢dι dI
⊢tel dI (ok-σ dS ok) = ⊢dσ dI dS (⊢lam (ty-El dS) (⊢tel (⊢wk dI) ok))
⊢tel dI (ok-ρ dj ok) = ⊢dρ dI dj (⊢tel dI ok)

------------------------------------------------------------------------
-- 3. THE PENDING SUBSTITUTION.  The σ-step's β lands on
--    `subTm (single a) (subTm (extS σ) ⌜T⌝)`, which is `⌜T⌝` under
--    `σ ,ₛ a` — one σ-calculus fact, used by both normal forms.
------------------------------------------------------------------------

sub-snoc : (σ : Sub Δ Γ) (a : RTm Γ) (t : RTm (Δ ∙)) →
           subTm (single a) (subTm (extS σ) t) ≡ subTm (σ ,ₛ a) t
sub-snoc σ a t = trans (subTm-subTm t) (subTm-cong pw t)
  where
    pw : (x : Var (_ ∙)) → (single a ∘ₛ extS σ) x ≡ (σ ,ₛ a) x
    pw vz     = refl
    pw (vs x) = wk-single (σ x)

------------------------------------------------------------------------
-- 4. ★ THE HYPOTHESES' TYPE.
------------------------------------------------------------------------

IhN : Sub Δ Γ → Tel Δ → RTm Γ → RTy ((Γ ∙) ∙) → RTm Γ → RTy Γ
IhN σ tι       D M p = Unit
IhN σ (tσ S T) D M p = IhN (σ ,ₛ fst p) T D M (snd p)
IhN σ (tρ j T) D M p =
  Σ' (iinst (subTm σ j) (fst p) M)
     (IhN (vs ᵣ∘ₛ σ) T (renTm vs D) (renTy (extR (extR vs)) M) (snd (renTm vs p)))

ihN-red : (σ : Sub Δ Γ) (T : Tel Δ) (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) (p : RTm Γ) →
          DIh D M (subTm σ ⌜ T ⌝ᵗ) p ⟶ᵀ* IhN σ T D M p
ihN-red σ tι D M p = stepᵀ (DIh-ι D M p) doneᵀ
ihN-red σ (tσ S T) D M p =
  stepᵀ (DIh-σ D M (subTm σ S) (lam (subTm (extS σ) ⌜ T ⌝ᵗ)) p)
  (stepᵀ (ξ-DIhᶜ (β (subTm (extS σ) ⌜ T ⌝ᵗ) (fst p)))
    (subst (λ C → DIh D M C (snd p) ⟶ᵀ* IhN (σ ,ₛ fst p) T D M (snd p))
           (sym (sub-snoc σ (fst p) ⌜ T ⌝ᵗ))
           (ihN-red (σ ,ₛ fst p) T D M (snd p))))
ihN-red σ (tρ j T) D M p =
  stepᵀ (DIh-ρ D M (subTm σ j) (subTm σ ⌜ T ⌝ᵗ) p)
  (⟶ᵀ*-Σʳ
    (subst (λ C → DIh (renTm vs D) M' C p' ⟶ᵀ* IhN (vs ᵣ∘ₛ σ) T (renTm vs D) M' p')
           (sym (renTm-subTm ⌜ T ⌝ᵗ))
           (ihN-red (vs ᵣ∘ₛ σ) T (renTm vs D) M' p')))
  where
    M' = renTy (extR (extR vs)) M
    p' = snd (renTm vs p)

------------------------------------------------------------------------
-- 5. ★ THE HYPOTHESES.  ⚠ `dih`'s ρ-step does NOT go under a binder (a
--    `pair`, not a `Σ'`), so unlike `IhN` nothing is renamed.
------------------------------------------------------------------------

dihN : Sub Δ Γ → Tel Δ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
dihN σ tι       D e p = unit
dihN σ (tσ S T) D e p = dihN (σ ,ₛ fst p) T D e (snd p)
dihN σ (tρ j T) D e p = pair (ielim D (subTm σ j) e (fst p)) (dihN σ T D e (snd p))

dihN-red : (σ : Sub Δ Γ) (T : Tel Δ) (D e p : RTm Γ) →
           dih D e (subTm σ ⌜ T ⌝ᵗ) p ⟶* dihN σ T D e p
dihN-red σ tι D e p = step (dih-ι D e p) done
dihN-red σ (tσ S T) D e p =
  step (dih-σ D e (subTm σ S) (lam (subTm (extS σ) ⌜ T ⌝ᵗ)) p)
  (step (ξ-dihᶜ (β (subTm (extS σ) ⌜ T ⌝ᵗ) (fst p)))
    (subst (λ C → dih D e C (snd p) ⟶* dihN (σ ,ₛ fst p) T D e (snd p))
           (sym (sub-snoc σ (fst p) ⌜ T ⌝ᵗ))
           (dihN-red (σ ,ₛ fst p) T D e (snd p))))
dihN-red σ (tρ j T) D e p =
  step (dih-ρ D e (subTm σ j) (subTm σ ⌜ T ⌝ᵗ) p) (⟶*-pairʳ (dihN-red σ T D e (snd p)))

-- …at the identity, which is where a method meets them
ihN-red₀ : (T : Tel Γ) (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) (p : RTm Γ) →
           DIh D M ⌜ T ⌝ᵗ p ⟶ᵀ* IhN idₛ T D M p
ihN-red₀ T D M p =
  subst (λ C → DIh D M C p ⟶ᵀ* IhN idₛ T D M p) (subTm-id ⌜ T ⌝ᵗ) (ihN-red idₛ T D M p)

dihN-red₀ : (T : Tel Γ) (D e p : RTm Γ) → dih D e ⌜ T ⌝ᵗ p ⟶* dihN idₛ T D e p
dihN-red₀ T D e p =
  subst (λ C → dih D e C p ⟶* dihN idₛ T D e p) (subTm-id ⌜ T ⌝ᵗ) (dihN-red idₛ T D e p)

------------------------------------------------------------------------
-- 5b. ★ THE PAYLOAD'S TYPE, in normal form: a `Σ'` per field — the
--     field's decoded code at `tσ`, the family at `tρ` — ending in
--     `Unit`.  What a method body needs to READ its payload (`fst`/`snd`
--     of the payload variable) without a per-example conversion chain.
------------------------------------------------------------------------

PayN : Sub Δ Γ → Tel Δ → RTm Γ → RTm Γ → RTy Γ
PayN σ tι       I D = Unit
PayN σ (tσ S T) I D = Σ' (El (subTm σ S)) (PayN (extS σ) T (renTm vs I) (renTm vs D))
PayN σ (tρ j T) I D = Σ' (IMu I D (subTm σ j)) (PayN (vs ᵣ∘ₛ σ) T (renTm vs I) (renTm vs D))

payN-red : (σ : Sub Δ Γ) (T : Tel Δ) (I D : RTm Γ) →
           El (dpay I D (subTm σ ⌜ T ⌝ᵗ)) ⟶ᵀ* PayN σ T I D
payN-red σ tι I D = stepᵀ (ξ-El (dpay-ι I D)) (stepᵀ El-⌜Unit⌝ doneᵀ)
payN-red σ (tσ S T) I D =
  stepᵀ (ξ-El (dpay-σ I D (subTm σ S) (lam X)))
  (stepᵀ (ξ-El (ξ-⌜Σ⌝ʳ (ξ-dpayᶜ (β (renTm (extR vs) X) (var vz)))))
  (stepᵀ (El-⌜Σ⌝ _ _)
    (⟶ᵀ*-Σʳ (subst (λ C → El (dpay (renTm vs I) (renTm vs D) C) ⟶ᵀ* PayN (extS σ) T (renTm vs I) (renTm vs D))
                   (sym (vz-cancel X))
                   (payN-red (extS σ) T (renTm vs I) (renTm vs D))))))
  where X = subTm (extS σ) ⌜ T ⌝ᵗ
payN-red σ (tρ j T) I D =
  stepᵀ (ξ-El (dpay-ρ I D (subTm σ j) (subTm σ ⌜ T ⌝ᵗ)))
  (stepᵀ (El-⌜Σ⌝ _ _)
  (⟶ᵀ*-trans (⟶ᵀ*-Σˡ (stepᵀ El-⌜IMu⌝ doneᵀ))
    (⟶ᵀ*-Σʳ (subst (λ C → El (dpay (renTm vs I) (renTm vs D) C) ⟶ᵀ* PayN (vs ᵣ∘ₛ σ) T (renTm vs I) (renTm vs D))
                   (sym (renTm-subTm ⌜ T ⌝ᵗ))
                   (payN-red (vs ᵣ∘ₛ σ) T (renTm vs I) (renTm vs D))))))

------------------------------------------------------------------------
-- 6. ★ A METHOD, read along the view.  The method's third binder is the
--    hypotheses at `DIh`; the body is written against their NORMAL FORM
--    (`HypCtx`), and `⊢methT` converts the context once.
------------------------------------------------------------------------

-- the method's context: index, payload of the telescope (OVER the index
--   binder — D074), hypotheses in normal form (the telescope's pending
--   substitution is the weakening past the payload)
HypCtx : (Γ : Ctx) → RTm ⌊ Γ ⌋ → RTm ⌊ Γ ⌋ → RTy ((⌊ Γ ⌋ ∙) ∙) → Tel (⌊ Γ ⌋ ∙) → Ctx
HypCtx Γ I D M T =
  ((Γ ▹ El I) ▹ El (dpay (renTm vs I) (renTm vs D) ⌜ T ⌝ᵗ))
    ▹ IhN ⟨ vs ⟩ᵣ T (renTm vs (renTm vs D)) (wk2M M) (var vz)

hyps≅ : (T : Tel (Γ ∙)) (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
        DIh (renTm vs (renTm vs D)) (wk2M M) (renTm vs ⌜ T ⌝ᵗ) (var vz)
          ≅ᵀ IhN ⟨ vs ⟩ᵣ T (renTm vs (renTm vs D)) (wk2M M) (var vz)
hyps≅ T D M =
  red→≅ᵀ (subst (λ C → DIh D₂ (wk2M M) C (var vz) ⟶ᵀ* IhN ⟨ vs ⟩ᵣ T D₂ (wk2M M) (var vz))
                (subTm-var vs ⌜ T ⌝ᵗ) (ihN-red ⟨ vs ⟩ᵣ T D₂ (wk2M M) (var vz)))
  where D₂ = renTm vs (renTm vs D)

private
  w2⊢ : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {B' : RTy (⌊ Γ ⌋ ∙)} → Ren⊢ Γ ((Γ ▹ B) ▹ B') (λ x → vs (vs x))
  w2⊢ {A = A} v = ∋-cast (renTy-renTy A) (there (there v))

⊢methT : {Γ : Ctx} {I D : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {T : Tel (⌊ Γ ⌋ ∙)}
         {s b : RTm (((⌊ Γ ⌋ ∙) ∙) ∙)} →
         Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → motCtx Γ I D ⊢ty M → TelOK (Γ ▹ El I) (renTm vs I) T →
         HypCtx Γ I D M T ⊢ b ∷ subTy (methSg s) M →
         Γ ⊢ lam (lam (lam b)) ∷ MethG I D M ⌜ T ⌝ᵗ s
⊢methT {Γ} {I} {D} {M} {T} dI dD dM ok db =
  ⊢lam (ty-El dI) (⊢lam dP₁ (⊢lam dH (conv-ctx (csymᵀ (hyps≅ T D M)) db)))
  where
    dC = ⊢tel (⊢wk dI) ok
    P₁ = El (dpay (renTm vs I) (renTm vs D) ⌜ T ⌝ᵗ)
    dP₁ = ty-El (⊢dpay (⊢wk dI) (⊢wkD dD) dC)
    Γ₂ = (Γ ▹ El I) ▹ P₁
    dM₂ : motCtx Γ₂ (renTm vs (renTm vs I)) (renTm vs (renTm vs D)) ⊢ty wk2M M
    dM₂ = subst (λ a → motCtx Γ₂ a (renTm vs (renTm vs D)) ⊢ty wk2M M) (sym (renTm-renTm I))
            (subst (λ b → motCtx Γ₂ (renTm (λ x → vs (vs x)) I) b ⊢ty wk2M M) (sym (renTm-renTm D))
              (mot-ren (w2⊢ {B = El I} {B' = P₁}) dM))
    dH = ty-DIh (⊢wk (⊢wk dI)) (⊢wkD (⊢wkD dD)) dM₂ (⊢wk dC) (⊢var here)

-- ★ the method's PAYLOAD variable, at its normal form (it sits two
--   binders out, under the pending weakening `w2`)
⊢payHyp : {Γ : Ctx} {I D : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {T : Tel (⌊ Γ ⌋ ∙)} →
          HypCtx Γ I D M T ⊢ var (vs vz) ∷
            PayN ⟨ (λ x → vs (vs x)) ⟩ᵣ T (renTm vs (renTm vs (renTm vs I))) (renTm vs (renTm vs (renTm vs D)))
⊢payHyp {Γ} {I} {D} {M} {T} =
  ⊢conv (subst (λ C → HypCtx Γ I D M T ⊢ var (vs vz) ∷ El (dpay I₃ D₃ C))
               (trans (renTm-renTm ⌜ T ⌝ᵗ) (sym (subTm-var (λ x → vs (vs x)) ⌜ T ⌝ᵗ)))
               (⊢var (there here)))
        (red→≅ᵀ (payN-red ⟨ (λ x → vs (vs x)) ⟩ᵣ T I₃ D₃))
  where I₃ = renTm vs (renTm vs (renTm vs I))
        D₃ = renTm vs (renTm vs (renTm vs D))

------------------------------------------------------------------------
-- 7. ★ …AND IT COMPUTES: the ι-step of the constructor-list form, with
--    the hypotheses already in normal form.
------------------------------------------------------------------------

-- the fibre and the outer TAG layer of `Dₗ`, peeled: the hypotheses at
--   constructor `k`'s telescope, instantiated at the index
dihₗ : {Cs : Cons (Δ ∙) c} {C : RTm (Δ ∙)} {e i p : RTm Δ} → Nth Cs k C →
       dih (Dₗ Cs) e (app (Dₗ Cs) i) (pair (tag k) p) ⟶* dih (Dₗ Cs) e (subTm (single i) C) p
dihₗ {k = k} {Cs = Cs} {C = C} {i = i} nt =
  step (ξ-dihᶜ (β (Dσ Cs) i))
  (step (dih-σ _ _ _ _ _)
  (step (ξ-dihᶜ (ξ-appʳ (βfst _ _)))
  (step (ξ-dihᵖ (βsnd _ _))
    (⟶*-dihᶜ (subst (λ X → app X (tag k) ⟶* subTm (single i) C) (sym (selF-sub (single i) Cs))
                    (selF-β (nth-sub (single i) nt)))))))

ιT : {Cs : Cons (Δ ∙) c} {ms : Cons Δ c} {T : Tel (Δ ∙)} {m i p : RTm Δ} →
     Nth Cs k ⌜ T ⌝ᵗ → Nth ms k m →
     ielim (Dₗ Cs) i (methₗ ms) (conₗ k p)
       ⟶* app (app (app m i) p) (dihN (single i) T (Dₗ Cs) (methₗ ms) p)
ιT {Cs = Cs} {ms} {T} {i = i} {p = p} nC nm =
  ⟶*-trans (ιₗ nm) (⟶*-appʳ (⟶*-trans (dihₗ nC) (dihN-red (single i) T (Dₗ Cs) (methₗ ms) p)))

------------------------------------------------------------------------
-- 8. ★ THE CONSTRUCTOR LIST, as telescopes.
------------------------------------------------------------------------

infixr 5 _∷ᵗ_ _∷ᵒ_
data Tels (Δ : Cx) : ℕ → Set where
  []ᵗ  : Tels Δ zero
  _∷ᵗ_ : Tel Δ → Tels Δ c → Tels Δ (suc c)

⌜_⌝ₛ : Tels Δ c → Cons Δ c
⌜ []ᵗ ⌝ₛ     = []
⌜ T ∷ᵗ Ts ⌝ₛ = ⌜ T ⌝ᵗ ∷ ⌜ Ts ⌝ₛ

data NthT : Tels Δ c → ℕ → Tel Δ → Set where
  nthᵗ-z : {T : Tel Δ} {Ts : Tels Δ c} → NthT (T ∷ᵗ Ts) zero T
  nthᵗ-s : {T T' : Tel Δ} {Ts : Tels Δ c} → NthT Ts k T → NthT (T' ∷ᵗ Ts) (suc k) T

nth-⌜⌝ : {Ts : Tels Δ c} {T : Tel Δ} → NthT Ts k T → Nth ⌜ Ts ⌝ₛ k ⌜ T ⌝ᵗ
nth-⌜⌝ nthᵗ-z     = nth-z
nth-⌜⌝ (nthᵗ-s n) = nth-s (nth-⌜⌝ n)

data AllOK (Γ : Ctx) (I : RTm ⌊ Γ ⌋) : Tels ⌊ Γ ⌋ c → Set where
  []ᵒ  : AllOK Γ I []ᵗ
  _∷ᵒ_ : {T : Tel ⌊ Γ ⌋} {Ts : Tels ⌊ Γ ⌋ c} → TelOK Γ I T → AllOK Γ I Ts → AllOK Γ I (T ∷ᵗ Ts)

allD : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Ts : Tels ⌊ Γ ⌋ c} → Γ ⊢ I ∷ U → AllOK Γ I Ts → AllD Γ I ⌜ Ts ⌝ₛ
allD dI []ᵒ          = []ᵈ
allD dI (ok ∷ᵒ oks) = ⊢tel dI ok ∷ᵈ allD dI oks

⊢Dₜ : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Ts : Tels (⌊ Γ ⌋ ∙) c} → Γ ⊢ I ∷ U →
      AllOK (Γ ▹ El I) (renTm vs I) Ts → Γ ⊢ Dₗ ⌜ Ts ⌝ₛ ∷ DescF I
⊢Dₜ dI oks = ⊢Dₗ dI (allD (⊢wk dI) oks)

------------------------------------------------------------------------
-- 9. ★ CONSTRUCTORS: the payload built field by field along the view.
--    At a concrete telescope `subTm (single a) ⌜T⌝` COMPUTES to the next
--    field's `⌜_⌝ᵗ`, so a use site chains these with no casts.
------------------------------------------------------------------------

module _ {Γ : Ctx} {I D : RTm ⌊ Γ ⌋} (dI : Γ ⊢ I ∷ U) (dD : Γ ⊢ D ∷ DescF I) where

  ⊢payι : {e : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ Unit → Γ ⊢ e ∷ El (dpay I D ⌜ tι ⌝ᵗ)
  ⊢payι = ⊢pay-ι

  ⊢payσ : {S a p : RTm ⌊ Γ ⌋} {T : Tel (⌊ Γ ⌋ ∙)} → TelOK Γ I (tσ S T) →
          Γ ⊢ a ∷ El S → Γ ⊢ p ∷ El (dpay I D (subTm (single a) ⌜ T ⌝ᵗ)) →
          Γ ⊢ pair a p ∷ El (dpay I D ⌜ tσ S T ⌝ᵗ)
  ⊢payσ (ok-σ dS ok) = ⊢pay-σλ dI dD (⊢lam (ty-El dS) (⊢tel (⊢wk dI) ok))

  ⊢payρ : {j r p : RTm ⌊ Γ ⌋} {T : Tel ⌊ Γ ⌋} → TelOK Γ I (tρ j T) →
          Γ ⊢ r ∷ IMu I D j → Γ ⊢ p ∷ El (dpay I D ⌜ T ⌝ᵗ) →
          Γ ⊢ pair r p ∷ El (dpay I D ⌜ tρ j T ⌝ᵗ)
  ⊢payρ (ok-ρ dj ok) = ⊢pay-ρ dI dD (⊢tel dI ok)

-- ★ constructor `k` at index `i`: its payload is the telescope
--   instantiated at the index (at a concrete telescope that COMPUTES to
--   the next `⌜_⌝ᵗ`, so the builders above chain with no casts)
⊢conₜ : {Γ : Ctx} {I i p : RTm ⌊ Γ ⌋} {Ts : Tels (⌊ Γ ⌋ ∙) c} {T : Tel (⌊ Γ ⌋ ∙)} →
        Γ ⊢ I ∷ U → AllOK (Γ ▹ El I) (renTm vs I) Ts → NthT Ts k T → Γ ⊢ i ∷ El I →
        Γ ⊢ p ∷ El (dpay I (Dₗ ⌜ Ts ⌝ₛ) (subTm (single i) ⌜ T ⌝ᵗ)) → Γ ⊢ conₗ k p ∷ IMu I (Dₗ ⌜ Ts ⌝ₛ) i
⊢conₜ dI oks n di dp = ⊢conₗ dI (allD (⊢wk dI) oks) di (nth-⌜⌝ n) dp
