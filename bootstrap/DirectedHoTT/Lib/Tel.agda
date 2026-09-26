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
  using ( ⟶*-trans; ⟶*-pairʳ; ⟶*-appʳ; ⟶*-dihᶜ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-Σʳ; red→≅ᵀ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; Ren⊢; ∋-cast; conv-ctx )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( _,ₛ_; subTm-var )
open import DirectedHoTT.Metatheory.Premises using ( MethG; methSg; mot-ren )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; Nth; nth-z; nth-s; tag; Dₗ; conₗ; selF-β; methₗ; ιₗ; MethK; AllD; []ᵈ; _∷ᵈ_
        ; ⊢Dₗ; ⊢conₗ; ⊢pay-ι; ⊢pay-σλ; ⊢pay-ρ )

private
  variable
    Γ Δ : Cx
    c k : ℕ

------------------------------------------------------------------------
-- 1. THE VIEW.
------------------------------------------------------------------------

data Tel (Δ : Cx) : Set where
  tι : RTm Δ → Tel Δ                 -- the end: the target index
  tσ : RTm Δ → Tel (Δ ∙) → Tel Δ     -- a non-recursive field (a code), BOUND
  tρ : RTm Δ → Tel Δ → Tel Δ         -- a recursive field at an index, NOT bound

⌜_⌝ᵗ : Tel Δ → RTm Δ
⌜ tι j ⌝ᵗ   = dι j
⌜ tσ S T ⌝ᵗ = dσ S (lam ⌜ T ⌝ᵗ)
⌜ tρ j T ⌝ᵗ = dρ j ⌜ T ⌝ᵗ

------------------------------------------------------------------------
-- 2. TYPING — the ordinary rules, read along the view.
------------------------------------------------------------------------

data TelOK (Γ : Ctx) (I : RTm ⌊ Γ ⌋) : Tel ⌊ Γ ⌋ → Set where
  ok-ι : {j : RTm ⌊ Γ ⌋} → Γ ⊢ j ∷ El I → TelOK Γ I (tι j)
  ok-σ : {S : RTm ⌊ Γ ⌋} {T : Tel (⌊ Γ ⌋ ∙)} →
         Γ ⊢ S ∷ U → TelOK (Γ ▹ El S) (renTm vs I) T → TelOK Γ I (tσ S T)
  ok-ρ : {j : RTm ⌊ Γ ⌋} {T : Tel ⌊ Γ ⌋} →
         Γ ⊢ j ∷ El I → TelOK Γ I T → TelOK Γ I (tρ j T)

⊢tel : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {T : Tel ⌊ Γ ⌋} →
       Γ ⊢ I ∷ U → TelOK Γ I T → Γ ⊢ ⌜ T ⌝ᵗ ∷ Desc I
⊢tel dI (ok-ι dj)    = ⊢dι dI dj
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
IhN σ (tι j)   D M p = Unit
IhN σ (tσ S T) D M p = IhN (σ ,ₛ fst p) T D M (snd p)
IhN σ (tρ j T) D M p =
  Σ' (iinst (subTm σ j) (fst p) M)
     (IhN (vs ᵣ∘ₛ σ) T (renTm vs D) (renTy (extR (extR vs)) M) (snd (renTm vs p)))

ihN-red : (σ : Sub Δ Γ) (T : Tel Δ) (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) (p : RTm Γ) →
          DIh D M (subTm σ ⌜ T ⌝ᵗ) p ⟶ᵀ* IhN σ T D M p
ihN-red σ (tι j) D M p = stepᵀ (DIh-ι D M (subTm σ j) p) doneᵀ
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
dihN σ (tι j)   D e p = unit
dihN σ (tσ S T) D e p = dihN (σ ,ₛ fst p) T D e (snd p)
dihN σ (tρ j T) D e p = pair (ielim D (subTm σ j) e (fst p)) (dihN σ T D e (snd p))

dihN-red : (σ : Sub Δ Γ) (T : Tel Δ) (D e p : RTm Γ) →
           dih D e (subTm σ ⌜ T ⌝ᵗ) p ⟶* dihN σ T D e p
dihN-red σ (tι j) D e p = step (dih-ι D e (subTm σ j) p) done
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
-- 6. ★ A METHOD, read along the view.  The method's third binder is the
--    hypotheses at `DIh`; the body is written against their NORMAL FORM
--    (`HypCtx`), and `⊢methT` converts the context once.
------------------------------------------------------------------------

wk2ₛ : Sub Γ ((Γ ∙) ∙)
wk2ₛ x = var (vs (vs x))

HypCtx : (Γ : Ctx) → RTm ⌊ Γ ⌋ → RTm ⌊ Γ ⌋ → RTy ((⌊ Γ ⌋ ∙) ∙) → Tel ⌊ Γ ⌋ → Ctx
HypCtx Γ I D M T =
  ((Γ ▹ El I) ▹ El (dpay (renTm vs I) (renTm vs D) (renTm vs ⌜ T ⌝ᵗ) (var vz)))
    ▹ IhN wk2ₛ T (renTm vs (renTm vs D)) (wk2M M) (var vz)

wk2-⌜⌝ : (T : Tel Γ) → subTm wk2ₛ ⌜ T ⌝ᵗ ≡ renTm vs (renTm vs ⌜ T ⌝ᵗ)
wk2-⌜⌝ T = trans (subTm-var (λ x → vs (vs x)) ⌜ T ⌝ᵗ) (sym (renTm-renTm ⌜ T ⌝ᵗ))

hyps≅ : (T : Tel Γ) (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
        DIh (renTm vs (renTm vs D)) (wk2M M) (renTm vs (renTm vs ⌜ T ⌝ᵗ)) (var vz)
          ≅ᵀ IhN wk2ₛ T (renTm vs (renTm vs D)) (wk2M M) (var vz)
hyps≅ T D M =
  red→≅ᵀ (subst (λ C → DIh D₂ (wk2M M) C (var vz) ⟶ᵀ* IhN wk2ₛ T D₂ (wk2M M) (var vz))
                (wk2-⌜⌝ T) (ihN-red wk2ₛ T D₂ (wk2M M) (var vz)))
  where D₂ = renTm vs (renTm vs D)

private
  w2⊢ : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {B' : RTy (⌊ Γ ⌋ ∙)} → Ren⊢ Γ ((Γ ▹ B) ▹ B') (λ x → vs (vs x))
  w2⊢ {A = A} v = ∋-cast (renTy-renTy A) (there (there v))

⊢methT : {Γ : Ctx} {I D : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {T : Tel ⌊ Γ ⌋}
         {s b : RTm (((⌊ Γ ⌋ ∙) ∙) ∙)} →
         Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → motCtx Γ I D ⊢ty M → TelOK Γ I T →
         HypCtx Γ I D M T ⊢ b ∷ subTy (methSg s) M →
         Γ ⊢ lam (lam (lam b)) ∷ MethG I D M ⌜ T ⌝ᵗ s
⊢methT {Γ} {I} {D} {M} {T} dI dD dM ok db =
  ⊢lam (ty-El dI) (⊢lam dP₁ (⊢lam dH (conv-ctx (csymᵀ (hyps≅ T D M)) db)))
  where
    dC = ⊢tel dI ok
    P₁ = El (dpay (renTm vs I) (renTm vs D) (renTm vs ⌜ T ⌝ᵗ) (var vz))
    dP₁ = ty-El (⊢dpay (⊢wk dI) (⊢wk dD) (⊢wk dC) (⊢var here))
    Γ₂ = (Γ ▹ El I) ▹ P₁
    dM₂ : motCtx Γ₂ (renTm vs (renTm vs I)) (renTm vs (renTm vs D)) ⊢ty wk2M M
    dM₂ = subst (λ a → motCtx Γ₂ a (renTm vs (renTm vs D)) ⊢ty wk2M M) (sym (renTm-renTm I))
            (subst (λ b → motCtx Γ₂ (renTm (λ x → vs (vs x)) I) b ⊢ty wk2M M) (sym (renTm-renTm D))
              (mot-ren (w2⊢ {B = El I} {B' = P₁}) dM))
    dH = ty-DIh (⊢wk (⊢wk dI)) (⊢wk (⊢wk dD)) dM₂ (⊢wk (⊢wk dC)) (⊢var (there here)) (⊢var here)

------------------------------------------------------------------------
-- 7. ★ …AND IT COMPUTES: the ι-step of the constructor-list form, with
--    the hypotheses already in normal form.
------------------------------------------------------------------------

-- the outer TAG layer of `Dₗ`, peeled
dihₗ : {Cs : Cons Δ c} {C e p : RTm Δ} → Nth Cs k C →
       dih (Dₗ Cs) e (Dₗ Cs) (pair (tag k) p) ⟶* dih (Dₗ Cs) e C p
dihₗ nt =
  step (dih-σ _ _ _ _ _)
  (step (ξ-dihᶜ (ξ-appʳ (βfst _ _)))
  (step (ξ-dihᵖ (βsnd _ _))
    (⟶*-dihᶜ (selF-β nt))))

ιT : {Cs ms : Cons Δ c} {T : Tel Δ} {m i p : RTm Δ} →
     Nth Cs k ⌜ T ⌝ᵗ → Nth ms k m →
     ielim (Dₗ Cs) i (methₗ ms) (conₗ k p)
       ⟶* app (app (app m i) p) (dihN idₛ T (Dₗ Cs) (methₗ ms) p)
ιT {Cs = Cs} {ms} {T} {p = p} nC nm =
  ⟶*-trans (ιₗ nm) (⟶*-appʳ (⟶*-trans (dihₗ nC) (dihN-red₀ T (Dₗ Cs) (methₗ ms) p)))

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

⊢Dₜ : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Ts : Tels ⌊ Γ ⌋ c} → Γ ⊢ I ∷ U → AllOK Γ I Ts →
      Γ ⊢ Dₗ ⌜ Ts ⌝ₛ ∷ Desc I
⊢Dₜ dI oks = ⊢Dₗ dI (allD dI oks)

------------------------------------------------------------------------
-- 9. ★ CONSTRUCTORS: the payload built field by field along the view.
--    At a concrete telescope `subTm (single a) ⌜T⌝` COMPUTES to the next
--    field's `⌜_⌝ᵗ`, so a use site chains these with no casts.
------------------------------------------------------------------------

module _ {Γ : Ctx} {I D i : RTm ⌊ Γ ⌋} (dI : Γ ⊢ I ∷ U) (dD : Γ ⊢ D ∷ Desc I) (di : Γ ⊢ i ∷ El I) where

  ⊢payι : {j e : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ Id (El I) j i → Γ ⊢ e ∷ El (dpay I D ⌜ tι j ⌝ᵗ i)
  ⊢payι = ⊢pay-ι

  ⊢payσ : {S a p : RTm ⌊ Γ ⌋} {T : Tel (⌊ Γ ⌋ ∙)} → TelOK Γ I (tσ S T) →
          Γ ⊢ a ∷ El S → Γ ⊢ p ∷ El (dpay I D (subTm (single a) ⌜ T ⌝ᵗ) i) →
          Γ ⊢ pair a p ∷ El (dpay I D ⌜ tσ S T ⌝ᵗ i)
  ⊢payσ (ok-σ dS ok) = ⊢pay-σλ dI dD (⊢lam (ty-El dS) (⊢tel (⊢wk dI) ok)) di

  ⊢payρ : {j r p : RTm ⌊ Γ ⌋} {T : Tel ⌊ Γ ⌋} → TelOK Γ I (tρ j T) →
          Γ ⊢ r ∷ IMu I D j → Γ ⊢ p ∷ El (dpay I D ⌜ T ⌝ᵗ i) →
          Γ ⊢ pair r p ∷ El (dpay I D ⌜ tρ j T ⌝ᵗ i)
  ⊢payρ (ok-ρ dj ok) = ⊢pay-ρ dI dD (⊢tel dI ok) di

⊢conₜ : {Γ : Ctx} {I i p : RTm ⌊ Γ ⌋} {Ts : Tels ⌊ Γ ⌋ c} {T : Tel ⌊ Γ ⌋} →
        Γ ⊢ I ∷ U → AllOK Γ I Ts → NthT Ts k T → Γ ⊢ i ∷ El I →
        Γ ⊢ p ∷ El (dpay I (Dₗ ⌜ Ts ⌝ₛ) ⌜ T ⌝ᵗ i) → Γ ⊢ conₗ k p ∷ IMu I (Dₗ ⌜ Ts ⌝ₛ) i
⊢conₜ dI oks n di dp = ⊢conₗ dI (allD dI oks) di (nth-⌜⌝ n) dp
