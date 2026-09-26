------------------------------------------------------------------------
-- OCP-0009 · the LEVITATED payload machinery for `fund` (PLAN-LEVITATION
-- stage 2).
--
-- ★ WHY THIS IS A SEPARATE MODULE.  None of it is mutual with `fund`:
--   everything here type-checks against the logical relation alone, so
--   it iterates in seconds rather than minutes (the split `Syntactic`/
--   `Semantic` already make, for the same reason).
--
-- ★ WHAT IS IN IT.  A telescope's interpretation (`IKInterp`) determines
--   everything the eliminator needs:
--     · `payInterp₀` — the payload CODE's decoding, `El (dpay I D C)`,
--       by recursion on the telescope's interpretation: `dι` gives
--       `⊩₀Unit` (D074: fibred, no index equation), `dσ` a `⊩₀Σ` over the field code's
--       interpretation, `dρ` a `⊩₀Σ` over the WHOLE family's `⊩₀IMu`, a
--       stuck telescope a neutral type, a head step `bwd₀`;
--     · `liftPay₀`/`payLift₀` — membership there IS `ILift` (definitionally,
--       up to the two casts): `ILift` was written in `⊩₀Σ` shape;
--     · `dihTy` — the hypotheses' TYPE, `DIh D M C p`, given the motive's
--       interpretation at semantic arguments;
--     · `sn-dpay` — SN of the payload code, SN-under-the-binder paid for by
--       `sn-body` at `x₀` (the anti-renaming trick every binder uses).
--   The hypotheses' MEMBERSHIP needs the eliminator's own induction
--   hypothesis, so it lives in `fund`'s `⊢ielim` case.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Fundamental.Indexed where

open import DirectedHoTT.Metatheory.LogicalRelation
  using ( stablecd? )
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_; ⊤ )

open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ )
open import DirectedHoTT.Metatheory.TySub
  using ( wk-cancel; wk-cancel-tm; iinst-monoˢ )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( meth-inst; ww-cancel; wk2M-cancel )
open import DirectedHoTT.Metatheory.RedCong
  using ( red→≅ᵀ )
open import DirectedHoTT.Metatheory.Injectivity
  using ( Desc-reduct; Σ-reduct; ΣRed; mkΣRed )
open import DirectedHoTT.Metatheory.SubjectReductionBase
  using ( wk-sub )
open import DirectedHoTT.Metatheory.LogicalRelation
open import DirectedHoTT.Metatheory.Fundamental.Syntactic
open import DirectedHoTT.Metatheory.Fundamental.Semantic

private
  variable
    Ξ Θ : Cx

------------------------------------------------------------------------
-- 0. The two tails and a cast.
------------------------------------------------------------------------

-- ★ D074: the family's interpretation is FIBRED — a telescope
--   interpretation over every VALID index — and its membership predicate
IKFam : {I₀ : RTm Ξ} (⊩I : ⊩₀ (El I₀)) → RTm Ξ → Set
IKFam {Ξ} ⊩I D = (j : RTm Ξ) → ⊩I ⊩₀∋ j → IKInterp ⊩I (app D j)

Mem : {I₀ D : RTm Ξ} {⊩I : ⊩₀ (El I₀)} → IKFam ⊩I D → (j : RTm Ξ) → ⊩I ⊩₀∋ j → RTm Ξ → Set
Mem {⊩I = ⊩I} KF = IMuMem (⊩I ⊩₀∋_) (λ j q → ikpredsOf (KF j q))

-- `dpay-σ`'s tail at a field value is the payload of the chosen branch
σ-tail : (I D f u : RTm Ξ) →
         subTy (single u) (El (dpay (renTm vs I) (renTm vs D) (app (renTm vs f) (var vz))))
         ≡ El (dpay I D (app f u))
σ-tail I D f u =
  cong₃ (λ a b g → El (dpay a b (app g u)))
        (wk-cancel-tm u I) (wk-cancel-tm u D) (wk-cancel-tm u f)

-- `dpay-ρ`'s tail is the rest of the telescope, independent of the field
ρ-tail : (I D C u : RTm Ξ) →
         subTy (single u) (El (dpay (renTm vs I) (renTm vs D) (renTm vs C)))
         ≡ El (dpay I D C)
ρ-tail I D C u =
  cong₃ (λ a b c → El (dpay a b c))
        (wk-cancel-tm u I) (wk-cancel-tm u D) (wk-cancel-tm u C)

-- membership rides across a cast — the equation is matched away.
⊩₀cast-mem : {A A' : RTy Ξ} (eq : A ≡ A') (R : ⊩₀ A) {t : RTm Ξ} →
             R ⊩₀∋ t → (⊩₀cast eq R) ⊩₀∋ t
⊩₀cast-mem refl R h = h

⊩₀cast-mem⁻ : {A A' : RTy Ξ} (eq : A ≡ A') (R : ⊩₀ A) {t : RTm Ξ} →
              (⊩₀cast eq R) ⊩₀∋ t → R ⊩₀∋ t
⊩₀cast-mem⁻ refl R h = h

⊩₁cast-mem : {A A' : RTy Ξ} (eq : A ≡ A') (R : ⊩₁ A) {t : RTm Ξ} →
             R ⊩₁∋ t → (⊩₁cast eq R) ⊩₁∋ t
⊩₁cast-mem refl R h = h

-- ★★ the TWO-SLOT twin of `sub-single-Ty`: `⊢ielim`'s result type is
--   `iinst i t M`, and `fund-ty` on the motive delivers `M` under a
--   CONS-substitution of both slots.
iinst-cons-Ty : {Θ : Cx} (σ : Sub Θ Ξ) (j u : RTm Ξ) (M : RTy ((Θ ∙) ∙)) →
                iinst j u (subTy (extS (extS σ)) M)
                  ≡ subTy ((σ ,ₛ j) ,ₛ u) M
iinst-cons-Ty {Θ = Θ} σ j u M =
  trans (cong (subTy (single u)) inner) (sub-single-Ty (σ ,ₛ j) u M)
  where
    bridge : (x : Var ((Θ ∙) ∙)) →
             subTm (extS (single j)) (extS (extS σ) x) ≡ extS (σ ,ₛ j) x
    bridge vz     = refl
    bridge (vs y) =
      trans (wk-sub (single j) (extS σ y))
            (cong (renTm vs) (single-exts σ j y))

    inner : subTy (extS (single j)) (subTy (extS (extS σ)) M)
              ≡ subTy (extS (σ ,ₛ j)) M
    inner = trans (subTy-subTy M) (subTy-cong bridge M)

-- a cons-substitution forgets a weakening
cons-wk-tm : {Θ : Cx} (σ : Sub Θ Ξ) (u : RTm Ξ) (t : RTm Θ) →
             subTm (σ ,ₛ u) (renTm vs t) ≡ subTm σ t
cons-wk-tm σ u t = trans (subTm-renTm t) (subTm-cong (λ _ → refl) t)

-- ★ a DESCRIPTION's semantics: every level-1 witness at `Desc I` is
--   `⊩₁Desc` (every other head clashes with `Desc-reduct`), and a member IS
--   an interpretation, of the index type's REPRESENTATIVE.
record DescView {Ξ} (I D : RTm Ξ) : Set where
  constructor mkDV
  field
    dvI₀ : RTm Ξ
    dvcI : I ≅ dvI₀
    dv⊩I : ⊩₀ (El dvI₀)
    dvK  : IKInterp dv⊩I D

desc-view : {I D : RTm Ξ} (R : ⊩₁ (Desc I)) → R ⊩₁∋ D → DescView I D
desc-view (⊩₁Desc p cI ⊩I) h with Desc-reduct p
... | J , (refl , rI) = mkDV _ (ctrn (hom→≅ rI) cI) ⊩I h
desc-view (⊩₁base p) h with Desc-reduct p
... | _ , (() , _)
desc-view (⊩₁U p) h with Desc-reduct p
... | _ , (() , _)
desc-view (⊩₁ne p _) h with Desc-reduct p
... | _ , (() , _)
desc-view (⊩₁Π p _ _) h with Desc-reduct p
... | _ , (() , _)
desc-view (⊩₁Σ p _ _) h with Desc-reduct p
... | _ , (() , _)
desc-view (⊩₁Hom p _) h with Desc-reduct p
... | _ , (() , _)
desc-view (⊩₁Unit p) h with Desc-reduct p
... | _ , (() , _)
desc-view (⊩₁Nat p) h with Desc-reduct p
... | _ , (() , _)
desc-view (⊩₁Id p) h with Desc-reduct p
... | _ , (() , _)
desc-view (⊩₁IMu p _ _ _ _ _ _) h with Desc-reduct p
... | _ , (() , _)
desc-view (⊩₁Fin p) h with Desc-reduct p
... | _ , (() , _)
desc-view (⊩₁DIhNe p _) h with Desc-reduct p
... | _ , (() , _)

------------------------------------------------------------------------
-- 1. The payload type's interpretation, and its membership.
--
-- `KD` interprets the family's own telescope (a REPRESENTATIVE `D₀` of
-- `D`, as `⊩₀IMu` stores it); `KC` the telescope being walked.
------------------------------------------------------------------------

payInterp₀ : {I D C I₀ D₀ : RTm Ξ} → I ≅ I₀ → D ≅ D₀ →
             (⊩I : ⊩₀ (El I₀)) → IKFam ⊩I D₀ → IKInterp ⊩I C →
             ⊩₀ (El (dpay I D C))
payInterp₀ cI cD ⊩I KF (iki-ne n) = ⊩₀ne doneᵀ (ne-dpay (sne→dstk n))
payInterp₀ cI cD ⊩I KF (iki-exp r k) =
  bwd₀ (stepᵀ (ξ-El (ξ-dpayᶜ (snr→⟶ r))) doneᵀ) (payInterp₀ cI cD ⊩I KF k)
payInterp₀ cI cD ⊩I KF iki-ι =
  ⊩₀Unit (stepᵀ (ξ-El (dpay-ι _ _)) (stepᵀ El-⌜Unit⌝ doneᵀ))
payInterp₀ {I = I} {D = D} cI cD ⊩I KF (iki-σ {f = f} _ _ w k) =
  ⊩₀Σ (stepᵀ (ξ-El (dpay-σ _ _ _ _)) (stepᵀ (El-⌜Σ⌝ _ _) doneᵀ)) w
      (λ u r → ⊩₀cast (sym (σ-tail I D f u)) (payInterp₀ cI cD ⊩I KF (k u r)))
payInterp₀ {I = I} {D = D} cI cD ⊩I KF (iki-ρ {C = C} _ vj k) =
  ⊩₀Σ (stepᵀ (ξ-El (dpay-ρ _ _ _ _)) (stepᵀ (El-⌜Σ⌝ _ _) doneᵀ))
      (⊩₀IMu (stepᵀ El-⌜IMu⌝ doneᵀ) cI cD crfl ⊩I vj KF)
      (λ u r → ⊩₀cast (sym (ρ-tail I D C u)) (payInterp₀ cI cD ⊩I KF k))

-- ★ an `ILift` IS a member of the payload type, and conversely.
liftPay₀ : {I D C I₀ D₀ : RTm Ξ} (cI : I ≅ I₀) (cD : D ≅ D₀) →
           (⊩I : ⊩₀ (El I₀)) (KF : IKFam ⊩I D₀) (KC : IKInterp ⊩I C) →
           {p : RTm Ξ} →
           ILift (ikpredsOf KC) (Mem KF) p →
           (payInterp₀ cI cD ⊩I KF KC) ⊩₀∋ p
payLift₀ : {I D C I₀ D₀ : RTm Ξ} (cI : I ≅ I₀) (cD : D ≅ D₀) →
           (⊩I : ⊩₀ (El I₀)) (KF : IKFam ⊩I D₀) (KC : IKInterp ⊩I C) →
           {p : RTm Ξ} →
           (payInterp₀ cI cD ⊩I KF KC) ⊩₀∋ p →
           ILift (ikpredsOf KC) (Mem KF) p

liftPay₀ cI cD ⊩I KF (iki-ne n) h = h
liftPay₀ cI cD ⊩I KF (iki-exp r k) h =
  bwd₀-mem⁻ (stepᵀ (ξ-El (ξ-dpayᶜ (snr→⟶ r))) doneᵀ) (payInterp₀ cI cD ⊩I KF k)
            (liftPay₀ cI cD ⊩I KF k h)
liftPay₀ cI cD ⊩I KF iki-ι h = h
liftPay₀ {I = I} {D = D} cI cD ⊩I KF (iki-σ {f = f} _ _ w k) {p = p} (sn , (q , rest)) =
  ( sn
  , ( q
    , ⊩₀cast-mem (sym (σ-tail I D f (fst p))) (payInterp₀ cI cD ⊩I KF (k (fst p) q))
                 (liftPay₀ cI cD ⊩I KF (k (fst p) q) rest) ) )
liftPay₀ {I = I} {D = D} cI cD ⊩I KF (iki-ρ {C = C} _ _ k) {p = p} (sn , (fm , rest)) =
  ( sn
  , ( fm
    , ⊩₀cast-mem (sym (ρ-tail I D C (fst p))) (payInterp₀ cI cD ⊩I KF k)
                 (liftPay₀ cI cD ⊩I KF k rest) ) )

payLift₀ cI cD ⊩I KF (iki-ne n) h = h
payLift₀ cI cD ⊩I KF (iki-exp r k) h =
  payLift₀ cI cD ⊩I KF k
           (bwd₀-mem (stepᵀ (ξ-El (ξ-dpayᶜ (snr→⟶ r))) doneᵀ) (payInterp₀ cI cD ⊩I KF k) h)
payLift₀ cI cD ⊩I KF iki-ι h = h
payLift₀ {I = I} {D = D} cI cD ⊩I KF (iki-σ {f = f} _ _ w k) {p = p} (sn , (q , rest)) =
  ( sn
  , ( q
    , payLift₀ cI cD ⊩I KF (k (fst p) q)
               (⊩₀cast-mem⁻ (sym (σ-tail I D f (fst p))) (payInterp₀ cI cD ⊩I KF (k (fst p) q)) rest) ) )
payLift₀ {I = I} {D = D} cI cD ⊩I KF (iki-ρ {C = C} _ _ k) {p = p} (sn , (fm , rest)) =
  ( sn
  , ( fm
    , payLift₀ cI cD ⊩I KF k
               (⊩₀cast-mem⁻ (sym (ρ-tail I D C (fst p))) (payInterp₀ cI cD ⊩I KF k) rest) ) )

-- the payload code's `U`-membership payload is trivial (its decoding is a
--   Σ/Id/neutral, never a Π), carried through the head steps.
payT-pay : {I D C I₀ D₀ : RTm Ξ} (cI : I ≅ I₀) (cD : D ≅ D₀) →
           (⊩I : ⊩₀ (El I₀)) (KF : IKFam ⊩I D₀) (KC : IKInterp ⊩I C) {c : RTm Ξ} →
           PayT (payInterp₀ cI cD ⊩I KF KC) c
payT-pay cI cD ⊩I KF (iki-ne n) = _
payT-pay cI cD ⊩I KF iki-ι = _
payT-pay cI cD ⊩I KF (iki-σ _ _ _ _) = _
payT-pay cI cD ⊩I KF (iki-ρ _ _ _) = _
payT-pay cI cD ⊩I KF (iki-exp r k) =
  payT-bwd₀' (stepᵀ (ξ-El (ξ-dpayᶜ (snr→⟶ r))) doneᵀ) (payInterp₀ cI cD ⊩I KF k)
             (payT-pay cI cD ⊩I KF k)

------------------------------------------------------------------------
-- 2. The hypotheses' TYPE, given the motive at semantic arguments.
------------------------------------------------------------------------

dihTy : {I₀ D C : RTm Ξ} {M : RTy ((Ξ ∙) ∙)} {⊩I : ⊩₀ (El I₀)} →
        (KF : IKFam ⊩I D) →
        (MotC : (j u : RTm Ξ) (hj : ⊩I ⊩₀∋ j) → SN u → Mem KF j hj u →
                ⊩₁ (iinst j u M)) →
        (KC : IKInterp ⊩I C) {p : RTm Ξ} →
        ILift (ikpredsOf KC) (Mem KF) p →
        ⊩₁ (DIh D M C p)
dihTy KF MotC (iki-ne n) l = ⊩₁DIhNe doneᵀ (sne→ne n)
dihTy KF MotC (iki-exp r k) l =
  bwd₁ (stepᵀ (ξ-DIhᶜ (snr→⟶ r)) doneᵀ) (dihTy KF MotC k l)
dihTy KF MotC iki-ι l = ⊩₁Unit (stepᵀ (DIh-ι _ _ _) doneᵀ)
dihTy KF MotC (iki-σ _ _ w k) {p = p} (sn , (q , rest)) =
  bwd₁ (stepᵀ (DIh-σ _ _ _ _ _) doneᵀ) (dihTy KF MotC (k (fst p) q) rest)
dihTy {D = D} {M = M} KF MotC (iki-ρ {j = j} {C = C} _ vj k) {p = p} (sn , ((snf , m) , rest)) =
  ⊩₁Σ (stepᵀ (DIh-ρ _ _ _ _ _) doneᵀ) (MotC j (fst p) vj snf m)
      (λ u r → ⊩₁cast (sym (wk-cancel u (DIh D M C (snd p)))) (dihTy KF MotC k rest))

------------------------------------------------------------------------
-- 2b. ★ The hypotheses' WALK — the SYNTACTIC shadow of `dihTy`'s
--   recursion: the telescope/payload pairs `DIh` visits on its way to a
--   head.  It carries no semantics, so it ANTI-RENAMES (`fund` runs at
--   `vs`; the type normaliser wants the walk back at the source scope),
--   and `NormTy.dihNF` recurses on it structurally — `DIh-σ` creates
--   `app f (fst p)`, which no syntactic measure sees shrink.
------------------------------------------------------------------------

data Walk {Ξ} : RTm Ξ → RTm Ξ → Set where
  w-ne  : {C p : RTm Ξ} → SNe C → Walk C p
  w-exp : {C C' p : RTm Ξ} → SNRed C C' → Walk C' p → Walk C p
  w-ι   : {p : RTm Ξ} → Walk dι p
  w-σ   : {S f p : RTm Ξ} → Walk (app f (fst p)) (snd p) → Walk (dσ S f) p
  w-ρ   : {j C p : RTm Ξ} → Walk C (snd p) → Walk (dρ j C) p

walkOf : {I₀ D C : RTm Ξ} {⊩I : ⊩₀ (El I₀)} (KF : IKFam ⊩I D) (KC : IKInterp ⊩I C)
         {p : RTm Ξ} → ILift (ikpredsOf KC) (Mem KF) p → Walk C p
walkOf KF (iki-ne n) l = w-ne n
walkOf KF (iki-exp r k) l = w-exp r (walkOf KF k l)
walkOf KF iki-ι l = w-ι
walkOf KF (iki-σ _ _ w k) {p = p} (sn , (q , rest)) = w-σ (walkOf KF (k (fst p) q) rest)
walkOf KF (iki-ρ _ vj k) (sn , (_ , rest)) = w-ρ (walkOf KF k rest)

-- the three telescope heads invert through a renaming (generated: one
-- clause per term former, no catch-all).

ren-dι-inv : {ρ : Ren Θ Ξ} (C : RTm Θ) → dι ≡ renTm ρ C → C ≡ dι
ren-dι-inv dι refl = refl
ren-dι-inv (var _) ()
ren-dι-inv (lam _) ()
ren-dι-inv (app _ _) ()
ren-dι-inv (pair _ _) ()
ren-dι-inv (absurd _ _) ()
ren-dι-inv (ordtr _ _ _ _ _) ()
ren-dι-inv (fst _) ()
ren-dι-inv (snd _) ()
ren-dι-inv ⌜base⌝ ()
ren-dι-inv (⌜Π⌝ _ _) ()
ren-dι-inv (⌜Σ⌝ _ _) ()
ren-dι-inv (⌜Hom⌝ _ _ _) ()
ren-dι-inv (hrefl _ _) ()
ren-dι-inv (tr _ _ _) ()
ren-dι-inv (ap _ _ _) ()
ren-dι-inv (⌜Id⌝ _ _ _) ()
ren-dι-inv (idrefl _ _) ()
ren-dι-inv (jsub _ _ _) ()
ren-dι-inv unit ()
ren-dι-inv nzero ()
ren-dι-inv (nsuc _) ()
ren-dι-inv (natrec _ _ _) ()
ren-dι-inv (con _) ()
ren-dι-inv (ielim _ _ _ _) ()
ren-dι-inv (dσ _ _) ()
ren-dι-inv (dρ _ _) ()
ren-dι-inv (dpay _ _ _) ()
ren-dι-inv (dih _ _ _ _) ()
ren-dι-inv fzero ()
ren-dι-inv (fsuc _) ()
ren-dι-inv (fcase _ _ _) ()
ren-dι-inv (fcase0 _) ()
ren-dι-inv (psplit _ _) ()
ren-dι-inv ⌜Nat⌝ ()
ren-dι-inv (⌜IMu⌝ _ _ _) ()
ren-dι-inv (⌜Fin⌝ _) ()
ren-dι-inv ⌜Unit⌝ ()

ren-dσ-inv : {ρ : Ren Θ Ξ} (C : RTm Θ) {S f : RTm Ξ} → dσ S f ≡ renTm ρ C →
             Σ (RTm Θ) (λ S₀ → Σ (RTm Θ) (λ f₀ →
               (C ≡ dσ S₀ f₀) × ((S ≡ renTm ρ S₀) × (f ≡ renTm ρ f₀))))
ren-dσ-inv (dσ S₀ f₀) refl = S₀ , (f₀ , (refl , (refl , refl)))
ren-dσ-inv (var _) ()
ren-dσ-inv (lam _) ()
ren-dσ-inv (app _ _) ()
ren-dσ-inv (pair _ _) ()
ren-dσ-inv (absurd _ _) ()
ren-dσ-inv (ordtr _ _ _ _ _) ()
ren-dσ-inv (fst _) ()
ren-dσ-inv (snd _) ()
ren-dσ-inv ⌜base⌝ ()
ren-dσ-inv (⌜Π⌝ _ _) ()
ren-dσ-inv (⌜Σ⌝ _ _) ()
ren-dσ-inv (⌜Hom⌝ _ _ _) ()
ren-dσ-inv (hrefl _ _) ()
ren-dσ-inv (tr _ _ _) ()
ren-dσ-inv (ap _ _ _) ()
ren-dσ-inv (⌜Id⌝ _ _ _) ()
ren-dσ-inv (idrefl _ _) ()
ren-dσ-inv (jsub _ _ _) ()
ren-dσ-inv unit ()
ren-dσ-inv nzero ()
ren-dσ-inv (nsuc _) ()
ren-dσ-inv (natrec _ _ _) ()
ren-dσ-inv (con _) ()
ren-dσ-inv (ielim _ _ _ _) ()
ren-dσ-inv dι ()
ren-dσ-inv (dρ _ _) ()
ren-dσ-inv (dpay _ _ _) ()
ren-dσ-inv (dih _ _ _ _) ()
ren-dσ-inv fzero ()
ren-dσ-inv (fsuc _) ()
ren-dσ-inv (fcase _ _ _) ()
ren-dσ-inv (fcase0 _) ()
ren-dσ-inv (psplit _ _) ()
ren-dσ-inv ⌜Nat⌝ ()
ren-dσ-inv (⌜IMu⌝ _ _ _) ()
ren-dσ-inv (⌜Fin⌝ _) ()
ren-dσ-inv ⌜Unit⌝ ()

ren-dρ-inv : {ρ : Ren Θ Ξ} (T : RTm Θ) {j C : RTm Ξ} → dρ j C ≡ renTm ρ T →
             Σ (RTm Θ) (λ j₀ → Σ (RTm Θ) (λ C₀ →
               (T ≡ dρ j₀ C₀) × ((j ≡ renTm ρ j₀) × (C ≡ renTm ρ C₀))))
ren-dρ-inv (dρ j₀ C₀) refl = j₀ , (C₀ , (refl , (refl , refl)))
ren-dρ-inv (var _) ()
ren-dρ-inv (lam _) ()
ren-dρ-inv (app _ _) ()
ren-dρ-inv (pair _ _) ()
ren-dρ-inv (absurd _ _) ()
ren-dρ-inv (ordtr _ _ _ _ _) ()
ren-dρ-inv (fst _) ()
ren-dρ-inv (snd _) ()
ren-dρ-inv ⌜base⌝ ()
ren-dρ-inv (⌜Π⌝ _ _) ()
ren-dρ-inv (⌜Σ⌝ _ _) ()
ren-dρ-inv (⌜Hom⌝ _ _ _) ()
ren-dρ-inv (hrefl _ _) ()
ren-dρ-inv (tr _ _ _) ()
ren-dρ-inv (ap _ _ _) ()
ren-dρ-inv (⌜Id⌝ _ _ _) ()
ren-dρ-inv (idrefl _ _) ()
ren-dρ-inv (jsub _ _ _) ()
ren-dρ-inv unit ()
ren-dρ-inv nzero ()
ren-dρ-inv (nsuc _) ()
ren-dρ-inv (natrec _ _ _) ()
ren-dρ-inv (con _) ()
ren-dρ-inv (ielim _ _ _ _) ()
ren-dρ-inv dι ()
ren-dρ-inv (dσ _ _) ()
ren-dρ-inv (dpay _ _ _) ()
ren-dρ-inv (dih _ _ _ _) ()
ren-dρ-inv fzero ()
ren-dρ-inv (fsuc _) ()
ren-dρ-inv (fcase _ _ _) ()
ren-dρ-inv (fcase0 _) ()
ren-dρ-inv (psplit _ _) ()
ren-dρ-inv ⌜Nat⌝ ()
ren-dρ-inv (⌜IMu⌝ _ _ _) ()
ren-dρ-inv (⌜Fin⌝ _) ()
ren-dρ-inv ⌜Unit⌝ ()

walk-anti : {ρ : Ren Θ Ξ} {C p : RTm Θ} {C' p' : RTm Ξ} →
            Walk C' p' → C' ≡ renTm ρ C → p' ≡ renTm ρ p → Walk C p
walk-anti (w-ne n) refl refl = w-ne (sne-anti n)
walk-anti (w-exp r k) refl ep with snr-anti r
... | C₀ , (r₀ , e₀) = w-exp r₀ (walk-anti k e₀ ep)
walk-anti {C = C} w-ι e ep with ren-dι-inv C e
... | refl = w-ι
walk-anti {C = C} (w-σ k) e ep with ren-dσ-inv C e
... | S₀ , (f₀ , (refl , (_ , ef))) = w-σ (walk-anti k (cong₂ app ef (cong fst ep)) (cong snd ep))
walk-anti {C = C} (w-ρ k) e ep with ren-dρ-inv C e
... | j₀ , (C₀ , (refl , (_ , eC))) = w-ρ (walk-anti k eC (cong snd ep))

------------------------------------------------------------------------
-- 3. SN of the payload CODE.  The `dσ`/`dρ` reducts put the tail under a
--    binder; its SN comes back from the tail's instance at `x₀` (`sn-body`).
------------------------------------------------------------------------

sn-dpay : (x₀ : Var Ξ) {I D C I₀ : RTm Ξ} {⊩I : ⊩₀ (El I₀)} →
          SN I → SN D → IKInterp ⊩I C → SN (dpay I D C)
sn-dpay x₀ snI snD (iki-ne n) = sn-ne (sne-dpay snI snD (sn-ne n) (sne→dstk n))
sn-dpay x₀ snI snD (iki-exp r k) = sn-exp (snr-dpayᶜ r) (sn-dpay x₀ snI snD k)
sn-dpay x₀ snI snD iki-ι = sn-exp (snr-dpay-ι snI snD) sn-cUnit
sn-dpay x₀ {I = I} {D = D} snI snD (iki-σ {S = S} {f = f} sS sf w k) =
  sn-exp snr-dpay-σ
    (sn-cΣ sS (sn-body x₀ (subst SN (sym (cong₃ (λ a b g → dpay a b (app g (var x₀)))
                                               (wk-cancel-tm (var x₀) I) (wk-cancel-tm (var x₀) D)
                                               (wk-cancel-tm (var x₀) f)))
                                   (sn-dpay x₀ snI snD (k (var x₀) (CR3₀ w (sne-var x₀)))))))
sn-dpay x₀ {I = I} {D = D} snI snD (iki-ρ {j = j} {C = C} sj _ k) =
  sn-exp snr-dpay-ρ
    (sn-cΣ (sn-cIMu snI snD sj)
           (sn-body x₀ (subst SN (sym (cong₃ dpay (wk-cancel-tm (var x₀) I) (wk-cancel-tm (var x₀) D)
                                                  (wk-cancel-tm (var x₀) C)))
                              (sn-dpay x₀ snI snD k))))

------------------------------------------------------------------------
-- 4. ★★★ THE ELIMINATOR'S SEMANTICS.  Induction on the family's membership
--    (`go`), the hypotheses by recursion on the telescope's interpretation
--    (`dihSem`), mutually: a `dρ` field's hypothesis IS `go` at its own
--    index, on a strictly smaller membership.  `natrec`'s scheme, with the
--    payload walked where `natrec` has a numeral.
--    At `con p`: one ι head step, then the method's Π-membership three
--    times — at the index, the payload (`liftPay₀`), the hypotheses — and
--    the result type is the motive at `con p` by σ-calculus alone.
------------------------------------------------------------------------

-- an `ILift` carries SN at its root
ilift-sn : {PI : RTm Ξ → Set} {C : RTm Ξ} (kp : IKPred Ξ PI C)
           {P : (j : RTm Ξ) → PI j → RTm Ξ → Set} {t : RTm Ξ} →
           ILift kp P t → SN t
ilift-sn ikp-ne        h = h
ilift-sn ikp-ι         h = h
ilift-sn (ikp-σ Q k)   h = projl h
ilift-sn (ikp-ρ q k)   h = projl h
ilift-sn (ikp-exp r k) h = ilift-sn k h

-- the method's two domain casts
Π-dom : {A A' : RTy Ξ} {B : RTy (Ξ ∙)} → A ≡ A' → Π A B ≡ Π A' B
Π-dom refl = refl

module ElimSem {I D I₀ e : RTm Ξ} {M : RTy ((Ξ ∙) ∙)}
  (cI : I ≅ I₀) (⊩I : ⊩₀ (El I₀)) (snD : SN D) (KF : IKFam ⊩I D)
  (MotC : (j u : RTm Ξ) (hj : ⊩I ⊩₀∋ j) → SN u → Mem KF j hj u → ⊩₁ (iinst j u M))
  (Rₑ : ⊩₁ (MethTy I D M)) (hₑ : Rₑ ⊩₁∋ e)
  where

  snE : SN e
  snE = CR1₁ Rₑ hₑ

  -- the index type's interpretation AT `El I` itself
  ⊩I' : ⊩₀ (El I)
  ⊩I' = conv₀ (El≅ (csym cI)) ⊩I

  idx : (j : RTm Ξ) → ⊩I ⊩₀∋ j → (emb ⊩I') ⊩₁∋ j
  idx j hj = projl (emb-coh ⊩I') j (projl (irrel₀ (El≅ (csym cI)) ⊩I ⊩I') j hj)

  go : (j u : RTm Ξ) (hj : ⊩I ⊩₀∋ j) (snu : SN u) (mm : Mem KF j hj u) →
       (MotC j u hj snu mm) ⊩₁∋ ielim D j e u
  dihSem : {C : RTm Ξ} (KC : IKInterp ⊩I C) {p : RTm Ξ}
           (l : ILift (ikpredsOf KC) (Mem KF) p) →
           (dihTy KF MotC KC l) ⊩₁∋ dih D e C p

  go j u hj snu (imm-ne nt) =
    CR3₁ (MotC j u hj snu (imm-ne nt))
         (sne-ielim snD (CR1₀ ⊩I hj) snE snu (sne→mustk nt))
  go j u hj snu (imm-exp {t' = u'} rr mm) =
    exp₁ (MotC j u hj snu (imm-exp rr mm)) (snr-ielimᵗ rr)
      (projl (irrel₁ (csymᵀ (red→≅ᵀ (iinst-monoˢ M j (step (snr→⟶ rr) done))))
                     (MotC j u' hj (sn-whred snu rr) mm) (MotC j u hj snu (imm-exp rr mm)))
             _ (go j u' hj (sn-whred snu rr) mm))
  go j .(con p) hj snu (imm-con {p = p} l) =
    exp₁ (MotC j (con p) hj snu (imm-con l)) (snr-ι snD (CR1₀ ⊩I hj) snE snp)
      (projl (irrel₁ crflᵀ (dfst a₃) (MotC j (con p) hj snu (imm-con l))) _ (dsnd a₃))
    where
    Kj = KF j hj
    snp = ilift-sn (ikpredsOf Kj) l
    a₁ = relTy (Π-dom (cong₂ (λ a b → El (dpay a b (app b j)))
                             (wk-cancel-tm j I) (wk-cancel-tm j D)))
               (⊩₁-app Rₑ (emb ⊩I') hₑ (idx j hj))
    S₂ = emb (payInterp₀ cI crfl ⊩I KF Kj)
    a₂ = relTy (Π-dom (cong₄ DIh (ww-cancel p j D) (wk2M-cancel p j M)
                             (cong₂ app (ww-cancel p j D) (wk-cancel-tm p j)) refl))
               (⊩₁-app (dfst a₁) S₂ (dsnd a₁)
                       (projl (emb-coh (payInterp₀ cI crfl ⊩I KF Kj)) p
                              (liftPay₀ cI crfl ⊩I KF Kj l)))
    a₃ = relTy (meth-inst (dih D e (app D j) p) p j M)
               (⊩₁-app (dfst a₂) (dihTy KF MotC Kj l) (dsnd a₂) (dihSem Kj l))

  dihSem (iki-ne n) {p = p} l =
    sn-ne (sne-dih snD snE (sn-ne n) l (sne→dstk n))
  dihSem (iki-exp r k) l =
    bwd₁-mem⁻ (stepᵀ (ξ-DIhᶜ (snr→⟶ r)) doneᵀ) (dihTy KF MotC k l)
      (exp₁ (dihTy KF MotC k l) (snr-dihᶜ r) (dihSem k l))
  dihSem iki-ι l =
    sn-exp (snr-dih-ι snD snE l) sn-unit
  dihSem (iki-σ sS sf w k) {p = p} (sn , (q , rest)) =
    bwd₁-mem⁻ (stepᵀ (DIh-σ _ _ _ _ _) doneᵀ) (dihTy KF MotC (k (fst p) q) rest)
      (exp₁ (dihTy KF MotC (k (fst p) q) rest) (snr-dih-σ sS) (dihSem (k (fst p) q) rest))
  dihSem (iki-ρ {j = j'} {C = C} sj vj k) {p = p} (sn , ((snf , m) , rest)) =
    exp₁ (dihTy KF MotC (iki-ρ sj vj k) (sn , ((snf , m) , rest))) snr-dih-ρ
      (sem-pair (stepᵀ (DIh-ρ D M j' C p) doneᵀ) (MotC j' (fst p) vj snf m)
                (λ u r → ⊩₁cast (sym (wk-cancel u (DIh D M C (snd p)))) (dihTy KF MotC k rest))
                {a = ielim D j' e (fst p)} {b = dih D e C (snd p)}
                (CR1₁ (MotC j' (fst p) vj snf m) hf) (CR1₁ (dihTy KF MotC k rest) hs)
                hf
                (⊩₁cast-mem (sym (wk-cancel (ielim D j' e (fst p)) (DIh D M C (snd p))))
                            (dihTy KF MotC k rest) hs))
    where
    hf = go j' (fst p) vj snf m
    hs = dihSem k rest

------------------------------------------------------------------------
-- 5. Glue for `fund`'s levitated cases (none of it is mutual with `fund`).
------------------------------------------------------------------------

-- a `U`-member, on the canonical `U` interpretation
uSem : {c : RTm Ξ} → Rel U c → (⊩₁U doneᵀ) ⊩₁∋ c
uSem h = projl (irrel₁ crflᵀ (dfst h) (⊩₁U doneᵀ)) _ (dsnd h)

-- an index, as a member of the index type's REPRESENTATIVE (and back)
elIdx : {I I₀ j : RTm Ξ} (cI : I ≅ I₀) (⊩I : ⊩₀ (El I₀)) → Rel (El I) j → ⊩I ⊩₀∋ j
elIdx {j = j} cI ⊩I h =
  projl (irrel₀ (El≅ cI) ⊩I' ⊩I) j
        (projr (emb-coh ⊩I') j (projl (irrel₁ crflᵀ (dfst h) (emb ⊩I')) j (dsnd h)))
  where ⊩I' = conv₀ (El≅ (csym cI)) ⊩I

idxMem : {I I₀ j : RTm Ξ} (cI : I ≅ I₀) (⊩I : ⊩₀ (El I₀)) → ⊩I ⊩₀∋ j →
         (emb (conv₀ (El≅ (csym cI)) ⊩I)) ⊩₁∋ j
idxMem {j = j} cI ⊩I hj =
  projl (emb-coh (conv₀ (El≅ (csym cI)) ⊩I)) j
        (projl (irrel₀ (El≅ (csym cI)) ⊩I (conv₀ (El≅ (csym cI)) ⊩I)) j hj)

-- a telescope's interpretation, re-based on the family's index witness
rebase : {I C I₀ : RTm Ξ} → DescView I C → (⊩I : ⊩₀ (El I₀)) → I ≅ I₀ → IKInterp ⊩I C
rebase (mkDV I₁ c₁ ⊩I₁ K) ⊩I cI = ikinterp-irrel (El≅ (ctrn (csym c₁) cI)) ⊩I₁ ⊩I K

-- ★ D074: a DESCRIPTION `D ∷ Π (El I) (Desc I)` gives a telescope
--   interpretation over every valid index — its fibre `D j`.
famInterp : {I D I₀ : RTm Ξ} (cI : I ≅ I₀) (⊩I : ⊩₀ (El I₀)) → Rel (DescF I) D → IKFam ⊩I D
famInterp {I = I} {D = D} cI ⊩I h j hj = rebase (desc-view (dfst a) (dsnd a)) ⊩I cI
  where
    a : Rel (Desc I) (app D j)
    a = relTy (cong Desc (wk-cancel-tm j I))
              (⊩₁-app (dfst h) (emb (conv₀ (El≅ (csym cI)) ⊩I)) (dsnd h) (idxMem cI ⊩I hj))

-- the `dσ` branch's type at a field value is the family's own `Desc I`
wk-tail : {Θ : Cx} (σ : Sub Θ Ξ) (I : RTm Θ) (v : RTm Ξ) →
          subTm (single v) (subTm (extS σ) (renTm vs I)) ≡ subTm σ I
wk-tail σ I v = trans (sub-single-Tm σ v (renTm vs I)) (cons-wk-tm σ v I)

snfsuc-inv : {t : RTm Ξ} → SN (fsuc t) → SN t
snfsuc-inv (sn-fsuc h) = h
snfsuc-inv (sn-ne ())
snfsuc-inv (sn-exp () _)

-- `fcase`'s successor branch lands at the motive's `fsuc` instance
fsuc-cons : {Θ : Cx} (σ : Sub Θ Ξ) (m : RTm Ξ) (P : RTy (Θ ∙)) →
            subTy (σ ,ₛ m) (subTy fsucS P) ≡ subTy (σ ,ₛ fsuc m) P
fsuc-cons σ m P = trans (subTy-subTy P) (subTy-cong (λ { vz → refl ; (vs x) → refl }) P)

-- `psplit`'s body lands at the motive's `pair` instance …
pair-cons : {Θ : Cx} (σ : Sub Θ Ξ) (x y : RTm Ξ) (P : RTy (Θ ∙)) →
            subTy ((σ ,ₛ x) ,ₛ y) (subTy pairS P) ≡ subTy (σ ,ₛ pair x y) P
pair-cons σ x y P = trans (subTy-subTy P) (subTy-cong (λ { vz → refl ; (vs z) → refl }) P)

-- … and its term is the double substitution
single2-cons : {Θ : Cx} (σ : Sub Θ Ξ) (x y : RTm Ξ) (b : RTm ((Θ ∙) ∙)) →
               subTm (single2 x y) (subTm (extS (extS σ)) b) ≡ subTm ((σ ,ₛ x) ,ₛ y) b
single2-cons {Θ = Θ} σ x y b = trans (subTm-subTm b) (subTm-cong pt b)
  where
    pt : (z : Var ((Θ ∙) ∙)) → subTm (single2 x y) (extS (extS σ) z) ≡ ((σ ,ₛ x) ,ₛ y) z
    pt vz          = refl
    pt (vs vz)     = refl
    pt (vs (vs w)) = trans (cong (subTm (single2 x y)) (renTm-renTm (σ w)))
                           (trans (subTm-renTm (σ w)) (trans (subTm-cong (λ _ → refl) (σ w)) (subTm-id (σ w))))

-- ★ a Σ-witness has component interpretations: the first at the whole
--   first component type, the second at a VARIABLE instance — what an
--   eliminator of a pair needs to take SN out from under its binders.
Σ-parts : {F : RTy Ξ} {G : RTy (Ξ ∙)} (R : ⊩₁ (Σ' F G)) (x₀ : Var Ξ) →
          Σ (⊩₁ F) (λ _ → Σ (⊩₁ (subTy (single (var x₀)) G)) (λ _ → ⊤))
Σ-parts (⊩₁Σ p ⊩F ⊩G) x₀ with Σ-reduct p
... | mkΣRed _ _ refl rF rG =
      ( bwd₁ rF ⊩F
      , ( bwd₁ (⟶ᵀ*-sub (single (var x₀)) rG) (⊩G (var x₀) (CR3₁ ⊩F (sne-var x₀))) , _ ) )
Σ-parts (⊩₁base p) x₀ with Σ-reduct p
... | mkΣRed _ _ () _ _
Σ-parts (⊩₁U p) x₀ with Σ-reduct p
... | mkΣRed _ _ () _ _
Σ-parts (⊩₁ne p _) x₀ with Σ-reduct p
... | mkΣRed _ _ () _ _
Σ-parts (⊩₁Π p _ _) x₀ with Σ-reduct p
... | mkΣRed _ _ () _ _
Σ-parts (⊩₁Hom p _) x₀ with Σ-reduct p
... | mkΣRed _ _ () _ _
Σ-parts (⊩₁Unit p) x₀ with Σ-reduct p
... | mkΣRed _ _ () _ _
Σ-parts (⊩₁Nat p) x₀ with Σ-reduct p
... | mkΣRed _ _ () _ _
Σ-parts (⊩₁Id p) x₀ with Σ-reduct p
... | mkΣRed _ _ () _ _
Σ-parts (⊩₁IMu p _ _ _ _ _ _) x₀ with Σ-reduct p
... | mkΣRed _ _ () _ _
Σ-parts (⊩₁Fin p) x₀ with Σ-reduct p
... | mkΣRed _ _ () _ _
Σ-parts (⊩₁Desc p _ _) x₀ with Σ-reduct p
... | mkΣRed _ _ () _ _
Σ-parts (⊩₁DIhNe p _) x₀ with Σ-reduct p
... | mkΣRed _ _ () _ _
