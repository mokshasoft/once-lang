------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ TYPES NORMALISE, and TYPE CONVERSION IS DECIDABLE.
--                      (PLAN-BIDI S4, route C — step 3)
--
-- ★ THE DELIVERABLE:
--       normTy    : ⊢ctx Γ → Γ ⊢ty A → WNᵀ A          -- a normal form
--       decConvᵀ  : ⊢ctx Γ → Γ ⊢ty A → Γ ⊢ty B → Dec (A ≅ᵀ B)
--   With `Algorithm/DecideConversionTyped` (terms) this closes conversion
--   for the whole declarative kernel.
--
-- ★★ WHY IT TERMINATES STRUCTURALLY, although `Hom-Π` makes types GROW.
--   `Hom (Π F G) f g ⟶ᵀ Π F (Hom G (app f↑ vz) (app g↑ vz))` creates new
--   terms, so a recursion on the formation DERIVATION cannot follow it.
--   But `homNF` recurses on the NORMAL AMBIENT, and `G` is a strict subterm
--   of the normal `Π F G`; the created applications are normalised by the
--   TYPED term normaliser `wnorm` — they are well-typed, so no "junk"
--   (a non-λ value applied) ever reaches it.  That is route C's point:
--   typing is what makes the created terms normalisable.
--   `elNF` likewise recurses on the NORMAL CODE; `Hom Nat` on the numerals.
--
-- ⚠ NO CATCH-ALLS in the head analyses: every `RTm`/`RTy` constructor has
--   its own clause (generated), so a new former is a coverage error here,
--   not a silently mis-classified row.  Normality of a stuck head is then
--   Agda's own index mismatch — `El-⌜base⌝` cannot target `El (app _ _)`.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.NormTy where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; ¬_; ⊥ )
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Variance using () renaming ( true to trueᵇ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ
        ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ; ⟶ᵀ*-Homᵀ; ⟶ᵀ*-Homˡ; ⟶ᵀ*-Homʳ
        ; ⟶ᵀ*-Idᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; ⟶ᵀ*-IMu; ⟶ᵀ*-IMuᴵ; ⟶ᵀ*-IMuᴰ; ⟶ᵀ*-Desc
        ; ⟶ᵀ*-DIhᴰ; ⟶ᵀ*-DIhᴹ; ⟶ᵀ*-DIhᶜ; ⟶ᵀ*-DIhᵖ; red→≅ᵀ )
open import DirectedHoTT.Metatheory.TySub
  using ( Sub⊢; Sub⊢-ext; ⊢single; sub-lemma; sub-ty; Ren⊢; Ren⊢-ext; ren-lemma; ren-ty
        ; ∋-cast; ⟶ᵀ-ren; iinst-wf; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var )
open import DirectedHoTT.Metatheory.Fundamental.Indexed using ( Walk; w-ne; w-exp; w-ι; w-σ; w-ρ )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( sr; sr*; gen-⌜Π⌝; gen-⌜Σ⌝; gen-⌜Hom⌝; gen-⌜Id⌝; gen-nsuc; ⊢wk; ⊢-cast; dσ-step; dρ-step )
open import DirectedHoTT.Metatheory.Validity using ( srᵀ*; wk-app-vz )
open import DirectedHoTT.Metatheory.LogicalRelation
  using ( IsNormal; WN; mkWN; dstk?; dstk?-red*; dstk?-ren; sne→dstk; snr→⟶ )
open import DirectedHoTT.Metatheory.Fundamental using ( wnorm; dih-walk )
open import DirectedHoTT.Metatheory.Injectivity using ( church-rosserᵀ )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no; _≟Ty_ )

------------------------------------------------------------------------
-- 0. Normal types, and a type WITH its normal form.
------------------------------------------------------------------------

IsNormalᵀ : {Γ : Cx} → RTy Γ → Set
IsNormalᵀ A = ∀ {B} → ¬ (A ⟶ᵀ B)

record WNᵀ {Γ : Cx} (A : RTy Γ) : Set where
  constructor mkWNᵀ
  field
    nfᵀ  : RTy Γ
    rdᵀ  : A ⟶ᵀ* nfᵀ
    nrmᵀ : IsNormalᵀ nfᵀ
open WNᵀ

infixr 5 _◁_
_◁_ : {Γ : Cx} {A B : RTy Γ} → A ⟶ᵀ* B → WNᵀ B → WNᵀ A
p ◁ mkWNᵀ C q n = mkWNᵀ C (⟶ᵀ*-trans p q) n

private
  nrmΠ : {Γ : Cx} {A : RTy Γ} {B : RTy (Γ ∙)} → IsNormalᵀ A → IsNormalᵀ B → IsNormalᵀ (Π A B)
  nrmΠ nA nB (ξ-Πˡ q) = nA q
  nrmΠ nA nB (ξ-Πʳ q) = nB q

  nrmΣ : {Γ : Cx} {A : RTy Γ} {B : RTy (Γ ∙)} → IsNormalᵀ A → IsNormalᵀ B → IsNormalᵀ (Σ' A B)
  nrmΣ nA nB (ξ-Σˡ q) = nA q
  nrmΣ nA nB (ξ-Σʳ q) = nB q

  -- a weakened term applied to the fresh variable, at the codomain
  appvz : {Γ : Ctx} {F : RTy ⌊ Γ ⌋} {G : RTy (⌊ Γ ⌋ ∙)} {h : RTm ⌊ Γ ⌋} →
          Γ ⊢ h ∷ Π F G → (Γ ▹ F) ⊢ app (renTm vs h) (var vz) ∷ G
  appvz {G = G} dh = ⊢-cast (wk-app-vz G) (⊢app (⊢wk dh) (⊢var here))

------------------------------------------------------------------------
-- 1. ★ Decoding a NORMAL code, and `Hom` at a NORMAL ambient.
--
-- ⚠ WHY TWO `homNF`s.  Decoding `⌜Hom⌝ c a b` needs `Hom` at the DECODED
--   `El c`, and `homNF` at `U` needs to decode its endpoints — a cycle
--   `elNF → homNF → elNF` that Agda cannot see is harmless.  It IS
--   harmless: there is no code for `U`, so a decoded type never has `U`
--   along its Π-codomain spine (`NoU`), and `Hom` at such an ambient never
--   decodes anything.  `elNF` RETURNS that fact and calls the `U`-free
--   `homNF⁰`; only the general `homNF` (reached from `normTy`) decodes.
--   ⇒ the call graph is acyclic and every recursion is structural.
------------------------------------------------------------------------

data NoU {Γ : Cx} : RTy Γ → Set where
  nu-base : NoU base
  nu-Π    : {F : RTy Γ} {G : RTy (Γ ∙)} → NoU G → NoU (Π F G)
  nu-Σ    : {F : RTy Γ} {G : RTy (Γ ∙)} → NoU (Σ' F G)
  nu-El   : {c : RTm Γ} → NoU (El c)
  nu-Hom  : {A : RTy Γ} {t u : RTm Γ} → NoU (Hom A t u)
  nu-Unit : NoU Unit
  nu-Nat  : NoU Nat
  nu-Id   : {A : RTy Γ} {t u : RTm Γ} → NoU (Id A t u)
  nu-IMu  : {I D i : RTm Γ} → NoU (IMu I D i)
  nu-Desc : {I : RTm Γ} → NoU (Desc I)
  nu-DIh  : {D C p : RTm Γ} {M : RTy ((Γ ∙) ∙)} → NoU (DIh D M C p)
  nu-Fin  : {n : ℕ} → NoU (Fin n)

-- a normal form that is moreover `U`-free
record WNᵁ {Γ : Cx} (A : RTy Γ) : Set where
  constructor mkWNᵁ
  field
    nfᵁ  : RTy Γ
    rdᵁ  : A ⟶ᵀ* nfᵁ
    nrmᵁ : IsNormalᵀ nfᵁ
    nou  : NoU nfᵁ

forgetU : {Γ : Cx} {A : RTy Γ} → WNᵁ A → WNᵀ A
forgetU (mkWNᵁ B r n _) = mkWNᵀ B r n

infixr 5 _◁ᵁ_
_◁ᵁ_ : {Γ : Cx} {A B : RTy Γ} → A ⟶ᵀ* B → WNᵁ B → WNᵁ A
p ◁ᵁ mkWNᵁ C q n u = mkWNᵁ C (⟶ᵀ*-trans p q) n u

homNF⁰ : {Γ : Ctx} → ⊢ctx Γ → (A : RTy ⌊ Γ ⌋) → Γ ⊢ty A → IsNormalᵀ A → NoU A →
         (t u : RTm ⌊ Γ ⌋) → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → IsNormal t → IsNormal u →
         WNᵁ (Hom A t u)
elNF : {Γ : Ctx} → ⊢ctx Γ → (c : RTm ⌊ Γ ⌋) → Γ ⊢ c ∷ U → IsNormal c → WNᵁ (El c)
homNF : {Γ : Ctx} → ⊢ctx Γ → (A : RTy ⌊ Γ ⌋) → Γ ⊢ty A → IsNormalᵀ A →
        (t u : RTm ⌊ Γ ⌋) → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → IsNormal t → IsNormal u →
        WNᵀ (Hom A t u)

elNF wΓ ⌜base⌝ dc nc = mkWNᵁ base (stepᵀ El-⌜base⌝ doneᵀ) (λ ()) nu-base
elNF wΓ (⌜Π⌝ c d) dc nc =
  let (dc₁ , (dd₁ , _)) = gen-⌜Π⌝ dc
      mkWNᵁ A₁ r₁ n₁ _  = elNF wΓ c dc₁ (λ q → nc (ξ-⌜Π⌝ˡ q))
      mkWNᵁ B₁ r₂ n₂ u₂ = elNF (c-▹ wΓ (ty-El dc₁)) d dd₁ (λ q → nc (ξ-⌜Π⌝ʳ q))
  in  mkWNᵁ (Π A₁ B₁) (stepᵀ (El-⌜Π⌝ c d) (⟶ᵀ*-trans (⟶ᵀ*-Πˡ r₁) (⟶ᵀ*-Πʳ r₂))) (nrmΠ n₁ n₂) (nu-Π u₂)
elNF wΓ (⌜Σ⌝ c d) dc nc =
  let (dc₁ , (dd₁ , _)) = gen-⌜Σ⌝ dc
      mkWNᵁ A₁ r₁ n₁ _ = elNF wΓ c dc₁ (λ q → nc (ξ-⌜Σ⌝ˡ q))
      mkWNᵁ B₁ r₂ n₂ _ = elNF (c-▹ wΓ (ty-El dc₁)) d dd₁ (λ q → nc (ξ-⌜Σ⌝ʳ q))
  in  mkWNᵁ (Σ' A₁ B₁) (stepᵀ (El-⌜Σ⌝ c d) (⟶ᵀ*-trans (⟶ᵀ*-Σˡ r₁) (⟶ᵀ*-Σʳ r₂))) (nrmΣ n₁ n₂) nu-Σ
elNF wΓ (⌜Hom⌝ c a b) dc nc =
  let (dc₁ , (da , (db , _))) = gen-⌜Hom⌝ dc
      mkWNᵁ A₁ r₁ n₁ u₁ = elNF wΓ c dc₁ (λ q → nc (ξ-⌜Hom⌝ᶜ q))
      k = red→≅ᵀ r₁
  in  stepᵀ (El-⌜Hom⌝ c a b) (⟶ᵀ*-Homᵀ r₁)
        ◁ᵁ homNF⁰ wΓ A₁ (srᵀ* (ty-El dc₁) r₁) n₁ u₁ a b (⊢conv da k) (⊢conv db k)
                (λ q → nc (ξ-⌜Hom⌝ˡ q)) (λ q → nc (ξ-⌜Hom⌝ʳ q))
elNF wΓ (⌜Id⌝ c a b) dc nc =
  let (dc₁ , _) = gen-⌜Id⌝ dc
      mkWNᵁ A₁ r₁ n₁ _ = elNF wΓ c dc₁ (λ q → nc (ξ-⌜Id⌝ᶜ q))
  in  mkWNᵁ (Id A₁ a b) (stepᵀ (El-⌜Id⌝ c a b) (⟶ᵀ*-Idᵀ r₁))
        (λ { (ξ-Idᵀ q) → n₁ q ; (ξ-Idˡ q) → nc (ξ-⌜Id⌝ˡ q) ; (ξ-Idʳ q) → nc (ξ-⌜Id⌝ʳ q) }) nu-Id
elNF wΓ ⌜Nat⌝ dc nc  = mkWNᵁ Nat (stepᵀ El-⌜Nat⌝ doneᵀ) (λ ()) nu-Nat
elNF wΓ ⌜Unit⌝ dc nc = mkWNᵁ Unit (stepᵀ El-⌜Unit⌝ doneᵀ) (λ ()) nu-Unit
elNF wΓ (⌜IMu⌝ I D i) dc nc =
  mkWNᵁ (IMu I D i) (stepᵀ El-⌜IMu⌝ doneᵀ)
    (λ { (ξ-IMuᴵ q) → nc (ξ-⌜IMu⌝ᴵ q) ; (ξ-IMuᴰ q) → nc (ξ-⌜IMu⌝ᴰ q) ; (ξ-IMuⁱ q) → nc (ξ-⌜IMu⌝ⁱ q) })
    nu-IMu
elNF wΓ (⌜Fin⌝ n) dc nc = mkWNᵁ (Fin n) (stepᵀ El-⌜Fin⌝ doneᵀ) (λ ()) nu-Fin
-- every other head: `El c` is stuck, and Agda refutes each decode rule by
-- index mismatch.
elNF wΓ c@(var _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(lam _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(app _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(pair _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(absurd _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(ordtr _ _ _ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(fst _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(snd _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(hrefl _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(tr _ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(ap _ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(idrefl _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(jsub _ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@unit dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@nzero dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(nsuc _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(natrec _ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(con _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(ielim _ _ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(dι _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(dσ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(dρ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(dpay _ _ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(dih _ _ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@fzero dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(fsuc _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(fcase _ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(fcase0 _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(psplit _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El

-- the U-free twin: the same clauses with `NoU` threaded and NO `U` clause —
-- `NoU` has no `U` row, so Agda knows that case is impossible.
-- ★ the pointwise family: recurse into the codomain `G`, a strict subterm
--   of the NORMAL ambient; the created applications go through `wnorm`.
homNF⁰ wΓ (Π F G) (ty-Π dF dG) nA (nu-Π uG) t u dt du nt nu =
  let wΓ' = c-▹ wΓ dF
      mkWN t' rt nt' _ = wnorm wΓ' (appvz dt)
      mkWN u' ru nu' _ = wnorm wΓ' (appvz du)
      mkWNᵁ H r n uH = homNF⁰ wΓ' G dG (λ q → nA (ξ-Πʳ q)) uG t' u'
                      (sr* (appvz dt) rt) (sr* (appvz du) ru) nt' nu'
  in  mkWNᵁ (Π F H)
        (stepᵀ (Hom-Π F G t u)
          (⟶ᵀ*-Πʳ (⟶ᵀ*-trans (⟶ᵀ*-Homˡ rt) (⟶ᵀ*-trans (⟶ᵀ*-Homʳ ru) r))))
        (nrmΠ (λ q → nA (ξ-Πˡ q)) n) (nu-Π uH)
-- the computing order at `Nat`
homNF⁰ wΓ Nat dA nA uA nzero u dt du nt nu =
  mkWNᵁ Unit (stepᵀ (Hom-Nat-z u) doneᵀ) (λ ()) nu-Unit
homNF⁰ wΓ Nat dA nA uA (nsuc m) nzero dt du nt nu =
  mkWNᵁ base (stepᵀ (Hom-Nat-sz m) doneᵀ) (λ ()) nu-base
homNF⁰ wΓ Nat dA nA uA (nsuc m) (nsuc k) dt du nt nu =
  let (dm , _) = gen-nsuc dt
      (dk , _) = gen-nsuc du
  in  stepᵀ (Hom-Nat-ss m k) doneᵀ
        ◁ᵁ homNF⁰ wΓ Nat dA nA uA m k dm dk (λ q → nt (ξ-nsuc q)) (λ q → nu (ξ-nsuc q))
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(var _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(lam _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(app _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(pair _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(absurd _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(ordtr _ _ _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(fst _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(snd _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@⌜base⌝ dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(⌜Π⌝ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(⌜Σ⌝ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(⌜Hom⌝ _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(hrefl _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(tr _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(ap _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(⌜Id⌝ _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(idrefl _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(jsub _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@unit dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(natrec _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(con _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(ielim _ _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(dι _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(dσ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(dρ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(dpay _ _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(dih _ _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@fzero dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(fsuc _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(fcase _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(fcase0 _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(psplit _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@⌜Nat⌝ dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(⌜IMu⌝ _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(⌜Fin⌝ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@⌜Unit⌝ dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(var _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(lam _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(app _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(pair _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(absurd _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(ordtr _ _ _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(fst _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(snd _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@⌜base⌝ u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(⌜Π⌝ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(⌜Σ⌝ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(⌜Hom⌝ _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(hrefl _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(tr _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(ap _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(⌜Id⌝ _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(idrefl _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(jsub _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@unit u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(natrec _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(con _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(ielim _ _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(dι _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(dσ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(dρ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(dpay _ _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(dih _ _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@fzero u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(fsuc _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(fcase _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(fcase0 _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(psplit _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@⌜Nat⌝ u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(⌜IMu⌝ _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(⌜Fin⌝ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@⌜Unit⌝ u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
-- every other normal ambient: `Hom` is stuck
homNF⁰ wΓ A@base dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(Σ' _ _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(El _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(Hom _ _ _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@Unit dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(Id _ _ _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(IMu _ _ _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(Desc _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(DIh _ _ _ _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(Fin _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom


-- directed univalence: `Hom U c d ⟶ᵀ Π (El c) (El d↑)`
homNF wΓ U dA nA t u dt du nt nu =
  let mkWNᵀ A₁ r₁ n₁ = forgetU (elNF wΓ t dt nt)
      wΓ' = c-▹ wΓ (ty-El dt)
      mkWN u' ru nu' _ = wnorm wΓ' (⊢wk du)
      mkWNᵀ B₁ r₂ n₂ = forgetU (elNF wΓ' u' (sr* (⊢wk du) ru) nu')
  in  mkWNᵀ (Π A₁ B₁)
        (stepᵀ (Hom-U t u) (⟶ᵀ*-trans (⟶ᵀ*-Πˡ r₁) (⟶ᵀ*-Πʳ (⟶ᵀ*-trans (⟶ᵀ*-El ru) r₂))))
        (nrmΠ n₁ n₂)
-- ★ the pointwise family: recurse into the codomain `G`, a strict subterm
--   of the NORMAL ambient; the created applications go through `wnorm`.
homNF wΓ (Π F G) (ty-Π dF dG) nA t u dt du nt nu =
  let wΓ' = c-▹ wΓ dF
      mkWN t' rt nt' _ = wnorm wΓ' (appvz dt)
      mkWN u' ru nu' _ = wnorm wΓ' (appvz du)
      mkWNᵀ H r n = homNF wΓ' G dG (λ q → nA (ξ-Πʳ q)) t' u'
                      (sr* (appvz dt) rt) (sr* (appvz du) ru) nt' nu'
  in  mkWNᵀ (Π F H)
        (stepᵀ (Hom-Π F G t u)
          (⟶ᵀ*-Πʳ (⟶ᵀ*-trans (⟶ᵀ*-Homˡ rt) (⟶ᵀ*-trans (⟶ᵀ*-Homʳ ru) r))))
        (nrmΠ (λ q → nA (ξ-Πˡ q)) n)
-- the computing order at `Nat`
homNF wΓ Nat dA nA nzero u dt du nt nu =
  mkWNᵀ Unit (stepᵀ (Hom-Nat-z u) doneᵀ) (λ ())
homNF wΓ Nat dA nA (nsuc m) nzero dt du nt nu =
  mkWNᵀ base (stepᵀ (Hom-Nat-sz m) doneᵀ) (λ ())
homNF wΓ Nat dA nA (nsuc m) (nsuc k) dt du nt nu =
  let (dm , _) = gen-nsuc dt
      (dk , _) = gen-nsuc du
  in  stepᵀ (Hom-Nat-ss m k) doneᵀ
        ◁ homNF wΓ Nat dA nA m k dm dk (λ q → nt (ξ-nsuc q)) (λ q → nu (ξ-nsuc q))
homNF wΓ Nat dA nA (nsuc m) u@(var _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(lam _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(app _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(pair _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(absurd _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(ordtr _ _ _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(fst _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(snd _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@⌜base⌝ dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(⌜Π⌝ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(⌜Σ⌝ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(⌜Hom⌝ _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(hrefl _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(tr _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(ap _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(⌜Id⌝ _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(idrefl _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(jsub _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@unit dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(natrec _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(con _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(ielim _ _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(dι _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(dσ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(dρ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(dpay _ _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(dih _ _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@fzero dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(fsuc _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(fcase _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(fcase0 _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(psplit _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@⌜Nat⌝ dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(⌜IMu⌝ _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(⌜Fin⌝ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@⌜Unit⌝ dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(var _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(lam _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(app _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(pair _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(absurd _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(ordtr _ _ _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(fst _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(snd _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@⌜base⌝ u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(⌜Π⌝ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(⌜Σ⌝ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(⌜Hom⌝ _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(hrefl _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(tr _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(ap _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(⌜Id⌝ _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(idrefl _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(jsub _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@unit u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(natrec _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(con _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(ielim _ _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(dι _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(dσ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(dρ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(dpay _ _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(dih _ _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@fzero u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(fsuc _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(fcase _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(fcase0 _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(psplit _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@⌜Nat⌝ u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(⌜IMu⌝ _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(⌜Fin⌝ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@⌜Unit⌝ u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
-- every other normal ambient: `Hom` is stuck
homNF wΓ A@base dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(Σ' _ _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(El _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(Hom _ _ _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@Unit dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(Id _ _ _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(IMu _ _ _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(Desc _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(DIh _ _ _ _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(Fin _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })

------------------------------------------------------------------------
-- 2. ★ EVERY WELL-FORMED TYPE HAS A NORMAL FORM — at every well-typed
--    SUBSTITUTION INSTANCE.
--
-- ★★ WHY SUBSTITUTION-PARAMETRIC.  `DIh-ρ` puts the motive's INSTANCE
--   `iinst j (fst p) M` into the type, so normalising `DIh` normalises
--   the motive at substitutions the recursion creates.  Stating the
--   theorem for `subTy σ A` keeps the recursion on the formation
--   DERIVATION structural: the motive's derivation is a strict premise
--   of `ty-DIh`, whatever substitution it is used at.
-- ★★ WHY A WALK.  `DIh-σ` creates `app f (fst p)`, which no syntactic
--   measure sees shrink; `dihNF` recurses on the telescope's `Walk`
--   (`Fundamental.dih-walk`), generalised over a RENAMING so `DIh-ρ`'s
--   second component — the rest of the walk under the Σ binder — is the
--   same walk at a weakened scope.
------------------------------------------------------------------------

private
  Sub⊢-ren : {Γ Δ : Ctx} {ρ : Ren ⌊ Γ ⌋ ⌊ Δ ⌋} → Ren⊢ Γ Δ ρ → Sub⊢ Γ Δ ⟨ ρ ⟩ᵣ
  Sub⊢-ren {ρ = ρ} h {A = A} v = ⊢-cast (sym (subTy-var ρ A)) (⊢var (h v))

  Sub⊢-∘ : {Γ Δ Θ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {τ : Sub ⌊ Δ ⌋ ⌊ Θ ⌋} →
           Sub⊢ Γ Δ σ → Sub⊢ Δ Θ τ → Sub⊢ Γ Θ (τ ∘ₛ σ)
  Sub⊢-∘ h₁ h₂ {A = A} v = ⊢-cast (subTy-subTy A) (sub-lemma (h₁ v) h₂)

  Sub⊢-id : {Γ : Ctx} → Sub⊢ Γ Γ idₛ
  Sub⊢-id {A = A} v = ⊢-cast (sym (subTy-id A)) (⊢var v)

  idR : {Γ : Cx} → Ren Γ Γ
  idR x = x

  renTy-idR : {Γ : Cx} (A : RTy Γ) → renTy idR A ≡ A
  renTy-idR A = trans (sym (subTy-var idR A)) (subTy-id A)

  Ren⊢-id : {Γ : Ctx} → Ren⊢ Γ Γ idR
  Ren⊢-id {A = A} v = ∋-cast (sym (renTy-idR A)) v

  -- a `DIh` whose telescope is stuck-keyed (and whose slots are normal) is
  --   normal: `dstk?` refutes the three head rules.
  dih-stuck : {Γ : Cx} {D C p : RTm Γ} {M : RTy ((Γ ∙) ∙)} {B : RTy Γ} →
              DIh D M C p ⟶ᵀ B → dstk? C ≡ trueᵇ →
              IsNormal D → IsNormalᵀ M → IsNormal C → IsNormal p → ⊥
  dih-stuck (ξ-DIhᴰ q) k nD nM nC np = nD q
  dih-stuck (ξ-DIhᴹ q) k nD nM nC np = nM q
  dih-stuck (ξ-DIhᶜ q) k nD nM nC np = nC q
  dih-stuck (ξ-DIhᵖ q) k nD nM nC np = np q
  dih-stuck (DIh-ι _ _ _ _)   () nD nM nC np
  dih-stuck (DIh-σ _ _ _ _ _) () nD nM nC np
  dih-stuck (DIh-ρ _ _ _ _ _) () nD nM nC np

------------------------------------------------------------------------
-- 2a. The hypotheses' type, by recursion on the walk.  `motNF` is the
--     motive's normaliser at any well-typed substitution (a closure over
--     `normTyS`'s recursive call on the motive's derivation).
------------------------------------------------------------------------

module _ {Θ : Ctx} {I D i : RTm ⌊ Θ ⌋} {M : RTy ((⌊ Θ ⌋ ∙) ∙)}
         (dI : Θ ⊢ I ∷ U) (dD : Θ ⊢ D ∷ Desc I) (dM : motCtx Θ I D ⊢ty M)
         (motNF : {Ξ : Ctx} {τ : Sub ((⌊ Θ ⌋ ∙) ∙) ⌊ Ξ ⌋} →
                  ⊢ctx Ξ → Sub⊢ (motCtx Θ I D) Ξ τ → WNᵀ (subTy τ M))
         where

  dihNF : {C p : RTm ⌊ Θ ⌋} → Walk C p → Θ ⊢ C ∷ Desc I → Θ ⊢ p ∷ El (dpay I D C i) →
          {Ξ : Ctx} {ρ : Ren ⌊ Θ ⌋ ⌊ Ξ ⌋} → ⊢ctx Ξ → Ren⊢ Θ Ξ ρ →
          WNᵀ (renTy ρ (DIh D M C p))
  -- a stuck telescope: normalise every slot; the motive at the renaming
  dihNF {C = C} (w-ne n) dC dp {ρ = ρ} wΞ hρ =
    let mkWN D' rD nD _ = wnorm wΞ (ren-lemma dD hρ)
        mkWN C' rC nC _ = wnorm wΞ (ren-lemma dC hρ)
        mkWN p' rp np _ = wnorm wΞ (ren-lemma dp hρ)
        wmot = c-▹ (c-▹ wΞ (ren-ty (ty-El dI) hρ))
                   (ren-ty (ty-IMu (⊢wk dI) (⊢wk dD) (⊢var here)) (Ren⊢-ext hρ))
        mkWNᵀ M' rM nM = subst WNᵀ (subTy-var (extR (extR ρ)) M)
                                (motNF wmot (Sub⊢-ren (Ren⊢-ext (Ren⊢-ext hρ))))
        key = dstk?-red* rC (trans (dstk?-ren ρ C) (sne→dstk n))
    in  mkWNᵀ (DIh D' M' C' p')
          (⟶ᵀ*-trans (⟶ᵀ*-DIhᴰ rD) (⟶ᵀ*-trans (⟶ᵀ*-DIhᴹ rM)
            (⟶ᵀ*-trans (⟶ᵀ*-DIhᶜ rC) (⟶ᵀ*-DIhᵖ rp))))
          (λ q → dih-stuck q key nD nM nC np)
  dihNF (w-exp r k) dC dp {ρ = ρ} wΞ hρ =
    stepᵀ (⟶ᵀ-ren ρ (ξ-DIhᶜ (snr→⟶ r))) doneᵀ
      ◁ dihNF k (sr dC (snr→⟶ r)) (⊢conv dp (credᵀ (ξ-El (ξ-dpayᶜ (snr→⟶ r))))) wΞ hρ
  dihNF w-ι dC dp {ρ = ρ} wΞ hρ =
    mkWNᵀ Unit (stepᵀ (⟶ᵀ-ren ρ (DIh-ι _ _ _ _)) doneᵀ) (λ ())
  dihNF (w-σ k) dC dp {ρ = ρ} wΞ hρ with dσ-step dC dp
  ... | dC' , dsnd = stepᵀ (⟶ᵀ-ren ρ (DIh-σ _ _ _ _ _)) doneᵀ ◁ dihNF k dC' dsnd wΞ hρ
  -- ★ the recursive field: the motive's instance, and the rest of the
  --   walk at the scope extended by it (a renaming, `vs ∘ᵣ ρ`).
  dihNF (w-ρ {j = j} {C = C₁} {p = p} k) dC dp {Ξ = Ξ} {ρ = ρ} wΞ hρ with dρ-step dC dp
  ... | dj , (dC₁ , (dfst , dsnd)) =
    stepᵀ (⟶ᵀ-ren ρ (DIh-ρ D M j C₁ p)) doneᵀ
      ◁ mkWNᵀ (Σ' F' B') (⟶ᵀ*-trans (⟶ᵀ*-Σˡ rF) (⟶ᵀ*-Σʳ rB)) (nrmΣ nF nB)
    where
      dfst' : Θ ⊢ fst p ∷ subTy (single j) (IMu (renTm vs I) (renTm vs D) (var vz))
      dfst' = ⊢-cast (cong₂ (λ a b → IMu a b j) (sym (wk-cancel-tm j I)) (sym (wk-cancel-tm j D))) dfst
      hτ : Sub⊢ (motCtx Θ I D) Ξ (⟨ ρ ⟩ᵣ ∘ₛ (single (fst p) ∘ₛ extS (single j)))
      hτ = Sub⊢-∘ (Sub⊢-∘ (Sub⊢-ext (⊢single dj)) (⊢single dfst')) (Sub⊢-ren hρ)
      eqF : subTy (⟨ ρ ⟩ᵣ ∘ₛ (single (fst p) ∘ₛ extS (single j))) M ≡ renTy ρ (iinst j (fst p) M)
      eqF = trans (sym (subTy-subTy {τ = ⟨ ρ ⟩ᵣ} {σ = single (fst p) ∘ₛ extS (single j)} M))
                  (trans (cong (subTy ⟨ ρ ⟩ᵣ)
                               (sym (subTy-subTy {τ = single (fst p)} {σ = extS (single j)} M)))
                         (subTy-var ρ (iinst j (fst p) M)))
      nfF = subst WNᵀ eqF (motNF wΞ hτ)
      F' = WNᵀ.nfᵀ nfF
      rF = WNᵀ.rdᵀ nfF
      nF = WNᵀ.nrmᵀ nfF
      wΞF : ⊢ctx (Ξ ▹ renTy ρ (iinst j (fst p) M))
      wΞF = c-▹ wΞ (ren-ty (iinst-wf M j (fst p) dj dfst dM) hρ)
      hρ' : Ren⊢ Θ (Ξ ▹ renTy ρ (iinst j (fst p) M)) (vs ∘ᵣ ρ)
      hρ' {A = A} v = ∋-cast (renTy-renTy A) (there (hρ v))
      nfB = subst WNᵀ (sym (renTy-renTy {ρ' = extR ρ} {ρ = vs} (DIh D M C₁ (snd p))))
                  (dihNF k dC₁ dsnd wΞF hρ')
      B' = WNᵀ.nfᵀ nfB
      rB = WNᵀ.rdᵀ nfB
      nB = WNᵀ.nrmᵀ nfB

normTyS : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {A : RTy ⌊ Γ ⌋} →
          ⊢ctx Δ → Γ ⊢ty A → Sub⊢ Γ Δ σ → WNᵀ (subTy σ A)
normTyS wΔ ty-base h = mkWNᵀ base doneᵀ (λ ())
normTyS wΔ ty-U    h = mkWNᵀ U doneᵀ (λ ())
normTyS wΔ ty-Unit h = mkWNᵀ Unit doneᵀ (λ ())
normTyS wΔ ty-Nat  h = mkWNᵀ Nat doneᵀ (λ ())
normTyS wΔ ty-Fin  h = mkWNᵀ (Fin _) doneᵀ (λ ())
normTyS wΔ (ty-IMu dI dD di) h =
  let mkWN I' rI nI _ = wnorm wΔ (sub-lemma dI h)
      mkWN D' rD nD _ = wnorm wΔ (sub-lemma dD h)
      mkWN i' ri ni _ = wnorm wΔ (sub-lemma di h)
  in  mkWNᵀ (IMu I' D' i') (⟶ᵀ*-trans (⟶ᵀ*-IMuᴵ rI) (⟶ᵀ*-trans (⟶ᵀ*-IMuᴰ rD) (⟶ᵀ*-IMu ri)))
        (λ { (ξ-IMuᴵ q) → nI q ; (ξ-IMuᴰ q) → nD q ; (ξ-IMuⁱ q) → ni q })
normTyS wΔ (ty-Desc dI) h =
  let mkWN I' rI nI _ = wnorm wΔ (sub-lemma dI h)
  in  mkWNᵀ (Desc I') (⟶ᵀ*-Desc rI) (λ { (ξ-Desc q) → nI q })
normTyS wΔ (ty-Π dA dB) h =
  let mkWNᵀ A' r₁ n₁ = normTyS wΔ dA h
      mkWNᵀ B' r₂ n₂ = normTyS (c-▹ wΔ (sub-ty dA h)) dB (Sub⊢-ext h)
  in  mkWNᵀ (Π A' B') (⟶ᵀ*-trans (⟶ᵀ*-Πˡ r₁) (⟶ᵀ*-Πʳ r₂)) (nrmΠ n₁ n₂)
normTyS wΔ (ty-Σ dA dB) h =
  let mkWNᵀ A' r₁ n₁ = normTyS wΔ dA h
      mkWNᵀ B' r₂ n₂ = normTyS (c-▹ wΔ (sub-ty dA h)) dB (Sub⊢-ext h)
  in  mkWNᵀ (Σ' A' B') (⟶ᵀ*-trans (⟶ᵀ*-Σˡ r₁) (⟶ᵀ*-Σʳ r₂)) (nrmΣ n₁ n₂)
normTyS wΔ (ty-El dc) h =
  let dc' = sub-lemma dc h
      mkWN c' r nc _ = wnorm wΔ dc'
  in  ⟶ᵀ*-El r ◁ forgetU (elNF wΔ c' (sr* dc' r) nc)
normTyS wΔ (ty-Id dA dt du) h =
  let mkWNᵀ A' rA nA = normTyS wΔ dA h
      mkWN t' rt nt _ = wnorm wΔ (sub-lemma dt h)
      mkWN u' ru nu _ = wnorm wΔ (sub-lemma du h)
  in  mkWNᵀ (Id A' t' u') (⟶ᵀ*-trans (⟶ᵀ*-Idᵀ rA) (⟶ᵀ*-trans (⟶ᵀ*-Idˡ rt) (⟶ᵀ*-Idʳ ru)))
        (λ { (ξ-Idᵀ q) → nA q ; (ξ-Idˡ q) → nt q ; (ξ-Idʳ q) → nu q })
normTyS wΔ (ty-Hom dA dt du) h =
  let dA' = sub-ty dA h
      mkWNᵀ A' rA nA = normTyS wΔ dA h
      k = red→≅ᵀ rA
      dt' = ⊢conv (sub-lemma dt h) k
      du' = ⊢conv (sub-lemma du h) k
      mkWN t' rt nt _ = wnorm wΔ dt'
      mkWN u' ru nu _ = wnorm wΔ du'
  in  ⟶ᵀ*-trans (⟶ᵀ*-Homᵀ rA) (⟶ᵀ*-trans (⟶ᵀ*-Homˡ rt) (⟶ᵀ*-Homʳ ru))
        ◁ homNF wΔ A' (srᵀ* dA' rA) nA t' u' (sr* dt' rt) (sr* du' ru) nt nu
-- ★ the hypotheses: the walk, at the identity renaming.
normTyS {Δ = Δ} {σ = σ} wΔ (ty-DIh {I = I} {D = D} {M = M} dI dD dM dC di dp) h =
  subst WNᵀ (renTy-idR _)
    (dihNF dI' dD' dM' motNF (dih-walk wΔ dD' dC' dp') dC' dp' wΔ Ren⊢-id)
  where
    dI' = sub-lemma dI h
    dD' = sub-lemma dD h
    dC' = sub-lemma dC h
    dp' = sub-lemma dp h
    ext-eq = cong₂ (λ a b → IMu a b (var vz)) (wk-sub σ I) (wk-sub σ D)
    hext : Sub⊢ (motCtx _ I D) (motCtx Δ (subTm σ I) (subTm σ D)) (extS (extS σ))
    hext = subst (λ A → Sub⊢ (motCtx _ I D) ((Δ ▹ El (subTm σ I)) ▹ A) (extS (extS σ)))
                 ext-eq (Sub⊢-ext (Sub⊢-ext h))
    dM' : motCtx Δ (subTm σ I) (subTm σ D) ⊢ty subTy (extS (extS σ)) M
    dM' = sub-ty dM hext
    motNF : {Ξ : Ctx} {τ : Sub ((⌊ Δ ⌋ ∙) ∙) ⌊ Ξ ⌋} →
            ⊢ctx Ξ → Sub⊢ (motCtx Δ (subTm σ I) (subTm σ D)) Ξ τ →
            WNᵀ (subTy τ (subTy (extS (extS σ)) M))
    motNF wΞ hτ = subst WNᵀ (sym (subTy-subTy M)) (normTyS wΞ dM (Sub⊢-∘ hext hτ))

normTy : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} → ⊢ctx Γ → Γ ⊢ty A → WNᵀ A
normTy {A = A} wΓ dA = subst WNᵀ (subTy-id A) (normTyS wΓ dA Sub⊢-id)

------------------------------------------------------------------------
-- 3. ★ TYPE CONVERSION IS DECIDABLE (for well-formed types).
------------------------------------------------------------------------

normalᵀ-⟶* : {Γ : Cx} {A B : RTy Γ} → IsNormalᵀ A → A ⟶ᵀ* B → A ≡ B
normalᵀ-⟶* n doneᵀ       = refl
normalᵀ-⟶* n (stepᵀ r _) with n r
... | ()

-- convertible normal types are EQUAL — Church–Rosser for types
convNormal≡ : {Γ : Cx} {A B : RTy Γ} → A ≅ᵀ B → IsNormalᵀ A → IsNormalᵀ B → A ≡ B
convNormal≡ c nA nB with church-rosserᵀ c
... | W , (aw , bw) = trans (normalᵀ-⟶* nA aw) (sym (normalᵀ-⟶* nB bw))

decConvᵀ : {Γ : Ctx} {A B : RTy ⌊ Γ ⌋} → ⊢ctx Γ → Γ ⊢ty A → Γ ⊢ty B → Dec (A ≅ᵀ B)
decConvᵀ wΓ dA dB with normTy wΓ dA | normTy wΓ dB
... | mkWNᵀ A' rA nA | mkWNᵀ B' rB nB with A' ≟Ty B'
...   | yes refl = yes (ctrnᵀ (red→≅ᵀ rA) (csymᵀ (red→≅ᵀ rB)))
...   | no  ne   =
        no (λ c → ne (convNormal≡ (ctrnᵀ (csymᵀ (red→≅ᵀ rA)) (ctrnᵀ c (red→≅ᵀ rB))) nA nB))

------------------------------------------------------------------------
-- 4. NON-VACUITY — it RUNS, both ways, through decoding AND `Hom-Π`.
------------------------------------------------------------------------

private
  isYes : {P : Set} → Dec P → Bool
  isYes (yes _) = true
  isYes (no  _) = false

  NN : {Γ : Cx} → RTy Γ
  NN = Π Nat Nat

  -- a code decodes: El (⌜Π⌝ ⌜Nat⌝ ⌜Nat⌝) ≅ Π Nat Nat
  run-decode : isYes (decConvᵀ c-◇ (ty-El (⊢⌜Π⌝ ⊢⌜Nat⌝ ⊢⌜Nat⌝)) (ty-Π ty-Nat ty-Nat)) ≡ true
  run-decode = refl

  -- directed univalence: Hom U ⌜Nat⌝ ⌜Nat⌝ ≅ Π Nat Nat
  run-homU : isYes (decConvᵀ c-◇ (ty-Hom ty-U ⊢⌜Nat⌝ ⊢⌜Nat⌝) (ty-Π ty-Nat ty-Nat)) ≡ true
  run-homU = refl

  -- rejection
  run-no : isYes (decConvᵀ c-◇ ty-Nat ty-Unit) ≡ false
  run-no = refl

  -- ★ `Hom-Π`: a hom between functions IS the pointwise family
  Γf : Ctx
  Γf = ◇ ▹ NN

  wΓf : ⊢ctx Γf
  wΓf = c-▹ c-◇ (ty-Π ty-Nat ty-Nat)

  f : RTm ⌊ Γf ⌋
  f = var vz

  fx : RTm (⌊ Γf ⌋ ∙)
  fx = app (var (vs vz)) (var vz)

  run-homΠ : isYes (decConvᵀ wΓf
                      (ty-Hom (ty-Π ty-Nat ty-Nat) (⊢var here) (⊢var here))
                      (ty-Π ty-Nat (ty-Hom ty-Nat (⊢app (⊢var (there here)) (⊢var here))
                                                  (⊢app (⊢var (there here)) (⊢var here)))))
             ≡ true
  run-homΠ = refl
