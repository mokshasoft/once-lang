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
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; Σ; _,_; ¬_ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ
        ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ; ⟶ᵀ*-Homᵀ; ⟶ᵀ*-Homˡ; ⟶ᵀ*-Homʳ
        ; ⟶ᵀ*-Idᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; ⟶ᵀ*-IMu; red→≅ᵀ )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( sr*; gen-⌜Π⌝; gen-⌜Σ⌝; gen-⌜Hom⌝; gen-⌜Id⌝; gen-nsuc; ⊢wk; ⊢-cast )
open import DirectedHoTT.Metatheory.Validity using ( srᵀ*; wk-app-vz )
open import DirectedHoTT.Metatheory.LogicalRelation using ( IsNormal; WN; mkWN )
open import DirectedHoTT.Metatheory.Fundamental using ( wnorm )
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
  nu-Mu   : {D : Desc} → NoU (Mu D)
  nu-IMu  : {D : IDesc} {I : RTy ε} {i : RTm Γ} → NoU (IMu D I i)

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
elNF wΓ (⌜Mu⌝ D) dc nc = mkWNᵁ (Mu D) (stepᵀ El-⌜Mu⌝ doneᵀ) (λ ()) nu-Mu
elNF wΓ (⌜IMu⌝ D I i) dc nc =
  mkWNᵁ (IMu D I i) (stepᵀ El-⌜IMu⌝ doneᵀ) (λ { (ξ-IMu q) → nc (ξ-⌜IMu⌝ q) }) nu-IMu
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
elNF wΓ c@(con _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(elim _ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(icon _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El
elNF wΓ c@(ielim _ _ _ _) dc nc = mkWNᵁ (El c) doneᵀ (λ { (ξ-El q) → nc q }) nu-El

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
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(con _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(elim _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(icon _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(ielim _ _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@⌜Nat⌝ dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(⌜Mu⌝ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA (nsuc m) u@(⌜IMu⌝ _ _ _) dt du nt nu = mkWNᵁ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
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
homNF⁰ wΓ Nat dA nA uA t@(con _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(elim _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(icon _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(ielim _ _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@⌜Nat⌝ u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(⌜Mu⌝ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@(⌜IMu⌝ _ _ _) u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ Nat dA nA uA t@⌜Unit⌝ u dt du nt nu = mkWNᵁ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
-- every other normal ambient: `Hom` is stuck
homNF⁰ wΓ A@base dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(Σ' _ _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(El _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(Hom _ _ _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@Unit dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(Id _ _ _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(Mu _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom
homNF⁰ wΓ A@(IMu _ _ _) dA nA uA t u dt du nt nu = mkWNᵁ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q }) nu-Hom


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
homNF wΓ Nat dA nA (nsuc m) u@(con _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(elim _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(icon _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(ielim _ _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@⌜Nat⌝ dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(⌜Mu⌝ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA (nsuc m) u@(⌜IMu⌝ _ _ _) dt du nt nu = mkWNᵀ (Hom Nat (nsuc m) u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
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
homNF wΓ Nat dA nA t@(con _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(elim _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(icon _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(ielim _ _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@⌜Nat⌝ u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(⌜Mu⌝ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@(⌜IMu⌝ _ _ _) u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ Nat dA nA t@⌜Unit⌝ u dt du nt nu = mkWNᵀ (Hom Nat t u) doneᵀ (λ { (ξ-Homᵀ ()) ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
-- every other normal ambient: `Hom` is stuck
homNF wΓ A@base dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(Σ' _ _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(El _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(Hom _ _ _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@Unit dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(Id _ _ _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(Mu _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })
homNF wΓ A@(IMu _ _ _) dA nA t u dt du nt nu = mkWNᵀ (Hom A t u) doneᵀ (λ { (ξ-Homᵀ q) → nA q ; (ξ-Homˡ q) → nt q ; (ξ-Homʳ q) → nu q })

------------------------------------------------------------------------
-- 2. ★ EVERY WELL-FORMED TYPE HAS A NORMAL FORM.
------------------------------------------------------------------------

normTy : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} → ⊢ctx Γ → Γ ⊢ty A → WNᵀ A
normTy wΓ ty-base = mkWNᵀ base doneᵀ (λ ())
normTy wΓ ty-U    = mkWNᵀ U doneᵀ (λ ())
normTy wΓ ty-Unit = mkWNᵀ Unit doneᵀ (λ ())
normTy wΓ ty-Nat  = mkWNᵀ Nat doneᵀ (λ ())
normTy wΓ (ty-Mu {D = D} w) = mkWNᵀ (Mu D) doneᵀ (λ ())
normTy wΓ (ty-IMu {D = D} {I = I} w di) =
  let mkWN i' r ni _ = wnorm wΓ di
  in  mkWNᵀ (IMu D I i') (⟶ᵀ*-IMu r) (λ { (ξ-IMu q) → ni q })
normTy wΓ (ty-Π dA dB) =
  let mkWNᵀ A' r₁ n₁ = normTy wΓ dA
      mkWNᵀ B' r₂ n₂ = normTy (c-▹ wΓ dA) dB
  in  mkWNᵀ (Π A' B') (⟶ᵀ*-trans (⟶ᵀ*-Πˡ r₁) (⟶ᵀ*-Πʳ r₂)) (nrmΠ n₁ n₂)
normTy wΓ (ty-Σ dA dB) =
  let mkWNᵀ A' r₁ n₁ = normTy wΓ dA
      mkWNᵀ B' r₂ n₂ = normTy (c-▹ wΓ dA) dB
  in  mkWNᵀ (Σ' A' B') (⟶ᵀ*-trans (⟶ᵀ*-Σˡ r₁) (⟶ᵀ*-Σʳ r₂)) (nrmΣ n₁ n₂)
normTy wΓ (ty-El dc) =
  let mkWN c' r nc _ = wnorm wΓ dc
  in  ⟶ᵀ*-El r ◁ forgetU (elNF wΓ c' (sr* dc r) nc)
normTy wΓ (ty-Id dA dt du) =
  let mkWNᵀ A' rA nA = normTy wΓ dA
      mkWN t' rt nt _ = wnorm wΓ dt
      mkWN u' ru nu _ = wnorm wΓ du
  in  mkWNᵀ (Id A' t' u') (⟶ᵀ*-trans (⟶ᵀ*-Idᵀ rA) (⟶ᵀ*-trans (⟶ᵀ*-Idˡ rt) (⟶ᵀ*-Idʳ ru)))
        (λ { (ξ-Idᵀ q) → nA q ; (ξ-Idˡ q) → nt q ; (ξ-Idʳ q) → nu q })
normTy wΓ (ty-Hom dA dt du) =
  let mkWNᵀ A' rA nA = normTy wΓ dA
      k = red→≅ᵀ rA
      mkWN t' rt nt _ = wnorm wΓ (⊢conv dt k)
      mkWN u' ru nu _ = wnorm wΓ (⊢conv du k)
  in  ⟶ᵀ*-trans (⟶ᵀ*-Homᵀ rA) (⟶ᵀ*-trans (⟶ᵀ*-Homˡ rt) (⟶ᵀ*-Homʳ ru))
        ◁ homNF wΓ A' (srᵀ* dA rA) nA t' u'
                (sr* (⊢conv dt k) rt) (sr* (⊢conv du k) ru) nt nu

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
