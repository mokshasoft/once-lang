-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ LAZY CONVERSION, certified.  (PLAN-BIDI S7b)
--
-- `decConvFast` (Algorithm/Eval) compares FULL normal forms: deciding, but
-- it expands everything — a payload type at the quoted Knot signature
-- normalises to the whole 39-constructor cascade of `KD`.  This is the
-- lazy fast path the checker tries FIRST:
--
--   · syntactic equality;
--   · else both sides weak-head reduced (certified chains) and compared;
--   · else, at the same head, the fields compared recursively — the
--     result assembled by ONE generic congruence (`cong≅`: any one-hole
--     context with its ξ-rule).
--
-- It only ever answers `just` with a PROOF of conversion, or `nothing`
-- (then the full-normal-form procedure decides, both ways).  So it is
-- sound by construction and needs no completeness argument.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; _<ˢ?_ )
module DirectedHoTT.Algorithm.ConvLazy (𝒮 : KSig) where
open import normalizer.Syntax.Types using ( _≡_; refl; Σ; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Reduction 𝒮 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( _⟶ᵀ*_; doneᵀ; stepᵀ; red→≅ᵀ )
open import DirectedHoTT.Algorithm.Eval 𝒮 using ( head; headᵀ; Step; Stepᵀ )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no; _≟Tm_; _≟Ty_ )

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- 1. ONE generic congruence per sort of hole.
------------------------------------------------------------------------

cong≅ : (f : RTm Δ → RTm Γ) → (∀ {x y} → x ⟶ y → f x ⟶ f y) → {a b : RTm Δ} → a ≅ b → f a ≅ f b
cong≅ f ξ (cred r)   = cred (ξ r)
cong≅ f ξ crfl       = crfl
cong≅ f ξ (csym c)   = csym (cong≅ f ξ c)
cong≅ f ξ (ctrn c d) = ctrn (cong≅ f ξ c) (cong≅ f ξ d)

cong≅ᵗ : (f : RTm Δ → RTy Γ) → (∀ {x y} → x ⟶ y → f x ⟶ᵀ f y) → {a b : RTm Δ} → a ≅ b → f a ≅ᵀ f b
cong≅ᵗ f ξ (cred r)   = credᵀ (ξ r)
cong≅ᵗ f ξ crfl       = crflᵀ
cong≅ᵗ f ξ (csym c)   = csymᵀ (cong≅ᵗ f ξ c)
cong≅ᵗ f ξ (ctrn c d) = ctrnᵀ (cong≅ᵗ f ξ c) (cong≅ᵗ f ξ d)

cong≅ᵀ : (f : RTy Δ → RTy Γ) → (∀ {x y} → x ⟶ᵀ y → f x ⟶ᵀ f y) → {A B : RTy Δ} → A ≅ᵀ B → f A ≅ᵀ f B
cong≅ᵀ f ξ (credᵀ r)   = credᵀ (ξ r)
cong≅ᵀ f ξ crflᵀ       = crflᵀ
cong≅ᵀ f ξ (csymᵀ c)   = csymᵀ (cong≅ᵀ f ξ c)
cong≅ᵀ f ξ (ctrnᵀ c d) = ctrnᵀ (cong≅ᵀ f ξ c) (cong≅ᵀ f ξ d)

red→≅ : {t u : RTm Γ} → t ⟶* u → t ≅ u
red→≅ done       = crfl
red→≅ (step r p) = ctrn (cred r) (red→≅ p)

------------------------------------------------------------------------
-- 2. WEAK-HEAD reduction: a head redex, else one step in the PRINCIPAL
--    position (the one a head rule inspects).
------------------------------------------------------------------------

private
  lift : {t : RTm Δ} (f : RTm Δ → RTm Γ) → (∀ {x y} → x ⟶ y → f x ⟶ f y) → Maybe (Step t) → Maybe (Step (f t))
  lift f ξ (just (v , r)) = just (f v , ξ r)
  lift f ξ nothing        = nothing

  liftᵗ : {t : RTm Δ} (f : RTm Δ → RTy Γ) → (∀ {x y} → x ⟶ y → f x ⟶ᵀ f y) → Maybe (Step t) → Maybe (Stepᵀ (f t))
  liftᵗ f ξ (just (v , r)) = just (f v , ξ r)
  liftᵗ f ξ nothing        = nothing

wstep : (t : RTm Γ) → Maybe (Step t)
inner : (t : RTm Γ) → Maybe (Step t)

wstep t with head t
... | just s  = just s
... | nothing = inner t

inner (app f u)       = lift (λ x → app x u) ξ-appˡ (wstep f)
inner (fst p)         = lift fst ξ-fst (wstep p)
inner (snd p)         = lift snd ξ-snd (wstep p)
inner (natrec z s n)  = lift (natrec z s) ξ-natrecⁿ (wstep n)
inner (fcase t a b)   = lift (λ x → fcase x a b) ξ-fcaseᵗ (wstep t)
inner (fcase0 t)      = lift fcase0 ξ-fcase0 (wstep t)
inner (ielim D i e t) = lift (ielim D i e) ξ-ielimᵗ (wstep t)
inner (dpay I D C)    = lift (dpay I D) ξ-dpayᶜ (wstep C)
inner (dih D e C p)   = lift (λ x → dih D e x p) ξ-dihᶜ (wstep C)
inner (psplit b q)    = lift (psplit b) ξ-psplitᵍ (wstep q)
inner _               = nothing

wstepᵀ : (A : RTy Γ) → Maybe (Stepᵀ A)
innerᵀ : (A : RTy Γ) → Maybe (Stepᵀ A)

wstepᵀ A with headᵀ A
... | just s  = just s
... | nothing = innerᵀ A

innerᵀ (El c)        = liftᵗ El ξ-El (wstep c)
innerᵀ (DIh D M C p) = liftᵗ (λ x → DIh D M x p) ξ-DIhᶜ (wstep C)
innerᵀ _             = nothing

whnf : ℕ → (t : RTm Γ) → Σ (RTm Γ) (t ⟶*_)
whnf zero    t = t , done
whnf (suc k) t with wstep t
... | nothing      = t , done
... | just (v , r) with whnf k v
...   | w , c = w , step r c

whnfᵀ : ℕ → (A : RTy Γ) → Σ (RTy Γ) (A ⟶ᵀ*_)
whnfᵀ zero    A = A , doneᵀ
whnfᵀ (suc k) A with wstepᵀ A
... | nothing      = A , doneᵀ
... | just (B , r) with whnfᵀ k B
...   | C , c = C , stepᵀ r c

------------------------------------------------------------------------
-- 3. ★ LAZY CONVERSION — `just` a proof, or `nothing`.
------------------------------------------------------------------------

private
  -- two fields at once
  both : {A B C : Set} → Maybe A → Maybe B → (A → B → C) → Maybe C
  both (just a) (just b) k = just (k a b)
  both _        _        k = nothing

  -- a conversion between the two reducts, back to the originals
  back : {t t' u u' : RTm Γ} → t ⟶* t' → u ⟶* u' → t' ≅ u' → t ≅ u
  back ct cu c = ctrn (red→≅ ct) (ctrn c (csym (red→≅ cu)))

  backᵀ : {A A' B B' : RTy Γ} → A ⟶ᵀ* A' → B ⟶ᵀ* B' → A' ≅ᵀ B' → A ≅ᵀ B
  backᵀ ca cb c = ctrnᵀ (red→≅ᵀ ca) (ctrnᵀ c (csymᵀ (red→≅ᵀ cb)))

  mapM : {A B : Set} → (A → B) → Maybe A → Maybe B
  mapM f (just a) = just (f a)
  mapM f nothing  = nothing

convTm : ℕ → (t u : RTm Γ) → Maybe (t ≅ u)
convTy : ℕ → (A B : RTy Γ) → Maybe (A ≅ᵀ B)
structTm : ℕ → (t u : RTm Γ) → Maybe (t ≅ u)
structTy : ℕ → (A B : RTy Γ) → Maybe (A ≅ᵀ B)

convTm zero t u with t ≟Tm u
... | yes refl = just crfl
... | no _     = nothing
convTm (suc k) t u with t ≟Tm u
... | yes refl = just crfl
... | no _ with whnf k t | whnf k u
...   | t' , ct | u' , cu with t' ≟Tm u'
...     | yes refl = just (back ct cu crfl)
...     | no _     = mapM (back ct cu) (structTm k t' u')

convTy zero A B with A ≟Ty B
... | yes refl = just crflᵀ
... | no _     = nothing
convTy (suc k) A B with A ≟Ty B
... | yes refl = just crflᵀ
... | no _ with whnfᵀ k A | whnfᵀ k B
...   | A' , ca | B' , cb with A' ≟Ty B'
...     | yes refl = just (backᵀ ca cb crflᵀ)
...     | no _     = mapM (backᵀ ca cb) (structTy k A' B')

-- the same head: the fields
structTm k (lam b) (lam b') = mapM (cong≅ lam ξ-lam) (convTm k b b')
structTm k (app f a) (app f' a') =
  both (convTm k f f') (convTm k a a') λ c₁ c₂ → ctrn (cong≅ (λ x → app x a) ξ-appˡ c₁) (cong≅ (app f') ξ-appʳ c₂)
structTm k (pair a b) (pair a' b') =
  both (convTm k a a') (convTm k b b') λ c₁ c₂ → ctrn (cong≅ (λ x → pair x b) ξ-pairˡ c₁) (cong≅ (pair a') ξ-pairʳ c₂)
structTm k (fst p) (fst p') = mapM (cong≅ fst ξ-fst) (convTm k p p')
structTm k (snd p) (snd p') = mapM (cong≅ snd ξ-snd) (convTm k p p')
structTm k (nsuc n) (nsuc n') = mapM (cong≅ nsuc ξ-nsuc) (convTm k n n')
structTm k (fsuc n) (fsuc n') = mapM (cong≅ fsuc ξ-fsuc) (convTm k n n')
structTm k (con p) (con p') = mapM (cong≅ con ξ-con) (convTm k p p')
structTm k (⌜Fin⌝ n) (⌜Fin⌝ n') = mapM (cong≅ ⌜Fin⌝ ξ-⌜Fin⌝) (convTm k n n')
structTm k (⌜Σ⌝ c d) (⌜Σ⌝ c' d') =
  both (convTm k c c') (convTm k d d') λ c₁ c₂ → ctrn (cong≅ (λ x → ⌜Σ⌝ x d) ξ-⌜Σ⌝ˡ c₁) (cong≅ (⌜Σ⌝ c') ξ-⌜Σ⌝ʳ c₂)
structTm k (⌜Π⌝ c d) (⌜Π⌝ c' d') =
  both (convTm k c c') (convTm k d d') λ c₁ c₂ → ctrn (cong≅ (λ x → ⌜Π⌝ x d) ξ-⌜Π⌝ˡ c₁) (cong≅ (⌜Π⌝ c') ξ-⌜Π⌝ʳ c₂)
structTm k (⌜IMu⌝ I D i) (⌜IMu⌝ I' D' i') =
  both (convTm k I I') (both (convTm k D D') (convTm k i i') (λ a b → a , b)) λ { c₁ (c₂ , c₃) →
    ctrn (cong≅ (λ x → ⌜IMu⌝ x D i) ξ-⌜IMu⌝ᴵ c₁)
         (ctrn (cong≅ (λ x → ⌜IMu⌝ I' x i) ξ-⌜IMu⌝ᴰ c₂) (cong≅ (⌜IMu⌝ I' D') ξ-⌜IMu⌝ⁱ c₃)) }
structTm k (dσ S f) (dσ S' f') =
  both (convTm k S S') (convTm k f f') λ c₁ c₂ → ctrn (cong≅ (λ x → dσ x f) ξ-dσˢ c₁) (cong≅ (dσ S') ξ-dσᶠ c₂)
structTm k (dρ j C) (dρ j' C') =
  both (convTm k j j') (convTm k C C') λ c₁ c₂ → ctrn (cong≅ (λ x → dρ x C) ξ-dρʲ c₁) (cong≅ (dρ j') ξ-dρᶜ c₂)
structTm k (dpay I D C) (dpay I' D' C') =
  both (convTm k I I') (both (convTm k D D') (convTm k C C') (λ a b → a , b)) λ { c₁ (c₂ , c₃) →
    ctrn (cong≅ (λ x → dpay x D C) ξ-dpayᴵ c₁)
         (ctrn (cong≅ (λ x → dpay I' x C) ξ-dpayᴰ c₂) (cong≅ (dpay I' D') ξ-dpayᶜ c₃)) }
structTm k (fcase t a b) (fcase t' a' b') =
  both (convTm k t t') (both (convTm k a a') (convTm k b b') (λ x y → x , y)) λ { c₁ (c₂ , c₃) →
    ctrn (cong≅ (λ x → fcase x a b) ξ-fcaseᵗ c₁)
         (ctrn (cong≅ (λ x → fcase t' x b) ξ-fcaseᵃ c₂) (cong≅ (fcase t' a') ξ-fcaseᵇ c₃)) }
structTm k (natrec z s n) (natrec z' s' n') =
  both (convTm k z z') (both (convTm k s s') (convTm k n n') (λ x y → x , y)) λ { c₁ (c₂ , c₃) →
    ctrn (cong≅ (λ x → natrec x s n) ξ-natrecᶻ c₁)
         (ctrn (cong≅ (λ x → natrec z' x n) ξ-natrecˢ c₂) (cong≅ (natrec z' s') ξ-natrecⁿ c₃)) }
structTm k _ _ = nothing

structTy k (Π A B) (Π A' B') =
  both (convTy k A A') (convTy k B B') λ c₁ c₂ → ctrnᵀ (cong≅ᵀ (λ X → Π X B) ξ-Πˡ c₁) (cong≅ᵀ (Π A') ξ-Πʳ c₂)
structTy k (Σ' A B) (Σ' A' B') =
  both (convTy k A A') (convTy k B B') λ c₁ c₂ → ctrnᵀ (cong≅ᵀ (λ X → Σ' X B) ξ-Σˡ c₁) (cong≅ᵀ (Σ' A') ξ-Σʳ c₂)
structTy k (El c) (El c') = mapM (cong≅ᵗ El ξ-El) (convTm k c c')
structTy k (Fin n) (Fin n') = mapM (cong≅ᵗ Fin ξ-Fin) (convTm k n n')
structTy k (Desc I) (Desc I') = mapM (cong≅ᵗ Desc ξ-Desc) (convTm k I I')
structTy k (IMu I D i) (IMu I' D' i') =
  both (convTm k I I') (both (convTm k D D') (convTm k i i') (λ a b → a , b)) λ { c₁ (c₂ , c₃) →
    ctrnᵀ (cong≅ᵗ (λ x → IMu x D i) ξ-IMuᴵ c₁)
          (ctrnᵀ (cong≅ᵗ (λ x → IMu I' x i) ξ-IMuᴰ c₂) (cong≅ᵗ (IMu I' D') ξ-IMuⁱ c₃)) }
structTy k (DIh D M C p) (DIh D' M' C' p') =
  both (convTm k D D') (both (convTy k M M') (both (convTm k C C') (convTm k p p') (λ a b → a , b)) (λ a b → a , b))
    λ { c₁ (c₂ , (c₃ , c₄)) →
      ctrnᵀ (cong≅ᵗ (λ x → DIh x M C p) ξ-DIhᴰ c₁)
            (ctrnᵀ (cong≅ᵀ (λ X → DIh D' X C p) ξ-DIhᴹ c₂)
                   (ctrnᵀ (cong≅ᵗ (λ x → DIh D' M' x p) ξ-DIhᶜ c₃) (cong≅ᵗ (DIh D' M' C') ξ-DIhᵖ c₄))) }
structTy k _ _ = nothing

------------------------------------------------------------------------
-- 4. ★ NORMAL ORDER, certified: weak-head first, then the fields of the
--    head — so an unapplied function is NEVER normalised (applicative
--    order inlines and normalises whole generic definitions before β).
--    The result is a reduct of the input, with its chain.
------------------------------------------------------------------------

private
  map* : {a b : RTm Δ} (f : RTm Δ → RTm Γ) → (∀ {x y} → x ⟶ y → f x ⟶ f y) → a ⟶* b → f a ⟶* f b
  map* f ξ done       = done
  map* f ξ (step r p) = step (ξ r) (map* f ξ p)

  trans* : {a b c : RTm Γ} → a ⟶* b → b ⟶* c → a ⟶* c
  trans* done       q = q
  trans* (step r p) q = step r (trans* p q)

  Red : RTm Γ → Set
  Red {Γ} t = Σ (RTm Γ) (t ⟶*_)

  -- one field: normalise it, carry the chain through the congruence
  fld₁ : {t : RTm Γ} {a : RTm Δ} (f : RTm Δ → RTm Γ) → (∀ {x y} → x ⟶ y → f x ⟶ f y) →
         t ⟶* f a → Red a → Red t
  fld₁ f ξ ch (a' , c) = f a' , trans* ch (map* f ξ c)

normLazy : ℕ → (t : RTm Γ) → Σ (RTm Γ) (t ⟶*_)
normFields : ℕ → {t₀ : RTm Γ} (t : RTm Γ) → t₀ ⟶* t → Σ (RTm Γ) (t₀ ⟶*_)

normLazy zero    t = t , done
normLazy (suc k) t with whnf k t
... | t' , c = normFields k t' c

normFields k (lam b) ch = fld₁ lam ξ-lam ch (normLazy k b)
normFields k (con p) ch = fld₁ con ξ-con ch (normLazy k p)
normFields k (fsuc n) ch = fld₁ fsuc ξ-fsuc ch (normLazy k n)
normFields k (nsuc n) ch = fld₁ nsuc ξ-nsuc ch (normLazy k n)
normFields k (⌜Fin⌝ n) ch = fld₁ ⌜Fin⌝ ξ-⌜Fin⌝ ch (normLazy k n)
normFields k (fst p) ch = fld₁ fst ξ-fst ch (normLazy k p)
normFields k (snd p) ch = fld₁ snd ξ-snd ch (normLazy k p)
normFields k (pair a b) ch with fld₁ (λ x → pair x b) ξ-pairˡ ch (normLazy k a)
... | pair a' b , ch' = fld₁ (pair a') ξ-pairʳ ch' (normLazy k b)
... | r = r
normFields k (app f a) ch with fld₁ (λ x → app x a) ξ-appˡ ch (normLazy k f)
... | app f' a , ch' = fld₁ (app f') ξ-appʳ ch' (normLazy k a)
... | r = r
normFields k (dσ S f) ch with fld₁ (λ x → dσ x f) ξ-dσˢ ch (normLazy k S)
... | dσ S' f , ch' = fld₁ (dσ S') ξ-dσᶠ ch' (normLazy k f)
... | r = r
normFields k (dρ j C) ch with fld₁ (λ x → dρ x C) ξ-dρʲ ch (normLazy k j)
... | dρ j' C , ch' = fld₁ (dρ j') ξ-dρᶜ ch' (normLazy k C)
... | r = r
normFields k (⌜Σ⌝ c d) ch with fld₁ (λ x → ⌜Σ⌝ x d) ξ-⌜Σ⌝ˡ ch (normLazy k c)
... | ⌜Σ⌝ c' d , ch' = fld₁ (⌜Σ⌝ c') ξ-⌜Σ⌝ʳ ch' (normLazy k d)
... | r = r
normFields k (fcase t a b) ch with fld₁ (λ x → fcase x a b) ξ-fcaseᵗ ch (normLazy k t)
... | fcase t' a b , ch' with fld₁ (λ x → fcase t' x b) ξ-fcaseᵃ ch' (normLazy k a)
...   | fcase t' a' b , ch'' = fld₁ (fcase t' a') ξ-fcaseᵇ ch'' (normLazy k b)
...   | r = r
normFields k (fcase t a b) ch | r = r
normFields k t ch = t , ch
