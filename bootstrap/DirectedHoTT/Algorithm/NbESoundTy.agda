-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE ENVIRONMENT EVALUATOR IS SOUND ON TYPES
-- (PLAN-EVAL E3, the type level):
--
--     nbeᵀ-sound : (k : ℕ) (A : RTy Γ) → A ≅ᵀ nbeᵀ k A
--
-- at every fuel.  The type level of `Algorithm/NbE` is a second layer
-- over the term evaluator (terms never contain types), so its proof is a
-- second layer over `Algorithm/NbESound`, by the same method: READ type
-- values as types (`⌊_⌋ᵀ`, defined with the evaluator), one lemma per
-- evaluator function by the same views, each case a kernel step
-- (`_⟶ᵀ_`'s El-⌜…⌝, Hom-…, DIh-… rules), a congruence, the term level's
-- lemma for the terms inside, or a fusion equation.
--
-- The scope invariant (`ScT`) and the reading lemmas for a fresh level
-- (`agreeᵀ`, `renᵀ`) mirror `Algorithm/NbERead`; they are what a type
-- closure read under its binder needs (`T-freshᵀ`).
--
-- `--safe`, ZERO postulates.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.NbESoundTy where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; _×_; _,_; ⊤; tt )
open import Agda.Builtin.Nat using ( zero; suc; _<_; _==_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_; ⌊_⌋ )
open import DirectedHoTT.Metatheory.TySub using ( wk-cancel; wk-cancel-tm; ⟶ᵀ-ren )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTm-var )
open import DirectedHoTT.Metatheory.Confluence using ( single-⟹; ⟶→⟹ )
open import DirectedHoTT.Metatheory.Injectivity using ( ⟹ᵀ-sub; ⟹ᵀ-refl; ⟹ᵀ→⟶ᵀ* )
open import DirectedHoTT.Algorithm.ConvCong using ( ≅app )
open import DirectedHoTT.Algorithm.NbE
open import DirectedHoTT.Algorithm.NbERead
open import DirectedHoTT.Algorithm.NbEScope
open import DirectedHoTT.Algorithm.NbESound
  using ( ≡→≅; _⨾_; S-eval; S-force; S-inst; S-vApp; S-vFst; S-vSnd; S-rb
        ; bind-here; bind-wk; sub-vz-wk; idEnv-read; sc-idEnv )

private
  variable
    Γ Δ Θ : Cx

------------------------------------------------------------------------
-- 1. Type conversion: congruences, renaming, substituting convertible terms.
------------------------------------------------------------------------

infixr 4 _⨾ᵀ_
_⨾ᵀ_ : {A B C : RTy Δ} → A ≅ᵀ B → B ≅ᵀ C → A ≅ᵀ C
_⨾ᵀ_ = ctrnᵀ

≡→≅ᵀ : {A B : RTy Δ} → A ≡ B → A ≅ᵀ B
≡→≅ᵀ refl = crflᵀ

-- a term slot of a type former, and a type slot
liftt : {Γ' : Cx} (F : RTm Γ' → RTy Γ) → (∀ {t t'} → t ⟶ t' → F t ⟶ᵀ F t') →
        {t u : RTm Γ'} → t ≅ u → F t ≅ᵀ F u
liftt F ξ (cred r)   = credᵀ (ξ r)
liftt F ξ crfl       = crflᵀ
liftt F ξ (csym c)   = csymᵀ (liftt F ξ c)
liftt F ξ (ctrn c d) = ctrnᵀ (liftt F ξ c) (liftt F ξ d)

liftT : {Γ' : Cx} (F : RTy Γ' → RTy Γ) → (∀ {A A'} → A ⟶ᵀ A' → F A ⟶ᵀ F A') →
        {A B : RTy Γ'} → A ≅ᵀ B → F A ≅ᵀ F B
liftT F ξ (credᵀ r)   = credᵀ (ξ r)
liftT F ξ crflᵀ       = crflᵀ
liftT F ξ (csymᵀ c)   = csymᵀ (liftT F ξ c)
liftT F ξ (ctrnᵀ c d) = ctrnᵀ (liftT F ξ c) (liftT F ξ d)

El≅ : {t u : RTm Δ} → t ≅ u → El t ≅ᵀ El u
El≅ = liftt El ξ-El

Π≅ : {A A' : RTy Δ} {B B' : RTy (Δ ∙)} → A ≅ᵀ A' → B ≅ᵀ B' → Π A B ≅ᵀ Π A' B'
Π≅ {A' = A'} {B = B} a b = liftT (λ X → Π X B) ξ-Πˡ a ⨾ᵀ liftT (Π A') ξ-Πʳ b

Σ≅ : {A A' : RTy Δ} {B B' : RTy (Δ ∙)} → A ≅ᵀ A' → B ≅ᵀ B' → Σ' A B ≅ᵀ Σ' A' B'
Σ≅ {A' = A'} {B = B} a b = liftT (λ X → Σ' X B) ξ-Σˡ a ⨾ᵀ liftT (Σ' A') ξ-Σʳ b

Hom≅ : {A A' : RTy Δ} {a a' b b' : RTm Δ} → A ≅ᵀ A' → a ≅ a' → b ≅ b' → Hom A a b ≅ᵀ Hom A' a' b'
Hom≅ {A' = A'} {a = a} {a'} {b} {b'} p q r =
  liftT (λ X → Hom X a b) ξ-Homᵀ p ⨾ᵀ liftt (λ x → Hom A' x b) ξ-Homˡ q ⨾ᵀ liftt (Hom A' a') ξ-Homʳ r

Id≅ : {A A' : RTy Δ} {a a' b b' : RTm Δ} → A ≅ᵀ A' → a ≅ a' → b ≅ b' → Id A a b ≅ᵀ Id A' a' b'
Id≅ {A' = A'} {a = a} {a'} {b} {b'} p q r =
  liftT (λ X → Id X a b) ξ-Idᵀ p ⨾ᵀ liftt (λ x → Id A' x b) ξ-Idˡ q ⨾ᵀ liftt (Id A' a') ξ-Idʳ r

IMu≅ : {I I' D D' i i' : RTm Δ} → I ≅ I' → D ≅ D' → i ≅ i' → IMu I D i ≅ᵀ IMu I' D' i'
IMu≅ {I' = I'} {D = D} {D'} {i} {i'} p q r =
  liftt (λ x → IMu x D i) ξ-IMuᴵ p ⨾ᵀ liftt (λ x → IMu I' x i) ξ-IMuᴰ q ⨾ᵀ liftt (IMu I' D') ξ-IMuⁱ r

Desc≅ : {I I' : RTm Δ} → I ≅ I' → Desc I ≅ᵀ Desc I'
Desc≅ = liftt Desc ξ-Desc

Fin≅ : {n n' : RTm Δ} → n ≅ n' → Fin n ≅ᵀ Fin n'
Fin≅ = liftt Fin ξ-Fin

DIh≅ : {D D' C C' p p' : RTm Δ} {M M' : RTy ((Δ ∙) ∙)} →
       D ≅ D' → M ≅ᵀ M' → C ≅ C' → p ≅ p' → DIh D M C p ≅ᵀ DIh D' M' C' p'
DIh≅ {D' = D'} {C = C} {C'} {p} {p'} {M} {M'} d m c q =
  liftt (λ x → DIh x M C p) ξ-DIhᴰ d ⨾ᵀ liftT (λ X → DIh D' X C p) ξ-DIhᴹ m
  ⨾ᵀ liftt (λ x → DIh D' M' x p) ξ-DIhᶜ c ⨾ᵀ liftt (DIh D' M' C') ξ-DIhᵖ q

≅ᵀ-ren : (ρ : Ren Γ Δ) {A B : RTy Γ} → A ≅ᵀ B → renTy ρ A ≅ᵀ renTy ρ B
≅ᵀ-ren ρ (credᵀ r)   = credᵀ (⟶ᵀ-ren ρ r)
≅ᵀ-ren ρ crflᵀ       = crflᵀ
≅ᵀ-ren ρ (csymᵀ c)   = csymᵀ (≅ᵀ-ren ρ c)
≅ᵀ-ren ρ (ctrnᵀ c d) = ctrnᵀ (≅ᵀ-ren ρ c) (≅ᵀ-ren ρ d)

-- substituting convertible terms into a type (parallel reduction)
sub1≅ᵀ : (Y : RTy (Δ ∙)) {X X' : RTm Δ} → X ≅ X' → subTy (single X) Y ≅ᵀ subTy (single X') Y
sub1≅ᵀ Y (cred r)   = red→≅ᵀ (⟹ᵀ→⟶ᵀ* (⟹ᵀ-sub (single-⟹ (⟶→⟹ r)) (⟹ᵀ-refl Y)))
sub1≅ᵀ Y crfl       = crflᵀ
sub1≅ᵀ Y (csym c)   = csymᵀ (sub1≅ᵀ Y c)
sub1≅ᵀ Y (ctrn c d) = ctrnᵀ (sub1≅ᵀ Y c) (sub1≅ᵀ Y d)

------------------------------------------------------------------------
-- 2. Scope of type values, and its preservation.
------------------------------------------------------------------------

ScT  : ℕ → TVal → Set
ScTᶜ : ℕ → TClo → Set
ScT² : ℕ → TClo₂ → Set

ScT² n (tclo₂ ρ M) = Scᵉ n ρ

ScTᶜ n (tclo ρ B)        = Scᵉ n ρ
ScTᶜ n (tcloK A)         = ScT n A
ScTᶜ n (tcloEl d)        = Scᶜ n d
ScTᶜ n (tcloHom B f g)   = ScTᶜ n B × (Sc n f × Sc n g)
ScTᶜ n (tcloDIh D M C p) = Sc n D × (ScT² n M × (Sc n C × Sc n p))

ScT n tbase           = ⊤
ScT n tU              = ⊤
ScT n tUnit           = ⊤
ScT n tNat            = ⊤
ScT n (tΠ A B)        = ScT n A × ScTᶜ n B
ScT n (tΣ A B)        = ScT n A × ScTᶜ n B
ScT n (tEl c)         = Sc n c
ScT n (tHom A a b)    = ScT n A × (Sc n a × Sc n b)
ScT n (tId A a b)     = ScT n A × (Sc n a × Sc n b)
ScT n (tIMu I D i)    = Sc n I × (Sc n D × Sc n i)
ScT n (tDesc I)       = Sc n I
ScT n (tDIh D M C p)  = Sc n D × (ScT² n M × (Sc n C × Sc n p))
ScT n (tFin t)        = Sc n t
ScT n (tinst c v)     = ScTᶜ n c × Sc n v
ScT n (tinst₂ c j t)  = ScT² n c × (Sc n j × Sc n t)

monoT  : {n m : ℕ} (A : TVal) → Up n m → ScT n A → ScT m A
monoTᶜ : {n m : ℕ} (c : TClo) → Up n m → ScTᶜ n c → ScTᶜ m c
monoT² : {n m : ℕ} (c : TClo₂) → Up n m → ScT² n c → ScT² m c

monoT² (tclo₂ ρ M) u s = monoᵉ ρ u s

monoTᶜ (tclo ρ B) u s = monoᵉ ρ u s
monoTᶜ (tcloK A) u s = monoT A u s
monoTᶜ (tcloEl d) u s = monoᶜ d u s
monoTᶜ (tcloHom B f g) u (sB , (sf , sg)) = monoTᶜ B u sB , (mono f u sf , mono g u sg)
monoTᶜ (tcloDIh D M C p) u (sD , (sM , (sC , sp))) = mono D u sD , (monoT² M u sM , (mono C u sC , mono p u sp))

monoT tbase u s = tt
monoT tU u s = tt
monoT tUnit u s = tt
monoT tNat u s = tt
monoT (tΠ A B) u (sA , sB) = monoT A u sA , monoTᶜ B u sB
monoT (tΣ A B) u (sA , sB) = monoT A u sA , monoTᶜ B u sB
monoT (tEl c) u s = mono c u s
monoT (tHom A a b) u (sA , (sa , sb)) = monoT A u sA , (mono a u sa , mono b u sb)
monoT (tId A a b) u (sA , (sa , sb)) = monoT A u sA , (mono a u sa , mono b u sb)
monoT (tIMu I D i) u (sI , (sD , si)) = mono I u sI , (mono D u sD , mono i u si)
monoT (tDesc I) u s = mono I u s
monoT (tDIh D M C p) u (sD , (sM , (sC , sp))) = mono D u sD , (monoT² M u sM , (mono C u sC , mono p u sp))
monoT (tFin t) u s = mono t u s
monoT (tinst c v) u (sc , sv) = monoTᶜ c u sc , mono v u sv
monoT (tinst₂ c j t) u (sc , (sj , st)) = monoT² c u sc , (mono j u sj , mono t u st)

sc-evalᵀ  : (k n : ℕ) (ρ : Env Γ) (A : RTy Γ) → Scᵉ n ρ → ScT n (evalᵀ k n ρ A)
sc-instᵀ  : (k n : ℕ) (c : TClo) (v : Val) → ScTᶜ n c → Sc n v → ScT n (instᵀ k n c v)
sc-instᵀ₂ : (k n : ℕ) (c : TClo₂) (j t : Val) → ScT² n c → Sc n j → Sc n t → ScT n (instᵀ₂ k n c j t)
sc-tElS   : (k n : ℕ) (c : Val) → Sc n c → ScT n (tElS k n c)
sc-tElF   : (k n : ℕ) {c : Val} (w : CodeV c) → Sc n c → ScT n (tElF k n w)
sc-tHomS  : (k n : ℕ) (A : TVal) (a b : Val) → ScT n A → Sc n a → Sc n b → ScT n (tHomS k n A a b)
sc-tHomF  : (k n : ℕ) {A : TVal} (w : TyV A) (a b : Val) → ScT n A → Sc n a → Sc n b → ScT n (tHomF k n w a b)
sc-tHomNat : (k n : ℕ) (a b : Val) → Sc n a → Sc n b → ScT n (tHomNat k a b)
sc-tHomA  : (k n : ℕ) {a : Val} (w : NatV a) (b : Val) → Sc n a → Sc n b → ScT n (tHomA k w b)
sc-tHomB  : (k n : ℕ) (m : Val) {b : Val} (w : NatV b) → Sc n m → Sc n b → ScT n (tHomB k m w)
sc-tDIhS  : (k n : ℕ) (D : Val) (M : TClo₂) (C p : Val) → Sc n D → ScT² n M → Sc n C → Sc n p → ScT n (tDIhS k n D M C p)
sc-tDIhF  : (k n : ℕ) (D : Val) (M : TClo₂) {C : Val} (w : DescV C) (p : Val) →
            Sc n D → ScT² n M → Sc n C → Sc n p → ScT n (tDIhF k n D M w p)

sc-evalᵀ k n ρ base          s = tt
sc-evalᵀ k n ρ U             s = tt
sc-evalᵀ k n ρ (Π A B)       s = sc-evalᵀ k n ρ A s , s
sc-evalᵀ k n ρ (Σ' A B)      s = sc-evalᵀ k n ρ A s , s
sc-evalᵀ k n ρ (El c)        s = sc-tElS k n (eval k n ρ c) (sc-eval k n ρ c s)
sc-evalᵀ k n ρ (Hom A a b)   s = sc-tHomS k n (evalᵀ k n ρ A) (eval k n ρ a) (eval k n ρ b) (sc-evalᵀ k n ρ A s) (sc-eval k n ρ a s) (sc-eval k n ρ b s)
sc-evalᵀ k n ρ Unit          s = tt
sc-evalᵀ k n ρ Nat           s = tt
sc-evalᵀ k n ρ (Id A a b)    s = sc-evalᵀ k n ρ A s , (sc-eval k n ρ a s , sc-eval k n ρ b s)
sc-evalᵀ k n ρ (IMu I D i)   s = sc-eval k n ρ I s , (sc-eval k n ρ D s , sc-eval k n ρ i s)
sc-evalᵀ k n ρ (Desc I)      s = sc-eval k n ρ I s
sc-evalᵀ k n ρ (DIh D M C p) s = sc-tDIhS k n (eval k n ρ D) (tclo₂ ρ M) (eval k n ρ C) (eval k n ρ p) (sc-eval k n ρ D s) s (sc-eval k n ρ C s) (sc-eval k n ρ p s)
sc-evalᵀ k n ρ (Fin t)       s = sc-eval k n ρ t s

sc-instᵀ zero    n c                 v sc sv = sc , sv
sc-instᵀ (suc k) n (tclo ρ B)        v sc sv = sc-evalᵀ k n (ρ , v) B (sc , sv)
sc-instᵀ (suc k) n (tcloK A)         v sc sv = sc
sc-instᵀ (suc k) n (tcloEl d)        v sc sv = sc-tElS k n (inst k n d v) (sc-inst k n d v sc sv)
sc-instᵀ (suc k) n (tcloHom B f g)   v (sB , (sf , sg)) sv =
  sc-tHomS k n (instᵀ k n B v) (vApp k n f v) (vApp k n g v) (sc-instᵀ k n B v sB sv) (sc-vApp k n f v sf sv) (sc-vApp k n g v sg sv)
sc-instᵀ (suc k) n (tcloDIh D M C p) v (sD , (sM , (sC , sp))) sv = sc-tDIhS k n D M C (vSnd k p) sD sM sC (sc-vSnd k n p sp)

sc-instᵀ₂ zero    n c           j t sc sj st = sc , (sj , st)
sc-instᵀ₂ (suc k) n (tclo₂ ρ M) j t sc sj st = sc-evalᵀ k n ((ρ , j) , t) M ((sc , sj) , st)

sc-tElS k n c s = sc-tElF k n (codeV (force k c)) (sc-force k n c s)

sc-tElF k       n cbase        s = tt
sc-tElF zero    n (cΠ c d)     s = s
sc-tElF (suc k) n (cΠ c d)     (sc , sd) = sc-tElS k n c sc , sd
sc-tElF zero    n (cΣ c d)     s = s
sc-tElF (suc k) n (cΣ c d)     (sc , sd) = sc-tElS k n c sc , sd
sc-tElF zero    n (cHom c a b) s = s
sc-tElF (suc k) n (cHom c a b) (sc , (sa , sb)) = sc-tHomS k n (tElS k n c) a b (sc-tElS k n c sc) sa sb
sc-tElF zero    n (cId c a b)  s = s
sc-tElF (suc k) n (cId c a b)  (sc , (sa , sb)) = sc-tElS k n c sc , (sa , sb)
sc-tElF k       n cNat         s = tt
sc-tElF k       n (cIMu I D i) s = s
sc-tElF k       n (cFin t)     s = s
sc-tElF k       n cUnit        s = tt
sc-tElF k       n (cOther c)   s = s

sc-tHomS k n A a b = sc-tHomF k n (tyV A) a b

sc-tHomF k       n tvNat       a b sA sa sb = sc-tHomNat k n a b sa sb
sc-tHomF zero    n tvU         c d sA sc sd = tt , (sc , sd)
sc-tHomF (suc k) n tvU         c d sA sc sd = sc-tElS k n c sc , sc-tElS k n d sd
sc-tHomF k       n (tvΠ A B)   f g (sA , sB) sf sg = sA , (sB , (sf , sg))
sc-tHomF k       n (tvOther A) a b sA sa sb = sA , (sa , sb)

sc-tHomNat k n a b sa sb = sc-tHomA k n (natV (force k a)) b (sc-force k n a sa) sb

sc-tHomA k n isZero     b sa sb = tt
sc-tHomA k n (isSuc m)  b sm sb = sc-tHomB k n m (natV (force k b)) sm (sc-force k n b sb)
sc-tHomA k n (notNat a) b sa sb = tt , (sa , sb)

sc-tHomB k       n m isZero     sm sb = tt
sc-tHomB zero    n m (isSuc b)  sm sb = tt , (sm , sb)
sc-tHomB (suc k) n m (isSuc b)  sm sb = sc-tHomNat k n m b sm sb
sc-tHomB k       n m (notNat b) sm sb = tt , (sm , sb)

sc-tDIhS k n D M C p sD sM sC sp = sc-tDIhF k n D M (descV (force k C)) p sD sM (sc-force k n C sC) sp

sc-tDIhF k       n D M isDι        p sD sM sC sp = tt
sc-tDIhF zero    n D M (isDσ S f)  p sD sM sC sp = sD , (sM , (sC , sp))
sc-tDIhF (suc k) n D M (isDσ S f)  p sD sM (sS , sf) sp =
  sc-tDIhS k n D M (vApp k n f (vFst k p)) (vSnd k p) sD sM (sc-vApp k n f (vFst k p) sf (sc-vFst k n p sp)) (sc-vSnd k n p sp)
sc-tDIhF zero    n D M (isDρ j C)  p sD sM sC sp = sD , (sM , (sC , sp))
sc-tDIhF (suc k) n D M (isDρ j C)  p sD sM (sj , sC) sp =
  sc-instᵀ₂ k n M j (vFst k p) sM sj (sc-vFst k n p sp) , (sD , (sM , (sC , sp)))
sc-tDIhF k       n D M (notDesc C) p sD sM sC sp = sD , (sM , (sC , sp))

------------------------------------------------------------------------
-- 3. Reading type values at agreeing level maps, and under a renaming.
------------------------------------------------------------------------

private
  ext-pt : {σ σ' : Sub Γ Δ} → (∀ x → σ x ≡ σ' x) → ∀ x → extS σ x ≡ extS σ' x
  ext-pt h vz     = refl
  ext-pt h (vs x) = cong (renTm vs) (h x)

  single-pt : {X X' : RTm Δ} → X ≡ X' → ∀ (x : Var (Δ ∙)) → single X x ≡ single X' x
  single-pt e vz     = e
  single-pt e (vs x) = refl

agreeᵀ  : (n : ℕ) (A : TVal) {L L' : Lv Δ} → Below n L L' → ScT n A → ⌊ A ⌋ᵀ L ≡ ⌊ A ⌋ᵀ L'
agreeᵀᶜ : (n : ℕ) (c : TClo) {L L' : Lv Δ} → Below n L L' → ScTᶜ n c → ⌊ c ⌋ᵀᶜ L ≡ ⌊ c ⌋ᵀᶜ L'
agreeᵀ² : (n : ℕ) (c : TClo₂) {L L' : Lv Δ} → Below n L L' → ScT² n c → ⌊ c ⌋ᵀ² L ≡ ⌊ c ⌋ᵀ² L'

agreeᵀ² n (tclo₂ ρ M) b s = subTy-cong (ext-pt (ext-pt (agreeᵉ n ρ b s))) M

agreeᵀᶜ n (tclo ρ B) b s = subTy-cong (ext-pt (agreeᵉ n ρ b s)) B
agreeᵀᶜ n (tcloK A) b s = cong (renTy vs) (agreeᵀ n A b s)
agreeᵀᶜ n (tcloEl d) b s = cong El (agreeᶜ n d b s)
agreeᵀᶜ n (tcloHom B f g) b (sB , (sf , sg)) =
  cong₂ (λ X Y → X Y) (cong₂ (λ X x → Hom X (app (wk x) (var vz))) (agreeᵀᶜ n B b sB) (agree n f b sf))
        (cong (λ x → app (wk x) (var vz)) (agree n g b sg))
agreeᵀᶜ n (tcloDIh D M C p) b (sD , (sM , (sC , sp))) =
  cong₂ (λ X Y → X Y)
    (cong₂ (λ X Y → X Y) (cong₂ (λ x X → DIh (wk x) (renTy (extR (extR vs)) X)) (agree n D b sD) (agreeᵀ² n M b sM))
           (cong wk (agree n C b sC)))
    (cong (λ x → snd (wk x)) (agree n p b sp))

agreeᵀ n tbase b s = refl
agreeᵀ n tU b s = refl
agreeᵀ n tUnit b s = refl
agreeᵀ n tNat b s = refl
agreeᵀ n (tΠ A B) b (sA , sB) = cong₂ Π (agreeᵀ n A b sA) (agreeᵀᶜ n B b sB)
agreeᵀ n (tΣ A B) b (sA , sB) = cong₂ Σ' (agreeᵀ n A b sA) (agreeᵀᶜ n B b sB)
agreeᵀ n (tEl c) b s = cong El (agree n c b s)
agreeᵀ n (tHom A a c) b (sA , (sa , sc)) = cong₂ (λ X Y → X Y) (cong₂ Hom (agreeᵀ n A b sA) (agree n a b sa)) (agree n c b sc)
agreeᵀ n (tId A a c) b (sA , (sa , sc)) = cong₂ (λ X Y → X Y) (cong₂ Id (agreeᵀ n A b sA) (agree n a b sa)) (agree n c b sc)
agreeᵀ n (tIMu I D i) b (sI , (sD , si)) = cong₂ (λ X Y → X Y) (cong₂ IMu (agree n I b sI) (agree n D b sD)) (agree n i b si)
agreeᵀ n (tDesc I) b s = cong Desc (agree n I b s)
agreeᵀ n (tDIh D M C p) b (sD , (sM , (sC , sp))) =
  cong₂ (λ X Y → X Y) (cong₂ (λ X Y → X Y) (cong₂ DIh (agree n D b sD) (agreeᵀ² n M b sM)) (agree n C b sC)) (agree n p b sp)
agreeᵀ n (tFin t) b s = cong Fin (agree n t b s)
agreeᵀ n (tinst c v) b (sc , sv) = cong₂ (λ X Y → subTy (single X) Y) (agree n v b sv) (agreeᵀᶜ n c b sc)
agreeᵀ n (tinst₂ c j t) b (sc , (sj , st)) =
  cong₂ (λ X Y → subTy (single X) Y) (agree n t b st)
        (cong₂ (λ X Y → subTy (extS (single X)) Y) (agree n j b sj) (agreeᵀ² n c b sc))

renᵀ  : (r : Ren Δ Θ) (A : TVal) (L : Lv Δ) → renTy r (⌊ A ⌋ᵀ L) ≡ ⌊ A ⌋ᵀ (r ᴸ L)
renᵀᶜ : (r : Ren Δ Θ) (c : TClo) (L : Lv Δ) → renTy (extR r) (⌊ c ⌋ᵀᶜ L) ≡ ⌊ c ⌋ᵀᶜ (r ᴸ L)
renᵀ² : (r : Ren Δ Θ) (c : TClo₂) (L : Lv Δ) → renTy (extR (extR r)) (⌊ c ⌋ᵀ² L) ≡ ⌊ c ⌋ᵀ² (r ᴸ L)

private
  -- a renaming past a binder commutes with the weakening
  ext-ren : (r : Ren Δ Θ) {σ : Sub Γ Δ} {σ' : Sub Γ Θ} → (∀ x → (r ᵣ∘ₛ σ) x ≡ σ' x) →
            ∀ x → (extR r ᵣ∘ₛ extS σ) x ≡ extS σ' x
  ext-ren r h vz     = refl
  ext-ren r {σ} h (vs x) = trans (wk-ren r (σ x)) (cong wk (h x))

  wk2-ren : (r : Ren Δ Θ) (x : Var ((Δ ∙) ∙)) → (extR (extR (extR r)) ∘ᵣ extR (extR vs)) x ≡ (extR (extR vs) ∘ᵣ extR (extR r)) x
  wk2-ren r vz          = refl
  wk2-ren r (vs vz)     = refl
  wk2-ren r (vs (vs x)) = refl

  wk1-ren : (r : Ren Δ Θ) (x : Var Δ) → (extR r ∘ᵣ vs) x ≡ (vs ∘ᵣ r) x
  wk1-ren r x = refl

renᵀ² r (tclo₂ ρ M) L = trans (renTy-subTy M) (subTy-cong (ext-ren (extR r) (ext-ren r (renᵉ r ρ L))) M)

renᵀᶜ r (tclo ρ B) L = trans (renTy-subTy B) (subTy-cong (ext-ren r (renᵉ r ρ L)) B)
renᵀᶜ r (tcloK A) L =
  trans (renTy-renTy (⌊ A ⌋ᵀ L)) (trans (renTy-cong (λ x → refl) (⌊ A ⌋ᵀ L))
        (trans (sym (renTy-renTy {ρ' = vs} {ρ = r} (⌊ A ⌋ᵀ L))) (cong (renTy vs) (renᵀ r A L))))
renᵀᶜ r (tcloEl d) L = cong El (renᶜ r d L)
renᵀᶜ r (tcloHom B f g) L =
  cong₂ (λ X Y → X Y) (cong₂ (λ X x → Hom X (app x (var vz))) (renᵀᶜ r B L) (trans (wk-ren r (⌊ f ⌋ L)) (cong wk (ren⌊⌋ r f L))))
        (cong (λ x → app x (var vz)) (trans (wk-ren r (⌊ g ⌋ L)) (cong wk (ren⌊⌋ r g L))))
renᵀᶜ r (tcloDIh D M C p) L =
  cong₂ (λ X Y → X Y)
    (cong₂ (λ X Y → X Y)
       (cong₂ DIh (trans (wk-ren r (⌊ D ⌋ L)) (cong wk (ren⌊⌋ r D L)))
                  (trans (renTy-renTy (⌊ M ⌋ᵀ² L))
                         (trans (renTy-cong (wk2-ren r) (⌊ M ⌋ᵀ² L))
                                (trans (sym (renTy-renTy (⌊ M ⌋ᵀ² L))) (cong (renTy (extR (extR vs))) (renᵀ² r M L))))))
       (trans (wk-ren r (⌊ C ⌋ L)) (cong wk (ren⌊⌋ r C L))))
    (cong snd (trans (wk-ren r (⌊ p ⌋ L)) (cong wk (ren⌊⌋ r p L))))

renᵀ r tbase L = refl
renᵀ r tU L = refl
renᵀ r tUnit L = refl
renᵀ r tNat L = refl
renᵀ r (tΠ A B) L = cong₂ Π (renᵀ r A L) (renᵀᶜ r B L)
renᵀ r (tΣ A B) L = cong₂ Σ' (renᵀ r A L) (renᵀᶜ r B L)
renᵀ r (tEl c) L = cong El (ren⌊⌋ r c L)
renᵀ r (tHom A a b) L = cong₂ (λ X Y → X Y) (cong₂ Hom (renᵀ r A L) (ren⌊⌋ r a L)) (ren⌊⌋ r b L)
renᵀ r (tId A a b) L = cong₂ (λ X Y → X Y) (cong₂ Id (renᵀ r A L) (ren⌊⌋ r a L)) (ren⌊⌋ r b L)
renᵀ r (tIMu I D i) L = cong₂ (λ X Y → X Y) (cong₂ IMu (ren⌊⌋ r I L) (ren⌊⌋ r D L)) (ren⌊⌋ r i L)
renᵀ r (tDesc I) L = cong Desc (ren⌊⌋ r I L)
renᵀ r (tDIh D M C p) L =
  cong₂ (λ X Y → X Y) (cong₂ (λ X Y → X Y) (cong₂ DIh (ren⌊⌋ r D L) (renᵀ² r M L)) (ren⌊⌋ r C L)) (ren⌊⌋ r p L)
renᵀ r (tFin t) L = cong Fin (ren⌊⌋ r t L)
renᵀ r (tinst c v) L =
  trans (renTy-subTy (⌊ c ⌋ᵀᶜ L))
        (trans (subTy-cong pt (⌊ c ⌋ᵀᶜ L))
               (trans (sym (subTy-renTy (⌊ c ⌋ᵀᶜ L))) (cong (subTy (single (⌊ v ⌋ (r ᴸ L)))) (renᵀᶜ r c L))))
  where
  pt : ∀ x → (r ᵣ∘ₛ single (⌊ v ⌋ L)) x ≡ (single (⌊ v ⌋ (r ᴸ L)) ₛ∘ᵣ extR r) x
  pt vz     = ren⌊⌋ r v L
  pt (vs x) = refl
renᵀ r (tinst₂ c j t) L =
  trans (renTy-subTy Y)
        (trans (subTy-cong pt Y)
               (trans (sym (subTy-renTy Y))
                      (cong (subTy (single (⌊ t ⌋ (r ᴸ L))))
                            (trans (renTy-subTy (⌊ c ⌋ᵀ² L))
                                   (trans (subTy-cong pt₂ (⌊ c ⌋ᵀ² L))
                                          (trans (sym (subTy-renTy (⌊ c ⌋ᵀ² L)))
                                                 (cong (subTy (extS (single (⌊ j ⌋ (r ᴸ L))))) (renᵀ² r c L))))))))
  where
  Y = subTy (extS (single (⌊ j ⌋ L))) (⌊ c ⌋ᵀ² L)
  pt : ∀ x → (r ᵣ∘ₛ single (⌊ t ⌋ L)) x ≡ (single (⌊ t ⌋ (r ᴸ L)) ₛ∘ᵣ extR r) x
  pt vz     = ren⌊⌋ r t L
  pt (vs x) = refl
  pt₂ : ∀ x → (extR r ᵣ∘ₛ extS (single (⌊ j ⌋ L))) x ≡ (extS (single (⌊ j ⌋ (r ᴸ L))) ₛ∘ᵣ extR (extR r)) x
  pt₂ vz          = refl
  pt₂ (vs vz)     = trans (wk-ren r (⌊ j ⌋ L)) (cong wk (ren⌊⌋ r j L))
  pt₂ (vs (vs x)) = refl

------------------------------------------------------------------------
-- 4. ★ Soundness: each type-level function, by its own views.
------------------------------------------------------------------------

T-eval   : (k n : ℕ) (ρ : Env Γ) (A : RTy Γ) (L : Lv Δ) → Scᵉ n ρ → subTy (⌊ ρ ⌋ᵉ L) A ≅ᵀ ⌊ evalᵀ k n ρ A ⌋ᵀ L
T-instᵀ  : (k n : ℕ) (c : TClo) (v : Val) (L : Lv Δ) → ScTᶜ n c → Sc n v →
           subTy (single (⌊ v ⌋ L)) (⌊ c ⌋ᵀᶜ L) ≅ᵀ ⌊ instᵀ k n c v ⌋ᵀ L
T-instᵀ₂ : (k n : ℕ) (c : TClo₂) (j t : Val) (L : Lv Δ) → ScT² n c → Sc n j → Sc n t →
           subTy (single (⌊ t ⌋ L)) (subTy (extS (single (⌊ j ⌋ L))) (⌊ c ⌋ᵀ² L)) ≅ᵀ ⌊ instᵀ₂ k n c j t ⌋ᵀ L
T-tElS   : (k n : ℕ) (c : Val) (L : Lv Δ) → Sc n c → El (⌊ c ⌋ L) ≅ᵀ ⌊ tElS k n c ⌋ᵀ L
T-tElF   : (k n : ℕ) {c : Val} (w : CodeV c) (L : Lv Δ) → Sc n c → El (⌊ c ⌋ L) ≅ᵀ ⌊ tElF k n w ⌋ᵀ L
T-tHomS  : (k n : ℕ) (A : TVal) (a b : Val) (L : Lv Δ) → ScT n A → Sc n a → Sc n b →
           Hom (⌊ A ⌋ᵀ L) (⌊ a ⌋ L) (⌊ b ⌋ L) ≅ᵀ ⌊ tHomS k n A a b ⌋ᵀ L
T-tHomF  : (k n : ℕ) {A : TVal} (w : TyV A) (a b : Val) (L : Lv Δ) → ScT n A → Sc n a → Sc n b →
           Hom (⌊ A ⌋ᵀ L) (⌊ a ⌋ L) (⌊ b ⌋ L) ≅ᵀ ⌊ tHomF k n w a b ⌋ᵀ L
T-tHomNat : (k : ℕ) (a b : Val) (L : Lv Δ) → Hom Nat (⌊ a ⌋ L) (⌊ b ⌋ L) ≅ᵀ ⌊ tHomNat k a b ⌋ᵀ L
T-tHomA  : (k : ℕ) {a : Val} (w : NatV a) (b : Val) (L : Lv Δ) → Hom Nat (⌊ a ⌋ L) (⌊ b ⌋ L) ≅ᵀ ⌊ tHomA k w b ⌋ᵀ L
T-tHomB  : (k : ℕ) (m : Val) {b : Val} (w : NatV b) (L : Lv Δ) → Hom Nat (nsuc (⌊ m ⌋ L)) (⌊ b ⌋ L) ≅ᵀ ⌊ tHomB k m w ⌋ᵀ L
T-tDIhS  : (k n : ℕ) (D : Val) (M : TClo₂) (C p : Val) (L : Lv Δ) → Sc n D → ScT² n M → Sc n C → Sc n p →
           DIh (⌊ D ⌋ L) (⌊ M ⌋ᵀ² L) (⌊ C ⌋ L) (⌊ p ⌋ L) ≅ᵀ ⌊ tDIhS k n D M C p ⌋ᵀ L
T-tDIhF  : (k n : ℕ) (D : Val) (M : TClo₂) {C : Val} (w : DescV C) (p : Val) (L : Lv Δ) →
           Sc n D → ScT² n M → Sc n C → Sc n p →
           DIh (⌊ D ⌋ L) (⌊ M ⌋ᵀ² L) (⌊ C ⌋ L) (⌊ p ⌋ L) ≅ᵀ ⌊ tDIhF k n D M w p ⌋ᵀ L

-- evaluation: congruences, then the smart eliminators
T-eval k n ρ base          L s = crflᵀ
T-eval k n ρ U             L s = crflᵀ
T-eval k n ρ (Π A B)       L s = Π≅ (T-eval k n ρ A L s) crflᵀ
T-eval k n ρ (Σ' A B)      L s = Σ≅ (T-eval k n ρ A L s) crflᵀ
T-eval k n ρ (El c)        L s = El≅ (S-eval k n ρ c L s) ⨾ᵀ T-tElS k n (eval k n ρ c) L (sc-eval k n ρ c s)
T-eval k n ρ (Hom A a b)   L s =
  Hom≅ (T-eval k n ρ A L s) (S-eval k n ρ a L s) (S-eval k n ρ b L s)
  ⨾ᵀ T-tHomS k n (evalᵀ k n ρ A) (eval k n ρ a) (eval k n ρ b) L (sc-evalᵀ k n ρ A s) (sc-eval k n ρ a s) (sc-eval k n ρ b s)
T-eval k n ρ Unit          L s = crflᵀ
T-eval k n ρ Nat           L s = crflᵀ
T-eval k n ρ (Id A a b)    L s = Id≅ (T-eval k n ρ A L s) (S-eval k n ρ a L s) (S-eval k n ρ b L s)
T-eval k n ρ (IMu I D i)   L s = IMu≅ (S-eval k n ρ I L s) (S-eval k n ρ D L s) (S-eval k n ρ i L s)
T-eval k n ρ (Desc I)      L s = Desc≅ (S-eval k n ρ I L s)
T-eval k n ρ (DIh D M C p) L s =
  DIh≅ (S-eval k n ρ D L s) crflᵀ (S-eval k n ρ C L s) (S-eval k n ρ p L s)
  ⨾ᵀ T-tDIhS k n (eval k n ρ D) (tclo₂ ρ M) (eval k n ρ C) (eval k n ρ p) L (sc-eval k n ρ D s) s (sc-eval k n ρ C s) (sc-eval k n ρ p s)
T-eval k n ρ (Fin t)       L s = Fin≅ (S-eval k n ρ t L s)

-- a closure instantiated
T-instᵀ zero    n c v L sc sv = crflᵀ
T-instᵀ (suc k) n (tclo ρ B) v L sc sv =
  ≡→≅ᵀ (trans (subTy-subTy B) (subTy-cong pt B)) ⨾ᵀ T-eval k n (ρ , v) B L (sc , sv)
  where
  pt : ∀ x → (single (⌊ v ⌋ L) ∘ₛ extS (⌊ ρ ⌋ᵉ L)) x ≡ ⌊ ρ , v ⌋ᵉ L x
  pt vz     = refl
  pt (vs x) = wk-cancel-tm (⌊ v ⌋ L) (⌊ ρ ⌋ᵉ L x)
T-instᵀ (suc k) n (tcloK A) v L sc sv = ≡→≅ᵀ (wk-cancel (⌊ v ⌋ L) (⌊ A ⌋ᵀ L))
T-instᵀ (suc k) n (tcloEl d) v L sc sv =
  El≅ (S-inst k n d v L sc sv) ⨾ᵀ T-tElS k n (inst k n d v) L (sc-inst k n d v sc sv)
T-instᵀ (suc k) n (tcloHom B f g) v L (sB , (sf , sg)) sv =
  ≡→≅ᵀ (cong₂ (λ X Y → Hom (subTy (single (⌊ v ⌋ L)) (⌊ B ⌋ᵀᶜ L)) X Y)
              (cong (λ x → app x (⌊ v ⌋ L)) (wk-cancel-tm (⌊ v ⌋ L) (⌊ f ⌋ L)))
              (cong (λ x → app x (⌊ v ⌋ L)) (wk-cancel-tm (⌊ v ⌋ L) (⌊ g ⌋ L))))
  ⨾ᵀ Hom≅ (T-instᵀ k n B v L sB sv) (S-vApp k n f v L sf sv) (S-vApp k n g v L sg sv)
  ⨾ᵀ T-tHomS k n (instᵀ k n B v) (vApp k n f v) (vApp k n g v) L (sc-instᵀ k n B v sB sv) (sc-vApp k n f v sf sv) (sc-vApp k n g v sg sv)
T-instᵀ (suc k) n (tcloDIh D M C p) v L (sD , (sM , (sC , sp))) sv =
  ≡→≅ᵀ (cong₂ (λ X Y → X Y)
          (cong₂ (λ X Y → X Y)
             (cong₂ DIh (wk-cancel-tm (⌊ v ⌋ L) (⌊ D ⌋ L)) eM)
             (wk-cancel-tm (⌊ v ⌋ L) (⌊ C ⌋ L)))
          (cong snd (wk-cancel-tm (⌊ v ⌋ L) (⌊ p ⌋ L))))
  ⨾ᵀ DIh≅ crfl crflᵀ crfl (S-vSnd k p L)
  ⨾ᵀ T-tDIhS k n D M C (vSnd k p) L sD sM sC (sc-vSnd k n p sp)
  where
  X = ⌊ M ⌋ᵀ² L
  pt : ∀ x → (extS (extS (single (⌊ v ⌋ L))) ₛ∘ᵣ extR (extR vs)) x ≡ idₛ x
  pt vz          = refl
  pt (vs vz)     = refl
  pt (vs (vs x)) = refl
  eM : subTy (extS (extS (single (⌊ v ⌋ L)))) (renTy (extR (extR vs)) X) ≡ X
  eM = trans (subTy-renTy X) (trans (subTy-cong pt X) (subTy-id X))

T-instᵀ₂ zero    n c j t L sc sj st = crflᵀ
T-instᵀ₂ (suc k) n (tclo₂ ρ M) j t L sc sj st =
  ≡→≅ᵀ (trans (cong (subTy (single (⌊ t ⌋ L))) (subTy-subTy M))
         (trans (subTy-subTy M) (subTy-cong pt M)))
  ⨾ᵀ T-eval k n ((ρ , j) , t) M L ((sc , sj) , st)
  where
  σ = ⌊ ρ ⌋ᵉ L
  pt : ∀ x → (single (⌊ t ⌋ L) ∘ₛ (extS (single (⌊ j ⌋ L)) ∘ₛ extS (extS σ))) x ≡ ⌊ (ρ , j) , t ⌋ᵉ L x
  pt vz          = refl
  pt (vs vz)     = wk-cancel-tm (⌊ t ⌋ L) (⌊ j ⌋ L)
  pt (vs (vs x)) =
    trans (cong (subTm (single (⌊ t ⌋ L)))
                (trans (subTm-renTm (renTm vs (σ x)))
                       (trans (subTm-renTm (σ x)) (trans (subTm-cong (λ _ → refl) (σ x)) (subTm-var vs (σ x))))))
          (wk-cancel-tm (⌊ t ⌋ L) (σ x))

-- El decodes a code
T-tElS k n c L s = El≅ (S-force k c L) ⨾ᵀ T-tElF k n (codeV (force k c)) L (sc-force k n c s)

T-tElF k       n cbase        L s = credᵀ El-⌜base⌝
T-tElF zero    n (cΠ c d)     L s = crflᵀ
T-tElF (suc k) n (cΠ c d)     L (sc , sd) = credᵀ (El-⌜Π⌝ _ _) ⨾ᵀ Π≅ (T-tElS k n c L sc) crflᵀ
T-tElF zero    n (cΣ c d)     L s = crflᵀ
T-tElF (suc k) n (cΣ c d)     L (sc , sd) = credᵀ (El-⌜Σ⌝ _ _) ⨾ᵀ Σ≅ (T-tElS k n c L sc) crflᵀ
T-tElF zero    n (cHom c a b) L s = crflᵀ
T-tElF (suc k) n (cHom c a b) L (sc , (sa , sb)) =
  credᵀ (El-⌜Hom⌝ _ _ _) ⨾ᵀ Hom≅ (T-tElS k n c L sc) crfl crfl
  ⨾ᵀ T-tHomS k n (tElS k n c) a b L (sc-tElS k n c sc) sa sb
T-tElF zero    n (cId c a b)  L s = crflᵀ
T-tElF (suc k) n (cId c a b)  L (sc , (sa , sb)) = credᵀ (El-⌜Id⌝ _ _ _) ⨾ᵀ Id≅ (T-tElS k n c L sc) crfl crfl
T-tElF k       n cNat         L s = credᵀ El-⌜Nat⌝
T-tElF k       n (cIMu I D i) L s = credᵀ El-⌜IMu⌝
T-tElF k       n (cFin t)     L s = credᵀ El-⌜Fin⌝
T-tElF k       n cUnit        L s = credᵀ El-⌜Unit⌝
T-tElF k       n (cOther c)   L s = crflᵀ

-- Hom computes at Nat, U and Π
T-tHomS k n A a b = T-tHomF k n (tyV A) a b

T-tHomF k       n tvNat       a b L sA sa sb = T-tHomNat k a b L
T-tHomF zero    n tvU         c d L sA sc sd = crflᵀ
T-tHomF (suc k) n tvU         c d L sA sc sd =
  credᵀ (Hom-U _ _) ⨾ᵀ Π≅ (T-tElS k n c L sc) (≅ᵀ-ren vs (T-tElS k n d L sd))
T-tHomF k       n (tvΠ A B)   f g L sA sf sg = credᵀ (Hom-Π _ _ _ _)
T-tHomF k       n (tvOther A) a b L sA sa sb = crflᵀ

T-tHomNat k a b L = Hom≅ crflᵀ (S-force k a L) crfl ⨾ᵀ T-tHomA k (natV (force k a)) b L

T-tHomA k isZero     b L = credᵀ (Hom-Nat-z _)
T-tHomA k (isSuc m)  b L = Hom≅ crflᵀ crfl (S-force k b L) ⨾ᵀ T-tHomB k m (natV (force k b)) L
T-tHomA k (notNat a) b L = crflᵀ

T-tHomB k       m isZero     L = credᵀ (Hom-Nat-sz _)
T-tHomB zero    m (isSuc b)  L = crflᵀ
T-tHomB (suc k) m (isSuc b)  L = credᵀ (Hom-Nat-ss _ _) ⨾ᵀ T-tHomNat k m b L
T-tHomB k       m (notNat b) L = crflᵀ

-- the hypotheses' type computes on the telescope head
T-tDIhS k n D M C p L sD sM sC sp =
  DIh≅ crfl crflᵀ (S-force k C L) crfl ⨾ᵀ T-tDIhF k n D M (descV (force k C)) p L sD sM (sc-force k n C sC) sp

T-tDIhF k       n D M isDι        p L sD sM sC sp = credᵀ (DIh-ι _ _ _)
T-tDIhF zero    n D M (isDσ S f)  p L sD sM sC sp = crflᵀ
T-tDIhF (suc k) n D M (isDσ S f)  p L sD sM (sS , sf) sp =
  credᵀ (DIh-σ _ _ _ _ _)
  ⨾ᵀ DIh≅ crfl crflᵀ (≅app crfl (S-vFst k p L) ⨾ S-vApp k n f (vFst k p) L sf (sc-vFst k n p sp)) (S-vSnd k p L)
  ⨾ᵀ T-tDIhS k n D M (vApp k n f (vFst k p)) (vSnd k p) L sD sM
             (sc-vApp k n f (vFst k p) sf (sc-vFst k n p sp)) (sc-vSnd k n p sp)
T-tDIhF zero    n D M (isDρ j C)  p L sD sM sC sp = crflᵀ
T-tDIhF (suc k) n D M (isDρ j C)  p L sD sM (sj , sC) sp =
  credᵀ (DIh-ρ _ _ _ _ _)
  ⨾ᵀ Σ≅ (sub1≅ᵀ (subTy (extS (single (⌊ j ⌋ L))) (⌊ M ⌋ᵀ² L)) (S-vFst k p L)
          ⨾ᵀ T-instᵀ₂ k n M j (vFst k p) L sM sj (sc-vFst k n p sp))
        crflᵀ
T-tDIhF k       n D M (notDesc C) p L sD sM sC sp = crflᵀ

------------------------------------------------------------------------
-- 5. A type closure at a fresh level, readback, and the theorem.
------------------------------------------------------------------------

private
  ≠suc : (n : ℕ) → (n == suc n) ≡ false
  ≠suc zero    = refl
  ≠suc (suc n) = ≠suc n

  lt-two : (n : ℕ) → (n < suc (suc n)) ≡ true
  lt-two zero    = refl
  lt-two (suc n) = lt-two n

  up2 : (n : ℕ) → Up n (suc (suc n))
  up2 n l p = lt-suc l (suc n) (lt-suc l n p)

  bind2-wk : (m : ℕ) (L : Lv Δ) → Below m (bindL (suc m) (bindL m L)) (vs ᴸ (vs ᴸ L))
  bind2-wk m L l p = trans (bind-wk (suc m) (bindL m L) l (lt-suc l m p)) (cong wk (bind-wk m L l p))

  -- the two-binder reading cancelled by its two fresh variables
  sub2-wk2ᵀ : (X : RTy ((Δ ∙) ∙)) →
              subTy (single (var vz)) (subTy (extS (single (var (vs vz))))
                (renTy (extR (extR vs)) (renTy (extR (extR vs)) X))) ≡ X
  sub2-wk2ᵀ X =
    trans (cong (subTy (single (var vz))) (trans (subTy-renTy (renTy (extR (extR vs)) X)) (subTy-renTy X)))
          (trans (subTy-subTy X) (trans (subTy-cong pt X) (subTy-id X)))
    where
    pt : ∀ x → (single (var vz) ∘ₛ ((extS (single (var (vs vz))) ₛ∘ᵣ extR (extR vs)) ₛ∘ᵣ extR (extR vs))) x ≡ idₛ x
    pt vz          = refl
    pt (vs vz)     = refl
    pt (vs (vs x)) = refl

  sub-vz-wkᵀ : (X : RTy (Δ ∙)) → subTy (single (var vz)) (renTy (extR vs) X) ≡ X
  sub-vz-wkᵀ X = trans (subTy-renTy X) (trans (subTy-cong pt X) (subTy-id X))
    where
    pt : ∀ x → (single (var vz) ₛ∘ᵣ extR vs) x ≡ idₛ x
    pt vz     = refl
    pt (vs x) = refl

T-freshᵀ : (k m : ℕ) (c : TClo) (L : Lv Δ) → ScTᶜ m c → ⌊ c ⌋ᵀᶜ L ≅ᵀ ⌊ instᵀ k (suc m) c (vvar m) ⌋ᵀ (bindL m L)
T-freshᵀ k m c L sc =
  ≡→≅ᵀ (sym eq) ⨾ᵀ T-instᵀ k (suc m) c (vvar m) (bindL m L) (monoTᶜ c (up-suc m) sc) (lt-self m)
  where
  eq : subTy (single (⌊ vvar m ⌋ (bindL m L))) (⌊ c ⌋ᵀᶜ (bindL m L)) ≡ ⌊ c ⌋ᵀᶜ L
  eq = trans (cong₂ (λ X Y → subTy (single X) Y) (bind-here m L)
                    (trans (agreeᵀᶜ m c (bind-wk m L) sc) (sym (renᵀᶜ vs c L))))
             (sub-vz-wkᵀ (⌊ c ⌋ᵀᶜ L))

T-freshᵀ₂ : (k m : ℕ) (c : TClo₂) (L : Lv Δ) → ScT² m c →
            ⌊ c ⌋ᵀ² L ≅ᵀ ⌊ instᵀ₂ k (suc (suc m)) c (vvar m) (vvar (suc m)) ⌋ᵀ (bindL (suc m) (bindL m L))
T-freshᵀ₂ k m c L sc =
  ≡→≅ᵀ (sym eq)
  ⨾ᵀ T-instᵀ₂ k (suc (suc m)) c (vvar m) (vvar (suc m)) L″ (monoT² c (up2 m) sc) (lt-two m) (lt-self (suc m))
  where
  L″ = bindL (suc m) (bindL m L)
  e₀ : ⌊ vvar m ⌋ L″ ≡ var (vs vz)
  e₀ = trans (cong (λ b → pickTm b (var vz) (wk (bindL m L m))) (≠suc m)) (cong wk (bind-here m L))
  eq : subTy (single (⌊ vvar (suc m) ⌋ L″)) (subTy (extS (single (⌊ vvar m ⌋ L″))) (⌊ c ⌋ᵀ² L″)) ≡ ⌊ c ⌋ᵀ² L
  eq = trans (cong₂ (λ X Y → subTy (single X) (subTy (extS (single Y)) (⌊ c ⌋ᵀ² L″))) (bind-here (suc m) (bindL m L)) e₀)
       (trans (cong (λ Z → subTy (single (var vz)) (subTy (extS (single (var (vs vz)))) Z))
                    (trans (agreeᵀ² m c (bind2-wk m L) sc)
                           (trans (sym (renᵀ² vs c (vs ᴸ L))) (cong (renTy (extR (extR vs))) (sym (renᵀ² vs c L))))))
              (sub2-wk2ᵀ (⌊ c ⌋ᵀ² L)))

T-rbᵀ  : (u : Bool) (k : ℕ) (Γ : Cx) (A : TVal) → ScT (len Γ) A → ⌊ A ⌋ᵀ (lvl Γ) ≅ᵀ rbᵀ u k Γ A
T-rbᵀᶜ : (u : Bool) (k : ℕ) (Γ : Cx) (c : TClo) → ScTᶜ (len Γ) c → ⌊ c ⌋ᵀᶜ (lvl Γ) ≅ᵀ rbᵀᶜ u k Γ c
T-rbᵀ₂ : (u : Bool) (k : ℕ) (Γ : Cx) (c : TClo₂) → ScT² (len Γ) c → ⌊ c ⌋ᵀ² (lvl Γ) ≅ᵀ rbᵀ₂ u k Γ c

T-rbᵀ u k Γ tbase s = crflᵀ
T-rbᵀ u k Γ tU s = crflᵀ
T-rbᵀ u k Γ tUnit s = crflᵀ
T-rbᵀ u k Γ tNat s = crflᵀ
T-rbᵀ u k Γ (tΠ A B) (sA , sB) = Π≅ (T-rbᵀ u k Γ A sA) (T-rbᵀᶜ u k Γ B sB)
T-rbᵀ u k Γ (tΣ A B) (sA , sB) = Σ≅ (T-rbᵀ u k Γ A sA) (T-rbᵀᶜ u k Γ B sB)
T-rbᵀ u k Γ (tEl c) s = El≅ (S-rb u k Γ c s)
T-rbᵀ u k Γ (tHom A a b) (sA , (sa , sb)) = Hom≅ (T-rbᵀ u k Γ A sA) (S-rb u k Γ a sa) (S-rb u k Γ b sb)
T-rbᵀ u k Γ (tId A a b) (sA , (sa , sb)) = Id≅ (T-rbᵀ u k Γ A sA) (S-rb u k Γ a sa) (S-rb u k Γ b sb)
T-rbᵀ u k Γ (tIMu I D i) (sI , (sD , si)) = IMu≅ (S-rb u k Γ I sI) (S-rb u k Γ D sD) (S-rb u k Γ i si)
T-rbᵀ u k Γ (tDesc I) s = Desc≅ (S-rb u k Γ I s)
T-rbᵀ u k Γ (tDIh D M C p) (sD , (sM , (sC , sp))) =
  DIh≅ (S-rb u k Γ D sD) (T-rbᵀ₂ u k Γ M sM) (S-rb u k Γ C sC) (S-rb u k Γ p sp)
T-rbᵀ u k Γ (tFin t) s = Fin≅ (S-rb u k Γ t s)
T-rbᵀ u zero    Γ (tinst c v) s = crflᵀ
T-rbᵀ u (suc k) Γ (tinst c v) (sc , sv) =
  T-instᵀ k (len Γ) c v (lvl Γ) sc sv ⨾ᵀ T-rbᵀ u k Γ (instᵀ k (len Γ) c v) (sc-instᵀ k (len Γ) c v sc sv)
T-rbᵀ u zero    Γ (tinst₂ c j t) s = crflᵀ
T-rbᵀ u (suc k) Γ (tinst₂ c j t) (sc , (sj , st)) =
  T-instᵀ₂ k (len Γ) c j t (lvl Γ) sc sj st ⨾ᵀ T-rbᵀ u k Γ (instᵀ₂ k (len Γ) c j t) (sc-instᵀ₂ k (len Γ) c j t sc sj st)

T-rbᵀᶜ u zero    Γ c s = crflᵀ
T-rbᵀᶜ u (suc k) Γ c s =
  T-freshᵀ k (len Γ) c (lvl Γ) s
  ⨾ᵀ T-rbᵀ u k (Γ ∙) (instᵀ k (suc (len Γ)) c (vvar (len Γ)))
           (sc-instᵀ k (suc (len Γ)) c (vvar (len Γ)) (monoTᶜ c (up-suc (len Γ)) s) (lt-self (len Γ)))

T-rbᵀ₂ u zero    Γ c s = crflᵀ
T-rbᵀ₂ u (suc k) Γ c s =
  T-freshᵀ₂ k (len Γ) c (lvl Γ) s
  ⨾ᵀ T-rbᵀ u k ((Γ ∙) ∙) (instᵀ₂ k (suc (suc (len Γ))) c (vvar (len Γ)) (vvar (suc (len Γ))))
           (sc-instᵀ₂ k (suc (suc (len Γ))) c (vvar (len Γ)) (vvar (suc (len Γ))) (monoT² c (up2 (len Γ)) s)
                      (lt-two (len Γ)) (lt-self (suc (len Γ))))

------------------------------------------------------------------------
-- ★★ THE THEOREM: the evaluator's normal form of a type is convertible
--     with the type — at every fuel.
------------------------------------------------------------------------

nbeᵀ-sound : (k : ℕ) (A : RTy Γ) → A ≅ᵀ nbeᵀ k A
nbeᵀ-sound {Γ} k A =
  ≡→≅ᵀ (trans (sym (subTy-id A)) (subTy-cong (λ x → sym (idEnv-read Γ x)) A))
  ⨾ᵀ T-eval k (len Γ) (idEnv Γ) A (lvl Γ) (sc-idEnv Γ)
  ⨾ᵀ T-rbᵀ true k Γ (evalᵀ k (len Γ) (idEnv Γ) A) (sc-evalᵀ k (len Γ) (idEnv Γ) A (sc-idEnv Γ))
