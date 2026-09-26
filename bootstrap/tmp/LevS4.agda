{-# OPTIONS --safe #-}
-- SPIKE-LEVITATION S4 — the TAG TYPE, and the constructor LIST as SUGAR.
--
-- The kernel keeps ONE telescope per datatype (S3).  The surface — and the
-- examples and the Knot — keep writing a constructor LIST `C₀ … C_{c-1}`
-- and one method PER constructor.  This spike elaborates the list form into
-- the one-telescope form and checks the elaboration is FAITHFUL:
--
--   Dₗ Cs          = dσ (enum c) (λ t. switch t Cs)      -- the datatype
--   conₗ k p       = con (tag k , p)                      -- constructor k
--   methₗ ms       = λ i q. split q (λ t p h. switch t (mₖ i) p h)
--
--   (a) ⊢Dₗ    — each Cₖ ∷ Desc  ⇒  Dₗ Cs ∷ Desc
--   (b) ⊢conₗ  — p ∷ pay D Cₖ i  ⇒  conₗ k p ∷ mu D i
--   (c) ⊢methₗ — each mₖ at ITS constructor's method type ⇒ methₗ ∷ MethTy D M
--   (d) ιₗ     — ielim D M methₗ i (conₗ k p) ⟶* mₖ i p (ih …)   (derived ι)
--   (e) CANONICITY: a well-typed tag is in range, so `switch` on it FIRES —
--       exactly what the list form lost (`lkp dnil k` was stuck, S3 note).
--
-- `methₗ` needs Σ-INDUCTION (`split`): the kernel has no Σ-η, and with only
-- fst/snd the rebuilt constructor `con (fst q , snd q)` is not `con q`.
module tmp.LevS4 where

open import tmp.LevSyn
open import tmp.LevS3
open Syntax Op ar
open import Agda.Builtin.Sigma using ( Σ; _,_ )

fsN : (k : Nat) {n : Nat} → Fin n → Fin (k + n)
fsN zero    x = x
fsN (suc k) x = fs (fsN k x)

W : (k : Nat) {n : Nat} → Tm n → Tm (k + n)
W k = ren (fsN k)

WA : (k : Nat) {n : Nat} {ks : List Nat} → Args n ks → Args (k + n) ks
WA k = renA (fsN k)

≡-tgt : t ⟶ u → u ≡ t' → t ⟶ t'
≡-tgt s refl = s

≡-src : t ⟶ u → t ≡ t' → t' ⟶ u
≡-src s refl = s

-- ═══ the elaboration ═════════════════════════════════════════════════════
fₗ : {c : Nat} → Args n (rep c) → Tm n
fₗ {c = c} Cs = lam (switch c Desc (var fz) (WA 1 Cs))

Dₗ : {c : Nat} → Args n (rep c) → Tm n
Dₗ {c = c} Cs = dσ (enum c) (fₗ Cs)

conₗ : Nat → Tm n → Tm n
conₗ k p = con (pair (tag k) p)

-- a weakening cancelled by the substitution that instantiates it
cancelA : {ks : List Nat} (a : Tm n) (as : Args n ks) → subA (sg a) (WA 1 as) ≡ as
cancelA a as = trans (subA-ren (sg a) fs as) (trans (subA-cong (λ _ → refl) as) (subA-var as))

-- ★ the constructor lookup IS a conversion: `f (tag k)` computes to Cₖ
switchConv : {c k : Nat} {Cs : Args n (rep c)} {C : Tm n} →
             Nth Cs k C → app (fₗ Cs) (tag k) ≃ C
switchConv {c = c} {k = k} {Cs = Cs} nt =
  ≃-trans (≃-step (≡-tgt β (cong (switch c Desc (tag k)) (cancelA (tag k) Cs))))
          (≃-step (desc (switch-ι nt)))

-- ═══ (e) CANONICITY of tags ══════════════════════════════════════════════
substLt : {k c c' : Nat} → c ≡ c' → Lt k c → Lt k c'
substLt refl l = l

tag-lt : (enum-inj : ∀ {n} {c c' : Nat} → _≃_ {n} (El (enum c)) (El (enum c')) → c ≡ c') →
         {k c : Nat} → Γ ⊢ tag k ∷ El (enum c) → Lt k c
tag-lt enum-inj d with inv-tag d
... | c' , q , l = substLt (enum-inj q) l

nth-total : {k c : Nat} → Lt k c → (ms : Args n (rep c)) → Σ (Tm n) (Nth ms k)
nth-total lt-z     (x ∷ xs) = x , nth-z
nth-total (lt-s l) (x ∷ xs) with nth-total l xs
... | y , nt = y , nth-s nt

-- ★ a well-typed switch on a tag ALWAYS fires — no stuck closed lookup
switch-fires : (enum-inj : ∀ {n} {c c' : Nat} → _≃_ {n} (El (enum c)) (El (enum c')) → c ≡ c') →
               {k c : Nat} → Γ ⊢ tag k ∷ El (enum c) →
               (P : Tm (suc n)) (ms : Args n (rep c)) →
               Σ (Tm n) λ m → switch c P (tag k) ms ⟶ m
switch-fires enum-inj d P ms with nth-total (tag-lt enum-inj d) ms
... | m , nt = m , desc (switch-ι nt)

module Elab
  (wk-⊢ : ∀ {n} {Γ : Ctx n} {t A B} → Γ ⊢ t ∷ A → (Γ ▹ B) ⊢ wk t ∷ wk A)
  where

  wkCases : {k c : Nat} {Cs : Args n (rep c)} → Cases Γ Desc k Cs → Cases (Γ ▹ B) Desc k (WA 1 Cs)
  wkCases cs-nil         = cs-nil
  wkCases (cs-cons d cs) = cs-cons (wk-⊢ d) (wkCases cs)

  -- (a) each constructor telescope is a description ⇒ so is the datatype
  ⊢Dₗ : {c : Nat} {Cs : Args n (rep c)} → Cases Γ Desc 0 Cs → Γ ⊢ Dₗ Cs ∷ Desc
  ⊢Dₗ cs = t-dσ t-enum (t-lam (t-switch t-var (wkCases cs)))

  -- (b) constructor k, from a payload of ITS telescope
  ⊢conₗ : {c k : Nat} {Cs : Args n (rep c)} {C : Tm n} →
          Γ ⊢ Dₗ Cs ∷ Desc → Γ ⊢ i ∷ El ix → Lt k c → Nth Cs k C →
          Γ ⊢ p ∷ El (pay (Dₗ Cs) C i) → Γ ⊢ conₗ k p ∷ El (mu (Dₗ Cs) i)
  ⊢conₗ {i = i} {c = c} {k = k} {Cs = Cs} dD di lt nt dp =
    let D  = Dₗ Cs
        f  = fₗ Cs
        p1 = t-conv dp (≃-sym (≃-map (λ x → El (pay D x i))
                                     (λ s → under (here (under (there (here s)))))
                                     (switchConv nt)))
        p2 = ≡-ty p1 (sym (cong₃ (λ X Y Z → El (pay X (app Y (tag k)) Z))
                                 (c1 (tag k) D) (c1 (tag k) f) (c1 (tag k) i)))
    in t-con dD di (t-conv (t-pair (t-tag lt) p2) (≃-sym (⟶ₑ pay-σ)))

-- ═══ (c) the ONE method, from one method per constructor ═════════════════
mapA : {m m' c : Nat} → (Tm m → Tm m') → Args m (rep c) → Args m' (rep c)
mapA {c = zero}  g []       = []
mapA {c = suc c} g (x ∷ xs) = g x ∷ mapA g xs

nth-map : {m m' c k : Nat} (g : Tm m → Tm m') {as : Args m (rep c)} {x : Tm m} →
          Nth as k x → Nth (mapA g as) k (g x)
nth-map g nth-z      = nth-z
nth-map g (nth-s nt) = nth-s (nth-map g nt)

nth-ren : {m m' c k : Nat} (ρ : Fin m → Fin m') {as : Args m (rep c)} {x : Tm m} →
          Nth as k x → Nth (renA ρ as) k (ren ρ x)
nth-ren ρ nth-z      = nth-z
nth-ren ρ (nth-s nt) = nth-s (nth-ren ρ nt)

wkN : (k : Nat) → Tm n → Tm (k + n)
wkN zero    t = t
wkN (suc k) t = wk (wkN k t)

rN : (k : Nat) (t : Tm n) → wkN k t ≡ W k t
rN zero    t = sym (trans (sym (ren-as-sub (λ x → x) t)) (sub-var t))
rN (suc k) t = trans (cong wk (rN k t)) (renRen fs (fsN k) (fsN (suc k)) (λ _ → refl) t)

subRen2 : {l m m' n : Nat} (σ : Fin m' → Tm n) (ρ₁ : Fin m → Fin m') (ρ₂ : Fin l → Fin m)
          (ρ' : Fin l → Fin n) → (∀ x → σ (ρ₁ (ρ₂ x)) ≡ var (ρ' x)) → (t : Tm l) →
          sub σ (ren ρ₁ (ren ρ₂ t)) ≡ ren ρ' t
subRen2 σ ρ₁ ρ₂ ρ' h t = trans (cong (sub σ) (ren-ren ρ₁ ρ₂ t)) (subRen σ _ ρ' h t)

subst : {X : Set} (P : X → Set) {x y : X} → x ≡ y → P x → P y
subst P refl p = p

≡-tm : Γ ⊢ t ∷ A → t ≡ t' → Γ ⊢ t' ∷ A
≡-tm d refl = d

-- the per-constructor method type: `con (tag k , p)` in the conclusion
MethK : Tm n → Tm n → Tm n → Nat → Tm n
MethK D M C k =
  Pi (El ix)
     (Pi (El (pay (wk D) (wk C) (var fz)))
         (Pi (El (ihTy (ren w2 D) (ren w2 M) (ren w2 C) (var fz)))
             (El (app (app (ren w3 M) (var (fs (fs fz)))) (con (pair (tag k) (var (fs fz))))))))

-- the concrete selector computes to `switch` under any renaming
fₗ-β : {c : Nat} (Cs : Args n (rep c)) {m : Nat} (ρ : Fin n → Fin m) (t : Tm m) →
       app (ren ρ (fₗ Cs)) t ≃ switch c Desc t (renA ρ Cs)
fₗ-β {c = c} Cs ρ t =
  ≃-step (≡-tgt β (cong (switch c Desc t)
    (trans (cong (subA (sg t)) (renRenA (ext ρ) fs (λ x → fs (ρ x)) (λ _ → refl) Cs))
           (subRenA (sg t) (λ x → fs (ρ x)) ρ (λ _ → refl) Cs))))

cong4 : {A₁ A₂ A₃ A₄ B : Set} (F : A₁ → A₂ → A₃ → A₄ → B)
        {a₁ b₁ : A₁} {a₂ b₂ : A₂} {a₃ b₃ : A₃} {a₄ b₄ : A₄} →
        a₁ ≡ b₁ → a₂ ≡ b₂ → a₃ ≡ b₃ → a₄ ≡ b₄ → F a₁ a₂ a₃ a₄ ≡ F b₁ b₂ b₃ b₄
cong4 F refl refl refl refl = refl

cong6 : {A₁ A₂ A₃ A₄ A₅ A₆ B : Set} (F : A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → B)
        {a₁ b₁ : A₁} {a₂ b₂ : A₂} {a₃ b₃ : A₃} {a₄ b₄ : A₄} {a₅ b₅ : A₅} {a₆ b₆ : A₆} →
        a₁ ≡ b₁ → a₂ ≡ b₂ → a₃ ≡ b₃ → a₄ ≡ b₄ → a₅ ≡ b₅ → a₆ ≡ b₆ →
        F a₁ a₂ a₃ a₄ a₅ a₆ ≡ F b₁ b₂ b₃ b₄ b₅ b₆
cong6 F refl refl refl refl refl refl = refl

infixr 5 _◅_
data _⟶*_ {n : Nat} : Tm n → Tm n → Set where
  ε*  : t ⟶* t
  _◅_ : t ⟶ u → u ⟶* t' → t ⟶* t'

nth-sub : {m m' c k : Nat} (σ : Fin m → Tm m') {as : Args m (rep c)} {x : Tm m} →
          Nth as k x → Nth (subA σ as) k (sub σ x)
nth-sub σ nth-z      = nth-z
nth-sub σ (nth-s nt) = nth-s (nth-sub σ nt)

sub3 : {l m₁ m₂ n : Nat} (a : Fin m₂ → Tm n) (b : Fin m₁ → Tm m₂) (c : Fin l → Tm m₁) (t : Tm l) →
       sub a (sub b (sub c t)) ≡ sub (λ x → sub a (sub b (c x))) t
sub3 a b c t = trans (cong (sub a) (sub-sub b c t)) (sub-sub a (λ x → sub b (c x)) t)

sub4 : {l m₁ m₂ m₃ n : Nat} (a : Fin m₃ → Tm n) (b : Fin m₂ → Tm m₃) (c : Fin m₁ → Tm m₂)
       (d : Fin l → Tm m₁) (t : Tm l) →
       sub a (sub b (sub c (sub d t))) ≡ sub (λ x → sub a (sub b (sub c (d x)))) t
sub4 a b c d t = trans (cong (λ z → sub a (sub b z)) (sub-sub c d t)) (sub3 a b (λ x → sub c (d x)) t)

ren-id : (t : Tm n) → ren (λ x → x) t ≡ t
ren-id t = trans (sym (ren-as-sub (λ x → x) t)) (sub-var t)

module Meth
  (wk-⊢ : ∀ {n} {Γ : Ctx n} {t A B} → Γ ⊢ t ∷ A → (Γ ▹ B) ⊢ wk t ∷ wk A)
  {n : Nat} {c : Nat} (Cs : Args n (rep c)) (f M : Tm n) (ms : Args n (rep c))
  where

  Dm : Tm n
  Dm = dσ (enum c) f

  -- split's motive (binds the payload q)
  Pq : Tm (3 + n)
  Pq = Pi (El (ihTy (W 3 Dm) (W 3 M) (W 3 Dm) (var fz)))
          (El (app (app (W 4 M) (var (fsN 3 fz))) (con (var (fs fz)))))

  -- switch's motive (binds the tag t)
  Pt : Tm (6 + n)
  Pt = Pi (El (pay (W 6 Dm) (switch c Desc (var fz) (WA 6 Cs)) (var (fsN 5 fz))))
          (Pi (El (ihTy (W 7 Dm) (W 7 M) (switch c Desc (var (fs fz)) (WA 7 Cs)) (var fz)))
              (El (app (app (W 8 M) (var (fsN 7 fz))) (con (pair (var (fs (fs fz))) (var (fs fz)))))))

  -- the cases: method k at the index i
  cases : Args (5 + n) (rep c)
  cases = mapA (λ m → app (W 5 m) (var (fsN 4 fz))) ms

  -- split's body (binds t, p), then h
  Bd : Tm (4 + n)
  Bd = lam (app (app (switch c Pt (var (fs (fs fz))) cases) (var (fs fz))) (var fz))

  methₗ : Tm n
  methₗ = lam (lam (split Pq (var fz) Bd))

  -- ─── (c) typing ──────────────────────────────────────────────────────────
  -- the ONE fact about the selector `f` the typing uses (proved for the
  -- concrete `fₗ Cs` by `fₗ-β`)
  FB : Set
  FB = ∀ {m} (ρ : Fin n → Fin m) (t : Tm m) → app (ren ρ f) t ≃ switch c Desc t (renA ρ Cs)

  -- method k is typed at constructor k's method type
  MHyp : Ctx n → Set
  MHyp Γ = ∀ {k m} → Nth ms k m → Σ (Tm n) λ C → Σ (Nth Cs k C) λ _ → Γ ⊢ m ∷ MethK Dm M C k

  -- the per-constructor method type after 5 weakenings and one application
  MKF : Nat → (f5 C5 : Tm (5 + n)) (f6 M6 C6 : Tm (6 + n)) (M7 : Tm (7 + n)) → Tm (5 + n)
  MKF k f5 C5 f6 M6 C6 M7 =
    Pi (El (pay (dσ (enum c) f5) C5 (var (fsN 4 fz))))
       (Pi (El (ihTy (dσ (enum c) f6) M6 C6 (var fz)))
           (El (app (app M7 (var (fsN 6 fz))) (con (pair (tag k) (var (fs fz)))))))

  T₂ : Tm (3 + n)
  T₂ = pay (dσ (enum c) (wkN 3 f)) (app (wkN 3 f) (var fz)) (var (fs (fs fz)))

  module _ {Γ : Ctx n} (fβ : FB) (mh : MHyp Γ) where

    Γ₂ : Ctx (2 + n)
    Γ₂ = (Γ ▹ El ix) ▹ El (pay (wk Dm) (wk Dm) (var fz))

    Γ₅ : Ctx (5 + n)
    Γ₅ = (((Γ₂ ▹ El (enum c)) ▹ El T₂) ▹ El (ihTy (W 4 Dm) (W 4 M) (W 4 Dm) (pair (var (fs fz)) (var fz))))

    g : Tm n → Tm (5 + n)
    g m = app (W 5 m) (var (fsN 4 fz))

    caseTy : (k : Nat) {m : Tm n} → Σ (Tm n) (λ C → Σ (Nth Cs k C) λ _ → Γ ⊢ m ∷ MethK Dm M C k) →
             Γ₅ ⊢ g m ∷ Pt [ tag k ]
    caseTy k {m} (C , nt , dm) =
      ≡-ty (t-conv (≡-ty (t-app dm5 t-var) eqM) MKconv) (sym eqPk)
      where
      v = var (fsN 4 fz)
      dm5 : Γ₅ ⊢ W 5 m ∷ W 5 (MethK Dm M C k)
      dm5 = ≡-tm (≡-ty (wk-⊢ (wk-⊢ (wk-⊢ (wk-⊢ (wk-⊢ dm))))) (rN 5 _)) (rN 5 m)
      eqM = cong6 (MKF k)
              (subRen2 (sg v) (ext (fsN 5)) fs (fsN 5) (λ _ → refl) f)
              (subRen2 (sg v) (ext (fsN 5)) fs (fsN 5) (λ _ → refl) C)
              (subRen2 (exts (sg v)) (ext (ext (fsN 5))) w2 (fsN 6) (λ _ → refl) f)
              (subRen2 (exts (sg v)) (ext (ext (fsN 5))) w2 (fsN 6) (λ _ → refl) M)
              (subRen2 (exts (sg v)) (ext (ext (fsN 5))) w2 (fsN 6) (λ _ → refl) C)
              (subRen2 (exts (exts (sg v))) (ext (ext (ext (fsN 5)))) w3 (fsN 7) (λ _ → refl) M)
      MKconv = ≃-trans
        (≃-map (λ x → MKF k (W 5 f) x (W 6 f) (W 6 M) (W 6 C) (W 7 M))
               (λ s → under (here (under (here (under (there (here s)))))))
               (≃-sym (≃-step (desc (switch-ι (nth-ren (fsN 5) nt))))))
        (≃-map (λ x → MKF k (W 5 f) (switch c Desc (tag k) (WA 5 Cs)) (W 6 f) (W 6 M) x (W 7 M))
               (λ s → under (there (here (under (here (under (here (under (there (there (here s)))))))))))
               (≃-sym (≃-step (desc (switch-ι (nth-ren (fsN 6) nt))))))
      σk = sg (tag k)
      eqPk = cong6 (MKF k)
              (subRen σk (fsN 6) (fsN 5) (λ _ → refl) f)
              (cong (switch c Desc (tag k)) (subRenA σk (fsN 6) (fsN 5) (λ _ → refl) Cs))
              (subRen (exts σk) (fsN 7) (fsN 6) (λ _ → refl) f)
              (subRen (exts σk) (fsN 7) (fsN 6) (λ _ → refl) M)
              (cong (switch c Desc (tag k)) (subRenA (exts σk) (fsN 7) (fsN 6) (λ _ → refl) Cs))
              (subRen (exts (exts σk)) (fsN 8) (fsN 7) (λ _ → refl) M)

    casesTy : (k0 : Nat) {c' : Nat} (ms' : Args n (rep c')) →
              (∀ {j m} → Nth ms' j m → Σ (Tm n) λ C → Σ (Nth Cs (k0 + j) C) λ _ →
                                       Γ ⊢ m ∷ MethK Dm M C (k0 + j)) →
              Cases Γ₅ Pt k0 (mapA g ms')
    casesTy k0 {zero}   []        h = cs-nil
    casesTy k0 {suc c'} (m ∷ ms') h =
      cs-cons (caseTy k0 (subst (λ k → Σ (Tm n) λ C → Σ (Nth Cs k C) λ _ → Γ ⊢ m ∷ MethK Dm M C k)
                                (+-zero k0) (h nth-z)))
              (casesTy (suc k0) ms' λ {j} {m'} nt →
                 subst (λ k → Σ (Tm n) λ C → Σ (Nth Cs k C) λ _ → Γ ⊢ m' ∷ MethK Dm M C k)
                       (+-suc k0 j) (h (nth-s nt)))

    PtF : (f5 : Tm (5 + n)) (Cs5 : Args (5 + n) (rep c)) (f6 M6 : Tm (6 + n))
          (Cs6 : Args (6 + n) (rep c)) (M7 : Tm (7 + n)) → Tm (5 + n)
    PtF f5 Cs5 f6 M6 Cs6 M7 =
      Pi (El (pay (dσ (enum c) f5) (switch c Desc (var (fs (fs fz))) Cs5) (var (fsN 4 fz))))
         (Pi (El (ihTy (dσ (enum c) f6) M6 (switch c Desc (var (fsN 3 fz)) Cs6) (var fz)))
             (El (app (app M7 (var (fsN 6 fz))) (con (pair (var (fsN 4 fz)) (var (fs fz)))))))

    dSW : Γ₅ ⊢ switch c Pt (var (fs (fs fz))) cases ∷ PtF (W 5 f) (WA 5 Cs) (W 6 f) (W 6 M) (WA 6 Cs) (W 7 M)
    dSW = ≡-ty (t-switch t-var (casesTy 0 ms mh)) eqPt
      where
      σ = sg (var (fs (fs fz)))
      eqPt = cong6 PtF
              (subRen σ (fsN 6) (fsN 5) (λ _ → refl) f)
              (subRenA σ (fsN 6) (fsN 5) (λ _ → refl) Cs)
              (subRen (exts σ) (fsN 7) (fsN 6) (λ _ → refl) f)
              (subRen (exts σ) (fsN 7) (fsN 6) (λ _ → refl) M)
              (subRenA (exts σ) (fsN 7) (fsN 6) (λ _ → refl) Cs)
              (subRen (exts (exts σ)) (fsN 8) (fsN 7) (λ _ → refl) M)

    D5 = dσ (enum c) (W 5 f)

    p1 : Γ₅ ⊢ var (fs fz) ∷ El (pay D5 (switch c Desc (var (fs (fs fz))) (WA 5 Cs)) (var (fsN 4 fz)))
    p1 = t-conv (≡-ty t-var (cong (λ X → El (pay (dσ (enum c) X) (app X (var (fs (fs fz)))) (var (fsN 4 fz))))
                                  (rN 5 f)))
                (≃-map (λ x → El (pay D5 x (var (fsN 4 fz))))
                       (λ s → under (here (under (there (here s)))))
                       (fβ (fsN 5) (var (fs (fs fz)))))

    h1 : Γ₅ ⊢ var fz ∷ El (ihTy D5 (W 5 M) (switch c Desc (var (fs (fs fz))) (WA 5 Cs)) (var (fs fz)))
    h1 = t-conv (≡-ty t-var (cong₂ (λ X Y → El (ihTy (dσ (enum c) X) Y (dσ (enum c) X)
                                                  (pair (var (fs (fs fz))) (var (fs fz)))))
                                   (w45 f) (w45 M)))
         (≃-trans (⟶ₑ ihTy-σ)
         (≃-trans (≃-step (under (here (under (there (there (here (under (there (here π₁))))))))))
         (≃-trans (≃-step (under (here (under (there (there (there (here π₂))))))))
                  (≃-map (λ x → El (ihTy D5 (W 5 M) x (var (fs fz))))
                         (λ s → under (here (under (there (there (here s))))))
                         (fβ (fsN 5) (var (fs (fs fz))))))))
      where w45 = renRen fs (fsN 4) (fsN 5) (λ _ → refl)

    dBB : Γ₅ ⊢ app (app (switch c Pt (var (fs (fs fz))) cases) (var (fs fz))) (var fz)
             ∷ El (app (app (W 5 M) (var (fsN 4 fz))) (con (pair (var (fs (fs fz))) (var (fs fz)))))
    dBB = ≡-ty (t-app (≡-ty (t-app dSW p1) eqQ) h1) eqFin
      where
      σp = sg (var (fs fz))
      eqQ = cong4 (λ X Y Z W' →
                     Pi (El (ihTy (dσ (enum c) X) Y (switch c Desc (var (fs (fs fz))) Z) (var (fs fz))))
                        (El (app (app W' (var (fsN 5 fz))) (con (pair (var (fsN 3 fz)) (var (fs (fs fz))))))))
              (subRen σp (fsN 6) (fsN 5) (λ _ → refl) f)
              (subRen σp (fsN 6) (fsN 5) (λ _ → refl) M)
              (subRenA σp (fsN 6) (fsN 5) (λ _ → refl) Cs)
              (subRen (exts σp) (fsN 7) (fsN 6) (λ _ → refl) M)
      eqFin = cong (λ X → El (app (app X (var (fsN 4 fz))) (con (pair (var (fs (fs fz))) (var (fs fz))))))
                   (subRen (sg (var fz)) (fsN 6) (fsN 5) (λ _ → refl) M)

    -- ★ (c): the elaborated method has the kernel's ONE method type
    ⊢methₗ : Γ ⊢ methₗ ∷ MethTy Dm M
    ⊢methₗ = t-lam (t-lam (≡-ty (t-split (t-conv t-var (⟶ₑ pay-σ)) (≡-ty (t-lam dBB) (sym eq4))) eqR2))
      where
      eq4 = cong₃ (λ X Y Z → Pi (El (ihTy (dσ (enum c) X) Y (dσ (enum c) X) (pair (var (fs fz)) (var fz))))
                                (El (app (app Z (var (fsN 4 fz))) (con (pair (var (fs (fs fz))) (var (fs fz)))))))
                  (subRen ρpair (fsN 3) (fsN 4) (λ _ → refl) f)
                  (subRen ρpair (fsN 3) (fsN 4) (λ _ → refl) M)
                  (subRen (exts ρpair) (fsN 4) (fsN 5) (λ _ → refl) M)
      eqR2 = cong₃ (λ X Y Z → Pi (El (ihTy (dσ (enum c) X) Y (dσ (enum c) X) (var fz)))
                                 (El (app (app Z (var (fs (fs fz)))) (con (var (fs fz))))))
                   (subRen (sg (var fz)) (fsN 3) w2 (λ _ → refl) f)
                   (subRen (sg (var fz)) (fsN 3) w2 (λ _ → refl) M)
                   (subRen (exts (sg (var fz))) (fsN 4) w3 (λ _ → refl) M)

  -- ─── (d) the DERIVED ι: the sugar computes like the list form's ι ────────
  ιₗ : {k : Nat} {i p m : Tm n} → Nth ms k m →
       ielim Dm M methₗ i (conₗ k p) ⟶* app (app (app m i) p) (ih Dm M methₗ Dm (pair (tag k) p))
  ιₗ {k = k} {i} {p} {m} nt =
    desc ι ◅ under (here (under (here β))) ◅ under (here β) ◅ under (here (desc split-ι)) ◅ β ◅
    ≡-tgt (under (here (under (here (desc (switch-ι
            (nth-sub σa (nth-sub σb (nth-sub σc (nth-sub σd (nth-map (λ m' → app (W 5 m') (var (fsN 4 fz))) nt)))))))))))
          (cong₂ (λ X Y → app (app X Y) h') (cong₂ app eqm eqi) (c1 h' p)) ◅ ε*
    where
    h' = ih Dm M methₗ Dm (pair (tag k) p)
    σa  = sg h'
    σb  = exts (sg2 (tag k) p)
    σc  = exts (exts (exts (sg (pair (tag k) p))))
    σd  = exts (exts (exts (exts (sg i))))
    eqm = trans (sub4 σa σb σc σd (W 5 m)) (trans (subRen _ (fsN 5) (λ x → x) (λ _ → refl) m) (ren-id m))
    eqi = trans (cong (λ z → sub σa (sub σb (sub σc z))) (rN 4 i))
         (trans (sub3 σa σb σc (W 4 i)) (trans (subRen _ (fsN 4) (λ x → x) (λ _ → refl) i) (ren-id i)))

-- ═══ (c) for the CONCRETE datatype: the selector hypothesis is discharged ══
⊢methₗ-concrete :
  (wk-⊢ : ∀ {n} {Γ : Ctx n} {t A B} → Γ ⊢ t ∷ A → (Γ ▹ B) ⊢ wk t ∷ wk A) →
  {c : Nat} (Cs : Args n (rep c)) (M : Tm n) (ms : Args n (rep c)) →
  Meth.MHyp wk-⊢ Cs (fₗ Cs) M ms Γ →
  Γ ⊢ Meth.methₗ wk-⊢ Cs (fₗ Cs) M ms ∷ MethTy (Dₗ Cs) M
⊢methₗ-concrete wk-⊢ Cs M ms mh = Meth.⊢methₗ wk-⊢ Cs (fₗ Cs) M ms (fₗ-β Cs) mh

-- ═══ CONTROL for (e): the out-of-range tag is exactly what typing excludes ═
data ⊥ : Set where

-- a closed switch on an out-of-range tag is STUCK (the list form's
-- `lkp dnil k`): no step at all
out-of-range-stuck : ∀ {t' : Tm n} → switch 2 U (tag 2) (unit ∷ unit ∷ []) ⟶ t' → ⊥
out-of-range-stuck (desc (switch-ι (nth-s (nth-s ()))))
out-of-range-stuck (under (here (desc ())))
out-of-range-stuck (under (here (under ())))
out-of-range-stuck (under (there (here (desc ()))))
out-of-range-stuck (under (there (here (under ()))))
out-of-range-stuck (under (there (there (here (desc ())))))
out-of-range-stuck (under (there (there (here (under ())))))
out-of-range-stuck (under (there (there (there (here (desc ()))))))
out-of-range-stuck (under (there (there (there (here (under ()))))))
out-of-range-stuck (under (there (there (there (there ())))))

-- … and it is UNTYPABLE: the tag's `Lt` premise is what buys canonicity
lt22 : Lt 2 2 → ⊥
lt22 (lt-s (lt-s ()))

out-of-range-untypable :
  (enum-inj : ∀ {n} {c c' : Nat} → _≃_ {n} (El (enum c)) (El (enum c')) → c ≡ c') →
  Γ ⊢ tag 2 ∷ El (enum 2) → ⊥
out-of-range-untypable enum-inj d = lt22 (tag-lt enum-inj d)
