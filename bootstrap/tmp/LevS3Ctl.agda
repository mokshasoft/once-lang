{-# OPTIONS --safe #-}
-- SPIKE-LEVITATION S3 — SUBJECT REDUCTION of description typing.
--
-- The levitated form of "The gentle art of levitation" (Chapman, Dagand,
-- McBride, Morris): a datatype is ONE telescope `D : Desc` (constructor
-- choice = an ordinary σ field over a tag type — no constructor LIST, no
-- `icon k`, no `ilookupD`), telescopes are TERMS
--     dι j | dσ S f (f : Π (El S) Desc) | dρ j C
-- well-formedness is TYPING (`Γ ⊢ D ∷ Desc` — no IDescWf), the payload and
-- hypothesis operators `pay`/`ihTy`/`ih` are FORMERS computing on the head
-- of the telescope, and the eliminator's methods are ONE Π:
--     MethTy D M = Π i. Π (p : pay D D i). Π (h : ihTy D M D p). M i (con p)
-- The index type is a fixed CLOSED code `ix` (A-math: `◇ ⊢ty I`).
--
-- SUCCESS: `sr-desc` — every description rule preserves typing — and the
-- inversion lemmas for the description formers, proved THROUGH the
-- conversion rule.  ASSUMED (the kernel's standard metatheory, unchanged by
-- levitation): weakening of typing, and injectivity of `El`/`mu` under
-- conversion (Church–Rosser).  NOT re-proved: SR for β/π/congruence.
module tmp.LevS3Ctl where

open import tmp.LevSyn
open import Agda.Builtin.Sigma using ( Σ; _,_ )

data Op : Set where
  `U `El `Pi `ix `unit `eqc `sig `tt `pair `fst `snd `lam `app : Op
  `Desc `dι `dσ `dρ `mu `con `pay `ihTy `ih `ielim : Op
  -- S4: the TAG type (a finite enumeration) and Σ-INDUCTION
  `enum `tag `switch : Nat → Op
  `split : Op

rep : Nat → List Nat          -- c plain arguments
rep zero    = []
rep (suc c) = 0 ∷ rep c

ar : Op → List Nat
ar `U     = []
ar `El    = 0 ∷ []
ar `Pi    = 0 ∷ 1 ∷ []
ar `ix    = []
ar `unit  = []
ar `eqc   = 0 ∷ 0 ∷ []                -- the index equation of `dι j` at i
ar `sig   = 0 ∷ 1 ∷ []
ar `tt    = []
ar `pair  = 0 ∷ 0 ∷ []
ar `fst   = 0 ∷ []
ar `snd   = 0 ∷ []
ar `lam   = 1 ∷ []
ar `app   = 0 ∷ 0 ∷ []
ar `Desc  = []                        -- LARGE: no `Desc ∷ U`
ar `dι    = 0 ∷ []
ar `dσ    = 0 ∷ 0 ∷ []
ar `dρ    = 0 ∷ 0 ∷ []
ar `mu    = 0 ∷ 0 ∷ []                -- mu D i
ar `con   = 0 ∷ []
ar `pay   = 0 ∷ 0 ∷ 0 ∷ []            -- pay D C i : payload of C, recursion into mu D
ar `ihTy  = 0 ∷ 0 ∷ 0 ∷ 0 ∷ []        -- ihTy D M C p
ar `ih    = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []    -- ih D M e C p
ar `ielim = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []    -- ielim D M e i t
ar (`enum c)   = []                  -- the code of {0 … c-1}
ar (`tag k)    = []
ar (`switch c) = 1 ∷ 0 ∷ rep c       -- switch c P t (m₀ … m_{c-1}), P binds the tag
ar `split      = 1 ∷ 0 ∷ 2 ∷ []      -- split P q b, P binds q, b binds both halves

open Syntax Op ar

pattern U            = node `U []
pattern El a         = node `El (a ∷ [])
pattern Pi A B       = node `Pi (A ∷ B ∷ [])
pattern ix           = node `ix []
pattern unit         = node `unit []
pattern eqc j i      = node `eqc (j ∷ i ∷ [])
pattern sig S T      = node `sig (S ∷ T ∷ [])
pattern tt           = node `tt []
pattern pair a b     = node `pair (a ∷ b ∷ [])
pattern fst p        = node `fst (p ∷ [])
pattern snd p        = node `snd (p ∷ [])
pattern lam b        = node `lam (b ∷ [])
pattern app t u      = node `app (t ∷ u ∷ [])
pattern Desc         = node `Desc []
pattern dι j         = node `dι (j ∷ [])
pattern dσ S f       = node `dσ (S ∷ f ∷ [])
pattern dρ j C       = node `dρ (j ∷ C ∷ [])
pattern mu D i       = node `mu (D ∷ i ∷ [])
pattern con p        = node `con (p ∷ [])
pattern pay D C i    = node `pay (D ∷ C ∷ i ∷ [])
pattern ihTy D M C p = node `ihTy (D ∷ M ∷ C ∷ p ∷ [])
pattern ih D M e C p = node `ih (D ∷ M ∷ e ∷ C ∷ p ∷ [])
pattern ielim D M e i t = node `ielim (D ∷ M ∷ e ∷ i ∷ t ∷ [])
pattern enum c          = node (`enum c) []
pattern tag k           = node (`tag k) []
pattern switch c P t ms = node (`switch c) (P ∷ t ∷ ms)
pattern split P q b     = node `split (P ∷ q ∷ b ∷ [])

infixr 2 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

cong₃ : {A B C E : Set} {a a' : A} {b b' : B} {c c' : C} (f : A → B → C → E) →
        a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

w2 : Fin n → Fin (suc (suc n))
w2 x = fs (fs x)

w3 : Fin n → Fin (suc (suc (suc n)))
w3 x = fs (fs (fs x))

-- the motive and the ONE method
MotTy : Tm n → Tm n
MotTy D = Pi (El ix) (Pi (El (mu (wk D) (var fz))) U)

MethTy : Tm n → Tm n → Tm n
MethTy D M =
  Pi (El ix)                                                   -- i
     (Pi (El (pay (wk D) (wk D) (var fz)))                     -- p
         (Pi (El (ihTy (ren w2 D) (ren w2 M) (ren w2 D) (var fz)))   -- h
             (El (app (app (ren w3 M) (var (fs (fs fz)))) (con (var (fs fz)))))))

variable
  a b c e f h i i' j p q t t' u A A' B S T D D' M C : Tm n
  bd B' : Tm (suc n)

-- the k-th of c plain arguments
data Nth {m : Nat} : {c : Nat} → Args m (rep c) → Nat → Tm m → Set where
  nth-z : {c : Nat} {x : Tm m} {xs : Args m (rep c)} → Nth {c = suc c} (x ∷ xs) zero x
  nth-s : {c k : Nat} {x y : Tm m} {xs : Args m (rep c)} →
          Nth xs k y → Nth {c = suc c} (x ∷ xs) (suc k) y

data Lt : Nat → Nat → Set where
  lt-z : {c : Nat} → Lt zero (suc c)
  lt-s : {k c : Nat} → Lt k c → Lt (suc k) (suc c)

-- instantiate split's two binders / re-pair them for the motive
sg2 : Tm n → Tm n → Fin (suc (suc n)) → Tm n
sg2 a b fz          = b
sg2 a b (fs fz)     = a
sg2 a b (fs (fs x)) = var x

ρpair : Fin (suc n) → Tm (suc (suc n))
ρpair fz     = pair (var (fs fz)) (var fz)
ρpair (fs x) = var (fs (fs x))

-- ═══ reduction ═══════════════════════════════════════════════════════════
infix 4 _⟶ᴰ_ _⟶_ _⟶ₐ_ _≃_

-- the DESCRIPTION rules (all compute on the HEAD of a telescope)
data _⟶ᴰ_ {n : Nat} : Tm n → Tm n → Set where
  ι      : ielim D M e i (con p) ⟶ᴰ app (app (app e i) p) (ih D M e D p)
  pay-ι  : pay D (dι j) i ⟶ᴰ eqc j i
  pay-σ  : pay D (dσ S f) i ⟶ᴰ sig S (pay (wk D) (app (wk f) (var fz)) (wk i))
  pay-ρ  : pay D (dρ j C) i ⟶ᴰ sig (mu D i) (pay (wk D) (wk C) (wk i))
  ihTy-ι : ihTy D M (dι j) p ⟶ᴰ unit
  ihTy-σ : ihTy D M (dσ S f) p ⟶ᴰ ihTy D M (app f (fst p)) (snd p)
  ihTy-ρ : ihTy D M (dρ j C) p ⟶ᴰ sig (app (app M j) (fst p)) (ihTy (wk D) (wk M) (wk C) (snd (wk p)))
  ih-ι   : ih D M e (dι j) p ⟶ᴰ tt
  ih-σ   : ih D M e (dσ S f) p ⟶ᴰ ih D M e (app f (fst p)) (snd p)
  ih-ρ   : ih D M e (dρ j C) p ⟶ᴰ pair (ielim D M e j (fst p)) (ih D M e C (snd p))
  -- S4: the tag eliminator and Σ-induction
  switch-ι : {c k : Nat} {P : Tm (suc n)} {ms : Args n (rep c)} {m : Tm n} →
             Nth ms k m → switch c P (tag k) ms ⟶ᴰ m
  split-ι  : {P : Tm (suc n)} {b2 : Tm (suc (suc n))} →
             split P (pair a b) b2 ⟶ᴰ sub (sg2 a b) b2

data _⟶_  {n : Nat} : Tm n → Tm n → Set
data _⟶ₐ_ {n : Nat} : {ks : List Nat} → Args n ks → Args n ks → Set

data _⟶_ {n} where
  β     : app (lam bd) u ⟶ bd [ u ]
  π₁    : fst (pair a b) ⟶ a
  π₂    : snd (pair a b) ⟶ b
  desc  : t ⟶ᴰ t' → t ⟶ t'
  under : {o : Op} {as as' : Args n (ar o)} → as ⟶ₐ as' → node o as ⟶ node o as'

data _⟶ₐ_ {n} where
  here  : {k : Nat} {ks : List Nat} {t t' : Tm (k + n)} {as : Args n ks} →
          t ⟶ t' → _⟶ₐ_ {ks = k ∷ ks} (t ∷ as) (t' ∷ as)
  there : {k : Nat} {ks : List Nat} {t : Tm (k + n)} {as as' : Args n ks} →
          as ⟶ₐ as' → _⟶ₐ_ {ks = k ∷ ks} (t ∷ as) (t ∷ as')

data _≃_ {n : Nat} : Tm n → Tm n → Set where
  ≃-refl  : t ≃ t
  ≃-step  : t ⟶ t' → t ≃ t'
  ≃-sym   : t ≃ t' → t' ≃ t
  ≃-trans : t ≃ u → u ≃ t' → t ≃ t'

≃-map : {m : Nat} (F : Tm n → Tm m) → (∀ {x y} → x ⟶ y → F x ⟶ F y) →
        t ≃ t' → F t ≃ F t'
≃-map F s ≃-refl        = ≃-refl
≃-map F s (≃-step x)    = ≃-step (s x)
≃-map F s (≃-sym q)     = ≃-sym (≃-map F s q)
≃-map F s (≃-trans q r) = ≃-trans (≃-map F s q) (≃-map F s r)

⟶ₑ : t ⟶ᴰ t' → El t ≃ El t'       -- a description step inside `El`
⟶ₑ s = ≃-step (under (here (desc s)))

-- ═══ typing ══════════════════════════════════════════════════════════════
data Ctx : Nat → Set where
  ε   : Ctx zero
  _▹_ : Ctx n → Tm n → Ctx (suc n)

lookup : Ctx n → Fin n → Tm n
lookup (Γ ▹ A) fz     = wk A
lookup (Γ ▹ A) (fs x) = wk (lookup Γ x)

variable Γ : Ctx n

infix 3 _⊢_∷_
data _⊢_∷_ {n : Nat} (Γ : Ctx n) : Tm n → Tm n → Set
-- the cases of a switch, from tag k on
data Cases {n : Nat} (Γ : Ctx n) (P : Tm (suc n)) : Nat → {c : Nat} → Args n (rep c) → Set

data _⊢_∷_ {n} Γ where
  t-var   : {x : Fin n} → Γ ⊢ var x ∷ lookup Γ x
  t-conv  : Γ ⊢ t ∷ A → A ≃ B → Γ ⊢ t ∷ B
  t-lam   : (Γ ▹ A) ⊢ bd ∷ B' → Γ ⊢ lam bd ∷ Pi A B'
  t-app   : {B' : Tm (suc n)} → Γ ⊢ t ∷ Pi A B' → Γ ⊢ u ∷ A → Γ ⊢ app t u ∷ B' [ u ]
  t-ix    : Γ ⊢ ix ∷ U
  t-unit  : Γ ⊢ unit ∷ U
  t-eqc   : Γ ⊢ j ∷ El ix → Γ ⊢ i ∷ El ix → Γ ⊢ eqc j i ∷ U
  t-sig   : {T' : Tm (suc n)} → Γ ⊢ S ∷ U → (Γ ▹ El S) ⊢ T' ∷ U → Γ ⊢ sig S T' ∷ U
  t-tt    : Γ ⊢ tt ∷ El unit
  t-pair  : {T' : Tm (suc n)} → Γ ⊢ a ∷ El S → Γ ⊢ b ∷ El (T' [ a ]) → Γ ⊢ pair a b ∷ El (sig S T')
  t-fst   : {T' : Tm (suc n)} → Γ ⊢ p ∷ El (sig S T') → Γ ⊢ fst p ∷ El S
  t-snd   : {T' : Tm (suc n)} → Γ ⊢ p ∷ El (sig S T') → Γ ⊢ snd p ∷ El (T' [ fst p ])
  -- descriptions: well-formedness IS typing
  t-dι    : Γ ⊢ j ∷ El ix → Γ ⊢ dι j ∷ Desc
  t-dσ    : Γ ⊢ S ∷ U → Γ ⊢ f ∷ Pi (El S) Desc → Γ ⊢ dσ S f ∷ Desc
  t-dρ    : Γ ⊢ j ∷ El ix → Γ ⊢ C ∷ Desc → Γ ⊢ dρ j C ∷ Desc
  t-mu    : Γ ⊢ D ∷ Desc → Γ ⊢ i ∷ El ix → Γ ⊢ mu D i ∷ U
  t-con   : Γ ⊢ D ∷ Desc → Γ ⊢ i ∷ El ix → Γ ⊢ p ∷ El (pay D D i) → Γ ⊢ con p ∷ El (mu D i)
  t-pay   : Γ ⊢ D ∷ Desc → Γ ⊢ C ∷ Desc → Γ ⊢ i ∷ El ix → Γ ⊢ pay D C i ∷ U
  t-ihTy  : Γ ⊢ D ∷ Desc → Γ ⊢ M ∷ MotTy D → Γ ⊢ C ∷ Desc →
            Γ ⊢ i ∷ El ix → Γ ⊢ p ∷ El (pay D C i) → Γ ⊢ ihTy D M C p ∷ U
  t-ih    : Γ ⊢ D ∷ Desc → Γ ⊢ M ∷ MotTy D → Γ ⊢ e ∷ MethTy D M → Γ ⊢ C ∷ Desc →
            Γ ⊢ i ∷ El ix → Γ ⊢ p ∷ El (pay D C i) → Γ ⊢ ih D M e C p ∷ El (ihTy D M C p)
  t-ielim : Γ ⊢ D ∷ Desc → Γ ⊢ M ∷ MotTy D → Γ ⊢ e ∷ MethTy D M →
            Γ ⊢ i ∷ El ix → Γ ⊢ t ∷ El (mu D i) → Γ ⊢ ielim D M e i t ∷ El (app (app M i) t)
  -- S4
  t-enum   : {c : Nat} → Γ ⊢ enum c ∷ U
  t-tag    : {c k : Nat} → Lt k c → Γ ⊢ tag k ∷ El (enum c)
  t-switch : {c : Nat} {P : Tm (suc n)} {ms : Args n (rep c)} →
             Γ ⊢ t ∷ El (enum c) → Cases Γ P 0 ms → Γ ⊢ switch c P t ms ∷ P [ t ]
  t-split  : {P T' : Tm (suc n)} {b2 : Tm (suc (suc n))} →
             Γ ⊢ q ∷ El (sig S T') → ((Γ ▹ El S) ▹ El T') ⊢ b2 ∷ sub ρpair P →
             Γ ⊢ split P q b2 ∷ P [ q ]

data Cases {n} Γ P where
  cs-nil  : {k : Nat} → Cases Γ P k {zero} []
  cs-cons : {k c : Nat} {x : Tm n} {xs : Args n (rep c)} →
            Γ ⊢ x ∷ P [ tag k ] → Cases Γ P (suc k) xs → Cases Γ P k {suc c} (x ∷ xs)

≡-ty : Γ ⊢ t ∷ A → A ≡ B → Γ ⊢ t ∷ B
≡-ty d refl = d

-- ═══ INVERSION for the description formers, through `t-conv` ═════════════
inv-dι : Γ ⊢ dι j ∷ A → Γ ⊢ j ∷ El ix
inv-dι (t-dι d)     = d
inv-dι (t-conv d _) = inv-dι d

inv-dσ : Γ ⊢ dσ S f ∷ A → (Γ ⊢ S ∷ U) × (Γ ⊢ f ∷ Pi (El S) Desc)
inv-dσ (t-dσ s g)   = s , g
inv-dσ (t-conv d _) = inv-dσ d

inv-dρ : Γ ⊢ dρ j C ∷ A → (Γ ⊢ j ∷ El ix) × (Γ ⊢ C ∷ Desc)
inv-dρ (t-dρ k c)   = k , c
inv-dρ (t-conv d _) = inv-dρ d

inv-pay : Γ ⊢ pay D C i ∷ A →
          (U ≃ A) × (Γ ⊢ D ∷ Desc) × (Γ ⊢ C ∷ Desc) × (Γ ⊢ i ∷ El ix)
inv-pay (t-pay d c k) = ≃-refl , d , c , k
inv-pay (t-conv d q) with inv-pay d
... | r , x = ≃-trans r q , x

inv-ihTy : Γ ⊢ ihTy D M C p ∷ A →
           (U ≃ A) × (Γ ⊢ D ∷ Desc) × (Γ ⊢ M ∷ MotTy D) × (Γ ⊢ C ∷ Desc) ×
           Σ (Tm _) (λ i → (Γ ⊢ i ∷ El ix) × (Γ ⊢ p ∷ El (pay D C i)))
inv-ihTy (t-ihTy d m c k q) = ≃-refl , d , m , c , _ , k , q
inv-ihTy (t-conv d q) with inv-ihTy d
... | r , x = ≃-trans r q , x

inv-ih : Γ ⊢ ih D M e C p ∷ A →
         (El (ihTy D M C p) ≃ A) × (Γ ⊢ D ∷ Desc) × (Γ ⊢ M ∷ MotTy D) ×
         (Γ ⊢ e ∷ MethTy D M) × (Γ ⊢ C ∷ Desc) ×
         Σ (Tm _) (λ i → (Γ ⊢ i ∷ El ix) × (Γ ⊢ p ∷ El (pay D C i)))
inv-ih (t-ih d m g c k q) = ≃-refl , d , m , g , c , _ , k , q
inv-ih (t-conv d q) with inv-ih d
... | r , x = ≃-trans r q , x

inv-ielim : Γ ⊢ ielim D M e i t ∷ A →
            (El (app (app M i) t) ≃ A) × (Γ ⊢ D ∷ Desc) × (Γ ⊢ M ∷ MotTy D) ×
            (Γ ⊢ e ∷ MethTy D M) × (Γ ⊢ i ∷ El ix) × (Γ ⊢ t ∷ El (mu D i))
inv-ielim (t-ielim d m g k s) = ≃-refl , d , m , g , k , s
inv-ielim (t-conv d q) with inv-ielim d
... | r , x = ≃-trans r q , x

inv-con : Γ ⊢ con p ∷ A →
          Σ (Tm _) λ D' → Σ (Tm _) λ i' →
          (El (mu D' i') ≃ A) × (Γ ⊢ D' ∷ Desc) × (Γ ⊢ i' ∷ El ix) × (Γ ⊢ p ∷ El (pay D' D' i'))
inv-con (t-con d k q) = _ , _ , ≃-refl , d , k , q
inv-con (t-conv d q) with inv-con d
... | D' , i' , r , x = D' , i' , ≃-trans r q , x

-- S4 inversions
inv-switch : {c : Nat} {P : Tm (suc n)} {ms : Args n (rep c)} →
             Γ ⊢ switch c P t ms ∷ A →
             (P [ t ] ≃ A) × (Γ ⊢ t ∷ El (enum c)) × Cases Γ P 0 ms
inv-switch (t-switch d cs) = ≃-refl , d , cs
inv-switch (t-conv d q) with inv-switch d
... | r , x = ≃-trans r q , x

inv-split : {P : Tm (suc n)} {b2 : Tm (suc (suc n))} → Γ ⊢ split P q b2 ∷ A →
            (P [ q ] ≃ A) × Σ (Tm _) λ S → Σ (Tm _) λ T' →
            (Γ ⊢ q ∷ El (sig S T')) × (((Γ ▹ El S) ▹ El T') ⊢ b2 ∷ sub ρpair P)
inv-split (t-split d b) = ≃-refl , _ , _ , d , b
inv-split (t-conv d q) with inv-split d
... | r , x = ≃-trans r q , x

inv-pair : Γ ⊢ pair a b ∷ A →
           Σ (Tm _) λ S → Σ (Tm _) λ T' →
           (El (sig S T') ≃ A) × (Γ ⊢ a ∷ El S) × (Γ ⊢ b ∷ El (T' [ a ]))
inv-pair (t-pair x y) = _ , _ , ≃-refl , x , y
inv-pair (t-conv d q) with inv-pair d
... | S , T' , r , x = S , T' , ≃-trans r q , x

inv-tag : {k : Nat} → Γ ⊢ tag k ∷ A → Σ Nat λ c → (El (enum c) ≃ A) × Lt k c
inv-tag (t-tag l) = _ , ≃-refl , l
inv-tag (t-conv d q) with inv-tag d
... | c , r , l = c , ≃-trans r q , l

+-zero : (k : Nat) → k + zero ≡ k
+-zero zero    = refl
+-zero (suc k) = cong suc (+-zero k)

+-suc : (a b : Nat) → a + suc b ≡ suc (a + b)
+-suc zero    b = refl
+-suc (suc a) b = cong suc (+-suc a b)

cases-nth : {k0 c k : Nat} {P : Tm (suc n)} {ms : Args n (rep c)} {m : Tm n} →
            Cases Γ P k0 ms → Nth ms k m → Γ ⊢ m ∷ P [ tag (k0 + k) ]
cases-nth {k0 = k0} {P = P} (cs-cons d _) nth-z =
  ≡-ty d (cong (λ x → P [ tag x ]) (sym (+-zero k0)))
cases-nth {k0 = k0} {P = P} (cs-cons _ cs) (nth-s {k = k} nt) =
  ≡-ty (cases-nth cs nt) (cong (λ x → P [ tag x ]) (sym (+-suc k0 k)))

El≃ : t ≃ t' → El t ≃ El t'
El≃ = ≃-map El (λ s → under (here s))

-- ═══ substitution bookkeeping (S2's lemmas, instantiated) ═════════════════
can : (σ : Fin m → Tm n) (ρ : Fin n → Fin m) → (∀ x → σ (ρ x) ≡ var x) →
      (t : Tm n) → sub σ (ren ρ t) ≡ t
can σ ρ h t = trans (sub-ren σ ρ t) (trans (sub-cong h t) (sub-var t))

c1 : (a t : Tm n) → sub (sg a) (wk t) ≡ t
c1 a = can (sg a) fs (λ _ → refl)

c2 : (a b t : Tm n) → sub (sg a) (sub (exts (sg b)) (ren w2 t)) ≡ t
c2 a b t = trans (sub-sub (sg a) (exts (sg b)) (ren w2 t)) (can _ w2 (λ _ → refl) t)

c3 : (a b c t : Tm n) →
     sub (sg a) (sub (exts (sg b)) (sub (exts (exts (sg c))) (ren w3 t))) ≡ t
c3 a b c t =
  trans (cong (sub (sg a)) (sub-sub (exts (sg b)) (exts (exts (sg c))) (ren w3 t)))
 (trans (sub-sub (sg a) _ (ren w3 t)) (can _ w3 (λ _ → refl) t))

cw : (a : Tm (suc n)) (t : Tm n) → sub (sg a) (ren (ext fs) (wk t)) ≡ wk t
cw a t = trans (cong (sub (sg a)) (ren-wk fs t)) (c1 a (wk t))

wk-MotTy : (D : Tm n) → wk (MotTy D) ≡ MotTy (wk D)
wk-MotTy D = cong (λ X → Pi (El ix) (Pi (El (mu X (var fz))) U)) (ren-wk fs D)

payEl≃ : D' ≃ D → i' ≃ i → El (pay D' D' i') ≃ El (pay D D i)
payEl≃ {D' = D'} {D = D} {i' = i'} {i = i} dd ii =
  ≃-trans (≃-map (λ x → El (pay x D' i')) (λ s → under (here (under (here s)))) dd)
 (≃-trans (≃-map (λ x → El (pay D x i')) (λ s → under (here (under (there (here s))))) dd)
          (≃-map (λ x → El (pay D D x)) (λ s → under (here (under (there (there (here s)))))) ii))

-- ═══ ★ S3: SUBJECT REDUCTION of the description rules ════════════════════
module SR
  (wk-⊢   : ∀ {n} {Γ : Ctx n} {t A B} → Γ ⊢ t ∷ A → (Γ ▹ B) ⊢ wk t ∷ wk A)
  (El-inj : ∀ {n} {a b : Tm n} → El a ≃ El b → a ≃ b)
  (mu-inj : ∀ {n} {D D' i i' : Tm n} → mu D i ≃ mu D' i' → (D ≃ D') × (i ≃ i'))
  -- S4 (standard Σ metatheory)
  (sig-inj : ∀ {n} {S S' : Tm n} {T T' : Tm (suc n)} → sig S T ≃ sig S' T' → (S ≃ S') × (T ≃ T'))
  (sub-≃   : ∀ {n} {T T' : Tm (suc n)} {a : Tm n} → T ≃ T' → (T [ a ]) ≃ (T' [ a ]))
  (sub-⊢₂  : ∀ {n} {Γ : Ctx n} {S : Tm n} {T : Tm (suc n)} {t X : Tm (suc (suc n))} {a b : Tm n} →
             ((Γ ▹ El S) ▹ El T) ⊢ t ∷ X → Γ ⊢ a ∷ El S → Γ ⊢ b ∷ El (T [ a ]) →
             Γ ⊢ sub (sg2 a b) t ∷ sub (sg2 a b) X)
  where

  split-ty : (P : Tm (suc n)) (a b : Tm n) → sub (sg2 a b) (sub ρpair P) ≡ P [ pair a b ]
  split-ty P a b = trans (sub-sub (sg2 a b) ρpair P) (sub-cong pt P)
    where pt : (λ x → sub (sg2 a b) (ρpair x)) ≗ sg (pair a b)
          pt fz     = refl
          pt (fs x) = refl

  sr-desc : Γ ⊢ t ∷ A → t ⟶ᴰ t' → Γ ⊢ t' ∷ A
  sr-desc d pay-ι with inv-pay d
  ... | q , _ , c , k = t-conv (t-eqc (inv-dι c) k) q
  sr-desc d pay-σ with inv-pay d
  ... | q , dD , c , k with inv-dσ c
  ... | s , g = t-conv (t-sig s (t-pay (wk-⊢ dD) (t-app (wk-⊢ g) t-var) (wk-⊢ k))) q
  sr-desc d pay-ρ with inv-pay d
  ... | q , dD , c , k with inv-dρ c
  ... | jj , cc = t-conv (t-sig (t-mu dD jj) (t-pay (wk-⊢ dD) (wk-⊢ cc) (wk-⊢ k))) q
  sr-desc d ihTy-ι with inv-ihTy d
  ... | q , _ = t-conv t-unit q
  sr-desc d (ihTy-σ {D = D} {S = S} {f = f} {p = p}) with inv-ihTy d
  ... | q , dD , m , c , i , k , pp with inv-dσ c
  ... | s , g =
    let p' = t-conv pp (⟶ₑ pay-σ)
        sp = ≡-ty (t-snd p') (cong₃ (λ X Y Z → El (pay X (app Y (fst p)) Z)) (c1 _ D) (c1 _ f) (c1 _ i))
    in t-conv (t-ihTy dD m (t-app g (t-fst p')) k sp) q
  sr-desc d (ihTy-ρ {D = D} {M = M} {j = j} {C = C} {p = p}) with inv-ihTy d
  ... | q , dD , m , c , i , k , pp with inv-dρ c
  ... | jj , cc =
    let p'  = t-conv pp (⟶ₑ pay-ρ)
        Mj  = ≡-ty (t-app m jj) (cong (λ X → Pi (El (mu X j)) U) (c1 j D))
        wp  = wk-⊢ {B = El (app (app M j) (fst p))} p'
        sp  = ≡-ty (t-snd wp) (cong₃ (λ X Y Z → El (pay X Y Z)) (cw _ D) (cw _ C) (cw _ i))
        wM  = ≡-ty (wk-⊢ m) (wk-MotTy D)
    in t-conv (t-sig (t-app Mj (t-fst p')) (t-ihTy (wk-⊢ dD) wM (wk-⊢ cc) (wk-⊢ k) sp)) q
  sr-desc d ih-ι with inv-ih d
  ... | q , _ = t-conv t-tt (≃-trans (≃-sym (⟶ₑ ihTy-ι)) q)
  sr-desc d (ih-σ {D = D} {S = S} {f = f} {p = p}) with inv-ih d
  ... | q , dD , m , g , c , i , k , pp with inv-dσ c
  ... | s , ff =
    let p' = t-conv pp (⟶ₑ pay-σ)
        sp = ≡-ty (t-snd p') (cong₃ (λ X Y Z → El (pay X (app Y (fst p)) Z)) (c1 _ D) (c1 _ f) (c1 _ i))
    in t-conv (t-ih dD m g (t-app ff (t-fst p')) k sp) (≃-trans (≃-sym (⟶ₑ ihTy-σ)) q)
  sr-desc d (ih-ρ {D = D} {M = M} {e = e} {j = j} {C = C} {p = p}) with inv-ih d
  ... | q , dD , m , g , c , i , k , pp with inv-dρ c
  ... | jj , cc =
    let p'  = t-conv pp (⟶ₑ pay-ρ)
        rec = t-ielim dD m g jj (t-fst p')
        sp  = ≡-ty (t-snd p') (cong₃ (λ X Y Z → El (pay X Y Z)) (c1 _ D) (c1 _ C) (c1 _ i))
        a   = ielim D M e j (fst p)
        hyp = ≡-ty (t-ih dD m g cc k sp)
                (sym (cong₃ (λ X Y Z → El (ihTy X Y Z (snd (sub (sg a) (wk p)))))
                            (c1 a D) (c1 a M) (c1 a C)
                      ◾ cong (λ P → El (ihTy D M C (snd P))) (c1 a p)))
    in t-conv (t-pair rec hyp) (≃-trans (≃-sym (⟶ₑ ihTy-ρ)) q)
    where
    _◾_ : {X : Set} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
    _◾_ = trans
  sr-desc d (ι {D = D} {M = M} {e = e} {i = i} {p = p}) with inv-ielim d
  ... | q , dD , m , g , k , cp with inv-con cp
  ... | D' , i' , q' , _ , _ , pp with mu-inj (El-inj q')
  ... | dd , ii =
    let p⊢  = t-conv pp (payEl≃ dd ii)
        R3  = El (app (app (ren w3 M) (var (fs (fs fz)))) (con (var (fs fz))))
        R2  = Pi (El (ihTy (ren w2 D) (ren w2 M) (ren w2 D) (var fz))) R3
        R3' = sub (exts (sg p)) (sub (exts (exts (sg i))) R3)
        ei  = ≡-ty (t-app g k) (cong (λ X → Pi (El (pay X X i)) (sub (exts (sg i)) R2)) (c1 i D))
        eip = ≡-ty (t-app ei p⊢)
                (cong₃ (λ X Y Z → Pi (El (ihTy X Y Z p)) R3') (c2 p i D) (c2 p i M) (c2 p i D))
        hh  = ih D M e D p
        res = ≡-ty (t-app eip (t-ih dD m g dD k p⊢))
                (cong₃ (λ X Y Z → El (app (app X Y) (con Z)))
                       (c3 hh p i M)
                       (trans (cong (sub (sg hh)) (sub-wk (sg p) (wk i))) (trans (c1 hh _) (c1 p i)))
                       (c1 hh p))
    in t-conv res q
  sr-desc d (switch-ι nt) with inv-switch d
  ... | q , _ , cs = t-conv (cases-nth cs nt) q
  sr-desc d (split-ι {a = a} {b = b} {P = P}) with inv-split d
  ... | q , S , T' , pq , body with inv-pair pq
  ... | S' , T'' , qq , da , db with sig-inj (El-inj qq)
  ... | ss , tt' =
    t-conv (≡-ty (sub-⊢₂ body (t-conv da (El≃ ss)) (t-conv db (El≃ (sub-≃ tt'))))
                 (split-ty P a b))
           q
