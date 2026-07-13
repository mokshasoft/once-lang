------------------------------------------------------------------------
-- OCP-0009 · OTT internalized, step 2 — HETEROGENEOUS equality, `coe`/`coh`,
--            and DEPENDENT `Σ` codes (the `NbEPOTTU` "remaining depth" item)
--
-- `NbEPOTTU` internalized homogeneous `eq` at first-order + `Π` codes. Full
-- OTT ("Observational Equality, Now!", Altenkirch–McBride–Swierstra) needs
-- the HETEROGENEOUS layer: value equality ACROSS types (`EQ a x b y`), TYPE
-- equality as evidence (`EQU a b`), coercion `coe : EQU a b → El a → El b`,
-- and coherence `coh : (q : EQU a b) (x : El a) → EQ a x b (coe q x)` —
-- "coercion doesn't change the value, observably." This module builds that
-- layer, with genuinely DEPENDENT `Σ` codes.
--
-- Design points:
--   * `EQU` is DATA (5 constructors), so `coe`/`coh` and the lemma suite
--     recurse structurally on the evidence — no mismatch clauses at all.
--   * `Σ` families are RESPECT-BUNDLED (`rb : EQ a x a y → EQU (b x) (b y)`
--     stored in the code): a raw Agda family need not respect observational
--     equality, and `rb` is exactly what `reflU` (and any client building
--     type equalities) needs. This is the setoid discipline, applied at the
--     one place the Σ-fragment needs it.
--   * The suite factors WITHOUT a big mutual block: `symE`, then `symU`,
--     then `coe`/`coh` (one mutual pair), then `transE`, then `transU` —
--     each structural on its own evidence.
--
-- WHY `Π` IS DEFERRED (the honest analysis — this is the setoid-model
-- step): for functions, `coh` at `` `π `` needs `EQ (b x) (f x) (b x₀)
-- (f x₀)` for `x`, `x₀` merely OBSERVATIONALLY equal — i.e. `f` must
-- RESPECT `EQ`, which is not provable for a raw Agda function (it is
-- exactly funext-strength); and heterogeneous transitivity at `` `π ``
-- must CONJURE a middle argument via `coe` along the domain equality.
-- Both are solved by bundling respect proofs into `El (`π …)` (the full
-- setoid universe) — `NbEPOTT` already took funext-as-a-parameter for the
-- same reason at the model level. `Σ` needs neither: pair values carry
-- their components, so every middle is already present, and the suite
-- below goes through structurally.
--
-- HEADLINE: `q-pad : EQU `TupPad `Tup` — a type equality between two
-- genuinely dependent Σ codes whose INDICES differ by `n+0` (the
-- `NbEPOTTU` induction, reused as evidence) — and `coe q-pad` transports a
-- dependent tuple across it, computing to the identity on closed values
-- (`refl`), with `coh q-pad` certifying the transport observationally.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPOTTH where

open import normalizer.Syntax.Types
  using ( ⊤; tt; ⊥; ¬_; Σ; _,_; _≡_; refl; cong; trans; subst )

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

eqℕ : ℕ → ℕ → Set
eqℕ zero    zero    = ⊤
eqℕ zero    (suc _) = ⊥
eqℕ (suc _) zero    = ⊥
eqℕ (suc m) (suc n) = eqℕ m n

eqℕ-refl : ∀ n → eqℕ n n
eqℕ-refl zero    = tt
eqℕ-refl (suc n) = eqℕ-refl n

sym-eqℕ : ∀ m n → eqℕ m n → eqℕ n m
sym-eqℕ zero    zero    e = tt
sym-eqℕ zero    (suc n) ()
sym-eqℕ (suc m) zero    ()
sym-eqℕ (suc m) (suc n) e = sym-eqℕ m n e

trans-eqℕ : ∀ m n k → eqℕ m n → eqℕ n k → eqℕ m k
trans-eqℕ zero    zero    zero    e₁ e₂ = tt
trans-eqℕ zero    zero    (suc k) e₁ ()
trans-eqℕ zero    (suc n) k       () e₂
trans-eqℕ (suc m) zero    k       () e₂
trans-eqℕ (suc m) (suc n) zero    e₁ ()
trans-eqℕ (suc m) (suc n) (suc k) e₁ e₂ = trans-eqℕ m n k e₁ e₂

eqℕ-sound : ∀ m n → eqℕ m n → m ≡ n
eqℕ-sound zero    zero    e = refl
eqℕ-sound zero    (suc n) ()
eqℕ-sound (suc m) zero    ()
eqℕ-sound (suc m) (suc n) e = cong suc (eqℕ-sound m n e)

------------------------------------------------------------------------
-- The universe (Σ-fragment), its decoding, heterogeneous value equality,
-- and type equality as data — one inductive-inductive-recursive block.
------------------------------------------------------------------------

data U : Set
El : U → Set
EQ : (a : U) → El a → (b : U) → El b → Set
data EQU : U → U → Set

data U where
  `⊥ `unit `nat : U
  `σ : (a : U) (b : El a → U)
       (rb : ∀ {x y} → EQ a x a y → EQU (b x) (b y)) → U

El `⊥           = ⊥
El `unit        = ⊤
El `nat         = ℕ
El (`σ a b rb)  = Σ (El a) (λ x → El (b x))

EQ `⊥    _ `⊥    _ = ⊤
EQ `unit _ `unit _ = ⊤
EQ `nat  m `nat  n = eqℕ m n
EQ (`σ a b rb) (x , p) (`σ a' b' rb') (x' , p') =
  Σ (EQ a x a' x') (λ _ → EQ (b x) p (b' x') p')
EQ _ _ _ _ = ⊥

data EQU where
  q⊥    : EQU `⊥ `⊥
  qunit : EQU `unit `unit
  qnat  : EQU `nat `nat
  qσ    : ∀ {a : U} {b : El a → U}
          {rb  : ∀ {x y} → EQ a x a y → EQU (b x) (b y)}
          {a' : U} {b' : El a' → U}
          {rb' : ∀ {x y} → EQ a' x a' y → EQU (b' x) (b' y)}
          (qa : EQU a a')
          (qb : ∀ {x x'} → EQ a x a' x' → EQU (b x) (b' x'))
        → EQU (`σ a b rb) (`σ a' b' rb')

------------------------------------------------------------------------
-- The suite. Reflexivity: the bundled family-respect is exactly what
-- `reflU` at `` `σ `` needs — the setoid discipline paying its way.
------------------------------------------------------------------------

reflE : ∀ a (x : El a) → EQ a x a x
reflE `⊥           x       = tt
reflE `unit        x       = tt
reflE `nat         n       = eqℕ-refl n
reflE (`σ a b rb)  (x , p) = reflE a x , reflE (b x) p

reflU : ∀ a → EQU a a
reflU `⊥          = q⊥
reflU `unit       = qunit
reflU `nat        = qnat
reflU (`σ a b rb) = qσ (reflU a) (λ {x} {y} e → rb {x} {y} e)

symE : ∀ {a b} (q : EQU a b) {x y} → EQ a x b y → EQ b y a x
symE q⊥          e         = tt
symE qunit       e         = tt
symE (qnat) {m} {n} e      = sym-eqℕ m n e
symE (qσ qa qb) {x , p} {x' , p'} (ex , ep) =
  symE qa ex , symE (qb ex) ep

symU : ∀ {a b} → EQU a b → EQU b a
symU q⊥         = q⊥
symU qunit      = qunit
symU qnat       = qnat
symU (qσ qa qb) = qσ (symU qa) (λ e → symU (qb (symE (symU qa) e)))

-- Coercion + coherence, mutually, structural on the evidence.
mutual
  coe : ∀ {a b} → EQU a b → El a → El b
  coe q⊥          x       = x
  coe qunit       x       = x
  coe qnat        n       = n
  coe (qσ qa qb)  (x , p) = coe qa x , coe (qb (coh qa x)) p

  coh : ∀ {a b} (q : EQU a b) (x : El a) → EQ a x b (coe q x)
  coh q⊥          x       = tt
  coh qunit       x       = tt
  coh qnat        n       = eqℕ-refl n
  coh (qσ qa qb)  (x , p) = coh qa x , coh (qb (coh qa x)) p

-- Heterogeneous transitivity — over Σ, the pair values provide every
-- middle, so it is plainly structural (contrast the `Π` analysis above).
transE : ∀ {a b c} (qab : EQU a b) (qbc : EQU b c) {x y z}
       → EQ a x b y → EQ b y c z → EQ a x c z
transE q⊥          q⊥            e₁ e₂ = tt
transE qunit       qunit         e₁ e₂ = tt
transE qnat qnat {m} {n} {k}     e₁ e₂ = trans-eqℕ m n k e₁ e₂
transE (qσ qa qb) (qσ qa' qb') {x , p} {y , r} {z , s} (ex₁ , ep₁) (ex₂ , ep₂) =
  transE qa qa' ex₁ ex₂ , transE (qb ex₁) (qb' ex₂) ep₁ ep₂

-- Composition of type equalities. At `` `σ `` the composite family equality
-- needs a middle INDEX — conjured by `coe`/`coh` along the first equality
-- (available because it is evidence, not a bare value equality).
transU : ∀ {a b c} → EQU a b → EQU b c → EQU a c
transU q⊥          q⊥           = q⊥
transU qunit       qunit        = qunit
transU qnat        qnat         = qnat
transU (qσ qa qb) (qσ qa' qb') =
  qσ (transU qa qa')
     (λ {x₁} {x₃} e →
        -- middle index: coerce x₁ across the first equality
        transU (qb (coh qa x₁))
               (qb' (transE (symU qa) (transU qa qa')
                            (symE qa (coh qa x₁)) e)))

------------------------------------------------------------------------
-- HEADLINE — transport a dependent pair along an `n+0` type equality.
------------------------------------------------------------------------

add : ℕ → ℕ → ℕ
add zero    n = n
add (suc m) n = suc (add m n)

n+0 : ∀ n → eqℕ (add n zero) n
n+0 zero    = tt
n+0 (suc n) = n+0 n

-- A genuinely dependent family: n-tuples of naturals.
P : ℕ → U
P zero    = `unit
P (suc n) = `σ `nat (λ _ → P n) (λ _ → reflU (P n))

-- Family respect, via first-order reflection (`eqℕ` → `≡` → `subst`).
P-resp : ∀ {m n} → EQ `nat m `nat n → EQU (P m) (P n)
P-resp {m} {n} e =
  subst (λ k → EQU (P m) (P k)) (eqℕ-sound m n e) (reflU (P m))

`Tup : U
`Tup = `σ `nat P (λ {m} {n} e → P-resp {m} {n} e)

`TupPad : U
`TupPad = `σ `nat (λ n → P (add n zero))
             (λ {m} {n} e →
                subst (λ k → EQU (P (add m zero)) (P (add k zero)))
                      (eqℕ-sound m n e)
                      (reflU (P (add m zero))))

-- THE type equality between the two dependent Σ codes: their index
-- families differ by `n+0` — the `NbEPOTTU` induction, reused as evidence.
q-pad : EQU `TupPad `Tup
q-pad = qσ qnat
           (λ {m} {n} e →
              subst (λ k → EQU (P (add m zero)) (P k))
                    (trans (eqℕ-sound (add m zero) m (n+0 m))
                           (eqℕ-sound m n e))
                    (reflU (P (add m zero))))

-- Transport computes to the identity on a closed dependent tuple…
two₂ five₂ seven₂ : ℕ
two₂   = suc (suc zero)
five₂  = suc (suc (suc two₂))
seven₂ = suc (suc five₂)

pad : El `TupPad
pad = two₂ , (five₂ , (seven₂ , tt))

_ : coe q-pad pad ≡ (two₂ , (five₂ , (seven₂ , tt)))
_ = refl

-- …and `coh` certifies the transport observationally: coercion changed
-- nothing, as witnessed by the heterogeneous equality itself.
_ : EQ `TupPad pad `Tup (coe q-pad pad)
_ = coh q-pad pad
