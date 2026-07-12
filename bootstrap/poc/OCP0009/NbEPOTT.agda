------------------------------------------------------------------------
-- OCP-0009 · Observational Type Theory — the equality foundation (§6 step 2)
--
-- Plan §6 chose OTT (Altenkirch–McBride; Pujet–Tabareau) as the equality
-- foundation over classical cubical: it fits Once's deterministic-NbE
-- architecture and — because equality is proof-irrelevant — erases cleanly at
-- QTT multiplicity `𝟘` (cubical paths, being computational, do not).
--
-- The defining OTT move: propositional equality is defined by RECURSION ON THE
-- TYPE, not as an inductive family. Its two headline consequences, both realized
-- here for the `{Void,Unit,×,+,⇒}` fragment:
--
--   * **funext holds BY DEFINITION** — function equality IS pointwise equality
--     (`eq (A ⇒ B) f g = ∀ x → eq B (f x) (g x)`), so the transport is the
--     identity. Extensionally-equal functions are provably equal WITHOUT any
--     funext axiom (`notnot=id` below decides `not ∘ not ≡ id`).
--   * equality is an EQUIVALENCE and a congruence, structurally.
--
-- Honest scope: this is observational VALUE equality on the non-recursive
-- fragment — the funext win, which is the point. Deferred (next OTT layers,
-- named): proof-IRRELEVANCE (the `⇒` case needs the internal funext this very
-- construction provides), observational TYPE equality `Eq A B` + coercion
-- `coe`/coherence, and the `μ` case (needs the `Fix` value model). `⟦ μ F ⟧` is
-- a labelled placeholder here so `⟦_⟧` stays total.
------------------------------------------------------------------------

module poc.OCP0009.NbEPOTT where

open import normalizer.Syntax.Types

------------------------------------------------------------------------
-- Denotation of the fragment into Agda sets.
------------------------------------------------------------------------

⟦_⟧ : Ty → Set
⟦ Void ⟧  = ⊥
⟦ Unit ⟧  = ⊤
⟦ A * B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A + B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧
⟦ μ F ⟧   = ⊤          -- deferred: observational μ needs the `Fix` value model

------------------------------------------------------------------------
-- Observational equality — by recursion on the TYPE.
------------------------------------------------------------------------

eq : (A : Ty) → ⟦ A ⟧ → ⟦ A ⟧ → Set
eq Void ()
eq Unit _ _ = ⊤
eq (A * B) (a , b) (a' , b') = eq A a a' × eq B b b'
eq (A + B) (inj₁ a) (inj₁ a') = eq A a a'
eq (A + B) (inj₁ _) (inj₂ _)  = ⊥
eq (A + B) (inj₂ _) (inj₁ _)  = ⊥
eq (A + B) (inj₂ b) (inj₂ b') = eq B b b'
eq (A ⇒ B) f g = ∀ (x : ⟦ A ⟧) → eq B (f x) (g x)   -- FUNEXT, by definition
eq (μ F) _ _ = ⊤

------------------------------------------------------------------------
-- `eq` is an equivalence relation (structurally).
------------------------------------------------------------------------

eq-refl : (A : Ty) (a : ⟦ A ⟧) → eq A a a
eq-refl Void ()
eq-refl Unit _ = tt
eq-refl (A * B) (a , b) = eq-refl A a , eq-refl B b
eq-refl (A + B) (inj₁ a) = eq-refl A a
eq-refl (A + B) (inj₂ b) = eq-refl B b
eq-refl (A ⇒ B) f = λ x → eq-refl B (f x)
eq-refl (μ F) _ = tt

eq-sym : (A : Ty) (a a' : ⟦ A ⟧) → eq A a a' → eq A a' a
eq-sym Void ()
eq-sym Unit _ _ _ = tt
eq-sym (A * B) (a , b) (a' , b') (p , q) = eq-sym A a a' p , eq-sym B b b' q
eq-sym (A + B) (inj₁ a) (inj₁ a') p = eq-sym A a a' p
eq-sym (A + B) (inj₂ b) (inj₂ b') p = eq-sym B b b' p
eq-sym (A ⇒ B) f g p = λ x → eq-sym B (f x) (g x) (p x)
eq-sym (μ F) _ _ _ = tt

eq-trans : (A : Ty) (a a' a'' : ⟦ A ⟧) → eq A a a' → eq A a' a'' → eq A a a''
eq-trans Void ()
eq-trans Unit _ _ _ _ _ = tt
eq-trans (A * B) (a , b) (a' , b') (a'' , b'') (p , q) (r , s) =
  eq-trans A a a' a'' p r , eq-trans B b b' b'' q s
eq-trans (A + B) (inj₁ a) (inj₁ a') (inj₁ a'') p q = eq-trans A a a' a'' p q
eq-trans (A + B) (inj₂ b) (inj₂ b') (inj₂ b'') p q = eq-trans B b b' b'' p q
eq-trans (A ⇒ B) f g h p q = λ x → eq-trans B (f x) (g x) (h x) (p x) (q x)
eq-trans (μ F) _ _ _ _ _ = tt

------------------------------------------------------------------------
-- funext — internal, and DEFINITIONAL (both directions are the identity).
------------------------------------------------------------------------

funext : (A B : Ty) (f g : ⟦ A ⟧ → ⟦ B ⟧)
       → (∀ x → eq B (f x) (g x)) → eq (A ⇒ B) f g
funext A B f g h = h

happly : (A B : Ty) (f g : ⟦ A ⟧ → ⟦ B ⟧)
       → eq (A ⇒ B) f g → ∀ x → eq B (f x) (g x)
happly A B f g p = p

------------------------------------------------------------------------
-- The headline: extensional function equality is PROVABLE, funext-free.
-- Booleans as `Unit + Unit`; `not ∘ not ≡ id` decided pointwise by `eq`.
------------------------------------------------------------------------

Bool₂ : Ty
Bool₂ = Unit + Unit

trueᵥ falseᵥ : ⟦ Bool₂ ⟧
trueᵥ  = inj₁ tt
falseᵥ = inj₂ tt

notᵥ : ⟦ Bool₂ ⟧ → ⟦ Bool₂ ⟧
notᵥ (inj₁ _) = falseᵥ
notᵥ (inj₂ _) = trueᵥ

-- `not ∘ not ≡ id` as functions — an equation Coq/Agda need the funext axiom
-- for. Here it is a pointwise `eq`-proof, checked on both inhabitants.
notnot=id : eq (Bool₂ ⇒ Bool₂) (λ x → notᵥ (notᵥ x)) (λ x → x)
notnot=id (inj₁ _) = tt
notnot=id (inj₂ _) = tt

-- …and the same fact routed through `funext` (definitionally the identity).
notnot=id′ : eq (Bool₂ ⇒ Bool₂) (λ x → notᵥ (notᵥ x)) (λ x → x)
notnot=id′ = funext Bool₂ Bool₂ (λ x → notᵥ (notᵥ x)) (λ x → x) notnot=id

------------------------------------------------------------------------
-- OTT step 1 — observational TYPE equality `Eq` + coercion `coe`.
--
-- `Eq A B` is the type-level counterpart of `eq`. Modelling it as an INDUCTIVE
-- family (one constructor per matching head) keeps `coe` total from the
-- constructors alone — mismatched types simply have no proof, so no off-diagonal
-- cases. `Eq` is an equivalence; `coe : Eq A B → ⟦A⟧ → ⟦B⟧` transports, with the
-- function case coercing its argument BACKWARDS along `Eq-sym`.
------------------------------------------------------------------------

data Eq : Ty → Ty → Set where
  eVoid : Eq Void Void
  eUnit : Eq Unit Unit
  ePair : ∀ {A B A' B'} → Eq A A' → Eq B B' → Eq (A * B) (A' * B')
  eSum  : ∀ {A B A' B'} → Eq A A' → Eq B B' → Eq (A + B) (A' + B')
  eArr  : ∀ {A B A' B'} → Eq A A' → Eq B B' → Eq (A ⇒ B) (A' ⇒ B')
  eMu   : ∀ {F G} → Eq (μ F) (μ G)     -- deferred (Fix), permissive placeholder

Eq-refl : (A : Ty) → Eq A A
Eq-refl Void    = eVoid
Eq-refl Unit    = eUnit
Eq-refl (A * B) = ePair (Eq-refl A) (Eq-refl B)
Eq-refl (A + B) = eSum (Eq-refl A) (Eq-refl B)
Eq-refl (A ⇒ B) = eArr (Eq-refl A) (Eq-refl B)
Eq-refl (μ F)   = eMu

Eq-sym : ∀ {A B} → Eq A B → Eq B A
Eq-sym eVoid       = eVoid
Eq-sym eUnit       = eUnit
Eq-sym (ePair p q) = ePair (Eq-sym p) (Eq-sym q)
Eq-sym (eSum p q)  = eSum (Eq-sym p) (Eq-sym q)
Eq-sym (eArr p q)  = eArr (Eq-sym p) (Eq-sym q)
Eq-sym eMu         = eMu

Eq-trans : ∀ {A B C} → Eq A B → Eq B C → Eq A C
Eq-trans eVoid       eVoid       = eVoid
Eq-trans eUnit       eUnit       = eUnit
Eq-trans (ePair p q) (ePair r s) = ePair (Eq-trans p r) (Eq-trans q s)
Eq-trans (eSum p q)  (eSum r s)  = eSum (Eq-trans p r) (Eq-trans q s)
Eq-trans (eArr p q)  (eArr r s)  = eArr (Eq-trans p r) (Eq-trans q s)
Eq-trans eMu         eMu         = eMu

-- Coercion — transport a value along a type equality. Total from the six
-- constructors; the function case coerces the argument backwards (`Eq-sym`).
coe : ∀ {A B} → Eq A B → ⟦ A ⟧ → ⟦ B ⟧
coe eVoid       ()
coe eUnit       _        = tt
coe (ePair p q) (a , b)  = coe p a , coe q b
coe (eSum p q)  (inj₁ a) = inj₁ (coe p a)
coe (eSum p q)  (inj₂ b) = inj₂ (coe q b)
coe (eArr p q)  f        = λ x' → coe q (f (coe (Eq-sym p) x'))
coe eMu         _        = tt

-- Coherence, first-order fragment: coercing along reflexivity is the identity
-- (here, definitionally — each `refl` runs `coe`). (`Eq` is structural, so it
-- relates only identical types; nontrivial `coe` arrives with the index /
-- quotient layers, where `Eq (Vec m) (Vec n)` follows from `m ≡ n`.)
_ : coe (Eq-refl Bool₂) trueᵥ ≡ trueᵥ
_ = refl

_ : coe (Eq-refl Bool₂) falseᵥ ≡ falseᵥ
_ = refl

_ : coe (Eq-refl (Bool₂ * Bool₂)) (trueᵥ , falseᵥ) ≡ (trueᵥ , falseᵥ)
_ = refl

------------------------------------------------------------------------
-- OTT step 2 — PROOF-IRRELEVANCE: `eq` is a mere proposition.
--
-- The first-order cases (`Void/Unit/×/+/μ`) need nothing. The `⇒` case needs
-- meta-level function extensionality — which is EXACTLY the internal funext this
-- very construction provides. To keep the module postulate-free and the
-- dependence explicit, we take `Funext` (Agda-level) as a parameter: `eq` is a
-- strict prop in the intended (OTT) model; in this Agda MODEL the `⇒` witness is
-- discharged by the ambient funext, consistent with OTT.
------------------------------------------------------------------------

Funext : Set₁
Funext = ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
       → (∀ x → f x ≡ g x) → f ≡ g

eq-irrel : Funext → (A : Ty) (a a' : ⟦ A ⟧) (p q : eq A a a') → p ≡ q
eq-irrel fe Void ()
eq-irrel fe Unit _ _ _ _ = refl
eq-irrel fe (A * B) (a , b) (a' , b') (p₁ , p₂) (q₁ , q₂) =
  cong₂ _,_ (eq-irrel fe A a a' p₁ q₁) (eq-irrel fe B b b' p₂ q₂)
eq-irrel fe (A + B) (inj₁ a) (inj₁ a') p q = eq-irrel fe A a a' p q
eq-irrel fe (A + B) (inj₁ _) (inj₂ _) ()
eq-irrel fe (A + B) (inj₂ _) (inj₁ _) ()
eq-irrel fe (A + B) (inj₂ b) (inj₂ b') p q = eq-irrel fe B b b' p q
eq-irrel fe (A ⇒ B) f g p q = fe (λ x → eq-irrel fe B (f x) (g x) (p x) (q x))
eq-irrel fe (μ F) _ _ _ _ = refl
