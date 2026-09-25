------------------------------------------------------------------------
-- OCP-0009 · dHoTT — DECIDABLE SYNTACTIC EQUALITY of the raw syntax
--
-- ★ WHY THIS MODULE.  `dec-conv-typed` (Metatheory/Fundamental) decides
--   conversion of well-typed terms and asks for exactly ONE input: a
--   decision procedure for `_≡_` on `RTm`.  It is also step (a) of the
--   bidirectional type checker — every comparison a checker makes bottoms
--   out here.
--
-- ★★ HOW: ENCODE, DON'T ENUMERATE.  The textbook `_≟_` needs a no-confusion
--   clause for every PAIR of distinct constructors — ~30² for `RTm` alone.
--   Instead every sort is encoded into one first-order `Tree` (a tag plus
--   children), and a partial DECODER is shown to invert it:
--       dec-enc : decTm Γ (encTm t) ≡ just t
--   ⇒ `encTm` is injective, and `_≟_` on `Tree` (TWO constructors) transfers.
--   Cost is ONE clause per constructor per function: linear, not quadratic.
--
-- ⚠ THE DECODER'S CATCH-ALL IS INTENTIONAL (a malformed tree ↦ `nothing`).
--   Coverage is guaranteed by `enc*` and `dec-enc*`, which have NO
--   catch-all: a constructor missing from either is a coverage error.
--   A constructor missing from `dec*` alone makes `dec-enc` fail to
--   typecheck (`nothing != just …`).  So no former can be silently dropped.
--
-- ⚠ Tags need only be distinct WITHIN a sort — each sort has its own
--   decoder.  `Cx` needs no encoding: it is an index, fixed by the type.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.DecEq where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; ¬_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax

------------------------------------------------------------------------
-- Decisions.  ⚠ This is THE `Dec` of the kernel: `Algorithm/DecideConversion`
-- re-exports it, so `dec-conv-typed`'s `dec-eq` parameter is exactly `_≟Tm_`.
------------------------------------------------------------------------

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- 1. The carrier: first-order trees, and their equality.
------------------------------------------------------------------------

data Tree : Set where
  nat  : ℕ → Tree
  node : ℕ → ℕ → List Tree → Tree   -- tag = (page, index), both < 10:
                                     -- Agda rejects pattern literals > 20

_≟ℕ_ : (m n : ℕ) → Dec (m ≡ n)
zero  ≟ℕ zero  = yes refl
zero  ≟ℕ suc n = no (λ ())
suc m ≟ℕ zero  = no (λ ())
suc m ≟ℕ suc n with m ≟ℕ n
... | yes refl = yes refl
... | no  m≢n  = no (λ { refl → m≢n refl })

mutual
  _≟T_ : (s t : Tree) → Dec (s ≡ t)
  nat m    ≟T nat n    with m ≟ℕ n
  ... | yes refl = yes refl
  ... | no  m≢n  = no (λ { refl → m≢n refl })
  nat _      ≟T node _ _ _ = no (λ ())
  node _ _ _ ≟T nat _      = no (λ ())
  node g k ss ≟T node h j ts with g ≟ℕ h | k ≟ℕ j | ss ≟L ts
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no  g≢h  | _        | _        = no (λ { refl → g≢h refl })
  ... | yes _    | no  k≢j  | _        = no (λ { refl → k≢j refl })
  ... | yes _    | yes _    | no  s≢t  = no (λ { refl → s≢t refl })

  _≟L_ : (ss ts : List Tree) → Dec (ss ≡ ts)
  []       ≟L []       = yes refl
  []       ≟L (_ ∷ _)  = no (λ ())
  (_ ∷ _)  ≟L []       = no (λ ())
  (s ∷ ss) ≟L (t ∷ ts) with s ≟T t | ss ≟L ts
  ... | yes refl | yes refl = yes refl
  ... | no  s≢t  | _        = no (λ { refl → s≢t refl })
  ... | yes _    | no  e    = no (λ { refl → e refl })

------------------------------------------------------------------------
-- 2. Encoding.  ⚠ NO catch-all anywhere in this section.
------------------------------------------------------------------------

encVar : Var Γ → ℕ
encVar vz     = zero
encVar (vs x) = suc (encVar x)

-- shorthands for the node arities
n0 : ℕ → ℕ → Tree
n0 g k = node g k []
n1 : ℕ → ℕ → Tree → Tree
n1 g k a = node g k (a ∷ [])
n2 : ℕ → ℕ → Tree → Tree → Tree
n2 g k a b = node g k (a ∷ b ∷ [])
n3 : ℕ → ℕ → Tree → Tree → Tree → Tree
n3 g k a b c = node g k (a ∷ b ∷ c ∷ [])
n4 : ℕ → ℕ → Tree → Tree → Tree → Tree → Tree
n4 g k a b c d = node g k (a ∷ b ∷ c ∷ d ∷ [])
n5 : ℕ → ℕ → Tree → Tree → Tree → Tree → Tree → Tree
n5 g k a b c d e = node g k (a ∷ b ∷ c ∷ d ∷ e ∷ [])

mutual
  encTy : RTy Γ → Tree
  encTy base          = n0 0 0
  encTy U             = n0 0 1
  encTy (Π A B)       = n2 0 2 (encTy A) (encTy B)
  encTy (Σ' A B)      = n2 0 3 (encTy A) (encTy B)
  encTy (El t)        = n1 0 4 (encTm t)
  encTy (Hom A t u)   = n3 0 5 (encTy A) (encTm t) (encTm u)
  encTy Unit          = n0 0 6
  encTy Nat           = n0 0 7
  encTy (Id A t u)    = n3 0 8 (encTy A) (encTm t) (encTm u)
  encTy (Mu D)        = n1 0 9 (encDesc D)
  encTy (IMu D I i)   = n3 1 0 (encIDesc D) (encTy I) (encTm i)

  encTm : RTm Γ → Tree
  encTm (var x)             = n1 0 0 (nat (encVar x))
  encTm (lam t)             = n1 0 1 (encTm t)
  encTm (app t u)           = n2 0 2 (encTm t) (encTm u)
  encTm (pair t u)          = n2 0 3 (encTm t) (encTm u)
  encTm (absurd t u)        = n2 0 4 (encTm t) (encTm u)
  encTm (ordtr a t u p q)   = n5 0 5 (encTm a) (encTm t) (encTm u) (encTm p) (encTm q)
  encTm (fst t)             = n1 0 6 (encTm t)
  encTm (snd t)             = n1 0 7 (encTm t)
  encTm ⌜base⌝              = n0 0 8
  encTm (⌜Π⌝ a b)           = n2 0 9 (encTm a) (encTm b)
  encTm (⌜Σ⌝ a b)           = n2 1 0 (encTm a) (encTm b)
  encTm (⌜Hom⌝ c t u)       = n3 1 1 (encTm c) (encTm t) (encTm u)
  encTm (hrefl c t)         = n2 1 2 (encTm c) (encTm t)
  encTm (tr d p e)          = n3 1 3 (encTm d) (encTm p) (encTm e)
  encTm (ap c b p)          = n3 1 4 (encTm c) (encTm b) (encTm p)
  encTm (⌜Id⌝ c t u)        = n3 1 5 (encTm c) (encTm t) (encTm u)
  encTm (idrefl c t)        = n2 1 6 (encTm c) (encTm t)
  encTm (jsub d p e)        = n3 1 7 (encTm d) (encTm p) (encTm e)
  encTm unit                = n0 1 8
  encTm nzero               = n0 1 9
  encTm (nsuc t)            = n1 2 0 (encTm t)
  encTm (natrec z s n)      = n3 2 1 (encTm z) (encTm s) (encTm n)
  encTm (con k p)           = n2 2 2 (nat k) (encTm p)
  encTm (elim D ms t)       = n3 2 3 (encDesc D) (encTm ms) (encTm t)
  encTm (icon k p)          = n2 2 4 (nat k) (encTm p)
  encTm (ielim D ms i t)    = n4 2 5 (encIDesc D) (encTm ms) (encTm i) (encTm t)
  encTm ⌜Nat⌝               = n0 2 6
  encTm (⌜Mu⌝ D)            = n1 2 7 (encDesc D)
  encTm (⌜IMu⌝ D I i)       = n3 2 8 (encIDesc D) (encTy I) (encTm i)
  encTm ⌜Unit⌝              = n0 2 9

  encDCon : DCon → Tree
  encDCon dι       = n0 0 0
  encDCon (dρ C)   = n1 0 1 (encDCon C)
  encDCon (dκ A C) = n2 0 2 (encTy A) (encDCon C)

  encDesc : Desc → Tree
  encDesc dnil    = n0 0 0
  encDesc (C ◃ D) = n2 0 1 (encDCon C) (encDesc D)

  encICon : ICon Δ → Tree
  encICon iι       = n0 0 0
  encICon (iρ t C) = n2 0 1 (encTm t) (encICon C)
  encICon (iκ t C) = n2 0 2 (encTm t) (encICon C)

  encIDesc : IDesc → Tree
  encIDesc inil    = n0 0 0
  encIDesc (C ◂ D) = n2 0 1 (encICon C) (encIDesc D)

------------------------------------------------------------------------
-- 3. Decoding — partial; the catch-alls answer `nothing` on malformed trees.
------------------------------------------------------------------------

infixl 1 _>>=_
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>= f = f a
nothing >>= f = nothing

-- ★ stepping through a decoder whose sub-decode is known to succeed.
--   ⚠ Chained in DECODE ORDER; the repo's `_≡_` is not the BUILTIN
--   equality, so `rewrite` is unavailable.
infixr 0 _⟫_
_⟫_ : {A B : Set} {m : Maybe A} {a : A} {f : A → Maybe B} {r : Maybe B} →
      m ≡ just a → f a ≡ r → (m >>= f) ≡ r
refl ⟫ p = p

decVarN : (Γ : Cx) → ℕ → Maybe (Var Γ)
decVarN ε       _       = nothing
decVarN (Γ ∙)   zero    = just vz
decVarN (Γ ∙)   (suc n) = decVarN Γ n >>= λ x → just (vs x)

mutual
  decTy : (Γ : Cx) → Tree → Maybe (RTy Γ)
  decTy Γ (node 0 0 [])               = just base
  decTy Γ (node 0 1 [])               = just U
  decTy Γ (node 0 2 (a ∷ b ∷ []))     = decTy Γ a >>= λ A → decTy (Γ ∙) b >>= λ B → just (Π A B)
  decTy Γ (node 0 3 (a ∷ b ∷ []))     = decTy Γ a >>= λ A → decTy (Γ ∙) b >>= λ B → just (Σ' A B)
  decTy Γ (node 0 4 (a ∷ []))         = decTm Γ a >>= λ t → just (El t)
  decTy Γ (node 0 5 (a ∷ b ∷ c ∷ [])) = decTy Γ a >>= λ A → decTm Γ b >>= λ t → decTm Γ c >>= λ u → just (Hom A t u)
  decTy Γ (node 0 6 [])               = just Unit
  decTy Γ (node 0 7 [])               = just Nat
  decTy Γ (node 0 8 (a ∷ b ∷ c ∷ [])) = decTy Γ a >>= λ A → decTm Γ b >>= λ t → decTm Γ c >>= λ u → just (Id A t u)
  decTy Γ (node 0 9 (a ∷ []))         = decDesc a >>= λ D → just (Mu D)
  decTy Γ (node 1 0 (a ∷ b ∷ c ∷ [])) = decIDesc a >>= λ D → decTy ε b >>= λ I → decTm Γ c >>= λ i → just (IMu D I i)
  decTy Γ _ = nothing

  decTm : (Γ : Cx) → Tree → Maybe (RTm Γ)
  decTm Γ (node 0 0 (nat n ∷ []))      = decVarN Γ n >>= λ x → just (var x)
  decTm Γ (node 0 1 (a ∷ []))          = decTm (Γ ∙) a >>= λ t → just (lam t)
  decTm Γ (node 0 2 (a ∷ b ∷ []))      = decTm Γ a >>= λ t → decTm Γ b >>= λ u → just (app t u)
  decTm Γ (node 0 3 (a ∷ b ∷ []))      = decTm Γ a >>= λ t → decTm Γ b >>= λ u → just (pair t u)
  decTm Γ (node 0 4 (a ∷ b ∷ []))      = decTm Γ a >>= λ t → decTm Γ b >>= λ u → just (absurd t u)
  decTm Γ (node 0 5 (a ∷ b ∷ c ∷ d ∷ e ∷ [])) =
    decTm Γ a >>= λ a' → decTm Γ b >>= λ t → decTm Γ c >>= λ u →
    decTm Γ d >>= λ p → decTm Γ e >>= λ q → just (ordtr a' t u p q)
  decTm Γ (node 0 6 (a ∷ []))          = decTm Γ a >>= λ t → just (fst t)
  decTm Γ (node 0 7 (a ∷ []))          = decTm Γ a >>= λ t → just (snd t)
  decTm Γ (node 0 8 [])                = just ⌜base⌝
  decTm Γ (node 0 9 (a ∷ b ∷ []))      = decTm Γ a >>= λ t → decTm (Γ ∙) b >>= λ u → just (⌜Π⌝ t u)
  decTm Γ (node 1 0 (a ∷ b ∷ []))     = decTm Γ a >>= λ t → decTm (Γ ∙) b >>= λ u → just (⌜Σ⌝ t u)
  decTm Γ (node 1 1 (a ∷ b ∷ c ∷ [])) = decTm Γ a >>= λ c' → decTm Γ b >>= λ t → decTm Γ c >>= λ u → just (⌜Hom⌝ c' t u)
  decTm Γ (node 1 2 (a ∷ b ∷ []))     = decTm Γ a >>= λ c → decTm Γ b >>= λ t → just (hrefl c t)
  decTm Γ (node 1 3 (a ∷ b ∷ c ∷ [])) = decTm (Γ ∙) a >>= λ d → decTm Γ b >>= λ p → decTm Γ c >>= λ e → just (tr d p e)
  decTm Γ (node 1 4 (a ∷ b ∷ c ∷ [])) = decTm Γ a >>= λ c' → decTm (Γ ∙) b >>= λ b' → decTm Γ c >>= λ p → just (ap c' b' p)
  decTm Γ (node 1 5 (a ∷ b ∷ c ∷ [])) = decTm Γ a >>= λ c' → decTm Γ b >>= λ t → decTm Γ c >>= λ u → just (⌜Id⌝ c' t u)
  decTm Γ (node 1 6 (a ∷ b ∷ []))     = decTm Γ a >>= λ c → decTm Γ b >>= λ t → just (idrefl c t)
  decTm Γ (node 1 7 (a ∷ b ∷ c ∷ [])) = decTm (Γ ∙) a >>= λ d → decTm Γ b >>= λ p → decTm Γ c >>= λ e → just (jsub d p e)
  decTm Γ (node 1 8 [])               = just unit
  decTm Γ (node 1 9 [])               = just nzero
  decTm Γ (node 2 0 (a ∷ []))         = decTm Γ a >>= λ t → just (nsuc t)
  decTm Γ (node 2 1 (a ∷ b ∷ c ∷ [])) = decTm Γ a >>= λ z → decTm ((Γ ∙) ∙) b >>= λ s → decTm Γ c >>= λ n → just (natrec z s n)
  decTm Γ (node 2 2 (nat k ∷ b ∷ [])) = decTm Γ b >>= λ p → just (con k p)
  decTm Γ (node 2 3 (a ∷ b ∷ c ∷ [])) = decDesc a >>= λ D → decTm Γ b >>= λ ms → decTm Γ c >>= λ t → just (elim D ms t)
  decTm Γ (node 2 4 (nat k ∷ b ∷ [])) = decTm Γ b >>= λ p → just (icon k p)
  decTm Γ (node 2 5 (a ∷ b ∷ c ∷ d ∷ [])) =
    decIDesc a >>= λ D → decTm Γ b >>= λ ms → decTm Γ c >>= λ i → decTm Γ d >>= λ t → just (ielim D ms i t)
  decTm Γ (node 2 6 [])               = just ⌜Nat⌝
  decTm Γ (node 2 7 (a ∷ []))         = decDesc a >>= λ D → just (⌜Mu⌝ D)
  decTm Γ (node 2 8 (a ∷ b ∷ c ∷ [])) = decIDesc a >>= λ D → decTy ε b >>= λ I → decTm Γ c >>= λ i → just (⌜IMu⌝ D I i)
  decTm Γ (node 2 9 [])               = just ⌜Unit⌝
  decTm Γ _ = nothing

  decDCon : Tree → Maybe DCon
  decDCon (node 0 0 [])           = just dι
  decDCon (node 0 1 (a ∷ []))     = decDCon a >>= λ C → just (dρ C)
  decDCon (node 0 2 (a ∷ b ∷ [])) = decTy ε a >>= λ A → decDCon b >>= λ C → just (dκ A C)
  decDCon _ = nothing

  decDesc : Tree → Maybe Desc
  decDesc (node 0 0 [])           = just dnil
  decDesc (node 0 1 (a ∷ b ∷ [])) = decDCon a >>= λ C → decDesc b >>= λ D → just (C ◃ D)
  decDesc _ = nothing

  decICon : (Δ : Cx) → Tree → Maybe (ICon Δ)
  decICon Δ (node 0 0 [])           = just iι
  decICon Δ (node 0 1 (a ∷ b ∷ [])) = decTm Δ a >>= λ t → decICon (Δ ∙) b >>= λ C → just (iρ t C)
  decICon Δ (node 0 2 (a ∷ b ∷ [])) = decTm Δ a >>= λ t → decICon (Δ ∙) b >>= λ C → just (iκ t C)
  decICon Δ _ = nothing

  decIDesc : Tree → Maybe IDesc
  decIDesc (node 0 0 [])           = just inil
  decIDesc (node 0 1 (a ∷ b ∷ [])) = decICon (ε ∙) a >>= λ C → decIDesc b >>= λ D → just (C ◂ D)
  decIDesc _ = nothing

------------------------------------------------------------------------
-- 4. ★ The decoder inverts the encoder.  ⚠ NO catch-all.
------------------------------------------------------------------------

dec-encVar : (x : Var Γ) → decVarN Γ (encVar x) ≡ just x
dec-encVar vz = refl
dec-encVar (vs x) = dec-encVar x ⟫ refl

mutual
  dec-encTy : (A : RTy Γ) → decTy Γ (encTy A) ≡ just A
  dec-encTy base = refl
  dec-encTy U = refl
  dec-encTy (Π A B) = dec-encTy A ⟫ dec-encTy B ⟫ refl
  dec-encTy (Σ' A B) = dec-encTy A ⟫ dec-encTy B ⟫ refl
  dec-encTy (El t) = dec-encTm t ⟫ refl
  dec-encTy (Hom A t u) = dec-encTy A ⟫ dec-encTm t ⟫ dec-encTm u ⟫ refl
  dec-encTy Unit = refl
  dec-encTy Nat = refl
  dec-encTy (Id A t u) = dec-encTy A ⟫ dec-encTm t ⟫ dec-encTm u ⟫ refl
  dec-encTy (Mu D) = dec-encDesc D ⟫ refl
  dec-encTy (IMu D I i) = dec-encIDesc D ⟫ dec-encTy I ⟫ dec-encTm i ⟫ refl

  dec-encTm : (t : RTm Γ) → decTm Γ (encTm t) ≡ just t
  dec-encTm (var x) = dec-encVar x ⟫ refl
  dec-encTm (lam t) = dec-encTm t ⟫ refl
  dec-encTm (app t u) = dec-encTm t ⟫ dec-encTm u ⟫ refl
  dec-encTm (pair t u) = dec-encTm t ⟫ dec-encTm u ⟫ refl
  dec-encTm (absurd t u) = dec-encTm t ⟫ dec-encTm u ⟫ refl
  dec-encTm (ordtr a t u p q) = dec-encTm a ⟫ dec-encTm t ⟫ dec-encTm u ⟫ dec-encTm p ⟫ dec-encTm q ⟫ refl
  dec-encTm (fst t) = dec-encTm t ⟫ refl
  dec-encTm (snd t) = dec-encTm t ⟫ refl
  dec-encTm ⌜base⌝ = refl
  dec-encTm (⌜Π⌝ a b) = dec-encTm a ⟫ dec-encTm b ⟫ refl
  dec-encTm (⌜Σ⌝ a b) = dec-encTm a ⟫ dec-encTm b ⟫ refl
  dec-encTm (⌜Hom⌝ c t u) = dec-encTm c ⟫ dec-encTm t ⟫ dec-encTm u ⟫ refl
  dec-encTm (hrefl c t) = dec-encTm c ⟫ dec-encTm t ⟫ refl
  dec-encTm (tr d p e) = dec-encTm d ⟫ dec-encTm p ⟫ dec-encTm e ⟫ refl
  dec-encTm (ap c b p) = dec-encTm c ⟫ dec-encTm b ⟫ dec-encTm p ⟫ refl
  dec-encTm (⌜Id⌝ c t u) = dec-encTm c ⟫ dec-encTm t ⟫ dec-encTm u ⟫ refl
  dec-encTm (idrefl c t) = dec-encTm c ⟫ dec-encTm t ⟫ refl
  dec-encTm (jsub d p e) = dec-encTm d ⟫ dec-encTm p ⟫ dec-encTm e ⟫ refl
  dec-encTm unit = refl
  dec-encTm nzero = refl
  dec-encTm (nsuc t) = dec-encTm t ⟫ refl
  dec-encTm (natrec z s n) = dec-encTm z ⟫ dec-encTm s ⟫ dec-encTm n ⟫ refl
  dec-encTm (con k p) = dec-encTm p ⟫ refl
  dec-encTm (elim D ms t) = dec-encDesc D ⟫ dec-encTm ms ⟫ dec-encTm t ⟫ refl
  dec-encTm (icon k p) = dec-encTm p ⟫ refl
  dec-encTm (ielim D ms i t) = dec-encIDesc D ⟫ dec-encTm ms ⟫ dec-encTm i ⟫ dec-encTm t ⟫ refl
  dec-encTm ⌜Nat⌝ = refl
  dec-encTm (⌜Mu⌝ D) = dec-encDesc D ⟫ refl
  dec-encTm (⌜IMu⌝ D I i) = dec-encIDesc D ⟫ dec-encTy I ⟫ dec-encTm i ⟫ refl
  dec-encTm ⌜Unit⌝ = refl

  dec-encDCon : (C : DCon) → decDCon (encDCon C) ≡ just C
  dec-encDCon dι = refl
  dec-encDCon (dρ C) = dec-encDCon C ⟫ refl
  dec-encDCon (dκ A C) = dec-encTy A ⟫ dec-encDCon C ⟫ refl

  dec-encDesc : (D : Desc) → decDesc (encDesc D) ≡ just D
  dec-encDesc dnil = refl
  dec-encDesc (C ◃ D) = dec-encDCon C ⟫ dec-encDesc D ⟫ refl

  dec-encICon : (C : ICon Δ) → decICon Δ (encICon C) ≡ just C
  dec-encICon iι = refl
  dec-encICon (iρ t C) = dec-encTm t ⟫ dec-encICon C ⟫ refl
  dec-encICon (iκ t C) = dec-encTm t ⟫ dec-encICon C ⟫ refl

  dec-encIDesc : (D : IDesc) → decIDesc (encIDesc D) ≡ just D
  dec-encIDesc inil = refl
  dec-encIDesc (C ◂ D) = dec-encICon C ⟫ dec-encIDesc D ⟫ refl

------------------------------------------------------------------------
-- 5. Injectivity, and the decisions.
------------------------------------------------------------------------

private
  just-inj : {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  -- A left inverse (up to `just`) makes the encoding injective.
  inj : {X : Set} (enc : X → Tree) (dec : Tree → Maybe X) →
        (∀ x → dec (enc x) ≡ just x) → ∀ {x y} → enc x ≡ enc y → x ≡ y
  inj enc dec de {x} {y} e =
    just-inj (trans (sym (de x)) (trans (cong dec e) (de y)))

  decide : {X : Set} (enc : X → Tree) (dec : Tree → Maybe X) →
           (∀ x → dec (enc x) ≡ just x) → (x y : X) → Dec (x ≡ y)
  decide enc dec de x y with enc x ≟T enc y
  ... | yes e = yes (inj enc dec de e)
  ... | no ne = no (λ x≡y → ne (cong enc x≡y))

_≟Var_ : (x y : Var Γ) → Dec (x ≡ y)
_≟Var_ {Γ} x y = decide (λ v → nat (encVar v)) dv (λ v → dec-encVar v) x y
  where
    dv : Tree → Maybe (Var Γ)
    dv (nat n) = decVarN Γ n
    dv _       = nothing

_≟Ty_ : (A B : RTy Γ) → Dec (A ≡ B)
_≟Ty_ {Γ} = decide encTy (decTy Γ) dec-encTy

_≟Tm_ : (t u : RTm Γ) → Dec (t ≡ u)
_≟Tm_ {Γ} = decide encTm (decTm Γ) dec-encTm

_≟DCon_ : (C C' : DCon) → Dec (C ≡ C')
_≟DCon_ = decide encDCon decDCon dec-encDCon

_≟Desc_ : (D D' : Desc) → Dec (D ≡ D')
_≟Desc_ = decide encDesc decDesc dec-encDesc

_≟ICon_ : (C C' : ICon Δ) → Dec (C ≡ C')
_≟ICon_ {Δ} = decide encICon (decICon Δ) dec-encICon

_≟IDesc_ : (D D' : IDesc) → Dec (D ≡ D')
_≟IDesc_ = decide encIDesc decIDesc dec-encIDesc

------------------------------------------------------------------------
-- 6. NON-VACUITY — the decisions RUN, both ways.
------------------------------------------------------------------------

private
  ⌊_⌋ : {P : Set} → Dec P → Bool
  ⌊ yes _ ⌋ = true
  ⌊ no  _ ⌋ = false

  t₁ t₂ : RTm (ε ∙)
  t₁ = app (lam (var vz)) (var vz)
  t₂ = app (lam (var (vs vz))) (var vz)   -- differs only in a DEEP variable

  runs-yes : ⌊ t₁ ≟Tm t₁ ⌋ ≡ true
  runs-yes = refl

  runs-no : ⌊ t₁ ≟Tm t₂ ⌋ ≡ false
  runs-no = refl

  -- a type mentioning a description and a closed index type
  A₁ : RTy ε
  A₁ = IMu ((iρ (var vz) iι) ◂ inil) Nat nzero

  runs-ty : ⌊ A₁ ≟Ty A₁ ⌋ ≡ true
  runs-ty = refl

  runs-ty-no : ⌊ A₁ ≟Ty IMu ((iκ (var vz) iι) ◂ inil) Nat nzero ⌋ ≡ false
  runs-ty-no = refl
