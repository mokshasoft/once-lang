------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE BIDIRECTIONAL TYPE CHECKER, slice 1.
--
-- ★★ CERTIFYING, NOT BOOLEAN.  `infer`/`check`/`checkTy` return the
--   DERIVATION (`Maybe (Γ ⊢ t ∷ A)`), so soundness is CONSTRUCTION, not a
--   lemma — the `Lib/Eval` lesson ("return the term WITH its chain"): a
--   separate `check-sound` would have to reduce `check` on abstract
--   arguments, which is the stuck-on-abstract wall.  A `just d` IS the proof.
--
-- ★ FUEL IS THE TERMINATION MEASURE, deliberately.  Checking `lam t`
--   against `A` must check the DOMAIN of `A`'s normal form — a type that is
--   not a subterm of anything the call received — so structural recursion
--   cannot see termination.  Every call spends one unit.  On concrete
--   inputs this computes, which is the point; `nothing` on exhaustion is
--   INCOMPLETENESS, never unsoundness.
--
-- ★ CONVERSION (`⊢conv`): both types are normalised by `evTy`, which
--   returns the type WITH its `⟶ᵀ*` chain, and the normal forms are
--   compared by `_≟Ty_` (`Algorithm/DecEq`).  ⚠ `evTy` reduces the terms
--   inside types with `Lib/Eval.evN` — the β/fst/snd family only — so a
--   type whose convertibility needs `natrec`/`elim`/`jsub`/… computation is
--   rejected (incomplete, not wrong).
--
-- ⚠ SCOPE OF SLICE 1 (the rest answer `nothing`):
--     types  base U Π Σ' El Unit Nat Hom Id
--     terms  var lam app pair fst snd absurd ordtr unit nzero nsuc
--            ⌜base⌝ ⌜Π⌝ ⌜Σ⌝ ⌜Hom⌝ ⌜Id⌝ ⌜Nat⌝ ⌜Unit⌝ hrefl idrefl jsub
--   NOT YET: tr ap natrec con ielim dpay dih fcase psplit ⌜IMu⌝ ⌜Fin⌝ dι dσ dρ
--            fzero fsuc, types IMu Desc DIh Fin.
--   ⚠ `natrec`/`ielim`/`dih`/`fcase`/`psplit` CANNOT be done on `RTm` at all: their motive
--   lives only in the derivation (the `⊢lam` pattern), so they need an
--   ANNOTATED input syntax.  That is slice 2's design question.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.Check where
open import normalizer.Syntax.Types using ( _≡_; refl; Σ; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing
open import DirectedHoTT.Metatheory.RedCong
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ
        ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ; ⟶ᵀ*-Homᵀ; ⟶ᵀ*-Homˡ; ⟶ᵀ*-Homʳ; ⟶ᵀ*-IMu; ⟶ᵀ*-IMuᴵ; ⟶ᵀ*-IMuᴰ; ⟶ᵀ*-Desc
        ; ⟶ᵀ*-Idᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; red→≅ᵀ )
open import DirectedHoTT.Lib.Eval using ( evN )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no; _≟Ty_ )

private
  variable
    Δ : Cx
    Γ : Ctx

------------------------------------------------------------------------
-- 0. Maybe plumbing.
------------------------------------------------------------------------

infixl 1 _>>=_
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>= f = f a
nothing >>= f = nothing

------------------------------------------------------------------------
-- 1. The certifying TYPE evaluator — a type together with its chain.
------------------------------------------------------------------------

RedT : RTy Δ → Set
RedT {Δ} A = Σ (RTy Δ) (λ B → A ⟶ᵀ* B)

private
  infixl 25 _▷_
  infixr 21 _then_
  _▷_ : {A B C : RTy Δ} → A ⟶ᵀ* B → B ⟶ᵀ C → A ⟶ᵀ* C
  p ▷ r = ⟶ᵀ*-trans p (stepᵀ r doneᵀ)

  -- continue evaluating from `B`, keeping the chain from `A`
  _then_ : {A B : RTy Δ} → A ⟶ᵀ* B → RedT B → RedT A
  p then (C , q) = C , ⟶ᵀ*-trans p q

mutual
  evTy : ℕ → (A : RTy Δ) → RedT A
  evTy zero A = A , doneᵀ
  evTy (suc n) (Π A B) =
    let (A' , p) = evTy n A ; (B' , q) = evTy n B
    in  Π A' B' , ⟶ᵀ*-trans (⟶ᵀ*-Πˡ p) (⟶ᵀ*-Πʳ q)
  evTy (suc n) (Σ' A B) =
    let (A' , p) = evTy n A ; (B' , q) = evTy n B
    in  Σ' A' B' , ⟶ᵀ*-trans (⟶ᵀ*-Σˡ p) (⟶ᵀ*-Σʳ q)
  evTy (suc n) (El t) =
    let (t' , p) = evN n t in unEl n t' (⟶ᵀ*-El p)
  evTy (suc n) (Hom A t u) =
    let (A' , p) = evTy n A ; (t' , q) = evN n t ; (u' , r) = evN n u
    in  unHom n A' t' u'
          (⟶ᵀ*-trans (⟶ᵀ*-Homᵀ p) (⟶ᵀ*-trans (⟶ᵀ*-Homˡ q) (⟶ᵀ*-Homʳ r)))
  evTy (suc n) (Id A t u) =
    let (A' , p) = evTy n A ; (t' , q) = evN n t ; (u' , r) = evN n u
    in  Id A' t' u' ,
        ⟶ᵀ*-trans (⟶ᵀ*-Idᵀ p) (⟶ᵀ*-trans (⟶ᵀ*-Idˡ q) (⟶ᵀ*-Idʳ r))
  evTy (suc n) (IMu I D i) =
    let (I' , p) = evN n I ; (D' , q) = evN n D ; (i' , r) = evN n i
    in  IMu I' D' i' , ⟶ᵀ*-trans (⟶ᵀ*-IMuᴵ p) (⟶ᵀ*-trans (⟶ᵀ*-IMuᴰ q) (⟶ᵀ*-IMu r))
  evTy (suc n) (Desc I) =
    let (I' , p) = evN n I in Desc I' , ⟶ᵀ*-Desc p
  evTy (suc n) A = A , doneᵀ          -- base U Unit Nat Fin: already normal; DIh: slice 2

  -- decode a code, if the evaluated term IS one
  unEl : ℕ → {A : RTy Δ} (t : RTm Δ) → A ⟶ᵀ* El t → RedT A
  unEl n ⌜base⌝        p = base , p ▷ El-⌜base⌝
  unEl n (⌜Π⌝ c d)     p = (p ▷ El-⌜Π⌝ c d) then evTy n (Π (El c) (El d))
  unEl n (⌜Σ⌝ c d)     p = (p ▷ El-⌜Σ⌝ c d) then evTy n (Σ' (El c) (El d))
  unEl n (⌜Hom⌝ c a b) p = (p ▷ El-⌜Hom⌝ c a b) then evTy n (Hom (El c) a b)
  unEl n (⌜Id⌝ c a b)  p = (p ▷ El-⌜Id⌝ c a b) then evTy n (Id (El c) a b)
  unEl n ⌜Nat⌝         p = Nat , p ▷ El-⌜Nat⌝
  unEl n ⌜Unit⌝        p = Unit , p ▷ El-⌜Unit⌝
  unEl n (⌜IMu⌝ I D i) p = (p ▷ El-⌜IMu⌝) then evTy n (IMu I D i)
  unEl n (⌜Fin⌝ k)     p = Fin k , p ▷ El-⌜Fin⌝
  unEl n t             p = El t , p

  -- the `Hom` computation rules, on already-evaluated components
  unHom : ℕ → {X : RTy Δ} (A : RTy Δ) (t u : RTm Δ) → X ⟶ᵀ* Hom A t u → RedT X
  unHom n Nat nzero    u         p = Unit , p ▷ Hom-Nat-z u
  unHom n Nat (nsuc m) nzero     p = base , p ▷ Hom-Nat-sz m
  unHom n Nat (nsuc m) (nsuc k)  p = (p ▷ Hom-Nat-ss m k) then evTy n (Hom Nat m k)
  unHom n U   c        d         p =
    (p ▷ Hom-U c d) then evTy n (Π (El c) (El (renTm vs d)))
  unHom n (Π A B) f    g         p =
    (p ▷ Hom-Π A B f g) then
      evTy n (Π A (Hom B (app (renTm vs f) (var vz)) (app (renTm vs g) (var vz))))
  unHom n A   t        u         p = Hom A t u , p

------------------------------------------------------------------------
-- 2. Certified conversion, and weak-head VIEWS of an expected type.
------------------------------------------------------------------------

convTy : ℕ → (A B : RTy Δ) → Maybe (A ≅ᵀ B)
convTy n A B with evTy n A | evTy n B
... | A' , p | B' , q with A' ≟Ty B'
...   | yes refl = just (ctrnᵀ (red→≅ᵀ p) (csymᵀ (red→≅ᵀ q)))
...   | no  _    = nothing

-- "this type is (convertible to) a Π", with the pieces
record IsΠ (T : RTy Δ) : Set where
  constructor isΠ
  field dom : RTy Δ
        cod : RTy (Δ ∙)
        cnv : T ≅ᵀ Π dom cod

record IsΣ (T : RTy Δ) : Set where
  constructor isΣ
  field dom : RTy Δ
        cod : RTy (Δ ∙)
        cnv : T ≅ᵀ Σ' dom cod

record IsHom (T : RTy Δ) : Set where
  constructor isHom
  field amb : RTy Δ
        lhs rhs : RTm Δ
        cnv : T ≅ᵀ Hom amb lhs rhs

record IsId (T : RTy Δ) : Set where
  constructor isId
  field amb : RTy Δ
        lhs rhs : RTm Δ
        cnv : T ≅ᵀ Id amb lhs rhs

private
  viewΠ : {T : RTy Δ} → RedT T → Maybe (IsΠ T)
  viewΠ (Π A B , p) = just (isΠ A B (red→≅ᵀ p))
  viewΠ _           = nothing

  viewΣ : {T : RTy Δ} → RedT T → Maybe (IsΣ T)
  viewΣ (Σ' A B , p) = just (isΣ A B (red→≅ᵀ p))
  viewΣ _            = nothing

  viewHom : {T : RTy Δ} → RedT T → Maybe (IsHom T)
  viewHom (Hom A t u , p) = just (isHom A t u (red→≅ᵀ p))
  viewHom _               = nothing

  viewId : {T : RTy Δ} → RedT T → Maybe (IsId T)
  viewId (Id A t u , p) = just (isId A t u (red→≅ᵀ p))
  viewId _              = nothing

------------------------------------------------------------------------
-- 3. Variables — lookup always succeeds and is exact.
------------------------------------------------------------------------

Infer : (Γ : Ctx) → RTm ⌊ Γ ⌋ → Set
Infer Γ t = Σ (RTy ⌊ Γ ⌋) (λ A → Γ ⊢ t ∷ A)

lookup : (Γ : Ctx) (x : Var ⌊ Γ ⌋) → Σ (RTy ⌊ Γ ⌋) (λ A → Γ ∋ x ∷ A)
lookup (Γ ▹ A) vz     = renTy vs A , here
lookup (Γ ▹ B) (vs x) = let (A , d) = lookup Γ x in renTy vs A , there d

------------------------------------------------------------------------
-- 4. ★ The checker.  ⚠ Every recursive call spends fuel.
------------------------------------------------------------------------

private
  conv : {t : RTm ⌊ Γ ⌋} {A B : RTy ⌊ Γ ⌋} → Γ ⊢ t ∷ A → A ≅ᵀ B → Γ ⊢ t ∷ B
  conv = ⊢conv

  -- the conversion `A ≅ᵀ B` read backwards, for re-typing into an expected type
  back : {A B : RTy Δ} → A ≅ᵀ B → B ≅ᵀ A
  back = csymᵀ

mutual
  checkTy : ℕ → (Γ : Ctx) (A : RTy ⌊ Γ ⌋) → Maybe (Γ ⊢ty A)
  checkTy zero    Γ A        = nothing
  checkTy (suc n) Γ base     = just ty-base
  checkTy (suc n) Γ U        = just ty-U
  checkTy (suc n) Γ Unit     = just ty-Unit
  checkTy (suc n) Γ Nat      = just ty-Nat
  checkTy (suc n) Γ (Π A B)  =
    checkTy n Γ A >>= λ dA → checkTy n (Γ ▹ A) B >>= λ dB → just (ty-Π dA dB)
  checkTy (suc n) Γ (Σ' A B) =
    checkTy n Γ A >>= λ dA → checkTy n (Γ ▹ A) B >>= λ dB → just (ty-Σ dA dB)
  checkTy (suc n) Γ (El c)   = check n Γ c U >>= λ d → just (ty-El d)
  checkTy (suc n) Γ (Hom A t u) =
    checkTy n Γ A >>= λ dA → check n Γ t A >>= λ dt → check n Γ u A >>= λ du →
    just (ty-Hom dA dt du)
  checkTy (suc n) Γ (Id A t u) =
    checkTy n Γ A >>= λ dA → check n Γ t A >>= λ dt → check n Γ u A >>= λ du →
    just (ty-Id dA dt du)
  checkTy (suc n) Γ _        = nothing          -- Mu, IMu: slice 2

  infer : ℕ → (Γ : Ctx) (t : RTm ⌊ Γ ⌋) → Maybe (Infer Γ t)
  infer zero    Γ t       = nothing
  infer (suc n) Γ (var x) = let (A , d) = lookup Γ x in just (A , ⊢var d)
  infer (suc n) Γ (app t u) =
    infer n Γ t >>= λ { (T , dt) →
    viewΠ (evTy n T) >>= λ { (isΠ A B c) →
    check n Γ u A >>= λ du →
    just (subTy (single u) B , ⊢app (conv dt c) du) } }
  infer (suc n) Γ (fst p) =
    infer n Γ p >>= λ { (T , dp) →
    viewΣ (evTy n T) >>= λ { (isΣ A B c) →
    just (A , ⊢fst (conv dp c)) } }
  infer (suc n) Γ (snd p) =
    infer n Γ p >>= λ { (T , dp) →
    viewΣ (evTy n T) >>= λ { (isΣ A B c) →
    just (subTy (single (fst p)) B , ⊢snd (conv dp c)) } }
  infer (suc n) Γ (absurd c e) =
    check n Γ c U >>= λ dc → check n Γ e base >>= λ de →
    just (El c , ⊢absurd dc de)
  infer (suc n) Γ (ordtr a t u p q) =
    check n Γ a Nat >>= λ da → check n Γ t Nat >>= λ dt →
    check n Γ u Nat >>= λ du →
    check n Γ p (Hom Nat a t) >>= λ dp → check n Γ q (Hom Nat t u) >>= λ dq →
    just (Hom Nat a u , ⊢ordtr da dt du dp dq)
  infer (suc n) Γ unit     = just (Unit , ⊢unit)
  infer (suc n) Γ nzero    = just (Nat , ⊢nzero)
  infer (suc n) Γ (nsuc t) = check n Γ t Nat >>= λ d → just (Nat , ⊢nsuc d)
  infer (suc n) Γ ⌜base⌝   = just (U , ⊢⌜base⌝)
  infer (suc n) Γ ⌜Nat⌝    = just (U , ⊢⌜Nat⌝)
  infer (suc n) Γ ⌜Unit⌝   = just (U , ⊢⌜Unit⌝)
  infer (suc n) Γ (⌜Π⌝ c d) =
    check n Γ c U >>= λ dc → check n (Γ ▹ El c) d U >>= λ dd →
    just (U , ⊢⌜Π⌝ dc dd)
  infer (suc n) Γ (⌜Σ⌝ c d) =
    check n Γ c U >>= λ dc → check n (Γ ▹ El c) d U >>= λ dd →
    just (U , ⊢⌜Σ⌝ dc dd)
  infer (suc n) Γ (⌜Hom⌝ c a b) =
    check n Γ c U >>= λ dc → check n Γ a (El c) >>= λ da →
    check n Γ b (El c) >>= λ db → just (U , ⊢⌜Hom⌝ dc da db)
  infer (suc n) Γ (⌜Id⌝ c a b) =
    check n Γ c U >>= λ dc → check n Γ a (El c) >>= λ da →
    check n Γ b (El c) >>= λ db → just (U , ⊢⌜Id⌝ dc da db)
  infer (suc n) Γ (hrefl c t) =
    check n Γ c U >>= λ dc → check n Γ t (El c) >>= λ dt →
    just (Hom (El c) t t , ⊢hrefl dc dt)
  infer (suc n) Γ (idrefl c t) =
    check n Γ c U >>= λ dc → check n Γ t (El c) >>= λ dt →
    just (Id (El c) t t , ⊢idrefl dc dt)
  infer (suc n) Γ (jsub d p e) =
    infer n Γ p >>= λ { (T , dp) →
    viewId (evTy n T) >>= λ { (isId A t u c) →
    check n (Γ ▹ A) d U >>= λ dd →
    check n Γ t A >>= λ dt → check n Γ u A >>= λ du →
    check n Γ e (El (subTm (single t) d)) >>= λ de →
    just (El (subTm (single u) d) , ⊢jsub dd dt du (conv dp c) de) } }
  infer (suc n) Γ _ = nothing                   -- lam/pair: check only; rest: slice 2

  check : ℕ → (Γ : Ctx) (t : RTm ⌊ Γ ⌋) (A : RTy ⌊ Γ ⌋) → Maybe (Γ ⊢ t ∷ A)
  check zero    Γ t       T = nothing
  check (suc n) Γ (lam t) T =
    viewΠ (evTy n T) >>= λ { (isΠ A B c) →
    checkTy n Γ A >>= λ dA → check n (Γ ▹ A) t B >>= λ dt →
    just (conv (⊢lam dA dt) (back c)) }
  check (suc n) Γ (pair a b) T =
    viewΣ (evTy n T) >>= λ { (isΣ A B c) →
    checkTy n (Γ ▹ A) B >>= λ dB → check n Γ a A >>= λ da →
    check n Γ b (subTy (single a) B) >>= λ db →
    just (conv (⊢pair dB da db) (back c)) }
  check (suc n) Γ t T =
    infer n Γ t >>= λ { (A , d) →
    convTy n A T >>= λ c → just (conv d c) }

------------------------------------------------------------------------
-- 5. NON-VACUITY — accepts, converts, and REJECTS.
------------------------------------------------------------------------

private
  isJust : {A : Set} → Maybe A → Bool
  isJust (just _) = true
  isJust nothing  = false

  -- λx.x ∷ Π base base
  ok-id : isJust (check 10 ◇ (lam (var vz)) (Π base base)) ≡ true
  ok-id = refl

  -- the same term against a CODE for that type: needs `El-⌜Π⌝` conversion
  ok-code : isJust (check 10 ◇ (lam (var vz)) (El (⌜Π⌝ ⌜base⌝ ⌜base⌝))) ≡ true
  ok-code = refl

  -- a β-redex in the TYPE: El ((λc.c) ⌜Nat⌝) ≅ Nat
  ok-beta : isJust (check 10 ◇ nzero (El (app (lam (var vz)) ⌜Nat⌝))) ≡ true
  ok-beta = refl

  -- dependent pair ⟨0, refl⟩ ∷ Σ (n : Nat). Id Nat n 0 — the snd's type is
  -- the codomain SUBSTITUTED, and the `El ⌜Nat⌝` from `idrefl` must convert
  ok-sigma : isJust (check 20 ◇ (pair nzero (idrefl ⌜Nat⌝ nzero))
                                 (Σ' Nat (Id Nat (var vz) nzero))) ≡ true
  ok-sigma = refl

  -- application through a variable: f : Π Nat Nat ⊢ f 0 ∷ Nat
  ok-app : isJust (infer 10 (◇ ▹ Π Nat Nat) (app (var vz) nzero)) ≡ true
  ok-app = refl

  -- `Hom Nat 0 n` COMPUTES to `Unit`, so `unit` inhabits it
  ok-homnat : isJust (check 10 (◇ ▹ Nat) unit (Hom Nat nzero (var vz))) ≡ true
  ok-homnat = refl

  -- REJECTIONS
  no-base : isJust (check 10 ◇ nzero base) ≡ false
  no-base = refl

  no-app : isJust (infer 10 ◇ (app nzero nzero)) ≡ false
  no-app = refl

  -- wrong pair component
  no-sigma : isJust (check 20 ◇ (pair nzero (idrefl ⌜Nat⌝ (nsuc nzero)))
                                 (Σ' Nat (Id Nat (var vz) nzero))) ≡ false
  no-sigma = refl
