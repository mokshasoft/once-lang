------------------------------------------------------------------------
-- OCP-0009 — ★ GATE 5b: DOES THE CURRENT `fields` SURVIVE A DEPENDENT
--                       MOTIVE?
--
-- Gate 5 proved subject reduction for ι with a NON-DEPENDENT motive
-- (`B : RTy Γ`) — a RECURSOR.  Every theorem proved BY INDUCTION over a
-- user datatype needs the dependent form (`M : RTy (Γ ∙)`), so this gate
-- asks whether that form is reachable WITHOUT changing the ι-rule.
--
-- ⚠⚠ WHY IT IS A DECISION POINT AND NOT A TASK.  `fields` applies methods
--   CURRIED — one field at a time:
--
--     fields D ms (dρ C) m p =
--       fields D ms C (app (app m (fst p)) (elim D ms (fst p))) (snd p)
--
--   The alternative is TUPLED methods (`app (app m p) (ihs …)`), which is
--   easier to type dependently — but changing `fields` changes the ι-rule,
--   hence `Conf` and `LR`, the two modules that were 40–60% of the axis
--   cost and are ALREADY DONE.  So the answer decides whether ~2000 lines
--   of finished work re-opens.
--
-- ★★★ THE QUESTION, REDUCED TO ITS SMALLEST INSTANCE.  Take the
--   one-recursive-field constructor (`suc`-shaped), `C = dρ dι`:
--
--     fields D ms (dρ dι) m p  =  app (app m (fst p)) (elim D ms (fst p))
--
--   Dependently, the method must be
--
--     m : Π (x : Mu D). Π (ih : M[x]). M[con k (pair x unit)]
--            ^^^^^^^^^^ the payload REBUILT FROM THE METHOD'S OWN BINDERS
--
--   because the method never receives `p` — only its projections.  So the
--   reduct has type   M[con k (pair (fst p) unit)].
--
--   But `⊢elim` says   elim D ms (con k p) : M[con k p].
--
--   ⇒ SUBJECT REDUCTION NEEDS   pair (fst p) unit ≡ p.
--
--   That is SURJECTIVE PAIRING (η for Σ), plus η for Unit.  It is not a
--   lemma about descriptions at all — it is a question about the KERNEL's
--   conversion relation, and `two-former-kernel-direction` records the η
--   decision (G4) as still OPEN.
--
-- Q22  ★★★ is `pair (fst p) unit ≡ p` really what the dependent case
--      needs, and is it really the ONLY thing it needs?
--
-- This module answers Q22 by taking the η as an explicit PREMISE and
-- showing the dependent case goes through with it and (by construction)
-- cannot be stated without it.
--
-- Self-contained: no imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeIotaDep where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

------------------------------------------------------------------------
-- the miniature kernel, as in gate 5 (Cx/Var/RTy/RTm), plus SINGLE
-- SUBSTITUTION — which the dependent motive needs and the recursor did not
------------------------------------------------------------------------

data Cx : Set where
  ε  : Cx
  _∙ : Cx → Cx

infixl 5 _∙

data Var : Cx → Set where
  vz : {Γ : Cx} → Var (Γ ∙)
  vs : {Γ : Cx} → Var Γ → Var (Γ ∙)

data Desc : Set
data DCon : Set
data RTy : Cx → Set
data RTm : Cx → Set

data RTy where
  Unit : {Γ : Cx} → RTy Γ
  Π    : {Γ : Cx} → RTy Γ → RTy (Γ ∙) → RTy Γ
  Σ'   : {Γ : Cx} → RTy Γ → RTy (Γ ∙) → RTy Γ
  Mu   : {Γ : Cx} → Desc → RTy Γ

data RTm where
  var  : {Γ : Cx} → Var Γ → RTm Γ
  lam  : {Γ : Cx} → RTm (Γ ∙) → RTm Γ
  app  : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
  unit : {Γ : Cx} → RTm Γ
  pair : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
  fst  : {Γ : Cx} → RTm Γ → RTm Γ
  snd  : {Γ : Cx} → RTm Γ → RTm Γ
  con  : {Γ : Cx} → ℕ → RTm Γ → RTm Γ
  elim : {Γ : Cx} → Desc → RTm Γ → RTm Γ → RTm Γ

data DCon where
  dι : DCon
  dρ : DCon → DCon
  dκ : RTy ε → DCon → DCon

data Desc where
  dnil : Desc
  _◃_  : DCon → Desc → Desc

infixr 5 _◃_

------------------------------------------------------------------------
-- renaming and single substitution
------------------------------------------------------------------------

Ren : Cx → Cx → Set
Ren Γ Δ = Var Γ → Var Δ

extR : {Γ Δ : Cx} → Ren Γ Δ → Ren (Γ ∙) (Δ ∙)
extR ρ vz     = vz
extR ρ (vs x) = vs (ρ x)

renTy : {Γ Δ : Cx} → Ren Γ Δ → RTy Γ → RTy Δ
renTm : {Γ Δ : Cx} → Ren Γ Δ → RTm Γ → RTm Δ

renTy ρ Unit     = Unit
renTy ρ (Π A B)  = Π (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (Σ' A B) = Σ' (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (Mu D)   = Mu D

renTm ρ (var x)       = var (ρ x)
renTm ρ (lam t)       = lam (renTm (extR ρ) t)
renTm ρ (app t u)     = app (renTm ρ t) (renTm ρ u)
renTm ρ unit          = unit
renTm ρ (pair a b)    = pair (renTm ρ a) (renTm ρ b)
renTm ρ (fst p)       = fst (renTm ρ p)
renTm ρ (snd p)       = snd (renTm ρ p)
renTm ρ (con k p)     = con k (renTm ρ p)
renTm ρ (elim D m t)  = elim D (renTm ρ m) (renTm ρ t)

wk : {Γ : Cx} → RTy Γ → RTy (Γ ∙)
wk = renTy vs

Sub : Cx → Cx → Set
Sub Γ Δ = Var Γ → RTm Δ

extS : {Γ Δ : Cx} → Sub Γ Δ → Sub (Γ ∙) (Δ ∙)
extS σ vz     = var vz
extS σ (vs x) = renTm vs (σ x)

subTy : {Γ Δ : Cx} → Sub Γ Δ → RTy Γ → RTy Δ
subTm : {Γ Δ : Cx} → Sub Γ Δ → RTm Γ → RTm Δ

subTy σ Unit     = Unit
subTy σ (Π A B)  = Π (subTy σ A) (subTy (extS σ) B)
subTy σ (Σ' A B) = Σ' (subTy σ A) (subTy (extS σ) B)
subTy σ (Mu D)   = Mu D

subTm σ (var x)      = σ x
subTm σ (lam t)      = lam (subTm (extS σ) t)
subTm σ (app t u)    = app (subTm σ t) (subTm σ u)
subTm σ unit         = unit
subTm σ (pair a b)   = pair (subTm σ a) (subTm σ b)
subTm σ (fst p)      = fst (subTm σ p)
subTm σ (snd p)      = snd (subTm σ p)
subTm σ (con k p)    = con k (subTm σ p)
subTm σ (elim D m t) = elim D (subTm σ m) (subTm σ t)

single : {Γ : Cx} → RTm Γ → Sub (Γ ∙) Γ
single u vz     = u
single u (vs x) = var x

-- `M[t]` — the motive instantiated at a scrutinee
_[_] : {Γ : Cx} → RTy (Γ ∙) → RTm Γ → RTy Γ
M [ t ] = subTy (single t) M

infix 30 _[_]

------------------------------------------------------------------------
-- ★ THE DEPENDENT METHOD TYPE, at the one-recursive-field constructor.
--
--   m : Π (x : Mu D). Π (ih : M[x]). M[con k (pair x unit)]
--
-- ⚠ the result mentions `pair x unit`, NOT `p` — the method is applied to
--   `fst p` and never sees `p`, so the payload can only be REBUILT from
--   the method's own binders.  That is the whole difficulty, and it is
--   forced by `fields` being CURRIED.
------------------------------------------------------------------------

methTyρ : {Γ : Cx} → Desc → ℕ → RTy (Γ ∙) → RTy Γ
methTyρ {Γ} D k M =
  Π (Mu D)                                   -- x
    (Π (renTy (extR vs) M [ var vz ])        -- ih : M[x]
       (renTy (extR (λ x → vs (vs x))) M
          [ con k (pair (var (vs vz)) unit) ]))

payTyρ : {Γ : Cx} → Desc → RTy Γ
payTyρ D = Σ' (Mu D) Unit

------------------------------------------------------------------------
-- typing.  Π/Σ rules are DEPENDENT here — that is the point of 5b.
------------------------------------------------------------------------

data Ctx : Cx → Set where
  ◇   : Ctx ε
  _▹_ : {Γ : Cx} → Ctx Γ → RTy Γ → Ctx (Γ ∙)

data _⊢_∷_ : {Γ : Cx} → Ctx Γ → RTm Γ → RTy Γ → Set where
  ⊢unit : {Γ : Cx} {Θ : Ctx Γ} → Θ ⊢ unit ∷ Unit
  ⊢app  : {Γ : Cx} {Θ : Ctx Γ} {A : RTy Γ} {B : RTy (Γ ∙)} {t u : RTm Γ} →
          Θ ⊢ t ∷ Π A B → Θ ⊢ u ∷ A → Θ ⊢ app t u ∷ B [ u ]
  ⊢pair : {Γ : Cx} {Θ : Ctx Γ} {A : RTy Γ} {B : RTy (Γ ∙)} {a b : RTm Γ} →
          Θ ⊢ a ∷ A → Θ ⊢ b ∷ B [ a ] → Θ ⊢ pair a b ∷ Σ' A B
  ⊢fst  : {Γ : Cx} {Θ : Ctx Γ} {A : RTy Γ} {B : RTy (Γ ∙)} {p : RTm Γ} →
          Θ ⊢ p ∷ Σ' A B → Θ ⊢ fst p ∷ A
  ⊢con  : {Γ : Cx} {Θ : Ctx Γ} {D : Desc} {k : ℕ} {p : RTm Γ} →
          Θ ⊢ p ∷ payTyρ D → Θ ⊢ con k p ∷ Mu D
  -- the DEPENDENT eliminator
  ⊢elim : {Γ : Cx} {Θ : Ctx Γ} {D : Desc} {M : RTy (Γ ∙)} {ms t : RTm Γ} →
          Θ ⊢ t ∷ Mu D → Θ ⊢ elim D ms t ∷ M [ t ]
  ⊢conv : {Γ : Cx} {Θ : Ctx Γ} {A B : RTy Γ} {t : RTm Γ} →
          Θ ⊢ t ∷ A → A ≡ B → Θ ⊢ t ∷ B

------------------------------------------------------------------------
-- ★★★ Q22 — THE ANSWER.
--
-- With the η premise the dependent case goes through; the proof below
-- uses it EXACTLY ONCE, and at exactly the place the header predicts.
------------------------------------------------------------------------

-- surjective pairing at a `dρ dι` payload, plus η for `Unit`
Ση : Set
Ση = {Γ : Cx} (p : RTm Γ) → pair (fst p) unit ≡ p

-- `fields` at the one-recursive-field constructor, verbatim from the kernel
fieldsρ : {Γ : Cx} → Desc → RTm Γ → RTm Γ → RTm Γ → RTm Γ
fieldsρ D ms m p = app (app m (fst p)) (elim D ms (fst p))

sr-ι-dep :
  Ση →
  {Γ : Cx} {Θ : Ctx Γ} (D : Desc) (k : ℕ) (M : RTy (Γ ∙))
  (ms m p : RTm Γ) →
  Θ ⊢ m ∷ methTyρ D k M →
  Θ ⊢ p ∷ payTyρ D →
  Θ ⊢ fieldsρ D ms m p ∷ M [ con k p ]
sr-ι-dep η D k M ms m p hm hp =
  ⊢conv (⊢app (⊢app hm (⊢fst hp)) (⊢elim (⊢fst hp)))
        (cong (λ q → M [ con k q ]) (η p))
        -- ⚠⚠ THE η IS USED HERE AND ONLY HERE.  Without it the reduct
        --    sits at `M [ con k (pair (fst p) unit) ]` and the goal is
        --    `M [ con k p ]`, and nothing else in the development can
        --    bridge them.
