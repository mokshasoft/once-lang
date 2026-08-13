------------------------------------------------------------------------
-- OCP-0009 — ★ GATE 5c: TUPLED METHODS — DEPENDENT ELIMINATION WITHOUT η.
--
-- Gate 5  : non-dependent (recursor), curried `fields`.  GREEN.
-- Gate 5b : DEPENDENT + curried `fields` ⇒ needs `pair (fst p) unit ≡ p`,
--           i.e. SURJECTIVE PAIRING, plus a substitution-composition
--           tower.  That η is the OPEN G4 decision, about the CONVERSION
--           RELATION and nothing to do with datatypes.
-- Gate 5c : THIS — dependent + TUPLED methods.  The claim is that η
--           disappears entirely.
--
-- ★★★ WHY TUPLED IS THE PRINCIPLED FORM, not merely the cheap one.
--
--   A description denotes a FUNCTOR; the payload IS the functor
--   application; the method is its ALGEBRA, `⟦D⟧ X → X`.  Passing the
--   payload WHOLE matches what the data is.
--
--   Curried methods DESTRUCTURE and REBUILD: the method receives `fst p`
--   and `snd p`, so its result type can only mention `pair (fst p) unit`
--   — which is `p` only up to η.  ⇒ THE η REQUIREMENT IS THE SYMPTOM OF AN
--   INFORMATION LOSS, not an incidental technicality.  Tupled loses
--   nothing, so `M[con k q]` instantiates to `M[con k p]` ON THE NOSE.
--
--   ⚠ And it keeps the AXES INDEPENDENT: curried would make inductive
--     types depend on the η decision, which is about conversion.
--
-- ⚠ WHAT TUPLED DOES **NOT** BUY — corrected after trying it.  It does
--   NOT avoid the substitution-composition tower: instantiating a type
--   that was BUILT by substitution (the motive with its scrutinee
--   replaced by `con k q`) needs `subTy-subTy` the moment the method is
--   applied to `p`.  Curried needs the same tower.
--
--   ⇒ SCORECARD: SAME TOWER, MINUS THE η.  The η is the part that matters
--     — an axiom papering over an information loss, and it would couple
--     this axis to the open G4 conversion decision.
--
--   ★ One thing tupled DOES buy structurally: the method's result
--     `M[con k q]` mentions the PAYLOAD binder and NOT the IH binder, so
--     the inner codomain is a WEAKENING and the second application needs
--     only the non-dependent rule.
--
-- Q23  ★★★ does dependent subject reduction for ι hold with tupled
--      methods and NO η premise?
-- Q24  ★★ how much substitution machinery does it actually cost, versus
--      5b's tower?
--
-- Self-contained: no imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeIotaTup where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B} →
        x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

------------------------------------------------------------------------
-- the miniature kernel
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
-- renaming, substitution, and the FOUR laws this gate needs
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

renTm ρ (var x)      = var (ρ x)
renTm ρ (lam t)      = lam (renTm (extR ρ) t)
renTm ρ (app t u)    = app (renTm ρ t) (renTm ρ u)
renTm ρ unit         = unit
renTm ρ (pair a b)   = pair (renTm ρ a) (renTm ρ b)
renTm ρ (fst p)      = fst (renTm ρ p)
renTm ρ (snd p)      = snd (renTm ρ p)
renTm ρ (con k p)    = con k (renTm ρ p)
renTm ρ (elim D m t) = elim D (renTm ρ m) (renTm ρ t)

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

_[_] : {Γ : Cx} → RTy (Γ ∙) → RTm Γ → RTy Γ
M [ t ] = subTy (single t) M

infix 30 _[_]

-- pointwise congruence, both actions
renTm-cong : {Γ Δ : Cx} {ρ τ : Ren Γ Δ} → (∀ x → ρ x ≡ τ x) →
             (t : RTm Γ) → renTm ρ t ≡ renTm τ t
extR-cong : {Γ Δ : Cx} {ρ τ : Ren Γ Δ} → (∀ x → ρ x ≡ τ x) →
            ∀ x → extR ρ x ≡ extR τ x
extR-cong h vz     = refl
extR-cong h (vs x) = cong vs (h x)

renTm-cong h (var x)      = cong var (h x)
renTm-cong h (lam t)      = cong lam (renTm-cong (extR-cong h) t)
renTm-cong h (app t u)    = cong₂ app (renTm-cong h t) (renTm-cong h u)
renTm-cong h unit         = refl
renTm-cong h (pair a b)   = cong₂ pair (renTm-cong h a) (renTm-cong h b)
renTm-cong h (fst p)      = cong fst (renTm-cong h p)
renTm-cong h (snd p)      = cong snd (renTm-cong h p)
renTm-cong h (con k p)    = cong (con k) (renTm-cong h p)
renTm-cong h (elim D m t) = cong₂ (elim D) (renTm-cong h m) (renTm-cong h t)

renTm-renTm : {Γ Δ Θ : Cx} (ρ : Ren Δ Θ) (τ : Ren Γ Δ) (t : RTm Γ) →
              renTm ρ (renTm τ t) ≡ renTm (λ x → ρ (τ x)) t
renTm-renTm ρ τ (var x)      = refl
renTm-renTm ρ τ (lam t)      =
  cong lam (trans (renTm-renTm (extR ρ) (extR τ) t)
                  (renTm-cong {ρ = λ x → extR ρ (extR τ x)}
                              {τ = extR (λ x → ρ (τ x))}
                              (λ { vz → refl ; (vs x) → refl }) t))
renTm-renTm ρ τ (app t u)    = cong₂ app (renTm-renTm ρ τ t) (renTm-renTm ρ τ u)
renTm-renTm ρ τ unit         = refl
renTm-renTm ρ τ (pair a b)   = cong₂ pair (renTm-renTm ρ τ a) (renTm-renTm ρ τ b)
renTm-renTm ρ τ (fst p)      = cong fst (renTm-renTm ρ τ p)
renTm-renTm ρ τ (snd p)      = cong snd (renTm-renTm ρ τ p)
renTm-renTm ρ τ (con k p)    = cong (con k) (renTm-renTm ρ τ p)
renTm-renTm ρ τ (elim D m t) =
  cong₂ (elim D) (renTm-renTm ρ τ m) (renTm-renTm ρ τ t)

-- weakening is natural on TERMS — the one fact `renTy-sub`'s Π case needs
renTm-nat : {Γ Δ : Cx} (ρ : Ren Γ Δ) (t : RTm Γ) →
            renTm (extR ρ) (renTm vs t) ≡ renTm vs (renTm ρ t)
renTm-nat ρ t = trans (renTm-renTm (extR ρ) vs t) (sym (renTm-renTm vs ρ t))

subTy-cong : {Γ Δ : Cx} {σ τ : Sub Γ Δ} → (∀ x → σ x ≡ τ x) →
             (A : RTy Γ) → subTy σ A ≡ subTy τ A
extS-cong : {Γ Δ : Cx} {σ τ : Sub Γ Δ} → (∀ x → σ x ≡ τ x) →
            ∀ x → extS σ x ≡ extS τ x
extS-cong h vz     = refl
extS-cong h (vs x) = cong (renTm vs) (h x)

subTy-cong h Unit     = refl
subTy-cong h (Π A B)  = cong₂ Π (subTy-cong h A) (subTy-cong (extS-cong h) B)
subTy-cong h (Σ' A B) = cong₂ Σ' (subTy-cong h A) (subTy-cong (extS-cong h) B)
subTy-cong h (Mu D)   = refl

subTy-ren : {Γ Δ Θ : Cx} (σ : Sub Δ Θ) (ρ : Ren Γ Δ) (A : RTy Γ) →
            subTy σ (renTy ρ A) ≡ subTy (λ x → σ (ρ x)) A
subTy-ren σ ρ Unit     = refl
subTy-ren σ ρ (Π A B)  =
  cong₂ Π (subTy-ren σ ρ A)
          (trans (subTy-ren (extS σ) (extR ρ) B)
                 (subTy-cong {σ = λ x → extS σ (extR ρ x)}
                             {τ = extS (λ x → σ (ρ x))}
                             (λ { vz → refl ; (vs x) → refl }) B))
subTy-ren σ ρ (Σ' A B) =
  cong₂ Σ' (subTy-ren σ ρ A)
           (trans (subTy-ren (extS σ) (extR ρ) B)
                  (subTy-cong {σ = λ x → extS σ (extR ρ x)}
                              {τ = extS (λ x → σ (ρ x))}
                              (λ { vz → refl ; (vs x) → refl }) B))
subTy-ren σ ρ (Mu D)   = refl

renTy-sub : {Γ Δ Θ : Cx} (ρ : Ren Δ Θ) (σ : Sub Γ Δ) (A : RTy Γ) →
            renTy ρ (subTy σ A) ≡ subTy (λ x → renTm ρ (σ x)) A
renTy-sub ρ σ Unit     = refl
renTy-sub ρ σ (Π A B)  =
  cong₂ Π (renTy-sub ρ σ A)
          (trans (renTy-sub (extR ρ) (extS σ) B)
                 (subTy-cong {σ = λ x → renTm (extR ρ) (extS σ x)}
                             {τ = extS (λ x → renTm ρ (σ x))}
                             (λ { vz → refl ; (vs x) → renTm-nat ρ (σ x) }) B))
renTy-sub ρ σ (Σ' A B) =
  cong₂ Σ' (renTy-sub ρ σ A)
           (trans (renTy-sub (extR ρ) (extS σ) B)
                  (subTy-cong {σ = λ x → renTm (extR ρ) (extS σ x)}
                              {τ = extS (λ x → renTm ρ (σ x))}
                              (λ { vz → refl ; (vs x) → renTm-nat ρ (σ x) }) B))
renTy-sub ρ σ (Mu D)   = refl

-- ★ L1 — substituting under a WEAKENING drops the substitution.
--   This is what lets the IH binder be skipped: the method's result type
--   does not mention it, so its codomain is a `wk`.
subTy-wk : {Γ Δ : Cx} (σ : Sub Γ Δ) (A : RTy Γ) →
           subTy (extS σ) (wk A) ≡ wk (subTy σ A)
subTy-wk σ A = trans (subTy-ren (extS σ) vs A) (sym (renTy-sub vs σ A))


-- ★ L2 — SUBSTITUTION COMPOSITION.  Needed by BOTH formulations (the 5c
--   header's earlier claim that tupled avoids it was wrong).  It is what
--   lets a type built by substitution be instantiated.
subTm-cong : {Γ Δ : Cx} {σ τ : Sub Γ Δ} → (∀ x → σ x ≡ τ x) →
             (t : RTm Γ) → subTm σ t ≡ subTm τ t
subTm-cong h (var x)      = h x
subTm-cong h (lam t)      = cong lam (subTm-cong (extS-cong h) t)
subTm-cong h (app t u)    = cong₂ app (subTm-cong h t) (subTm-cong h u)
subTm-cong h unit         = refl
subTm-cong h (pair a b)   = cong₂ pair (subTm-cong h a) (subTm-cong h b)
subTm-cong h (fst p)      = cong fst (subTm-cong h p)
subTm-cong h (snd p)      = cong snd (subTm-cong h p)
subTm-cong h (con k p)    = cong (con k) (subTm-cong h p)
subTm-cong h (elim D m t) = cong₂ (elim D) (subTm-cong h m) (subTm-cong h t)

subTm-ren : {Γ Δ Θ : Cx} (σ : Sub Δ Θ) (ρ : Ren Γ Δ) (t : RTm Γ) →
            subTm σ (renTm ρ t) ≡ subTm (λ x → σ (ρ x)) t
subTm-ren σ ρ (var x)      = refl
subTm-ren σ ρ (lam t)      =
  cong lam (trans (subTm-ren (extS σ) (extR ρ) t)
                  (subTm-cong {σ = λ x → extS σ (extR ρ x)}
                              {τ = extS (λ x → σ (ρ x))}
                              (λ { vz → refl ; (vs x) → refl }) t))
subTm-ren σ ρ (app t u)    = cong₂ app (subTm-ren σ ρ t) (subTm-ren σ ρ u)
subTm-ren σ ρ unit         = refl
subTm-ren σ ρ (pair a b)   = cong₂ pair (subTm-ren σ ρ a) (subTm-ren σ ρ b)
subTm-ren σ ρ (fst p)      = cong fst (subTm-ren σ ρ p)
subTm-ren σ ρ (snd p)      = cong snd (subTm-ren σ ρ p)
subTm-ren σ ρ (con k p)    = cong (con k) (subTm-ren σ ρ p)
subTm-ren σ ρ (elim D m t) =
  cong₂ (elim D) (subTm-ren σ ρ m) (subTm-ren σ ρ t)

renTm-sub : {Γ Δ Θ : Cx} (ρ : Ren Δ Θ) (σ : Sub Γ Δ) (t : RTm Γ) →
            renTm ρ (subTm σ t) ≡ subTm (λ x → renTm ρ (σ x)) t
renTm-sub ρ σ (var x)      = refl
renTm-sub ρ σ (lam t)      =
  cong lam (trans (renTm-sub (extR ρ) (extS σ) t)
                  (subTm-cong {σ = λ x → renTm (extR ρ) (extS σ x)}
                              {τ = extS (λ x → renTm ρ (σ x))}
                              (λ { vz → refl ; (vs x) → renTm-nat ρ (σ x) }) t))
renTm-sub ρ σ (app t u)    = cong₂ app (renTm-sub ρ σ t) (renTm-sub ρ σ u)
renTm-sub ρ σ unit         = refl
renTm-sub ρ σ (pair a b)   = cong₂ pair (renTm-sub ρ σ a) (renTm-sub ρ σ b)
renTm-sub ρ σ (fst p)      = cong fst (renTm-sub ρ σ p)
renTm-sub ρ σ (snd p)      = cong snd (renTm-sub ρ σ p)
renTm-sub ρ σ (con k p)    = cong (con k) (renTm-sub ρ σ p)
renTm-sub ρ σ (elim D m t) =
  cong₂ (elim D) (renTm-sub ρ σ m) (renTm-sub ρ σ t)

subTm-subTm : {Γ Δ Θ : Cx} (σ : Sub Δ Θ) (τ : Sub Γ Δ) (t : RTm Γ) →
              subTm σ (subTm τ t) ≡ subTm (λ x → subTm σ (τ x)) t
subTm-subTm σ τ (var x)      = refl
subTm-subTm σ τ (lam t)      =
  cong lam (trans (subTm-subTm (extS σ) (extS τ) t)
                  (subTm-cong {σ = λ x → subTm (extS σ) (extS τ x)}
                              {τ = extS (λ x → subTm σ (τ x))}
                              (λ { vz → refl
                                 ; (vs x) → trans (subTm-ren (extS σ) vs (τ x))
                                                  (sym (renTm-sub vs σ (τ x))) }) t))
subTm-subTm σ τ (app t u)    = cong₂ app (subTm-subTm σ τ t) (subTm-subTm σ τ u)
subTm-subTm σ τ unit         = refl
subTm-subTm σ τ (pair a b)   = cong₂ pair (subTm-subTm σ τ a) (subTm-subTm σ τ b)
subTm-subTm σ τ (fst p)      = cong fst (subTm-subTm σ τ p)
subTm-subTm σ τ (snd p)      = cong snd (subTm-subTm σ τ p)
subTm-subTm σ τ (con k p)    = cong (con k) (subTm-subTm σ τ p)
subTm-subTm σ τ (elim D m t) =
  cong₂ (elim D) (subTm-subTm σ τ m) (subTm-subTm σ τ t)

subTy-subTy : {Γ Δ Θ : Cx} (σ : Sub Δ Θ) (τ : Sub Γ Δ) (A : RTy Γ) →
              subTy σ (subTy τ A) ≡ subTy (λ x → subTm σ (τ x)) A
subTy-subTy σ τ Unit     = refl
subTy-subTy σ τ (Π A B)  =
  cong₂ Π (subTy-subTy σ τ A)
          (trans (subTy-subTy (extS σ) (extS τ) B)
                 (subTy-cong {σ = λ x → subTm (extS σ) (extS τ x)}
                             {τ = extS (λ x → subTm σ (τ x))}
                             (λ { vz → refl
                                ; (vs x) → trans (subTm-ren (extS σ) vs (τ x))
                                                 (sym (renTm-sub vs σ (τ x))) }) B))
subTy-subTy σ τ (Σ' A B) =
  cong₂ Σ' (subTy-subTy σ τ A)
           (trans (subTy-subTy (extS σ) (extS τ) B)
                  (subTy-cong {σ = λ x → subTm (extS σ) (extS τ x)}
                              {τ = extS (λ x → subTm σ (τ x))}
                              (λ { vz → refl
                                 ; (vs x) → trans (subTm-ren (extS σ) vs (τ x))
                                                  (sym (renTm-sub vs σ (τ x))) }) B))
subTy-subTy σ τ (Mu D)   = refl

------------------------------------------------------------------------
-- ★ THE MOTIVE, RE-BASED AT THE PAYLOAD BINDER.
--
--   `atCon k M` is `M` with its SCRUTINEE binder replaced by `con k ⟨-⟩`,
--   so its own binder is now the PAYLOAD.  One substitution, not a
--   weaken-then-substitute pair.
------------------------------------------------------------------------

conS : {Γ : Cx} → ℕ → Sub (Γ ∙) (Γ ∙)
conS k vz     = con k (var vz)
conS k (vs x) = var (vs x)

atCon : {Γ : Cx} → ℕ → RTy (Γ ∙) → RTy (Γ ∙)
atCon k M = subTy (conS k) M

-- ★★★ L3 — instantiating the re-based motive at a payload IS the motive
--     at that constructor.  NO η ANYWHERE.
atCon-inst : {Γ : Cx} (k : ℕ) (M : RTy (Γ ∙)) (p : RTm Γ) →
             atCon k M [ p ] ≡ M [ con k p ]
atCon-inst k M p =
  trans (subTy-subTy (single p) (conS k) M)
        (subTy-cong {σ = λ x → subTm (single p) (conS k x)}
                    {τ = single (con k p)}
                    (λ { vz → refl ; (vs x) → refl }) M)

-- identity substitution, and substituting under a weakening
subTm-id : {Γ : Cx} (t : RTm Γ) → subTm var t ≡ t
subTm-id (var x)      = refl
subTm-id (lam t)      =
  cong lam (trans (subTm-cong {σ = extS var} {τ = var}
                              (λ { vz → refl ; (vs x) → refl }) t)
                  (subTm-id t))
subTm-id (app t u)    = cong₂ app (subTm-id t) (subTm-id u)
subTm-id unit         = refl
subTm-id (pair a b)   = cong₂ pair (subTm-id a) (subTm-id b)
subTm-id (fst p)      = cong fst (subTm-id p)
subTm-id (snd p)      = cong snd (subTm-id p)
subTm-id (con k p)    = cong (con k) (subTm-id p)
subTm-id (elim D m t) = cong₂ (elim D) (subTm-id m) (subTm-id t)

subTy-id : {Γ : Cx} (A : RTy Γ) → subTy var A ≡ A
subTy-id Unit     = refl
subTy-id (Π A B)  =
  cong₂ Π (subTy-id A)
          (trans (subTy-cong {σ = extS var} {τ = var}
                             (λ { vz → refl ; (vs x) → refl }) B)
                 (subTy-id B))
subTy-id (Σ' A B) =
  cong₂ Σ' (subTy-id A)
           (trans (subTy-cong {σ = extS var} {τ = var}
                              (λ { vz → refl ; (vs x) → refl }) B)
                  (subTy-id B))
subTy-id (Mu D)   = refl

-- ★ L4 — a weakened type ignores the substitution.  This is what lets the
--   IH argument be consumed without touching the result type.
sub-single-wk : {Γ : Cx} (u : RTm Γ) (X : RTy Γ) → wk X [ u ] ≡ X
sub-single-wk u X =
  trans (subTy-ren (single u) vs X)
        (trans (subTy-cong {σ = λ x → single u (vs x)} {τ = var}
                           (λ x → refl) X)
               (subTy-id X))

------------------------------------------------------------------------
-- ★★ THE TUPLED FORMULATION, GENERAL IN `DCon`.
--
--   payTy  D C      Σ-chain over the field list
--   ihTy   D C q M  Σ-chain of `M[πᵢ q]` over the `dρ` fields ONLY
--   methTy D k C M  Π (payTy) (Π (ihTy) (wk (atCon k M)))
--
--   ⚠ the result mentions the PAYLOAD binder only, never the IH binder,
--     so it is a `wk` over the latter — that is what keeps the second
--     application non-dependent.
------------------------------------------------------------------------

-- the unique renaming out of the empty context: a `dκ`'s CLOSED field
-- type used at an arbitrary Γ
εren : {Γ : Cx} → Ren ε Γ
εren ()

εwkTy : {Γ : Cx} → RTy ε → RTy Γ
εwkTy = renTy εren

renTy-cong : {Γ Δ : Cx} {ρ τ : Ren Γ Δ} → (∀ x → ρ x ≡ τ x) →
             (A : RTy Γ) → renTy ρ A ≡ renTy τ A
renTy-cong h Unit     = refl
renTy-cong h (Π A B)  = cong₂ Π (renTy-cong h A) (renTy-cong (extR-cong h) B)
renTy-cong h (Σ' A B) = cong₂ Σ' (renTy-cong h A) (renTy-cong (extR-cong h) B)
renTy-cong h (Mu D)   = refl

renTy-renTy : {Γ Δ Θ : Cx} (ρ : Ren Δ Θ) (τ : Ren Γ Δ) (A : RTy Γ) →
              renTy ρ (renTy τ A) ≡ renTy (λ x → ρ (τ x)) A
renTy-renTy ρ τ Unit     = refl
renTy-renTy ρ τ (Π A B)  =
  cong₂ Π (renTy-renTy ρ τ A)
          (trans (renTy-renTy (extR ρ) (extR τ) B)
                 (renTy-cong {ρ = λ x → extR ρ (extR τ x)}
                             {τ = extR (λ x → ρ (τ x))}
                             (λ { vz → refl ; (vs x) → refl }) B))
renTy-renTy ρ τ (Σ' A B) =
  cong₂ Σ' (renTy-renTy ρ τ A)
           (trans (renTy-renTy (extR ρ) (extR τ) B)
                  (renTy-cong {ρ = λ x → extR ρ (extR τ x)}
                              {τ = extR (λ x → ρ (τ x))}
                              (λ { vz → refl ; (vs x) → refl }) B))
renTy-renTy ρ τ (Mu D)   = refl

εwk-ren : {Γ Δ : Cx} (ρ : Ren Γ Δ) (A : RTy ε) →
          renTy ρ (εwkTy A) ≡ εwkTy A
εwk-ren ρ A =
  trans (renTy-renTy ρ εren A)
        (renTy-cong {ρ = λ x → ρ (εren x)} {τ = εren} (λ ()) A)

εwk-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) (A : RTy ε) →
          subTy σ (εwkTy A) ≡ εwkTy A
εwk-sub σ A =
  trans (subTy-ren σ εren A)
        (trans (subTy-cong {σ = λ x → σ (εren x)} {τ = λ x → var (εren x)}
                           (λ ()) A)
               (sym (renTy-is-sub εren A)))
  where
    renTy-is-sub : {Γ Δ : Cx} (ρ : Ren Γ Δ) (A : RTy Γ) →
                   renTy ρ A ≡ subTy (λ x → var (ρ x)) A
    renTy-is-sub ρ Unit     = refl
    renTy-is-sub ρ (Π A B)  =
      cong₂ Π (renTy-is-sub ρ A)
              (trans (renTy-is-sub (extR ρ) B)
                     (subTy-cong {σ = λ x → var (extR ρ x)}
                                 {τ = extS (λ x → var (ρ x))}
                                 (λ { vz → refl ; (vs x) → refl }) B))
    renTy-is-sub ρ (Σ' A B) =
      cong₂ Σ' (renTy-is-sub ρ A)
               (trans (renTy-is-sub (extR ρ) B)
                      (subTy-cong {σ = λ x → var (extR ρ x)}
                                  {τ = extS (λ x → var (ρ x))}
                                  (λ { vz → refl ; (vs x) → refl }) B))
    renTy-is-sub ρ (Mu D)   = refl

------------------------------------------------------------------------

payTy : {Γ : Cx} → Desc → DCon → RTy Γ
payTy D dι       = Unit
payTy D (dρ C)   = Σ' (Mu D)    (payTy D C)
payTy D (dκ A C) = Σ' (εwkTy A) (payTy D C)

-- payloads are CLOSED, so both actions are inert on them
payTy-ren : {Γ Δ : Cx} (ρ : Ren Γ Δ) (D : Desc) (C : DCon) →
            renTy ρ (payTy D C) ≡ payTy D C
payTy-ren ρ D dι       = refl
payTy-ren ρ D (dρ C)   = cong (Σ' (Mu D)) (payTy-ren (extR ρ) D C)
payTy-ren ρ D (dκ A C) =
  cong₂ Σ' (εwk-ren ρ A) (payTy-ren (extR ρ) D C)

payTy-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) (D : Desc) (C : DCon) →
            subTy σ (payTy D C) ≡ payTy D C
payTy-sub σ D dι       = refl
payTy-sub σ D (dρ C)   = cong (Σ' (Mu D)) (payTy-sub (extS σ) D C)
payTy-sub σ D (dκ A C) =
  cong₂ Σ' (εwk-sub σ A) (payTy-sub (extS σ) D C)

------------------------------------------------------------------------

ihTy : {Γ : Cx} → Desc → DCon → RTm Γ → RTy (Γ ∙) → RTy Γ
ihTy D dι       q M = Unit
ihTy D (dρ C)   q M = Σ' (M [ fst q ]) (wk (ihTy D C (snd q) M))
ihTy D (dκ A C) q M = ihTy D C (snd q) M

-- ★ the IH tuple's substitution law.  `M` travels under `extS`, `q` under
--   the substitution itself.
ihTy-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) (D : Desc) (C : DCon)
           (q : RTm Γ) (M : RTy (Γ ∙)) →
           subTy σ (ihTy D C q M)
             ≡ ihTy D C (subTm σ q) (subTy (extS σ) M)
ihTy-sub σ D dι       q M = refl
ihTy-sub σ D (dρ C)   q M =
  cong₂ Σ' (trans (subTy-subTy σ (single (fst q)) M)
                  (trans (subTy-cong
                            {σ = λ x → subTm σ (single (fst q) x)}
                            {τ = λ x → subTm (single (fst (subTm σ q)))
                                              (extS σ x)}
                            (λ { vz → refl
                               ; (vs x) → sym (trans (subTm-ren (single (fst (subTm σ q))) vs (σ x))
                                                     (subTm-id (σ x))) }) M)
                         (sym (subTy-subTy (single (fst (subTm σ q))) (extS σ) M))))
           (trans (subTy-wk σ (ihTy D C (snd q) M))
                  (cong wk (ihTy-sub σ D C (snd q) M)))
ihTy-sub σ D (dκ A C) q M = ihTy-sub σ D C (snd q) M

------------------------------------------------------------------------

methTy : {Γ : Cx} → Desc → ℕ → DCon → RTy (Γ ∙) → RTy Γ
methTy D k C M =
  Π (payTy D C)
    (Π (ihTy D C (var vz) (renTy (extR vs) M))
       (wk (atCon k M)))

ihs : {Γ : Cx} → Desc → RTm Γ → DCon → RTm Γ → RTm Γ
ihs D ms dι       p = unit
ihs D ms (dρ C)   p = pair (elim D ms (fst p)) (ihs D ms C (snd p))
ihs D ms (dκ A C) p = ihs D ms C (snd p)

fieldsT : {Γ : Cx} → Desc → RTm Γ → DCon → RTm Γ → RTm Γ → RTm Γ
fieldsT D ms C m p = app (app m p) (ihs D ms C p)

-- ★ L5 — weaken past a binder, then substitute it: the identity.
wk-single-id : {Γ : Cx} (p : RTm Γ) (M : RTy (Γ ∙)) →
               subTy (extS (single p)) (renTy (extR vs) M) ≡ M
wk-single-id p M =
  trans (subTy-ren (extS (single p)) (extR vs) M)
        (trans (subTy-cong {σ = λ x → extS (single p) (extR vs x)} {τ = var}
                           (λ { vz → refl ; (vs x) → refl }) M)
               (subTy-id M))

------------------------------------------------------------------------
-- typing — DEPENDENT Π/Σ
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
  ⊢snd  : {Γ : Cx} {Θ : Ctx Γ} {A : RTy Γ} {B : RTy (Γ ∙)} {p : RTm Γ} →
          Θ ⊢ p ∷ Σ' A B → Θ ⊢ snd p ∷ B [ fst p ]
  ⊢elim : {Γ : Cx} {Θ : Ctx Γ} {D : Desc} {M : RTy (Γ ∙)} {ms t : RTm Γ} →
          Θ ⊢ t ∷ Mu D → Θ ⊢ elim D ms t ∷ M [ t ]
  ⊢conv : {Γ : Cx} {Θ : Ctx Γ} {A B : RTy Γ} {t : RTm Γ} →
          Θ ⊢ t ∷ A → A ≡ B → Θ ⊢ t ∷ B

------------------------------------------------------------------------
-- ★ the IH tuple really inhabits its type, at EVERY field list.
--   ⚠ `dρ` contributes an IH, `dκ` does not — a non-recursive field owes
--     no induction hypothesis, the same accounting `SpikeDescSigma`'s
--     `elimLift` made in the model.
------------------------------------------------------------------------

ihs-ty : {Γ : Cx} {Θ : Ctx Γ} (D : Desc) (ms : RTm Γ) (C : DCon)
         (p : RTm Γ) (M : RTy (Γ ∙)) →
         Θ ⊢ p ∷ payTy D C → Θ ⊢ ihs D ms C p ∷ ihTy D C p M
ihs-ty D ms dι p M hp = ⊢unit
ihs-ty {Θ = Θ} D ms (dρ C) p M hp =
  ⊢pair (⊢elim (⊢fst hp))
        (subst (λ z → Θ ⊢ ihs D ms C (snd p) ∷ z)
               (sym (sub-single-wk (elim D ms (fst p)) (ihTy D C (snd p) M)))
               (ihs-ty D ms C (snd p) M htail))
  where
    htail : Θ ⊢ snd p ∷ payTy D C
    htail = ⊢conv (⊢snd hp) (payTy-sub (single (fst p)) D C)
ihs-ty {Θ = Θ} D ms (dκ A C) p M hp = ihs-ty D ms C (snd p) M htail
  where
    htail : Θ ⊢ snd p ∷ payTy D C
    htail = ⊢conv (⊢snd hp) (payTy-sub (single (fst p)) D C)

------------------------------------------------------------------------
-- ★★★ THE GATE, GENERAL IN `DCon`.  Dependent subject reduction for ι,
--     tupled methods, and STILL NO η PREMISE.
------------------------------------------------------------------------

sr-ι-tup :
  {Γ : Cx} {Θ : Ctx Γ} (D : Desc) (k : ℕ) (C : DCon) (M : RTy (Γ ∙))
  (ms m p : RTm Γ) →
  Θ ⊢ m ∷ methTy D k C M →
  Θ ⊢ p ∷ payTy D C →
  Θ ⊢ fieldsT D ms C m p ∷ M [ con k p ]
sr-ι-tup {Γ} {Θ} D k C M ms m p hm hp =
  ⊢conv (⊢app step1 (ihs-ty D ms C p M hp))
        (trans (sub-single-wk (ihs D ms C p) (atCon k M [ p ]))
               (atCon-inst k M p))
  where
    ihTy-eq : subTy (single p) (ihTy D C (var vz) (renTy (extR vs) M))
                ≡ ihTy D C p M
    ihTy-eq =
      trans (ihTy-sub (single p) D C (var vz) (renTy (extR vs) M))
            (cong (ihTy D C p) (wk-single-id p M))

    step1 : Θ ⊢ app m p ∷ Π (ihTy D C p M) (wk (atCon k M [ p ]))
    step1 = ⊢conv (⊢app hm hp)
                  (cong₂ Π ihTy-eq (subTy-wk (single p) (atCon k M)))
