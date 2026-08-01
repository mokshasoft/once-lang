------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 20 — THE EXPERIMENT: dependent Π/Σ over a de Bruijn
--                            base, with substitution STRICTLY stable
--
-- The load-bearing test of the design decision (HANDOFF §1). The directed
-- functor-category CwF was RULED OUT as the kernel because its Π is only
-- LAX-stable — `(Π A B)[σ] ≢ Π (A[σ]) (B[σ↑])`, the failure of Beck–Chevalley
-- (`NbEPDirPiSub`, dHoTT-12e). The design's bet is that a STRICT SYNTACTIC
-- presentation fixes this by construction. This module runs the experiment.
--
-- A genuinely DEPENDENT raw syntax (well-scoped de Bruijn, base an arbitrary
-- context depth `Cx`): types `RTy` and terms `RTm` are MUTUAL, and `El`
-- injects a term into a type — so a type can mention a term VARIABLE
-- (`Π base (El (var vz))` is `(x : base) → El x`, a real dependency).
-- Substitution acts on both, defined structurally.
--
--   * `Π-stable`/`Σ-stable`/`El-stable` — substitution-stability is
--     DEFINITIONAL (`refl`): `(Π A B)[σ] ≡ Π (A[σ]) (B[σ↑])`. The lax
--     comparison map of the semantic CwF is here an EQUALITY, for free — the
--     syntactic presentation structurally has no Beck–Chevalley obstruction.
--   * `[id]ᵀ`/`[∘]ᵀ` — and it is a COHERENT strict substitution calculus:
--     type substitution satisfies the identity and COMPOSITION laws (the four
--     mutual fusion lemmas, funext-free via pointwise `*-cong`, exactly the
--     `NbEPDirDB` technique doubled for types+terms). `[∘]ᵀ` is the one that
--     matters for Beck–Chevalley: Π commutes STRICTLY with COMPOSED
--     substitutions, `subTy τ (subTy σ (Π A B)) ≡ subTy (τ ∘ₛ σ) (Π A B)` with
--     the Π structure preserved on the nose.
--
-- VERDICT: the experiment PASSES — dependent Π/Σ substitution-stability, the
-- exact thing that was only lax semantically, is definitional syntactically,
-- and sits inside a proven strict substitution calculus. Honest ceiling: this
-- is RAW syntax (scoping enforced, typing not) — enough to settle the
-- stability question; intrinsic typing + conversion is the next slice.
-- `--safe`, ZERO axioms (funext-free).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBPi where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂ )

------------------------------------------------------------------------
-- Scopes (de Bruijn depth) and variables. Untyped scoping — genuine
-- dependency without the transport hell of intrinsic dependent typing.
------------------------------------------------------------------------

data Cx : Set where
  ε  : Cx
  _∙ : Cx → Cx

data Var : Cx → Set where
  vz : ∀ {Γ} → Var (Γ ∙)
  vs : ∀ {Γ} → Var Γ → Var (Γ ∙)

------------------------------------------------------------------------
-- The MUTUAL dependent raw syntax: types and terms, with `El` bringing a
-- term into a type. `Π A B` / `Σ' A B` bind one variable in `B`.
------------------------------------------------------------------------

data RTy : Cx → Set
data RTm : Cx → Set

data RTy where
  base : ∀ {Γ} → RTy Γ
  U    : ∀ {Γ} → RTy Γ                    -- a universe (codes decode via `El`)
  Π    : ∀ {Γ} → RTy Γ → RTy (Γ ∙) → RTy Γ
  Σ'   : ∀ {Γ} → RTy Γ → RTy (Γ ∙) → RTy Γ
  El   : ∀ {Γ} → RTm Γ → RTy Γ
  -- ★ W2 (option a): the DIRECTED IDENTITY TYPE, a primitive former that
  -- COMPUTES like `El` (SpikeHomTy): it unfolds at `U` (directed univalence as
  -- a computation rule) and at `Π` (the pointwise family, item 2); it is STUCK
  -- at `base` (discrete by generation, item 4), at a neutral `El`, at `Σ'`
  -- (the unfolding needs transport in the second component — a TERM former
  -- W2's eliminator introduces; deferred, not dropped), and at `Hom` (higher
  -- paths, unscoped).
  Hom  : ∀ {Γ} → RTy Γ → RTm Γ → RTm Γ → RTy Γ

data RTm where
  var  : ∀ {Γ} → Var Γ → RTm Γ
  lam  : ∀ {Γ} → RTm (Γ ∙) → RTm Γ
  app  : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ
  pair : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ    -- Σ introduction
  fst  : ∀ {Γ} → RTm Γ → RTm Γ            -- Σ elimination
  snd  : ∀ {Γ} → RTm Γ → RTm Γ
  ⌜base⌝ : ∀ {Γ} → RTm Γ                  -- code for `base`
  ⌜Π⌝    : ∀ {Γ} → RTm Γ → RTm (Γ ∙) → RTm Γ  -- code for `Π` (dependent codomain)
  ⌜Σ⌝    : ∀ {Γ} → RTm Γ → RTm (Γ ∙) → RTm Γ  -- code for `Σ`

private
  variable
    Γ Δ Θ : Cx

------------------------------------------------------------------------
-- Renamings (variable-for-variable) and their action on types + terms.
------------------------------------------------------------------------

Ren : Cx → Cx → Set
Ren Γ Δ = Var Γ → Var Δ

extR : Ren Γ Δ → Ren (Γ ∙) (Δ ∙)
extR ρ vz     = vz
extR ρ (vs x) = vs (ρ x)

renTy : Ren Γ Δ → RTy Γ → RTy Δ
renTm : Ren Γ Δ → RTm Γ → RTm Δ
renTy ρ base     = base
renTy ρ U        = U
renTy ρ (Π A B)  = Π (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (Σ' A B) = Σ' (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (El t)   = El (renTm ρ t)
renTy ρ (Hom A t u) = Hom (renTy ρ A) (renTm ρ t) (renTm ρ u)
renTm ρ (var x)   = var (ρ x)
renTm ρ (lam t)   = lam (renTm (extR ρ) t)
renTm ρ (app t u)  = app (renTm ρ t) (renTm ρ u)
renTm ρ (pair a b) = pair (renTm ρ a) (renTm ρ b)
renTm ρ (fst p)    = fst (renTm ρ p)
renTm ρ (snd p)    = snd (renTm ρ p)
renTm ρ ⌜base⌝     = ⌜base⌝
renTm ρ (⌜Π⌝ c d)  = ⌜Π⌝ (renTm ρ c) (renTm (extR ρ) d)
renTm ρ (⌜Σ⌝ c d)  = ⌜Σ⌝ (renTm ρ c) (renTm (extR ρ) d)

------------------------------------------------------------------------
-- Parallel substitutions (variable-for-term) and their action.
------------------------------------------------------------------------

Sub : Cx → Cx → Set
Sub Γ Δ = Var Γ → RTm Δ

extS : Sub Γ Δ → Sub (Γ ∙) (Δ ∙)
extS σ vz     = var vz
extS σ (vs x) = renTm vs (σ x)

subTy : Sub Γ Δ → RTy Γ → RTy Δ
subTm : Sub Γ Δ → RTm Γ → RTm Δ
subTy σ base     = base
subTy σ U        = U
subTy σ (Π A B)  = Π (subTy σ A) (subTy (extS σ) B)
subTy σ (Σ' A B) = Σ' (subTy σ A) (subTy (extS σ) B)
subTy σ (El t)   = El (subTm σ t)
subTy σ (Hom A t u) = Hom (subTy σ A) (subTm σ t) (subTm σ u)
subTm σ (var x)   = σ x
subTm σ (lam t)   = lam (subTm (extS σ) t)
subTm σ (app t u)  = app (subTm σ t) (subTm σ u)
subTm σ (pair a b) = pair (subTm σ a) (subTm σ b)
subTm σ (fst p)    = fst (subTm σ p)
subTm σ (snd p)    = snd (subTm σ p)
subTm σ ⌜base⌝     = ⌜base⌝
subTm σ (⌜Π⌝ c d)  = ⌜Π⌝ (subTm σ c) (subTm (extS σ) d)
subTm σ (⌜Σ⌝ c d)  = ⌜Σ⌝ (subTm σ c) (subTm (extS σ) d)

-- Identity and the four composition operators (explicit-index, genuine
-- Ren/Sub — same shape as NbEPDirDB).
idₛ : Sub Γ Γ
idₛ = var

infixr 8 _∘ᵣ_ _ₛ∘ᵣ_ _ᵣ∘ₛ_ _∘ₛ_
_∘ᵣ_ : Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
(ρ' ∘ᵣ ρ) x = ρ' (ρ x)

_ₛ∘ᵣ_ : Sub Δ Θ → Ren Γ Δ → Sub Γ Θ
(σ ₛ∘ᵣ ρ) x = σ (ρ x)

_ᵣ∘ₛ_ : Ren Δ Θ → Sub Γ Δ → Sub Γ Θ
(ρ ᵣ∘ₛ σ) x = renTm ρ (σ x)

_∘ₛ_ : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
(τ ∘ₛ σ) x = subTm τ (σ x)

------------------------------------------------------------------------
-- ★ THE HEADLINE: substitution-stability of the dependent formers is
--   DEFINITIONAL. This is the lax comparison map of the semantic CwF,
--   here an EQUALITY for free — no Beck–Chevalley obstruction.
------------------------------------------------------------------------

Π-stable : (σ : Sub Γ Δ) (A : RTy Γ) (B : RTy (Γ ∙)) →
           subTy σ (Π A B) ≡ Π (subTy σ A) (subTy (extS σ) B)
Π-stable σ A B = refl

Σ-stable : (σ : Sub Γ Δ) (A : RTy Γ) (B : RTy (Γ ∙)) →
           subTy σ (Σ' A B) ≡ Σ' (subTy σ A) (subTy (extS σ) B)
Σ-stable σ A B = refl

-- Dependency substitutes coherently: `El` follows its term.
El-stable : (σ : Sub Γ Δ) (t : RTm Γ) → subTy σ (El t) ≡ El (subTm σ t)
El-stable σ t = refl

-- `Hom` is substitution-stable definitionally too — the former adds no
-- Beck–Chevalley debt.
Hom-stable : (σ : Sub Γ Δ) (A : RTy Γ) (t u : RTm Γ) →
             subTy σ (Hom A t u) ≡ Hom (subTy σ A) (subTm σ t) (subTm σ u)
Hom-stable σ A t u = refl

-- three-argument congruence, for the `Hom` clauses of the calculus below
Hom-cong₃ : {A A' : RTy Γ} {t t' u u' : RTm Γ} →
            A ≡ A' → t ≡ t' → u ≡ u' → Hom A t u ≡ Hom A' t' u'
Hom-cong₃ refl refl refl = refl

-- A concrete dependent type and its substitution: `(x : base) → El x`.
Πdep : RTy Γ
Πdep = Π base (El (var vz))

_ : (σ : Sub Γ Δ) → subTy σ Πdep ≡ Π base (El (var vz))
_ = λ σ → refl

------------------------------------------------------------------------
-- ...and it is a COHERENT strict calculus: the mutual substitution laws.
-- Congruence under pointwise-equal renamings/substitutions (funext-free).
------------------------------------------------------------------------

extR-cong : {ρ ρ' : Ren Γ Δ} → (∀ (x : Var Γ) → ρ x ≡ ρ' x) →
            ∀ (x : Var (Γ ∙)) → extR ρ x ≡ extR ρ' x
extR-cong h vz     = refl
extR-cong h (vs x) = cong vs (h x)

renTy-cong : {ρ ρ' : Ren Γ Δ} → (∀ (x : Var Γ) → ρ x ≡ ρ' x) →
             (A : RTy Γ) → renTy ρ A ≡ renTy ρ' A
renTm-cong : {ρ ρ' : Ren Γ Δ} → (∀ (x : Var Γ) → ρ x ≡ ρ' x) →
             (t : RTm Γ) → renTm ρ t ≡ renTm ρ' t
renTy-cong h base     = refl
renTy-cong h U        = refl
renTy-cong h (Π A B)  = cong₂ Π (renTy-cong h A) (renTy-cong (extR-cong h) B)
renTy-cong h (Σ' A B) = cong₂ Σ' (renTy-cong h A) (renTy-cong (extR-cong h) B)
renTy-cong h (El t)   = cong El (renTm-cong h t)
renTy-cong h (Hom A t u) =
  Hom-cong₃ (renTy-cong h A) (renTm-cong h t) (renTm-cong h u)
renTm-cong h (var x)   = cong var (h x)
renTm-cong h (lam t)   = cong lam (renTm-cong (extR-cong h) t)
renTm-cong h (app t u)  = cong₂ app (renTm-cong h t) (renTm-cong h u)
renTm-cong h (pair a b) = cong₂ pair (renTm-cong h a) (renTm-cong h b)
renTm-cong h (fst p)    = cong fst (renTm-cong h p)
renTm-cong h (snd p)    = cong snd (renTm-cong h p)
renTm-cong h ⌜base⌝     = refl
renTm-cong h (⌜Π⌝ c d)  = cong₂ ⌜Π⌝ (renTm-cong h c) (renTm-cong (extR-cong h) d)
renTm-cong h (⌜Σ⌝ c d)  = cong₂ ⌜Σ⌝ (renTm-cong h c) (renTm-cong (extR-cong h) d)

extS-cong : {σ σ' : Sub Γ Δ} → (∀ (x : Var Γ) → σ x ≡ σ' x) →
            ∀ (x : Var (Γ ∙)) → extS σ x ≡ extS σ' x
extS-cong h vz     = refl
extS-cong h (vs x) = cong (renTm vs) (h x)

subTy-cong : {σ σ' : Sub Γ Δ} → (∀ (x : Var Γ) → σ x ≡ σ' x) →
             (A : RTy Γ) → subTy σ A ≡ subTy σ' A
subTm-cong : {σ σ' : Sub Γ Δ} → (∀ (x : Var Γ) → σ x ≡ σ' x) →
             (t : RTm Γ) → subTm σ t ≡ subTm σ' t
subTy-cong h base     = refl
subTy-cong h U        = refl
subTy-cong h (Π A B)  = cong₂ Π (subTy-cong h A) (subTy-cong (extS-cong h) B)
subTy-cong h (Σ' A B) = cong₂ Σ' (subTy-cong h A) (subTy-cong (extS-cong h) B)
subTy-cong h (El t)   = cong El (subTm-cong h t)
subTy-cong h (Hom A t u) =
  Hom-cong₃ (subTy-cong h A) (subTm-cong h t) (subTm-cong h u)
subTm-cong h (var x)   = h x
subTm-cong h (lam t)   = cong lam (subTm-cong (extS-cong h) t)
subTm-cong h (app t u)  = cong₂ app (subTm-cong h t) (subTm-cong h u)
subTm-cong h (pair a b) = cong₂ pair (subTm-cong h a) (subTm-cong h b)
subTm-cong h (fst p)    = cong fst (subTm-cong h p)
subTm-cong h (snd p)    = cong snd (subTm-cong h p)
subTm-cong h ⌜base⌝     = refl
subTm-cong h (⌜Π⌝ c d)  = cong₂ ⌜Π⌝ (subTm-cong h c) (subTm-cong (extS-cong h) d)
subTm-cong h (⌜Σ⌝ c d)  = cong₂ ⌜Σ⌝ (subTm-cong h c) (subTm-cong (extS-cong h) d)

------------------------------------------------------------------------
-- The four mutual fusion lemmas (each a type/term pair). Binder cases bridge
-- lift-then-compose vs compose-then-lift via a pointwise ext-lemma + `*-cong`.
------------------------------------------------------------------------

-- ren ∘ ren.
extr-extr : (ρ' : Ren Δ Θ) (ρ : Ren Γ Δ) (x : Var (Γ ∙)) →
            (extR ρ' ∘ᵣ extR ρ) x ≡ extR (ρ' ∘ᵣ ρ) x
extr-extr ρ' ρ vz     = refl
extr-extr ρ' ρ (vs x) = refl

renTy-renTy : {ρ' : Ren Δ Θ} {ρ : Ren Γ Δ} (A : RTy Γ) →
              renTy ρ' (renTy ρ A) ≡ renTy (ρ' ∘ᵣ ρ) A
renTm-renTm : {ρ' : Ren Δ Θ} {ρ : Ren Γ Δ} (t : RTm Γ) →
              renTm ρ' (renTm ρ t) ≡ renTm (ρ' ∘ᵣ ρ) t
renTy-renTy base     = refl
renTy-renTy U        = refl
renTy-renTy {ρ' = ρ'} {ρ} (Π A B) =
  cong₂ Π (renTy-renTy A) (trans (renTy-renTy B) (renTy-cong (extr-extr ρ' ρ) B))
renTy-renTy {ρ' = ρ'} {ρ} (Σ' A B) =
  cong₂ Σ' (renTy-renTy A) (trans (renTy-renTy B) (renTy-cong (extr-extr ρ' ρ) B))
renTy-renTy (El t)   = cong El (renTm-renTm t)
renTy-renTy (Hom A t u) =
  Hom-cong₃ (renTy-renTy A) (renTm-renTm t) (renTm-renTm u)
renTm-renTm (var x)   = refl
renTm-renTm {ρ' = ρ'} {ρ} (lam t) =
  cong lam (trans (renTm-renTm t) (renTm-cong (extr-extr ρ' ρ) t))
renTm-renTm (app t u)  = cong₂ app (renTm-renTm t) (renTm-renTm u)
renTm-renTm (pair a b) = cong₂ pair (renTm-renTm a) (renTm-renTm b)
renTm-renTm (fst p)    = cong fst (renTm-renTm p)
renTm-renTm (snd p)    = cong snd (renTm-renTm p)
renTm-renTm ⌜base⌝     = refl
renTm-renTm {ρ' = ρ'} {ρ} (⌜Π⌝ c d) =
  cong₂ ⌜Π⌝ (renTm-renTm c) (trans (renTm-renTm d) (renTm-cong (extr-extr ρ' ρ) d))
renTm-renTm {ρ' = ρ'} {ρ} (⌜Σ⌝ c d) =
  cong₂ ⌜Σ⌝ (renTm-renTm c) (trans (renTm-renTm d) (renTm-cong (extr-extr ρ' ρ) d))

-- sub ∘ ren.
exts-extr : (σ : Sub Δ Θ) (ρ : Ren Γ Δ) (x : Var (Γ ∙)) →
            (extS σ ₛ∘ᵣ extR ρ) x ≡ extS (σ ₛ∘ᵣ ρ) x
exts-extr σ ρ vz     = refl
exts-extr σ ρ (vs x) = refl

subTy-renTy : {σ : Sub Δ Θ} {ρ : Ren Γ Δ} (A : RTy Γ) →
              subTy σ (renTy ρ A) ≡ subTy (σ ₛ∘ᵣ ρ) A
subTm-renTm : {σ : Sub Δ Θ} {ρ : Ren Γ Δ} (t : RTm Γ) →
              subTm σ (renTm ρ t) ≡ subTm (σ ₛ∘ᵣ ρ) t
subTy-renTy base     = refl
subTy-renTy U        = refl
subTy-renTy {σ = σ} {ρ} (Π A B) =
  cong₂ Π (subTy-renTy A) (trans (subTy-renTy B) (subTy-cong (exts-extr σ ρ) B))
subTy-renTy {σ = σ} {ρ} (Σ' A B) =
  cong₂ Σ' (subTy-renTy A) (trans (subTy-renTy B) (subTy-cong (exts-extr σ ρ) B))
subTy-renTy (El t)   = cong El (subTm-renTm t)
subTy-renTy (Hom A t u) =
  Hom-cong₃ (subTy-renTy A) (subTm-renTm t) (subTm-renTm u)
subTm-renTm (var x)   = refl
subTm-renTm {σ = σ} {ρ} (lam t) =
  cong lam (trans (subTm-renTm t) (subTm-cong (exts-extr σ ρ) t))
subTm-renTm (app t u)  = cong₂ app (subTm-renTm t) (subTm-renTm u)
subTm-renTm (pair a b) = cong₂ pair (subTm-renTm a) (subTm-renTm b)
subTm-renTm (fst p)    = cong fst (subTm-renTm p)
subTm-renTm (snd p)    = cong snd (subTm-renTm p)
subTm-renTm ⌜base⌝     = refl
subTm-renTm {σ = σ} {ρ} (⌜Π⌝ c d) =
  cong₂ ⌜Π⌝ (subTm-renTm c) (trans (subTm-renTm d) (subTm-cong (exts-extr σ ρ) d))
subTm-renTm {σ = σ} {ρ} (⌜Σ⌝ c d) =
  cong₂ ⌜Σ⌝ (subTm-renTm c) (trans (subTm-renTm d) (subTm-cong (exts-extr σ ρ) d))

-- ren ∘ sub.
extr-exts : (ρ : Ren Δ Θ) (σ : Sub Γ Δ) (x : Var (Γ ∙)) →
            (extR ρ ᵣ∘ₛ extS σ) x ≡ extS (ρ ᵣ∘ₛ σ) x
extr-exts ρ σ vz     = refl
extr-exts ρ σ (vs x) = trans (renTm-renTm (σ x)) (sym (renTm-renTm (σ x)))

renTy-subTy : {ρ : Ren Δ Θ} {σ : Sub Γ Δ} (A : RTy Γ) →
              renTy ρ (subTy σ A) ≡ subTy (ρ ᵣ∘ₛ σ) A
renTm-subTm : {ρ : Ren Δ Θ} {σ : Sub Γ Δ} (t : RTm Γ) →
              renTm ρ (subTm σ t) ≡ subTm (ρ ᵣ∘ₛ σ) t
renTy-subTy base     = refl
renTy-subTy U        = refl
renTy-subTy {ρ = ρ} {σ} (Π A B) =
  cong₂ Π (renTy-subTy A) (trans (renTy-subTy B) (subTy-cong (extr-exts ρ σ) B))
renTy-subTy {ρ = ρ} {σ} (Σ' A B) =
  cong₂ Σ' (renTy-subTy A) (trans (renTy-subTy B) (subTy-cong (extr-exts ρ σ) B))
renTy-subTy (El t)   = cong El (renTm-subTm t)
renTy-subTy (Hom A t u) =
  Hom-cong₃ (renTy-subTy A) (renTm-subTm t) (renTm-subTm u)
renTm-subTm (var x)   = refl
renTm-subTm {ρ = ρ} {σ} (lam t) =
  cong lam (trans (renTm-subTm t) (subTm-cong (extr-exts ρ σ) t))
renTm-subTm (app t u)  = cong₂ app (renTm-subTm t) (renTm-subTm u)
renTm-subTm (pair a b) = cong₂ pair (renTm-subTm a) (renTm-subTm b)
renTm-subTm (fst p)    = cong fst (renTm-subTm p)
renTm-subTm (snd p)    = cong snd (renTm-subTm p)
renTm-subTm ⌜base⌝     = refl
renTm-subTm {ρ = ρ} {σ} (⌜Π⌝ c d) =
  cong₂ ⌜Π⌝ (renTm-subTm c) (trans (renTm-subTm d) (subTm-cong (extr-exts ρ σ) d))
renTm-subTm {ρ = ρ} {σ} (⌜Σ⌝ c d) =
  cong₂ ⌜Σ⌝ (renTm-subTm c) (trans (renTm-subTm d) (subTm-cong (extr-exts ρ σ) d))

-- sub ∘ sub.
exts-exts : (τ : Sub Δ Θ) (σ : Sub Γ Δ) (x : Var (Γ ∙)) →
            (extS τ ∘ₛ extS σ) x ≡ extS (τ ∘ₛ σ) x
exts-exts τ σ vz     = refl
exts-exts τ σ (vs x) = trans (subTm-renTm (σ x)) (sym (renTm-subTm (σ x)))

subTy-subTy : {τ : Sub Δ Θ} {σ : Sub Γ Δ} (A : RTy Γ) →
              subTy τ (subTy σ A) ≡ subTy (τ ∘ₛ σ) A
subTm-subTm : {τ : Sub Δ Θ} {σ : Sub Γ Δ} (t : RTm Γ) →
              subTm τ (subTm σ t) ≡ subTm (τ ∘ₛ σ) t
subTy-subTy base     = refl
subTy-subTy U        = refl
subTy-subTy {τ = τ} {σ} (Π A B) =
  cong₂ Π (subTy-subTy A) (trans (subTy-subTy B) (subTy-cong (exts-exts τ σ) B))
subTy-subTy {τ = τ} {σ} (Σ' A B) =
  cong₂ Σ' (subTy-subTy A) (trans (subTy-subTy B) (subTy-cong (exts-exts τ σ) B))
subTy-subTy (El t)   = cong El (subTm-subTm t)
subTy-subTy (Hom A t u) =
  Hom-cong₃ (subTy-subTy A) (subTm-subTm t) (subTm-subTm u)
subTm-subTm (var x)   = refl
subTm-subTm {τ = τ} {σ} (lam t) =
  cong lam (trans (subTm-subTm t) (subTm-cong (exts-exts τ σ) t))
subTm-subTm (app t u)  = cong₂ app (subTm-subTm t) (subTm-subTm u)
subTm-subTm (pair a b) = cong₂ pair (subTm-subTm a) (subTm-subTm b)
subTm-subTm (fst p)    = cong fst (subTm-subTm p)
subTm-subTm (snd p)    = cong snd (subTm-subTm p)
subTm-subTm ⌜base⌝     = refl
subTm-subTm {τ = τ} {σ} (⌜Π⌝ c d) =
  cong₂ ⌜Π⌝ (subTm-subTm c) (trans (subTm-subTm d) (subTm-cong (exts-exts τ σ) d))
subTm-subTm {τ = τ} {σ} (⌜Σ⌝ c d) =
  cong₂ ⌜Σ⌝ (subTm-subTm c) (trans (subTm-subTm d) (subTm-cong (exts-exts τ σ) d))

-- Identity: `exts` preserves `idₛ`, hence `subTy idₛ = id`.
exts-id : (x : Var (Γ ∙)) → extS idₛ x ≡ idₛ x
exts-id vz     = refl
exts-id (vs x) = refl

subTy-id : (A : RTy Γ) → subTy idₛ A ≡ A
subTm-id : (t : RTm Γ) → subTm idₛ t ≡ t
subTy-id base     = refl
subTy-id U        = refl
subTy-id (Π A B)  = cong₂ Π (subTy-id A) (trans (subTy-cong exts-id B) (subTy-id B))
subTy-id (Σ' A B) = cong₂ Σ' (subTy-id A) (trans (subTy-cong exts-id B) (subTy-id B))
subTy-id (El t)   = cong El (subTm-id t)
subTy-id (Hom A t u) = Hom-cong₃ (subTy-id A) (subTm-id t) (subTm-id u)
subTm-id (var x)   = refl
subTm-id (lam t)   = cong lam (trans (subTm-cong exts-id t) (subTm-id t))
subTm-id (app t u)  = cong₂ app (subTm-id t) (subTm-id u)
subTm-id (pair a b) = cong₂ pair (subTm-id a) (subTm-id b)
subTm-id (fst p)    = cong fst (subTm-id p)
subTm-id (snd p)    = cong snd (subTm-id p)
subTm-id ⌜base⌝     = refl
subTm-id (⌜Π⌝ c d)  = cong₂ ⌜Π⌝ (subTm-id c) (trans (subTm-cong exts-id d) (subTm-id d))
subTm-id (⌜Σ⌝ c d)  = cong₂ ⌜Σ⌝ (subTm-id c) (trans (subTm-cong exts-id d) (subTm-id d))

------------------------------------------------------------------------
-- ★ THE CATEGORY-OF-CONTEXTS LAWS ON TYPES — the coherence that makes the
--   definitional Π-stability NON-vacuous. `[∘]ᵀ` is the Beck–Chevalley-
--   relevant law: type substitution commutes with COMPOSITION, so Π commutes
--   STRICTLY with composed substitutions (combine with `Π-stable`).
------------------------------------------------------------------------

[id]ᵀ : (A : RTy Γ) → subTy idₛ A ≡ A
[id]ᵀ = subTy-id

[∘]ᵀ : {τ : Sub Δ Θ} {σ : Sub Γ Δ} (A : RTy Γ) →
       subTy τ (subTy σ A) ≡ subTy (τ ∘ₛ σ) A
[∘]ᵀ = subTy-subTy

-- Π commutes with composed substitution, on the nose (Beck–Chevalley,
-- strictly): both routes land at the same Π with no comparison map.
Π-BeckChevalley : {τ : Sub Δ Θ} {σ : Sub Γ Δ} (A : RTy Γ) (B : RTy (Γ ∙)) →
                  subTy τ (subTy σ (Π A B)) ≡ subTy (τ ∘ₛ σ) (Π A B)
Π-BeckChevalley A B = subTy-subTy (Π A B)
