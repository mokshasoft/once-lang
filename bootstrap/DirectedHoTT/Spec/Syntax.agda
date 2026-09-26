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
module DirectedHoTT.Spec.Syntax where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂ )
-- ★ INDUCTIVE-TYPES AXIS: a metalanguage ℕ, used only as a CONSTRUCTOR
--   TAG.  It is not the object-language `Nat`.
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )

-- ⚠ LOCAL: `normalizer.Syntax.Types` exports `cong₂` but not `cong₃`, and
--   `Lib/Wk`'s copy is downstream of this module.  Three lines beats an
--   import cycle.
cong₃ : {A B C D : Set} (f : A → B → C → D) {a a' : A} {b b' : B} {c c' : C} →
        a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

cong₄ : {A B C D E : Set} (f : A → B → C → D → E) {a a' : A} {b b' : B} {c c' : C} {d d' : D} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → f a b c d ≡ f a' b' c' d'
cong₄ f refl refl refl refl = refl

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
-- ★★ LEVITATION (PLAN-LEVITATION, D071–D073): descriptions are TERMS
--   of the large type `Desc I`, so there is no separate description
--   syntax — and renaming/substitution traverse them like any term.

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
  -- ★ WF-axis stage A (SPIKE-WF): the datatype core's type formers.
  Unit : ∀ {Γ} → RTy Γ
  Nat  : ∀ {Γ} → RTy Γ
  -- ★ the TWO-FORMER kernel (SPIKE-TWOFORMER): the SYMMETRIC identity
  -- type, INERT — no type-level computation, ξ-congruences only.
  Id   : ∀ {Γ} → RTy Γ → RTm Γ → RTm Γ → RTy Γ
  -- ★★ INDUCTIVE FAMILIES (levitated).  `IMu I D i`: the family described
  --   by the TERM `D : Desc I` at index `i : El I`.  The index type is a
  --   CODE in Γ (D073).
  IMu  : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ → RTy Γ
  -- ★ the LARGE type of descriptions over the index code `I` (no code:
  --   level 1, SPIKE-LEVITATION S0).
  Desc : ∀ {Γ} → RTm Γ → RTy Γ
  -- ★ the induction hypotheses a payload `p` of telescope `C` owes, for
  --   the motive `M` (index, scrutinee).  Computes on the telescope head
  --   (`_⟶ᵀ_`); stuck on a neutral telescope.
  DIh  : ∀ {Γ} → RTm Γ → RTy ((Γ ∙) ∙) → RTm Γ → RTm Γ → RTy Γ
  -- ★ the TAG type: a finite enumeration {0 … n-1} (constructor choice).
  Fin  : ∀ {Γ} → ℕ → RTy Γ

data RTm where
  var  : ∀ {Γ} → Var Γ → RTm Γ
  lam  : ∀ {Γ} → RTm (Γ ∙) → RTm Γ
  app  : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ
  pair : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ    -- Σ introduction
  -- ★★ WF-axis stage D: EX FALSO.  `base` had formation only — no
  -- intro, no elim — so a false inequality COMPUTED to the empty type
  -- but could not be USED: the impossible branch was refutable only
  -- meta-theoretically, via `consistency`.  This is the eliminator that
  -- turns that metatheorem into a programming technique, and it is what
  -- strong induction needs at `Hom Nat (nsuc k) nzero ⟶ᵀ base`.
  --
  -- The result type lives in the DERIVATION only (the `⊢lam`/`⊢natrec`
  -- motive pattern), so the syntax stays unary.
  absurd : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ
  -- ★★ WF-axis: ORDER TRANSPORT — ≤-transitivity at OPEN naturals.
  -- `tr` cannot serve: it is endpoint-BLIND (its `t`/`u` live only in
  -- the derivation), and at a `Nat` ambient the answer depends on them.
  -- So `ordtr` carries all THREE endpoints in the term.
  --                     a        t        u        p        q
  ordtr : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  fst  : ∀ {Γ} → RTm Γ → RTm Γ            -- Σ elimination
  snd  : ∀ {Γ} → RTm Γ → RTm Γ
  ⌜base⌝ : ∀ {Γ} → RTm Γ                  -- code for `base`
  ⌜Π⌝    : ∀ {Γ} → RTm Γ → RTm (Γ ∙) → RTm Γ  -- code for `Π` (dependent codomain)
  ⌜Σ⌝    : ∀ {Γ} → RTm Γ → RTm (Γ ∙) → RTm Γ  -- code for `Σ`
  -- ★ W2 eliminator (SpikeHomRefl design (B) + SpikeTr): the code for
  -- `Hom` (hom-sets of small types are small; there is still no code for
  -- `U`), the code-annotated identity path, and directed transport with a
  -- CODE motive — `tr d p e` transports `e` along the path `p`, with
  -- motive `El d`; `d` binds the transported variable.
  ⌜Hom⌝  : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  hrefl  : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ
  tr     : ∀ {Γ} → RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ
  -- ★ directed `ap` (SpikeAp): a term's action on a hom.  `ap cB b p` —
  -- `cB` the TARGET code (the result reflexivity's annotation), `b` the
  -- body (vz free), `p` the path.  Typing restricts the SOURCE ambient
  -- to stable codes; `ap-J` is the one computation rule.
  ap     : ∀ {Γ} → RTm Γ → RTm (Γ ∙) → RTm Γ → RTm Γ
  -- ★ the two-former kernel: the Id code, the (code-annotated)
  -- reflexivity, and subst-style J at an UNRESTRICTED code family.
  ⌜Id⌝   : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  idrefl : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ
  jsub   : ∀ {Γ} → RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ
  -- ★ WF-axis stage A: unit, numerals, and the TYPE-motived recursor
  -- (motive in the derivation only, the ⊢lam pattern; `s` binds the
  -- number then the IH).
  unit   : ∀ {Γ} → RTm Γ
  nzero  : ∀ {Γ} → RTm Γ
  nsuc   : ∀ {Γ} → RTm Γ → RTm Γ
  natrec : ∀ {Γ} → RTm Γ → RTm ((Γ ∙) ∙) → RTm Γ → RTm Γ
  -- ★★ INDUCTIVE FAMILIES (levitated, one-telescope form).
  --   `con p`           a constructor: the payload of the WHOLE telescope
  --                     (constructor choice is its first, tag, field).
  --   `ielim D i e t`   eliminate at index `i` with ONE method `e`; the
  --                     motive lives in the derivation (the ⊢natrec pattern).
  con   : ∀ {Γ} → RTm Γ → RTm Γ
  ielim : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  -- ★ telescopes: end at index `j` / a field of code `S` then the rest as
  --   a FUNCTION of it / a recursive field at index `j`.  Strict
  --   positivity is the GRAMMAR: `dρ` names an index, never a family.
  dι    : ∀ {Γ} → RTm Γ → RTm Γ
  dσ    : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ
  dρ    : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ
  -- ★ the payload CODE of telescope `C` at index `i`, recursion into
  --   `IMu I D` (`dpay I D C i`), and the IH tuple (`dih D e C p`).
  dpay  : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  dih   : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  -- ★ tags: `fzero`, `fsuc`, the case split of Fin (n+1) ≅ 1 + Fin n
  --   (motive in the derivation), and the elimination of the empty Fin 0.
  fzero  : ∀ {Γ} → RTm Γ
  fsuc   : ∀ {Γ} → RTm Γ → RTm Γ
  fcase  : ∀ {Γ} → RTm Γ → RTm Γ → RTm (Γ ∙) → RTm Γ
  fcase0 : ∀ {Γ} → RTm Γ → RTm Γ
  -- ★ Σ-INDUCTION (D071): `psplit b q`, `b` binds both halves.
  psplit : ∀ {Γ} → RTm ((Γ ∙) ∙) → RTm Γ → RTm Γ
  -- ★ WF-axis stage C (N-in): `Nat` becomes SMALL — it gets a code, so
  -- it can appear in `U`-families.  That is what unlocks Id-rewriting
  -- AT `Nat` (`jsub` needs a code family), cong-at-ℕ, and ≤ as a
  -- transportable relation.
  ⌜Nat⌝  : ∀ {Γ} → RTm Γ
  -- ★ the CODE of a family at an index: families are SMALL, so they
  --   nest (a field of code `⌜IMu⌝ …`) and are `amrec` carriers.
  ⌜IMu⌝  : ∀ {Γ} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  ⌜Fin⌝  : ∀ {Γ} → ℕ → RTm Γ
  ⌜Unit⌝ : ∀ {Γ} → RTm Γ

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

-- ★ A THINNING — an order-preserving embedding, as FIRST-ORDER data.
--   Where a renaming is any function on variables, a thinning can only
--   KEEP a variable or DROP (skip) one of the target's, in order — so
--   it is exactly a WEAKENING.  A-math's constructor telescopes are the
--   customer: the constructor's own scope embeds into the telescope
--   omitting the abstract family, and that embedding is a thinning, not
--   an arbitrary renaming.  First-order is what lets the Knot reify it.
data Thin : Cx → Cx → Set where
  done : Thin ε ε
  keep : Thin Γ Δ → Thin (Γ ∙) (Δ ∙)
  drop : Thin Γ Δ → Thin Γ (Δ ∙)

-- its action on variables.  ⚠ `thinR (keep θ)` IS `extR (thinR θ)`
--   clause by clause, so a walk that extends by `keep` needs no lemma.
thinR : Thin Γ Δ → Ren Γ Δ
thinR (keep θ) vz     = vz
thinR (keep θ) (vs x) = vs (thinR θ x)
thinR (drop θ) x      = vs (thinR θ x)

renTy : Ren Γ Δ → RTy Γ → RTy Δ
renTm : Ren Γ Δ → RTm Γ → RTm Δ
renTy ρ Unit       = Unit
renTy ρ Nat        = Nat
renTy ρ base     = base
renTy ρ U        = U
renTy ρ (Π A B)  = Π (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (Σ' A B) = Σ' (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (El t)   = El (renTm ρ t)
renTy ρ (Hom A t u) = Hom (renTy ρ A) (renTm ρ t) (renTm ρ u)
renTy ρ (Id A t u) = Id (renTy ρ A) (renTm ρ t) (renTm ρ u)
renTy ρ (IMu I D i) = IMu (renTm ρ I) (renTm ρ D) (renTm ρ i)
renTy ρ (Desc I) = Desc (renTm ρ I)
renTy ρ (DIh D M C p) = DIh (renTm ρ D) (renTy (extR (extR ρ)) M) (renTm ρ C) (renTm ρ p)
renTy ρ (Fin n) = Fin n
renTm ρ (var x)   = var (ρ x)
renTm ρ (lam t)   = lam (renTm (extR ρ) t)
renTm ρ (app t u)  = app (renTm ρ t) (renTm ρ u)
renTm ρ (pair a b) = pair (renTm ρ a) (renTm ρ b)
renTm ρ (absurd c e) = absurd (renTm ρ c) (renTm ρ e)
renTm ρ (ordtr a t u p q) =
  ordtr (renTm ρ a) (renTm ρ t) (renTm ρ u) (renTm ρ p) (renTm ρ q)
renTm ρ (fst p)    = fst (renTm ρ p)
renTm ρ (snd p)    = snd (renTm ρ p)
renTm ρ ⌜base⌝     = ⌜base⌝
renTm ρ (⌜Π⌝ c d)  = ⌜Π⌝ (renTm ρ c) (renTm (extR ρ) d)
renTm ρ (⌜Σ⌝ c d)  = ⌜Σ⌝ (renTm ρ c) (renTm (extR ρ) d)
renTm ρ (⌜Hom⌝ c a b) = ⌜Hom⌝ (renTm ρ c) (renTm ρ a) (renTm ρ b)
renTm ρ (⌜Id⌝ c a b) = ⌜Id⌝ (renTm ρ c) (renTm ρ a) (renTm ρ b)
renTm ρ (hrefl c t)   = hrefl (renTm ρ c) (renTm ρ t)
renTm ρ (idrefl c t)   = idrefl (renTm ρ c) (renTm ρ t)
renTm ρ (tr d p e)    = tr (renTm (extR ρ) d) (renTm ρ p) (renTm ρ e)
renTm ρ (jsub d p e)    = jsub (renTm (extR ρ) d) (renTm ρ p) (renTm ρ e)
renTm ρ (ap c b p)    = ap (renTm ρ c) (renTm (extR ρ) b) (renTm ρ p)
renTm ρ ⌜Nat⌝         = ⌜Nat⌝
renTm ρ (⌜IMu⌝ I D i) = ⌜IMu⌝ (renTm ρ I) (renTm ρ D) (renTm ρ i)
renTm ρ (⌜Fin⌝ n) = ⌜Fin⌝ n
renTm ρ (con p) = con (renTm ρ p)
renTm ρ (ielim D i e t) = ielim (renTm ρ D) (renTm ρ i) (renTm ρ e) (renTm ρ t)
renTm ρ (dι j) = dι (renTm ρ j)
renTm ρ (dσ S f) = dσ (renTm ρ S) (renTm ρ f)
renTm ρ (dρ j C) = dρ (renTm ρ j) (renTm ρ C)
renTm ρ (dpay I D C i) = dpay (renTm ρ I) (renTm ρ D) (renTm ρ C) (renTm ρ i)
renTm ρ (dih D e C p) = dih (renTm ρ D) (renTm ρ e) (renTm ρ C) (renTm ρ p)
renTm ρ fzero = fzero
renTm ρ (fsuc t) = fsuc (renTm ρ t)
renTm ρ (fcase t a b) = fcase (renTm ρ t) (renTm ρ a) (renTm (extR ρ) b)
renTm ρ (fcase0 t) = fcase0 (renTm ρ t)
renTm ρ (psplit b q) = psplit (renTm (extR (extR ρ)) b) (renTm ρ q)
renTm ρ ⌜Unit⌝        = ⌜Unit⌝
renTm ρ unit          = unit
renTm ρ nzero         = nzero
renTm ρ (nsuc n)      = nsuc (renTm ρ n)
renTm ρ (natrec z s n) =
  natrec (renTm ρ z) (renTm (extR (extR ρ)) s) (renTm ρ n)

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
subTy σ Unit       = Unit
subTy σ Nat        = Nat
subTy σ base     = base
subTy σ U        = U
subTy σ (Π A B)  = Π (subTy σ A) (subTy (extS σ) B)
subTy σ (Σ' A B) = Σ' (subTy σ A) (subTy (extS σ) B)
subTy σ (El t)   = El (subTm σ t)
subTy σ (Hom A t u) = Hom (subTy σ A) (subTm σ t) (subTm σ u)
subTy σ (Id A t u) = Id (subTy σ A) (subTm σ t) (subTm σ u)
subTy σ (IMu I D i) = IMu (subTm σ I) (subTm σ D) (subTm σ i)
subTy σ (Desc I) = Desc (subTm σ I)
subTy σ (DIh D M C p) = DIh (subTm σ D) (subTy (extS (extS σ)) M) (subTm σ C) (subTm σ p)
subTy σ (Fin n) = Fin n
subTm σ (var x)   = σ x
subTm σ (lam t)   = lam (subTm (extS σ) t)
subTm σ (app t u)  = app (subTm σ t) (subTm σ u)
subTm σ (pair a b) = pair (subTm σ a) (subTm σ b)
subTm σ (absurd c e) = absurd (subTm σ c) (subTm σ e)
subTm σ (ordtr a t u p q) =
  ordtr (subTm σ a) (subTm σ t) (subTm σ u) (subTm σ p) (subTm σ q)
subTm σ (fst p)    = fst (subTm σ p)
subTm σ (snd p)    = snd (subTm σ p)
subTm σ ⌜base⌝     = ⌜base⌝
subTm σ (⌜Π⌝ c d)  = ⌜Π⌝ (subTm σ c) (subTm (extS σ) d)
subTm σ (⌜Σ⌝ c d)  = ⌜Σ⌝ (subTm σ c) (subTm (extS σ) d)
subTm σ (⌜Hom⌝ c a b) = ⌜Hom⌝ (subTm σ c) (subTm σ a) (subTm σ b)
subTm σ (⌜Id⌝ c a b) = ⌜Id⌝ (subTm σ c) (subTm σ a) (subTm σ b)
subTm σ (hrefl c t)   = hrefl (subTm σ c) (subTm σ t)
subTm σ (idrefl c t)   = idrefl (subTm σ c) (subTm σ t)
subTm σ (tr d p e)    = tr (subTm (extS σ) d) (subTm σ p) (subTm σ e)
subTm σ (jsub d p e)    = jsub (subTm (extS σ) d) (subTm σ p) (subTm σ e)
subTm σ (ap c b p)    = ap (subTm σ c) (subTm (extS σ) b) (subTm σ p)
subTm σ ⌜Nat⌝         = ⌜Nat⌝
subTm σ (⌜IMu⌝ I D i) = ⌜IMu⌝ (subTm σ I) (subTm σ D) (subTm σ i)
subTm σ (⌜Fin⌝ n) = ⌜Fin⌝ n
subTm σ (con p) = con (subTm σ p)
subTm σ (ielim D i e t) = ielim (subTm σ D) (subTm σ i) (subTm σ e) (subTm σ t)
subTm σ (dι j) = dι (subTm σ j)
subTm σ (dσ S f) = dσ (subTm σ S) (subTm σ f)
subTm σ (dρ j C) = dρ (subTm σ j) (subTm σ C)
subTm σ (dpay I D C i) = dpay (subTm σ I) (subTm σ D) (subTm σ C) (subTm σ i)
subTm σ (dih D e C p) = dih (subTm σ D) (subTm σ e) (subTm σ C) (subTm σ p)
subTm σ fzero = fzero
subTm σ (fsuc t) = fsuc (subTm σ t)
subTm σ (fcase t a b) = fcase (subTm σ t) (subTm σ a) (subTm (extS σ) b)
subTm σ (fcase0 t) = fcase0 (subTm σ t)
subTm σ (psplit b q) = psplit (subTm (extS (extS σ)) b) (subTm σ q)
subTm σ ⌜Unit⌝        = ⌜Unit⌝
subTm σ unit          = unit
subTm σ nzero         = nzero
subTm σ (nsuc n)      = nsuc (subTm σ n)
subTm σ (natrec z s n) =
  natrec (subTm σ z) (subTm (extS (extS σ)) s) (subTm σ n)

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

-- ★ WF-axis: ordtr is 5-ary, so it gets its own congruence, in the
-- house style of `Hom-cong₃`.
ordtr-cong₅ : {a a' t t' u u' p p' q q' : RTm Γ} →
              a ≡ a' → t ≡ t' → u ≡ u' → p ≡ p' → q ≡ q' →
              ordtr a t u p q ≡ ordtr a' t' u' p' q'
ordtr-cong₅ refl refl refl refl refl = refl

Id-cong₃ : {A A' : RTy Γ} {t t' u u' : RTm Γ} →
           A ≡ A' → t ≡ t' → u ≡ u' → Id A t u ≡ Id A' t' u'
Id-cong₃ refl refl refl = refl

-- …and its term-level mirrors for the three W2 formers
⌜Hom⌝-cong₃ : {c c' a a' b b' : RTm Γ} →
              c ≡ c' → a ≡ a' → b ≡ b' → ⌜Hom⌝ c a b ≡ ⌜Hom⌝ c' a' b'
⌜Hom⌝-cong₃ refl refl refl = refl

tr-cong₃ : {d d' : RTm (Γ ∙)} {p p' e e' : RTm Γ} →
           d ≡ d' → p ≡ p' → e ≡ e' → tr d p e ≡ tr d' p' e'
tr-cong₃ refl refl refl = refl

ap-cong₃ : {c c' : RTm Γ} {b b' : RTm (Γ ∙)} {p p' : RTm Γ} →
           c ≡ c' → b ≡ b' → p ≡ p' → ap c b p ≡ ap c' b' p'
ap-cong₃ refl refl refl = refl

⌜Id⌝-cong₃ : {c c' a a' b b' : RTm Γ} →
             c ≡ c' → a ≡ a' → b ≡ b' → ⌜Id⌝ c a b ≡ ⌜Id⌝ c' a' b'
⌜Id⌝-cong₃ refl refl refl = refl

jsub-cong₃ : {d d' : RTm (Γ ∙)} {p p' e e' : RTm Γ} →
             d ≡ d' → p ≡ p' → e ≡ e' → jsub d p e ≡ jsub d' p' e'
jsub-cong₃ refl refl refl = refl

natrec-cong₃ : {z z' : RTm Γ} {s s' : RTm ((Γ ∙) ∙)} {n n' : RTm Γ} →
               z ≡ z' → s ≡ s' → n ≡ n' → natrec z s n ≡ natrec z' s' n'
natrec-cong₃ refl refl refl = refl

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
renTy-cong h Unit     = refl
renTy-cong h Nat      = refl
renTy-cong h U        = refl
renTy-cong h (Π A B)  = cong₂ Π (renTy-cong h A) (renTy-cong (extR-cong h) B)
renTy-cong h (Σ' A B) = cong₂ Σ' (renTy-cong h A) (renTy-cong (extR-cong h) B)
renTy-cong h (El t)   = cong El (renTm-cong h t)
renTy-cong h (Hom A t u) =
  Hom-cong₃ (renTy-cong h A) (renTm-cong h t) (renTm-cong h u)
renTy-cong h (Id A t u) =
  Id-cong₃ (renTy-cong h A) (renTm-cong h t) (renTm-cong h u)
renTy-cong h (IMu I D i) =
  cong₃ IMu (renTm-cong h I) (renTm-cong h D) (renTm-cong h i)
renTy-cong h (Desc I) =
  cong Desc (renTm-cong h I)
renTy-cong h (DIh D M C p) =
  cong₄ DIh (renTm-cong h D) (renTy-cong (extR-cong (extR-cong h)) M) (renTm-cong h C) (renTm-cong h p)
renTy-cong h (Fin n) =
  refl
renTm-cong h (var x)   = cong var (h x)
renTm-cong h (lam t)   = cong lam (renTm-cong (extR-cong h) t)
renTm-cong h (app t u)  = cong₂ app (renTm-cong h t) (renTm-cong h u)
renTm-cong h (pair a b) = cong₂ pair (renTm-cong h a) (renTm-cong h b)
renTm-cong h (absurd c e)    = cong₂ absurd (renTm-cong h c) (renTm-cong h e)
renTm-cong h (ordtr a t u p q)    = ordtr-cong₅ (renTm-cong h a) (renTm-cong h t) (renTm-cong h u) (renTm-cong h p) (renTm-cong h q)
renTm-cong h (fst p)    = cong fst (renTm-cong h p)
renTm-cong h (snd p)    = cong snd (renTm-cong h p)
renTm-cong h ⌜base⌝     = refl
renTm-cong h ⌜Nat⌝      = refl
renTm-cong h (⌜IMu⌝ I D i) =
  cong₃ ⌜IMu⌝ (renTm-cong h I) (renTm-cong h D) (renTm-cong h i)
renTm-cong h (⌜Fin⌝ n) =
  refl
renTm-cong h (con p) =
  cong con (renTm-cong h p)
renTm-cong h (ielim D i e t) =
  cong₄ ielim (renTm-cong h D) (renTm-cong h i) (renTm-cong h e) (renTm-cong h t)
renTm-cong h (dι j) =
  cong dι (renTm-cong h j)
renTm-cong h (dσ S f) =
  cong₂ dσ (renTm-cong h S) (renTm-cong h f)
renTm-cong h (dρ j C) =
  cong₂ dρ (renTm-cong h j) (renTm-cong h C)
renTm-cong h (dpay I D C i) =
  cong₄ dpay (renTm-cong h I) (renTm-cong h D) (renTm-cong h C) (renTm-cong h i)
renTm-cong h (dih D e C p) =
  cong₄ dih (renTm-cong h D) (renTm-cong h e) (renTm-cong h C) (renTm-cong h p)
renTm-cong h fzero =
  refl
renTm-cong h (fsuc t) =
  cong fsuc (renTm-cong h t)
renTm-cong h (fcase t a b) =
  cong₃ fcase (renTm-cong h t) (renTm-cong h a) (renTm-cong (extR-cong h) b)
renTm-cong h (fcase0 t) =
  cong fcase0 (renTm-cong h t)
renTm-cong h (psplit b q) =
  cong₂ psplit (renTm-cong (extR-cong (extR-cong h)) b) (renTm-cong h q)
renTm-cong h ⌜Unit⌝     = refl
renTm-cong h unit      = refl
renTm-cong h nzero     = refl
renTm-cong h (nsuc n)  = cong nsuc (renTm-cong h n)
renTm-cong h (natrec z s₂ n) =
  natrec-cong₃ (renTm-cong h z) (renTm-cong (extR-cong (extR-cong h)) s₂) (renTm-cong h n)
renTm-cong h (⌜Π⌝ c d)  = cong₂ ⌜Π⌝ (renTm-cong h c) (renTm-cong (extR-cong h) d)
renTm-cong h (⌜Σ⌝ c d)  = cong₂ ⌜Σ⌝ (renTm-cong h c) (renTm-cong (extR-cong h) d)
renTm-cong h (⌜Hom⌝ c a b) =
  ⌜Hom⌝-cong₃ (renTm-cong h c) (renTm-cong h a) (renTm-cong h b)
renTm-cong h (⌜Id⌝ c a b) =
  ⌜Id⌝-cong₃ (renTm-cong h c) (renTm-cong h a) (renTm-cong h b)
renTm-cong h (hrefl c t)   = cong₂ hrefl (renTm-cong h c) (renTm-cong h t)
renTm-cong h (idrefl c t)   = cong₂ idrefl (renTm-cong h c) (renTm-cong h t)
renTm-cong h (tr d p e)    =
  tr-cong₃ (renTm-cong (extR-cong h) d) (renTm-cong h p) (renTm-cong h e)
renTm-cong h (jsub d p e)    =
  jsub-cong₃ (renTm-cong (extR-cong h) d) (renTm-cong h p) (renTm-cong h e)
renTm-cong h (ap c b p)    =
  ap-cong₃ (renTm-cong h c) (renTm-cong (extR-cong h) b) (renTm-cong h p)

extS-cong : {σ σ' : Sub Γ Δ} → (∀ (x : Var Γ) → σ x ≡ σ' x) →
            ∀ (x : Var (Γ ∙)) → extS σ x ≡ extS σ' x
extS-cong h vz     = refl
extS-cong h (vs x) = cong (renTm vs) (h x)

subTy-cong : {σ σ' : Sub Γ Δ} → (∀ (x : Var Γ) → σ x ≡ σ' x) →
             (A : RTy Γ) → subTy σ A ≡ subTy σ' A
subTm-cong : {σ σ' : Sub Γ Δ} → (∀ (x : Var Γ) → σ x ≡ σ' x) →
             (t : RTm Γ) → subTm σ t ≡ subTm σ' t
subTy-cong h base     = refl
subTy-cong h Unit     = refl
subTy-cong h Nat      = refl
subTy-cong h U        = refl
subTy-cong h (Π A B)  = cong₂ Π (subTy-cong h A) (subTy-cong (extS-cong h) B)
subTy-cong h (Σ' A B) = cong₂ Σ' (subTy-cong h A) (subTy-cong (extS-cong h) B)
subTy-cong h (El t)   = cong El (subTm-cong h t)
subTy-cong h (Hom A t u) =
  Hom-cong₃ (subTy-cong h A) (subTm-cong h t) (subTm-cong h u)
subTy-cong h (Id A t u) =
  Id-cong₃ (subTy-cong h A) (subTm-cong h t) (subTm-cong h u)
subTy-cong h (IMu I D i) =
  cong₃ IMu (subTm-cong h I) (subTm-cong h D) (subTm-cong h i)
subTy-cong h (Desc I) =
  cong Desc (subTm-cong h I)
subTy-cong h (DIh D M C p) =
  cong₄ DIh (subTm-cong h D) (subTy-cong (extS-cong (extS-cong h)) M) (subTm-cong h C) (subTm-cong h p)
subTy-cong h (Fin n) =
  refl
subTm-cong h (var x)   = h x
subTm-cong h (lam t)   = cong lam (subTm-cong (extS-cong h) t)
subTm-cong h (app t u)  = cong₂ app (subTm-cong h t) (subTm-cong h u)
subTm-cong h (pair a b) = cong₂ pair (subTm-cong h a) (subTm-cong h b)
subTm-cong h (absurd c e)    = cong₂ absurd (subTm-cong h c) (subTm-cong h e)
subTm-cong h (ordtr a t u p q)    = ordtr-cong₅ (subTm-cong h a) (subTm-cong h t) (subTm-cong h u) (subTm-cong h p) (subTm-cong h q)
subTm-cong h (fst p)    = cong fst (subTm-cong h p)
subTm-cong h (snd p)    = cong snd (subTm-cong h p)
subTm-cong h ⌜base⌝     = refl
subTm-cong h ⌜Nat⌝      = refl
subTm-cong h (⌜IMu⌝ I D i) =
  cong₃ ⌜IMu⌝ (subTm-cong h I) (subTm-cong h D) (subTm-cong h i)
subTm-cong h (⌜Fin⌝ n) =
  refl
subTm-cong h (con p) =
  cong con (subTm-cong h p)
subTm-cong h (ielim D i e t) =
  cong₄ ielim (subTm-cong h D) (subTm-cong h i) (subTm-cong h e) (subTm-cong h t)
subTm-cong h (dι j) =
  cong dι (subTm-cong h j)
subTm-cong h (dσ S f) =
  cong₂ dσ (subTm-cong h S) (subTm-cong h f)
subTm-cong h (dρ j C) =
  cong₂ dρ (subTm-cong h j) (subTm-cong h C)
subTm-cong h (dpay I D C i) =
  cong₄ dpay (subTm-cong h I) (subTm-cong h D) (subTm-cong h C) (subTm-cong h i)
subTm-cong h (dih D e C p) =
  cong₄ dih (subTm-cong h D) (subTm-cong h e) (subTm-cong h C) (subTm-cong h p)
subTm-cong h fzero =
  refl
subTm-cong h (fsuc t) =
  cong fsuc (subTm-cong h t)
subTm-cong h (fcase t a b) =
  cong₃ fcase (subTm-cong h t) (subTm-cong h a) (subTm-cong (extS-cong h) b)
subTm-cong h (fcase0 t) =
  cong fcase0 (subTm-cong h t)
subTm-cong h (psplit b q) =
  cong₂ psplit (subTm-cong (extS-cong (extS-cong h)) b) (subTm-cong h q)
subTm-cong h ⌜Unit⌝     = refl
subTm-cong h unit      = refl
subTm-cong h nzero     = refl
subTm-cong h (nsuc n)  = cong nsuc (subTm-cong h n)
subTm-cong h (natrec z s₂ n) =
  natrec-cong₃ (subTm-cong h z) (subTm-cong (extS-cong (extS-cong h)) s₂) (subTm-cong h n)
subTm-cong h (⌜Π⌝ c d)  = cong₂ ⌜Π⌝ (subTm-cong h c) (subTm-cong (extS-cong h) d)
subTm-cong h (⌜Σ⌝ c d)  = cong₂ ⌜Σ⌝ (subTm-cong h c) (subTm-cong (extS-cong h) d)
subTm-cong h (⌜Hom⌝ c a b) =
  ⌜Hom⌝-cong₃ (subTm-cong h c) (subTm-cong h a) (subTm-cong h b)
subTm-cong h (⌜Id⌝ c a b) =
  ⌜Id⌝-cong₃ (subTm-cong h c) (subTm-cong h a) (subTm-cong h b)
subTm-cong h (hrefl c t)   = cong₂ hrefl (subTm-cong h c) (subTm-cong h t)
subTm-cong h (idrefl c t)   = cong₂ idrefl (subTm-cong h c) (subTm-cong h t)
subTm-cong h (tr d p e)    =
  tr-cong₃ (subTm-cong (extS-cong h) d) (subTm-cong h p) (subTm-cong h e)
subTm-cong h (jsub d p e)    =
  jsub-cong₃ (subTm-cong (extS-cong h) d) (subTm-cong h p) (subTm-cong h e)
subTm-cong h (ap c b p)    =
  ap-cong₃ (subTm-cong h c) (subTm-cong (extS-cong h) b) (subTm-cong h p)

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
renTy-renTy Unit     = refl
renTy-renTy Nat      = refl
renTy-renTy U        = refl
renTy-renTy {ρ' = ρ'} {ρ} (Π A B) =
  cong₂ Π (renTy-renTy A) (trans (renTy-renTy B) (renTy-cong (extr-extr ρ' ρ) B))
renTy-renTy {ρ' = ρ'} {ρ} (Σ' A B) =
  cong₂ Σ' (renTy-renTy A) (trans (renTy-renTy B) (renTy-cong (extr-extr ρ' ρ) B))
renTy-renTy (El t)   = cong El (renTm-renTm t)
renTy-renTy (Hom A t u) =
  Hom-cong₃ (renTy-renTy A) (renTm-renTm t) (renTm-renTm u)
renTy-renTy (Id A t u) =
  Id-cong₃ (renTy-renTy A) (renTm-renTm t) (renTm-renTm u)
renTy-renTy {ρ' = ρ'} {ρ} (IMu I D i) =
  cong₃ IMu (renTm-renTm I) (renTm-renTm D) (renTm-renTm i)
renTy-renTy {ρ' = ρ'} {ρ} (Desc I) =
  cong Desc (renTm-renTm I)
renTy-renTy {ρ' = ρ'} {ρ} (DIh D M C p) =
  cong₄ DIh (renTm-renTm D) (trans (renTy-renTy M) (renTy-cong (λ x → trans (extr-extr (extR ρ') (extR ρ) x) (extR-cong (extr-extr ρ' ρ) x)) M)) (renTm-renTm C) (renTm-renTm p)
renTy-renTy {ρ' = ρ'} {ρ} (Fin n) =
  refl
renTm-renTm (var x)   = refl
renTm-renTm {ρ' = ρ'} {ρ} (lam t) =
  cong lam (trans (renTm-renTm t) (renTm-cong (extr-extr ρ' ρ) t))
renTm-renTm (app t u)  = cong₂ app (renTm-renTm t) (renTm-renTm u)
renTm-renTm (pair a b) = cong₂ pair (renTm-renTm a) (renTm-renTm b)
renTm-renTm (absurd c e)    = cong₂ absurd (renTm-renTm c) (renTm-renTm e)
renTm-renTm (ordtr a t u p q)    = ordtr-cong₅ (renTm-renTm a) (renTm-renTm t) (renTm-renTm u) (renTm-renTm p) (renTm-renTm q)
renTm-renTm (fst p)    = cong fst (renTm-renTm p)
renTm-renTm (snd p)    = cong snd (renTm-renTm p)
renTm-renTm ⌜base⌝     = refl
renTm-renTm ⌜Nat⌝      = refl
renTm-renTm {ρ' = ρ'} {ρ} (⌜IMu⌝ I D i) =
  cong₃ ⌜IMu⌝ (renTm-renTm I) (renTm-renTm D) (renTm-renTm i)
renTm-renTm {ρ' = ρ'} {ρ} (⌜Fin⌝ n) =
  refl
renTm-renTm {ρ' = ρ'} {ρ} (con p) =
  cong con (renTm-renTm p)
renTm-renTm {ρ' = ρ'} {ρ} (ielim D i e t) =
  cong₄ ielim (renTm-renTm D) (renTm-renTm i) (renTm-renTm e) (renTm-renTm t)
renTm-renTm {ρ' = ρ'} {ρ} (dι j) =
  cong dι (renTm-renTm j)
renTm-renTm {ρ' = ρ'} {ρ} (dσ S f) =
  cong₂ dσ (renTm-renTm S) (renTm-renTm f)
renTm-renTm {ρ' = ρ'} {ρ} (dρ j C) =
  cong₂ dρ (renTm-renTm j) (renTm-renTm C)
renTm-renTm {ρ' = ρ'} {ρ} (dpay I D C i) =
  cong₄ dpay (renTm-renTm I) (renTm-renTm D) (renTm-renTm C) (renTm-renTm i)
renTm-renTm {ρ' = ρ'} {ρ} (dih D e C p) =
  cong₄ dih (renTm-renTm D) (renTm-renTm e) (renTm-renTm C) (renTm-renTm p)
renTm-renTm {ρ' = ρ'} {ρ} fzero =
  refl
renTm-renTm {ρ' = ρ'} {ρ} (fsuc t) =
  cong fsuc (renTm-renTm t)
renTm-renTm {ρ' = ρ'} {ρ} (fcase t a b) =
  cong₃ fcase (renTm-renTm t) (renTm-renTm a) (trans (renTm-renTm b) (renTm-cong (extr-extr ρ' ρ) b))
renTm-renTm {ρ' = ρ'} {ρ} (fcase0 t) =
  cong fcase0 (renTm-renTm t)
renTm-renTm {ρ' = ρ'} {ρ} (psplit b q) =
  cong₂ psplit (trans (renTm-renTm b) (renTm-cong (λ x → trans (extr-extr (extR ρ') (extR ρ) x) (extR-cong (extr-extr ρ' ρ) x)) b)) (renTm-renTm q)
renTm-renTm ⌜Unit⌝     = refl
renTm-renTm unit       = refl
renTm-renTm nzero      = refl
renTm-renTm (nsuc n)   = cong nsuc (renTm-renTm n)
renTm-renTm {ρ' = ρ'} {ρ} (natrec z s n) =
  natrec-cong₃ (renTm-renTm z)
    (trans (renTm-renTm s)
           (renTm-cong (λ x → trans (extr-extr (extR ρ') (extR ρ) x) (extR-cong (extr-extr ρ' ρ) x)) s))
    (renTm-renTm n)
renTm-renTm {ρ' = ρ'} {ρ} (⌜Π⌝ c d) =
  cong₂ ⌜Π⌝ (renTm-renTm c) (trans (renTm-renTm d) (renTm-cong (extr-extr ρ' ρ) d))
renTm-renTm {ρ' = ρ'} {ρ} (⌜Σ⌝ c d) =
  cong₂ ⌜Σ⌝ (renTm-renTm c) (trans (renTm-renTm d) (renTm-cong (extr-extr ρ' ρ) d))
renTm-renTm (⌜Hom⌝ c a b) =
  ⌜Hom⌝-cong₃ (renTm-renTm c) (renTm-renTm a) (renTm-renTm b)
renTm-renTm (⌜Id⌝ c a b) =
  ⌜Id⌝-cong₃ (renTm-renTm c) (renTm-renTm a) (renTm-renTm b)
renTm-renTm (hrefl c t)   = cong₂ hrefl (renTm-renTm c) (renTm-renTm t)
renTm-renTm (idrefl c t)   = cong₂ idrefl (renTm-renTm c) (renTm-renTm t)
renTm-renTm {ρ' = ρ'} {ρ} (tr d p e) =
  tr-cong₃ (trans (renTm-renTm d) (renTm-cong (extr-extr ρ' ρ) d))
           (renTm-renTm p) (renTm-renTm e)
renTm-renTm {ρ' = ρ'} {ρ} (jsub d p e) =
  jsub-cong₃ (trans (renTm-renTm d) (renTm-cong (extr-extr ρ' ρ) d))
           (renTm-renTm p) (renTm-renTm e)
renTm-renTm {ρ' = ρ'} {ρ} (ap c b p) =
  ap-cong₃ (renTm-renTm c)
           (trans (renTm-renTm b) (renTm-cong (extr-extr ρ' ρ) b))
           (renTm-renTm p)

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
subTy-renTy Unit     = refl
subTy-renTy Nat      = refl
subTy-renTy U        = refl
subTy-renTy {σ = σ} {ρ} (Π A B) =
  cong₂ Π (subTy-renTy A) (trans (subTy-renTy B) (subTy-cong (exts-extr σ ρ) B))
subTy-renTy {σ = σ} {ρ} (Σ' A B) =
  cong₂ Σ' (subTy-renTy A) (trans (subTy-renTy B) (subTy-cong (exts-extr σ ρ) B))
subTy-renTy (El t)   = cong El (subTm-renTm t)
subTy-renTy (Hom A t u) =
  Hom-cong₃ (subTy-renTy A) (subTm-renTm t) (subTm-renTm u)
subTy-renTy (Id A t u) =
  Id-cong₃ (subTy-renTy A) (subTm-renTm t) (subTm-renTm u)
subTy-renTy {σ = σ} {ρ} (IMu I D i) =
  cong₃ IMu (subTm-renTm I) (subTm-renTm D) (subTm-renTm i)
subTy-renTy {σ = σ} {ρ} (Desc I) =
  cong Desc (subTm-renTm I)
subTy-renTy {σ = σ} {ρ} (DIh D M C p) =
  cong₄ DIh (subTm-renTm D) (trans (subTy-renTy M) (subTy-cong (λ x → trans (exts-extr (extS σ) (extR ρ) x) (extS-cong (exts-extr σ ρ) x)) M)) (subTm-renTm C) (subTm-renTm p)
subTy-renTy {σ = σ} {ρ} (Fin n) =
  refl
subTm-renTm (var x)   = refl
subTm-renTm {σ = σ} {ρ} (lam t) =
  cong lam (trans (subTm-renTm t) (subTm-cong (exts-extr σ ρ) t))
subTm-renTm (app t u)  = cong₂ app (subTm-renTm t) (subTm-renTm u)
subTm-renTm (pair a b) = cong₂ pair (subTm-renTm a) (subTm-renTm b)
subTm-renTm (absurd c e)    = cong₂ absurd (subTm-renTm c) (subTm-renTm e)
subTm-renTm (ordtr a t u p q)    = ordtr-cong₅ (subTm-renTm a) (subTm-renTm t) (subTm-renTm u) (subTm-renTm p) (subTm-renTm q)
subTm-renTm (fst p)    = cong fst (subTm-renTm p)
subTm-renTm (snd p)    = cong snd (subTm-renTm p)
subTm-renTm ⌜base⌝     = refl
subTm-renTm ⌜Nat⌝      = refl
subTm-renTm {σ = σ} {ρ} (⌜IMu⌝ I D i) =
  cong₃ ⌜IMu⌝ (subTm-renTm I) (subTm-renTm D) (subTm-renTm i)
subTm-renTm {σ = σ} {ρ} (⌜Fin⌝ n) =
  refl
subTm-renTm {σ = σ} {ρ} (con p) =
  cong con (subTm-renTm p)
subTm-renTm {σ = σ} {ρ} (ielim D i e t) =
  cong₄ ielim (subTm-renTm D) (subTm-renTm i) (subTm-renTm e) (subTm-renTm t)
subTm-renTm {σ = σ} {ρ} (dι j) =
  cong dι (subTm-renTm j)
subTm-renTm {σ = σ} {ρ} (dσ S f) =
  cong₂ dσ (subTm-renTm S) (subTm-renTm f)
subTm-renTm {σ = σ} {ρ} (dρ j C) =
  cong₂ dρ (subTm-renTm j) (subTm-renTm C)
subTm-renTm {σ = σ} {ρ} (dpay I D C i) =
  cong₄ dpay (subTm-renTm I) (subTm-renTm D) (subTm-renTm C) (subTm-renTm i)
subTm-renTm {σ = σ} {ρ} (dih D e C p) =
  cong₄ dih (subTm-renTm D) (subTm-renTm e) (subTm-renTm C) (subTm-renTm p)
subTm-renTm {σ = σ} {ρ} fzero =
  refl
subTm-renTm {σ = σ} {ρ} (fsuc t) =
  cong fsuc (subTm-renTm t)
subTm-renTm {σ = σ} {ρ} (fcase t a b) =
  cong₃ fcase (subTm-renTm t) (subTm-renTm a) (trans (subTm-renTm b) (subTm-cong (exts-extr σ ρ) b))
subTm-renTm {σ = σ} {ρ} (fcase0 t) =
  cong fcase0 (subTm-renTm t)
subTm-renTm {σ = σ} {ρ} (psplit b q) =
  cong₂ psplit (trans (subTm-renTm b) (subTm-cong (λ x → trans (exts-extr (extS σ) (extR ρ) x) (extS-cong (exts-extr σ ρ) x)) b)) (subTm-renTm q)
subTm-renTm ⌜Unit⌝     = refl
subTm-renTm unit       = refl
subTm-renTm nzero      = refl
subTm-renTm (nsuc n)   = cong nsuc (subTm-renTm n)
subTm-renTm {σ = σ} {ρ} (natrec z s n) =
  natrec-cong₃ (subTm-renTm z)
    (trans (subTm-renTm s)
           (subTm-cong (λ x → trans (exts-extr (extS σ) (extR ρ) x) (extS-cong (exts-extr σ ρ) x)) s))
    (subTm-renTm n)
subTm-renTm {σ = σ} {ρ} (⌜Π⌝ c d) =
  cong₂ ⌜Π⌝ (subTm-renTm c) (trans (subTm-renTm d) (subTm-cong (exts-extr σ ρ) d))
subTm-renTm {σ = σ} {ρ} (⌜Σ⌝ c d) =
  cong₂ ⌜Σ⌝ (subTm-renTm c) (trans (subTm-renTm d) (subTm-cong (exts-extr σ ρ) d))
subTm-renTm (⌜Hom⌝ c a b) =
  ⌜Hom⌝-cong₃ (subTm-renTm c) (subTm-renTm a) (subTm-renTm b)
subTm-renTm (⌜Id⌝ c a b) =
  ⌜Id⌝-cong₃ (subTm-renTm c) (subTm-renTm a) (subTm-renTm b)
subTm-renTm (hrefl c t)   = cong₂ hrefl (subTm-renTm c) (subTm-renTm t)
subTm-renTm (idrefl c t)   = cong₂ idrefl (subTm-renTm c) (subTm-renTm t)
subTm-renTm {σ = σ} {ρ} (tr d p e) =
  tr-cong₃ (trans (subTm-renTm d) (subTm-cong (exts-extr σ ρ) d))
           (subTm-renTm p) (subTm-renTm e)
subTm-renTm {σ = σ} {ρ} (jsub d p e) =
  jsub-cong₃ (trans (subTm-renTm d) (subTm-cong (exts-extr σ ρ) d))
           (subTm-renTm p) (subTm-renTm e)
subTm-renTm {σ = σ} {ρ} (ap c b p) =
  ap-cong₃ (subTm-renTm c)
           (trans (subTm-renTm b) (subTm-cong (exts-extr σ ρ) b))
           (subTm-renTm p)

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
renTy-subTy Unit     = refl
renTy-subTy Nat      = refl
renTy-subTy U        = refl
renTy-subTy {ρ = ρ} {σ} (Π A B) =
  cong₂ Π (renTy-subTy A) (trans (renTy-subTy B) (subTy-cong (extr-exts ρ σ) B))
renTy-subTy {ρ = ρ} {σ} (Σ' A B) =
  cong₂ Σ' (renTy-subTy A) (trans (renTy-subTy B) (subTy-cong (extr-exts ρ σ) B))
renTy-subTy (El t)   = cong El (renTm-subTm t)
renTy-subTy (Hom A t u) =
  Hom-cong₃ (renTy-subTy A) (renTm-subTm t) (renTm-subTm u)
renTy-subTy (Id A t u) =
  Id-cong₃ (renTy-subTy A) (renTm-subTm t) (renTm-subTm u)
renTy-subTy {ρ = ρ} {σ} (IMu I D i) =
  cong₃ IMu (renTm-subTm I) (renTm-subTm D) (renTm-subTm i)
renTy-subTy {ρ = ρ} {σ} (Desc I) =
  cong Desc (renTm-subTm I)
renTy-subTy {ρ = ρ} {σ} (DIh D M C p) =
  cong₄ DIh (renTm-subTm D) (trans (renTy-subTy M) (subTy-cong (λ x → trans (extr-exts (extR ρ) (extS σ) x) (extS-cong (extr-exts ρ σ) x)) M)) (renTm-subTm C) (renTm-subTm p)
renTy-subTy {ρ = ρ} {σ} (Fin n) =
  refl
renTm-subTm (var x)   = refl
renTm-subTm {ρ = ρ} {σ} (lam t) =
  cong lam (trans (renTm-subTm t) (subTm-cong (extr-exts ρ σ) t))
renTm-subTm (app t u)  = cong₂ app (renTm-subTm t) (renTm-subTm u)
renTm-subTm (pair a b) = cong₂ pair (renTm-subTm a) (renTm-subTm b)
renTm-subTm (absurd c e) = cong₂ absurd (renTm-subTm c) (renTm-subTm e)
renTm-subTm (ordtr a t u p q) = ordtr-cong₅ (renTm-subTm a) (renTm-subTm t) (renTm-subTm u) (renTm-subTm p) (renTm-subTm q)
renTm-subTm (fst p)    = cong fst (renTm-subTm p)
renTm-subTm (snd p)    = cong snd (renTm-subTm p)
renTm-subTm ⌜base⌝     = refl
renTm-subTm ⌜Nat⌝      = refl
renTm-subTm {ρ = ρ} {σ} (⌜IMu⌝ I D i) =
  cong₃ ⌜IMu⌝ (renTm-subTm I) (renTm-subTm D) (renTm-subTm i)
renTm-subTm {ρ = ρ} {σ} (⌜Fin⌝ n) =
  refl
renTm-subTm {ρ = ρ} {σ} (con p) =
  cong con (renTm-subTm p)
renTm-subTm {ρ = ρ} {σ} (ielim D i e t) =
  cong₄ ielim (renTm-subTm D) (renTm-subTm i) (renTm-subTm e) (renTm-subTm t)
renTm-subTm {ρ = ρ} {σ} (dι j) =
  cong dι (renTm-subTm j)
renTm-subTm {ρ = ρ} {σ} (dσ S f) =
  cong₂ dσ (renTm-subTm S) (renTm-subTm f)
renTm-subTm {ρ = ρ} {σ} (dρ j C) =
  cong₂ dρ (renTm-subTm j) (renTm-subTm C)
renTm-subTm {ρ = ρ} {σ} (dpay I D C i) =
  cong₄ dpay (renTm-subTm I) (renTm-subTm D) (renTm-subTm C) (renTm-subTm i)
renTm-subTm {ρ = ρ} {σ} (dih D e C p) =
  cong₄ dih (renTm-subTm D) (renTm-subTm e) (renTm-subTm C) (renTm-subTm p)
renTm-subTm {ρ = ρ} {σ} fzero =
  refl
renTm-subTm {ρ = ρ} {σ} (fsuc t) =
  cong fsuc (renTm-subTm t)
renTm-subTm {ρ = ρ} {σ} (fcase t a b) =
  cong₃ fcase (renTm-subTm t) (renTm-subTm a) (trans (renTm-subTm b) (subTm-cong (extr-exts ρ σ) b))
renTm-subTm {ρ = ρ} {σ} (fcase0 t) =
  cong fcase0 (renTm-subTm t)
renTm-subTm {ρ = ρ} {σ} (psplit b q) =
  cong₂ psplit (trans (renTm-subTm b) (subTm-cong (λ x → trans (extr-exts (extR ρ) (extS σ) x) (extS-cong (extr-exts ρ σ) x)) b)) (renTm-subTm q)
renTm-subTm ⌜Unit⌝     = refl
renTm-subTm unit       = refl
renTm-subTm nzero      = refl
renTm-subTm (nsuc n)   = cong nsuc (renTm-subTm n)
renTm-subTm {ρ = ρ} {σ} (natrec z s n) =
  natrec-cong₃ (renTm-subTm z)
    (trans (renTm-subTm s)
           (subTm-cong (λ x → trans (extr-exts (extR ρ) (extS σ) x) (extS-cong (extr-exts ρ σ) x)) s))
    (renTm-subTm n)
renTm-subTm {ρ = ρ} {σ} (⌜Π⌝ c d) =
  cong₂ ⌜Π⌝ (renTm-subTm c) (trans (renTm-subTm d) (subTm-cong (extr-exts ρ σ) d))
renTm-subTm {ρ = ρ} {σ} (⌜Σ⌝ c d) =
  cong₂ ⌜Σ⌝ (renTm-subTm c) (trans (renTm-subTm d) (subTm-cong (extr-exts ρ σ) d))
renTm-subTm (⌜Hom⌝ c a b) =
  ⌜Hom⌝-cong₃ (renTm-subTm c) (renTm-subTm a) (renTm-subTm b)
renTm-subTm (⌜Id⌝ c a b) =
  ⌜Id⌝-cong₃ (renTm-subTm c) (renTm-subTm a) (renTm-subTm b)
renTm-subTm (hrefl c t)   = cong₂ hrefl (renTm-subTm c) (renTm-subTm t)
renTm-subTm (idrefl c t)   = cong₂ idrefl (renTm-subTm c) (renTm-subTm t)
renTm-subTm {ρ = ρ} {σ} (tr d p e) =
  tr-cong₃ (trans (renTm-subTm d) (subTm-cong (extr-exts ρ σ) d))
           (renTm-subTm p) (renTm-subTm e)
renTm-subTm {ρ = ρ} {σ} (jsub d p e) =
  jsub-cong₃ (trans (renTm-subTm d) (subTm-cong (extr-exts ρ σ) d))
           (renTm-subTm p) (renTm-subTm e)
renTm-subTm {ρ = ρ} {σ} (ap c b p) =
  ap-cong₃ (renTm-subTm c)
           (trans (renTm-subTm b) (subTm-cong (extr-exts ρ σ) b))
           (renTm-subTm p)

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
subTy-subTy Unit     = refl
subTy-subTy Nat      = refl
subTy-subTy U        = refl
subTy-subTy {τ = τ} {σ} (Π A B) =
  cong₂ Π (subTy-subTy A) (trans (subTy-subTy B) (subTy-cong (exts-exts τ σ) B))
subTy-subTy {τ = τ} {σ} (Σ' A B) =
  cong₂ Σ' (subTy-subTy A) (trans (subTy-subTy B) (subTy-cong (exts-exts τ σ) B))
subTy-subTy (El t)   = cong El (subTm-subTm t)
subTy-subTy (Hom A t u) =
  Hom-cong₃ (subTy-subTy A) (subTm-subTm t) (subTm-subTm u)
subTy-subTy (Id A t u) =
  Id-cong₃ (subTy-subTy A) (subTm-subTm t) (subTm-subTm u)
subTy-subTy {τ = τ} {σ} (IMu I D i) =
  cong₃ IMu (subTm-subTm I) (subTm-subTm D) (subTm-subTm i)
subTy-subTy {τ = τ} {σ} (Desc I) =
  cong Desc (subTm-subTm I)
subTy-subTy {τ = τ} {σ} (DIh D M C p) =
  cong₄ DIh (subTm-subTm D) (trans (subTy-subTy M) (subTy-cong (λ x → trans (exts-exts (extS τ) (extS σ) x) (extS-cong (exts-exts τ σ) x)) M)) (subTm-subTm C) (subTm-subTm p)
subTy-subTy {τ = τ} {σ} (Fin n) =
  refl
subTm-subTm (var x)   = refl
subTm-subTm {τ = τ} {σ} (lam t) =
  cong lam (trans (subTm-subTm t) (subTm-cong (exts-exts τ σ) t))
subTm-subTm (app t u)  = cong₂ app (subTm-subTm t) (subTm-subTm u)
subTm-subTm (pair a b) = cong₂ pair (subTm-subTm a) (subTm-subTm b)
subTm-subTm (absurd c e)    = cong₂ absurd (subTm-subTm c) (subTm-subTm e)
subTm-subTm (ordtr a t u p q)    = ordtr-cong₅ (subTm-subTm a) (subTm-subTm t) (subTm-subTm u) (subTm-subTm p) (subTm-subTm q)
subTm-subTm (fst p)    = cong fst (subTm-subTm p)
subTm-subTm (snd p)    = cong snd (subTm-subTm p)
subTm-subTm ⌜base⌝     = refl
subTm-subTm ⌜Nat⌝      = refl
subTm-subTm {τ = τ} {σ} (⌜IMu⌝ I D i) =
  cong₃ ⌜IMu⌝ (subTm-subTm I) (subTm-subTm D) (subTm-subTm i)
subTm-subTm {τ = τ} {σ} (⌜Fin⌝ n) =
  refl
subTm-subTm {τ = τ} {σ} (con p) =
  cong con (subTm-subTm p)
subTm-subTm {τ = τ} {σ} (ielim D i e t) =
  cong₄ ielim (subTm-subTm D) (subTm-subTm i) (subTm-subTm e) (subTm-subTm t)
subTm-subTm {τ = τ} {σ} (dι j) =
  cong dι (subTm-subTm j)
subTm-subTm {τ = τ} {σ} (dσ S f) =
  cong₂ dσ (subTm-subTm S) (subTm-subTm f)
subTm-subTm {τ = τ} {σ} (dρ j C) =
  cong₂ dρ (subTm-subTm j) (subTm-subTm C)
subTm-subTm {τ = τ} {σ} (dpay I D C i) =
  cong₄ dpay (subTm-subTm I) (subTm-subTm D) (subTm-subTm C) (subTm-subTm i)
subTm-subTm {τ = τ} {σ} (dih D e C p) =
  cong₄ dih (subTm-subTm D) (subTm-subTm e) (subTm-subTm C) (subTm-subTm p)
subTm-subTm {τ = τ} {σ} fzero =
  refl
subTm-subTm {τ = τ} {σ} (fsuc t) =
  cong fsuc (subTm-subTm t)
subTm-subTm {τ = τ} {σ} (fcase t a b) =
  cong₃ fcase (subTm-subTm t) (subTm-subTm a) (trans (subTm-subTm b) (subTm-cong (exts-exts τ σ) b))
subTm-subTm {τ = τ} {σ} (fcase0 t) =
  cong fcase0 (subTm-subTm t)
subTm-subTm {τ = τ} {σ} (psplit b q) =
  cong₂ psplit (trans (subTm-subTm b) (subTm-cong (λ x → trans (exts-exts (extS τ) (extS σ) x) (extS-cong (exts-exts τ σ) x)) b)) (subTm-subTm q)
subTm-subTm ⌜Unit⌝     = refl
subTm-subTm unit       = refl
subTm-subTm nzero      = refl
subTm-subTm (nsuc n)   = cong nsuc (subTm-subTm n)
subTm-subTm {τ = τ} {σ} (natrec z s n) =
  natrec-cong₃ (subTm-subTm z)
    (trans (subTm-subTm s)
           (subTm-cong (λ x → trans (exts-exts (extS τ) (extS σ) x) (extS-cong (exts-exts τ σ) x)) s))
    (subTm-subTm n)
subTm-subTm {τ = τ} {σ} (⌜Π⌝ c d) =
  cong₂ ⌜Π⌝ (subTm-subTm c) (trans (subTm-subTm d) (subTm-cong (exts-exts τ σ) d))
subTm-subTm {τ = τ} {σ} (⌜Σ⌝ c d) =
  cong₂ ⌜Σ⌝ (subTm-subTm c) (trans (subTm-subTm d) (subTm-cong (exts-exts τ σ) d))
subTm-subTm (⌜Hom⌝ c a b) =
  ⌜Hom⌝-cong₃ (subTm-subTm c) (subTm-subTm a) (subTm-subTm b)
subTm-subTm (⌜Id⌝ c a b) =
  ⌜Id⌝-cong₃ (subTm-subTm c) (subTm-subTm a) (subTm-subTm b)
subTm-subTm (hrefl c t)   = cong₂ hrefl (subTm-subTm c) (subTm-subTm t)
subTm-subTm (idrefl c t)   = cong₂ idrefl (subTm-subTm c) (subTm-subTm t)
subTm-subTm {τ = τ} {σ} (tr d p e) =
  tr-cong₃ (trans (subTm-subTm d) (subTm-cong (exts-exts τ σ) d))
           (subTm-subTm p) (subTm-subTm e)
subTm-subTm {τ = τ} {σ} (jsub d p e) =
  jsub-cong₃ (trans (subTm-subTm d) (subTm-cong (exts-exts τ σ) d))
           (subTm-subTm p) (subTm-subTm e)
subTm-subTm {τ = τ} {σ} (ap c b p) =
  ap-cong₃ (subTm-subTm c)
           (trans (subTm-subTm b) (subTm-cong (exts-exts τ σ) b))
           (subTm-subTm p)

-- Identity: `exts` preserves `idₛ`, hence `subTy idₛ = id`.
exts-id : (x : Var (Γ ∙)) → extS idₛ x ≡ idₛ x
exts-id vz     = refl
exts-id (vs x) = refl

subTy-id : (A : RTy Γ) → subTy idₛ A ≡ A
subTm-id : (t : RTm Γ) → subTm idₛ t ≡ t
subTy-id base     = refl
subTy-id Unit     = refl
subTy-id Nat      = refl
subTy-id U        = refl
subTy-id (Π A B)  = cong₂ Π (subTy-id A) (trans (subTy-cong exts-id B) (subTy-id B))
subTy-id (Σ' A B) = cong₂ Σ' (subTy-id A) (trans (subTy-cong exts-id B) (subTy-id B))
subTy-id (El t)   = cong El (subTm-id t)
subTy-id (Hom A t u) = Hom-cong₃ (subTy-id A) (subTm-id t) (subTm-id u)
subTy-id (Id A t u) = Id-cong₃ (subTy-id A) (subTm-id t) (subTm-id u)
subTy-id (IMu I D i) =
  cong₃ IMu (subTm-id I) (subTm-id D) (subTm-id i)
subTy-id (Desc I) =
  cong Desc (subTm-id I)
subTy-id (DIh D M C p) =
  cong₄ DIh (subTm-id D) (trans (subTy-cong (λ x → trans (extS-cong exts-id x) (exts-id x)) M) (subTy-id M)) (subTm-id C) (subTm-id p)
subTy-id (Fin n) =
  refl
subTm-id (var x)   = refl
subTm-id (lam t)   = cong lam (trans (subTm-cong exts-id t) (subTm-id t))
subTm-id (app t u)  = cong₂ app (subTm-id t) (subTm-id u)
subTm-id (pair a b) = cong₂ pair (subTm-id a) (subTm-id b)
subTm-id (absurd c e)    = cong₂ absurd (subTm-id c) (subTm-id e)
subTm-id (ordtr a t u p q)    = ordtr-cong₅ (subTm-id a) (subTm-id t) (subTm-id u) (subTm-id p) (subTm-id q)
subTm-id (fst p)    = cong fst (subTm-id p)
subTm-id (snd p)    = cong snd (subTm-id p)
subTm-id ⌜base⌝     = refl
subTm-id ⌜Nat⌝      = refl
subTm-id (⌜IMu⌝ I D i) =
  cong₃ ⌜IMu⌝ (subTm-id I) (subTm-id D) (subTm-id i)
subTm-id (⌜Fin⌝ n) =
  refl
subTm-id (con p) =
  cong con (subTm-id p)
subTm-id (ielim D i e t) =
  cong₄ ielim (subTm-id D) (subTm-id i) (subTm-id e) (subTm-id t)
subTm-id (dι j) =
  cong dι (subTm-id j)
subTm-id (dσ S f) =
  cong₂ dσ (subTm-id S) (subTm-id f)
subTm-id (dρ j C) =
  cong₂ dρ (subTm-id j) (subTm-id C)
subTm-id (dpay I D C i) =
  cong₄ dpay (subTm-id I) (subTm-id D) (subTm-id C) (subTm-id i)
subTm-id (dih D e C p) =
  cong₄ dih (subTm-id D) (subTm-id e) (subTm-id C) (subTm-id p)
subTm-id fzero =
  refl
subTm-id (fsuc t) =
  cong fsuc (subTm-id t)
subTm-id (fcase t a b) =
  cong₃ fcase (subTm-id t) (subTm-id a) (trans (subTm-cong exts-id b) (subTm-id b))
subTm-id (fcase0 t) =
  cong fcase0 (subTm-id t)
subTm-id (psplit b q) =
  cong₂ psplit (trans (subTm-cong (λ x → trans (extS-cong exts-id x) (exts-id x)) b) (subTm-id b)) (subTm-id q)
subTm-id ⌜Unit⌝     = refl
subTm-id unit       = refl
subTm-id nzero      = refl
subTm-id (nsuc n)   = cong nsuc (subTm-id n)
subTm-id (natrec z s n) =
  natrec-cong₃ (subTm-id z)
    (trans (subTm-cong (λ x → trans (extS-cong exts-id x) (exts-id x)) s)
           (subTm-id s))
    (subTm-id n)
subTm-id (⌜Π⌝ c d)  = cong₂ ⌜Π⌝ (subTm-id c) (trans (subTm-cong exts-id d) (subTm-id d))
subTm-id (⌜Σ⌝ c d)  = cong₂ ⌜Σ⌝ (subTm-id c) (trans (subTm-cong exts-id d) (subTm-id d))
subTm-id (⌜Hom⌝ c a b) = ⌜Hom⌝-cong₃ (subTm-id c) (subTm-id a) (subTm-id b)
subTm-id (⌜Id⌝ c a b) = ⌜Id⌝-cong₃ (subTm-id c) (subTm-id a) (subTm-id b)
subTm-id (hrefl c t)   = cong₂ hrefl (subTm-id c) (subTm-id t)
subTm-id (idrefl c t)   = cong₂ idrefl (subTm-id c) (subTm-id t)
subTm-id (tr d p e)    =
  tr-cong₃ (trans (subTm-cong exts-id d) (subTm-id d)) (subTm-id p) (subTm-id e)
subTm-id (jsub d p e)    =
  jsub-cong₃ (trans (subTm-cong exts-id d) (subTm-id d)) (subTm-id p) (subTm-id e)
subTm-id (ap c b p)    =
  ap-cong₃ (subTm-id c) (trans (subTm-cong exts-id b) (subTm-id b)) (subTm-id p)



------------------------------------------------------------------------
-- ★ closed things weakened into any scope (the unique substitution out of
--   the empty context).
------------------------------------------------------------------------

εsub : Sub ε Γ
εsub ()

εwkTy : RTy ε → RTy Γ
εwkTy = subTy εsub

εwk-ren : (ρ : Ren Γ Δ) (A : RTy ε) → renTy ρ (εwkTy A) ≡ εwkTy A
εwk-ren ρ A = trans (renTy-subTy A) (subTy-cong (λ ()) A)

εwk-sub : (σ : Sub Γ Δ) (A : RTy ε) → subTy σ (εwkTy A) ≡ εwkTy A
εwk-sub σ A = trans (subTy-subTy A) (subTy-cong (λ ()) A)

εwkTm : RTm ε → RTm Γ
εwkTm = subTm εsub

εwkTm-ren : (ρ : Ren Γ Δ) (t : RTm ε) → renTm ρ (εwkTm t) ≡ εwkTm t
εwkTm-ren ρ t = trans (renTm-subTm t) (subTm-cong (λ ()) t)

εwkTm-sub : (σ : Sub Γ Δ) (t : RTm ε) → subTm σ (εwkTm t) ≡ εwkTm t
εwkTm-sub σ t = trans (subTm-subTm t) (subTm-cong (λ ()) t)

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
