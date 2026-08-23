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
-- ★ INDUCTIVE-TYPES AXIS.  ⚠ DESCRIPTIONS ARE CLOSED: `Con` carries field
--   types at `ε`, so a description mentions no ambient variable and
--   `renTy ρ (Mu D) = Mu D` holds ON THE NOSE.  That is what keeps this
--   former from needing a parallel `renDesc`/`subDesc` development with
--   its own naturality tower — the single biggest cost decision here.
--   ⚠ Limitation, recorded: a PARAMETERISED datatype (`List A` for a
--   variable `A`) needs open descriptions and is NOT step 1.
data DCon : Set
data Desc : Set
-- ★★ INDEXED descriptions (2026-08-22).  Added ALONGSIDE the non-indexed
--   pair rather than re-typing `dρ`, so everything already green stays
--   green and the two coexist while the indexed one is brought up.
-- ★★★ THE FIELD TELESCOPE.  `ICx n` is the context a description's
--   carried terms live in: the AMBIENT INDEX, then one binder per field
--   already introduced.  ⚠ It is a `Cx`, NOT the ambient `Γ` — descriptions
--   must stay CLOSED (they appear in types, and `renTy ρ (IMu D I i) =
--   IMu D I (renTm ρ i)` must not have to rename `D`).
-- ⚠ INDEXED BY THE TELESCOPE CONTEXT, not by a field COUNT.  With a count
--   you cannot state well-formedness — `IConWf` must track each field's
--   TYPE, and "a typed context whose erasure is `ICx n`" needs an equality
--   proof threaded everywhere.  Indexed by `Cx` it falls out, because
--   `⌊ Θ ▹ A ⌋ = ⌊ Θ ⌋ ∙` holds ON THE NOSE.
data ICon : Cx → Set
data IDesc : Set

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
  -- ★★ INDUCTIVE TYPES: a datatype, given by its description.
  Mu   : ∀ {Γ} → Desc → RTy Γ
  -- ★★★ INDEXED inductive types: a description AND an index VALUE.
  -- ⚠ Unlike `Mu`, this is NOT stable under renaming on the nose — the
  --   INDEX lives in `Γ`.  The description stays CLOSED (see `ICon`), so
  --   only the index needs naturality, exactly as for `El`.  That keeps
  --   the "no parallel renDesc/subDesc tower" decision at line 67 intact.
  -- ⚠ CARRIES THE INDEX TYPE, as a CLOSED `RTy ε`.  Without it `ty-IMu`
  --   cannot say what the index is an inhabitant OF — `ty-Mu` needs only
  --   the description, but an INDEXED type must type its index.  Exactly
  --   the precedent `dκ : RTy ε → DCon → DCon` sets, and `εwkTy` weakens
  --   it into `Γ` the same way `payTy` already does for a `dκ` field.
  IMu  : ∀ {Γ} → IDesc → RTy ε → RTm Γ → RTy Γ

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
  -- ★★ INDUCTIVE TYPES.
  --   `con k p`      constructor TAG `k` and a PAYLOAD built from
  --                  `unit`/`pair` — the choice lives in the term, which
  --                  is why no coproduct is needed (SpikeDescTm).
  --   `elim D ms t`  the description, a METHOD TUPLE (again nested
  --                  pairs), and the scrutinee.
  con  : ∀ {Γ} → ℕ → RTm Γ → RTm Γ
  elim : ∀ {Γ} → Desc → RTm Γ → RTm Γ → RTm Γ
  -- ★★★ their INDEXED twins.  `icon` carries the tag and payload as `con`
  --   does; `ielim` additionally carries the index it eliminates AT.
  icon  : ∀ {Γ} → ℕ → RTm Γ → RTm Γ
  ielim : ∀ {Γ} → IDesc → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  -- ★ WF-axis stage C (N-in): `Nat` becomes SMALL — it gets a code, so
  -- it can appear in `U`-families.  That is what unlocks Id-rewriting
  -- AT `Nat` (`jsub` needs a code family), cong-at-ℕ, and ≤ as a
  -- transportable relation.
  ⌜Nat⌝  : ∀ {Γ} → RTm Γ
  -- ★★ INDUCTIVE TYPES: the CODE for `Mu`.  Structurally NULLARY — a
  -- `Desc` is closed and contains no terms — so both actions are inert
  -- on it, exactly as for `⌜Nat⌝`/`⌜Unit⌝`.  This is what makes `Mu D`
  -- a SMALL type, and hence what unlocks NESTED datatypes (`dκ` at
  -- `El (⌜Mu⌝ D')`).
  ⌜Mu⌝   : ∀ {Γ} → Desc → RTm Γ
  -- ★ the INDEXED code.  Required so an indexed type can live in `U` and
  --   hence be `amrec`'s carrier — see ⊢⌜IMu⌝ in Spec/Typing.
  ⌜IMu⌝  : ∀ {Γ} → IDesc → RTy ε → RTm Γ → RTm Γ
  ⌜Unit⌝ : ∀ {Γ} → RTm Γ

-- ★ DESCRIPTIONS.  `DCon` is one constructor's field list; `Desc` is the
--   datatype, i.e. the list of its constructors.  ⚠ Both CLOSED — see the
--   note at the forward declarations.
data DCon where
  dι : DCon                  -- no more fields
  dρ : DCon → DCon           -- a RECURSIVE field, then more
  dκ : RTy ε → DCon → DCon   -- a NON-RECURSIVE field of a CLOSED type

data Desc where
  dnil : Desc
  _◃_  : DCon → Desc → Desc

-- ★★★ INDEXED descriptions.  A carried term lives in the FIELD
--   TELESCOPE `ICx n`: `var vz` is the most recent field, and the
--   ambient index is the innermost variable.
--
-- ⚠⚠ WHY A TERM AND NOT AN AGDA FUNCTION.  `IMu` lands in `RTy`, so a
--   FUNCTION FIELD would put Agda functions inside TYPES and decidable
--   equality on `RTy` — hence `Algorithm/DecideConversion` — would be
--   gone.  A first-order `RTm` keeps equality decidable.  Same move
--   `dκ : RTy ε → DCon → DCon` already makes for the field type.
--
-- ⚠⚠ REVISED 2026-08-23 (PLAN-INDEXED §9.2).  These previously carried
--   `RTm ε` applied to the AMBIENT INDEX ONLY.  That could not express
--   this project's own `Vec`: the forded
--       cons : (m : Nat) → A → Vec A m → (n ≡ suc m) → Vec A n
--   recurses at `m`, an EARLIER FIELD, which a closed function of the
--   ambient index cannot name.  Two comments in this very block said
--   opposite things about it and both stayed green — the honest one was
--   the SCOPE note ("does NOT cover Vec … needs σ"), and the `iκ`
--   note claiming Vec was expressible was an overclaim: `iκ` supplies
--   the CONSTRAINT FIELD, which is necessary and not sufficient.
--
-- ★ `iι` targets the AMBIENT index — every constructor is available at
--   every index, which is what keeps the logical relation UNIFORM in the
--   index and never reasoning up to index conversion.  That is why
--   Fording is cheap here and native computed targets are not.
data ICon where
  iι : ∀ {Δ} → ICon Δ
  -- RECURSIVE field, at an index that MAY MENTION EARLIER FIELDS.
  iρ : ∀ {Δ} → RTm Δ → ICon (Δ ∙) → ICon Δ
  -- NON-RECURSIVE field, type `El κ`, `κ` a code that may mention
  --   earlier fields and the ambient index.  A FORDING constraint is
  --   just such a field: `iκ (⌜Id⌝ ⌜Nat⌝ ⟨n⟩ (nsuc ⟨m⟩)) …`.
  iκ : ∀ {Δ} → RTm Δ → ICon (Δ ∙) → ICon Δ

data IDesc where
  inil : IDesc
  -- ★ a constructor starts with NO fields bound, only the ambient index.
  _◂_  : ICon (ε ∙) → IDesc → IDesc

infixr 5 _◂_

infixr 5 _◃_

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
renTy ρ Unit       = Unit
renTy ρ Nat        = Nat
renTy ρ base     = base
renTy ρ U        = U
renTy ρ (Π A B)  = Π (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (Σ' A B) = Σ' (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (El t)   = El (renTm ρ t)
renTy ρ (Hom A t u) = Hom (renTy ρ A) (renTm ρ t) (renTm ρ u)
renTy ρ (Id A t u) = Id (renTy ρ A) (renTm ρ t) (renTm ρ u)
renTy ρ (Mu D) = Mu D
renTy ρ (IMu D I i) = IMu D I (renTm ρ i)
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
renTm ρ (⌜Mu⌝ D)      = ⌜Mu⌝ D
renTm ρ (⌜IMu⌝ D I i) = ⌜IMu⌝ D I (renTm ρ i)
renTm ρ ⌜Unit⌝        = ⌜Unit⌝
renTm ρ unit          = unit
renTm ρ nzero         = nzero
renTm ρ (nsuc n)      = nsuc (renTm ρ n)
renTm ρ (natrec z s n) =
  natrec (renTm ρ z) (renTm (extR (extR ρ)) s) (renTm ρ n)
renTm ρ (con k p) = con k (renTm ρ p)
renTm ρ (elim D ms t) = elim D (renTm ρ ms) (renTm ρ t)
renTm ρ (icon k p) = icon k (renTm ρ p)
renTm ρ (ielim D i ms t) = ielim D (renTm ρ i) (renTm ρ ms) (renTm ρ t)

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
subTy σ (Mu D) = Mu D
subTy σ (IMu D I i) = IMu D I (subTm σ i)
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
subTm σ (⌜Mu⌝ D)      = ⌜Mu⌝ D
subTm σ (⌜IMu⌝ D I i) = ⌜IMu⌝ D I (subTm σ i)
subTm σ ⌜Unit⌝        = ⌜Unit⌝
subTm σ unit          = unit
subTm σ nzero         = nzero
subTm σ (nsuc n)      = nsuc (subTm σ n)
subTm σ (natrec z s n) =
  natrec (subTm σ z) (subTm (extS (extS σ)) s) (subTm σ n)
subTm σ (con k p) = con k (subTm σ p)
subTm σ (elim D ms t) = elim D (subTm σ ms) (subTm σ t)
subTm σ (icon k p) = icon k (subTm σ p)
subTm σ (ielim D i ms t) = ielim D (subTm σ i) (subTm σ ms) (subTm σ t)

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
renTy-cong h (Mu D) = refl
renTy-cong h (IMu D I i) = cong (IMu D I) (renTm-cong h i)
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
renTm-cong h (⌜Mu⌝ D)   = refl
renTm-cong h (⌜IMu⌝ D I i) = cong (⌜IMu⌝ D I) (renTm-cong h i)
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
renTm-cong h (con k p) = cong (con k) (renTm-cong h p)
renTm-cong h (elim D ms t) = cong₂ (elim D) (renTm-cong h ms) (renTm-cong h t)
renTm-cong h (icon k p) = cong (icon k) (renTm-cong h p)
renTm-cong h (ielim D i ms t) =
  cong₃ (ielim D) (renTm-cong h i) (renTm-cong h ms) (renTm-cong h t)

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
subTy-cong h (Mu D) = refl
subTy-cong h (IMu D I i) = cong (IMu D I) (subTm-cong h i)
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
subTm-cong h (⌜Mu⌝ D)   = refl
subTm-cong h (⌜IMu⌝ D I i) = cong (⌜IMu⌝ D I) (subTm-cong h i)
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
subTm-cong h (con k p) = cong (con k) (subTm-cong h p)
subTm-cong h (elim D ms t) = cong₂ (elim D) (subTm-cong h ms) (subTm-cong h t)
subTm-cong h (icon k p) = cong (icon k) (subTm-cong h p)
subTm-cong h (ielim D i ms t) =
  cong₃ (ielim D) (subTm-cong h i) (subTm-cong h ms) (subTm-cong h t)

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
renTy-renTy (Mu D) = refl
renTy-renTy (IMu D I i) = cong (IMu D I) (renTm-renTm i)
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
renTm-renTm (⌜Mu⌝ D)   = refl
renTm-renTm (⌜IMu⌝ D I i) = cong (⌜IMu⌝ D I) (renTm-renTm i)
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
renTm-renTm (con k p) = cong (con k) (renTm-renTm p)
renTm-renTm (elim D ms t) = cong₂ (elim D) (renTm-renTm ms) (renTm-renTm t)
renTm-renTm (icon k p) = cong (icon k) (renTm-renTm p)
renTm-renTm (ielim D i ms t) =
  cong₃ (ielim D) (renTm-renTm i) (renTm-renTm ms) (renTm-renTm t)

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
subTy-renTy (Mu D) = refl
subTy-renTy (IMu D I i) = cong (IMu D I) (subTm-renTm i)
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
subTm-renTm (⌜Mu⌝ D)   = refl
subTm-renTm (⌜IMu⌝ D I i) = cong (⌜IMu⌝ D I) (subTm-renTm i)
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
subTm-renTm (con k p) = cong (con k) (subTm-renTm p)
subTm-renTm (elim D ms t) = cong₂ (elim D) (subTm-renTm ms) (subTm-renTm t)
subTm-renTm (icon k p) = cong (icon k) (subTm-renTm p)
subTm-renTm (ielim D i ms t) =
  cong₃ (ielim D) (subTm-renTm i) (subTm-renTm ms) (subTm-renTm t)

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
renTy-subTy (Mu D) = refl
renTy-subTy (IMu D I i) = cong (IMu D I) (renTm-subTm i)
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
renTm-subTm (⌜Mu⌝ D)   = refl
renTm-subTm (⌜IMu⌝ D I i) = cong (⌜IMu⌝ D I) (renTm-subTm i)
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
renTm-subTm (con k p) = cong (con k) (renTm-subTm p)
renTm-subTm (elim D ms t) = cong₂ (elim D) (renTm-subTm ms) (renTm-subTm t)
renTm-subTm (icon k p) = cong (icon k) (renTm-subTm p)
renTm-subTm (ielim D i ms t) =
  cong₃ (ielim D) (renTm-subTm i) (renTm-subTm ms) (renTm-subTm t)

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
subTy-subTy (Mu D) = refl
subTy-subTy (IMu D I i) = cong (IMu D I) (subTm-subTm i)
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
subTm-subTm (⌜Mu⌝ D)   = refl
subTm-subTm (⌜IMu⌝ D I i) = cong (⌜IMu⌝ D I) (subTm-subTm i)
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
subTm-subTm (con k p) = cong (con k) (subTm-subTm p)
subTm-subTm (elim D ms t) = cong₂ (elim D) (subTm-subTm ms) (subTm-subTm t)
subTm-subTm (icon k p) = cong (icon k) (subTm-subTm p)
subTm-subTm (ielim D i ms t) =
  cong₃ (ielim D) (subTm-subTm i) (subTm-subTm ms) (subTm-subTm t)

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
subTy-id (Mu D) = refl
subTy-id (IMu D I i) = cong (IMu D I) (subTm-id i)
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
subTm-id (⌜Mu⌝ D)   = refl
subTm-id (⌜IMu⌝ D I i) = cong (⌜IMu⌝ D I) (subTm-id i)
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
subTm-id (con k p) = cong (con k) (subTm-id p)
subTm-id (elim D ms t) = cong₂ (elim D) (subTm-id ms) (subTm-id t)
subTm-id (icon k p) = cong (icon k) (subTm-id p)
subTm-id (ielim D i ms t) =
  cong₃ (ielim D) (subTm-id i) (subTm-id ms) (subTm-id t)



------------------------------------------------------------------------
-- ★ THE ι-RULE'S MACHINERY — three TOTAL metalevel functions on raw
--   syntax, and their four naturality lemmas.
--
-- ⚠ ALL THREE ARE TOTAL, deliberately.  `lookupD` returns `dι` off the end
--   of a description and `sel` bottoms out in whatever `snd`-chain it is
--   handed; neither can get stuck.  That is what keeps `_⟶_` a
--   SIDE-CONDITION-FREE relation — the ι-rule needs no `lookup D k ≡ just C`
--   premise, so determinism stays a one-line pattern match and confluence
--   never has to invert a `just`.  Junk tags reduce to junk; ⊢con rules
--   them out, exactly as the rest of this raw syntax is disciplined.
------------------------------------------------------------------------

-- the k-th constructor's field list; `dι` (no fields) off the end
lookupD : Desc → ℕ → DCon
lookupD dnil    _       = dι
lookupD (C ◃ D) zero    = C
lookupD (C ◃ D) (suc k) = lookupD D k

-- the k-th METHOD out of a right-nested tuple `pair m₀ (pair m₁ …)`
sel : ℕ → RTm Γ → RTm Γ
sel zero    ms = fst ms
sel (suc k) ms = sel k (snd ms)

-- ★★ THE IH TUPLE.  One entry per RECURSIVE field; a `dκ` field owes no
--   induction hypothesis and is SKIPPED, not filled with a placeholder —
--   the same accounting `SpikeDescSigma`'s `elimLift` made in the model.
ihs : Desc → RTm Γ → DCon → RTm Γ → RTm Γ
ihs D ms dι       p = unit
ihs D ms (dρ C)   p = pair (elim D ms (fst p)) (ihs D ms C (snd p))
ihs D ms (dκ A C) p = ihs D ms C (snd p)

-- ★★★ APPLY a method to a payload — TUPLED (gate 5c): the method receives
--   the payload WHOLE and the IH tuple beside it.
--
--   ⚠⚠ NOT CURRIED, and that is a decision, not a style.  Curried
--     application hands the method `fst p`/`snd p` and never `p`, so under
--     a DEPENDENT motive its result type can only mention the payload
--     REBUILT from its own binders — `pair (fst p) unit` — which is `p`
--     only up to SURJECTIVE PAIRING.  Gate 5b could not even STATE
--     subject reduction without that η; gate 5c proves it here without.
--
--   ⇒ the η requirement was the SYMPTOM of an information loss, and it
--     would have coupled this axis to the OPEN G4 conversion decision.
--     Passing the payload whole is also the ALGEBRA form: a description
--     denotes a functor, the payload IS the functor application.
fields : Desc → RTm Γ → DCon → RTm Γ → RTm Γ → RTm Γ
fields D ms C m p = app (app m p) (ihs D ms C p)

ren-sel : (ρ : Ren Γ Δ) (k : ℕ) (ms : RTm Γ) →
          renTm ρ (sel k ms) ≡ sel k (renTm ρ ms)
ren-sel ρ zero    ms = refl
ren-sel ρ (suc k) ms = ren-sel ρ k (snd ms)

sub-sel : (σ : Sub Γ Δ) (k : ℕ) (ms : RTm Γ) →
          subTm σ (sel k ms) ≡ sel k (subTm σ ms)
sub-sel σ zero    ms = refl
sub-sel σ (suc k) ms = sub-sel σ k (snd ms)

ren-ihs : (ρ : Ren Γ Δ) (D : Desc) (ms : RTm Γ) (C : DCon) (p : RTm Γ) →
          renTm ρ (ihs D ms C p) ≡ ihs D (renTm ρ ms) C (renTm ρ p)
ren-ihs ρ D ms dι       p = refl
ren-ihs ρ D ms (dρ C)   p = cong₂ pair refl (ren-ihs ρ D ms C (snd p))
ren-ihs ρ D ms (dκ A C) p = ren-ihs ρ D ms C (snd p)

sub-ihs : (σ : Sub Γ Δ) (D : Desc) (ms : RTm Γ) (C : DCon) (p : RTm Γ) →
          subTm σ (ihs D ms C p) ≡ ihs D (subTm σ ms) C (subTm σ p)
sub-ihs σ D ms dι       p = refl
sub-ihs σ D ms (dρ C)   p = cong₂ pair refl (sub-ihs σ D ms C (snd p))
sub-ihs σ D ms (dκ A C) p = sub-ihs σ D ms C (snd p)

ren-fields : (ρ : Ren Γ Δ) (D : Desc) (ms : RTm Γ) (C : DCon) (m p : RTm Γ) →
             renTm ρ (fields D ms C m p)
               ≡ fields D (renTm ρ ms) C (renTm ρ m) (renTm ρ p)
ren-fields ρ D ms C m p = cong (app (app (renTm ρ m) (renTm ρ p)))
                               (ren-ihs ρ D ms C p)

sub-fields : (σ : Sub Γ Δ) (D : Desc) (ms : RTm Γ) (C : DCon) (m p : RTm Γ) →
             subTm σ (fields D ms C m p)
               ≡ fields D (subTm σ ms) C (subTm σ m) (subTm σ p)
sub-fields σ D ms C m p = cong (app (app (subTm σ m) (subTm σ p)))
                               (sub-ihs σ D ms C p)

------------------------------------------------------------------------
-- ★★ THE ELIMINATOR'S COMPUTED TYPES (gate 5c, general in `DCon`).
--
--   payTy   D C      the PAYLOAD's type — a Σ-chain over the field list
--   ihTy    D C q M  the IH TUPLE's type — one entry per `dρ`, NONE per
--                    `dκ` (a non-recursive field owes no hypothesis)
--   atCon   k M      the motive RE-BASED at the payload binder
--   methTy  D k C M  Π (payTy) (Π (ihTy) (wk (atCon k M)))
--
-- ⚠ No new JUDGMENT is needed: `⊢con`/`⊢elim` reuse the existing Π/Σ
--   rules against these.
------------------------------------------------------------------------

-- ★ the unique SUBSTITUTION out of the empty context.  ⚠ defined by
--   `subTy`, not `renTy`, on purpose: both inertness laws below then come
--   from one composition law plus a VACUOUS congruence (`Var ε` is
--   empty), with no ren-versus-sub mismatch to bridge.
εsub : Sub ε Γ
εsub ()

εwkTy : RTy ε → RTy Γ
εwkTy = subTy εsub

εwk-ren : (ρ : Ren Γ Δ) (A : RTy ε) → renTy ρ (εwkTy A) ≡ εwkTy A
εwk-ren ρ A = trans (renTy-subTy A) (subTy-cong (λ ()) A)

εwk-sub : (σ : Sub Γ Δ) (A : RTy ε) → subTy σ (εwkTy A) ≡ εwkTy A
εwk-sub σ A = trans (subTy-subTy A) (subTy-cong (λ ()) A)

-- ★★ the PAYLOAD's type: a Σ-chain over one constructor's field list.
--    Closed, so both actions are inert on it.
payTy : Desc → DCon → RTy Γ
payTy D dι       = Unit
payTy D (dρ C)   = Σ' (Mu D)    (payTy D C)
payTy D (dκ A C) = Σ' (εwkTy A) (payTy D C)

payTy-ren : (ρ : Ren Γ Δ) (D : Desc) (C : DCon) →
            renTy ρ (payTy D C) ≡ payTy D C
payTy-ren ρ D dι       = refl
payTy-ren ρ D (dρ C)   = cong (Σ' (Mu D)) (payTy-ren (extR ρ) D C)
payTy-ren ρ D (dκ A C) = cong₂ Σ' (εwk-ren ρ A) (payTy-ren (extR ρ) D C)

payTy-sub : (σ : Sub Γ Δ) (D : Desc) (C : DCon) →
            subTy σ (payTy D C) ≡ payTy D C
payTy-sub σ D dι       = refl
payTy-sub σ D (dρ C)   = cong (Σ' (Mu D)) (payTy-sub (extS σ) D C)
payTy-sub σ D (dκ A C) = cong₂ Σ' (εwk-sub σ A) (payTy-sub (extS σ) D C)

-- ★★ the TAG INDEXES A REAL CONSTRUCTOR.  ⚠⚠ gate 5's Q21: `lookupD` is
--    TOTAL (it answers `dι` off the end, so `_⟶_` needs no side
--    condition), and `payTy D dι = Unit` — so WITHOUT this premise an
--    out-of-range tag with payload `unit` would be typeable, ι would
--    reduce it to `sel k ms`, and that bottoms out in `fst unit`.
--    SUBJECT REDUCTION WOULD BE FALSE.  Totality relocates the
--    obligation; it does not remove it.
------------------------------------------------------------------------
-- ★★★ THE INDEXED APPARATUS — the twins of everything above.
--
-- ⚠⚠ AND HERE THE "CLOSED DESCRIPTIONS ARE CHEAP" DECISION (line 67) STOPS
--   PAYING. `payTy` is inert under both actions because `Mu D` mentions no
--   ambient variable. `ipayTy` carries the INDEX, which does — so its
--   naturality lemmas are real congruences over a renamed/substituted
--   index, not `refl`. That is the price of indexing, and it is confined
--   to the index: the DESCRIPTION is still closed, so no `renIDesc` tower
--   is needed.
------------------------------------------------------------------------

εwkTm : RTm ε → RTm Γ
εwkTm = subTm εsub

εwkTm-ren : (ρ : Ren Γ Δ) (t : RTm ε) → renTm ρ (εwkTm t) ≡ εwkTm t
εwkTm-ren ρ t = trans (renTm-subTm t) (subTm-cong (λ ()) t)

εwkTm-sub : (σ : Sub Γ Δ) (t : RTm ε) → subTm σ (εwkTm t) ≡ εwkTm t
εwkTm-sub σ t = trans (subTm-subTm t) (subTm-cong (λ ()) t)

ilookupD : IDesc → ℕ → ICon (ε ∙)
ilookupD inil    _       = iι
ilookupD (C ◂ D) zero    = C
ilookupD (C ◂ D) (suc k) = ilookupD D k

-- ★ the PAYLOAD's type at ambient index `i`.  A recursive field sits at
--   the SHIFTED index `f i`, where `f` is the constructor's closed shift.
-- ★ the ENVIRONMENT for a description's telescope: what the ambient
--   index and each already-bound field actually are, in `Γ`.
isingle : RTm Γ → Sub (ε ∙) Γ
isingle i vz      = i
isingle i (vs ())

-- ★ the PAYLOAD's type.  ⚠ REVISED (§9.2): walks the telescope with an
--   environment rather than applying a closed function to the ambient
--   index.  `extS σ : Sub (ICx n ∙) (Γ ∙)` IS `Sub (ICx (suc n)) (Γ ∙)`,
--   so the field just introduced is `var vz` in the tail — which is what
--   lets a later `iρ` name it.
ipayTy : IDesc → RTy ε → ∀ {Δ} → Sub Δ Γ → ICon Δ → RTy Γ
ipayTy D I σ iι       = Unit
ipayTy D I σ (iρ j C) = Σ' (IMu D I (subTm σ j)) (ipayTy D I (extS σ) C)
ipayTy D I σ (iκ κ C) = Σ' (El (subTm σ κ))      (ipayTy D I (extS σ) C)

-- two environments agreeing pointwise give the same payload type.
ipayTy-cong : (D : IDesc) (I : RTy ε) {Δ : Cx} {σ σ' : Sub Δ Γ}
              (C : ICon Δ) → (∀ x → σ x ≡ σ' x) →
              ipayTy D I σ C ≡ ipayTy D I σ' C
ipayTy-cong D I iι       h = refl
ipayTy-cong D I (iρ j C) h =
  cong₂ Σ' (cong (IMu D I) (subTm-cong h j))
           (ipayTy-cong D I C (λ { vz → refl ; (vs x) → cong (renTm vs) (h x) }))
ipayTy-cong D I (iκ κ C) h =
  cong₂ Σ' (cong El (subTm-cong h κ))
           (ipayTy-cong D I C (λ { vz → refl ; (vs x) → cong (renTm vs) (h x) }))

-- naturality.  ⚠ the environment absorbs the action — that is the whole
--   point of carrying one: `renTy ρ (ipayTy D I σ C) ≡ ipayTy D I (ρ ∘ σ) C`,
--   with no per-former index bookkeeping.
ipayTy-ren : (ρ : Ren Γ Δ) (D : IDesc) (I : RTy ε) {Θ : Cx}
             (σ : Sub Θ Γ) (C : ICon Θ) →
             renTy ρ (ipayTy D I σ C) ≡ ipayTy D I (λ x → renTm ρ (σ x)) C
ipayTy-ren ρ D I σ iι = refl
ipayTy-ren ρ D I σ (iρ j C) =
  cong₂ Σ' (cong (IMu D I) (renTm-subTm j))
           (trans (ipayTy-ren (extR ρ) D I (extS σ) C)
                  (ipayTy-cong D I C (λ { vz → refl
                                        ; (vs x) → trans (renTm-renTm (σ x))
                                                         (sym (renTm-renTm (σ x))) })))
ipayTy-ren ρ D I σ (iκ κ C) =
  cong₂ Σ' (cong El (renTm-subTm κ))
           (trans (ipayTy-ren (extR ρ) D I (extS σ) C)
                  (ipayTy-cong D I C (λ { vz → refl
                                        ; (vs x) → trans (renTm-renTm (σ x))
                                                         (sym (renTm-renTm (σ x))) })))

ipayTy-sub : (τ : Sub Γ Δ) (D : IDesc) (I : RTy ε) {Θ : Cx}
             (σ : Sub Θ Γ) (C : ICon Θ) →
             subTy τ (ipayTy D I σ C) ≡ ipayTy D I (λ x → subTm τ (σ x)) C
ipayTy-sub τ D I σ iι = refl
ipayTy-sub τ D I σ (iρ j C) =
  cong₂ Σ' (cong (IMu D I) (subTm-subTm j))
           (trans (ipayTy-sub (extS τ) D I (extS σ) C)
                  (ipayTy-cong D I C (λ { vz → refl
                                        ; (vs x) → trans (subTm-renTm (σ x))
                                                         (sym (renTm-subTm (σ x))) })))
ipayTy-sub τ D I σ (iκ κ C) =
  cong₂ Σ' (cong El (subTm-subTm κ))
           (trans (ipayTy-sub (extS τ) D I (extS σ) C)
                  (ipayTy-cong D I C (λ { vz → refl
                                        ; (vs x) → trans (subTm-renTm (σ x))
                                                         (sym (renTm-subTm (σ x))) })))

data _∈ID_ : ℕ → IDesc → Set where
  hereID  : {C : ICon (ε ∙)} {E : IDesc} → zero ∈ID (C ◂ E)
  thereID : {k : ℕ} {C : ICon (ε ∙)} {E : IDesc} → k ∈ID E → suc k ∈ID (C ◂ E)

-- ★ EXTENDING AN ENVIRONMENT BY A VALUE.  ⚠ this is where the TERM level
--   parts company with the TYPE level: `ipayTy` extends with `extS`,
--   because its tail lives under a `Σ'` BINDER; `iihs` extends with the
--   actual field VALUE, because its tail lives under a `pair`, which
--   binds nothing and stays in `Γ`.
iext : ∀ {Δ} → Sub Δ Γ → RTm Γ → Sub (Δ ∙) Γ
iext σ v vz     = v
iext σ v (vs x) = σ x

-- ★ the INDEXED IH tuple.  Each recursive call is eliminated AT ITS OWN
--   index, read off the environment — the whole content of indexing at
--   the term level.
-- ⚠ NO INDEX TYPE. `I` was threaded here and NEVER USED — the index TYPE
--   is a TYPE-level concern (`IMu`, `ipayTy`, well-formedness); the term
--   level only needs the index VALUE. Found by writing Confluence's
--   parallel-reduction rule `pιi`, whose conclusion would have mentioned
--   an `I` its premise could not determine.
iihs : IDesc → RTm Γ → ∀ {Δ} → Sub Δ Γ → ICon Δ → RTm Γ → RTm Γ
iihs D ms σ iι       p = unit
iihs D ms σ (iρ j C) p =
  pair (ielim D (subTm σ j) ms (fst p))
       (iihs D ms (iext σ (fst p)) C (snd p))
iihs D ms σ (iκ κ C) p = iihs D ms (iext σ (fst p)) C (snd p)

-- ★★ ⚠ REVISED (§9.1): the method is applied to the INDEX first, so ONE
--   method tuple serves every recursive index.
ifields : IDesc → RTm Γ → RTm Γ → ∀ {Δ} → Sub Δ Γ → ICon Δ →
          RTm Γ → RTm Γ → RTm Γ
ifields D i ms σ C m p = app (app (app m i) p) (iihs D ms σ C p)

iihs-cong : (D : IDesc) (ms : RTm Γ) {Δ : Cx} {σ σ' : Sub Δ Γ}
            (C : ICon Δ) (p : RTm Γ) → (∀ x → σ x ≡ σ' x) →
            iihs D ms σ C p ≡ iihs D ms σ' C p
iihs-cong D ms iι       p h = refl
iihs-cong D ms (iρ j C) p h =
  cong₂ pair (cong (λ z → ielim D z ms (fst p)) (subTm-cong h j))
             (iihs-cong D ms C (snd p) (λ { vz → refl ; (vs x) → h x }))
iihs-cong D ms (iκ κ C) p h =
  iihs-cong D ms C (snd p) (λ { vz → refl ; (vs x) → h x })

ren-iihs : (ρ : Ren Γ Δ) (D : IDesc) (ms : RTm Γ) {Θ : Cx}
           (σ : Sub Θ Γ) (C : ICon Θ) (p : RTm Γ) →
           renTm ρ (iihs D ms σ C p)
             ≡ iihs D (renTm ρ ms) (λ x → renTm ρ (σ x)) C (renTm ρ p)
ren-iihs ρ D ms σ iι       p = refl
ren-iihs ρ D ms σ (iρ j C) p =
  cong₂ pair (cong (λ z → ielim D z (renTm ρ ms) (fst (renTm ρ p)))
                   (renTm-subTm j))
             (trans (ren-iihs ρ D ms (iext σ (fst p)) C (snd p))
                    (iihs-cong D (renTm ρ ms) C (renTm ρ (snd p))
                               (λ { vz → refl ; (vs x) → refl })))
ren-iihs ρ D ms σ (iκ κ C) p =
  trans (ren-iihs ρ D ms (iext σ (fst p)) C (snd p))
        (iihs-cong D (renTm ρ ms) C (renTm ρ (snd p))
                   (λ { vz → refl ; (vs x) → refl }))

sub-iihs : (τ : Sub Γ Δ) (D : IDesc) (ms : RTm Γ) {Θ : Cx}
           (σ : Sub Θ Γ) (C : ICon Θ) (p : RTm Γ) →
           subTm τ (iihs D ms σ C p)
             ≡ iihs D (subTm τ ms) (λ x → subTm τ (σ x)) C (subTm τ p)
sub-iihs τ D ms σ iι       p = refl
sub-iihs τ D ms σ (iρ j C) p =
  cong₂ pair (cong (λ z → ielim D z (subTm τ ms) (fst (subTm τ p)))
                   (subTm-subTm j))
             (trans (sub-iihs τ D ms (iext σ (fst p)) C (snd p))
                    (iihs-cong D (subTm τ ms) C (subTm τ (snd p))
                               (λ { vz → refl ; (vs x) → refl })))
sub-iihs τ D ms σ (iκ κ C) p =
  trans (sub-iihs τ D ms (iext σ (fst p)) C (snd p))
        (iihs-cong D (subTm τ ms) C (subTm τ (snd p))
                   (λ { vz → refl ; (vs x) → refl }))

ren-ifields : (ρ : Ren Γ Δ) (D : IDesc) (i ms : RTm Γ) {Θ : Cx}
              (σ : Sub Θ Γ) (C : ICon Θ) (m p : RTm Γ) →
              renTm ρ (ifields D i ms σ C m p)
                ≡ ifields D (renTm ρ i) (renTm ρ ms) (λ x → renTm ρ (σ x)) C
                            (renTm ρ m) (renTm ρ p)
ren-ifields ρ D i ms σ C m p = cong (app _) (ren-iihs ρ D ms σ C p)

sub-ifields : (τ : Sub Γ Δ) (D : IDesc) (i ms : RTm Γ) {Θ : Cx}
              (σ : Sub Θ Γ) (C : ICon Θ) (m p : RTm Γ) →
              subTm τ (ifields D i ms σ C m p)
                ≡ ifields D (subTm τ i) (subTm τ ms) (λ x → subTm τ (σ x)) C
                            (subTm τ m) (subTm τ p)
sub-ifields τ D i ms σ C m p = cong (app _) (sub-iihs τ D ms σ C p)


data _∈D_ : ℕ → Desc → Set where
  hereD  : {C : DCon} {E : Desc} → zero ∈D (C ◃ E)
  thereD : {k : ℕ} {C : DCon} {E : Desc} → k ∈D E → suc k ∈D (C ◃ E)

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
