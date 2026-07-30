------------------------------------------------------------------------
-- OCP-0009 · LINEARIZATION step 8 — ★ THE Lin↔QTT BRIDGE
--
-- `PLAN-dHoTT-kernel.md` §1.3 gap 3, and HANDOFF-2026-07-28 thread (B): "no
-- module imports both lines". `NbEPQTT`/`J`/`Erase`/`EraseTm` is a graded
-- calculus elaborating to the CARTESIAN CCC; `NbEPLin*` is Fox over a free
-- linear category. This module is the join — the first module to import both.
--
-- THE SHAPE THE PLAN ASKED FOR, built:
--   * `𝟙` reaches the linear core with NO `dup`  — `bridge-linear`;
--   * `ω` goes through the comonoid, one `dup` per extra use — `split`'s
--     both-demanded case, and `ω-alloc-1`;
--   * `𝟘` ERASES — definitionally: an erased slot is absent from the context
--     OBJECT, so `Lq⟦ lam {𝟘} t ⟧ = Lq⟦ t ⟧` on the nose (`erase-K`).
--
-- ★ THE CENTRAL MOVE: CONTEXT ADDITION IS TENSOR SPLITTING, NOT DUPLICATION.
-- QTT's `app`/`pair` combine sub-usages with `_+ᵘ_`. The cartesian elaboration
-- (`NbEPQTTJ.⟦_⟧`) renders that as `⟨_,_⟩`, which `NbEPLinPass.L⟦_⟧` must then
-- linearize with a `dup` — one allocation per application and per pairing,
-- ALWAYS. Here `_+ᵘ_` becomes `split`, which routes each context slot to
-- whichever side demands it. A `dup` appears in exactly one case: when BOTH
-- sides demand the same slot. And the semiring makes that case exactly the
-- `ω` case, because `𝟙` cannot be written as a sum of two nonzero
-- multiplicities — `𝟙 +ᵐ 𝟙 = ω`. So "a `𝟙`-graded variable needs no `dup`" is
-- not an optimization to be argued for; it is forced by `Mult`'s addition.
--
-- ⚠ WHAT THIS COSTS THE LINEAR CORE. `LTm` had no associator and no braiding
-- until now — the cartesian pass never needed them, because `⟨_,_⟩L` can
-- express any rearrangement at the price of a copy. Splitting cannot pay that
-- price (it would insert the very `dup` the grading proves unnecessary), so
-- `lassoc`/`lassoc⁻`/`lswap` were added to `NbEPLinRec` (dup-free, cost 0),
-- with clauses through `Lⁱ`/`dupCount`/`frees`/`Lᶜ`/`dyn-linear`. The core is
-- only now genuinely symmetric monoidal.
--
-- ⚠ SCOPE. `dupCount` is STATIC; `NbEPLinDyn`'s four divergences apply here
-- unchanged. The operational claim is `bridge-dyn` (via `dyn-linear`), and it
-- holds for the `LinD` fragment only. `ω` is a PERMISSION to allocate, not a
-- count of allocations.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPLinQTT where

open import normalizer.Syntax.Types
  using ( Ty; Unit; _*_; _⇒_; μ_; Func; One; _⊕_
        ; ⊤; tt; _×_; _,_; Σ; _⊎_; inj₁; ¬_
        ; _≡_; refl; cong; cong₂; trans )
open Σ using ( fst; snd )
open import normalizer.Testing.Evaluator using ( ⟦_⟧T; Fix; fix; eval )
open import poc.OCP0009.NbEPQTT using ( Mult; 𝟘; 𝟙; ω; _+ᵐ_; _·ᵐ_ )
open import poc.OCP0009.NbEPQTTJ
  using ( Tyq; ι; _×q_; _⇒[_]_
        ; Con; ∅; Use; []; _∷_; 0ᵘ; _+ᵘ_; _·ᵘ_
        ; _∋_; vz; vs; useVar; _⊢[_]_; var; lam; app; pair
        ; ⌊_⌋ᵗ; ιT; idₗ; K; dupPair; ⟦_⟧ )
  renaming ( _,_ to _▸_ )
open import poc.OCP0009.NbEPLinRec
  using ( LTm; lid; _∘l_; _⊗l_; ρl⁻; dup; drop; lcurry; leval
        ; lassoc; lassoc⁻; lswap; fstL; sndL; mixL
        ; DupFree; df-id; df-∘; df-⊗; df-ρl⁻; df-drop
        ; df-lcurry; df-leval; df-lassoc; df-lassoc⁻; df-lswap
        ; fstL-df; sndL-df; mixL-df )
open import poc.OCP0009.NbEPLinPass
  using ( ℕ; zero; suc; Lⁱ; dupCount; FunExt; dupfree-no-alloc
        ; FO; fo-∘; fo-fst; fo-snd; fo-pair; fo-apply; L⟦_⟧; pairCount )
open import poc.OCP0009.NbEPLinDyn using ( ⟦_⟧C; Free; Lᶜ; dyn-linear )

------------------------------------------------------------------------
-- 1. THE USAGE-INDEXED CONTEXT OBJECT.
--
-- A `𝟘`-graded slot is not "present but ignored" — it is ABSENT from the
-- object. That is what makes erasure definitional rather than a theorem
-- (`NbEPQTTEraseTm`'s trick, carried to the linear side). `𝟙` and `ω` slots
-- are both present; the object cannot tell them apart, and should not — the
-- difference between them is how many times the slot may be CONSUMED, which
-- is a property of the split, not of the shape.
------------------------------------------------------------------------

⟪_⟫ᶜ : ∀ {Γ} → Use Γ → Ty
⟪ [] ⟫ᶜ              = Unit
⟪ ρ ∷ 𝟘 ⟫ᶜ           = ⟪ ρ ⟫ᶜ
⟪ _∷_ {A = A} ρ 𝟙 ⟫ᶜ = ⟪ ρ ⟫ᶜ * ⌊ A ⌋ᵗ
⟪ _∷_ {A = A} ρ ω ⟫ᶜ = ⟪ ρ ⟫ᶜ * ⌊ A ⌋ᵗ

------------------------------------------------------------------------
-- 2. THE SPLIT — `_+ᵘ_` realized as a linear morphism.
--
-- One derived combinator first: carrying a payload into the LEFT half.
-- (Into the right half is plain `lassoc`.)
------------------------------------------------------------------------

carryL : ∀ {L R X} → LTm ((L * R) * X) ((L * X) * R)
carryL = lassoc⁻ ∘l (lid ⊗l lswap) ∘l lassoc

carryL-df : ∀ {L R X} → DupFree (carryL {L} {R} {X})
carryL-df = df-∘ df-lassoc⁻ (df-∘ (df-⊗ df-id df-lswap) df-lassoc)

-- ★ Splitting a graded context. Read the clauses as a routing table:
--   (𝟘,𝟘) slot absent on both sides — nothing to route;
--   (𝟘,n) present only on the right — `lassoc` carries it right;
--   (m,𝟘) present only on the left  — `carryL` carries it left;
--   (m,n) both nonzero — THE ONLY `dup`. And `m +ᵐ n` is then necessarily
--         `ω`, so this clause is unreachable for an `ω`-free usage.
split : ∀ {Γ} (ρ σ : Use Γ) → LTm ⟪ ρ +ᵘ σ ⟫ᶜ (⟪ ρ ⟫ᶜ * ⟪ σ ⟫ᶜ)
split []      []      = ρl⁻
split (ρ ∷ 𝟘) (σ ∷ 𝟘) = split ρ σ
split (ρ ∷ 𝟘) (σ ∷ 𝟙) = lassoc ∘l (split ρ σ ⊗l lid)
split (ρ ∷ 𝟘) (σ ∷ ω) = lassoc ∘l (split ρ σ ⊗l lid)
split (ρ ∷ 𝟙) (σ ∷ 𝟘) = carryL ∘l (split ρ σ ⊗l lid)
split (ρ ∷ ω) (σ ∷ 𝟘) = carryL ∘l (split ρ σ ⊗l lid)
split (ρ ∷ 𝟙) (σ ∷ 𝟙) = mixL ∘l (split ρ σ ⊗l dup)
split (ρ ∷ 𝟙) (σ ∷ ω) = mixL ∘l (split ρ σ ⊗l dup)
split (ρ ∷ ω) (σ ∷ 𝟙) = mixL ∘l (split ρ σ ⊗l dup)
split (ρ ∷ ω) (σ ∷ ω) = mixL ∘l (split ρ σ ⊗l dup)

------------------------------------------------------------------------
-- 3. SCALING — `_·ᵘ_` at a nonzero multiplicity is a relabelling, not a
-- reshaping: `π ·ᵐ m` is zero exactly when `m` is, so the object is
-- unchanged and the coercion is built from identities alone (hence free,
-- and dup-free). At `𝟘` there is no coercion and none is needed — the
-- argument is dropped instead.
------------------------------------------------------------------------

scale𝟙 : ∀ {Γ} (ρ : Use Γ) → LTm ⟪ 𝟙 ·ᵘ ρ ⟫ᶜ ⟪ ρ ⟫ᶜ
scale𝟙 []      = lid
scale𝟙 (ρ ∷ 𝟘) = scale𝟙 ρ
scale𝟙 (ρ ∷ 𝟙) = scale𝟙 ρ ⊗l lid
scale𝟙 (ρ ∷ ω) = scale𝟙 ρ ⊗l lid

scaleω : ∀ {Γ} (ρ : Use Γ) → LTm ⟪ ω ·ᵘ ρ ⟫ᶜ ⟪ ρ ⟫ᶜ
scaleω []      = lid
scaleω (ρ ∷ 𝟘) = scaleω ρ
scaleω (ρ ∷ 𝟙) = scaleω ρ ⊗l lid
scaleω (ρ ∷ ω) = scaleω ρ ⊗l lid

scale𝟙-df : ∀ {Γ} (ρ : Use Γ) → DupFree (scale𝟙 ρ)
scale𝟙-df []      = df-id
scale𝟙-df (ρ ∷ 𝟘) = scale𝟙-df ρ
scale𝟙-df (ρ ∷ 𝟙) = df-⊗ (scale𝟙-df ρ) df-id
scale𝟙-df (ρ ∷ ω) = df-⊗ (scale𝟙-df ρ) df-id

scaleω-df : ∀ {Γ} (ρ : Use Γ) → DupFree (scaleω ρ)
scaleω-df []      = df-id
scaleω-df (ρ ∷ 𝟘) = scaleω-df ρ
scaleω-df (ρ ∷ 𝟙) = df-⊗ (scaleω-df ρ) df-id
scaleω-df (ρ ∷ ω) = df-⊗ (scaleω-df ρ) df-id

------------------------------------------------------------------------
-- 4. ★ THE ELABORATION: `Γ ⊢[ ρ ] A` straight into the linear core.
--
-- Note what variable lookup became. In the cartesian elaboration
-- `⟦var vs x ⟧ = ⟦var x ⟧ ∘ fst` — a projection per skipped slot. Here the
-- skipped slots are the UNUSED ones, and unused slots are not in the object
-- at all, so there is nothing to project past: lookup is a single `sndL`.
------------------------------------------------------------------------

Lqvar : ∀ {Γ A} (x : Γ ∋ A) → LTm ⟪ useVar x ⟫ᶜ ⌊ A ⌋ᵗ
Lqvar vz     = sndL
Lqvar (vs x) = Lqvar x

Lq⟦_⟧ : ∀ {Γ ρ A} → Γ ⊢[ ρ ] A → LTm ⟪ ρ ⟫ᶜ ⌊ A ⌋ᵗ
Lq⟦ var x ⟧ = Lqvar x
-- ★ ERASURE, definitionally: at `𝟘` the bound slot is absent from the body's
-- context object and the arrow is absent from the target type, so the erased
-- abstraction IS its body — no `curry`, no runtime argument.
Lq⟦ lam {π = 𝟘} t ⟧ = Lq⟦ t ⟧
Lq⟦ lam {π = 𝟙} t ⟧ = lcurry Lq⟦ t ⟧
Lq⟦ lam {π = ω} t ⟧ = lcurry Lq⟦ t ⟧
-- ★ ERASURE at the application: the argument is never elaborated. Its share
-- of the environment is split off and dropped.
Lq⟦ app {π = 𝟘} {ρf = ρf} {ρa = ρa} f a ⟧ =
  Lq⟦ f ⟧ ∘l fstL ∘l split ρf (𝟘 ·ᵘ ρa)
Lq⟦ app {π = 𝟙} {ρf = ρf} {ρa = ρa} f a ⟧ =
  leval ∘l (Lq⟦ f ⟧ ⊗l (Lq⟦ a ⟧ ∘l scale𝟙 ρa)) ∘l split ρf (𝟙 ·ᵘ ρa)
Lq⟦ app {π = ω} {ρf = ρf} {ρa = ρa} f a ⟧ =
  leval ∘l (Lq⟦ f ⟧ ⊗l (Lq⟦ a ⟧ ∘l scaleω ρa)) ∘l split ρf (ω ·ᵘ ρa)
-- ★ and the pairing SPLITS instead of duplicating — the cartesian
-- elaboration's `⟨_,_⟩` (hence one forced `dup`) is gone.
Lq⟦ pair {ρa = ρa} {ρb = ρb} a b ⟧ =
  (Lq⟦ a ⟧ ⊗l Lq⟦ b ⟧) ∘l split ρa ρb

------------------------------------------------------------------------
-- 5. ω-FREEDOM, and the theorem the plan asked for.
------------------------------------------------------------------------

data ωFree : ∀ {Γ} → Use Γ → Set where
  ωf-[] : ωFree []
  ωf-𝟘  : ∀ {Γ A} {ρ : Use Γ} → ωFree ρ → ωFree (_∷_ {A = A} ρ 𝟘)
  ωf-𝟙  : ∀ {Γ A} {ρ : Use Γ} → ωFree ρ → ωFree (_∷_ {A = A} ρ 𝟙)

-- ★ The split is dup-free exactly when the usage it splits is ω-free. The
-- four both-demanded clauses are ABSURD here: their head sum is `ω`, and
-- `ωFree` has no constructor at `ω`. This is the semiring doing the work —
-- `𝟙` is not a sum of two nonzero multiplicities, so a linearly-used slot
-- can never be demanded by both halves of a split.
split-df : ∀ {Γ} (ρ σ : Use Γ) → ωFree (ρ +ᵘ σ) → DupFree (split ρ σ)
split-df []      []      ωf-[]      = df-ρl⁻
split-df (ρ ∷ 𝟘) (σ ∷ 𝟘) (ωf-𝟘 w)   = split-df ρ σ w
split-df (ρ ∷ 𝟘) (σ ∷ 𝟙) (ωf-𝟙 w)   = df-∘ df-lassoc (df-⊗ (split-df ρ σ w) df-id)
split-df (ρ ∷ 𝟙) (σ ∷ 𝟘) (ωf-𝟙 w)   = df-∘ carryL-df (df-⊗ (split-df ρ σ w) df-id)
split-df (ρ ∷ 𝟘) (σ ∷ ω) ()
split-df (ρ ∷ ω) (σ ∷ 𝟘) ()
split-df (ρ ∷ 𝟙) (σ ∷ 𝟙) ()
split-df (ρ ∷ 𝟙) (σ ∷ ω) ()
split-df (ρ ∷ ω) (σ ∷ 𝟙) ()
split-df (ρ ∷ ω) (σ ∷ ω) ()

-- A derivation is LINEAR when every SPLIT POINT in it carries an ω-free
-- usage. Splits happen at `app` and `pair` and nowhere else, so those are the
-- only constructors carrying an obligation.
--
-- ★ Note `lin-app𝟘`: an ERASED argument imposes NO obligation on itself. Its
-- derivation is never elaborated, so however lavishly it uses the context —
-- an `ω`-heavy proof term, say — it cannot cost an allocation. Erasure buys
-- linearity of the runtime term for free.
data LinD : ∀ {Γ ρ A} → Γ ⊢[ ρ ] A → Set where
  lin-var  : ∀ {Γ A} (x : Γ ∋ A) → LinD (var x)
  lin-lam  : ∀ {Γ A B π} {ρ : Use Γ} {t : (Γ ▸ A) ⊢[ ρ ∷ π ] B} →
             LinD t → LinD (lam t)
  lin-app𝟘 : ∀ {Γ A B} {ρf ρa : Use Γ}
             {f : Γ ⊢[ ρf ] (A ⇒[ 𝟘 ] B)} {a : Γ ⊢[ ρa ] A} →
             ωFree (ρf +ᵘ (𝟘 ·ᵘ ρa)) → LinD f → LinD (app f a)
  lin-app𝟙 : ∀ {Γ A B} {ρf ρa : Use Γ}
             {f : Γ ⊢[ ρf ] (A ⇒[ 𝟙 ] B)} {a : Γ ⊢[ ρa ] A} →
             ωFree (ρf +ᵘ (𝟙 ·ᵘ ρa)) → LinD f → LinD a → LinD (app f a)
  lin-appω : ∀ {Γ A B} {ρf ρa : Use Γ}
             {f : Γ ⊢[ ρf ] (A ⇒[ ω ] B)} {a : Γ ⊢[ ρa ] A} →
             ωFree (ρf +ᵘ (ω ·ᵘ ρa)) → LinD f → LinD a → LinD (app f a)
  lin-pair : ∀ {Γ A B} {ρa ρb : Use Γ}
             {a : Γ ⊢[ ρa ] A} {b : Γ ⊢[ ρb ] B} →
             ωFree (ρa +ᵘ ρb) → LinD a → LinD b → LinD (pair a b)

Lqvar-df : ∀ {Γ A} (x : Γ ∋ A) → DupFree (Lqvar x)
Lqvar-df vz     = sndL-df
Lqvar-df (vs x) = Lqvar-df x

-- ★★ THE BRIDGE THEOREM. A linearly-graded derivation reaches the linear core
-- with NO `dup` at all. This is §1.3's "a `𝟙`-graded variable reaches the
-- linear core with no `dup`", machine-checked, for whole derivations.
bridge-linear : ∀ {Γ ρ A} {t : Γ ⊢[ ρ ] A} → LinD t → DupFree Lq⟦ t ⟧
bridge-linear (lin-var x)              = Lqvar-df x
bridge-linear (lin-lam {π = 𝟘} d)      = bridge-linear d
bridge-linear (lin-lam {π = 𝟙} d)      = df-lcurry (bridge-linear d)
bridge-linear (lin-lam {π = ω} d)      = df-lcurry (bridge-linear d)
bridge-linear (lin-app𝟘 {ρf = ρf} {ρa = ρa} w df) =
  df-∘ (bridge-linear df) (df-∘ fstL-df (split-df ρf (𝟘 ·ᵘ ρa) w))
bridge-linear (lin-app𝟙 {ρf = ρf} {ρa = ρa} w df da) =
  df-∘ df-leval
    (df-∘ (df-⊗ (bridge-linear df) (df-∘ (bridge-linear da) (scale𝟙-df ρa)))
          (split-df ρf (𝟙 ·ᵘ ρa) w))
bridge-linear (lin-appω {ρf = ρf} {ρa = ρa} w df da) =
  df-∘ df-leval
    (df-∘ (df-⊗ (bridge-linear df) (df-∘ (bridge-linear da) (scaleω-df ρa)))
          (split-df ρf (ω ·ᵘ ρa) w))
bridge-linear (lin-pair {ρa = ρa} {ρb = ρb} w da db) =
  df-∘ (df-⊗ (bridge-linear da) (bridge-linear db)) (split-df ρa ρb w)

-- …hence it allocates nothing, statically.
bridge-alloc : ∀ {Γ ρ A} {t : Γ ⊢[ ρ ] A} → LinD t → dupCount Lq⟦ t ⟧ ≡ zero
bridge-alloc d = dupfree-no-alloc (bridge-linear d)

-- ★ …and nothing at RUNTIME. Straight composition with `NbEPLinDyn.dyn-linear`:
-- the operational reading of the memory dividend, now reached from a GRADED
-- SOURCE rather than from a hand-written linear term.
bridge-dyn : ∀ {Γ ρ A} {t : Γ ⊢[ ρ ] A} → LinD t →
             (x : ⟦ ⟪ ρ ⟫ᶜ ⟧C) → Free ⟪ ρ ⟫ᶜ x →
             Free ⌊ A ⌋ᵗ (fst (Lᶜ Lq⟦ t ⟧ x)) × (snd (Lᶜ Lq⟦ t ⟧ x) ≡ zero)
bridge-dyn d x fx = dyn-linear (bridge-linear d) x fx

------------------------------------------------------------------------
-- 6. ★ THE PAYOFF, MEASURED: the naive route allocates where the grading
-- already knew it need not.
--
-- `NbEPQTTJ.dupPair` is `pair (var (vs vz)) (var vz)` over `(∅ , ι , ι)` —
-- two DISTINCT variables, each used once, so `⊢[ ([] ∷ 𝟙) ∷ 𝟙 ]`: perfectly
-- linear, nothing shared, nothing to copy.
--
--   · via the cartesian elaboration then `NbEPLinPass.L⟦_⟧`: ONE `dup`.
--     `⟦_⟧` renders the context split as `⟨_,_⟩`, and `L⟦_⟧` has no choice
--     but to linearize a pairing with the comonoid.
--   · via the bridge: ZERO. `split` routes the left variable left and the
--     right variable right.
--
-- That single allocation is the cost of throwing the usage vector away at
-- elaboration — §1.3's "stop discarding information you already compute",
-- as a number.
------------------------------------------------------------------------

linear-dupPair : LinD dupPair
linear-dupPair = lin-pair (ωf-𝟙 (ωf-𝟙 ωf-[])) (lin-var (vs vz)) (lin-var vz)

bridge-dupPair-0 : dupCount Lq⟦ dupPair ⟧ ≡ zero
bridge-dupPair-0 = refl

-- the same source through the cartesian elaboration…
naiveFO : FO ⟦ dupPair ⟧
naiveFO = fo-pair (fo-∘ fo-snd fo-fst) fo-snd

-- …costs one allocation.
naive-dupPair-1 : dupCount L⟦ naiveFO ⟧ ≡ suc zero
naive-dupPair-1 = refl

-- The same contrast at an APPLICATION, which is where `_+ᵘ_` does its real
-- work: `f x` with `f` and `x` distinct linear variables.
-- `NbEPLinUse.beta-alloc-1` measured the cartesian β-redex at ONE `dup` — the
-- one cartesian pairing feeding `apply`. Graded, that pairing is a context
-- SPLIT, and the split is free.
applyLin : (∅ ▸ (ι ⇒[ 𝟙 ] ι) ▸ ι) ⊢[ ([] ∷ 𝟙) ∷ 𝟙 ] ι
applyLin = app (var (vs vz)) (var vz)

linear-applyLin : LinD applyLin
linear-applyLin = lin-app𝟙 (ωf-𝟙 (ωf-𝟙 ωf-[])) (lin-var (vs vz)) (lin-var vz)

bridge-applyLin-0 : dupCount Lq⟦ applyLin ⟧ ≡ zero
bridge-applyLin-0 = refl

naiveApFO : FO ⟦ applyLin ⟧
naiveApFO = fo-∘ fo-apply (fo-pair (fo-∘ fo-snd fo-fst) fo-snd)

naive-applyLin-1 : dupCount L⟦ naiveApFO ⟧ ≡ suc zero
naive-applyLin-1 = refl

------------------------------------------------------------------------
-- 7. `ω` — and that the `dup` is genuinely there when sharing is.
--
-- `pair (var vz) (var vz)`: ONE variable used TWICE, so `𝟙 +ᵐ 𝟙 = ω`. The
-- split's both-demanded clause fires, and it is the only place it can.
------------------------------------------------------------------------

ωPair : (∅ ▸ ι) ⊢[ [] ∷ ω ] (ι ×q ι)
ωPair = pair (var vz) (var vz)

-- exactly one allocation — `NbEPLinUse.dupN 2`'s figure, arrived at from the
-- grading rather than from a usage analysis.
ω-alloc-1 : dupCount Lq⟦ ωPair ⟧ ≡ suc zero
ω-alloc-1 = refl

-- …and it is not linear, for the reason the semiring says: the slot's
-- multiplicity is `ω`, so `ωFree` has no derivation and `LinD` is empty here.
ω-not-linear : ¬ LinD ωPair
ω-not-linear (lin-pair () _ _)

------------------------------------------------------------------------
-- 8. `𝟘` — erasure, on the nose.
--
-- `K : ι ⇒[𝟙] (ι ⇒[𝟘] ι)` ignores its second argument. `NbEPQTTJ` elaborates
-- it CARTESIANLY to the two-argument `curry (curry (snd ∘ fst))`;
-- `NbEPQTTEraseTm`'s erasing elaboration recovers the one-argument
-- `curry snd`. The bridge lands on the erased form DIRECTLY — there is no
-- erasure pass here, because a `𝟘`-graded slot is never in the context object
-- to begin with.
------------------------------------------------------------------------

erase-K : Lq⟦ K ⟧ ≡ lcurry sndL
erase-K = refl

erase-id : Lq⟦ idₗ ⟧ ≡ lcurry sndL
erase-id = refl

-- ★ the constant function and the linear identity compile to the SAME linear
-- term (`NbEPQTTEraseTm`'s headline, on the linear side).
erase-K≡id : Lq⟦ K ⟧ ≡ Lq⟦ idₗ ⟧
erase-K≡id = refl

------------------------------------------------------------------------
-- 9. SEMANTICS PRESERVATION.
--
-- The bridge is a compiler pass, so it owes the same debt `NbEPLinPass.L-sound`
-- pays: it must not change meaning. `Qⁱ` below is the graded calculus's own
-- denotational semantics — environment-passing, direct variable lookup,
-- ordinary function application — defined independently of the elaboration.
-- The content of `Lq-sound` is that the point-free routing (splits, braids,
-- scalings) computes what direct lookup computes.
--
-- Two things to note in `Qⁱ`. A `𝟘`-graded APPLICATION does not evaluate its
-- argument (`Qⁱ (app {𝟘} f a) γ = Qⁱ f γ`) — erasure, semantically. And a
-- `𝟘`-graded ABSTRACTION feeds its body a DEFAULT (`dflt`), which is sound
-- precisely because the elaborated term cannot observe that slot: it is not in
-- the object. `dflt` exists for every type because `⌊_⌋ᵗ` never lands in
-- `Void` — the base type is `μ (One ⊕ One)`, and arrows inherit inhabitation
-- from their codomain.
--
-- `funext` is THREADED (§1.2's ground rule), and needed in exactly the two
-- `lcurry` clauses, for the same reason `L-sound` needs it.
------------------------------------------------------------------------

Env : Con → Set
Env ∅       = ⊤
Env (Γ ▸ A) = Env Γ × ⟦ ⌊ A ⌋ᵗ ⟧T

-- the environment RESTRICTED to a usage: erased slots dropped.
res : ∀ {Γ} (ρ : Use Γ) → Env Γ → ⟦ ⟪ ρ ⟫ᶜ ⟧T
res []      γ       = tt
res (ρ ∷ 𝟘) (γ , a) = res ρ γ
res (ρ ∷ 𝟙) (γ , a) = (res ρ γ , a)
res (ρ ∷ ω) (γ , a) = (res ρ γ , a)

look : ∀ {Γ A} → Γ ∋ A → Env Γ → ⟦ ⌊ A ⌋ᵗ ⟧T
look vz     (γ , a) = a
look (vs x) (γ , a) = look x γ

dflt : ∀ A → ⟦ ⌊ A ⌋ᵗ ⟧T
dflt ι            = fix (inj₁ tt)
dflt (A ×q B)     = (dflt A , dflt B)
dflt (A ⇒[ 𝟘 ] B) = dflt B
dflt (A ⇒[ 𝟙 ] B) = λ _ → dflt B
dflt (A ⇒[ ω ] B) = λ _ → dflt B

Qⁱ : ∀ {Γ ρ A} → Γ ⊢[ ρ ] A → Env Γ → ⟦ ⌊ A ⌋ᵗ ⟧T
Qⁱ (var x)                   γ = look x γ
Qⁱ (lam {A = A} {π = 𝟘} t)   γ = Qⁱ t (γ , dflt A)
Qⁱ (lam {π = 𝟙} t)           γ = λ a → Qⁱ t (γ , a)
Qⁱ (lam {π = ω} t)           γ = λ a → Qⁱ t (γ , a)
Qⁱ (app {π = 𝟘} f a)         γ = Qⁱ f γ
Qⁱ (app {π = 𝟙} f a)         γ = Qⁱ f γ (Qⁱ a γ)
Qⁱ (app {π = ω} f a)         γ = Qⁱ f γ (Qⁱ a γ)
Qⁱ (pair a b)                γ = (Qⁱ a γ , Qⁱ b γ)

-- ★ the split is the semantic pair of restrictions — routing, not copying.
split-sem : ∀ {Γ} (ρ σ : Use Γ) (γ : Env Γ) →
            Lⁱ (split ρ σ) (res (ρ +ᵘ σ) γ) ≡ (res ρ γ , res σ γ)
split-sem []      []      γ       = refl
split-sem (ρ ∷ 𝟘) (σ ∷ 𝟘) (γ , a) = split-sem ρ σ γ
split-sem (ρ ∷ 𝟘) (σ ∷ 𝟙) (γ , a) = cong (λ p → Lⁱ lassoc (p , a)) (split-sem ρ σ γ)
split-sem (ρ ∷ 𝟘) (σ ∷ ω) (γ , a) = cong (λ p → Lⁱ lassoc (p , a)) (split-sem ρ σ γ)
split-sem (ρ ∷ 𝟙) (σ ∷ 𝟘) (γ , a) = cong (λ p → Lⁱ carryL (p , a)) (split-sem ρ σ γ)
split-sem (ρ ∷ ω) (σ ∷ 𝟘) (γ , a) = cong (λ p → Lⁱ carryL (p , a)) (split-sem ρ σ γ)
split-sem (ρ ∷ 𝟙) (σ ∷ 𝟙) (γ , a) = cong (λ p → Lⁱ mixL (p , (a , a))) (split-sem ρ σ γ)
split-sem (ρ ∷ 𝟙) (σ ∷ ω) (γ , a) = cong (λ p → Lⁱ mixL (p , (a , a))) (split-sem ρ σ γ)
split-sem (ρ ∷ ω) (σ ∷ 𝟙) (γ , a) = cong (λ p → Lⁱ mixL (p , (a , a))) (split-sem ρ σ γ)
split-sem (ρ ∷ ω) (σ ∷ ω) (γ , a) = cong (λ p → Lⁱ mixL (p , (a , a))) (split-sem ρ σ γ)

scale𝟙-sem : ∀ {Γ} (ρ : Use Γ) (γ : Env Γ) →
             Lⁱ (scale𝟙 ρ) (res (𝟙 ·ᵘ ρ) γ) ≡ res ρ γ
scale𝟙-sem []      γ       = refl
scale𝟙-sem (ρ ∷ 𝟘) (γ , a) = scale𝟙-sem ρ γ
scale𝟙-sem (ρ ∷ 𝟙) (γ , a) = cong (λ p → (p , a)) (scale𝟙-sem ρ γ)
scale𝟙-sem (ρ ∷ ω) (γ , a) = cong (λ p → (p , a)) (scale𝟙-sem ρ γ)

scaleω-sem : ∀ {Γ} (ρ : Use Γ) (γ : Env Γ) →
             Lⁱ (scaleω ρ) (res (ω ·ᵘ ρ) γ) ≡ res ρ γ
scaleω-sem []      γ       = refl
scaleω-sem (ρ ∷ 𝟘) (γ , a) = scaleω-sem ρ γ
scaleω-sem (ρ ∷ 𝟙) (γ , a) = cong (λ p → (p , a)) (scaleω-sem ρ γ)
scaleω-sem (ρ ∷ ω) (γ , a) = cong (λ p → (p , a)) (scaleω-sem ρ γ)

Lqvar-sem : ∀ {Γ A} (x : Γ ∋ A) (γ : Env Γ) →
            Lⁱ (Lqvar x) (res (useVar x) γ) ≡ look x γ
Lqvar-sem vz     (γ , a) = refl
Lqvar-sem (vs x) (γ , a) = Lqvar-sem x γ

-- ★★ THE PASS PRESERVES MEANING.
Lq-sound : FunExt → ∀ {Γ ρ A} (t : Γ ⊢[ ρ ] A) (γ : Env Γ) →
           Lⁱ Lq⟦ t ⟧ (res ρ γ) ≡ Qⁱ t γ
Lq-sound fe (var x) γ = Lqvar-sem x γ
Lq-sound fe (lam {A = A} {π = 𝟘} t) γ = Lq-sound fe t (γ , dflt A)
Lq-sound fe (lam {π = 𝟙} t) γ = fe (λ a → Lq-sound fe t (γ , a))
Lq-sound fe (lam {π = ω} t) γ = fe (λ a → Lq-sound fe t (γ , a))
Lq-sound fe (app {π = 𝟘} {ρf = ρf} {ρa = ρa} f a) γ =
  trans (cong (λ p → Lⁱ Lq⟦ f ⟧ (Lⁱ fstL p)) (split-sem ρf (𝟘 ·ᵘ ρa) γ))
        (Lq-sound fe f γ)
Lq-sound fe (app {π = 𝟙} {ρf = ρf} {ρa = ρa} f a) γ =
  trans (cong (λ p → Lⁱ leval (Lⁱ (Lq⟦ f ⟧ ⊗l (Lq⟦ a ⟧ ∘l scale𝟙 ρa)) p))
              (split-sem ρf (𝟙 ·ᵘ ρa) γ))
        (cong₂ (λ u v → u v) (Lq-sound fe f γ)
               (trans (cong (λ p → Lⁱ Lq⟦ a ⟧ p) (scale𝟙-sem ρa γ))
                      (Lq-sound fe a γ)))
Lq-sound fe (app {π = ω} {ρf = ρf} {ρa = ρa} f a) γ =
  trans (cong (λ p → Lⁱ leval (Lⁱ (Lq⟦ f ⟧ ⊗l (Lq⟦ a ⟧ ∘l scaleω ρa)) p))
              (split-sem ρf (ω ·ᵘ ρa) γ))
        (cong₂ (λ u v → u v) (Lq-sound fe f γ)
               (trans (cong (λ p → Lⁱ Lq⟦ a ⟧ p) (scaleω-sem ρa γ))
                      (Lq-sound fe a γ)))
Lq-sound fe (pair {ρa = ρa} {ρb = ρb} a b) γ =
  trans (cong (λ p → Lⁱ (Lq⟦ a ⟧ ⊗l Lq⟦ b ⟧) p) (split-sem ρa ρb γ))
        (cong₂ (λ u v → (u , v)) (Lq-sound fe a γ) (Lq-sound fe b γ))

------------------------------------------------------------------------
-- 10. ★ THE BRIDGE, END TO END.
--
-- For a linearly-graded source: the linear output computes the same function
-- AND performs no allocation at runtime. The two halves the plan wanted from
-- the join, in one statement.
------------------------------------------------------------------------

bridge : FunExt → ∀ {Γ ρ A} {t : Γ ⊢[ ρ ] A} → LinD t →
         (∀ (γ : Env Γ) → Lⁱ Lq⟦ t ⟧ (res ρ γ) ≡ Qⁱ t γ)
         × (∀ (x : ⟦ ⟪ ρ ⟫ᶜ ⟧C) → Free ⟪ ρ ⟫ᶜ x → snd (Lᶜ Lq⟦ t ⟧ x) ≡ zero)
bridge fe {t = t} d =
  ( (λ γ → Lq-sound fe t γ)
  , (λ x fx → snd (bridge-dyn d x fx)) )
