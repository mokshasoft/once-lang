------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 17 — A REAL OPTIMIZER PASS AS A DIRECTED `Id`,
--                            and correctness by DIRECTED TRANSPORT
--
-- Path 2 earning its keep on real code (HANDOFF §2, §5b). The design claim is
-- that Once's optimizer passes LITERALLY ARE reductions `⟶*`, i.e. inhabitants
-- of the directed identity type `Id = Hom` (`NbEPDirKernel`/`NbEPDir`). This
-- module makes that operational on the actual CCC IR:
--
--   * `Pass = Hom` — an optimizer pass IS a reduction sequence. Passes have a
--     no-op (`idH`, the empty pass) and COMPOSE (`_∘H_`) — a pipeline of passes
--     is a composite pass, still an inhabitant of `Id`. Optimization is
--     functorial data, not folklore.
--   * Three GENUINE passes, each a `⟶*` on real IR: identity/copy elimination
--     (`id-elim`), dead-code elimination via projection (`dead-code`, the
--     discarded `double` is never evaluated), and dead-branch elimination via
--     case-of-known-constructor (`dead-branch`).
--   * `pass-preserves` — CORRECTNESS BY DIRECTED TRANSPORT: any semantic
--     property `Q` of a program's output transports COVARIANTLY along a pass,
--     `(∀ x → Q (eval s x)) → (∀ x → Q (eval t x))`. This is `transport⟶`
--     (`NbEPDirJ`) / `apd`/`transp` (`NbEPDirAp`) at the semantic-property
--     family — the compiler-relevant use of the directed identity type. The
--     covariance fee is per-step evaluation soundness (`⟶ ⊆ ≋`), threaded as a
--     hypothesis (the tower's one funext theorem, `EvalSound.eval-sound`).
--   * `dead-code-preserves` — the SAME, AXIOM-FREE, on the concrete pass: the
--     eliminated code is discarded before evaluation forces it, so source and
--     target denote definitionally and no soundness input is needed.
--
-- WHY DIRECTED. `dead-code` is IRREVERSIBLE (`dead-code-no-back`): once the
-- dead `double` is projected away it cannot be recovered — the reverse `⟶*`
-- does not exist. A SYMMETRIC identity type could not model this: it would let
-- you "un-optimize", inventing code from nothing. Transport is one-directional
-- (covariant) exactly because optimization is. The identity type for a
-- compiler MUST be directed; its symmetric core (`NbEPDirKernel.Core`) is the
-- separate notion of "these two programs are interchangeable".
--
-- `--safe`, ZERO axioms in this module (soundness threaded, never assumed).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirPass where

open import normalizer.Syntax.Types
  using ( Ty; _≡_; refl; ¬_; ⊥; subst )
open import normalizer.Syntax.CCC as C
  using ( Term; _∘_; id; fst; ⟨_,_⟩; inl; _+_; _*_; _⟶_; _⟶*_; done; step
        ; id-left; fst-pair; case-inl; ⟶-∘-l )
open import normalizer.Testing.Evaluator
  using ( ⟦_⟧T; eval )
open import poc.OCP0009.NbE
  using ( Nat; double )
open import poc.OCP0009.NbEPDir
  using ( Hom; idH; _∘H_ )
open import poc.OCP0009.NbEPDirJ
  using ( transport⟶ )

------------------------------------------------------------------------
-- A pass IS a reduction sequence. `idH` is the no-op pass; `_∘H_` runs one
-- pass after another. (Category laws proven in `NbEPDir`.)
------------------------------------------------------------------------

Pass : ∀ {A B} → Term A B → Term A B → Set
Pass s t = Hom s t

no-op : ∀ {A B} {t : Term A B} → Pass t t
no-op = idH

_then_ : ∀ {A B} {s t u : Term A B} → Pass s t → Pass t u → Pass s u
p then q = q ∘H p

------------------------------------------------------------------------
-- Three genuine optimizer passes on the real CCC IR, each a `⟶*`.
------------------------------------------------------------------------

-- (1) Identity / copy elimination: `id ∘ f` ↦ `f`.
id-elim : ∀ {A B} (f : Term A B) → Pass (id ∘ f) f
id-elim f = step id-left done

-- (2) Dead-code elimination via projection: the program builds a pair whose
-- second component is an expensive `double`, then projects the first — so
-- `double` is DEAD. `(id ∘ fst) ∘ ⟨ id , double ⟩` optimizes to `id`, and the
-- `double` computation vanishes. Two steps (identity-elim, then projection).
source tgt : Term Nat Nat
source = (id ∘ fst) ∘ ⟨ id , double ⟩
tgt    = id

dead-code : Pass source tgt
dead-code = step (⟶-∘-l id-left) (step fst-pair done)

-- (3) Dead-branch elimination (case of a known constructor): the scrutinee is
-- statically `inl`, so the `double` branch is DEAD. `[ id , double ] ∘ inl`
-- optimizes to `id`.
dead-branch : Pass (C.[ id , double ] ∘ inl) id
dead-branch = step case-inl done

------------------------------------------------------------------------
-- CORRECTNESS BY DIRECTED TRANSPORT. A semantic property `Q` of the output
-- transports covariantly ALONG a pass. This is `transport⟶` at the family
-- `λ prog → ∀ x → Q (eval prog x)`; the covariance fee is per-step evaluation
-- soundness, threaded (the tower's funext theorem `EvalSound.eval-sound`).
------------------------------------------------------------------------

-- Per-step semantic soundness `⟶ ⊆ ≋` (proven axiom-free-modulo-funext in
-- `EvalSound`/`Complete`; passed in, so THIS module assumes nothing).
Sound : Set
Sound = ∀ {A B} {t u : Term A B} → t ⟶ u → (x : ⟦ A ⟧T) → eval t x ≡ eval u x

pass-preserves : Sound → ∀ {A B} {s t : Term A B} (Q : ⟦ B ⟧T → Set) →
                 Pass s t → (∀ x → Q (eval s x)) → (∀ x → Q (eval t x))
pass-preserves sound Q =
  transport⟶ (λ prog → ∀ x → Q (eval prog x))
             (λ r h x → subst Q (sound r x) (h x))

-- The no-op pass transports trivially (transport along `idH` is the identity)
-- — directed `transport-id`, on real code.
pass-preserves-noop : (sd : Sound) → ∀ {A B} {t : Term A B} (Q : ⟦ B ⟧T → Set)
                      (h : ∀ x → Q (eval t x)) →
                      pass-preserves sd Q (no-op {t = t}) h ≡ h
pass-preserves-noop sd Q h = refl

------------------------------------------------------------------------
-- The dead-code pass preserves EVERY property AXIOM-FREE: `double` is
-- discarded by `fst` before evaluation forces it, so `eval source x` and
-- `eval tgt x` are definitionally the same value — no soundness input needed.
------------------------------------------------------------------------

dead-code-preserves : (Q : ⟦ Nat ⟧T → Set) →
                      (∀ x → Q (eval source x)) → (∀ x → Q (eval tgt x))
dead-code-preserves Q h x = h x

------------------------------------------------------------------------
-- WHY THE IDENTITY TYPE MUST BE DIRECTED. The dead-code pass is IRREVERSIBLE:
-- `id` is fully reduced (no rule's redex), so there is NO pass back to the
-- source — the eliminated `double` is gone forever. A symmetric identity type
-- could not express this (it would let you un-optimize). Directedness is not a
-- restriction here; it is the correct model of optimization.
------------------------------------------------------------------------

id-stuck : ∀ {A} {v : Term A A} → id ⟶ v → ⊥
id-stuck ()

dead-code-no-back : ¬ Pass tgt source
dead-code-no-back (step s _) = id-stuck s
