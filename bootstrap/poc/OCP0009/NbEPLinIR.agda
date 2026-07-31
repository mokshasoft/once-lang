------------------------------------------------------------------------
-- OCP-0009 · W0d — PORTING THE REAL IR TO THE LINEAR CORE.  The measurement.
--
-- W0e removed the THEORY blocker (`SpikeLinNu`: codata has a cost-carrying
-- linear semantics, and `dynN` covers `ν`).  This module measures what is left,
-- against the real `Once.Type`/`Once.IR` rather than against prose, and the
-- answer is not what PLAN §8 assumed.
--
-- ★ THE FINDING: THE BLOCKER IS NO LONGER CODATA, IT IS `Ty` ITSELF.
--
-- PLAN §8 says the codata exclusion can be lifted "at the price of folding `ν`
-- into `Ty`/`LTm`, which is a syntax extension and cascades".  Measured, that
-- price is not payable: `LTm : Ty → Ty → Set` over
-- `normalizer.Syntax.Types.Ty`, and of the eleven modules that pattern-match
-- on `Ty`'s constructors, **ten are in `normalizer/TCB0/`** — the trusted
-- computing base.  Adding a constructor to `Ty` means re-verifying the TCB for
-- a POC experiment.  That is the wrong trade, and it is not codata-specific:
-- `Int`/`Float`/`Str`/`Buffer` (PLAN §8.1(4), "mechanical, not research") are
-- blocked by exactly the same wall.
--
-- ★ AND THE MISMATCH IS TWO-SIDED.  It is not simply that the real language is
-- bigger.  `Func`'s `Kc` (a constant that is a CODE) is **unreachable** from
-- any well-formed real functor, because `WellFormedF` restricts `K` to BASE
-- types and `μ-type G` is not one (`Kc-unreachable`).  The two functor
-- languages each have something the other cannot say, and they agree on
-- exactly one constant: `Unit`.
--
-- WHAT IS DELIVERED HERE.  `PortableT`/`PortableF` — the fragment of the real
-- `Type`/`Functor` that HAS a linear-core target — with the translation defined
-- on the predicate (so the domain is explicit rather than a partial function),
-- the functor-action coherence that any morphism port needs, and concrete
-- witnesses on both sides.  This turns PLAN §8's prose coverage table into
-- checked code.
--
-- WHAT IS NOT.  The IR-morphism translation `IR A B → LTm ⌊A⌋ᵀ ⌊B⌋ᵀ` itself.
-- It is now a well-defined obligation rather than an open question — §6 states
-- it precisely — but it should not be written against a target that cannot
-- receive `ν`, `Int`, or `const`, because the fragment it would cover is
-- narrower than the fragment W0e already justifies.  See §6.
--
-- ⚠ FLAGS, and why this module is the one exception on the Lin line.  It is
-- `--guardedness` WITHOUT `--safe`, because it imports the real `Once.Type`
-- and the `Once` library sets only `--exact-split --guardedness`.  That is a
-- LIBRARY-FLAG fact, not an unsoundness one: `Once.Type` contains no
-- postulates (checked).  The alternative — mirroring `Type`/`Functor`/`⟦_⟧T`/
-- `WellFormedF` locally to keep `--safe` — would measure a COPY, and W0d's
-- method is explicitly to assess against the real files rather than against
-- prose.  A copy that drifted would be worse than a lost flag.  Zero
-- postulates and zero holes here regardless.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}
module poc.OCP0009.NbEPLinIR where

-- ⚠ QUALIFIED on purpose.  The two towers share nine constructor names
-- (`Unit`/`Void`/`_*_`/`_+_`/`Id`/`_⊕_`/`_⊗_`/…) and mean different things by
-- them; unqualifying either side makes the mismatch this module measures
-- invisible at the point of use.
import Once.Type as T
import Once.Functor.Translate as TR
import normalizer.Syntax.Types as N

open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; ¬_; Σ; _,_ )

------------------------------------------------------------------------
-- 1. THE PORTABLE FRAGMENT.
--
-- Stated as a PREDICATE, not a partial function into `Maybe Ty`: the whole
-- point is to name the domain, and a `Maybe` would let a caller pretend the
-- gap does not exist.  Every constructor below is present because `Ty` (resp.
-- `Func`) has something to receive it; every real constructor NOT below is
-- absent because it does not.
------------------------------------------------------------------------

data PortableF : T.Functor → Set
data PortableT : T.Type → Set

data PortableT where
  p-Unit : PortableT T.Unit
  p-Void : PortableT T.Void
  p-*    : ∀ {A B} → PortableT A → PortableT B → PortableT (A T.* B)
  p-+    : ∀ {A B} → PortableT A → PortableT B → PortableT (A T.+ B)
  -- ★ THE GRADE IS DROPPED.  `Ty`'s `⇒` is ungraded, and that is correct
  -- rather than lossy: W0c's finding is that the usage indexes the target
  -- OBJECT (`⟪ ρ ⟫ᶜ`), not the arrow.  The `ArrowKind` is consumed on the
  -- SOURCE side by `NbEPLinQTT`, and has nothing to do in the target.
  p-⇒    : ∀ {A B k} → PortableT A → PortableT B → PortableT (A T.⇒[ k ] B)
  p-μ    : ∀ {F} → PortableF F → PortableT (T.μ-type F)

data PortableF where
  -- ★ `K Unit` is the ONLY constant that ports.  `Func`'s constants are `One`
  -- (the Unit leaf) and `Kc` (a code); `WellFormedF` restricts `K` to base
  -- types; `Unit` is the unique type that is both.
  pf-K1 : PortableF (T.K T.Unit)
  pf-Id : PortableF T.Id
  pf-⊕  : ∀ {F G} → PortableF F → PortableF G → PortableF (F T.⊕ G)
  pf-⊗  : ∀ {F G} → PortableF F → PortableF G → PortableF (F T.⊗ G)

------------------------------------------------------------------------
-- 2. THE TRANSLATION, defined ON the witness.
------------------------------------------------------------------------

⌊_⌋ᶠ : ∀ {F} → PortableF F → N.Func
⌊ pf-K1 ⌋ᶠ    = N.One
⌊ pf-Id ⌋ᶠ    = N.Id
⌊ pf-⊕ p q ⌋ᶠ = ⌊ p ⌋ᶠ N.⊕ ⌊ q ⌋ᶠ
⌊ pf-⊗ p q ⌋ᶠ = ⌊ p ⌋ᶠ N.⊗ ⌊ q ⌋ᶠ

⌊_⌋ᵀ : ∀ {A} → PortableT A → N.Ty
⌊ p-Unit ⌋ᵀ    = N.Unit
⌊ p-Void ⌋ᵀ    = N.Void
⌊ p-* p q ⌋ᵀ   = ⌊ p ⌋ᵀ N.* ⌊ q ⌋ᵀ
⌊ p-+ p q ⌋ᵀ   = ⌊ p ⌋ᵀ N.+ ⌊ q ⌋ᵀ
⌊ p-⇒ p q ⌋ᵀ   = ⌊ p ⌋ᵀ N.⇒ ⌊ q ⌋ᵀ
⌊ p-μ p ⌋ᵀ     = N.μ ⌊ p ⌋ᶠ

-- Portability is a PROPERTY, not structure: the translation cannot depend on
-- which witness was supplied.  (Needed the moment a caller reconstructs a
-- witness rather than threading one — e.g. `WellFormedF-irrelevant`'s role on
-- the real side.)
portT-irr : ∀ {A} (p q : PortableT A) → ⌊ p ⌋ᵀ ≡ ⌊ q ⌋ᵀ
portF-irr : ∀ {F} (p q : PortableF F) → ⌊ p ⌋ᶠ ≡ ⌊ q ⌋ᶠ
portT-irr p-Unit      p-Unit      = refl
portT-irr p-Void      p-Void      = refl
portT-irr (p-* a b)   (p-* c d)   = cong₂ N._*_ (portT-irr a c) (portT-irr b d)
portT-irr (p-+ a b)   (p-+ c d)   = cong₂ N._+_ (portT-irr a c) (portT-irr b d)
portT-irr (p-⇒ a b)   (p-⇒ c d)   = cong₂ N._⇒_ (portT-irr a c) (portT-irr b d)
portT-irr (p-μ a)     (p-μ c)     = cong (λ x → N.μ x) (portF-irr a c)
portF-irr pf-K1       pf-K1       = refl
portF-irr pf-Id       pf-Id       = refl
portF-irr (pf-⊕ a b)  (pf-⊕ c d)  = cong₂ N._⊕_ (portF-irr a c) (portF-irr b d)
portF-irr (pf-⊗ a b)  (pf-⊗ c d)  = cong₂ N._⊗_ (portF-irr a c) (portF-irr b d)

------------------------------------------------------------------------
-- 3. ★ THE COHERENCE — what a morphism port actually runs on.
--
-- `In : IR (⟦ F ⟧T (μ-type F)) (μ-type F)` must land on
-- `lIn : LTm (⟦ F ⟧F (μ F)) (μ F)`, so the translation has to COMMUTE with the
-- functor action.  It does, on the nose, and this is the lemma every one of
-- `In`/`out-μ`/`Cata`/`Para`/`Fuse` would consume.  Proving it here is the
-- reason §6's obligation is now mechanical rather than open.
------------------------------------------------------------------------

appP : ∀ {F A} → PortableF F → PortableT A → PortableT (T.⟦ F ⟧T A)
appP pf-K1      pa = p-Unit
appP pf-Id      pa = pa
appP (pf-⊕ p q) pa = p-+ (appP p pa) (appP q pa)
appP (pf-⊗ p q) pa = p-* (appP p pa) (appP q pa)

appP-coh : ∀ {F A} (pf : PortableF F) (pa : PortableT A) →
           ⌊ appP pf pa ⌋ᵀ ≡ N.⟦ ⌊ pf ⌋ᶠ ⟧F ⌊ pa ⌋ᵀ
appP-coh pf-K1      pa = refl
appP-coh pf-Id      pa = refl
appP-coh (pf-⊕ p q) pa = cong₂ N._+_ (appP-coh p pa) (appP-coh q pa)
appP-coh (pf-⊗ p q) pa = cong₂ N._*_ (appP-coh p pa) (appP-coh q pa)

------------------------------------------------------------------------
-- 4. ★ THE GAP, BOTH WAYS.
--
-- (a) SOURCE → TARGET.  `ν-type`, `Int`, `Float`, `Str`, `Buffer` have no
--     `PortableT` clause because `Ty = Void | Unit | _*_ | _+_ | _⇒_ | μ_` has
--     nothing to map them to.  These are `()` because the predicate SAYS so —
--     the content is not the proof, it is that no clause could be added
--     without a new `Ty` constructor, i.e. without touching the TCB.
--
-- (b) TARGET → SOURCE.  `Kc` is unreachable.  THIS one is a theorem: no
--     well-formed real functor translates to a `Kc`, because `WellFormedF`
--     admits `K A` only for base `A`, and `Kc` wants a code.
------------------------------------------------------------------------

ν-not-portable : ∀ {F} → ¬ (PortableT (T.ν-type F))
ν-not-portable ()

Int-not-portable : ¬ (PortableT T.Int)
Int-not-portable ()

Buffer-not-portable : ¬ (PortableT T.Buffer)
Buffer-not-portable ()

-- ★ the other direction: `Func`'s code-constant has no well-formed preimage.
Kc-unreachable : ∀ {F} (pf : PortableF F) {G : N.Func} → ¬ (⌊ pf ⌋ᶠ ≡ N.Kc G)
Kc-unreachable pf-K1      ()
Kc-unreachable pf-Id      ()
Kc-unreachable (pf-⊕ p q) ()
Kc-unreachable (pf-⊗ p q) ()

-- ★ (c) THE CONTAINMENT, which makes (a) and (b) precise.  Everything the port
-- accepts, the real compiler already accepts: `PortableF ⊆ WellFormedF`.  So
-- the port is SOUND with respect to the real well-formedness discipline and
-- never has to widen it.
portable→wf : ∀ {F} → PortableF F → TR.WellFormedF F
portable→wf pf-K1      = TR.wf-K TR.base-Unit
portable→wf pf-Id      = TR.wf-Id
portable→wf (pf-⊕ p q) = TR.wf-Sum (portable→wf p) (portable→wf q)
portable→wf (pf-⊗ p q) = TR.wf-Prod (portable→wf p) (portable→wf q)

-- …and the containment is STRICT: `K Int` is well-formed and not portable.
-- That is the gap of §4(a), stated as a proper inclusion rather than a list.
wf-not-portable : TR.WellFormedF (T.K T.Int)
wf-not-portable = TR.wf-K TR.base-Int

K-Int-not-portable : ¬ (PortableF (T.K T.Int))
K-Int-not-portable ()

-- …and it is not vacuous — `Kc` really is a `Func`, and really does denote a
-- type the linear core can talk about.  So the target has expressive power the
-- port cannot reach, which is the half of the mismatch PLAN §8 did not record.
Kc-inhabited : N.Func
Kc-inhabited = N.Kc (N.One N.⊕ N.Id)

------------------------------------------------------------------------
-- 5. WITNESSES — the coverage table, checked.
------------------------------------------------------------------------

-- ✅ `Nat = μ (K Unit ⊕ Id)` ports, and to exactly what it should.
natF-portable : PortableF T.NatF
natF-portable = pf-⊕ pf-K1 pf-Id

nat-ports : ⌊ p-μ natF-portable ⌋ᵀ ≡ (N.μ (N.One N.⊕ N.Id))
nat-ports = refl

-- ✅ `Tree Unit = μ (K Unit ⊕ Id ⊗ Id)` ports — branching is no obstacle.
treeF-Unit-portable : PortableF (T.TreeF T.Unit)
treeF-Unit-portable = pf-⊕ pf-K1 (pf-⊗ pf-Id pf-Id)

-- ❌ `List Int` does NOT, and the reason is the ELEMENT, not the list: `K Int`
-- is well-formed on the real side (`Int` is a base type) and has no `Func`
-- counterpart.  This is the practically important case — `List Int` is what a
-- real program uses, and it is out until `Ty` gains base types.
listF-Int-not-portable : ¬ (PortableF (T.ListF T.Int))
listF-Int-not-portable (pf-⊕ _ (pf-⊗ () _))

-- ❌ and a stream — the case W0e paid for — is out for the OTHER reason.
streamF-Unit-portable : PortableF (T.ListF T.Unit)
streamF-Unit-portable = pf-⊕ pf-K1 (pf-⊗ pf-K1 pf-Id)

stream-not-portable : ¬ (PortableT (T.ν-type (T.ListF T.Unit)))
stream-not-portable ()

-- ⚠ READ THOSE TWO TOGETHER.  The functor of a `Unit`-stream IS portable; it
-- is `ν-type` applied to it that is not.  So W0e's result is not what blocks
-- codata here — `SpikeLinNu` shows the semantics works — the block is purely
-- that `Ty` has no `ν` constructor to be the target of the translation.

------------------------------------------------------------------------
-- 6. THE REMAINING OBLIGATION, stated precisely.
--
-- With §3 in hand the morphism port is mechanical for the covered fragment:
--
--     ⌈_⌉ : ∀ {A B} (pa : PortableT A) (pb : PortableT B) →
--           LinearIR → IR A B → LTm ⌊ pa ⌋ᵀ ⌊ pb ⌋ᵀ
--
-- with `In`/`out-μ`/`Cata` landing on `lIn`/`lcata` through `appP-coh`,
-- `⟨_,_⟩`/`fst`/`snd` through `NbEPLinFox`, `curry`/`apply` through W0's
-- `lcurry`/`leval`, and `Para` carried across `ω`-graded per PLAN §8.1(2).
--
-- ⚠ IT SHOULD NOT BE WRITTEN YET, and the reason is §4 rather than difficulty.
-- The fragment it would cover — no `ν`, no `Int`/`Float`/`Str`/`Buffer`, hence
-- no `const`, hence no `SigOp` — is NARROWER THAN WHAT W0e ALREADY JUSTIFIES,
-- so writing it now would bank a result strictly weaker than the theory in
-- hand and would have to be redone the moment `Ty` grows.  The decision that
-- gates it is an architecture question, not a proof question:
--
--   OPTION A — extend `normalizer.Syntax.Types.Ty` with `ν`, base types, and
--     whatever else the port needs.  REJECTED on measurement: ten of the
--     eleven `Ty`-matching modules are in `normalizer/TCB0/`.
--
--   OPTION B — give the linear core its OWN object language (`SpikeLinNu`'s
--     `NTy` grown up), with `LTm`'s generators re-declared over it and a
--     conservative-extension theorem back to `Ty`.  Costs a re-declaration of
--     the core plus three structural inductions (`DupFree`, `Lᶜ`,
--     `dyn-linear`) — but it is POC-local and touches no TCB.  This is the
--     recommendation, and it is what "consolidating `SpikeLinNu`" has to mean.
--
--   OPTION C — port only what fits today and accept the narrow fragment.
--     Cheapest, and strictly dominated: §5's `listF-Int-not-portable` shows it
--     excludes `List Int`.
--
-- Option B also subsumes the W0e consolidation, which is why the two items
-- should be done as ONE piece of work rather than in sequence.
------------------------------------------------------------------------
