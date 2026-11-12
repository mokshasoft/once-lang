-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.FromIR — plan 0.146 B1.3: master's IR into the linear core.
--
-- Master's IR (`Once.IR`) is translated into the RESOLVED, GRADED IR of
-- `Once.LinCore.Pass` (its definitions are labels over the earlier ones, its
-- blocks carry their grade judgments), which `Pass.tr` compiles into the core
-- and `Pass.pass-ok` proves. This module is the first half: the types.
--
--   * `⟪_⟫ : IRTy → LTy`. An arrow keeps its purity as the core's grade (D413:
--     `pure` and `act` are both a finite block); the IR's arrows are many-use.
--   * `lf : IRFunctor → LF`. A constant of a base type is a code built from
--     `Kone`, `Kzero`, `Kb` (`K (A * B)` is `K A ⊗ K B`), so `⟪ ⟦ F ⟧ X ⟫` is
--     `LF∙ (lf F) ⟪ X ⟫` for every well-formed functor (`⟪⟫-TI`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.Spec.Grade using (Purity; fin; eff)
open import Once.IRTy
  using (IRTy; IRFunctor; K; Id; Unit; Void; _*_; _+_; _⇛[_]_; μ-type; ν-type; Int; Float;
         ⟦_⟧TI; IsBaseTypeI; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum;
         WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod)
  renaming (_⊕_ to _⊕ᴵ_; _⊗_ to _⊗ᴵ_)
open import Once.IRTy using (⌊_⌋)
import Once.Spec.Type as ST
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
import Data.Maybe
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
open import Once.IRTy using (_≟IRTy_; fits-int; fits-float)
import Once.IR as M
open import Once.Spec.Name using (CanonicalName; gen)
open import Once.CanonicalName using (_≟ᶜ_)
open import Once.Spec.Numerics using (module TargetNum)
open TargetNum using (int-bits; float-format)
open import Once.Spec.Float.Decimal using (round)
import Once.Spec.Word as OnceWord
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo; mk-info'; haltsV)
open import Once.Denotation.Program using (IRFun; module IRFun)
open IRFun using (fname; fdom; fcod; fbody)
import Once.LinCore.Pass

module Once.LinCore.FromIR (fmt : TargetNum) (ans : FFIAnswers) where

open import Once.LinCore.NbEPLinCore fmt ans
module P = Once.LinCore.Pass fmt ans

------------------------------------------------------------------------
-- 1. THE TYPES.
------------------------------------------------------------------------

-- an arrow's purity, as far as the core tells grades apart (D412: the Spec's
-- `pure` is the block with no event)
grade : Purity → Gr
grade (fin _) = act
grade eff     = eff

mutual
  ⟪_⟫ : IRTy → LTy
  ⟪ Unit ⟫         = One
  ⟪ Void ⟫         = Zero
  ⟪ A * B ⟫        = ⟪ A ⟫ ⊗t ⟪ B ⟫
  ⟪ A + B ⟫        = ⟪ A ⟫ ⊕t ⟪ B ⟫
  ⟪ A ⇛[ π ] B ⟫   = Fn many (grade π) ⟪ A ⟫ ⟪ B ⟫
  ⟪ μ-type F ⟫     = μt (lf F)
  ⟪ ν-type F ⟫     = Nu (lf F)
  ⟪ Int ⟫          = Bt int
  ⟪ Float ⟫        = Bt float

  lf : IRFunctor → LF
  lf (K A)     = lfK A
  lf Id        = Idf
  lf (F ⊕ᴵ G)  = lf F ⊕f lf G
  lf (F ⊗ᴵ G)  = lf F ⊗f lf G

  -- a functor's constant. `WellFormedFI` admits only base types; an arrow or
  -- a ν has no code (the Spec's functor constants are base, `WFFun`), so they
  -- are given `Kzero`, which no well-formed functor reaches.
  lfK : IRTy → LF
  lfK Unit             = Kone
  lfK Void             = Kzero
  lfK Int              = Kb int
  lfK Float            = Kb float
  lfK (A * B)          = lfK A ⊗f lfK B
  lfK (A + B)          = lfK A ⊕f lfK B
  lfK (μ-type G)       = Kμ (lf G)
  lfK (_ ⇛[ _ ] _)     = Kzero
  lfK (ν-type _)       = Kzero

-- a base constant's code means the type, at every carrier
⟪⟫-K : ∀ {A} → IsBaseTypeI A → ∀ X → LF∙ (lfK A) X ≡ ⟪ A ⟫
⟪⟫-K base-Unit         X = refl
⟪⟫-K base-Void         X = refl
⟪⟫-K base-Int          X = refl
⟪⟫-K base-Float        X = refl
⟪⟫-K (base-Prod a b)   X = cong₂ _⊗t_ (⟪⟫-K a X) (⟪⟫-K b X)
⟪⟫-K (base-Sum a b)    X = cong₂ _⊕t_ (⟪⟫-K a X) (⟪⟫-K b X)

-- ★ a well-formed functor's layer translates as its code's layer
⟪⟫-TI : ∀ {F} → WellFormedFI F → ∀ X → ⟪ ⟦ F ⟧TI X ⟫ ≡ LF∙ (lf F) ⟪ X ⟫
⟪⟫-TI (wf-K b)      X = Relation.Binary.PropositionalEquality.sym (⟪⟫-K b ⟪ X ⟫)
⟪⟫-TI wf-Id         X = refl
⟪⟫-TI (wf-Sum f g)  X = cong₂ _⊕t_ (⟪⟫-TI f X) (⟪⟫-TI g X)
⟪⟫-TI (wf-Prod f g) X = cong₂ _⊗t_ (⟪⟫-TI f X) (⟪⟫-TI g X)

------------------------------------------------------------------------
-- 2. AN OP'S TYPES: a base type's IR object is its flat type.
------------------------------------------------------------------------

⟪⌊⌋⟫-flat : ∀ {A : ST.Type} (b : ST.Base ST.∅ₖ A) → ⟪ ⌊ A ⌋ ⟫ ≡ ⌜ flat b ⌝
⟪⌊⌋⟫-flat (ST.b-var {i = ()} _)
⟪⌊⌋⟫-flat ST.b-Unit    = refl
⟪⌊⌋⟫-flat ST.b-Void    = refl
⟪⌊⌋⟫-flat ST.b-Int     = refl
⟪⌊⌋⟫-flat ST.b-Float   = refl
⟪⌊⌋⟫-flat (ST.b-* a b) = cong₂ _⊗t_ (⟪⌊⌋⟫-flat a) (⟪⌊⌋⟫-flat b)
⟪⌊⌋⟫-flat (ST.b-+ a b) = cong₂ _⊕t_ (⟪⌊⌋⟫-flat a) (⟪⌊⌋⟫-flat b)

------------------------------------------------------------------------
-- 3. THE GRADE JUDGMENT, DECIDED on the resolved IR: an `act` arrow's body,
-- a coalgebra and a round must be blocks (D412). The Spec types them at
-- `act`; a program the elaborator emits is owed to pass.
------------------------------------------------------------------------

blk? : ∀ {Γ A B} (f : P.IR Γ A B) → Maybe (P.BlkIR Γ f)
blk? P.id                 = just P.i-id
blk? (g P.∘ f)            = blk? g >>= λ bg → blk? f >>= λ bf → just (P.i-∘ bg bf)
blk? P.⟨ f , g ⟩          = blk? f >>= λ bf → blk? g >>= λ bg → just (P.i-pair bf bg)
blk? P.fst                = just P.i-fst
blk? P.snd                = just P.i-snd
blk? P.inl                = just P.i-inl
blk? P.inr                = just P.i-inr
blk? (P.case f g)         = blk? f >>= λ bf → blk? g >>= λ bg → just (P.i-case bf bg)
blk? P.terminal           = just P.i-term
blk? P.initial            = just P.i-init
blk? (P.curry g f γ)      = just P.i-curry
blk? (P.apply {act})      = just P.i-apply
blk? (P.apply {eff})      = nothing
blk? (P.In F)             = just P.i-In
blk? (P.out-μ F)          = just P.i-out
blk? (P.Cata F alg)       = blk? alg >>= λ b → just (P.i-cata b)
blk? (P.Ana F c φ)        = just P.i-ana
blk? (P.Out F)            = just P.i-Out
blk? (P.in-ν F)           = just P.i-inν
blk? (P.Iter body φ)      = nothing
blk? (P.const v)          = just P.i-const
blk? (P.SigOp s)          = just P.i-op
blk? (P.Call {g = act} p) = just P.i-call
blk? (P.Call {g = eff} p) = nothing

-- a body at an arrow's grade
gd? : ∀ {Γ A B} g (f : P.IR Γ A B) → Maybe (P.GdIR Γ g f)
gd? act f = blk? f
gd? eff f = just tt

------------------------------------------------------------------------
-- 4. CALLS: a name at its types, resolved to a label as `tableCalls` finds
-- it (the latest definition first); an unlinked call halts as master's
-- `unlinkedT` does.
------------------------------------------------------------------------

record Hit (Γ : Cx) (A B : LTy) : Set where
  constructor hit
  field
    {l} : ℕ
    g   : Gr
    p   : Γ ∋[ l ] sg once g One A B

Resolver : Cx → Set
Resolver Γ = CanonicalName → (A B : IRTy) → Maybe (Hit Γ ⟪ A ⟫ ⟪ B ⟫)

-- `unlinkedT`: the op that halts as `gen "unlinked"` on `tt`
unlinked-i : SigOpInfo ST.Unit ST.Void
unlinked-i = mk-info' (gen "unlinked") (haltsV refl) ST.b-Unit ST.b-Void

unlinked : ∀ {Γ A B} → P.IR Γ ⟪ A ⟫ ⟪ B ⟫
unlinked = P.initial P.∘ (P.SigOp (sig unlinked-i) P.∘ P.terminal)

------------------------------------------------------------------------
-- 5. THE TERMS: clause for clause, over `⟪_⟫`. It fails only where a grade
-- judgment does (`blk?`).
------------------------------------------------------------------------

module _ {Γ : Cx} (rs : Resolver Γ) where

  trI : ∀ {A B} → M.IR A B → Maybe (P.IR Γ ⟪ A ⟫ ⟪ B ⟫)
  trI M.id                = just P.id
  trI (g M.∘ f)           = trI g >>= λ g′ → trI f >>= λ f′ → just (g′ P.∘ f′)
  trI M.⟨ f , g ⟩         = trI f >>= λ f′ → trI g >>= λ g′ → just P.⟨ f′ , g′ ⟩
  trI M.fst               = just P.fst
  trI M.snd               = just P.snd
  trI M.inl               = just P.inl
  trI M.inr               = just P.inr
  trI (M.case f g)        = trI f >>= λ f′ → trI g >>= λ g′ → just (P.case f′ g′)
  trI M.terminal          = just P.terminal
  trI M.initial           = just P.initial
  trI (M.curry {π = π} f) = trI f >>= λ f′ → gd? (grade π) f′ >>= λ γ → just (P.curry (grade π) f′ γ)
  trI (M.apply {π = π})   = just (P.apply {g = grade π})
  trI (M.In {F} wf)       =
    just (subst (λ X → P.IR Γ X ⟪ μ-type F ⟫) (sym (⟪⟫-TI wf (μ-type F))) (P.In (lf F)))
  trI (M.out-μ {F} wf)    =
    just (subst (λ X → P.IR Γ ⟪ μ-type F ⟫ X) (sym (⟪⟫-TI wf (μ-type F))) (P.out-μ (lf F)))
  trI (M.Cata {F} wf {E} {A} alg) = trI alg >>= λ a′ →
    just (P.Cata (lf F) (subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t X) ⟪ A ⟫) (⟪⟫-TI wf A) a′))
  trI (M.Out {F} wf)      =
    just (subst (λ X → P.IR Γ ⟪ ν-type F ⟫ X) (sym (⟪⟫-TI wf (ν-type F))) (P.Out (lf F)))
  trI (M.in-ν {F} wf)     =
    just (subst (λ X → P.IR Γ X ⟪ ν-type F ⟫) (sym (⟪⟫-TI wf (ν-type F))) (P.in-ν (lf F)))
  trI (M.Ana {F} wf {E} {A} c) = trI c >>= λ c′ →
    let c″ = subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t ⟪ A ⟫) X) (⟪⟫-TI wf A) c′
    in blk? c″ >>= λ φ → just (P.Ana (lf F) c″ φ)
  trI (M.Iter b)          = trI b >>= λ b′ → blk? b′ >>= λ φ → just (P.Iter b′ φ)
  trI (M.const fits-int v)   = just (P.const {b = int} (OnceWord.Width.fromℤ (int-bits fmt) v))
  trI (M.const fits-float v) = just (P.const {b = float} (round (float-format fmt) v))
  trI (M.SigOp {A} {B} si)   =
    just (subst₂ (P.IR Γ) (sym (⟪⌊⌋⟫-flat (SigOpInfo.baseA si))) (sym (⟪⌊⌋⟫-flat (SigOpInfo.conB si)))
                 (P.SigOp (sig si)))
  trI (M.Call {A} {B} f) with rs f A B
  ... | just (hit g p) = just (P.Call p)
  ... | nothing        = just unlinked

------------------------------------------------------------------------
-- 6. THE TABLE: from its earliest definition (the list's last), each body
-- over the ones before it; a definition is `act` when its body is a block.
------------------------------------------------------------------------

record TrProg : Set where
  constructor trProg
  field
    {Γ}  : Cx
    prog : P.Prog Γ
    rs   : Resolver Γ
open TrProg

weaken : ∀ {Γ τ A B} → Hit Γ A B → Hit (Γ ▸ τ) A B
weaken (hit g p) = hit g (there p)

-- one more definition: its label answers its name, the rest as before
extend : ∀ {Γ} g (rs : Resolver Γ) (e : IRFun) → Resolver (Γ ▸ sg once g One ⟪ fdom e ⟫ ⟪ fcod e ⟫)
extend g rs e f A B with fname e ≟ᶜ f | fdom e ≟IRTy A | fcod e ≟IRTy B
... | yes _ | yes refl | yes refl = just (hit g here)
{-# CATCHALL #-}
... | _     | _        | _        = Data.Maybe.map weaken (rs f A B)

entry : ∀ {Γ} → P.Prog Γ → Resolver Γ → (e : IRFun) → P.IR Γ ⟪ fdom e ⟫ ⟪ fcod e ⟫ → TrProg
entry P rs e b with blk? b
... | just φ  = trProg (P P.▹ b ∣ φ)  (extend act rs e)
... | nothing = trProg (P P.▹ b ∣ tt) (extend eff rs e)

trTable : List IRFun → Maybe TrProg
trTable []       = just (trProg P.ε (λ _ _ _ → nothing))
trTable (e ∷ es) = trTable es >>= λ t → trI (rs t) (fbody e) >>= λ b → just (entry (prog t) (rs t) e b)
