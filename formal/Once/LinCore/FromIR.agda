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
open import Data.Product using (Σ; _,_; _×_)
import Data.Maybe
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
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
-- (on the decisions as master's `tableEnv-at` takes them, so the two reduce
-- together)
extend-at : ∀ {Γ} g (rs : Resolver Γ) (e : IRFun) f A B
          → Dec (fname e ≡ f) → Dec (fdom e ≡ A) → Dec (fcod e ≡ B)
          → Maybe (Hit (Γ ▸ sg once g One ⟪ fdom e ⟫ ⟪ fcod e ⟫) ⟪ A ⟫ ⟪ B ⟫)
extend-at g rs e f A B (yes _) (yes p)    (yes q)    =
  just (subst₂ (λ X Y → Hit (_ ▸ sg once g One ⟪ fdom e ⟫ ⟪ fcod e ⟫) ⟪ X ⟫ ⟪ Y ⟫) p q (hit g here))
extend-at g rs e f A B (yes _) (yes _)    (no _)     = Data.Maybe.map weaken (rs f A B)
extend-at g rs e f A B (yes _) (no _)     _          = Data.Maybe.map weaken (rs f A B)
extend-at g rs e f A B (no _)  _          _          = Data.Maybe.map weaken (rs f A B)

extend : ∀ {Γ} g (rs : Resolver Γ) (e : IRFun) → Resolver (Γ ▸ sg once g One ⟪ fdom e ⟫ ⟪ fcod e ⟫)
extend g rs e f A B = extend-at g rs e f A B (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B)

entry-at : ∀ {Γ} → P.Prog Γ → Resolver Γ → (e : IRFun) (b : P.IR Γ ⟪ fdom e ⟫ ⟪ fcod e ⟫) → Maybe (P.BlkIR Γ b) → TrProg
entry-at P rs e b (just φ) = trProg (P P.▹ b ∣ φ)  (extend act rs e)
entry-at P rs e b nothing  = trProg (P P.▹ b ∣ tt) (extend eff rs e)

entry : ∀ {Γ} → P.Prog Γ → Resolver Γ → (e : IRFun) → P.IR Γ ⟪ fdom e ⟫ ⟪ fcod e ⟫ → TrProg
entry P rs e b = entry-at P rs e b (blk? b)

trTable : List IRFun → Maybe TrProg
trTable []       = just (trProg P.ε (λ _ _ _ → nothing))
trTable (e ∷ es) = trTable es >>= λ t → trI (rs t) (fbody e) >>= λ b → just (entry (prog t) (rs t) e b)

------------------------------------------------------------------------
-- 7. THE TRANSLATION AS A RELATION: `Tr rs ir c`, `c` translates `ir`
-- (what `trI` gives, `trI-Tr`), for the proof by induction on it.
------------------------------------------------------------------------

module _ {Γ : Cx} (rs : Resolver Γ) where

  data Tr : ∀ {A B} → M.IR A B → P.IR Γ ⟪ A ⟫ ⟪ B ⟫ → Set where
    t-id    : ∀ {A} → Tr (M.id {A}) P.id
    t-∘     : ∀ {A B C} {g : M.IR B C} {f : M.IR A B} {g′ f′} → Tr g g′ → Tr f f′ → Tr (g M.∘ f) (g′ P.∘ f′)
    t-pair  : ∀ {A B C} {f : M.IR A B} {g : M.IR A C} {f′ g′} → Tr f f′ → Tr g g′ → Tr M.⟨ f , g ⟩ P.⟨ f′ , g′ ⟩
    t-fst   : ∀ {A B} → Tr (M.fst {A} {B}) P.fst
    t-snd   : ∀ {A B} → Tr (M.snd {A} {B}) P.snd
    t-inl   : ∀ {A B} → Tr (M.inl {A} {B}) P.inl
    t-inr   : ∀ {A B} → Tr (M.inr {A} {B}) P.inr
    t-case  : ∀ {A B C} {f : M.IR A C} {g : M.IR B C} {f′ g′} → Tr f f′ → Tr g g′ → Tr (M.case f g) (P.case f′ g′)
    t-term  : ∀ {A} → Tr (M.terminal {A}) P.terminal
    t-init  : ∀ {A} → Tr (M.initial {A}) P.initial
    t-curry : ∀ {A B C π} {f : M.IR (A * B) C} {f′ γ} → Tr f f′ → Tr (M.curry {π = π} f) (P.curry (grade π) f′ γ)
    t-apply : ∀ {A B π} → Tr (M.apply {A} {B} {π}) (P.apply {g = grade π})
    t-In    : ∀ {F} (wf : WellFormedFI F) →
              Tr (M.In wf) (subst (λ X → P.IR Γ X ⟪ μ-type F ⟫) (sym (⟪⟫-TI wf (μ-type F))) (P.In (lf F)))
    t-out   : ∀ {F} (wf : WellFormedFI F) →
              Tr (M.out-μ wf) (subst (λ X → P.IR Γ ⟪ μ-type F ⟫ X) (sym (⟪⟫-TI wf (μ-type F))) (P.out-μ (lf F)))
    t-cata  : ∀ {F} (wf : WellFormedFI F) {E A} {alg : M.IR (E * ⟦ F ⟧TI A) A} {a′} → Tr alg a′ →
              Tr (M.Cata wf alg) (P.Cata (lf F) (subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t X) ⟪ A ⟫) (⟪⟫-TI wf A) a′))
    t-Out   : ∀ {F} (wf : WellFormedFI F) →
              Tr (M.Out wf) (subst (λ X → P.IR Γ ⟪ ν-type F ⟫ X) (sym (⟪⟫-TI wf (ν-type F))) (P.Out (lf F)))
    t-inν   : ∀ {F} (wf : WellFormedFI F) →
              Tr (M.in-ν wf) (subst (λ X → P.IR Γ X ⟪ ν-type F ⟫) (sym (⟪⟫-TI wf (ν-type F))) (P.in-ν (lf F)))
    t-ana   : ∀ {F} (wf : WellFormedFI F) {E A} {c : M.IR (E * A) (⟦ F ⟧TI A)} {c′} → Tr c c′ → ∀ φ →
              Tr (M.Ana wf c) (P.Ana (lf F) (subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t ⟪ A ⟫) X) (⟪⟫-TI wf A) c′) φ)
    t-iter  : ∀ {E A B} {b : M.IR (E * A) (B + A)} {b′} → Tr b b′ → ∀ φ → Tr (M.Iter b) (P.Iter b′ φ)
    t-int   : ∀ {v} → Tr (M.const fits-int v) (P.const {b = int} (OnceWord.Width.fromℤ (int-bits fmt) v))
    t-float : ∀ {v} → Tr (M.const fits-float v) (P.const {b = float} (round (float-format fmt) v))
    t-op    : ∀ {A B} (si : SigOpInfo A B) →
              Tr (M.SigOp si) (subst₂ (P.IR Γ) (sym (⟪⌊⌋⟫-flat (SigOpInfo.baseA si))) (sym (⟪⌊⌋⟫-flat (SigOpInfo.conB si)))
                                      (P.SigOp (sig si)))
    t-hit   : ∀ {A B f g l} {p : Γ ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫} → rs f A B ≡ just (hit g p) → Tr (M.Call f) (P.Call p)
    t-miss  : ∀ {A B f} → rs f A B ≡ nothing → Tr (M.Call {A} {B} f) unlinked

  -- what `trI` gives, it translates
  private
    bind-just : ∀ {X Y : Set} {m : Maybe X} {k : X → Maybe Y} {y} → (m >>= k) ≡ just y
              → Σ X (λ x → m ≡ just x × k x ≡ just y)
    bind-just {m = just x} e = x , refl , e

  trI-Tr : ∀ {A B} (ir : M.IR A B) {c} → trI rs ir ≡ just c → Tr ir c
  trI-Tr M.id refl = t-id
  trI-Tr (g M.∘ f) e with bind-just {m = trI rs g} e
  ... | g′ , eg , e₁ with bind-just {m = trI rs f} e₁
  ...   | f′ , ef , refl = t-∘ (trI-Tr g eg) (trI-Tr f ef)
  trI-Tr M.⟨ f , g ⟩ e with bind-just {m = trI rs f} e
  ... | f′ , ef , e₁ with bind-just {m = trI rs g} e₁
  ...   | g′ , eg , refl = t-pair (trI-Tr f ef) (trI-Tr g eg)
  trI-Tr M.fst refl = t-fst
  trI-Tr M.snd refl = t-snd
  trI-Tr M.inl refl = t-inl
  trI-Tr M.inr refl = t-inr
  trI-Tr (M.case f g) e with bind-just {m = trI rs f} e
  ... | f′ , ef , e₁ with bind-just {m = trI rs g} e₁
  ...   | g′ , eg , refl = t-case (trI-Tr f ef) (trI-Tr g eg)
  trI-Tr M.terminal refl = t-term
  trI-Tr M.initial refl = t-init
  trI-Tr (M.curry {π = π} f) e with bind-just {m = trI rs f} e
  ... | f′ , ef , e₁ with bind-just {m = gd? (grade π) f′} e₁
  ...   | γ , _ , refl = t-curry (trI-Tr f ef)
  trI-Tr M.apply refl = t-apply
  trI-Tr (M.In wf) refl = t-In wf
  trI-Tr (M.out-μ wf) refl = t-out wf
  trI-Tr (M.Cata wf alg) e with bind-just {m = trI rs alg} e
  ... | a′ , ea , refl = t-cata wf (trI-Tr alg ea)
  trI-Tr (M.Out wf) refl = t-Out wf
  trI-Tr (M.in-ν wf) refl = t-inν wf
  trI-Tr (M.Ana {F} wf {E} {A} c) e with bind-just {m = trI rs c} e
  ... | c′ , ec , e₁
      with bind-just {m = blk? (subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t ⟪ A ⟫) X) (⟪⟫-TI wf A) c′)}
                     {k = λ φ → just (P.Ana (lf F) (subst (λ X → P.IR Γ (⟪ E ⟫ ⊗t ⟪ A ⟫) X) (⟪⟫-TI wf A) c′) φ)} e₁
  ...   | φ , _ , refl = t-ana wf (trI-Tr c ec) φ
  trI-Tr (M.Iter b) e with bind-just {m = trI rs b} e
  ... | b′ , eb , e₁ with bind-just {m = blk? b′} e₁
  ...   | φ , _ , refl = t-iter (trI-Tr b eb) φ
  trI-Tr (M.const fits-int v) refl = t-int
  trI-Tr (M.const fits-float v) refl = t-float
  trI-Tr (M.SigOp si) refl = t-op si
  trI-Tr (M.Call {A} {B} f) e with rs f A B in eq
  trI-Tr (M.Call f) refl | just (hit g p) = t-hit eq
  trI-Tr (M.Call f) refl | nothing        = t-miss eq
