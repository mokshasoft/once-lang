-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.PassTr — plan 0.146 A15 (D426): THE PASS'S SYNTAX. A copy of
-- `Once.IR`'s constructors over the core's types (`IR`, their grades `BlkIR`,
-- `GdIR`), a program of them (`Prog`), and the translation into the core
-- (`tr`, `trP`). D457: at the target's numerics alone; what they mean and the
-- theorem that the translation means the same are `Pass`'.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂; subst)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Once.Spec.Numerics using (TargetNum)
open import Once.LinCore.Flat using (Base; FTy; funit; fvoid; fw; _f*_; _f+_)

module Once.LinCore.PassTr (fmt : TargetNum) where

open import Once.LinCore.Core fmt

------------------------------------------------------------------------
-- 1. THE IR: master's constructors, over the core's types.
------------------------------------------------------------------------

-- ★ The Spec's grades (`⊢iter`, `⊢lam`, `⊢unfold`): a loop's round, an `act`
-- arrow's body and a coalgebra are finite blocks, here as on the core
-- (`Blk`, `Gd`).
-- ★ `Γ`: the program's definitions before this one (the Spec's `Program`: a
-- definition refers only to EARLIER ones, so there is no recursion), each a
-- label of the core with nothing in its environment.
module _ (Γ : Cx) where
  infixr 9 _∘_
  data IR : LTy → LTy → Set
  data BlkIR : ∀ {A B} → IR A B → Set
  -- a body at its arrow's grade
  GdIR : ∀ {A B} → Gr → IR A B → Set

  data IR where
    id      : ∀ {A} → IR A A
    _∘_      : ∀ {A B C} → IR B C → IR A B → IR A C
    ⟨_,_⟩    : ∀ {A B C} → IR A B → IR A C → IR A (B ⊗t C)
    fst      : ∀ {A B} → IR (A ⊗t B) A
    snd      : ∀ {A B} → IR (A ⊗t B) B
    inl      : ∀ {A B} → IR A (A ⊕t B)
    inr      : ∀ {A B} → IR B (A ⊕t B)
    case     : ∀ {A B C} → IR A C → IR B C → IR (A ⊕t B) C
    terminal : ∀ {A} → IR A One
    initial  : ∀ {A} → IR Zero A
    -- ★ the exponential (the IR's `A ⇛ B`, graded as the Spec's arrow; the
    -- IR's arrows are many-use)
    curry    : ∀ {A B C} g (f : IR (A ⊗t B) C) → GdIR g f → IR A (Fn many g B C)
    apply    : ∀ {g A B} → IR (Fn many g A B ⊗t A) B
    In       : ∀ F → IR (LF∙ F (μt F)) (μt F)
    out-μ    : ∀ F → IR (μt F) (LF∙ F (μt F))
    -- the parameterised fold (D131): the algebra reads a fixed environment
    Cata     : ∀ F {E A} → IR (E ⊗t LF∙ F A) A → IR (E ⊗t μt F) A
    -- ★ the parameterised unfold (D273): the coalgebra reads a fixed
    -- environment at every observation; the observation; Lambek's inverse
    Ana      : ∀ F {E A} (c : IR (E ⊗t A) (LF∙ F A)) → BlkIR c → IR (E ⊗t A) (Nu F)
    Out      : ∀ F → IR (Nu F) (LF∙ F (Nu F))
    in-ν     : ∀ F → IR (LF∙ F (Nu F)) (Nu F)
    -- the loop (D317): the round reads a fixed environment and the state
    Iter     : ∀ {E A B} (body : IR (E ⊗t A) (B ⊕t A)) → BlkIR body → IR (E ⊗t A) B
    const    : ∀ {b} → Lit b → IR One (Bt b)
    SigOp    : (s : Sig) → IR ⌜ sdom s ⌝ ⌜ scod s ⌝
    -- ★ D245: a direct call of an earlier definition of the program (the D064
    -- direct-call ABI, `call once_f`)
    Call     : ∀ {l g A B} → Γ ∋[ l ] sg once g One A B → IR A B

  -- a finite block: no loop inside
  data BlkIR where
    i-id    : ∀ {A} → BlkIR (id {A})
    i-∘     : ∀ {A B C} {g : IR B C} {f : IR A B} → BlkIR g → BlkIR f → BlkIR (g ∘ f)
    i-pair  : ∀ {A B C} {f : IR A B} {g : IR A C} → BlkIR f → BlkIR g → BlkIR ⟨ f , g ⟩
    i-fst   : ∀ {A B} → BlkIR (fst {A} {B})
    i-snd   : ∀ {A B} → BlkIR (snd {A} {B})
    i-inl   : ∀ {A B} → BlkIR (inl {A} {B})
    i-inr   : ∀ {A B} → BlkIR (inr {A} {B})
    i-case  : ∀ {A B C} {f : IR A C} {g : IR B C} → BlkIR f → BlkIR g → BlkIR (case f g)
    i-term  : ∀ {A} → BlkIR (terminal {A})
    i-init  : ∀ {A} → BlkIR (initial {A})
    i-curry : ∀ {A B C g} {f : IR (A ⊗t B) C} {γ : GdIR g f} → BlkIR (curry g f γ)
    i-apply : ∀ {A B} → BlkIR (apply {act} {A} {B})
    i-In    : ∀ {F} → BlkIR (In F)
    i-out   : ∀ {F} → BlkIR (out-μ F)
    i-cata  : ∀ {F E A} {alg : IR (E ⊗t LF∙ F A) A} → BlkIR alg → BlkIR (Cata F alg)
    i-ana   : ∀ {F E A} {c : IR (E ⊗t A) (LF∙ F A)} {φ : BlkIR c} → BlkIR (Ana F c φ)
    i-Out   : ∀ {F} → BlkIR (Out F)
    i-inν   : ∀ {F} → BlkIR (in-ν F)
    i-const : ∀ {b} {v : Lit b} → BlkIR (const v)
    i-op    : ∀ {s} → BlkIR (SigOp s)
    -- a call of a definition of grade `act` is a block
    i-call  : ∀ {l A B} {p : Γ ∋[ l ] sg once act One A B} → BlkIR (Call p)

  GdIR act f = BlkIR f
  GdIR eff f = ⊤

------------------------------------------------------------------------
-- 3. THE TRANSLATION into the core (nothing lent; the program's earlier
-- definitions are the core's labels, `Γ` the same).
------------------------------------------------------------------------

-- drop the left of a pair
dropl : ∀ {Γ E A B} → Tm Γ E (A ⊗t B) B
dropl = lul ∘l (drop ⊗l lid)

k-dropl : ∀ {Γ E A B} → Blk (dropl {Γ} {E} {A} {B})
k-dropl = k-∘ k-lul (k-⊗ k-drop k-id)

-- a body that owns `E`, run where `E` is lent: copy it in
withE : ∀ {Γ E A B} → LTm Γ (E ⊗t A) B → Tm Γ (One ⊗t E) A B
withE b = blift b ∘l (bsnd bcopy ⊗l lid) ∘l lul⁻

k-withE : ∀ {Γ E A B} {b : LTm Γ (E ⊗t A) B} → Blk b → Blk (withE b)
k-withE β = k-∘ (k-lift β) (k-∘ (k-⊗ (k-snd k-copy) k-id) k-lul⁻)

-- the same, where `X` is all that is lent (a closure's environment)
copyIn : ∀ {Γ X A B} → LTm Γ (X ⊗t A) B → Tm Γ X A B
copyIn b = blift b ∘l (bcopy ⊗l lid) ∘l lul⁻

k-copyIn : ∀ {Γ X A B} {b : LTm Γ (X ⊗t A) B} → Blk b → Blk (copyIn b)
k-copyIn β = k-∘ (k-lift β) (k-∘ (k-⊗ k-copy k-id) k-lul⁻)

-- the functor's action on a step
mapL : ∀ {Γ E A B} G → Tm Γ E A B → Tm Γ E (LF∙ G A) (LF∙ G B)
mapL Idf      f = f
mapL Kone     f = lid
mapL Kzero    f = lid
mapL (Kb b)   f = lid
mapL (Kμ G)   f = lid
mapL (G ⊕f H) f = lcase (linl ∘l mapL G f) (linr ∘l mapL H f)
mapL (G ⊗f H) f = mapL G f ⊗l mapL H f

k-mapL : ∀ {Γ E A B} G {f : Tm Γ E A B} → Blk f → Blk (mapL G f)
k-mapL Idf      φ = φ
k-mapL Kone     φ = k-id
k-mapL Kzero    φ = k-id
k-mapL (Kb b)   φ = k-id
k-mapL (Kμ G)   φ = k-id
k-mapL (G ⊕f H) φ = k-case (k-∘ k-inl (k-mapL G φ)) (k-∘ k-inr (k-mapL H φ))
k-mapL (G ⊗f H) φ = k-⊗ (k-mapL G φ) (k-mapL H φ)

-- ★ Lambek's inverse as an unfold: the seeds are a layer still to be given
-- out, or a ν to observe. The layer is given out as it is; a ν is observed
-- once and its layer given out. (Observing the children while building the
-- ν would run their coalgebras early.)
InS : LF → LTy
InS F = LF∙ F (Nu F) ⊕t Nu F

inco : ∀ {Γ} F → Tm Γ One (InS F) (LF∙ F (InS F))
inco F = lcase (mapL F linr) (mapL F linr ∘l lout)

k-inco : ∀ {Γ} F → Blk (inco {Γ} F)
k-inco F = k-case (k-mapL F k-inr) (k-∘ (k-mapL F k-inr) k-nout)

tr : ∀ {Γ A B} → IR Γ A B → LTm Γ A B
-- a block translates to a block
tr-blk : ∀ {Γ A B} {f : IR Γ A B} → BlkIR Γ f → Blk (tr f)
-- a body at its grade, to the core's
tr-gd : ∀ g {Γ A B C} {f : IR Γ (A ⊗t B) C} → GdIR Γ g f → Gd g (copyIn (tr f))

tr id           = lid
tr (g ∘ f)      = tr g ∘l tr f
tr ⟨ f , g ⟩    = (tr f ⊗l tr g) ∘l dup
tr fst          = ρl ∘l (lid ⊗l drop)
tr snd          = dropl
tr inl          = linl
tr inr          = linr
tr (case f g)   = lcase (tr f) (tr g)
tr terminal     = drop
tr initial      = lzero
-- the environment moves into the closure's cell, lent to the body per call
tr (curry g f γ) = llamω (copyIn (tr f)) (tr-gd g γ)
-- the closure is applied while lent, then dropped (the IR's arrows are many-use)
tr apply        = dropl ∘l lend (bsnd bev)
tr (In F)       = lIn
tr (out-μ F)    = lOutμ
tr (Cata F alg) = dropl ∘l lend (lcata F (withE (tr alg)))
-- the environment moves into the coalgebra's cell, beside the seed
tr (Ana F c φ)  = lunf ∘l (llamω (copyIn (tr c)) (k-copyIn (tr-blk φ)) ⊗l lid)
tr (Out F)      = lout
tr (in-ν F)     = lunf ∘l (llamω (inco F) (k-inco F) ⊗l linl) ∘l lul⁻
tr (Iter body φ) = dropl ∘l lend (liter (withE (tr body)) (k-withE (tr-blk φ)))
tr (const v)    = lconst v
tr (SigOp s)    = lop s
-- the label's closure (its environment is `One`: no cell, no word), called
tr (Call p)     = lapp p ∘l (lclo Idf p ⊗l lid) ∘l lul⁻

tr-gd act φ = k-copyIn (tr-blk φ)
tr-gd eff _ = tt

tr-blk i-id         = k-id
tr-blk (i-∘ g f)    = k-∘ (tr-blk g) (tr-blk f)
tr-blk (i-pair f g) = k-∘ (k-⊗ (tr-blk f) (tr-blk g)) k-dup
tr-blk i-fst        = k-∘ k-ρ (k-⊗ k-id k-drop)
tr-blk i-snd        = k-dropl
tr-blk i-inl        = k-inl
tr-blk i-inr        = k-inr
tr-blk (i-case f g) = k-case (tr-blk f) (tr-blk g)
tr-blk i-term       = k-drop
tr-blk i-init       = k-zero
tr-blk i-curry      = k-lamω
tr-blk i-apply      = k-∘ k-dropl (k-lend (k-snd k-bev))
tr-blk i-In         = k-in
tr-blk i-out        = k-out
tr-blk (i-cata a)   = k-∘ k-dropl (k-lend (k-cata (k-withE (tr-blk a))))
tr-blk i-ana        = k-∘ k-unf (k-⊗ k-lamω k-id)
tr-blk i-Out        = k-nout
tr-blk i-inν        = k-∘ k-unf (k-∘ (k-⊗ k-lamω k-inl) k-lul⁻)
tr-blk i-const      = k-const
tr-blk i-op         = k-op
tr-blk i-call       = k-∘ k-app (k-∘ (k-⊗ k-clo k-id) k-lul⁻)

------------------------------------------------------------------------
-- 3½. ★ A PROGRAM: its definitions in order, each over the ones before
-- (the Spec's `Program`), and its meaning and translation built in order.
------------------------------------------------------------------------

infixl 4 _▹_∣_
data Prog : Cx → Set where
  ε     : Prog ε
  _▹_∣_ : ∀ {Γ g A B} → Prog Γ → (f : IR Γ A B) → GdIR Γ g f → Prog (Γ ▸ sg once g One A B)

-- each definition, a label whose body is its translation
tr-def : ∀ g {Γ A B} {f : IR Γ A B} → GdIR Γ g f → Gd g (tr f ∘l lul)
tr-def act φ = k-∘ (tr-blk φ) k-lul
tr-def eff _ = tt

trP : ∀ {Γ} → Prog Γ → Defs Γ
trP ε                       = ε
trP (_▹_∣_ {g = g} P f γ) = trP P ▸ b1 (tr f ∘l lul) (tr-def g γ)

