-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Pass — plan 0.146 A15 (D409): THE PASS.
--
-- A copy of `Once.IR`'s constructors, their meaning shaped as master's
-- `evalᴰ` (`Once.Denotation.DenotTrace`: a computation in `T∞`), the
-- translation into the linear core, and the theorem: the translation MEANS
-- THE SAME, up to bisimilarity (`LinCore.Bisim`).
--
-- Part 1: the first-order constructors. Part 2 (D409 part 3): the
-- EXPONENTIAL (`curry`/`apply`) and the FINAL COALGEBRA (`Ana`/`Out`/`in-ν`),
-- as the Spec has them: the arrow graded (`⟦ A ⇒[ q π ] B ⟧ = ⟦ A ⟧ → M π ⟦ B ⟧`,
-- an `act` arrow's body a finite block, as `Iter`'s round), a ν the Spec's
-- `νM act` (its coalgebra a finite block, `⊢unfold`). Master's IR is ungraded
-- (plan 0.52 M2); its programs come from Spec-typed sources, so B's pass
-- carries the grade from the typing into the IR (plan 0.146 §3).
--
-- A computation that returns a function or a ν cannot be compared by `≡`
-- (no function extensionality; a ν is coinductive), so the theorem is
-- stated up to the LOGICAL RELATION `V`: arrows related pointwise, ν's by
-- bisimulation, first-order values by `≡` (where it is `≡`, `Whole`).
--
-- The translation is the faithful one: `⟨f,g⟩` duplicates its input; a
-- fold's and a loop's environment is LENT to the body and COPIED per use (the
-- IR's algebra owns `E`); a closure's environment is moved into its cell and
-- copied per call (the IR's body owns it); `fst`/`snd`/`terminal` drop. The
-- cheaper choices (a lent pair, no copy) are refinements of this
-- translation, proved the same way.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂; subst)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (Pointwise)
  renaming (inj₁ to ⊎₁; inj₂ to ⊎₂)
open import Data.Unit using (⊤; tt)
open import LinCore.Flat using (FTy; funit; fvoid; fw; _f*_; _f+_)

module LinCore.Pass
  (Base : Set) (⟦_⟧b : Base → Set)
  (Sig : Set) (sdom scod : Sig → FTy Base)
  where

open import LinCore.NbEPLinCore Base ⟦_⟧b Sig sdom scod
open import LinCore.Bisim Base ⟦_⟧b Sig sdom scod
open import LinCore.Grade Base ⟦_⟧b Sig sdom scod using (same; ret≈; bind≈; blk-coh; cata-coh)

------------------------------------------------------------------------
-- 1. THE IR: master's constructors, over the core's types.
------------------------------------------------------------------------

-- ★ The Spec's grades (`⊢iter`, `⊢lam`, `⊢unfold`): a loop's round, an `act`
-- arrow's body and a coalgebra are finite blocks, here as on the core
-- (`Blk`, `Gd`).
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
  const    : ∀ {b} → ⟦ b ⟧b → IR One (Bt b)
  SigOp    : (s : Sig) → IR ⌜ sdom s ⌝ ⌜ scod s ⌝

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
  i-const : ∀ {b} {v : ⟦ b ⟧b} → BlkIR (const v)
  i-op    : ∀ {s} → BlkIR (SigOp s)

GdIR act f = BlkIR f
GdIR eff f = ⊤

------------------------------------------------------------------------
-- 2. ITS MEANING, clause for clause master's `evalᴰ`, at the Spec's grades:
-- `ev` in `T∞`, and a block's in `T` (`evB`), as an `act` arrow means.
------------------------------------------------------------------------

-- Lambek's inverse: a ν whose observation is the layer given
inν : ∀ {F} → FS F (Nuᵐ F) → Nuᵐ F
outν (inν w) = ret w

mutual
  ev : ∀ {A B} → IR A B → ⟦ A ⟧ → T∞ ⟦ B ⟧
  ev id               a        = return∞ a
  ev (g ∘ f)          a        = ev f a >>=∞ ev g
  ev ⟨ f , g ⟩        a        = ev f a >>=∞ λ b → ev g a >>=∞ λ c → return∞ (b , c)
  ev fst              (a , b)  = return∞ a
  ev snd              (a , b)  = return∞ b
  ev inl              a        = return∞ (inj₁ a)
  ev inr              b        = return∞ (inj₂ b)
  ev (case f g)       (inj₁ a) = ev f a
  ev (case f g)       (inj₂ b) = ev g b
  ev terminal         _        = return∞ tt
  ev initial          ()
  ev (curry g f γ)    a        = return∞ (λ b → evG g f γ (a , b))
  ev (apply {g})      (f , a)  = up g (f a)
  ev (In F)           x        = return∞ (inμ (coh F (μt F) x))
  ev (out-μ F)        x        = return∞ (coh⁻¹ F (μt F) (outμ x))
  ev (Cata F alg)     (e , x)  = cataC ε F (λ y → ev alg (e , coh⁻¹ F _ y)) x
  ev (Ana F {A = A} c φ) (e , a) = return∞ (anaN F (λ a′ → fmapT (coh F A) (evB φ (e , a′))) a)
  ev (Out F)          v        = emb (fmapT (coh⁻¹ F (Nu F)) (outν v))
  ev (in-ν F)         x        = return∞ (inν (coh F (Nu F) x))
  ev (Iter body _)    (e , a)  = iter∞ (λ a′ → ev body (e , a′)) a
  ev (const v)        _        = return∞ v
  ev (SigOp s)        x        = callT s x

  evB : ∀ {A B} {f : IR A B} → BlkIR f → ⟦ A ⟧ → T ⟦ B ⟧
  evB i-id            a        = ret a
  evB (i-∘ φ ψ)       a        = bindT (evB ψ a) (evB φ)
  evB (i-pair φ ψ)    a        = bindT (evB φ a) λ b → bindT (evB ψ a) λ c → ret (b , c)
  evB i-fst           (a , b)  = ret a
  evB i-snd           (a , b)  = ret b
  evB i-inl           a        = ret (inj₁ a)
  evB i-inr           b        = ret (inj₂ b)
  evB (i-case φ ψ)    (inj₁ a) = evB φ a
  evB (i-case φ ψ)    (inj₂ b) = evB ψ b
  evB i-term          _        = ret tt
  evB i-init          ()
  evB (i-curry {g = g} {f} {γ}) a = ret (λ b → evG g f γ (a , b))
  evB i-apply         (f , a)  = f a
  evB (i-In {F})      x        = ret (inμ (coh F (μt F) x))
  evB (i-out {F})     x        = ret (coh⁻¹ F (μt F) (outμ x))
  evB (i-cata {F} φ)  (e , x)  = cataB ε F (λ y → evB φ (e , coh⁻¹ F _ y)) x
  evB (i-ana {F} {A = A} {φ = φ}) (e , a) = ret (anaN F (λ a′ → fmapT (coh F A) (evB φ (e , a′))) a)
  evB (i-Out {F})     v        = fmapT (coh⁻¹ F (Nu F)) (outν v)
  evB (i-inν {F})     x        = ret (inν (coh F (Nu F) x))
  evB (i-const {v = v}) _      = ret v
  evB (i-op {s})      x        = callB s x

  evG : ∀ g {A B} (f : IR A B) → GdIR g f → ⟦ A ⟧ → Mg g ⟦ B ⟧
  evG act f φ = evB φ
  evG eff f _ = ev f

-- ★ an IR block's computation is its block (as the core's, `Grade.blk-coh`)
ev-coh : ∀ {A B} {f : IR A B} (φ : BlkIR f) a → ev f a ≈ emb (evB φ a)
ev-coh i-id           a        = ret≈
ev-coh (i-∘ φ ψ)      a        = bind≈ (ev-coh ψ a) (ev-coh φ)
ev-coh (i-pair φ ψ)   a        = bind≈ (ev-coh φ a) (λ b → bind≈ (ev-coh ψ a) (λ c → ret≈))
ev-coh i-fst          (a , b)  = ret≈
ev-coh i-snd          (a , b)  = ret≈
ev-coh i-inl          a        = ret≈
ev-coh i-inr          b        = ret≈
ev-coh (i-case φ ψ)   (inj₁ a) = ev-coh φ a
ev-coh (i-case φ ψ)   (inj₂ b) = ev-coh ψ b
ev-coh i-term         _        = ret≈
ev-coh i-init         ()
ev-coh i-curry        a        = ret≈
ev-coh i-apply        (f , a)  = ≈-refl
ev-coh i-In           x        = ret≈
ev-coh i-out          x        = ret≈
ev-coh (i-cata {F} φ) (e , x)  = cata-coh ε F (λ y → ev-coh φ (e , coh⁻¹ F _ y)) x
ev-coh i-ana          a        = ret≈
ev-coh i-Out          v        = ≈-refl
ev-coh i-inν          x        = ret≈
ev-coh i-const        _        = ret≈
ev-coh i-op           x        = same refl

------------------------------------------------------------------------
-- 3. THE TRANSLATION into the core (closed: nothing lent, no labels).
------------------------------------------------------------------------

-- drop the left of a pair
dropl : ∀ {Γ E A B} → Tm Γ E (A ⊗t B) B
dropl = lul ∘l (drop ⊗l lid)

k-dropl : ∀ {Γ E A B} → Blk (dropl {Γ} {E} {A} {B})
k-dropl = k-∘ k-lul (k-⊗ k-drop k-id)

-- a body that owns `E`, run where `E` is lent: copy it in
withE : ∀ {E A B} → LTm ε (E ⊗t A) B → Tm ε (One ⊗t E) A B
withE b = blift b ∘l (bsnd bcopy ⊗l lid) ∘l lul⁻

k-withE : ∀ {E A B} {b : LTm ε (E ⊗t A) B} → Blk b → Blk (withE b)
k-withE β = k-∘ (k-lift β) (k-∘ (k-⊗ (k-snd k-copy) k-id) k-lul⁻)

-- the same, where `X` is all that is lent (a closure's environment)
copyIn : ∀ {X A B} → LTm ε (X ⊗t A) B → Tm ε X A B
copyIn b = blift b ∘l (bcopy ⊗l lid) ∘l lul⁻

k-copyIn : ∀ {X A B} {b : LTm ε (X ⊗t A) B} → Blk b → Blk (copyIn b)
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

inco : ∀ F → Tm ε One (InS F) (LF∙ F (InS F))
inco F = lcase (mapL F linr) (mapL F linr ∘l lout)

k-inco : ∀ F → Blk (inco F)
k-inco F = k-case (k-mapL F k-inr) (k-∘ (k-mapL F k-inr) k-nout)

tr : ∀ {A B} → IR A B → LTm ε A B
-- a block translates to a block
tr-blk : ∀ {A B} {f : IR A B} → BlkIR f → Blk (tr f)
-- a body at its grade, to the core's
tr-gd : ∀ g {A B C} {f : IR (A ⊗t B) C} → GdIR g f → Gd g (copyIn (tr f))

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

------------------------------------------------------------------------
-- 4. ★ THE VALUE RELATION: the same value, up to what the meaning cannot
-- compare by `≡`. Arrows: related arguments give related computations; ν's:
-- a BISIMULATION (each observation, the same calls and related layers).
------------------------------------------------------------------------

mutual
  record VNu (F : LF) (v v′ : Nuᵐ F) : Set where
    coinductive
    field vout : TR (LR F F) (outν v) (outν v′)

  -- on a layer: the ν's related, the rest equal
  LR : ∀ F G → FS G (Nuᵐ F) → FS G (Nuᵐ F) → Set
  LR F Idf      = VNu F
  LR F Kone     _ _ = ⊤
  LR F Kzero    _ _ = ⊤
  LR F (Kb b)   = _≡_
  LR F (Kμ G)   = _≡_
  LR F (G ⊕f H) = Pointwise (LR F G) (LR F H)
  LR F (G ⊗f H) p q = LR F G (proj₁ p) (proj₁ q) × LR F H (proj₂ p) (proj₂ q)
open VNu public

V : (A : LTy) → ⟦ A ⟧ → ⟦ A ⟧ → Set
V One          _ _  = ⊤
V Zero         _ _  = ⊤
V (A ⊗t B)     p q  = V A (proj₁ p) (proj₁ q) × V B (proj₂ p) (proj₂ q)
V (A ⊕t B)          = Pointwise (V A) (V B)
V (Ct l X)          = V X
V (Fn k g A B) f f′ = ∀ {a a′} → V A a a′ → up g (f a) ≈[ V B ] up g (f′ a′)
V (Nu F)            = VNu F
V (μt F)            = _≡_
V (Bt b)            = _≡_

-- ★ on a first-order type it is `≡`
module _ {X : LTy} where
  VL≡ : ∀ G → (∀ {x y} → V X x y → x ≡ y) → ∀ {x y} → V (LF∙ G X) x y → x ≡ y
  VL≡ Idf      h r          = h r
  VL≡ Kone     h r          = refl
  VL≡ Kzero    h {()}
  VL≡ (Kb b)   h r          = r
  VL≡ (Kμ G)   h r          = r
  VL≡ (G ⊕f H) h (⊎₁ r)     = cong inj₁ (VL≡ G h r)
  VL≡ (G ⊕f H) h (⊎₂ r)     = cong inj₂ (VL≡ H h r)
  VL≡ (G ⊗f H) h (r , r′)   = cong₂ _,_ (VL≡ G h r) (VL≡ H h r′)

  VL-refl : ∀ G → (∀ x → V X x x) → ∀ x → V (LF∙ G X) x x
  VL-refl Idf      h x        = h x
  VL-refl Kone     h x        = tt
  VL-refl Kzero    h ()
  VL-refl (Kb b)   h x        = refl
  VL-refl (Kμ G)   h x        = refl
  VL-refl (G ⊕f H) h (inj₁ x) = ⊎₁ (VL-refl G h x)
  VL-refl (G ⊕f H) h (inj₂ y) = ⊎₂ (VL-refl H h y)
  VL-refl (G ⊗f H) h (x , y)  = VL-refl G h x , VL-refl H h y

Vf≡ : ∀ a {x y} → V ⌜ a ⌝ x y → x ≡ y
Vf≡ funit    r        = refl
Vf≡ fvoid    {()}
Vf≡ (fw b)   r        = r
Vf≡ (a f* b) (r , r′) = cong₂ _,_ (Vf≡ a r) (Vf≡ b r′)
Vf≡ (a f+ b) (⊎₁ r)   = cong inj₁ (Vf≡ a r)
Vf≡ (a f+ b) (⊎₂ r)   = cong inj₂ (Vf≡ b r)

Vf-refl : ∀ a x → V ⌜ a ⌝ x x
Vf-refl funit    x        = tt
Vf-refl fvoid    ()
Vf-refl (fw b)   x        = refl
Vf-refl (a f* b) (x , y)  = Vf-refl a x , Vf-refl b y
Vf-refl (a f+ b) (inj₁ x) = ⊎₁ (Vf-refl a x)
Vf-refl (a f+ b) (inj₂ y) = ⊎₂ (Vf-refl b y)

-- a layer of ν's, between the two views of it
module _ {F : LF} where
  V→LR : ∀ G {x y} → V (LF∙ G (Nu F)) x y → LR F G (coh G (Nu F) x) (coh G (Nu F) y)
  V→LR Idf      r        = r
  V→LR Kone     r        = tt
  V→LR Kzero    {()}
  V→LR (Kb b)   r        = r
  V→LR (Kμ G)   r        = r
  V→LR (G ⊕f H) (⊎₁ r)   = ⊎₁ (V→LR G r)
  V→LR (G ⊕f H) (⊎₂ r)   = ⊎₂ (V→LR H r)
  V→LR (G ⊗f H) (r , r′) = V→LR G r , V→LR H r′

  LR→V : ∀ G {x y} → LR F G x y → V (LF∙ G (Nu F)) (coh⁻¹ G (Nu F) x) (coh⁻¹ G (Nu F) y)
  LR→V Idf      r        = r
  LR→V Kone     r        = tt
  LR→V Kzero    {()}
  LR→V (Kb b)   r        = r
  LR→V (Kμ G)   r        = r
  LR→V (G ⊕f H) (⊎₁ r)   = ⊎₁ (LR→V G r)
  LR→V (G ⊕f H) (⊎₂ r)   = ⊎₂ (LR→V H r)
  LR→V (G ⊗f H) (r , r′) = LR→V G r , LR→V H r′

------------------------------------------------------------------------
-- 5. ★ AN UNFOLD SIMULATES a ν: if each seed's block is related to the ν's
-- observation, the seed's layer to its layer, the unfold is related to it.
------------------------------------------------------------------------

module Sim (F : LF) {X : Set} (Q : X → Nuᵐ F → Set) where
  -- on a layer: seeds and ν's related by `Q`, the rest equal
  QL : ∀ G → FS G X → FS G (Nuᵐ F) → Set
  QL Idf      = Q
  QL Kone     _ _ = ⊤
  QL Kzero    _ _ = ⊤
  QL (Kb b)   = _≡_
  QL (Kμ G)   = _≡_
  QL (G ⊕f H) = Pointwise (QL G) (QL H)
  QL (G ⊗f H) p q = QL G (proj₁ p) (proj₁ q) × QL H (proj₂ p) (proj₂ q)

  module _ (c : X → T (FS F X)) (h : ∀ {s v} → Q s v → TR (QL F) (c s) (outν v)) where
    mutual
      ana-sim : ∀ {s v} → Q s v → VNu F (anaN F c s) v
      vout (ana-sim q) = tree-sim (h q)

      tree-sim : ∀ {m : T (FS F X)} {m′ : T (FS F (Nuᵐ F))} → TR (QL F) m m′ → TR (LR F F) (treeN F c m) m′
      tree-sim (tret r)  = tret (map-sim F r)
      tree-sim (tcall f) = tcall (λ y → tree-sim (f y))
      tree-sim thalt     = thalt

      map-sim : ∀ G {l l′} → QL G l l′ → LR F G (mapN F G c l) l′
      map-sim Idf      q        = ana-sim q
      map-sim Kone     q        = tt
      map-sim Kzero    {()}
      map-sim (Kb b)   r        = r
      map-sim (Kμ G)   r        = r
      map-sim (G ⊕f H) (⊎₁ r)   = ⊎₁ (map-sim G r)
      map-sim (G ⊕f H) (⊎₂ r)   = ⊎₂ (map-sim H r)
      map-sim (G ⊗f H) (r , r′) = map-sim G r , map-sim H r′

-- ★ two unfolds of related coalgebras, from related seeds, are related
module _ (F : LF) (A : LTy) (c₀ c₀′ : ⟦ A ⟧ → T ⟦ LF∙ F A ⟧)
         (cc : ∀ {s s′} → V A s s′ → TR (V (LF∙ F A)) (c₀ s) (c₀′ s′)) where
  private
    c′ : ⟦ A ⟧ → T (FS F ⟦ A ⟧)
    c′ s = fmapT (coh F A) (c₀′ s)

    Q : ⟦ A ⟧ → Nuᵐ F → Set
    Q s v = Σ ⟦ A ⟧ λ s′ → (v ≡ anaN F c′ s′) × V A s s′
  open Sim F Q

  private
    layer : ∀ G {x x′} → V (LF∙ G A) x x′ → QL G (coh G A x) (mapN F G c′ (coh G A x′))
    layer Idf      r        = _ , refl , r
    layer Kone     r        = tt
    layer Kzero    {()}
    layer (Kb b)   r        = r
    layer (Kμ G)   r        = r
    layer (G ⊕f H) (⊎₁ r)   = ⊎₁ (layer G r)
    layer (G ⊕f H) (⊎₂ r)   = ⊎₂ (layer H r)
    layer (G ⊗f H) (r , r′) = layer G r , layer H r′

    step : ∀ {m m′} → TR (V (LF∙ F A)) m m′ → TR (QL F) (fmapT (coh F A) m) (treeN F c′ (fmapT (coh F A) m′))
    step (tret r)  = tret (layer F r)
    step (tcall f) = tcall (λ y → step (f y))
    step thalt     = thalt

    h : ∀ {s v} → Q s v → TR (QL F) (fmapT (coh F A) (c₀ s)) (outν v)
    h (s′ , refl , r) = step (cc r)

  ana-V : ∀ {s s′} → V A s s′
        → VNu F (anaN F (λ x → fmapT (coh F A) (c₀ x)) s) (anaN F (λ x → fmapT (coh F A) (c₀′ x)) s′)
  ana-V r = ana-sim (λ x → fmapT (coh F A) (c₀ x)) h (_ , refl , r)

-- ★ Lambek's inverse, as the unfold `tr` builds, is the layer given
module _ (F : LF) where
  private
    S : LTy
    S = InS F

    Q : ⟦ S ⟧ → Nuᵐ F → Set
    Q (inj₁ y) v = TR (LR F F) (ret (coh F (Nu F) y)) (outν v)
    Q (inj₂ u) v = VNu F u v
  open Sim F Q

  private
    -- `linr` over a layer, as a function
    mapI : ∀ G → ⟦ LF∙ G (Nu F) ⟧ → ⟦ LF∙ G S ⟧
    mapI Idf      u        = inj₂ u
    mapI Kone     x        = x
    mapI Kzero    ()
    mapI (Kb b)   x        = x
    mapI (Kμ G)   x        = x
    mapI (G ⊕f H) (inj₁ x) = inj₁ (mapI G x)
    mapI (G ⊕f H) (inj₂ y) = inj₂ (mapI H y)
    mapI (G ⊗f H) (x , y)  = (mapI G x , mapI H y)

    mapI-ret : ∀ G y → Lᴮ ε (k-mapL G (k-inr {A = LF∙ F (Nu F)} {B = Nu F} {E = One})) tt y ≡ ret (mapI G y)
    mapI-ret Idf      u        = refl
    mapI-ret Kone     x        = refl
    mapI-ret Kzero    ()
    mapI-ret (Kb b)   x        = refl
    mapI-ret (Kμ G)   x        = refl
    mapI-ret (G ⊕f H) (inj₁ x) = cong (λ m → bindT m (λ z → ret (inj₁ z))) (mapI-ret G x)
    mapI-ret (G ⊕f H) (inj₂ y) = cong (λ m → bindT m (λ z → ret (inj₂ z))) (mapI-ret H y)
    mapI-ret (G ⊗f H) (x , y)  = cong₂ (λ m n → bindT m (λ a′ → fmapT (a′ ,_) n)) (mapI-ret G x) (mapI-ret H y)

    lay₁ : ∀ G {y w} → LR F G (coh G (Nu F) y) w → QL G (coh G S (mapI G y)) w
    lay₁ Idf      r                  = r
    lay₁ Kone     r                  = tt
    lay₁ Kzero    {()}
    lay₁ (Kb b)   r                  = r
    lay₁ (Kμ G)   r                  = r
    lay₁ (G ⊕f H) {inj₁ y} (⊎₁ r)    = ⊎₁ (lay₁ G r)
    lay₁ (G ⊕f H) {inj₂ y} (⊎₂ r)    = ⊎₂ (lay₁ H r)
    lay₁ (G ⊗f H) {y₁ , y₂} (r , r′) = lay₁ G r , lay₁ H r′

    lay₂ : ∀ G {l w} → LR F G l w → QL G (coh G S (mapI G (coh⁻¹ G (Nu F) l))) w
    lay₂ Idf      r                  = r
    lay₂ Kone     r                  = tt
    lay₂ Kzero    {()}
    lay₂ (Kb b)   r                  = r
    lay₂ (Kμ G)   r                  = r
    lay₂ (G ⊕f H) {inj₁ l} (⊎₁ r)    = ⊎₁ (lay₂ G r)
    lay₂ (G ⊕f H) {inj₂ l} (⊎₂ r)    = ⊎₂ (lay₂ H r)
    lay₂ (G ⊗f H) {l₁ , l₂} (r , r′) = lay₂ G r , lay₂ H r′

    c : ⟦ S ⟧ → T (FS F ⟦ S ⟧)
    c s = fmapT (coh F S) (Lᴮ ε (k-inco F) tt s)

    -- a layer still to give: given now
    h₁ : ∀ {y m′} → TR (LR F F) (ret (coh F (Nu F) y)) m′ → TR (QL F) (ret (coh F S (mapI F y))) m′
    h₁ (tret r) = tret (lay₁ F r)

    -- a ν: observed once, its layer given
    h₂ : ∀ {m m′} → TR (LR F F) m m′
       → TR (QL F) (fmapT (coh F S) (bindT (fmapT (coh⁻¹ F (Nu F)) m)
                                          (Lᴮ ε (k-mapL F (k-inr {A = LF∙ F (Nu F)} {B = Nu F} {E = One})) tt))) m′
    h₂ (tret {x = l} r) = subst (λ z → TR (QL F) (fmapT (coh F S) z) _) (sym (mapI-ret F (coh⁻¹ F (Nu F) l)))
                                (tret (lay₂ F r))
    h₂ (tcall f)        = tcall (λ y → h₂ (f y))
    h₂ thalt            = thalt

    h : ∀ {s v} → Q s v → TR (QL F) (c s) (outν v)
    h {inj₁ y} q = subst (λ z → TR (QL F) (fmapT (coh F S) z) _) (sym (mapI-ret F y)) (h₁ q)
    h {inj₂ u} q = h₂ (vout q)

  inν-V : ∀ {x x′} → V (LF∙ F (Nu F)) x x′ → VNu F (anaN F c (inj₁ x)) (inν (coh F (Nu F) x′))
  inν-V r = ana-sim c h (tret (V→LR F r))

------------------------------------------------------------------------
-- 6. ★ THE THEOREM: the translation means what the IR means, up to `V`.
------------------------------------------------------------------------

-- the fold respects related algebras
module _ {F : LF} {A : LTy} where
  RL : ∀ G → FS G ⟦ A ⟧ → FS G ⟦ A ⟧ → Set
  RL G y y′ = V (LF∙ G A) (coh⁻¹ G A y) (coh⁻¹ G A y′)

  mutual
    cata-congR : {alg alg′ : FS F ⟦ A ⟧ → T∞ ⟦ A ⟧} → (∀ {y y′} → RL F y y′ → alg y ≈[ V A ] alg′ y′)
               → ∀ x → cataC ε F alg x ≈[ V A ] cataC ε F alg′ x
    cata-congR aa (inμ w) = >>=-congR (trav-congR F aa w) aa

    trav-congR : ∀ G {alg alg′ : FS F ⟦ A ⟧ → T∞ ⟦ A ⟧} → (∀ {y y′} → RL F y y′ → alg y ≈[ V A ] alg′ y′)
               → ∀ w → travC ε F G alg w ≈[ RL G ] travC ε F G alg′ w
    trav-congR Idf      aa y        = cata-congR aa y
    trav-congR Kone     aa y        = ret≈R tt
    trav-congR Kzero    aa ()
    trav-congR (Kb _)   aa y        = ret≈R refl
    trav-congR (Kμ _)   aa y        = ret≈R refl
    trav-congR (G ⊕f H) aa (inj₁ y) = fmap-congR (trav-congR G aa y) (λ r → ⊎₁ r)
    trav-congR (G ⊕f H) aa (inj₂ z) = fmap-congR (trav-congR H aa z) (λ r → ⊎₂ r)
    trav-congR (G ⊗f H) aa (y , z)  =
      >>=-congR (trav-congR G aa y) (λ r → fmap-congR (trav-congR H aa z) (λ r′ → r , r′))

mutual
  pass-ok : ∀ {A B} (f : IR A B) {a a′} → V A a a′ → Lᶜ ε (tr f) tt a ≈[ V B ] ev f a′
  pass-ok id           r = ret≈R r
  pass-ok (g ∘ f)      r = >>=-congR (pass-ok f r) (pass-ok g)
  pass-ok ⟨ f , g ⟩    r = ≈R-blk refl (>>=-congR (pass-ok f r) (λ rb → >>=-congR (pass-ok g r) (λ rc → ret≈R (rb , rc))))
  pass-ok fst          {a , b} {a′ , b′} (ra , rb) = ≈R-blk refl (ret≈R ra)
  pass-ok snd          {a , b} {a′ , b′} (ra , rb) = ≈R-blk refl (ret≈R rb)
  pass-ok inl          r = ret≈R (⊎₁ r)
  pass-ok inr          r = ret≈R (⊎₂ r)
  pass-ok (case f g)   (⊎₁ r) = pass-ok f r
  pass-ok (case f g)   (⊎₂ r) = pass-ok g r
  pass-ok terminal     r = ret≈R tt
  pass-ok initial      {()}
  pass-ok (curry eff f γ) r = ret≈R (λ rb → ≈R-blk refl (pass-ok f (r , rb)))
  pass-ok (curry act f φ) r = ret≈R (λ rb → blk-V f φ r rb)
  pass-ok (apply {g} {A} {B}) {f , a} {f′ , a′} (rf , ra) =
    ≈-≈R (pair-drop (f ,_) (λ p → Lᶜ ε (dropl {E = One} {A = Fn many g A B} {B = B}) tt p) (λ _ → refl)) (rf ra)
  pass-ok (In F)       r = ret≈R (cong (λ z → inμ (coh F (μt F) z)) (VL≡ {X = μt F} F (λ e → e) r))
  pass-ok (out-μ F)    refl = ret≈R (VL-refl {X = μt F} F (λ _ → refl) _)
  pass-ok (Cata F {E} {R} alg) {e , x} {e′ , x′} (re , refl) =
    ≈-≈R (pair-drop (e ,_) (λ p → Lᶜ ε (dropl {E = One} {A = E} {B = R}) tt p) (λ _ → refl))
         (cata-congR {F = F} {A = R} (λ ry → ≈R-blk refl (pass-ok alg (re , ry))) x)
  pass-ok (Ana F {E} {A} c φ) {e , a} {e′ , a′} (re , ra) =
    ≈R-blk refl (ret≈R (ana-V F A (Lᴮ ε (k-copyIn (tr-blk φ)) e) (λ s → evB φ (e′ , s))
                              (λ {s} {s′} rs → TR-emb _ _ (blk-V c φ re rs)) ra))
  pass-ok (Out F)      {v} {v′} q = emb-TR (TR-bind (vout q) (λ r → tret (LR→V {F = F} F r)))
  pass-ok (in-ν F)     r = ≈R-blk refl (ret≈R (inν-V F r))
  pass-ok (Iter {E} {S} {R} body _) {e , a} {e′ , a′} (re , ra) =
    ≈-≈R (pair-drop (e ,_) (λ p → Lᶜ ε (dropl {E = One} {A = E} {B = R}) tt p) (λ _ → refl))
         (iter-congR (λ rs → ≈R-blk refl (pass-ok body (re , rs))) (≈R-blk refl (pass-ok body (re , ra))))
  pass-ok (const v)    r = ret≈R refl
  pass-ok (SigOp s)    {x} {x′} r =
    subst (λ z → callT s x ≈[ V ⌜ scod s ⌝ ] callT s z) (Vf≡ (sdom s) r) (≈→≈R (Vf-refl (scod s)) ≈-refl)

  -- a body of grade `act`, in its closure: its block, related to the IR's
  blk-V : ∀ {X A B} (f : IR (X ⊗t A) B) (φ : BlkIR f) {x x′ a a′} → V X x x′ → V A a a′
        → emb (Lᴮ ε (k-copyIn (tr-blk φ)) x a) ≈[ V B ] emb (evB φ (x′ , a′))
  blk-V f φ {x} {x′} {a} {a′} rx ra =
    ≈-≈R (≈-sym (blk-coh ε (k-copyIn (tr-blk φ)) x a))
         (≈R-blk refl (≈R-≈ (pass-ok f (rx , ra)) (ev-coh φ (x′ , a′))))

-- ★ where the program's types are first-order, the relation is `≡`: plain
-- bisimilarity (`Whole`)
pass-okᶠ : ∀ a b (f : IR ⌜ a ⌝ ⌜ b ⌝) x → Lᶜ ε (tr f) tt x ≈ ev f x
pass-okᶠ a b f x = ≈R→≈ (Vf≡ b) (pass-ok f (Vf-refl a x))
