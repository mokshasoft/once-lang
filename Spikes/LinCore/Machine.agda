-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Machine — plan 0.146 A16 (D410): A MODEL MACHINE, AND THE
-- SIMULATION.
--
-- A stack machine with CODE: instructions over two stacks — the OPERANDS
-- (owned values) and the ENVIRONMENT (lent views: what a scope lends, a part
-- of it, a node looked into, a closure's environment) — branching on a sum's
-- tag (`case` on an operand, `ecase` on a view), its own events per
-- instruction. The lowering (`comp`) is continuation-passing: a term is
-- compiled in front of the code that follows it.
--
-- Two generators run INSIDE A FRAME (`enter` … `leave`): a fold, node by node,
-- and a closure's body. A frame is a heap block, a TEMPORARY of the lowering
-- (A13): the fold's work stack is in the heap. The loop expands round by
-- round (`loop`: the round, then a branch: done, or the loop again). `ehalt`
-- ends the machine (`halted`, code with no step).
--
-- ★ The simulation (`sim`), by induction on the run, for EVERY OUTCOME: a run
-- that gives a value — the machine reaches the code that follows with it, its
-- events the run's (temporaries erased) with balanced temporaries woven in; a
-- run that stopped (halted, or cut: a server after its last round) — the
-- machine runs to a point whose events, erased, have the run's as a prefix,
-- with legal temporaries. Then `machine-noleak` (a finished run: the machine
-- legal, all cells and frames freed) and `machine-legal` (any run: what the
-- machine did up to the run's last event is legal, its frames too).
--
-- The one generator outside the lowering: a fold that rebuilds in place (A8,
-- the compiler's choice; this lowering folds plainly).
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (n∸n≡0)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Relation.Nullary using (yes; no)
open import LinCore.Flat using (FTy)
open import LinCore.Free
  using (_≼_; []≼; ∷≼; ++-≼; ≼-trans; ≼-refl; Weave; w-[]; w-run; w-tmp; w-++; w-self; weave-pre; Along-++)

module LinCore.Machine
  (Base : Set) (⟦_⟧b : Base → Set)
  (Sig : Set) (sdom scod : Sig → FTy Base)
  (bw : Base → ℕ)
  where

open import LinCore.NbEPLinCore Base ⟦_⟧b Sig sdom scod
open import LinCore.Events Base ⟦_⟧b Sig sdom scod bw
open import LinCore.Temps Base ⟦_⟧b Sig sdom scod bw

------------------------------------------------------------------------
-- 1. THE MACHINE.
------------------------------------------------------------------------

-- a frame: one word (where to return), in a heap block of its own
fsz : ℕ
fsz = 1

-- the machine's shape: the environment's types and the operands'
infix 4 _∣_
record Sh : Set where
  constructor _∣_
  field env ops : List LTy

infixr 5 _∷ˢ_
data Stk : List LTy → Set where
  []ˢ  : Stk []
  _∷ˢ_ : ∀ {A S} → MV A → Stk S → Stk (A ∷ S)

infix 4 _∥_
record Cfg (sh : Sh) : Set where
  constructor _∥_
  field envs : Stk (Sh.env sh)
        opds : Stk (Sh.ops sh)

data Ins : Sh → Sh → Set where
  unpair  : ∀ {Es A B S} → Ins (Es ∣ (A ⊗t B) ∷ S) (Es ∣ A ∷ B ∷ S)
  pair    : ∀ {Es A B S} → Ins (Es ∣ A ∷ B ∷ S) (Es ∣ (A ⊗t B) ∷ S)
  swap    : ∀ {Es A B S} → Ins (Es ∣ A ∷ B ∷ S) (Es ∣ B ∷ A ∷ S)
  -- a generator with no control and no view of its own, as one step
  prim    : ∀ {Γ} (ds : Defs Γ) {Es A B S} → LTm Γ A B → Ins (Es ∣ A ∷ S) (Es ∣ B ∷ S)
  untag   : ∀ {Es l X A S} → Ins (Es ∣ (Ct l X ⊗t A) ∷ S) (Es ∣ (X ⊗t A) ∷ S)
  enter   : ∀ {sh} → Ins sh sh
  leave   : ∀ {sh} → Ins sh sh
  -- the views: lend (the lent view and the owned value beside it), nothing
  -- lent, a part, a node looked into (a read), a closure's environment; and
  -- a view's end
  elend   : ∀ {E Es X A S} → Ins (E ∷ Es ∣ (X ⊗t A) ∷ S) ((E ⊗t X) ∷ E ∷ Es ∣ A ∷ S)
  eunlend : ∀ {E Es X B S} → Ins ((E ⊗t X) ∷ E ∷ Es ∣ B ∷ S) (E ∷ Es ∣ (X ⊗t B) ∷ S)
  elift   : ∀ {Es S} → Ins (Es ∣ S) (One ∷ Es ∣ S)
  efst    : ∀ {E₁ E₂ Es S} → Ins ((E₁ ⊗t E₂) ∷ Es ∣ S) (E₁ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S)
  esnd    : ∀ {E₁ E₂ Es S} → Ins ((E₁ ⊗t E₂) ∷ Es ∣ S) (E₂ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S)
  eout    : ∀ {F Es S} → Ins (μt F ∷ Es ∣ S) (LF∙ F (μt F) ∷ μt F ∷ Es ∣ S)
  eapp    : ∀ {l X Es S} → Ins (Ct l X ∷ Es ∣ S) (X ∷ Ct l X ∷ Es ∣ S)
  epop    : ∀ {E Es S} → Ins (E ∷ Es ∣ S) (Es ∣ S)
  ecopy   : ∀ {E Es S} → Ins (E ∷ Es ∣ One ∷ S) (E ∷ Es ∣ E ∷ S)
  ehalt   : ∀ {Es} (s : Sig) {S} → Ins (Es ∣ ⌜ sdom s ⌝ ∷ S) (Es ∣ Zero ∷ S)
  -- a fold's node, a loop's round: expanded when reached
  fold    : ∀ {Γ} (ds : Defs Γ) F {E A Es S} → Tm Γ E (LF∙ F A) A → Ins (E ∷ Es ∣ μt F ∷ S) (E ∷ Es ∣ A ∷ S)
  loop    : ∀ {Γ} (ds : Defs Γ) {E A B Es S} → Tm Γ E A (B ⊕t A) → Ins (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ B ∷ S)
  stuck   : ∀ {sh sh′} → Ins sh sh′

infixr 5 _⨾_
data Code : Sh → Sh → Set where
  end    : ∀ {sh} → Code sh sh
  _⨾_    : ∀ {sh sh′ T} → Ins sh sh′ → Code sh′ T → Code sh T
  case   : ∀ {Es A B S T} → Code (Es ∣ A ∷ S) T → Code (Es ∣ B ∷ S) T → Code (Es ∣ (A ⊕t B) ∷ S) T
  ecase  : ∀ {E₁ E₂ Es S T} → Code (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) T → Code (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) T
         → Code ((E₁ ⊕t E₂) ∷ Es ∣ S) T
  halted : ∀ {sh T} → Code sh T

------------------------------------------------------------------------
-- 2. THE LOWERING, in front of the code that follows.
------------------------------------------------------------------------

mutual
  comp : ∀ {Γ} (ds : Defs Γ) {E A B} → Tm Γ E A B → ∀ {Es S T} → Code (E ∷ Es ∣ B ∷ S) T → Code (E ∷ Es ∣ A ∷ S) T
  comp ds lid k            = k
  comp ds (f ∘l g) k       = comp ds g (comp ds f k)
  comp ds (f ⊗l g) k       = unpair ⨾ comp ds f (swap ⨾ comp ds g (swap ⨾ pair ⨾ k))
  comp ds (lcase f g) k    = case (comp ds f k) (comp ds g k)
  comp ds (lcata F alg) k  = fold ds F alg ⨾ k
  comp ds (liter f φ) k      = loop ds f ⨾ k
  comp ds (lapp p) k       = untag ⨾ enter ⨾ elift ⨾ body ds p (epop ⨾ leave ⨾ k)
  comp ds (lend b) k       = elend ⨾ comp ds b (eunlend ⨾ k)
  comp ds (blift f) k      = elift ⨾ comp ds f (epop ⨾ k)
  comp ds (bfst f) k       = efst ⨾ comp ds f (epop ⨾ k)
  comp ds (bsnd f) k       = esnd ⨾ comp ds f (epop ⨾ k)
  comp ds (bcaseE f g) k   = ecase (comp ds f (epop ⨾ k)) (comp ds g (epop ⨾ k))
  comp ds (bout f) k       = eout ⨾ comp ds f (epop ⨾ k)
  comp ds bcopy k          = ecopy ⨾ k
  comp ds (bapp p) k       = eapp ⨾ enter ⨾ bodyω ds p (leave ⨾ epop ⨾ k)
  comp ds (lhalt s) k      = ehalt s ⨾ k
  comp ds ρl k             = prim ds ρl ⨾ k
  comp ds ρl⁻ k            = prim ds ρl⁻ ⨾ k
  comp ds lul k            = prim ds lul ⨾ k
  comp ds lul⁻ k           = prim ds lul⁻ ⨾ k
  comp ds lassoc k         = prim ds lassoc ⨾ k
  comp ds lassoc⁻ k        = prim ds lassoc⁻ ⨾ k
  comp ds lswap k          = prim ds lswap ⨾ k
  comp ds dup k            = prim ds dup ⨾ k
  comp ds drop k           = prim ds drop ⨾ k
  comp ds linl k           = prim ds linl ⨾ k
  comp ds linr k           = prim ds linr ⨾ k
  comp ds lIn k            = prim ds lIn ⨾ k
  comp ds lOutμ k          = prim ds lOutμ ⨾ k
  comp ds (lclo F p) k     = prim ds (lclo F p) ⨾ k
  comp ds (lconst v) k     = prim ds (lconst v) ⨾ k
  comp ds (lop s) k        = prim ds (lop s) ⨾ k
  comp ds lzero k          = stuck ⨾ k

  -- a one-shot label's body (nothing lent), compiled in place over its prefix
  body : ∀ {Γ l g X A B} (ds : Defs Γ) → Γ ∋[ l ] sg once g X A B → ∀ {Es S T}
       → Code (One ∷ Es ∣ B ∷ S) T → Code (One ∷ Es ∣ (X ⊗t A) ∷ S) T
  body (ds ▸ _)    (there p) k = body ds p k
  body (ds ▸ b1 b _) here      k = comp ds b k

  -- a many-use label's body (its environment lent)
  bodyω : ∀ {Γ l g X A B} (ds : Defs Γ) → Γ ∋[ l ] sg many g X A B → ∀ {Es S T}
        → Code (X ∷ Es ∣ B ∷ S) T → Code (X ∷ Es ∣ A ∷ S) T
  bodyω (ds ▸ _)    (there p) k = bodyω ds p k
  bodyω (ds ▸ bω b _) here      k = comp ds b k

-- a fold's node: its children folded in order, the layer rebuilt
trav : ∀ {Γ} (ds : Defs Γ) F {E A} (alg : Tm Γ E (LF∙ F A) A) G → ∀ {Es S T}
     → Code (E ∷ Es ∣ LF∙ G A ∷ S) T → Code (E ∷ Es ∣ LF∙ G (μt F) ∷ S) T
trav ds F alg Idf      k = fold ds F alg ⨾ k
trav ds F alg Kone     k = k
trav ds F alg Kzero    k = k
trav ds F alg (Kb _)   k = k
trav ds F alg (Kμ _)   k = k
trav ds F alg (G ⊕f H) k = case (trav ds F alg G (prim ε linl ⨾ k)) (trav ds F alg H (prim ε linr ⨾ k))
trav ds F alg (G ⊗f H) k = unpair ⨾ trav ds F alg G (swap ⨾ trav ds F alg H (swap ⨾ pair ⨾ k))

------------------------------------------------------------------------
-- 3. STEPPING.
------------------------------------------------------------------------

data Step {T : Sh} : ∀ {sh sh′} → Code sh T → Cfg sh → ℕ → Trace → Code sh′ T → Cfg sh′ → ℕ → Set where
  s-unpair : ∀ {Es A B S} {k : Code (Es ∣ A ∷ B ∷ S) T} {es} {a : MV A} {b : MV B} {os n}
           → Step (unpair ⨾ k) (es ∥ mpair a b ∷ˢ os) n [] k (es ∥ a ∷ˢ b ∷ˢ os) n
  s-pair   : ∀ {Es A B S} {k : Code (Es ∣ (A ⊗t B) ∷ S) T} {es} {a : MV A} {b : MV B} {os n}
           → Step (pair ⨾ k) (es ∥ a ∷ˢ b ∷ˢ os) n [] k (es ∥ mpair a b ∷ˢ os) n
  s-swap   : ∀ {Es A B S} {k : Code (Es ∣ B ∷ A ∷ S) T} {es} {a : MV A} {b : MV B} {os n}
           → Step (swap ⨾ k) (es ∥ a ∷ˢ b ∷ˢ os) n [] k (es ∥ b ∷ˢ a ∷ˢ os) n
  s-prim   : ∀ {Γ} {ds : Defs Γ} {Es A B S} {g : LTm Γ A B} {k : Code (Es ∣ B ∷ S) T} {es v w os n n′ t}
           → Run ds g mone v n (gives w n′) t → Step (prim ds g ⨾ k) (es ∥ v ∷ˢ os) n t k (es ∥ w ∷ˢ os) n′
  s-untag  : ∀ {Es l X A S} {k : Code (Es ∣ (X ⊗t A) ∷ S) T} {es} {x : MV X} {a : MV A} {os n}
           → Step (untag {l = l} ⨾ k) (es ∥ mpair (mct x) a ∷ˢ os) n [] k (es ∥ mpair x a ∷ˢ os) n
  s-enter  : ∀ {sh} {k : Code sh T} {m n} → Step (enter ⨾ k) m n (tmp (tnew fsz) ∷ []) k m n
  s-leave  : ∀ {sh} {k : Code sh T} {m n} → Step (leave ⨾ k) m n (tmp (tdel fsz) ∷ []) k m n
  s-case₁  : ∀ {Es A B S} {c₁ : Code (Es ∣ A ∷ S) T} {c₂ : Code (Es ∣ B ∷ S) T} {es a os n}
           → Step (case c₁ c₂) (es ∥ minl a ∷ˢ os) n [] c₁ (es ∥ a ∷ˢ os) n
  s-case₂  : ∀ {Es A B S} {c₁ : Code (Es ∣ A ∷ S) T} {c₂ : Code (Es ∣ B ∷ S) T} {es b os n}
           → Step (case c₁ c₂) (es ∥ minr b ∷ˢ os) n [] c₂ (es ∥ b ∷ˢ os) n
  s-elend  : ∀ {E Es X A S} {k : Code ((E ⊗t X) ∷ E ∷ Es ∣ A ∷ S) T} {e : MV E} {es} {x : MV X} {a : MV A} {os n}
           → Step (elend ⨾ k) (e ∷ˢ es ∥ mpair x a ∷ˢ os) n [] k (mpair e x ∷ˢ e ∷ˢ es ∥ a ∷ˢ os) n
  s-eunlend : ∀ {E Es X B S} {k : Code (E ∷ Es ∣ (X ⊗t B) ∷ S) T} {e e′ : MV E} {es} {x : MV X} {w : MV B} {os n}
           → Step (eunlend ⨾ k) (mpair e x ∷ˢ e′ ∷ˢ es ∥ w ∷ˢ os) n [] k (e′ ∷ˢ es ∥ mpair x w ∷ˢ os) n
  s-elift  : ∀ {Es S} {k : Code (One ∷ Es ∣ S) T} {es os n}
           → Step (elift ⨾ k) (es ∥ os) n [] k (mone ∷ˢ es ∥ os) n
  s-efst   : ∀ {E₁ E₂ Es S} {k : Code (E₁ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S) T} {e₁ : MV E₁} {e₂ : MV E₂} {es os n}
           → Step (efst ⨾ k) (mpair e₁ e₂ ∷ˢ es ∥ os) n [] k (e₁ ∷ˢ mpair e₁ e₂ ∷ˢ es ∥ os) n
  s-esnd   : ∀ {E₁ E₂ Es S} {k : Code (E₂ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S) T} {e₁ : MV E₁} {e₂ : MV E₂} {es os n}
           → Step (esnd ⨾ k) (mpair e₁ e₂ ∷ˢ es ∥ os) n [] k (e₂ ∷ˢ mpair e₁ e₂ ∷ˢ es ∥ os) n
  s-eout   : ∀ {F Es S} {k : Code (LF∙ F (μt F) ∷ μt F ∷ Es ∣ S) T} {i v es os n}
           → Step (eout ⨾ k) (mmu i v ∷ˢ es ∥ os) n (peek i ∷ []) k (v ∷ˢ mmu i v ∷ˢ es ∥ os) n
  s-ecase₁ : ∀ {E₁ E₂ Es S} {c₁ : Code (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) T} {c₂ : Code (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) T} {e es os n}
           → Step (ecase c₁ c₂) (minl e ∷ˢ es ∥ os) n [] c₁ (e ∷ˢ minl e ∷ˢ es ∥ os) n
  s-ecase₂ : ∀ {E₁ E₂ Es S} {c₁ : Code (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) T} {c₂ : Code (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) T} {e es os n}
           → Step (ecase c₁ c₂) (minr e ∷ˢ es ∥ os) n [] c₂ (e ∷ˢ minr e ∷ˢ es ∥ os) n
  s-eapp   : ∀ {l X Es S} {k : Code (X ∷ Ct l X ∷ Es ∣ S) T} {x : MV X} {es os n}
           → Step (eapp ⨾ k) (mct x ∷ˢ es ∥ os) n [] k (x ∷ˢ mct x ∷ˢ es ∥ os) n
  s-epop   : ∀ {E Es S} {k : Code (Es ∣ S) T} {e : MV E} {es os n}
           → Step (epop ⨾ k) (e ∷ˢ es ∥ os) n [] k (es ∥ os) n
  s-ecopy  : ∀ {E Es S} {k : Code (E ∷ Es ∣ E ∷ S) T} {e : MV E} {es os n}
           → Step (ecopy ⨾ k) (e ∷ˢ es ∥ mone ∷ˢ os) n (snd (snd (copy e n))) k (e ∷ˢ es ∥ fst (copy e n) ∷ˢ os) (fst (snd (copy e n)))
  s-ehalt  : ∀ {Es} {s : Sig} {S} {k : Code (Es ∣ Zero ∷ S) T} {es} {x : MV ⌜ sdom s ⌝} {os n}
           → Step (ehalt s ⨾ k) (es ∥ x ∷ˢ os) n (stp s (toF (sdom s) (er x)) ∷ []) halted (es ∥ os) n
  s-fold   : ∀ {Γ} {ds : Defs Γ} {F E A Es S} {alg : Tm Γ E (LF∙ F A) A} {k : Code (E ∷ Es ∣ A ∷ S) T} {e es i v os n}
           → Step (fold ds F alg ⨾ k) (e ∷ˢ es ∥ mmu i v ∷ˢ os) n (free i ∷ [])
                  (enter ⨾ trav ds F alg F (comp ds alg (leave ⨾ k))) (e ∷ˢ es ∥ v ∷ˢ os) n
  s-loop   : ∀ {Γ} {ds : Defs Γ} {E A B Es S} {f : Tm Γ E A (B ⊕t A)} {k : Code (E ∷ Es ∣ B ∷ S) T} {m n}
           → Step (loop ds f ⨾ k) m n [] (comp ds f (case k (loop ds f ⨾ k))) m n

infixr 5 _⟫_
data Steps {T : Sh} : ∀ {sh sh′} → Code sh T → Cfg sh → ℕ → Trace → Code sh′ T → Cfg sh′ → ℕ → Set where
  done : ∀ {sh} {c : Code sh T} {m n} → Steps c m n [] c m n
  _⟫_  : ∀ {sh sh′ sh″} {c : Code sh T} {c′ : Code sh′ T} {c″ : Code sh″ T} {m m′ m″ n n′ n″ t₁ t₂}
       → Step c m n t₁ c′ m′ n′ → Steps c′ m′ n′ t₂ c″ m″ n″ → Steps c m n (t₁ ++ t₂) c″ m″ n″

steps-++ : ∀ {T sh sh′ sh″} {c : Code sh T} {c′ : Code sh′ T} {c″ : Code sh″ T} {m m′ m″ n n′ n″ t₁ t₂}
         → Steps c m n t₁ c′ m′ n′ → Steps c′ m′ n′ t₂ c″ m″ n″ → Steps c m n (t₁ ++ t₂) c″ m″ n″
steps-++ done st₂ = st₂
steps-++ {c = c} {c″ = c″} {m = m} {m″ = m″} {n = n} {n″ = n″} {t₂ = t₂} (_⟫_ {t₁ = u₁} {t₂ = u₂} x st₁) st₂ =
  subst (λ z → Steps c m n z c″ m″ n″) (sym (++-assoc u₁ u₂ t₂)) (x ⟫ steps-++ st₁ st₂)

one : ∀ {T sh sh′} {c : Code sh T} {c′ : Code sh′ T} {m m′ n n′ t}
    → Step c m n t c′ m′ n′ → Steps c m n t c′ m′ n′
one {c = c} {c′} {m} {m′} {n} {n′} {t} x = subst (λ z → Steps c m n z c′ m′ n′) (++-identityʳ t) (x ⟫ done)

------------------------------------------------------------------------
-- 4. WHAT THE SIMULATION CLAIMS of a stretch of the machine's run.
------------------------------------------------------------------------

-- to a configuration: the events are a run's (erased) with balanced
-- temporaries woven in
record Out {T sh sh′} (c : Code sh T) (m : Cfg sh) (n : ℕ) (t : Trace) (c′ : Code sh′ T) (m′ : Cfg sh′) (n′ : ℕ) : Set where
  constructor out
  field
    ts    : List TEv
    mt    : Trace
    steps : Steps c m n mt c′ m′ n′
    woven : Weave tmp (erase t) ts mt
    bal   : TBal (tmps ts)

-- to some point: the events weave a cell trace `t₀` that the run's events
-- (erased) are a prefix of, with legal temporaries (a frame may be open)
record Paused {T sh} (c : Code sh T) (m : Cfg sh) (n : ℕ) (t : Trace) : Set where
  constructor paused
  field
    {sh′} : Sh
    c′    : Code sh′ T
    m′    : Cfg sh′
    n′    : ℕ
    ts    : List TEv
    mt t₀ : Trace
    steps : Steps c m n mt c′ m′ n′
    woven : Weave tmp t₀ ts mt
    pref  : erase t ≼ t₀
    clean : NoT t₀
    leg   : TLeg (tmps ts)

-- by the run's outcome
SimR : ∀ {T sh E Es B S} → Outcome B → Code sh T → Cfg sh → ℕ → Trace → Code (E ∷ Es ∣ B ∷ S) T → MV E → Stk Es → Stk S → Set
SimR (gives w n′) c m n t k e es os = Out c m n t k (e ∷ˢ es ∥ w ∷ˢ os) n′
SimR (stop y)     c m n t k e es os = Paused c m n t

private
  δn-same : ∀ k → δn k k ≡ 1
  δn-same k with k ≟ k
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne refl)

  bal∅ : TBal (tmps [])
  bal∅ = (tt , λ k → refl)

  -- a frame around balanced temporaries: balanced
  bracket : ∀ k ts → TBal (tmps ts) → TBal (tmps (tnew k ∷ (ts ++ tdel k ∷ [])))
  bracket k ts (okX , zX) rewrite map-++ tmp ts (tdel k ∷ []) =
    ( (tt , Along-++ X (tmp (tdel k) ∷ []) L₁ okX′ (subst (1 ≤_) (sym (eqX k)) one≤ , tt))
    , λ j → trans (cong (λ M → M j) (tplay-++ X (tmp (tdel k) ∷ []) L₁))
                  (trans (cong (_∸ δn k j) (eqX j)) (n∸n≡0 (δn k j))) )
    where
      X  = tmps ts
      L₁ : TL
      L₁ j = 0 + δn k j
      w  = weave-ok (w-self X) none L₁ L₁ (λ j → refl) okX tt
      okX′ = fst w
      eqX : ∀ j → tplay X L₁ j ≡ L₁ j
      eqX j = trans (snd w j) (cong (_+ L₁ j) (zX j))
      one≤ : 1 ≤ L₁ k
      one≤ = subst (1 ≤_) (sym (δn-same k)) (s≤s z≤n)

  -- an open frame around legal temporaries: legal
  opened : ∀ k ts → TLeg (tmps ts) → TLeg (tmps (tnew k ∷ ts))
  opened k ts l = (tt , TOK-mono (tmps ts) (λ j → z≤n) l)

------------------------------------------------------------------------
-- 5. COMPOSING CLAIMS.
------------------------------------------------------------------------

-- a silent step first
pre : ∀ {T sh sh′ sh″} {c : Code sh T} {c′ : Code sh′ T} {c″ : Code sh″ T} {m m′ m″ n n′ n″ t}
    → Step c m n [] c′ m′ n′ → Out c′ m′ n′ t c″ m″ n″ → Out c m n t c″ m″ n″
pre x (out ts mt st w b) = out ts mt (x ⟫ st) w b

preP : ∀ {T sh sh′} {c : Code sh T} {c′ : Code sh′ T} {m m′ n n′ t}
     → Step c m n [] c′ m′ n′ → Paused c′ m′ n′ t → Paused c m n t
preP x (paused c′ m′ n′ ts mt t₀ st w p cl l) = paused c′ m′ n′ ts mt t₀ (x ⟫ st) w p cl l

preR : ∀ {T sh sh′ E Es B S} (o : Outcome B) {c : Code sh T} {c′ : Code sh′ T} {m m′ n t}
       {k : Code (E ∷ Es ∣ B ∷ S) T} {e es os}
     → Step c m n [] c′ m′ n → SimR o c′ m′ n t k e es os → SimR o c m n t k e es os
preR (gives _ _) x r = pre x r
preR (stop _)    x r = preP x r

-- a silent step after
after : ∀ {T sh sh′ sh″} {c : Code sh T} {c′ : Code sh′ T} {c″ : Code sh″ T} {m m′ m″ n n′ n″ t}
      → Out c m n t c′ m′ n′ → Step c′ m′ n′ [] c″ m″ n″ → Out c m n t c″ m″ n″
after {t = t} (out ts mt st w b) x =
  out ts (mt ++ []) (steps-++ st (one x)) (subst (λ z → Weave tmp (erase t) ts z) (sym (++-identityʳ mt)) w) b

-- one step whose events hold no temporary
leaf : ∀ {T sh sh′} {c : Code sh T} {c′ : Code sh′ T} {m m′ n n′ t}
     → Step c m n t c′ m′ n′ → NoT t → Out c m n t c′ m′ n′
leaf {t = t} x nt = out [] t (one x) (subst (λ z → Weave tmp z [] t) (sym (erase-NoT t nt)) (w-self t)) bal∅

-- one stretch, then the next
then : ∀ {T sh sh′ sh″} {c : Code sh T} {c′ : Code sh′ T} {c″ : Code sh″ T} {m m′ m″ n n′ n″ t₁ t₂}
     → Out c m n t₁ c′ m′ n′ → Out c′ m′ n′ t₂ c″ m″ n″ → Out c m n (t₁ ++ t₂) c″ m″ n″
then {t₁ = t₁} {t₂} (out ts₁ m₁ st₁ w₁ b₁) (out ts₂ m₂ st₂ w₂ b₂) =
  out (ts₁ ++ ts₂) (m₁ ++ m₂) (steps-++ st₁ st₂)
      (subst (λ z → Weave tmp z (ts₁ ++ ts₂) (m₁ ++ m₂)) (sym (erase-++ t₁ t₂)) (w-++ w₁ w₂))
      (subst TBal (sym (map-++ tmp ts₁ ts₂)) (IsSubmonoid.∙-∈ balanced {tmps ts₁} {tmps ts₂} b₁ b₂))

thenP : ∀ {T sh sh′} {c : Code sh T} {c′ : Code sh′ T} {m m′ n n′ t₁ t₂}
      → Out c m n t₁ c′ m′ n′ → Paused c′ m′ n′ t₂ → Paused c m n (t₁ ++ t₂)
thenP {t₁ = t₁} {t₂} (out ts₁ m₁ st₁ w₁ b₁) (paused c″ m″ n″ ts₂ m₂ t₀ st₂ w₂ p cl l) =
  paused c″ m″ n″ (ts₁ ++ ts₂) (m₁ ++ m₂) (erase t₁ ++ t₀) (steps-++ st₁ st₂) (w-++ w₁ w₂)
         (subst (_≼ erase t₁ ++ t₀) (sym (erase-++ t₁ t₂)) (++-≼ (erase t₁) p))
         (++⁺ (erase-clean t₁) cl)
         (subst TLeg (sym (map-++ tmp ts₁ ts₂)) (IsSubmonoid.∙-∈ legal {tmps ts₁} {tmps ts₂} (fst b₁) l))

thenR : ∀ {T sh sh′ E Es B S} (o : Outcome B) {c : Code sh T} {c′ : Code sh′ T} {m m′ n n′ t₁ t₂}
        {k : Code (E ∷ Es ∣ B ∷ S) T} {e es os}
      → Out c m n t₁ c′ m′ n′ → SimR o c′ m′ n′ t₂ k e es os → SimR o c m n (t₁ ++ t₂) k e es os
thenR (gives _ _) a r = then a r
thenR (stop _)    a r = thenP a r

-- inside a frame
framed : ∀ {T sh sh′} {c : Code sh T} {c′ : Code sh′ T} {m m′ n n′ t}
       → Out c m n t (leave ⨾ c′) m′ n′ → Out (enter ⨾ c) m n t c′ m′ n′
framed {t = t} (out ts mt st w b) =
  out (tnew fsz ∷ (ts ++ tdel fsz ∷ [])) (tmp (tnew fsz) ∷ (mt ++ tmp (tdel fsz) ∷ []))
      (s-enter ⟫ steps-++ st (one s-leave))
      (w-tmp (subst (λ z → Weave tmp z (ts ++ tdel fsz ∷ []) (mt ++ tmp (tdel fsz) ∷ []))
                    (++-identityʳ (erase t)) (w-++ w (w-tmp w-[]))))
      (bracket fsz ts b)

framedP : ∀ {T sh} {c : Code sh T} {m n t} → Paused c m n t → Paused (enter ⨾ c) m n t
framedP (paused c′ m′ n′ ts mt t₀ st w p cl l) =
  paused c′ m′ n′ (tnew fsz ∷ ts) (tmp (tnew fsz) ∷ mt) t₀ (s-enter ⟫ st) (w-tmp w) p cl (opened fsz ts l)

framedR : ∀ {T sh E Es B S} (o : Outcome B) {c : Code sh T} {m n t} {k : Code (E ∷ Es ∣ B ∷ S) T} {e es os}
        → SimR o c m n t (leave ⨾ k) e es os → SimR o (enter ⨾ c) m n t k e es os
framedR (gives _ _) r = framed r
framedR (stop _)    r = framedP r

-- a view opened by a silent step, closed after
around : ∀ {T E E′ Es B S S₀} (o : Outcome B) {c₀ : Code (E ∷ Es ∣ S₀) T} {c₁ : Code (E′ ∷ E ∷ Es ∣ S₀) T}
           {e : MV E} {e′ : MV E′} {es : Stk Es} {v : Stk S₀} {os : Stk S} {n t} {k : Code (E ∷ Es ∣ B ∷ S) T}
       → Step c₀ (e ∷ˢ es ∥ v) n [] c₁ (e′ ∷ˢ e ∷ˢ es ∥ v) n
       → SimR o c₁ (e′ ∷ˢ e ∷ˢ es ∥ v) n t (epop ⨾ k) e′ (e ∷ˢ es) os
       → SimR o c₀ (e ∷ˢ es ∥ v) n t k e es os
around (gives _ _) x r = pre x (after r s-epop)
around (stop _)    x r = preP x r

-- a stretch whose trace gains `++ []`
P-[] : ∀ {T sh} {c : Code sh T} {m n t} → Paused c m n t → Paused c m n (t ++ [])
P-[] {t = t} (paused c′ m′ n′ ts mt t₀ st w p cl l) =
  paused c′ m′ n′ ts mt t₀ st w (subst (_≼ t₀) (sym (trans (erase-++ t []) (++-identityʳ (erase t)))) p) cl l

O-[] : ∀ {T sh sh′} {c : Code sh T} {c′ : Code sh′ T} {m m′ n n′ t}
     → Out c m n t c′ m′ n′ → Out c m n (t ++ []) c′ m′ n′
O-[] {t = t} (out ts mt st w b) =
  out ts mt st (subst (λ z → Weave tmp z ts mt) (sym (trans (erase-++ t []) (++-identityʳ (erase t)))) w) b

-- the run's own temporaries: erased, the same events
tmpR : ∀ {T sh E Es B S} (o : Outcome B) {c : Code sh T} {m n t t″ ts₀} {k : Code (E ∷ Es ∣ B ∷ S) T} {e es os}
     → Weave tmp t ts₀ t″ → SimR o c m n t k e es os → SimR o c m n t″ k e es os
tmpR (gives _ _) w (out ts mt st wv b) = out ts mt st (subst (λ z → Weave tmp z ts mt) (sym (erase-weave w)) wv) b
tmpR (stop _)    w (paused c′ m′ n′ ts mt t₀ st wv p cl l) =
  paused c′ m′ n′ ts mt t₀ st wv (subst (_≼ t₀) (sym (erase-weave w)) p) cl l

-- a run cut short: what the machine did for the whole run covers the prefix
cutR : ∀ {T sh E Es B S} (o : Outcome B) {c : Code sh T} {m n t t′} {k : Code (E ∷ Es ∣ B ∷ S) T} {e es os}
     → t′ ≼ t → SimR o c m n t k e es os → Paused c m n t′
cutR (gives _ _) {t = t} q (out ts mt st w b) = paused _ _ _ ts mt (erase t) st w (erase-≼ q) (erase-clean t) (fst b)
cutR (stop _) q (paused c′ m′ n′ ts mt t₀ st w p cl l) = paused c′ m′ n′ ts mt t₀ st w (≼-trans (erase-≼ q) p) cl l

done∅ : ∀ {T sh} {c : Code sh T} {m n} → Out c m n [] c m n
done∅ = out [] [] done w-[] bal∅

------------------------------------------------------------------------
-- 6. ★ THE SIMULATION.
------------------------------------------------------------------------

-- this lowering folds plainly; a fold that may rebuild in place (A8) is the
-- compiler's other choice
isReuse : ∀ {Γ E A B} → Tm Γ E A B → Bool
isReuse (lIn ∘l g) = true
isReuse _          = false

mutual
  Frag : ∀ {Γ} (ds : Defs Γ) {E A B} → Tm Γ E A B → Set
  Frag ds (f ∘l g)      = Frag ds f × Frag ds g
  Frag ds (f ⊗l g)      = Frag ds f × Frag ds g
  Frag ds (lcase f g)   = Frag ds f × Frag ds g
  Frag ds (lcata F alg) = Frag ds alg × isReuse alg ≡ false
  Frag ds (liter f φ)     = Frag ds f
  Frag ds (lapp p)      = FragB ds p
  Frag ds (lend b)      = Frag ds b
  Frag ds (blift f)     = Frag ds f
  Frag ds (bfst f)      = Frag ds f
  Frag ds (bsnd f)      = Frag ds f
  Frag ds (bcaseE f g)  = Frag ds f × Frag ds g
  Frag ds (bout f)      = Frag ds f
  Frag ds (bapp p)      = FragΩ ds p
  Frag ds _             = ⊤

  FragB : ∀ {Γ l g X A B} (ds : Defs Γ) → Γ ∋[ l ] sg once g X A B → Set
  FragB (ds ▸ _)    (there p) = FragB ds p
  FragB (ds ▸ b1 b _) here      = Frag ds b

  FragΩ : ∀ {Γ l g X A B} (ds : Defs Γ) → Γ ∋[ l ] sg many g X A B → Set
  FragΩ (ds ▸ _)    (there p) = FragΩ ds p
  FragΩ (ds ▸ bω b _) here      = Frag ds b

look-body : ∀ {Γ Δ l g X A B} {ds : Defs Γ} {p : Γ ∋[ l ] sg once g X A B} {ds′ : Defs Δ} {b : LTm Δ (X ⊗t A) B} {γ : Gd g b}
          → Look ds p ds′ (b1 b γ) → ∀ {Es S T} (k : Code (One ∷ Es ∣ B ∷ S) T) → body ds p k ≡ comp ds′ b k
look-body lk-here      k = refl
look-body (lk-there q) k = look-body q k

look-frag : ∀ {Γ Δ l g X A B} {ds : Defs Γ} {p : Γ ∋[ l ] sg once g X A B} {ds′ : Defs Δ} {b : LTm Δ (X ⊗t A) B} {γ : Gd g b}
          → Look ds p ds′ (b1 b γ) → FragB ds p → Frag ds′ b
look-frag lk-here      fr = fr
look-frag (lk-there q) fr = look-frag q fr

look-bodyω : ∀ {Γ Δ l g X A B} {ds : Defs Γ} {p : Γ ∋[ l ] sg many g X A B} {ds′ : Defs Δ} {b : Tm Δ X A B} {γ : Gd g b}
           → Look ds p ds′ (bω b γ) → ∀ {Es S T} (k : Code (X ∷ Es ∣ B ∷ S) T) → bodyω ds p k ≡ comp ds′ b k
look-bodyω lk-here      k = refl
look-bodyω (lk-there q) k = look-bodyω q k

look-fragω : ∀ {Γ Δ l g X A B} {ds : Defs Γ} {p : Γ ∋[ l ] sg many g X A B} {ds′ : Defs Δ} {b : Tm Δ X A B} {γ : Gd g b}
           → Look ds p ds′ (bω b γ) → FragΩ ds p → Frag ds′ b
look-fragω lk-here      fr = fr
look-fragω (lk-there q) fr = look-fragω q fr

simM : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x o n t}
     → RunMap ds F alg e G x n o t → Frag ds alg → isReuse alg ≡ false
     → ∀ {Es S T} (es : Stk Es) (os : Stk S) (k : Code (E ∷ Es ∣ LF∙ G A ∷ S) T)
     → SimR o (trav ds F alg G k) (e ∷ˢ es ∥ x ∷ˢ os) n t k e es os

-- ★ the machine runs the compiled code as the term runs, for every outcome
sim : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v o n t}
    → Run ds f e v n o t → Frag ds f
    → ∀ {Es S T} (es : Stk Es) (os : Stk S) (k : Code (E ∷ Es ∣ B ∷ S) T)
    → SimR o (comp ds f k) (e ∷ˢ es ∥ v ∷ˢ os) n t k e es os
sim r-id fr es os k = done∅
sim (r-∘ rg (go-on {o = o} rf)) (ff , fg) es os k = thenR o (sim rg fg es os _) (sim rf ff es os k)
sim (r-∘ rg stopped) (ff , fg) es os k = P-[] (sim rg fg es os _)
sim (r-⊗ {c = c} rf (go-on {u = a′} (fm-gives rg))) (ff , fg) es os k =
  pre s-unpair (then (sim rf ff es (c ∷ˢ os) _) (pre s-swap (after (after (sim rg fg es (a′ ∷ˢ os) _) s-swap) s-pair)))
sim (r-⊗ {c = c} rf (go-on {u = a′} (fm-stop rg))) (ff , fg) es os k =
  preP s-unpair (thenP (sim rf ff es (c ∷ˢ os) _) (preP s-swap (sim rg fg es (a′ ∷ˢ os) _)))
sim (r-⊗ {c = c} rf stopped) (ff , fg) es os k = P-[] (preP s-unpair (sim rf ff es (c ∷ˢ os) _))
sim r-ρ     fr es os k = leaf (s-prim r-ρ) []
sim r-ρ⁻    fr es os k = leaf (s-prim r-ρ⁻) []
sim r-λ     fr es os k = leaf (s-prim r-λ) []
sim r-λ⁻    fr es os k = leaf (s-prim r-λ⁻) []
sim r-α     fr es os k = leaf (s-prim r-α) []
sim r-α⁻    fr es os k = leaf (s-prim r-α⁻) []
sim r-swap  fr es os k = leaf (s-prim r-swap) []
sim (r-dup {v = v} {n}) fr es os k = leaf (s-prim r-dup) (NoT-copy v n)
sim (r-drop {v = v}) fr es os k = leaf (s-prim r-drop) (NoT-freeAll v)
sim r-inl   fr es os k = leaf (s-prim r-inl) []
sim r-inr   fr es os k = leaf (s-prim r-inr) []
sim (r-case₁ {o = o} r) (ff , fg) es os k = preR o s-case₁ (sim r ff es os k)
sim (r-case₂ {o = o} r) (ff , fg) es os k = preR o s-case₂ (sim r fg es os k)
sim r-In    fr es os k = leaf (s-prim r-In) (k-alloc ∷ [])
sim r-Outμ  fr es os k = leaf (s-prim r-Outμ) (k-free ∷ [])
sim r-clo   fr es os k = leaf (s-prim r-clo) []
sim (r-app {e = e} {o = o} q r) fr es os k
  rewrite look-body q {Es = _ ∷ _} (epop ⨾ leave ⨾ k) =
  preR o s-untag (framedR o (around o s-elift (sim r (look-frag q fr) (e ∷ˢ es) os _)))
sim (r-cata rm (go-on {o = o} ra)) (fa , nr) es os k =
  thenR o (leaf s-fold (k-free ∷ [])) (framedR o (thenR o (simM rm fa nr es os _) (sim ra fa es os (leave ⨾ k))))
sim (r-cata rm stopped) (fa , nr) es os k =
  thenP (leaf s-fold (k-free ∷ [])) (framedP (P-[] (simM rm fa nr es os _)))
sim (r-cata-reuse rm th) (fa , ()) es os k
sim (r-lend {e = e} (fm-gives r)) fr es os k = pre s-elend (after (sim r fr (e ∷ˢ es) os _) s-eunlend)
sim (r-lend {e = e} (fm-stop r))  fr es os k = preP s-elend (sim r fr (e ∷ˢ es) os _)
sim (r-lift {e = e} {o = o} r) fr es os k = around o s-elift (sim r fr (e ∷ˢ es) os _)
sim (r-fst {e₁ = e₁} {e₂} {o = o} r) fr es os k = around o s-efst (sim r fr (mpair e₁ e₂ ∷ˢ es) os _)
sim (r-snd {e₁ = e₁} {e₂} {o = o} r) fr es os k = around o s-esnd (sim r fr (mpair e₁ e₂ ∷ˢ es) os _)
sim (r-caseE₁ {e = e} {o = o} r) (ff , fg) es os k = around o s-ecase₁ (sim r ff (minl e ∷ˢ es) os _)
sim (r-caseE₂ {e = e} {o = o} r) (ff , fg) es os k = around o s-ecase₂ (sim r fg (minr e ∷ˢ es) os _)
sim (r-out {B = B} {i = i} {v} {a} {o = o} {n} r) fr es os k = outR o (sim r fr (mmu i v ∷ˢ es) os _)
  where
    outR : (o : Outcome B) → ∀ {c₁ t} → SimR o c₁ (v ∷ˢ mmu i v ∷ˢ es ∥ a ∷ˢ os) n t (epop ⨾ k) v (mmu i v ∷ˢ es) os
         → SimR o (eout ⨾ c₁) (mmu i v ∷ˢ es ∥ a ∷ˢ os) n (peek i ∷ t) k (mmu i v) es os
    outR (gives _ _) r′ = then (leaf s-eout (k-peek ∷ [])) (after r′ s-epop)
    outR (stop _)    r′ = thenP (leaf s-eout (k-peek ∷ [])) r′
sim (r-copy {e = e} {n}) fr es os k = leaf s-ecopy (NoT-copy e n)
sim (r-bapp {x = x} {o = o} q r) fr es os k
  rewrite look-bodyω q {Es = _ ∷ _} (leave ⨾ epop ⨾ k) =
  around o s-eapp (framedR o (sim r (look-fragω q fr) (mct x ∷ˢ es) os _))
sim r-const fr es os k = leaf (s-prim r-const) []
sim r-op    fr es os k = leaf (s-prim r-op) (k-io ∷ [])
sim r-halt  fr es os k = paused halted _ _ [] _ _ (one s-ehalt) (w-self _) (≼-refl _) (k-stp ∷ []) tt
sim (r-iter r (go-on done)) fr es os k = O-[] (pre s-loop (after (sim r fr es os _) s-case₁))
sim (r-iter r (go-on (again {o = o} rn))) fr es os k =
  preR o s-loop (thenR o (sim r fr es os _) (preR o s-case₂ (sim rn fr es os k)))
sim (r-iter r stopped) fr es os k = P-[] (preP s-loop (sim r fr es os _))
sim r-exh fr es os k = paused _ _ _ [] [] [] done w-[] []≼ [] tt
sim (r-cut {o = o} r q) fr es os k = cutR o q (sim r fr es os k)
sim (r-tmp {o = o} r w p) fr es os k = tmpR o w (sim r fr es os k)

simM (m-id r) fa nr es os k = sim r (fa , nr) es os k
simM m-one fa nr es os k = done∅
simM m-b fa nr es os k = done∅
simM m-μ fa nr es os k = done∅
simM (m-inl (fm-gives r)) fa nr es os k = pre s-case₁ (after (simM r fa nr es os _) (s-prim r-inl))
simM (m-inl (fm-stop r))  fa nr es os k = preP s-case₁ (simM r fa nr es os _)
simM (m-inr (fm-gives r)) fa nr es os k = pre s-case₂ (after (simM r fa nr es os _) (s-prim r-inr))
simM (m-inr (fm-stop r))  fa nr es os k = preP s-case₂ (simM r fa nr es os _)
simM (m-pair {x′ = x′} r (go-on {u = y} (fm-gives r′))) fa nr es os k =
  pre s-unpair (then (simM r fa nr es (x′ ∷ˢ os) _) (pre s-swap (after (after (simM r′ fa nr es (y ∷ˢ os) _) s-swap) s-pair)))
simM (m-pair {x′ = x′} r (go-on {u = y} (fm-stop r′))) fa nr es os k =
  preP s-unpair (thenP (simM r fa nr es (x′ ∷ˢ os) _) (preP s-swap (simM r′ fa nr es (y ∷ˢ os) _)))
simM (m-pair {x′ = x′} r stopped) fa nr es os k = P-[] (preP s-unpair (simM r fa nr es (x′ ∷ˢ os) _))

------------------------------------------------------------------------
-- 7. ★ ON THE MACHINE.
------------------------------------------------------------------------

private
  pre₀ : Pre (λ _ → 0) 0 mone (λ _ → 0)
  pre₀ = record { le1 = λ _ → z≤n ; above = λ _ _ → refl ; sub = λ _ → z≤n }

-- a finished run of a closed program: the machine on its compiled code is
-- legal on the cell heap, leaves it empty, and frees every frame it entered
machine-noleak : ∀ {Γ} {ds : Defs Γ} {f : LTm Γ One One} {n′ t}
               → Run ds f mone mone 0 (gives mone n′) t → Frag ds f
               → Σ Trace λ mt → Steps (comp ds f end) (mone ∷ˢ []ˢ ∥ mone ∷ˢ []ˢ) 0 mt end (mone ∷ˢ []ˢ ∥ mone ∷ˢ []ˢ) n′
                 × OK mt (λ _ → 0) × (∀ i → play mt (λ _ → 0) i ≡ 0) × TBal mt
machine-noleak {t = t} run fr with sim run fr []ˢ []ˢ end | noleak (plain run)
... | out ts mt st w b | (ok , clean) =
  ( mt , st
  , OK-weave w (λ _ → 0) ok
  , (λ i → trans (cong (λ h → h i) (play-weave w (λ _ → 0))) (clean i))
  , weave-post (gives mone 0) w (NoT-Bal (erase t) (erase-clean t)) b )

-- ★ ANY stopped run of a closed program from nothing (a server cut after its
-- last round, a halt): the machine on its compiled code runs at least as far,
-- and what it did up to the run's last event is legal on the cell heap, with
-- legal frames
machine-legal : ∀ {Γ} {ds : Defs Γ} {f : LTm Γ One One} {y t}
              → Run ds f mone mone 0 (stop y) t → Frag ds f
              → Σ Trace λ mt′ → Σ (List TEv) λ ts′ → Weave tmp (erase t) ts′ mt′
                 × OK mt′ (λ _ → 0) × TLeg mt′
                 × Σ Trace λ mt → mt′ ≼ mt × Σ Sh λ sh → Σ (Code sh (_ ∣ _)) λ c′ → Σ (Cfg sh) λ m′ → Σ ℕ λ n′
                   → Steps (comp ds f end) (mone ∷ˢ []ˢ ∥ mone ∷ˢ []ˢ) 0 mt c′ m′ n′
machine-legal {t = t} run fr with sim run fr []ˢ []ˢ end
... | paused {sh′} c′ m′ n′ ts mt t₀ st w p cl l with weave-pre w p
...   | (ts′ , mt′ , w′ , q) =
  ( mt′ , ts′ , w′
  , OK-weave w′ (λ _ → 0) (fst (exchange (plain run) pre₀ lent₀))
  , TOK-≼ q (weave-post (stop {One} exhausted) w (fst (NoT-Bal t₀ cl)) l)
  , mt , q , sh′ , c′ , m′ , n′ , st )
