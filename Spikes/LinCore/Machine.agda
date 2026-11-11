-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Machine — plan 0.146 A16 (D410): A MODEL MACHINE, AND THE
-- SIMULATION.
--
-- A stack machine with CODE: sequences of instructions over an operand stack,
-- branching on a sum's tag (`case`), its own events per instruction. The
-- lowering (`comp`) is continuation-passing: a term is compiled in front of
-- the code that follows it. Two generators run INSIDE A FRAME (`enter` …
-- `leave`): a fold, node by node (`fold` expands into the traversal of the
-- node's children and the algebra), and a closure's body. A frame is a heap
-- block, a TEMPORARY of the lowering (A13): the fold's work stack is in the
-- heap, not on a machine stack of bounded depth.
--
-- ★ The simulation (`sim`), by induction on the run: the machine, started on
-- the compiled code, reaches the code that follows with the run's result,
-- and its events are the run's (temporaries erased) with balanced
-- temporaries woven in. Then `machine-noleak`: the machine's own trace is
-- legal on the cell heap, frees every cell, and frees every frame.
--
-- The fragment (`Frag`): every generator but the lent views (`lend`, `blift`,
-- `bfst`, `bsnd`, `bcaseE`, `bout`, `bcopy`, `bapp`), the loop and `lhalt`
-- (their lowering is the same pattern: an environment register, a back jump,
-- a stop), and a fold that may rebuild in place (A8: the compiler's choice,
-- here always the plain fold).
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
open import Relation.Nullary using (yes; no)
open import LinCore.Flat using (FTy)
open import LinCore.Free using (Weave; w-[]; w-run; w-tmp; w-++; w-self; Along-++)

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

-- the operand stack
infixr 5 _∷ˢ_
data Stk : List LTy → Set where
  []ˢ  : Stk []
  _∷ˢ_ : ∀ {A S} → MV A → Stk S → Stk (A ∷ S)

-- instructions: data moves, a generator's own step, frames, the fold
data Ins : List LTy → List LTy → Set where
  unpair : ∀ {A B S} → Ins ((A ⊗t B) ∷ S) (A ∷ B ∷ S)
  pair   : ∀ {A B S} → Ins (A ∷ B ∷ S) ((A ⊗t B) ∷ S)
  swap   : ∀ {A B S} → Ins (A ∷ B ∷ S) (B ∷ A ∷ S)
  -- a generator with no control of its own, run as one step
  prim   : ∀ {Γ} (ds : Defs Γ) {A B S} → LTm Γ A B → Ins (A ∷ S) (B ∷ S)
  -- a closure's environment, out of its tag, beside the argument
  untag  : ∀ {l X A S} → Ins ((Ct l X ⊗t A) ∷ S) ((X ⊗t A) ∷ S)
  enter  : ∀ {S} → Ins S S
  leave  : ∀ {S} → Ins S S
  -- fold the node on top with the algebra's code
  fold   : ∀ {Γ} (ds : Defs Γ) F {E A S} → Tm Γ E (LF∙ F A) A → Ins (μt F ∷ S) (A ∷ S)
  -- outside the fragment: no step
  stuck  : ∀ {S S′} → Ins S S′

-- code: instructions in order, or a branch on the tag on top
infixr 5 _⨾_
data Code : List LTy → List LTy → Set where
  end  : ∀ {S} → Code S S
  _⨾_  : ∀ {S S′ T} → Ins S S′ → Code S′ T → Code S T
  case : ∀ {A B S T} → Code (A ∷ S) T → Code (B ∷ S) T → Code ((A ⊕t B) ∷ S) T

------------------------------------------------------------------------
-- 2. THE LOWERING, in front of the code that follows.
------------------------------------------------------------------------

mutual
  comp : ∀ {Γ} (ds : Defs Γ) {E A B} → Tm Γ E A B → ∀ {S T} → Code (B ∷ S) T → Code (A ∷ S) T
  comp ds lid k            = k
  comp ds (f ∘l g) k       = comp ds g (comp ds f k)
  comp ds (f ⊗l g) k       = unpair ⨾ comp ds f (swap ⨾ comp ds g (swap ⨾ pair ⨾ k))
  comp ds (lcase f g) k    = case (comp ds f k) (comp ds g k)
  comp ds (lcata F alg) k  = fold ds F alg ⨾ k
  comp ds (lapp p) k       = untag ⨾ enter ⨾ body ds p (leave ⨾ k)
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
  comp ds (lend b) k       = stuck ⨾ k
  comp ds (blift f) k      = stuck ⨾ k
  comp ds (bfst f) k       = stuck ⨾ k
  comp ds (bsnd f) k       = stuck ⨾ k
  comp ds (bcaseE f g) k   = stuck ⨾ k
  comp ds (bout f) k       = stuck ⨾ k
  comp ds bcopy k          = stuck ⨾ k
  comp ds (bapp p) k       = stuck ⨾ k
  comp ds (lhalt s) k      = stuck ⨾ k
  comp ds (liter f) k      = stuck ⨾ k

  -- a one-shot label's body, compiled in place over its own prefix
  body : ∀ {Γ l X A B} (ds : Defs Γ) → Γ ∋[ l ] sg once X A B → ∀ {S T} → Code (B ∷ S) T → Code ((X ⊗t A) ∷ S) T
  body (ds ▸ _)    (there p) k = body ds p k
  body (ds ▸ b1 b) here      k = comp ds b k

-- a fold's node: its children folded, in order (`Idf` positions re-enter
-- the fold), the layer rebuilt around them
trav : ∀ {Γ} (ds : Defs Γ) F {E A} (alg : Tm Γ E (LF∙ F A) A) G → ∀ {S T}
     → Code (LF∙ G A ∷ S) T → Code (LF∙ G (μt F) ∷ S) T
trav ds F alg Idf      k = fold ds F alg ⨾ k
trav ds F alg Kone     k = k
trav ds F alg Kzero    k = k
trav ds F alg (Kb _)   k = k
trav ds F alg (Kμ _)   k = k
trav ds F alg (G ⊕f H) k = case (trav ds F alg G (prim ε linl ⨾ k)) (trav ds F alg H (prim ε linr ⨾ k))
trav ds F alg (G ⊗f H) k = unpair ⨾ trav ds F alg G (swap ⨾ trav ds F alg H (swap ⨾ pair ⨾ k))

------------------------------------------------------------------------
-- 3. STEPPING: one instruction, its events.
------------------------------------------------------------------------

data Step {T : List LTy} : ∀ {S S′} → Code S T → Stk S → ℕ → Trace → Code S′ T → Stk S′ → ℕ → Set where
  s-unpair : ∀ {A B S} {k : Code (A ∷ B ∷ S) T} {a : MV A} {b : MV B} {s n}
           → Step (unpair ⨾ k) (mpair a b ∷ˢ s) n [] k (a ∷ˢ b ∷ˢ s) n
  s-pair   : ∀ {A B S} {k : Code ((A ⊗t B) ∷ S) T} {a : MV A} {b : MV B} {s n}
           → Step (pair ⨾ k) (a ∷ˢ b ∷ˢ s) n [] k (mpair a b ∷ˢ s) n
  s-swap   : ∀ {A B S} {k : Code (B ∷ A ∷ S) T} {a : MV A} {b : MV B} {s n}
           → Step (swap ⨾ k) (a ∷ˢ b ∷ˢ s) n [] k (b ∷ˢ a ∷ˢ s) n
  -- a generator's own step is its run (any lent value: these read none)
  s-prim   : ∀ {Γ} {ds : Defs Γ} {A B S} {g : LTm Γ A B} {k : Code (B ∷ S) T} {v w s n n′ t}
           → Run ds g mone v n (gives w n′) t → Step (prim ds g ⨾ k) (v ∷ˢ s) n t k (w ∷ˢ s) n′
  s-untag  : ∀ {l X A S} {k : Code ((X ⊗t A) ∷ S) T} {x : MV X} {a : MV A} {s n}
           → Step (untag {l = l} ⨾ k) (mpair (mct x) a ∷ˢ s) n [] k (mpair x a ∷ˢ s) n
  s-enter  : ∀ {S} {k : Code S T} {s n} → Step (enter ⨾ k) s n (tmp (tnew fsz) ∷ []) k s n
  s-leave  : ∀ {S} {k : Code S T} {s n} → Step (leave ⨾ k) s n (tmp (tdel fsz) ∷ []) k s n
  s-case₁  : ∀ {A B S} {c₁ : Code (A ∷ S) T} {c₂ : Code (B ∷ S) T} {a s n}
           → Step (case c₁ c₂) (minl a ∷ˢ s) n [] c₁ (a ∷ˢ s) n
  s-case₂  : ∀ {A B S} {c₁ : Code (A ∷ S) T} {c₂ : Code (B ∷ S) T} {b s n}
           → Step (case c₁ c₂) (minr b ∷ˢ s) n [] c₂ (b ∷ˢ s) n
  -- a fold's node: free it, then, in a frame, fold its children and run
  -- the algebra
  s-fold   : ∀ {Γ} {ds : Defs Γ} {F E A S} {alg : Tm Γ E (LF∙ F A) A} {k : Code (A ∷ S) T} {i v s n}
           → Step (fold ds F alg ⨾ k) (mmu i v ∷ˢ s) n (free i ∷ [])
                  (enter ⨾ trav ds F alg F (comp ds alg (leave ⨾ k))) (v ∷ˢ s) n

-- many steps, their events in order
infixr 5 _⟫_
data Steps {T : List LTy} : ∀ {S S′} → Code S T → Stk S → ℕ → Trace → Code S′ T → Stk S′ → ℕ → Set where
  done : ∀ {S} {c : Code S T} {s n} → Steps c s n [] c s n
  _⟫_  : ∀ {S S′ S″} {c : Code S T} {c′ : Code S′ T} {c″ : Code S″ T} {s s′ s″ n n′ n″ t₁ t₂}
       → Step c s n t₁ c′ s′ n′ → Steps c′ s′ n′ t₂ c″ s″ n″ → Steps c s n (t₁ ++ t₂) c″ s″ n″

steps-++ : ∀ {T S S′ S″} {c : Code S T} {c′ : Code S′ T} {c″ : Code S″ T} {s s′ s″ n n′ n″ t₁ t₂}
         → Steps c s n t₁ c′ s′ n′ → Steps c′ s′ n′ t₂ c″ s″ n″ → Steps c s n (t₁ ++ t₂) c″ s″ n″
steps-++ done st₂ = st₂
steps-++ {c = c} {c″ = c″} {s = s} {s″ = s″} {n = n} {n″ = n″} {t₂ = t₂} (_⟫_ {t₁ = u₁} {t₂ = u₂} x st₁) st₂ =
  subst (λ z → Steps c s n z c″ s″ n″) (sym (++-assoc u₁ u₂ t₂)) (x ⟫ steps-++ st₁ st₂)

one : ∀ {T S S′} {c : Code S T} {c′ : Code S′ T} {s s′ n n′ t}
    → Step c s n t c′ s′ n′ → Steps c s n t c′ s′ n′
one {c = c} {c′} {s} {s′} {n} {n′} {t} x = subst (λ z → Steps c s n z c′ s′ n′) (++-identityʳ t) (x ⟫ done)

------------------------------------------------------------------------
-- 4. WHAT THE SIMULATION CLAIMS of a stretch of the machine's run: it
-- steps from one configuration to the next; its events are a run's (its
-- temporaries erased) with balanced temporaries woven in.
------------------------------------------------------------------------

record Out {T S S′} (c : Code S T) (s : Stk S) (n : ℕ) (t : Trace) (c′ : Code S′ T) (s′ : Stk S′) (n′ : ℕ) : Set where
  constructor out
  field
    ts    : List TEv
    mt    : Trace
    steps : Steps c s n mt c′ s′ n′
    woven : Weave tmp (erase t) ts mt
    bal   : TBal (tmps ts)

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

-- a silent step first
pre : ∀ {T S S′ S″} {c : Code S T} {c′ : Code S′ T} {c″ : Code S″ T} {s s′ s″ n n′ n″ t}
    → Step c s n [] c′ s′ n′ → Out c′ s′ n′ t c″ s″ n″ → Out c s n t c″ s″ n″
pre x (out ts mt st w b) = out ts mt (x ⟫ st) w b

-- a silent step after
after : ∀ {T S S′ S″} {c : Code S T} {c′ : Code S′ T} {c″ : Code S″ T} {s s′ s″ n n′ n″ t}
     → Out c s n t c′ s′ n′ → Step c′ s′ n′ [] c″ s″ n″ → Out c s n t c″ s″ n″
after {t = t} (out ts mt st w b) x =
  out ts (mt ++ []) (steps-++ st (one x))
      (subst (λ z → Weave tmp (erase t) ts z) (sym (++-identityʳ mt)) w) b

-- one step whose events hold no temporary
leaf : ∀ {T S S′} {c : Code S T} {c′ : Code S′ T} {s s′ n n′ t}
     → Step c s n t c′ s′ n′ → NoT t → Out c s n t c′ s′ n′
leaf {t = t} x nt = out [] t (one x) (subst (λ z → Weave tmp z [] t) (sym (erase-NoT t nt)) (w-self t)) bal∅

-- one stretch, then the next
then : ∀ {T S S′ S″} {c : Code S T} {c′ : Code S′ T} {c″ : Code S″ T} {s s′ s″ n n′ n″ t₁ t₂}
     → Out c s n t₁ c′ s′ n′ → Out c′ s′ n′ t₂ c″ s″ n″ → Out c s n (t₁ ++ t₂) c″ s″ n″
then {t₁ = t₁} {t₂} (out ts₁ m₁ st₁ w₁ b₁) (out ts₂ m₂ st₂ w₂ b₂) =
  out (ts₁ ++ ts₂) (m₁ ++ m₂) (steps-++ st₁ st₂)
      (subst (λ z → Weave tmp z (ts₁ ++ ts₂) (m₁ ++ m₂)) (sym (erase-++ t₁ t₂)) (w-++ w₁ w₂))
      (subst TBal (sym (map-++ tmp ts₁ ts₂)) (IsSubmonoid.∙-∈ balanced {tmps ts₁} {tmps ts₂} b₁ b₂))

-- a stretch inside a frame
framed : ∀ {T S S′} {c : Code S T} {c′ : Code S′ T} {s s′ n n′ t}
       → Out c s n t (leave ⨾ c′) s′ n′ → Out (enter ⨾ c) s n t c′ s′ n′
framed {t = t} (out ts mt st w b) =
  out (tnew fsz ∷ (ts ++ tdel fsz ∷ [])) (tmp (tnew fsz) ∷ (mt ++ tmp (tdel fsz) ∷ []))
      (s-enter ⟫ steps-++ st (one s-leave))
      (w-tmp (subst (λ z → Weave tmp z (ts ++ tdel fsz ∷ []) (mt ++ tmp (tdel fsz) ∷ []))
                    (++-identityʳ (erase t)) (w-++ w (w-tmp w-[]))))
      (bracket fsz ts b)

------------------------------------------------------------------------
-- 5. ★ THE FRAGMENT, AND THE SIMULATION.
------------------------------------------------------------------------

-- a fold whose algebra rebuilds with the same functor may reuse cells (A8);
-- this lowering always folds plainly
isReuse : ∀ {Γ E A B} → Tm Γ E A B → Bool
isReuse (lIn ∘l g) = true
isReuse _          = false

mutual
  Frag : ∀ {Γ} (ds : Defs Γ) {E A B} → Tm Γ E A B → Set
  Frag ds lid           = ⊤
  Frag ds (f ∘l g)      = Frag ds f × Frag ds g
  Frag ds (f ⊗l g)      = Frag ds f × Frag ds g
  Frag ds (lcase f g)   = Frag ds f × Frag ds g
  Frag ds (lcata F alg) = Frag ds alg × isReuse alg ≡ false
  Frag ds (lapp p)      = FragB ds p
  Frag ds ρl            = ⊤
  Frag ds ρl⁻           = ⊤
  Frag ds lul           = ⊤
  Frag ds lul⁻          = ⊤
  Frag ds lassoc        = ⊤
  Frag ds lassoc⁻       = ⊤
  Frag ds lswap         = ⊤
  Frag ds dup           = ⊤
  Frag ds drop          = ⊤
  Frag ds linl          = ⊤
  Frag ds linr          = ⊤
  Frag ds lIn           = ⊤
  Frag ds lOutμ         = ⊤
  Frag ds (lclo F p)    = ⊤
  Frag ds (lconst v)    = ⊤
  Frag ds (lop s)       = ⊤
  Frag ds lzero         = ⊤
  Frag ds (lend b)      = ⊥
  Frag ds (blift f)     = ⊥
  Frag ds (bfst f)      = ⊥
  Frag ds (bsnd f)      = ⊥
  Frag ds (bcaseE f g)  = ⊥
  Frag ds (bout f)      = ⊥
  Frag ds bcopy         = ⊥
  Frag ds (bapp p)      = ⊥
  Frag ds (lhalt s)     = ⊥
  Frag ds (liter f)     = ⊥

  FragB : ∀ {Γ l X A B} (ds : Defs Γ) → Γ ∋[ l ] sg once X A B → Set
  FragB (ds ▸ _)    (there p) = FragB ds p
  FragB (ds ▸ b1 b) here      = Frag ds b

-- what a label runs is what the lowering compiled in place, and in the fragment
look-body : ∀ {Γ Δ l X A B} {ds : Defs Γ} {p : Γ ∋[ l ] sg once X A B} {ds′ : Defs Δ} {b : LTm Δ (X ⊗t A) B}
          → Look ds p ds′ (b1 b) → ∀ {S T} (k : Code (B ∷ S) T) → body ds p k ≡ comp ds′ b k
look-body lk-here      k = refl
look-body (lk-there q) k = look-body q k

look-frag : ∀ {Γ Δ l X A B} {ds : Defs Γ} {p : Γ ∋[ l ] sg once X A B} {ds′ : Defs Δ} {b : LTm Δ (X ⊗t A) B}
          → Look ds p ds′ (b1 b) → FragB ds p → Frag ds′ b
look-frag lk-here      fr = fr
look-frag (lk-there q) fr = look-frag q fr

simM : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x y n n′ t}
     → RunMap ds F alg e G x n (gives y n′) t → Frag ds alg → isReuse alg ≡ false
     → ∀ {S T} (s : Stk S) (k : Code (LF∙ G A ∷ S) T) → Out (trav ds F alg G k) (x ∷ˢ s) n t k (y ∷ˢ s) n′

-- ★ the machine runs the compiled code as the term runs
sim : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v w n n′ t}
    → Run ds f e v n (gives w n′) t → Frag ds f
    → ∀ {S T} (s : Stk S) (k : Code (B ∷ S) T) → Out (comp ds f k) (v ∷ˢ s) n t k (w ∷ˢ s) n′
sim r-id fr s k = out [] [] done w-[] bal∅
sim (r-∘ rg (go-on rf)) (ff , fg) s k = then (sim rg fg s _) (sim rf ff s k)
sim (r-⊗ {a = a} {c = c} rf (go-on (fm-gives {u = c′} rg))) (ff , fg) s k =
  pre s-unpair (then (sim rf ff (c ∷ˢ s) _) (pre s-swap (after (after (sim rg fg _ _) s-swap) s-pair)))
sim r-ρ     fr s k = leaf (s-prim r-ρ) []
sim r-ρ⁻    fr s k = leaf (s-prim r-ρ⁻) []
sim r-λ     fr s k = leaf (s-prim r-λ) []
sim r-λ⁻    fr s k = leaf (s-prim r-λ⁻) []
sim r-α     fr s k = leaf (s-prim r-α) []
sim r-α⁻    fr s k = leaf (s-prim r-α⁻) []
sim r-swap  fr s k = leaf (s-prim r-swap) []
sim (r-dup {v = v} {n}) fr s k = leaf (s-prim r-dup) (NoT-copy v n)
sim (r-drop {v = v}) fr s k = leaf (s-prim r-drop) (NoT-freeAll v)
sim r-inl   fr s k = leaf (s-prim r-inl) []
sim r-inr   fr s k = leaf (s-prim r-inr) []
sim (r-case₁ r) (ff , fg) s k = pre s-case₁ (sim r ff s k)
sim (r-case₂ r) (ff , fg) s k = pre s-case₂ (sim r fg s k)
sim r-In    fr s k = leaf (s-prim r-In) (k-alloc ∷ [])
sim r-Outμ  fr s k = leaf (s-prim r-Outμ) (k-free ∷ [])
sim r-clo   fr s k = leaf (s-prim r-clo) []
sim (r-app {b = b} q r) fr s k =
  pre s-untag (framed (subst (λ c → Out c _ _ _ _ _ _) (sym (look-body q (leave ⨾ k))) (sim r (look-frag q fr) s (leave ⨾ k))))
sim (r-cata rm (go-on ra)) (fa , nr) s k =
  then (leaf s-fold (k-free ∷ []))
       (framed (then (simM rm fa nr s _) (sim ra fa s (leave ⨾ k))))
sim (r-cata-reuse rm th) (fa , ()) s k
sim (r-lend _) () s k
sim (r-lift _) () s k
sim (r-fst _) () s k
sim (r-snd _) () s k
sim (r-caseE₁ _) () s k
sim (r-caseE₂ _) () s k
sim (r-out _) () s k
sim r-copy () s k
sim (r-bapp _ _) () s k
sim r-const fr s k = leaf (s-prim r-const) []
sim r-op    fr s k = leaf (s-prim r-op) (k-io ∷ [])
sim (r-iter _ _) () s k
sim (r-tmp {t = t} {t′ = t″} r w p) fr s k with sim r fr s k
... | out ts mt st wv b = out ts mt st (subst (λ z → Weave tmp z ts mt) (sym (erase-weave w)) wv) b

simM (m-id r) fa nr s k = sim r (fa , nr) s k
simM m-one fa nr s k = out [] [] done w-[] bal∅
simM m-b fa nr s k = out [] [] done w-[] bal∅
simM m-μ fa nr s k = out [] [] done w-[] bal∅
simM (m-inl (fm-gives r)) fa nr s k = pre s-case₁ (after (simM r fa nr s _) (s-prim r-inl))
simM (m-inr (fm-gives r)) fa nr s k = pre s-case₂ (after (simM r fa nr s _) (s-prim r-inr))
simM (m-pair {x′ = x′} r (go-on (fm-gives r′))) fa nr s k =
  pre s-unpair (then (simM r fa nr (x′ ∷ˢ s) _) (pre s-swap (after (after (simM r′ fa nr _ _) s-swap) s-pair)))

------------------------------------------------------------------------
-- 6. ★ LEAK-FREE, ON THE MACHINE: a finished run of a closed program in the
-- fragment; the machine, on its compiled code, is legal on the cell heap,
-- leaves it empty, and frees every frame it entered.
------------------------------------------------------------------------

machine-noleak : ∀ {Γ} {ds : Defs Γ} {f : LTm Γ One One} {n′ t}
               → Run ds f mone mone 0 (gives mone n′) t → Frag ds f
               → Σ Trace λ mt → Steps (comp ds f end) (mone ∷ˢ []ˢ) 0 mt end (mone ∷ˢ []ˢ) n′
                 × OK mt (λ _ → 0) × (∀ i → play mt (λ _ → 0) i ≡ 0) × TBal mt
machine-noleak {t = t} run fr with sim run fr []ˢ end | noleak (plain run)
... | out ts mt st w b | (ok , clean) =
  ( mt , st
  , OK-weave w (λ _ → 0) ok
  , (λ i → trans (cong (λ h → h i) (play-weave w (λ _ → 0))) (clean i))
  , weave-post (gives mone 0) w (NoT-Bal (erase t) (erase-clean t)) b )
