-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Act — plan 0.146 A1: effects over the linear core, and the loop.
--
-- Once's effects are blocks of SigOps inside loops (D317): `Act A B` is a
-- finite block, and a server is the anamorphism into `Eff`, which is the loop
-- `iter round seed` over a round `Act A (B + A)`. The core stays pure; this
-- layer sits on it:
--
--   * `ATm E A B` — a ROUND: core steps (`BTm`, so it may read a lent `E`),
--     sequencing, both sides of a pair, a case, and the SigOps: `aop s` (Pure
--     or Emits: an event, and the world's answer) and `ahalt s` (Halts: the
--     run ends; its codomain is `Zero`).
--   * `Loop round` — `k` rounds, each continuing with the next state.
--
-- The world chooses every answer (`io s x y`: any `y`), so a run is any run the
-- world allows. The memory theorems are about every one of them:
--
--   * `exchangeA`: a round's heap events are legal; if it returns, its output's
--     cells replace its input's (the frame untouched); if it HALTS, only
--     legality is claimed — what is live at an exit stays (the user's
--     exception, 2026-11-08; master's `Run.LeakFree`'s `StoppedAt`).
--   * `loop-exchange`: after any number of rounds the heap is the frame plus
--     the CURRENT STATE's cells. A server's memory is its state, round after
--     round: the space claim, at round boundaries, for a run that never ends.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n+m)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List using (List; []; _∷_; _++_; map)

module LinCore.Act
  (Base : Set) (⟦_⟧b : Base → Set)
  -- the SigOps: each takes a base value and answers one (an `Int → Int` op,
  -- an emit answering `Unit`, …); which ones halt is the term's choice
  (Sig : Set) (sdom scod : Sig → Base)
  where

open import LinCore.NbEPLinCore Base ⟦_⟧b
open import LinCore.Events Base ⟦_⟧b
open Pre

------------------------------------------------------------------------
-- 1. ROUNDS.
------------------------------------------------------------------------

infixl 5 _⨾_
infixr 7 _⊗a_
data ATm (E : LTy) : LTy → LTy → Set where
  apure : ∀ {A B} → BTm E A B → ATm E A B
  _⨾_   : ∀ {A B C} → ATm E A B → ATm E B C → ATm E A C
  _⊗a_  : ∀ {A B C D} → ATm E A B → ATm E C D → ATm E (A ⊗t C) (B ⊗t D)   -- left, then right
  acase : ∀ {A B C} → ATm E A C → ATm E B C → ATm E (A ⊕t B) C
  aop   : (s : Sig) → ATm E (Bt (sdom s)) (Bt (scod s))                   -- Pure / Emits
  ahalt : (s : Sig) → ATm E (Bt (sdom s)) Zero                            -- Halts

-- what a run shows: its heap events, its SigOp calls, its halt
data AEv : Set where
  mem  : Ev → AEv
  io   : (s : Sig) → ⟦ sdom s ⟧b → ⟦ scod s ⟧b → AEv
  stop : (s : Sig) → ⟦ sdom s ⟧b → AEv

memOf : List AEv → Trace
memOf []             = []
memOf (mem e ∷ t)    = e ∷ memOf t
memOf (io _ _ _ ∷ t) = memOf t
memOf (stop _ _ ∷ t) = memOf t

memOf-++ : ∀ t₁ t₂ → memOf (t₁ ++ t₂) ≡ memOf t₁ ++ memOf t₂
memOf-++ []             t₂ = refl
memOf-++ (mem e ∷ t₁)   t₂ = cong (e ∷_) (memOf-++ t₁ t₂)
memOf-++ (io _ _ _ ∷ t₁) t₂ = memOf-++ t₁ t₂
memOf-++ (stop _ _ ∷ t₁) t₂ = memOf-++ t₁ t₂

memOf-map : ∀ t → memOf (map mem t) ≡ t
memOf-map []      = refl
memOf-map (e ∷ t) = cong (e ∷_) (memOf-map t)

-- a round either returns (a value, the counter after it) or halts
data Outcome (B : LTy) : Set where
  ret    : MV B → ℕ → Outcome B
  halted : Outcome B

data RunA {E : LTy} : ∀ {A B} → ATm E A B → MV E → MV A → ℕ → Outcome B → List AEv → Set where
  a-pure    : ∀ {A B} {b : BTm E A B} {e a w n n′ t}
            → RunB b e a n w n′ t → RunA (apure b) e a n (ret w n′) (map mem t)
  a-seq     : ∀ {A B C} {f : ATm E A B} {g : ATm E B C} {e a u n n₁ o t₁ t₂}
            → RunA f e a n (ret u n₁) t₁ → RunA g e u n₁ o t₂ → RunA (f ⨾ g) e a n o (t₁ ++ t₂)
  a-seq!    : ∀ {A B C} {f : ATm E A B} {g : ATm E B C} {e a n t₁}
            → RunA f e a n halted t₁ → RunA (f ⨾ g) e a n halted t₁
  a-⊗       : ∀ {A B C D} {f : ATm E A B} {g : ATm E C D} {e a a′ c c′ n n₁ n₂ t₁ t₂}
            → RunA f e a n (ret a′ n₁) t₁ → RunA g e c n₁ (ret c′ n₂) t₂
            → RunA (f ⊗a g) e (mpair a c) n (ret (mpair a′ c′) n₂) (t₁ ++ t₂)
  a-⊗!₁     : ∀ {A B C D} {f : ATm E A B} {g : ATm E C D} {e a c n t₁}
            → RunA f e a n halted t₁ → RunA (f ⊗a g) e (mpair a c) n halted t₁
  a-⊗!₂     : ∀ {A B C D} {f : ATm E A B} {g : ATm E C D} {e a a′ c n n₁ t₁ t₂}
            → RunA f e a n (ret a′ n₁) t₁ → RunA g e c n₁ halted t₂
            → RunA (f ⊗a g) e (mpair a c) n halted (t₁ ++ t₂)
  a-case₁   : ∀ {A B C} {f : ATm E A C} {g : ATm E B C} {e a n o t}
            → RunA f e a n o t → RunA (acase f g) e (minl a) n o t
  a-case₂   : ∀ {A B C} {f : ATm E A C} {g : ATm E B C} {e b n o t}
            → RunA g e b n o t → RunA (acase f g) e (minr b) n o t
  -- a SigOp: an event, and whatever the world answers (a word: no cell)
  a-op      : ∀ {s e x y n} → RunA (aop s) e (mbase x) n (ret (mbase y) n) (io s x y ∷ [])
  a-halt    : ∀ {s e x n} → RunA (ahalt s) e (mbase x) n halted (stop s x ∷ [])

------------------------------------------------------------------------
-- 2. THE MEMORY OF A ROUND.
------------------------------------------------------------------------

private
  chain : ∀ P U H₁ W V H → P + U ≡ H₁ + W → H₁ + V ≡ H + U → P + V ≡ H + W
  chain P U H₁ W V H e₁ e₂ = cancelʳ U (trans (r1 P V U) (trans (cong (_+ V) e₁) (trans (r2 H₁ W V) (trans (cong (_+ W) e₂) (r3 H U W)))))
    where
      r1 : ∀ P V U → (P + V) + U ≡ (P + U) + V
      r1 = solve-∀
      r2 : ∀ H₁ W V → (H₁ + W) + V ≡ (H₁ + V) + W
      r2 = solve-∀
      r3 : ∀ H U W → (H + U) + W ≡ (H + W) + U
      r3 = solve-∀
      cancelˡ : ∀ c {a b} → c + a ≡ c + b → a ≡ b
      cancelˡ zero    e = e
      cancelˡ (suc c) e = cancelˡ c (cong (λ { zero → zero ; (suc x) → x }) e)
      cancelʳ : ∀ c {a b} → a + c ≡ b + c → a ≡ b
      cancelʳ c {a} {b} e = cancelˡ c (trans (comm c a) (trans e (comm b c)))
        where comm : ∀ x y → x + y ≡ y + x
              comm = solve-∀
  chain⊗ : ∀ P B H₁ B′ A H A′ → P + B ≡ H₁ + B′ → H₁ + A ≡ H + A′ → P + (A + B) ≡ H + (A′ + B′)
  chain⊗ P B H₁ B′ A H A′ e₁ e₂ =
    trans (r1 P A B) (trans (cong (_+ A) e₁) (trans (r2 H₁ B′ A) (trans (cong (_+ B′) e₂) (r3 H A′ B′))))
    where
      r1 : ∀ P A B → P + (A + B) ≡ (P + B) + A
      r1 = solve-∀
      r2 : ∀ H₁ B′ A → (H₁ + B′) + A ≡ (H₁ + A) + B′
      r2 = solve-∀
      r3 : ∀ H A′ B′ → (H + A′) + B′ ≡ H + (A′ + B′)
      r3 = solve-∀
  assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  assoc = solve-∀
  sw : ∀ A′ B R → A′ + (B + R) ≡ B + (A′ + R)
  sw = solve-∀
  +≡0ˡ : ∀ m n → m + n ≡ 0 → m ≡ 0
  +≡0ˡ zero n e = refl
  +≡0ʳ : ∀ m n → m + n ≡ 0 → n ≡ 0
  +≡0ʳ zero n e = e

monoA : ∀ {E A B} {f : ATm E A B} {e a w n n′ t} → RunA f e a n (ret w n′) t → n ≤ n′
monoA (a-pure r)    = monoB r
monoA (a-seq rf rg) = ≤-trans (monoA rf) (monoA rg)
monoA (a-⊗ rf rg)   = ≤-trans (monoA rf) (monoA rg)
monoA (a-case₁ r)   = monoA r
monoA (a-case₂ r)   = monoA r
monoA a-op          = ≤-refl

belowA : ∀ {E A B} {f : ATm E A B} {e a w n n′ t} → RunA f e a n (ret w n′) t → Below a n → Below w n′
belowA (a-pure r)    b = belowB r b
belowA (a-seq rf rg) b = belowA rg (belowA rf b)
belowA (a-⊗ {a = a} {c = c} rf rg) b i le =
  cong₂ _+_ (belowA rf (λ j l → +≡0ˡ (cnt a j) (cnt c j) (b j l)) i (≤-trans (monoA rg) le))
            (belowA rg (λ j l → +≡0ʳ (cnt a j) (cnt c j) (b j (≤-trans (monoA rf) l))) i le)
belowA (a-case₁ r)   b = belowA r b
belowA (a-case₂ r)   b = belowA r b
belowA a-op          b i le = refl

-- what a round claims of the heap, by how it ended
Post : ∀ {A B} → Trace → Heap → MV A → Outcome B → Set
Post t h a (ret w n′) = ∀ i → play t h i + cnt a i ≡ h i + cnt w i
Post t h a halted     = ⊤

exchangeA : ∀ {E A B} {f : ATm E A B} {e a n o t} → RunA f e a n o t → ∀ {h r} → Pre h n a r → Lent e r
          → OK (memOf t) h × Post (memOf t) h a o
exchangeA (a-pure {t = t} r) {h} pre lent
  rewrite memOf-map t = exchangeB r pre lent
exchangeA (a-seq {a = a} {u} {o = ret w n′} {t₁} {t₂} rf rg) {h} pre lent with exchangeA rf pre lent
... | (ok₁ , eq₁) with exchangeA rg (post-gen (monoA rf) (belowA rf) pre ok₁ eq₁) lent
...   | (ok₂ , eq₂) rewrite memOf-++ t₁ t₂ =
  ( OK-++ (memOf t₁) (memOf t₂) h ok₁ ok₂
  , λ i → trans (cong (λ z → z i + cnt a i) (play-++ (memOf t₁) (memOf t₂) h))
            (chain (play (memOf t₂) (play (memOf t₁) h) i) (cnt u i) (play (memOf t₁) h i) (cnt w i) (cnt a i) (h i) (eq₂ i) (eq₁ i)) )
exchangeA (a-seq {o = halted} {t₁} {t₂} rf rg) {h} pre lent with exchangeA rf pre lent
... | (ok₁ , eq₁) with exchangeA rg (post-gen (monoA rf) (belowA rf) pre ok₁ eq₁) lent
...   | (ok₂ , _) rewrite memOf-++ t₁ t₂ = (OK-++ (memOf t₁) (memOf t₂) h ok₁ ok₂ , tt)
exchangeA (a-seq! r) pre lent = (fst (exchangeA r pre lent) , tt)
exchangeA (a-⊗ {a = a} {a′} {c} {c′} {t₁ = t₁} {t₂} rf rg) {h} {r} pre lent
  with exchangeA rf {h} {λ i → cnt c i + r i}
         record { le1 = le1 pre ; above = above pre
                ; sub = λ i → subst (_≤ h i) (assoc (cnt a i) (cnt c i) (r i)) (sub pre i) }
         (λ i p → ≤-trans (lent i p) (m≤n+m (r i) (cnt c i)))
... | (ok₁ , eq₁)
  with exchangeA rg {play (memOf t₁) h} {λ i → cnt a′ i + r i}
         (let p₁ = post-gen {v = a} {w = a′} {r = λ i → cnt c i + r i} (monoA rf) (belowA rf)
                     (record { le1 = le1 pre ; above = above pre
                             ; sub = λ i → subst (_≤ h i) (assoc (cnt a i) (cnt c i) (r i)) (sub pre i) })
                     ok₁ eq₁
          in record { le1 = le1 p₁ ; above = above p₁
                    ; sub = λ i → subst (_≤ play (memOf t₁) h i) (sw (cnt a′ i) (cnt c i) (r i)) (sub p₁ i) })
         (λ i p → ≤-trans (lent i p) (m≤n+m (r i) (cnt a′ i)))
...   | (ok₂ , eq₂) rewrite memOf-++ t₁ t₂ =
  ( OK-++ (memOf t₁) (memOf t₂) h ok₁ ok₂
  , λ i → trans (cong (λ z → z i + (cnt a i + cnt c i)) (play-++ (memOf t₁) (memOf t₂) h))
            (chain⊗ (play (memOf t₂) (play (memOf t₁) h) i) (cnt c i) (play (memOf t₁) h i) (cnt c′ i)
                    (cnt a i) (h i) (cnt a′ i) (eq₂ i) (eq₁ i)) )
exchangeA (a-⊗!₁ {a = a} {c} r) {h} {rf} pre lent =
  ( fst (exchangeA r {h} {λ i → cnt c i + rf i}
           record { le1 = le1 pre ; above = above pre
                  ; sub = λ i → subst (_≤ h i) (assoc (cnt a i) (cnt c i) (rf i)) (sub pre i) }
           (λ i p → ≤-trans (lent i p) (m≤n+m (rf i) (cnt c i))))
  , tt )
exchangeA (a-⊗!₂ {a = a} {a′} {c} {t₁ = t₁} {t₂} rf rg) {h} {r} pre lent
  with exchangeA rf {h} {λ i → cnt c i + r i}
         record { le1 = le1 pre ; above = above pre
                ; sub = λ i → subst (_≤ h i) (assoc (cnt a i) (cnt c i) (r i)) (sub pre i) }
         (λ i p → ≤-trans (lent i p) (m≤n+m (r i) (cnt c i)))
... | (ok₁ , eq₁)
  with exchangeA rg {play (memOf t₁) h} {λ i → cnt a′ i + r i}
         (let p₁ = post-gen {v = a} {w = a′} {r = λ i → cnt c i + r i} (monoA rf) (belowA rf)
                     (record { le1 = le1 pre ; above = above pre
                             ; sub = λ i → subst (_≤ h i) (assoc (cnt a i) (cnt c i) (r i)) (sub pre i) })
                     ok₁ eq₁
          in record { le1 = le1 p₁ ; above = above p₁
                    ; sub = λ i → subst (_≤ play (memOf t₁) h i) (sw (cnt a′ i) (cnt c i) (r i)) (sub p₁ i) })
         (λ i p → ≤-trans (lent i p) (m≤n+m (r i) (cnt a′ i)))
...   | (ok₂ , _) rewrite memOf-++ t₁ t₂ = (OK-++ (memOf t₁) (memOf t₂) h ok₁ ok₂ , tt)
exchangeA (a-case₁ {o = ret w n′} r) pre lent = exchangeA r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchangeA (a-case₁ {o = halted} r) pre lent = exchangeA r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchangeA (a-case₂ {o = ret w n′} r) pre lent = exchangeA r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchangeA (a-case₂ {o = halted} r) pre lent = exchangeA r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchangeA a-op pre lent = (tt , λ i → refl)
exchangeA a-halt pre lent = (tt , tt)

------------------------------------------------------------------------
-- 3. ★ THE LOOP (D317: a server is `iter round seed`).
--
-- `Loop round e s n k s′ n′ t`: `k` rounds from the state `s`, each returning
-- `inr` of the next state, end at `s′`. A loop that never ends is every `k`.
------------------------------------------------------------------------

data Loop {E A B : LTy} (round : ATm E A (B ⊕t A)) (e : MV E)
  : MV A → ℕ → ℕ → MV A → ℕ → List AEv → Set where
  l-zero : ∀ {s n} → Loop round e s n zero s n []
  l-suc  : ∀ {s s′ s″ n n₁ n₂ k t₁ t₂}
         → RunA round e s n (ret (minr s′) n₁) t₁ → Loop round e s′ n₁ k s″ n₂ t₂
         → Loop round e s n (suc k) s″ n₂ (t₁ ++ t₂)

loop-mono : ∀ {E A B} {round : ATm E A (B ⊕t A)} {e s n k s′ n′ t} → Loop round e s n k s′ n′ t → n ≤ n′
loop-mono l-zero        = ≤-refl
loop-mono (l-suc r rs)  = ≤-trans (monoA r) (loop-mono rs)

loop-below : ∀ {E A B} {round : ATm E A (B ⊕t A)} {e s n k s′ n′ t} → Loop round e s n k s′ n′ t
           → Below s n → Below s′ n′
loop-below l-zero       b = b
loop-below (l-suc r rs) b = loop-below rs (belowA r b)

-- ★ after any number of rounds, the heap is the frame plus the current state
loop-exchange : ∀ {E A B} {round : ATm E A (B ⊕t A)} {e s n k s′ n′ t} → Loop round e s n k s′ n′ t
              → ∀ {h r} → Pre h n s r → Lent e r
              → OK (memOf t) h × (∀ i → play (memOf t) h i + cnt s i ≡ h i + cnt s′ i)
loop-exchange l-zero pre lent = (tt , λ i → refl)
loop-exchange (l-suc {s = s} {s′} {s″} {t₁ = t₁} {t₂} r rs) {h} pre lent with exchangeA r pre lent
... | (ok₁ , eq₁) with loop-exchange rs (post-gen (monoA r) (belowA r) pre ok₁ eq₁) lent
...   | (ok₂ , eq₂) rewrite memOf-++ t₁ t₂ =
  ( OK-++ (memOf t₁) (memOf t₂) h ok₁ ok₂
  , λ i → trans (cong (λ z → z i + cnt s i) (play-++ (memOf t₁) (memOf t₂) h))
            (chain (play (memOf t₂) (play (memOf t₁) h) i) (cnt s′ i) (play (memOf t₁) h i) (cnt s″ i) (cnt s i) (h i) (eq₂ i) (eq₁ i)) )

-- ★ The gate's server (`loop-forever-emit`: its state is an `Int`, a word):
-- after every round the heap is exactly what it was. Nothing accumulates, so
-- such a server never runs out; frames alone would already give this, which
-- is why the gate needs a server with a heap-shaped state too (plan 0.146 §4).
word-server : ∀ {E B b} {round : ATm E (Bt b) (B ⊕t Bt b)} {e : MV E} {x y : ⟦ b ⟧b} {n k n′ t}
            → Loop round e (mbase x) n k (mbase y) n′ t → ∀ {h r} → Pre h n (mbase x) r → Lent e r
            → OK (memOf t) h × (∀ i → play (memOf t) h i ≡ h i)
word-server rs pre lent with loop-exchange rs pre lent
... | (ok , eq) = (ok , λ i → trans (sym (+0 _)) (trans (eq i) (+0 _)))
  where +0 : ∀ x → x + 0 ≡ x
        +0 = solve-∀

------------------------------------------------------------------------
-- ★ LIFETIMES, with the exit exception (the user's invariant, 2026-11-08).
--
-- A whole program here is a round from the empty heap. If it returns, every
-- block it allocates is freed exactly once, read only in between. If it HALTS,
-- every block's events are still lifetimes — none freed twice, none read dead —
-- but the last lifetime of a block may be open: the block is live at the exit.
------------------------------------------------------------------------

private
  empty₀ : Pre (λ _ → 0) 0 mone (λ _ → 0)
  empty₀ = record { le1 = λ _ → z≤n ; above = λ _ _ → refl ; sub = λ _ → z≤n }

lifetimesA : ∀ {f : ATm One One One} {n′ t} → RunA f mone mone 0 (ret mone n′) t
           → ∀ i → Life dead (on i (memOf t)) dead
lifetimesA {t = t} r i with exchangeA r empty₀ (λ i ())
... | (ok , eq) = subst (λ x → Life dead (on i (memOf t)) (st x)) (trans (sym (+0 _)) (eq i))
                        (life (memOf t) (λ _ → 0) i ok z≤n)
  where +0 : ∀ x → x + 0 ≡ x
        +0 = solve-∀

lifetimes-exit : ∀ {B} {f : ATm One One B} {t} → RunA f mone mone 0 halted t
               → ∀ i → Σ St (λ s → Life dead (on i (memOf t)) s)
lifetimes-exit {t = t} r i = (_ , life (memOf t) (λ _ → 0) i (fst (exchangeA r empty₀ (λ i ()))) z≤n)
