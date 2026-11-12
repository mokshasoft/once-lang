-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Moves — plan 0.146 B1.4b, `LowerSim` layer (1): what the
-- lowering's word moves do on the flat machine.
--
-- `Seg prog pc tr`: the trace `tr` sits in `prog` at `pc`. A move of `n`
-- words is `2n` steps, each a `flat-step-straight` (the program is not
-- consulted): a load into `Output`, a store from it. Its end state has the
-- words moved and every other slot, every other frame, the heap, `Input1`
-- and the control state as before.
--
-- Here: one load and one store of the current frame, by computation, and
-- what a store leaves in each slot.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (false)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.Memory.HeapAddress using (heap-loc)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Once.LinCore.Moves {FS : FrameSemantics} where

open FlatMachine {FS}
open FrameSemantics FS using (Frame; _≟F_)
open MemOps {FS}
open LocState
open AllocState using (current-frame)

------------------------------------------------------------------------
-- 1. A TRACE AT A PC.
------------------------------------------------------------------------

Seg : AbstractTrace → ℕ → AbstractTrace → Set
Seg prog pc []       = ⊤
Seg prog pc (i ∷ is) = fetch prog pc ≡ just i × Seg prog (suc pc) is

Seg-++ˡ : ∀ prog pc xs ys → Seg prog pc (xs ++ ys) → Seg prog pc xs
Seg-++ˡ prog pc []       ys s       = tt
Seg-++ˡ prog pc (x ∷ xs) ys (f , s) = f , Seg-++ˡ prog (suc pc) xs ys s

Seg-++ʳ : ∀ prog pc xs ys → Seg prog pc (xs ++ ys) → Seg prog (pc + length xs) ys
Seg-++ʳ prog pc []       ys s       rewrite +-identityʳ pc = s
Seg-++ʳ prog pc (x ∷ xs) ys (f , s) rewrite +-suc pc (length xs) = Seg-++ʳ prog (suc pc) xs ys s

------------------------------------------------------------------------
-- 2. ONE LOAD, ONE STORE of the current frame.
------------------------------------------------------------------------

-- the current frame's slot
slot : FlatState → ℕ → Maybe (StoredValue FS)
slot fs k = stackMem (floc fs) (current-frame (falloc fs)) k

-- a load of a defined slot: `Output` holds its word
load-step : ∀ (fs : FlatState) a {v} → slot fs a ≡ just v
          → flat-step-straight (load-from-slot a) fs
            ≡ record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
load-step fs a e =
  cong (λ m → record fs { floc   = Data.Product.proj₁ (exec-load-from-slot-with-value m (floc fs) (falloc fs))
                        ; falloc = Data.Product.proj₂ (exec-load-from-slot-with-value m (floc fs) (falloc fs))
                        ; fpc    = suc (fpc fs) }) e
  where import Data.Product
        open AbstractExec {FS} using (exec-load-from-slot-with-value)

-- a store: the slot holds `Output`'s word
store-step : ∀ (fs : FlatState) b
           → flat-step-straight (store-at-slot b) fs
             ≡ record fs { floc = writeLoc (floc fs) (AtStack (current-frame (falloc fs)) b) (readReg (regs (floc fs)) Output)
                         ; fpc = suc (fpc fs) }
store-step fs b = refl

-- what a store to the current frame leaves: the slot written, the rest as before
private
  ws-same : ∀ (mem : StackMem FS) f k v → writeStackMem mem f k v f k ≡ just v
  ws-same mem f k v with f ≟F f | k ≟ k
  ... | yes _ | yes _ = refl
  ... | yes _ | no ne = ⊥-elim (ne refl)
  ... | no ne | _     = ⊥-elim (ne refl)

  ws-other : ∀ (mem : StackMem FS) f k v k′ → ¬ k ≡ k′ → writeStackMem mem f k v f k′ ≡ mem f k′
  ws-other mem f k v k′ ne with f ≟F f | k ≟ k′
  ... | yes _ | yes e = ⊥-elim (ne e)
  ... | yes _ | no _  = refl
  ... | no _  | _     = refl

  ws-frame : ∀ (mem : StackMem FS) f k v f′ k′ → ¬ f ≡ f′ → writeStackMem mem f k v f′ k′ ≡ mem f′ k′
  ws-frame mem f k v f′ k′ ne with f ≟F f′
  ... | yes e = ⊥-elim (ne e)
  ... | no _  = refl

store-same : ∀ (s : LocState FS) f k v → stackMem (writeLoc s (AtStack f k) v) f k ≡ just v
store-same s f k v = ws-same (stackMem s) f k v

store-other : ∀ (s : LocState FS) f k v k′ → ¬ k ≡ k′ → stackMem (writeLoc s (AtStack f k) v) f k′ ≡ stackMem s f k′
store-other s f k v k′ ne = ws-other (stackMem s) f k v k′ ne

store-frame : ∀ (s : LocState FS) f k v f′ k′ → ¬ f ≡ f′ → stackMem (writeLoc s (AtStack f k) v) f′ k′ ≡ stackMem s f′ k′
store-frame s f k v f′ k′ ne = ws-frame (stackMem s) f k v f′ k′ ne

------------------------------------------------------------------------
-- 3. ★ A MOVE BETWEEN SLOTS (`Lower.mvSS`): `n` loads and stores.
------------------------------------------------------------------------

open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps; []; _∷_; step-at)
open import Data.Nat using (_<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-comm)

open import Once.LinCore.MoveCode using (mvSS)

-- its steps
ln : ℕ → ℕ
ln zero    = 0
ln (suc n) = suc (suc (ln n))

-- what a move leaves: the words moved; every other slot, frame, the heap,
-- `Input1` and the control state as before
record MovedS (fs fs′ : FlatState) (a b n : ℕ) : Set where
  field
    m-pc    : fpc fs′ ≡ ln n + fpc fs
    m-alloc : falloc fs′ ≡ falloc fs
    m-ret   : fret fs′ ≡ fret fs
    m-clo   : fclosure fs′ ≡ fclosure fs
    m-link  : flink fs′ ≡ flink fs
    m-heap  : heapMem (floc fs′) ≡ heapMem (floc fs)
    m-halt  : halted (floc fs′) ≡ halted (floc fs)
    m-in    : readReg (regs (floc fs′)) Input1 ≡ readReg (regs (floc fs)) Input1
    m-moved : ∀ k → k < n → slot fs′ (k + b) ≡ slot fs (k + a)
    m-rest  : ∀ x → (∀ k → k < n → ¬ x ≡ k + b) → slot fs′ x ≡ slot fs x
    m-frame : ∀ f x → ¬ f ≡ current-frame (falloc fs) → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x
open MovedS public

private
  ln-pc : ∀ n p → ln n + suc (suc p) ≡ ln (suc n) + p
  ln-pc n p = trans (+-suc (ln n) (suc p)) (cong suc (+-suc (ln n) p))

-- ★ a move whose stores never clobber a word still to be read
mvSS-run : ∀ prog (fs : FlatState) a b n → Seg prog (fpc fs) (mvSS a b n) → halted (floc fs) ≡ false
         → (∀ k → k < n → Σ (StoredValue FS) λ v → slot fs (k + a) ≡ just v)
         → (∀ k k′ → k < k′ → k′ < n → ¬ k + b ≡ k′ + a)
         → Σ FlatState λ fs′ → FlatSteps prog (ln n) fs fs′ × MovedS fs fs′ a b n
mvSS-run prog fs a b zero s h d nc =
  fs , [] , record { m-pc = refl ; m-alloc = refl ; m-ret = refl ; m-clo = refl ; m-link = refl ; m-heap = refl
                   ; m-halt = refl ; m-in = refl ; m-moved = λ k () ; m-rest = λ x _ → refl ; m-frame = λ _ _ _ → refl }
mvSS-run prog fs a b (suc n) (f₁ , f₂ , s) h d nc with d 0 (s≤s z≤n)
... | (v , e) with mvSS-run prog fs₂ (suc a) (suc b) n s h d₂ nc₂
  where
    cf = current-frame (falloc fs)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = writeLoc (floc fs₁) (AtStack cf b) v ; fpc = suc (fpc fs₁) }
    d₂ : ∀ k → k < n → Σ (StoredValue FS) λ w → slot fs₂ (k + suc a) ≡ just w
    d₂ k k<n with d (suc k) (s≤s k<n)
    ... | (w , ew) = w , trans (cong (slot fs₂) (+-suc k a))
                         (trans (store-other (floc fs₁) cf b v (suc k + a) (nc 0 (suc k) (s≤s z≤n) (s≤s k<n))) ew)
    nc₂ : ∀ k k′ → k < k′ → k′ < n → ¬ k + suc b ≡ k′ + suc a
    nc₂ k k′ lt lt′ eq = nc (suc k) (suc k′) (s≤s lt) (s≤s lt′) (trans (sym (+-suc k b)) (trans eq (+-suc k′ a)))
... | (fs′ , st , M) =
  fs′ , step-at _ (h , f₁) (load-step fs a e) (step-at _ (h , f₂) (store-step _ b) st)
  , record { m-pc = trans (m-pc M) (ln-pc n (fpc fs))
           ; m-alloc = m-alloc M ; m-ret = m-ret M ; m-clo = m-clo M ; m-link = m-link M
           ; m-heap = m-heap M ; m-halt = m-halt M ; m-in = m-in M
           ; m-moved = moved ; m-rest = rest ; m-frame = frm }
  where
    cf = current-frame (falloc fs)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = writeLoc (floc fs₁) (AtStack cf b) v ; fpc = suc (fpc fs₁) }
    -- the first word: written, and no later store touches it
    moved : ∀ k → k < suc n → slot fs′ (k + b) ≡ slot fs (k + a)
    moved zero _ =
      trans (m-rest M b (λ k _ eq → nb k (trans eq (+-suc k b))))
            (trans (store-same (floc fs₁) cf b v) (sym e))
      where
        nb : ∀ k → ¬ b ≡ suc (k + b)
        nb k eq = Data.Nat.Properties.m≢1+n+m b eq
          where import Data.Nat.Properties
    moved (suc k) (s≤s k<n) =
      trans (cong (slot fs′) (sym (+-suc k b)))
        (trans (m-moved M k k<n)
          (trans (cong (slot fs₂) (+-suc k a))
            (store-other (floc fs₁) cf b v (suc k + a) (nc 0 (suc k) (s≤s z≤n) (s≤s k<n)))))
    rest : ∀ x → (∀ k → k < suc n → ¬ x ≡ k + b) → slot fs′ x ≡ slot fs x
    rest x nx =
      trans (m-rest M x (λ k k<n eq → nx (suc k) (s≤s k<n) (trans eq (+-suc k b))))
            (store-other (floc fs₁) cf b v x (λ eq → nx 0 (s≤s z≤n) (sym eq)))
    frm : ∀ f x → ¬ f ≡ cf → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x
    frm f x ne = trans (m-frame M f x ne) (store-frame (floc fs₁) cf b v f x (λ eq → ne (sym eq)))

------------------------------------------------------------------------
-- 4. ★ A MOVE FROM A POINTER'S WORDS TO SLOTS (`Lower.mvPS`): `Input1`
-- holds the pointer and keeps it.
------------------------------------------------------------------------

open ExecFinal {FS} using (exec-load-at-resolved; exec-load-with-value)
open import Once.LinCore.MoveCode using (mvPS)

-- a load at an offset from `Input1`'s pointer
loadat-step : ∀ (fs : FlatState) o {loc v} → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
            → readLoc (floc fs) (offsetLoc loc o) ≡ just v
            → flat-step-straight (load-at o) fs
              ≡ record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
loadat-step fs o {loc} e₁ e₂ =
  trans (cong (λ r → record fs { floc = exec-load-at-resolved o Output (sv-as-loc r) (floc fs) ; fpc = suc (fpc fs) }) e₁)
        (cong (λ m → record fs { floc = exec-load-with-value Output m (floc fs) ; fpc = suc (fpc fs) }) e₂)

-- what a move from a pointer leaves
record MovedP (fs fs′ : FlatState) (loc : ValueLocation FS) (o b n : ℕ) : Set where
  field
    p-pc    : fpc fs′ ≡ ln n + fpc fs
    p-alloc : falloc fs′ ≡ falloc fs
    p-ret   : fret fs′ ≡ fret fs
    p-clo   : fclosure fs′ ≡ fclosure fs
    p-link  : flink fs′ ≡ flink fs
    p-heap  : heapMem (floc fs′) ≡ heapMem (floc fs)
    p-halt  : halted (floc fs′) ≡ halted (floc fs)
    p-in    : readReg (regs (floc fs′)) Input1 ≡ readReg (regs (floc fs)) Input1
    p-moved : ∀ k → k < n → slot fs′ (k + b) ≡ readLoc (floc fs) (offsetLoc loc (k + o))
    p-rest  : ∀ x → (∀ k → k < n → ¬ x ≡ k + b) → slot fs′ x ≡ slot fs x
    p-frame : ∀ f x → ¬ f ≡ current-frame (falloc fs) → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x
open MovedP public

private
  off-suc : ∀ (loc : ValueLocation FS) k o → offsetLoc loc (k + suc o) ≡ offsetLoc loc (suc k + o)
  off-suc loc k o = cong (offsetLoc loc) (+-suc k o)

-- a register's update leaves memory as it was
readLoc-regs : ∀ (s : LocState FS) r (l : ValueLocation FS) → readLoc (record s { regs = r }) l ≡ readLoc s l
readLoc-regs s r (AtStack f k)  = refl
readLoc-regs s r (AtDynamic hl) = refl

-- ★ a move from a pointer whose stores never clobber a word still to be read
mvPS-run : ∀ prog (fs : FlatState) (loc : ValueLocation FS) o b n → Seg prog (fpc fs) (mvPS o b n)
         → halted (floc fs) ≡ false → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
         → (∀ k → k < n → Σ (StoredValue FS) λ v → readLoc (floc fs) (offsetLoc loc (k + o)) ≡ just v)
         → (∀ k k′ → k < k′ → k′ < n → ¬ AtStack (current-frame (falloc fs)) (k + b) ≡ offsetLoc loc (k′ + o))
         → Σ FlatState λ fs′ → FlatSteps prog (ln n) fs fs′ × MovedP fs fs′ loc o b n
mvPS-run prog fs loc o b zero s h i d nc =
  fs , [] , record { p-pc = refl ; p-alloc = refl ; p-ret = refl ; p-clo = refl ; p-link = refl ; p-heap = refl
                   ; p-halt = refl ; p-in = refl ; p-moved = λ k () ; p-rest = λ x _ → refl ; p-frame = λ _ _ _ → refl }
mvPS-run prog fs loc o b (suc n) (f₁ , f₂ , s) h i d nc with d 0 (s≤s z≤n)
... | (v , e) with mvPS-run prog fs₂ loc (suc o) (suc b) n s h i d₂ nc₂
  where
    cf = current-frame (falloc fs)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = writeLoc (floc fs₁) (AtStack cf b) v ; fpc = suc (fpc fs₁) }
    d₂ : ∀ k → k < n → Σ (StoredValue FS) λ w → readLoc (floc fs₂) (offsetLoc loc (k + suc o)) ≡ just w
    d₂ k k<n with d (suc k) (s≤s k<n)
    ... | (w , ew) = w , trans (cong (readLoc (floc fs₂)) (off-suc loc k o))
                         (trans (writeLoc-preserves-other (floc fs₁) (AtStack cf b) (offsetLoc loc (suc k + o)) v
                                   (nc 0 (suc k) (s≤s z≤n) (s≤s k<n)))
                                (trans (readLoc-regs (floc fs) _ (offsetLoc loc (suc k + o))) ew))
    nc₂ : ∀ k k′ → k < k′ → k′ < n → ¬ AtStack cf (k + suc b) ≡ offsetLoc loc (k′ + suc o)
    nc₂ k k′ lt lt′ eq = nc (suc k) (suc k′) (s≤s lt) (s≤s lt′)
                           (trans (cong (AtStack cf) (sym (+-suc k b))) (trans eq (off-suc loc k′ o)))
... | (fs′ , st , M) =
  fs′ , step-at _ (h , f₁) (loadat-step fs o i e) (step-at _ (h , f₂) (store-step _ b) st)
  , record { p-pc = trans (p-pc M) (ln-pc n (fpc fs))
           ; p-alloc = p-alloc M ; p-ret = p-ret M ; p-clo = p-clo M ; p-link = p-link M
           ; p-heap = p-heap M ; p-halt = p-halt M ; p-in = trans (p-in M) i′
           ; p-moved = moved ; p-rest = rest ; p-frame = frm }
  where
    cf = current-frame (falloc fs)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = writeLoc (floc fs₁) (AtStack cf b) v ; fpc = suc (fpc fs₁) }
    i′ : readReg (regs (floc fs₂)) Input1 ≡ readReg (regs (floc fs)) Input1
    i′ = refl
    moved : ∀ k → k < suc n → slot fs′ (k + b) ≡ readLoc (floc fs) (offsetLoc loc (k + o))
    moved zero _ =
      trans (p-rest M b (λ k _ eq → Data.Nat.Properties.m≢1+n+m b (trans eq (+-suc k b))))
            (trans (store-same (floc fs₁) cf b v) (sym e))
      where import Data.Nat.Properties
    moved (suc k) (s≤s k<n) =
      trans (cong (slot fs′) (sym (+-suc k b)))
        (trans (p-moved M k k<n)
          (trans (cong (readLoc (floc fs₂)) (off-suc loc k o))
            (trans (writeLoc-preserves-other (floc fs₁) (AtStack cf b) (offsetLoc loc (suc k + o)) v
                      (nc 0 (suc k) (s≤s z≤n) (s≤s k<n)))
                   (readLoc-regs (floc fs) _ (offsetLoc loc (suc k + o))))))
    rest : ∀ x → (∀ k → k < suc n → ¬ x ≡ k + b) → slot fs′ x ≡ slot fs x
    rest x nx =
      trans (p-rest M x (λ k k<n eq → nx (suc k) (s≤s k<n) (trans eq (+-suc k b))))
            (store-other (floc fs₁) cf b v x (λ eq → nx 0 (s≤s z≤n) (sym eq)))
    frm : ∀ f x → ¬ f ≡ cf → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x
    frm f x ne = trans (p-frame M f x ne) (store-frame (floc fs₁) cf b v f x (λ eq → ne (sym eq)))

------------------------------------------------------------------------
-- 5. ★ A MOVE FROM SLOTS TO A POINTER'S WORDS (`Lower.mvSP`): `Input1`
-- holds the pointer and keeps it; each word stored inside its block.
------------------------------------------------------------------------

open ExecFinal {FS} using (exec-store-at-resolved; exec-store-in-block; in-block?)
open import Once.CCC.Machine.SMPrimitives using (module MemoryOps)
open MemoryOps {FS} using (readLoc-writeLoc-same)
open import Once.LinCore.MoveCode using (mvSP)
open import Data.Bool using (true)
open AllocState using (block-size)

-- a store at an offset from `Input1`'s pointer, inside its block
storeat-step : ∀ (fs : FlatState) o {loc} → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
             → in-block? (block-size (falloc fs)) (offsetLoc loc o) ≡ true
             → flat-step-straight (store-at o) fs
               ≡ record fs { floc = writeLoc (floc fs) (offsetLoc loc o) (readReg (regs (floc fs)) Output) ; fpc = suc (fpc fs) }
storeat-step fs o {loc} e₁ e₂ =
  trans (cong (λ r → record fs { floc = exec-store-at-resolved (block-size (falloc fs)) o (sv-as-loc r)
                                          (readReg (regs (floc fs)) Output) (floc fs) ; fpc = suc (fpc fs) }) e₁)
        (cong (λ q → record fs { floc = exec-store-in-block q (offsetLoc loc o) (readReg (regs (floc fs)) Output) (floc fs)
                               ; fpc = suc (fpc fs) }) e₂)

-- distinct offsets are distinct words
offset-inj : ∀ (loc : ValueLocation FS) {m n} → offsetLoc loc m ≡ offsetLoc loc n → m ≡ n
offset-inj (AtStack f k)  e = Data.Nat.Properties.+-cancelʳ-≡ k _ _ (cong at e)
  where import Data.Nat.Properties
        at : ValueLocation FS → ℕ
        at (AtStack _ s)  = s
        at (AtDynamic _)  = 0
offset-inj (AtDynamic (heap-loc r o)) e = Data.Nat.Properties.+-cancelʳ-≡ o _ _ (cong at e)
  where import Data.Nat.Properties
        at : ValueLocation FS → ℕ
        at (AtStack _ _)  = 0
        at (AtDynamic (heap-loc _ off)) = off

-- what a move to a pointer leaves
record MovedW (fs fs′ : FlatState) (loc : ValueLocation FS) (a o n : ℕ) : Set where
  field
    w-pc    : fpc fs′ ≡ ln n + fpc fs
    w-alloc : falloc fs′ ≡ falloc fs
    w-ret   : fret fs′ ≡ fret fs
    w-clo   : fclosure fs′ ≡ fclosure fs
    w-link  : flink fs′ ≡ flink fs
    w-halt  : halted (floc fs′) ≡ halted (floc fs)
    w-in    : readReg (regs (floc fs′)) Input1 ≡ readReg (regs (floc fs)) Input1
    w-moved : ∀ k → k < n → readLoc (floc fs′) (offsetLoc loc (k + o)) ≡ slot fs (k + a)
    w-rest  : ∀ l → (∀ k → k < n → ¬ l ≡ offsetLoc loc (k + o)) → readLoc (floc fs′) l ≡ readLoc (floc fs) l
open MovedW public

-- ★ a move to a pointer whose stores never clobber a slot still to be read
mvSP-run : ∀ prog (fs : FlatState) (loc : ValueLocation FS) a o n → Seg prog (fpc fs) (mvSP a o n)
         → halted (floc fs) ≡ false → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
         → (∀ k → k < n → Σ (StoredValue FS) λ v → slot fs (k + a) ≡ just v)
         → (∀ k → k < n → in-block? (block-size (falloc fs)) (offsetLoc loc (k + o)) ≡ true)
         → (∀ k k′ → k < k′ → k′ < n → ¬ offsetLoc loc (k + o) ≡ AtStack (current-frame (falloc fs)) (k′ + a))
         → Σ FlatState λ fs′ → FlatSteps prog (ln n) fs fs′ × MovedW fs fs′ loc a o n
mvSP-run prog fs loc a o zero s h i d ib nc =
  fs , [] , record { w-pc = refl ; w-alloc = refl ; w-ret = refl ; w-clo = refl ; w-link = refl
                   ; w-halt = refl ; w-in = refl ; w-moved = λ k () ; w-rest = λ l _ → refl }
mvSP-run prog fs loc a o (suc n) (f₁ , f₂ , s) h i d ib nc with d 0 (s≤s z≤n)
... | (v , e) with mvSP-run prog fs₂ loc (suc a) (suc o) n s h₂ i₂ d₂ ib₂ nc₂
  where
    cf = current-frame (falloc fs)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = writeLoc (floc fs₁) (offsetLoc loc o) v ; fpc = suc (fpc fs₁) }
    h₂ : halted (floc fs₂) ≡ false
    h₂ = trans (writeLoc-halted (floc fs₁) (offsetLoc loc o) v) h
    i₂ : readReg (regs (floc fs₂)) Input1 ≡ SV-Ptr loc
    i₂ = trans (cong (λ r → readReg r Input1) (writeLoc-regs (floc fs₁) (offsetLoc loc o) v)) i
    d₂ : ∀ k → k < n → Σ (StoredValue FS) λ w → slot fs₂ (k + suc a) ≡ just w
    d₂ k k<n with d (suc k) (s≤s k<n)
    ... | (w , ew) = w , trans (cong (slot fs₂) (+-suc k a))
                         (trans (writeLoc-preserves-other (floc fs₁) (offsetLoc loc o) (AtStack cf (suc k + a)) v
                                   (nc 0 (suc k) (s≤s z≤n) (s≤s k<n))) ew)
    ib₂ : ∀ k → k < n → in-block? (block-size (falloc fs₂)) (offsetLoc loc (k + suc o)) ≡ true
    ib₂ k k<n = trans (cong (λ z → in-block? (block-size (falloc fs)) (offsetLoc loc z)) (+-suc k o)) (ib (suc k) (s≤s k<n))
    nc₂ : ∀ k k′ → k < k′ → k′ < n → ¬ offsetLoc loc (k + suc o) ≡ AtStack cf (k′ + suc a)
    nc₂ k k′ lt lt′ eq = nc (suc k) (suc k′) (s≤s lt) (s≤s lt′)
                           (trans (cong (offsetLoc loc) (sym (+-suc k o))) (trans eq (cong (AtStack cf) (+-suc k′ a))))
... | (fs′ , st , M) =
  fs′ , step-at _ (h , f₁) (load-step fs a e) (step-at _ (wh , f₂) (storeat-step fs₁ o i (ib 0 (s≤s z≤n))) st)
  , record { w-pc = trans (w-pc M) (ln-pc n (fpc fs))
           ; w-alloc = w-alloc M ; w-ret = w-ret M ; w-clo = w-clo M ; w-link = w-link M
           ; w-halt = trans (w-halt M) (wl-halt (floc fs₁) (offsetLoc loc o) v) ; w-in = trans (w-in M) (wl-in (floc fs₁) (offsetLoc loc o) v)
           ; w-moved = moved ; w-rest = rest }
  where
    cf = current-frame (falloc fs)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = writeLoc (floc fs₁) (offsetLoc loc o) v ; fpc = suc (fpc fs₁) }
    wh : halted (floc fs₁) ≡ false
    wh = h
    wl-halt : ∀ (s : LocState FS) l w → halted (writeLoc s l w) ≡ halted s
    wl-halt s l w = writeLoc-halted s l w
    wl-in : ∀ (s : LocState FS) l w → readReg (regs (writeLoc s l w)) Input1 ≡ readReg (regs s) Input1
    wl-in s l w = cong (λ r → readReg r Input1) (writeLoc-regs s l w)
    ne-off : ∀ k → ¬ offsetLoc loc o ≡ offsetLoc loc (suc k + o)
    ne-off k eq = Data.Nat.Properties.m≢1+n+m o (offset-inj loc eq)
      where import Data.Nat.Properties
    moved : ∀ k → k < suc n → readLoc (floc fs′) (offsetLoc loc (k + o)) ≡ slot fs (k + a)
    moved zero _ =
      trans (w-rest M (offsetLoc loc o) (λ k _ eq → ne-off k (trans eq (cong (offsetLoc loc) (+-suc k o)))))
            (trans (readLoc-writeLoc-same (floc fs₁) (offsetLoc loc o) v) (sym e))
    moved (suc k) (s≤s k<n) =
      trans (cong (λ z → readLoc (floc fs′) (offsetLoc loc z)) (sym (+-suc k o)))
        (trans (w-moved M k k<n)
          (trans (cong (slot fs₂) (+-suc k a))
            (writeLoc-preserves-other (floc fs₁) (offsetLoc loc o) (AtStack cf (suc k + a)) v
               (nc 0 (suc k) (s≤s z≤n) (s≤s k<n)))))
    rest : ∀ l → (∀ k → k < suc n → ¬ l ≡ offsetLoc loc (k + o)) → readLoc (floc fs′) l ≡ readLoc (floc fs) l
    rest l nl =
      trans (w-rest M l (λ k k<n eq → nl (suc k) (s≤s k<n) (trans eq (cong (offsetLoc loc) (+-suc k o)))))
        (trans (writeLoc-preserves-other (floc fs₁) (offsetLoc loc o) l v (λ eq → nl 0 (s≤s z≤n) (sym eq)))
               (readLoc-regs (floc fs) _ l))
