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

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≟_; _<ᵇ_; _≤?_; _<?_; _<_; _≤_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-comm; <-≤-trans; ≤-trans; ≤-reflexive; +-monoˡ-<; +-monoʳ-<; +-monoʳ-≤; ∸-+-assoc; m≤n+m; m≤m+n; m∸n+n≡m)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (false; true; T; _∨_)
open import Data.Nat using (_≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no; ¬_; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.Memory.HeapAddress using (heap-loc; mkHeapRef; HeapLocation; HeapRef)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Machine.InstrSlot using (slot-of)
open import Once.CCC.Machine.FlatLog using (module LogPres)

module Once.LinCore.Moves {FS : FrameSemantics} where

open FlatMachine {FS}
open FlatState
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
Seg-++ʳ prog pc []       ys s       = subst (λ z → Seg prog z ys) (sym (+-identityʳ pc)) s
Seg-++ʳ prog pc (x ∷ xs) ys (f , s) = subst (λ z → Seg prog z ys) (sym (+-suc pc (length xs))) (Seg-++ʳ prog (suc pc) xs ys s)

------------------------------------------------------------------------
-- 2. ONE LOAD, ONE STORE of the current frame.
------------------------------------------------------------------------

-- the current frame's slot
slot : FlatState → ℕ → Maybe (StoredValue FS)
slot fs k = stackMem (floc fs) (current-frame (falloc fs)) k

-- B1.7b (D456): each slot step proves the machine's slot gate (`Flat.slot-ok-in`):
-- the slot is inside the current frame
private
  gate : ∀ i (fs : FlatState) {k} → slot-of i ≡ just k → k < AllocState.frame-slots (falloc fs)
       → flat-step-straight i fs ≡ straight-go i fs
  gate i fs sk lt = straight-pass i fs (slot-ok-in i (floc fs) (falloc fs) sk lt)

-- a load of a defined slot: `Output` holds its word
load-step : ∀ (fs : FlatState) a {v} → a < AllocState.frame-slots (falloc fs) → slot fs a ≡ just v
          → flat-step-straight (load-from-slot a) fs
            ≡ record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
load-step fs a lt e =
  trans (gate (load-from-slot a) fs refl lt)
    (cong (λ m → record fs { floc   = Data.Product.proj₁ (exec-load-from-slot-with-value m (floc fs) (falloc fs))
                           ; falloc = Data.Product.proj₂ (exec-load-from-slot-with-value m (floc fs) (falloc fs))
                           ; fpc    = suc (fpc fs) }) e)
  where import Data.Product
        open AbstractExec {FS} using (exec-load-from-slot-with-value)

-- a store: the slot holds `Output`'s word
store-step : ∀ (fs : FlatState) b → b < AllocState.frame-slots (falloc fs)
           → flat-step-straight (store-at-slot b) fs
             ≡ record fs { floc = writeLoc (floc fs) (AtStack (current-frame (falloc fs)) b) (readReg (regs (floc fs)) Output)
                         ; fpc = suc (fpc fs) }
store-step fs b lt = gate (store-at-slot b) fs refl lt

-- what a store to the current frame leaves: the slot written, the rest as before
private
  ws-same : ∀ (mem : StackMem FS) f k v → writeStackMem mem f k v f k ≡ just v
  ws-same mem f k v = go (f ≟F f) (k ≟ k)
    where
      go : (d₁ : Dec (f ≡ f)) (d₂ : Dec (k ≡ k)) → writeStackMem-aux d₁ d₂ (mem f k) v ≡ just v
      go (yes _) (yes _) = refl
      go (yes _) (no ne) = ⊥-elim (ne refl)
      go (no ne) _       = ⊥-elim (ne refl)

  ws-other : ∀ (mem : StackMem FS) f k v k′ → ¬ k ≡ k′ → writeStackMem mem f k v f k′ ≡ mem f k′
  ws-other mem f k v k′ ne = go (f ≟F f) (k ≟ k′)
    where
      go : (d₁ : Dec (f ≡ f)) (d₂ : Dec (k ≡ k′)) → writeStackMem-aux d₁ d₂ (mem f k′) v ≡ mem f k′
      go (yes _) (yes e) = ⊥-elim (ne e)
      go (yes _) (no _)  = refl
      go (no _)  _       = refl

  ws-frame : ∀ (mem : StackMem FS) f k v f′ k′ → ¬ f ≡ f′ → writeStackMem mem f k v f′ k′ ≡ mem f′ k′
  ws-frame mem f k v f′ k′ ne = go (f ≟F f′)
    where
      go : (d₁ : Dec (f ≡ f′)) → writeStackMem-aux d₁ (k ≟ k′) (mem f′ k′) v ≡ mem f′ k′
      go (yes e) = ⊥-elim (ne e)
      go (no _)  = refl

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
    m-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)
    m-in    : readReg (regs (floc fs′)) Input1 ≡ readReg (regs (floc fs)) Input1
    m-moved : ∀ k → k < n → slot fs′ (k + b) ≡ slot fs (k + a)
    m-rest  : ∀ x → (∀ k → k < n → ¬ x ≡ k + b) → slot fs′ x ≡ slot fs x
    m-frame : ∀ f x → ¬ f ≡ current-frame (falloc fs) → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x
open MovedS

private
  ln-pc : ∀ n p → ln n + suc (suc p) ≡ ln (suc n) + p
  ln-pc n p = trans (+-suc (ln n) (suc p)) (cong suc (+-suc (ln n) p))

-- B1.7b (D456): the slots a move addresses are inside the current frame
-- (`Fr fs`, the frame's reservation): the machine's slot gate at each access
Fr : FlatState → ℕ
Fr fs = AllocState.frame-slots (falloc fs)

-- (a record: its state index is injective, so a use infers it)
record InFr (fs : FlatState) (a n : ℕ) : Set where
  constructor mkInFr
  field in-fr : ∀ k → k < n → k + a < Fr fs
open InFr

private
  infr-hd : ∀ {fs a n} → InFr fs a (suc n) → a < Fr fs
  infr-hd r = in-fr r 0 (s≤s z≤n)

  infr-tl : ∀ {fs fs′ a n} → Fr fs′ ≡ Fr fs → InFr fs a (suc n) → InFr fs′ (suc a) n
  infr-tl {fs} {fs′} {a} e r =
    mkInFr (λ k lt → subst (λ z → z < Fr fs′) (sym (+-suc k a)) (subst (λ F → suc k + a < F) (sym e) (in-fr r (suc k) (s≤s lt))))

-- the descending form: `a + k` for `k < n`
record InFrD (fs : FlatState) (a n : ℕ) : Set where
  constructor mkInFrD
  field in-frD : ∀ k → k < n → a + k < Fr fs
open InFrD

-- …a range ending by a bound inside the frame is in it
infr : ∀ {fs hi a n} → hi ≤ Fr fs → a + n ≤ hi → InFr fs a n
infr {a = a} {n} B le = mkInFr (λ k lt →
  <-≤-trans (+-monoˡ-< a lt) (≤-trans (≤-reflexive (+-comm n a)) (≤-trans le B)))

infrD : ∀ {fs hi a n} → hi ≤ Fr fs → a + n ≤ hi → InFrD fs a n
infrD {a = a} B le = mkInFrD (λ k lt → <-≤-trans (+-monoʳ-< a lt) (≤-trans le B))

-- the regions' ends: `w` words below `b ∸ s`, `a` words at `b ∸ (a + s)`, `y` at `b ∸ x`
top-in : ∀ b s w → w + s ≤ b → ((b ∸ s) ∸ w) + w ≤ b
top-in b s w le =
  ≤-trans (≤-reflexive (cong (_+ w) (∸-+-assoc b s w)))
    (≤-trans (+-monoʳ-≤ (b ∸ (s + w)) (m≤n+m w s)) (≤-reflexive (m∸n+n≡m (≤-trans (≤-reflexive (+-comm s w)) le))))

sub-le : ∀ b x y → y ≤ x → x ≤ b → (b ∸ x) + y ≤ b
sub-le b x y yx xb = ≤-trans (+-monoʳ-≤ (b ∸ x) yx) (≤-reflexive (m∸n+n≡m xb))

sub-in : ∀ b a s → a + s ≤ b → (b ∸ (a + s)) + a ≤ b
sub-in b a s le = ≤-trans (+-monoʳ-≤ (b ∸ (a + s)) (m≤m+n a s)) (≤-reflexive (m∸n+n≡m le))

-- ★ a move whose stores never clobber a word still to be read
mvSS-run′ : ∀ prog (fs : FlatState) a b n → Seg prog (fpc fs) (mvSS a b n) → halted (floc fs) ≡ false
         → InFr fs a n → InFr fs b n
         → (∀ k → k < n → Σ (StoredValue FS) λ v → slot fs (k + a) ≡ just v)
         → (∀ k k′ → k < k′ → k′ < n → ¬ k + b ≡ k′ + a)
         → Σ FlatState λ fs′ → FlatSteps prog (ln n) fs fs′ × MovedS fs fs′ a b n
mvSS-run′ prog fs a b zero s h ra rb d nc =
  fs , [] , record { m-pc = refl ; m-alloc = refl ; m-ret = refl ; m-clo = refl ; m-link = refl ; m-heap = refl
                   ; m-halt = refl ; m-log = refl ; m-in = refl ; m-moved = λ k () ; m-rest = λ x _ → refl ; m-frame = λ _ _ _ → refl }
mvSS-run′ prog fs a b (suc n) (f₁ , f₂ , s) h ra rb d nc =
  fs′ , step-at _ (h , f₁) (load-step fs a (infr-hd ra) e) (step-at _ (h , f₂) (store-step _ b (infr-hd rb)) st)
  , record { m-pc = trans (m-pc M) (ln-pc n (fpc fs))
           ; m-alloc = m-alloc M ; m-ret = m-ret M ; m-clo = m-clo M ; m-link = m-link M
           ; m-heap = m-heap M ; m-halt = m-halt M ; m-log = m-log M ; m-in = m-in M
           ; m-moved = moved ; m-rest = rest ; m-frame = frm }
  where
    v = proj₁ (d 0 (s≤s z≤n))
    e = proj₂ (d 0 (s≤s z≤n))
    cf = current-frame (falloc fs)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = writeLoc (floc fs₁) (AtStack cf b) v ; fpc = suc (fpc fs₁) }
    d₂ : ∀ k → k < n → Σ (StoredValue FS) λ w → slot fs₂ (k + suc a) ≡ just w
    d₂ k k<n = let (w , ew) = d (suc k) (s≤s k<n) in
      w , trans (cong (slot fs₂) (+-suc k a))
                         (trans (store-other (floc fs₁) cf b v (suc k + a) (nc 0 (suc k) (s≤s z≤n) (s≤s k<n))) ew)
    nc₂ : ∀ k k′ → k < k′ → k′ < n → ¬ k + suc b ≡ k′ + suc a
    nc₂ k k′ lt lt′ eq = nc (suc k) (suc k′) (s≤s lt) (s≤s lt′) (trans (sym (+-suc k b)) (trans eq (+-suc k′ a)))
    nxt = mvSS-run′ prog fs₂ (suc a) (suc b) n s h (infr-tl refl ra) (infr-tl refl rb) d₂ nc₂
    fs′ = proj₁ nxt
    st = proj₁ (proj₂ nxt)
    M = proj₂ (proj₂ nxt)
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

-- sealed: a use sees its facts, never its unfolded end state
opaque
  mvSS-run : ∀ prog (fs : FlatState) a b n → Seg prog (fpc fs) (mvSS a b n) → halted (floc fs) ≡ false
           → InFr fs a n → InFr fs b n
           → (∀ k → k < n → Σ (StoredValue FS) λ v → slot fs (k + a) ≡ just v)
           → (∀ k k′ → k < k′ → k′ < n → ¬ k + b ≡ k′ + a)
           → Σ FlatState λ fs′ → FlatSteps prog (ln n) fs fs′ × MovedS fs fs′ a b n
  mvSS-run = mvSS-run′

------------------------------------------------------------------------
-- 4. ★ A MOVE FROM A POINTER'S WORDS TO SLOTS (`Lower.mvPS`): `Input1`
-- holds the pointer and keeps it.
------------------------------------------------------------------------

open ExecFinal {FS} using (exec-load-at-resolved; exec-load-with-value; frame-gate; heap-gate)
open import Once.LinCore.MoveCode using (mvPS)

-- a load at an offset from `Input1`'s pointer
loadat-step : ∀ (fs : FlatState) o {loc v} → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
            → frame-gate (falloc fs) o (just loc) ≡ just loc
            → readLoc (floc fs) (offsetLoc loc o) ≡ just v
            → flat-step-straight (load-at o) fs
              ≡ record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
loadat-step fs o {loc} e₁ g e₂ =
  trans (cong (λ r → record fs { floc = exec-load-at-resolved o Output (frame-gate (falloc fs) o (sv-as-loc r)) (floc fs) ; fpc = suc (fpc fs) }) e₁)
    (trans (cong (λ m → record fs { floc = exec-load-at-resolved o Output m (floc fs) ; fpc = suc (fpc fs) }) g)
        (cong (λ m → record fs { floc = exec-load-with-value Output m (floc fs) ; fpc = suc (fpc fs) }) e₂))

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
    p-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)
    p-in    : readReg (regs (floc fs′)) Input1 ≡ readReg (regs (floc fs)) Input1
    p-moved : ∀ k → k < n → slot fs′ (k + b) ≡ readLoc (floc fs) (offsetLoc loc (k + o))
    p-rest  : ∀ x → (∀ k → k < n → ¬ x ≡ k + b) → slot fs′ x ≡ slot fs x
    p-frame : ∀ f x → ¬ f ≡ current-frame (falloc fs) → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x
open MovedP

private
  off-suc : ∀ (loc : ValueLocation FS) k o → offsetLoc loc (k + suc o) ≡ offsetLoc loc (suc k + o)
  off-suc loc k o = cong (offsetLoc loc) (+-suc k o)

-- a register's update leaves memory as it was
readLoc-regs : ∀ (s : LocState FS) r (l : ValueLocation FS) → readLoc (record s { regs = r }) l ≡ readLoc s l
readLoc-regs s r (AtStack f k)  = refl
readLoc-regs s r (AtDynamic hl) = refl

-- ★ a move from a pointer whose stores never clobber a word still to be read
mvPS-run′ : ∀ prog (fs : FlatState) (loc : ValueLocation FS) o b n → Seg prog (fpc fs) (mvPS o b n)
         → halted (floc fs) ≡ false → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
         → (∀ k → k < n → Σ (StoredValue FS) λ v → readLoc (floc fs) (offsetLoc loc (k + o)) ≡ just v)
         → (∀ k → k < n → frame-gate (falloc fs) (k + o) (just loc) ≡ just loc)
         → (∀ k k′ → k < k′ → k′ < n → ¬ AtStack (current-frame (falloc fs)) (k + b) ≡ offsetLoc loc (k′ + o))
         → InFr fs b n
         → Σ FlatState λ fs′ → FlatSteps prog (ln n) fs fs′ × MovedP fs fs′ loc o b n
mvPS-run′ prog fs loc o b zero s h i d gt nc rb =
  fs , [] , record { p-pc = refl ; p-alloc = refl ; p-ret = refl ; p-clo = refl ; p-link = refl ; p-heap = refl
                   ; p-halt = refl ; p-log = refl ; p-in = refl ; p-moved = λ k () ; p-rest = λ x _ → refl ; p-frame = λ _ _ _ → refl }
mvPS-run′ prog fs loc o b (suc n) (f₁ , f₂ , s) h i d gt nc rb =
  fs′ , step-at _ (h , f₁) (loadat-step fs o i (gt 0 (s≤s z≤n)) e) (step-at _ (h , f₂) (store-step _ b (infr-hd rb)) st)
  , record { p-pc = trans (p-pc M) (ln-pc n (fpc fs))
           ; p-alloc = p-alloc M ; p-ret = p-ret M ; p-clo = p-clo M ; p-link = p-link M
           ; p-heap = p-heap M ; p-halt = p-halt M ; p-log = p-log M ; p-in = trans (p-in M) i′
           ; p-moved = moved ; p-rest = rest ; p-frame = frm }
  where
    v = proj₁ (d 0 (s≤s z≤n))
    e = proj₂ (d 0 (s≤s z≤n))
    gt₂ : ∀ k → k < n → frame-gate (falloc fs) (k + suc o) (just loc) ≡ just loc
    gt₂ k k<n = trans (cong (λ z → frame-gate (falloc fs) z (just loc)) (+-suc k o)) (gt (suc k) (s≤s k<n))
    cf = current-frame (falloc fs)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = writeLoc (floc fs₁) (AtStack cf b) v ; fpc = suc (fpc fs₁) }
    d₂ : ∀ k → k < n → Σ (StoredValue FS) λ w → readLoc (floc fs₂) (offsetLoc loc (k + suc o)) ≡ just w
    d₂ k k<n = let (w , ew) = d (suc k) (s≤s k<n) in
      w , trans (cong (readLoc (floc fs₂)) (off-suc loc k o))
                         (trans (writeLoc-preserves-other (floc fs₁) (AtStack cf b) (offsetLoc loc (suc k + o)) v
                                   (nc 0 (suc k) (s≤s z≤n) (s≤s k<n)))
                                (trans (readLoc-regs (floc fs) _ (offsetLoc loc (suc k + o))) ew))
    nc₂ : ∀ k k′ → k < k′ → k′ < n → ¬ AtStack cf (k + suc b) ≡ offsetLoc loc (k′ + suc o)
    nc₂ k k′ lt lt′ eq = nc (suc k) (suc k′) (s≤s lt) (s≤s lt′)
                           (trans (cong (AtStack cf) (sym (+-suc k b))) (trans eq (off-suc loc k′ o)))
    nxt = mvPS-run′ prog fs₂ loc (suc o) (suc b) n s h i d₂ gt₂ nc₂ (infr-tl refl rb)
    fs′ = proj₁ nxt
    st = proj₁ (proj₂ nxt)
    M = proj₂ (proj₂ nxt)
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

-- sealed: a use sees its facts, never its unfolded end state
opaque
  mvPS-run : ∀ prog (fs : FlatState) (loc : ValueLocation FS) o b n → Seg prog (fpc fs) (mvPS o b n)
           → halted (floc fs) ≡ false → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
           → (∀ k → k < n → Σ (StoredValue FS) λ v → readLoc (floc fs) (offsetLoc loc (k + o)) ≡ just v)
           → (∀ k → k < n → frame-gate (falloc fs) (k + o) (just loc) ≡ just loc)
           → (∀ k k′ → k < k′ → k′ < n → ¬ AtStack (current-frame (falloc fs)) (k + b) ≡ offsetLoc loc (k′ + o))
           → InFr fs b n
           → Σ FlatState λ fs′ → FlatSteps prog (ln n) fs fs′ × MovedP fs fs′ loc o b n
  mvPS-run = mvPS-run′

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
             → frame-gate (falloc fs) o (just loc) ≡ just loc
             → in-block? (block-size (falloc fs)) (offsetLoc loc o) ≡ true
             → flat-step-straight (store-at o) fs
               ≡ record fs { floc = writeLoc (floc fs) (offsetLoc loc o) (readReg (regs (floc fs)) Output) ; fpc = suc (fpc fs) }
storeat-step fs o {loc} e₁ g e₂ =
  trans (cong (λ r → record fs { floc = exec-store-at-resolved (block-size (falloc fs)) o (frame-gate (falloc fs) o (sv-as-loc r))
                                          (readReg (regs (floc fs)) Output) (floc fs) ; fpc = suc (fpc fs) }) e₁)
    (trans (cong (λ m → record fs { floc = exec-store-at-resolved (block-size (falloc fs)) o m
                                          (readReg (regs (floc fs)) Output) (floc fs) ; fpc = suc (fpc fs) }) g)
        (cong (λ q → record fs { floc = exec-store-in-block q (offsetLoc loc o) (readReg (regs (floc fs)) Output) (floc fs)
                               ; fpc = suc (fpc fs) }) e₂))

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

-- D452: a slot inside a live frame's window passes the frame gate
ltᵇ : ∀ {m n} → m < n → (m <ᵇ n) ≡ true
ltᵇ {zero}  {suc n} _        = refl
ltᵇ {suc m} {suc n} (s≤s lt) = ltᵇ lt

win-here-at : ∀ (f : Frame) b fr j → j < b → (d : Dec (f ≡ f)) → win-pick d (j <ᵇ b) (ExecFinal.in-window {FS} fr f j) ≡ true
win-here-at f b fr j lt (yes _) = cong (λ z → z Data.Bool.∨ ExecFinal.in-window {FS} fr f j) (ltᵇ lt)
win-here-at f b fr j lt (no ne) = ⊥-elim (ne refl)

win-here : ∀ (f : Frame) b fr j → j < b → ExecFinal.in-window {FS} ((f , b) ∷ fr) f j ≡ true
win-here f b fr j lt = win-here-at f b fr j lt (f ≟F f)

win-there-at : ∀ (g f : Frame) b fr j → ExecFinal.in-window {FS} fr f j ≡ true → (d : Dec (g ≡ f))
             → win-pick d (j <ᵇ b) (ExecFinal.in-window {FS} fr f j) ≡ true
win-there-at g f b fr j w (yes _) = trans (cong (λ z → (j <ᵇ b) Data.Bool.∨ z) w) (Data.Bool.Properties.∨-zeroʳ (j <ᵇ b))
  where import Data.Bool.Properties
win-there-at g f b fr j w (no _)  = w

win-there : ∀ (g f : Frame) b fr j → ExecFinal.in-window {FS} fr f j ≡ true → ExecFinal.in-window {FS} ((g , b) ∷ fr) f j ≡ true
win-there g f b fr j w = win-there-at g f b fr j w (g ≟F f)

-- …and stays inside one when a call pushes a frame over it
win-push : ∀ (al al′ : AllocState {FS}) (f : Frame) j
         → AllocState.saved-frames al′ ≡ (AllocState.current-frame al , AllocState.frame-slots al) ∷ AllocState.saved-frames al
         → ExecFinal.in-window {FS} (ExecFinal.live-frames {FS} al) f j ≡ true
         → ExecFinal.in-window {FS} (ExecFinal.live-frames {FS} al′) f j ≡ true
win-push al al′ f j sv w =
  win-there (AllocState.current-frame al′) f (AllocState.frame-slots al′) (AllocState.saved-frames al′) j
    (subst (λ L → ExecFinal.in-window {FS} L f j ≡ true) (sym sv) w)

gate-stack : ∀ (al : AllocState {FS}) k (f : Frame) j → ExecFinal.in-window {FS} (ExecFinal.live-frames {FS} al) f (k + j) ≡ true
           → frame-gate al k (just (AtStack f j)) ≡ just (AtStack f j)
gate-stack al k f j w = cong (λ b → ExecFinal.stack-gate {FS} b (AtStack f j)) w

-- what a move to a pointer leaves
record MovedW (fs fs′ : FlatState) (loc : ValueLocation FS) (a o n : ℕ) : Set where
  field
    w-pc    : fpc fs′ ≡ ln n + fpc fs
    w-alloc : falloc fs′ ≡ falloc fs
    w-ret   : fret fs′ ≡ fret fs
    w-clo   : fclosure fs′ ≡ fclosure fs
    w-link  : flink fs′ ≡ flink fs
    w-halt  : halted (floc fs′) ≡ halted (floc fs)
    w-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)
    w-in    : readReg (regs (floc fs′)) Input1 ≡ readReg (regs (floc fs)) Input1
    w-moved : ∀ k → k < n → readLoc (floc fs′) (offsetLoc loc (k + o)) ≡ slot fs (k + a)
    w-rest  : ∀ l → (∀ k → k < n → ¬ l ≡ offsetLoc loc (k + o)) → readLoc (floc fs′) l ≡ readLoc (floc fs) l
open MovedW

-- ★ a move to a pointer whose stores never clobber a slot still to be read
mvSP-run′ : ∀ prog (fs : FlatState) (loc : ValueLocation FS) a o n → Seg prog (fpc fs) (mvSP a o n)
         → halted (floc fs) ≡ false → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
         → (∀ k → k < n → Σ (StoredValue FS) λ v → slot fs (k + a) ≡ just v)
         → (∀ k → k < n → frame-gate (falloc fs) (k + o) (just loc) ≡ just loc)
         → (∀ k → k < n → in-block? (block-size (falloc fs)) (offsetLoc loc (k + o)) ≡ true)
         → (∀ k k′ → k < k′ → k′ < n → ¬ offsetLoc loc (k + o) ≡ AtStack (current-frame (falloc fs)) (k′ + a))
         → InFr fs a n
         → Σ FlatState λ fs′ → FlatSteps prog (ln n) fs fs′ × MovedW fs fs′ loc a o n
mvSP-run′ prog fs loc a o zero s h i d gt ib nc ra =
  fs , [] , record { w-pc = refl ; w-alloc = refl ; w-ret = refl ; w-clo = refl ; w-link = refl
                   ; w-halt = refl ; w-log = refl ; w-in = refl ; w-moved = λ k () ; w-rest = λ l _ → refl }
mvSP-run′ prog fs loc a o (suc n) (f₁ , f₂ , s) h i d gt ib nc ra =
  fs′ , step-at _ (h , f₁) (load-step fs a (infr-hd ra) e) (step-at _ (wh , f₂) (storeat-step fs₁ o i (gt 0 (s≤s z≤n)) (ib 0 (s≤s z≤n))) st)
  , record { w-pc = trans (w-pc M) (ln-pc n (fpc fs))
           ; w-alloc = w-alloc M ; w-ret = w-ret M ; w-clo = w-clo M ; w-link = w-link M
           ; w-halt = trans (w-halt M) (wl-halt (floc fs₁) (offsetLoc loc o) v) ; w-log = trans (w-log M) (LogPres.writeLoc-log {FS} (floc fs₁) (offsetLoc loc o) v) ; w-in = trans (w-in M) (wl-in (floc fs₁) (offsetLoc loc o) v)
           ; w-moved = moved ; w-rest = rest }
  where
    v = proj₁ (d 0 (s≤s z≤n))
    e = proj₂ (d 0 (s≤s z≤n))
    gt₂ : ∀ k → k < n → frame-gate (falloc fs) (k + suc o) (just loc) ≡ just loc
    gt₂ k k<n = trans (cong (λ z → frame-gate (falloc fs) z (just loc)) (+-suc k o)) (gt (suc k) (s≤s k<n))
    cf = current-frame (falloc fs)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = writeLoc (floc fs₁) (offsetLoc loc o) v ; fpc = suc (fpc fs₁) }
    h₂ : halted (floc fs₂) ≡ false
    h₂ = trans (writeLoc-halted (floc fs₁) (offsetLoc loc o) v) h
    i₂ : readReg (regs (floc fs₂)) Input1 ≡ SV-Ptr loc
    i₂ = trans (cong (λ r → readReg r Input1) (writeLoc-regs (floc fs₁) (offsetLoc loc o) v)) i
    d₂ : ∀ k → k < n → Σ (StoredValue FS) λ w → slot fs₂ (k + suc a) ≡ just w
    d₂ k k<n = let (w , ew) = d (suc k) (s≤s k<n) in
      w , trans (cong (slot fs₂) (+-suc k a))
                         (trans (writeLoc-preserves-other (floc fs₁) (offsetLoc loc o) (AtStack cf (suc k + a)) v
                                   (nc 0 (suc k) (s≤s z≤n) (s≤s k<n))) ew)
    ib₂ : ∀ k → k < n → in-block? (block-size (falloc fs₂)) (offsetLoc loc (k + suc o)) ≡ true
    ib₂ k k<n = trans (cong (λ z → in-block? (block-size (falloc fs)) (offsetLoc loc z)) (+-suc k o)) (ib (suc k) (s≤s k<n))
    nc₂ : ∀ k k′ → k < k′ → k′ < n → ¬ offsetLoc loc (k + suc o) ≡ AtStack cf (k′ + suc a)
    nc₂ k k′ lt lt′ eq = nc (suc k) (suc k′) (s≤s lt) (s≤s lt′)
                           (trans (cong (offsetLoc loc) (sym (+-suc k o))) (trans eq (cong (AtStack cf) (+-suc k′ a))))
    nxt = mvSP-run′ prog fs₂ loc (suc a) (suc o) n s h₂ i₂ d₂ gt₂ ib₂ nc₂ (infr-tl refl ra)
    fs′ = proj₁ nxt
    st = proj₁ (proj₂ nxt)
    M = proj₂ (proj₂ nxt)
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

-- sealed: a use sees its facts, never its unfolded end state
opaque
  mvSP-run : ∀ prog (fs : FlatState) (loc : ValueLocation FS) a o n → Seg prog (fpc fs) (mvSP a o n)
           → halted (floc fs) ≡ false → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
           → (∀ k → k < n → Σ (StoredValue FS) λ v → slot fs (k + a) ≡ just v)
           → (∀ k → k < n → frame-gate (falloc fs) (k + o) (just loc) ≡ just loc)
           → (∀ k → k < n → in-block? (block-size (falloc fs)) (offsetLoc loc (k + o)) ≡ true)
           → (∀ k k′ → k < k′ → k′ < n → ¬ offsetLoc loc (k + o) ≡ AtStack (current-frame (falloc fs)) (k′ + a))
           → InFr fs a n
           → Σ FlatState λ fs′ → FlatSteps prog (ln n) fs fs′ × MovedW fs fs′ loc a o n
  mvSP-run = mvSP-run′

------------------------------------------------------------------------
-- 6. ★ A MOVE BETWEEN SLOTS, HIGHEST FIRST (`Lower.mvSSd`): for a shift
-- to higher slots that overlaps.
------------------------------------------------------------------------

open import Once.LinCore.MoveCode using (mvSSd)
open import Data.Nat.Properties using (m<1+n⇒m<n∨m≡n; m<n⇒m<1+n; n<1+n; <⇒≢; +-cancelˡ-≡)
open import Data.Sum using (_⊎_; inj₁; inj₂)

record MovedD (fs fs′ : FlatState) (a b n : ℕ) : Set where
  field
    d-pc    : fpc fs′ ≡ ln n + fpc fs
    d-alloc : falloc fs′ ≡ falloc fs
    d-ret   : fret fs′ ≡ fret fs
    d-clo   : fclosure fs′ ≡ fclosure fs
    d-link  : flink fs′ ≡ flink fs
    d-heap  : heapMem (floc fs′) ≡ heapMem (floc fs)
    d-halt  : halted (floc fs′) ≡ halted (floc fs)
    d-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)
    d-in    : readReg (regs (floc fs′)) Input1 ≡ readReg (regs (floc fs)) Input1
    d-moved : ∀ k → k < n → slot fs′ (b + k) ≡ slot fs (a + k)
    d-rest  : ∀ x → (∀ k → k < n → ¬ x ≡ b + k) → slot fs′ x ≡ slot fs x
    d-frame : ∀ f x → ¬ f ≡ current-frame (falloc fs) → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x
open MovedD

-- ★ highest first, its stores never clobbering a word still to be read
mvSSd-run′ : ∀ prog (fs : FlatState) a b n → Seg prog (fpc fs) (mvSSd a b n) → halted (floc fs) ≡ false
          → InFrD fs a n → InFrD fs b n
          → (∀ k → k < n → Σ (StoredValue FS) λ v → slot fs (a + k) ≡ just v)
          → (∀ k k′ → k′ < k → k < n → ¬ b + k ≡ a + k′)
          → Σ FlatState λ fs′ → FlatSteps prog (ln n) fs fs′ × MovedD fs fs′ a b n
mvSSd-run′ prog fs a b zero s h ra rb d nc =
  fs , [] , record { d-pc = refl ; d-alloc = refl ; d-ret = refl ; d-clo = refl ; d-link = refl ; d-heap = refl
                   ; d-halt = refl ; d-log = refl ; d-in = refl ; d-moved = λ k () ; d-rest = λ x _ → refl ; d-frame = λ _ _ _ → refl }
mvSSd-run′ prog fs a b (suc n) (f₁ , f₂ , s) h ra rb d nc =
  fs′ , step-at _ (h , f₁) (load-step fs (a + n) (in-frD ra n (n<1+n n)) e) (step-at _ (h , f₂) (store-step _ (b + n) (in-frD rb n (n<1+n n))) st)
  , record { d-pc = trans (d-pc M) (ln-pc n (fpc fs))
           ; d-alloc = d-alloc M ; d-ret = d-ret M ; d-clo = d-clo M ; d-link = d-link M
           ; d-heap = d-heap M ; d-halt = d-halt M ; d-log = d-log M ; d-in = d-in M
           ; d-moved = moved ; d-rest = rest ; d-frame = frm }
  where
    v = proj₁ (d n (n<1+n n))
    e = proj₂ (d n (n<1+n n))
    cf = current-frame (falloc fs)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = writeLoc (floc fs₁) (AtStack cf (b + n)) v ; fpc = suc (fpc fs₁) }
    d₂ : ∀ k → k < n → Σ (StoredValue FS) λ w → slot fs₂ (a + k) ≡ just w
    d₂ k k<n = let (w , ew) = d k (m<n⇒m<1+n k<n) in
      w , trans (store-other (floc fs₁) cf (b + n) v (a + k) (nc n k k<n (n<1+n n))) ew
    nc₂ : ∀ k k′ → k′ < k → k < n → ¬ b + k ≡ a + k′
    nc₂ k k′ lt lt′ = nc k k′ lt (m<n⇒m<1+n lt′)
    nxt = mvSSd-run′ prog fs₂ a b n s h (mkInFrD (λ k lt → in-frD ra k (m<n⇒m<1+n lt))) (mkInFrD (λ k lt → in-frD rb k (m<n⇒m<1+n lt))) d₂ nc₂
    fs′ = proj₁ nxt
    st = proj₁ (proj₂ nxt)
    M = proj₂ (proj₂ nxt)
    moved : ∀ k → k < suc n → slot fs′ (b + k) ≡ slot fs (a + k)
    moved k k<sn = mv k (m<1+n⇒m<n∨m≡n k<sn)
      where
        mv : ∀ k → k < n ⊎ k ≡ n → slot fs′ (b + k) ≡ slot fs (a + k)
        mv k (inj₁ k<n) = trans (d-moved M k k<n) (store-other (floc fs₁) cf (b + n) v (a + k) (nc n k k<n (n<1+n n)))
        mv k (inj₂ refl) =
          trans (d-rest M (b + k) (λ k′ k′<n eq → <⇒≢ k′<n (sym (+-cancelˡ-≡ b _ _ eq))))
                (trans (store-same (floc fs₁) cf (b + k) v) (sym e))
    rest : ∀ x → (∀ k → k < suc n → ¬ x ≡ b + k) → slot fs′ x ≡ slot fs x
    rest x nx =
      trans (d-rest M x (λ k k<n → nx k (m<n⇒m<1+n k<n)))
            (store-other (floc fs₁) cf (b + n) v x (λ eq → nx n (n<1+n n) (sym eq)))
    frm : ∀ f x → ¬ f ≡ cf → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x
    frm f x ne = trans (d-frame M f x ne) (store-frame (floc fs₁) cf (b + n) v f x (λ eq → ne (sym eq)))

-- sealed: a use sees its facts, never its unfolded end state
opaque
  mvSSd-run : ∀ prog (fs : FlatState) a b n → Seg prog (fpc fs) (mvSSd a b n) → halted (floc fs) ≡ false
            → InFrD fs a n → InFrD fs b n
            → (∀ k → k < n → Σ (StoredValue FS) λ v → slot fs (a + k) ≡ just v)
            → (∀ k k′ → k′ < k → k < n → ¬ b + k ≡ a + k′)
            → Σ FlatState λ fs′ → FlatSteps prog (ln n) fs fs′ × MovedD fs fs′ a b n
  mvSSd-run = mvSSd-run′

------------------------------------------------------------------------
-- 7. ★ A TAG, AND `Output`'s WORD INTO SLOTS (`MoveCode.stores`).
------------------------------------------------------------------------

open import Once.LinCore.MoveCode using (stores)

-- a tag into `Output`
tag-step : ∀ (fs : FlatState) n
         → flat-step-straight (instr-load-tag-lit n) fs
           ≡ record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output (SV-Tag n) } ; fpc = suc (fpc fs) }
tag-step fs n = refl

-- what `n` stores of `Output`'s word leave
record Filled (fs fs′ : FlatState) (b n : ℕ) : Set where
  field
    f-pc    : fpc fs′ ≡ n + fpc fs
    f-alloc : falloc fs′ ≡ falloc fs
    f-ret   : fret fs′ ≡ fret fs
    f-clo   : fclosure fs′ ≡ fclosure fs
    f-link  : flink fs′ ≡ flink fs
    f-heap  : heapMem (floc fs′) ≡ heapMem (floc fs)
    f-halt  : halted (floc fs′) ≡ halted (floc fs)
    f-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)
    f-regs  : regs (floc fs′) ≡ regs (floc fs)
    f-set   : ∀ k → k < n → slot fs′ (k + b) ≡ just (readReg (regs (floc fs)) Output)
    f-rest  : ∀ x → (∀ k → k < n → ¬ x ≡ k + b) → slot fs′ x ≡ slot fs x
    f-frame : ∀ f x → ¬ f ≡ current-frame (falloc fs) → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x
open Filled

stores-run′ : ∀ prog (fs : FlatState) b n → Seg prog (fpc fs) (stores b n) → halted (floc fs) ≡ false
           → InFr fs b n
           → Σ FlatState λ fs′ → FlatSteps prog n fs fs′ × Filled fs fs′ b n
stores-run′ prog fs b zero s h rb =
  fs , [] , record { f-pc = refl ; f-alloc = refl ; f-ret = refl ; f-clo = refl ; f-link = refl ; f-heap = refl
                   ; f-halt = refl ; f-log = refl ; f-regs = refl ; f-set = λ k () ; f-rest = λ x _ → refl ; f-frame = λ _ _ _ → refl }
stores-run′ prog fs b (suc n) (f₁ , s) h rb =
  fs′ , step-at _ (h , f₁) (store-step fs b (infr-hd rb)) st
  , record { f-pc = trans (f-pc F) (+-suc n (fpc fs))
           ; f-alloc = f-alloc F ; f-ret = f-ret F ; f-clo = f-clo F ; f-link = f-link F
           ; f-heap = f-heap F ; f-halt = f-halt F ; f-log = f-log F ; f-regs = f-regs F
           ; f-set = set ; f-rest = rest ; f-frame = frm }
  where
    cf = current-frame (falloc fs)
    fs₁ = record fs { floc = writeLoc (floc fs) (AtStack cf b) (readReg (regs (floc fs)) Output) ; fpc = suc (fpc fs) }
    nxt = stores-run′ prog fs₁ (suc b) n s h (infr-tl refl rb)
    fs′ = proj₁ nxt
    st = proj₁ (proj₂ nxt)
    F = proj₂ (proj₂ nxt)
    v = readReg (regs (floc fs)) Output
    set : ∀ k → k < suc n → slot fs′ (k + b) ≡ just v
    set zero _ = trans (f-rest F b (λ k _ eq → Data.Nat.Properties.m≢1+n+m b (trans eq (+-suc k b)))) (store-same (floc fs) cf b v)
      where import Data.Nat.Properties
    set (suc k) (s≤s k<n) = trans (cong (slot fs′) (sym (+-suc k b))) (f-set F k k<n)
    rest : ∀ x → (∀ k → k < suc n → ¬ x ≡ k + b) → slot fs′ x ≡ slot fs x
    rest x nx = trans (f-rest F x (λ k k<n eq → nx (suc k) (s≤s k<n) (trans eq (+-suc k b))))
                      (store-other (floc fs) cf b v x (λ eq → nx 0 (s≤s z≤n) (sym eq)))
    frm : ∀ f x → ¬ f ≡ cf → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x
    frm f x ne = trans (f-frame F f x ne) (store-frame (floc fs) cf b v f x (λ eq → ne (sym eq)))

-- sealed: a use sees its facts, never its unfolded end state
opaque
  stores-run : ∀ prog (fs : FlatState) b n → Seg prog (fpc fs) (stores b n) → halted (floc fs) ≡ false
             → InFr fs b n
             → Σ FlatState λ fs′ → FlatSteps prog n fs fs′ × Filled fs fs′ b n
  stores-run = stores-run′

------------------------------------------------------------------------
-- 8. ★ THE OTHER STRAIGHT STEPS the lowering uses, by computation.
------------------------------------------------------------------------

open import Once.Memory.HeapAddress using (mkHeapRef)
open import Once.CCC.Label using (LabelId)

-- `Input1` from a defined slot
restore-step : ∀ (fs : FlatState) a {v} → a < AllocState.frame-slots (falloc fs) → slot fs a ≡ just v
             → flat-step-straight (restore-input a) fs
               ≡ record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Input1 v } ; fpc = suc (fpc fs) }
restore-step fs a lt e =
  trans (gate (restore-input a) fs refl lt)
    (cong (λ m → record fs { floc   = Data.Product.proj₁ (exec-restore-input-with-value m (floc fs) (falloc fs))
                           ; falloc = Data.Product.proj₂ (exec-restore-input-with-value m (floc fs) (falloc fs))
                           ; fpc    = suc (fpc fs) }) e)
  where import Data.Product
        open AbstractExec {FS} using (exec-restore-input-with-value)

-- the register moves
mov-in-step : ∀ (fs : FlatState)
            → flat-step-straight mov-to-input fs
              ≡ record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Input1 (readReg (regs (floc fs)) Output) }
                          ; fpc = suc (fpc fs) }
mov-in-step fs = refl

mov-out-step : ∀ (fs : FlatState)
             → flat-step-straight mov-to-output fs
               ≡ record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output (readReg (regs (floc fs)) Input1) }
                           ; fpc = suc (fpc fs) }
mov-out-step fs = refl

-- a slot's address
lea-step : ∀ (fs : FlatState) a → a < AllocState.frame-slots (falloc fs)
         → flat-step-straight (lea-slot a) fs
           ≡ record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output (SV-Ptr (AtStack (current-frame (falloc fs)) a)) }
                       ; fpc = suc (fpc fs) }
lea-step fs a lt = gate (lea-slot a) fs refl lt

-- a code address
code-step : ∀ (fs : FlatState) (ℓ : LabelId)
          → flat-step-straight (instr-load-code-addr ℓ) fs
            ≡ record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output (SV-Code ℓ) } ; fpc = suc (fpc fs) }
code-step fs ℓ = refl

open AbstractExec {FS} using (freeMem; freeMark; freeMem-just; freeMem-unmarked; freeMark-mono; heapRefOf; freeAtMark)
open AllocState using (freed)

-- a free's state after (D468): the block `Input1` points at, its cells cleared and marked freed
freed-st : FlatState → FlatState
freed-st fs = record fs { floc   = record (floc fs) { heapMem = freeMem (readReg (regs (floc fs)) Input1) (heapMem (floc fs)) }
                        ; falloc = record (falloc fs) { freed = freeMark (readReg (regs (floc fs)) Input1) (freed (falloc fs)) }
                        ; fpc    = suc (fpc fs) }

-- a free: past the gate (`Input1` the base of a live block of `n` words), that state
free-step : ∀ (fs : FlatState) n → block-base? n (readReg (regs (floc fs)) Input1) (falloc fs) ≡ true
          → flat-step-straight (instr-free-heap n) fs ≡ freed-st fs
free-step fs n g = straight-pass (instr-free-heap n) fs g


-- an allocation: the counter names the fresh block, of `n` words
alloc-step : ∀ (fs : FlatState) n
           → flat-step-straight (instr-alloc-heap n) fs
             ≡ record fs { floc   = record (floc fs) { regs = writeReg (regs (floc fs)) Output
                                                                (SV-Ptr (AtDynamic (heap-loc (mkHeapRef (AllocState.next-heap-ref (falloc fs))) 0))) }
                         ; falloc = record (falloc fs) { next-heap-ref = suc (AllocState.next-heap-ref (falloc fs))
                                                       ; block-size = size-with n (AllocState.next-heap-ref (falloc fs)) (block-size (falloc fs)) }
                         ; fpc    = suc (fpc fs) }
alloc-step fs n = refl

open ExecFinal {FS} using (exec-addr-at-resolved; exec-addr-in-block)

-- an address at an offset from `Input1`'s pointer, inside its block
addr-step : ∀ (fs : FlatState) o {loc} → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
          → heap-gate (just loc) ≡ just loc
          → in-block? (block-size (falloc fs)) (offsetLoc loc o) ≡ true
          → flat-step-straight (addr-at o) fs
            ≡ record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output (SV-Ptr (offsetLoc loc o)) }
                        ; fpc = suc (fpc fs) }
addr-step fs o {loc} e₁ g e₂ =
  trans (cong (λ r → record fs { floc = exec-addr-at-resolved (block-size (falloc fs)) o (heap-gate (sv-as-loc r)) (floc fs) ; fpc = suc (fpc fs) }) e₁)
    (trans (cong (λ m → record fs { floc = exec-addr-at-resolved (block-size (falloc fs)) o m (floc fs) ; fpc = suc (fpc fs) }) g)
        (cong (λ q → record fs { floc = exec-addr-in-block q (offsetLoc loc o) (floc fs) ; fpc = suc (fpc fs) }) e₂))

-- ★ D441: every written heap word lies in its block, below the counter
-- (so an address inside a cell the relation knows the words of is in it)
InBlk : FlatState → Set
InBlk fs = ∀ (hl : HeapLocation) {v} → heapMem (floc fs) hl ≡ just v
         → HeapRef.ref-id (HeapLocation.heap-ref hl) Data.Nat.< AllocState.next-heap-ref (falloc fs)
           × in-block? (AllocState.block-size (falloc fs)) (AtDynamic hl) ≡ true

-- the same heap and allocator
inb-same : ∀ {fs fs′ : FlatState} → heapMem (floc fs′) ≡ heapMem (floc fs) → falloc fs′ ≡ falloc fs → InBlk fs → InBlk fs′
inb-same {fs} {fs′} eh ea I hl e =
  subst (λ al → HeapRef.ref-id (HeapLocation.heap-ref hl) Data.Nat.< AllocState.next-heap-ref al
              × in-block? (AllocState.block-size al) (AtDynamic hl) ≡ true)
        (sym ea) (I hl (trans (cong (λ h → h hl) (sym eh)) e))

-- the same heap words, counter and block sizes (a call, a return: frames only)
inb-pt : ∀ {fs fs′ : FlatState} → (∀ hl → heapMem (floc fs′) hl ≡ heapMem (floc fs) hl)
       → AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs)
       → AllocState.block-size (falloc fs′) ≡ AllocState.block-size (falloc fs)
       → InBlk fs → InBlk fs′
inb-pt {fs} {fs′} eh en eb I hl e =
  subst (λ n → HeapRef.ref-id (HeapLocation.heap-ref hl) Data.Nat.< n × in-block? (AllocState.block-size (falloc fs′)) (AtDynamic hl) ≡ true)
        (sym en)
        (subst (λ bs → HeapRef.ref-id (HeapLocation.heap-ref hl) Data.Nat.< AllocState.next-heap-ref (falloc fs) × in-block? bs (AtDynamic hl) ≡ true)
               (sym eb) (I hl (trans (sym (eh hl)) e)))

-- an allocation leaves every other block's size
sw-old : ∀ n st (bs : ℕ → ℕ) r → ¬ r ≡ st → size-with n st bs r ≡ bs r
sw-old n st bs r ne = aux (r ≟ st)
  where
    aux : (d : Dec (r ≡ st)) → size-with-aux n {r} {st} bs d ≡ bs r
    aux (yes p) = ⊥-elim (ne p)
    aux (no _)  = refl

private
  T-true : ∀ {b} → T b → b ≡ true
  T-true {true} _ = refl

  refOf offOf : ValueLocation FS → ℕ
  refOf (AtDynamic hl) = HeapRef.ref-id (HeapLocation.heap-ref hl)
  refOf (AtStack _ _)  = 0
  offOf (AtDynamic hl) = HeapLocation.heap-offset hl
  offOf (AtStack _ _)  = 0

-- an allocation: the fresh block past every written word
inb-alloc : ∀ (fs : FlatState) n → InBlk fs → InBlk (flat-step-straight (instr-alloc-heap n) fs)
inb-alloc fs n I hl e = after (I hl e)
  where
    import Data.Nat.Properties
    r = HeapRef.ref-id (HeapLocation.heap-ref hl)
    nx = AllocState.next-heap-ref (falloc fs)
    after : r Data.Nat.< nx × in-block? (AllocState.block-size (falloc fs)) (AtDynamic hl) ≡ true
          → r Data.Nat.< suc nx × (HeapLocation.heap-offset hl <ᵇ size-with n nx (AllocState.block-size (falloc fs)) r) ≡ true
    after (lt , ib) =
      Data.Nat.Properties.m<n⇒m<1+n lt ,
      trans (cong (HeapLocation.heap-offset hl <ᵇ_) (sw-old n nx (AllocState.block-size (falloc fs)) r (λ eq → Data.Nat.Properties.<-irrefl eq lt))) ib

-- ★ words written into a block below the counter, each inside it
inb-write : ∀ {fs fs′ : FlatState} {a o n} (r : ℕ) → MovedW fs fs′ (AtDynamic (heap-loc (mkHeapRef r) 0)) a o n
          → r Data.Nat.< AllocState.next-heap-ref (falloc fs)
          → (∀ k → k Data.Nat.< n → (k + o) Data.Nat.< AllocState.block-size (falloc fs) r)
          → InBlk fs → InBlk fs′
inb-write {fs} {fs′} {a} {o} {n} r M lt bnd I hl e =
  subst (λ al → HeapRef.ref-id (HeapLocation.heap-ref hl) Data.Nat.< AllocState.next-heap-ref al
              × in-block? (AllocState.block-size al) (AtDynamic hl) ≡ true)
        (sym (w-alloc M)) (by-ref (HeapRef.ref-id (HeapLocation.heap-ref hl) ≟ r))
  where
    import Data.Nat.Properties
    off = HeapLocation.heap-offset hl
    Goal = HeapRef.ref-id (HeapLocation.heap-ref hl) Data.Nat.< AllocState.next-heap-ref (falloc fs)
         × in-block? (AllocState.block-size (falloc fs)) (AtDynamic hl) ≡ true
    -- a word not written: as before
    old : (∀ k → k Data.Nat.< n → ¬ AtDynamic hl ≡ offsetLoc (AtDynamic (heap-loc (mkHeapRef r) 0)) (k + o)) → Goal
    old nw = I hl (trans (sym (w-rest M (AtDynamic hl) nw)) e)
    -- a written word: in the block, by the bound
    written : HeapRef.ref-id (HeapLocation.heap-ref hl) ≡ r → o Data.Nat.≤ off → off Data.Nat.< o + n → Goal
    written refl le lt′ =
      lt , T-true (Data.Nat.Properties.<⇒<ᵇ (subst (Data.Nat._< AllocState.block-size (falloc fs) r) (Data.Nat.Properties.m∸n+n≡m le)
                                               (bnd (off Data.Nat.∸ o) (subst (off Data.Nat.∸ o Data.Nat.<_) (Data.Nat.Properties.m+n∸m≡n o n) (Data.Nat.Properties.∸-monoˡ-< lt′ le′)))))
      where
        le′ : o Data.Nat.≤ off
        le′ = le
    by-off : HeapRef.ref-id (HeapLocation.heap-ref hl) ≡ r → Dec (o Data.Nat.≤ off) → Dec (off Data.Nat.< o + n) → Goal
    by-off er (yes le) (yes lt′) = written er le lt′
    by-off er (no nle) _ = old (λ k k< eq → nle (subst (o Data.Nat.≤_) (sym (trans (cong offOf eq) (+-identityʳ (k + o))))
                                                     (Data.Nat.Properties.m≤n+m o k)))
    by-off er (yes le) (no nlt) = old (λ k k< eq → nlt (subst (Data.Nat._< o + n) (sym (trans (cong offOf eq) (+-identityʳ (k + o))))
                                                            (subst (Data.Nat._< o + n) (Data.Nat.Properties.+-comm o k)
                                                              (Data.Nat.Properties.+-monoʳ-< o k<))))
    by-ref : Dec (HeapRef.ref-id (HeapLocation.heap-ref hl) ≡ r) → Goal
    by-ref (yes er) = by-off er (o ≤? off) (off <? o + n)
    by-ref (no ne)  = old (λ k k< eq → ne (cong refOf eq))

------------------------------------------------------------------------
-- ★ WHAT A RUN LEAVES ALONE (D435): the frame, its slots' count, the saved
-- frames, the return pcs, and every other frame's slots. A move says so in
-- its record; a run of moves composes them.
------------------------------------------------------------------------

-- the blocks a run freed, by its free's input (a free names one block)
freeList : Maybe ℕ → List ℕ
freeList (just r) = r ∷ []
freeList nothing  = []

freedList : StoredValue FS → List ℕ
freedList v = freeList (heapRefOf v)

-- (D469: `fl` the blocks the run freed)
record Keep (fl : List ℕ) (fs fs′ : FlatState) : Set where
  field
    k-frame : current-frame (falloc fs′) ≡ current-frame (falloc fs)
    k-slots : AllocState.frame-slots (falloc fs′) ≡ AllocState.frame-slots (falloc fs)
    k-saved : AllocState.saved-frames (falloc fs′) ≡ AllocState.saved-frames (falloc fs)
    k-ret   : fret fs′ ≡ fret fs
    k-other : ∀ f x → ¬ f ≡ current-frame (falloc fs) → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x
    k-halt  : halted (floc fs′) ≡ halted (floc fs)
    k-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)
    k-inb   : InBlk fs → InBlk fs′
    -- D468: a freed block stays freed
    k-freed : ∀ r → AllocState.freed (falloc fs) r ≡ true → AllocState.freed (falloc fs′) r ≡ true
    -- D469: the counter only grows, and a block below it keeps its size
    k-next  : AllocState.next-heap-ref (falloc fs) ≤ AllocState.next-heap-ref (falloc fs′)
    k-size  : ∀ r → r < AllocState.next-heap-ref (falloc fs) → AllocState.block-size (falloc fs′) r ≡ AllocState.block-size (falloc fs) r
    -- D469: a block the run freed is one of `fl`
    k-unfr  : ∀ r → AllocState.freed (falloc fs′) r ≡ true → AllocState.freed (falloc fs) r ≡ true ⊎ r ∈ fl
open Keep

keep-refl : ∀ {fs} → Keep [] fs fs
keep-refl = record { k-frame = refl ; k-slots = refl ; k-saved = refl ; k-ret = refl ; k-other = λ _ _ _ → refl ; k-halt = refl ; k-log = refl ; k-inb = λ I → I ; k-freed = λ _ e → e
            ; k-next = ≤-reflexive refl ; k-size = λ _ _ → refl ; k-unfr = λ _ e → inj₁ e }

keep-trans : ∀ {fl₁ fl₂ fs₁ fs₂ fs₃} → Keep fl₁ fs₁ fs₂ → Keep fl₂ fs₂ fs₃ → Keep (fl₁ ++ fl₂) fs₁ fs₃
keep-trans {fl₁} K₁ K₂ = record
  { k-frame = trans (k-frame K₂) (k-frame K₁)
  ; k-slots = trans (k-slots K₂) (k-slots K₁)
  ; k-saved = trans (k-saved K₂) (k-saved K₁)
  ; k-ret   = trans (k-ret K₂) (k-ret K₁)
  ; k-other = λ f x ne → trans (k-other K₂ f x (λ e → ne (trans e (k-frame K₁)))) (k-other K₁ f x ne)
  ; k-halt  = trans (k-halt K₂) (k-halt K₁)
  ; k-log   = trans (k-log K₂) (k-log K₁)
  ; k-inb   = λ I → k-inb K₂ (k-inb K₁ I)
  ; k-freed = λ r e → k-freed K₂ r (k-freed K₁ r e)
  ; k-next  = ≤-trans (k-next K₁) (k-next K₂)
  ; k-size  = λ r lt → trans (k-size K₂ r (<-≤-trans lt (k-next K₁))) (k-size K₁ r lt)
  ; k-unfr  = λ r e → [ (λ e₁ → [ inj₁ , (λ m → inj₂ (∈-++⁺ˡ m)) ]′ (k-unfr K₁ r e₁)) , (λ m → inj₂ (∈-++⁺ʳ fl₁ m)) ]′ (k-unfr K₂ r e) }

-- a run that keeps the whole allocation state, the return pcs, the other frames and the flag
keep-alloc : ∀ {fs fs′} → falloc fs′ ≡ falloc fs → fret fs′ ≡ fret fs
           → (∀ f x → ¬ f ≡ current-frame (falloc fs) → stackMem (floc fs′) f x ≡ stackMem (floc fs) f x)
           → halted (floc fs′) ≡ halted (floc fs)
           → LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)
           → (InBlk fs → InBlk fs′)
           → Keep [] fs fs′
keep-alloc a r o h lg ib = record { k-frame = cong current-frame a ; k-slots = cong AllocState.frame-slots a
                                  ; k-saved = cong AllocState.saved-frames a ; k-ret = r ; k-other = o ; k-halt = h ; k-log = lg ; k-inb = ib
                                  ; k-freed = λ r e → trans (cong (λ al → AllocState.freed al r) a) e
                                  ; k-next = ≤-reflexive (cong AllocState.next-heap-ref (sym a))
                                  ; k-size = λ r _ → cong (λ al → AllocState.block-size al r) a
                                  ; k-unfr = λ r e → inj₁ (trans (cong (λ al → AllocState.freed al r) (sym a)) e) }

keepS : ∀ {fs fs′ a b n} → MovedS fs fs′ a b n → Keep [] fs fs′
keepS {fs} {fs′} M = keep-alloc (m-alloc M) (m-ret M) (m-frame M) (m-halt M) (m-log M) (inb-same {fs} {fs′} (m-heap M) (m-alloc M))

keepP : ∀ {fs fs′ loc o b n} → MovedP fs fs′ loc o b n → Keep [] fs fs′
keepP {fs} {fs′} M = keep-alloc (p-alloc M) (p-ret M) (p-frame M) (p-halt M) (p-log M) (inb-same {fs} {fs′} (p-heap M) (p-alloc M))

keepD : ∀ {fs fs′ a b n} → MovedD fs fs′ a b n → Keep [] fs fs′
keepD {fs} {fs′} M = keep-alloc (d-alloc M) (d-ret M) (d-frame M) (d-halt M) (d-log M) (inb-same {fs} {fs′} (d-heap M) (d-alloc M))

-- a move into a block: no other frame's slot is written when none is the target
keepW : ∀ {fs fs′ loc a o n} → MovedW fs fs′ loc a o n
      → (∀ f x → ¬ f ≡ current-frame (falloc fs) → ∀ k → k Data.Nat.< n → ¬ AtStack f x ≡ offsetLoc loc (k + o))
      → (InBlk fs → InBlk fs′)
      → Keep [] fs fs′
keepW M h ib = keep-alloc (w-alloc M) (w-ret M) (λ f x ne → w-rest M (AtStack f x) (h f x ne)) (w-halt M) (w-log M) ib

keepF : ∀ {fs fs′ b n} → Filled fs fs′ b n → Keep [] fs fs′
keepF {fs} {fs′} F = keep-alloc (f-alloc F) (f-ret F) (f-frame F) (f-halt F) (f-log F) (inb-same {fs} {fs′} (f-heap F) (f-alloc F))

-- a step on the registers alone
keep-regs : ∀ {fs} rs pc → Keep [] fs (record fs { floc = record (floc fs) { regs = rs } ; fpc = pc })
keep-regs rs pc = keep-alloc refl refl (λ _ _ _ → refl) refl refl (λ I → I)

-- a store to the current frame
keep-store : ∀ fs b v → Keep [] fs (record fs { floc = writeLoc (floc fs) (AtStack (current-frame (falloc fs)) b) v ; fpc = suc (fpc fs) })
keep-store fs b v = keep-alloc refl refl (λ f x ne → store-frame (floc fs) (current-frame (falloc fs)) b v f x (λ e → ne (sym e)))
                      (writeLoc-halted (floc fs) (AtStack (current-frame (falloc fs)) b) v)
                      (LogPres.writeLoc-log {FS} (floc fs) (AtStack (current-frame (falloc fs)) b) v) (λ I → I)

-- a step on the pc alone (a free: the heap's blocks are the allocator's)
keep-pc : ∀ {fs} pc → Keep [] fs (record fs { fpc = pc })
keep-pc pc = keep-alloc refl refl (λ _ _ _ → refl) refl refl (λ I → I)

-- an allocation: the counter and the blocks' sizes move, the frames do not
keep-heap : ∀ fs n → Keep [] fs (flat-step-straight (instr-alloc-heap n) fs)
keep-heap fs n = record { k-frame = refl ; k-slots = refl ; k-saved = refl ; k-ret = refl ; k-other = λ _ _ _ → refl ; k-halt = refl ; k-log = refl
                        ; k-inb = inb-alloc fs n ; k-freed = λ _ e → e
                        ; k-next = Data.Nat.Properties.n≤1+n (AllocState.next-heap-ref (falloc fs))
                        ; k-size = λ r lt → sw-old n (AllocState.next-heap-ref (falloc fs)) (AllocState.block-size (falloc fs)) r (λ eq → Data.Nat.Properties.<-irrefl eq lt)
                        ; k-unfr = λ _ e → inj₁ e }
  where import Data.Nat.Properties

------------------------------------------------------------------------
-- ★ A STRAIGHT RUN of `n` steps: it keeps what `Keep` says, and ends `n`
-- past where it began. Composed as `FlatSteps-++` composes the steps, so a
-- lemma's `Ran` count is its `FlatSteps` count.
------------------------------------------------------------------------

-- a wider list of what may have been freed
keep-widen : ∀ {fl fl′ fs fs′} → (∀ {q} → q ∈ fl → q ∈ fl′) → Keep fl fs fs′ → Keep fl′ fs fs′
keep-widen sub K = record
  { k-frame = k-frame K ; k-slots = k-slots K ; k-saved = k-saved K ; k-ret = k-ret K ; k-other = k-other K
  ; k-halt = k-halt K ; k-log = k-log K ; k-inb = k-inb K ; k-freed = k-freed K ; k-next = k-next K ; k-size = k-size K
  ; k-unfr = λ r e → [ inj₁ , (λ m → inj₂ (sub m)) ]′ (k-unfr K r e) }

-- unfreed after, unfreed before (a freed block stays freed)
unfreed-back : ∀ {fl fs fs′ r} → Keep fl fs fs′ → AllocState.freed (falloc fs′) r ≡ false → AllocState.freed (falloc fs) r ≡ false
unfreed-back {fs = fs} {r = r} K f = at (AllocState.freed (falloc fs) r) refl
  where
    at : ∀ b → AllocState.freed (falloc fs) r ≡ b → AllocState.freed (falloc fs) r ≡ false
    at false e = e
    at true  e = ⊥-elim (true≢false (trans (sym (k-freed K r e)) f))
      where true≢false : true ≡ false → ⊥
            true≢false ()

-- the heap's blocks below `lo` as they were, unless freed since (D468: a free
-- clears its block; a held value's blocks are never freed)
-- (D469: every block below `lo` but the ones the run freed, `fl`)
Old : ℕ → List ℕ → FlatState → FlatState → Set
Old lo fl fs fs′ = ∀ (hl : Once.Memory.HeapAddress.HeapLocation)
              → Once.Memory.HeapAddress.HeapRef.ref-id (Once.Memory.HeapAddress.HeapLocation.heap-ref hl) Data.Nat.< lo
              → ¬ (Once.Memory.HeapAddress.HeapRef.ref-id (Once.Memory.HeapAddress.HeapLocation.heap-ref hl) ∈ fl)
              → heapMem (floc fs′) hl ≡ heapMem (floc fs) hl

-- `n` steps, `a` of them allocations: the heap counter `a` past where it
-- was; every block below `lo` (a lemma's: the counter where it began) as it
-- was; every slot of the frame from `hi` up (a lemma's: the frame's budget,
-- where its save slots are) as it was
-- the blocks a run allocated, from the counter `s` on, at sizes `bl` (D469)
BornAt : List ℕ → ℕ → (ℕ → ℕ) → Set
BornAt []       s bs = ⊤
BornAt (k ∷ bl) s bs = bs s ≡ k × BornAt bl (suc s) bs

-- `n` steps, allocating blocks of sizes `bl`, freeing the blocks `fl` (D468/D469)
record Ran (n : ℕ) (bl fl : List ℕ) (lo hi : ℕ) (fs fs′ : FlatState) : Set where
  field
    r-keep : Keep fl fs fs′
    r-pc   : fpc fs′ ≡ n + fpc fs
    r-next : AllocState.next-heap-ref (falloc fs′) ≡ length bl + AllocState.next-heap-ref (falloc fs)
    r-born : BornAt bl (AllocState.next-heap-ref (falloc fs)) (AllocState.block-size (falloc fs′))
    r-old  : Old lo fl fs fs′
    r-top  : ∀ x → hi Data.Nat.≤ x → slot fs′ x ≡ slot fs x
open Ran

-- D469: a block freed by the run is one of `fl`
r-unfr : ∀ {n bl fl lo hi fs fs′} → Ran n bl fl lo hi fs fs′ → ∀ r → AllocState.freed (falloc fs′) r ≡ true → AllocState.freed (falloc fs) r ≡ true ⊎ r ∈ fl
r-unfr R = k-unfr (r-keep R)

-- a free (`free-step`) keeps the frames, and every block it did not free
keep-free : ∀ fs → Keep (freedList (readReg (regs (floc fs)) Input1)) fs (freed-st fs)
keep-free fs = record { k-frame = refl ; k-slots = refl ; k-saved = refl ; k-ret = refl ; k-other = λ _ _ _ → refl
                      ; k-halt = refl ; k-log = refl
                      ; k-inb = λ I hl e → I hl (freeMem-just (readReg (regs (floc fs)) Input1) (heapMem (floc fs)) hl e)
                      ; k-freed = λ r e → freeMark-mono (readReg (regs (floc fs)) Input1) (freed (falloc fs)) r e
                      ; k-next = ≤-reflexive refl ; k-size = λ _ _ → refl
                      ; k-unfr = λ r e → marked (heapRefOf (readReg (regs (floc fs)) Input1)) r e }
  where
    marked : ∀ (m : Maybe ℕ) r → freeAtMark m (freed (falloc fs)) r ≡ true
           → freed (falloc fs) r ≡ true ⊎ r ∈ freeList m
    marked (just q) r e = by (r ≡ᵇ q) refl e
      where
        by : ∀ b → (r ≡ᵇ q) ≡ b → b ∨ freed (falloc fs) r ≡ true → freed (falloc fs) r ≡ true ⊎ r ∈ q ∷ []
        by true  eq _ = inj₂ (here (≡ᵇ⇒≡ r q (subst T (sym eq) tt)))
        by false eq e′ = inj₁ e′
    marked nothing r e = inj₁ e

-- a run that freed nothing: freed exactly as before
keep-freed-eq : ∀ {fs fs′} → Keep [] fs fs′ → ∀ q → AllocState.freed (falloc fs′) q ≡ AllocState.freed (falloc fs) q
keep-freed-eq {fs} {fs′} K q = by (AllocState.freed (falloc fs) q) refl
  where
    by : ∀ b → AllocState.freed (falloc fs) q ≡ b → AllocState.freed (falloc fs′) q ≡ AllocState.freed (falloc fs) q
    by true  e = trans (k-freed K q e) (sym e)
    by false e = by′ (AllocState.freed (falloc fs′) q) refl
      where
        by′ : ∀ b′ → AllocState.freed (falloc fs′) q ≡ b′ → AllocState.freed (falloc fs′) q ≡ AllocState.freed (falloc fs) q
        by′ false e′ = trans e′ (sym e)
        by′ true  e′ = [ (λ e″ → trans e′ (sym e″)) , (λ ()) ]′ (k-unfr K q e′)

-- a longer list of what may have been freed
old-widen : ∀ {lo fl fl′ fs fs′} → (∀ {q} → q ∈ fl → q ∈ fl′) → Old lo fl fs fs′ → Old lo fl′ fs fs′
old-widen sub o hl lt nf = o hl lt (λ m → nf (sub m))

-- a block not freed is not marked
unmarked : ∀ (m : Maybe ℕ) r → ¬ (r ∈ freeList m) → freeAtMark m (λ _ → false) r ≡ false
unmarked (just q) r nf = by (r ≡ᵇ q) refl
  where
    by : ∀ b → (r ≡ᵇ q) ≡ b → b ∨ false ≡ false
    by true  e = ⊥-elim (nf (here (≡ᵇ⇒≡ r q (subst T (sym e) tt))))
    by false e = refl
unmarked nothing r nf = refl

ran-free : ∀ {lo hi} fs → Ran 1 [] (freedList (readReg (regs (floc fs)) Input1)) lo hi fs (freed-st fs)
ran-free fs = record { r-keep = keep-free fs ; r-pc = refl ; r-next = refl
                     ; r-old = λ hl _ nf → freeMem-unmarked (readReg (regs (floc fs)) Input1) (heapMem (floc fs)) (λ _ → false) hl
                                              (unmarked (heapRefOf (readReg (regs (floc fs)) Input1)) _ nf)
                     ; r-top = λ _ _ → refl }

-- a free whose input is known
ran-free-at : ∀ {lo hi} fs {w} → readReg (regs (floc fs)) Input1 ≡ w → Ran 1 [] (freedList w) lo hi fs (freed-st fs)
ran-free-at fs refl = ran-free fs

-- a run keeps every word in its block (D441; by its `Keep`)
r-inb : ∀ {n bl fl lo hi fs fs′} → Ran n bl fl lo hi fs fs′ → InBlk fs → InBlk fs′
r-inb R = k-inb (r-keep R)

private
  add-trans : ∀ {u v w} a b → v ≡ a + u → w ≡ b + v → w ≡ (a + b) + u
  add-trans {u} a b e₁ e₂ =
    trans e₂ (trans (cong (b +_) e₁) (trans (sym (Data.Nat.Properties.+-assoc b a u)) (cong (_+ u) (Data.Nat.Properties.+-comm b a))))
    where import Data.Nat.Properties

  -- a slot at or past `hi` is not one of `n` from `b`, when they end by `hi`
  not-in : ∀ {hi b n x k} → b + n Data.Nat.≤ hi → hi Data.Nat.≤ x → k Data.Nat.< n → ¬ x ≡ k + b
  not-in {hi} {b} {n} {x} {k} bnd le k< e =
    Data.Nat.Properties.<-irrefl (sym e)
      (Data.Nat.Properties.<-≤-trans (Data.Nat.Properties.+-monoˡ-< b k<)
        (Data.Nat.Properties.≤-trans (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-comm n b))
          (Data.Nat.Properties.≤-trans bnd le)))
    where import Data.Nat.Properties

  not-in′ : ∀ {hi b n x k} → b + n Data.Nat.≤ hi → hi Data.Nat.≤ x → k Data.Nat.< n → ¬ x ≡ b + k
  not-in′ {b = b} {k = k} bnd le k< e = not-in bnd le k< (trans e (Data.Nat.Properties.+-comm b k))
    where import Data.Nat.Properties

-- a fresh block's size is the allocation's
sw-new : ∀ n st (bs : ℕ → ℕ) → size-with n st bs st ≡ n
sw-new n st bs = aux (st ≟ st)
  where
    aux : (d : Dec (st ≡ st)) → size-with-aux n {st} {st} bs d ≡ n
    aux (yes _) = refl
    aux (no ne) = ⊥-elim (ne refl)

-- the blocks of two runs, the first's kept by the second
born-++ : ∀ bl₁ bl₂ s {bs₂ bs₃ : ℕ → ℕ} → BornAt bl₁ s bs₂ → (∀ r → r < length bl₁ + s → bs₃ r ≡ bs₂ r)
        → BornAt bl₂ (length bl₁ + s) bs₃ → BornAt (bl₁ ++ bl₂) s bs₃
born-++ []        bl₂ s b₁ kp b₂ = b₂
born-++ (k ∷ bl₁) bl₂ s {bs₂} {bs₃} (e , b₁) kp b₂ =
  trans (kp s (s≤s (m≤n+m s (length bl₁)))) e ,
  born-++ bl₁ bl₂ (suc s) b₁ (λ r lt → kp r (subst (r <_) (+-suc (length bl₁) s) lt))
    (subst (λ z → BornAt bl₂ z bs₃) (sym (+-suc (length bl₁) s)) b₂)
  where open import Data.Nat using (s≤s)

ran-refl : ∀ {lo hi fs} → Ran 0 [] [] lo hi fs fs
ran-refl = record { r-keep = keep-refl ; r-pc = refl ; r-next = refl ; r-born = tt ; r-old = λ _ _ _ → refl ; r-top = λ _ _ → refl }

ran-trans : ∀ {n₁ n₂ bl₁ bl₂ fl₁ fl₂ lo hi fs₁ fs₂ fs₃} → Ran n₁ bl₁ fl₁ lo hi fs₁ fs₂ → Ran n₂ bl₂ fl₂ lo hi fs₂ fs₃
          → Ran (n₁ + n₂) (bl₁ ++ bl₂) (fl₁ ++ fl₂) lo hi fs₁ fs₃
ran-trans {n₁} {n₂} {bl₁} {bl₂} {fl₁} {fl₂} {fs₁ = fs₁} {fs₂} {fs₃} R₁ R₂ = record
  { r-keep = keep-trans (r-keep R₁) (r-keep R₂)
  ; r-pc   = add-trans n₁ n₂ (r-pc R₁) (r-pc R₂)
  ; r-next = trans (add-trans (length bl₁) (length bl₂) (r-next R₁) (r-next R₂))
                   (cong (_+ AllocState.next-heap-ref (falloc fs₁)) (sym (length-++ bl₁)))
  ; r-born = born-++ bl₁ bl₂ (AllocState.next-heap-ref (falloc fs₁)) (r-born R₁)
               (λ r lt → k-size (r-keep R₂) r (subst (r <_) (sym (r-next R₁)) lt))
               (subst (λ s → BornAt bl₂ s (AllocState.block-size (falloc fs₃))) (r-next R₁) (r-born R₂))
  ; r-old  = λ hl lt nf → trans (r-old R₂ hl lt (λ m → nf (∈-++⁺ʳ fl₁ m))) (r-old R₁ hl lt (λ m → nf (∈-++⁺ˡ m)))
  ; r-top  = λ x le → trans (r-top R₂ x le) (r-top R₁ x le)
  }

ranS : ∀ {lo hi fs fs′ a b n} → MovedS fs fs′ a b n → b + n Data.Nat.≤ hi → Ran (ln n) [] [] lo hi fs fs′
ranS {fs = fs} {fs′} M bnd = record { r-keep = keepS M ; r-pc = m-pc M ; r-next = cong AllocState.next-heap-ref (m-alloc M) ; r-born = tt
                    ; r-old = λ hl _ _ → cong (λ h → h hl) (m-heap M) ; r-top = λ x le → m-rest M x (λ k k< → not-in bnd le k<)                    }

ranP : ∀ {lo hi fs fs′ loc o b n} → MovedP fs fs′ loc o b n → b + n Data.Nat.≤ hi → Ran (ln n) [] [] lo hi fs fs′
ranP {fs = fs} {fs′} M bnd = record { r-keep = keepP M ; r-pc = p-pc M ; r-next = cong AllocState.next-heap-ref (p-alloc M) ; r-born = tt
                    ; r-old = λ hl _ _ → cong (λ h → h hl) (p-heap M) ; r-top = λ x le → p-rest M x (λ k k< → not-in bnd le k<)                    }

ranD : ∀ {lo hi fs fs′ a b n} → MovedD fs fs′ a b n → b + n Data.Nat.≤ hi → Ran (ln n) [] [] lo hi fs fs′
ranD {fs = fs} {fs′} M bnd = record { r-keep = keepD M ; r-pc = d-pc M ; r-next = cong AllocState.next-heap-ref (d-alloc M) ; r-born = tt
                    ; r-old = λ hl _ _ → cong (λ h → h hl) (d-heap M) ; r-top = λ x le → d-rest M x (λ k k< → not-in′ bnd le k<)                    }

-- a move into a block at or past `lo` (no slot of the frame written)
ranW : ∀ {lo hi fs fs′ loc a o n} → MovedW fs fs′ loc a o n
     → (∀ f x → ¬ f ≡ current-frame (falloc fs) → ∀ k → k Data.Nat.< n → ¬ AtStack f x ≡ offsetLoc loc (k + o))
     → (∀ x → ∀ k → k Data.Nat.< n → ¬ AtStack (current-frame (falloc fs)) x ≡ offsetLoc loc (k + o))
     → (∀ hl → Once.Memory.HeapAddress.HeapRef.ref-id (Once.Memory.HeapAddress.HeapLocation.heap-ref hl) Data.Nat.< lo
           → ∀ k → k Data.Nat.< n → ¬ AtDynamic hl ≡ offsetLoc loc (k + o))
     → (InBlk fs → InBlk fs′)
     → Ran (ln n) [] [] lo hi fs fs′
ranW {fs = fs} {fs′} M h hc d ib = record
  { r-keep = keepW M h ib ; r-pc = w-pc M ; r-next = cong AllocState.next-heap-ref (w-alloc M) ; r-born = tt
  ; r-old = λ hl lt _ → w-rest M (AtDynamic hl) (d hl lt)
  ; r-top = λ x _ → trans (cong (λ g → stackMem (floc fs′) g x) (cong current-frame (w-alloc M)))
                          (w-rest M (AtStack (current-frame (falloc fs)) x) (hc x))
  }

-- a block's words are not below its own reference
fresh-block : ∀ r hl o → Once.Memory.HeapAddress.HeapRef.ref-id (Once.Memory.HeapAddress.HeapLocation.heap-ref hl) Data.Nat.< r
            → ¬ AtDynamic {FS} hl ≡ offsetLoc (AtDynamic (heap-loc (mkHeapRef r) 0)) o
fresh-block r hl o lt refl = Data.Nat.Properties.<-irrefl refl lt
  where import Data.Nat.Properties

ranF : ∀ {lo hi fs fs′ b n} → Filled fs fs′ b n → b + n Data.Nat.≤ hi → Ran n [] [] lo hi fs fs′
ranF {fs = fs} {fs′} F bnd = record { r-keep = keepF F ; r-pc = f-pc F ; r-next = cong AllocState.next-heap-ref (f-alloc F) ; r-born = tt
                    ; r-old = λ hl _ _ → cong (λ h → h hl) (f-heap F) ; r-top = λ x le → f-rest F x (λ k k< → not-in bnd le k<)                    }

ran-regs : ∀ {lo hi fs} rs → Ran 1 [] [] lo hi fs (record fs { floc = record (floc fs) { regs = rs } ; fpc = suc (fpc fs) })
ran-regs rs = record { r-keep = keep-regs rs _ ; r-pc = refl ; r-next = refl ; r-born = tt ; r-old = λ _ _ _ → refl ; r-top = λ _ _ → refl }

ran-store : ∀ {lo hi} fs b v → b Data.Nat.< hi
          → Ran 1 [] [] lo hi fs (record fs { floc = writeLoc (floc fs) (AtStack (current-frame (falloc fs)) b) v ; fpc = suc (fpc fs) })
ran-store fs b v b< = record
  { r-keep = keep-store fs b v ; r-pc = refl ; r-next = refl ; r-born = tt ; r-old = λ _ _ _ → refl
  ; r-top = λ x le → store-other (floc fs) (current-frame (falloc fs)) b v x
                       (λ e → Data.Nat.Properties.<-irrefl e (Data.Nat.Properties.<-≤-trans b< le))
  }
  where import Data.Nat.Properties

ran-pc : ∀ {lo hi fs} → Ran 1 [] [] lo hi fs (record fs { fpc = suc (fpc fs) })
ran-pc = record { r-keep = keep-pc _ ; r-pc = refl ; r-next = refl ; r-born = tt ; r-old = λ _ _ _ → refl ; r-top = λ _ _ → refl }

ran-heap : ∀ {lo hi} fs n → Ran 1 (n ∷ []) [] lo hi fs (flat-step-straight (instr-alloc-heap n) fs)
ran-heap fs n = record { r-keep = keep-heap fs n ; r-pc = refl ; r-next = refl ; r-born = sw-new n (AllocState.next-heap-ref (falloc fs)) (AllocState.block-size (falloc fs)) , tt ; r-old = λ _ _ _ → refl ; r-top = λ _ _ → refl }

-- a bound further up
ran-hi : ∀ {n bl fl lo hi hi′ fs fs′} → hi Data.Nat.≤ hi′ → Ran n bl fl lo hi fs fs′ → Ran n bl fl lo hi′ fs fs′
ran-hi le R = record { r-keep = r-keep R ; r-pc = r-pc R ; r-next = r-next R ; r-born = r-born R ; r-old = r-old R
                     ; r-top = λ x le′ → r-top R x (Data.Nat.Properties.≤-trans le le′) }
  where import Data.Nat.Properties

-- the slot below a nonzero bound
pred< : ∀ {b} → 1 Data.Nat.≤ b → b Data.Nat.∸ 1 Data.Nat.< b
pred< {suc b} _ = Data.Nat.Properties.n<1+n b
  where import Data.Nat.Properties
