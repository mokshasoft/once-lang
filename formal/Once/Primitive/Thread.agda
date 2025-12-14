------------------------------------------------------------------------
-- Once.Primitive.Thread
--
-- Axiomatic specification of concurrency primitives.
--
-- This module provides an abstract model of threads, mutexes, and
-- atomic operations, independent of implementation details.
--
-- CONCURRENCY MODEL:
-- We use a sequential consistency model where operations on shared
-- state appear to execute in some global total order. This is simpler
-- than relaxed memory models but sufficient for reasoning about
-- correctly synchronized programs.
--
-- KEY INSIGHT: Concurrency is orthogonal to the type system. These
-- axioms constrain runtime behavior without affecting type checking.
--
------------------------------------------------------------------------

module Once.Primitive.Thread where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)

------------------------------------------------------------------------
-- Abstract Types
------------------------------------------------------------------------

-- | Thread identifier
postulate
  ThreadId : Set

-- | Thread ID equality is decidable
postulate
  _≟ThreadId_ : (t₁ t₂ : ThreadId) → Dec (t₁ ≡ t₂)

-- | Thread handle (for joining)
postulate
  ThreadHandle : Set

-- | Mutex (mutual exclusion lock)
postulate
  Mutex : Set

-- | Condition variable
postulate
  CondVar : Set

-- | Atomic memory location
postulate
  AtomicLoc : Set

-- | Concurrent world state
--
-- This extends the sequential World with thread-related state:
-- - Set of running threads
-- - Lock ownership
-- - Condition variable wait queues
-- - Atomic memory contents
postulate
  CWorld : Set

-- | Initial concurrent world (single main thread)
postulate
  initialCWorld : CWorld

------------------------------------------------------------------------
-- Thread Lifecycle
------------------------------------------------------------------------

-- | Spawn a new thread
--
-- spawn f w = (handle, w')
--   Creates a new thread that will execute f.
--   Returns a handle for joining.
postulate
  spawn : (ℕ → ℕ) → CWorld → ThreadHandle × CWorld
  -- Note: The function type (ℕ → ℕ) is simplified.
  -- Real threads take effectful functions.

-- | Join a thread (wait for completion)
--
-- join h w = w'
--   Blocks until the thread completes.
postulate
  join : ThreadHandle → CWorld → CWorld

-- | Detach a thread (don't wait for completion)
postulate
  detach : ThreadHandle → CWorld → CWorld

-- | Get current thread ID
postulate
  getCurrentThread : CWorld → ThreadId × CWorld

------------------------------------------------------------------------
-- Mutex Operations
------------------------------------------------------------------------

-- | Create a new mutex (initially unlocked)
postulate
  mutexInit : CWorld → Mutex × CWorld

-- | Lock a mutex
--
-- Blocks if already held by another thread.
-- MUST NOT be called if already held by current thread (undefined).
postulate
  mutexLock : Mutex → CWorld → CWorld

-- | Unlock a mutex
--
-- MUST be called by the thread that holds the lock.
postulate
  mutexUnlock : Mutex → CWorld → CWorld

-- | Try to lock without blocking
--
-- Returns true if lock acquired, false otherwise.
postulate
  mutexTryLock : Mutex → CWorld → Bool × CWorld

------------------------------------------------------------------------
-- Mutex Axioms
------------------------------------------------------------------------

-- | Mutex state tracking
postulate
  isLocked : Mutex → CWorld → Bool
  lockOwner : Mutex → CWorld → Maybe ThreadId

-- | New mutexes are unlocked
postulate
  mutex-init-unlocked : ∀ w →
    let (m , w') = mutexInit w
    in isLocked m w' ≡ false

-- | Lock makes mutex locked
postulate
  mutex-lock-locks : ∀ m w →
    isLocked m (mutexLock m w) ≡ true

-- | Unlock makes mutex unlocked
postulate
  mutex-unlock-unlocks : ∀ m w →
    isLocked m w ≡ true →
    isLocked m (mutexUnlock m w) ≡ false

-- | Mutual exclusion: at most one thread holds a lock
-- (This is implicit in the model - lockOwner returns Maybe ThreadId)

------------------------------------------------------------------------
-- Condition Variables
------------------------------------------------------------------------

-- | Create a new condition variable
postulate
  condInit : CWorld → CondVar × CWorld

-- | Wait on condition variable
--
-- MUST hold the associated mutex when called.
-- Releases mutex, waits for signal, then reacquires mutex.
postulate
  condWait : CondVar → Mutex → CWorld → CWorld

-- | Signal one waiting thread
postulate
  condSignal : CondVar → CWorld → CWorld

-- | Broadcast to all waiting threads
postulate
  condBroadcast : CondVar → CWorld → CWorld

------------------------------------------------------------------------
-- Condition Variable Axioms
------------------------------------------------------------------------

-- | Wait releases and reacquires mutex
--
-- After condWait returns, the calling thread holds the mutex.
-- (The mutex is released during the wait.)
postulate
  cond-wait-reacquires : ∀ cv m w tid →
    let (tid' , _) = getCurrentThread w
    in tid' ≡ tid →
    isLocked m w ≡ true →
    lockOwner m w ≡ just tid →
    let w' = condWait cv m w
    in isLocked m w' ≡ true

------------------------------------------------------------------------
-- Atomic Operations
------------------------------------------------------------------------

-- | Create an atomic location (initialized to 0)
postulate
  atomicInit : CWorld → AtomicLoc × CWorld

-- | Atomic load
postulate
  atomicLoad : AtomicLoc → CWorld → ℤ × CWorld

-- | Atomic store
postulate
  atomicStore : AtomicLoc → ℤ → CWorld → CWorld

-- | Compare-and-swap
--
-- cas loc expected new w = (old, w')
--   If loc contains expected, atomically replace with new.
--   Returns the old value (whether swap succeeded or not).
postulate
  atomicCAS : AtomicLoc → ℤ → ℤ → CWorld → ℤ × CWorld

-- | Fetch-and-add
--
-- Returns old value, stores old + delta.
postulate
  atomicFetchAdd : AtomicLoc → ℤ → CWorld → ℤ × CWorld

------------------------------------------------------------------------
-- Atomic Axioms
------------------------------------------------------------------------

-- | New atomics are zero
postulate
  atomic-init-zero : ∀ w →
    let (loc , w') = atomicInit w
        (v , _) = atomicLoad loc w'
    in v ≡ Data.Integer.0ℤ

-- | Load after store returns stored value (same thread, no interleaving)
postulate
  atomic-load-store : ∀ loc v w →
    let w' = atomicStore loc v w
        (v' , _) = atomicLoad loc w'
    in v' ≡ v

-- | CAS success case
postulate
  atomic-cas-success : ∀ loc expected new w →
    let (old , _) = atomicLoad loc w
    in old ≡ expected →
    let (old' , w') = atomicCAS loc expected new w
        (v , _) = atomicLoad loc w'
    in old' ≡ expected × v ≡ new

-- | CAS failure case
postulate
  atomic-cas-failure : ∀ loc expected new w →
    let (old , _) = atomicLoad loc w
    in old ≢ expected →
    let (old' , w') = atomicCAS loc expected new w
        (v , _) = atomicLoad loc w'
    in old' ≡ old × v ≡ old

-- | Fetch-add semantics
postulate
  atomic-fetch-add-correct : ∀ loc delta w →
    let (old , _) = atomicLoad loc w
        (old' , w') = atomicFetchAdd loc delta w
        (new , _) = atomicLoad loc w'
    in old' ≡ old × new ≡ (old Data.Integer.+ delta)

------------------------------------------------------------------------
-- Memory Barriers
------------------------------------------------------------------------

-- | Full memory barrier
--
-- Ensures all memory operations before the barrier are visible
-- to other threads before any operations after the barrier.
postulate
  memoryBarrier : CWorld → CWorld

-- | Memory barrier is identity on sequential reasoning
-- (Its effect is only observable in concurrent interleavings)
postulate
  barrier-sequential : ∀ w →
    memoryBarrier (memoryBarrier w) ≡ memoryBarrier w

------------------------------------------------------------------------
-- Sequential Consistency Model
------------------------------------------------------------------------

-- | Under sequential consistency, there exists a total order of all
-- operations across all threads such that:
--   1. Operations within each thread appear in program order
--   2. Each read sees the value of the most recent write in the total order
--
-- We don't formalize this directly, but the axioms above are consistent
-- with sequential consistency.

------------------------------------------------------------------------
-- Summary of Trusted Axioms
------------------------------------------------------------------------

-- This module introduces the following postulates:
--
-- Types:
--   ThreadId, ThreadHandle, Mutex, CondVar, AtomicLoc, CWorld
--
-- Threads:
--   spawn, join, detach, getCurrentThread
--
-- Mutexes:
--   mutexInit, mutexLock, mutexUnlock, mutexTryLock,
--   isLocked, lockOwner,
--   mutex-init-unlocked, mutex-lock-locks, mutex-unlock-unlocks
--
-- Condition Variables:
--   condInit, condWait, condSignal, condBroadcast,
--   cond-wait-reacquires
--
-- Atomics:
--   atomicInit, atomicLoad, atomicStore, atomicCAS, atomicFetchAdd,
--   atomic-init-zero, atomic-load-store,
--   atomic-cas-success, atomic-cas-failure, atomic-fetch-add-correct
--
-- Barriers:
--   memoryBarrier, barrier-sequential
--
-- These axioms are validated by the implementations in
-- Strata/Interpretations/Linux/Thread.*.
--

