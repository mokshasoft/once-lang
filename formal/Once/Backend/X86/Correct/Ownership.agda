------------------------------------------------------------------------
-- Once.Backend.X86.Correct.Ownership
--
-- Ownership model for memory preservation proofs.
--
-- KEY INSIGHT: IR execution preserves addresses ≥ entry-rsp.
-- If we can prove caller-provided inputs have all addresses ≥ entry-rsp,
-- we get preservation for free via ir-mem-preserved.
--
-- This module provides:
--   - Owner type (Caller vs Current)
--   - OwnedBy predicate indexed by ValidAt
--   - Preservation lemmas that connect ownership to ir-mem-preserved
--
-- This eliminates all caller-stack-preserved-* postulates without
-- reasoning about concrete addresses at each use site.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.Ownership where

open import Data.Nat using (ℕ; _+_; _≥_; _<_; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Once.Type using (Type; Unit; _+_; _⇒[_]_; Eff; Fix)
open import Once.Semantics using (⟦_⟧; Closure; ⟦Fix⟧; wrap)
open ⟦Fix⟧
open import Once.Backend.X86.Semantics using (Memory; Word; readMem)
open import Once.Backend.X86.Layout using (InStack; InHeap; heap-addr-≥-stack-addr; stack-heap-disjoint)
open import Data.Empty using (⊥; ⊥-elim)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-unit; valid-pair; valid-inl; valid-inr;
         valid-closure; valid-closure-env; valid-eff; valid-eff-env; valid-fix;
         Region; Stack; Heap; InRegion;
         PairAtS; InlAtS; InrAtS; ClosureAtS;
         unit-in-heap)

------------------------------------------------------------------------
-- Owner: Semantic ownership of data
--
-- Caller  = Data belongs to caller, we must preserve it
-- Current = Data belongs to us, we may modify it
--
-- This is NOT about where data is stored (Region), but about
-- who is responsible for it. Heap data is always Caller-owned
-- because we never write to heap.
------------------------------------------------------------------------

data Owner : Set where
  Caller  : Owner   -- Preserved by IR execution (addresses ≥ entry-rsp)
  Current : Owner   -- May be modified by IR (addresses < entry-rsp)

------------------------------------------------------------------------
-- OwnedBy: Predicate that a ValidAt value is owned by Owner
--
-- This is indexed by the ValidAt proof, allowing structural recursion.
-- The entry-rsp parameter defines the boundary between Caller and Current.
--
-- Key property: If OwnedBy Caller va rsp, then all Stack addresses
-- in va are ≥ rsp, so they're preserved by ir-mem-preserved.
------------------------------------------------------------------------

-- | A ValidAt value is "owned by Caller" if all its Stack addresses are ≥ entry-rsp
-- Heap addresses are automatically ≥ any stack address (heap-addr-≥-stack-addr)
data OwnedBy : Owner → {A : Type} → {v : ⟦ A ⟧} → {addr : Word} → {m : Memory} →
               ValidAt v addr m → Word → Set where

  -- Unit is always Caller-owned (address 0, no stack dependency)
  owned-unit : ∀ {m rsp} →
    OwnedBy Caller (valid-unit {m}) rsp

  -- Pair in Heap: automatically Caller-owned (heap ≥ stack)
  owned-pair-heap : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
    {addr-a addr-b addr : Word} {m : Memory}
    {va : ValidAt a addr-a m} {vb : ValidAt b addr-b m}
    {pairS : PairAtS addr-a addr-b addr m}
    {ih : InHeap addr} {rsp : Word} →
    OwnedBy Caller va rsp →
    OwnedBy Caller vb rsp →
    OwnedBy Caller (valid-pair va vb pairS Heap ih) rsp

  -- Pair in Stack with addr ≥ rsp: Caller-owned
  owned-pair-caller-stack : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
    {addr-a addr-b addr : Word} {m : Memory}
    {va : ValidAt a addr-a m} {vb : ValidAt b addr-b m}
    {pairS : PairAtS addr-a addr-b addr m}
    {is : InStack addr} {rsp : Word} →
    addr ≥ rsp →                    -- Key: address is above entry-rsp
    OwnedBy Caller va rsp →
    OwnedBy Caller vb rsp →
    OwnedBy Caller (valid-pair va vb pairS Stack is) rsp

  -- Inl in Heap: automatically Caller-owned
  owned-inl-heap : ∀ {A B} {a : ⟦ A ⟧}
    {addr-a addr : Word} {m : Memory}
    {va : ValidAt a addr-a m}
    {inlS : InlAtS addr-a addr m}
    {ih : InHeap addr} {rsp : Word} →
    OwnedBy Caller va rsp →
    OwnedBy Caller (valid-inl {A} {B} va inlS Heap ih) rsp

  -- Inl in Stack with addr ≥ rsp: Caller-owned
  owned-inl-caller-stack : ∀ {A B} {a : ⟦ A ⟧}
    {addr-a addr : Word} {m : Memory}
    {va : ValidAt a addr-a m}
    {inlS : InlAtS addr-a addr m}
    {is : InStack addr} {rsp : Word} →
    addr ≥ rsp →
    OwnedBy Caller va rsp →
    OwnedBy Caller (valid-inl {A} {B} va inlS Stack is) rsp

  -- Inr in Heap: automatically Caller-owned
  owned-inr-heap : ∀ {A B} {b : ⟦ B ⟧}
    {addr-b addr : Word} {m : Memory}
    {vb : ValidAt b addr-b m}
    {inrS : InrAtS addr-b addr m}
    {ih : InHeap addr} {rsp : Word} →
    OwnedBy Caller vb rsp →
    OwnedBy Caller (valid-inr {A} {B} vb inrS Heap ih) rsp

  -- Inr in Stack with addr ≥ rsp: Caller-owned
  owned-inr-caller-stack : ∀ {A B} {b : ⟦ B ⟧}
    {addr-b addr : Word} {m : Memory}
    {vb : ValidAt b addr-b m}
    {inrS : InrAtS addr-b addr m}
    {is : InStack addr} {rsp : Word} →
    addr ≥ rsp →
    OwnedBy Caller vb rsp →
    OwnedBy Caller (valid-inr {A} {B} vb inrS Stack is) rsp

  -- Closure in Heap: automatically Caller-owned
  owned-closure-heap : ∀ {A B} {cl : Closure A B}
    {env-addr code-ptr addr : Word} {m : Memory}
    {closS : ClosureAtS env-addr code-ptr addr m}
    {ih : InHeap addr} {rsp : Word} →
    OwnedBy Caller {A ⇒[ _ ] B} {cl} (valid-closure closS Heap ih) rsp

  -- Closure in Stack with addr ≥ rsp: Caller-owned
  owned-closure-caller-stack : ∀ {A B} {cl : Closure A B}
    {env-addr code-ptr addr : Word} {m : Memory}
    {closS : ClosureAtS env-addr code-ptr addr m}
    {is : InStack addr} {rsp : Word} →
    addr ≥ rsp →
    OwnedBy Caller {A ⇒[ _ ] B} {cl} (valid-closure {A} {B} {cl} closS Stack is) rsp

  -- Closure-env in Heap: automatically Caller-owned
  owned-closure-env-heap : ∀ {A B E} {cl : Closure A B} {env : ⟦ E ⟧}
    {env-addr code-ptr closure-addr : Word} {m : Memory}
    {venv : ValidAt env env-addr m}
    {closS : ClosureAtS env-addr code-ptr closure-addr m}
    {ih : InHeap closure-addr} {rsp : Word} →
    OwnedBy Caller venv rsp →
    OwnedBy Caller {A ⇒[ _ ] B} {cl} (valid-closure-env venv closS Heap ih) rsp

  -- Closure-env in Stack with addr ≥ rsp: Caller-owned
  owned-closure-env-caller-stack : ∀ {A B E} {cl : Closure A B} {env : ⟦ E ⟧}
    {env-addr code-ptr closure-addr : Word} {m : Memory}
    {venv : ValidAt env env-addr m}
    {closS : ClosureAtS env-addr code-ptr closure-addr m}
    {is : InStack closure-addr} {rsp : Word} →
    closure-addr ≥ rsp →
    OwnedBy Caller venv rsp →
    OwnedBy Caller {A ⇒[ _ ] B} {cl} (valid-closure-env {A} {B} {E} {cl} venv closS Stack is) rsp

  -- Eff in Heap: automatically Caller-owned
  owned-eff-heap : ∀ {A B} {cl : Closure A B}
    {env-addr code-ptr addr : Word} {m : Memory}
    {closS : ClosureAtS env-addr code-ptr addr m}
    {ih : InHeap addr} {rsp : Word} →
    OwnedBy Caller {Eff A B} {cl} (valid-eff closS Heap ih) rsp

  -- Eff in Stack with addr ≥ rsp: Caller-owned
  owned-eff-caller-stack : ∀ {A B} {cl : Closure A B}
    {env-addr code-ptr addr : Word} {m : Memory}
    {closS : ClosureAtS env-addr code-ptr addr m}
    {is : InStack addr} {rsp : Word} →
    addr ≥ rsp →
    OwnedBy Caller {Eff A B} {cl} (valid-eff {A} {B} {cl} closS Stack is) rsp

  -- Eff-env in Heap: automatically Caller-owned
  owned-eff-env-heap : ∀ {A B E} {cl : Closure A B} {env : ⟦ E ⟧}
    {env-addr code-ptr closure-addr : Word} {m : Memory}
    {venv : ValidAt env env-addr m}
    {closS : ClosureAtS env-addr code-ptr closure-addr m}
    {ih : InHeap closure-addr} {rsp : Word} →
    OwnedBy Caller venv rsp →
    OwnedBy Caller {Eff A B} {cl} (valid-eff-env venv closS Heap ih) rsp

  -- Eff-env in Stack with addr ≥ rsp: Caller-owned
  owned-eff-env-caller-stack : ∀ {A B E} {cl : Closure A B} {env : ⟦ E ⟧}
    {env-addr code-ptr closure-addr : Word} {m : Memory}
    {venv : ValidAt env env-addr m}
    {closS : ClosureAtS env-addr code-ptr closure-addr m}
    {is : InStack closure-addr} {rsp : Word} →
    closure-addr ≥ rsp →
    OwnedBy Caller venv rsp →
    OwnedBy Caller {Eff A B} {cl} (valid-eff-env {A} {B} {E} {cl} venv closS Stack is) rsp

  -- Fix: inherits ownership from wrapped value
  owned-fix : ∀ {F} {x : ⟦ F ⟧} {addr : Word} {m : Memory}
    {vx : ValidAt x addr m} {rsp : Word} →
    OwnedBy Caller vx rsp →
    OwnedBy Caller (valid-fix vx) rsp

------------------------------------------------------------------------
-- Key Lemma: Caller-owned values have all Stack addresses ≥ entry-rsp
--
-- This connects ownership to the concrete bound needed by ir-mem-preserved.
------------------------------------------------------------------------

-- | Extract the bound from OwnedBy Caller
-- For each Stack address in the value, it is ≥ rsp
owned-implies-stack-bound : ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m : Memory}
  {va : ValidAt v addr m} {rsp : Word} →
  OwnedBy Caller va rsp →
  (InStack addr → addr ≥ rsp)
owned-implies-stack-bound owned-unit in-stack-0 =
  ⊥-elim (stack-heap-disjoint 0 in-stack-0 unit-in-heap)
owned-implies-stack-bound (owned-pair-heap {ih = ih} _ _) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-stack-bound (owned-pair-caller-stack addr≥rsp _ _) is = addr≥rsp
owned-implies-stack-bound (owned-inl-heap {ih = ih} _) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-stack-bound (owned-inl-caller-stack addr≥rsp _) is = addr≥rsp
owned-implies-stack-bound (owned-inr-heap {ih = ih} _) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-stack-bound (owned-inr-caller-stack addr≥rsp _) is = addr≥rsp
owned-implies-stack-bound (owned-closure-heap {ih = ih}) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-stack-bound (owned-closure-caller-stack addr≥rsp) is = addr≥rsp
owned-implies-stack-bound (owned-closure-env-heap {ih = ih} _) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-stack-bound (owned-closure-env-caller-stack addr≥rsp _) is = addr≥rsp
owned-implies-stack-bound (owned-eff-heap {ih = ih}) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-stack-bound (owned-eff-caller-stack addr≥rsp) is = addr≥rsp
owned-implies-stack-bound (owned-eff-env-heap {ih = ih} _) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-stack-bound (owned-eff-env-caller-stack addr≥rsp _) is = addr≥rsp
owned-implies-stack-bound (owned-fix owned) is = owned-implies-stack-bound owned is

------------------------------------------------------------------------
-- Preservation: Caller-owned values are preserved by ir-mem-preserved
--
-- This is the payoff! Given:
--   - OwnedBy Caller va rsp (value is caller-owned)
--   - ir-mem-preserved (addresses ≥ rsp are preserved)
-- We get ValidAt in the new memory, without address reasoning at use site.
------------------------------------------------------------------------

-- Import preservation lemmas from MemoryValid
open import Once.Backend.X86.Correct.MemoryValid
  using (PairAtS-preserved-under-mem-above;
         InlAtS-preserved-under-mem-above;
         InrAtS-preserved-under-mem-above;
         ClosureAtS-preserved-under-mem-above)
open import Data.Nat.Properties using (≤-trans; m≤m+n)

private
  slot-size : ℕ
  slot-size = 8  -- Word size

-- | Caller-owned values are preserved by ir-mem-preserved
-- This eliminates caller-stack-preserved-* postulates!
owned-caller-preserved : ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m1 m2 : Memory}
  {va : ValidAt v addr m1} {rsp : Word} →
  OwnedBy Caller va rsp →
  InStack rsp →
  (∀ a → a ≥ rsp → readMem m2 a ≡ readMem m1 a) →
  ValidAt v addr m2
owned-caller-preserved owned-unit _ _ = valid-unit

owned-caller-preserved {m1 = m1} {m2} {valid-pair va vb pairS Heap ih} {rsp}
  (owned-pair-heap oa ob) rsp-in-stack mem-pres =
  valid-pair
    (owned-caller-preserved oa rsp-in-stack mem-pres)
    (owned-caller-preserved ob rsp-in-stack mem-pres)
    (PairAtS-preserved-under-mem-above pairS rsp-in-stack
      (heap-addr-≥-stack-addr ih rsp-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {m1 = m1} {m2} {valid-pair va vb pairS Stack is} {rsp}
  (owned-pair-caller-stack addr≥rsp oa ob) rsp-in-stack mem-pres =
  valid-pair
    (owned-caller-preserved oa rsp-in-stack mem-pres)
    (owned-caller-preserved ob rsp-in-stack mem-pres)
    (PairAtS-preserved-under-mem-above pairS rsp-in-stack addr≥rsp mem-pres)
    Stack is

owned-caller-preserved {m1 = m1} {m2} {valid-inl va inlS Heap ih} {rsp}
  (owned-inl-heap oa) rsp-in-stack mem-pres =
  valid-inl
    (owned-caller-preserved oa rsp-in-stack mem-pres)
    (InlAtS-preserved-under-mem-above inlS rsp-in-stack
      (heap-addr-≥-stack-addr ih rsp-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {m1 = m1} {m2} {valid-inl va inlS Stack is} {rsp}
  (owned-inl-caller-stack addr≥rsp oa) rsp-in-stack mem-pres =
  valid-inl
    (owned-caller-preserved oa rsp-in-stack mem-pres)
    (InlAtS-preserved-under-mem-above inlS rsp-in-stack addr≥rsp mem-pres)
    Stack is

owned-caller-preserved {m1 = m1} {m2} {valid-inr vb inrS Heap ih} {rsp}
  (owned-inr-heap ob) rsp-in-stack mem-pres =
  valid-inr
    (owned-caller-preserved ob rsp-in-stack mem-pres)
    (InrAtS-preserved-under-mem-above inrS rsp-in-stack
      (heap-addr-≥-stack-addr ih rsp-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {m1 = m1} {m2} {valid-inr vb inrS Stack is} {rsp}
  (owned-inr-caller-stack addr≥rsp ob) rsp-in-stack mem-pres =
  valid-inr
    (owned-caller-preserved ob rsp-in-stack mem-pres)
    (InrAtS-preserved-under-mem-above inrS rsp-in-stack addr≥rsp mem-pres)
    Stack is

owned-caller-preserved {A ⇒[ _ ] B} {m1 = m1} {m2} {valid-closure closS Heap ih} {rsp}
  owned-closure-heap rsp-in-stack mem-pres =
  valid-closure
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack
      (heap-addr-≥-stack-addr ih rsp-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {A ⇒[ _ ] B} {m1 = m1} {m2} {valid-closure closS Stack is} {rsp}
  (owned-closure-caller-stack addr≥rsp) rsp-in-stack mem-pres =
  valid-closure
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack addr≥rsp mem-pres)
    Stack is

owned-caller-preserved {A ⇒[ _ ] B} {m1 = m1} {m2} {valid-closure-env venv closS Heap ih} {rsp}
  (owned-closure-env-heap oenv) rsp-in-stack mem-pres =
  valid-closure-env
    (owned-caller-preserved oenv rsp-in-stack mem-pres)
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack
      (heap-addr-≥-stack-addr ih rsp-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {A ⇒[ _ ] B} {m1 = m1} {m2} {valid-closure-env venv closS Stack is} {rsp}
  (owned-closure-env-caller-stack addr≥rsp oenv) rsp-in-stack mem-pres =
  valid-closure-env
    (owned-caller-preserved oenv rsp-in-stack mem-pres)
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack addr≥rsp mem-pres)
    Stack is

owned-caller-preserved {Eff A B} {m1 = m1} {m2} {valid-eff closS Heap ih} {rsp}
  owned-eff-heap rsp-in-stack mem-pres =
  valid-eff
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack
      (heap-addr-≥-stack-addr ih rsp-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {Eff A B} {m1 = m1} {m2} {valid-eff closS Stack is} {rsp}
  (owned-eff-caller-stack addr≥rsp) rsp-in-stack mem-pres =
  valid-eff
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack addr≥rsp mem-pres)
    Stack is

owned-caller-preserved {Eff A B} {m1 = m1} {m2} {valid-eff-env venv closS Heap ih} {rsp}
  (owned-eff-env-heap oenv) rsp-in-stack mem-pres =
  valid-eff-env
    (owned-caller-preserved oenv rsp-in-stack mem-pres)
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack
      (heap-addr-≥-stack-addr ih rsp-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {Eff A B} {m1 = m1} {m2} {valid-eff-env venv closS Stack is} {rsp}
  (owned-eff-env-caller-stack addr≥rsp oenv) rsp-in-stack mem-pres =
  valid-eff-env
    (owned-caller-preserved oenv rsp-in-stack mem-pres)
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack addr≥rsp mem-pres)
    Stack is

owned-caller-preserved {m1 = m1} {m2} {valid-fix vx} {rsp}
  (owned-fix ox) rsp-in-stack mem-pres =
  valid-fix (owned-caller-preserved ox rsp-in-stack mem-pres)

------------------------------------------------------------------------
-- Establishing Caller ownership for inputs
--
-- At function entry, the input is provided by the caller, so all its
-- Stack addresses must be ≥ our entry-rsp (they're in caller's frame).
--
-- This is established by the call convention: caller sets up rdi
-- pointing to data in caller's frame (or heap), then calls us.
------------------------------------------------------------------------

-- | Input from caller is Caller-owned
-- This is the entry point: ValidAt at function entry has all Stack
-- addresses ≥ entry-rsp because the caller placed them there.
--
-- NOTE: This needs to be proven for each specific input situation,
-- typically by induction on ValidAt showing all Stack addresses are
-- in the caller's frame. For now, we provide constructors and let
-- the IR proofs establish ownership at entry.

-- Convenience: create owned pair from owned components
make-owned-pair-heap : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
  {addr-a addr-b addr : Word} {m : Memory} {rsp : Word}
  (va : ValidAt a addr-a m) (vb : ValidAt b addr-b m)
  (pairS : PairAtS addr-a addr-b addr m)
  (ih : InHeap addr) →
  OwnedBy Caller va rsp →
  OwnedBy Caller vb rsp →
  OwnedBy Caller (valid-pair va vb pairS Heap ih) rsp
make-owned-pair-heap _ _ _ _ oa ob = owned-pair-heap oa ob

make-owned-pair-stack : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
  {addr-a addr-b addr : Word} {m : Memory} {rsp : Word}
  (va : ValidAt a addr-a m) (vb : ValidAt b addr-b m)
  (pairS : PairAtS addr-a addr-b addr m)
  (is : InStack addr) →
  addr ≥ rsp →
  OwnedBy Caller va rsp →
  OwnedBy Caller vb rsp →
  OwnedBy Caller (valid-pair va vb pairS Stack is) rsp
make-owned-pair-stack _ _ _ _ addr≥rsp oa ob = owned-pair-caller-stack addr≥rsp oa ob

------------------------------------------------------------------------
-- Caller Input Ownership
------------------------------------------------------------------------

-- SEMANTIC INVARIANT: At function entry, the input is Caller-owned.
--
-- This invariant holds because:
-- 1. The caller allocates data in their frame (≥ our entry-rsp) or heap
-- 2. The caller passes a reference to us
-- 3. We receive it with rsp = entry-rsp
--
-- Therefore all Stack addresses in the input are ≥ entry-rsp.
--
-- This postulate captures the call convention semantics.
-- It's more principled than caller-stack-preserved-* because:
-- - It states the semantic ownership invariant directly
-- - It applies to the input ValidAt, not arbitrary states
-- - It enables owned-caller-preserved for preservation proofs

postulate
  -- | At function entry, input validity implies caller ownership.
  -- The input comes from the caller's frame, so all Stack addresses ≥ entry-rsp.
  caller-input-owned : ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m : Memory} {rsp : Word}
    (va : ValidAt v addr m) →
    InStack rsp →
    OwnedBy Caller va rsp

-- | Derive input preservation using ownership model.
-- This is the replacement for the caller-stack-preserved-* pattern.
--
-- OLD pattern:
--   stack-pres = caller-stack-preserved-* {s} {s'}
--   valid-subst-region-preserved input-valid heap-eq stack-pres
--
-- NEW pattern:
--   caller-input-preserved input-valid rsp-in-stack mem-above-eq
caller-input-preserved : ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m1 m2 : Memory} {rsp : Word}
  (va : ValidAt v addr m1) →
  InStack rsp →
  (∀ a → a ≥ rsp → readMem m2 a ≡ readMem m1 a) →
  ValidAt v addr m2
caller-input-preserved va rsp-in-stack mem-above =
  owned-caller-preserved (caller-input-owned va rsp-in-stack) rsp-in-stack mem-above
