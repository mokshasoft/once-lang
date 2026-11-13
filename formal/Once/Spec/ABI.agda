{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.ABI — THE LAYOUT OF A BASE VALUE AT THE BOUNDARY (plan 0.138 S1).
--
-- SPEC. What crosses a boundary — an Interpretation's operation called by Once
-- (FFI out), a library's export called by a client (FFI in) — is a value of a
-- BASE type, and this is the memory it occupies there: the layout of the C type
-- that represents it, under the target's standard procedure-call standard.
-- An Interpretation's author and a library's client rely on it, and it is all
-- they need to know of Once's values.
--
-- In WORDS of the target (`Spec.Numerics.int-bits`; 8 bytes on x86-64 and
-- riscv64, 4 on x86-32), in order of increasing address:
--
--   Int          one word: the value (`Spec.Domain`: an `Int` denotes a word);
--   Float        one word: the value's encoding in the target's format
--                (`Spec.Float.Encoding`; a `Float` denotes a level-2 value,
--                plan 0.150 N6, so its one NaN is the canonical pattern);
--   Unit         no words (a C struct omits it; an argument of type Unit is
--                not passed);
--   A * B        A's words, then B's (a flat C struct);
--   A + B        a tag word (0 for `inl`, 1 for `inr`), then the payload,
--                padded to the larger alternative (a tagged union); so
--                `Bool = Unit + Unit` is one word;
--   Void         no value exists.
--
-- Every scalar is one word on every target Once has, so a layout is a sequence
-- of words with no alignment gaps. The padding of a sum's shorter alternative
-- is UNSPECIFIED: any words; a reader must not look at it.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

-- At a signature only because the value domain is stated at one; a base
-- value's words do not depend on it.
module Once.Spec.ABI (Σ : Signature) where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤ᵇ_; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Type
  using (Type; Base; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; ∅ₖ)
open import Once.Spec.Word using (Carrier)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Float.Dyadic using (FloatFormat)
open import Once.Spec.Float.Encoding using (encode)

-- THE SIZE, in words: a base type's size is static.
words : ∀ {A : Type} → Base ∅ₖ A → ℕ
words (b-var {()} _)
words b-Unit    = 0
words b-Void    = 0
words b-Int     = 1
words b-Float   = 1
words (b-* a b) = words a + words b
words (b-+ a b) = suc (words a ⊔ words b)

-- THE LAYOUT: `Layout F b v ws` — the value `v` of the base type `b` occupies
-- the words `ws`, from its address up, at the target's float format `F`.
data Layout (F : FloatFormat) : ∀ {A : Type} (b : Base ∅ₖ A) → ⟦ A ⟧ᵛ → List Carrier → Set where
  l-unit  : Layout F b-Unit tt []
  l-int   : ∀ {v} → Layout F b-Int v (v ∷ [])
  l-float : ∀ {v} → Layout F b-Float v (encode F v ∷ [])
  l-pair  : ∀ {A B} {a : Base ∅ₖ A} {b : Base ∅ₖ B} {x y ws vs}
          → Layout F a x ws → Layout F b y vs → Layout F (b-* a b) (x , y) (ws ++ vs)
  -- a sum: the tag, the payload, then padding (any words) to the larger side
  l-inl   : ∀ {A B} {a : Base ∅ₖ A} {b : Base ∅ₖ B} {x ws pad}
          → Layout F a x ws → length (ws ++ pad) ≡ words a ⊔ words b
          → Layout F (b-+ a b) (inj₁ x) (0 ∷ ws ++ pad)
  l-inr   : ∀ {A B} {a : Base ∅ₖ A} {b : Base ∅ₖ B} {y vs pad}
          → Layout F b y vs → length (vs ++ pad) ≡ words a ⊔ words b
          → Layout F (b-+ a b) (inj₂ y) (1 ∷ vs ++ pad)

------------------------------------------------------------------------
-- PASSING (D382): how an argument and an answer of a base type cross a call —
-- exactly as C passes the struct above, under the target's procedure-call
-- standard. An operation takes one argument and gives one answer, so the
-- standard's rules reduce to: where each WORD of the layout goes.
------------------------------------------------------------------------

-- The three standards of Once's targets.
data PCS : Set where
  sysv-x86-64 lp64d-riscv64 sysv-i386 : PCS

-- A word's CLASS: an integer word (an `Int`, a tag) or a floating one.
data Class : Set where
  int-word float-word : Class

-- Two alternatives' words at one position: floating only if both are.
merge : Class → Class → Class
merge float-word float-word = float-word
merge float-word int-word   = int-word
merge int-word   _          = int-word

private
  -- merge position by position; where one side has no word (padding) the
  -- other side's class stands
  merges : List Class → List Class → List Class
  merges []       ds       = ds
  merges (c ∷ cs) []       = c ∷ cs
  merges (c ∷ cs) (d ∷ ds) = merge c d ∷ merges cs ds

-- The class of each word of the layout, in order.
classes : ∀ {A : Type} → Base ∅ₖ A → List Class
classes (b-var {()} _)
classes b-Unit    = []
classes b-Void    = []
classes b-Int     = int-word ∷ []
classes b-Float   = float-word ∷ []
classes (b-* a b) = classes a ++ classes b
classes (b-+ a b) = int-word ∷ merges (classes a) (classes b)

-- WHERE A WORD GOES.
--   ireg n  the n-th integer register of the sequence in question: for an
--           argument x86-64 rdi rsi rdx rcx r8 r9, riscv64 a0 … a7; for an
--           answer x86-64 rax rdx, riscv64 a0 a1, i386 eax;
--   freg n  the n-th floating register: argument x86-64 xmm0 …, riscv64
--           fa0 …; answer x86-64 xmm0 xmm1, riscv64 fa0 fa1, i386 st0;
--   mem n   the n-th word of the value in memory: an argument's on the stack
--           (x86-64, i386: the stack argument area at the call), or of the
--           copy whose address is passed (riscv64, a large argument); an
--           answer's in the caller's buffer.
data Loc : Set where
  ireg freg mem : ℕ → Loc

private
  -- registers by class, counting integer and floating ones apart, from the
  -- given first integer register
  by-class : List Class → ℕ → ℕ → List Loc
  by-class []                 i f = []
  by-class (int-word   ∷ cs) i f = ireg i ∷ by-class cs (suc i) f
  by-class (float-word ∷ cs) i f = freg f ∷ by-class cs i (suc f)

  in-memory : ℕ → ℕ → List Loc
  in-memory from zero    = []
  in-memory from (suc n) = mem from ∷ in-memory (suc from) n

  small? : ℕ → Bool
  small? n = n ≤ᵇ 2

  scalar? : ∀ {A : Type} → Base ∅ₖ A → Bool
  scalar? b-Int   = true
  scalar? b-Float = true
  {-# CATCHALL #-}
  scalar? _       = false

  -- riscv64's floating convention: the flattened fields are one `Float`, or two
  -- scalars at least one a `Float`; a struct holding a sum (a union) never is
  fields : ∀ {A : Type} → Base ∅ₖ A → Maybe (List Class)
  fields (b-var {()} _)
  fields b-Unit    = just []
  fields b-Void    = just []
  fields b-Int     = just (int-word ∷ [])
  fields b-Float   = just (float-word ∷ [])
  fields (b-* a b) = Data.Maybe.zipWith _++_ (fields a) (fields b)
  fields (b-+ _ _) = nothing

  any-float : List Class → Bool
  any-float []                 = false
  any-float (float-word ∷ _)   = true
  any-float (int-word   ∷ cs)  = any-float cs

  fp-eligible : ∀ {A : Type} → Base ∅ₖ A → Bool
  fp-eligible b with fields b
  ... | just cs = (length cs ≤ᵇ 2) ∧ any-float cs ∧ not (length cs ≡ᵇ 0)
  ... | nothing = false

-- THE ANSWER: in the return registers, or (`false`) in a buffer the caller
-- provides, whose address it passes as a hidden first argument (x86-64 rdi,
-- riscv64 a0, i386 the first stack word) and the callee returns (rax, a0, eax).
answer-in-registers : PCS → ∀ {A : Type} → Base ∅ₖ A → Bool
answer-in-registers sysv-x86-64   b = small? (words b)
answer-in-registers lp64d-riscv64 b = small? (words b)
answer-in-registers sysv-i386     b = scalar? b ∨ (words b ≡ᵇ 0)

-- …and where each of its words goes (a buffered answer's words: `mem`).
answer : PCS → ∀ {A : Type} → Base ∅ₖ A → List Loc
answer pcs b = if answer-in-registers pcs b then in-registers pcs else in-memory 0 (words b)
  where
    in-ireg : ℕ → ℕ → List Loc
    in-ireg zero    _ = []
    in-ireg (suc n) i = ireg i ∷ in-ireg n (suc i)
    in-registers : PCS → List Loc
    in-registers sysv-x86-64   = by-class (classes b) 0 0
    in-registers lp64d-riscv64 = if fp-eligible b then by-class (classes b) 0 0 else in-ireg (words b) 0
    in-registers sysv-i386     = by-class (classes b) 0 0

-- THE ARGUMENT, for an operation of codomain `B`: a buffered answer's hidden
-- address takes the first integer register (the first stack word on i386).
argument : PCS → ∀ {A B : Type} → Base ∅ₖ A → Base ∅ₖ B → List Loc
argument pcs a r = go pcs (if answer-in-registers pcs r then 0 else 1)
  where
    in-ireg : ℕ → ℕ → List Loc
    in-ireg zero    _ = []
    in-ireg (suc n) i = ireg i ∷ in-ireg n (suc i)
    go : PCS → ℕ → List Loc
    -- x86-64: up to two words in registers by class, more on the stack
    go sysv-x86-64   h = if small? (words a) then by-class (classes a) h 0 else in-memory 0 (words a)
    -- riscv64: the floating convention, else up to two words in integer
    -- registers, else by reference: the address of a copy in the next one
    go lp64d-riscv64 h =
      if fp-eligible a then by-class (classes a) h 0
      else if small? (words a) then in-ireg (words a) h
      else in-memory 0 (words a)
    -- i386: on the stack, after the hidden address if there is one
    go sysv-i386     h = in-memory h (words a)
