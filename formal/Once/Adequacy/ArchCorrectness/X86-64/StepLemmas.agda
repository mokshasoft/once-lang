-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas
--
-- Plan 0.27 (C3): a thin SEMANTIC API over the X86-64 CPU model, so loop
-- proofs reason by COMPOSING per-step lemmas instead of normalising `exec`
-- and `rewrite`-ing equalities into its half-reduced guts. The latter
-- (raw-reduction altitude) is what produced the recurring `with`-aux and
-- `cannot split on non-datatype Memory` friction: generalising a memory
-- read inside `exec`'s reduction forces a higher-order split of the
-- function-typed `Memory`. Here:
--
--   * the memory algebra (read-own-write / read-other-write + address
--     disjointness) characterises reads WITHOUT unfolding writeMem chains;
--   * `exec-1` peels one step, rewriting only `halted` (Bool) and the step
--     result (Maybe State) — never a memory application — so it is immune
--     to the split-mem problem;
--   * per-instruction step-lemmas characterise `step-not-halted` for the
--     shapes that read (mov-from-mem) or branch (je/jne); read-free
--     instructions need no lemma (their step is `refl`).
--
-- Loop proofs then chain `exec-1`s, letting Agda INFER the intermediate
-- states from each `step-not-halted ≡ just s'` equation.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-64.StepLemmas where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.CCC.Label using (thunk)
open import Once.CCC.Target.X86-64.Syntax
open import Once.CCC.Target.X86-64.Semantics

open State using (regs; memory; flags; pc; halted)
open Flags using (zf)

------------------------------------------------------------------------
-- Memory algebra
------------------------------------------------------------------------

≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

-- An address never equals itself plus a positive offset.
self≢plus : ∀ n k → (n ≡ᵇ (n + suc k)) ≡ false
self≢plus zero    k = refl
self≢plus (suc n) k = self≢plus n k

-- Offsets off a common base compare by their offsets.
+-cancelᵇ : ∀ p a b → ((p + a) ≡ᵇ (p + b)) ≡ (a ≡ᵇ b)
+-cancelᵇ zero    a b = refl
+-cancelᵇ (suc p) a b = +-cancelᵇ p a b

-- read-own-write
read-write-same : ∀ m a v → readMem (writeMem m a v) a ≡ just v
read-write-same m a v rewrite ≡ᵇ-refl a = refl

-- read-other-write (addresses provably distinct)
read-write-diff : ∀ m a b v → (a ≡ᵇ b) ≡ false
                → readMem (writeMem m b v) a ≡ readMem m a
read-write-diff m a b v a≢b rewrite a≢b = refl

------------------------------------------------------------------------
-- exec-1 : one step of `exec`, driven by the step result.
--
-- Rewrites ONLY `halted s` (Bool) and `step-not-halted prog s` (Maybe
-- State) and `halted s'` (Bool). No memory application is generalised, so
-- the `cannot split mem` problem cannot arise.
------------------------------------------------------------------------
exec-1 : ∀ {prog n s s'}
       → halted s ≡ false
       → step-not-halted prog s ≡ just s'
       → halted s' ≡ false
       → exec (suc n) prog s ≡ exec n prog s'
exec-1 hs snh hs' rewrite hs | snh | hs' = refl

------------------------------------------------------------------------
-- Per-instruction step-lemmas.
--
-- CRUCIAL: these are stated over an OPAQUE state `s` (never destructuring
-- `Memory` into a clause pattern). Binding `mem : Memory` as a pattern and
-- proving by `refl`/`rewrite` makes Agda's coverage checker try to split
-- the function-typed `Memory` → `SplitError.NotADatatype`. Over opaque `s`
-- the reduction goes through. The fetched instruction is supplied as a
-- hypothesis (`refl` at concrete call sites); reads/flags/jump targets are
-- supplied likewise, characterised via the memory algebra above.
------------------------------------------------------------------------

-- label: pc advances, nothing else.
step-label : ∀ {prog s n}
           → fetch prog (pc s) ≡ just (label n)
           → step-not-halted prog s ≡ just (record s { pc = pc s + 1 })
step-label ft rewrite ft = refl

-- mov reg ← reg
step-mov-rr : ∀ {prog s r r'}
            → fetch prog (pc s) ≡ just (mov (reg r) (reg r'))
            → step-not-halted prog s
              ≡ just (record s { regs = writeReg (regs s) r (readReg (regs s) r')
                               ; pc = pc s + 1 })
step-mov-rr ft rewrite ft = refl

-- push reg: sp := rsp − 8 ; [sp] := reg ; pc += 1
step-push : ∀ {prog s r}
          → fetch prog (pc s) ≡ just (push (reg r))
          → step-not-halted prog s
            ≡ just (record s { regs   = writeReg (regs s) rsp (readReg (regs s) rsp ∸ slot-size)
                             ; memory = writeMem (memory s) (readReg (regs s) rsp ∸ slot-size) (readReg (regs s) r)
                             ; pc     = pc s + 1 })
step-push ft rewrite ft = refl

-- lea reg, mem: reg := effectiveAddr mem ; pc += 1.
--
-- D096 SPLIT THIS IN TWO. A `rip+label` operand no longer goes through
-- `effectiveAddr` — `execInstr` RESOLVES it against the program — so the
-- general form is stated for the addressing modes that do, and the code
-- address gets its own lemma below. Stating one lemma over an arbitrary `m`
-- would now be FALSE at `rip+label`, which is precisely the defect that was
-- being papered over.
step-lea : ∀ {prog s r b d}
         → fetch prog (pc s) ≡ just (lea r (base+disp b d))
         → step-not-halted prog s
           ≡ just (record s { regs = writeReg (regs s) r (effectiveAddr s (base+disp b d))
                            ; pc = pc s + 1 })
step-lea ft rewrite ft = refl

-- …and THE CODE ADDRESS (D096): `lea r, .L_thunk_ℓ(%rip)` puts the label's
-- INDEX in `r`, resolved exactly as `jmp` resolves a target. This is the lemma
-- that makes a code address a real address, which is what the closure call
-- needs before it can jump to one.
step-lea-label : ∀ {prog s r ℓ j}
               → fetch prog (pc s) ≡ just (lea r (rip+label ℓ))
               → find-label prog (thunk ℓ) ≡ just j
               → step-not-halted prog s
                 ≡ just (record s { regs = writeReg (regs s) r j ; pc = pc s + 1 })
step-lea-label ft fl rewrite ft | fl = refl

-- pop reg: reg := [rsp] ; rsp := rsp + 8 ; pc += 1  (needs [rsp] mapped)
step-pop : ∀ {prog s r v}
         → fetch prog (pc s) ≡ just (pop r)
         → readMem (memory s) (readReg (regs s) rsp) ≡ just v
         → step-not-halted prog s
           ≡ just (record s { regs = writeReg (writeReg (regs s) r v) rsp (readReg (regs s) rsp + slot-size)
                            ; pc   = pc s + 1 })
step-pop ft rd rewrite ft | rd = refl

-- mov reg ← imm
step-mov-ri : ∀ {prog s r n}
            → fetch prog (pc s) ≡ just (mov (reg r) (imm n))
            → step-not-halted prog s
              ≡ just (record s { regs = writeReg (regs s) r n ; pc = pc s + 1 })
step-mov-ri ft rewrite ft = refl

-- mov reg ← [mem]: needs the read value.
step-mov-rm : ∀ {prog s r m v}
            → fetch prog (pc s) ≡ just (mov (reg r) (mem m))
            → readMem (memory s) (effectiveAddr s m) ≡ just v
            → step-not-halted prog s
              ≡ just (record s { regs = writeReg (regs s) r v ; pc = pc s + 1 })
step-mov-rm ft rd rewrite ft | rd = refl

-- mov [mem] ← imm
step-mov-mi : ∀ {prog s m n}
            → fetch prog (pc s) ≡ just (mov (mem m) (imm n))
            → step-not-halted prog s
              ≡ just (record s { memory = writeMem (memory s) (effectiveAddr s m) n
                               ; pc = pc s + 1 })
step-mov-mi ft rewrite ft = refl

-- mov [mem] ← reg
step-mov-mr : ∀ {prog s m r}
            → fetch prog (pc s) ≡ just (mov (mem m) (reg r))
            → step-not-halted prog s
              ≡ just (record s { memory = writeMem (memory s) (effectiveAddr s m)
                                          (readReg (regs s) r)
                               ; pc = pc s + 1 })
step-mov-mr ft rewrite ft = refl

-- cmp reg, imm: sets flags.
step-cmp-ri : ∀ {prog s r n}
            → fetch prog (pc s) ≡ just (cmp (reg r) (imm n))
            → step-not-halted prog s
              ≡ just (record s { flags = mkflags (readReg (regs s) r ≡ᵇ n)
                                                 (readReg (regs s) r <ᵇ n) false
                               ; pc = pc s + 1 })
step-cmp-ri ft rewrite ft = refl

-- cmp [mem], imm (reads memory — needs the read value).
step-cmp-mi : ∀ {prog s m n v}
            → fetch prog (pc s) ≡ just (cmp (mem m) (imm n))
            → readMem (memory s) (effectiveAddr s m) ≡ just v
            → step-not-halted prog s
              ≡ just (record s { flags = mkflags (v ≡ᵇ n) (v <ᵇ n) false ; pc = pc s + 1 })
step-cmp-mi ft rd rewrite ft | rd = refl

-- THE CALL (D098): read the target through the closure register, push the
-- return address one slot down, and transfer control. A fetch and a READ, like
-- `step-mov-rm` — the read being the closure record's code cell.
step-call : ∀ {prog s m v}
          → fetch prog (pc s) ≡ just (call (mem m))
          → readMem (memory s) (effectiveAddr s m) ≡ just v
          → step-not-halted prog s
            ≡ just (record s { regs   = writeReg (regs s) rsp (readReg (regs s) rsp ∸ slot-size)
                             ; memory = writeMem (memory s) (readReg (regs s) rsp ∸ slot-size)
                                                 (pc s + 1)
                             ; pc     = v })
step-call ft rd rewrite ft | rd = refl

-- THE RETURN (D095): pop the address at `[%rsp]`, raise `%rsp` by a slot and
-- jump there. Same shape as `step-mov-rm` — a fetch and a READ — which is why
-- the correspondence needs the pending-return component before it can use
-- this: the read is exactly the cell `RetAddrs` describes.
step-ret : ∀ {prog s v}
         → fetch prog (pc s) ≡ just ret
         → readMem (memory s) (readReg (regs s) rsp) ≡ just v
         → step-not-halted prog s
           ≡ just (record s { regs = writeReg (regs s) rsp (readReg (regs s) rsp + slot-size)
                            ; pc = v })
step-ret ft rd rewrite ft | rd = refl

-- add reg, imm
step-add-ri : ∀ {prog s r n}
            → fetch prog (pc s) ≡ just (add (reg r) (imm n))
            → step-not-halted prog s
              ≡ just (record s { regs = writeReg (regs s) r (readReg (regs s) r + n)
                               ; flags = updateFlags (readReg (regs s) r + n)
                                                     (readReg (regs s) r)
                               ; pc = pc s + 1 })
step-add-ri ft rewrite ft = refl

-- add reg, reg (the lea-indexed doublings: `add rcx, rcx`)
step-add-rr : ∀ {prog s r r'}
            → fetch prog (pc s) ≡ just (add (reg r) (reg r'))
            → step-not-halted prog s
              ≡ just (record s { regs = writeReg (regs s) r (readReg (regs s) r + readReg (regs s) r')
                               ; flags = updateFlags (readReg (regs s) r + readReg (regs s) r')
                                                     (readReg (regs s) r)
                               ; pc = pc s + 1 })
step-add-rr ft rewrite ft = refl

-- sub reg, imm
step-sub-ri : ∀ {prog s r n}
            → fetch prog (pc s) ≡ just (sub (reg r) (imm n))
            → step-not-halted prog s
              ≡ just (record s { regs = writeReg (regs s) r (readReg (regs s) r ∸ n)
                               ; flags = updateFlags (readReg (regs s) r ∸ n)
                                                     (readReg (regs s) r)
                               ; pc = pc s + 1 })
step-sub-ri ft rewrite ft = refl

-- jmp: jump to the resolved label.
step-jmp : ∀ {prog s n tgt}
         → fetch prog (pc s) ≡ just (jmp n)
         → find-label prog n ≡ just tgt
         → step-not-halted prog s ≡ just (record s { pc = tgt })
step-jmp ft fl rewrite ft | fl = refl

-- je taken / not taken (driven by zf).
step-je-taken : ∀ {prog s n tgt}
              → fetch prog (pc s) ≡ just (je n)
              → zf (flags s) ≡ true
              → find-label prog n ≡ just tgt
              → step-not-halted prog s ≡ just (record s { pc = tgt })
step-je-taken ft zf-eq fl rewrite ft | zf-eq | fl = refl

step-je-not : ∀ {prog s n}
            → fetch prog (pc s) ≡ just (je n)
            → zf (flags s) ≡ false
            → step-not-halted prog s ≡ just (record s { pc = pc s + 1 })
step-je-not ft zf-eq rewrite ft | zf-eq = refl

step-jne-taken : ∀ {prog s n tgt}
               → fetch prog (pc s) ≡ just (jne n)
               → zf (flags s) ≡ false
               → find-label prog n ≡ just tgt
               → step-not-halted prog s ≡ just (record s { pc = tgt })
step-jne-taken ft zf-eq fl rewrite ft | zf-eq | fl = refl

step-jne-not : ∀ {prog s n}
             → fetch prog (pc s) ≡ just (jne n)
             → zf (flags s) ≡ true
             → step-not-halted prog s ≡ just (record s { pc = pc s + 1 })
step-jne-not ft zf-eq rewrite ft | zf-eq = refl

------------------------------------------------------------------------
-- Chaining: a `Steps prog k s s'` is k consecutive non-halting steps.
-- Each link's post-state s' is FORCED by its `step-not-halted ≡ just s'`
-- equation, so the intermediate states are inferred from the step-lemmas;
-- only the phase's final state must be written. `exec-steps` discharges
-- the fuel split. (Build on `exec-1`; never touches a memory pattern.)
------------------------------------------------------------------------
infixr 5 _∷_
data Steps (prog : Program) : ℕ → State → State → Set where
  [] : ∀ {s} → Steps prog 0 s s
  _∷_ : ∀ {k s s' s''}
      → (halted s ≡ false × step-not-halted prog s ≡ just s' × halted s' ≡ false)
      → Steps prog k s' s''
      → Steps prog (suc k) s s''

exec-steps : ∀ {prog} {k} b {s s'} → Steps prog k s s' → exec (k + b) prog s ≡ exec b prog s'
exec-steps b []                       = refl
exec-steps b (_∷_ {k = k} (hs , snh , hs') rest) =
  trans (exec-1 {n = k + b} hs snh hs') (exec-steps b rest)
