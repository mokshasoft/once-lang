-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas
--
-- Plan 0.66 X2: x86-32's thin SEMANTIC API over its CPU model — the same
-- module x86-64 and riscv64 carry, at this ISA.
--
-- Every lemma below is a PREMISE-FREE READOUT of one `execInstr` clause: a
-- fetch hypothesis (and, where the clause reads, a read hypothesis) in, the
-- post-state out, proved by `rewrite`. That discipline is not stylistic —
-- x86-64 measured a `norm`-premise formulation of `step-mov-ri` that DID NOT
-- TYPECHECK IN 900 s, because a `rewrite` by a modulus equation forces
-- reduction against `2 ^ 32` at every use. Consumers that know their immediate
-- fits convert with `W.norm-id`, where they have the facts to pay for it.
--
-- THREE PLACES x86-32 GENUINELY DIFFERS FROM x86-64, and they are the reason
-- this is written rather than copied:
--
--   1. `updateFlags` takes ONE argument (`Word → Flags`), not two. Plan 0.66
--      called this out in advance as the test of whether 0.65's core obeyed
--      its own rule — the core takes the branch OUTCOME in read-back form and
--      never mentions `Flags`. It does: nothing below is exported to it.
--   2. There is no `rip+label` operand. A code address is loaded by its own
--      instruction, `mov-code r ℓ`, which RESOLVES the label — so D096's split
--      lemma is a single clean readout here (`step-mov-code`), and `step-lea`
--      is stated for every addressing mode without exception.
--   3. `jmp` takes an OPERAND (a computed address); the label jump is
--      `jmp-l`. `step-jmp-l` is therefore the one the emitter's control flow
--      uses, and `step-jmp` is stated for completeness of the read.
--
-- `slot-size` is 4 here, but no lemma says 4: they say `slot-size`, which is
-- what makes the width axis a genuine variable rather than a coincidence.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-32.StepLemmas where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _<_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.CCC.Label using (thunk)
open import Once.CCC.Target.X86-32.Syntax
open import Once.CCC.Target.X86-32.Semantics

open State using (regs; memory; flags; pc; halted)
open Flags using (zf)

------------------------------------------------------------------------
-- Memory algebra
--
-- Characterises reads WITHOUT unfolding `writeMem` chains, which is what keeps
-- every proof below clear of the function-typed `Memory` (splitting on it is
-- `SplitError.NotADatatype`).
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
-- exec-1 : one step of `exec`, driven by the step result. Rewrites ONLY
-- `halted` (Bool) and `step-not-halted` (Maybe State) — never a memory
-- application, so the split-mem problem cannot arise.
------------------------------------------------------------------------
exec-1 : ∀ {prog n s s'}
       → halted s ≡ false
       → step-not-halted prog s ≡ just s'
       → halted s' ≡ false
       → exec (suc n) prog s ≡ exec n prog s'
exec-1 hs snh hs' rewrite hs | snh | hs' = refl

------------------------------------------------------------------------
-- Per-instruction step-lemmas, over an OPAQUE state `s`.
------------------------------------------------------------------------

-- label: pc advances, nothing else.
step-label : ∀ {prog s n}
           → fetch prog (pc s) ≡ just (label n)
           → step-not-halted prog s ≡ just (record s { pc = pc s + 1 })
step-label ft rewrite ft = refl

-- nop: the same shape, and the emitter does emit it.
step-nop : ∀ {prog s}
         → fetch prog (pc s) ≡ just nop
         → step-not-halted prog s ≡ just (record s { pc = pc s + 1 })
step-nop ft rewrite ft = refl

-- mov reg ← reg
step-mov-rr : ∀ {prog s r r'}
            → fetch prog (pc s) ≡ just (mov (reg r) (reg r'))
            → step-not-halted prog s
              ≡ just (record s { regs = writeReg (regs s) r (readReg (regs s) r')
                               ; pc = pc s + 1 })
step-mov-rr ft rewrite ft = refl

-- mov reg ← imm. THE LITERAL SEAM (plan 0.70 phase D): the machine NORMS an
-- immediate, because an instruction's immediate field is a machine word — 32
-- bits wide here — and a wider value has no encoding. Says exactly what
-- `execInstr` does and nothing more.
step-mov-ri : ∀ {prog s r n}
            → fetch prog (pc s) ≡ just (mov (reg r) (imm n))
            → step-not-halted prog s
              ≡ just (record s { regs = writeReg (regs s) r (W.norm n) ; pc = pc s + 1 })
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
              ≡ just (record s { memory = writeMem (memory s) (effectiveAddr s m) (W.norm n)
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

-- THE CODE ADDRESS (D096/D103 at this arch): `movl $.L_thunk_ℓ, r` puts the
-- label's INDEX in `r`, resolved exactly as a jump resolves a target. Until
-- 2026-08-13 this clause advanced the pc and left `r` UNTOUCHED, which is the
-- defect that made a code address not an address at all.
step-mov-code : ∀ {prog s r ℓ j}
              → fetch prog (pc s) ≡ just (mov-code r ℓ)
              → find-label prog (thunk ℓ) ≡ just j
              → step-not-halted prog s
                ≡ just (record s { regs = writeReg (regs s) r j ; pc = pc s + 1 })
step-mov-code ft fl rewrite ft | fl = refl

-- …and the MISS route: an unresolvable code label halts rather than stepping.
step-mov-code-miss : ∀ {prog s r ℓ}
                   → fetch prog (pc s) ≡ just (mov-code r ℓ)
                   → find-label prog (thunk ℓ) ≡ nothing
                   → step-not-halted prog s ≡ just (record s { halted = true })
step-mov-code-miss ft fl rewrite ft | fl = refl

-- lea reg, [mem]: reg := effectiveAddr mem. Stated for EVERY addressing mode —
-- x86-32 has no `rip+label`, so D096's exception does not arise here.
step-lea : ∀ {prog s r m}
         → fetch prog (pc s) ≡ just (lea r m)
         → step-not-halted prog s
           ≡ just (record s { regs = writeReg (regs s) r (effectiveAddr s m)
                            ; pc = pc s + 1 })
step-lea ft rewrite ft = refl

-- push reg: esp := esp − 4 ; [esp] := reg ; pc += 1
step-push : ∀ {prog s r}
          → fetch prog (pc s) ≡ just (push (reg r))
          → step-not-halted prog s
            ≡ just (record s { regs   = writeReg (regs s) esp (readReg (regs s) esp ∸ slot-size)
                             ; memory = writeMem (memory s) (readReg (regs s) esp ∸ slot-size)
                                                 (readReg (regs s) r)
                             ; pc     = pc s + 1 })
step-push ft rewrite ft = refl

-- pop reg: reg := [esp] ; esp := esp + 4 ; pc += 1  (needs [esp] mapped)
step-pop : ∀ {prog s r v}
         → fetch prog (pc s) ≡ just (pop r)
         → readMem (memory s) (readReg (regs s) esp) ≡ just v
         → step-not-halted prog s
           ≡ just (record s { regs = writeReg (writeReg (regs s) r v) esp
                                              (readReg (regs s) esp + slot-size)
                            ; pc   = pc s + 1 })
step-pop ft rd rewrite ft | rd = refl

-- add reg, imm. Plan 0.70 phase C: the machine adds MODULARLY at 32 bits, so
-- this says `⊕` and carries NO no-overflow premise (D054: wraparound is defined
-- semantics). A consumer needing plain `+` converts with `W.⊕≡+`, paying the
-- `< modulus` obligation as a LAYOUT bound of the HeapRoom/StackRoom family
-- (D087) — never as an assumption about what user values do.
step-add-ri : ∀ {prog s r n}
            → fetch prog (pc s) ≡ just (add (reg r) (imm n))
            → step-not-halted prog s
              ≡ just (record s { regs = writeReg (regs s) r (readReg (regs s) r W.⊕ W.norm n)
                               ; flags = updateFlags (readReg (regs s) r W.⊕ W.norm n)
                               ; pc = pc s + 1 })
step-add-ri ft rewrite ft = refl

-- add reg, reg (the `lea-indexed` doublings: `add eax, eax`)
step-add-rr : ∀ {prog s r r'}
            → fetch prog (pc s) ≡ just (add (reg r) (reg r'))
            → step-not-halted prog s
              ≡ just (record s { regs = writeReg (regs s) r (readReg (regs s) r W.⊕ readReg (regs s) r')
                               ; flags = updateFlags (readReg (regs s) r W.⊕ readReg (regs s) r')
                               ; pc = pc s + 1 })
step-add-rr ft rewrite ft = refl

-- sub reg, imm. Modular likewise (`⊖`); a consumer that knows the subtraction
-- does not borrow converts with `W.⊖≡∸`, which is exactly what the `fits`/`room`
-- premises beside every stack reservation supply.
step-sub-ri : ∀ {prog s r n}
            → fetch prog (pc s) ≡ just (sub (reg r) (imm n))
            → step-not-halted prog s
              ≡ just (record s { regs = writeReg (regs s) r (readReg (regs s) r W.⊖ W.norm n)
                               ; flags = updateFlags (readReg (regs s) r W.⊖ W.norm n)
                               ; pc = pc s + 1 })
step-sub-ri ft rewrite ft = refl

-- cmp reg, imm: sets flags, touches no register.
step-cmp-ri : ∀ {prog s r n}
            → fetch prog (pc s) ≡ just (cmp (reg r) (imm n))
            → step-not-halted prog s
              ≡ just (record s { pc = pc s + 1
                               ; flags = mkflags (readReg (regs s) r ≡ᵇ W.norm n)
                                                 (readReg (regs s) r <ᵇ W.norm n) false })
step-cmp-ri ft rewrite ft = refl

-- cmp [mem], imm (reads memory — needs the read value). This is the tag branch.
step-cmp-mi : ∀ {prog s m n v}
            → fetch prog (pc s) ≡ just (cmp (mem m) (imm n))
            → readMem (memory s) (effectiveAddr s m) ≡ just v
            → step-not-halted prog s
              ≡ just (record s { pc = pc s + 1
                               ; flags = mkflags (v ≡ᵇ W.norm n) (v <ᵇ W.norm n) false })
step-cmp-mi ft rd rewrite ft | rd = refl

-- THE CALL: read the target through the closure register, push the return
-- address one slot down, and transfer control. x86-32's call PUSHES, like
-- x86-64's — the return address does NOT live in a register, so none of
-- riscv64's four-layer spill machinery (D106) applies here.
step-call : ∀ {prog s m v}
          → fetch prog (pc s) ≡ just (call (mem m))
          → readMem (memory s) (effectiveAddr s m) ≡ just v
          → step-not-halted prog s
            ≡ just (record s { regs   = writeReg (regs s) esp (readReg (regs s) esp ∸ slot-size)
                             ; memory = writeMem (memory s) (readReg (regs s) esp ∸ slot-size)
                                                 (pc s + 1)
                             ; pc     = v })
step-call ft rd rewrite ft | rd = refl

-- A SIGOP CALL HALTS the modelled machine: `call-sym` is the boundary where an
-- external body runs, and the trace layer resumes past it.
step-call-sym : ∀ {prog s nm}
              → fetch prog (pc s) ≡ just (call-sym nm)
              → step-not-halted prog s ≡ just (record s { halted = true })
step-call-sym ft rewrite ft = refl

-- THE RETURN: pop the address at `[%esp]`, raise `%esp` by a slot, jump there.
-- The read is exactly the cell `RetAddrs` describes.
step-ret : ∀ {prog s v}
         → fetch prog (pc s) ≡ just ret
         → readMem (memory s) (readReg (regs s) esp) ≡ just v
         → step-not-halted prog s
           ≡ just (record s { regs = writeReg (regs s) esp (readReg (regs s) esp + slot-size)
                            ; pc = v })
step-ret ft rd rewrite ft | rd = refl

-- jmp-l: the LABEL jump the emitter uses for flat control (plan 0.63).
step-jmp-l : ∀ {prog s n tgt}
           → fetch prog (pc s) ≡ just (jmp-l n)
           → find-label prog n ≡ just tgt
           → step-not-halted prog s ≡ just (record s { pc = tgt })
step-jmp-l ft fl rewrite ft | fl = refl

step-jmp-l-miss : ∀ {prog s n}
                → fetch prog (pc s) ≡ just (jmp-l n)
                → find-label prog n ≡ nothing
                → step-not-halted prog s ≡ just (record s { halted = true })
step-jmp-l-miss ft fl rewrite ft | fl = refl

-- jmp through an OPERAND (a computed address). Not emitted by the CCC
-- lowering; stated so the ISA readout is complete.
step-jmp-i : ∀ {prog s n}
           → fetch prog (pc s) ≡ just (jmp (imm n))
           → step-not-halted prog s ≡ just (record s { pc = W.norm n })
step-jmp-i ft rewrite ft = refl

-- je taken / not taken (driven by zf), and the missing-label route.
step-je-taken : ∀ {prog s n tgt}
              → fetch prog (pc s) ≡ just (je n)
              → zf (flags s) ≡ true
              → find-label prog n ≡ just tgt
              → step-not-halted prog s ≡ just (record s { pc = tgt })
step-je-taken ft zf-eq fl rewrite ft | zf-eq | fl = refl

step-je-miss : ∀ {prog s n}
             → fetch prog (pc s) ≡ just (je n)
             → zf (flags s) ≡ true
             → find-label prog n ≡ nothing
             → step-not-halted prog s ≡ just (record s { halted = true })
step-je-miss ft zf-eq fl rewrite ft | zf-eq | fl = refl

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

-- ud2 traps: the emitter uses it for the unemittable structured nodes, so the
-- correspondence needs its halt route to be a readout like any other.
step-ud2 : ∀ {prog s}
         → fetch prog (pc s) ≡ just ud2
         → step-not-halted prog s ≡ just (record s { halted = true })
step-ud2 ft rewrite ft = refl

------------------------------------------------------------------------
-- Chaining: a `Steps prog k s s'` is k consecutive non-halting steps. Each
-- link's post-state is FORCED by its `step-not-halted ≡ just s'` equation, so
-- the intermediate states are inferred from the step-lemmas; only the phase's
-- final state must be written.
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
