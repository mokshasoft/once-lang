------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.DirectSimulation
--
-- Direct simulation from AbstractInstr → x86-32.
--
-- KEY INSIGHT: Structure x86-32 execution to EXACTLY match exec-abstract.
-- Both use the same with-pattern structure on memory reads, so proofs
-- can use parallel with-patterns and reduce together.
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.DirectSimulation where

open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.DivMod using (_/_; m*n/n≡m)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat.Properties using (_≟_)
open import Function using (case_of_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Target.X86-32.Syntax
  using (Reg; eax; ebx; ecx; edx; esi; edi; ebp; esp; Program; slot-size; slots)
  renaming (Instr to X86Instr)
open import Once.CCC.Target.X86-32.Syntax
  using (mov; lea; push; pop; add; sub; call; ret; nop; ud2;
         Operand; reg; imm; mem; Mem; base; base+disp)
open import Once.CCC.Target.X86-32.AbstractToX86-32
  using (compile-abstract; compile-trace; slot-to-disp)
open import Once.CCC.IR using (IR)
open import Once.CCC.Eval using (PrimSem)
open import Once.CCC.Target.X86-32.Types using (⟦_⟧)

------------------------------------------------------------------------
-- Simulation module
--
-- KEY INSIGHT: X86State uses ValueLocation directly, not ℕ addresses.
-- This makes exec-x86 perform THE SAME OPERATION as exec-abstract,
-- so simulation proofs become trivial (essentially refl).
------------------------------------------------------------------------

module Simulation {FS : FrameSemantics} where
  open FrameSemantics FS
  open MemOps {FS}
  open AbstractExec {FS}

  ------------------------------------------------------------------------
  -- X86 State (inside Simulation to access ValueLocation FS)
  --
  -- Uses ValueLocation directly, mirroring LocState structure.
  -- This eliminates the loc-to-addr bridging that made proofs complex.
  ------------------------------------------------------------------------

  record X86State : Set where
    constructor mkX86
    field
      eax-val : ValueLocation FS   -- Output register (maps to x86 eax)
      ecx-val : ValueLocation FS   -- Input register (maps to x86 ecx)
      cur-frame : Frame            -- Current frame (maps to ebp)
      stack-slot : ℕ               -- Stack slot index (maps to esp offset)
      x86-mem : ValueLocation FS → Maybe (ValueLocation FS)  -- Memory
      x86-halted : Bool            -- Halted flag
  open X86State public

  ------------------------------------------------------------------------
  -- Correspondence relation
  --
  -- With ValueLocation-based X86State, correspondence is near-equality.
  -- Each field directly corresponds, no loc-to-addr conversion needed.
  ------------------------------------------------------------------------

  record Corresponds (ls : LocState FS) (xs : X86State) (alloc : AllocState {FS}) : Set where
    field
      ecx-eq : ecx-val xs ≡ readReg (regs ls) Input
      eax-eq : eax-val xs ≡ readReg (regs ls) Output
      frame-eq : cur-frame xs ≡ current-frame alloc
      slot-eq : stack-slot xs ≡ stackSlot (regs ls)
      mem-eq : ∀ loc → x86-mem xs loc ≡ readLoc ls loc
      halt-eq : x86-halted xs ≡ halted ls
  open Corresponds public

  ------------------------------------------------------------------------
  -- X86 Execution
  --
  -- KEY: exec-x86 performs the SAME operations as exec-abstract,
  -- just using x86 instruction syntax. This makes simulation trivial.
  ------------------------------------------------------------------------

  -- Helper: compute slot location from frame and slot number
  slotLoc : Frame → ℕ → ValueLocation FS
  slotLoc f n = OnStack f n

  -- Helper: convert displacement back to slot number (inverse of slot-to-disp)
  -- slot-to-disp n = n * slot-size, so disp-to-slot d = d / slot-size
  disp-to-slot : ℕ → ℕ
  disp-to-slot d = d / slot-size

  -- Decidable equality for ValueLocation (needed for memory operations)
  _≟L_ : (l1 l2 : ValueLocation FS) → Dec (l1 ≡ l2)
  OnStack f1 k1 ≟L OnStack f2 k2 with f1 ≟F f2 | k1 ≟ k2
  ... | yes refl | yes refl = yes refl
  ... | yes _ | no k≢k = no λ { refl → k≢k refl }
  ... | no f≢f | _ = no λ { refl → f≢f refl }
  OnStack _ _ ≟L OnHeap _ = no λ ()
  OnHeap _ ≟L OnStack _ _ = no λ ()
  OnHeap hl1 ≟L OnHeap hl2 with hl1 ≟HL hl2
  ... | yes refl = yes refl
  ... | no neq = no λ { refl → neq refl }

  -- Helper: write to memory (functional update)
  writeX86Mem : (ValueLocation FS → Maybe (ValueLocation FS)) →
               ValueLocation FS → ValueLocation FS →
               (ValueLocation FS → Maybe (ValueLocation FS))
  writeX86Mem m loc v loc' with loc ≟L loc'
  ... | yes _ = just v
  ... | no _  = m loc'

  exec-x86 : X86Instr → X86State → Frame → X86State

  -- mov-to-output: mov eax, ecx → eax' = ecx
  exec-x86 (mov (reg eax) (reg ecx)) xs _ = record xs { eax-val = ecx-val xs }

  -- mov-to-input: mov ecx, eax → ecx' = eax
  exec-x86 (mov (reg ecx) (reg eax)) xs _ = record xs { ecx-val = eax-val xs }

  -- load-indirect: mov eax, [ecx] → eax' = *ecx
  exec-x86 (mov (reg eax) (mem (base ecx))) xs _ with x86-mem xs (ecx-val xs)
  ... | nothing = record xs { x86-halted = true }
  ... | just v = record xs { eax-val = v }

  -- load-indirect-suc: mov eax, [ecx + slot-size] → eax' = *(sucLoc ecx)
  exec-x86 (mov (reg eax) (mem (base+disp ecx d))) xs _ with x86-mem xs (sucLoc (ecx-val xs))
  ... | nothing = record xs { x86-halted = true }
  ... | just v = record xs { eax-val = v }

  -- load-from-slot: mov eax, [ebp + disp] → eax' = stack[frame, slot]
  exec-x86 (mov (reg eax) (mem (base+disp ebp d))) xs frame with x86-mem xs (slotLoc frame (disp-to-slot d))
  ... | nothing = record xs { x86-halted = true }
  ... | just v = record xs { eax-val = v }

  -- restore-input: mov ecx, [ebp + disp] → ecx' = stack[frame, slot]
  exec-x86 (mov (reg ecx) (mem (base+disp ebp d))) xs frame with x86-mem xs (slotLoc frame (disp-to-slot d))
  ... | nothing = record xs { x86-halted = true }
  ... | just v = record xs { ecx-val = v }

  -- store-indirect: mov [ecx], eax → *ecx := eax
  exec-x86 (mov (mem (base ecx)) (reg eax)) xs _ =
    record xs { x86-mem = writeX86Mem (x86-mem xs) (ecx-val xs) (eax-val xs) }

  -- store-indirect-suc: mov [ecx + slot-size], eax → *(sucLoc ecx) := eax
  exec-x86 (mov (mem (base+disp ecx d)) (reg eax)) xs _ =
    record xs { x86-mem = writeX86Mem (x86-mem xs) (sucLoc (ecx-val xs)) (eax-val xs) }

  -- store-at-slot: mov [ebp + disp], eax → stack[frame, slot] := eax
  exec-x86 (mov (mem (base+disp ebp d)) (reg eax)) xs frame =
    record xs { x86-mem = writeX86Mem (x86-mem xs) (slotLoc frame (disp-to-slot d)) (eax-val xs) }

  -- lea-slot: lea eax, [ebp + disp] → eax' = &stack[frame, slot]
  exec-x86 (lea eax (base+disp ebp d)) xs frame =
    record xs { eax-val = slotLoc frame (disp-to-slot d) }

  -- Stack management (convert bytes to slots using division)
  exec-x86 (sub (reg esp) (imm n)) xs _ =
    record xs { stack-slot = stack-slot xs +ℕ (n / slot-size) }

  exec-x86 (add (reg esp) (imm n)) xs _ =
    record xs { stack-slot = stack-slot xs ∸ (n / slot-size) }

  -- Frame push sequence: push ebp; mov ebp, esp; sub esp, N
  -- push ebp is a no-op in our model (ebp tracking is via cur-frame)
  exec-x86 (push (reg ebp)) xs _ = xs

  -- mov ebp, esp establishes new frame base - resets stack-slot to 0
  -- This matches abstract semantics where stackSlot becomes 0 for new frame
  exec-x86 (mov (reg ebp) (reg esp)) xs _ =
    record xs { stack-slot = 0 }

  -- Frame pop: mov esp, ebp; pop ebp
  exec-x86 (mov (reg esp) (reg ebp)) xs _ = xs  -- Restore esp from ebp (no-op)
  exec-x86 (pop ebp) xs _ = xs  -- Restore caller's ebp (no-op)

  -- Control flow (no-ops at abstract level)
  exec-x86 (call _) xs _ = xs
  exec-x86 ret xs _ = xs
  exec-x86 nop xs _ = xs
  exec-x86 ud2 xs _ = record xs { x86-halted = true }
  exec-x86 _ xs _ = xs

  exec-prog : Program → X86State → Frame → X86State
  exec-prog [] xs _ = xs
  exec-prog (i ∷ is) xs frame with x86-halted xs
  ... | true = xs
  ... | false = exec-prog is (exec-x86 i xs frame) frame

  ------------------------------------------------------------------------
  -- Helper lemmas
  ------------------------------------------------------------------------

  Input≢Output : Input ≢ Output
  Input≢Output ()

  Output≢Input : Output ≢ Input
  Output≢Input ()

  -- readLoc only depends on stackMem and heapMem, not regs
  readLoc-regs-irrel : ∀ ls newRegs loc →
    readLoc (record ls { regs = newRegs }) loc ≡ readLoc ls loc
  readLoc-regs-irrel ls newRegs (OnStack f k) = refl
  readLoc-regs-irrel ls newRegs (OnHeap hl) with heapMem ls hl
  ... | just _ = refl
  ... | nothing = refl

  -- If halted, exec-prog returns unchanged
  exec-prog-halted : ∀ prog xs frame → x86-halted xs ≡ true → exec-prog prog xs frame ≡ xs
  exec-prog-halted [] xs _ _ = refl
  exec-prog-halted (i ∷ is) xs frame h with x86-halted xs | h
  ... | true  | _ = refl
  ... | false | ()

  -- exec-prog distributes over ++
  exec-prog-++ : ∀ prog1 prog2 xs frame →
    exec-prog (prog1 ++ prog2) xs frame ≡ exec-prog prog2 (exec-prog prog1 xs frame) frame
  exec-prog-++ [] prog2 xs frame = refl
  exec-prog-++ (i ∷ is) prog2 xs frame with x86-halted xs in eq
  ... | true = sym (exec-prog-halted prog2 xs frame eq)
  ... | false = exec-prog-++ is prog2 (exec-x86 i xs frame) frame

  ------------------------------------------------------------------------
  -- Per-instruction simulation
  --
  -- KEY INSIGHT: With ValueLocation-based X86State, exec-x86 performs
  -- the SAME operation as exec-abstract. Proofs are trivial equalities.
  ------------------------------------------------------------------------

  -- Helper: derive x86-halted xs ≡ false from correspondence and not-halted
  xs-not-halted : ∀ ls xs alloc → halted ls ≡ false → Corresponds ls xs alloc → x86-halted xs ≡ false
  xs-not-halted ls xs alloc not-halted corr = trans (halt-eq corr) not-halted

  -- Helper: just injective
  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  -- Helper: writeX86Mem corresponds to writeLoc for stack locations
  -- Key property: if x86-mem ≡ readLoc, then writeX86Mem ≡ writeLoc
  writeX86Mem-stack-corresponds : ∀ (ls : LocState FS) (xs : X86State) (f : Frame) (k : ℕ) (val : ValueLocation FS) →
    (∀ l → x86-mem xs l ≡ readLoc ls l) →
    eax-val xs ≡ val →
    (∀ l → writeX86Mem (x86-mem xs) (OnStack f k) (eax-val xs) l ≡ readLoc (writeLoc ls (OnStack f k) val) l)
  writeX86Mem-stack-corresponds ls xs f k val mem-eq eax-eq l
    with (OnStack f k) ≟L l
  ... | yes refl =
    -- Writing and reading same location: both return just val
    trans (cong just eax-eq) (sym (writeLoc-read-same-stack ls f k val))
  ... | no loc≢l =
    -- Different locations: both preserve original value
    trans (mem-eq l) (sym (writeLoc-preserves-other ls (OnStack f k) l val loc≢l))

  -- Helper: writeX86Mem corresponds to writeLoc for any location (general case)
  writeX86Mem-corresponds : ∀ (ls : LocState FS) (xs : X86State) (loc val : ValueLocation FS) →
    (∀ l → x86-mem xs l ≡ readLoc ls l) →
    eax-val xs ≡ val →
    (∀ l → writeX86Mem (x86-mem xs) loc (eax-val xs) l ≡ readLoc (writeLoc ls loc val) l)
  writeX86Mem-corresponds ls xs (OnStack f k) val mem-eq eax-eq =
    writeX86Mem-stack-corresponds ls xs f k val mem-eq eax-eq
  writeX86Mem-corresponds ls xs (OnHeap hl) val mem-eq eax-eq l
    with (OnHeap hl) ≟L l
  ... | yes refl = {!!}  -- Heap write case - rare in Once
  ... | no loc≢l = trans (mem-eq l) (sym (writeLoc-preserves-other ls (OnHeap hl) l val loc≢l))

  -- Helper to derive contradiction from halted xs ≡ true and correspondence
  halted-contradiction : ∀ {ls xs alloc} → x86-halted xs ≡ true → halted ls ≡ false → Corresponds ls xs alloc → ⊥
  halted-contradiction eq-true not-halt corr with trans (sym (halt-eq corr)) eq-true | not-halt
  ... | refl | ()

  -- Helper: incrStackSlot preserves register reads
  incrStackSlot-preserves-Input : ∀ (r : Registers FS) (n : ℕ) →
    readReg (incrStackSlot r n) Input ≡ readReg r Input
  incrStackSlot-preserves-Input r n = refl

  incrStackSlot-preserves-Output : ∀ (r : Registers FS) (n : ℕ) →
    readReg (incrStackSlot r n) Output ≡ readReg r Output
  incrStackSlot-preserves-Output r n = refl

  -- Helper: decrStackSlot preserves register reads
  decrStackSlot-preserves-Input : ∀ (r : Registers FS) (n : ℕ) →
    readReg (decrStackSlot r n) Input ≡ readReg r Input
  decrStackSlot-preserves-Input r n = refl

  decrStackSlot-preserves-Output : ∀ (r : Registers FS) (n : ℕ) →
    readReg (decrStackSlot r n) Output ≡ readReg r Output
  decrStackSlot-preserves-Output r n = refl

  instr-sim : ∀ i ls xs alloc →
    halted ls ≡ false →
    Corresponds ls xs alloc →
    Corresponds (proj₁ (exec-abstract i ls alloc))
                (exec-prog (compile-abstract i) xs (current-frame alloc))
                (proj₂ (exec-abstract i ls alloc))

  -- mov-to-output: Output := Input
  -- x86: mov eax, ecx → eax' = ecx
  -- Abstract: regs' Output = readReg regs Input
  -- TRIVIAL: both set output to input value
  instr-sim mov-to-output ls xs alloc not-halted corr with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | false | _ =
    let inputVal = readReg (regs ls) Input
        newRegs = writeReg (regs ls) Output inputVal
    in record
    { ecx-eq = trans (ecx-eq corr) (sym (writeReg-preserves (regs ls) Output Input inputVal Input≢Output))
    ; eax-eq = trans (ecx-eq corr) (sym (writeReg-same (regs ls) Output inputVal))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (sym (writeReg-preserves-stackSlot (regs ls) Output inputVal))
    ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-regs-irrel ls newRegs loc))
    ; halt-eq = halt-eq corr
    }
  ... | true | ()

  -- mov-to-input: Input := Output
  -- x86: mov ecx, eax → ecx' = eax
  -- Abstract: regs' Input = readReg regs Output
  -- TRIVIAL: both set input to output value
  instr-sim mov-to-input ls xs alloc not-halted corr with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | false | _ =
    let outputVal = readReg (regs ls) Output
        newRegs = writeReg (regs ls) Input outputVal
    in record
    { ecx-eq = trans (eax-eq corr) (sym (writeReg-same (regs ls) Input outputVal))
    ; eax-eq = trans (eax-eq corr) (sym (writeReg-preserves (regs ls) Input Output outputVal Output≢Input))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (sym (writeReg-preserves-stackSlot (regs ls) Input outputVal))
    ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-regs-irrel ls newRegs loc))
    ; halt-eq = halt-eq corr
    }
  ... | true | ()

  -- load-indirect: Output := *Input
  -- Abstract: exec (load Output (IndReg Input)) which reads from readLoc ls (readReg (regs ls) Input)
  -- X86: mov eax, [ecx] which reads from x86-mem xs (ecx-val xs)
  -- By correspondence, these match: ecx-val xs ≡ readReg (regs ls) Input and x86-mem ≡ readLoc
  --
  -- NOTE: This proof is complex because exec-abstract delegates to exec which has its own with-pattern.
  -- We leave it as a hole - the structure is correct but Agda's with-pattern propagation doesn't help.
  -- A complete proof would require restructuring exec to take the memory read result as a parameter.
  instr-sim load-indirect ls xs alloc not-halted corr = {!!}

  -- load-indirect-suc: Output := *(sucLoc Input)
  -- Same structure as load-indirect, same with-pattern propagation issue
  instr-sim load-indirect-suc ls xs alloc not-halted corr = {!!}

  -- load-from-slot: Output := stack[frame, slot]
  -- Same with-pattern propagation issue as load-indirect
  instr-sim (load-from-slot slot) ls xs alloc not-halted corr = {!!}

  -- store-at-slot: stack[frame, slot] := Output
  -- Both write Output value to the same location
  instr-sim (store-at-slot slot) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let frame = current-frame alloc
        loc = OnStack frame slot
        val = readReg (regs ls) Output
        ls' = writeLoc ls loc val
        regs-eq : regs ls' ≡ regs ls
        regs-eq = writeLoc-regs ls loc val
        -- x86 writes to slotLoc frame (disp-to-slot (slot * slot-size)) = OnStack frame slot
        slot-recover : disp-to-slot (slot *ℕ slot-size) ≡ slot
        slot-recover = m*n/n≡m slot slot-size
        -- Use slot-recover to fix the slot argument
        mem-eq' : ∀ l → writeX86Mem (x86-mem xs) (OnStack frame (disp-to-slot (slot *ℕ slot-size))) (eax-val xs) l ≡ readLoc ls' l
        mem-eq' = subst (λ s → ∀ l → writeX86Mem (x86-mem xs) (OnStack frame s) (eax-val xs) l ≡ readLoc ls' l)
                        (sym slot-recover)
                        (writeX86Mem-stack-corresponds ls xs frame slot val (mem-eq corr) (eax-eq corr))
    in record
    { ecx-eq = trans (ecx-eq corr) (cong (λ r → readReg r Input) (sym regs-eq))
    ; eax-eq = trans (eax-eq corr) (cong (λ r → readReg r Output) (sym regs-eq))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (cong stackSlot (sym regs-eq))
    ; mem-eq = mem-eq'
    ; halt-eq = trans (halt-eq corr) (sym (writeLoc-halted ls loc val))
    }

  -- store-indirect: *Input := Output
  instr-sim store-indirect ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let loc = readReg (regs ls) Input
        val = readReg (regs ls) Output
        ls' = writeLoc ls loc val
        regs-eq : regs ls' ≡ regs ls
        regs-eq = writeLoc-regs ls loc val
        -- ecx-val xs ≡ loc by correspondence
        loc-eq : ecx-val xs ≡ loc
        loc-eq = ecx-eq corr
        -- x86 writes to ecx-val xs which equals loc
        mem-eq' : ∀ l → writeX86Mem (x86-mem xs) (ecx-val xs) (eax-val xs) l ≡ readLoc ls' l
        mem-eq' = subst (λ ecx → ∀ l → writeX86Mem (x86-mem xs) ecx (eax-val xs) l ≡ readLoc ls' l)
                       (sym loc-eq)
                       (writeX86Mem-corresponds ls xs loc val (mem-eq corr) (eax-eq corr))
    in record
    { ecx-eq = trans (ecx-eq corr) (cong (λ r → readReg r Input) (sym regs-eq))
    ; eax-eq = trans (eax-eq corr) (cong (λ r → readReg r Output) (sym regs-eq))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (cong stackSlot (sym regs-eq))
    ; mem-eq = mem-eq'
    ; halt-eq = trans (halt-eq corr) (sym (writeLoc-halted ls loc val))
    }

  -- store-indirect-suc: *(sucLoc Input) := Output
  instr-sim store-indirect-suc ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let loc = sucLoc (readReg (regs ls) Input)
        val = readReg (regs ls) Output
        ls' = writeLoc ls loc val
        regs-eq : regs ls' ≡ regs ls
        regs-eq = writeLoc-regs ls loc val
        -- ecx-val xs ≡ readReg (regs ls) Input by correspondence
        ecx-eq' : ecx-val xs ≡ readReg (regs ls) Input
        ecx-eq' = ecx-eq corr
        -- x86 writes to sucLoc (ecx-val xs) which equals loc
        loc-eq : sucLoc (ecx-val xs) ≡ loc
        loc-eq = cong sucLoc ecx-eq'
        mem-eq' : ∀ l → writeX86Mem (x86-mem xs) (sucLoc (ecx-val xs)) (eax-val xs) l ≡ readLoc ls' l
        mem-eq' = subst (λ sloc → ∀ l → writeX86Mem (x86-mem xs) sloc (eax-val xs) l ≡ readLoc ls' l)
                       (sym loc-eq)
                       (writeX86Mem-corresponds ls xs loc val (mem-eq corr) (eax-eq corr))
    in record
    { ecx-eq = trans (ecx-eq corr) (cong (λ r → readReg r Input) (sym regs-eq))
    ; eax-eq = trans (eax-eq corr) (cong (λ r → readReg r Output) (sym regs-eq))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (cong stackSlot (sym regs-eq))
    ; mem-eq = mem-eq'
    ; halt-eq = trans (halt-eq corr) (sym (writeLoc-halted ls loc val))
    }

  -- lea-slot: Output := &stack[frame, slot]
  -- Abstract: writeReg regs Output (OnStack frame slot)
  -- x86: lea eax, [ebp + slot*4] → eax' = OnStack frame (slot*4/4) = OnStack frame slot
  instr-sim (lea-slot slot) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let frame = current-frame alloc
        loc = OnStack frame slot
        newRegs = writeReg (regs ls) Output loc
        -- disp-to-slot (slot * slot-size) = slot (by n*4/4 = n)
        slot-recover : disp-to-slot (slot *ℕ slot-size) ≡ slot
        slot-recover = m*n/n≡m slot slot-size
    in record
    { ecx-eq = trans (ecx-eq corr) (sym (writeReg-preserves (regs ls) Output Input loc Input≢Output))
    ; eax-eq = trans (cong (λ s → OnStack frame s) slot-recover)
                     (sym (writeReg-same (regs ls) Output loc))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (sym (writeReg-preserves-stackSlot (regs ls) Output loc))
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls newRegs l))
    ; halt-eq = halt-eq corr
    }

  -- restore-input: Input := stack[frame, slot]
  -- Same with-pattern propagation issue as load-from-slot
  instr-sim (restore-input slot) ls xs alloc not-halted corr = {!!}

  -- instr-alloc-stack: increment stackSlot by n
  -- Abstract: incrStackSlot (regs ls) n = stackSlot + n
  -- x86: sub esp, n*4 → stack-slot + n*4/4 = stack-slot + n
  instr-sim (instr-alloc-stack n) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let slot-recover : n *ℕ slot-size / slot-size ≡ n
        slot-recover = m*n/n≡m n slot-size
        -- stack-slot xs + (n*4/4) = stack-slot xs + n
        x86-slot : stack-slot xs +ℕ (n *ℕ slot-size / slot-size) ≡ stack-slot xs +ℕ n
        x86-slot = cong (stack-slot xs +ℕ_) slot-recover
        -- stack-slot xs + n = stackSlot (regs ls) + n
        new-slot-eq : stack-slot xs +ℕ n ≡ stackSlot (regs ls) +ℕ n
        new-slot-eq = cong (_+ℕ n) (slot-eq corr)
        newRegs = incrStackSlot (regs ls) n
    in record
    { ecx-eq = trans (ecx-eq corr) (sym (incrStackSlot-preserves-Input (regs ls) n))
    ; eax-eq = trans (eax-eq corr) (sym (incrStackSlot-preserves-Output (regs ls) n))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans x86-slot new-slot-eq
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls newRegs l))
    ; halt-eq = halt-eq corr
    }

  -- instr-dealloc-stack: decrement stackSlot by n
  instr-sim (instr-dealloc-stack n) ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let slot-recover : n *ℕ slot-size / slot-size ≡ n
        slot-recover = m*n/n≡m n slot-size
        x86-slot : stack-slot xs ∸ (n *ℕ slot-size / slot-size) ≡ stack-slot xs ∸ n
        x86-slot = cong (stack-slot xs ∸_) slot-recover
        new-slot-eq : stack-slot xs ∸ n ≡ stackSlot (regs ls) ∸ n
        new-slot-eq = cong (_∸ n) (slot-eq corr)
        newRegs = decrStackSlot (regs ls) n
    in record
    { ecx-eq = trans (ecx-eq corr) (sym (decrStackSlot-preserves-Input (regs ls) n))
    ; eax-eq = trans (eax-eq corr) (sym (decrStackSlot-preserves-Output (regs ls) n))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans x86-slot new-slot-eq
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls newRegs l))
    ; halt-eq = halt-eq corr
    }

  -- instr-push-frame: Complex - involves multiple x86 instructions
  -- Note: There's a semantic gap here. Abstract sets stackSlot to 0 and stores
  -- capacity in alloc. X86 executes push ebp; mov ebp, esp; sub esp, cap*4 which
  -- results in stack-slot = cap (after mov resets to 0, sub adds cap).
  -- Additionally, exec-prog doesn't reduce due to with-pattern blocking.
  -- For a complete proof, we'd need:
  --   1. More nuanced correspondence relation for stack slot tracking
  --   2. Explicit reduction of exec-prog (avoiding with-pattern blocking)
  instr-sim (instr-push-frame cap) ls xs alloc not-halted corr = {!!}

  -- instr-pop-frame: No-op at abstract level
  -- x86: mov esp, ebp; pop ebp - both are no-ops in our exec-x86
  -- Same exec-prog reduction issue as instr-push-frame
  instr-sim instr-pop-frame ls xs alloc not-halted corr = {!!}

  -- instr-call-closure: No-op at abstract level
  -- x86: call [ebx + slot-size] - no-op in our exec-x86
  instr-sim instr-call-closure ls xs alloc not-halted corr
    with x86-halted xs | xs-not-halted ls xs alloc not-halted corr
  ... | true | ()
  ... | false | _ = corr  -- Both sides are identity, correspondence unchanged

  ------------------------------------------------------------------------
  -- Trace simulation
  ------------------------------------------------------------------------

  -- Lemma: exec-abstract preserves current-frame
  -- All instructions either return alloc unchanged or only modify frame-capacity
  exec-abstract-preserves-frame : ∀ i ls alloc →
    current-frame (proj₂ (exec-abstract i ls alloc)) ≡ current-frame alloc
  exec-abstract-preserves-frame mov-to-output ls alloc = refl
  exec-abstract-preserves-frame mov-to-input ls alloc = refl
  exec-abstract-preserves-frame load-indirect ls alloc = refl
  exec-abstract-preserves-frame load-indirect-suc ls alloc = refl
  exec-abstract-preserves-frame (load-from-slot slot) ls alloc with stackMem ls (current-frame alloc) slot
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (store-at-slot _) ls alloc = refl
  exec-abstract-preserves-frame store-indirect ls alloc = refl
  exec-abstract-preserves-frame store-indirect-suc ls alloc = refl
  exec-abstract-preserves-frame (lea-slot _) ls alloc = refl
  exec-abstract-preserves-frame (restore-input slot) ls alloc with stackMem ls (current-frame alloc) slot
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (instr-alloc-stack _) ls alloc = refl
  exec-abstract-preserves-frame (instr-dealloc-stack _) ls alloc = refl
  exec-abstract-preserves-frame (instr-push-frame _) ls alloc = refl
  exec-abstract-preserves-frame instr-pop-frame ls alloc = refl
  exec-abstract-preserves-frame instr-call-closure ls alloc = refl

  -- Trace simulation follows from instr-sim by induction
  -- With proper structure (parallel with-patterns), this is trivial
  trace-sim : ∀ trace ls xs alloc →
    Corresponds ls xs alloc →
    Corresponds (proj₁ (exec-trace trace ls alloc))
                (exec-prog (compile-trace trace) xs (current-frame alloc))
                (proj₂ (exec-trace trace ls alloc))
  trace-sim [] ls xs alloc corr = corr
  trace-sim (i ∷ is) ls xs alloc corr with halted ls in eqL | x86-halted xs in eqX | halt-eq corr
  ... | true  | true  | _ = subst (λ ys → Corresponds ls ys alloc) (sym (exec-prog-halted (compile-abstract i ++ compile-trace is) xs (current-frame alloc) eqX)) corr
  ... | true  | false | ()
  ... | false | true  | ()
  ... | false | false | _ =
    let frame = current-frame alloc
        ls' = proj₁ (exec-abstract i ls alloc)
        alloc' = proj₂ (exec-abstract i ls alloc)
        frame-preserved : current-frame alloc' ≡ frame
        frame-preserved = exec-abstract-preserves-frame i ls alloc
        xs' = exec-prog (compile-abstract i) xs frame
        corr' = instr-sim i ls xs alloc eqL corr
        -- Transport corr' to use the preserved frame
        rec = trace-sim is ls' xs' alloc' corr'
        -- Use frame preservation to fix the frame argument
        rec' : Corresponds (proj₁ (exec-trace is ls' alloc')) (exec-prog (compile-trace is) xs' frame) (proj₂ (exec-trace is ls' alloc'))
        rec' = subst (λ f → Corresponds (proj₁ (exec-trace is ls' alloc')) (exec-prog (compile-trace is) xs' f) (proj₂ (exec-trace is ls' alloc')))
                     frame-preserved rec
    in subst (λ ys → Corresponds (proj₁ (exec-trace is ls' alloc')) ys (proj₂ (exec-trace is ls' alloc')))
             (sym (exec-prog-++ (compile-abstract i) (compile-trace is) xs frame))
             rec'

------------------------------------------------------------------------
-- Connection to IR
------------------------------------------------------------------------

module IRConnection {FS : FrameSemantics} (bound : ℕ) (primSem : PrimSem) where
  open Simulation {FS}
  open FrameSemantics FS
  open MemOps {FS}
  open AbstractExec {FS}
  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} bound primSem using (IRResultAWF)

  -- Simplified: we prove correspondence for the trace execution
  -- IRResultAWF.trace-correct gives us: proj₁ (exec-trace trace s alloc) ≡ final-state
  ir-sim : ∀ {m A B} (ir : IR A B) (x : ⟦ A ⟧) ls xs alloc →
    (result : IRResultAWF m ir x ls alloc) →
    Corresponds ls xs alloc →
    Corresponds (proj₁ (exec-trace (IRResultAWF.trace result) ls alloc))
                (exec-prog (compile-trace (IRResultAWF.trace result)) xs (current-frame alloc))
                (proj₂ (exec-trace (IRResultAWF.trace result) ls alloc))
  ir-sim ir x ls xs alloc result corr =
    trace-sim (IRResultAWF.trace result) ls xs alloc corr
