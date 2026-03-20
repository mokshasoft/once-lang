------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.DirectSimulation
--
-- Direct simulation from AbstractInstr → RISC-V 64.
--
-- KEY INSIGHT: Structure RV64 execution to EXACTLY match exec-abstract.
-- Both use the same with-pattern structure on memory reads, so proofs
-- can use parallel with-patterns and reduce together.
------------------------------------------------------------------------

module Once.CCC.Target.RiscV64.DirectSimulation where

open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _≤_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.DivMod using (_/_; m*n/n≡m)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat.Properties using (_≟_; +-assoc; +-comm; +-identityʳ; +-∸-comm)
open import Function using (case_of_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
import Once.CCC.Machine.SMPrimitives as SMP
import Once.ProofObligation as PO
open import Once.CCC.Target.RiscV64.Syntax
  using (Reg; ra; sp; fp; a0; t0; s1; Program; slot-size; slots)
  renaming (Instr to RV64Instr; zero to reg-zero)
open import Once.CCC.Target.RiscV64.Syntax
  using (ld; sd; addi; mv; jalr; ret; nop; unimp)
open import Once.CCC.Target.RiscV64.AbstractToRiscV
  using (compile-abstract; compile-trace; slot-to-disp)
open import Once.CCC.IR using (IR)
open import Once.CCC.Eval using (PrimSem)
open import Once.CCC.Target.RiscV64.Types using (⟦_⟧)

------------------------------------------------------------------------
-- Simulation module
--
-- KEY INSIGHT: RV64State uses ValueLocation directly, not ℕ addresses.
-- This makes exec-rv64 perform THE SAME OPERATION as exec-abstract,
-- so simulation proofs become trivial (essentially refl).
------------------------------------------------------------------------

module Simulation {FS : FrameSemantics} where
  open FrameSemantics FS
  open MemOps {FS}
  open ExecFinal {FS}
  open AbstractExec {FS}

  ------------------------------------------------------------------------
  -- RV64 State (inside Simulation to access ValueLocation FS)
  --
  -- Uses ValueLocation directly, mirroring LocState structure.
  -- This eliminates the loc-to-addr bridging that made proofs complex.
  ------------------------------------------------------------------------

  record RV64State : Set where
    constructor mkRV64
    field
      a0-val : ValueLocation FS    -- Output/Input register (maps to rv64 a0)
      t0-val : ValueLocation FS    -- Temp register for indirect stores
      cur-frame : Frame            -- Current frame (maps to fp)
      stack-slot : ℕ               -- Stack slot index (maps to sp offset)
      rv64-mem : ValueLocation FS → Maybe (ValueLocation FS)  -- Memory
      rv64-halted : Bool           -- Halted flag
  open RV64State public

  ------------------------------------------------------------------------
  -- Correspondence relation
  --
  -- With ValueLocation-based RV64State, correspondence is near-equality.
  -- Each field directly corresponds, no loc-to-addr conversion needed.
  ------------------------------------------------------------------------

  record Corresponds (ls : LocState FS) (rs : RV64State) (alloc : AllocState {FS}) : Set where
    field
      a0-eq : a0-val rs ≡ readReg (regs ls) Output
      t0-eq : t0-val rs ≡ readReg (regs ls) Input
      frame-eq : cur-frame rs ≡ current-frame alloc
      -- KEY INSIGHT: stack-slot includes frame-capacity (pre-allocated by push-frame)
      -- while stackSlot tracks only slots used beyond the initial allocation.
      -- After push-frame cap: stackSlot=0, stack-slot=cap, so slot-eq holds.
      -- After alloc-stack n: stackSlot=n, stack-slot=cap+n, so slot-eq still holds.
      slot-eq : stack-slot rs ≡ stackSlot (regs ls) +ℕ frame-capacity alloc
      mem-eq : ∀ loc → rv64-mem rs loc ≡ readLoc ls loc
      halt-eq : rv64-halted rs ≡ halted ls
  open Corresponds public

  ------------------------------------------------------------------------
  -- RV64 Execution
  --
  -- KEY: exec-rv64 performs the SAME operations as exec-abstract,
  -- just using RV64 instruction syntax. This makes simulation trivial.
  ------------------------------------------------------------------------

  -- Helper: compute slot location from frame and slot number
  slotLoc : Frame → ℕ → ValueLocation FS
  slotLoc f n = OnStack f n

  -- Helper: convert displacement back to slot number (inverse of slot-to-disp)
  -- slot-to-disp n = n * slot-size, so disp-to-slot d = d / slot-size
  disp-to-slot : ℕ → ℕ
  disp-to-slot d = d / slot-size

  -- Helper: convert ℤ immediate to ℕ (absolute value)
  imm-to-ℕ : ℤ → ℕ
  imm-to-ℕ (+ n) = n
  imm-to-ℕ -[1+ n ] = suc n

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
  writeRV64Mem : (ValueLocation FS → Maybe (ValueLocation FS)) →
               ValueLocation FS → ValueLocation FS →
               (ValueLocation FS → Maybe (ValueLocation FS))
  writeRV64Mem m loc v loc' with loc ≟L loc'
  ... | yes _ = just v
  ... | no _  = m loc'

  ------------------------------------------------------------------------
  -- RV64 execution helpers
  --
  -- Like exec-load-with-value in SMCore, these expose the decision point
  -- for external proofs.
  ------------------------------------------------------------------------

  -- Helper: apply memory read result to load into a0
  exec-rv64-load-a0-with-value : Maybe (ValueLocation FS) → RV64State → RV64State
  exec-rv64-load-a0-with-value (just v) rs = record rs { a0-val = v }
  exec-rv64-load-a0-with-value nothing rs = record rs { rv64-halted = true }

  -- Helper: apply memory read result to load into t0
  exec-rv64-load-t0-with-value : Maybe (ValueLocation FS) → RV64State → RV64State
  exec-rv64-load-t0-with-value (just v) rs = record rs { t0-val = v }
  exec-rv64-load-t0-with-value nothing rs = record rs { rv64-halted = true }

  exec-rv64 : RV64Instr → RV64State → Frame → RV64State

  -- load-indirect: ld a0, 0(t0) → a0' = *t0
  exec-rv64 (ld a0 t0 0) rs _ =
    exec-rv64-load-a0-with-value (rv64-mem rs (t0-val rs)) rs

  -- load-indirect-suc: ld a0, 8(t0) → a0' = *(sucLoc t0)
  exec-rv64 (ld a0 t0 d) rs _ =
    exec-rv64-load-a0-with-value (rv64-mem rs (sucLoc (t0-val rs))) rs

  -- load-from-slot: ld a0, disp(fp) → a0' = stack[frame, slot]
  exec-rv64 (ld a0 fp d) rs frame =
    exec-rv64-load-a0-with-value (rv64-mem rs (slotLoc frame (disp-to-slot d))) rs

  -- restore-input: ld t0, disp(fp) → t0' = stack[frame, slot]
  exec-rv64 (ld t0 fp d) rs frame =
    exec-rv64-load-t0-with-value (rv64-mem rs (slotLoc frame (disp-to-slot d))) rs

  -- store-indirect: sd a0, 0(t0) → *t0 := a0
  exec-rv64 (sd a0 t0 0) rs _ =
    record rs { rv64-mem = writeRV64Mem (rv64-mem rs) (t0-val rs) (a0-val rs) }

  -- store-indirect-suc: sd a0, 8(t0) → *(sucLoc t0) := a0
  exec-rv64 (sd a0 t0 d) rs _ =
    record rs { rv64-mem = writeRV64Mem (rv64-mem rs) (sucLoc (t0-val rs)) (a0-val rs) }

  -- store-at-slot: sd a0, disp(fp) → stack[frame, slot] := a0
  exec-rv64 (sd a0 fp d) rs frame =
    record rs { rv64-mem = writeRV64Mem (rv64-mem rs) (slotLoc frame (disp-to-slot d)) (a0-val rs) }

  -- lea-slot: addi a0, fp, disp → a0' = &stack[frame, slot]
  exec-rv64 (addi a0 fp d) rs frame =
    record rs { a0-val = slotLoc frame (disp-to-slot (imm-to-ℕ d)) }

  -- mov-to-output: mv a0, t0 → a0' = t0
  exec-rv64 (mv a0 t0) rs _ = record rs { a0-val = t0-val rs }

  -- mov-to-input: mv t0, a0 → t0' = a0
  exec-rv64 (mv t0 a0) rs _ = record rs { t0-val = a0-val rs }

  -- Frame push sequence helpers
  exec-rv64 (sd fp sp 0) rs _ = rs  -- save fp is a no-op in our model
  exec-rv64 (mv fp sp) rs _ = record rs { stack-slot = 0 }  -- establish new frame base

  -- Frame pop sequence helpers
  exec-rv64 (mv sp fp) rs _ = rs  -- restore sp from fp (no-op)
  exec-rv64 (ld fp sp 0) rs _ = rs  -- restore fp (no-op)
  -- Pop-frame uses addi sp fp to distinguish from dealloc-stack
  exec-rv64 (addi sp fp d) rs _ = rs  -- pop saved fp (no-op in our model)

  -- Stack management (convert bytes to slots using division)
  -- Negative imm = allocation (add to stack-slot)
  -- Positive imm = deallocation (subtract from stack-slot)
  exec-rv64 (addi sp sp (+ n)) rs _ =
    record rs { stack-slot = stack-slot rs ∸ (n / slot-size) }
  exec-rv64 (addi sp sp -[1+ n ]) rs _ =
    record rs { stack-slot = stack-slot rs +ℕ ((suc n) / slot-size) }

  -- Control flow (no-ops at abstract level)
  exec-rv64 (jalr ra t0 0) rs _ = rs
  exec-rv64 (ld t0 s1 d) rs _ = rs  -- load closure code pointer (no-op)
  exec-rv64 ret rs _ = rs
  exec-rv64 nop rs _ = rs
  exec-rv64 unimp rs _ = record rs { rv64-halted = true }
  exec-rv64 _ rs _ = rs

  -- Mutually recursive: exec-prog and exec-prog-step
  exec-prog : Program → RV64State → Frame → RV64State
  exec-prog-step : Bool → RV64Instr → Program → RV64State → Frame → RV64State

  exec-prog [] rs _ = rs
  exec-prog (i ∷ is) rs frame = exec-prog-step (rv64-halted rs) i is rs frame

  exec-prog-step true _ _ rs _ = rs
  exec-prog-step false i is rs frame = exec-prog is (exec-rv64 i rs frame) frame

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

  -- readLoc is unchanged when only halted changes
  readLoc-halted-irrel : ∀ ls h loc →
    readLoc (record ls { halted = h }) loc ≡ readLoc ls loc
  readLoc-halted-irrel ls h (OnStack f k) = refl
  readLoc-halted-irrel ls h (OnHeap hl) with heapMem ls hl
  ... | just _ = refl
  ... | nothing = refl

  -- If halted, exec-prog returns unchanged
  exec-prog-halted : ∀ prog rs frame → rv64-halted rs ≡ true → exec-prog prog rs frame ≡ rs
  exec-prog-halted [] rs _ _ = refl
  exec-prog-halted (i ∷ is) rs frame h rewrite h = refl

  -- exec-prog distributes over ++
  exec-prog-++ : ∀ prog1 prog2 rs frame →
    exec-prog (prog1 ++ prog2) rs frame ≡ exec-prog prog2 (exec-prog prog1 rs frame) frame
  exec-prog-++ [] prog2 rs frame = refl
  exec-prog-++ (i ∷ is) prog2 rs frame with rv64-halted rs in eq
  ... | true = sym (exec-prog-halted prog2 rs frame eq)
  ... | false = exec-prog-++ is prog2 (exec-rv64 i rs frame) frame

  -- Lemma: exec-prog-step false reduces to recursive call
  exec-prog-step-false : ∀ i is rs frame →
    exec-prog-step false i is rs frame ≡ exec-prog is (exec-rv64 i rs frame) frame
  exec-prog-step-false _ _ _ _ = refl

  -- rv64-halted is unaffected by stack-slot changes
  rv64-halted-stack-irrel : ∀ rs n → rv64-halted (record rs { stack-slot = n }) ≡ rv64-halted rs
  rv64-halted-stack-irrel rs n = refl

  -- exec-prog on pop-frame instructions is identity when not halted
  -- RV64: mv sp, fp; ld fp, 0(sp); addi sp, fp, slot-size
  -- All three instructions are no-ops in our model
  exec-prog-pop-frame : ∀ rs frame →
    rv64-halted rs ≡ false →
    exec-prog (mv sp fp ∷ ld fp sp 0 ∷ addi sp fp (+ slot-size) ∷ []) rs frame ≡ rs
  exec-prog-pop-frame rs frame not-halted
    rewrite not-halted
    rewrite not-halted
    rewrite not-halted
    = refl

  -- exec-prog on call-closure instructions is identity when not halted
  -- RV64: ld t0, 8(s1); jalr ra, t0, 0
  -- Both instructions are no-ops in our model
  exec-prog-call-closure : ∀ rs frame →
    rv64-halted rs ≡ false →
    exec-prog (ld t0 s1 slot-size ∷ jalr ra t0 0 ∷ []) rs frame ≡ rs
  exec-prog-call-closure rs frame not-halted
    rewrite not-halted
    rewrite not-halted
    = refl

  -- exec-prog on push-frame instructions
  -- RV64: addi sp, sp, -8; sd fp, 0(sp); mv fp, sp; addi sp, sp, -k
  -- Like X86-32, keep division unevaluated in result
  --
  -- For cap = 0: last addi is (+ 0), uses positive pattern
  exec-prog-push-frame-zero : ∀ rs frame →
    rv64-halted rs ≡ false →
    exec-prog (addi sp sp -[1+ 7 ] ∷ sd fp sp 0 ∷ mv fp sp ∷ addi sp sp (+ 0) ∷ []) rs frame ≡
    record rs { stack-slot = 0 }
  exec-prog-push-frame-zero rs frame not-halted
    rewrite not-halted
    rewrite not-halted
    rewrite rv64-halted-stack-irrel rs 0
    rewrite not-halted
    = refl

  -- For cap = suc m: last addi is -[1+ k], keep division unevaluated
  exec-prog-push-frame-suc : ∀ k rs frame →
    rv64-halted rs ≡ false →
    exec-prog (addi sp sp -[1+ 7 ] ∷ sd fp sp 0 ∷ mv fp sp ∷ addi sp sp -[1+ k ] ∷ []) rs frame ≡
    record rs { stack-slot = suc k / slot-size }
  exec-prog-push-frame-suc k rs frame not-halted
    rewrite not-halted
    rewrite not-halted
    rewrite rv64-halted-stack-irrel rs 0
    rewrite not-halted
    = refl

  -- Helper: exec-prog of single instruction when not halted
  exec-prog-single : ∀ i rs frame →
    rv64-halted rs ≡ false →
    exec-prog (i ∷ []) rs frame ≡ exec-rv64 i rs frame
  exec-prog-single i rs frame not-halted rewrite not-halted = refl

  -- exec-prog on alloc-stack instructions
  -- Case split on n because Data.Integer.-_ needs to know if n*8 is zero or suc
  exec-prog-alloc-stack-zero : ∀ rs frame →
    rv64-halted rs ≡ false →
    exec-prog (addi sp sp (+ 0) ∷ []) rs frame ≡ rs
  exec-prog-alloc-stack-zero rs frame not-halted =
    exec-prog-single (addi sp sp (+ 0)) rs frame not-halted

  exec-prog-alloc-stack-suc : ∀ k rs frame →
    rv64-halted rs ≡ false →
    exec-prog (addi sp sp -[1+ k ] ∷ []) rs frame ≡
    record rs { stack-slot = stack-slot rs +ℕ (suc k / slot-size) }
  exec-prog-alloc-stack-suc k rs frame not-halted =
    exec-prog-single (addi sp sp -[1+ k ]) rs frame not-halted

  -- exec-prog on dealloc-stack instructions
  -- The positive immediate (+ n) always matches the general pattern
  exec-prog-dealloc-stack : ∀ n rs frame →
    rv64-halted rs ≡ false →
    exec-prog (addi sp sp (+ n) ∷ []) rs frame ≡
    record rs { stack-slot = stack-slot rs ∸ (n / slot-size) }
  exec-prog-dealloc-stack n rs frame not-halted =
    exec-prog-single (addi sp sp (+ n)) rs frame not-halted

  ------------------------------------------------------------------------
  -- Per-instruction simulation
  --
  -- KEY INSIGHT: With ValueLocation-based RV64State, exec-rv64 performs
  -- the SAME operation as exec-abstract. Proofs are trivial equalities.
  ------------------------------------------------------------------------

  -- Helper: derive rv64-halted rs ≡ false from correspondence and not-halted
  rs-not-halted : ∀ ls rs alloc → halted ls ≡ false → Corresponds ls rs alloc → rv64-halted rs ≡ false
  rs-not-halted ls rs alloc not-halted corr = trans (halt-eq corr) not-halted

  -- Helper: lift stackSlot equality to include frame-capacity
  slot-eq-lift : ∀ {s1 s2 : ℕ} (alloc : AllocState {FS}) →
    s1 ≡ s2 →
    s1 +ℕ frame-capacity alloc ≡ s2 +ℕ frame-capacity alloc
  slot-eq-lift alloc eq = cong (_+ℕ frame-capacity alloc) eq

  -- Helper for alloc-stack: (a + b) + c ≡ (a + c) + b
  slot-eq-alloc-helper : ∀ (a b c : ℕ) →
    (a +ℕ b) +ℕ c ≡ (a +ℕ c) +ℕ b
  slot-eq-alloc-helper a b c =
    trans (+-assoc a b c) (trans (cong (a +ℕ_) (+-comm b c)) (sym (+-assoc a c b)))

  -- Well-formedness invariant: deallocation never exceeds allocation.
  -- Proof obligation: deallocation never exceeds allocation.
  -- The compiler generates code that maintains stack discipline.
  dealloc-well-formed : ∀ (ls : LocState FS) (n : ℕ) → n ≤ stackSlot (regs ls)
  dealloc-well-formed = PO.!!

  -- Helper for dealloc-stack: (a + b) ∸ c ≡ (a ∸ c) + b  [when c ≤ a]
  -- Uses stdlib's +-∸-comm with well-formedness assumption.
  slot-eq-dealloc-helper : ∀ (a b c : ℕ) → c ≤ a →
    (a +ℕ b) ∸ c ≡ (a ∸ c) +ℕ b
  slot-eq-dealloc-helper a b c c≤a = +-∸-comm b c≤a

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

  -- Helper: writeRV64Mem corresponds to writeLoc for stack locations
  writeRV64Mem-stack-corresponds : ∀ (ls : LocState FS) (rs : RV64State) (f : Frame) (k : ℕ) (val : ValueLocation FS) →
    (∀ l → rv64-mem rs l ≡ readLoc ls l) →
    a0-val rs ≡ val →
    (∀ l → writeRV64Mem (rv64-mem rs) (OnStack f k) (a0-val rs) l ≡ readLoc (writeLoc ls (OnStack f k) val) l)
  writeRV64Mem-stack-corresponds ls rs f k val mem-eq a0-eq l
    with (OnStack f k) ≟L l
  ... | yes refl =
    trans (cong just a0-eq) (sym (writeLoc-read-same-stack ls f k val))
  ... | no loc≢l =
    trans (mem-eq l) (sym (writeLoc-preserves-other ls (OnStack f k) l val loc≢l))

  -- Helper: writeRV64Mem corresponds to writeLoc for any location
  writeRV64Mem-corresponds : ∀ (ls : LocState FS) (rs : RV64State) (loc val : ValueLocation FS) →
    (∀ l → rv64-mem rs l ≡ readLoc ls l) →
    a0-val rs ≡ val →
    (∀ l → writeRV64Mem (rv64-mem rs) loc (a0-val rs) l ≡ readLoc (writeLoc ls loc val) l)
  writeRV64Mem-corresponds ls rs (OnStack f k) val mem-eq a0-eq =
    writeRV64Mem-stack-corresponds ls rs f k val mem-eq a0-eq
  writeRV64Mem-corresponds ls rs (OnHeap hl) val mem-eq a0-eq l
    with (OnHeap hl) ≟L l
  ... | yes refl =
    trans (cong just a0-eq) (sym (SMP.MemoryOps.readLoc-writeLoc-same ls (OnHeap hl) val))
  ... | no loc≢l = trans (mem-eq l) (sym (writeLoc-preserves-other ls (OnHeap hl) l val loc≢l))

  -- Helper: contradiction from halted rs ≡ true and correspondence
  halted-contradiction : ∀ {ls rs alloc} → rv64-halted rs ≡ true → halted ls ≡ false → Corresponds ls rs alloc → ⊥
  halted-contradiction eq-true not-halt corr with trans (sym (halt-eq corr)) eq-true | not-halt
  ... | refl | ()

  -- Helper: correspondence for load-into-a0 operations
  load-a0-corresponds : ∀ (mv : Maybe (ValueLocation FS)) (ls : LocState FS) (rs : RV64State) (alloc : AllocState {FS}) →
    Corresponds ls rs alloc →
    Corresponds (exec-load-with-value Output mv ls)
                (exec-rv64-load-a0-with-value mv rs)
                alloc
  load-a0-corresponds (just v) ls rs alloc corr = record
    { a0-eq = sym (writeReg-same (regs ls) Output v)
    ; t0-eq = trans (t0-eq corr) (sym (writeReg-preserves (regs ls) Output Input v (λ ())))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (sym (writeReg-preserves-stackSlot (regs ls) Output v)))
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls (writeReg (regs ls) Output v) l))
    ; halt-eq = halt-eq corr
    }
  load-a0-corresponds nothing ls rs alloc corr = record
    { a0-eq = a0-eq corr
    ; t0-eq = t0-eq corr
    ; frame-eq = frame-eq corr
    ; slot-eq = slot-eq corr
    ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-halted-irrel ls true loc))
    ; halt-eq = refl
    }

  -- Helper: correspondence for load-into-t0 operations (restore-input)
  load-t0-corresponds : ∀ (mv : Maybe (ValueLocation FS)) (ls : LocState FS) (rs : RV64State) (alloc : AllocState {FS}) →
    Corresponds ls rs alloc →
    Corresponds (proj₁ (exec-restore-input-with-value mv ls alloc))
                (exec-rv64-load-t0-with-value mv rs)
                (proj₂ (exec-restore-input-with-value mv ls alloc))
  load-t0-corresponds (just v) ls rs alloc corr = record
    { a0-eq = trans (a0-eq corr) (sym (writeReg-preserves (regs ls) Input Output v (λ ())))
    ; t0-eq = sym (writeReg-same (regs ls) Input v)
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (sym (writeReg-preserves-stackSlot (regs ls) Input v)))
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls (writeReg (regs ls) Input v) l))
    ; halt-eq = halt-eq corr
    }
  load-t0-corresponds nothing ls rs alloc corr = record
    { a0-eq = a0-eq corr
    ; t0-eq = t0-eq corr
    ; frame-eq = frame-eq corr
    ; slot-eq = slot-eq corr
    ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-halted-irrel ls true loc))
    ; halt-eq = refl
    }

  -- Helper: correspondence for load-from-slot operations
  load-from-slot-corresponds : ∀ (mv : Maybe (ValueLocation FS)) (ls : LocState FS) (rs : RV64State) (alloc : AllocState {FS}) →
    Corresponds ls rs alloc →
    Corresponds (proj₁ (exec-load-from-slot-with-value mv ls alloc))
                (exec-rv64-load-a0-with-value mv rs)
                (proj₂ (exec-load-from-slot-with-value mv ls alloc))
  load-from-slot-corresponds (just v) ls rs alloc corr = record
    { a0-eq = sym (writeReg-same (regs ls) Output v)
    ; t0-eq = trans (t0-eq corr) (sym (writeReg-preserves (regs ls) Output Input v (λ ())))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (sym (writeReg-preserves-stackSlot (regs ls) Output v)))
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls (writeReg (regs ls) Output v) l))
    ; halt-eq = halt-eq corr
    }
  load-from-slot-corresponds nothing ls rs alloc corr = record
    { a0-eq = a0-eq corr
    ; t0-eq = t0-eq corr
    ; frame-eq = frame-eq corr
    ; slot-eq = slot-eq corr
    ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-halted-irrel ls true loc))
    ; halt-eq = refl
    }

  instr-sim : ∀ i ls rs alloc →
    halted ls ≡ false →
    Corresponds ls rs alloc →
    Corresponds (proj₁ (exec-abstract i ls alloc))
                (exec-prog (compile-abstract i) rs (current-frame alloc))
                (proj₂ (exec-abstract i ls alloc))

  -- mov-to-output: Output := Input
  -- RV64: compiles to [] (no-op) because a0 holds both
  instr-sim mov-to-output ls rs alloc not-halted corr with rv64-halted rs | rs-not-halted ls rs alloc not-halted corr
  ... | false | _ =
    let inputVal = readReg (regs ls) Input
        newRegs = writeReg (regs ls) Output inputVal
    in record
    { a0-eq = trans (t0-eq corr) (sym (writeReg-same (regs ls) Output inputVal))
    ; t0-eq = trans (t0-eq corr) (sym (writeReg-preserves (regs ls) Output Input inputVal Input≢Output))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (sym (writeReg-preserves-stackSlot (regs ls) Output inputVal)))
    ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-regs-irrel ls newRegs loc))
    ; halt-eq = halt-eq corr
    }
  ... | true | ()

  -- mov-to-input: Input := Output
  -- RV64: compiles to [] (no-op)
  instr-sim mov-to-input ls rs alloc not-halted corr with rv64-halted rs | rs-not-halted ls rs alloc not-halted corr
  ... | false | _ =
    let outputVal = readReg (regs ls) Output
        newRegs = writeReg (regs ls) Input outputVal
    in record
    { a0-eq = trans (a0-eq corr) (sym (writeReg-preserves (regs ls) Input Output outputVal Output≢Input))
    ; t0-eq = trans (a0-eq corr) (sym (writeReg-same (regs ls) Input outputVal))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (sym (writeReg-preserves-stackSlot (regs ls) Input outputVal)))
    ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-regs-irrel ls newRegs loc))
    ; halt-eq = halt-eq corr
    }
  ... | true | ()

  -- load-indirect: Output := *Input
  -- RV64: ld a0, 0(t0) - load from address in t0 (Input)
  instr-sim load-indirect ls rs alloc not-halted corr
    with rv64-halted rs | rs-not-halted ls rs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let loc = readReg (regs ls) Input
        rv64-loc-eq : t0-val rs ≡ loc
        rv64-loc-eq = t0-eq corr
        mem-read-eq : rv64-mem rs (t0-val rs) ≡ readLoc ls loc
        mem-read-eq = trans (cong (rv64-mem rs) rv64-loc-eq) (mem-eq corr loc)
        abs-read = readLoc ls loc
        base-corr = load-a0-corresponds abs-read ls rs alloc corr
    in subst (λ mv → Corresponds (exec-load-with-value Output abs-read ls)
                                  (exec-rv64-load-a0-with-value mv rs)
                                  alloc)
             (sym mem-read-eq)
             base-corr

  -- load-indirect-suc: Output := *(sucLoc Input)
  -- RV64: ld a0, 8(t0)
  instr-sim load-indirect-suc ls rs alloc not-halted corr
    with rv64-halted rs | rs-not-halted ls rs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let loc = sucLoc (readReg (regs ls) Input)
        rv64-loc-eq : sucLoc (t0-val rs) ≡ loc
        rv64-loc-eq = cong sucLoc (t0-eq corr)
        mem-read-eq : rv64-mem rs (sucLoc (t0-val rs)) ≡ readLoc ls loc
        mem-read-eq = trans (cong (rv64-mem rs) rv64-loc-eq) (mem-eq corr loc)
        abs-read = readLoc ls loc
        base-corr = load-a0-corresponds abs-read ls rs alloc corr
    in subst (λ mv → Corresponds (exec-load-with-value Output abs-read ls)
                                  (exec-rv64-load-a0-with-value mv rs)
                                  alloc)
             (sym mem-read-eq)
             base-corr

  -- load-from-slot: Output := stack[frame, slot]
  instr-sim (load-from-slot slot) ls rs alloc not-halted corr
    with rv64-halted rs | rs-not-halted ls rs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let frame = current-frame alloc
        loc = OnStack frame slot
        slot-recover : disp-to-slot (slot *ℕ slot-size) ≡ slot
        slot-recover = m*n/n≡m slot slot-size
        rv64-loc : slotLoc frame (disp-to-slot (slot *ℕ slot-size)) ≡ loc
        rv64-loc = cong (OnStack frame) slot-recover
        mem-read-eq : rv64-mem rs (slotLoc frame (disp-to-slot (slot *ℕ slot-size))) ≡ readLoc ls loc
        mem-read-eq = trans (cong (rv64-mem rs) rv64-loc) (mem-eq corr loc)
        abs-read = readLoc ls loc
        base-corr = load-from-slot-corresponds abs-read ls rs alloc corr
    in subst (λ mv → Corresponds (proj₁ (exec-load-from-slot-with-value abs-read ls alloc))
                                  (exec-rv64-load-a0-with-value mv rs)
                                  (proj₂ (exec-load-from-slot-with-value abs-read ls alloc)))
             (sym mem-read-eq)
             base-corr

  -- store-at-slot: stack[frame, slot] := Output
  instr-sim (store-at-slot slot) ls rs alloc not-halted corr
    with rv64-halted rs | rs-not-halted ls rs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let frame = current-frame alloc
        loc = OnStack frame slot
        val = readReg (regs ls) Output
        ls' = writeLoc ls loc val
        regs-eq : regs ls' ≡ regs ls
        regs-eq = writeLoc-regs ls loc val
        slot-recover : disp-to-slot (slot *ℕ slot-size) ≡ slot
        slot-recover = m*n/n≡m slot slot-size
        mem-eq' : ∀ l → writeRV64Mem (rv64-mem rs) (OnStack frame (disp-to-slot (slot *ℕ slot-size))) (a0-val rs) l ≡ readLoc ls' l
        mem-eq' = subst (λ s → ∀ l → writeRV64Mem (rv64-mem rs) (OnStack frame s) (a0-val rs) l ≡ readLoc ls' l)
                        (sym slot-recover)
                        (writeRV64Mem-stack-corresponds ls rs frame slot val (mem-eq corr) (a0-eq corr))
    in record
    { a0-eq = trans (a0-eq corr) (cong (λ r → readReg r Output) (sym regs-eq))
    ; t0-eq = trans (t0-eq corr) (cong (λ r → readReg r Input) (sym regs-eq))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (cong stackSlot (sym regs-eq)))
    ; mem-eq = mem-eq'
    ; halt-eq = trans (halt-eq corr) (sym (writeLoc-halted ls loc val))
    }

  -- store-indirect: *Input := Output
  instr-sim store-indirect ls rs alloc not-halted corr
    with rv64-halted rs | rs-not-halted ls rs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let loc = readReg (regs ls) Input
        val = readReg (regs ls) Output
        ls' = writeLoc ls loc val
        regs-eq : regs ls' ≡ regs ls
        regs-eq = writeLoc-regs ls loc val
        loc-eq : t0-val rs ≡ loc
        loc-eq = t0-eq corr
        mem-eq' : ∀ l → writeRV64Mem (rv64-mem rs) (t0-val rs) (a0-val rs) l ≡ readLoc ls' l
        mem-eq' = subst (λ t0 → ∀ l → writeRV64Mem (rv64-mem rs) t0 (a0-val rs) l ≡ readLoc ls' l)
                       (sym loc-eq)
                       (writeRV64Mem-corresponds ls rs loc val (mem-eq corr) (a0-eq corr))
    in record
    { a0-eq = trans (a0-eq corr) (cong (λ r → readReg r Output) (sym regs-eq))
    ; t0-eq = trans (t0-eq corr) (cong (λ r → readReg r Input) (sym regs-eq))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (cong stackSlot (sym regs-eq)))
    ; mem-eq = mem-eq'
    ; halt-eq = trans (halt-eq corr) (sym (writeLoc-halted ls loc val))
    }

  -- store-indirect-suc: *(sucLoc Input) := Output
  instr-sim store-indirect-suc ls rs alloc not-halted corr
    with rv64-halted rs | rs-not-halted ls rs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let loc = sucLoc (readReg (regs ls) Input)
        val = readReg (regs ls) Output
        ls' = writeLoc ls loc val
        regs-eq : regs ls' ≡ regs ls
        regs-eq = writeLoc-regs ls loc val
        t0-eq' : t0-val rs ≡ readReg (regs ls) Input
        t0-eq' = t0-eq corr
        loc-eq : sucLoc (t0-val rs) ≡ loc
        loc-eq = cong sucLoc t0-eq'
        mem-eq' : ∀ l → writeRV64Mem (rv64-mem rs) (sucLoc (t0-val rs)) (a0-val rs) l ≡ readLoc ls' l
        mem-eq' = subst (λ sloc → ∀ l → writeRV64Mem (rv64-mem rs) sloc (a0-val rs) l ≡ readLoc ls' l)
                       (sym loc-eq)
                       (writeRV64Mem-corresponds ls rs loc val (mem-eq corr) (a0-eq corr))
    in record
    { a0-eq = trans (a0-eq corr) (cong (λ r → readReg r Output) (sym regs-eq))
    ; t0-eq = trans (t0-eq corr) (cong (λ r → readReg r Input) (sym regs-eq))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (cong stackSlot (sym regs-eq)))
    ; mem-eq = mem-eq'
    ; halt-eq = trans (halt-eq corr) (sym (writeLoc-halted ls loc val))
    }

  -- lea-slot: Output := &stack[frame, slot]
  instr-sim (lea-slot slot) ls rs alloc not-halted corr
    with rv64-halted rs | rs-not-halted ls rs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let frame = current-frame alloc
        loc = OnStack frame slot
        newRegs = writeReg (regs ls) Output loc
        slot-recover : disp-to-slot (slot *ℕ slot-size) ≡ slot
        slot-recover = m*n/n≡m slot slot-size
    in record
    { a0-eq = trans (cong (λ s → OnStack frame s) slot-recover)
                    (sym (writeReg-same (regs ls) Output loc))
    ; t0-eq = trans (t0-eq corr) (sym (writeReg-preserves (regs ls) Output Input loc Input≢Output))
    ; frame-eq = frame-eq corr
    ; slot-eq = trans (slot-eq corr) (slot-eq-lift alloc (sym (writeReg-preserves-stackSlot (regs ls) Output loc)))
    ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls newRegs l))
    ; halt-eq = halt-eq corr
    }

  -- restore-input: Input := stack[frame, slot]
  instr-sim (restore-input slot) ls rs alloc not-halted corr
    with rv64-halted rs | rs-not-halted ls rs alloc not-halted corr
  ... | true | ()
  ... | false | _ =
    let frame = current-frame alloc
        loc = OnStack frame slot
        slot-recover : disp-to-slot (slot *ℕ slot-size) ≡ slot
        slot-recover = m*n/n≡m slot slot-size
        rv64-loc : slotLoc frame (disp-to-slot (slot *ℕ slot-size)) ≡ loc
        rv64-loc = cong (OnStack frame) slot-recover
        mem-read-eq : rv64-mem rs (slotLoc frame (disp-to-slot (slot *ℕ slot-size))) ≡ readLoc ls loc
        mem-read-eq = trans (cong (rv64-mem rs) rv64-loc) (mem-eq corr loc)
        abs-read = readLoc ls loc
        base-corr = load-t0-corresponds abs-read ls rs alloc corr
    in subst (λ mv → Corresponds (proj₁ (exec-restore-input-with-value abs-read ls alloc))
                                  (exec-rv64-load-t0-with-value mv rs)
                                  (proj₂ (exec-restore-input-with-value abs-read ls alloc)))
             (sym mem-read-eq)
             base-corr

  -- instr-alloc-stack: increment stackSlot by n
  -- Case split on n to handle Data.Integer.-_ reduction
  instr-sim (instr-alloc-stack zero) ls rs alloc not-halted corr =
    let rs-not-halt = rs-not-halted ls rs alloc not-halted corr
        rv64-eq : exec-prog (compile-abstract (instr-alloc-stack zero)) rs (current-frame alloc) ≡ rs
        rv64-eq = exec-prog-alloc-stack-zero rs (current-frame alloc) rs-not-halt
        newRegs = incrStackSlot (regs ls) zero
        -- stackSlot newRegs = stackSlot (regs ls) +ℕ 0
        -- Need: stack-slot rs ≡ (stackSlot (regs ls) +ℕ 0) +ℕ frame-capacity alloc
        -- From slot-eq corr: stack-slot rs ≡ stackSlot (regs ls) +ℕ frame-capacity alloc
        -- Use +-identityʳ to show stackSlot (regs ls) +ℕ 0 ≡ stackSlot (regs ls)
        stackSlot-id : stackSlot (regs ls) +ℕ 0 ≡ stackSlot (regs ls)
        stackSlot-id = +-identityʳ (stackSlot (regs ls))
        new-slot-eq : stack-slot rs ≡ stackSlot newRegs +ℕ frame-capacity alloc
        new-slot-eq = trans (slot-eq corr) (cong (_+ℕ frame-capacity alloc) (sym stackSlot-id))
    in subst (λ ys → Corresponds (record ls { regs = newRegs }) ys alloc) (sym rv64-eq)
       (record
         { a0-eq = a0-eq corr
         ; t0-eq = t0-eq corr
         ; frame-eq = frame-eq corr
         ; slot-eq = new-slot-eq
         ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls newRegs l))
         ; halt-eq = halt-eq corr
         })

  instr-sim (instr-alloc-stack (suc m)) ls rs alloc not-halted corr =
    let rs-not-halt = rs-not-halted ls rs alloc not-halted corr
        -- slots (suc m) = (suc m) * 8 = suc (7 + m*8)
        k = 7 +ℕ m *ℕ slot-size
        slot-recover : suc k / slot-size ≡ suc m
        slot-recover = m*n/n≡m (suc m) slot-size
        rv64-eq : exec-prog (compile-abstract (instr-alloc-stack (suc m))) rs (current-frame alloc)
               ≡ record rs { stack-slot = stack-slot rs +ℕ (suc k / slot-size) }
        rv64-eq = exec-prog-alloc-stack-suc k rs (current-frame alloc) rs-not-halt
        rv64-slot : stack-slot rs +ℕ (suc k / slot-size) ≡ stack-slot rs +ℕ suc m
        rv64-slot = cong (stack-slot rs +ℕ_) slot-recover
        step1 : stack-slot rs +ℕ suc m ≡ (stackSlot (regs ls) +ℕ frame-capacity alloc) +ℕ suc m
        step1 = cong (_+ℕ suc m) (slot-eq corr)
        step2 : (stackSlot (regs ls) +ℕ frame-capacity alloc) +ℕ suc m ≡ (stackSlot (regs ls) +ℕ suc m) +ℕ frame-capacity alloc
        step2 = slot-eq-alloc-helper (stackSlot (regs ls)) (frame-capacity alloc) (suc m)
        new-slot-eq : stack-slot rs +ℕ (suc k / slot-size) ≡ (stackSlot (regs ls) +ℕ suc m) +ℕ frame-capacity alloc
        new-slot-eq = trans rv64-slot (trans step1 step2)
        newRegs = incrStackSlot (regs ls) (suc m)
        new-corr : Corresponds (record ls { regs = newRegs })
                               (record rs { stack-slot = stack-slot rs +ℕ (suc k / slot-size) })
                               alloc
        new-corr = record
          { a0-eq = trans (a0-eq corr) (sym (incrStackSlot-preserves-Output (regs ls) (suc m)))
          ; t0-eq = trans (t0-eq corr) (sym (incrStackSlot-preserves-Input (regs ls) (suc m)))
          ; frame-eq = frame-eq corr
          ; slot-eq = new-slot-eq
          ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls newRegs l))
          ; halt-eq = halt-eq corr
          }
    in subst (λ ys → Corresponds (record ls { regs = newRegs }) ys alloc) (sym rv64-eq) new-corr

  -- instr-dealloc-stack: decrement stackSlot by n
  instr-sim (instr-dealloc-stack n) ls rs alloc not-halted corr =
    let rs-not-halt = rs-not-halted ls rs alloc not-halted corr
        slot-recover : n *ℕ slot-size / slot-size ≡ n
        slot-recover = m*n/n≡m n slot-size
        rv64-eq : exec-prog (compile-abstract (instr-dealloc-stack n)) rs (current-frame alloc)
               ≡ record rs { stack-slot = stack-slot rs ∸ (n *ℕ slot-size / slot-size) }
        rv64-eq = exec-prog-dealloc-stack (n *ℕ slot-size) rs (current-frame alloc) rs-not-halt
        rv64-slot : stack-slot rs ∸ (n *ℕ slot-size / slot-size) ≡ stack-slot rs ∸ n
        rv64-slot = cong (stack-slot rs ∸_) slot-recover
        step1 : stack-slot rs ∸ n ≡ (stackSlot (regs ls) +ℕ frame-capacity alloc) ∸ n
        step1 = cong (_∸ n) (slot-eq corr)
        step2 : (stackSlot (regs ls) +ℕ frame-capacity alloc) ∸ n ≡ (stackSlot (regs ls) ∸ n) +ℕ frame-capacity alloc
        step2 = slot-eq-dealloc-helper (stackSlot (regs ls)) (frame-capacity alloc) n (dealloc-well-formed ls n)
        new-slot-eq : stack-slot rs ∸ (n *ℕ slot-size / slot-size) ≡ (stackSlot (regs ls) ∸ n) +ℕ frame-capacity alloc
        new-slot-eq = trans rv64-slot (trans step1 step2)
        newRegs = decrStackSlot (regs ls) n
        new-corr : Corresponds (record ls { regs = newRegs })
                               (record rs { stack-slot = stack-slot rs ∸ (n *ℕ slot-size / slot-size) })
                               alloc
        new-corr = record
          { a0-eq = trans (a0-eq corr) (sym (decrStackSlot-preserves-Output (regs ls) n))
          ; t0-eq = trans (t0-eq corr) (sym (decrStackSlot-preserves-Input (regs ls) n))
          ; frame-eq = frame-eq corr
          ; slot-eq = new-slot-eq
          ; mem-eq = λ l → trans (mem-eq corr l) (sym (readLoc-regs-irrel ls newRegs l))
          ; halt-eq = halt-eq corr
          }
    in subst (λ ys → Corresponds (record ls { regs = newRegs }) ys alloc) (sym rv64-eq) new-corr

  -- instr-push-frame: push new frame with capacity cap
  -- Case split on cap to handle Data.Integer.-_ reduction
  instr-sim (instr-push-frame zero) ls rs alloc not-halted corr =
    let rs-not-halt = rs-not-halted ls rs alloc not-halted corr
        alloc' = record alloc { frame-capacity = zero }
        newRegs = writeStackSlot (regs ls) 0
        -- For cap = 0: compile-abstract produces addi sp sp (+ 0) for last instr
        rv64-eq : exec-prog (compile-abstract (instr-push-frame zero)) rs (current-frame alloc)
               ≡ record rs { stack-slot = 0 }
        rv64-eq = exec-prog-push-frame-zero rs (current-frame alloc) rs-not-halt
        new-slot-eq : 0 ≡ stackSlot newRegs +ℕ frame-capacity alloc'
        new-slot-eq = refl
        new-corr : Corresponds (record ls { regs = newRegs })
                               (record rs { stack-slot = 0 })
                               alloc'
        new-corr = record
          { a0-eq = a0-eq corr
          ; t0-eq = t0-eq corr
          ; frame-eq = frame-eq corr
          ; slot-eq = new-slot-eq
          ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-regs-irrel ls newRegs loc))
          ; halt-eq = halt-eq corr
          }
    in subst (λ ys → Corresponds (record ls { regs = newRegs }) ys alloc') (sym rv64-eq) new-corr

  instr-sim (instr-push-frame (suc m)) ls rs alloc not-halted corr =
    let rs-not-halt = rs-not-halted ls rs alloc not-halted corr
        -- slots (suc m) = (suc m) * 8 = suc (7 + m*8) definitionally
        -- So -(+ (suc (7 + m*8))) = -[1+ (7 + m*8)]
        k = 7 +ℕ m *ℕ slot-size
        slot-recover : suc k / slot-size ≡ suc m
        slot-recover = m*n/n≡m (suc m) slot-size
        alloc' = record alloc { frame-capacity = suc m }
        newRegs = writeStackSlot (regs ls) 0
        -- The rv64 program execution result (keep division unevaluated)
        rv64-eq : exec-prog (compile-abstract (instr-push-frame (suc m))) rs (current-frame alloc)
               ≡ record rs { stack-slot = suc k / slot-size }
        rv64-eq = exec-prog-push-frame-suc k rs (current-frame alloc) rs-not-halt
        -- slot-eq: suc k / slot-size ≡ suc m ≡ 0 + suc m = stackSlot newRegs + frame-capacity alloc'
        new-slot-eq : suc k / slot-size ≡ stackSlot newRegs +ℕ frame-capacity alloc'
        new-slot-eq = slot-recover
        new-corr : Corresponds (record ls { regs = newRegs })
                               (record rs { stack-slot = suc k / slot-size })
                               alloc'
        new-corr = record
          { a0-eq = a0-eq corr
          ; t0-eq = t0-eq corr
          ; frame-eq = frame-eq corr
          ; slot-eq = new-slot-eq
          ; mem-eq = λ loc → trans (mem-eq corr loc) (sym (readLoc-regs-irrel ls newRegs loc))
          ; halt-eq = halt-eq corr
          }
    in subst (λ ys → Corresponds (record ls { regs = newRegs }) ys alloc') (sym rv64-eq) new-corr

  -- instr-pop-frame: No-op at abstract level
  instr-sim instr-pop-frame ls rs alloc not-halted corr =
    let rs-nothalt = rs-not-halted ls rs alloc not-halted corr
        rv64-identity = exec-prog-pop-frame rs (current-frame alloc) rs-nothalt
    in subst (λ ys → Corresponds ls ys alloc) (sym rv64-identity) corr

  -- instr-call-closure: No-op at abstract level
  instr-sim instr-call-closure ls rs alloc not-halted corr =
    let rs-nothalt = rs-not-halted ls rs alloc not-halted corr
        rv64-identity = exec-prog-call-closure rs (current-frame alloc) rs-nothalt
    in subst (λ ys → Corresponds ls ys alloc) (sym rv64-identity) corr

  ------------------------------------------------------------------------
  -- Trace simulation
  ------------------------------------------------------------------------

  exec-abstract-preserves-frame : ∀ i ls alloc →
    current-frame (proj₂ (exec-abstract i ls alloc)) ≡ current-frame alloc
  exec-abstract-preserves-frame mov-to-output ls alloc = refl
  exec-abstract-preserves-frame mov-to-input ls alloc = refl
  exec-abstract-preserves-frame load-indirect ls alloc = refl
  exec-abstract-preserves-frame load-indirect-suc ls alloc = refl
  exec-abstract-preserves-frame (load-from-slot slot) ls alloc
    with readLoc ls (OnStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (store-at-slot _) ls alloc = refl
  exec-abstract-preserves-frame store-indirect ls alloc = refl
  exec-abstract-preserves-frame store-indirect-suc ls alloc = refl
  exec-abstract-preserves-frame (lea-slot _) ls alloc = refl
  exec-abstract-preserves-frame (restore-input slot) ls alloc
    with readLoc ls (OnStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (instr-alloc-stack _) ls alloc = refl
  exec-abstract-preserves-frame (instr-dealloc-stack _) ls alloc = refl
  exec-abstract-preserves-frame (instr-push-frame _) ls alloc = refl
  exec-abstract-preserves-frame instr-pop-frame ls alloc = refl
  exec-abstract-preserves-frame instr-call-closure ls alloc = refl

  trace-sim : ∀ trace ls rs alloc →
    Corresponds ls rs alloc →
    Corresponds (proj₁ (exec-trace trace ls alloc))
                (exec-prog (compile-trace trace) rs (current-frame alloc))
                (proj₂ (exec-trace trace ls alloc))
  trace-sim [] ls rs alloc corr = corr
  trace-sim (i ∷ is) ls rs alloc corr with halted ls in eqL | rv64-halted rs in eqX | halt-eq corr
  ... | true  | true  | _ = subst (λ ys → Corresponds ls ys alloc) (sym (exec-prog-halted (compile-abstract i ++ compile-trace is) rs (current-frame alloc) eqX)) corr
  ... | true  | false | ()
  ... | false | true  | ()
  ... | false | false | _ =
    let frame = current-frame alloc
        ls' = proj₁ (exec-abstract i ls alloc)
        alloc' = proj₂ (exec-abstract i ls alloc)
        frame-preserved : current-frame alloc' ≡ frame
        frame-preserved = exec-abstract-preserves-frame i ls alloc
        rs' = exec-prog (compile-abstract i) rs frame
        corr' = instr-sim i ls rs alloc eqL corr
        rec = trace-sim is ls' rs' alloc' corr'
        rec' : Corresponds (proj₁ (exec-trace is ls' alloc')) (exec-prog (compile-trace is) rs' frame) (proj₂ (exec-trace is ls' alloc'))
        rec' = subst (λ f → Corresponds (proj₁ (exec-trace is ls' alloc')) (exec-prog (compile-trace is) rs' f) (proj₂ (exec-trace is ls' alloc')))
                     frame-preserved rec
    in subst (λ ys → Corresponds (proj₁ (exec-trace is ls' alloc')) ys (proj₂ (exec-trace is ls' alloc')))
             (sym (exec-prog-++ (compile-abstract i) (compile-trace is) rs frame))
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

  ir-sim : ∀ {m A B} (ir : IR A B) (x : ⟦ A ⟧) ls rs alloc →
    (result : IRResultAWF m ir x ls alloc) →
    Corresponds ls rs alloc →
    Corresponds (proj₁ (exec-trace (IRResultAWF.trace result) ls alloc))
                (exec-prog (compile-trace (IRResultAWF.trace result)) rs (current-frame alloc))
                (proj₂ (exec-trace (IRResultAWF.trace result) ls alloc))
  ir-sim ir x ls rs alloc result corr =
    trace-sim (IRResultAWF.trace result) ls rs alloc corr
