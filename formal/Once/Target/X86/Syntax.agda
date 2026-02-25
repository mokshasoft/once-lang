------------------------------------------------------------------------
-- Once.Target.X86.Syntax
--
-- x86-64 instruction subset used by Once.
-- This is a minimal subset sufficient for the 12 categorical generators.
--
-- Based on the Sail x86-64 formal specification from REMS project.
------------------------------------------------------------------------

module Once.Target.X86.Syntax where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; foldr)

------------------------------------------------------------------------
-- Registers
------------------------------------------------------------------------

-- | x86-64 general-purpose registers (64-bit)
--
-- We use a subset relevant to Once's calling convention:
--   rax: return value
--   rdi: first argument (System V ABI)
--   rsi: second argument
--   rdx: third argument
--   r12: environment pointer (callee-saved, used for closures)
--   rsp: stack pointer
--   rbp: frame pointer
--
data Reg : Set where
  rax : Reg    -- Return value / accumulator
  rbx : Reg    -- Callee-saved (base)
  rcx : Reg    -- Fourth argument (Windows) / counter
  rdx : Reg    -- Third argument
  rsi : Reg    -- Second argument (source index)
  rdi : Reg    -- First argument (destination index)
  rbp : Reg    -- Frame pointer (callee-saved)
  rsp : Reg    -- Stack pointer
  r8  : Reg    -- Fifth argument
  r9  : Reg    -- Sixth argument
  r10 : Reg    -- Temporary
  r11 : Reg    -- Temporary
  r12 : Reg    -- Callee-saved (environment pointer for closures)
  r13 : Reg    -- Callee-saved
  r14 : Reg    -- Callee-saved
  r15 : Reg    -- Callee-saved

------------------------------------------------------------------------
-- Memory operands
------------------------------------------------------------------------

-- | Memory addressing modes
--
-- x86-64 supports complex addressing: [base + index*scale + displacement]
-- For Once, we primarily use simple base+displacement addressing.
--
data Mem : Set where
  -- [reg]: dereference register
  base : Reg → Mem
  -- [reg + offset]: base plus displacement (8-byte aligned for 64-bit)
  base+disp : Reg → ℕ → Mem
  -- [rip + offset]: RIP-relative addressing for position-independent code
  -- Used by curry to compute absolute address of thunk code
  rip+disp : ℕ → Mem

------------------------------------------------------------------------
-- Operands
------------------------------------------------------------------------

-- | Instruction operands
data Operand : Set where
  reg : Reg → Operand           -- Register operand
  mem : Mem → Operand           -- Memory operand
  imm : ℕ → Operand             -- Immediate value

------------------------------------------------------------------------
-- Instructions
------------------------------------------------------------------------

-- | x86-64 instruction subset for Once
--
-- This is the minimal subset needed to implement the 12 categorical generators:
--
-- | Generator | Instructions Used |
-- |-----------|-------------------|
-- | id        | (none/nop)        |
-- | compose   | sequencing        |
-- | fst       | mov reg, [reg+0]  |
-- | snd       | mov reg, [reg+8]  |
-- | pair      | mov [reg+0], val; mov [reg+8], val |
-- | inl       | mov [reg+0], 0; mov [reg+8], val (tag=0 + value) |
-- | inr       | mov [reg+0], 1; mov [reg+8], val (tag=1 + value) |
-- | case      | cmp + je/jne      |
-- | terminal  | (none/nop)        |
-- | initial   | ud2 (unreachable) |
-- | curry     | lea + mov (closure creation) |
-- | apply     | call indirect     |
--
data Instr : Set where
  -- Data movement
  mov    : Operand → Operand → Instr    -- mov dst, src
  lea    : Reg → Mem → Instr            -- lea reg, [mem] (load effective address)

  -- Arithmetic (for pointer arithmetic, tag operations)
  add    : Operand → Operand → Instr    -- add dst, src
  sub    : Operand → Operand → Instr    -- sub dst, src

  -- Comparison
  cmp    : Operand → Operand → Instr    -- cmp op1, op2 (sets flags)
  test   : Operand → Operand → Instr    -- test op1, op2 (AND, sets flags)

  -- Control flow
  jmp    : ℕ → Instr                    -- jmp label (unconditional)
  je     : ℕ → Instr                    -- je label (jump if equal/zero)
  jne    : ℕ → Instr                    -- jne label (jump if not equal/not zero)
  call   : Operand → Instr              -- call target (direct or indirect)
  ret    : Instr                        -- ret (return from function)

  -- Stack operations
  push   : Operand → Instr              -- push src
  pop    : Reg → Instr                  -- pop dst

  -- Special
  nop    : Instr                        -- no operation
  ud2    : Instr                        -- undefined instruction (trap for unreachable)

  -- Label (pseudo-instruction for assembly)
  label  : ℕ → Instr                    -- label n:

------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------

-- | A program is a list of instructions
Program : Set
Program = List Instr

-- | A function consists of a name and its body
record Function : Set where
  constructor mkfun
  field
    name : ℕ        -- Function identifier
    body : Program  -- Function body

------------------------------------------------------------------------
-- Once-specific conventions
------------------------------------------------------------------------

-- | Calling convention for Once
--
-- Arguments:
--   rdi: first argument (input value)
--   rsi: second argument (if needed)
--
-- Return:
--   rax: return value
--
-- Callee-saved (preserved across calls):
--   rbx, rbp, r12-r15
--
-- For closures:
--   r12: environment pointer
--   The closure structure is: [env_ptr, code_ptr]
--
-- For products (pairs):
--   Memory layout: [fst (8 bytes), snd (8 bytes)]
--   Access: fst at offset 0, snd at offset 8
--
-- For sums (tagged unions):
--   Memory layout: [tag (8 bytes), value (8 bytes)]
--   tag = 0 for inl, tag = 1 for inr
--   Access: tag at offset 0, value at offset 8

-- | Word/slot size for x86-64 (8 bytes)
slot-size : ℕ
slot-size = 8

-- | Convert slots to bytes: n slots = n * 8 bytes
slots : ℕ → ℕ
slots n = n *ℕ slot-size

------------------------------------------------------------------------
-- Stack consumption analysis
--
-- Compute how many stack slots an instruction consumes (positive)
-- or frees (negative represented as 0 here since we track max depth).
-- Used to derive stack requirements from codegen.
------------------------------------------------------------------------

-- | Stack slots consumed by a single instruction
-- Only counts allocations, not deallocations (for max depth calculation)
instr-consumed-slots : Instr → ℕ
instr-consumed-slots (push _) = 1
instr-consumed-slots (sub dst (imm n)) with dst
... | reg rsp = n / slot-size  -- sub rsp, n consumes n/8 slots
  where open import Data.Nat using (_/_)
... | _ = 0
instr-consumed-slots (call _) = 1  -- call pushes return address
instr-consumed-slots _ = 0

-- | Total stack slots consumed by an instruction sequence
-- Note: This counts allocations only, not the net change (ignores pop/add/ret)
instrs-consumed-slots : List Instr → ℕ
instrs-consumed-slots = foldr (λ i acc → instr-consumed-slots i +ℕ acc) 0

-- | Offsets for product fields
fstOffset : ℕ
fstOffset = 0

sndOffset : ℕ
sndOffset = slot-size

-- | Offsets for sum fields
tagOffset : ℕ
tagOffset = 0

valueOffset : ℕ
valueOffset = slot-size

-- | Tag values for sums
inlTag : ℕ
inlTag = 0

inrTag : ℕ
inrTag = 1
