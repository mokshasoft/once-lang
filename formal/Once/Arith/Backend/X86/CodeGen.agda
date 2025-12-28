------------------------------------------------------------------------
-- Once.Arith.Backend.X86.CodeGen
--
-- Code generation from ArithIR to x86-64 instructions.
-- Includes a simple register allocator for expression evaluation.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Backend.X86.CodeGen where

open import Once.Arith.Type
open import Once.Arith.IR
open import Once.Arith.Backend.X86.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; _++_; length; reverse)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Register allocation state
------------------------------------------------------------------------

-- | Available GPR registers for allocation (caller-saved, can be clobbered)
-- We exclude rax (return), rcx/rdx (division), rdi (input)
availableGPRs : List GPReg
availableGPRs = r8 ∷ r9 ∷ r10 ∷ r11 ∷ rbx ∷ []

-- | Available XMM registers for allocation
availableXMMs : List XMMReg
availableXMMs = xmm1 ∷ xmm2 ∷ xmm3 ∷ xmm4 ∷ xmm5 ∷ xmm6 ∷ xmm7 ∷ []

-- | Register allocation state
--
-- Tracks which registers are available and which are in use.
-- For simplicity, we use a counter-based approach.
--
record AllocState : Set where
  constructor mkState
  field
    nextGPR : ℕ      -- Index into availableGPRs
    nextXMM : ℕ      -- Index into availableXMMs

-- | Initial allocation state
initAlloc : AllocState
initAlloc = mkState 0 0

-- | Get the nth GPR (wrapping if needed - simple for now)
getGPR : ℕ → GPReg
getGPR 0 = r8
getGPR 1 = r9
getGPR 2 = r10
getGPR 3 = r11
getGPR 4 = rbx
getGPR _ = r8  -- Wrap (should spill in real allocator)

-- | Get the nth XMM
getXMM : ℕ → XMMReg
getXMM 0 = xmm1
getXMM 1 = xmm2
getXMM 2 = xmm3
getXMM 3 = xmm4
getXMM 4 = xmm5
getXMM 5 = xmm6
getXMM 6 = xmm7
getXMM _ = xmm1  -- Wrap

-- | Allocate a GPR
allocGPR : AllocState → GPReg × AllocState
allocGPR (mkState n m) = getGPR n , mkState (suc n) m

-- | Allocate an XMM
allocXMM : AllocState → XMMReg × AllocState
allocXMM (mkState n m) = getXMM m , mkState n (suc m)

-- | Free a register (decrement counter)
freeGPR : AllocState → AllocState
freeGPR (mkState n m) = mkState (n ∸ 1) m

freeXMM : AllocState → AllocState
freeXMM (mkState n m) = mkState n (m ∸ 1)

------------------------------------------------------------------------
-- Code generation result
------------------------------------------------------------------------

-- | Result of compiling an expression
--
-- Contains the generated code and the register holding the result.
--
record IntResult : Set where
  constructor mkIntResult
  field
    code : ArithProgram
    result : GPReg
    state : AllocState

record FloatResult : Set where
  constructor mkFloatResult
  field
    code : ArithProgram
    result : XMMReg
    state : AllocState

------------------------------------------------------------------------
-- Type coercions
------------------------------------------------------------------------

-- | Coerce integer type semantic value to ℤ
-- This is safe because ⟦ τ ⟧N = ℤ for all integer types
toℤ : ∀ {τ} → isInteger τ ≡ true → ⟦ τ ⟧N → ℤ
toℤ {I8}  refl n = n
toℤ {I16} refl n = n
toℤ {I32} refl n = n
toℤ {I64} refl n = n

------------------------------------------------------------------------
-- Integer code generation
------------------------------------------------------------------------

-- | Generate code for an integer arithmetic expression
--
-- Result is left in a GPR register.
-- Uses a simple stack-based evaluation approach.
--
compile-int : ∀ {Γ τ} → ArithIR Γ τ → isInteger τ ≡ true → AllocState → IntResult

-- Literal: load immediate into fresh register
compile-int (Lit {τ} n) p st =
  let (r , st') = allocGPR st
  in mkIntResult
       (intI (movI r (immI (toℤ p n))) ∷ [])
       r
       st'

-- Variable: load from environment (placeholder - needs env offset calculation)
compile-int (Var {x} {τ} _) _ st =
  let (r , st') = allocGPR st
  in mkIntResult
       (intI (movI r (memI (base rdi))) ∷ [])  -- Placeholder: load from [rdi]
       r
       st'

-- Binary operations: compile both operands, combine
compile-int (Add {_} {_} {τ} e₁ e₂) p st =
  let res₁ = compile-int e₁ p st
      res₂ = compile-int e₂ p (IntResult.state res₁)
      r₁ = IntResult.result res₁
      r₂ = IntResult.result res₂
      -- Add r₂ to r₁, result in r₁
      addCode = intI (addI r₁ (regI r₂)) ∷ []
  in mkIntResult
       (IntResult.code res₁ ++ IntResult.code res₂ ++ addCode)
       r₁
       (freeGPR (IntResult.state res₂))

compile-int (Sub {_} {_} {τ} e₁ e₂) p st =
  let res₁ = compile-int e₁ p st
      res₂ = compile-int e₂ p (IntResult.state res₁)
      r₁ = IntResult.result res₁
      r₂ = IntResult.result res₂
      subCode = intI (subI r₁ (regI r₂)) ∷ []
  in mkIntResult
       (IntResult.code res₁ ++ IntResult.code res₂ ++ subCode)
       r₁
       (freeGPR (IntResult.state res₂))

compile-int (Mul {_} {_} {τ} e₁ e₂) p st =
  let res₁ = compile-int e₁ p st
      res₂ = compile-int e₂ p (IntResult.state res₁)
      r₁ = IntResult.result res₁
      r₂ = IntResult.result res₂
      mulCode = intI (imulI r₁ (regI r₂)) ∷ []
  in mkIntResult
       (IntResult.code res₁ ++ IntResult.code res₂ ++ mulCode)
       r₁
       (freeGPR (IntResult.state res₂))

compile-int (Div {_} {_} {τ} e₁ e₂) p st =
  let res₁ = compile-int e₁ p st
      res₂ = compile-int e₂ p (IntResult.state res₁)
      r₁ = IntResult.result res₁
      r₂ = IntResult.result res₂
      -- Division: move dividend to rax, sign-extend to rdx:rax, idiv
      divCode = intI (movI rax (regI r₁)) ∷
                intI cqo ∷
                intI (idivI (regI r₂)) ∷
                intI (movI r₁ (regI rax)) ∷ []  -- Result (quotient) back to r₁
  in mkIntResult
       (IntResult.code res₁ ++ IntResult.code res₂ ++ divCode)
       r₁
       (freeGPR (IntResult.state res₂))

compile-int (Mod {_} {_} {τ} e₁ e₂) p st =
  let res₁ = compile-int e₁ p st
      res₂ = compile-int e₂ p (IntResult.state res₁)
      r₁ = IntResult.result res₁
      r₂ = IntResult.result res₂
      -- Modulo: like division, but result is in rdx
      modCode = intI (movI rax (regI r₁)) ∷
                intI cqo ∷
                intI (idivI (regI r₂)) ∷
                intI (movI r₁ (regI rdx)) ∷ []  -- Remainder from rdx to r₁
  in mkIntResult
       (IntResult.code res₁ ++ IntResult.code res₂ ++ modCode)
       r₁
       (freeGPR (IntResult.state res₂))

compile-int (Neg e) p st =
  let res = compile-int e p st
      r = IntResult.result res
      negCode = intI (negI r) ∷ []
  in mkIntResult
       (IntResult.code res ++ negCode)
       r
       (IntResult.state res)

-- Comparison: compute subtraction (sets flags), result is 0/1 placeholder
-- Full implementation would use setcc instructions based on flags.
-- For now, just compute the subtraction (matches Haskell backend).
compile-int (Cmp {_} {_} {τ} _ e₁ e₂) p st =
  let res₁ = compile-int e₁ p st
      res₂ = compile-int e₂ p (IntResult.state res₁)
      r₁ = IntResult.result res₁
      r₂ = IntResult.result res₂
      -- Placeholder: just compute difference (real impl would use cmp + setcc)
      cmpCode = intI (subI r₁ (regI r₂)) ∷ []
  in mkIntResult
       (IntResult.code res₁ ++ IntResult.code res₂ ++ cmpCode)
       r₁
       (freeGPR (IntResult.state res₂))

------------------------------------------------------------------------
-- Float code generation
------------------------------------------------------------------------

-- | Generate code for a floating-point expression
--
-- Result is left in an XMM register.
--
compile-float : ∀ {Γ τ} → ArithIR Γ τ → isFloat τ ≡ true → AllocState → FloatResult

-- Literal: load from constant pool (placeholder)
compile-float (Lit {F32} n) _ st =
  let (r , st') = allocXMM st
  in mkFloatResult
       (floatI (movss r (memF (base rdi))) ∷ [])  -- Placeholder
       r
       st'

compile-float (Lit {F64} n) _ st =
  let (r , st') = allocXMM st
  in mkFloatResult
       (floatI (movsd r (memF (base rdi))) ∷ [])  -- Placeholder
       r
       st'

-- Can't have Lit for integer types with float proof
compile-float (Lit {I8}  _) () _
compile-float (Lit {I16} _) () _
compile-float (Lit {I32} _) () _
compile-float (Lit {I64} _) () _

-- Variable: load from environment
compile-float (Var {_} {F32} _) _ st =
  let (r , st') = allocXMM st
  in mkFloatResult
       (floatI (movss r (memF (base rdi))) ∷ [])
       r
       st'

compile-float (Var {_} {F64} _) _ st =
  let (r , st') = allocXMM st
  in mkFloatResult
       (floatI (movsd r (memF (base rdi))) ∷ [])
       r
       st'

compile-float (Var {_} {I8}  _) () _
compile-float (Var {_} {I16} _) () _
compile-float (Var {_} {I32} _) () _
compile-float (Var {_} {I64} _) () _

-- Binary operations for F32
compile-float (Add {_} {_} {F32} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
      addCode = floatI (addss r₁ (regF r₂)) ∷ []
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ addCode)
       r₁
       (freeXMM (FloatResult.state res₂))

-- Binary operations for F64
compile-float (Add {_} {_} {F64} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
      addCode = floatI (addsd r₁ (regF r₂)) ∷ []
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ addCode)
       r₁
       (freeXMM (FloatResult.state res₂))

-- Can't have Add for integer types with float proof
compile-float (Add {_} {_} {I8}  _ _) () _
compile-float (Add {_} {_} {I16} _ _) () _
compile-float (Add {_} {_} {I32} _ _) () _
compile-float (Add {_} {_} {I64} _ _) () _

-- Sub for F32
compile-float (Sub {_} {_} {F32} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
      subCode = floatI (subss r₁ (regF r₂)) ∷ []
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ subCode)
       r₁
       (freeXMM (FloatResult.state res₂))

-- Sub for F64
compile-float (Sub {_} {_} {F64} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
      subCode = floatI (subsd r₁ (regF r₂)) ∷ []
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ subCode)
       r₁
       (freeXMM (FloatResult.state res₂))

compile-float (Sub {_} {_} {I8}  _ _) () _
compile-float (Sub {_} {_} {I16} _ _) () _
compile-float (Sub {_} {_} {I32} _ _) () _
compile-float (Sub {_} {_} {I64} _ _) () _

-- Mul for F32
compile-float (Mul {_} {_} {F32} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
      mulCode = floatI (mulss r₁ (regF r₂)) ∷ []
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ mulCode)
       r₁
       (freeXMM (FloatResult.state res₂))

-- Mul for F64
compile-float (Mul {_} {_} {F64} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
      mulCode = floatI (mulsd r₁ (regF r₂)) ∷ []
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ mulCode)
       r₁
       (freeXMM (FloatResult.state res₂))

compile-float (Mul {_} {_} {I8}  _ _) () _
compile-float (Mul {_} {_} {I16} _ _) () _
compile-float (Mul {_} {_} {I32} _ _) () _
compile-float (Mul {_} {_} {I64} _ _) () _

-- Div for F32
compile-float (Div {_} {_} {F32} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
      divCode = floatI (divss r₁ (regF r₂)) ∷ []
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ divCode)
       r₁
       (freeXMM (FloatResult.state res₂))

-- Div for F64
compile-float (Div {_} {_} {F64} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
      divCode = floatI (divsd r₁ (regF r₂)) ∷ []
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ divCode)
       r₁
       (freeXMM (FloatResult.state res₂))

compile-float (Div {_} {_} {I8}  _ _) () _
compile-float (Div {_} {_} {I16} _ _) () _
compile-float (Div {_} {_} {I32} _ _) () _
compile-float (Div {_} {_} {I64} _ _) () _

-- Mod is not standard for floats; placeholder
compile-float (Mod {_} {_} {F32} e₁ e₂) p st =
  compile-float e₁ p st  -- Placeholder: just return first operand

compile-float (Mod {_} {_} {F64} e₁ e₂) p st =
  compile-float e₁ p st  -- Placeholder: just return first operand

compile-float (Mod {_} {_} {I8}  _ _) () _
compile-float (Mod {_} {_} {I16} _ _) () _
compile-float (Mod {_} {_} {I32} _ _) () _
compile-float (Mod {_} {_} {I64} _ _) () _

-- Negation for F32 (xor with sign mask)
compile-float (Neg {_} {F32} e) p st =
  let res = compile-float e p st
      r = FloatResult.result res
      -- Negation via xorps with sign mask (placeholder: would need constant pool)
      negCode = floatI (xorps r r) ∷ []  -- Placeholder
  in mkFloatResult
       (FloatResult.code res ++ negCode)
       r
       (FloatResult.state res)

-- Negation for F64
compile-float (Neg {_} {F64} e) p st =
  let res = compile-float e p st
      r = FloatResult.result res
      negCode = floatI (xorpd r r) ∷ []  -- Placeholder
  in mkFloatResult
       (FloatResult.code res ++ negCode)
       r
       (FloatResult.state res)

compile-float (Neg {_} {I8}  _) () _
compile-float (Neg {_} {I16} _) () _
compile-float (Neg {_} {I32} _) () _
compile-float (Neg {_} {I64} _) () _

-- Comparison for F32 (placeholder: compute subtraction)
compile-float (Cmp {_} {_} {F32} _ e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
      cmpCode = floatI (subss r₁ (regF r₂)) ∷ []
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ cmpCode)
       r₁
       (freeXMM (FloatResult.state res₂))

-- Comparison for F64
compile-float (Cmp {_} {_} {F64} _ e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
      cmpCode = floatI (subsd r₁ (regF r₂)) ∷ []
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ cmpCode)
       r₁
       (freeXMM (FloatResult.state res₂))

compile-float (Cmp {_} {_} {I8}  _ _ _) () _
compile-float (Cmp {_} {_} {I16} _ _ _) () _
compile-float (Cmp {_} {_} {I32} _ _ _) () _
compile-float (Cmp {_} {_} {I64} _ _ _) () _

------------------------------------------------------------------------
-- Entry point
------------------------------------------------------------------------

-- | Compile an arithmetic expression to x86-64 code
--
-- Returns the program with result in rax (for integers) or xmm0 (for floats).
--
compile-arith : ∀ {Γ τ} → ArithIR Γ τ → ArithProgram
compile-arith {_} {I8}  e with compile-int e refl initAlloc
... | mkIntResult code r _ = code ++ (intI (movI rax (regI r)) ∷ [])
compile-arith {_} {I16} e with compile-int e refl initAlloc
... | mkIntResult code r _ = code ++ (intI (movI rax (regI r)) ∷ [])
compile-arith {_} {I32} e with compile-int e refl initAlloc
... | mkIntResult code r _ = code ++ (intI (movI rax (regI r)) ∷ [])
compile-arith {_} {I64} e with compile-int e refl initAlloc
... | mkIntResult code r _ = code ++ (intI (movI rax (regI r)) ∷ [])
compile-arith {_} {F32} e with compile-float e refl initAlloc
... | mkFloatResult code r _ = code ++ (floatI (movss xmm0 (regF r)) ∷ [])
compile-arith {_} {F64} e with compile-float e refl initAlloc
... | mkFloatResult code r _ = code ++ (floatI (movsd xmm0 (regF r)) ∷ [])

------------------------------------------------------------------------
-- Code length (for correctness proofs)
------------------------------------------------------------------------

-- | Length of generated code
code-length : ArithProgram → ℕ
code-length = length

------------------------------------------------------------------------
-- Compilation characterization lemmas (for correctness proofs)
------------------------------------------------------------------------

-- | Characterize compile-arith for integer literals
-- compile-arith (Lit n) = [movI r8 (immI n), movI rax (regI r8)]
compile-lit-int-char : ∀ {τ} (n : ⟦ τ ⟧N) (p : isInteger τ ≡ true) →
  compile-arith (Lit n) ≡
    intI (movI r8 (immI (toℤ p n))) ∷ intI (movI rax (regI r8)) ∷ []
compile-lit-int-char {I8}  n refl = refl
compile-lit-int-char {I16} n refl = refl
compile-lit-int-char {I32} n refl = refl
compile-lit-int-char {I64} n refl = refl
