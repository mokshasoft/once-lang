------------------------------------------------------------------------
-- Once.Arith.Backend.AArch64.CodeGen
--
-- Code generation from ArithIR to AArch64 instructions.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Backend.AArch64.CodeGen where

open import Once.Arith.Type
open import Once.Arith.IR
open import Once.Arith.Backend.AArch64.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Register allocation state
------------------------------------------------------------------------

availableGPRs : List GPReg
availableGPRs = x9 ∷ x10 ∷ x11 ∷ x12 ∷ x13 ∷ x14 ∷ x15 ∷ []

availableFPs : List FPReg
availableFPs = d16 ∷ d17 ∷ d18 ∷ d19 ∷ d20 ∷ d21 ∷ d22 ∷ d23 ∷ []

record AllocState : Set where
  constructor mkState
  field
    nextGPR : ℕ
    nextFP  : ℕ

initAlloc : AllocState
initAlloc = mkState 0 0

getGPR : ℕ → GPReg
getGPR 0 = x9
getGPR 1 = x10
getGPR 2 = x11
getGPR 3 = x12
getGPR 4 = x13
getGPR 5 = x14
getGPR 6 = x15
getGPR _ = x9

getFP : ℕ → FPReg
getFP 0 = d16
getFP 1 = d17
getFP 2 = d18
getFP 3 = d19
getFP 4 = d20
getFP 5 = d21
getFP 6 = d22
getFP 7 = d23
getFP _ = d16

allocGPR : AllocState → GPReg × AllocState
allocGPR (mkState n m) = getGPR n , mkState (suc n) m

allocFP : AllocState → FPReg × AllocState
allocFP (mkState n m) = getFP m , mkState n (suc m)

freeGPR : AllocState → AllocState
freeGPR (mkState n m) = mkState (n ∸ 1) m

freeFP : AllocState → AllocState
freeFP (mkState n m) = mkState n (m ∸ 1)

------------------------------------------------------------------------
-- Code generation result
------------------------------------------------------------------------

record IntResult : Set where
  constructor mkIntResult
  field
    code   : ArithProgram
    result : GPReg
    state  : AllocState

record FloatResult : Set where
  constructor mkFloatResult
  field
    code   : ArithProgram
    result : FPReg
    state  : AllocState

------------------------------------------------------------------------
-- Type coercions
------------------------------------------------------------------------

toℤ : ∀ {τ} → isInteger τ ≡ true → ⟦ τ ⟧N → ℤ
toℤ {I8}  refl n = n
toℤ {I16} refl n = n
toℤ {I32} refl n = n
toℤ {I64} refl n = n

------------------------------------------------------------------------
-- Integer code generation
------------------------------------------------------------------------

compile-int : ∀ {Γ τ} → ArithIR Γ τ → isInteger τ ≡ true → AllocState → IntResult

compile-int (Lit {τ} n) p st =
  let (r , st') = allocGPR st
  in mkIntResult
       (intI (movz r (toℤ p n) 0) ∷ [])
       r
       st'

compile-int (Var {x} {τ} _) _ st =
  let (r , st') = allocGPR st
  in mkIntResult
       (intI (mov r (regOp x0)) ∷ [])
       r
       st'

compile-int (Add {_} {_} {τ} e₁ e₂) p st =
  let res₁ = compile-int e₁ p st
      res₂ = compile-int e₂ p (IntResult.state res₁)
      r₁ = IntResult.result res₁
      r₂ = IntResult.result res₂
      addCode = intI (add r₁ r₁ (regOp r₂)) ∷ []
  in mkIntResult
       (IntResult.code res₁ ++ IntResult.code res₂ ++ addCode)
       r₁
       (freeGPR (IntResult.state res₂))

compile-int (Sub {_} {_} {τ} e₁ e₂) p st =
  let res₁ = compile-int e₁ p st
      res₂ = compile-int e₂ p (IntResult.state res₁)
      r₁ = IntResult.result res₁
      r₂ = IntResult.result res₂
      subCode = intI (sub r₁ r₁ (regOp r₂)) ∷ []
  in mkIntResult
       (IntResult.code res₁ ++ IntResult.code res₂ ++ subCode)
       r₁
       (freeGPR (IntResult.state res₂))

compile-int (Mul {_} {_} {τ} e₁ e₂) p st =
  let res₁ = compile-int e₁ p st
      res₂ = compile-int e₂ p (IntResult.state res₁)
      r₁ = IntResult.result res₁
      r₂ = IntResult.result res₂
      mulCode = intI (mul r₁ r₁ r₂) ∷ []
  in mkIntResult
       (IntResult.code res₁ ++ IntResult.code res₂ ++ mulCode)
       r₁
       (freeGPR (IntResult.state res₂))

compile-int (Div {_} {_} {τ} e₁ e₂) p st =
  let res₁ = compile-int e₁ p st
      res₂ = compile-int e₂ p (IntResult.state res₁)
      r₁ = IntResult.result res₁
      r₂ = IntResult.result res₂
      divCode = intI (sdiv r₁ r₁ r₂) ∷ []
  in mkIntResult
       (IntResult.code res₁ ++ IntResult.code res₂ ++ divCode)
       r₁
       (freeGPR (IntResult.state res₂))

compile-int (Mod {_} {_} {τ} e₁ e₂) p st =
  let res₁ = compile-int e₁ p st
      res₂ = compile-int e₂ p (IntResult.state res₁)
      r₁ = IntResult.result res₁
      r₂ = IntResult.result res₂
      (rTmp , st') = allocGPR (IntResult.state res₂)
      modCode = intI (sdiv rTmp r₁ r₂) ∷
                intI (msub r₁ rTmp r₂ r₁) ∷ []
  in mkIntResult
       (IntResult.code res₁ ++ IntResult.code res₂ ++ modCode)
       r₁
       (freeGPR (freeGPR st'))

compile-int (Neg e) p st =
  let res = compile-int e p st
      r = IntResult.result res
      negCode = intI (neg r r) ∷ []
  in mkIntResult
       (IntResult.code res ++ negCode)
       r
       (IntResult.state res)

------------------------------------------------------------------------
-- Float code generation
------------------------------------------------------------------------

compile-float : ∀ {Γ τ} → ArithIR Γ τ → isFloat τ ≡ true → AllocState → FloatResult

compile-float (Lit {F32} n) _ st =
  let (r , st') = allocFP st
  in mkFloatResult (fpI (fmov r (fpRegOp d0)) ∷ []) r st'

compile-float (Lit {F64} n) _ st =
  let (r , st') = allocFP st
  in mkFloatResult (fpI (fmov r (fpRegOp d0)) ∷ []) r st'

compile-float (Lit {I8}  _) () _
compile-float (Lit {I16} _) () _
compile-float (Lit {I32} _) () _
compile-float (Lit {I64} _) () _

compile-float (Var {_} {F32} _) _ st =
  let (r , st') = allocFP st
  in mkFloatResult (fpI (fmov r (fpRegOp d0)) ∷ []) r st'

compile-float (Var {_} {F64} _) _ st =
  let (r , st') = allocFP st
  in mkFloatResult (fpI (fmov r (fpRegOp d0)) ∷ []) r st'

compile-float (Var {_} {I8}  _) () _
compile-float (Var {_} {I16} _) () _
compile-float (Var {_} {I32} _) () _
compile-float (Var {_} {I64} _) () _

compile-float (Add {_} {_} {F32} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ (fpI (faddS r₁ r₁ r₂) ∷ []))
       r₁ (freeFP (FloatResult.state res₂))

compile-float (Add {_} {_} {F64} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ (fpI (fadd r₁ r₁ r₂) ∷ []))
       r₁ (freeFP (FloatResult.state res₂))

compile-float (Add {_} {_} {I8}  _ _) () _
compile-float (Add {_} {_} {I16} _ _) () _
compile-float (Add {_} {_} {I32} _ _) () _
compile-float (Add {_} {_} {I64} _ _) () _

compile-float (Sub {_} {_} {F32} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ (fpI (fsubS r₁ r₁ r₂) ∷ []))
       r₁ (freeFP (FloatResult.state res₂))

compile-float (Sub {_} {_} {F64} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ (fpI (fsub r₁ r₁ r₂) ∷ []))
       r₁ (freeFP (FloatResult.state res₂))

compile-float (Sub {_} {_} {I8}  _ _) () _
compile-float (Sub {_} {_} {I16} _ _) () _
compile-float (Sub {_} {_} {I32} _ _) () _
compile-float (Sub {_} {_} {I64} _ _) () _

compile-float (Mul {_} {_} {F32} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ (fpI (fmulS r₁ r₁ r₂) ∷ []))
       r₁ (freeFP (FloatResult.state res₂))

compile-float (Mul {_} {_} {F64} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ (fpI (fmul r₁ r₁ r₂) ∷ []))
       r₁ (freeFP (FloatResult.state res₂))

compile-float (Mul {_} {_} {I8}  _ _) () _
compile-float (Mul {_} {_} {I16} _ _) () _
compile-float (Mul {_} {_} {I32} _ _) () _
compile-float (Mul {_} {_} {I64} _ _) () _

compile-float (Div {_} {_} {F32} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ (fpI (fdivS r₁ r₁ r₂) ∷ []))
       r₁ (freeFP (FloatResult.state res₂))

compile-float (Div {_} {_} {F64} e₁ e₂) p st =
  let res₁ = compile-float e₁ p st
      res₂ = compile-float e₂ p (FloatResult.state res₁)
      r₁ = FloatResult.result res₁
      r₂ = FloatResult.result res₂
  in mkFloatResult
       (FloatResult.code res₁ ++ FloatResult.code res₂ ++ (fpI (fdiv r₁ r₁ r₂) ∷ []))
       r₁ (freeFP (FloatResult.state res₂))

compile-float (Div {_} {_} {I8}  _ _) () _
compile-float (Div {_} {_} {I16} _ _) () _
compile-float (Div {_} {_} {I32} _ _) () _
compile-float (Div {_} {_} {I64} _ _) () _

compile-float (Mod {_} {_} {F32} e₁ e₂) p st = compile-float e₁ p st
compile-float (Mod {_} {_} {F64} e₁ e₂) p st = compile-float e₁ p st

compile-float (Mod {_} {_} {I8}  _ _) () _
compile-float (Mod {_} {_} {I16} _ _) () _
compile-float (Mod {_} {_} {I32} _ _) () _
compile-float (Mod {_} {_} {I64} _ _) () _

compile-float (Neg {_} {F32} e) p st =
  let res = compile-float e p st
      r = FloatResult.result res
  in mkFloatResult (FloatResult.code res ++ (fpI (fnegS r r) ∷ [])) r (FloatResult.state res)

compile-float (Neg {_} {F64} e) p st =
  let res = compile-float e p st
      r = FloatResult.result res
  in mkFloatResult (FloatResult.code res ++ (fpI (fneg r r) ∷ [])) r (FloatResult.state res)

compile-float (Neg {_} {I8}  _) () _
compile-float (Neg {_} {I16} _) () _
compile-float (Neg {_} {I32} _) () _
compile-float (Neg {_} {I64} _) () _

------------------------------------------------------------------------
-- Entry point
------------------------------------------------------------------------

compile-arith : ∀ {Γ τ} → ArithIR Γ τ → ArithProgram
compile-arith {_} {I8}  e with compile-int e refl initAlloc
... | mkIntResult code r _ = code ++ (intI (mov x0 (regOp r)) ∷ [])
compile-arith {_} {I16} e with compile-int e refl initAlloc
... | mkIntResult code r _ = code ++ (intI (mov x0 (regOp r)) ∷ [])
compile-arith {_} {I32} e with compile-int e refl initAlloc
... | mkIntResult code r _ = code ++ (intI (mov x0 (regOp r)) ∷ [])
compile-arith {_} {I64} e with compile-int e refl initAlloc
... | mkIntResult code r _ = code ++ (intI (mov x0 (regOp r)) ∷ [])
compile-arith {_} {F32} e with compile-float e refl initAlloc
... | mkFloatResult code r _ = code ++ (fpI (fmov d0 (fpRegOp r)) ∷ [])
compile-arith {_} {F64} e with compile-float e refl initAlloc
... | mkFloatResult code r _ = code ++ (fpI (fmov d0 (fpRegOp r)) ∷ [])

------------------------------------------------------------------------
-- Compilation characterization lemmas
------------------------------------------------------------------------

compile-lit-int-char : ∀ {τ} (n : ⟦ τ ⟧N) (p : isInteger τ ≡ true) →
  compile-arith (Lit n) ≡
    intI (movz x9 (toℤ p n) 0) ∷ intI (mov x0 (regOp x9)) ∷ []
compile-lit-int-char {I8}  n refl = refl
compile-lit-int-char {I16} n refl = refl
compile-lit-int-char {I32} n refl = refl
compile-lit-int-char {I64} n refl = refl
