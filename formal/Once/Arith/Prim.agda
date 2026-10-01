-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Prim — THE COMPILER'S OWN ARITHMETIC PRIMITIVES, BY IDENTITY (D255).
--
-- A SigOp minted by the compiler for arithmetic carries `primV p`: its meaning
-- is `primSem p`, fixed by the primitive, not supplied. So a consumer that
-- needs "this SigOp IS addition" (the arith recogniser, D165) matches the
-- constructor, and the meaning follows definitionally. It used to match the
-- NAME (`arith.add.int`), which a pure FFI contract (`pureV`, any function)
-- could in principle carry as well.
------------------------------------------------------------------------

module Once.Arith.Prim where

open import Data.Product using (_,_)
open import Once.Type using (Type; Int; Float; _*_)
open import Once.Word using (Carrier)
import Once.Word as OnceWord
open import Once.Target.Arch using (TargetNum; int-bits; float-format)
import Once.Float.Arith as FA
import Once.Semantics.Value Carrier Carrier as M

module W (tn : TargetNum) = OnceWord.Width (int-bits tn)

------------------------------------------------------------------------
-- The meanings
------------------------------------------------------------------------

-- Binary arithmetic — Int * Int → Int
add-semM : TargetNum → M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
add-semM tn (a , b) = W._⊕_ tn a b

sub-semM : TargetNum → M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
sub-semM tn (a , b) = W._⊖_ tn a b

mul-semM : TargetNum → M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
mul-semM tn (a , b) = W._⊗_ tn a b

-- Unary: Int → Int
neg-semM : TargetNum → M.⟦ Int ⟧ → M.⟦ Int ⟧
neg-semM tn x = W.⊝_ tn x

------------------------------------------------------------------------
-- FLOAT arithmetic (plan 0.75 F4)
--
-- The same shape as the integer family above and for the same reason. `⊕` is
-- `norm tn (x + y)` — the exact operation in a scaffolding domain, then the
-- target's normalisation — and `Once.Float.Arith.fadd` is that sentence with
-- "rounding at the format" in place of "reduction mod 2^w". Neither is a
-- postulate; both read the target out of the `TargetNum` they are handed.
--
-- ONE fact comes off `tn`: the format. An invalid operation gives THE
-- canonical NaN at every target, by D055's rule — the targets genuinely
-- disagree in hardware (x86 sets the sign and propagates payloads, RISC-V
-- canonicalises), and D055 says the answer is to pick one and make the
-- backends conform, not to let the meaning vary by backend.
------------------------------------------------------------------------

fadd-semM : TargetNum → M.⟦ Float * Float ⟧ → M.⟦ Float ⟧
fadd-semM tn (a , b) = FA.fadd (float-format tn) a b

fsub-semM : TargetNum → M.⟦ Float * Float ⟧ → M.⟦ Float ⟧
fsub-semM tn (a , b) = FA.fsub (float-format tn) a b

fmul-semM : TargetNum → M.⟦ Float * Float ⟧ → M.⟦ Float ⟧
fmul-semM tn (a , b) = FA.fmul (float-format tn) a b

-- | Division. TOTAL like its integer sibling (D055) — `x/0` is a signed
-- infinity and `0/0` the canonical NaN — so there is no guard and no second
-- shape; `FA.fdiv` carries the sticky bit that makes the quotient correctly
-- rounded, and nothing above this line has to know about it.
fdiv-semM : TargetNum → M.⟦ Float * Float ⟧ → M.⟦ Float ⟧
fdiv-semM tn (a , b) = FA.fdiv (float-format tn) a b

-- | `Int` → `Float` (D125). The word is read at its SIGNED value — `W.toℤ`,
-- the target's width — and then rounded by the same `roundB` every float
-- result goes through. Reading it unsigned would make `-1` convert to
-- `2^64 - 1`, which is the `absℤ` bug this branch already found once.
i2f-semM : TargetNum → M.⟦ Int ⟧ → M.⟦ Float ⟧
i2f-semM tn w = FA.i2f (float-format tn) (W.toℤ tn w)

-- | Division and remainder (D055): TOTAL over `Word`, RISC-V's defined results
-- (`x / 0`, `MIN / -1`), no trap — `Word.Width._/ˢ_`/`_%ˢ_`. These were
-- postulated placeholders "pending a division-by-zero policy"; D055 is that
-- policy, and the arith block's own meaning (`block-semM`) already read it.
div-semM : TargetNum → M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
div-semM tn (a , b) = W._/ˢ_ tn a b

mod-semM : TargetNum → M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
mod-semM tn (a , b) = W._%ˢ_ tn a b

------------------------------------------------------------------------
-- The primitives
------------------------------------------------------------------------

data ArithPrim : Type → Type → Set where
  p-add p-sub p-mul p-div p-mod : ArithPrim (Int * Int) Int
  p-neg                         : ArithPrim Int Int
  p-fadd p-fsub p-fmul p-fdiv   : ArithPrim (Float * Float) Float
  p-i2f                         : ArithPrim Int Float

primSem : ∀ {A B} → ArithPrim A B → TargetNum → M.⟦ A ⟧ → M.⟦ B ⟧ᵍ
primSem p-add  = add-semM
primSem p-sub  = sub-semM
primSem p-mul  = mul-semM
primSem p-div  = div-semM
primSem p-mod  = mod-semM
primSem p-neg  = neg-semM
primSem p-fadd = fadd-semM
primSem p-fsub = fsub-semM
primSem p-fmul = fmul-semM
primSem p-fdiv = fdiv-semM
primSem p-i2f  = i2f-semM
