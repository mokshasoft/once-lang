-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.TableCall — plan 0.103 6b, leg C.3: A CALL OF A TABLE ENTRY.
--
-- A reference to a module entry is `refIR U f`, a call of the table entry `f`
-- (D245, D246). The entry is its definition's DIRECT-CALL form
-- (`directCallIR`): a non-arrow definition as it is, an arrow one uncurried to
-- `apply ∘ ⟨ ir ∘ terminal , id ⟩`. So a reference means the body's
-- computation, and at an arrow it means the closure that RUNS the body's
-- computation at each application (`abi`). The two agree when that
-- computation is pure, which `TeleWalk` supplies.
--
-- Also: a lookup skips an entry of another name, and finds its own.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

open import Once.SigOp.Info using (FFIAnswers)

-- Plan 0.105: over the interpretation's FFI half `φ`, which the table's call
-- environment carries.
module Once.Adequacy.TableCall (fmt : TargetNum) (φ : FFIAnswers) where

open import Data.List using (List; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans)

open import Once.Postulates using (extensionality)
open import Once.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; mk-kind; Zero; One; Many;
  μ-type; ν-type; rigid)
open import Once.IR using (IR)
open import Once.IRTy using (IRTy; ⌊_⌋; _≟IRTy_)
open import Once.CanonicalName using (CanonicalName; bare; _≟ᶜ_)
open import Once.IR.Ref using (refIR)
import Once.Compile as C
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.Denotation.TraceMonadLaws using (>>=T-assoc)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ)
open import Once.Denotation.Program using (IRFun; irFun; tableEnv; tableCalls)
open Once.Denotation.Program.IRFun using (fname)
open import Once.Compile using (irFunOf)

------------------------------------------------------------------------
-- Lookup
------------------------------------------------------------------------

tableEnv-skip : ∀ (e : IRFun) (es : List IRFun) {f : CanonicalName} {A B : IRTy} → fname e ≢ f
              → ∀ (a : ⟦ A ⟧ᴰᴵ) → tableCalls fmt φ (e ∷ es) f A B a ≡ tableCalls fmt φ es f A B a
tableEnv-skip e es {f} {A} {B} ne a with fname e ≟ᶜ f
... | yes p = ⊥-elim (ne p)
... | no _  = refl

tableEnv-hit : ∀ (f : CanonicalName) (D E : IRTy) (body : IR D E) (es : List IRFun) (a : ⟦ D ⟧ᴰᴵ)
             → tableCalls fmt φ (irFun f D E body ∷ es) f D E a ≡ evalᴰ fmt (tableEnv fmt φ es) body a
tableEnv-hit f D E body es a with f ≟ᶜ f | D ≟IRTy D | E ≟IRTy E
... | yes _  | yes refl | yes refl = refl
... | no ¬p  | _        | _        = ⊥-elim (¬p refl)
... | yes _  | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes _  | yes refl | no ¬p    = ⊥-elim (¬p refl)

------------------------------------------------------------------------
-- The direct-call ABI
------------------------------------------------------------------------

-- What a reference to an entry whose body computes `M` means: `M` itself, or,
-- at an arrow, the closure that runs `M` and applies its result.
abiT : (U : Type) → T ⟦ ⌊ U ⌋ ⟧ᴰᴵ → T ⟦ ⌊ U ⌋ ⟧ᴰᴵ
abiT (A ⇒[ mk-kind Zero π ] B) M = returnT (λ u → M >>=T λ c → c u)
abiT (A ⇒[ mk-kind One  π ] B) M = returnT (λ a → M >>=T λ c → c a)
abiT (A ⇒[ mk-kind Many π ] B) M = returnT (λ a → M >>=T λ c → c a)
abiT Unit         M = M
abiT Void         M = M
abiT (A * B)      M = M
abiT (A + B)      M = M
abiT (μ-type F)   M = M
abiT (ν-type F π) M = M
abiT Int          M = M
abiT Float        M = M
abiT (rigid k i)  M = M

-- THE ABI ROUND TRIP: a reference to the head entry, compiled from `ir`, means
-- `ir`'s computation in the rest of the table, read through `abiT`.
-- The direct-call form (`directCallIR`) of an arrow entry, run on an argument:
-- the closure its body computes, applied to it.
uncurry-app : ∀ {D E : IRTy} (ρ : CallEnv) (ir : IR Once.IRTy.Unit (D Once.IRTy.⇛ E)) (a : ⟦ D ⟧ᴰᴵ)
            → evalᴰ fmt ρ (IR.apply IR.∘ IR.⟨ ir IR.∘ IR.terminal , IR.id ⟩) a
              ≡ (evalᴰ fmt ρ ir tt >>=T λ c → c a)
uncurry-app ρ ir a = >>=T-assoc (evalᴰ fmt ρ ir tt) (λ c → returnT (c , a)) (λ p → proj₁ p (proj₂ p))

abi : ∀ (U : Type) (x : _) (es : List IRFun) (ir : IR ⌊ Unit ⌋ ⌊ U ⌋)
    → evalᴰ fmt (tableEnv fmt φ (irFunOf (C.mkCompiledFun (bare x) U ir) ∷ es)) (refIR U (bare x)) tt
      ≡ abiT U (evalᴰ fmt (tableEnv fmt φ es) ir tt)
abi (A ⇒[ mk-kind Zero π ] B) x es ir =
  cong returnT (extensionality λ u →
    trans (tableEnv-hit (bare x) _ _ _ es u) (uncurry-app (tableEnv fmt φ es) ir u))
abi (A ⇒[ mk-kind One π ] B) x es ir =
  cong returnT (extensionality λ a →
    trans (tableEnv-hit (bare x) _ _ _ es a) (uncurry-app (tableEnv fmt φ es) ir a))
abi (A ⇒[ mk-kind Many π ] B) x es ir =
  cong returnT (extensionality λ a →
    trans (tableEnv-hit (bare x) _ _ _ es a) (uncurry-app (tableEnv fmt φ es) ir a))
abi Unit         x es ir = tableEnv-hit (bare x) _ _ ir es tt
abi Void         x es ir = tableEnv-hit (bare x) _ _ ir es tt
abi (A * B)      x es ir = tableEnv-hit (bare x) _ _ ir es tt
abi (A + B)      x es ir = tableEnv-hit (bare x) _ _ ir es tt
abi (μ-type F)   x es ir = tableEnv-hit (bare x) _ _ ir es tt
abi (ν-type F π) x es ir = tableEnv-hit (bare x) _ _ ir es tt
abi Int          x es ir = tableEnv-hit (bare x) _ _ ir es tt
abi Float        x es ir = tableEnv-hit (bare x) _ _ ir es tt
abi (rigid k i)  x es ir = tableEnv-hit (bare x) _ _ ir es tt
