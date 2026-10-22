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
-- computation at each application (`abi`, related step for step — plan 0.119
-- D5 — using that the body's run is related to itself). The two agree when
-- that computation is pure, which `TeleWalk` supplies.
--
-- Also: a lookup skips an entry of another name, and finds its own.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

open import Once.Internal.Trace using (FFIAnswers)

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
open import Once.Spec.Grade using (mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_)
open import Once.Internal.Type using (μ-type; ν-type)
open import Once.IR using (IR)
open import Once.IRTy using (IRTy; ⌊_⌋; _≟IRTy_)
open import Once.Spec.Name using (CanonicalName; bare)
open import Once.CanonicalName using (_≟ᶜ_)
open import Once.IR.Ref using (refIR)
import Once.Compile as C
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_)
open T∞ using (force)
open import Once.Denotation.TraceMonadInfLaws using (RelS; relS-ret)
open import Once.Denotation.ValueRel using (RelD; RelS-assocˡ; retargetˡ)
open import Once.Denotation.EvalRel using (eval-rel; table-self)
open import Once.IRTy using (⌈_⌉)
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
abiT : (U : Type) → T∞ ⟦ ⌊ U ⌋ ⟧ᴰᴵ → T∞ ⟦ ⌊ U ⌋ ⟧ᴰᴵ
abiT (A ⇒[ mk-kind Zero π ] B) M = return∞ (λ u → M >>=∞ λ c → c u)
abiT (A ⇒[ mk-kind One  π ] B) M = return∞ (λ a → M >>=∞ λ c → c a)
abiT (A ⇒[ mk-kind Many π ] B) M = return∞ (λ a → M >>=∞ λ c → c a)
abiT Unit         M = M
abiT Void         M = M
abiT (A * B)      M = M
abiT (A + B)      M = M
abiT (μ-type F)   M = M
abiT (ν-type F π) M = M
abiT Int          M = M
abiT Float        M = M
abiT (rigid k i)  M = M

-- The direct-call form (`directCallIR`) of an arrow entry, run on an argument:
-- the closure its body computes, applied to it — related to any run related to
-- the body's, applied to a related argument.
uncurry-app : ∀ {D E : IRTy} (ρ : CallEnv) (ir : IR Once.IRTy.Unit (D Once.IRTy.⇛ E)) {n : T∞ ⟦ D Once.IRTy.⇛ E ⟧ᴰᴵ}
            → RelS (RelD ⌈ D Once.IRTy.⇛ E ⌉) (evalᴰ fmt ρ ir tt) n
            → ∀ {a a′} → RelD ⌈ D ⌉ a a′
            → RelS (RelD ⌈ E ⌉) (evalᴰ fmt ρ (IR.apply IR.∘ IR.⟨ ir IR.∘ IR.terminal , IR.id ⟩) a) (n >>=∞ λ c → c a′)
uncurry-app ρ ir h ra = retargetˡ refl (RelS-assocˡ h (λ rc → retargetˡ refl (rc ra)))

-- An entry's body evaluated in the rest of the table is related to itself.
self : ∀ {D E : IRTy} (es : List IRFun) (ir : IR D E) {a a′} → RelD ⌈ D ⌉ a a′
     → RelS (RelD ⌈ E ⌉) (evalᴰ fmt (tableEnv fmt φ es) ir a) (evalᴰ fmt (tableEnv fmt φ es) ir a′)
self es ir r = eval-rel fmt (table-self fmt φ es) ir r

-- THE ABI ROUND TRIP: a reference to the head entry, compiled from `ir`, is
-- related to `ir`'s computation in the rest of the table, read through `abiT`.
abi : ∀ (U : Type) (x : _) (es : List IRFun) (ir : IR ⌊ Unit {0} ⌋ ⌊ U ⌋)
    → RelS (RelD ⌈ ⌊ U ⌋ ⌉) (evalᴰ fmt (tableEnv fmt φ (irFunOf (C.mkCompiledFun (bare x) _ U ir) ∷ es)) (refIR U (bare x)) tt)
                            (abiT U (evalᴰ fmt (tableEnv fmt φ es) ir tt))
abi (A ⇒[ mk-kind Zero π ] B) x es ir =
  relS-ret λ {u} ru → retargetˡ (cong force (tableEnv-hit (bare x) _ _ _ es u)) (uncurry-app (tableEnv fmt φ es) ir (self es ir tt) ru)
abi (A ⇒[ mk-kind One π ] B) x es ir =
  relS-ret λ {a} ra → retargetˡ (cong force (tableEnv-hit (bare x) _ _ _ es a)) (uncurry-app (tableEnv fmt φ es) ir (self es ir tt) ra)
abi (A ⇒[ mk-kind Many π ] B) x es ir =
  relS-ret λ {a} ra → retargetˡ (cong force (tableEnv-hit (bare x) _ _ _ es a)) (uncurry-app (tableEnv fmt φ es) ir (self es ir tt) ra)
abi Unit         x es ir = retargetˡ (cong force (tableEnv-hit (bare x) _ _ ir es tt)) (self es ir {tt} {tt} tt)
abi Void         x es ir = retargetˡ (cong force (tableEnv-hit (bare x) _ _ ir es tt)) (self es ir {tt} {tt} tt)
abi (A * B)      x es ir = retargetˡ (cong force (tableEnv-hit (bare x) _ _ ir es tt)) (self es ir {tt} {tt} tt)
abi (A + B)      x es ir = retargetˡ (cong force (tableEnv-hit (bare x) _ _ ir es tt)) (self es ir {tt} {tt} tt)
abi (μ-type F)   x es ir = retargetˡ (cong force (tableEnv-hit (bare x) _ _ ir es tt)) (self es ir {tt} {tt} tt)
abi (ν-type F π) x es ir = retargetˡ (cong force (tableEnv-hit (bare x) _ _ ir es tt)) (self es ir {tt} {tt} tt)
abi Int          x es ir = retargetˡ (cong force (tableEnv-hit (bare x) _ _ ir es tt)) (self es ir {tt} {tt} tt)
abi Float        x es ir = retargetˡ (cong force (tableEnv-hit (bare x) _ _ ir es tt)) (self es ir {tt} {tt} tt)
abi (rigid k i)  x es ir = retargetˡ (cong force (tableEnv-hit (bare x) _ _ ir es tt)) (self es ir {tt} {tt} tt)
