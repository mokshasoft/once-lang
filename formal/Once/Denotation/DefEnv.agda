-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.DefEnv — plan 0.103 phase 1c: the ENVIRONMENT of a
-- telescope of definitions.
--
-- A reference to a ground telescope entry is a variable of the context
-- (`t-var-poly-instantiate-infer`, no body premise): its body is typed ONCE,
-- at the declaration (`Spec.Module.PolysTyped`). Its meaning is therefore
-- read from an environment holding one datum per telescope position, and a
-- reference looks it up along exactly the path `lookupPolyPrefix` takes.
--
-- The environment is generic in what it holds (`F schema`): the meaning of
-- the entry, its realized term, or the relatedness of the two. The tail at a
-- found entry is the environment of that entry's prefix, where its body (and
-- a non-ground check-mode use's body) is interpreted.
------------------------------------------------------------------------

module Once.Denotation.DefEnv where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
import Data.String.Properties as StrProp
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (PolyType)
open import Once.TypeCheck.Classify using (PolyCtx; lookupPolyPrefix)
open import Once.TypeCheck.Raw using (RawExpr)

DefEnvOf : (PolyType → Set) → PolyCtx → Set
DefEnvOf F []                    = ⊤
DefEnvOf F ((_ , s , _) ∷ rest)  = F s × DefEnvOf F rest

-- The head entry, transported along the lookup's answer.
defAt-found : ∀ {F : PolyType → Set} {s′ s : PolyType} {b′ b : RawExpr} {rest prefix : PolyCtx}
  → just (s′ , b′ , rest) ≡ just (s , b , prefix) → F s′ → F s
defAt-found refl e = e

tailAt-found : ∀ {F : PolyType → Set} {s′ s : PolyType} {b′ b : RawExpr} {rest prefix : PolyCtx}
  → just (s′ , b′ , rest) ≡ just (s , b , prefix) → DefEnvOf F rest → DefEnvOf F prefix
tailAt-found refl ρ = ρ

-- The entry a reference finds.
defAt : ∀ {F : PolyType → Set} (polys : PolyCtx) (x : String) {s b prefix}
  → DefEnvOf F polys → lookupPolyPrefix polys x ≡ just (s , b , prefix) → F s
defAt [] x _ ()
defAt ((n , s′ , b′) ∷ rest) x (e , ρ) lp with StrProp._≟_ n x
... | yes _ = defAt-found lp e
... | no _  = defAt rest x ρ lp

-- The environment of the found entry's prefix.
tailAt : ∀ {F : PolyType → Set} (polys : PolyCtx) (x : String) {s b prefix}
  → DefEnvOf F polys → lookupPolyPrefix polys x ≡ just (s , b , prefix) → DefEnvOf F prefix
tailAt [] x _ ()
tailAt ((n , s′ , b′) ∷ rest) x (e , ρ) lp with StrProp._≟_ n x
... | yes _ = tailAt-found lp ρ
... | no _  = tailAt rest x ρ lp

------------------------------------------------------------------------
-- A property of paired environments, entrywise (e.g. "the meaning of the
-- entry is related to the meaning of its realized term").
------------------------------------------------------------------------

DefEnvAll : ∀ {F₁ F₂ : PolyType → Set} (R : ∀ s → F₁ s → F₂ s → Set)
  (polys : PolyCtx) → DefEnvOf F₁ polys → DefEnvOf F₂ polys → Set
DefEnvAll R []                   _          _          = ⊤
DefEnvAll R ((_ , s , _) ∷ rest) (e₁ , ρ₁) (e₂ , ρ₂) = R s e₁ e₂ × DefEnvAll R rest ρ₁ ρ₂

defAt-all : ∀ {F₁ F₂ : PolyType → Set} {R : ∀ s → F₁ s → F₂ s → Set}
  (polys : PolyCtx) (x : String) {s b prefix} {ρ₁ : DefEnvOf F₁ polys} {ρ₂ : DefEnvOf F₂ polys}
  → DefEnvAll R polys ρ₁ ρ₂ → (lp : lookupPolyPrefix polys x ≡ just (s , b , prefix))
  → R s (defAt polys x ρ₁ lp) (defAt polys x ρ₂ lp)
defAt-all [] x _ ()
defAt-all {R = R} ((n , s′ , b′) ∷ rest) x {s} {b} {prefix} {e₁ , ρ₁} {e₂ , ρ₂} (r , rs) lp
  with StrProp._≟_ n x
... | yes _ = found lp
  where
    found : (lp′ : just (s′ , b′ , rest) ≡ just (s , b , prefix))
          → R s (defAt-found {F = _} lp′ e₁) (defAt-found {F = _} lp′ e₂)
    found refl = r
... | no _ = defAt-all rest x rs lp

tailAt-all : ∀ {F₁ F₂ : PolyType → Set} {R : ∀ s → F₁ s → F₂ s → Set}
  (polys : PolyCtx) (x : String) {s b prefix} {ρ₁ : DefEnvOf F₁ polys} {ρ₂ : DefEnvOf F₂ polys}
  → DefEnvAll R polys ρ₁ ρ₂ → (lp : lookupPolyPrefix polys x ≡ just (s , b , prefix))
  → DefEnvAll R prefix (tailAt polys x ρ₁ lp) (tailAt polys x ρ₂ lp)
tailAt-all [] x _ ()
tailAt-all {R = R} ((n , s′ , b′) ∷ rest) x {s} {b} {prefix} {e₁ , ρ₁} {e₂ , ρ₂} (r , rs) lp
  with StrProp._≟_ n x
... | yes _ = found lp
  where
    found : (lp′ : just (s′ , b′ , rest) ≡ just (s , b , prefix))
          → DefEnvAll R prefix (tailAt-found {F = _} lp′ ρ₁) (tailAt-found {F = _} lp′ ρ₂)
    found refl = rs
... | no _ = tailAt-all rest x rs lp
