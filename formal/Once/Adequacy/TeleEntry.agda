-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.TeleEntry — plan 0.103 6b, leg C: A TABLE ENTRY'S CALL
-- MEANS THE ENTRY.
--
-- A reference to a module entry is a call of its table entry (D246), which is
-- the entry's direct-call form (D245, `TableCall.abi`). The direct-call form
-- runs the entry's computation at each application rather than at the
-- reference, so the two agree only if that computation is silent and returns
-- a closure (`abi-rel`). D250: that is not a side condition any more — an
-- entry is pure, its meaning is a VALUE, and the relation at `pure` already
-- says the implementation side returns a related value silently.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

open import Once.Lang.Trace using (FFIAnswers)
open import Once.Lang.Trace using (Interp; pureHalf)

-- Plan 0.105 (D257 amendment 2): in a world `ι` — its signatures and their
-- implementation; the IR reads its pure half.
module Once.Adequacy.TeleEntry (fmt : TargetNum) (ι : Interp) where

φ : FFIAnswers
φ = pureHalf ι

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Lang.Type.Grade using (mk-kind; Zero; One; Many; pure)
open import Once.Lang.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; rigid)
open import Once.IRTy using (⌊_⌋)
open import Once.Lang.Trace using (ret)
open import Once.Lang.Iterative using (T∞; return∞; _>>=∞_; bindBlock)
open T∞ using (force)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret; relS-ret)
open RelS using (forceS)
open import Once.Denotation.ValueRel using (retargetˡ; retargetʳ)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; cohᴰ)
open import Once.Lang.Graded using (⟦_⟧ᵛ)
open import Once.Adequacy.GradedRelation fmt using (RelGV; RelGM)
open import Once.Adequacy.TableCall fmt φ using (abiT)

private
  -- A run related to a returned value returns, at once, a related value.
  returns-of : ∀ {X Y} {R : X → Y → Set} {v : X} {t : T∞ Y} → RelS R (return∞ v) t
             → Σ[ y ∈ Y ] (force t ≡ ret (inj₁ y)) × R v y
  returns-of h = inv (forceS h)
    where inv : ∀ {X Y} {R : X → Y → Set} {v : X} {b} → RelSB R (ret (inj₁ v)) b → Σ[ y ∈ Y ] (b ≡ ret (inj₁ y)) × R v y
          inv (s-ret r) = _ , refl , r

  abi-many : ∀ {X X′ Y Y′ : Set} (e₁ : X ≡ X′) (e₂ : Y ≡ Y′) (M : T∞ (X → T∞ Y))
           → subst T∞ (cong₂ (λ x y → x → T∞ y) e₁ e₂) (return∞ (λ a → M >>=∞ λ c → c a))
             ≡ return∞ (λ a′ → subst T∞ (cong₂ (λ x y → x → T∞ y) e₁ e₂) M >>=∞ λ c′ → c′ a′)
  abi-many refl refl M = refl

  abi-zero : ∀ {Y Y′ : Set} (e₂ : Y ≡ Y′) (M : T∞ (⊤ → T∞ Y))
           → subst T∞ (cong (λ y → ⊤ → T∞ y) e₂) (return∞ (λ u → M >>=∞ λ c → c u))
             ≡ return∞ (λ u → subst T∞ (cong (λ y → ⊤ → T∞ y) e₂) M >>=∞ λ c′ → c′ u)
  abi-zero refl M = refl

  ≡ʳ : ∀ {X Y} {R : X → Y → Set} {m : T∞ X} {n n′ : T∞ Y} → n ≡ n′ → RelS R m n′ → RelS R m n
  ≡ʳ refl h = h

-- THE ABI, SEMANTICALLY: an entry's value and its direct call agree. The
-- entry's computation returns a related closure at once (it is pure), so the
-- direct call — which runs it at each application — forces to that closure's
-- application.
abi-rel : ∀ (U : Type) (v : ⟦ U ⟧ᵛ) (M : T∞ ⟦ ⌊ U ⌋ ⟧ᴰᴵ)
        → RelGM pure U v (subst T∞ (cohᴰ U) M) → RelGM pure U v (subst T∞ (cohᴰ U) (abiT U M))
abi-rel (A ⇒[ mk-kind Zero π ] B) v M rel with returns-of rel
... | v′ , eq , (h , d) =
  ≡ʳ (abi-zero (cohᴰ B) M)
     (relS-ret ( retargetʳ (cong (λ l → bindBlock l (λ c′ → c′ _)) eq) h
               , retargetˡ (cong (λ l → bindBlock l (λ c′ → c′ _)) eq) (retargetʳ (cong (λ l → bindBlock l (λ c′ → c′ _)) eq) d) ))
abi-rel (A ⇒[ mk-kind One π ] B) v M rel with returns-of rel
... | v′ , eq , (h , d) =
  ≡ʳ (abi-many (cohᴰ A) (cohᴰ B) M)
     (relS-ret ( (λ rab → retargetʳ (cong (λ l → bindBlock l (λ c′ → c′ _)) eq) (h rab))
               , (λ ra → retargetˡ (cong (λ l → bindBlock l (λ c′ → c′ _)) eq) (retargetʳ (cong (λ l → bindBlock l (λ c′ → c′ _)) eq) (d ra))) ))
abi-rel (A ⇒[ mk-kind Many π ] B) v M rel with returns-of rel
... | v′ , eq , (h , d) =
  ≡ʳ (abi-many (cohᴰ A) (cohᴰ B) M)
     (relS-ret ( (λ rab → retargetʳ (cong (λ l → bindBlock l (λ c′ → c′ _)) eq) (h rab))
               , (λ ra → retargetˡ (cong (λ l → bindBlock l (λ c′ → c′ _)) eq) (retargetʳ (cong (λ l → bindBlock l (λ c′ → c′ _)) eq) (d ra))) ))
abi-rel Unit         v M rel = rel
abi-rel Void         v M rel = rel
abi-rel (A * B)      v M rel = rel
abi-rel (A + B)      v M rel = rel
abi-rel (μ-type F)   v M rel = rel
abi-rel (ν-type F π) v M rel = rel
abi-rel Int          v M rel = rel
abi-rel Float        v M rel = rel
abi-rel (rigid k i)  v M rel = rel
