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

open import Once.Target.Arch using (TargetNum)

open import Once.SigOp.Info using (FFIAnswers)
open import Once.Denotation.TraceMonad using (Interp; pureHalf)

-- Plan 0.105 (D257 amendment 2): in a world `ι` — its signatures and their
-- implementation; the IR reads its pure half.
module Once.Adequacy.TeleEntry (fmt : TargetNum) (ι : Interp) where

φ : FFIAnswers
φ = pureHalf ι

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; mk-kind; Zero; One; Many; pure;
  μ-type; ν-type; rigid)
open import Once.IRTy using (⌊_⌋)
import Once.Surface.Syntax as Srf
import Once.Compile as C
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.TraceMonad using (T; ret; returnT; _>>=T_; rel-ret)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰᴵ; cohᴰ)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ)
open import Once.Adequacy.GradedRelation fmt using (RelGT; RelGV; RelGM; RelGT-return)
open import Once.Adequacy.TableCall fmt φ using (abiT)
import Once.Adequacy.MeaningBridge as MB
import Once.Adequacy.SourceFaithful as SF
import Once.Adequacy.FaithfulLemmas as FLm

private
  -- A computation related to a value returns silently, a related value.
  returns-of : ∀ (U : Type) {v : ⟦ U ⟧ᵛ} (M : T ⟦ U ⟧ᴰ) → RelGT U (returnT v) M
             → Σ-syntax ⟦ U ⟧ᴰ (λ v′ → (M ≡ returnT v′) × RelGV U v v′)
  -- Plan 0.105: a tree related to a `ret` IS a `ret`.
  returns-of U .(ret _) (rel-ret rv) = _ , refl , rv

  abi-many : ∀ {X X′ Y Y′ : Set} (e₁ : X ≡ X′) (e₂ : Y ≡ Y′) (M : T (X → T Y))
           → subst T (cong₂ (λ x y → x → T y) e₁ e₂) (returnT (λ a → M >>=T λ c → c a))
             ≡ returnT (λ a′ → subst T (cong₂ (λ x y → x → T y) e₁ e₂) M >>=T λ c′ → c′ a′)
  abi-many refl refl M = refl

  abi-zero : ∀ {Y Y′ : Set} (e₂ : Y ≡ Y′) (M : T (⊤ → T Y))
           → subst T (cong (λ y → ⊤ → T y) e₂) (returnT (λ u → M >>=T λ c → c u))
             ≡ returnT (λ u → subst T (cong (λ y → ⊤ → T y) e₂) M >>=T λ c′ → c′ u)
  abi-zero refl M = refl

-- THE ABI, SEMANTICALLY: an entry's value and its direct call agree.
abi-rel : ∀ (U : Type) (v : ⟦ U ⟧ᵛ) (M : T ⟦ ⌊ U ⌋ ⟧ᴰᴵ)
        → RelGM pure U v (subst T (cohᴰ U) M) → RelGM pure U v (subst T (cohᴰ U) (abiT U M))
abi-rel (A ⇒[ mk-kind Zero π ] B) v M rel with returns-of (A ⇒[ mk-kind Zero π ] B) _ rel
... | v′ , eq , rv =
  subst (RelGT (A ⇒[ mk-kind Zero π ] B) (returnT v))
        (sym (trans (abi-zero (cohᴰ B) M) (cong (λ M′ → returnT (λ u → M′ >>=T λ c′ → c′ u)) eq)))
        (RelGT-return {A ⇒[ mk-kind Zero π ] B} rv)
abi-rel (A ⇒[ mk-kind One π ] B) v M rel with returns-of (A ⇒[ mk-kind One π ] B) _ rel
... | v′ , eq , rv =
  subst (RelGT (A ⇒[ mk-kind One π ] B) (returnT v))
        (sym (trans (abi-many (cohᴰ A) (cohᴰ B) M) (cong (λ M′ → returnT (λ a′ → M′ >>=T λ c′ → c′ a′)) eq)))
        (RelGT-return {A ⇒[ mk-kind One π ] B} rv)
abi-rel (A ⇒[ mk-kind Many π ] B) v M rel with returns-of (A ⇒[ mk-kind Many π ] B) _ rel
... | v′ , eq , rv =
  subst (RelGT (A ⇒[ mk-kind Many π ] B) (returnT v))
        (sym (trans (abi-many (cohᴰ A) (cohᴰ B) M) (cong (λ M′ → returnT (λ a′ → M′ >>=T λ c′ → c′ a′)) eq)))
        (RelGT-return {A ⇒[ mk-kind Many π ] B} rv)
abi-rel Unit         v M rel = rel
abi-rel Void         v M rel = rel
abi-rel (A * B)      v M rel = rel
abi-rel (A + B)      v M rel = rel
abi-rel (μ-type F)   v M rel = rel
abi-rel (ν-type F π) v M rel = rel
abi-rel Int          v M rel = rel
abi-rel Float        v M rel = rel
abi-rel (rigid k i)  v M rel = rel

