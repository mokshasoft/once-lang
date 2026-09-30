-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.TeleEntry — plan 0.103 6b, leg C: A TABLE ENTRY'S CALL
-- MEANS THE ENTRY.
--
-- A reference to a module entry is a call of its table entry (D246), which is
-- the entry's direct-call form (D245, `TableCall.abi`). Relating that to the
-- entry's own meaning takes one side condition at an arrow: the entry's
-- computation is PURE (it returns a closure and emits nothing), because the
-- direct-call form runs it at each application rather than at the reference
-- (`abi-rel`). An FFI entry's contract is (`ffi-entry`).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.TeleEntry (fmt : TargetNum) where

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Postulates using (extensionality)
open import Once.Type using (Type; Unit; Void; Int; Float; Str; Buffer; _*_; _+_; _⇒[_]_; mk-kind; Zero; One; Many;
  μ-type; ν-type; rigid)
open import Once.Functor.Translate using (IsConcrete; con-base; con-fun)
open import Once.IRTy using (⌊_⌋)
open import Once.CanonicalName using (CanonicalName; bare)
open import Once.Res using (returns; rel-returns)
import Once.Surface.Syntax as Srf
open import Once.Surface.Elaborate using (elaborateFull)
import Once.Compile as C
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.TraceMonad using (T; mkT; returnT; _>>=T_; projTrace)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; ⟦_⟧ᴰᴵ; cohᴰ)
open import Once.Denotation.Meaning using (sigOpRefᴰ)
open import Once.Denotation.Program using (IRFun; tableEnv)
open import Once.Adequacy.MeaningRelation fmt using (RelT; RelV; RelT-return)
open import Once.Adequacy.TableCall fmt using (abiT; abi)
open import Once.Adequacy.SourceTrace using (irFunOf)
open import Once.IR.Ref using (refIR)
import Once.Adequacy.MeaningBridge as MB
import Once.Adequacy.SourceFaithful as SF
import Once.Adequacy.FaithfulLemmas as FLm

------------------------------------------------------------------------
-- Purity at an arrow
------------------------------------------------------------------------

PureAt : (U : Type) → T ⟦ U ⟧ᴰ → Set
PureAt (A ⇒[ mk-kind q π ] B) m = Σ-syntax ⟦ A ⇒[ mk-kind q π ] B ⟧ᴰ (λ v → m ≡ returnT v)
PureAt Unit         m = ⊤
PureAt Void         m = ⊤
PureAt (A * B)      m = ⊤
PureAt (A + B)      m = ⊤
PureAt (μ-type F)   m = ⊤
PureAt (ν-type F π) m = ⊤
PureAt Int          m = ⊤
PureAt Float        m = ⊤
PureAt Str          m = ⊤
PureAt Buffer       m = ⊤
PureAt (rigid k i)  m = ⊤

private
  -- A computation related to a pure one is pure, at a related value.
  returns-of : ∀ (U : Type) {v : ⟦ U ⟧ᴰ} (M : T ⟦ U ⟧ᴰ) → RelT U (returnT v) M
             → Σ-syntax ⟦ U ⟧ᴰ (λ v′ → (M ≡ returnT v′) × RelV U v v′)
  returns-of U (mkT tr (returns v′)) rel with proj₂ (rel 0)
  ... | rel-returns rv =
    v′ , cong (λ t → mkT t (returns v′)) (extensionality (λ n → sym (proj₁ (rel n)))) , rv
  returns-of U (mkT tr Once.Res.stopped) rel with proj₂ (rel 0)
  ... | ()

  abi-many : ∀ {X X′ Y Y′ : Set} (e₁ : X ≡ X′) (e₂ : Y ≡ Y′) (M : T (X → T Y))
           → subst T (cong₂ (λ x y → x → T y) e₁ e₂) (returnT (λ a → M >>=T λ c → c a))
             ≡ returnT (λ a′ → subst T (cong₂ (λ x y → x → T y) e₁ e₂) M >>=T λ c′ → c′ a′)
  abi-many refl refl M = refl

  abi-zero : ∀ {Y Y′ : Set} (e₂ : Y ≡ Y′) (M : T (⊤ → T Y))
           → subst T (cong (λ y → ⊤ → T y) e₂) (returnT (λ u → M >>=T λ c → c u))
             ≡ returnT (λ u → subst T (cong (λ y → ⊤ → T y) e₂) M >>=T λ c′ → c′ u)
  abi-zero refl M = refl

-- THE ABI, SEMANTICALLY: a pure entry's reference and its direct call agree.
abi-rel : ∀ (U : Type) (m : T ⟦ U ⟧ᴰ) (M : T ⟦ ⌊ U ⌋ ⟧ᴰᴵ) → PureAt U m
        → RelT U m (subst T (cohᴰ U) M) → RelT U m (subst T (cohᴰ U) (abiT U M))
abi-rel (A ⇒[ mk-kind Zero π ] B) .(returnT v) M (v , refl) rel with returns-of (A ⇒[ mk-kind Zero π ] B) _ rel
... | v′ , eq , rv =
  subst (RelT (A ⇒[ mk-kind Zero π ] B) (returnT v))
        (sym (trans (abi-zero (cohᴰ B) M) (cong (λ M′ → returnT (λ u → M′ >>=T λ c′ → c′ u)) eq)))
        (RelT-return {A ⇒[ mk-kind Zero π ] B} rv)
abi-rel (A ⇒[ mk-kind One π ] B) .(returnT v) M (v , refl) rel with returns-of (A ⇒[ mk-kind One π ] B) _ rel
... | v′ , eq , rv =
  subst (RelT (A ⇒[ mk-kind One π ] B) (returnT v))
        (sym (trans (abi-many (cohᴰ A) (cohᴰ B) M) (cong (λ M′ → returnT (λ a′ → M′ >>=T λ c′ → c′ a′)) eq)))
        (RelT-return {A ⇒[ mk-kind One π ] B} rv)
abi-rel (A ⇒[ mk-kind Many π ] B) .(returnT v) M (v , refl) rel with returns-of (A ⇒[ mk-kind Many π ] B) _ rel
... | v′ , eq , rv =
  subst (RelT (A ⇒[ mk-kind Many π ] B) (returnT v))
        (sym (trans (abi-many (cohᴰ A) (cohᴰ B) M) (cong (λ M′ → returnT (λ a′ → M′ >>=T λ c′ → c′ a′)) eq)))
        (RelT-return {A ⇒[ mk-kind Many π ] B} rv)
abi-rel Unit         m M _ rel = rel
abi-rel Void         m M _ rel = rel
abi-rel (A * B)      m M _ rel = rel
abi-rel (A + B)      m M _ rel = rel
abi-rel (μ-type F)   m M _ rel = rel
abi-rel (ν-type F π) m M _ rel = rel
abi-rel Int          m M _ rel = rel
abi-rel Float        m M _ rel = rel
abi-rel Str          m M _ rel = rel
abi-rel Buffer       m M _ rel = rel
abi-rel (rigid k i)  m M _ rel = rel

------------------------------------------------------------------------
-- An FFI entry
------------------------------------------------------------------------

-- A contract reference is pure (the effect fires at the application).
sigop-pure : ∀ (U : Type) (cn : CanonicalName) (c : IsConcrete U) → PureAt U (sigOpRefᴰ fmt cn c)
sigop-pure (A ⇒[ mk-kind Zero π ] B) cn (con-fun _ _) = _ , refl
sigop-pure (A ⇒[ mk-kind One  π ] B) cn (con-fun _ _) = _ , refl
sigop-pure (A ⇒[ mk-kind Many π ] B) cn (con-fun _ _) = _ , refl
sigop-pure (A ⇒[ mk-kind _ π ] B)    cn (con-base ())
sigop-pure Unit         cn c = tt
sigop-pure Void         cn c = tt
sigop-pure (A * B)      cn c = tt
sigop-pure (A + B)      cn c = tt
sigop-pure (μ-type F)   cn c = tt
sigop-pure (ν-type F π) cn c = tt
sigop-pure Int          cn c = tt
sigop-pure Float        cn c = tt
sigop-pure Str          cn c = tt
sigop-pure Buffer       cn c = tt
sigop-pure (rigid k i)  cn c = tt

-- The call of an FFI entry (its compiled SigOp wrapper) means its contract.
ffi-entry : ∀ (pre : List IRFun) (x : _) (U : Type) (c : IsConcrete U)
  → RelT U (sigOpRefᴰ fmt (bare x) c)
           (subst T (cohᴰ U) (evalᴰ fmt (tableEnv fmt (irFunOf (C.mkCompiledFun (bare x) U
                                  (elaborateFull C.Heap (Srf.sigOp {Γ = Srf.∅} (bare x) c)) true) ∷ pre))
                                (refIR U (bare x)) tt))
ffi-entry pre x U c =
  subst (RelT U (sigOpRefᴰ fmt (bare x) c)) (cong (subst T (cohᴰ U)) (sym (abi U x pre ir)))
    (abi-rel U (sigOpRefᴰ fmt (bare x) c) (evalᴰ fmt ρ ir tt) (sigop-pure U (bare x) c)
      (subst (RelT U (sigOpRefᴰ fmt (bare x) c)) (sym (FLm.T-ext-at fmt ρ (SF.faithful∅ fmt ρ (Srf.sigOp {Γ = Srf.∅} (bare x) c))))
             (MB.sigop-ref-bridge fmt (SD.internalDefs fmt ρ) {Γ = Srf.∅} {A = U} (bare x) c tt)))
  where
    ρ  = tableEnv fmt pre
    ir = elaborateFull C.Heap (Srf.sigOp {Γ = Srf.∅} (bare x) c)
