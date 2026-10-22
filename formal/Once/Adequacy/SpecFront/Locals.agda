-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Locals — the compiler's local variables as the
-- Spec's (plan 0.121 §3.6, F4).
--
-- The compiler keeps its locals twice — their names (innermost first) and
-- the de Bruijn context its derivations are indexed by — and the Spec once
-- (`Locals`, a name and a type per variable). `LR` relates the two, type by
-- type (`TyR`). A name the compiler finds is the Spec's variable at the same
-- index (`lk-R`); a name it does not find is bound by no enclosing binder
-- (`lk-out`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Once.Spec.Type as ST
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Name using (CanonicalName)
import Once.Spec.Core.Syntax as SC

module Once.Adequacy.SpecFront.Locals
  (Σ : Signature) {s : ℕ} (S′ : SC.Defs s) (nm : Fin s → CanonicalName) {m : ℕ} (Δ : ST.KCtx m) where

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

import Once.Spec.Grade as LG
import Once.Internal.Context as LC
import Once.Spec.Context as SCx
open import Once.Internal.Context using (svar)
open import Once.Internal.Typing.Scope using (Binding; lookupLocal-go; lookupLocal-at; lookupLocal-next)
open Binding using (name)
import Once.Spec.Surface.Typing Σ S′ nm as SU
open SU using (Locals; ∅; _▹_∶_)
open import Once.Adequacy.SpecCore.Type using (TyR)

-- The names the compiler's locals bind.
names : List (Binding m) → List String
names = map name

data LR : ∀ {n} → List (Binding m) → LC.Ctx m n → Locals m n → Set where
  lr-∅ : LR [] LC.∅ ∅
  lr-▸ : ∀ {n} {Γn} {Γd : LC.Ctx m n} {L b A A′} → LR Γn Γd L → TyR Δ A A′
       → LR (b ∷ Γn) (Γd SCx.▸ A) (L ▹ name b ∶ A′)

private
  -- the index a lookup found
  idx : ∀ {n} {Γd : LC.Ctx m n} → Maybe (Σ[ A ∈ _ ] Σ[ Ψ ∈ _ ] LC.SVar Γd Ψ A) → Maybe (Fin n)
  idx nothing                 = nothing
  idx (just (_ , _ , svar i)) = just i

  zero≢suc : ∀ {n} {i : Fin n} → zero ≡ suc i → ⊥
  zero≢suc ()

  suc-inj : ∀ {n} {i j : Fin n} → suc i ≡ suc j → i ≡ j
  suc-inj refl = refl

  next-zero : ∀ {n} {Γd : LC.Ctx m n} {B} (r : Maybe (Σ[ A ∈ _ ] Σ[ Ψ ∈ _ ] LC.SVar Γd Ψ A))
            → lookupLocal-next {B = B} r ≡ just (LC.lookup (Γd SCx.▸ B) zero , LC.singleUse zero LG.One , svar zero) → ⊥
  next-zero nothing ()
  next-zero (just (_ , _ , svar j)) e = zero≢suc (sym (just-injective (cong idx e)))

  next-suc : ∀ {n} {Γd : LC.Ctx m n} {B} (r : Maybe (Σ[ A ∈ _ ] Σ[ Ψ ∈ _ ] LC.SVar Γd Ψ A)) (i : Fin n)
           → lookupLocal-next {B = B} r ≡ just (LC.lookup (Γd SCx.▸ B) (suc i) , LC.singleUse (suc i) LG.One , svar (suc i))
           → r ≡ just (LC.lookup Γd i , LC.singleUse i LG.One , svar i)
  next-suc nothing i ()
  next-suc {Γd = Γd} (just (_ , _ , svar j)) i e =
    cong (λ k → just (LC.lookup Γd k , LC.singleUse k LG.One , svar k)) (suc-inj (just-injective (cong idx e)))

-- A name the compiler finds is the Spec's variable at that index, at a
-- related type.
lk-R : ∀ {n x} {Γn} {Γd : LC.Ctx m n} {L} → LR Γn Γd L → (i : Fin n)
     → lookupLocal-go x Γn Γd ≡ just (LC.lookup Γd i , LC.singleUse i LG.One , svar i)
     → Σ[ A′ ∈ ST.Ty m ] (TyR Δ (LC.lookup Γd i) A′ × SU._∋_⦂_at_ L x A′ i)
lk-at : ∀ {n x} {b} {Γn} {Γd : LC.Ctx m n} {L A A′} → LR Γn Γd L → TyR Δ A A′ → (i : Fin (ℕ.suc n))
      → (d : Dec (x ≡ name b))
      → lookupLocal-at x b Γn Γd {B = A} d ≡ just (LC.lookup (Γd SCx.▸ A) i , LC.singleUse i LG.One , svar i)
      → Σ[ A″ ∈ ST.Ty m ] (TyR Δ (LC.lookup (Γd SCx.▸ A) i) A″ × SU._∋_⦂_at_ (L ▹ name b ∶ A′) x A″ i)
lk-R lr-∅ () eq
lk-R {x = x} (lr-▸ {b = b} lr ra) i eq = lk-at lr ra i (x ≟ name b) eq
lk-at {b = b} {L = L} {A′ = A′} lr ra zero (yes e) eq = A′ , ra , subst (λ y → SU._∋_⦂_at_ (L ▹ name b ∶ A′) y A′ zero) (sym e) SU.here
lk-at lr ra (suc i) (yes e) eq = ⊥-elim (zero≢suc (just-injective (cong idx eq)))
lk-at {x = x} {Γn = Γn} {Γd} lr ra zero (no ¬e) eq = ⊥-elim (next-zero (lookupLocal-go x Γn Γd) eq)
lk-at {x = x} {Γn = Γn} {Γd} lr ra (suc i) (no ¬e) eq = past (lk-R lr i (next-suc (lookupLocal-go x Γn Γd) i eq))
  where
    past : _ → _
    past (A″ , r , m) = A″ , r , SU.there ¬e m

private
  next-just : ∀ {n} {Γd : LC.Ctx m n} {B} (r : Maybe (Σ[ A ∈ _ ] Σ[ Ψ ∈ _ ] LC.SVar Γd Ψ A)) {r″}
            → lookupLocal-next {B = B} r ≡ just r″ → Σ[ r′ ∈ _ ] (r ≡ just r′)
  next-just nothing ()
  next-just (just r′) e = r′ , refl

  next-nothing : ∀ {n} {Γd : LC.Ctx m n} {B} (r : Maybe (Σ[ A ∈ _ ] Σ[ Ψ ∈ _ ] LC.SVar Γd Ψ A))
               → lookupLocal-next {B = B} r ≡ nothing → r ≡ nothing
  next-nothing nothing               e = refl
  next-nothing (just (_ , _ , svar i)) ()

-- A name the compiler finds is bound by an enclosing binder…
lk-in : ∀ {n x} Γn {Γd : LC.Ctx m n} {r} → lookupLocal-go x Γn Γd ≡ just r → x ∈ names Γn
lk-in-at : ∀ {n x} b Γn {Γd : LC.Ctx m n} {B} {r} (d : Dec (x ≡ name b))
         → lookupLocal-at x b Γn Γd {B = B} d ≡ just r → x ∈ names (b ∷ Γn)
lk-in []       {LC.∅}         ()
lk-in []       {Γd SCx.▸ _} ()
lk-in (b ∷ Γn) {LC.∅}         ()
lk-in {x = x} (b ∷ Γn) {Γd SCx.▸ B} e = lk-in-at b Γn (x ≟ name b) e
lk-in-at b Γn (yes e) _ = here e
lk-in-at {x = x} b Γn {Γd} (no _) e = there (lk-in Γn (proj₂ (next-just (lookupLocal-go x Γn Γd) e)))

-- …and a name it does not find is bound by none.
lk-out : ∀ {n x} {Γn} {Γd : LC.Ctx m n} {L} → LR Γn Γd L → x ∈ names Γn → lookupLocal-go x Γn Γd ≡ nothing → ⊥
lk-out-at : ∀ {n x} {b} {Γn} {Γd : LC.Ctx m n} {L B} → LR Γn Γd L → x ∈ names (b ∷ Γn) → (d : Dec (x ≡ name b))
          → lookupLocal-at x b Γn Γd {B = B} d ≡ nothing → ⊥
lk-out lr-∅ () e
lk-out {x = x} (lr-▸ {b = b} lr ra) m e = lk-out-at lr m (x ≟ name b) e
lk-out-at lr m (yes _) ()
lk-out-at lr (here e) (no ¬e) _ = ¬e e
lk-out-at {x = x} {Γn = Γn} {Γd} lr (there m) (no _) e = lk-out lr m (next-nothing (lookupLocal-go x Γn Γd) e)
