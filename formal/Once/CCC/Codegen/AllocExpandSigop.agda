-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandSigop — a SigOp under the renaming (D468, 3c3b).
--
-- A SigOp reads its argument through Input1 (a register value, or a pointer to
-- its words) and writes its answer at Output's location. A typed read that the
-- primitive run makes succeed reads held cells, and the expanded run's read at
-- the renamed location reads the same value; the answer's words are literals,
-- which the renaming fixes.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandSigop {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.Spec.Type using (Ty; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; var)
open import Once.Type using (fits-int; fits-float)
open import Once.Semantics.Machine using (module Value)
open Value using (⟦_⟧)
open import Once.CCC.Codegen.AllocExpandRen {FS} using (ref-of; rhl; rloc; rv)
open import Once.CCC.Codegen.AllocExpandStep {FS} using (module L; rhl-off)
open MemOps {FS} using (readLoc)
open AbstractExec {FS} using (readTyped; readTyped-int; readTyped-float; readTyped-sum; combine-typed; tsize)

rloc-off : ∀ ρ (loc : ValueLocation FS) k → rloc ρ (offsetLoc loc k) ≡ offsetLoc (rloc ρ loc) k
rloc-off ρ (AtStack f j)  k = refl
rloc-off ρ (AtDynamic hl) k = cong AtDynamic (rhl-off ρ hl k)

rloc-suc : ∀ ρ (loc : ValueLocation FS) → rloc ρ (sucLoc loc) ≡ sucLoc (rloc ρ loc)
rloc-suc ρ (AtStack f j)                      = refl
rloc-suc ρ (AtDynamic (heap-loc r o))         = refl

module _ (ρ : ℕ → ℕ) (Lv : ℕ → Set) (inj : ∀ r r′ → Lv r → Lv r′ → ρ r ≡ ρ r′ → r ≡ r′)
         {s t : LocState FS} (R : L.LRel ρ Lv inj s t) where

  -- a cell holding a value, at its renamed location
  cell-rel : ∀ loc v → readLoc s loc ≡ just v → readLoc t (rloc ρ loc) ≡ just (rv ρ v)
  cell-rel (AtStack f k)  v e = trans (L.LRel.l-stack R f k) (cong (Data.Maybe.map (rv ρ)) e)
  cell-rel (AtDynamic hl) v e = L.LRel.l-heap R hl v (L.LRel.l-live R hl v e) e

  private
    int-inv : ∀ mv {a} → readTyped-int mv ≡ just a → mv ≡ just (SV-Lit fits-int a)
    int-inv (just (SV-Lit fits-int v)) refl = refl
    int-inv (just (SV-Lit fits-float _)) ()
    int-inv (just (SV-Ptr _)) ()
    int-inv (just (SV-Tag _)) ()
    int-inv (just (SV-Code _)) ()
    int-inv nothing ()

    float-inv : ∀ mv {a} → readTyped-float mv ≡ just a → mv ≡ just (SV-Lit fits-float a)
    float-inv (just (SV-Lit fits-float v)) refl = refl
    float-inv (just (SV-Lit fits-int _)) ()
    float-inv (just (SV-Ptr _)) ()
    float-inv (just (SV-Tag _)) ()
    float-inv (just (SV-Code _)) ()
    float-inv nothing ()

    pair-inv : ∀ {A B : Ty 0} (ma : Maybe ⟦ A ⟧) (mb : Maybe ⟦ B ⟧) {p} → combine-typed ma mb ≡ just p
             → (ma ≡ just (proj₁ p)) × (mb ≡ just (proj₂ p))
    pair-inv (just a) (just b) refl = refl , refl
    pair-inv (just a) nothing ()
    pair-inv nothing  _       ()

  -- ★ a typed read the primitive makes succeed, at the renamed location
  read-rel : ∀ (A : Ty 0) loc {a} → readTyped A loc s ≡ just a → readTyped A (rloc ρ loc) t ≡ just a
  read-rel Unit loc e = e
  read-rel Int loc e =
    trans (cong readTyped-int (cell-rel loc _ (int-inv (readLoc s loc) e))) refl
  read-rel Float loc e =
    trans (cong readTyped-float (cell-rel loc _ (float-inv (readLoc s loc) e))) refl
  read-rel (A * B) loc {a , b} e =
    trans (cong₂′ (read-rel A loc (proj₁ inv))
                  (trans (cong (λ l → readTyped B l t) (sym (rloc-off ρ loc (tsize A)))) (read-rel B (offsetLoc loc (tsize A)) (proj₂ inv))))
          refl
    where
      inv = pair-inv (readTyped A loc s) (readTyped B (offsetLoc loc (tsize A)) s) e
      cong₂′ : ∀ {ma mb} → ma ≡ just a → mb ≡ just b → combine-typed {A} {B} ma mb ≡ just (a , b)
      cong₂′ refl refl = refl
  read-rel (A + B) loc {x} e = sum (readLoc s loc) refl e
    where
      sl = sucLoc loc
      sum : ∀ mt → readLoc s loc ≡ mt
          → readTyped-sum (λ _ → readTyped A sl s) (λ _ → readTyped B sl s) mt (readLoc s sl) ≡ just x
          → readTyped-sum (λ _ → readTyped A (sucLoc (rloc ρ loc)) t) (λ _ → readTyped B (sucLoc (rloc ρ loc)) t)
                          (readLoc t (rloc ρ loc)) (readLoc t (sucLoc (rloc ρ loc))) ≡ just x
      sum (just (SV-Tag zero)) et e′ =
        trans (cong (λ m → readTyped-sum (λ _ → readTyped A (sucLoc (rloc ρ loc)) t) (λ _ → readTyped B (sucLoc (rloc ρ loc)) t) m (readLoc t (sucLoc (rloc ρ loc))))
                    (cell-rel loc (SV-Tag zero) et))
              (inl-of (readTyped A sl s) refl e′)
        where
          inl-of : ∀ ma → readTyped A sl s ≡ ma → Data.Maybe.map inj₁ ma ≡ just x
                 → Data.Maybe.map inj₁ (readTyped A (sucLoc (rloc ρ loc)) t) ≡ just x
          inl-of (just a) ea refl = cong (Data.Maybe.map inj₁) (trans (cong (λ l → readTyped A l t) (sym (rloc-suc ρ loc))) (read-rel A sl ea))
          inl-of nothing  ea ()
      sum (just (SV-Tag (suc zero))) et e′ =
        trans (cong (λ m → readTyped-sum (λ _ → readTyped A (sucLoc (rloc ρ loc)) t) (λ _ → readTyped B (sucLoc (rloc ρ loc)) t) m (readLoc t (sucLoc (rloc ρ loc))))
                    (cell-rel loc (SV-Tag (suc zero)) et))
              (inr-of (readTyped B sl s) refl e′)
        where
          inr-of : ∀ mb → readTyped B sl s ≡ mb → Data.Maybe.map inj₂ mb ≡ just x
                 → Data.Maybe.map inj₂ (readTyped B (sucLoc (rloc ρ loc)) t) ≡ just x
          inr-of (just b) eb refl = cong (Data.Maybe.map inj₂) (trans (cong (λ l → readTyped B l t) (sym (rloc-suc ρ loc))) (read-rel B sl eb))
          inr-of nothing  eb ()
      sum (just (SV-Tag (suc (suc _)))) et ()
      sum (just (SV-Ptr _)) et ()
      sum (just (SV-Lit _ _)) et ()
      sum (just (SV-Code _)) et ()
      sum nothing et ()
  read-rel Void loc ()
  read-rel (_ ⇒[ _ ] _) loc ()
  read-rel (μ _) loc ()
  read-rel (ν _ _) loc ()

  open AbstractExec {FS} using (decode-at)
  open import Once.Spec.Type using (Base; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; ∅ₖ)

  -- ★ the argument the primitive decodes, decoded alike from the renamed register
  decode-rel : ∀ {A} (b : Base ∅ₖ A) v {a} → decode-at b v s ≡ just a → decode-at b (rv ρ v) t ≡ just a
  decode-rel b-Unit  v e = e
  decode-rel b-Int   (SV-Lit fits-int _)   e = e
  decode-rel b-Int   (SV-Lit fits-float _) ()
  decode-rel b-Int   (SV-Ptr _) ()
  decode-rel b-Int   (SV-Tag _) ()
  decode-rel b-Int   (SV-Code _) ()
  decode-rel b-Float (SV-Lit fits-float _) e = e
  decode-rel b-Float (SV-Lit fits-int _) ()
  decode-rel b-Float (SV-Ptr _) ()
  decode-rel b-Float (SV-Tag _) ()
  decode-rel b-Float (SV-Code _) ()
  decode-rel {A} (b-* _ _) (SV-Ptr loc) e = read-rel A loc e
  decode-rel (b-* _ _) (SV-Lit _ _) ()
  decode-rel (b-* _ _) (SV-Tag _) ()
  decode-rel (b-* _ _) (SV-Code _) ()
  decode-rel {A} (b-+ _ _) (SV-Ptr loc) e = read-rel A loc e
  decode-rel (b-+ _ _) (SV-Lit _ _) ()
  decode-rel (b-+ _ _) (SV-Tag _) ()
  decode-rel (b-+ _ _) (SV-Code _) ()
  decode-rel b-Void v ()
