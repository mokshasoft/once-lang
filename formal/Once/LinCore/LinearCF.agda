-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LinearCF — plan 0.157 S2 step 3 (D6, D500): ★ a program the
-- linearity checker passes is bridged to a core term that copies nothing.
--
--   linear-cf : Linear.sites lc e ≡ [] → CopyFree.CF lc (FromExpr.Lq rs e)
--
-- No warning ⇔ `Linear₀` (`Linear.linear?`) ⇒ the bridge names no `dup` or
-- `bcopy` of cells and no closure owning cells at a lent-called type. By
-- induction beside `Lq`, clause for clause; each place the bridge may copy is
-- a site of the checker:
--   * the split: a `dup` exactly where both shares hold a variable (`sharedIx`);
--   * a read copies out only at a type without cells (`keepRd`'s `flatRd`);
--   * a fork's projections: `splitP` copies exactly where `ov` says;
--   * a closure owning its environment: the checker's `cloSite`, `heldSite`, `mapSite`.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.LinCore.LinearCF (fmt : TargetNum) where

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_; T)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (yes; no; Dec)
import Data.Fin

import Once.Spec.Grade as G
import Once.Spec.Type as ST
open import Once.Spec.Type using (Ty; _⇒[_]_)
import Once.Spec.Context as SC
open import Once.Spec.Context using (Ctx; Usage; []; _∷_; _+ᵘ_; _*ᵘ_; zeroUsage; _⊑ᵘ_; _⊑∷_; singleUse)
open import Once.Spec.Sub using (_<:_)
open import Once.Context using (_⊔ᵘ_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.Arith.SigOp.AsBlock using (as-block)
open import Once.LinCore.PassTr fmt using (dropl)
open import Once.LinCore.FromIR fmt using (⟪_⟫; ⟪⌊⌋⟫-flat; grade)
open import Once.IRTy using (⌊_⌋; ⌊wk₀⌋)
import Once.IRTy as I
open import Once.Spec.Name using (CanonicalName; bare)
open import Once.Type.Concrete using (IsConcrete; con-base; con-fun)
open import Once.Arith.SigOp.Builders using (numInfo; i2f-info; value-info; arrow-info)
open import Once.Spec.Theory using (Has; Sym)
import Once.Spec.Theory as Th
open import Once.Surface.CoerceIR using (VoidFree; voidFree?; erase-eq)
open import Once.Surface.Properties using (erase-arg-usage)
open import Once.Spec.Sub using (sub-void; sub-var; sub-unit; sub-int; sub-float; sub-arr; sub-*; sub-+; sub-μ; sub-ν)
open import Once.Context using (⊑ᵘ-refl)
open import Once.Surface.Map
open import Once.Surface.Syntax

open import Once.LinCore.Core fmt
open import Once.LinCore.FromExpr fmt
open import Once.LinCore.Linear fmt
open import Once.LinCore.CopyFree fmt

------------------------------------------------------------------------
-- 1. Empty site lists.
------------------------------------------------------------------------

++-[] : ∀ {X : Set} (xs : List X) {ys : List X} → xs ++ ys ≡ [] → xs ≡ [] × ys ≡ []
++-[] []      e = refl , e
++-[] (_ ∷ _) ()

map-[] : ∀ (xs : List ℕ) → map suc xs ≡ [] → xs ≡ []
map-[] []      _ = refl
map-[] (_ ∷ _) ()

site-[] : ∀ k (vs : List ℕ) → site k vs ≡ [] → vs ≡ []
site-[] k []      _ = refl
site-[] k (_ ∷ _) ()

ifNil : ∀ (b : Bool) {xs : List ℕ} → (if b then 0 ∷ [] else []) ++ xs ≡ [] → T (not b) × xs ≡ []
ifNil true  ()
ifNil false e = tt , e

ifSite : ∀ (b : Bool) {k} {xs} → (if b then site k xs else []) ≡ [] → T (not b) ⊎ xs ≡ []
ifSite true  {k} {xs} e = inj₂ (site-[] k xs e)
ifSite false          e = inj₁ tt

ifHeld : ∀ (b : Bool) {x : Site} → (if b then x ∷ [] else []) ≡ [] → T (not b)
ifHeld true  ()
ifHeld false e = tt

------------------------------------------------------------------------
-- 2. Types without cells.
------------------------------------------------------------------------

flatC : ∀ {m} (A : Ty m) → T (flat? A) → NC (ty A)
flatC ST.Unit       _ = tt
flatC ST.Void       _ = tt
flatC ST.Int        _ = tt
flatC ST.Float      _ = tt
flatC (A ST.* B)    f = nc-∨ (flatC A (proj₁ (T-∧ f))) (flatC B (proj₂ (T-∧ f)))
flatC (A ST.+ B)    f = nc-∨ (flatC A (proj₁ (T-∧ f))) (flatC B (proj₂ (T-∧ f)))
flatC (A ⇒[ k ] B)  ()
flatC (ST.μ F)      ()
flatC (ST.ν F φ)    ()
flatC (ST.var i)    ()

capC : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → capIx Γ Ψ ≡ [] → NC (Co Γ Ψ)
capC SC.∅          []             _ = tt
capC (Γ SC.▸ A) (G.Zero ∷ Ψ) e = capC Γ Ψ (map-[] _ e)
capC (Γ SC.▸ A) (G.One  ∷ Ψ) e =
  nc-∨ (capC Γ Ψ (map-[] _ (proj₂ (ifNil (not (flat? A)) e)))) (flatC A (notnot (proj₁ (ifNil (not (flat? A)) e))))
capC (Γ SC.▸ A) (G.Many ∷ Ψ) e =
  nc-∨ (capC Γ Ψ (map-[] _ (proj₂ (ifNil (not (flat? A)) e)))) (flatC A (notnot (proj₁ (ifNil (not (flat? A)) e))))

nc-zero : ∀ {m n} (Γ : Ctx m n) → NC (Co Γ zeroUsage)
nc-zero SC.∅          = tt
nc-zero (Γ SC.▸ A) = nc-zero Γ

------------------------------------------------------------------------
-- 3. The context's plumbing copies nothing; the split only where shared.
------------------------------------------------------------------------

module _ (lc : LTy → Bool) {L : Cx} where

  cf-weak : ∀ {E m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ ⊑ᵘ Ψ′) → CF lc (weak {L} {E} {Γ = Γ} p)
  cf-weak {Γ = SC.∅}       []           = tt
  cf-weak {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) = cf-weak {Γ = Γ} p
  cf-weak {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) = tt , (cf-weak {Γ = Γ} p , tt)
  cf-weak {Γ = Γ SC.▸ A} (z≤m ⊑∷ p) = tt , (cf-weak {Γ = Γ} p , tt)
  cf-weak {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) = cf-weak {Γ = Γ} p , tt
  cf-weak {Γ = Γ SC.▸ A} (o≤m ⊑∷ p) = cf-weak {Γ = Γ} p , tt
  cf-weak {Γ = Γ SC.▸ A} (m≤m ⊑∷ p) = cf-weak {Γ = Γ} p , tt

  cf-split : ∀ {E m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) → sharedIx Γ Ψ₁ Ψ₂ ≡ [] → CF lc (split {L} {E} Γ Ψ₁ Ψ₂)
  -- (a slot both shares hold: `mixL ∘l (split ⊗l dup)`, the `dup` at the slot's type)
  cf-dupSlot : ∀ {E m n} (Γ : Ctx m n) (A : Ty m) (Ψ₁ Ψ₂ : Usage n)
             → (if not (flat? A) then 0 ∷ [] else []) ++ map suc (sharedIx Γ Ψ₁ Ψ₂) ≡ []
             → CF lc (mixL {L} {E} {Co Γ Ψ₁} {Co Γ Ψ₂} {ty A} {ty A} ∘l (split Γ Ψ₁ Ψ₂ ⊗l dup))
  cf-split SC.∅          []          []          _ = tt
  cf-split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Zero ∷ Ψ₂) e = cf-split Γ Ψ₁ Ψ₂ (map-[] _ e)
  cf-split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.One  ∷ Ψ₂) e = tt , (cf-split Γ Ψ₁ Ψ₂ (map-[] _ e) , tt)
  cf-split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Many ∷ Ψ₂) e = tt , (cf-split Γ Ψ₁ Ψ₂ (map-[] _ e) , tt)
  cf-split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Zero ∷ Ψ₂) e = _ , (cf-split Γ Ψ₁ Ψ₂ (map-[] _ e) , tt)
  cf-split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Zero ∷ Ψ₂) e = _ , (cf-split Γ Ψ₁ Ψ₂ (map-[] _ e) , tt)
  cf-split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.One  ∷ Ψ₂) e = cf-dupSlot Γ A Ψ₁ Ψ₂ e
  cf-split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Many ∷ Ψ₂) e = cf-dupSlot Γ A Ψ₁ Ψ₂ e
  cf-split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.One  ∷ Ψ₂) e = cf-dupSlot Γ A Ψ₁ Ψ₂ e
  cf-split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Many ∷ Ψ₂) e = cf-dupSlot Γ A Ψ₁ Ψ₂ e

  cf-dupSlot Γ A Ψ₁ Ψ₂ e =
    _ , (cf-split Γ Ψ₁ Ψ₂ (map-[] _ (proj₂ (ifNil (not (flat? A)) e))) , flatC A (notnot (proj₁ (ifNil (not (flat? A)) e))))

  cf-var : ∀ {E m n} {Γ : Ctx m n} (i : Data.Fin.Fin n) → CF lc (var-at {L} {E} {Γ = Γ} i)
  cf-var {Γ = Γ SC.▸ A} Data.Fin.zero    = _
  cf-var {Γ = Γ SC.▸ A} (Data.Fin.suc i) = cf-var {Γ = Γ} i

  cf-bind : ∀ {E m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (q : G.Quantity) → CF lc (bindL {L} {E} {Γ = Γ} {Ψ} {A} q)
  cf-bind G.Zero = _
  cf-bind G.One  = tt
  cf-bind G.Many = tt

  cf-castΦ : ∀ (rs : Rs L) {m n} {Γ : Ctx m n} {Φ Φ′ : Usage n} {B} (e : Φ ≡ Φ′) {t : LTm L (Co Γ Φ) B} → CF lc t → CF lc (castΦ rs {Γ = Γ} e t)
  cf-castΦ rs refl c = c

  cf-cast : ∀ {E A A′ B B′} (p : A ≡ A′) (q : B ≡ B′) {t : Tm L E A B} → CF lc t → CF lc (cast p q t)
  cf-cast refl refl c = c

------------------------------------------------------------------------
-- 4. The leaves: SigOps, references, numbers, conversions, structure maps.
------------------------------------------------------------------------

  cf-opL : ∀ {E A B} (si : SigOpInfo A B) → CF lc (opL {L} {E} si)
  cf-opL si = cf-cast (sym (⟪⌊⌋⟫-flat (SigOpInfo.baseA si))) (sym (⟪⌊⌋⟫-flat (SigOpInfo.conB si))) tt

  cf-numL : ∀ {E m A U k} (h : Has A U) (o : Sym U k) → CF lc (numL {L} {E} {m} {A} {U} {k} h o)
  cf-numL {E = E} {A = Th.int}   {k = Th.unary}   h o = cf-opL {E = E} (numInfo h o)
  cf-numL {E = E} {A = Th.int}   {k = Th.binary}  h o = cf-opL {E = E} (numInfo h o)
  cf-numL {E = E} {A = Th.int}   {k = Th.compare} h o = cf-opL {E = E} (numInfo h o)
  cf-numL {E = E} {A = Th.float} {k = Th.unary}   h o = cf-opL {E = E} (numInfo h o)
  cf-numL {E = E} {A = Th.float} {k = Th.binary}  h o = cf-opL {E = E} (numInfo h o)
  cf-numL {E = E} {A = Th.float} {k = Th.compare} h o = cf-opL {E = E} (numInfo h o)

  -- a conversion re-wraps closures as closures that READ them (`wrap`, D497): no copy
  cf-coeL : ∀ {m} {A B : Ty m} (p : A <: B) → CF lc (coeL {L} p)
  cf-coeL sub-void   = tt
  cf-coeL sub-unit   = tt
  cf-coeL sub-int    = tt
  cf-coeL sub-float  = tt
  cf-coeL (sub-arr {q = G.Zero} a b r) = cf-coeL b , tt
  cf-coeL (sub-arr {q = G.One}  a b r) = cf-coeL b , (tt , cf-coeL a)
  cf-coeL (sub-arr {q = G.Many} a b r) = cf-coeL b , (tt , cf-coeL a)
  cf-coeL (sub-* a b) = cf-coeL a , cf-coeL b
  cf-coeL (sub-+ a b) = (tt , cf-coeL a) , (tt , cf-coeL b)
  cf-coeL sub-μ      = tt
  cf-coeL (sub-ν _)  = tt
  cf-coeL sub-var    = tt

  cf-coeR : ∀ {m Z} {A B : Ty m} (p : A <: B) (d : Dec (VoidFree p)) {t : LTm L Z (ty A)} → CF lc t → CF lc (coeR p d t)
  cf-coeR p (yes vf) c = cf-cast refl (cong ⟪_⟫ (erase-eq p vf)) c
  cf-coeR p (no _)   c = cf-coeL p , c

  cf-coeRd : ∀ {m X} {A B : Ty m} (p : A <: B) (d : Dec (VoidFree p)) {t : Tm L X One (ty A)} → CF lc t → CF lc (coeRd p d t)
  cf-coeRd p (yes vf) c = cf-cast refl (cong ⟪_⟫ (erase-eq p vf)) c
  cf-coeRd p (no _)   c = cf-coeL p , c

  -- a SigOp's closure holds nothing (`One`)
  cf-sigL : (A : ST.Type) (name : CanonicalName) (c : IsConcrete A) → CF lc (sigL {L} A name c)
  cf-sigL (Dom ⇒[ G.mk-kind G.Zero (G.fin G.pureᶠ) ] Cod) name (con-fun bDom cCod) =
    (cf-opL (value-info name ST.b-Unit cCod) , _) , inj₂ tt
  cf-sigL (Dom ⇒[ G.mk-kind G.Zero G.eff ] Cod) name (con-fun bDom cCod) =
    (cf-opL (arrow-info (G.mk-kind G.Zero G.eff) name ST.b-Unit cCod) , _) , inj₂ tt
  cf-sigL (Dom ⇒[ G.mk-kind G.Zero (G.fin G.actᶠ) ] Cod) name (con-fun bDom cCod) =
    (cf-opL (arrow-info (G.mk-kind G.Zero G.act) name ST.b-Unit cCod) , _) , inj₂ tt
  cf-sigL (Dom ⇒[ G.mk-kind G.One π ] Cod) name (con-fun bDom cCod) =
    (cf-opL (arrow-info (G.mk-kind G.One π) name bDom cCod) , _) , inj₂ tt
  cf-sigL (Dom ⇒[ G.mk-kind G.Many π ] Cod) name (con-fun bDom cCod) =
    (cf-opL (arrow-info (G.mk-kind G.Many π) name bDom cCod) , _) , inj₂ tt
  cf-sigL _ name (con-base (ST.b-var {i = ()} _))
  cf-sigL _ name (con-base ib@ST.b-Unit)      = cf-opL {E = One} (value-info name ST.b-Unit ib) , tt
  cf-sigL _ name (con-base ib@ST.b-Void)      = cf-opL {E = One} (value-info name ST.b-Unit ib) , tt
  cf-sigL _ name (con-base ib@ST.b-Int)       = cf-opL {E = One} (value-info name ST.b-Unit ib) , tt
  cf-sigL _ name (con-base ib@ST.b-Float)     = cf-opL {E = One} (value-info name ST.b-Unit ib) , tt
  cf-sigL _ name (con-base ib@(ST.b-* a b))   = cf-opL {E = One} (value-info name ST.b-Unit ib) , tt
  cf-sigL _ name (con-base ib@(ST.b-+ a b))   = cf-opL {E = One} (value-info name ST.b-Unit ib) , tt

  cf-callM : ∀ {g A B} (r : Maybe (Data.Product.Σ ℕ λ l → L ∋[ l ] sg once g One A B)) → CF lc (callM r)
  cf-callM (just (l , p)) = _
  cf-callM nothing        = _

  -- a reference's closure holds nothing (`One`)
  cf-refL : (rs : Rs L) → ∀ {m} (U : Ty m) (f : CanonicalName) → CF lc (refL rs U f)
  cf-refL rs (A ⇒[ G.mk-kind G.Zero π ] B) f = (cf-callM (rs f I.Unit ⌊ B ⌋ (grade π)) , _) , inj₂ tt
  cf-refL rs (A ⇒[ G.mk-kind G.One π ] B) f  = (cf-callM (rs f ⌊ A ⌋ ⌊ B ⌋ (grade π)) , _) , inj₂ tt
  cf-refL rs (A ⇒[ G.mk-kind G.Many π ] B) f = (cf-callM (rs f ⌊ A ⌋ ⌊ B ⌋ (grade π)) , _) , inj₂ tt
  cf-refL rs U@ST.Unit      f = cf-callM (rs f I.Unit ⌊ U ⌋ act) , tt
  cf-refL rs U@ST.Void      f = cf-callM (rs f I.Unit ⌊ U ⌋ act) , tt
  cf-refL rs U@(_ ST.* _)   f = cf-callM (rs f I.Unit ⌊ U ⌋ act) , tt
  cf-refL rs U@(_ ST.+ _)   f = cf-callM (rs f I.Unit ⌊ U ⌋ act) , tt
  cf-refL rs U@(ST.μ _)     f = cf-callM (rs f I.Unit ⌊ U ⌋ act) , tt
  cf-refL rs U@(ST.ν _ _)   f = cf-callM (rs f I.Unit ⌊ U ⌋ act) , tt
  cf-refL rs U@ST.Int       f = cf-callM (rs f I.Unit ⌊ U ⌋ act) , tt
  cf-refL rs U@ST.Float     f = cf-callM (rs f I.Unit ⌊ U ⌋ act) , tt
  cf-refL rs U@(ST.var _)   f = cf-callM (rs f I.Unit ⌊ U ⌋ act) , tt

  -- a structure map: its suspended closures are the checker's `mapSite`
  cf-mapT : ∀ {m} {A B : Ty m} (mp : Map A B) → mapSite lc mp ≡ [] → CF lc (mapT {L} mp)
  cf-mapT mp-id         _ = tt
  cf-mapT mp-fst        _ = _
  cf-mapT mp-snd        _ = _
  cf-mapT mp-terminal   _ = tt
  cf-mapT mp-inl        _ = tt
  cf-mapT mp-inr        _ = tt
  cf-mapT mp-initial    _ = tt
  cf-mapT (mp-apply A B (G.fin G.pureᶠ)) _ = tt
  cf-mapT (mp-apply A B (G.fin G.actᶠ))  s = _ , inj₁ (ifHeld _ s)
  cf-mapT (mp-apply A B G.eff)          s = _ , inj₁ (ifHeld _ s)
  cf-mapT (mp-In F w)                   _ = cf-cast (sym (layerEq F w (ST.μ F))) refl tt
  cf-mapT (mp-Out F G.pureᶠ w)          _ = cf-cast refl (sym (layerEq F w (ST.ν F G.pureᶠ))) tt
  cf-mapT (mp-Out F G.actᶠ w)           s = (cf-cast refl (sym (layerEq F w (ST.ν F G.actᶠ))) tt , tt) , inj₁ (ifHeld _ s)
  cf-mapT mp-toFloat                    _ = cf-opL {E = One} i2f-info

------------------------------------------------------------------------
-- 5. Reads: they copy out only at types without cells.
------------------------------------------------------------------------

  cf-lv : ∀ {m n} {Γ : Ctx m n} {Φ : Usage n} {X C : LTy} (i : Data.Fin.Fin n) (q : singleUse i G.One ⊑ᵘ Φ)
        {t : Tm L (ty (SC.lookup Γ i)) X C} → CF lc t → CF lc (lv {L} {Γ = Γ} i q t)
  cf-lv {Γ = Γ SC.▸ A} Data.Fin.zero    (o≤o ⊑∷ q) c = c
  cf-lv {Γ = Γ SC.▸ A} Data.Fin.zero    (o≤m ⊑∷ q) c = c
  cf-lv {Γ = Γ SC.▸ A} (Data.Fin.suc i) (z≤z ⊑∷ q) c = cf-lv {Γ = Γ} i q c
  cf-lv {Γ = Γ SC.▸ A} (Data.Fin.suc i) (z≤o ⊑∷ q) c = cf-lv {Γ = Γ} i q c
  cf-lv {Γ = Γ SC.▸ A} (Data.Fin.suc i) (z≤m ⊑∷ q) c = cf-lv {Γ = Γ} i q c

  cf-Rp : ∀ {m n} {Γ : Ctx m n} {Ψ Φ : Usage n} {A : Ty m} {X C : LTy} {e : Expr Γ Ψ A} (d : Pth e) (q : Ψ ⊑ᵘ Φ)
        {t : Tm L (ty A) X C} → CF lc t → CF lc (Rp {L} d q t)
  cf-Rp {Γ = Γ} (p-var i) q c = cf-lv {Γ = Γ} i q c
  cf-Rp (p-fst d)  q c = cf-Rp d q c
  cf-Rp (p-snd d)  q c = cf-Rp d q c
  cf-Rp (p-mfst d) q c = cf-Rp d _ c
  cf-Rp (p-msnd d) q c = cf-Rp d _ c

  cf-Rt : ∀ {m n} {Γ : Ctx m n} {Ψ Φ : Usage n} {A : Ty m} {e : Expr Γ Ψ A} (d : Rd e) (q : Ψ ⊑ᵘ Φ)
        → T (flatRd d) → CF lc (Rt {L} {Γ = Γ} d q)
  cf-Rt {A = A} (rd-path d) q f = cf-Rp d q (flatC A f)
  cf-Rt (rd-int z)      q f = tt
  cf-Rt (rd-float d)    q f = tt
  cf-Rt (rd-num h o d)  q f = cf-numL h o , cf-Rt d _ f
  cf-Rt (rd-coe c d)    q f = cf-coeRd c (voidFree? c) (cf-Rt d _ f)
  cf-Rt (rd-pair da db) q f = (cf-Rt da _ (proj₁ (T-∧ f)) , cf-Rt db _ (proj₂ (T-∧ f))) , tt
  cf-Rt (rd-app p d)    q f = cf-Rp p _ tt , cf-Rt d _ f

  cf-lentS : ∀ {m n} {Γ : Ctx m n} {Ψs Φ : Usage n} {S : Ty m} {s : Expr Γ Ψs S} (d : Rd s) → T (flatRd d)
           → CF lc (lentS {L} {Γ = Γ} {Ψs} {Φ} d)
  cf-lentS {Γ = Γ} d f = (cf-weak {Γ = Γ} _ , tt) , (cf-Rt d _ f , tt)

  -- what the bridge reads in place is read at types without cells (`keepRd`)
  OnJust : ∀ {X : Set} → (X → Set) → Maybe X → Set
  OnJust P (just x) = P x
  OnJust P nothing  = ⊤

  Flat : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {e : Expr Γ Ψ A} → Rd e → Set
  Flat d = T (flatRd d)

  kf : ∀ {X : Set} {P : X → Set} (b c : Bool) (x : X) → (T b → P x) → OnJust P (if b ∧ c then just x else nothing)
  kf true  true  x h = h tt
  kf true  false x h = tt
  kf false c     x h = tt

  keep-flat : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {e : Expr Γ Ψ A} (c : Bool) (md : Maybe (Rd e))
            → OnJust Flat (keepRd c md)
  keep-flat c nothing  = tt
  keep-flat c (just d) = kf (flatRd d) (not (appRd d) ∨ c) d (λ t → t)

  ifOn : ∀ {X : Set} {P : X → Set} (b : Bool) {md : Maybe X} → OnJust P md → OnJust P (if b then md else nothing)
  ifOn true  h = h
  ifOn false h = tt

  rdw-flat : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (e : Expr Γ Ψ A) → OnJust Flat (rdw? e)
  rdw-flat e = keep-flat false (rd? e)

  rdx-flat : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (Ψa Ψb : Usage n) (e : Expr Γ Ψ A) → OnJust Flat (rdx? Ψa Ψb e)
  rdx-flat {Γ = Γ} Ψa Ψb e = ifOn (shared? Γ Ψa Ψb) (keep-flat true (rd? e))

  rdl-flat : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m} {q′} (e : Expr (Γ SC.▸ A) (q′ ∷ Ψ) B) → OnJust Flat (rdl? e)
  rdl-flat {Γ = Γ} {Ψ} e = ifOn (capCells? Γ Ψ) (keep-flat true (rd? e))

  onRt : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {e : Expr Γ Ψ A} (md : Maybe (Rd e)) → OnJust Flat md
       → OnJust (λ d → CF lc (Rt {L} {Γ = Γ} d (⊑ᵘ-refl Ψ))) md
  onRt nothing  _ = tt
  onRt (just d) f = cf-Rt d _ f

------------------------------------------------------------------------
-- 6. The closures and the fork's projections.
------------------------------------------------------------------------

  -- a closure owning its captures: at a lent-called type only if they have no cells
  cloC : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) (q : G.Quantity) (U : LTy)
       → cloSite lc Γ Ψ q false U ≡ [] → T (not (lc U)) ⊎ NC (Co Γ Ψ)
  cloC Γ Ψ q U s = Data.Sum.map not-∨ʳ (capC Γ Ψ) (ifSite (isMany q ∨ lc U) s)

  cf-lamOr : (rs : Rs L) → ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m} {R : Set} (q : G.Quantity) (π : G.Purity)
             (b : LTm L (Co Γ Ψ ⊗t ty A) (ty B)) (β : Blk b) (md : Maybe R)
             (rt : R → Tm L (Co Γ Ψ ⊗t ty A) One (ty B)) (kt : ∀ d → Blk (rt d))
           → OnJust (λ d → CF lc (rt d)) md → CF lc b
           → cloSite lc Γ Ψ q (isJust md) (Fn many (grade π) (ty A) (ty B)) ≡ []
           → CF lc (lamOr rs π b β md rt kt)
  cf-lamOr rs {Γ = Γ} {Ψ} q π b β nothing  rt kt _  cb s = cb , cloC Γ Ψ q _ s
  cf-lamOr rs          q π b β (just d) rt kt cr cb s = _ , (cr , tt)

  cf-splitP : ∀ {E m} {A Af Ag : Ty m} {pf : Map A Af} {pg : Map A Ag} (p : IsPj pf) (q : IsPj pg)
            → T (not (ov p q)) → CF lc (splitP {L} {E = E} p q)
  cf-splitP (pj-id {A = A})  pj-id            t = flatC A (notnot t)
  cf-splitP pj-id            (pj-fst {A = X}) t = flatC X (notnot t) , tt
  cf-splitP pj-id            (pj-snd {B = Y}) t = flatC Y (notnot t) , tt
  cf-splitP (pj-fst {A = X}) pj-id            t = tt , (flatC X (notnot t) , tt)
  cf-splitP (pj-snd {B = Y}) pj-id            t = tt , (flatC Y (notnot t) , tt)
  cf-splitP (pj-fst {A = X}) pj-fst           t = flatC X (notnot t) , _
  cf-splitP (pj-snd {B = Y}) pj-snd           t = flatC Y (notnot t) , _
  cf-splitP pj-fst           pj-snd           t = tt
  cf-splitP pj-snd           pj-fst           t = tt

------------------------------------------------------------------------
-- 7. ★★ THE LEMMA, clause for clause the bridge.
------------------------------------------------------------------------

  module _ (rs : Rs L) where

    cf-appS : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m} (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Many G.pure ] B)) (x : Expr Γ Ψ₂ A) {k}
            → CF lc (Lq rs f) → CF lc (Lq rs x) → splitSite Γ k Ψ₁ (G.Many *ᵘ Ψ₂) ≡ [] → CF lc (appS rs f x)
    cf-appS {Γ = Γ} {Ψ₁} {Ψ₂} f x cf cx s = tt , ((cf , (cx , cf-weak {Γ = Γ} _)) , cf-split Γ Ψ₁ _ (site-[] _ _ s))

    cf-scrutA : ∀ {m n} {Γ : Ctx m n} {Φ Ψs : Usage n} {S : Ty m} (s : Expr Γ Ψs S) (d : Maybe (Rd s)) {k}
              → OnJust Flat d → CF lc (Lq rs s)
              → (if isJust d then [] else splitSite Γ k Φ (G.Many *ᵘ Ψs)) ≡ [] → CF lc (scrutA rs {Γ = Γ} {Φ = Φ} s d)
    cf-scrutA {Γ = Γ} {Φ} s nothing  _ cs h = (tt , (cs , cf-weak {Γ = Γ} _)) , cf-split Γ Φ _ (site-[] _ _ h)
    cf-scrutA {Γ = Γ} {Φ} s (just d) f cs h = (cf-weak {Γ = Γ} _ , tt) , (cf-Rt d _ f , tt)

    cf-appR : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m} (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Many G.pure ] B)) (x : Expr Γ Ψ₂ A)
              (p : Maybe (Pth f)) (d : Maybe (Rd x)) {k} → OnJust Flat d → CF lc (Lq rs f) → CF lc (Lq rs x)
            → (if isJust p ∧ isJust d then [] else splitSite Γ k Ψ₁ (G.Many *ᵘ Ψ₂)) ≡ [] → CF lc (appR rs f x p d)
    cf-appR f x (just p) (just d) fd cf cx h = tt , ((cf , tt) , cf-scrutA x (just d) {k = "_"} fd cx refl)
    cf-appR f x (just p) nothing  fd cf cx h = cf-appS f x cf cx h
    cf-appR f x nothing  md       fd cf cx h = cf-appS f x cf cx h

    cf-scrutL : ∀ {m n} {Γ : Ctx m n} {Ψs Φ : Usage n} {S : Ty m} (s : Expr Γ Ψs S) (d : Maybe (Rd s)) {k}
              → OnJust Flat d → CF lc (Lq rs s)
              → (if isJust d then [] else splitSite Γ k Ψs Φ) ≡ [] → CF lc (scrutL rs {Γ = Γ} {Φ = Φ} s d)
    cf-scrutL {Γ = Γ} {Ψs} {Φ} s nothing  _ cs h = (tt , cs) , (tt , cf-split Γ Ψs Φ (site-[] _ _ h))
    cf-scrutL                  s (just d) f cs h = cf-lentS d f

    cf-pairL : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m} (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B) (d : Maybe (Rd a)) {k}
             → OnJust Flat d → CF lc (Lq rs a) → CF lc (Lq rs b)
             → (if isJust d then [] else splitSite Γ k Ψ₁ Ψ₂) ≡ [] → CF lc (pairL rs a b d)
    cf-pairL {Γ = Γ} {Ψ₁} {Ψ₂} a b nothing  _ ca cb h = (ca , cb) , cf-split Γ Ψ₁ Ψ₂ (site-[] _ _ h)
    cf-pairL                   a b (just d) f ca cb h = (tt , cb) , (tt , cf-lentS d f)

    cf-forkS : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty m} {π}
               (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ G.mk-kind G.Many π ] C))
               (a : Maybe (Arm f)) (b : Maybe (Arm g))
             → T (not (armK a (λ p → armK b (λ q → ov p q))))
             → ∀ {E} → CF lc (splitP {L} {E = E} (ArmD.pj (armOf rs f a)) (ArmD.pj (armOf rs g b)))
    cf-forkS {A = A} f g nothing                     nothing                     t {E} = cf-splitP {E = E} (pj-id {A = A}) (pj-id {A = A}) t
    cf-forkS {A = A} f g nothing                     (just (arm-map (pjl q)))    t {E} = cf-splitP {E = E} (pj-id {A = A}) q t
    cf-forkS {A = A} f g nothing                     (just (arm-comp h (pjl q))) t {E} = cf-splitP {E = E} (pj-id {A = A}) q t
    cf-forkS {A = A} f g (just (arm-map (pjl p)))    nothing                     t {E} = cf-splitP {E = E} p (pj-id {A = A}) t
    cf-forkS {A = A} f g (just (arm-map (pjl p)))    (just (arm-map (pjl q)))    t {E} = cf-splitP {E = E} p q t
    cf-forkS {A = A} f g (just (arm-map (pjl p)))    (just (arm-comp h (pjl q))) t {E} = cf-splitP {E = E} p q t
    cf-forkS {A = A} f g (just (arm-comp h (pjl p))) nothing                     t {E} = cf-splitP {E = E} p (pj-id {A = A}) t
    cf-forkS {A = A} f g (just (arm-comp h (pjl p))) (just (arm-map (pjl q)))    t {E} = cf-splitP {E = E} p q t
    cf-forkS {A = A} f g (just (arm-comp h (pjl p))) (just (arm-comp k (pjl q))) t {E} = cf-splitP {E = E} p q t

    cf-Lq : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (e : Expr Γ Ψ A) → sites lc e ≡ [] → CF lc (Lq rs e)
    cf-appL : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m} (f : Expr Γ Ψ₁ (A ⇒[ G.mk-kind G.Many G.pure ] B)) (x : Expr Γ Ψ₂ A)
              (c : Maybe (CP f)) → sites lc f ≡ [] → sites lc x ≡ [] → appSite lc f x c ≡ [] → CF lc (appL rs f x c)
    cf-armOf : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m} {π} (f : Expr Γ Ψ (A ⇒[ G.mk-kind G.Many π ] B)) (a : Maybe (Arm f))
             → sites lc f ≡ [] → CF lc (ArmD.env (armOf rs f a)) × CF lc (ArmD.ap (armOf rs f a))

    cf-armOf f nothing s = cf-Lq f s , tt
    cf-armOf _ (just (arm-map (pjl p))) s = tt , tt
    cf-armOf {Γ = Γ} _ (just (arm-comp h (pjl p))) s = (cf-Lq h (proj₁ (++-[] (sites lc h) s)) , cf-weak {Γ = Γ} _) , tt

    cf-appL {Ψ₁ = Ψ₁} {Ψ₂} f x nothing sf sx sa =
      cf-appR f x (pth? f) (rdx? Ψ₁ Ψ₂ x) (rdx-flat Ψ₁ Ψ₂ x) (cf-Lq f sf) (cf-Lq x sx) sa
    cf-appL {Γ = Γ} (copair' f g) x (just (cp _ _)) sf sx sa =
      ((tt , ((cf-Lq f (proj₁ (++-[] (sites lc f) sf)) , cf-weak {Γ = Γ} _) , tt))
      , (tt , ((cf-Lq g (proj₁ (++-[] (sites lc g) (proj₂ (++-[] (sites lc f) sf)))) , cf-weak {Γ = Γ} _) , tt)))
      , (tt , cf-scrutA x (rdw? x) (rdw-flat x) (cf-Lq x sx) sa)

    cf-Lq {Γ = Γ} (var i) s = cf-var {Γ = Γ} i
    cf-Lq {Γ = Γ} (lam {Ψ = Ψ} {q' = G.Zero} G.Zero _ e) s =
      (cf-Lq e (proj₁ (++-[] (sites lc e) s)) , _) , cloC Γ Ψ G.Zero _ (proj₂ (++-[] (sites lc e) s))
    cf-Lq {Γ = Γ} (lam {Ψ = Ψ} {q' = G.Zero} G.One _ e) s =
      (cf-Lq e (proj₁ (++-[] (sites lc e) s)) , _) , cloC Γ Ψ G.One _ (proj₂ (++-[] (sites lc e) s))
    cf-Lq {Γ = Γ} (lam {Ψ = Ψ} {q' = G.Zero} G.Many _ e) s =
      (cf-Lq e (proj₁ (++-[] (sites lc e) s)) , _) , cloC Γ Ψ G.Many _ (proj₂ (++-[] (sites lc e) s))
    cf-Lq {Γ = Γ} (lam {Ψ = Ψ} {q' = G.One} {π = π} {A = A} {B = B} G.One _ e) s =
      cf-lamOr rs {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} G.One π (Lq rs e) (Lq-blk rs e) (rdl? e) _ _ (onRt (rdl? e) (rdl-flat e)) (cf-Lq e (proj₁ (++-[] (sites lc e) s))) (proj₂ (++-[] (sites lc e) s))
    cf-Lq {Γ = Γ} (lam {Ψ = Ψ} {q' = G.One} {π = π} {A = A} {B = B} G.Many _ e) s =
      cf-lamOr rs {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} G.Many π (Lq rs e) (Lq-blk rs e) (rdl? e) _ _ (onRt (rdl? e) (rdl-flat e)) (cf-Lq e (proj₁ (++-[] (sites lc e) s))) (proj₂ (++-[] (sites lc e) s))
    cf-Lq {Γ = Γ} (lam {Ψ = Ψ} {q' = G.Many} {π = π} {A = A} {B = B} G.Many _ e) s =
      cf-lamOr rs {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} G.Many π (Lq rs e) (Lq-blk rs e) (rdl? e) _ _ (onRt (rdl? e) (rdl-flat e)) (cf-Lq e (proj₁ (++-[] (sites lc e) s))) (proj₂ (++-[] (sites lc e) s))
    cf-Lq {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Zero} f x) s = cf-castΦ rs {Γ = Γ} (sym (erase-arg-usage Ψ₁ Ψ₂)) (tt , ((cf-Lq f s , tt) , tt))
    cf-Lq {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} f x) s =
      let (a , r) = ++-[] (sites lc f) s ; (b , c) = ++-[] (sites lc x) r in
      tt , ((cf-Lq f a , (cf-Lq x b , cf-weak {Γ = Γ} _)) , cf-split Γ Ψ₁ _ (site-[] _ _ c))
    cf-Lq (app {q = G.Many} f x) s =
      let (a , r) = ++-[] (sites lc f) s ; (b , c) = ++-[] (sites lc x) r in
      cf-appL f x (cp? f) a b c
    cf-Lq {Γ = Γ} (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Zero} f x) s =
      let (a , b) = ++-[] (sites lc f) s in
      cf-castΦ rs {Γ = Γ} (sym (erase-arg-usage Ψ₁ Ψ₂)) (((tt , ((cf-Lq f a , tt) , tt)) , tt) , cloC Γ Ψ₁ G.One _ b)
    cf-Lq {Γ = Γ} (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} f x) s =
      let (a , r) = ++-[] (sites lc f) s ; (b , r′) = ++-[] (sites lc x) r ; (c , d) = ++-[] (splitSite Γ _ Ψ₁ (G.One *ᵘ Ψ₂)) r′ in
      ((tt , ((cf-Lq f a , (cf-Lq x b , cf-weak {Γ = Γ} _)) , cf-split Γ Ψ₁ _ (site-[] _ _ c))) , tt) , cloC Γ _ G.One _ d
    cf-Lq {Γ = Γ} (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} f x) s =
      let (a , r) = ++-[] (sites lc f) s ; (b , r′) = ++-[] (sites lc x) r ; (c , d) = ++-[] (splitSite Γ _ Ψ₁ (G.Many *ᵘ Ψ₂)) r′ in
      ((tt , ((cf-Lq f a , (cf-Lq x b , cf-weak {Γ = Γ} _)) , cf-split Γ Ψ₁ _ (site-[] _ _ c))) , tt) , cloC Γ _ G.One _ d
    cf-Lq (pair a b) s =
      let (x₁ , r) = ++-[] (sites lc a) s ; (x₂ , x₃) = ++-[] (sites lc b) r in
      cf-pairL a b (rdw? a) (rdw-flat a) (cf-Lq a x₁) (cf-Lq b x₂) x₃
    cf-Lq (fst' p) s = _ , cf-Lq p s
    cf-Lq (snd' p) s = _ , cf-Lq p s
    cf-Lq (inl' a) s = tt , cf-Lq a s
    cf-Lq (inr' b) s = tt , cf-Lq b s
    cf-Lq {Γ = Γ} (case' {qℓ = qℓ} {qr = qr} s l r) h =
      let (a , h₁) = ++-[] (sites lc s) h ; (b , h₂) = ++-[] (sites lc l) h₁ ; (c , d) = ++-[] (sites lc r) h₂ in
      ((cf-Lq l b , (cf-bind qℓ , (cf-weak {Γ = Γ} _ , tt))) , (cf-Lq r c , (cf-bind qr , (cf-weak {Γ = Γ} _ , tt))))
      , (tt , cf-scrutL s (rdw? s) (rdw-flat s) (cf-Lq s a) d)
    cf-Lq unit s = tt
    cf-Lq (absurd v) s = tt , cf-Lq v s
    cf-Lq {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Zero} e1 e2) s = cf-castΦ rs {Γ = Γ} (sym (erase-arg-usage Ψ₂ Ψ₁)) (cf-Lq e2 s)
    cf-Lq {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} e1 e2) s =
      let (a , r) = ++-[] (sites lc e1) s ; (b , c) = ++-[] (sites lc e2) r in
      cf-Lq e2 b , (tt , ((tt , (cf-Lq e1 a , cf-weak {Γ = Γ} _)) , cf-split Γ Ψ₂ _ (site-[] _ _ c)))
    cf-Lq {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} e1 e2) s =
      let (a , r) = ++-[] (sites lc e1) s ; (b , c) = ++-[] (sites lc e2) r in
      cf-Lq e2 b , (tt , ((tt , (cf-Lq e1 a , cf-weak {Γ = Γ} _)) , cf-split Γ Ψ₂ _ (site-[] _ _ c)))
    cf-Lq (int n) s = _
    cf-Lq (float d) s = _
    cf-Lq (num h o e) s = cf-numL h o , cf-Lq e s
    cf-Lq (coerce p f) s = cf-coeR p (voidFree? p) (cf-Lq f s)
    cf-Lq (sigOp {A = A} name c) s = cf-cast refl (cong ⟪_⟫ (sym (⌊wk₀⌋ A))) (cf-sigL A name c , tt)
    cf-Lq {A = A} (closure name) s = cf-refL rs A (bare name) , tt
    cf-Lq {A = A} (poly name _) s = cf-refL rs A (bare name) , tt
    cf-Lq (closed e) s = cf-Lq e s , tt
    cf-Lq {Γ = Γ} (lift-morphism mp) s = (cf-mapT mp s , _) , inj₂ (nc-zero Γ)
    cf-Lq {Γ = Γ} (morph-app mp x) s =
      let (a , b) = ++-[] (sites lc x) s in
      cf-mapT mp b , (cf-Lq x a , cf-weak {Γ = Γ} _)
    cf-Lq {Γ = Γ} (comp' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) s =
      let (a , r) = ++-[] (sites lc f) s ; (b , c) = ++-[] (sites lc g) r in
      _ , ((cf-Lq f a , (cf-Lq g b , cf-weak {Γ = Γ} _)) , cf-split Γ Ψ₁ _ (site-[] _ _ c))
    cf-Lq {Γ = Γ} (copair' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) s =
      let (a , r) = ++-[] (sites lc f) s ; (b , c) = ++-[] (sites lc g) r in
      _ , ((cf-Lq f a , cf-Lq g b) , cf-split Γ Ψ₁ Ψ₂ (site-[] _ _ c))
    cf-Lq {Γ = Γ} (fork' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} f g) s =
      let (a , r) = ++-[] (sites lc f) s ; (b , r′) = ++-[] (sites lc g) r ; (c , d) = ++-[] (splitSite Γ _ Ψ₁ Ψ₂) r′
          ea = cf-armOf f (arm? f) a ; eb = cf-armOf g (arm? g) b in
      (((proj₂ ea , proj₂ eb) , cf-forkS f g (arm? f) (arm? g) (ifHeld _ d)) , (proj₁ ea , proj₁ eb))
      , cf-split Γ Ψ₁ Ψ₂ (site-[] _ _ c)
    cf-Lq (curry' f) s =
      let (a , r) = ++-[] (sites lc f) s ; (b , c) = ++-[] (heldSite lc _ _) r in
      ((_ , inj₁ (ifHeld _ c)) , inj₁ (ifHeld _ b)) , cf-Lq f a
    cf-Lq {Γ = Γ} (cata {F = F} {A = A} wfF alg) s = cf-cast (layerEq F wfF A) refl tt , (cf-Lq alg s , cf-weak {Γ = Γ} _)
    cf-Lq {Γ = Γ} (ana {F = F} {A = A} wfF coalg) s =
      let (a , r) = ++-[] (sites lc coalg) s ; (b , c) = ++-[] (heldSite lc _ _) r in
      ((ifHeld _ c , (cf-cast refl (cong (Fn many act (ty A)) (layerEq F wfF A)) tt , tt)) , inj₁ (ifHeld _ b)) , (cf-Lq coalg a , cf-weak {Γ = Γ} _)
    cf-Lq {Γ = Γ} (loop round) s = tt , (cf-Lq round s , cf-weak {Γ = Γ} _)

    -- ★ D500: the checker's `Linear₀` (no warning) ⇒ the bridge copies nothing
    linear-cf : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (e : Expr Γ Ψ A) → sites lc e ≡ [] → CF lc (Lq rs e)
    linear-cf = cf-Lq
