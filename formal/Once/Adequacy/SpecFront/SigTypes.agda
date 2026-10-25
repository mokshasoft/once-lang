-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.SigTypes — a `signature` declaration's type, read
-- by the compiler and by the Spec (plan 0.121 §3.6, F6).
--
-- The compiler reads a `signature`'s written type as a ground, concrete,
-- honest compiler type (`Parser.projectSig`, the FFI entry's type); the Spec
-- as a declaration type (`DeclTypeOf`: a base constant, a pure arrow between
-- base types, an `Act` one). The two agree: a Spec reading of the written type
-- is the compiler's type back (`decl-eq`), and the compiler's type has one
-- (`decl-of`) — so the signature's compiler table is the Spec signature's
-- (`SpecInterp.toISig`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.SigTypes where

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

import Once.Internal.Type as LT

import Once.Spec.Type as LT
import Once.Spec.Grade as LG
open import Once.Spec.Surface.Syntax using (PolyType; PTVar; PUnit; PVoid; PInt; PFloat; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ; Pν)
open import Once.Internal.Type.Poly using (Ground; extractGround)
open import Once.Internal.Type.WellFormed using (IsConcrete; con-base; con-fun)
open import Once.Spec.Type using (Base; b-*; b-+; b-Float; b-Int; b-Unit; b-Void; ∅ₖ)
open import Once.Internal.Type.Honest using (HonestFFI)
import Once.Spec.Grade as SG
open import Once.Spec.Signature using (BTy; unit; void; int; float; DeclType; constant; value; operation)
import Once.Spec.Signature as SSig
open import Once.Spec.Surface.Program using (BaseType; bt-unit; bt-void; bt-int; bt-float; bt-*; bt-+; DeclTypeOf; dt-const; dt-pure; dt-act)
open import Once.Adequacy.SpecGrammar.Conv using (toPoly)
open import Once.Adequacy.SpecInterp using (⌞_⌟; declTy)

------------------------------------------------------------------------
-- The Spec's reading is the compiler's type
------------------------------------------------------------------------

base-eq : ∀ (A : PolyType) (g : Ground A) {a} → BaseType (toPoly A) a → ⌞ a ⌟ ≡ extractGround A g
base-eq PUnit  _ bt-unit  = refl
base-eq PVoid  _ bt-void  = refl
base-eq PInt   _ bt-int   = refl
base-eq PFloat _ bt-float = refl
base-eq (A P* B) (ga , gb) (bt-* a b) = cong₂ LT._*_ (base-eq A ga a) (base-eq B gb b)
base-eq (A P+ B) (ga , gb) (bt-+ a b) = cong₂ LT._+_ (base-eq A ga a) (base-eq B gb b)
base-eq (PTVar _) () _
base-eq (A P⇒[ q ] B) _ ()
base-eq (PEff A B) _ ()
base-eq (PAct A B) _ ()
base-eq (Pμ F) _ ()
base-eq (Pν F φ) _ ()

decl-eq : ∀ (T : PolyType) (g : Ground T) {t} → DeclTypeOf (toPoly T) t → declTy t ≡ extractGround T g
decl-eq T g (dt-const b) = base-eq T g b
decl-eq (A P⇒[ q ] B) (ga , gb) (dt-pure a b) =
  cong₂ (λ x y → x LT.⇒[ LG.mk-kind q LG.pure ] y) (base-eq A ga a) (base-eq B gb b)
decl-eq (PAct A B) (ga , gb) (dt-act a b) = cong₂ (λ x y → x LT.⇒[ LG.mk-kind LG.Many LG.act ] y) (base-eq A ga a) (base-eq B gb b)

------------------------------------------------------------------------
-- The compiler's type has a Spec reading
------------------------------------------------------------------------

base-of : ∀ (A : PolyType) (g : Ground A) → Base ∅ₖ (extractGround A g) → Σ[ a ∈ BTy ] BaseType (toPoly A) a
base-of PUnit  _ _ = unit , bt-unit
base-of PVoid  _ _ = void , bt-void
base-of PInt   _ _ = int , bt-int
base-of PFloat _ _ = float , bt-float
base-of (A P* B) (ga , gb) (b-* a b) =
  let (x , bx) = base-of A ga a ; (y , by) = base-of B gb b in x SSig.* y , bt-* bx by
base-of (A P+ B) (ga , gb) (b-+ a b) =
  let (x , bx) = base-of A ga a ; (y , by) = base-of B gb b in x SSig.+ y , bt-+ bx by
base-of (PTVar _) () _
base-of (A P⇒[ q ] B) _ ()
base-of (PEff A B) _ ()
base-of (PAct A B) _ ()
base-of (Pμ F) _ ()
base-of (Pν F φ) _ ()

private
  const-of : ∀ (T : PolyType) (g : Ground T) → Base ∅ₖ (extractGround T g) → Σ[ t ∈ DeclType ] DeclTypeOf (toPoly T) t
  const-of T g b = let (a , ba) = base-of T g b in constant a , dt-const ba

decl-of : ∀ (T : PolyType) (g : Ground T) → IsConcrete (extractGround T g) → HonestFFI (extractGround T g)
        → Σ[ t ∈ DeclType ] DeclTypeOf (toPoly T) t
decl-of (A P⇒[ q ] B) (ga , gb) (con-fun a b) h =
  let (x , bx) = base-of A ga a ; (y , by) = base-of B gb b in value x q y , dt-pure bx by
decl-of (A P⇒[ q ] B) _ (con-base ()) _
decl-of (PAct A B) (ga , gb) (con-fun a b) h =
  let (x , bx) = base-of A ga a ; (y , by) = base-of B gb b in operation x SG.Many y , dt-act bx by
decl-of (PAct A B) _ (con-base ()) _
decl-of (PEff A B) _ (con-fun _ _) ()
decl-of (PEff A B) _ (con-base ()) _
decl-of (PTVar _) () _ _
decl-of PUnit g (con-base b) h = const-of PUnit g b
decl-of PVoid g (con-base b) h = const-of PVoid g b
decl-of PInt g (con-base b) h = const-of PInt g b
decl-of PFloat g (con-base b) h = const-of PFloat g b
decl-of (A P* B) g (con-base b) h = const-of (A P* B) g b
decl-of (A P+ B) g (con-base b) h = const-of (A P+ B) g b
decl-of (Pμ F) g (con-base ()) h
decl-of (Pν F φ) g (con-base ()) h
