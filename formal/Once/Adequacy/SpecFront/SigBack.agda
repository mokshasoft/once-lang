-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.SigBack — an FFI declaration the Spec reads is one
-- the compiler reads (plan 0.121 `complete`; the converse of `SigTypes` and
-- `SigWF`).
--
-- The Spec reads a `signature`'s written type as a declaration type
-- (`DeclTypeOf`); the program's signature is well-formed (`WellFormedDecl`).
-- Such a type is ground (`decl-ground`) and, at the compiler's reading, honest
-- (`decl-honest`), so the extractor's `projectSig` reads it, at the
-- declaration's type (`project-of`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.SigBack where

open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

import Once.Internal.Type as LT

import Once.Spec.Type as LT
import Once.Internal.Type.WellFormed as LW
import Once.Spec.Type as LW
import Once.Internal.Type.Honest as LH
import Once.Spec.Grade as LG
open import Data.List using ([])
open import Once.Spec.Surface.Syntax using (PolyType; PTVar; PUnit; PVoid; PInt; PFloat; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ; Pν)
open import Once.Internal.Type.Poly using (Ground; extractGround)
import Once.Spec.Grade as SG
import Once.Spec.Signature as S
open import Once.Spec.Signature using (DeclType; constant; value; operation; WellFormedDecl)
open import Once.Spec.Surface.Program using (BaseType; bt-unit; bt-void; bt-int; bt-float; bt-*; bt-+; DeclTypeOf; dt-const; dt-pure; dt-act)
open import Once.Adequacy.SpecGrammar.Conv using (toPoly)
open import Once.Adequacy.SpecInterp using (⌞_⌟; declTy)
open import Once.Adequacy.SpecFront.SigTypes using (decl-eq)
open import Once.Parser using (projectSig)
open import Once.Type using (isGround)
open import Once.Type.Honest using (honest?-complete)
open import Once.TypeCheck.DeciderComplete using (isGround-complete-at)

------------------------------------------------------------------------
-- Ground
------------------------------------------------------------------------

base-ground : ∀ (A : PolyType) {a} → BaseType (toPoly A) a → Ground A
base-ground PUnit    bt-unit    = tt
base-ground PVoid    bt-void    = tt
base-ground PInt     bt-int     = tt
base-ground PFloat   bt-float   = tt
base-ground (A P* B) (bt-* a b) = base-ground A a , base-ground B b
base-ground (A P+ B) (bt-+ a b) = base-ground A a , base-ground B b
base-ground (PTVar _)     ()
base-ground (_ P⇒[ _ ] _) ()
base-ground (PEff _ _)    ()
base-ground (PAct _ _)    ()
base-ground (Pμ _)   ()
base-ground (Pν _ _) ()

decl-ground : ∀ (T : PolyType) {t} → DeclTypeOf (toPoly T) t → Ground T
decl-ground (A P⇒[ q ] B) (dt-pure a b) = base-ground A a , base-ground B b
decl-ground (A P⇒[ q ] B) (dt-const ())
decl-ground (PAct A B)    (dt-act a b)  = base-ground A a , base-ground B b
decl-ground (PAct A B)    (dt-const ())
decl-ground (PEff A B)    (dt-const ())
decl-ground PUnit         (dt-const b)  = base-ground PUnit b
decl-ground PVoid         (dt-const b)  = base-ground PVoid b
decl-ground PInt          (dt-const b)  = base-ground PInt b
decl-ground PFloat        (dt-const b)  = base-ground PFloat b
decl-ground (A P* B)      (dt-const b)  = base-ground (A P* B) b
decl-ground (A P+ B)      (dt-const b)  = base-ground (A P+ B) b
decl-ground (PTVar _)     (dt-const ())
decl-ground (Pμ _)   (dt-const ())
decl-ground (Pν _ _) (dt-const ())

------------------------------------------------------------------------
-- Honest
------------------------------------------------------------------------

private
  ne← : ∀ b → S.NotEmpty b → LH.NotEmpty ⌞ b ⌟
  ne← S.unit    _ = tt
  ne← S.void    ()
  ne← S.int     _ = tt
  ne← S.float   _ = tt
  ne← (a S.* b) (x , y) = ne← a x , ne← b y
  ne← (a S.+ b) (inj₁ x) = inj₁ (ne← a x)
  ne← (a S.+ b) (inj₂ y) = inj₂ (ne← b y)

  ns← : ∀ b → S.NotSingleton b → LH.NotSingleton ⌞ b ⌟
  ns← S.unit    ()
  ns← S.void    _ = tt
  ns← S.int     _ = tt
  ns← S.float   _ = tt
  ns← (a S.* b) (inj₁ x) = inj₁ (ns← a x)
  ns← (a S.* b) (inj₂ y) = inj₂ (ns← b y)
  ns← (a S.+ b) (inj₁ (x , y)) = inj₁ (ne← a x , ne← b y)
  ns← (a S.+ b) (inj₂ (x , y)) = inj₂ (ns← a x , ns← b y)

  -- a constant: inhabited, not `Unit`
  const-honest : ∀ b → S.NotEmpty b → b ≢ S.unit → LH.HonestFFI ⌞ b ⌟
  const-honest S.unit    _ n = ⊥-elim (n refl)
  const-honest S.void    () _
  const-honest S.int     _ _ = tt
  const-honest S.float   _ _ = tt
  const-honest (a S.* b) x _ = ne← (a S.* b) x
  const-honest (a S.+ b) x _ = ne← (a S.+ b) x

  -- a pure function's answer: inhabited, not `Unit`
  value-cod : ∀ b → S.NotEmpty b → b ≢ S.unit → LH.HonestCod LG.pure ⌞ b ⌟
  value-cod S.unit    _ n = ⊥-elim (n refl)
  value-cod S.void    () _
  value-cod S.int     _ _ = tt
  value-cod S.float   _ _ = tt
  value-cod (a S.* b) x _ = ne← (a S.* b) x
  value-cod (a S.+ b) x _ = ne← (a S.+ b) x

  -- an operation's answer: `Unit`, `Void` or proper data
  op-cod : ∀ b → S.EffCod b → LH.HonestCod LG.act ⌞ b ⌟
  op-cod S.unit    _ = tt
  op-cod S.void    _ = tt
  op-cod S.int     _ = tt
  op-cod S.float   _ = tt
  op-cod (a S.* b) (inj₁ ())
  op-cod (a S.* b) (inj₂ (inj₁ ()))
  op-cod (a S.* b) (inj₂ (inj₂ (x , y))) = ne← (a S.* b) x , ns← (a S.* b) y
  op-cod (a S.+ b) (inj₁ ())
  op-cod (a S.+ b) (inj₂ (inj₁ ()))
  op-cod (a S.+ b) (inj₂ (inj₂ (x , y))) = ne← (a S.+ b) x , ns← (a S.+ b) y

-- A well-formed declaration type is honest at the compiler's reading.
decl-honest : ∀ {P t} → DeclTypeOf P t → WellFormedDecl t → LH.HonestFFI (declTy t)
decl-honest (dt-const {a = a} _) (x , n) = const-honest a x n
decl-honest (dt-pure {b = b} {q = SG.Zero} _ _) (x , n) = value-cod b x n
decl-honest (dt-pure {b = b} {q = SG.One} _ _)  (x , n) = value-cod b x n
decl-honest (dt-pure {b = b} {q = SG.Many} _ _) (x , n) = value-cod b x n
decl-honest (dt-act {b = b} _ _) e = op-cod b e

------------------------------------------------------------------------
-- The extractor reads it
------------------------------------------------------------------------

project-of : ∀ n (T : PolyType) {t} → DeclTypeOf (toPoly T) t → WellFormedDecl t → projectSig n T ≡ inj₂ (declTy t)
project-of n T {t} dt wf = at (decl-ground T dt)
  where
    at : (g : Ground T) → projectSig n T ≡ inj₂ (declTy t)
    at g rewrite isGround-complete-at T g = hs _ refl
      where
        hs : ∀ X → X ≡ extractGround T g → Once.Parser.honestSig n X (LH.honest? X) ≡ inj₂ (declTy t)
        hs .(extractGround T g) refl
          rewrite proj₂ (honest?-complete {extractGround T g} (subst LH.HonestFFI (decl-eq T g dt) (decl-honest dt wf)))
          = cong inj₂ (sym (decl-eq T g dt))

------------------------------------------------------------------------
-- Concrete and ground
------------------------------------------------------------------------

private
  base-b : ∀ b → (LW.Base LW.∅ₖ) ⌞ b ⌟
  base-b S.unit    = LW.b-Unit
  base-b S.void    = LW.b-Void
  base-b S.int     = LW.b-Int
  base-b S.float   = LW.b-Float
  base-b (a S.* b) = LW.b-* (base-b a) (base-b b)
  base-b (a S.+ b) = LW.b-+ (base-b a) (base-b b)

-- A declaration's type is concrete.
declTy-concrete : ∀ t → LW.IsConcrete (declTy t)
declTy-concrete (constant b)      = LW.con-base (base-b b)
declTy-concrete (S.value a q b)   = LW.con-fun (base-b a) (base-b b)
declTy-concrete (S.operation a q b) = LW.con-fun (base-b a) (base-b b)

