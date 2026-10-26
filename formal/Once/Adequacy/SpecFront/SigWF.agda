-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.SigWF — the program's signature is well-formed
-- (plan 0.121 §3.6, F6).
--
-- The compiler types an FFI declaration only at an HONEST type (D231/D318:
-- a value inhabited and not `Unit`, an operation at `Act` answering `Unit`,
-- `Void` or proper data); read back, that is the Spec's `WellFormedDecl`
-- (`honest-wf`). Every declaration of Σ is one of the module's FFI entries,
-- so Σ is well-formed (`wf-of`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.SigWF where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

import Once.Type.Honest as LH
open LH using (HonestFFI)
import Once.Spec.Grade as SG
import Once.Spec.Signature as S
open S using (Signature; _∶_; DeclType; constant; value; operation; WellFormed; WellFormedDecl; []; _∷_)
import Once.Parser as Parser
open import Once.Module using (entrySig)
open import Once.Adequacy.SpecInterp using (declTy; ⌞_⌟)
open import Once.Core.Decl using (toISig)
open import Once.Adequacy.SpecFront.Extract using (FFIFacts)
open import Once.Adequacy.SpecFront.SigFacts using (mem-toISig; facts-at)

ne : ∀ b → LH.NotEmpty ⌞ b ⌟ → S.NotEmpty b
ne S.unit    _ = tt
ne S.void    ()
ne S.int     _ = tt
ne S.float   _ = tt
ne (a S.* b) (x , y) = ne a x , ne b y
ne (a S.+ b) (inj₁ x) = inj₁ (ne a x)
ne (a S.+ b) (inj₂ y) = inj₂ (ne b y)

ns : ∀ b → LH.NotSingleton ⌞ b ⌟ → S.NotSingleton b
ns S.unit    ()
ns S.void    _ = tt
ns S.int     _ = tt
ns S.float   _ = tt
ns (a S.* b) (inj₁ x) = inj₁ (ns a x)
ns (a S.* b) (inj₂ y) = inj₂ (ns b y)
ns (a S.+ b) (inj₁ (x , y)) = inj₁ (ne a x , ne b y)
ns (a S.+ b) (inj₂ (x , y)) = inj₂ (ns a x , ns b y)

honest-wf : ∀ t → HonestFFI (declTy t) → WellFormedDecl t
honest-wf (constant S.unit) ()
honest-wf (constant S.void) ()
honest-wf (constant S.int) _ = tt , λ ()
honest-wf (constant S.float) _ = tt , λ ()
honest-wf (constant (a S.* b)) h = ne (a S.* b) h , λ ()
honest-wf (constant (a S.+ b)) h = ne (a S.+ b) h , λ ()
honest-wf (value a q S.unit) ()
honest-wf (value a q S.void) ()
honest-wf (value a q S.int) _ = tt , λ ()
honest-wf (value a q S.float) _ = tt , λ ()
honest-wf (value a q (b S.* c)) h = ne (b S.* c) h , λ ()
honest-wf (value a q (b S.+ c)) h = ne (b S.+ c) h , λ ()
honest-wf (operation a SG.Zero b) ()
honest-wf (operation a SG.One b) ()
honest-wf (operation a SG.Many S.unit) _ = inj₁ refl
honest-wf (operation a SG.Many S.void) _ = inj₂ (inj₁ refl)
honest-wf (operation a SG.Many S.int) _ = inj₂ (inj₂ (tt , tt))
honest-wf (operation a SG.Many S.float) _ = inj₂ (inj₂ (tt , tt))
honest-wf (operation a SG.Many (b S.* c)) (x , y) = inj₂ (inj₂ (ne (b S.* c) x , ns (b S.* c) y))
honest-wf (operation a SG.Many (b S.+ c)) (x , y) = inj₂ (inj₂ (ne (b S.+ c) x , ns (b S.+ c) y))

-- The program's signature is well-formed.
wf-of : ∀ (Σ : Signature) fs → toISig Σ ≡ entrySig fs → All FFIFacts fs → WellFormed Σ
wf-of Σ fs e fa = go Σ (λ m → m)
  where
    go : ∀ Σ′ → (∀ {d} → d ∈ Σ′ → d ∈ Σ) → WellFormed Σ′
    go [] _ = []
    go ((c ∶ t) ∷ Σ′) sub =
      honest-wf t ((proj₂ (facts-at fa (subst (_ ∈_) e (mem-toISig (sub (here refl)))))))
        ∷ go Σ′ (λ m → sub (there m))
