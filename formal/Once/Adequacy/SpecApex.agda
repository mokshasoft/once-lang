-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecApex — the compiler over the Spec's source (plan 0.119
-- D6): `Spec.Correct` instantiated with `Spec.Source`'s `Source`, `Typed`,
-- `_⊢_`, `behaviour` and `Admissible`, its signatures the Spec's and its
-- implementations the Spec's Interpretations.
--
-- The compiler runs on its own front end (`Once.Adequacy.Compile`): a source's
-- module texts are parsed by the compiler's parser, and a binary is run
-- against a Spec Interpretation through its translation (`SpecInterp`). What
-- the compiler proves about its own typed programs (`correctᵈ`) becomes the
-- Spec's claim through two bridges, which are this module's PARAMETERS — the
-- exact statement of what is left to prove:
--
--   * SOUNDNESS of the front end and the meaning: a source the compiler types
--     denotes, in the Spec, a typed program the target can express, and the
--     compiler's meaning of its program is the Spec's behaviour, against every
--     Interpretation.
--   * COMPLETENESS of the front end: a source that denotes an expressible
--     Spec program parses, and types in the compiler.
--
-- They are parameters rather than postulates on purpose: until the compiler
-- follows D314 (a signature is the body's principal type), soundness is
-- FALSE for a program whose signature is wider than its body's type, and a
-- postulated false statement would make the apex inconsistent.
------------------------------------------------------------------------

open import Once.Lang.Trace using (Interp)
open import Once.Target.Arch using (Arch)
import Once.Adequacy.Compile as Compile

module Once.Adequacy.SpecApex
  (arch-correct : ∀ (ι : Interp) (arch : Arch) → Compile.ArchCorrect arch ι) where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

open import Once.Adequacy.CPU.Interface using (Byte)
open import Once.Target.Arch using (arch-numerics)
import Once.Denotation.Behavior as B
open import Once.Lang.Trace using (interp)
open import Once.Lang.Contract using (Impl)
open import Once.Spec.Trace using (Tr; _≈ᵗ⟨_⟩_)
open import Once.Metatheory.Trace using (WB-trans; WB-sym)
open import Once.Adequacy.MachineTrace using (silentTr)
open import Once.Spec.Correct using (CorrectCompiler)
open import Once.Spec.Signature using (Signature; WellFormed)
import Once.Spec.Observation as Obs
import Once.Spec.Core.Program as CoreProgram
import Once.Spec.Source as SP
open SP using (Source; Typed; _⊢_; behaviour; Admissible)
open SP.Typed using (signature; program)
open import Once.Adequacy.SpecInterp using (toInterp; wellFormed?)
open import Once.Adequacy.SpecSource using (parseModules; toSource)

module VC = Compile.WithCPU arch-correct

------------------------------------------------------------------------
-- The compiler's reading of a Spec source
------------------------------------------------------------------------

compile : Arch → Bool → Source → Maybe (List Byte)
compile arch doOpt src = toSource src >>= VC.compile arch doOpt

-- A binary run against a Spec Interpretation of a well-formed signature, as
-- the compiler's Interpretation. (Every Spec program's signature is
-- well-formed; for any other the run is the silent one.)
exec : Arch → (Σ : Signature) → Obs.Interp Σ → List Byte → Tr ⊤
exec arch Σ J bytes with wellFormed? Σ
... | yes wf = VC.exec (toInterp Σ wf J) arch bytes
... | no  _  = silentTr

_≈_ : Tr ⊤ → Tr ⊤ → Set
b₁ ≈ b₂ = b₁ ≈ᵗ⟨ _≡_ ⟩ b₂

------------------------------------------------------------------------
-- The bridges still owed
------------------------------------------------------------------------

record Bridges : Set₁ where
  field
    -- The front end and the meaning, soundly: what the compiler types is a
    -- Spec program, and the compiler's meaning of it is the Spec's behaviour.
    sound : ∀ (arch : Arch) (src : Source) (srcC : B.Source) (tp : VC.Typed)
          → toSource src ≡ just srcC → srcC VC.⊢R tp → VC.Admissible arch tp
          → Σ[ tp′ ∈ Typed ]
              (src ⊢ tp′) × Admissible (arch-numerics arch) tp′
              × (∀ (wf : WellFormed (signature tp′)) (J : Obs.Interp (signature tp′))
                 → Σ[ I ∈ Impl (VC.sigOfT tp) ]
                     (∀ bytes → VC.exec (toInterp (signature tp′) wf J) arch bytes
                                ≡ VC.exec (interp (VC.sigOfT tp) I) arch bytes)
                     × (VC.⟦ arch ⟧ᵈᴵ tp I ≈ behaviour (arch-numerics arch) tp′ J))
    -- The front end, completely: what the Spec types, the compiler parses and types.
    complete : ∀ (arch : Arch) (src : Source) (tp′ : Typed)
             → src ⊢ tp′ → Admissible (arch-numerics arch) tp′
             → Σ[ srcC ∈ B.Source ] (toSource src ≡ just srcC)
               × Σ[ tp ∈ VC.Typed ] (srcC VC.⊢R tp) × VC.Admissible arch tp

------------------------------------------------------------------------
-- The Spec's claim, from the compiler's and the bridges
------------------------------------------------------------------------

module _ (br : Bridges) where
  open Bridges br

  private
    bind-just : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b}
              → (m >>= f) ≡ just b → Σ[ a ∈ A ] (m ≡ just a) × (f a ≡ just b)
    bind-just (just a) f eq = a , refl , eq

    -- A program's signature is well-formed, so `exec` runs the translation.
    exec-wf : ∀ arch (tp′ : Typed) J bytes
            → Σ[ wf ∈ WellFormed (signature tp′) ]
                exec arch (signature tp′) J bytes ≡ VC.exec (toInterp (signature tp′) wf J) arch bytes
    exec-wf arch tp′ J bytes with wellFormed? (signature tp′)
    ... | yes wf = wf , refl
    ... | no ¬wf = ⊥-elim′ (¬wf (CoreProgram.Program.wf (program tp′)))
      where
        open import Data.Empty using (⊥-elim)
        ⊥-elim′ = ⊥-elim

  correct : ∀ arch doOpt src →
      ( ∀ bytes → compile arch doOpt src ≡ just bytes →
          Σ[ tp ∈ Typed ] ((src ⊢ tp) × Admissible (arch-numerics arch) tp
                           × (∀ J → exec arch (signature tp) J bytes ≈ behaviour (arch-numerics arch) tp J)) )
    × ( ∀ tp → src ⊢ tp → Admissible (arch-numerics arch) tp →
          Σ[ bytes ∈ List Byte ] (compile arch doOpt src ≡ just bytes) )
  correct arch doOpt src = soundness , completeness
    where
      soundness : ∀ bytes → compile arch doOpt src ≡ just bytes →
          Σ[ tp ∈ Typed ] ((src ⊢ tp) × Admissible (arch-numerics arch) tp
                           × (∀ J → exec arch (signature tp) J bytes ≈ behaviour (arch-numerics arch) tp J))
      soundness bytes eq with bind-just (toSource src) (VC.compile arch doOpt) eq
      ... | srcC , eqS , eqC with proj₁ (VC.correctᵈ arch doOpt srcC) bytes eqC
      ...   | tp , ⊢tp , adm , runs with sound arch src srcC tp eqS ⊢tp adm
      ...     | tp′ , ⊢tp′ , adm′ , means = tp′ , ⊢tp′ , adm′ , λ J → behaves J
        where
          behaves : ∀ J → exec arch (signature tp′) J bytes ≈ behaviour (arch-numerics arch) tp′ J
          behaves J with exec-wf arch tp′ J bytes
          ... | wf , eqE with means wf J
          ...   | I , same , agrees rewrite eqE | same bytes = WB-trans trans (runs I) agrees

      completeness : ∀ tp → src ⊢ tp → Admissible (arch-numerics arch) tp →
          Σ[ bytes ∈ List Byte ] (compile arch doOpt src ≡ just bytes)
      completeness tp′ ⊢tp′ adm′ with complete arch src tp′ ⊢tp′ adm′
      ... | srcC , eqS , tp , ⊢tp , adm with proj₂ (VC.correctᵈ arch doOpt srcC) tp ⊢tp adm
      ...   | bytes , eqC = bytes , compile-eq
        where
          compile-eq : compile arch doOpt src ≡ just bytes
          compile-eq rewrite eqS = eqC

  -- `Spec.Correct`, over the Spec's source.
  spec-compiler : CorrectCompiler
  spec-compiler = record
    { Arch           = Arch
    ; Source         = Source
    ; Bytes          = List Byte
    ; Behavior       = Tr ⊤
    ; Signature      = Signature
    ; Implementation = Obs.Interp
    ; Typed          = Typed
    ; _⊢_            = _⊢_
    ; sigOf          = signature
    ; ⟦_⟧ˢ           = λ arch tp J → behaviour (arch-numerics arch) tp J
    ; exec           = exec
    ; _≈_            = _≈_
    ; Admissible     = λ arch → Admissible (arch-numerics arch)
    ; compile        = compile
    ; correct        = correct
    }
