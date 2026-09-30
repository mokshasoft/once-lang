-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreEnv — plan 0.103 6b, leg C.1: THE SURFACE ENVIRONMENT OF
-- A CORE TELESCOPE.
--
-- Leg B (`CoreMeaningBridge`) holds in any surface environment that `Agree`s
-- with the core's `δ`. The telescope walk builds that environment FROM `δ`,
-- entry by entry along the scope's signature (`ImpSig`/`TeleSig`, the View's
-- data), so the agreement holds by construction:
--   * a definition means its core entry at the instance (`refSem`);
--   * an FFI declaration means its contract (`sigOpRefᴰ`).
-- The one fact not about `δ` is that a qualified or resolved (not own) name
-- never finds a definition: a definition's name is a valid identifier (the
-- extractor's guard), and such a name is not (it has a dot, or is empty).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)
open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)

module Once.Adequacy.CoreEnv (fmt : TargetNum) {s : ℕ} (S : Sig s) where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList) renaming (_++_ to _++ˢ_)
open import Data.String.Unsafe using (toList-++)
import Data.String.Properties as StrProp
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

import Once.Compile as C
open C.PolyFunInfo using (pfunName; pfunType)
open import Once.Type using (Type)
open import Once.Type.Rigid using (KindedInstance; ground-kinded)
open import Once.Functor.Translate using (IsConcrete; IsConcrete-irrelevant)
open import Once.Functor.Decide using (isConcrete?; isConcrete?-complete)
open import Once.CanonicalName using (CanonicalName; canonical; own; bare; showCanonical)
open import Once.TypeCheck.Classify using (lookupImport; lookupPolyPrefix)
open import Once.Parser using (validIdentB; validCharsB; allIdentContinue)
open import Once.Denotation.DefEnv using (defAt; impAt)
open import Once.Denotation.Meaning using (DefMeanings; ImpMeanings; Meanings; meanings; sigOpRefᴰ)
open import Once.Denotation.TraceMonad using (T)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.Program using (unlinkedT)
import Once.Spec.Core.Meaning S as GM
import Once.Spec.Core.Translate as TR
open TR using (ImpSig; TeleSig; mono-inst; poly-inst; telFind; viewOf) renaming (impAt to sigAt)
open import Once.Spec.Elaboration S using (ImportAt; ffi; def)
open import Once.Adequacy.CoreMeaningBridge fmt S using (refSem; impSem; Agree; NotOwn)

------------------------------------------------------------------------
-- Names that are not identifiers
------------------------------------------------------------------------

private
  cont-dot : ∀ (cs ds : List Char) → allIdentContinue (cs ++ '.' ∷ ds) ≡ false
  cont-dot []       ds = refl
  cont-dot (c ∷ cs) ds = trans (cong (_ ∧_) (cont-dot cs ds)) (∧-zeroʳ _)

  chars-dot : ∀ (cs ds : List Char) → validCharsB (cs ++ '.' ∷ ds) ≡ false
  chars-dot []       ds = refl
  chars-dot (c ∷ cs) ds = trans (cong (_ ∧_) (cont-dot cs ds)) (∧-zeroʳ _)

-- A dotted name is not an identifier.
dot-invalid : ∀ (a b : String) → validIdentB (a ++ˢ "." ++ˢ b) ≡ false
dot-invalid a b =
  trans (cong validCharsB (trans (toList-++ a ("." ++ˢ b)) (cong (toList a ++_) (toList-++ "." b))))
        (chars-dot (toList a) (toList b))

-- Nor is a canonical name that is not an own-module entry's.
notOwn-invalid : ∀ (cn : CanonicalName) → NotOwn cn → validIdentB (showCanonical cn) ≡ false
notOwn-invalid (canonical [])            _ = refl
notOwn-invalid (canonical (a ∷ b ∷ rest)) _ = dot-invalid a (showCanonical (canonical (b ∷ rest)))

------------------------------------------------------------------------
-- The environment of a scope, from the core's
------------------------------------------------------------------------

module _ (δ : GM.DefSem) where

  ffiSem : String → (U : Type) → Maybe (IsConcrete U) → T ⟦ U ⟧ᴰ
  ffiSem x U (just k) = sigOpRefᴰ fmt (bare x) k
  ffiSem x U nothing  = unlinkedT

  impEnv : ∀ {imps} → ImpSig S imps → ImpMeanings imps
  impEnv TR.[]                                = tt
  impEnv (TR.i-ffi {x = x} {T = U} _ _ is)    = ffiSem x U (isConcrete? U) , impEnv is
  impEnv (TR.i-def d e is)                    = refSem δ (mono-inst {S = S} e) , impEnv is

  defEnv : ∀ {ps} → TeleSig S ps → DefMeanings (C.buildPolyCtx ps)
  defEnv TR.[]                        = tt
  defEnv (TR.t-def {p = p} d e ts)    = (λ U ki → refSem δ (poly-inst {S = S} {sc = pfunType p} e ki)) , defEnv ts

  envOf : ∀ {imps ps} → ImpSig S imps → TeleSig S ps → Meanings (C.buildPolyCtx ps) imps
  envOf is ts = meanings (defEnv ts) (impEnv is)

  ----------------------------------------------------------------------
  -- Agreement
  ----------------------------------------------------------------------

  private
    ffiSem-k : ∀ x U (m : Maybe (IsConcrete U)) → isConcrete? U ≡ m → (k : IsConcrete U)
             → ffiSem x U m ≡ sigOpRefᴰ fmt (bare x) k
    ffiSem-k x U (just k′) _ k = cong (sigOpRefᴰ fmt (bare x)) (IsConcrete-irrelevant k′ k)
    ffiSem-k x U nothing eq k with isConcrete?-complete k
    ... | c , e with trans (sym e) eq
    ...   | ()

  agree-imp : ∀ {imps} (is : ImpSig S imps) {x U} (lk : lookupImport imps x ≡ just U) (k : IsConcrete U)
            → impAt imps x (impEnv is) lk ≡ impSem δ (bare x) k (sigAt {S = S} is lk)
  agree-imp TR.[] () k
  agree-imp {(n , T₀) ∷ rest} (TR.i-ffi h g is) {x} lk k with StrProp._≟_ n x
  ... | yes refl with lk
  ...   | refl = ffiSem-k x T₀ (isConcrete? T₀) refl k
  agree-imp {(n , T₀) ∷ rest} (TR.i-ffi h g is) {x} lk k | no _ = agree-imp is lk k
  agree-imp {(n , T₀) ∷ rest} (TR.i-def d e is) {x} lk k with StrProp._≟_ n x
  ... | yes refl with lk
  ...   | refl = refl
  agree-imp {(n , T₀) ∷ rest} (TR.i-def d e is) {x} lk k | no _ = agree-imp is lk k

  agree-def : ∀ {ps} (ts : TeleSig S ps) {x sc body prefix U}
                (lp : lookupPolyPrefix (C.buildPolyCtx ps) x ≡ just (sc , body , prefix)) (ki : KindedInstance sc U)
            → defAt (C.buildPolyCtx ps) x (defEnv ts) lp U ki ≡ refSem δ (poly-inst {S = S} {sc = sc} (proj₂ (telFind {S = S} ts lp)) ki)
  agree-def TR.[] () ki
  agree-def {C.mkPolyFunInfo n ty b ∷ ps} (TR.t-def d e ts) {x} lp ki with StrProp._≟_ n x
  ... | yes refl with lp
  ...   | refl = refl
  agree-def {C.mkPolyFunInfo n ty b ∷ ps} (TR.t-def d e ts) {x} lp ki | no _ = agree-def ts lp ki

  -- Every definition of the scope has an identifier for a name.
  DefsValid : ∀ {imps} → ImpSig S imps → Set
  DefsValid TR.[]                        = ⊤
  DefsValid (TR.i-ffi _ _ is)            = DefsValid is
  DefsValid (TR.i-def {x = x} _ _ is)    = (validIdentB x ≡ true) × DefsValid is

  IsFFI : ∀ {U} → ImportAt U → Set
  IsFFI (ffi _ _) = ⊤
  IsFFI (def _ _) = ⊥

  lookup-ffi : ∀ {imps} (is : ImpSig S imps) → DefsValid is → ∀ {q U} → validIdentB q ≡ false
             → (lk : lookupImport imps q ≡ just U) → IsFFI (sigAt {S = S} is lk)
  lookup-ffi TR.[] _ _ ()
  lookup-ffi {(n , T₀) ∷ rest} (TR.i-ffi h g is) dv {q} nv lk with StrProp._≟_ n q
  ... | yes refl with lk
  ...   | refl = tt
  lookup-ffi {(n , T₀) ∷ rest} (TR.i-ffi h g is) dv {q} nv lk | no _ = lookup-ffi is dv nv lk
  lookup-ffi {(n , T₀) ∷ rest} (TR.i-def d e is) (v , dv) {q} nv lk with StrProp._≟_ n q
  ... | yes refl with trans (sym v) nv
  ...   | ()
  lookup-ffi {(n , T₀) ∷ rest} (TR.i-def d e is) (v , dv) {q} nv lk | no _ = lookup-ffi is dv nv lk

  -- THE AGREEMENT, by construction.
  private
    ffi-sem : ∀ {U} (c : CanonicalName) (k : IsConcrete U) (i : ImportAt U) → IsFFI i → impSem δ c k i ≡ sigOpRefᴰ fmt c k
    ffi-sem c k (ffi _ _) _ = refl

  -- THE AGREEMENT, by construction.
  agree : ∀ {imps ps} (is : ImpSig S imps) (ts : TeleSig S ps) → DefsValid is
        → Agree (viewOf {S = S} is ts) (envOf is ts) δ
  agree is ts dv = record
    { agree-inst      = λ lp ng ki → agree-def ts lp ki
    ; agree-ground    = λ {x} {sc} lp g → agree-def ts lp (ground-kinded sc g)
    ; agree-import    = λ lk k → agree-imp is lk k
    ; agree-qualified = λ {name} {alias} lk k →
        ffi-sem _ k (sigAt {S = S} is lk) (lookup-ffi is dv (dot-invalid alias name) lk)
    ; agree-resolved  = λ {cn} no lk k →
        ffi-sem cn k (sigAt {S = S} is lk) (lookup-ffi is dv (notOwn-invalid cn no) lk)
    }
