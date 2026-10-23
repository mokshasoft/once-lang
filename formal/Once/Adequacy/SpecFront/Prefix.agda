-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Prefix — the FFI declarations at the head of the
-- compiler's typed telescope (plan 0.121 §3.6, F6).
--
-- The extractor puts the `signature` declarations first (`sigsFirst`); in the
-- typed telescope each is an FFI entry (`ffi`), which extends the scope's
-- signature table and nothing else. Past them (`prefix`): the scope holds
-- the table, in reverse (`ʳ++`), the entries' facts are the telescope's, and
-- the core program built from the whole telescope is the one built from the
-- rest, the table recorded (`SigSig`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecFront.Prefix where

open import Data.List using (List; []; _∷_; _++_; _ʳ++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Once.Spec.Core.Syntax using (Defs)
import Once.Spec.Core.Program
import Once.Parser as Parser
open Parser.FunInfo using (funName; funType; funIsPrimitive)
open import Once.Internal.Module using (Scope; scope; ModTele; []; ffi; mono; poly; MainIn; MainsEffUU; entrySig)
open import Once.Adequacy.SpecFront.Extract using (FFIEntry; FFIFacts)

private
  t≢f : true ≡ false → ⊥
  t≢f ()

module _ (Σ : Signature) where

  private
    module TL = Once.Spec.Core.Program Σ
  open import Once.Internal.Core.Translate Σ using (SigSig; s-ffi; ImpSig; TeleSig; SigIn; toProgram)

  record Past {s} (S : Defs s) (sc : Scope) (fs es : List Parser.Entry)
              (tl : TL.Tele S) (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
              (mt : ModTele sc (fs ++ es)) (mi : MainIn mt) (u : SigIn mt) : Set where
    constructor past
    field
      mt′   : ModTele (scope (entrySig fs ʳ++ Scope.sig sc) (Scope.imps sc) (Scope.tele sc)) es
      ss′   : SigSig (entrySig fs ʳ++ Scope.sig sc)
      mi′   : MainIn mt′
      u′    : SigIn mt′
      facts : All FFIFacts fs
      same  : toProgram tl ss is ts mt mi u ≡ toProgram tl ss′ is ts mt′ mi′ u′

  prefix : ∀ {s} {S : Defs s} {sc} (fs : List Parser.Entry) {es} → All FFIEntry fs
         → (tl : TL.Tele S) (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
         → (mt : ModTele sc (fs ++ es)) (mi : MainIn mt) (u : SigIn mt) → Past S sc fs es tl ss is ts mt mi u
  prefix [] [] tl ss is ts mt mi u = past mt ss mi u [] refl
  prefix (Parser.e-fun (Parser.mkFunInfo x ft b p) ∷ fs) (fe ∷ fa) tl ss is ts (ffi {ty = ty} refl refl c h rest) mi u =
    let past mt′ ss′ mi′ u′ facts same = prefix fs fa tl (s-ffi c h (u (here refl)) ss) is ts rest mi (λ m → u (there m))
    in past mt′ ss′ mi′ u′ ((refl , ty , refl , c , h) ∷ facts) same
  prefix (Parser.e-fun (Parser.mkFunInfo x ft b p) ∷ fs) (fe ∷ fa) tl ss is ts (mono ep _ _ _ _) mi u = ⊥-elim (t≢f (trans (sym fe) ep))
  prefix (Parser.e-poly _ ∷ fs) (() ∷ fa) tl ss is ts mt mi u

  -- (the FFI entries' facts alone)

ffi-facts : ∀ {sc} (fs : List Parser.Entry) {es} → All FFIEntry fs → ModTele sc (fs ++ es) → All FFIFacts fs
ffi-facts [] [] mt = []
ffi-facts (Parser.e-fun (Parser.mkFunInfo x ft b p) ∷ fs) (fe ∷ fa) (ffi {ty = ty} refl refl c h rest) = (refl , ty , refl , c , h) ∷ ffi-facts fs fa rest
ffi-facts (Parser.e-fun (Parser.mkFunInfo x ft b p) ∷ fs) (fe ∷ fa) (mono ep _ _ _ _) = ⊥-elim (t≢f (trans (sym fe) ep))
ffi-facts (Parser.e-poly _ ∷ fs) (() ∷ fa) mt

-- (`main`: a monomorphic entry)
main-entry : ∀ {sc es} (mt : ModTele sc es) → MainIn mt
           → Σ[ fi ∈ Parser.FunInfo ] (Parser.e-fun fi ∈ es) × (funName fi ≡ "main")
main-entry [] ()
main-entry (ffi _ _ _ _ rest) mi = let (fi , m , e) = main-entry rest mi in fi , there m , e
main-entry (poly _ _ rest) mi = let (fi , m , e) = main-entry rest mi in fi , there m , e
main-entry (mono {fi = fi} _ _ _ _ rest) (inj₁ (e , _)) = fi , here refl , e
main-entry (mono _ _ _ _ rest) (inj₂ mi) = let (fi , m , e) = main-entry rest mi in fi , there m , e

-- Conversely (plan 0.121 `complete`): FFI entries with the telescope's facts
-- head a telescope of the rest, in the scope past them; `main` is as the
-- rest has it.
prefix← : ∀ {sc} (fs : List Parser.Entry) {es} → All FFIFacts fs
        → (mt : ModTele (scope (entrySig fs ʳ++ Scope.sig sc) (Scope.imps sc) (Scope.tele sc)) es)
        → Σ[ mt′ ∈ ModTele sc (fs ++ es) ] (MainsEffUU mt → MainsEffUU mt′) × (MainIn mt → MainIn mt′)
prefix← [] [] mt = mt , (λ m → m) , (λ m → m)
prefix← {sc} (Parser.e-fun (Parser.mkFunInfo x ft b p) ∷ fs) ((refl , ty , refl , c , h) ∷ fa) mt =
  let (mt′ , ms , mi) = prefix← {sc = scope ((x , ty) ∷ Scope.sig sc) (Scope.imps sc) (Scope.tele sc)} fs fa mt
  in ffi refl refl c h mt′ , ms , mi
prefix← (Parser.e-poly _ ∷ fs) (() ∷ fa) mt
