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

module Once.Adequacy.SpecFront.Prefix where

open import Data.List using (List; []; _∷_; _++_; _ʳ++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Once.Lang.Contract using (ISig)
import Once.Lang.Core.PolyTy as LP
import Once.Lang.Core.Telescope as TL
import Once.Parser as Parser
open Parser.FunInfo using (funName; funType; funIsPrimitive)
open import Once.Lang.Module using (Scope; scope; ModTele; []; ffi; mono; poly; MainIn; entrySig)
open import Once.Lang.Core.Translate using (SigSig; s-ffi; ImpSig; TeleSig; SigCF; SigIn; toProgram)
open import Once.Adequacy.SpecFront.Extract using (FFIEntry; FFIFacts)

private
  t≢f : true ≡ false → ⊥
  t≢f ()

record Past {Fs s} (S : LP.Sig Fs s) (sc : Scope) (fs es : List Parser.Entry)
            (tl : TL.Tele S) (ss : SigSig Fs (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc)) (sgcf : SigCF S)
            (mt : ModTele sc (fs ++ es)) (mi : MainIn mt) (u : SigIn mt S) : Set where
  constructor past
  field
    mt′   : ModTele (scope (entrySig fs ʳ++ Scope.sig sc) (Scope.imps sc) (Scope.tele sc)) es
    ss′   : SigSig Fs (entrySig fs ʳ++ Scope.sig sc)
    mi′   : MainIn mt′
    u′    : SigIn mt′ S
    facts : All FFIFacts fs
    same  : toProgram tl ss is ts sgcf mt mi u ≡ toProgram tl ss′ is ts sgcf mt′ mi′ u′

prefix : ∀ {Fs s} {S : LP.Sig Fs s} {sc} (fs : List Parser.Entry) {es} → All FFIEntry fs
       → (tl : TL.Tele S) (ss : SigSig Fs (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc)) (sgcf : SigCF S)
       → (mt : ModTele sc (fs ++ es)) (mi : MainIn mt) (u : SigIn mt S) → Past S sc fs es tl ss is ts sgcf mt mi u
prefix [] [] tl ss is ts sgcf mt mi u = past mt ss mi u [] refl
prefix (Parser.e-fun (Parser.mkFunInfo x ft b p) ∷ fs) (fe ∷ fa) tl ss is ts sgcf (ffi {ty = ty} refl refl c h g rest) mi u =
  let past mt′ ss′ mi′ u′ facts same = prefix fs fa tl (s-ffi h g (u (here refl)) ss) is ts sgcf rest mi (λ m → u (there m))
  in past mt′ ss′ mi′ u′ ((refl , ty , refl , c , h , g) ∷ facts) same
prefix (Parser.e-fun (Parser.mkFunInfo x ft b p) ∷ fs) (fe ∷ fa) tl ss is ts sgcf (mono ep _ _ _ _ _) mi u = ⊥-elim (t≢f (trans (sym fe) ep))
prefix (Parser.e-poly _ ∷ fs) (() ∷ fa) tl ss is ts sgcf mt mi u
