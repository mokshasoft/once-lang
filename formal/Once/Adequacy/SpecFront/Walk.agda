-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Walk — the compiler's typed telescope is the
-- Spec's walk (plan 0.121 §3.6, F6).
--
-- The compiler types a module as a telescope of entries (`ModTele`), each
-- definition in the scope of those before it, and translates it into a core
-- program (`Translate`); the Spec walks the module's resolved declarations
-- (`Walk`), elaborating each definition. Given the declarations and the
-- entries aligned (`Align`: a definition with a signature, a polymorphic one,
-- one without; the other declarations skipped; each body related by `RX`)
-- and the entries' names new and classified (`EntriesOK`), the compiler's
-- telescope gives the Spec's walk, from the translated start to the
-- translated end (`walk`): each step's body checks at the term the
-- compiler's telescope holds and its type is principal (`Def`), in a scope
-- the walk keeps (`WalkState`).
--
-- Plan 0.122: the compiler's telescope IS the Spec's (`Translate` elaborates
-- into the Spec's core); a definition's term is its elaboration.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Spec.Name using (CanonicalName; canonical; NotGenerator)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
import Once.Internal.Type.WellFormed as LW
import Once.Spec.Type as ST
open import Once.Internal.Type using (wk₀)
open import Once.Internal.Typing.Scope using (Imports; lookupImport)
open import Once.Adequacy.SpecCore.Type using (TyR)

module Once.Adequacy.SpecFront.Walk
  (Σ : Signature) (ps : List String) (sg : Imports)
  -- the program's signature is the scope's FFI table (`Back`'s `h-sig`)…
  (h-sig : ∀ {m} (Δ : ST.KCtx m) {c t} → NotGenerator c → (c ∶ t) ∈ Σ
         → Σ[ T ∈ ST.Type ] (lookupImport sg (showCanonical c) ≡ just T) × LW.IsConcrete T × TyR Δ (wk₀ T) ⌜ t ⌝ᵈ)
  -- …and no polymorphic definition's name is a declaration's
  (h-own-sig : ∀ {x t} → x ∈ ps → ¬ ((canonical (x ∷ []) ∶ t) ∈ Σ))
  -- …nor an FFI declaration's (R11, D330)
  (h-psig : ∀ {x} → x ∈ ps → lookupImport sg x ≡ nothing)
  -- …and every declaration of Σ has a word name (D329)
  (h-word : ∀ {c t} → (c ∶ t) ∈ Σ → WordName c)
  where

open import Data.Nat using (zero; suc; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (_++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym; trans; cong; subst)

import Once.Internal.Type.Poly as TP
import Once.Spec.Core.Syntax as SC
import Once.Spec.Surface.Syntax as SX
import Once.Spec.Surface.Program as SPr
import Once.Spec.Core.Program Σ as SP
import Once.Spec.Grade
import Once.Spec.Surface.Typing
import Data.String
import Once.Compile as C
import Once.Parser as Parser
open Parser.FunInfo using (funName; funType; funBody; funIsPrimitive)
open Parser.PolyFunInfo using (pfunName; pfunType; pfunBody)
open import Once.Internal.Module using (Scope; scope; ModTele; []; ffi; mono; poly; addImp; addPoly; ctxOf; MonoBody)
open import Once.Internal.Type.Schema using (schemaOf)
open import Once.Internal.Type.Instance using (kindsOf; rigidOf)
import Once.Internal.Elaboration as E
open import Once.Internal.Core.Translate Σ
  using (SigSig; ImpSig; TeleSig; i-def; t-def; wkI; wkT; impDefs; monoSchema; monoDef; polyDef; viewOf; telFind; elabM; u0)
open import Once.Adequacy.SpecCore.Type using (tyR; TyR-≡)
open import Once.Adequacy.SpecFront.Expr using (RX)
import Once.Adequacy.SpecFront.ScopeNames as SN
open import Once.Adequacy.SpecFront.SchemaOf using (ground-arity; open-arity; schema-arrow)
open import Once.Adequacy.SpecFront.WalkState Σ ps
open import Once.Adequacy.SpecFront.End Σ ps using (EntryKind; End; end; endOf; no-ffi; all-tail)
import Once.Adequacy.SpecFront.Def as Def
open import Once.Adequacy.SpecFront.Align Σ using (Align; al-nil; al-skip; al-mono; al-nosig; al-poly)

open SPr using (Body; Principal; Walk; w-end; w-skip; w-sig; w-nosig)

------------------------------------------------------------------------
-- The bridges at a walk state
------------------------------------------------------------------------

private
  arrow-at : ∀ {sc} (sch : SC.Schema) → sch ≡ schemaOf sc → ∀ {sd sco π′} → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco
           → Σ[ X ∈ ST.Ty (SC.Schema.arity sch) ] Σ[ Y ∈ ST.Ty (SC.Schema.arity sch) ]
               (SC.Schema.type sch ≡ X ST.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] Y)
               × (∀ i → ST.Occurs i Y → ST.Occurs i X)
  arrow-at {sc} .(schemaOf sc) refl = schema-arrow sc

module AtState {s} {S : SC.Defs s} {imps tele} (ss : SigSig sg) (is : ImpSig S imps) (ts : TeleSig S tele)
               (nm : Fin s → CanonicalName) (w : WInv S (scope sg imps tele) is ts nm) =
  Def Σ S nm {imps} {sg} {C.buildPolyCtx tele} {ps} (viewOf {S = S} ss is ts)
      (λ lk → proj₁ (SN.h-imp-of Σ S nm is (WInv.imp-named w) lk))
      (SN.h-poly-of Σ S nm ts (WInv.tele-named w))
      (λ {x} {sc} lp g → trans (cong SC.Schema.arity (proj₂ (telFind {S = S} ts lp))) (ground-arity sc g))
      (λ {x} {sc} lp ng → subst (0 <_) (sym (cong SC.Schema.arity (proj₂ (telFind {S = S} ts lp)))) (open-arity sc ng))
      (λ {x} {sc} lp → arrow-at {sc} _ (proj₂ (telFind {S = S} ts lp)))
      (WInv.named w) h-sig (WInv.mono-at w) (WInv.ps-at w) (WInv.poly-at w) h-own-sig h-psig h-word

------------------------------------------------------------------------
-- The declarations and the entries
------------------------------------------------------------------------

-- The entries: definitions (`EntryKind`), their names distinct, new to the
-- scope and to the signature.
record EntriesOK (sc : Scope) (es : List Parser.Entry) : Set where
  field
    distinct : AllPairs _≢_ (map Parser.entryNameOf es)
    fresh    : All (λ x → All (x ≢_) (defNames sc)) (map Parser.entryNameOf es)
    nosig    : All (λ x → lookupImport sg x ≡ nothing) (map Parser.entryNameOf es)
    kinds    : All EntryKind es
open EntriesOK

private
  ap-head : ∀ {x : String} {xs} → AllPairs _≢_ (x ∷ xs) → All (x ≢_) xs
  ap-head (h ∷ _) = h
  ap-tail : ∀ {x : String} {xs} → AllPairs _≢_ (x ∷ xs) → AllPairs _≢_ xs
  ap-tail (_ ∷ t) = t

  -- the rest are new to the scope with one more definition of another name
  fresh-ins : ∀ {x} (as bs : List String) {ys : List String} → All (x ≢_) ys
            → All (λ y → All (y ≢_) (as ++ bs)) ys → All (λ y → All (y ≢_) (as ++ x ∷ bs)) ys
  fresh-ins as bs [] [] = []
  fresh-ins as bs (n ∷ ns) (h ∷ hs) = ins as h n ∷ fresh-ins as bs ns hs
    where
      ins : ∀ {x y} (as : List String) {bs} → All (y ≢_) (as ++ bs) → x ≢ y → All (y ≢_) (as ++ x ∷ bs)
      ins []       hs′       ne = (λ e → ne (sym e)) ∷ hs′
      ins (a ∷ as) (h′ ∷ hs′) ne = h′ ∷ ins as hs′ ne

  -- `main` (D324) leaves the scope as it was
  fresh-mono-at : ∀ {sc fi es} (b : Bool) (ty : ST.Type) → EntriesOK sc (Parser.e-fun fi ∷ es)
                → All (λ y → All (y ≢_) (defNames (scope (Scope.sig sc) (C.extendDefs-at b (Scope.imps sc) (funName fi) ty) (Scope.tele sc))))
                      (map Parser.entryNameOf es)
  fresh-mono-at true ty o = all-tail (fresh o)
  fresh-mono-at {sc} false ty o = fresh-ins [] (defNames sc) (ap-head (distinct o)) (all-tail (fresh o))

eok-mono : ∀ {sc fi es} (ty : ST.Type) → EntriesOK sc (Parser.e-fun fi ∷ es) → EntriesOK (addImp sc (funName fi) ty) es
eok-mono {fi = fi} ty o = record
  { distinct = ap-tail (distinct o)
  ; fresh    = fresh-mono-at (funName fi Data.String.== "main") ty o
  ; nosig    = all-tail (nosig o)
  ; kinds    = all-tail (kinds o)
  }

eok-poly : ∀ {sc pfi es} → EntriesOK sc (Parser.e-poly pfi ∷ es) → EntriesOK (addPoly sc pfi) es
eok-poly {sc} {pfi} o =
  record { distinct = ap-tail (distinct o)
         ; fresh = fresh-ins (map proj₁ (Scope.imps sc)) (map pfunName (Scope.tele sc)) (ap-head (distinct o)) (all-tail (fresh o))
         ; nosig = all-tail (nosig o) ; kinds = all-tail (kinds o) }

------------------------------------------------------------------------
-- The walk
------------------------------------------------------------------------

private
  all-head : ∀ {a} {X : Set a} {P : X → Set} {x xs} → All P (x ∷ xs) → P x
  all-head (h ∷ _) = h

  head-poly : ∀ {pfi es} → All EntryKind (Parser.e-poly pfi ∷ es) → pfunName pfi ∈ ps
  head-poly (h ∷ _) = h

walk : ∀ {s} {S : SC.Defs s} {imps tele es ds}
         (tl : SP.Tele S) (ss : SigSig sg) (is : ImpSig S imps) (ts : TeleSig S tele) (nm : Fin s → CanonicalName)
       → (mt : ModTele (scope sg imps tele) es) → Align ds es → (w : WInv S (scope sg imps tele) is ts nm)
       → (o : EntriesOK (scope sg imps tele) es)
       → let e = endOf tl ss is ts nm mt (kinds o)
         in Walk Σ S nm tl ds (End.S e) (End.nm e) (End.tl e)
walk tl ss is ts nm mt (al-skip nd al) w o = w-skip nd (walk tl ss is ts nm mt al w o)
walk tl ss is ts nm [] al-nil w o = w-end
{-# CATCHALL #-}
walk tl ss is ts nm (ffi ep _ _ _ _ _) _ w o = ⊥-elim (no-ffi ep (kinds o))
-- a telescope definition
walk {S = S} {imps} {tele} tl ss is ts nm (poly {pfi = pfi@(Parser.mkPolyFunInfo x T e)} {Ψ = Ψ} pr D rest) (al-poly so _ rx al) w o =
  w-sig so b (AtState.principal ss is ts nm w κ pr rx (tyR _))
    (walk (polyDef {S = S} {sc = scope sg imps tele} {pfi = pfi} {Ψ = Ψ} tl ss is ts D) ss (wkI is) (t-def zero refl (wkT ts))
          (canonical (x ∷ []) ∷ⁿ nm) rest al (winv-poly pfi w (head-poly (kinds o)) (all-head (fresh o))) (eok-poly o))
  where
    κ = kindsOf T
    el = E.elabᶜ Σ S (viewOf {S = S} ss is ts) D
    b : Body Σ S nm (schemaOf T) _
    b = record
      { term  = proj₁ el
      ; check = AtState.body-check ss is ts nm w κ D rx (tyR _)
      ; typed = u0 (proj₂ el)
      }
-- a monomorphic definition with a signature
walk {S = S} {imps} {tele} tl ss is ts nm (mono {fi = fi@(Parser.mkFunInfo x (just ty) e false)} {ty = .ty} {Ψ = Ψ} ep refl pr g D rest) (al-mono so _ rx al) w o =
  w-sig so b (AtState.principal ss is ts nm w ST.∅ₖ pr rx (tyR _))
    (walk (monoDef {S = S} {sc = scope sg imps tele} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D) ss (impDefs (x Data.String.== "main") is) (wkT ts)
          (canonical (x ∷ []) ∷ⁿ nm) rest al
          (winv-mono w (proj₂ (all-head (kinds o))) (all-head (nosig o)) (all-head (fresh o))) (eok-mono ty o))
  where
    el = elabM {S = S} (just ty) (viewOf {S = S} ss is ts) D
    b : Body Σ S nm (monoSchema ty) _
    b = record
      { term  = proj₁ el
      ; check = AtState.body-check ss is ts nm w ST.∅ₖ D rx (tyR _)
      ; typed = u0 (proj₂ el)
      }
-- one without: the type its body synthesizes
walk {S = S} {imps} {tele} tl ss is ts nm (mono {fi = fi@(Parser.mkFunInfo x nothing e false)} {ty = ty} {Ψ = Ψ} ep er pr g D rest) (al-nosig rx al) w o =
  w-nosig
    (subst (λ A′ → Once.Spec.Surface.Typing._⊢_⇒_↝_ Σ S nm ST.∅ₖ Once.Spec.Surface.Typing.∅ _ A′ _)
           (sym (TyR-≡ (proj₁ (proj₂ syn)))) (proj₂ (proj₂ syn)))
    (u0 (proj₂ el))
    (AtState.principal ss is ts nm w ST.∅ₖ pr rx (tyR _))
    (walk (monoDef {S = S} {sc = scope sg imps tele} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D) ss (impDefs (x Data.String.== "main") is) (wkT ts)
          (canonical (x ∷ []) ∷ⁿ nm) rest al
          (winv-mono w (proj₂ (all-head (kinds o))) (all-head (nosig o)) (all-head (fresh o))) (eok-mono ty o))
  where
    el = elabM {S = S} nothing (viewOf {S = S} ss is ts) D
    syn = AtState.body-synth ss is ts nm w ST.∅ₖ D rx
