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
-- A definition without a signature is at the Spec's `schema 0 ∅ₖ A`; the
-- translated schema's kinds are `kindsS noKinds`, the same function out of
-- the empty type, equal by function extensionality (P1).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Internal.Contract using (ISig)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Spec.Name using (CanonicalName; canonical; NotGenerator)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
open import Once.Spec.Numerics using (TargetNum)
import Once.Internal.Type as LT
import Once.Spec.Type as LT
import Once.Internal.Type.WellFormed as LW
import Once.Spec.Type as LW
import Once.Spec.Type as ST
open import Once.Internal.Typing.Scope using (Imports; lookupImport)
open import Once.Adequacy.SpecCore.Type using (TyR)
open import Once.Internal.Core.Decl using (declS)

module Once.Adequacy.SpecFront.Walk
  (Σ : Signature) {Fs : ISig}
  (sigop-S : ∀ {c A} → WordName c → (showCanonical c , A) ∈ Fs → (c ∶ declS A) ∈ Σ)
  (fmt : TargetNum) (ps : List String) (sg : Imports)
  -- the program's signature is the scope's FFI table (`Back`'s `h-sig`)…
  (h-sig : ∀ {m} (Δ : ST.KCtx m) {c t} → NotGenerator c → (c ∶ t) ∈ Σ
         → Σ[ T ∈ LT.Type ] (lookupImport sg (showCanonical c) ≡ just T) × LW.IsConcrete T × TyR Δ T ⌜ t ⌝ᵈ)
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
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym; trans; cong; subst)
import Data.String.Properties as StrProp

open import Once.Postulates using (extensionality)
import Once.Internal.Type.Poly as TP
import Once.Internal.Core.PolyTy as LP
import Once.Internal.Core.Telescope as TL
open import Once.Internal.Core.AbsTy using (ConstFree; ConstFreeF; absTy-ground; cf-var; cf-Unit; cf-Void; cf-Int; cf-Float; cf-*; cf-+; cf-⇒; cf-μ; cf-ν; cf-K; cf-Id; cf-⊕; cf-⊗)
import Once.Internal.Core.Abstract as A
import Once.Spec.Core.Syntax as SC
import Once.Spec.Surface.Syntax as SX
import Once.Spec.Surface.Program as SPr
import Once.Spec.Core.Program Σ as SP
import Once.Spec.Surface.Typing
import Once.Spec.Core.Typing
import Once.Spec.Context
import Once.Spec.Grade
import Once.Spec.Grade
import Data.String
import Once.Compile as C
import Once.Parser as Parser
open Parser.FunInfo using (funName; funType; funBody; funIsPrimitive)
open Parser.PolyFunInfo using (pfunName; pfunType; pfunBody)
open import Once.Internal.Module using (Scope; scope; ModTele; []; ffi; mono; poly; addImp; addPoly; ctxOf; MonoBody)
open import Once.Internal.Core.Schema using (schemaOf; kindsOf; schemaOf-cf)
open import Once.Internal.Core.Translate
  using (SigSig; ImpSig; TeleSig; SigCF; i-def; t-def; wkI; wkT; impDefs; monoSchema; monoDef; polyDef; monoSg; polySg; viewOf; telFind;
         monoElab; monoBody; polyElab; polyBody; ground-cf)
open import Once.Adequacy.SpecCore.Schema using (Clean; CleanF; CleanSig; c-var; c-Unit; c-Void; c-Int; c-Float; c-*; c-+; c-⇒; c-μ; c-ν; c-K; c-Id; c-⊕; c-⊗; defsS; schS; ptyS; kindsS)
open import Once.Adequacy.SpecCore.Type using (TyR-uniqueˢ)
open import Once.Adequacy.SpecCore.Poly using (module Translate)
import Once.Adequacy.SpecCore.Program as PG
open import Once.Adequacy.SpecFront.Expr using (RX)
open import Once.Adequacy.SpecFront.ScopeNames using (h-imp-of; h-poly-of)
open import Once.Adequacy.SpecFront.SchemaOf using (ground-arity; open-arity; schema-occ; schema-arrow)
open import Once.Adequacy.SpecFront.WalkState {Fs} Σ ps
open import Once.Adequacy.SpecFront.End {Fs} Σ ps using (EntryKind; End; end; endOf; no-ffi; all-tail)
import Once.Adequacy.SpecFront.Def as Def
open import Once.Adequacy.SpecFront.Align Σ using (Align; al-nil; al-skip; al-mono; al-nosig; al-poly)
open import Once.Adequacy.SpecFront.AbsR using (cf-R)
import Once.Internal.Type.Instance

open SPr using (SchemaOf; Body; Principal; NotDefinition; Walk; w-end; w-skip; w-sig; w-nosig)

private
  module TP′ = Translate
  teleS : ∀ {s} {S : LP.Sig Fs s} → TL.Tele S → SP.Tele (defsS S)
  teleS tl = PG.teleS Σ sigop-S fmt tl

------------------------------------------------------------------------
-- A constant-free type has no rigid constant
------------------------------------------------------------------------

mutual
  cf→clean : ∀ {a} {A : LP.Ty a} → ConstFree A → Clean A
  cf→clean cf-var     = c-var
  cf→clean cf-Unit    = c-Unit
  cf→clean cf-Void    = c-Void
  cf→clean cf-Int     = c-Int
  cf→clean cf-Float   = c-Float
  cf→clean (cf-* a b) = c-* (cf→clean a) (cf→clean b)
  cf→clean (cf-+ a b) = c-+ (cf→clean a) (cf→clean b)
  cf→clean (cf-⇒ a b) = c-⇒ (cf→clean a) (cf→clean b)
  cf→clean (cf-μ f)   = c-μ (cfF→clean f)
  cf→clean (cf-ν f)   = c-ν (cfF→clean f)

  cfF→clean : ∀ {a} {F : LP.Fun a} → ConstFreeF F → CleanF F
  cfF→clean (cf-K a)   = c-K (cf→clean a)
  cfF→clean cf-Id      = c-Id
  cfF→clean (cf-⊕ f g) = c-⊕ (cfF→clean f) (cfF→clean g)
  cfF→clean (cf-⊗ f g) = c-⊗ (cfF→clean f) (cfF→clean g)

------------------------------------------------------------------------
-- The bridges at a walk state
------------------------------------------------------------------------

private
  occ-at : ∀ {sc} (sch : LP.Schema) → sch ≡ schemaOf sc → ∀ i → ST.Occurs i (ptyS (LP.Schema.type sch))
  occ-at {sc} .(schemaOf sc) refl = schema-occ sc

  arrow-at : ∀ {sc} (sch : LP.Schema) → sch ≡ schemaOf sc → ∀ {sd sco π′} → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco
           → Σ[ X ∈ LP.Ty (LP.Schema.arity sch) ] Σ[ Y ∈ LP.Ty (LP.Schema.arity sch) ]
               (LP.Schema.type sch ≡ X LP.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] Y)
               × (∀ i → ST.Occurs i (ptyS Y) → ST.Occurs i (ptyS X))
  arrow-at {sc} .(schemaOf sc) refl = schema-arrow sc

module AtState {s} {S : LP.Sig Fs s} {imps tele} (ss : SigSig Fs sg) (is : ImpSig S imps) (ts : TeleSig S tele)
               (sgcf : SigCF S) (nm : Fin s → CanonicalName) (w : WInv S (scope sg imps tele) is ts nm) =
  Def S Σ sigop-S nm (λ d → cf→clean (sgcf d)) {imps} {sg} {C.buildPolyCtx tele} {ps} (viewOf {S = S} ss is ts)
      (h-imp-of S nm is (WInv.imp-named w))
      (h-poly-of S nm ts (WInv.tele-named w))
      (λ {x} {sc} lp g → trans (cong LP.Schema.arity (proj₂ (telFind ts lp))) (ground-arity sc g))
      (λ {x} {sc} lp ng → subst (0 <_) (sym (cong LP.Schema.arity (proj₂ (telFind ts lp)))) (open-arity sc ng))
      (λ {x} {sc} lp → occ-at {sc} _ (proj₂ (telFind ts lp)))
      (λ {x} {sc} lp → arrow-at {sc} _ (proj₂ (telFind ts lp)))
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
  fresh-mono-at : ∀ {sc fi es} (b : Bool) (ty : LT.Type) → EntriesOK sc (Parser.e-fun fi ∷ es)
                → All (λ y → All (y ≢_) (defNames (scope (Scope.sig sc) (C.extendDefs-at b (Scope.imps sc) (funName fi) ty) (Scope.tele sc))))
                      (map Parser.entryNameOf es)
  fresh-mono-at true ty o = all-tail (fresh o)
  fresh-mono-at {sc} false ty o = fresh-ins [] (defNames sc) (ap-head (distinct o)) (all-tail (fresh o))

eok-mono : ∀ {sc fi es} (ty : LT.Type) → EntriesOK sc (Parser.e-fun fi ∷ es) → EntriesOK (addImp sc (funName fi) ty) es
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

-- a ground type, at its (variable-free) schema's type
ground-A : ∀ {ty} → LW.RigidFree ty → TyR (kindsS TL.noKinds) ty (ptyS (LP.⌈_⌉ {0} ty))
ground-A {ty} g =
  subst (λ X → TyR (kindsS TL.noKinds) ty (ptyS X)) (absTy-ground TL.noKinds g)
        (cf-R TL.noKinds ty (subst ConstFree (sym (absTy-ground TL.noKinds g)) (ground-cf g)))

-- `kindsS noKinds` is the Spec's empty kinds
noKinds-S : kindsS TL.noKinds ≡ ST.∅ₖ
noKinds-S = extensionality (λ ())

private
  fin0 : Fin 0 → ⊥
  fin0 ()


  all-head : ∀ {a} {X : Set a} {P : X → Set} {x xs} → All P (x ∷ xs) → P x
  all-head (h ∷ _) = h

  head-poly : ∀ {pfi es} → All EntryKind (Parser.e-poly pfi ∷ es) → pfunName pfi ∈ ps
  head-poly (h ∷ _) = h


  -- a definition without a signature, at kinds equal to the empty ones
  nosig-at : ∀ {s′} {S′ : SC.Defs s′} {nm : Fin s′ → CanonicalName} {tl : SP.Tele S′} {x e′ ds s″} {S″ : SC.Defs s″} {nm″ tl″}
             {k : ST.KCtx 0} (ek : k ≡ ST.∅ₖ) {A t}
           → Once.Spec.Surface.Typing._⊢_⇒_↝_ Σ S′ nm k Once.Spec.Surface.Typing.∅ e′ A t
           → (typed : Once.Spec.Core.Typing._⊩_⊢[_]_∷_!_ Σ S′ k Once.Spec.Context.∅ Once.Spec.Context.[] t A Once.Spec.Grade.pure)
           → Principal Σ S′ nm (SC.schema 0 k A) e′
           → Walk Σ (S′ SC.▷ SC.schema 0 k A) (canonical (x ∷ []) ∷ⁿ nm) (SP.def tl (SC.schema 0 k A) t typed) ds S″ nm″ tl″
           → Walk Σ S′ nm tl (SX.DFunDef x e′ ∷ ds) S″ nm″ tl″
  nosig-at refl syn typed pr rest = w-nosig syn typed pr rest

walk : ∀ {s} {S : LP.Sig Fs s} {imps tele es ds}
         (tl : TL.Tele S) (ss : SigSig Fs sg) (is : ImpSig S imps) (ts : TeleSig S tele) (sgcf : SigCF S) (nm : Fin s → CanonicalName)
       → (mt : ModTele (scope sg imps tele) es) → Align ds es → (w : WInv S (scope sg imps tele) is ts nm)
       → (o : EntriesOK (scope sg imps tele) es)
       → let e = endOf tl ss is ts sgcf nm mt (kinds o)
         in Walk Σ (defsS S) nm (teleS tl) ds (defsS (End.S e)) (End.nm e) (teleS (End.tl e))
walk tl ss is ts sgcf nm mt (al-skip nd al) w o = w-skip nd (walk tl ss is ts sgcf nm mt al w o)
walk tl ss is ts sgcf nm [] al-nil w o = w-end
{-# CATCHALL #-}
walk tl ss is ts sgcf nm (ffi ep _ _ _ _ _) _ w o = ⊥-elim (no-ffi ep (kinds o))
-- a telescope definition
walk {S = S} {imps} {tele} tl ss is ts sgcf nm (poly {pfi = pfi@(Parser.mkPolyFunInfo x T e)} {Ψ = Ψ} pr D rest) (al-poly so _ rx al) w o =
  w-sig so b (AtState.principal ss is ts sgcf nm w κ pr rx rA)
    (walk (polyDef {S = S} {sc = scope sg imps tele} {pfi = pfi} {Ψ = Ψ} tl ss is ts sgcf D) ss (wkI is) (t-def zero refl (wkT ts))
          (polySg sgcf pfi) (canonical (x ∷ []) ∷ⁿ nm) rest al (winv-poly pfi w (head-poly (kinds o)) (all-head (fresh o))) (eok-poly o))
  where
    κ = kindsOf T
    rA = cf-R κ (Once.Internal.Type.Instance.rigidOf T) (schemaOf-cf T)
    b : Body Σ (defsS S) nm (schS (schemaOf T)) _
    b = record
      { term  = TP′.ptmS S Σ sigop-S (A.absTm S κ (proj₁ (polyElab {S = S} {sc = scope sg imps tele} {pfi = pfi} {Ψ = Ψ} ss is ts D)))
      ; check = AtState.body-check ss is ts sgcf nm w κ D rx rA
      ; typed = TP′.trD S Σ sigop-S (polyBody {S = S} {sc = scope sg imps tele} {pfi = pfi} {Ψ = Ψ} ss is ts sgcf D)
      }
-- a monomorphic definition with a signature
walk {S = S} {imps} {tele} tl ss is ts sgcf nm (mono {fi = fi@(Parser.mkFunInfo x (just ty) e false)} {ty = .ty} {Ψ = Ψ} ep refl pr g D rest) (al-mono so _ rx al) w o =
  w-sig so b (AtState.principal ss is ts sgcf nm w TL.noKinds pr rx (ground-A g))
    (walk (monoDef {S = S} {sc = scope sg imps tele} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sgcf g D) ss (impDefs (x Data.String.== "main") is) (wkT ts)
          (monoSg sgcf g) (canonical (x ∷ []) ∷ⁿ nm) rest al
          (winv-mono w g (proj₂ (all-head (kinds o))) (all-head (nosig o)) (all-head (fresh o))) (eok-mono ty o))
  where
    b : Body Σ (defsS S) nm (schS (monoSchema ty)) _
    b = record
      { term  = TP′.ptmS S Σ sigop-S (A.absTm S TL.noKinds (proj₁ (monoElab {S = S} {sc = scope sg imps tele} {fi = fi} {ty = ty} {Ψ = Ψ} ss is ts D)))
      ; check = AtState.body-check ss is ts sgcf nm w TL.noKinds D rx (ground-A g)
      ; typed = TP′.trD S Σ sigop-S (monoBody {S = S} {sc = scope sg imps tele} {fi = fi} {ty = ty} {Ψ = Ψ} ss is ts sgcf g D)
      }
-- one without: the type its body synthesizes
walk {S = S} {imps} {tele} tl ss is ts sgcf nm (mono {fi = fi@(Parser.mkFunInfo x nothing e false)} {ty = ty} {Ψ = Ψ} ep er pr g D rest) (al-nosig rx al) w o =
  nosig-at noKinds-S
    (subst (λ A′ → Once.Spec.Surface.Typing._⊢_⇒_↝_ Σ (defsS S) nm (kindsS TL.noKinds) Once.Spec.Surface.Typing.∅ _ A′ _)
           (TyR-uniqueˢ (proj₁ (proj₂ syn)) (ground-A g)) (proj₂ (proj₂ syn)))
    (TP′.trD S Σ sigop-S (monoBody {S = S} {sc = scope sg imps tele} {fi = fi} {ty = ty} {Ψ = Ψ} ss is ts sgcf g D))
    (AtState.principal ss is ts sgcf nm w TL.noKinds pr rx (ground-A g))
    (walk (monoDef {S = S} {sc = scope sg imps tele} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sgcf g D) ss (impDefs (x Data.String.== "main") is) (wkT ts)
          (monoSg sgcf g) (canonical (x ∷ []) ∷ⁿ nm) rest al
          (winv-mono w g (proj₂ (all-head (kinds o))) (all-head (nosig o)) (all-head (fresh o))) (eok-mono ty o))
  where
    syn = AtState.body-synth ss is ts sgcf nm w TL.noKinds D rx
