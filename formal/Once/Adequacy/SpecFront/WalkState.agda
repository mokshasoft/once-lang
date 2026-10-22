-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.WalkState — the scope facts along the telescope
-- walk (plan 0.121 §3.6, F6).
--
-- The two typing bridges ask the same things of a definition's scope: that the
-- name a Spec reference resolves to is the compiler's lookup of that name —
-- a monomorphic definition in the definitions table at its type, a
-- polymorphic one in the telescope with its schema (`Back`'s `h-…`), and the
-- entries the compiler's lookups find named so (`Check`'s, via `ScopeNames`).
-- `WInv` collects them for a walk state: the compiler's signature `S` and
-- scope, the core entries recorded for it (`ImpSig`/`TeleSig`), and the Spec's
-- names `nm`. It holds of the empty state and is kept by each definition,
-- given that the definition's name is new to the scope and is polymorphic
-- exactly when it is one of `ps`, the module's polymorphic names.
------------------------------------------------------------------------

open import Data.List using (List)
open import Data.String using (String)
open import Once.Internal.Contract using (ISig)

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecFront.WalkState {Fs : ISig} (Σ : Signature) (ps : List String) where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
import Data.String.Properties as StrProp

import Once.Internal.Type as LT

import Once.Spec.Type as LT
import Once.Internal.Type.WellFormed as LW
import Once.Spec.Type as LW
import Once.Internal.Core.PolyTy as LP
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
import Once.Compile as C
import Once.Parser as Parser
open Parser.PolyFunInfo using (pfunName; pfunType; pfunBody)
open import Once.Spec.Name using (CanonicalName; canonical)
import Once.Spec.Surface.Program
open import Once.Internal.Typing.Scope using (Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.Internal.Module using (Scope; scope; emptyScope; addImp; addPoly)
open import Once.Internal.Core.Schema using (schemaOf)
open import Once.Internal.Core.Translate using (ImpSig; TeleSig; []; i-def; t-def; wkI; wkT; impDefs; monoSchema)
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.Schema using (defsS; schS; ptyS; pfunS)
open import Once.Adequacy.SpecFront.ScopeNames using (ImpNamed; TeleNamed)
import Once.Adequacy.SpecFront.Scope as Sc
import Once.Adequacy.SpecFront.Inst as In
open import Once.Adequacy.TelePosition using (lookup-head; lookup-skip)

------------------------------------------------------------------------
-- The scope's names
------------------------------------------------------------------------

-- The definitions in scope (monomorphic ones and the telescope's).
defNames : Scope → List String
defNames sc = map proj₁ (Scope.imps sc) ++ map pfunName (Scope.tele sc)

-- (the Spec's walk's: a new definition's name before the others)
_∷ⁿ_ : ∀ {s} → CanonicalName → (Fin s → CanonicalName) → Fin (suc s) → CanonicalName
c ∷ⁿ nm = Once.Spec.Surface.Program._∷ⁿ_ Σ c nm

private
  canon-inj : ∀ {x y : String} → canonical (x ∷ []) ≡ canonical (y ∷ []) → x ≡ y
  canon-inj refl = refl

  -- a name found by a lookup is one of the table's
  imp-in : ∀ (imps : Imports) {y T} → lookupImport imps y ≡ just T → y ∈ map proj₁ imps
  imp-in [] ()
  imp-in ((n , T₀) ∷ rest) {y} lk with StrProp._≟_ n y
  ... | yes e = here (sym e)
  ... | no _  = there (imp-in rest lk)

  tele-in : ∀ (tele : List Parser.PolyFunInfo) {y r} → lookupPolyPrefix (C.buildPolyCtx tele) y ≡ just r → y ∈ map pfunName tele
  tele-in [] ()
  tele-in (p ∷ tele) {y} lp with StrProp._≟_ (pfunName p) y
  ... | yes e = here (sym e)
  ... | no _  = there (tele-in tele lp)

  -- a name no entry has is not found
  imp-none : ∀ (imps : Imports) {y} → ¬ (y ∈ map proj₁ imps) → lookupImport imps y ≡ nothing
  imp-none [] _ = refl
  imp-none ((n , T₀) ∷ rest) {y} ∉ with StrProp._≟_ n y
  ... | yes e = ⊥-elim (∉ (here (sym e)))
  ... | no _  = imp-none rest (λ m → ∉ (there m))

  imp-head : ∀ (imps : Imports) x T → lookupImport ((x , T) ∷ imps) x ≡ just T
  imp-head imps x T with StrProp._≟_ x x
  ... | yes _ = refl
  ... | no ¬e = ⊥-elim (¬e refl)

  imp-skip : ∀ (imps : Imports) {x y} T → x ≢ y → lookupImport ((x , T) ∷ imps) y ≡ lookupImport imps y
  imp-skip imps {x} {y} T ne with StrProp._≟_ x y
  ... | yes e = ⊥-elim (ne e)
  ... | no _  = refl

  ∉-all : ∀ {x : String} {xs : List String} → All (x ≢_) xs → ¬ (x ∈ xs)
  ∉-all (h ∷ hs) (here e)  = h e
  ∉-all (h ∷ hs) (there m) = ∉-all hs m

  all-ˡ : ∀ {x : String} (as : List String) {bs} → All (x ≢_) (as ++ bs) → All (x ≢_) as
  all-ˡ []       _        = []
  all-ˡ (a ∷ as) (h ∷ hs) = h ∷ all-ˡ as hs

  all-ʳ : ∀ {x : String} (as : List String) {bs} → All (x ≢_) (as ++ bs) → All (x ≢_) bs
  all-ʳ []       hs       = hs
  all-ʳ (a ∷ as) (h ∷ hs) = all-ʳ as hs

  ne-of : ∀ {x y : String} {xs : List String} → All (x ≢_) xs → y ∈ xs → x ≢ y
  ne-of (h ∷ hs) (here refl) = h
  ne-of (h ∷ hs) (there m)   = ne-of hs m

------------------------------------------------------------------------
-- A ground type, at any instance of its (variable-free) schema
------------------------------------------------------------------------

mutual
  ground-R : ∀ {m k} {Δ : ST.KCtx m} {A : LT.Type} (τ : ST.TySub k m) → LW.RigidFree A → TyR Δ A (ptyS (LP.⌈_⌉ {k} A) ST.⟨ τ ⟩)
  ground-R τ LW.rf-Unit   = r-unit
  ground-R τ LW.rf-Void   = r-void
  ground-R τ LW.rf-Int    = r-int
  ground-R τ LW.rf-Float  = r-float
  ground-R τ (LW.rf-* a b) = r-* (ground-R τ a) (ground-R τ b)
  ground-R τ (LW.rf-+ a b) = r-+ (ground-R τ a) (ground-R τ b)
  ground-R τ (LW.rf-⇒ a b) = r-⇒ refl (ground-R τ a) (ground-R τ b)
  ground-R τ (LW.rf-μ f)   = r-μ (groundF-R τ f)
  ground-R τ (LW.rf-ν f)   = r-ν refl (groundF-R τ f)

  groundF-R : ∀ {m k} {Δ : ST.KCtx m} {F : LT.Functor} (τ : ST.TySub k m) → LW.RigidFreeF F → FunR Δ F (pfunS (LP.⌈_⌉F {k} F) ST.⟨ τ ⟩F)
  groundF-R τ (LW.rf-K a)   = r-K (ground-R τ a)
  groundF-R τ LW.rf-Id      = r-Id
  groundF-R τ (LW.rf-⊕ f g) = r-⊕ (groundF-R τ f) (groundF-R τ g)
  groundF-R τ (LW.rf-⊗ f g) = r-⊗ (groundF-R τ f) (groundF-R τ g)

------------------------------------------------------------------------
-- The invariant
------------------------------------------------------------------------

record WInv {s} (S : LP.Sig Fs s) (sc : Scope) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
            (nm : Fin s → CanonicalName) : Set where
  field
    imp-named  : ImpNamed S nm is
    tele-named : TeleNamed S nm ts
    named      : ∀ d → Σ[ x ∈ String ] nm d ≡ canonical (x ∷ [])
    -- a monomorphic definition (not `main`): the definitions table's, at its type
    mono-at    : ∀ {m} (Δ : ST.KCtx m) {d x} → nm d ≡ canonical (x ∷ []) → ¬ (x ∈ ps) → x ≢ "main"
               → (lookupImport (Scope.sig sc) x ≡ nothing)
                 × Σ[ T ∈ LT.Type ] (lookupImport (Scope.imps sc) x ≡ just T)
                     × (∀ τ → TyR Δ T (SC.Schema.type (defsS S SC.!! d) ST.⟨ τ ⟩))
    -- a definition with type variables is a polymorphic one
    ps-at      : ∀ {d x} → nm d ≡ canonical (x ∷ []) → 0 < SC.Schema.arity (defsS S SC.!! d) → x ∈ ps
    -- a polymorphic definition: the telescope's
    poly-at    : ∀ {m} (Δ : ST.KCtx m) {d x} → nm d ≡ canonical (x ∷ []) → x ∈ ps
               → Sc.PolyAt (defsS S) (Scope.imps sc) (C.buildPolyCtx (Scope.tele sc)) Δ d x
open WInv

-- The start: nothing in scope.
winv-empty : ∀ {sig} {nm : Fin 0 → CanonicalName} → WInv (LP.[] {Fs = Fs}) (scope sig C.emptyFunCtx []) [] [] nm
winv-empty = record
  { imp-named  = tt
  ; tele-named = tt
  ; named      = λ ()
  ; mono-at    = λ Δ {d} → ⊥-elim (fin0 d)
  ; ps-at      = λ {d} → ⊥-elim (fin0 d)
  ; poly-at    = λ Δ {d} → ⊥-elim (fin0 d)
  }
  where
    fin0 : Fin 0 → ⊥
    fin0 ()

------------------------------------------------------------------------
-- Weakening the records
------------------------------------------------------------------------

private
  imp-named-wk : ∀ {s} {S : LP.Sig Fs s} {sc′ c nm imps} (is : ImpSig S imps)
               → ImpNamed S nm is → ImpNamed (S LP.▷ sc′) (c ∷ⁿ nm) (wkI is)
  imp-named-wk []             _          = tt
  imp-named-wk (i-def d e is) (nd , ns) = nd , imp-named-wk is ns

  tele-named-wk : ∀ {s} {S : LP.Sig Fs s} {sc′ c nm tele} (ts : TeleSig S tele)
                → TeleNamed S nm ts → TeleNamed (S LP.▷ sc′) (c ∷ⁿ nm) (wkT ts)
  tele-named-wk []             _          = tt
  tele-named-wk (t-def d e ts) (nd , ns) = nd , tele-named-wk ts ns

  -- an entry's facts, at the next index of a longer signature
  polyAt-wk : ∀ {s} {S : LP.Sig Fs s} {sc′ : LP.Schema} {imps polys m} {Δ : ST.KCtx m} {d x}
            → Sc.PolyAt (defsS S) imps polys Δ d x → Sc.PolyAt (defsS (S LP.▷ sc′)) imps polys Δ (suc d) x
  polyAt-wk p = record
    { lki = Sc.PolyAt.lki p ; lp = Sc.PolyAt.lp p ; ground = Sc.PolyAt.ground p ; open′ = Sc.PolyAt.open′ p
    ; inst = Sc.PolyAt.inst p ; arrow = Sc.PolyAt.arrow p }

  -- …with one more monomorphic definition in the table, of another name
  polyAt-imp : ∀ {s′} {S′ : SC.Defs s′} {imps polys m} {Δ : ST.KCtx m} {d x y T}
             → y ≢ x → Sc.PolyAt S′ imps polys Δ d x → Sc.PolyAt S′ ((y , T) ∷ imps) polys Δ d x
  polyAt-imp {imps = imps} {T = T} ne p = record
    { lki = trans (imp-skip imps T ne) (Sc.PolyAt.lki p) ; lp = Sc.PolyAt.lp p ; ground = Sc.PolyAt.ground p
    ; open′ = Sc.PolyAt.open′ p ; inst = Sc.PolyAt.inst p ; arrow = Sc.PolyAt.arrow p }

  -- …with one more telescope entry, of another name
  polyAt-tele : ∀ {s′} {S′ : SC.Defs s′} {imps polys m} {Δ : ST.KCtx m} {d x y sc b}
              → y ≢ x → Sc.PolyAt S′ imps polys Δ d x → Sc.PolyAt S′ imps ((y , sc , b) ∷ polys) Δ d x
  polyAt-tele {polys = polys} {x = x} {y = y} ne p = record
    { lki = Sc.PolyAt.lki p ; lp = trans (lookup-skip y polys x ne) (Sc.PolyAt.lp p) ; ground = Sc.PolyAt.ground p
    ; open′ = Sc.PolyAt.open′ p ; inst = Sc.PolyAt.inst p ; arrow = Sc.PolyAt.arrow p }

------------------------------------------------------------------------
-- A monomorphic definition
------------------------------------------------------------------------

-- `main` (D324) joins the signature and the names, not the table.
private
  mono-main-at : ∀ {s} {S : LP.Sig Fs s} {sc is ts nm} {x ty}
               → WInv S sc is ts nm → x ≡ "main" → ¬ (x ∈ ps)
               → WInv (S LP.▷ monoSchema ty) sc (wkI is) (wkT ts) (canonical (x ∷ []) ∷ⁿ nm)
  mono-main-at {S = S} {sc = sc} {is} {ts} {nm} {x} {ty} w xm x∉ = record
    { imp-named  = imp-named-wk is (imp-named w)
    ; tele-named = tele-named-wk ts (tele-named w)
    ; named      = λ { zero → x , refl ; (suc d) → named w d }
    ; mono-at    = mono
    ; ps-at      = λ { {zero} e () ; {suc d} e pos → ps-at w e pos }
    ; poly-at    = λ { Δ {zero} e x∈ → ⊥-elim (x∉ (subst (_∈ ps) (sym (canon-inj e)) x∈)) ; Δ {suc d} e x∈ → polyAt-wk (poly-at w Δ e x∈) }
    }
    where
      mono : ∀ {m} (Δ : ST.KCtx m) {d y} → (canonical (x ∷ []) ∷ⁿ nm) d ≡ canonical (y ∷ []) → ¬ (y ∈ ps) → y ≢ "main" → _
      mono Δ {zero}  e y∉ ym = ⊥-elim (ym (trans (sym (canon-inj e)) xm))
      mono Δ {suc d} e y∉ ym = mono-at w Δ e y∉ ym

  mono-def-at : ∀ {s} {S : LP.Sig Fs s} {sc is ts nm} {x ty}
              → WInv S sc is ts nm → LW.RigidFree ty → ¬ (x ∈ ps)
              → lookupImport (Scope.sig sc) x ≡ nothing → All (x ≢_) (defNames sc)
              → WInv (S LP.▷ monoSchema ty) (scope (Scope.sig sc) ((x , ty) ∷ Scope.imps sc) (Scope.tele sc))
                     (i-def zero refl (wkI is)) (wkT ts) (canonical (x ∷ []) ∷ⁿ nm)
  mono-def-at {S = S} {sc = sc} {is} {ts} {nm} {x} {ty} w g x∉ nsig fr = record
    { imp-named  = refl , imp-named-wk is (imp-named w)
    ; tele-named = tele-named-wk ts (tele-named w)
    ; named      = λ { zero → x , refl ; (suc d) → named w d }
    ; mono-at    = mono
    ; ps-at      = λ { {zero} e () ; {suc d} e pos → ps-at w e pos }
    ; poly-at    = poly
    }
    where
      mono : ∀ {m} (Δ : ST.KCtx m) {d y} → (canonical (x ∷ []) ∷ⁿ nm) d ≡ canonical (y ∷ []) → ¬ (y ∈ ps) → y ≢ "main"
           → (lookupImport (Scope.sig sc) y ≡ nothing)
             × Σ[ T ∈ LT.Type ] (lookupImport ((x , ty) ∷ Scope.imps sc) y ≡ just T)
                 × (∀ τ → TyR Δ T (SC.Schema.type (defsS (S LP.▷ monoSchema ty) SC.!! d) ST.⟨ τ ⟩))
      mono Δ {zero} refl y∉ ym = nsig , ty , imp-head (Scope.imps sc) x ty , λ τ → ground-R τ g
      mono Δ {suc d} {y} e y∉ ym =
        let (ns , T , lk , r) = mono-at w Δ e y∉ ym
            ne = ne-of (all-ˡ (map proj₁ (Scope.imps sc)) fr) (imp-in (Scope.imps sc) lk)
        in ns , T , trans (imp-skip (Scope.imps sc) ty ne) lk , r
      poly : ∀ {m} (Δ : ST.KCtx m) {d y} → (canonical (x ∷ []) ∷ⁿ nm) d ≡ canonical (y ∷ []) → y ∈ ps
           → Sc.PolyAt (defsS (S LP.▷ monoSchema ty)) ((x , ty) ∷ Scope.imps sc) (C.buildPolyCtx (Scope.tele sc)) Δ d y
      poly Δ {zero} refl y∈ = ⊥-elim (x∉ y∈)
      poly Δ {suc d} e y∈ =
        let p = poly-at w Δ e y∈
            ne = ne-of (all-ʳ (map proj₁ (Scope.imps sc)) fr) (tele-in (Scope.tele sc) (Sc.PolyAt.lp p))
        in polyAt-wk (polyAt-imp ne p)

-- A monomorphic definition, new to the scope, joins it (`main` only the names).
winv-mono : ∀ {s} {S : LP.Sig Fs s} {sc is ts nm} {x ty}
          → WInv S sc is ts nm → LW.RigidFree ty → ¬ (x ∈ ps)
          → lookupImport (Scope.sig sc) x ≡ nothing → All (x ≢_) (defNames sc)
          → WInv (S LP.▷ monoSchema ty) (addImp sc x ty) (impDefs (x Data.String.== "main") is) (wkT ts) (canonical (x ∷ []) ∷ⁿ nm)
winv-mono {s} {S} {sc} {is} {ts} {nm} {x} {ty} w g x∉ nsig fr = at (x StrProp.≟ "main")
  where
    at : (d : Dec (x ≡ "main"))
       → WInv (S LP.▷ monoSchema ty) (scope (Scope.sig sc) (C.extendDefs-at (Relation.Nullary.isYes d) (Scope.imps sc) x ty) (Scope.tele sc))
              (impDefs (Relation.Nullary.isYes d) is) (wkT ts) (canonical (x ∷ []) ∷ⁿ nm)
    at (yes xm) = mono-main-at w xm x∉
    at (no _)   = mono-def-at w g x∉ nsig fr

------------------------------------------------------------------------
-- A telescope definition
------------------------------------------------------------------------

winv-poly : ∀ {s} {S : LP.Sig Fs s} {sc is ts nm} (pfi : Parser.PolyFunInfo)
          → WInv S sc is ts nm → pfunName pfi ∈ ps → All (pfunName pfi ≢_) (defNames sc)
          → WInv (S LP.▷ schemaOf (pfunType pfi)) (addPoly sc pfi) (wkI is) (t-def zero refl (wkT ts))
                 (canonical (pfunName pfi ∷ []) ∷ⁿ nm)
winv-poly {s} {S} {sc} {is} {ts} {nm} pfi w x∈ fr = record
  { imp-named  = imp-named-wk is (imp-named w)
  ; tele-named = refl , tele-named-wk ts (tele-named w)
  ; named      = λ { zero → x , refl ; (suc d) → named w d }
  ; mono-at    = mono
  ; ps-at      = λ { {zero} refl _ → x∈ ; {suc d} e pos → ps-at w e pos }
  ; poly-at    = poly
  }
  where
    x = pfunName pfi
    T = pfunType pfi
    mono : ∀ {m} (Δ : ST.KCtx m) {d y} → (canonical (x ∷ []) ∷ⁿ nm) d ≡ canonical (y ∷ []) → ¬ (y ∈ ps) → y ≢ "main" → _
    mono Δ {zero} refl y∉ ym = ⊥-elim (y∉ x∈)
    mono Δ {suc d} e y∉ ym   = mono-at w Δ e y∉ ym
    poly : ∀ {m} (Δ : ST.KCtx m) {d y} → (canonical (x ∷ []) ∷ⁿ nm) d ≡ canonical (y ∷ []) → y ∈ ps
         → Sc.PolyAt (defsS (S LP.▷ schemaOf T)) (Scope.imps sc) (C.buildPolyCtx (pfi ∷ Scope.tele sc)) Δ d y
    poly Δ {zero} refl y∈ = record
      { lki    = imp-none (Scope.imps sc) (∉-all (all-ˡ (map proj₁ (Scope.imps sc)) fr))
      ; lp     = lookup-head x (C.buildPolyCtx (Scope.tele sc))
      ; ground = In.ground-at Δ T _ refl
      ; open′  = In.open-at Δ T _ refl
      ; inst   = In.inst-at Δ T _ refl
      ; arrow  = In.arrow-at Δ T _ refl
      }
    poly Δ {suc d} e y∈ =
      let p = poly-at w Δ e y∈
          ne = ne-of (all-ʳ (map proj₁ (Scope.imps sc)) fr) (tele-in (Scope.tele sc) (Sc.PolyAt.lp p))
      in polyAt-wk (polyAt-tele ne p)
