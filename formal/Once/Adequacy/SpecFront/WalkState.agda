-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.WalkState — the scope facts along the telescope
-- walk (plan 0.121 §3.6, F6).
--
-- The checker's completeness at a walk state (`Def`) asks of a definition's
-- scope that a name a Spec reference resolves to is the one the checker's
-- lookups find — a monomorphic definition in the definitions table, a
-- polymorphic one in the telescope, after no FFI declaration (`View.InView`)
-- — and the entries those lookups find named so (`ScopeNames`), the names
-- distinct.
-- `WInv` collects them for a walk state: the compiler's signature `S` and
-- scope, the core entries recorded for it (`ImpSig`/`TeleSig`), and the Spec's
-- names `nm`. It holds of the empty state and is kept by each definition,
-- given that the definition's name is new to the scope and is polymorphic
-- exactly when it is one of `ps`, the module's polymorphic names.
------------------------------------------------------------------------

open import Data.List using (List)
open import Data.String using (String)

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecFront.WalkState (Σ : Signature) (ps : List String) where

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
open import Data.List.Membership.DecPropositional StrProp._≟_ using (_∈?_)

import Once.Spec.Type as LT
import Once.Type.Concrete as LW
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
import Once.Compile as C
import Once.Parser as Parser
open Parser.PolyFunInfo using (pfunName; pfunType; pfunBody)
open import Once.Spec.Name using (CanonicalName; canonical)
import Once.Spec.Surface.Program
open import Once.TypeCheck.Scope using (Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.Module using (Scope; scope; emptyScope; addImp; addPoly)
open import Once.Type.Schema using (schemaOf)
open import Once.Core.Translate Σ using (ImpSig; TeleSig; []; i-def; t-def; wkI; wkT; impDefs; monoSchema)
import Once.Adequacy.SpecFront.ScopeNames as SN
import Once.Adequacy.SpecFront.Scope as Sc
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

-- a monomorphic definition's type, at any instance of its (variable-free) schema


record WInv {s} (S : SC.Defs s) (sc : Scope) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
            (nm : Fin s → CanonicalName) : Set where
  field
    imp-named  : SN.ImpNamed Σ S nm is
    tele-named : SN.TeleNamed Σ S nm ts
    named      : ∀ d → Σ[ x ∈ String ] nm d ≡ canonical (x ∷ [])
    -- a monomorphic definition (not `main`): the definitions table's, at its type
    mono-at    : ∀ {d x} → nm d ≡ canonical (x ∷ []) → ¬ (x ∈ ps) → x ≢ "main"
               → (lookupImport (Scope.sig sc) x ≡ nothing)
                 × Σ[ T ∈ ST.Type ] (lookupImport (Scope.imps sc) x ≡ just T)
    -- a definition with type variables is a polymorphic one
    ps-at      : ∀ {d x} → nm d ≡ canonical (x ∷ []) → 0 < SC.Schema.arity (S SC.!! d) → x ∈ ps
    -- a polymorphic definition: the telescope's
    poly-at    : ∀ {d x} → nm d ≡ canonical (x ∷ []) → x ∈ ps
               → Sc.PolyAt (S) (Scope.imps sc) (C.buildPolyCtx (Scope.tele sc)) d x
    -- the entries' names are distinct (`main`'s aside: it leaves the scope, D324)
    inj        : ∀ {d d′} → nm d ≡ nm d′ → nm d ≢ canonical ("main" ∷ []) → d ≡ d′
open WInv

-- The start: nothing in scope.
winv-empty : ∀ {sig} {nm : Fin 0 → CanonicalName} → WInv SC.[] (scope sig C.emptyFunCtx []) [] [] nm
winv-empty = record
  { imp-named  = tt
  ; tele-named = tt
  ; named      = λ ()
  ; mono-at    = λ {d} → ⊥-elim (fin0 d)
  ; ps-at      = λ {d} → ⊥-elim (fin0 d)
  ; poly-at    = λ {d} → ⊥-elim (fin0 d)
  ; inj        = λ {d} → ⊥-elim (fin0 d)
  }
  where
    fin0 : Fin 0 → ⊥
    fin0 ()

------------------------------------------------------------------------
-- Weakening the records
------------------------------------------------------------------------

private
  -- an entry's name, not `main`, is one of the scope's
  in-scope : ∀ {s} {S : SC.Defs s} {sc is ts nm} → WInv S sc is ts nm
           → ∀ {d x} → nm d ≡ canonical (x ∷ []) → x ≢ "main" → x ∈ defNames sc
  in-scope {sc = sc} w {x = x} e xm with x ∈? ps
  ... | yes x∈ = ∈-++⁺ʳ (map proj₁ (Scope.imps sc)) (tele-in (Scope.tele sc) (Sc.PolyAt.lp (poly-at w e x∈)))
  ... | no x∉  = ∈-++⁺ˡ (imp-in (Scope.imps sc) (proj₂ (proj₂ (mono-at w e x∉ xm))))

  -- …so a new name, fresh to the scope, is no entry's but `main`'s
  inj-new : ∀ {s} {S : SC.Defs s} {sc is ts nm} {x} → WInv S sc is ts nm → All (x ≢_) (defNames sc)
          → ∀ {d} → canonical (x ∷ []) ≡ nm d → canonical (x ∷ []) ≢ canonical ("main" ∷ []) → ⊥
  inj-new {x = x} w fr e ne = ∉-all fr (in-scope w (sym e) (λ xm → ne (cong (λ y → canonical (y ∷ [])) xm)))

  -- the distinct names of a longer table, the new one fresh
  inj-ext : ∀ {s} {nm : Fin s → CanonicalName} {c}
          → (∀ {d d′} → nm d ≡ nm d′ → nm d ≢ canonical ("main" ∷ []) → d ≡ d′)
          → (∀ {d} → c ≡ nm d → c ≢ canonical ("main" ∷ []) → ⊥)
          → ∀ {d d′} → (c ∷ⁿ nm) d ≡ (c ∷ⁿ nm) d′ → (c ∷ⁿ nm) d ≢ canonical ("main" ∷ []) → d ≡ d′
  inj-ext i new {zero}  {zero}   e ne = refl
  inj-ext i new {zero}  {suc d′} e ne = ⊥-elim (new e ne)
  inj-ext i new {suc d} {zero}   e ne = ⊥-elim (new (sym e) (λ m → ne (trans e m)))
  inj-ext i new {suc d} {suc d′} e ne = cong suc (i e ne)

private
  imp-named-wk : ∀ {s} {S : SC.Defs s} {sc′ c nm imps} (is : ImpSig S imps)
               → SN.ImpNamed Σ S nm is → SN.ImpNamed Σ (S SC.▷ sc′) (c ∷ⁿ nm) (wkI is)
  imp-named-wk []             _          = tt
  imp-named-wk (i-def d e is) (nd , ns) = nd , imp-named-wk is ns

  tele-named-wk : ∀ {s} {S : SC.Defs s} {sc′ c nm tele} (ts : TeleSig S tele)
                → SN.TeleNamed Σ S nm ts → SN.TeleNamed Σ (S SC.▷ sc′) (c ∷ⁿ nm) (wkT ts)
  tele-named-wk []             _          = tt
  tele-named-wk (t-def d e ts) (nd , ns) = nd , tele-named-wk ts ns

  -- an entry's facts, at the next index of a longer signature
  polyAt-wk : ∀ {s} {S : SC.Defs s} {sc′ : SC.Schema} {imps polys} {d x}
            → Sc.PolyAt (S) imps polys d x → Sc.PolyAt ((S SC.▷ sc′)) imps polys (suc d) x
  polyAt-wk p = record
    { lki = Sc.PolyAt.lki p ; lp = Sc.PolyAt.lp p }

  -- …with one more monomorphic definition in the table, of another name
  polyAt-imp : ∀ {s′} {S′ : SC.Defs s′} {imps polys} {d x y T}
             → y ≢ x → Sc.PolyAt S′ imps polys d x → Sc.PolyAt S′ ((y , T) ∷ imps) polys d x
  polyAt-imp {imps = imps} {T = T} ne p = record
    { lki = trans (imp-skip imps T ne) (Sc.PolyAt.lki p) ; lp = Sc.PolyAt.lp p }

  -- …with one more telescope entry, of another name
  polyAt-tele : ∀ {s′} {S′ : SC.Defs s′} {imps polys} {d x y sc b}
              → y ≢ x → Sc.PolyAt S′ imps polys d x → Sc.PolyAt S′ imps ((y , sc , b) ∷ polys) d x
  polyAt-tele {polys = polys} {x = x} {y = y} ne p = record
    { lki = Sc.PolyAt.lki p ; lp = trans (lookup-skip y polys x ne) (Sc.PolyAt.lp p) }

------------------------------------------------------------------------
-- A monomorphic definition
------------------------------------------------------------------------

-- `main` (D324) joins the signature and the names, not the table.
private
  mono-main-at : ∀ {s} {S : SC.Defs s} {sc is ts nm} {x ty}
               → WInv S sc is ts nm → x ≡ "main" → ¬ (x ∈ ps)
               → WInv (S SC.▷ monoSchema ty) sc (wkI is) (wkT ts) (canonical (x ∷ []) ∷ⁿ nm)
  mono-main-at {S = S} {sc = sc} {is} {ts} {nm} {x} {ty} w xm x∉ = record
    { imp-named  = imp-named-wk is (imp-named w)
    ; tele-named = tele-named-wk ts (tele-named w)
    ; named      = λ { zero → x , refl ; (suc d) → named w d }
    ; mono-at    = λ {d} → mono {d}
    ; ps-at      = λ { {zero} e () ; {suc d} e pos → ps-at w e pos }
    ; poly-at    = λ { {zero} e x∈ → ⊥-elim (x∉ (subst (_∈ ps) (sym (canon-inj e)) x∈)) ; {suc d} e x∈ → polyAt-wk (poly-at w {d} e x∈) }
    ; inj        = inj-ext (inj w) (λ _ ne → ne (cong (λ y → canonical (y ∷ [])) xm))
    }
    where
      mono : ∀ {d y} → (canonical (x ∷ []) ∷ⁿ nm) d ≡ canonical (y ∷ []) → ¬ (y ∈ ps) → y ≢ "main"
           → (lookupImport (Scope.sig sc) y ≡ nothing) × Σ[ T ∈ ST.Type ] (lookupImport (Scope.imps sc) y ≡ just T)
      mono {zero}  e y∉ ym = ⊥-elim (ym (trans (sym (canon-inj e)) xm))
      mono {suc d} e y∉ ym = mono-at w {d} e y∉ ym

  mono-def-at : ∀ {s} {S : SC.Defs s} {sc is ts nm} {x ty}
              → WInv S sc is ts nm → ¬ (x ∈ ps)
              → lookupImport (Scope.sig sc) x ≡ nothing → All (x ≢_) (defNames sc)
              → WInv (S SC.▷ monoSchema ty) (scope (Scope.sig sc) ((x , ty) ∷ Scope.imps sc) (Scope.tele sc))
                     (i-def zero refl (wkI is)) (wkT ts) (canonical (x ∷ []) ∷ⁿ nm)
  mono-def-at {S = S} {sc = sc} {is} {ts} {nm} {x} {ty} w x∉ nsig fr = record
    { imp-named  = refl , imp-named-wk is (imp-named w)
    ; tele-named = tele-named-wk ts (tele-named w)
    ; named      = λ { zero → x , refl ; (suc d) → named w d }
    ; mono-at    = λ {d} → mono {d}
    ; ps-at      = λ { {zero} e () ; {suc d} e pos → ps-at w e pos }
    ; poly-at    = λ {d} → poly {d}
    ; inj        = inj-ext (inj w) (inj-new w fr)
    }
    where
      mono : ∀ {d y} → (canonical (x ∷ []) ∷ⁿ nm) d ≡ canonical (y ∷ []) → ¬ (y ∈ ps) → y ≢ "main"
           → (lookupImport (Scope.sig sc) y ≡ nothing)
             × Σ[ T ∈ ST.Type ] (lookupImport ((x , ty) ∷ Scope.imps sc) y ≡ just T)
      mono {zero} refl y∉ ym = nsig , ty , imp-head (Scope.imps sc) x ty
      mono {suc d} {y} e y∉ ym =
        let (ns , T , lk) = mono-at w {d} e y∉ ym
            ne = ne-of (all-ˡ (map proj₁ (Scope.imps sc)) fr) (imp-in (Scope.imps sc) lk)
        in ns , T , trans (imp-skip (Scope.imps sc) ty ne) lk
      poly : ∀ {d y} → (canonical (x ∷ []) ∷ⁿ nm) d ≡ canonical (y ∷ []) → y ∈ ps
           → Sc.PolyAt ((S SC.▷ monoSchema ty)) ((x , ty) ∷ Scope.imps sc) (C.buildPolyCtx (Scope.tele sc)) d y
      poly {zero} refl y∈ = ⊥-elim (x∉ y∈)
      poly {suc d} e y∈ =
        let p = poly-at w {d} e y∈
            ne = ne-of (all-ʳ (map proj₁ (Scope.imps sc)) fr) (tele-in (Scope.tele sc) (Sc.PolyAt.lp p))
        in polyAt-wk (polyAt-imp ne p)

-- A monomorphic definition, new to the scope, joins it (`main` only the names).
winv-mono : ∀ {s} {S : SC.Defs s} {sc is ts nm} {x ty}
          → WInv S sc is ts nm → ¬ (x ∈ ps)
          → lookupImport (Scope.sig sc) x ≡ nothing → All (x ≢_) (defNames sc)
          → WInv (S SC.▷ monoSchema ty) (addImp sc x ty) (impDefs (x Data.String.== "main") is) (wkT ts) (canonical (x ∷ []) ∷ⁿ nm)
winv-mono {s} {S} {sc} {is} {ts} {nm} {x} {ty} w x∉ nsig fr = at (x StrProp.≟ "main")
  where
    at : (d : Dec (x ≡ "main"))
       → WInv (S SC.▷ monoSchema ty) (scope (Scope.sig sc) (C.extendDefs-at (Relation.Nullary.isYes d) (Scope.imps sc) x ty) (Scope.tele sc))
              (impDefs (Relation.Nullary.isYes d) is) (wkT ts) (canonical (x ∷ []) ∷ⁿ nm)
    at (yes xm) = mono-main-at w xm x∉
    at (no _)   = mono-def-at w x∉ nsig fr

------------------------------------------------------------------------
-- A telescope definition
------------------------------------------------------------------------

winv-poly : ∀ {s} {S : SC.Defs s} {sc is ts nm} (pfi : Parser.PolyFunInfo)
          → WInv S sc is ts nm → pfunName pfi ∈ ps → All (pfunName pfi ≢_) (defNames sc)
          → WInv (S SC.▷ schemaOf (pfunType pfi)) (addPoly sc pfi) (wkI is) (t-def zero refl (wkT ts))
                 (canonical (pfunName pfi ∷ []) ∷ⁿ nm)
winv-poly {s} {S} {sc} {is} {ts} {nm} pfi w x∈ fr = record
  { imp-named  = imp-named-wk is (imp-named w)
  ; tele-named = refl , tele-named-wk ts (tele-named w)
  ; named      = λ { zero → x , refl ; (suc d) → named w d }
  ; mono-at    = λ {d} → mono {d}
  ; ps-at      = λ { {zero} refl _ → x∈ ; {suc d} e pos → ps-at w e pos }
  ; poly-at    = λ {d} → poly {d}
  ; inj        = inj-ext (inj w) (inj-new w fr)
  }
  where
    x = pfunName pfi
    T = pfunType pfi
    mono : ∀ {d y} → (canonical (x ∷ []) ∷ⁿ nm) d ≡ canonical (y ∷ []) → ¬ (y ∈ ps) → y ≢ "main"
         → (lookupImport (Scope.sig sc) y ≡ nothing) × Σ[ T ∈ ST.Type ] (lookupImport (Scope.imps sc) y ≡ just T)
    mono {zero} refl y∉ ym = ⊥-elim (y∉ x∈)
    mono {suc d} e y∉ ym   = mono-at w {d} e y∉ ym
    poly : ∀ {d y} → (canonical (x ∷ []) ∷ⁿ nm) d ≡ canonical (y ∷ []) → y ∈ ps
         → Sc.PolyAt ((S SC.▷ schemaOf T)) (Scope.imps sc) (C.buildPolyCtx (pfi ∷ Scope.tele sc)) d y
    poly {zero} refl y∈ = record
      { lki    = imp-none (Scope.imps sc) (∉-all (all-ˡ (map proj₁ (Scope.imps sc)) fr))
      ; lp     = lookup-head x (C.buildPolyCtx (Scope.tele sc))
      }
    poly {suc d} e y∈ =
      let p = poly-at w {d} e y∈
          ne = ne-of (all-ʳ (map proj₁ (Scope.imps sc)) fr) (tele-in (Scope.tele sc) (Sc.PolyAt.lp p))
      in polyAt-wk (polyAt-tele ne p)
