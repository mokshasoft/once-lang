-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonPolyNames — discharge of `CanonModule.polyInB-bridge`.
--
-- Every name in the `polys` context built from `extractFunctions` IS one of the
-- `polyDefNames` (the resolver's bound) of the module's decls. Both come from the
-- NON-GROUND `DTypeSig`s; `extractFunctions` additionally requires a matching
-- `DFunDef`, so its poly names are a SUBSET of `polyDefNames`. Proven by induction
-- on `extractFunctions-go`, tracking the pending non-ground signature.
------------------------------------------------------------------------

module Once.Adequacy.CanonPolyNames where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_) renaming (_≟_ to _≟s_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Once.Type using (Type; PolyType; isGround; extractGround)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Parser.Module.Core using (Decl; DTypeSig; DFunDef; DSignature; DImport; DTypeAlias; Module; mkModule)
open import Once.Parser
  using ( FunInfo; PolyFunInfo; PendingSig; projectSig; EFResult
        ; extractFunctions; extractFunctions-go; extractAliases; guardDistinct; distinctOrErr)
open Once.Parser.PolyFunInfo using (pfunName)
open Once.Parser.Module.Core.Module using (decls)
open import Once.Parser.Module.Resolve using (polyDefNames; pdn-go; elemStr)
open import Once.TypeCheck.Principal using (siglessSchema)
open import Once.Compile using (buildPolyCtx)
open import Once.TypeCheck.Classify using (lookupPoly)

------------------------------------------------------------------------
-- ∨ / elemStr helpers.
------------------------------------------------------------------------

∨-introˡ : ∀ {a b} → a ≡ true → (a ∨ b) ≡ true
∨-introˡ refl = refl

∨-introʳ : ∀ {a b} → b ≡ true → (a ∨ b) ≡ true
∨-introʳ {true}  _ = refl
∨-introʳ {false} e = e

∨-false : ∀ {b} → (b ∨ false) ≡ b
∨-false {true}  = refl
∨-false {false} = refl

drop-∨false : ∀ {b} → (b ∨ false) ≡ true → b ≡ true
drop-∨false {b} e = trans (sym (∨-false {b})) e

∨-cases : ∀ {a b} {C : Set} → (a ∨ b) ≡ true → (a ≡ true → C) → (b ≡ true → C) → C
∨-cases {true}  e l r = l refl
∨-cases {false} e l r = r e

elemStr-cons-head : ∀ (n : String) (L : List String) → elemStr n (n ∷ L) ≡ true
elemStr-cons-head n L with n ≟s n
... | yes _  = refl
... | no ¬p  = ⊥-elim (¬p refl)

elemStr-cons-mono : ∀ (x n : String) (L : List String) → elemStr x L ≡ true → elemStr x (n ∷ L) ≡ true
elemStr-cons-mono x n L h with x ≟s n
... | yes _ = refl
... | no  _ = h

elemStr-cons-split : ∀ (x n : String) (L : List String)
  → elemStr x (n ∷ L) ≡ true → (x ≡ n) ⊎ (elemStr x L ≡ true)
elemStr-cons-split x n L h with x ≟s n
... | yes p = inj₁ p
... | no  _ = inj₂ h

------------------------------------------------------------------------
-- Pending non-ground signature's name.
------------------------------------------------------------------------

pendingPoly : Maybe PendingSig → List String
pendingPoly (just (n , inj₂ _)) = n ∷ []
pendingPoly _                   = []

-- D072 M3: `polyDefNames` threads the same pending state as
-- `extractFunctions-go` (as `pdn-go`); this projects the tracked name.
pendingName : Maybe PendingSig → Maybe String
pendingName (just (n , _)) = just n
pendingName nothing        = nothing

-- non-ground DTypeSig keeps `name` in polyDefNames AND in the new pending; the
-- `name`-prepend re-introduction used by the DTypeSig non-ground case.
prepend-name : ∀ (x name : String) (rest : List String)
  → (elemStr x rest ∨ elemStr x (name ∷ [])) ≡ true → elemStr x (name ∷ rest) ≡ true
prepend-name x name rest e = ∨-cases e
  (λ l → elemStr-cons-mono x name rest l)
  (λ r → split r)
  where split : elemStr x (name ∷ []) ≡ true → elemStr x (name ∷ rest) ≡ true
        split r with elemStr-cons-split x name [] r
        ... | inj₁ refl = elemStr-cons-head name rest
        ... | inj₂ ()

------------------------------------------------------------------------
-- The subset induction.
------------------------------------------------------------------------

poly⊆ : ∀ (al : _) (ds : List Decl) (pending : Maybe PendingSig) {funs polys}
  → extractFunctions-go al ds pending ≡ inj₂ (funs , polys)
  → ∀ (x : String) → elemStr x (map pfunName polys) ≡ true
  → (elemStr x (pdn-go ds (pendingName pending)) ∨ elemStr x (pendingPoly pending)) ≡ true
poly⊆ al [] pending refl x ()
-- DTypeSig: overwrites pending; recurse, then re-attach `name` if non-ground.
poly⊆ al (DTypeSig name ty ∷ rest) pending eq x h with isGround ty
... | inj₂ _ = ∨-introˡ (prepend-name x name (pdn-go rest (just name)) (poly⊆ al rest _ eq x h))
... | inj₁ g with isConcrete? (extractGround ty g)
...   | just _  = ∨-introˡ (drop-∨false (poly⊆ al rest _ eq x h))
...   | nothing = ∨-introˡ (prepend-name x name (pdn-go rest (just name)) (poly⊆ al rest _ eq x h))
-- DFunDef, GROUND pending: consFun (match) or direct recurse (mismatch).
poly⊆ al (DFunDef name alloc body ∷ rest) (just (sigName , inj₁ gty)) eq x h with sigName ≟s name
... | yes _ with extractFunctions-go al rest nothing in eq2
...   | inj₂ (gs , ps) with eq
...     | refl = ∨-introˡ (drop-∨false (poly⊆ al rest nothing eq2 x h))
poly⊆ al (DFunDef name alloc body ∷ rest) (just (sigName , inj₁ gty)) eq x h | no _ =
      ∨-introˡ (drop-∨false (poly⊆ al rest nothing eq x h))
-- DFunDef, NON-GROUND pending: consPoly (match, emits `name`) or direct recurse.
poly⊆ al (DFunDef name alloc body ∷ rest) (just (sigName , inj₂ pty)) eq x h with sigName ≟s name
... | yes refl with extractFunctions-go al rest nothing in eq2
...   | inj₂ (gs , ps) with eq
...     | refl with elemStr-cons-split x name (map pfunName ps) h
...       | inj₁ refl = ∨-introʳ (elemStr-cons-head name [])
...       | inj₂ inps = ∨-introˡ (drop-∨false (poly⊆ al rest nothing eq2 x inps))
poly⊆ al (DFunDef name alloc body ∷ rest) (just (sigName , inj₂ pty)) eq x h | no _ =
      ∨-introˡ (drop-∨false (poly⊆ al rest nothing eq x h))
-- DFunDef, NO pending: D072 sig-less routing — schema-shaped bodies
-- consPoly (name emitted, matched by pdn-go's identical split), others
-- consFun (D007).
poly⊆ al (DFunDef name alloc body ∷ rest) nothing eq x h with siglessSchema body
poly⊆ al (DFunDef name alloc body ∷ rest) nothing eq x h | just pty
  with extractFunctions-go al rest nothing in eq2
... | inj₂ (gs , ps) with eq
...   | refl with elemStr-cons-split x name (map pfunName ps) h
...     | inj₁ refl = ∨-introˡ (elemStr-cons-head name (pdn-go rest nothing))
...     | inj₂ inps =
          ∨-introˡ (elemStr-cons-mono x name (pdn-go rest nothing)
                     (drop-∨false (poly⊆ al rest nothing eq2 x inps)))
poly⊆ al (DFunDef name alloc body ∷ rest) nothing eq x h | nothing
  with extractFunctions-go al rest nothing in eq2
... | inj₂ (gs , ps) with eq
...   | refl = ∨-introˡ (drop-∨false (poly⊆ al rest nothing eq2 x h))
-- DSignature: primitive (consFun) when projectSig succeeds.
poly⊆ al (DSignature name nothing ty se ∷ rest) pending eq x h with projectSig al name ty
... | inj₂ gty with extractFunctions-go al rest nothing in eq2
...   | inj₂ (gs , ps) with eq
...     | refl = ∨-introˡ (drop-∨false (poly⊆ al rest nothing eq2 x h))
poly⊆ al (DSignature name (just owner) ty se ∷ rest) pending eq x h with projectSig al (owner ++ "." ++ name) ty
... | inj₂ gty with extractFunctions-go al rest nothing in eq2
...   | inj₂ (gs , ps) with eq
...     | refl = ∨-introˡ (drop-∨false (poly⊆ al rest nothing eq2 x h))
-- DImport / DTypeAlias: pass through.
poly⊆ al (DImport imp ∷ rest) pending eq x h = poly⊆ al rest pending eq x h
poly⊆ al (DTypeAlias n ps t ∷ rest) pending eq x h = poly⊆ al rest pending eq x h

------------------------------------------------------------------------
-- Wiring: lookupPoly → membership, peel guardDistinct, combine.
------------------------------------------------------------------------

elemStr-head-eq : ∀ {x n} (L : List String) → x ≡ n → elemStr x (n ∷ L) ≡ true
elemStr-head-eq {x} L refl = elemStr-cons-head x L

lookupPoly-name : ∀ (ps : List PolyFunInfo) (x : String) {r}
  → lookupPoly (buildPolyCtx ps) x ≡ just r → elemStr x (map pfunName ps) ≡ true
lookupPoly-name [] x ()
lookupPoly-name (pfi ∷ rest) x lp with pfunName pfi ≟s x
... | yes p = elemStr-head-eq (map pfunName rest) (sym p)
... | no  _ = elemStr-cons-mono x (pfunName pfi) (map pfunName rest) (lookupPoly-name rest x lp)

distinctOrErr-inj₂ : ∀ (b : Bool) (X : EFResult) {Y} → distinctOrErr b X ≡ inj₂ Y → X ≡ inj₂ Y
distinctOrErr-inj₂ true  X eq = eq
distinctOrErr-inj₂ false X ()

guardDistinct-inj₂ : ∀ (R : EFResult) {Y} → guardDistinct R ≡ inj₂ Y → R ≡ inj₂ Y
guardDistinct-inj₂ (inj₁ e) ()
guardDistinct-inj₂ (inj₂ (f , p)) eq = distinctOrErr-inj₂ _ (inj₂ (f , p)) eq

-- The CanonModule obligation, discharged.
polyInB-bridge :
  ∀ (mU : Module) (funsU : List FunInfo) (polysU : List PolyFunInfo)
  → extractFunctions (extractAliases mU) mU ≡ inj₂ (funsU , polysU)
  → ∀ {x s b} → lookupPoly (buildPolyCtx polysU) x ≡ just (s , b)
  → elemStr x (polyDefNames (decls mU)) ≡ true
polyInB-bridge (mkModule ds) funsU polysU ef-eq {x} lp =
  drop-∨false (poly⊆ (extractAliases (mkModule ds)) ds nothing
                 (guardDistinct-inj₂ (extractFunctions-go (extractAliases (mkModule ds)) ds nothing) ef-eq)
                 x (lookupPoly-name polysU x lp))
