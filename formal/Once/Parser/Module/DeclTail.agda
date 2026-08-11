-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Module.DeclTail
--
-- Declarations whose leading identifier has been consumed (or will be
-- consumed locally): type aliases and primitive declarations.
------------------------------------------------------------------------

module Once.Parser.Module.DeclTail where

open import Data.Bool using (Bool; true; false)
open import Data.List using (reverse)

open import Once.Parser.Module.Core
open import Once.Parser.PolyType using (parsePolyTypeB; ParsePolyAtB)
open import Data.Product using (proj₁; proj₂)
open import Data.Nat.Properties using (<-≤-trans)

-- Local head classifier + `taDrop1` (Plan 0.52 bridge-readiness).
taEqHead : List Token → Bool
taEqHead (TEquals ∷ _) = true
taEqHead _             = false

taDrop1 : List Token → List Token
taDrop1 []       = []
taDrop1 (_ ∷ xs) = xs

taDrop1-≤ : (xs : List Token) → length (taDrop1 xs) ≤ length xs
taDrop1-≤ []       = ≤-refl
taDrop1-≤ (_ ∷ xs) = m≤n⇒m≤1+n ≤-refl

-- | Parameter-scanning helper inside parseTypeAlias. Consumes `=` plus a type,
-- so the residual is strictly shorter. CLASSIFIER-ROUTED + WF: words are consumed
-- via `anyWordB` (accumulate the param + recurse on its tail), `=` via `taEqHead`.
goTypeAliasB : String → (toks : List Token) → List String → ParseAtB {Decl} toks
goTypeAliasWF : String → (toks : List Token) → List String → Acc _<_ (length toks) → ParseAtB {Decl} toks
gta-aw : (name : String) (toks : List Token) (params : List String)
         (rec : ∀ {y} → y < length toks → Acc _<_ y) (aw : ParseAtB {String} toks) → ParseAtB {Decl} toks
gta-eq : (name : String) (toks : List Token) (params : List String) → Bool → ParseAtB {Decl} toks
gta-type : (name : String) (toks : List Token) (params : List String)
           (t : ParseAtB {Type} (taDrop1 toks)) → ParseAtB {Decl} toks
gta-sub : (name : String) (toks : List Token) (params : List String) (p : String) (rest' : List Token)
          (bnd : length rest' < length toks) (sub : ParseAtB {Decl} rest') → ParseAtB {Decl} toks

goTypeAliasB name toks params = goTypeAliasWF name toks params (<-wellFounded (length toks))
goTypeAliasWF name toks params (acc rec) = gta-aw name toks params rec (anyWordB toks)

gta-aw name toks params rec nothing                  = gta-eq name toks params (taEqHead toks)
gta-aw name toks params rec (just (p , rest' , bnd)) =
  gta-sub name toks params p rest' bnd (goTypeAliasWF name rest' (p ∷ params) (rec bnd))

gta-eq name toks params true  = gta-type name toks params (parseTypeB (taDrop1 toks))
gta-eq name toks params false = nothing

gta-type name toks params (just (ty , rest'' , bnd)) =
  just (DTypeAlias name (reverse params) ty , rest'' , <-≤-trans bnd (taDrop1-≤ toks))
gta-type name toks params nothing = nothing

gta-sub name toks params p rest' bnd (just (d , rest'' , bnd')) = just (d , rest'' , <-trans bnd' bnd)
gta-sub name toks params p rest' bnd nothing                    = nothing

parseTypeAliasB : (toks : List Token) → ParseAtB {Decl} toks
pta-aw : (toks : List Token) (aw : ParseAtB {String} toks) → ParseAtB {Decl} toks
pta-go : (toks : List Token) (name : String) (rest : List Token) (bnd : length rest < length toks)
         (g : ParseAtB {Decl} rest) → ParseAtB {Decl} toks
parseTypeAliasB toks = pta-aw toks (anyWordB toks)
pta-aw toks nothing                  = nothing
pta-aw toks (just (name , rest , bnd)) = pta-go toks name rest bnd (goTypeAliasB name rest [])
pta-go toks name rest bnd (just (d , rest' , bnd')) = just (d , rest' , <-trans bnd' bnd)
pta-go toks name rest bnd nothing                   = nothing

parseTypeAlias : Parser Decl
parseTypeAlias toks with parseTypeAliasB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

-- | Map a shape word to its `SigEffect`. Only `halts`/`emits` are
-- recognised; anything else is not a shape (the `!` is left in place,
-- so the decl parser reports the stray token). Plan 0.38 M0.2.
shapeWord : String → Maybe SigEffect
shapeWord w with w ≟ "halts"
... | yes _ = just halts
... | no _ with w ≟ "emits"
...   | yes _ = just emits
...   | no _  = nothing

-- | Optional trailing `! <shape>` EffectShape annotation. Consumes the
-- two tokens `TBang ∷ TWord <shape>` when `<shape>` is a recognised
-- shape word; otherwise consumes nothing. The remainder is never longer
-- than the input.
-- Routed through the `effAnnotShape` classifier (instead of matching the
-- `TBang ∷ TWord w` prefix directly) so the bridge cases it in 2 clauses.
effAnnotShape : List Token → Maybe SigEffect
effAnnotShape (TBang ∷ TWord w ∷ _) = shapeWord w
effAnnotShape _                     = nothing

eaDrop2 : List Token → List Token
eaDrop2 (_ ∷ _ ∷ xs) = xs
eaDrop2 xs           = xs

eaDrop2-≤ : (toks : List Token) → length (eaDrop2 toks) ≤ length toks
eaDrop2-≤ (_ ∷ _ ∷ xs) = m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)
eaDrop2-≤ []           = ≤-refl
eaDrop2-≤ (_ ∷ [])     = ≤-refl

parseEffAnnot-go : (toks : List Token) → Maybe SigEffect →
                   Maybe SigEffect × Σ[ rest ∈ List Token ] (length rest ≤ length toks)
parseEffAnnot-go toks (just se) = just se , eaDrop2 toks , eaDrop2-≤ toks
parseEffAnnot-go toks nothing   = nothing , toks , ≤-refl

parseEffAnnot : (toks : List Token) →
                Maybe SigEffect ×
                Σ[ rest ∈ List Token ] (length rest ≤ length toks)
parseEffAnnot toks = parseEffAnnot-go toks (effAnnotShape toks)

-- `name : polytype [! shape]` signature. Routed through `colonHead` + `colDrop1`
-- (instead of matching `TColon ∷ rest` on the anyWordB residual) for the bridge.
colonHead : List Token → Bool
colonHead (TColon ∷ _) = true
colonHead _            = false

colDrop1 : List Token → List Token
colDrop1 (_ ∷ xs) = xs
colDrop1 []       = []

colDrop1-≤ : (toks : List Token) → length (colDrop1 toks) ≤ length toks
colDrop1-≤ (_ ∷ xs) = m≤n⇒m≤1+n ≤-refl
colDrop1-≤ []       = ≤-refl

psig-poly : (toks : List Token) (name : String) (residual : List Token)
            (bnd : length residual < length toks) → ParsePolyAtB (colDrop1 residual) →
            ParseAtB {Decl} toks
psig-poly toks name residual bnd nothing = nothing
psig-poly toks name residual bnd (just (ty , rest' , bnd')) =
  just (DSignature name nothing ty (proj₁ (parseEffAnnot rest'))
       , proj₁ (proj₂ (parseEffAnnot rest'))
       , <-trans (<-≤-trans (≤-<-trans (proj₂ (proj₂ (parseEffAnnot rest'))) bnd')
                            (colDrop1-≤ residual)) bnd)

psig-colon : (toks : List Token) (name : String) (residual : List Token)
             (bnd : length residual < length toks) → Bool → ParseAtB {Decl} toks
psig-colon toks name residual bnd false = nothing
psig-colon toks name residual bnd true  =
  psig-poly toks name residual bnd (parsePolyTypeB (colDrop1 residual))

parseSignatureB : (toks : List Token) → ParseAtB {Decl} toks
parseSignatureB toks with anyWordB toks
... | nothing                       = nothing
... | just (name , residual , bnd)  = psig-colon toks name residual bnd (colonHead residual)

parseSignature : Parser Decl
parseSignature toks with parseSignatureB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing
