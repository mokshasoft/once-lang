-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Extract.Names — THE HASKELL-FACING SURFACE, DECLARED IN ONE PLACE.
--
-- WHY THIS MODULE EXISTS.
--
-- `Once.Compile.Bridge` (hand-written Haskell) used to reach into the
-- extracted code by MANGLED NAME WITH AGDA'S INTERNAL SERIAL:
--
--     MMR.d_resolveImports_1018        -- a function
--     MMC.C_DFunDef_36 name _ _        -- a constructor, AND its arity
--
-- Those serials are an artifact of the extractor; any edit renumbers them, and
-- nothing relates the two sides. On 2026-09-08 one extraction cost 24 renames
-- by hand. Worse, `C_DFunDef_36 name _ _` was a SECOND COPY OF THE
-- CONSTRUCTOR'S SHAPE: `DFunDef` had dropped a field, and the mirror only
-- broke loudly because the ARITY changed — had a field's meaning changed with
-- the count intact, the Haskell would have compiled and misread the AST.
--
-- Two fixes, and this module is both:
--
--   * (INTENDED, NOT AVAILABLE) stable extracted names via `COMPILE GHC f as
--     …`. Measured 2026-09-08: that pragma requires EVERY type in the
--     signature to have a Haskell binding, so `Module → Bool` is rejected at
--     extraction ("contains …Module which does not have a COMPILE pragma").
--     Supplying one means asserting an Agda↔Haskell representation
--     correspondence that nothing checks — a new axiom in all but name — so
--     the serials stay, and `make check-bridge` catches them instead.
--   * every predicate the bridge computed BY DESTRUCTURING an Agda datatype is
--     defined here instead, so there is no shape mirrored in Haskell at all.
--     That is the D161 move again: not "relate the two implementations", but
--     "have one".
--
-- WHY A SEPARATE MODULE. It keeps the whole Haskell-facing surface in one
-- declared place instead of scattered across the verified modules. (It was
-- also going to hold compile pragmas, which `--safe` rejects outright and
-- which would therefore have broken `make denot-safe` had they been attached
-- to `Once.Type` or `Once.Target.Arch` — both in that gate's cone.)
--
-- NOTHING HERE ADDS TRUST: the predicates are ordinary total Agda, and the
-- module carries no pragmas at all. What it removes is the SHAPE MIRRORING —
-- the bridge no longer spells any constructor or its arity. The serial churn
-- remains (see above) and is a build-time check, not a correctness question.
------------------------------------------------------------------------
module Once.Extract.Names where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)

open import Once.Spec.Surface.Syntax using (Module; Decl; DImport; DTypeSig; DFunDef; DSignature; DTypeAlias)
open import Once.Spec.Surface.Syntax using (Import)
open Once.Spec.Surface.Syntax.Module using (decls)
open Once.Spec.Surface.Syntax.Import using (path; alias)

------------------------------------------------------------------------
-- What the bridge used to compute by pattern-matching MAlonzo constructors.
-- (`module-has-main`, whose Haskell mirror carried the stale arity, is gone:
-- `build` asks the compiler's `moduleToIR`, the apex's own case split, D354.)
------------------------------------------------------------------------

-- | The module's imports, as (path, alias) pairs. The bridge rebuilds its own
-- `ImportRef` from these, so it never names `DImport` or its fields.
-- (`Extract.Names.Proof.imports-declared`: exactly the `import` declarations.)
imports-of : List Decl → List (List String × Maybe String)
imports-of []                    = []
imports-of (DImport i ∷ ds)      = (path i , alias i) ∷ imports-of ds
imports-of (DTypeSig _ _ ∷ ds)   = imports-of ds
imports-of (DFunDef _ _ ∷ ds)    = imports-of ds
imports-of (DSignature _ _ ∷ ds) = imports-of ds
imports-of (DTypeAlias _ _ _ ∷ ds) = imports-of ds

module-imports : Module → List (List String × Maybe String)
module-imports m = imports-of (decls m)

-- …and its two projections, so the bridge never names `Σ`'s extracted fields
-- either (those carry serials like everything else).
import-path : (List String × Maybe String) → List String
import-path (p , _) = p

import-alias : (List String × Maybe String) → Maybe String
import-alias (_ , a) = a
