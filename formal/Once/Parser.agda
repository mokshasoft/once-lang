-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser
--
-- Top-level parser entry point.
-- Tokenizes a string and parses it into a Module.
------------------------------------------------------------------------

module Once.Parser where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String; _≟_; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (yes; no)

open import Once.Type using (Type; PolyType; isGround; extractGround; showPolyType)
open import Once.TypeCheck.Raw using (RawExpr; RVar)
open import Once.Parser.Token
open import Once.Parser.Lexer using (tokenizeString)
open import Once.Parser.Core using (Parser)
open import Once.Parser.Type using (parseType) public
open import Once.Parser.PolyType using (parsePolyType) public
open import Once.Parser.Expr using (parseExpr) public
open import Once.Parser.Module public
open import Once.Parser.Inline public
open import Once.Parser.TypeAlias public

-- Parser smoke tests (plan 0.3 G1): pull into the compilation graph
-- so a regression in parser behaviour fails `make parser`.
import Once.Parser.Tests

-- Grammar pretty-printer + round-trip smoke tests (plan 0.3 G1):
-- same principle — force the printer/parser consistency into
-- the parser-target dependency chain.
import Once.Grammar.Printer

-- G1 parser correctness proofs: type-side round-trip and NoMuNu
-- invariant. Both wired in here so regressions in the parser's
-- reduction shape surface via `make parser` / `make frontend` rather
-- than silently breaking the proofs.
import Once.Grammar.Roundtrip
import Once.Grammar.ParserInvariant

-- G1 expression-side round-trip infrastructure (plan 0.3 task #38):
-- printer, ConcreteExpr predicate, converter, and per-leaf round-trip
-- smoke tests. The general compound-case theorem is future work —
-- see `Once.Grammar.ExprRoundtrip`'s header comment for the
-- outstanding blocker (Parser/Expr Dec-valued refactor).
import Once.Grammar.ExprPrinter
import Once.Grammar.ExprConvert
import Once.Grammar.ExprRoundtrip

-- Phase 3a of task #38: inductive parsing relations for expressions.
-- Used by the future Dec-valued Parser/Expr refactor and the structural
-- round-trip proof. Wired in here so the relation file is type-checked
-- under `make frontend` / `make parser`.
import Once.Parser.ExprRelation

-- Phase 3c of task #38: WF-parser ↔ relation bridge for expressions.
-- Provides soundness (and completeness, once lifted) between
-- `parseExpr` and `ParsesExpr`.
import Once.Grammar.ExprBridge

-- Phase 3c of task #38: structural round-trip for the parsing relation.
import Once.Grammar.ExprRelRoundtrip


------------------------------------------------------------------------
-- Top-level Parse Function
------------------------------------------------------------------------

-- | Parse a source string into a Module.
-- Returns Nothing on parse failure.
--
-- DEPRECATED for new callers — use `parseStrict` instead so
-- unexpected trailing tokens surface as errors rather than silent
-- drops. Kept for compatibility with callers that intentionally
-- want a partial parse (none in-tree as of plan 0.6 Phase A).
parse : String → Maybe Module
parse source with parseModule (tokenizeString source)
... | just (m , _) = just m
... | nothing = nothing

-- | A parse residual is "trivial" iff it contains only trailing
-- `TNewline`s and `TEOF`s. Anything else means the parser stopped
-- early because a declaration failed — which was silently recovered
-- by `parseDeclsWF` but should surface as an error at the top level.
-- Plan 0.6 Phase A: strict parser errors, no silent drops.
allTrailing : List Token → Bool
allTrailing []              = true
allTrailing (TNewline ∷ xs) = allTrailing xs
allTrailing (TEOF     ∷ xs) = allTrailing xs
allTrailing _               = false

-- | Show the first few tokens (approximate position indicator) for
-- error messages. We don't have column numbers yet; the first few
-- token tags are still the single most useful piece of information
-- for pointing a user to the failing decl.
showTokenPrefix : List Token → String
showTokenPrefix [] = ""
showTokenPrefix (TWord s    ∷ _) = "TWord \"" ++ s ++ "\""
showTokenPrefix (TInt _     ∷ _) = "TInt"
showTokenPrefix (TString _  ∷ _) = "TString"
showTokenPrefix (TNewline   ∷ xs) = showTokenPrefix xs
showTokenPrefix (TLParen    ∷ _) = "TLParen"
showTokenPrefix (TRParen    ∷ _) = "TRParen"
showTokenPrefix (TLBrace    ∷ _) = "TLBrace"
showTokenPrefix (TRBrace    ∷ _) = "TRBrace"
showTokenPrefix (TColon     ∷ _) = "TColon"
showTokenPrefix (TEquals    ∷ _) = "TEquals"
showTokenPrefix (TArrow     ∷ _) = "TArrow"
showTokenPrefix (TLambda    ∷ _) = "TLambda"
showTokenPrefix (TComma     ∷ _) = "TComma"
showTokenPrefix (TSemicolon ∷ _) = "TSemicolon"
showTokenPrefix (TAt        ∷ _) = "TAt"
showTokenPrefix (TPipe      ∷ _) = "TPipe"
showTokenPrefix (TDot       ∷ _) = "TDot"
showTokenPrefix (TPlus      ∷ _) = "TPlus"
showTokenPrefix (TMinus     ∷ _) = "TMinus"
showTokenPrefix (TStar      ∷ _) = "TStar"
showTokenPrefix (TSlash     ∷ _) = "TSlash"
showTokenPrefix (TPercent   ∷ _) = "TPercent"
showTokenPrefix (TAmpersand ∷ _) = "TAmpersand"
showTokenPrefix (TLt        ∷ _) = "TLt"
showTokenPrefix (TLe        ∷ _) = "TLe"
showTokenPrefix (TGt        ∷ _) = "TGt"
showTokenPrefix (TGe        ∷ _) = "TGe"
showTokenPrefix (TEqEq      ∷ _) = "TEqEq"
showTokenPrefix (TNeq       ∷ _) = "TNeq"
showTokenPrefix (TCaret1    ∷ _) = "TCaret1"
showTokenPrefix (TCaret0    ∷ _) = "TCaret0"
showTokenPrefix (TCaretW    ∷ _) = "TCaretW"
showTokenPrefix (TEOF       ∷ xs) = showTokenPrefix xs

-- | Strict parse entry: returns `inj₁ err` if tokenisation parses
-- any decls but leaves non-trivial tokens behind (i.e. the parser
-- gave up silently on a malformed decl), or if it parses nothing at
-- all. Returns `inj₂ m` only when every token is accounted for.
--
-- Plan 0.6 Phase A — motivation: earlier this week two different
-- silent-drop bugs cost material debugging time (dotted primitive
-- names in the import preprocessor; TVars in type signatures). Both
-- symptoms were "the thing I wrote just isn't there." This entry
-- point makes that class of failure impossible.
parseStrict : String → String ⊎ Module
parseStrict source with parseModule (tokenizeString source)
... | nothing       = inj₁ "Parse error: module failed to parse"
... | just (m , r) with allTrailing r
...   | true  = inj₂ m
...   | false = inj₁ ("Parse error: unexpected tokens remaining after last parsed decl (starting at: " ++ showTokenPrefix r ++ ")")

------------------------------------------------------------------------
-- Processing Pipeline Helpers
------------------------------------------------------------------------

-- | Extract type aliases from a module's declarations
extractAliases : Module → TypeAliasEnv
extractAliases (mkModule ds) = go ds
  where
  go : List Decl → TypeAliasEnv
  go [] = []
  go (DTypeAlias name params body ∷ rest) = (name , params , body) ∷ go rest
  go (_ ∷ rest) = go rest

-- | Extract function definitions with their types (paired sig + def)
-- Returns: List (name, type, maybe alloc, body)
-- Processes declarations in order, matching type sigs with subsequent defs.
record FunInfo : Set where
  constructor mkFunInfo
  field
    funName  : String
    funType  : Type
    funAlloc : Maybe AllocStrategy
    funBody  : RawExpr

-- | Polymorphic counterpart of `FunInfo`. User-declared definitions
-- whose signature carries `TVar`s flow through this record and are
-- handled downstream by schema instantiation at use sites — plan 0.6
-- Phase C.1. Kept structurally separate from `FunInfo` so the ground
-- compile pipeline stays untouched; the two lists are processed
-- independently by `compileAllFuns`.
record PolyFunInfo : Set where
  constructor mkPolyFunInfo
  field
    pfunName  : String
    pfunType  : PolyType
    pfunAlloc : Maybe AllocStrategy
    pfunBody  : RawExpr

-- | Project a parsed `PolyType` signature to a ground `Type`. Used
-- for declarations (primitives, ground-typed user defs) where
-- polymorphic signatures are not admissible. User `DFunDef`s with
-- polymorphic sigs route into `PolyFunInfo` instead of going through
-- this projector.
--
-- Applies alias expansion after projection (aliases currently live
-- in ground `Type` land — see `expandAliases`). If a future phase
-- introduces polymorphic aliases, expansion moves pre-projection.
projectSig : TypeAliasEnv → String → PolyType → String ⊎ Type
projectSig aliases name ty with isGround ty
... | inj₁ g  = inj₂ (expandAliases aliases (extractGround ty g))
... | inj₂ _  = inj₁ ("Polymorphic signature not admissible here for `" ++ name
                        ++ "`: " ++ showPolyType ty
                        ++ " — primitives and type aliases must be ground. "
                        ++ "User `DFunDef`s with polymorphic sigs route into "
                        ++ "`PolyFunInfo` (plan 0.6 Phase C.1).")

-- | Pending-signature state for `extractFunctions`' fold. A user
-- `DTypeSig` is deferred until the subsequent `DFunDef` is seen:
-- ground sigs yield a `FunInfo`, polymorphic sigs a `PolyFunInfo`.
PendingSig : Set
PendingSig = String × (Type ⊎ PolyType)

extractFunctions : TypeAliasEnv → Module → String ⊎ (List FunInfo × List PolyFunInfo)
extractFunctions aliases (mkModule ds) = go ds nothing
  where
  Result : Set
  Result = String ⊎ (List FunInfo × List PolyFunInfo)

  consFun : Result → FunInfo → Result
  consFun (inj₁ err)        _  = inj₁ err
  consFun (inj₂ (gs , ps)) fi = inj₂ (fi ∷ gs , ps)

  consPoly : Result → PolyFunInfo → Result
  consPoly (inj₁ err)        _   = inj₁ err
  consPoly (inj₂ (gs , ps)) pfi = inj₂ (gs , pfi ∷ ps)

  go : List Decl → Maybe PendingSig → Result
  go [] _ = inj₂ ([] , [])
  -- Signatures are classified now: ground types get expanded eagerly;
  -- polymorphic types are carried as-is for the matching DFunDef.
  go (DTypeSig name ty ∷ rest) _ with isGround ty
  ... | inj₁ g  = go rest (just (name , inj₁ (expandAliases aliases (extractGround ty g))))
  ... | inj₂ _  = go rest (just (name , inj₂ ty))
  -- DFunDef with matching ground sig → FunInfo
  go (DFunDef name alloc body ∷ rest) (just (sigName , inj₁ gty)) with sigName ≟ name
  ... | yes _ = consFun (go rest nothing) (mkFunInfo name gty alloc body)
  ... | no  _ = go rest nothing
  -- DFunDef with matching polymorphic sig → PolyFunInfo
  go (DFunDef name alloc body ∷ rest) (just (sigName , inj₂ pty)) with sigName ≟ name
  ... | yes _ = consPoly (go rest nothing) (mkPolyFunInfo name pty alloc body)
  ... | no  _ = go rest nothing
  go (DFunDef _ _ _ ∷ rest) nothing = go rest nothing  -- no sig: definition dropped
  -- Primitives: use RVar as placeholder body (actual impl is external).
  -- Owned primitives (from resolved imports) get qualified names
  -- `alias.name` — same textual form that the typechecker's
  -- `lookupImport` uses for `RQualified`, so user code `exit@S`
  -- resolves to this FunInfo without further wiring. Primitives must
  -- be ground; polymorphic primitive signatures are rejected by
  -- `projectSig`.
  go (DPrimitive name nothing ty ∷ rest) _ with projectSig aliases name ty
  ... | inj₁ err  = inj₁ err
  ... | inj₂ gty  = consFun (go rest nothing) (mkFunInfo name gty nothing (RVar name))
  go (DPrimitive name (just owner) ty ∷ rest) _ with projectSig aliases (owner ++ "." ++ name) ty
  ... | inj₁ err  = inj₁ err
  ... | inj₂ gty  =
           let qname = owner ++ "." ++ name
           in consFun (go rest nothing) (mkFunInfo qname gty nothing (RVar qname))
  go (_ ∷ rest) pending = go rest pending

-- | Inline all functions and return elaboration-ready pairs
-- Each function's body is inlined with all previously-defined function bodies.
-- Returns: List (name, type, maybe alloc, inlined-body)
inlineAll : ℕ → List FunInfo → List FunInfo
inlineAll fuel fns = go [] fns
  where
  go : Defs → List FunInfo → List FunInfo
  go _ [] = []
  go defs (mkFunInfo name ty alloc body ∷ rest) =
    let inlined = inlineReferences fuel defs body
    in  mkFunInfo name ty alloc inlined ∷ go ((name , body) ∷ defs) rest