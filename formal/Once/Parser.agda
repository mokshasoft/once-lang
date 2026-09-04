-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser
--
-- Top-level parser entry point.
-- Tokenizes a string and parses it into a Module.
------------------------------------------------------------------------

module Once.Parser where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String; _≟_; _++_; toList)
open import Data.Char using (Char)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (yes; no; does)

open import Once.Type using (Type; PolyType; isGround; extractGround; showPolyType)
open import Once.Functor.Decide using (isConcrete?)
open import Once.TypeCheck.Raw using (RawExpr; RVar)
-- D072 M3: the principal-type oracle's sig-less schema criterion.
open import Once.TypeCheck.Principal using (siglessSchema)
open import Once.Parser.Token
open import Once.Parser.Lexer using (tokenizeString; isIdentStart; isIdentContinue)
open import Once.Parser.Core using (Parser)
open import Once.Parser.Type using (parseType; isUpperWord) public
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
showTokenPrefix (TInt _ _     ∷ _) = "TInt"
showTokenPrefix (TFloat _ _ _ _ ∷ _) = "TFloat"
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
showTokenPrefix (TBang      ∷ _) = "TBang"
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
-- The leftover often starts at a type signature using an uppercase word for
-- a type *variable* (e.g. `swap : A * B -> B * A`) — uppercase names are
-- concrete types (Int/Unit/…), type variables are lowercase. Detect that and
-- add a hint instead of the bare "unexpected tokens". (Top-level so the
-- clause-based `parseStrict` below stays analysable — front-end
-- soundness/completeness reduce through its success path.)
knownTypeWord : String → Bool
knownTypeWord w = does (w ≟ "Unit") ∨ does (w ≟ "Void") ∨ does (w ≟ "Int")
            ∨ does (w ≟ "Float") ∨ does (w ≟ "Buffer") ∨ does (w ≟ "String")
hasUpperTVar : List Token → Bool
hasUpperTVar []              = false
hasUpperTVar (TWord w  ∷ ts) = (isUpperWord w ∧ not (knownTypeWord w)) ∨ hasUpperTVar ts
hasUpperTVar (_        ∷ ts) = hasUpperTVar ts
tvarHint : List Token → String
tvarHint toks with hasUpperTVar toks
... | true  = "\n  hint: type variables must be lowercase (e.g. `a`, not `A`); uppercase names like `Int`/`Unit` are concrete types"
... | false = ""

-- Clause-based dispatch (NO `with`) on the `allTrailing` decision and the
-- `parseModule` result, so the success path `inj₂ m` reduces under hypotheses
-- (the verified front-end's `parseStrict-sound`/`-complete` step through it).
parseStrict-at : List Token → Module → Bool → String ⊎ Module
parseStrict-at r m true  = inj₂ m
parseStrict-at r m false =
  inj₁ ("Parse error: unexpected tokens remaining after last parsed decl (starting at: "
        ++ showTokenPrefix r ++ ")" ++ tvarHint r)

parseStrict-pm : Maybe (Module × List Token) → String ⊎ Module
parseStrict-pm nothing        = inj₁ "Parse error: module failed to parse"
parseStrict-pm (just (m , r)) = parseStrict-at r m (allTrailing r)

parseStrict : String → String ⊎ Module
parseStrict source = parseStrict-pm (parseModule (tokenizeString source))

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
-- Returns: List (name, type, body)
-- Processes declarations in order, matching type sigs with subsequent defs.
record FunInfo : Set where
  constructor mkFunInfo
  field
    funName  : String
    -- | D007: signatures are OPTIONAL. `just ty` = explicit signature;
    -- `nothing` = no explicit signature, so the type is INFERRED from the
    -- body's composition during compilation (`Compile.inferType`). Primitives
    -- always carry `just`. (Was `Type`; the `nothing` case was previously
    -- DROPPED in `extractFunctions`, contradicting D007.)
    funType  : Maybe Type
    funBody  : RawExpr
    -- | Plan 0.11: `true` for signatures (external declarations
    -- whose implementations live in `Strata/Interpretations/<…>.<arch>`
    -- as `once_<name>` symbols), `false` for user-defined function
    -- definitions. Primitives are typechecked + tracked in FunCtx
    -- (so user code can reference them), but their function body
    -- is NOT emitted at codegen time — that would produce a
    -- recursive `once_<name>: ...; call once_<name>; ret` stub.
    funIsPrimitive : Bool

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

-- `consFun`/`consPoly`/`go` lifted to TOP LEVEL (were `where`-locals of
-- `extractFunctions`) so the verified frontend can induct on them (a
-- non-primitive "main" `FunInfo` traces back to a `DFunDef "main"`).
-- `aliases` is now an explicit parameter.
EFResult : Set
EFResult = String ⊎ (List FunInfo × List PolyFunInfo)

extractFunctions-consFun : EFResult → FunInfo → EFResult
extractFunctions-consFun (inj₁ err)        _  = inj₁ err
extractFunctions-consFun (inj₂ (gs , ps)) fi = inj₂ (fi ∷ gs , ps)

extractFunctions-consPoly : EFResult → PolyFunInfo → EFResult
extractFunctions-consPoly (inj₁ err)        _   = inj₁ err
extractFunctions-consPoly (inj₂ (gs , ps)) pfi = inj₂ (gs , pfi ∷ ps)

extractFunctions-go : TypeAliasEnv → List Decl → Maybe PendingSig → EFResult
extractFunctions-go aliases [] _ = inj₂ ([] , [])
-- Signatures are classified now: ground types get expanded eagerly;
-- polymorphic types are carried as-is for the matching DFunDef.
-- Plan 0.58 / D071: a ground signature routes to a monomorphic `FunInfo`
-- (direct-call symbol) ONLY when it is also CONCRETE; a ground-but-non-concrete
-- sig (e.g. `μNat → Int`, a cata) — like a polymorphic one — is a context
-- projection carried as a `PolyFunInfo` and δ-reduced at use sites, NOT gated by
-- FFI concreteness. The resolver's keep-bare set (`polyDefNames`) uses the SAME
-- `isGround`-then-`isConcrete?` criterion, so the two classifications agree.
extractFunctions-go aliases (DTypeSig name ty ∷ rest) _ with isGround ty
... | inj₂ _  = extractFunctions-go aliases rest (just (name , inj₂ ty))
... | inj₁ g  with isConcrete? (extractGround ty g)
...   | just _  = extractFunctions-go aliases rest (just (name , inj₁ (expandAliases aliases (extractGround ty g))))
...   | nothing = extractFunctions-go aliases rest (just (name , inj₂ ty))
-- DFunDef with matching ground sig → FunInfo (user-defined; not primitive)
extractFunctions-go aliases (DFunDef name body ∷ rest) (just (sigName , inj₁ gty)) with sigName ≟ name
... | yes _ = extractFunctions-consFun (extractFunctions-go aliases rest nothing) (mkFunInfo name (just gty) body false)
... | no  _ = extractFunctions-go aliases rest nothing
-- DFunDef with matching polymorphic sig → PolyFunInfo
extractFunctions-go aliases (DFunDef name body ∷ rest) (just (sigName , inj₂ pty)) with sigName ≟ name
... | yes _ = extractFunctions-consPoly (extractFunctions-go aliases rest nothing) (mkPolyFunInfo name pty body)
... | no  _ = extractFunctions-go aliases rest nothing
-- D007: NO explicit signature → KEEP the definition (was dropped).
-- D072 M3: if the body's principal type is a SCHEMA (`siglessSchema`),
-- the def is a telescope entry (PolyFunInfo) with that schema — the
-- oracle acting as an automatic signature-writer; uses instantiate via
-- t-var-poly-instantiate and every instantiation is kernel-checked, so
-- a wrong oracle schema is a rejected use, never unsoundness. Ground or
-- unknown bodies keep the FunInfo path (type INFERRED during
-- compilation — inferElab, or the oracle's ground answers via
-- inferType, D072 M2). `polyDefNames` (Resolve) uses the SAME
-- criterion, so the keep-bare set agrees.
extractFunctions-go aliases (DFunDef name body ∷ rest) nothing
  with siglessSchema body
... | just pty = extractFunctions-consPoly (extractFunctions-go aliases rest nothing) (mkPolyFunInfo name pty body)
... | nothing  = extractFunctions-consFun (extractFunctions-go aliases rest nothing) (mkFunInfo name nothing body false)
-- Primitives: use RVar as placeholder body (actual impl is external).
-- Owned primitives (from resolved imports) get qualified names
-- `alias.name` — same textual form that the typechecker's
-- `lookupImport` uses for `RQualified`, so user code `exit@S`
-- resolves to this FunInfo without further wiring. Primitives must
-- be ground; polymorphic primitive signatures are rejected by
-- `projectSig`.
extractFunctions-go aliases (DSignature name nothing ty _ ∷ rest) _ with projectSig aliases name ty
... | inj₁ err  = inj₁ err
... | inj₂ gty  = extractFunctions-consFun (extractFunctions-go aliases rest nothing) (mkFunInfo name (just gty) (RVar name) true)
extractFunctions-go aliases (DSignature name (just owner) ty _ ∷ rest) _ with projectSig aliases (owner ++ "." ++ name) ty
... | inj₁ err  = inj₁ err
... | inj₂ gty  =
         let qname = owner ++ "." ++ name
         in extractFunctions-consFun (extractFunctions-go aliases rest nothing) (mkFunInfo qname (just gty) (RVar qname) true)
extractFunctions-go aliases (_ ∷ rest) pending = extractFunctions-go aliases rest pending

-- Plan 0.50 (clash-freedom): REJECT duplicate top-level definition names. Two
-- definitions named `foo` both compile to the symbol `once_…foo` → "symbol
-- already defined" / a misdirected call. Enforcing distinctness HERE —
-- `extractFunctions` feeds BOTH `moduleToIR` (the compiler) and `ModuleTyped`
-- (the typing predicate) — makes a duplicate a compile error AND makes any typed
-- module IMPLY distinct names (the no-clash theorem's precondition, for free).
nameElem : String → List String → Bool
nameElem _ []       = false
nameElem x (y ∷ ys) with x ≟ y
... | yes _ = true
... | no  _ = nameElem x ys

namesDistinct : List String → Bool
namesDistinct []       = true
namesDistinct (x ∷ xs) = not (nameElem x xs) ∧ namesDistinct xs

-- Plan 0.50 (clash-freedom, validity half): each top-level definition name must
-- be a genuine lexer identifier — head `isIdentStart`, tail `isIdentContinue` —
-- the SAME predicates the lexer tokenises with. This is the precondition the
-- symbol mangling needs to be INJECTIVE (`once-symbol-path-injective`): the
-- self-delimiting length prefix only works because an identifier never starts
-- with a digit. Checked HERE (no `with`), so `extractFunctions` success carries
-- it; `program-no-clash` reads it back off via `validIdentB-sound`.
allIdentContinue : List Char → Bool
allIdentContinue []       = true
allIdentContinue (c ∷ cs) = isIdentContinue c ∧ allIdentContinue cs

validCharsB : List Char → Bool
validCharsB []       = false
validCharsB (c ∷ cs) = isIdentStart c ∧ allIdentContinue cs

validIdentB : String → Bool
validIdentB s = validCharsB (toList s)

allValidIdentB : List String → Bool
allValidIdentB []       = true
allValidIdentB (x ∷ xs) = validIdentB x ∧ allValidIdentB xs

-- The names that actually get EMITTED as symbols: only NON-primitive defs get a
-- `functionPrologue`/`.globl` label (primitives are external Strata symbols,
-- skipped by `compileFunWithTarget`). Clash-freedom + validity are required only
-- over these. This is FORCED by the codegen-faithful no-clash proof (`caf-syms`
-- in `Once.Adequacy.NameClash`), whose emitted-symbol set runs over exactly the
-- non-primitive `CompiledFun`s — checking imported/injected primitives (which may
-- carry qualified/owner-tagged names) would wrongly reject valid programs.
-- de-withed (Bool-helper) so the codegen-faithfulness proof (`caf-syms`) can
-- case on `funIsPrimitive` and reduce both this and `emittedSyms` in lockstep.
emittedNames-cons : Bool → FunInfo → List String → List String
emittedNames-cons true  fi rest = rest
emittedNames-cons false fi rest = FunInfo.funName fi ∷ rest

emittedNames : List FunInfo → List String
emittedNames []         = []
emittedNames (fi ∷ fis) = emittedNames-cons (FunInfo.funIsPrimitive fi) fi (emittedNames fis)

-- Guard `extractFunctions-go`'s result on name well-formedness — DISTINCT and
-- each a valid identifier (with-free dispatch on the combined Bool).
distinctOrErr : Bool → EFResult → EFResult
distinctOrErr true  r = r
distinctOrErr false _ = inj₁ "ill-formed top-level definition name (duplicate or not an identifier)"

guardDistinct : EFResult → EFResult
guardDistinct (inj₁ err)            = inj₁ err
guardDistinct (inj₂ (funs , polys)) =
  distinctOrErr (namesDistinct nms ∧ allValidIdentB nms) (inj₂ (funs , polys))
  where nms = emittedNames funs

extractFunctions : TypeAliasEnv → Module → String ⊎ (List FunInfo × List PolyFunInfo)
extractFunctions aliases (mkModule ds) = guardDistinct (extractFunctions-go aliases ds nothing)

-- Plan 0.6.2: `inlineAll`, `inlineAllWithPoly`, `polySeedDefs` all
-- removed. The eager RawExpr-level inlining pipeline is replaced by
-- typecheck-time schema instantiation via `PolyCtx`
-- (Once.TypeCheck.Elaborate). Ground function cross-references flow
-- through the `FunCtx` import list; user polymorphic definitions
-- flow through `NamedCtx.polys`. See D045.