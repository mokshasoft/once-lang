-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser
--
-- Top-level parser entry point.
-- Tokenizes a string and parses it into a Module.
------------------------------------------------------------------------

module Once.Parser where

open import Once.Type.Honest using (HonestFFI; honest?)

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++ₗ_)
open import Once.Spec.Name using (canonical)
open import Once.Name using (showCanonical)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_; _++_; toList)
open import Data.Char using (Char)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Nullary.Decidable using (¬?)
open import Data.List.Relation.Unary.AllPairs using (allPairs?)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Spec.Grade using (mk-kind; Many; eff)
open import Once.Spec.Type using (Type; Unit; _⇒[_]_)
open import Once.Spec.Surface.Syntax using (PolyType)
open import Once.Type.Poly using (extractGround)
open import Once.Type using (isGround; showPolyType)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Spec.Surface.Syntax using (RVar)
open import Once.Spec.Surface.Syntax using (Expr)
-- D072 M3: the principal-type oracle's sig-less schema criterion.
open import Once.Parser.Token
open import Once.Parser.Lexer using (tokenizeString; isIdentStart; isIdentContinue; isOpNameChar)
open import Once.Parser.Type using (isUpperWord)
open import Once.Parser.Module
open import Once.Parser.Module.Core using (Resolved; resolved)
open import Once.Spec.Surface.Syntax using (Module; mkModule; Decl; DTypeAlias; DTypeSig; DFunDef; DSignature)


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

-- | A parse residual is "trivial" iff it is `TNewline`s, then the `TEOF`
-- that ends the text. Anything else means the parser stopped early because
-- a declaration failed — which was silently recovered by `parseDeclsWF` but
-- should surface as an error at the top level (plan 0.6 Phase A: strict
-- parser errors, no silent drops). A residual without `TEOF` means the lexer
-- stopped before the end of the text: an unterminated string (D343).
allTrailing : List Token → Bool
allTrailing []              = false
allTrailing (TNewline ∷ xs) = allTrailing xs
allTrailing (TEOF ∷ [])     = true
{-# CATCHALL #-}
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
            ∨ does (w ≟ "Float")
hasUpperTVar : List Token → Bool
hasUpperTVar []              = false
hasUpperTVar (TWord w  ∷ ts) = (isUpperWord w ∧ not (knownTypeWord w)) ∨ hasUpperTVar ts
{-# CATCHALL #-}
hasUpperTVar (_        ∷ ts) = hasUpperTVar ts
tvarHint : List Token → String
tvarHint toks with hasUpperTVar toks
... | true  = "\n  hint: type variables must be lowercase (e.g. `a`, not `A`); uppercase names like `Int`/`Unit` are concrete types"
... | false = ""

-- Clause-based dispatch (NO `with`) on the `allTrailing` decision and the
-- `parseModule` result, so the success path `inj₂ m` reduces under hypotheses
-- (the verified front-end's `parseStrict-sound`/`-complete` step through it).
residualError : List Token → String
residualError [] = "Lex error: unterminated string literal (no closing `\"`; the text after it is not read)"
residualError r@(_ ∷ _) =
  "Parse error: unexpected tokens remaining after last parsed decl (starting at: "
  ++ showTokenPrefix r ++ ")" ++ tvarHint r

parseStrict-at : List Token → Module → Bool → String ⊎ Module
parseStrict-at r m true  = inj₂ m
parseStrict-at r m false = inj₁ (residualError r)

parseStrict-pm : Maybe (Module × List Token) → String ⊎ Module
parseStrict-pm nothing        = inj₁ "Parse error: module failed to parse"
parseStrict-pm (just (m , r)) = parseStrict-at r m (allTrailing r)

parseStrict : String → String ⊎ Module
parseStrict source = parseStrict-pm (parseModule (tokenizeString source))

------------------------------------------------------------------------
-- Processing Pipeline Helpers
------------------------------------------------------------------------

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
    funBody  : Expr
    -- | Plan 0.11: `true` for signatures (external declarations
    -- whose implementations live in `Strata/Interpretations/<…>.<arch>`
    -- as `once_<name>` symbols), `false` for user-defined function
    -- definitions. Primitives are typechecked + tracked in FunCtx
    -- (so user code can reference them), but their function body
    -- is NOT emitted at codegen time — that would produce a
    -- recursive `once_<name>: ...; call once_<name>; ret` stub.
    funIsPrimitive : Bool

-- | A telescope definition: polymorphic, or ground but not concrete (a
-- context projection, D071). Typed ONCE, over its schema's parameters, where
-- it is declared (D243; plan 0.122).
record PolyFunInfo : Set where
  constructor mkPolyFunInfo
  field
    pfunName  : String
    pfunType  : PolyType
    pfunBody  : Expr

-- | D241/D242: the module is ONE declaration-ordered telescope. Every
-- definition sees exactly the definitions declared before it; an FFI
-- declaration is a `e-fun` whose `funIsPrimitive` is set.
data Entry : Set where
  e-fun  : FunInfo → Entry
  e-poly : PolyFunInfo → Entry

funsOf : List Entry → List FunInfo
funsOf []              = []
funsOf (e-fun fi ∷ es)  = fi ∷ funsOf es
funsOf (e-poly _ ∷ es)  = funsOf es

polysOf : List Entry → List PolyFunInfo
polysOf []               = []
polysOf (e-fun _ ∷ es)    = polysOf es
polysOf (e-poly pfi ∷ es) = pfi ∷ polysOf es

-- | Project a parsed `PolyType` signature to a ground `Type`. Used
-- for declarations (primitives, ground-typed user defs) where
-- polymorphic signatures are not admissible. User `DFunDef`s with
-- polymorphic sigs route into `PolyFunInfo` instead of going through
-- this projector.
-- D231: an FFI declaration must be HONEST (`Once.Type.HonestComplete`): a SigOp
-- returning `Unit` emits and one returning `Void` halts, so such an arrow must
-- be `Eff`, and a bare `Unit`/`Void` constant is not a declaration. Checked
-- HERE — on the `signature` itself — so it constrains FFI declarations and
-- nothing else (a user `f : Int -> Unit` stays a pure function).
honestSig : String → (T : Type) → Maybe (HonestFFI T) → String ⊎ Type
honestSig name T (just _) = inj₂ T
honestSig name T nothing  =
  inj₁ ("Signature `" ++ name ++ "` : " ++ Once.Type.showType T ++ " hides an effect: a SigOp "
        ++ "returning Unit emits and one returning Void halts, so its arrow must be Eff "
        ++ "(a bare Unit/Void constant is written Eff Unit Unit)")

projectSig : String → PolyType → String ⊎ Type
projectSig name ty with isGround ty
... | inj₁ g  = honestSig name (extractGround ty g) (honest? (extractGround ty g))
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
EFResult : Set
EFResult = String ⊎ List Entry

extractFunctions-consFun : EFResult → FunInfo → EFResult
extractFunctions-consFun (inj₁ err) _  = inj₁ err
extractFunctions-consFun (inj₂ es)  fi = inj₂ (e-fun fi ∷ es)

extractFunctions-consPoly : EFResult → String → PolyType → Expr → EFResult
extractFunctions-consPoly (inj₁ err) _ _ _ = inj₁ err
extractFunctions-consPoly (inj₂ es)  n t b = inj₂ (e-poly (mkPolyFunInfo n t b) ∷ es)

-- A signature is followed by its own definition, and by nothing else (the
-- Spec's `Walk`: `w-sig`); a signature left over is an error, never dropped.
danglingSig : String → String
danglingSig s = "The signature of `" ++ s ++ "` is not followed by its definition"

extractFunctions-go : List Decl → Maybe PendingSig → EFResult
extractFunctions-sigless : (name : String) → Expr → List Decl → Dec (name ≡ "main") → EFResult
extractFunctions-go [] nothing = inj₂ []
extractFunctions-go [] (just (s , _)) = inj₁ (danglingSig s)
-- Signatures are classified now: ground types get expanded eagerly;
-- polymorphic types are carried as-is for the matching DFunDef.
-- Plan 0.58 / D071: a ground signature routes to a monomorphic `FunInfo`
-- (direct-call symbol) ONLY when it is also CONCRETE; a ground-but-non-concrete
-- sig (e.g. `μNat → Int`, a cata) — like a polymorphic one — is a context
-- projection carried as a `PolyFunInfo` and δ-reduced at use sites, NOT gated by
-- FFI concreteness. The resolver's keep-bare set (`polyDefNames`) uses the SAME
-- `isGround`-then-`isConcrete?` criterion, so the two classifications agree.
extractFunctions-go (DTypeSig name ty ∷ rest) (just (s , _)) = inj₁ (danglingSig s)
extractFunctions-go (DTypeSig name ty ∷ rest) nothing with isGround ty
... | inj₂ _  = extractFunctions-go rest (just (name , inj₂ ty))
... | inj₁ g  with isConcrete? (extractGround ty g)
...   | just _  = extractFunctions-go rest (just (name , inj₁ (extractGround ty g)))
...   | nothing = extractFunctions-go rest (just (name , inj₂ ty))
-- DFunDef with matching ground sig → FunInfo (user-defined; not primitive)
extractFunctions-go (DFunDef name body ∷ rest) (just (sigName , inj₁ gty)) with sigName ≟ name
... | yes _ = extractFunctions-consFun (extractFunctions-go rest nothing) (mkFunInfo name (just gty) body false)
... | no  _ = inj₁ (danglingSig sigName)
-- DFunDef with matching polymorphic sig → PolyFunInfo
extractFunctions-go (DFunDef name body ∷ rest) (just (sigName , inj₂ pty)) with sigName ≟ name
... | yes _ = extractFunctions-consPoly (extractFunctions-go rest nothing) name pty body
... | no  _ = inj₁ (danglingSig sigName)
-- D323: NO explicit signature → a monomorphic definition at the type its
-- body SYNTHESIZES (`inferElab`, during compilation). No oracle: the
-- definition alone decides its type. `polyDefNames` (Resolve) never keeps a
-- sig-less definition bare, so the two classifications agree.
extractFunctions-go (DFunDef name body ∷ rest) nothing =
  extractFunctions-sigless name body rest (name ≟ "main")
-- Primitives: use RVar as placeholder body (actual impl is external). A
-- primitive's name is the one a reference to it resolves to: an own one's
-- bare, an imported one's qualified by its module's path (`Resolved.imported`,
-- the same textual form `lookupImport` uses). Primitives must be ground;
-- polymorphic primitive signatures are rejected by `projectSig`.
extractFunctions-go (DSignature name ty ∷ rest) (just (s , _)) = inj₁ (danglingSig s)
extractFunctions-go (DSignature name ty ∷ rest) nothing with projectSig name ty
... | inj₁ err  = inj₁ err
... | inj₂ gty  = extractFunctions-consFun (extractFunctions-go rest nothing) (mkFunInfo name (just gty) (RVar name) true)
{-# CATCHALL #-}
extractFunctions-go (_ ∷ rest) nothing = extractFunctions-go rest nothing
{-# CATCHALL #-}
extractFunctions-go (_ ∷ rest) (just (s , _)) = inj₁ (danglingSig s)

-- D315/D323: a sig-less definition, `main` included, is a FunInfo at its
-- synthesized type (`main` is then used at `Eff Unit Unit`); never a schema.
extractFunctions-sigless name body rest _ =
  extractFunctions-consFun (extractFunctions-go rest nothing)
    (mkFunInfo name nothing body false)


-- Plan 0.50 (clash-freedom): REJECT duplicate top-level definition names. Two
-- definitions named `foo` both compile to the symbol `once_…foo` → "symbol
-- already defined" / a misdirected call. Enforcing distinctness HERE —
-- `extractFunctions` feeds BOTH `moduleToIR` (the compiler) and `ModuleTyped`
-- (the typing predicate) — makes a duplicate a compile error AND makes any typed
-- module IMPLY distinct names (the no-clash theorem's precondition, for free).
namesDistinct : List String → Bool
namesDistinct xs = does (allPairs? (λ x y → ¬? (x ≟ y)) xs)

-- Plan 0.50 (clash-freedom, validity half): each top-level definition name must
-- be a name the lexer makes — an identifier (head `isIdentStart`, tail
-- `isIdentContinue`) or an operator's (`isOpNameChar`, R14) — the SAME
-- predicates the lexer tokenises with. This is the precondition the symbol
-- mangling needs to be INJECTIVE (`once-symbol-path-injective`): the
-- self-delimiting length prefix only works because such a name's encoding never
-- starts with a digit. Checked HERE (no `with`), so `extractFunctions` success
-- carries it; `program-no-clash` reads it back off via `validNameB-sound`.
allIdentContinue : List Char → Bool
allIdentContinue []       = true
allIdentContinue (c ∷ cs) = isIdentContinue c ∧ allIdentContinue cs

validCharsB : List Char → Bool
validCharsB []       = false
validCharsB (c ∷ cs) = isIdentStart c ∧ allIdentContinue cs

allOpNameChars : List Char → Bool
allOpNameChars []       = true
allOpNameChars (c ∷ cs) = isOpNameChar c ∧ allOpNameChars cs

opCharsB : List Char → Bool
opCharsB []       = false
opCharsB (c ∷ cs) = allOpNameChars (c ∷ cs)

validNameB : String → Bool
validNameB s = validCharsB (toList s) ∨ opCharsB (toList s)

allValidNameB : List String → Bool
allValidNameB []       = true
allValidNameB (x ∷ xs) = validNameB x ∧ allValidNameB xs

-- The names that actually get EMITTED as symbols: only NON-primitive defs get a
-- `functionPrologue`/`.globl` label (primitives are external Strata symbols,
-- skipped by `compileFunWithTarget`). Clash-freedom + validity are required only
-- over these. This is FORCED by the codegen-faithful no-clash proof (`caf-syms`
-- in `Once.Adequacy.NameClash`), whose emitted-symbol set runs over exactly the
-- non-primitive `CompiledFun`s — checking imported/injected primitives (which may
-- carry qualified names) would wrongly reject valid programs.
-- de-withed (Bool-helper) so the codegen-faithfulness proof (`caf-syms`) can
-- case on `funIsPrimitive` and reduce both this and `emittedSyms` in lockstep.
emittedNames-cons : Bool → FunInfo → List String → List String
emittedNames-cons true  fi rest = rest
emittedNames-cons false fi rest = FunInfo.funName fi ∷ rest

emittedNames : List FunInfo → List String
emittedNames []         = []
emittedNames (fi ∷ fis) = emittedNames-cons (FunInfo.funIsPrimitive fi) fi (emittedNames fis)

-- Guard `extractFunctions-go`'s result on name well-formedness — DISTINCT and
-- each a valid identifier (with-free dispatch on the combined Bool). The
-- message is the guard's diagnosis (`guardMsg`); only the Bool decides.
distinctOrErr : Bool → String → EFResult → EFResult
distinctOrErr true  _   r = r
distinctOrErr false msg _ = inj₁ msg

-- The first name that occurs again later in the list, if any.
firstDuplicate : List String → Maybe String
duplicateOr    : Bool → String → List String → Maybe String
firstDuplicate []       = nothing
firstDuplicate (x ∷ xs) = duplicateOr (any (λ y → does (x ≟ y)) xs) x xs
duplicateOr true  x _  = just x
duplicateOr false _ xs = firstDuplicate xs

-- The first name that is neither an identifier nor an operator name, if any.
firstInvalid : List String → Maybe String
invalidOr    : Bool → String → List String → Maybe String
firstInvalid []       = nothing
firstInvalid (x ∷ xs) = invalidOr (validNameB x) x xs
invalidOr true  _ xs = firstInvalid xs
invalidOr false x _  = just x

-- The name an entry binds.
entryNameOf : Entry → String
entryNameOf (e-fun fi)   = FunInfo.funName fi
entryNameOf (e-poly pfi) = PolyFunInfo.pfunName pfi

-- What the guard reports when it fails. Every name the guard compares is an
-- entry name, so a duplicate among them is found in `map entryNameOf es`; a
-- guard with no duplicate failed on validity.
guardMsg : List Entry → String
guardMsg es = dupMsg (firstDuplicate (map entryNameOf es))
  where
    invalidMsg : Maybe String → String
    invalidMsg (just x) = "`" ++ x ++ "` is not an identifier or an operator name"
    invalidMsg nothing  = "ill-formed top-level name (duplicate or not an identifier)"
    dupMsg : Maybe String → String
    dupMsg (just x) = "`" ++ x ++ "` is declared more than once: definitions and `signature` declarations share one namespace, and each name is declared once"
    dupMsg nothing  = invalidMsg (firstInvalid (emittedNames (funsOf es)))

guardDistinct : EFResult → EFResult
guardDistinct (inj₁ err)            = inj₁ err
-- Plan 0.103 phase 1c / D241: every definition name is distinct — monomorphic
-- and telescope together (a definitions context with two entries of one name
-- is ill-formed, and a reference is resolved by name).
-- D249: and so is every ENTRY name, FFI declarations included — the function
-- table holds them all, and a call is resolved by name.
guardDistinct (inj₂ es) =
  distinctOrErr (((namesDistinct nms ∧ allValidNameB nms) ∧ namesDistinct (nms ++ₗ map PolyFunInfo.pfunName (polysOf es)))
                 ∧ namesDistinct (map entryNameOf es))
                (guardMsg es) (inj₂ es)
  where nms = emittedNames (funsOf es)

-- The Spec's `Walk` (`w-sig`): a type signature is IMMEDIATELY followed by
-- its own definition. Checked on the declarations as written, before the
-- signatures move (`sigsFirst`), so moving them cannot make a separated
-- signature and definition adjacent.
sigsAdjacent : List Decl → Maybe String → String ⊎ ⊤
-- (top level, so a proof can follow the decision)
sigsAdjacent-def : (s n : String) → Dec (s ≡ n) → List Decl → String ⊎ ⊤
sigsAdjacent []                    nothing  = inj₂ tt
sigsAdjacent []                    (just s) = inj₁ (danglingSig s)
sigsAdjacent (DTypeSig n _ ∷ ds)   nothing  = sigsAdjacent ds (just n)
sigsAdjacent (DTypeSig n _ ∷ ds)   (just s) = inj₁ (danglingSig s)
sigsAdjacent (DFunDef n _ ∷ ds)    nothing  = sigsAdjacent ds nothing
sigsAdjacent (DFunDef n _ ∷ ds)    (just s) = sigsAdjacent-def s n (s ≟ n) ds
{-# CATCHALL #-}
sigsAdjacent (_ ∷ ds)              nothing  = sigsAdjacent ds nothing
{-# CATCHALL #-}
sigsAdjacent (_ ∷ ds)              (just s) = inj₁ (danglingSig s)
sigsAdjacent-def s n (yes _) ds′ = sigsAdjacent ds′ nothing
sigsAdjacent-def s n (no _)  _   = inj₁ (danglingSig s)

-- The program's signature is its own `signature` declarations, then those
-- of its imports (the Spec's `Σ₀ ++ Σᵢ`), and every definition sees all of
-- it: the signature entries come first, in that order.
ownSigs : List Decl → List Decl
ownSigs []                        = []
ownSigs (DSignature n t ∷ ds)     = DSignature n t ∷ ownSigs ds
{-# CATCHALL #-}
ownSigs (_ ∷ ds)                  = ownSigs ds

-- (an imported signature, under its resolved name)
importedSigs : List (String × PolyType) → List Decl
importedSigs []             = []
importedSigs ((n , t) ∷ is) = DSignature n t ∷ importedSigs is

nonSigs : List Decl → List Decl
nonSigs []                    = []
nonSigs (DSignature _ _ ∷ ds) = nonSigs ds
{-# CATCHALL #-}
nonSigs (d ∷ ds)              = d ∷ nonSigs ds

sigsFirst : List Decl → List (String × PolyType) → List Decl
sigsFirst ds is = ownSigs ds ++ₗ (importedSigs is ++ₗ nonSigs ds)

thenExtract : String ⊎ ⊤ → EFResult → EFResult
thenExtract (inj₁ err) _ = inj₁ err
thenExtract (inj₂ _)   r = r

extractFunctions : Resolved → String ⊎ List Entry
extractFunctions (resolved (mkModule ds) is) =
  guardDistinct (thenExtract (sigsAdjacent ds nothing) (extractFunctions-go (sigsFirst ds is) nothing))

-- Plan 0.6.2: `inlineAll`, `inlineAllWithPoly`, `polySeedDefs` all
-- removed. The eager Expr-level inlining pipeline is replaced by
-- typecheck-time schema instantiation via `PolyCtx`
-- (Once.TypeCheck.Elaborate). Ground function cross-references flow
-- through the `FunCtx` import list; user polymorphic definitions
-- flow through `NamedCtx.polys`. See D045.