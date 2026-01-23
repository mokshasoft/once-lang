module Once.Parser
  ( -- * Parsing
    parseModule
  , parseExpr
  , parseType
    -- * Error type
  , ParseError
  ) where

import Control.Monad (void)
import Data.Functor (($>))
import Data.List (foldl')
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Text.Megaparsec hiding (ParseError)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Once.Quantity (Quantity (..))
import Once.Syntax
import Once.Type (Encoding (..))

-- | Simple pattern for let bindings
data Pattern
  = PVar Name           -- ^ Simple variable: x
  | PWild               -- ^ Wildcard: _ (discard)
  | PTuple [Pattern]    -- ^ Tuple pattern: (x, y, z)
  deriving (Eq, Show)

-- | Parser type
type Parser = Parsec Void Text

-- | Parse error type
type ParseError = ParseErrorBundle Text Void

-- -----------------------------------------------------------------------------
-- Lexer
-- -----------------------------------------------------------------------------

-- | Space consumer (handles whitespace and comments)
sc :: Parser ()
sc = L.space space1 lineComment blockComment
  where
    lineComment = L.skipLineComment "--"
    blockComment = L.skipBlockComment "{-" "-}"

-- | Lexeme wrapper
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- | Symbol parser
symbol :: Text -> Parser Text
symbol = L.symbol sc

-- | Parse a reserved word
reserved :: Text -> Parser ()
reserved w = lexeme $ try (string w *> notFollowedBy alphaNumChar)

-- | Reserved words (keywords that cannot be used as identifiers)
reservedWords :: [Text]
reservedWords =
  -- Keywords
  [ "of", "Left", "Right"
  , "Unit", "Void", "Int", "Float", "Buffer", "String"
  , "Utf8", "Utf16", "Ascii"
  , "primitive"
  , "type", "Fix"             -- Type aliases and fixed points
  , "Eff", "IO"               -- Effect types (D032)
  , "import", "as"            -- Module system
  , "let", "in"               -- Let bindings
  -- The 12 categorical generators + arr for effects
  , "id", "compose"           -- Category
  , "fst", "snd", "pair"      -- Products
  , "inl", "inr", "case"      -- Coproducts (case = generator, destruct = syntax)
  , "terminal", "initial"     -- Terminal/Initial
  , "curry", "apply"          -- Closed
  , "arr"                     -- Arrow: lift pure to effectful (D032)
  , "destruct"                -- Sum elimination syntax (D041)
  -- Recursive type generators
  , "fold", "unfold"          -- Fix isomorphism
  -- Allocation strategies
  , "stack", "heap", "pool", "arena", "const"
  ]

-- | Parse an integer literal
integer :: Parser Integer
integer = lexeme L.decimal

-- | Parse a string literal
stringLiteral :: Parser Text
stringLiteral = lexeme $ do
  void $ char '"'
  content <- many stringChar
  void $ char '"'
  pure $ T.pack content
  where
    stringChar = (char '\\' *> escapeChar) <|> satisfy (\c -> c /= '"' && c /= '\\')
    escapeChar = choice
      [ char 'n' $> '\n'
      , char 't' $> '\t'
      , char 'r' $> '\r'
      , char '\\' $> '\\'
      , char '"' $> '"'
      ]

-- | Parse a type variable (uppercase identifier)
typeVar :: Parser Name
typeVar = lexeme $ try $ do
  c <- upperChar
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = T.pack (c : cs)
  if name `elem` ["Unit", "Void", "Left", "Right", "Buffer", "String", "Utf8", "Utf16", "Ascii", "Int", "Float", "Eff", "IO", "Fix"]
    then fail $ "Reserved type: " ++ T.unpack name
    else pure name

-- | Parse a lowercase identifier (variable/function name)
lowerIdent :: Parser Name
lowerIdent = lexeme $ try $ do
  c <- lowerChar <|> char '_'
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = T.pack (c : cs)
  if name `elem` reservedWords
    then fail $ "Reserved word: " ++ T.unpack name
    else pure name

-- | Parse an operator identifier: (.) (&) (|>) (+) etc.
-- Used for operator function definitions like: (.) = compose
-- Uses try so it backtracks if it doesn't match (e.g., for normal parens)
operatorIdent :: Parser Name
operatorIdent = lexeme $ try $ do
  void $ char '('
  op <- some (oneOf ("!#$%&*+./<=>?@\\^|-~" :: String))
  void $ char ')'  -- Must close immediately after operators
  pure $ T.pack op

-- | Parse a name (either lowercase identifier or operator in parens)
-- Used for function definitions and type signatures
nameIdent :: Parser Name
nameIdent = operatorIdent <|> lowerIdent

-- | Parse an uppercase identifier (module name component)
upperIdent :: Parser Name
upperIdent = lexeme $ try $ do
  c <- upperChar
  cs <- many (alphaNumChar <|> char '_')
  let name = T.pack (c : cs)
  -- Module names like Canonical, Product are allowed
  pure name

-- | Parentheses
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- -----------------------------------------------------------------------------
-- Type Parser
-- -----------------------------------------------------------------------------

-- | Parse a type
parseType :: Parser SType
parseType = makeTypeExpr
  where
    -- Function arrow is right-associative, lowest precedence
    makeTypeExpr = do
      t <- sumType
      option t (STArrow t <$> (symbol "->" *> makeTypeExpr))

    -- Sum type (+) is left-associative
    sumType = chainl1 productType (STSum <$ symbol "+")

    -- Product type (*) is left-associative, higher precedence than sum
    productType = chainl1 quantType (STProduct <$ symbol "*")

    -- Quantity annotation (^) is postfix
    quantType = do
      t <- atomType
      option t (do
        void $ symbol "^"
        q <- quantity
        pure $ STQuant q t)

    quantity :: Parser Quantity
    quantity = choice
      [ Zero <$ symbol "0"
      , One <$ symbol "1"
      , Omega <$ symbol "w"
      ]

    atomType = choice
      [ STUnit <$ reserved "Unit"
      , STVoid <$ reserved "Void"
      , STInt <$ reserved "Int"
      , STFloat <$ reserved "Float"
      , STBuffer <$ reserved "Buffer"
      , stringType
      , fixType
      , effType     -- Eff A B (effectful morphism, D032)
      , ioType      -- IO A = Eff Unit A (sugar, D032)
      , typeApp
      , STVar <$> typeVar
      , parens parseType
      ]

    -- Fix F (fixed point of functor F)
    fixType = do
      reserved "Fix"
      STFix <$> atomType

    -- Eff A B (effectful morphism from A to B, D032)
    effType = do
      reserved "Eff"
      a <- simpleType
      b <- simpleType
      pure $ STEff a b

    -- IO A = Eff Unit A (sugar for effectful computation, D032)
    ioType = do
      reserved "IO"
      a <- simpleType
      pure $ STEff STUnit a

    -- Type constructor application: Maybe A, List Int, Either A B
    -- Must be a named type followed by one or more type arguments
    -- Arguments must be "simple" types (not type applications themselves)
    typeApp = try $ do
      name <- upperIdent
      args <- some simpleType
      pure $ STApp name args

    -- Simple types that can be arguments to type applications
    -- These don't include typeApp to avoid left recursion issues
    simpleType = choice
      [ STUnit <$ reserved "Unit"
      , STVoid <$ reserved "Void"
      , STInt <$ reserved "Int"
      , STFloat <$ reserved "Float"
      , STBuffer <$ reserved "Buffer"
      , stringType
      , fixType
      , STVar <$> typeVar
      , parens parseType
      ]

    -- String with optional encoding: "String Utf8", "String Ascii", or just "String" (defaults to Utf8)
    stringType = do
      reserved "String"
      enc <- option Utf8 encoding
      pure $ STString enc

    encoding = choice
      [ Utf8 <$ reserved "Utf8"
      , Utf16 <$ reserved "Utf16"
      , Ascii <$ reserved "Ascii"
      ]

-- | Left-associative chain
chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = do
  x <- p
  rest x
  where
    rest x = (do
      f <- op
      y <- p
      rest (f x y)) <|> pure x

-- -----------------------------------------------------------------------------
-- Expression Parser
-- -----------------------------------------------------------------------------

-- | Parse an expression
--
-- Precedence (low to high):
--   1. Type annotation (:)
--   2. Composition (.)
--   3. Comparison (<, <=, >, >=, ==, !=) - non-associative
--   4. Additive (+, -) - left-associative
--   5. Multiplicative (*, /, %) - left-associative
--   6. Unary negation (-)
--   7. Application
--
parseExpr :: Parser Expr
parseExpr = annotExpr
  where
    annotExpr = do
      e <- composeExpr
      option e (EAnnot e <$> (symbol ":" *> parseType))

    -- Composition with . is right-associative (like Haskell)
    -- f . g . h = f . (g . h)
    composeExpr = do
      e <- compareExpr
      option e (do
        void $ symbol "."
        e2 <- composeExpr
        -- Desugar f . g to compose f g
        pure $ EApp (EApp (EVar "compose") e) e2)

    -- Comparison operators (non-associative, lowest arithmetic precedence)
    -- a < b < c is a parse error (non-associative)
    compareExpr = do
      e1 <- addExpr
      option e1 $ do
        op <- compareOp
        e2 <- addExpr
        pure $ EBinOp op e1 e2

    compareOp :: Parser BinOp
    compareOp = choice
      [ OpLe <$ try (symbol "<=")  -- try to handle <= vs <
      , OpGe <$ try (symbol ">=")  -- try to handle >= vs >
      , OpEq <$ try (symbol "==")
      , OpNe <$ try (symbol "!=")
      , OpLt <$ symbol "<"
      , OpGt <$ symbol ">"
      ]

    -- Additive operators (left-associative)
    -- Note: we use addOp which excludes unary - context
    addExpr = chainl1 mulExpr addOp

    addOp :: Parser (Expr -> Expr -> Expr)
    addOp = choice
      [ (\l r -> EBinOp OpAdd l r) <$ symbol "+"
      , (\l r -> EBinOp OpSub l r) <$ symbol "-"
      ]

    -- Multiplicative operators (left-associative)
    mulExpr = chainl1 unaryExpr mulOp

    mulOp :: Parser (Expr -> Expr -> Expr)
    mulOp = choice
      [ (\l r -> EBinOp OpMul l r) <$ symbol "*"
      , (\l r -> EBinOp OpDiv l r) <$ symbol "/"
      , (\l r -> EBinOp OpMod l r) <$ symbol "%"
      ]

    -- Unary negation (higher precedence than binary operators)
    unaryExpr = choice
      [ do void $ symbol "-"
           e <- unaryExpr
           pure $ EUnaryOp OpNeg e
      , appExpr
      ]

    -- Application is left-associative
    -- But don't consume identifiers that start a new declaration (name : Type)
    appExpr = chainl1 atomExprNoDecl (pure EApp)

    -- Atom expression that doesn't consume what looks like a new declaration
    atomExprNoDecl = try $ do
      e <- atomExpr
      -- If this is an identifier followed by :, it might be a type signature
      -- Don't consume it - let the declaration parser handle it
      case e of
        EVar _ -> notFollowedBy (symbol ":") *> pure e
        _ -> pure e

    atomExpr = choice
      [ EUnit <$ try (symbol "()")  -- try needed: ( might start other things
      , EInt <$> integer
      , EStringLit <$> stringLiteral
      , destructExpr  -- D041: destruct is the syntax for sum elimination
      , letExpr
      , lamExpr
      , generator
      , qualifiedOrVar  -- Before pairOrParens so (&) operator refs are matched
      , pairOrParens
      ]

    -- Parse either a qualified name (name@Module.Path) or plain variable
    -- The @ for qualified access is different from @alloc annotations:
    -- - @alloc comes after name in definitions: foo @heap = ...
    -- - @Module comes after name in expressions: swap@Product x
    -- Also supports operator identifiers like (&) for references: (|>) = (&)
    qualifiedOrVar = do
      name <- nameIdent
      option (EVar name) $ do
        void $ char '@'  -- no space allowed between name and @
        modPath <- modulePath
        pure $ EQualified name modPath

    -- Parse a generator (reserved primitive)
    generator = choice
      [ EVar "id" <$ reserved "id"
      , EVar "compose" <$ reserved "compose"
      , EVar "fst" <$ reserved "fst"
      , EVar "snd" <$ reserved "snd"
      , EVar "pair" <$ reserved "pair"
      , EVar "inl" <$ reserved "inl"
      , EVar "inr" <$ reserved "inr"
      , EVar "case" <$ reserved "case"  -- Copairing: (A → C) → (B → C) → (A + B → C) (D041)
      , EVar "terminal" <$ reserved "terminal"
      , EVar "initial" <$ reserved "initial"
      , EVar "curry" <$ reserved "curry"
      , EVar "apply" <$ reserved "apply"
      -- Arrow generator (D032)
      , EVar "arr" <$ reserved "arr"
      -- Recursive type generators
      , EVar "fold" <$ reserved "fold"
      , EVar "unfold" <$ reserved "unfold"
      ]

    -- Lambda with multiple parameters: \a b c -> e  desugars to \a -> \b -> \c -> e
    lamExpr = do
      void $ symbol "\\"
      params <- some lowerIdent  -- one or more parameters
      void $ symbol "->"
      e <- parseExpr
      pure $ foldr ELam e params

    -- let bindings with semicolon separation:
    --   let x = e1; y = e2 in body
    --   let (a, b, c) = e in body   -- tuple pattern
    -- Desugars to nested lets with fst/snd projections for tuples
    letExpr = do
      reserved "let"
      bindings <- letBinding `sepBy1` symbol ";"
      reserved "in"
      body <- parseExpr
      pure $ foldr desugarBinding body bindings

    -- Single binding: pattern = e
    -- Uses simpleExpr to avoid consuming too much (stops at ; or 'in')
    letBinding = do
      pat <- pattern_
      void $ symbol "="
      e <- simpleExpr
      pure (pat, e)

    -- Parse a pattern (variable, wildcard, or tuple)
    pattern_ = choice
      [ PWild <$ symbol "_"   -- Wildcard pattern (discard)
      , PVar <$> lowerIdent
      , tuplePattern
      ]

    -- Parse tuple pattern: (x, y) or (a, b, c, d, ...)
    tuplePattern = do
      void $ symbol "("
      p1 <- pattern_
      void $ symbol ","
      rest <- pattern_ `sepBy1` symbol ","
      void $ symbol ")"
      pure $ PTuple (p1 : rest)

    -- Desugar pattern binding to nested lets with projections
    -- let x = e in body  →  ELet x e body
    -- let _ = e in body  →  body (discard e, but evaluate for effects)
    -- let (a, b) = e in body  →  let temp = e in let a = fst temp in let b = snd temp in body
    desugarBinding :: (Pattern, Expr) -> Expr -> Expr
    desugarBinding (PVar x, e) body = ELet x e body
    desugarBinding (PWild, _e) body = body  -- Wildcard: discard the value
    desugarBinding (PTuple pats, e) body =
      let tempName = "_tuple"
      in ELet tempName e (desugarTuplePatternLeft tempName pats body)

    -- Desugar tuple pattern with projections for LEFT-nested tuples
    -- For left-nested tuples: (a, b, c, d) = (((a, b), c), d)
    desugarTuplePatternLeft :: Name -> [Pattern] -> Expr -> Expr
    desugarTuplePatternLeft temp pats body =
      let n = length pats
          applyFsts k = iterate (EApp (EVar "fst")) (EVar temp) !! k
          buildProjection idx
            | idx == 0  = applyFsts (n - 1)  -- First: just fst's
            | otherwise = EApp (EVar "snd") (applyFsts (n - 1 - idx))  -- Others: fst's then snd
          bindings = zip pats (map buildProjection [0..])
      in foldr (\(p, proj) acc -> desugarBinding (p, proj) acc) body bindings

    -- Simple expression that doesn't consume ; or 'in'
    simpleExpr = composeExpr

    -- Sum elimination: destruct e of { Left x -> e1; Right y -> e2 }
    -- Note: 'case' is now a generator (copairing). Use 'destruct' for pattern matching.
    -- D041: The 'destruct' keyword is the syntax for sum elimination with variable binding.
    destructExpr = do
      reserved "destruct"
      e <- parseExpr
      reserved "of"
      void $ symbol "{"
      reserved "Left"
      x <- lowerIdent
      void $ symbol "->"
      e1 <- parseExpr
      void $ symbol ";"
      reserved "Right"
      y <- lowerIdent
      void $ symbol "->"
      e2 <- parseExpr
      void $ symbol "}"
      pure $ ECase e x e1 y e2

    -- Parse tuple literals or parenthesized expressions
    -- (e) = just e (parentheses for grouping)
    -- (e1, e2) = EPair e1 e2
    -- (e1, e2, e3) = EPair (EPair e1 e2) e3  -- left-nested to match type A * B * C
    pairOrParens = do
      void $ symbol "("
      e1 <- parseExpr
      choice
        [ do
            void $ symbol ","
            rest <- parseExpr `sepBy1` symbol ","
            void $ symbol ")"
            -- Fold into left-nested pairs: (a, b, c, d) → (((a, b), c), d)
            pure $ foldl' EPair e1 rest
        , symbol ")" $> e1
        ]

-- -----------------------------------------------------------------------------
-- Declaration Parser
-- -----------------------------------------------------------------------------

-- | Parse a declaration
parseDecl :: Parser Decl
parseDecl = choice
  [ primitiveDecl
  , typeAliasDecl
  , try typeSig
  , funDef
  ]
  where
    primitiveDecl = do
      reserved "primitive"
      name <- lowerIdent
      void $ symbol ":"
      ty <- parseType
      pure $ Primitive name ty

    -- | Parse type alias: type Name A B C = Type
    typeAliasDecl = do
      reserved "type"
      name <- upperIdent
      params <- many typeVar
      void $ symbol "="
      ty <- parseType
      pure $ TypeAlias name params ty

    typeSig = do
      name <- nameIdent
      void $ symbol ":"
      ty <- parseType
      pure $ TypeSig name ty

    -- | Parse function definition with optional named parameters
    -- f x y = e  desugars to  f = \x -> \y -> e
    -- Also supports operator definitions: (.) = compose
    funDef = do
      name <- nameIdent
      params <- many lowerIdent  -- zero or more parameters (not for operators)
      alloc <- optional allocAnnotation
      void $ symbol "="
      e <- parseExpr
      -- Desugar: f x y = e  →  f = \x -> \y -> e
      pure $ FunDef name alloc (foldr ELam e params)

    allocAnnotation = do
      void $ symbol "@"
      choice
        [ AllocStack <$ reserved "stack"
        , AllocHeap <$ reserved "heap"
        , AllocPool <$ reserved "pool"
        , AllocArena <$ reserved "arena"
        , AllocConst <$ reserved "const"
        ]

-- -----------------------------------------------------------------------------
-- Import Parser
-- -----------------------------------------------------------------------------

-- | Parse an import declaration
--
-- Syntax:
--   import Module.Path          -- simple import
--   import Module.Path as Alias -- aliased import
--
parseImport :: Parser Import
parseImport = do
  reserved "import"
  modPath <- modulePath
  alias <- optional (reserved "as" *> upperIdent)
  pure $ Import modPath alias

-- | Parse a module path (dot-separated uppercase identifiers)
--
-- Example: Canonical.Product -> ["Canonical", "Product"]
--
modulePath :: Parser [Name]
modulePath = sepBy1 upperIdent (symbol ".")

-- -----------------------------------------------------------------------------
-- Module Parser
-- -----------------------------------------------------------------------------

-- | Parse a module (imports followed by declarations)
parseModule :: Text -> Either ParseError Module
parseModule input = parse (sc *> moduleP <* eof) "<input>" input
  where
    moduleP = Module <$> many parseImport <*> many parseDecl
