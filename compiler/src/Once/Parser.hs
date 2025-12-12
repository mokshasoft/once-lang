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
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Text.Megaparsec hiding (ParseError)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Once.Quantity (Quantity (..))
import Once.Syntax
import Once.Type (Encoding (..))

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
  , "Unit", "Void", "Int", "Buffer", "String"
  , "Utf8", "Utf16", "Ascii"
  , "primitive"
  , "type", "Fix"             -- Type aliases and fixed points
  , "import", "as"            -- Module system
  , "let", "in"               -- Let bindings
  -- The 12 categorical generators
  , "id", "compose"           -- Category
  , "fst", "snd", "pair"      -- Products
  , "inl", "inr", "case"      -- Coproducts
  , "terminal", "initial"     -- Terminal/Initial
  , "curry", "apply"          -- Closed
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
  if name `elem` ["Unit", "Void", "Left", "Right", "Buffer", "String", "Utf8", "Utf16", "Ascii", "Int"]
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
      , STBuffer <$ reserved "Buffer"
      , stringType
      , fixType
      , typeApp
      , STVar <$> typeVar
      , parens parseType
      ]

    -- Fix F (fixed point of functor F)
    fixType = do
      reserved "Fix"
      STFix <$> atomType

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
parseExpr :: Parser Expr
parseExpr = annotExpr
  where
    annotExpr = do
      e <- composeExpr
      option e (EAnnot e <$> (symbol ":" *> parseType))

    -- Composition with . is right-associative (like Haskell)
    -- f . g . h = f . (g . h)
    composeExpr = do
      e <- appExpr
      option e (do
        void $ symbol "."
        e2 <- composeExpr
        -- Desugar f . g to compose f g
        pure $ EApp (EApp (EVar "compose") e) e2)

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
      [ EUnit <$ symbol "()"
      , EInt <$> integer
      , EStringLit <$> stringLiteral
      , caseExpr
      , letExpr
      , lamExpr
      , pairOrParens
      , generator
      , qualifiedOrVar
      ]

    -- Parse either a qualified name (name@Module.Path) or plain variable
    -- The @ for qualified access is different from @alloc annotations:
    -- - @alloc comes after name in definitions: foo @heap = ...
    -- - @Module comes after name in expressions: swap@Product x
    qualifiedOrVar = do
      name <- lowerIdent
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
      , EVar "terminal" <$ reserved "terminal"
      , EVar "initial" <$ reserved "initial"
      , EVar "curry" <$ reserved "curry"
      , EVar "apply" <$ reserved "apply"
      -- Recursive type generators
      , EVar "fold" <$ reserved "fold"
      , EVar "unfold" <$ reserved "unfold"
      ]

    lamExpr = do
      void $ symbol "\\"
      x <- lowerIdent
      void $ symbol "->"
      e <- parseExpr
      pure $ ELam x e

    -- let bindings with semicolon separation:
    --   let x = e1; y = e2 in body
    -- Desugars to nested lets: let x = e1 in let y = e2 in body
    -- Single binding also works: let x = e1 in body
    letExpr = do
      reserved "let"
      bindings <- letBinding `sepBy1` symbol ";"
      reserved "in"
      body <- parseExpr
      pure $ foldr (\(x, e) acc -> ELet x e acc) body bindings

    -- Single binding: x = e
    -- Uses simpleExpr to avoid consuming too much (stops at ; or 'in')
    letBinding = do
      x <- lowerIdent
      void $ symbol "="
      e <- simpleExpr
      pure (x, e)

    -- Simple expression that doesn't consume ; or 'in'
    -- This is a workaround - proper solution would be expression with precedence
    simpleExpr = composeExpr

    caseExpr = do
      reserved "case"
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

    pairOrParens = do
      void $ symbol "("
      e1 <- parseExpr
      choice
        [ do
            void $ symbol ","
            e2 <- parseExpr
            void $ symbol ")"
            pure $ EPair e1 e2
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
      name <- lowerIdent
      void $ symbol ":"
      ty <- parseType
      pure $ TypeSig name ty

    funDef = do
      name <- lowerIdent
      alloc <- optional allocAnnotation
      void $ symbol "="
      e <- parseExpr
      pure $ FunDef name alloc e

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
