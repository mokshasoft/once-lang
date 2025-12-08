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
  [ "case", "of", "Left", "Right"
  , "Unit", "Void", "Int"
  , "primitive"
  -- Generators (the 12 categorical primitives)
  , "id", "compose"
  , "fst", "snd", "pair"
  , "inl", "inr"
  , "terminal", "initial"
  , "curry", "apply"
  ]

-- | Parse an integer literal
integer :: Parser Integer
integer = lexeme L.decimal

-- | Parse a type variable (uppercase identifier)
typeVar :: Parser Name
typeVar = lexeme $ try $ do
  c <- upperChar
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = T.pack (c : cs)
  if name `elem` ["Unit", "Void", "Left", "Right"]
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
      , STVar <$> typeVar
      , parens parseType
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
      e <- appExpr
      option e (EAnnot e <$> (symbol ":" *> parseType))

    -- Application is left-associative
    appExpr = chainl1 atomExpr (pure EApp)

    atomExpr = choice
      [ EUnit <$ symbol "()"
      , EInt <$> integer
      , caseExpr
      , lamExpr
      , pairOrParens
      , generator
      , EVar <$> lowerIdent
      ]

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
      ]

    lamExpr = do
      void $ symbol "\\"
      x <- lowerIdent
      void $ symbol "->"
      e <- parseExpr
      pure $ ELam x e

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

    typeSig = do
      name <- lowerIdent
      void $ symbol ":"
      ty <- parseType
      pure $ TypeSig name ty

    funDef = do
      name <- lowerIdent
      void $ symbol "="
      e <- parseExpr
      pure $ FunDef name e

-- -----------------------------------------------------------------------------
-- Module Parser
-- -----------------------------------------------------------------------------

-- | Parse a module (list of declarations)
parseModule :: Text -> Either ParseError Module
parseModule input = Module <$> parse (sc *> many parseDecl <* eof) "<input>" input
