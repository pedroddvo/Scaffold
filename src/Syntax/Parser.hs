module Syntax.Parser where

import Control.Applicative (Alternative (..))
import Data.Char (isAlpha, isAlphaNum, isDigit)
import Data.Foldable (foldr')
import Data.List (foldl1')
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Span (Span (..))
import Syntax.Ast qualified as Ast
import Syntax.Name qualified as Name
import Text.Megaparsec qualified as M
import Text.Megaparsec.Char qualified as M
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = M.Parsec Void Text

sc :: Parser ()
sc = L.space M.space1 (L.skipLineComment "//") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

type Name = Name.Name Text

type Node a = Ast.Node (a Name) Span

type TNode a = a Name Span

span :: Parser a -> Parser Span
span p = do
  start <- M.getOffset
  _ <- p
  Span start <$> M.getOffset

node :: Parser (a Span) -> Parser (Ast.Node a Span)
node p = do
  start <- M.getOffset
  a <- p
  Ast.Node a . Span start <$> M.getOffset

keywords :: [Text]
keywords = ["let", "in", "fun", "def", "type"]

symbolP :: Parser Text
symbolP = M.try $ do
  sym <- T.cons <$> M.satisfy isAlpha <*> M.takeWhileP (Just "alphanumeric symbol") isAlphaNum
  if sym `elem` keywords
    then fail "unexpected keyword"
    else return sym

nameP :: Parser Name
nameP = Name.fromList <$> M.sepBy1 symbolP "."

-- stringLit :: Parser Text
-- stringLit =
--   T.cons
--     <$> M.satisfy (\c -> isAlpha c || c == '_')
--     <*> M.takeWhile1P (Just "C identifier") (\c -> isAlphaNum c || c == '_')

stringLit :: Parser Text
stringLit = M.between (symbol "\"") (symbol "\"") $ M.takeWhile1P (Just "C identifier") (/= '"')

pfoldr :: Parser a -> Parser b -> (a -> c) -> (a -> b -> c) -> Parser c
pfoldr pa pb fa fab = pa >>= \a -> (fab a <$> pb) <|> return (fa a)

pfoldl1 :: Parser a -> (a -> a -> a) -> Parser a
pfoldl1 pa f = foldl1' f <$> some pa

paren :: Parser a -> Parser a
paren = M.between (symbol "(") (symbol ")") . lexeme

curly :: Parser a -> Parser a
curly = M.between (symbol "{") (symbol "}") . lexeme

typeBase :: Parser (TNode Ast.TypeNode)
typeBase =
  (Ast.TSymbol <$> nameP)
    <|> (Ast.TBorrow <$> (symbol "&" >> typeP))
    <|> paren typeNode

typeArrow :: Parser (TNode Ast.TypeNode)
typeArrow = pfoldr (node $ lexeme typeBase) (symbol "->" >> node typeArrow) Ast.node_kind Ast.TArrow

typeNode :: Parser (TNode Ast.TypeNode)
typeNode = typeArrow

typeP :: Parser (Node Ast.TypeNode)
typeP = node typeNode

patternBase :: Parser (TNode Ast.PatternNode)
patternBase =
  paren patternNode
    <|> (Ast.PSymbol . Name.Name <$> symbolP)
    <|> (Ast.PNumeric <$> M.takeWhile1P (Just "number") isDigit)
    <|> (Ast.PWildcard <$ symbol "_")

patternAnno :: Parser (TNode Ast.PatternNode)
patternAnno = pfoldr (node $ lexeme patternBase) (symbol ":" >> typeP) Ast.node_kind Ast.PAnno

patternNode :: Parser (TNode Ast.PatternNode)
patternNode = patternAnno

patternP :: Parser (Node Ast.PatternNode)
patternP = node patternNode

exprSymbol :: Parser Name
exprSymbol = Name.Name <$> symbolP

exprBase :: Parser (TNode Ast.ExprNode)
exprBase =
  paren exprNode
    <|> (Ast.Symbol <$> exprSymbol)
    <|> (Ast.Numeric <$> M.takeWhile1P (Just "number") isDigit)
    <|> (Ast.String <$> stringLit)

leftRec :: Parser a -> Parser (a -> a) -> Parser a
leftRec p op = rest =<< p
  where
    rest x =
      do
        f <- op
        rest (f x)
        <|> return x

exprDot :: Parser (TNode Ast.ExprNode)
exprDot = Ast.node_kind <$> leftRec (node $ lexeme exprBase) (pdot <|> papp)
  where
    pdot = do
      start <- M.getOffset
      a <- Ast.DotUnresolved <$> ("." >> nameP)
      end <- M.getOffset
      return $ \e -> Ast.Node (Ast.Dot e a) (Ast.node_data e <> Span start end)

    papp = do
      start <- M.getOffset
      a <- paren (M.sepBy exprP (symbol ","))
      end <- M.getOffset
      return $ \e -> Ast.Node (Ast.App e a) (Ast.node_data e <> Span start end)

-- exprApp :: Parser (TNode Ast.ExprNode)
-- exprApp = Ast.node_kind <$> pfoldl1 (node $ lexeme exprBase) (\a b -> Ast.Node (Ast.App a b) (Ast.node_data a <> Ast.node_data b))

matchBranch :: Parser (Node Ast.PatternNode, Node Ast.ExprNode)
matchBranch = (,) <$> patternP <*> (symbol "=>" >> exprP)

exprNode :: Parser (TNode Ast.ExprNode)
exprNode =
  (Ast.Let <$> (symbol "let" >> patternP) <*> (symbol "=" >> exprP) <*> (symbol ";" >> exprP))
    <|> (Ast.Lam <$> (symbol "fun" >> patternP) <*> (symbol "=>" >> exprP))
    <|> (Ast.Match <$> (symbol "match" >> exprP) <*> curly (M.sepBy matchBranch (symbol ",")))
    <|> exprDot

exprP :: Parser (Node Ast.ExprNode)
exprP = node exprNode

type Stmt = Node Ast.ExprNode -> (Span, TNode Ast.ExprNode)

stmt :: Parser Stmt
stmt = externStmt <|> stmtDef <|> stmtType Ast.NonExtern

externStmt :: Parser Stmt
externStmt = symbol "extern" >> (externStmtDef <|> stmtType Ast.Extern)

externStmtDef :: Parser Stmt
externStmtDef = do
  start <- M.getOffset
  name <- symbol "def" >> lexeme nameP
  args <- defArgs
  ret <- symbol ":" >> typeP
  cident <- symbol "=" >> stringLit
  end <- M.getOffset
  return $ \rest -> (Span start end, Ast.ExternDef name args ret cident rest)

stmtDef :: Parser Stmt
stmtDef = do
  start <- M.getOffset
  name <- symbol "def" >> lexeme nameP
  args <- defArgs
  ret <- M.optional (symbol ":" >> typeP)
  e <- symbol "=" >> exprP
  end <- M.getOffset
  return $ \rest -> (Span start end, Ast.Def name args ret e rest)

defArgs :: Parser [Node Ast.PatternNode]
defArgs = concat <$> paren (M.sepBy defArg (symbol ","))

defArg :: Parser [Node Ast.PatternNode]
defArg =
  (\pats t -> map (\p -> Ast.Node (Ast.PAnno p t) (Ast.node_data p <> Ast.node_data t)) pats)
    <$> some (node $ lexeme patternBase)
    <*> (symbol ":" >> typeP)

stmtType :: Ast.Extern -> Parser Stmt
stmtType extern = do
  start <- M.getOffset
  name <- symbol "type" >> lexeme nameP
  cident <- symbol "=" >> stringLit
  end <- M.getOffset
  return $ \rest -> (Span start end, Ast.Type extern name cident rest)

program :: Parser (Node Ast.ExprNode)
program = do
  stmts <- some stmt
  let unit = Ast.Node Ast.Unit (Span 0 0)
  return $ foldr' foldStmt unit stmts
  where
    foldStmt f a = let (sp, b) = f a in Ast.Node b sp
