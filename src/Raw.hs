{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# LANGUAGE TupleSections #-}
module Raw (
  RVar, Raw (..),
  parseString, parseStdin
) where
import Unbound.Generics.LocallyNameless
import Text.Megaparsec
import qualified Text.Megaparsec.Char as C
import qualified Data.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import GHC.Generics (Generic)
import Data.Void (Void)
import Control.Monad
import Control.Monad.Except
import System.Exit (exitSuccess)

import Utils

-- Raw terms
type RVar = Name Raw
data Raw
  = RVar RVar
  | RLam (Bind RVar Raw) | RApp Raw Raw | RPi Raw (Bind RVar Raw)
  | RPair Raw Raw | RFst Raw | RSnd Raw | RSigma Raw (Bind RVar Raw)
  | RZero | RSuc Raw
  | RNatElim
    {- motive -} (Bind RVar Raw)
    {- zero -} Raw
    {- suc -} (Bind (RVar, RVar) Raw)
    {- arg -} Raw
  | RNat
  | RUniverse -- implicit Coquand universe
  | RThe Raw Raw
  deriving (Generic, Show)

instance Alpha Raw

instance Subst Raw Raw where
  isvar (RVar x) = Just (SubstName x)
  isvar _ = Nothing

------ Parser ------

type Parser = Parsec Void String
type Identifier = String
data ParseTree
  = TNode Identifier [([Identifier], ParseTree)]
  | TApp ParseTree ParseTree
  | TInt Integer
  deriving Show

spaceEater :: Parser ()
spaceEater = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceEater

symbol :: String -> Parser String
symbol = lexeme . C.string

char :: Char -> Parser Char
char = lexeme . C.char

parens :: Parser a -> Parser a
parens p = char '(' *> p <* char ')'

pArrow, pTimes :: Parser String
pArrow = (symbol "→" <|> symbol "->") <?> "arrow"
pTimes = (symbol "×" <|> symbol "*") <?> "times"

pArrowTimes :: Parser Bool
pArrowTimes = (True <$ pArrow) <|> (False <$ pTimes)

pIdent :: Parser String
pIdent = try (do
  x0 <- C.letterChar
  guard $ x0 /= 'λ'
  x <- takeWhileP Nothing (\x -> C.isAlphaNum x || (x == '\''))
  -- guard $ notElem (x0:x) [] -- keywords
  (x0:x) <$ spaceEater) <?> "identifier"

pAtom :: Parser ParseTree
pAtom = choice [
    TInt <$> lexeme L.decimal,
    try pCons,
    (`TNode` []) <$> pIdent,
    parens pRaw
  ]

pBinder :: Parser Identifier
pBinder = pIdent <|> symbol "_"

pBinders :: Parser ([Identifier], ParseTree)
pBinders = do
  xs <- some pBinder
  char '.'
  t <- pRaw
  return (xs, t)

pSpine :: Parser ParseTree
pSpine  = foldl1 TApp <$> some pAtom

pLam :: Parser ParseTree
pLam = do
  (char 'λ' <|> char '\\') <?> "lambda"
  (xs, t) <- pBinders
  pure (foldr (\x b -> TNode "Lam" [([x], b)]) t xs)

pPiSigma :: Parser ParseTree
pPiSigma = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pRaw)))
  isPi <- pArrowTimes
  cod <- pRaw
  pure $ foldr
    (\(xs, a) t -> foldr
      (\x b -> TNode
        (if isPi then "Pi" else "Sigma")
        [([], a), ([x], b)])
      t xs)
    cod dom

funOrSpine :: Parser ParseTree
funOrSpine = do
  sp <- pSpine
  optional pArrowTimes >>= \case
    Nothing -> pure sp
    Just isPi -> (\b -> TNode
      (if isPi then "Pi" else "Sigma")
      [([], sp), (["_"], b)]) <$> pRaw

pCons :: Parser ParseTree
pCons = do
  cons <- pIdent
  args <- parens $ (try pBinders <|> (([],) <$> pRaw)) `sepBy` char ','
  return $ TNode cons args

pRaw :: Parser ParseTree
pRaw = pLam
  <|> try pPiSigma
  <|> funOrSpine

pSrc :: Parser ParseTree
pSrc = spaceEater *> pRaw <* eof

toRaw :: ParseTree -> Either String Raw
toRaw = runExcept . runFreshMT . go []
  where
    pushVar x vx = if x == "_" then id else ((x,vx):)

    go :: [(Identifier, RVar)] -> ParseTree -> FreshMT (Except String) Raw
    go env (TNode "Lam" [([x], b)]) = do
      v <- fresh (s2n x)
      RLam . bind v <$> go (pushVar x v env) b
    go env (TApp t1 t2) = RApp <$> go env t1 <*> go env t2
    go env (TNode "Pi" [([], dom), ([x], cod)]) = do
      rdom <- go env dom
      v <- fresh (s2n x)
      rcod <- go (pushVar x v env) cod
      return $ RPi rdom (bind v rcod)

    go env (TNode "pair" [([], p), ([], q)]) = RPair <$> go env p <*> go env q
    go env (TNode "fst" [([], p)]) = RFst <$> go env p
    go env (TNode "snd" [([], p)]) = RSnd <$> go env p
    go env (TNode "Sigma" [([], dom), ([x], cod)]) = do
      rdom <- go env dom
      v <- fresh (s2n x)
      rcod <- go (pushVar x v env) cod
      return $ RSigma rdom (bind v rcod)

    go _ (TNode "zero" []) = return RZero
    go env (TNode "suc" [([], p)]) = RSuc <$> go env p
    go _ (TInt k) = return $ nTimes k RSuc RZero
    go _ (TNode "Nat" []) = return RNat
    go env (TNode "elim" [([y], m), ([], z), ([x, r], s), ([], n)]) = do
      vy <- fresh (s2n y)
      rm <- go (pushVar y vy env) m
      rz <- go env z
      vx <- fresh (s2n x)
      vr <- fresh (s2n r)
      rs <- go (pushVar x vx $ pushVar r vr env) s
      rn <- go env n
      return $ RNatElim (bind vy rm) rz (bind (vx, vr) rs) rn

    go _ (TNode "U" []) = return RUniverse

    go env (TNode "the" [([], p), ([], q)]) = RThe <$> go env p <*> go env q

    go env (TNode v []) = case lookup v env of
      Just v' -> return $ RVar v'
      Nothing -> throwError $ "Unrecognized identifier: " ++ v
    go _ (TNode v _) = throwError $ "Unrecognized constructor: " ++ show v

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t -> case toRaw t of
      Left s -> do
        putStrLn s
        exitSuccess
      Right r -> return r

parseStdin :: IO (Raw, String)
parseStdin = do
  file <- getContents
  tm   <- parseString file
  pure (tm, file)

