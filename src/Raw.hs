{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Raw (
  RVar, Raw (..), RawJudgment (..),
  parseString
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
  = RVar RVar | RConst Identifier [Raw]
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
  | RHole
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
  | THole
  deriving Show

spaceEater :: Parser ()
spaceEater = L.space C.space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

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

pIdent_ :: Parser String
pIdent_ = try (do
  x0 <- C.letterChar
  guard $ x0 /= 'λ'
  x <- takeWhileP Nothing (\x -> C.isAlphaNum x || (x == '\''))
  guard $ notElem (x0:x) ["define", "postulate", "eval"] -- keywords
  return (x0:x)) <?> "identifier"

pIdent :: Parser String
pIdent = pIdent_ <* spaceEater

pAtom :: Parser ParseTree
pAtom = choice [
    TInt <$> lexeme L.decimal,
    THole <$ symbol "_",
    try pCons,
    (`TNode` []) <$> pIdent,
    parens pRaw
  ]

pBinder :: Parser Identifier
pBinder = pIdent <|> symbol "_"

pBinders :: Parser ([Identifier], ParseTree)
pBinders = do
  xs <- some pBinder
  -- todo for any repeat, replace the earlier ones with _ (or unreachable variants of it)
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
  cons <- pIdent_ -- you can't have space here
  args <- parens $ (try pBinders <|> (([],) <$> pRaw)) `sepBy` char ','
  return $ TNode cons args

pRaw :: Parser ParseTree
pRaw = pLam
  <|> try pPiSigma
  <|> funOrSpine

pushVar :: String -> b -> [(String, b)] -> [(String, b)]
pushVar x vx = if x == "_" then id else ((x,vx):)

toRaw :: [Identifier]
  -> [(Identifier, RVar)]
  -> ParseTree
  -> FreshMT (Except String) Raw
toRaw _ _ THole = return RHole

toRaw _ env (TNode v []) | Just v' <- lookup v env = return $ RVar v'

toRaw cenv env (TNode v args) | v `elem` cenv = do
  -- make sure args are not bound, construct a constant
  if not (all (null . fst) args) then
    throwError "Binders not allowed here."
  else
    RConst v <$> mapM (toRaw cenv env . snd) args

toRaw cenv env (TNode "Lam" [([x], b)]) = do
  v <- fresh (s2n x)
  RLam . bind v <$> toRaw cenv (pushVar x v env) b
toRaw cenv env (TApp t1 t2) = RApp <$> toRaw cenv env t1 <*> toRaw cenv env t2
toRaw cenv env (TNode "Pi" [([], dom), ([x], cod)]) = do
  rdom <- toRaw cenv env dom
  v <- fresh (s2n x)
  rcod <- toRaw cenv (pushVar x v env) cod
  return $ RPi rdom (bind v rcod)

toRaw cenv env (TNode "pair" [([], p), ([], q)]) = RPair <$> toRaw cenv env p <*> toRaw cenv env q
toRaw cenv env (TNode "fst" [([], p)]) = RFst <$> toRaw cenv env p
toRaw cenv env (TNode "snd" [([], p)]) = RSnd <$> toRaw cenv env p
toRaw cenv env (TNode "Sigma" [([], dom), ([x], cod)]) = do
  rdom <- toRaw cenv env dom
  v <- fresh (s2n x)
  rcod <- toRaw cenv (pushVar x v env) cod
  return $ RSigma rdom (bind v rcod)

toRaw _ _ (TNode "zero" []) = return RZero
toRaw cenv env (TNode "suc" [([], p)]) = RSuc <$> toRaw cenv env p
toRaw _ _ (TInt k) = return $ nTimes k RSuc RZero
toRaw _ _ (TNode "Nat" []) = return RNat
toRaw cenv env (TNode "elim" [([y], m), ([], z), ([x, r], s), ([], n)]) = do
  vy <- fresh (s2n y)
  rm <- toRaw cenv (pushVar y vy env) m
  rz <- toRaw cenv env z
  vx <- fresh (s2n x)
  vr <- fresh (s2n r)
  rs <- toRaw cenv (pushVar x vx $ pushVar r vr env) s
  rn <- toRaw cenv env n
  return $ RNatElim (bind vy rm) rz (bind (vx, vr) rs) rn

toRaw _ _ (TNode "U" []) = return RUniverse

toRaw cenv env (TNode "the" [([], p), ([], q)]) = RThe <$> toRaw cenv env p <*> toRaw cenv env q

toRaw _ _ (TNode v _) = throwError $ "Unrecognized identifier: " ++ v

{-
postulate
  x : A ; y : B ⊢ c : C

define
  x : A ; y : B ⊢ c : C
    = E

eval E'
-}

type ParseJudgment = ([(Identifier, ParseTree)], Identifier, ParseTree)
data RawJudgment
  = Judge Raw (Maybe Raw)
  | Hypo Raw (Bind RVar RawJudgment)
  deriving (Generic, Show)
instance Alpha RawJudgment
instance Subst Raw RawJudgment

parseJudgment :: Parser ParseJudgment
parseJudgment = do
  scopes <- do
    args <- ((,) <$> some pBinder <*> (char ':' *> pRaw)) `sepBy` char ';'
    return [ (v, rty) | (vs, rty) <- args , v <- vs ]
  (symbol "|-" <|> symbol "⊢") <?> "turnstile"
  c <- pIdent
  char ':'
  cty <- pRaw
  return (scopes, c, cty)

parseDef :: Parser (ParseJudgment, ParseTree)
parseDef = do
  symbol "define"
  j <- parseJudgment
  char '='
  expr <- pRaw
  return (j, expr)

parsePostulate :: Parser ParseJudgment
parsePostulate = do
  symbol "postulate"
  parseJudgment

parseTop :: [Identifier] -> Parser (RawJudgment, Identifier)
parseTop cenv = do
    ((pJ, name, pty), ptm) <- parseDef
    case runExcept $ runFreshMT $ go pJ [] pty (Just ptm) of
      Right j -> return (j, name)
      Left s -> fail s
  <|> do
    (pJ, name, pty) <- parsePostulate
    case runExcept $ runFreshMT $ go pJ [] pty Nothing of
      Right j -> return (j, name)
      Left s -> fail s
  where
    go :: [(Identifier, ParseTree)]
      -> [(Identifier, RVar)]
      -> ParseTree -> Maybe ParseTree
      -> FreshMT (Except String) RawJudgment
    go [] scope pty mtm = do
      rty <- toRaw cenv scope pty
      rtm <- case mtm of
        Nothing -> return Nothing
        Just ptm -> Just <$> toRaw cenv scope ptm
      return $ Judge rty rtm
    go ((x,xpty):cs) scope pty mtm = do
      xrty <- toRaw cenv scope xpty
      v <- fresh $ s2n x
      res <- go cs (pushVar x v scope) pty mtm
      return $ Hypo xrty (bind v res)

parseFile :: Parser ([(RawJudgment, Identifier)], Raw)
parseFile = spaceEater *> go [] <* eof
  where
    go cenv = do
        symbol "eval"
        result <- runExcept . runFreshMT . toRaw cenv [] <$> pRaw
        case result of
          Right rtm -> return ([], rtm)
          Left err -> fail err
      <|> do
        (j, x) <- parseTop cenv
        (js, rtm) <- go (x:cenv)
        return ((j,x):js, rtm)

parseString :: String -> IO ([(RawJudgment, Identifier)], Raw)
parseString src =
  case parse parseFile "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t -> return t
