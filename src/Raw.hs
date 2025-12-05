{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Raw (
  Var, Raw (..), Judgment (..), TopLevel (..),
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
type Var = Name Raw
data Raw
  = Var Var | Con Identifier [Raw]
  | Lam (Bind Var Raw) | App Raw Raw | Pi Raw (Bind Var Raw)
  | Pair Raw Raw | Fst Raw | Snd Raw | Sigma Raw (Bind Var Raw)
  | Zero | Suc Raw
  | NatElim
    {- motive -} (Bind Var Raw)
    {- zero -} Raw
    {- suc -} (Bind (Var, Var) Raw)
    {- arg -} Raw
  | Nat
  | Universe -- implicit Coquand universe
  | The Raw Raw
  | Hole
  deriving (Generic, Show)

instance Alpha Raw

instance Subst Raw Raw where
  isvar (Var x) = Just (SubstName x)
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
  guard $ notElem (x0:x)
    ["define", "opaque", "abbrev", "unfolding", "postulate", "eval"] -- keywords
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
  -> [(Identifier, Var)]
  -> ParseTree
  -> FreshMT (Except String) Raw
toRaw _ _ THole = return Hole

toRaw _ env (TNode v []) | Just v' <- lookup v env = return $ Var v'

toRaw cenv env (TNode v args) | v `elem` cenv = do
  -- make sure args are not bound, construct a constant
  if not (all (null . fst) args) then
    throwError "Binders not allowed here."
  else
    Con v <$> mapM (toRaw cenv env . snd) args

toRaw cenv env (TNode "Lam" [([x], b)]) = do
  v <- fresh (s2n x)
  Lam . bind v <$> toRaw cenv (pushVar x v env) b
toRaw cenv env (TApp t1 t2) = App <$> toRaw cenv env t1 <*> toRaw cenv env t2
toRaw cenv env (TNode "Pi" [([], dom), ([x], cod)]) = do
  rdom <- toRaw cenv env dom
  v <- fresh (s2n x)
  rcod <- toRaw cenv (pushVar x v env) cod
  return $ Pi rdom (bind v rcod)

toRaw cenv env (TNode "pair" [([], p), ([], q)]) = Pair <$> toRaw cenv env p <*> toRaw cenv env q
toRaw cenv env (TNode "fst" [([], p)]) = Fst <$> toRaw cenv env p
toRaw cenv env (TNode "snd" [([], p)]) = Snd <$> toRaw cenv env p
toRaw cenv env (TNode "Sigma" [([], dom), ([x], cod)]) = do
  rdom <- toRaw cenv env dom
  v <- fresh (s2n x)
  rcod <- toRaw cenv (pushVar x v env) cod
  return $ Sigma rdom (bind v rcod)

toRaw _ _ (TNode "zero" []) = return Zero
toRaw cenv env (TNode "suc" [([], p)]) = Suc <$> toRaw cenv env p
toRaw _ _ (TInt k) = return $ nTimes k Suc Zero
toRaw _ _ (TNode "Nat" []) = return Nat
toRaw cenv env (TNode "elim" [([y], m), ([], z), ([x, r], s), ([], n)]) = do
  vy <- fresh (s2n y)
  rm <- toRaw cenv (pushVar y vy env) m
  rz <- toRaw cenv env z
  vx <- fresh (s2n x)
  vr <- fresh (s2n r)
  rs <- toRaw cenv (pushVar x vx $ pushVar r vr env) s
  rn <- toRaw cenv env n
  return $ NatElim (bind vy rm) rz (bind (vx, vr) rs) rn

toRaw _ _ (TNode "U" []) = return Universe

toRaw cenv env (TNode "the" [([], p), ([], q)]) = The <$> toRaw cenv env p <*> toRaw cenv env q

toRaw _ _ (TNode v _) = throwError $ "Unrecognized identifier: " ++ v

{-
postulate
  x : A ; y : B ⊢ c : C

define unfolding {p, q}
  x : A ; y : B ⊢ c : C
    = E

eval E'
-}

data ParseJudgment = ParseJudgment {
  unfoldingP :: [Identifier],
  argP :: [(Identifier, ParseTree)],
  nameP :: Identifier,
  typeP :: ParseTree
}
data Judgment
  = Postulate Raw
  | Definition (Ignore Unfolding) Raw Raw
  | Hypothesis Raw (Bind Var Judgment)
  deriving (Generic, Show)
instance Alpha Judgment
instance Subst Raw Judgment

parseUnfolding :: Parser [Identifier]
parseUnfolding = do
  symbol "unfolding"
  char '{'
  r <- pIdent `sepBy` char ','
  char '}'
  return r

parseJudgment :: Parser ParseJudgment
parseJudgment = do
  cs <- parseUnfolding <|> return []
  scopes <- do
    args <- ((,) <$> some pBinder <*> (char ':' *> pRaw)) `sepBy` char ';'
    return [ (v, rty) | (vs, rty) <- args , v <- vs ]
  (symbol "|-" <|> symbol "⊢") <?> "turnstile"
  c <- pIdent
  char ':'
  ParseJudgment cs scopes c <$> pRaw

parseDef :: Parser (Unfolding, ParseJudgment, ParseTree)
parseDef = do
  u <-
    (Controlled <$ symbol "define") <|>
    (Opaque <$ symbol "opaque") <|>
    (Transparent <$ symbol "abbrev")
  j <- parseJudgment
  char '='
  expr <- pRaw
  return (u, j, expr)

parsePostulate :: Parser ParseJudgment
parsePostulate = do
  symbol "postulate"
  parseJudgment

data TopLevel = TopLevel {
  judgment :: Judgment,
  unfolding :: [Identifier],
  name :: Identifier
}

parseTop :: [Identifier] -> Parser TopLevel
parseTop cenv = do
    (u, pJ, ptm) <- parseDef
    guard (all (`elem` cenv) $ unfoldingP pJ)
    case runExcept $ runFreshMT $
      go (argP pJ) [] (typeP pJ) (Just (u, ptm)) of
      Right j -> return $ TopLevel j (unfoldingP pJ) (nameP pJ)
      Left s -> fail s
  <|> do
    pJ <- parsePostulate
    guard (all (`elem` cenv) $ unfoldingP pJ)
    case runExcept $ runFreshMT $
      go (argP pJ) [] (typeP pJ) Nothing of
      Right j -> return $ TopLevel j (unfoldingP pJ) (nameP pJ)
      Left s -> fail s
  where
    go :: [(Identifier, ParseTree)]
      -> [(Identifier, Var)]
      -> ParseTree -> Maybe (Unfolding, ParseTree)
      -> FreshMT (Except String) Judgment
    go [] scope pty mtm = do
      rty <- toRaw cenv scope pty
      case mtm of
        Nothing -> return $ Postulate rty
        Just (u, ptm) -> Definition (ignore u) rty <$> toRaw cenv scope ptm
    go ((x,xpty):cs) scope pty mtm = do
      xrty <- toRaw cenv scope xpty
      v <- fresh $ s2n x
      res <- go cs (pushVar x v scope) pty mtm
      return $ Hypothesis xrty (bind v res)

parseFile :: Parser ([TopLevel], Raw)
parseFile = spaceEater *> go [] <* eof
  where
    go cenv = do
        symbol "eval"
        result <- runExcept . runFreshMT . toRaw cenv [] <$> pRaw
        case result of
          Right rtm -> return ([], rtm)
          Left err -> fail err
      <|> do
        top <- parseTop cenv
        (js, rtm) <- go (name top:cenv)
        return (top:js, rtm)

parseString :: String -> IO ([TopLevel], Raw)
parseString src =
  case parse parseFile "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t -> return t
