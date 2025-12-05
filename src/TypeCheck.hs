module TypeCheck (
  TyckM, execTyckM, evalTyckM, emptyContext,
  check, checkTy, infer, conv, convTy,
  zonk, zonkTy, processFile
) where
import Control.Monad (unless)
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import Unbound.Generics.LocallyNameless hiding (close)
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.IntSet as IS
import Data.Coerce (coerce)
import Debug.Trace (trace)

import qualified Raw as R
import Raw (Raw)
import Syntax
import qualified NbE as V
import NbE (Val, TyVal, Spine)
import NbE hiding (Val(..), TyVal(..), Spine(..))
import Utils
import Cofibration

-- Prepare some primitive operations
newVar :: Tyck m => R.Var -> Var -> Thunk TyVal -> m a -> m a
newVar vraw var ty = bindVar [(var, V.Var var)] . local \ctx -> ctx {
  rvars = (vraw, ty) : rvars ctx
}

freshAnonMeta :: Tyck m => m (MetaVar Term)
freshAnonMeta = do
  vs <- asks rvars
  st <- get
  let (ix, g) = newNode $ graph (metas st)
  put st { metas = (metas st) { graph = g } }
  return $ MetaVar
    ("?" ++ show ix) ix (map (Var . coerce . fst) vs)

insertTermSol :: Tyck m => Int -> Closure [Var] Term -> m ()
insertTermSol i s = trace (show i ++ " == " ++ show s) do
  st <- get
  let newGraph = insertNode (graph (metas st)) i (IS.toList $ getClosureMetas getMetas s)
  trace (show newGraph) if hasCycle newGraph then
    throwError "Occurs check"
  else
    put st {
      metas = (metas st) {
        termSol = IM.insertWith (error "Repeated solution")
          i s (termSol (metas st)),
        graph = newGraph
      }
    }

insertTypeSol :: Tyck m => Int -> Closure [Var] Type -> m ()
insertTypeSol i s = trace (show i ++ " == " ++ show s) do
  st <- get
  let newGraph = insertNode (graph (metas st)) i (IS.toList $ getClosureMetas getTyMetas s)
  trace (show newGraph) if hasCycle newGraph then
    throwError "Occurs check"
  else
    put st {
      metas = (metas st) {
        typeSol = IM.insertWith (error "Repeated solution")
          i s (typeSol (metas st)),
        graph = newGraph
      }
    }

closeM :: (Tyck m, Alpha a) => a -> Thunk Val -> m (Closure a Term)
closeM a th = do
  t <- force th
  tm <- reify t
  closeB (bind a tm)

closeTyM :: (Tyck m, Alpha a) => a -> Thunk TyVal -> m (Closure a Type)
closeTyM a th = do
  t <- forceTy th
  ty <- reifyTy  t
  closeB (bind a ty)

---- Bidirectional type checking ----
check :: Tyck m => Raw -> TyVal -> m Term
check R.Hole _ =
  MVar <$> freshAnonMeta

check (R.Lam f) (V.Pi thdom cod) = do
  (x, t) <- unbind f
  let x' = coerce x :: Var
  ty <- cod $$: \y -> [(y, V.Var x')]
  t' <- newVar x x' thdom $ check t ty
  return $ Lam $ bind x' t'

check (R.Pair s1 s2) (V.Sigma th1 t2) = do
  t1 <- forceTy th1
  s1' <- check s1 t1
  v1 <- eval s1'
  t2' <- t2 $$: \y -> [(y, v1)]
  s2' <- check s2 t2'
  return $ Pair s1' s2'

-- Do we need these?
check R.Zero V.Nat = return Zero
check (R.Suc t) V.Nat = Suc <$> check t V.Nat

check (R.InCof p _) (V.Ext _ q _)
  | p /= q = throwError "Cofibration mismatch"
  | otherwise = error "todo"

check tm ty = trace ("Trying to infer the type of "++show tm) do
  (tm', thty') <- infer tm
  trace ("Infer success: " ++ show tm') do
    unify' [Right (Thunk ty, thty')]
    return tm'

checkTy :: Tyck m => Raw -> m Type
checkTy (R.Pi rdom rc) = do
  dom <- checkTy rdom
  vdom <- evalTy dom
  (x, rcod) <- unbind rc
  let x' = coerce x :: Var
  cod <- newVar x x' (Thunk vdom) $ checkTy rcod
  return (Pi dom (bind x' cod)) -- ?
checkTy (R.Sigma rty1 rc) = do
  ty1 <- checkTy rty1
  vty1 <- evalTy ty1
  (x, rty2) <- unbind rc
  let x' = coerce x :: Var
  ty2 <- newVar x x' (Thunk vty1) $ checkTy rty2
  return (Sigma ty1 (bind x' ty2))
checkTy R.Nat = return Nat
checkTy R.Universe = return Universe
checkTy R.Hole = MTyVar <$> freshAnonMeta
checkTy rtm = El <$> check rtm V.Universe

data JudgmentResult a
  = JPostulate a
  | JDefinition Bool Cof a a
  deriving Functor
internalName :: String -> String
internalName n = "_internal_" ++ n

checkJudgment :: Tyck m =>
  Cof -> String -> R.Judgment -> m (JudgmentResult Entry)
checkJudgment _ _ (R.Postulate rty) = do
  ty <- checkTy rty
  return $ JPostulate $ Postulate ty
checkJudgment p name (R.Definition u rty rtm) = do
  ty <- checkTy rty
  vty <- evalTy ty
  tm <- bindCof p $ check rtm vty
  cof <- case unignore u of
    Opaque -> freshCof name p
    Controlled -> freshCof name p
    Transparent -> return p
  vs <- asks rvars
  return $ JDefinition (unignore u == Opaque) cof
    (Definition ty tm) -- the definition
    (Postulate (Ext ty cof (Con
      (Const (internalName name) (map (Var . coerce . fst) vs)))))

checkJudgment p name (R.Hypothesis rty bj) = do
  ty <- checkTy rty
  vty <- evalTy ty
  (x, j) <- unbind bj
  let x' = coerce x :: Var
  entry <- newVar x x' (Thunk vty) $ checkJudgment p name j
  return $ Hypothesis ty . bind x' <$> entry

infer :: Tyck m => Raw -> m (Term, Thunk TyVal)
infer R.Hole = do
  m <- freshAnonMeta
  mty <- freshAnonMeta
  vty <- evalTy (MTyVar mty)
  return (MVar m, Thunk vty)

infer (R.Con' name args) = do
  n <- gets (M.lookup name . decls)
  case n of
    Nothing -> error "Impossible: constant not found"
    Just (unfold, entry) -> do
      good <- isTrue unfold
      unless good $ throwError "Impossible: Cofibration mismatch"
      (targs, ty) <- go entry args
      return (Con (Const name targs), ty)
  where
    go :: Tyck m => Entry -> [Raw] -> m ([Term], Thunk TyVal)
    -- check arguments
    go (Hypothesis ty bentry) (rtm:rtms) = do
      vty <- evalTy ty
      tm <- check rtm vty
      (x, entry) <- unbind bentry
      vtm <- eval tm
      (tms, thty) <- bindVar [(x, vtm)] $ go entry rtms
      return (tm:tms, thty)
    -- substitute to get type
    go (Definition ty _) [] = do
      vty <- evalTy ty
      return ([], Thunk vty)
    go (Postulate ty) [] = do
      vty <- evalTy ty
      return ([], Thunk vty)
    go _ _ = throwError "Wrong number of arguments"

infer (R.Con name args) = do
  c <- gets (M.lookup name . symbs)
  case c of
    -- this is a true postulate
    Nothing -> infer (R.Con' name args)
    -- this is a definition
    Just (_, cof) -> trace ("Inferring user constant " ++ name) $ infer
      (R.OutCof cof
        (R.Con' (internalName name) args)
        (R.Con' name args))

infer (R.The rty rtm) = do
  ty <- checkTy rty
  vty <- evalTy ty
  tm <- check rtm vty
  return (The ty tm, Thunk vty)

infer (R.Var x) = do
  vs <- asks rvars
  case lookup x vs of
    Just y -> return (Var (coerce x), y)
    Nothing -> throwError $ "Variable out of scope: " ++ show x

infer (R.App rfun rarg) = do
  (fun, thty) <- infer rfun
  ty <- forceTy thty
  (dom, cod) <- case ty of
    V.Pi thdom cod -> do
      dom <- forceTy thdom
      return (dom, cod)
    _ -> expectPiSigma True ty
  arg <- check rarg dom
  varg <- eval arg
  vcod <- cod $$: \y -> [(y, varg)]
  return (App fun arg, Thunk vcod)
infer (R.Lam f) = do
  mdom <- freshAnonMeta
  vdom <- Thunk <$> evalTy (MTyVar mdom)
  (x, rt) <- unbind f
  let x' = coerce x :: Var
  (t, vcod) <- newVar x x' vdom $ infer rt
  cod <- closeTyM x' vcod
  return (Lam $ bind x' t, Thunk $ V.Pi vdom cod)
infer rty@R.Pi {} = do
  ty <- checkTy rty
  return (Quote ty, Thunk V.Universe)

infer (R.Fst r) = do
  (t, th) <- infer r
  ty <- forceTy th
  case ty of
    V.Sigma ty1 _ -> return (Fst t, ty1)
    _ -> do
      (ty1, _) <- expectPiSigma False ty
      return (Fst t, Thunk ty1)
infer (R.Snd r) = do
  (t, th) <- infer r
  ty <- forceTy th
  ty2 <- case ty of
    V.Sigma _ ty2 -> return ty2
    _ -> snd <$> expectPiSigma False ty
  varg <- eval (Fst t)
  sty2 <- ty2 $$: \y -> [(y, varg)]
  return (Snd t, Thunk sty2)
infer (R.Pair t1 t2) = do
  mt1 <- freshAnonMeta
  ty1 <- evalTy (MTyVar mt1)
  z <- fresh (s2n "z")
  bt2 <- bindVar [(z, V.Var z)] do
    mt2 <- freshAnonMeta
    evalTy (MTyVar mt2)
  ty2 <- closeTyM z (Thunk bt2)
  let ty = V.Sigma (Thunk ty1) ty2
  t <- check (R.Pair t1 t2) ty
  return (t, Thunk ty)
infer rty@R.Sigma {} = do
  ty <- checkTy rty
  return (Quote ty, Thunk V.Universe)

infer R.Zero = return (Zero, Thunk V.Nat)
infer (R.Suc r) = do
  t <- check r V.Nat
  return (Suc t, Thunk V.Nat)
infer (R.NatElim rmc rz rsc rarg) = do
  -- check argument
  arg <- check rarg V.Nat
  -- check motive
  (n, rm) <- unbind rmc
  let n' = coerce n :: Var
  tym <- newVar n n' (Thunk V.Nat) $ checkTy rm
  -- check zero argument
  tym_z <- bindVar [(n', V.Zero)] $ evalTy tym
  tz <- check rz tym_z
  -- check suc argument
  ((x, r), rs) <- unbind rsc
  let x' = coerce x :: Var
  let r' = coerce r :: Var
  tyr_s <- bindVar [(n', V.Var x')] $ evalTy tym
  tym_s <- bindVar [(n', V.Suc 1 (Thunk (V.Var x')))] $ evalTy tym
  ts <- newVar x x' (Thunk V.Nat)
    $ newVar r r' (Thunk tyr_s)
    $ check rs tym_s
  -- evaluate the type
  varg <- eval arg
  ty <- bindVar [(n', varg)] $ evalTy tym
  return (NatElim (bind n' tym) tz (bind (x', r') ts) arg, Thunk ty)
infer R.Nat = return (Quote Nat, Thunk V.Universe)
  -- since it's just one step we can inline it

infer (R.InCof _ _) = error "todo"

infer t@(R.OutCof p rres rterm) = trace ("Inferring " ++ show t) do
  (tres, vtyres) <- bindCof p $ infer rres
  cres <- closeB (bind () tres)
  mty <- freshAnonMeta
  vty <- Thunk <$> evalTy (MTyVar mty)
  term <- check rterm (V.Ext vty p cres)
  bindCof p $ unify' [Right (vtyres, vty)]
  return (OutCof p tres term, vty)

infer R.Universe = return (Quote Universe, Thunk V.Universe)
  -- todo add universe constraint (i.e. don't inline this)

expectPiSigma :: Tyck m => Bool -> TyVal -> m (TyVal, Closure Var Type)
expectPiSigma b ty = do
  mdom <- freshAnonMeta
  dom <- evalTy (MTyVar mdom)
  z <- fresh (s2n "z")
  bcod <- bindVar [(z, V.Var z)] do
    mcod <- freshAnonMeta
    evalTy (MTyVar mcod)
  cod <- closeTyM z (Thunk bcod)
  unify' [Right (Thunk ty,
    Thunk $ (if b then V.Pi else V.Sigma) (Thunk dom) cod)]
  return (dom, cod)

----- Unification algorithm -----
-- the `conv` family of functions output Nothing when it should be postponed,
-- error when it is definitely not true, and outputs a list of equations otherwise

convSp :: Tyck m => [Spine] -> [Spine] -> m [Equation]
convSp [] [] = return []
convSp (sp0:sp) (sp0':sp') = (++) <$> convSp sp sp' <*> case (sp0, sp0') of
  (V.App th, V.App th') -> withCtx [Left (th, th')]
  (V.Fst, V.Fst) -> return []
  (V.Snd, V.Snd) -> return []
  (V.NatElim _ z s, V.NatElim _ z' s') -> do
    -- since we are assuming they have the same type,
    -- conversion should not depend on the motive
    vz <- z $$ \() -> []
    vz' <- z' $$ \() -> []

    ((m, k), vs) <- s $$+ \(m, k) -> [(m, V.Var m), (k, V.Var k)]
    vs' <- s' $$ \(m', k') -> [(m', V.Var m), (k', V.Var k)]

    withCtx [Left (Thunk vz, Thunk vz'), Left (Thunk vs, Thunk vs')]
  (V.OutCof _ _, V.OutCof _ _) -> return [] -- similar thing here
  p -> throwError $ "Not convertible: " ++ show p
convSp p q = throwError $ "Not convertible: " ++ show p ++ show q

conv :: Tyck m => Val -> Val -> m (Maybe [Equation])
-- We assume this has been forced.
conv (V.Rigid v sp _) (V.Rigid v' sp' _) =
  if v == v' then
    Just <$> convSp sp sp'
  else
    throwError $ "Not convertible: " ++ show v ++ " /= " ++ show v'
-- constants that don't unfold are also rigid
conv (V.Con (Const name arg) sp _) (V.Con (Const name' arg') sp' _) =
  if name /= name' then
    throwError $ "Not convertible: " ++ name ++ " /= " ++ name'
  else do
    eq_arg <- withCtx $ zipWith (curry Left) arg arg'
    sp_arg <- convSp sp sp'
    return $ Just (eq_arg ++ sp_arg)
-- rigid-flex and flex-rigid
conv (V.Flex (MetaVar _ mid _) _ _) (V.Flex (MetaVar _ mid' _) _ _)
  | mid == mid' = return Nothing -- todo deal with it properly
conv (V.Flex m sp _) v = do
  b <- solve m sp v
  if b then return (Just []) else return Nothing
conv v m@V.Flex {} = conv m v

conv (V.Lam f) (V.Lam g) = do
  -- We can use a fresh variable, but that loses the name information
  -- so we use this slighly cursed leaking implementation
  (x, s) <- f $$+ \x -> [(x, V.Var x)]
  t <- g $$ \y -> [(y, V.Var x)]
  s' <- force (Thunk s)
  t' <- force (Thunk t)
  conv s' t'
conv (V.Lam f) g = do
  (x, s) <- f $$+ \x -> [(x, V.Var x)]
  t <- vApp g (V.Var x)
  s' <- force (Thunk s)
  t' <- force (Thunk t)
  conv s' t'
conv g f@V.Lam {} = conv f g

conv (V.Pair ths1 tht1) (V.Pair ths2 tht2) =
  Just <$> withCtx [Left (ths1, ths2), Left (tht1, tht2)]
conv (V.Pair ths tht) m =
  Just <$> withCtx [Left (ths, Thunk (vFst m)), Left (tht, Thunk (vSnd m))]
conv m n@V.Pair {} = conv n m

conv V.Zero V.Zero = return (Just [])
conv (V.Suc n th) (V.Suc m th') =
  if n == m then do
    t <- force th
    t' <- force th'
    conv t t'
  else
    throwError $ show n ++ " /= " ++ show m

conv (V.InCof p1 th1) (V.InCof p2 th2) =
  if p1 == p2 then bindCof p1 do
    t1 <- force th1
    t2 <- force th2
    conv t1 t2
  else
    throwError $ show p1 ++ " /= " ++ show p2

conv (V.Quote th1) (V.Quote th2) = do
  ty1 <- forceTy th1
  ty2 <- forceTy th2
  convTy ty1 ty2
conv (V.Quote th) tm = do
  ty <- forceTy th
  convTy ty (V.vEl tm)
conv tm tm'@V.Quote {} = conv tm' tm

conv p q = throwError $ "Not convertible: " ++ show p ++ " /= " ++ show q

convTy :: Tyck m => TyVal -> TyVal -> m (Maybe [Equation])
convTy (V.MTyVar m _) t = do
  b <- solveTy m t
  if b then return (Just []) else return Nothing
convTy t t'@V.MTyVar {} = convTy t' t

convTy (V.Sigma ty c) (V.Sigma ty' c') = do
  (x, s) <- c $$:+ \x -> [(x, V.Var x)]
  t <- c' $$: \y -> [(y, V.Var x)]
  Just <$> withCtx [Right (ty, ty'), Right (Thunk s, Thunk t)]
convTy (V.Pi ty c) (V.Pi ty' c') -- small hack to reduce repeat
  = convTy (V.Sigma ty c) (V.Sigma ty' c')
convTy V.Nat V.Nat = return (Just [])
convTy (V.Ext ty p tm) (V.Ext ty' p' tm') =
  if p /= p' then
    throwError $ "Not convertible: " ++ show p ++ " /= " ++ show p'
  else do
    e <- asks env
    q <- asks cofEnv
    v <- tm $$? p
    v' <- tm' $$? p'
    return $ Just
      [(e, q, Right (ty, ty')),
      (e, p <> q, Left (Thunk v, Thunk v'))]
convTy V.Universe V.Universe = return (Just [])
convTy (V.El t1) (V.El t2) = conv t1 t2
-- This is needed because V.El is special
convTy (V.El m@(V.Flex {})) t = conv m (V.Quote (Thunk t))
convTy t (V.El m@(V.Flex {})) = conv m (V.Quote (Thunk t))
convTy p q = throwError $ "Not convertible: " ++ show p ++ " /= " ++ show q

-- Searches if the substitution and the spine constitutes
-- a linear set of variables, and if so adds the solution
solve :: Tyck m => MetaVar (Thunk Val) -> [Spine] -> Val -> m Bool
solve (MetaVar _ mid subs) sp v = do
  -- todo check that the cofibration environment is correct
  vsp <- mapM spine sp
  vsubs <- mapM force subs
  let vars' = sequence (map toVar vsubs ++ map (toVar =<<) vsp)
  case vars' of
    Nothing -> return False
    Just vars -> if allUnique vars then do
      -- todo this causes a tiny of rechecking
      sol <- closeM vars (Thunk v)
      insertTermSol mid sol
      return True
    else
      return False
  where
    spine :: Tyck m => Spine -> m (Maybe Val)
    spine (V.App s) = Just <$> force s
    spine _ = return Nothing

solveTy :: Tyck m => MetaVar (Thunk Val) -> TyVal -> m Bool
solveTy (MetaVar _ mid subs) v = do
  vsubs <- mapM force subs
  let rvars' = mapM toVar vsubs
  case rvars' of
    Nothing -> return False
    Just vars -> if allUnique vars then do
      -- todo this causes a tiny of rechecking
      sol <- closeTyM vars (Thunk v)
      insertTypeSol mid sol
      return True
    else
      return False


-- Attempt to solve the equation, which either postpones it or
-- splits into zero or more smaller equations, without recursively solving
-- (unless it's straightforward to do so)
attempt :: Tyck m => Equation -> m (Maybe [Equation])
attempt (e, c, Left (th1, th2)) = withContext e c do
  t1 <- force th1
  t2 <- force th2
  conv t1 t2
attempt (e, c, Right (th1, th2)) = withContext e c do
  t1 <- forceTy th1
  t2 <- forceTy th2
  convTy t1 t2

-- Adds the equations under current context
withCtx :: Tyck m => [a] -> m [(Env, Cof, a)]
withCtx eqs = do
  ctx <- ask
  return $ map (\eq -> (env ctx, cofEnv ctx, eq)) eqs

unify' :: Tyck m =>
  [Either (Thunk Val, Thunk Val) (Thunk TyVal, Thunk TyVal)] -> m ()
unify' eqs = unify =<< withCtx eqs

-- The postponing logic
unify :: Tyck m => [Equation] -> m ()
unify [] = return ()
unify (eq:eqs) = do
  result <- attempt eq
  case result of
    Just eqs' -> do
      st <- get
      put st {
        metas = (metas st) {
          equations = []
        } -- todo filter only the relevant ones
      }
      unify (eqs' ++ eqs ++ equations (metas st))
    Nothing -> do
      -- ? use snoc list
      modify \st -> st {
        metas = (metas st) { equations = eq : equations (metas st) }
      }
      unify eqs

-- Substitute in the metas given a term, without normalizing first
zonkMeta :: Tyck m => Closure [Var] Term -> [Term] -> m Term
zonkMeta sol subs = do
  vsubs <- mapM eval subs
  val <- sol $$ (`zip'` vsubs)
  zonk =<< reify val

zonkMetaTy :: Tyck m => Closure [Var] Type -> [Term] -> m Type
zonkMetaTy sol subs = do
  vsubs <- mapM eval subs
  val <- sol $$: (`zip'` vsubs)
  zonkTy =<< reifyTy val

zonk :: Tyck m => Term -> m Term
zonk (MVar (MetaVar name mid subs)) = do
  sol <- gets (IM.lookup mid . termSol . metas)
  case sol of
    Just s -> zonkMeta s subs
    Nothing -> MVar . MetaVar name mid <$> mapM zonk subs
zonk (Var v) = return $ Var v
zonk (Con (Const name subs)) = Con . Const name <$> mapM zonk subs
zonk (Lam f) = do
  (x, f') <- unbind f
  zf <- bindVar [(x, V.Var x)] $ zonk f'
  return $ Lam $ bind x zf
zonk (App s t) = App <$> zonk s <*> zonk t
zonk (Pair s t) = Pair <$> zonk s <*> zonk t
zonk (Fst s) = Fst <$> zonk s
zonk (Snd s) = Snd <$> zonk s
zonk Zero = return Zero
zonk (Suc s) = Suc <$> zonk s
zonk (NatElim m z s c) = do
  (x, m') <- unbind m
  zm <- bindVar [(x, V.Var x)] $ zonkTy m'
  zz <- zonk z
  ((n, r), s') <- unbind s
  zs <- bindVar [(n, V.Var n), (r, V.Var r)] $ zonk s'
  zc <- zonk c
  return $ NatElim (bind x zm) zz (bind (n, r) zs) zc
zonk (InCof p tm) = InCof p <$> zonk tm
zonk (OutCof p t1 t2) = OutCof p <$> zonk t1 <*> zonk t2
zonk (Quote ty) = Quote <$> zonkTy ty
zonk (The ty tm) = The <$> zonkTy ty <*> zonk tm

zonkTy :: Tyck m => Type -> m Type
zonkTy m@(MTyVar (MetaVar _ mid subs)) = do
  sol <- gets (IM.lookup mid . typeSol . metas)
  case sol of
    Just s -> zonkMetaTy s subs
    Nothing -> return m
zonkTy (Sigma ty f) = do
  zty <- zonkTy ty
  (x, f') <- unbind f
  zf <- bindVar [(x, V.Var x)] $ zonkTy f'
  return $ Sigma zty $ bind x zf
zonkTy (Pi ty f) = do
  zty <- zonkTy ty
  (x, f') <- unbind f
  zf <- bindVar [(x, V.Var x)] $ zonkTy f'
  return $ Pi zty $ bind x zf
zonkTy Nat = return Nat
zonkTy (Ext ty p tm) = (`Ext` p) <$> zonkTy ty <*> zonk tm
zonkTy Universe = return Universe
zonkTy (El tm) = El <$> zonk tm

---- Processing whole files ----
calculateUnfolds :: Tyck m => [String] -> m Cof
calculateUnfolds ns = do
  e <- gets symbs
  return $ mconcat (map (go e) ns)
  where
    go e v = case M.lookup v e of
      Just (False, c) -> c
      Just (True, _) -> error $ "calculateUnfolds: cannot unfold opaque " ++ v
      Nothing -> error $ "calculateUnfolds: unknown constant " ++ v

processFile :: Tyck m => [R.TopLevel] -> Raw -> m (Type, Term, Term)
processFile [] expr = trace ("Evaluating: " ++ show expr) do
  (tm, vty) <- infer expr
  vtm <- eval tm
  ztm <- zonk tm
  -- You probably need to force whenever metas could be solved
  ty <- reifyTy =<< forceTy vty
  ntm <- reify =<< force (Thunk vtm)
  return (ty, ztm, ntm)
processFile (R.TopLevel rj unfolding name:decl) expr =
  trace ("Defining " ++ name) do
  -- calculate the unfoldings and work locally
  cof <- calculateUnfolds unfolding
  result <- checkJudgment cof name rj
  case result of
    JPostulate j -> modify \st -> st {
      -- todo the cof assumption here doesn't look necessary
      decls = M.insert name (cof, j) (decls st)
    }
    JDefinition opaque newcof def con -> modify \st -> st {
      decls =
        M.insert name (mempty, con) $
        M.insert (internalName name) (cof, def) $
        decls st,
      symbs = M.insert name (opaque, newcof) (symbs st)
    }
  processFile decl expr
  -- todo freeze metas

----- Example monad to use functions ----
newtype TyckM a = TyckM {
  runTyckM :: StateT Decls (ReaderT Context (ExceptT String FreshM)) a
} deriving (
  Functor, Applicative, Monad,
  Fresh, MonadError String, MonadReader Context, MonadState Decls)
instance Tyck TyckM

execTyckM :: TyckM a -> Either String (a, Decls)
execTyckM m = runFreshM $
  runExceptT $
  runReaderT (runStateT (runTyckM m) emptyDecls)
    emptyContext

evalTyckM :: TyckM a -> Either String a
evalTyckM m = fst <$> execTyckM m
