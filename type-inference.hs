{-# LANGUAGE FlexibleContexts #-}
import Data.List (union,group) -- нужно для проверки, не убирайте!
import Data.Monoid
import Data.Semigroup
import Control.Monad.Except
import Control.Monad.State



infixl 4 :@
infixr 3 :->

type Symb = String 

-- Терм
data Expr = Var Symb 
          | Expr :@ Expr
          | Lam Symb Expr
  deriving (Eq,Show)

-- Тип
data Type = TVar Symb 
          | Type :-> Type
  deriving (Eq,Show)

-- Контекст
newtype Env = Env [(Symb,Type)]
  deriving (Eq,Show)

-- Подстановка
newtype SubsTy = SubsTy [(Symb, Type)]
  deriving (Eq,Show)


freeVars :: Expr -> [Symb] 
freeVars (Var ch) = [ch] 
freeVars (e1 :@ e2) = freeVars e1 ++ freeVars e2
freeVars (Lam ch e) = filter (/= ch) (freeVars e)

freeTVars :: Type -> [Symb]
freeTVars (TVar t) = [t] 
freeTVars (t1 :-> t2) = freeTVars t1 ++ freeTVars t2

freeTVarsEnv :: Env -> [Symb]
freeTVarsEnv (Env env) = foldr (\(e, t) s -> s ++ freeTVars t) [] env

extendEnv :: Env -> Symb -> Type -> Env
extendEnv (Env env) e t = Env $ (e, t) : env

appEnv :: (MonadError String m) => Env -> Symb -> m Type
appEnv (Env []) v = throwError $ "There is no variable " ++ show v ++ " in the enviroment."
appEnv (Env ((s, t):xs)) v | s == v    = return t
                           | otherwise = appEnv (Env xs) v

appSubsTy :: SubsTy -> Type -> Type
appSubsTy (SubsTy [])         (TVar v) = TVar v
appSubsTy (SubsTy ((s, t):xs))(TVar v) | s == v    = t 
                                       | otherwise = appSubsTy (SubsTy xs) (TVar v)
appSubsTy sbs (t1 :-> t2) = appSubsTy sbs t1 :-> appSubsTy sbs t2

appSubsEnv :: SubsTy -> Env -> Env
appSubsEnv sbs (Env []) = (Env []) 
appSubsEnv sbs (Env ((s, t):xs)) = Env $ (s, appSubsTy sbs t) : xs 

composeSubsTy :: SubsTy -> SubsTy -> SubsTy
composeSubsTy (SubsTy s1) (SubsTy s2) = SubsTy $ map fun (s1 ++ s2) where
    fun (s, t) = (s, appSubsTy (SubsTy s1) $ appSubsTy (SubsTy s2) $ TVar s)

instance Semigroup SubsTy where
    (<>) = composeSubsTy
instance Monoid SubsTy where
    mempty = SubsTy []
    mappend = composeSubsTy

unify :: MonadError String m => Type -> Type -> m SubsTy
unify (TVar a) (TVar b) | a == b = return $ SubsTy []
unify (TVar a) t | filter (== a) (freeTVars t) /= [] = throwError $ "Can't unify " ++ show (TVar a) ++ " with " ++ show t ++ "!"
unify (TVar a) t | otherwise                         = return $ SubsTy [(a, t)]
unify t (TVar b) = unify (TVar b) t
unify (a1 :-> a2) (b1 :-> b2) = do
    u2 <- unify a2 b2
    let a1' = appSubsTy u2 a1
    let b1' = appSubsTy u2 b1
    u1 <- unify a1' b1'
    return $ u1 `mappend` u2


equations ::  MonadError String m => Env -> Expr -> Type -> m [(Type,Type)]
equations env e t = evalState (equations' env e t) "d"

equations' :: MonadError String m => Env -> Expr -> Type -> State String (m [(Type,Type)])
equations' env (Var a) t = do
    return $ do
        t2 <- appEnv env a
        return $ [(t, t2)]

equations' env (m :@ n) t = do
    newv <- get
    modify ('\'' :)
    eq1 <- equations' env m ((TVar newv) :-> t)
    eq2 <- equations' env n (TVar newv)
    return $ do
         l1 <- eq1
         l2 <- eq2
         return $ l1 ++ l2

equations' env (Lam x m) t = do
    newv1 <- get
    modify ('\'' :)
    newv2 <- get
    modify ('\'' :)
    let env' = extendEnv env x (TVar newv1)
    eq1 <- equations' env' m (TVar newv2)
    return $ do
         l1 <- eq1
         return $ l1 ++ [((TVar newv1) :-> (TVar newv2), t)]



principlePair :: (MonadError String m) =>  Expr -> m (Env,Type)
principlePair e = do
    let fv = freeVars e
    let g0 = Env $ zip fv (map TVar fv)
    let t0 = TVar "t0"
    es <- equations g0 e t0
    let t1 = foldr1 (:->) (fst $ unzip es) 
    let t2 = foldr1 (:->) (snd $ unzip es) 
    sbst <- unify t1 t2
    return $ (appSubsEnv sbst g0, appSubsTy sbst t0)
