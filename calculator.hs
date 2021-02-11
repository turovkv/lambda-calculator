import Data.Set (Set)
import qualified Data.Set as Set

type Symb = String 
infixl 2 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)

freeVarsSet :: Expr -> Set Symb
freeVarsSet (Var ch) = Set.singleton ch 
freeVarsSet (e1 :@ e2) = Set.union (freeVarsSet e1) (freeVarsSet e2)
freeVarsSet (Lam ch e) = Set.delete ch (freeVarsSet e)

subst :: Symb -> Expr -> Expr -> Expr
subst v n m = subst' v n m (freeVarsSet n) 

subst' :: Symb -> Expr -> Expr -> Set Symb -> Expr
subst' v n (Var ch)   s | ch == v   = n
                        | otherwise = Var ch


subst' v n (e1 :@ e2) s = (subst' v n e1 s) :@ (subst' v n e2 s)

subst' v n (Lam ch e) s | v == ch               = Lam ch e
subst' v n (Lam ch e) s | not (Set.member ch s) = Lam ch (subst' v n e s)
subst' v n (Lam ch e) s | otherwise             = Lam ch_new (subst' v n (rename e) s) where
    rnm x = if x == ch then ch_new else x
    rename (Var ch') = Var (rnm ch')
    rename (e1' :@ e2') = (rename e1') :@ (rename e2')
    rename (Lam x e') = (Lam (rnm x) (rename e'))

    ch_new = makeunique ch (freeVarsSet e) s
    makeunique x st1 st2 | (Set.member x st1) || (Set.member x st2) = makeunique ('\'' : x)  st1 st2
                         | otherwise                                = x


infixl 1 `alphaEq`
infixl 1 `betaEq`


alphaEq :: Expr -> Expr -> Bool
alphaEq e1 e2 | freeVarsSet e1 /= freeVarsSet e2 = False
alphaEq (Var ch1) (Var ch2)    = ch1 == ch2
alphaEq (a1 :@ b1) (a2 :@ b2)  = (alphaEq a1 a2) && (alphaEq b1 b2)
alphaEq (Lam x1 e1) (Lam x2 e2)= alphaEq e1 (subst x2 (Var x1) e2)
alphaEq _ _ = False

reduceOnce :: Expr -> Maybe Expr
reduceOnce ((Lam x1 e1) :@ e2) = do
      return $ subst x1 e2 e1 
reduceOnce (Lam x1 e1) = do
      e' <- reduceOnce e1
      return $ Lam x1 e'
reduceOnce (e1 :@ e2) = res where
      kek (Just e') _        = Just $ e' :@ e2
      kek Nothing  (Just e') = Just $ e1 :@ e'
      kek Nothing  Nothing  = Nothing
      res = kek (reduceOnce e1) (reduceOnce e2)

reduceOnce (Var ch)    = Nothing

nf :: Expr -> Expr 
nf e = case reduceOnce e of
          Just e' -> nf e'
          Nothing -> e

betaEq :: Expr -> Expr -> Bool 
betaEq e1 e2 = (nf e1) `alphaEq` (nf e2)
