{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

import Data.List
import Control.Monad
import Control.Monad.State
import Test.QuickCheck hiding (Fun, (==>))
import System.IO.Unsafe

-- useful for debugging
debug :: Show a => String -> a -> a
debug str x = seq (unsafePerformIO $ do putStr "<"; putStr str; putStr ": "; print x; putStr ">") x

partitions :: [a] -> [[[a]]]
partitions [] = [[]]
partitions (x:xs) = [[x]:yss | yss <- partitions xs] ++ [(x:ys):yss | (ys:yss) <- partitions xs]

-- all possible ways to split n into the sum of stricly positive integers
catalan :: Int -> [[Int]]
catalan n = map (map length) $ partitions [1..n]

todo = undefined

type VarName = String
type FunName = String
type RelName = String

-- enumerate variants of a variable name
variants :: VarName -> [VarName]
variants x = x : [x ++ show n | n <- [0..]]

--instance {-# OVERLAPPING #-} Arbitrary VarName where
--  arbitrary = elements ["x", "y", "z", "t"]
  
--instance {-# OVERLAPPING #-} Arbitrary FunName where
--  arbitrary = elements ["f", "g", "h", "i"]
  
--instance {-# OVERLAPPING #-} Arbitrary RelName where
--  arbitrary = elements ["R", "S", "T", "U"]

data Term = Var VarName | Fun FunName [Term] deriving (Eq, Ord, Show)

varsT :: Term -> [VarName]
varsT (Var x) = [x]
varsT (Fun _ ts) = nub $ concatMap varsT ts

instance Arbitrary Term where
  arbitrary = resize 8 $ sized f where
    f size | size == 0 || size == 1 = do x <- arbitrary
                                         return $ Var x
           | otherwise = frequency [ (1, go sizes) | sizes <- catalan size]
              where go sizes = do ts <- sequence $ map f sizes
                                  return $ Fun "f" ts

data Formula =
  T |
  F |
  Rel RelName [Term] |
  Not Formula |
  And Formula Formula |
  Or Formula Formula |
  Implies Formula Formula |
  Iff Formula Formula |
  Exists VarName Formula |
  Forall VarName Formula deriving (Eq, Ord, Show)

infixr 8 /\, ∧
(/\) = And
(∧) = And

infixr 5 \/, ∨, ==>
(\/) = Or
(∨) = Or -- input with "\or"
(==>) = Implies

infixr 4 <==>, ⇔
(<==>) = Iff
(⇔) = Iff -- input with "\lr"

instance Arbitrary Formula where
    arbitrary = resize 30 $ sized f where
      f 0 = do ts <- arbitrary
               return $ Rel "R" ts
      f size = frequency [
        (1, liftM Not (f (size - 1))),
        (4, do
              size' <- choose (0, size - 1)
              conn <- oneof $ map return [And, Or, Implies, Iff]
              left <- f $ size'
              right <- f $ size - size' - 1
              return $ conn left right),
        (5, do conn <- oneof $ map return [Exists, Forall]
               phi <- f $ size - 1
               x <- arbitrary
               return $ conn x phi)
        ]

vars :: Formula -> [VarName]
vars T = []
vars F = []
vars (Rel _ ts) = varsT (Fun "dummy" ts)
vars (Not phi) = vars phi
vars (And phi psi) = nub $ vars phi ++ vars psi
vars (Or phi psi) = nub $ vars phi ++ vars psi
vars (Implies phi psi) = nub $ vars phi ++ vars psi
vars (Iff phi psi) = nub $ vars phi ++ vars psi
vars (Exists x phi) = nub $ x : vars phi
vars (Forall x phi) = nub $ x : vars phi

freshIn :: VarName -> Formula -> Bool
x `freshIn` phi = not $ x `elem` vars phi

freshVariant :: VarName -> Formula -> VarName
freshVariant x phi = head [ y | y <- variants x, y `freshIn` phi ]

renameT :: VarName -> VarName -> Term -> Term
renameT x y (Var z)
  | z == x = Var y
  | otherwise = Var z

renameT x y (Fun f ts) = Fun f (map (renameT x y) ts)

rename :: VarName -> VarName -> Formula -> Formula
rename x y T = T
rename x y F = F
rename x y (Rel r ts) = Rel r (map (renameT x y) ts)
rename x y (Not phi) = Not (rename x y phi)
rename x y (And phi psi) = And (rename x y phi) (rename x y psi)
rename x y (Or phi psi) = Or (rename x y phi) (rename x y psi)
rename x y (Implies phi psi) = Implies (rename x y phi) (rename x y psi)
rename x y (Iff phi psi) = Iff (rename x y phi) (rename x y psi)
rename x y (Forall z phi)
  | z == x = Forall z phi
  | otherwise = Forall z (rename x y phi)
rename x y (Exists z phi)
  | z == x = Exists z phi
  | otherwise = Exists z (rename x y phi)

d x = Rel "d" [Var x]
drinker = Exists "x" (d "x" ==> Forall "y" (d "y"))
--print drinker

t x y = Rel "t" [Var x, Var y]
lem = Forall "x" $ Forall "y" $ t "x" "y" ∨ (Not $ t "x" "y")
--print lem

swap = Exists "x" (Forall "y" $ t "x" "y") ==> Forall "y" (Exists "x" $ t "x" "y")
--print swap

is_nnf :: Formula -> Bool
is_nnf T = True
is_nnf F = True
is_nnf (Rel _ _) = True
is_nnf (Not (Rel _ _)) = True
is_nnf (And phi psi) = is_nnf phi && is_nnf psi
is_nnf (Or phi psi) = is_nnf phi && is_nnf psi
is_nnf (Implies phi psi) = False
is_nnf (Iff phi psi) = False
is_nnf (Not _) = False
is_nnf (Exists _ phi) = is_nnf phi
is_nnf (Forall _ phi) = is_nnf phi

nnf :: Formula -> Formula
nnf (Implies phi psi) = Or (propagateNot e1) e2
  where
    e1 = nnf phi
    e2 = nnf psi
nnf (Iff phi psi) = Or (And e1 e2) (And (propagateNot e1) (propagateNot e2))
  where
    e1 = nnf phi
    e2 = nnf psi
nnf (Not phi) = propagateNot e1
  where
    e1 = nnf phi
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Exists var f) = (Exists var (nnf f))
nnf (Forall var f) = (Forall var (nnf f))
nnf x = x

propagateNot :: Formula -> Formula
propagateNot (Or phi psi) = And (propagateNot phi) (propagateNot psi)
propagateNot (And phi psi) = Or (propagateNot phi) (propagateNot psi)
propagateNot (F) = T
propagateNot (T) = F
propagateNot (Not x) = x
propagateNot (Exists var f) = (Forall var (propagateNot f))
propagateNot (Forall var f) = (Exists var (propagateNot f))
propagateNot x = Not x

nnfProp :: Formula -> Bool
nnfProp phi = is_nnf (nnf phi)

-- quickCheck nnfProp

is_pnf :: Formula -> Bool
is_pnf (Forall _ phi) = is_pnf phi
is_pnf (Exists _ phi) = is_pnf phi
is_pnf phi = qf phi

-- check whether the formula is quantifier-free
qf :: Formula -> Bool
qf (Rel _ _) = True
qf (Not phi) = qf phi
qf (And phi psi) = qf phi && qf psi
qf (Or phi psi) = qf phi && qf psi
qf (Implies phi psi) = qf phi && qf psi
qf (Iff phi psi) = qf phi && qf psi
qf _ = False

update :: Eq a => (a -> b) -> a -> b -> a -> b
update f a b x | x == a = b
               | otherwise = f x

-- alternating merge of two (potentially infinite) lists
merge :: [a] -> [a] -> [a]
merge [] bs = bs
merge (a : as) bs = a : merge bs as

-- alternating merge of a (potentially infinite) list of (potentially infinite) lists
merges :: [[a]] -> [a]
merges [] = []
merges (as:ass) = merge as (merges ass)

-- collect all functions from a finite list to a (potentially infinite) list
functions :: Eq a => [a] -> [b] -> [a -> b]
functions [] _ = [undefined]
functions (a:as) bs = merges [[update f a b | f <- functions as bs] | b <- bs]

fv :: Formula -> [VarName]
fv T = []
fv F = []
fv (Rel _ ts) = varsT (Fun "dummy" ts)
fv (Not phi) = fv phi
fv (And phi psi) = nub $ fv phi ++ fv psi
fv (Or phi psi) = nub $ fv phi ++ fv psi
fv (Implies phi psi) = nub $ fv phi ++ fv psi
fv (Iff phi psi) = nub $ fv phi ++ fv psi
fv (Exists x phi) = delete x $ fv phi
fv (Forall x phi) = delete x $ fv phi

prop_fv = fv (Exists "x" (Rel "R" [Fun "f" [Var "x", Var "y"], Var "z"])) == ["y", "z"]
-- quickCheck prop_fv

type Substitution = VarName -> Term

substT :: Substitution -> Term -> Term
substT σ (Var x) = σ x
substT σ (Fun f ts) = Fun f (map (substT σ) ts)

subst :: Substitution -> Formula -> Formula
subst _ T = T
subst _ F = F
subst σ (Rel r ts) = Rel r $ map (substT σ) ts
subst σ (Not phi) = Not $ subst σ phi
subst σ (And phi psi) = And (subst σ phi) (subst σ psi)
subst σ (Or phi psi) = Or (subst σ phi) (subst σ psi)
subst σ (Implies phi psi) = Implies (subst σ phi) (subst σ psi)
subst σ (Iff phi psi) = Iff (subst σ phi) (subst σ psi)
subst σ (Exists x phi) = Exists x (subst (update σ x (Var x)) phi)
subst σ (Forall x phi) = Forall x (subst (update σ x (Var x)) phi)

generalise :: Formula -> Formula
generalise phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Forall x $ go xs

prop_generalise = generalise (Exists "x" (Rel "R" [Fun "f" [Var "x", Var "y"], Var "z"])) == Forall "y" (Forall "z" (Exists "x" (Rel "R" [Fun "f" [Var "x",Var "y"],Var "z"])))

-- quickCheck prop_generalise

fresh :: Formula -> Formula
fresh phi = evalState (go phi) $ fv phi
  where go :: Formula -> State [VarName] Formula
        go T = return T
        go F = return F
        go phi@(Rel _ _) = return phi
        go (Not phi) = liftM Not (go phi)
        go (And phi psi) = liftM2 And (go phi) (go psi)
        go (Or phi psi) = liftM2 Or (go phi) (go psi)
        go (Implies phi psi) = liftM2 Implies (go phi) (go psi)
        go (Iff phi psi) = liftM2 Iff (go phi) (go psi)
        go (Forall x phi) = go2 Forall x phi
        go (Exists x phi) = go2 Exists x phi
        
        go2 quantifier x phi =
          do xs <- get
             let y = head [y | y <- variants x, not $ y `elem` xs]
             let psi = rename x y phi
             put $ y : xs
             liftM (quantifier y) $ go psi

phi = Exists "x" (Exists "x" (Rel "r" [Fun "f" [Var "x", Var "y"]]))
psi = Exists "x" (Rel "r" [Fun "f" [Var "x"]])

--fresh (And phi psi)

