-- Basically just labs
-- Starting with LAB 1
{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}

import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad
import Test.QuickCheck
import System.IO.Unsafe

-- updating a function
update :: Eq a => (a -> b) -> a -> b -> a -> b
update ρ x v = \y -> if x == y then v else ρ y

-- useful for debugging
debug :: Show a => String -> a -> a
debug str x = seq (unsafePerformIO $ do putStr "<"; putStr str; putStr ": "; print x; putStr ">") x

todo :: a
todo = undefined

-- propositional variable names are just strings
type PropName = String

data Formula =
      T
    | F
    | Prop PropName -- atomic formulas
    | Not Formula
    | And Formula Formula
    | Or Formula Formula
    | Implies Formula Formula
    | Iff Formula Formula
    deriving (Eq, Show)

infixr 8 /\, ∧
(/\) = And
(∧) = And -- input with "\and"

infixr 5 \/, ∨, ==>
(\/) = Or
(∨) = Or -- input with "\or"
(==>) = Implies

infixr 4 <==>, ⇔
(<==>) = Iff
(⇔) = Iff -- input with "\lr"

p, q, r, s, t :: Formula

p = Prop "p"
q = Prop "q"
r = Prop "r"
s = Prop "s"
t = Prop "t"

satisfiable_formulas = [
    p ∧ q ∧ s ∧ p,
    T,
    p,
    Not p,
    (p ∨ q ∧ r) ∧ (Not p ∨ Not r),
    (p ∨ q) ∧ (Not p ∨ Not q)
  ]

unsatisfiable_formulas = [
    p ∧ q ∧ s ∧ Not p,
    T ∧ F,
    F,
    (p ∨ q ∧ r) ∧ Not p ∧ Not r,
    (p ⇔ q) ∧ (q ⇔ r) ∧ (r ⇔ s) ∧ (s ⇔ Not p)
  ]

instance Arbitrary Formula where
    arbitrary = sized f where
      
      f 0 = oneof $ map return $ [p, q, r, s, t] ++ [T, F]

      f size = frequency [
        (1, liftM Not (f (size - 1))),
        (4, do
              size' <- choose (0, size - 1)
              conn <- oneof $ map return [And, Or, Implies, Iff]
              left <- f size'
              right <- f $ size - size' - 1
              return $ conn left right)
        ]

-- truth valuations
type Valuation = PropName -> Bool

-- the evaluation function
eval :: Formula -> Valuation -> Bool
eval T _ = True
eval F _ = False
eval (Prop p) ρ = ρ p
eval (Not φ) ρ = not (eval φ ρ)
eval (And φ ψ) ρ = e1 && e2
  where
    e1 = eval φ ρ
    e2 = eval ψ ρ
eval (Or φ ψ) ρ = e1 || e2
  where
    e1 = eval φ ρ
    e2 = eval ψ ρ
eval (Implies φ ψ) ρ = (not e1) || e2
  where
    e1 = eval φ ρ
    e2 = eval ψ ρ
eval (Iff φ ψ) ρ = e1 == e2
  where
    e1 = eval φ ρ
    e2 = eval ψ ρ
eval _  _ = error "not a propositional formula"

ρ0 = const True
ρ1 = const False
ρ2 = update ρ0 "p" False

test_eval =
  eval (p ∧ Not p) ρ0 == False &&
  eval (p ∧ Not p) ρ1 == False &&
  eval (p ∨ q) ρ2 == True

-- quickCheck test_eval

-- check that the eval function is efficient
-- ifformula 3 == Iff (Iff (Iff T T) T) T
ifformula :: Int -> Formula
ifformula 0 = T
ifformula n = Iff (ifformula (n-1)) T

-- this should evaluate within a fraction of second
test_eval2 = eval (ifformula 23) (const True) == True

-- quickCheck test_eval2

variables :: Formula -> [PropName]
variables = nub . go where
  go T = []
  go F = []
  go (Prop p) = [p]
  go (Not φ) = go φ
  go (And φ ψ) = go φ ++ go ψ
  go (Or φ ψ) = go φ ++ go ψ
  go (Implies φ ψ) = go φ ++ go ψ
  go (Iff φ ψ) = go φ ++ go ψ
  go _ = error "not a propositional formula"

type SATSolver = Formula -> Bool

-- the list of all valuations on a given list of variables
valuations :: [PropName] -> [Valuation]
valuations [] = [undefined]
valuations (x : xs) = concat [[update ρ x True, update ρ x False] | ρ <- valuations xs]

satisfiable :: SATSolver
satisfiable φ = or [eval φ ρ | ρ <- valuations (variables φ)]

tautology :: Formula -> Bool
tautology φ = and [eval φ ρ | ρ <- valuations (variables φ)] -- not $ satisfiable $ Not \phi 

is_nnf :: Formula -> Bool
is_nnf T = True
is_nnf F = True
is_nnf (Prop _) = True
is_nnf (Not (Prop _)) = True
is_nnf (And phi psi) = is_nnf phi && is_nnf psi
is_nnf (Or phi psi) = is_nnf phi && is_nnf psi
is_nnf (Implies phi psi) = False
is_nnf (Iff phi psi) = False
is_nnf (Not _) = False
is_nnf _ = error "not a propositional formula"

-- quickCheck $
--  is_nnf (Not p ∧ (q ∨ (r ∧ s)))  -- NNF example
--  && (not $ is_nnf $ Not (p ∨ q)) -- NNF non-example

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
nnf x = x

propagateNot :: Formula -> Formula
propagateNot (Or phi psi) = And (propagateNot phi) (propagateNot psi)
propagateNot (And phi psi) = Or (propagateNot phi) (propagateNot psi)
propagateNot (F) = T
propagateNot (T) = F
propagateNot (Not x) = x
propagateNot x = Not x

prop_nnf :: Formula -> Bool
prop_nnf φ = let ψ = nnf φ in is_nnf ψ && (tautology $ φ ⇔ ψ)

-- quickCheck prop_nnf


data Literal = Pos PropName | Neg PropName deriving (Eq, Show, Ord)

literal2var :: Literal -> PropName
literal2var (Pos p) = p
literal2var (Neg p) = p

type DNFClause = [Literal]
type DNF = [DNFClause]

dnf2formula :: [[Literal]] -> Formula
dnf2formula [] = F
dnf2formula lss = foldr1 Or (map go lss) where
  go [] = T
  go ls = foldr1 And (map go2 ls)
  go2 (Pos p) = Prop p
  go2 (Neg p) = Not (Prop p)

dnf :: Formula -> DNF
dnf f = nnfToDnf normal
  where
    normal = nnf f

  
nnfToDnf :: Formula -> DNF
nnfToDnf (And left right) = mergeDnf l r
  where
    l = nnfToDnf left
    r = nnfToDnf right
nnfToDnf (Or left right) = (nnfToDnf left) ++ (nnfToDnf right)
nnfToDnf (Prop x) = [[Pos x]]
nnfToDnf (Not (Prop x)) = [[Neg x]]
nnfToDnf T = [[(Pos "a")], [(Neg "a")]]
nnfToDnf F = [[(Pos "a"), (Neg "a")]]

mergeDnf :: DNF -> DNF -> DNF
mergeDnf ls rs = [ l++r | l <- ls, r <- rs] 

test_dnf :: Formula -> Bool
test_dnf φ = tautology $ φ ⇔ (dnf2formula (dnf φ))

-- quickCheckWith (stdArgs {maxSize = 18}) test_dnf

sat_dnf :: SATSolver
sat_dnf f = checkClauses cs
  where
    cs = dnf f
    
checkClauses :: DNF -> Bool
checkClauses [] = False
checkClauses (c:cs) = (checkOneClause c) || (checkClauses cs)

checkOneClause :: DNFClause -> Bool
checkOneClause [] = True
checkOneClause (l:ls) = (not $ (negg l) `elem` ls) && (checkOneClause ls)

negg :: Literal -> Literal
negg (Pos x) = (Neg x)
negg (Neg x) = (Pos x)

prop_sat_dnf :: Formula -> Bool
prop_sat_dnf phi = sat_dnf phi == satisfiable phi

-- quickCheckWith (stdArgs {maxSize = 20}) prop_sat_dnf

test_solver :: SATSolver -> Bool
test_solver solver = and $ map solver satisfiable_formulas ++ map (not . solver) unsatisfiable_formulas

-- quickCheck (test_solver sat_dnf)


-- LAB 2 starts here

-- generation of fresh variable names
fresh :: [PropName] -> PropName
fresh vars = head $ filter (not . (`elem` vars)) $ map (("p"++) . show) [0..]

opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p

type CNFClause = [Literal]
type CNF = [CNFClause]

cnf2formula :: CNF -> Formula
cnf2formula [] = T
cnf2formula lss = foldr1 And (map go lss) where
  go [] = F
  go ls = foldr1 Or (map go2 ls)
  go2 (Pos p) = Prop p
  go2 (Neg p) = Not (Prop p)
  
positive_literals :: CNFClause -> [PropName]
positive_literals ls = nub [p | Pos p <- ls]

negative_literals :: CNFClause -> [PropName]
negative_literals ls = nub [p | Neg p <- ls]

literals :: [Literal] -> [PropName]
literals ls = nub $ positive_literals ls ++ negative_literals ls

cnf :: Formula -> CNF
cnf = go . nnf where
  go T = []
  go F = [[]]
  go (Prop p) = [[Pos p]]
  go (Not (Prop p)) = [[Neg p]]
  go (φ `And` ψ) = go φ ++ go ψ
  go (φ `Or` ψ) = [as ++ bs | as <- go φ, bs <- go ψ]

test_cnf :: Formula -> Bool
test_cnf φ = tautology $ φ ⇔ (cnf2formula (cnf φ))

-- quickCheckWith (stdArgs {maxSize = 18}) test_cnf

equi_satisfiable :: Formula -> Formula -> Bool
equi_satisfiable φ ψ = satisfiable φ == satisfiable ψ

ecnf :: Formula -> CNF
ecnf f = cnf conjunction
  where
    vars = variables f
    res = ecnfMiddleStep f vars
    conjunction = makeConjunction ((getFirst res):(getThird res))

getFirst (x, _, _) = x
getSecond (_, x, _) = x
getThird (_, _, x) = x

makeConjunction :: [Formula] -> Formula
makeConjunction [] = T 
makeConjunction (x:[]) = x
makeConjunction (x:xs) = And x (makeConjunction xs)

ecnfMiddleStep :: Formula -> [PropName] -> (Formula, [PropName], [Formula])
ecnfMiddleStep (Not f) vars = ((Prop newVar), (newVar:updatedVars), ((Iff (Prop newVar) (Not newFormula)):formulas))
  where 
    x = ecnfMiddleStep f vars
    newFormula = getFirst x
    updatedVars = getSecond x
    formulas = getThird x
    newVar = fresh updatedVars
ecnfMiddleStep (And f1 f2) vars = ((Prop newVar), (newVar:updatedVars), ((Iff (Prop newVar) (And newF1 newF2)):(formulas)))
  where 
    x = ecnfMiddleStep f1 vars
    y = ecnfMiddleStep f2 (getSecond x)
    newF1 = getFirst x
    newF2 = getFirst y
    updatedVars = getSecond y
    formulas = (getThird x) ++ (getThird y)
    newVar = fresh updatedVars
ecnfMiddleStep (Or f1 f2) vars = ((Prop newVar), (newVar:updatedVars), ((Iff (Prop newVar) (Or newF1 newF2)):(formulas)))
  where 
    x = ecnfMiddleStep f1 vars
    y = ecnfMiddleStep f2 (getSecond x)
    newF1 = getFirst x
    newF2 = getFirst y
    updatedVars = getSecond y
    formulas = (getThird x) ++ (getThird y)
    newVar = fresh updatedVars
ecnfMiddleStep (Implies f1 f2) vars = ((Prop newVar), (newVar:updatedVars), ((Iff (Prop newVar) (Implies newF1 newF2)):(formulas)))
  where 
    x = ecnfMiddleStep f1 vars
    y = ecnfMiddleStep f2 (getSecond x)
    newF1 = getFirst x
    newF2 = getFirst y
    updatedVars = getSecond y
    formulas = (getThird x) ++ (getThird y)
    newVar = fresh updatedVars
ecnfMiddleStep (Iff f1 f2) vars = ((Prop newVar), (newVar:updatedVars), ((Iff (Prop newVar) (Iff newF1 newF2)):(formulas)))
  where 
    x = ecnfMiddleStep f1 vars
    y = ecnfMiddleStep f2 (getSecond x)
    newF1 = getFirst x
    newF2 = getFirst y
    updatedVars = getSecond y
    formulas = (getThird x) ++ (getThird y)
    newVar = fresh updatedVars
ecnfMiddleStep f vars = (f, vars, [])


-- ecnf (T ∧ F ∨ T)

prop_ecnf :: Formula -> Bool
prop_ecnf phi = equi_satisfiable phi (cnf2formula $ ecnf phi)

-- quickCheckWith (stdArgs {maxSize = 10}) prop_ecnf

remove_tautologies :: CNF -> CNF
remove_tautologies c = filter (isNotTautology Set.empty) c

isNotTautology :: Set.Set Literal -> [Literal] -> Bool
isNotTautology set [] = True
isNotTautology set (x:xs) = (Set.notMember (opposite x) set) && (isNotTautology (Set.insert x set) xs)

one_literal :: CNF -> CNF
one_literal cnf = do
    let withoutTautologies = remove_tautologies cnf
    let set = getOneLiterals withoutTautologies Set.empty 
    if Set.null set 
        then withoutTautologies
        else one_literal $ removeLiterals withoutTautologies set

getOneLiterals :: CNF -> Set.Set Literal -> Set.Set Literal
-- If we already have Pos q, do not fetch Neg q, because we should change [Neg q] to [] later.
getOneLiterals (([l]):xs) s = if (Set.notMember (opposite l) s) 
  then getOneLiterals xs (Set.insert l s)
  else getOneLiterals xs s
getOneLiterals ((_):xs) s = getOneLiterals xs s
getOneLiterals _ s = s 

removeLiterals :: CNF -> Set.Set Literal -> CNF
removeLiterals (c:cs) s = if (doesNotContainSomeLiteral c s)
    then (cleared:t)
    else t
  where
    cleared = filter (\x -> Set.notMember (opposite x) s) c
    t = removeLiterals cs s
removeLiterals [] _ = []

doesNotContainSomeLiteral :: [Literal] -> Set.Set Literal -> Bool
doesNotContainSomeLiteral [] _ = True
doesNotContainSomeLiteral (x:xs) s = (Set.notMember x s) && (doesNotContainSomeLiteral xs s)


-- one_literal [[Pos "p"], [Pos "p", Pos "q", Pos "p", Pos "r"], [Neg "q", Pos "r", Neg "p", Neg "r", Neg "p"], [Neg "q", Neg "p"], [Pos "q", Pos "r", Pos "s"], [Neg "p", Pos "p"]]

prop_one_literal =
  one_literal [[Pos "p"], [Pos "p", Pos "q", Pos "p", Pos "r"], [Neg "q", Pos "r", Neg "p", Neg "r", Neg "p"], [Neg "q", Neg "p"], [Pos "q", Pos "r", Pos "s"], [Neg "p", Pos "p"]] == [[Pos "r",Pos "s"]] &&
  one_literal [[Pos "p"],[Pos "p1"],[Neg "p",Pos "q"],[Pos "p1",Pos "p0"],[Pos "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "q0",Neg "p"],[Neg "s",Neg "p",Pos "p0"]] ==
    [[Neg "p0",Pos "s"],[Neg "s",Pos "p0"]] &&
  one_literal
    [[Pos "q"],[Pos "p0"],[Neg "p0",Pos "s"],[Neg "p0"]] ==
    [[]]

-- quickCheck prop_one_literal

affirmative_negative :: CNF -> CNF
affirmative_negative cnf = removeOnlyPosOrNeg newCnf sets
  where
    newCnf = one_literal cnf
    sets = getLiterals newCnf Set.empty

getLiterals :: CNF -> Set.Set Literal -> Set.Set Literal
getLiterals [] s = s
getLiterals (c:cs) s = getLiterals cs (insertLiterals c s)

insertLiterals :: CNFClause -> Set.Set Literal -> Set.Set Literal
insertLiterals [] s = s 
insertLiterals (l:ls) s = insertLiterals ls (Set.insert l s)

removeOnlyPosOrNeg :: CNF -> Set.Set Literal -> CNF
removeOnlyPosOrNeg [] _ = []
removeOnlyPosOrNeg (c:cs) s = if newClause /= []
  then (newClause:newTail)
  else newTail
  where
    newClause = removeClauseIfOnlyPositiveOrNegative c s
    newTail = removeOnlyPosOrNeg cs s

removeClauseIfOnlyPositiveOrNegative :: CNFClause -> Set.Set Literal -> CNFClause
removeClauseIfOnlyPositiveOrNegative [] _ = [Pos "a"]
removeClauseIfOnlyPositiveOrNegative (l:ls) s = if (isOnlyPosOrNeg l s)
  then []
  else
    if newTail == []
      then []
      else (l:ls)
  where
    newTail = removeClauseIfOnlyPositiveOrNegative ls s

isOnlyPosOrNeg :: Literal -> Set.Set Literal -> Bool
isOnlyPosOrNeg l s = (posOk && (not negOk)) || ((not posOk) && negOk)
  where
    posOk = Set.member l s 
    negOk = Set.member (opposite l) s

prop_affirmative_negative :: Bool
prop_affirmative_negative =
  affirmative_negative
    [[Neg "p2",Pos "p"],[Neg "p2",Pos "p1"],[Neg "p",Neg "p1",Neg "p2"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] ==
    [[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] &&
  affirmative_negative
    [[Pos "p", Pos "q"], [Pos "p", Neg "q"]] ==
    []
    
-- quickCheck prop_affirmative_negative

resolution :: CNF -> CNF
resolution cnf = doResolution cnf minVar
  where
    occurenceMap = getLeastCommonVar cnf Map.empty
    min = minimum $ Map.elems occurenceMap
    minVar = head $ Map.keys $ Map.filter (== min) occurenceMap

doResolution :: CNF -> String -> CNF
doResolution [] _ = [[]]
doResolution (c:cs) var = if (clauseContainsVar c var) 
  then (((removeVarFromClause c var) ++ newHead):newTail)
  else (newHead:c:newTail)
  where
    res = doResolution cs var
    newHead = head res
    newTail = tail res

clauseContainsVar :: CNFClause -> String -> Bool
clauseContainsVar cs var = foldr (\x a -> a || (getVarFromLiteral x == var)) True cs

removeVarFromClause :: CNFClause -> String -> CNFClause
removeVarFromClause [] _ = []
removeVarFromClause (l:ls) var = if (getVarFromLiteral l == var)
  then ls
  else (l:(removeVarFromClause ls var))

getLeastCommonVar :: CNF -> Map.Map String Int -> Map.Map String Int
getLeastCommonVar [] m = m 
getLeastCommonVar (c:cs) m = getLeastCommonVar cs (getLeastCommonVarInClause c m)

getLeastCommonVarInClause :: CNFClause -> Map.Map String Int -> Map.Map String Int
getLeastCommonVarInClause [] m = m 
getLeastCommonVarInClause (l:ls) m = getLeastCommonVarInClause ls (Map.insertWith (+) s 1 m)
  where
    s = getVarFromLiteral l

getVarFromLiteral :: Literal -> String
getVarFromLiteral (Pos x) = x
getVarFromLiteral (Neg x) = x

prop_resolution :: Bool
prop_resolution = resolution [[Pos "p", Pos "q"],[Neg "p", Neg "q"]] == [[Pos "q", Neg "q"]]

