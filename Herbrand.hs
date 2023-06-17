{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}

module Herbrand where

import Control.Monad
import Data.List
import Text.Show

import Formula
import Dnf

useHerbrandTheorem :: Formula -> Bool
useHerbrandTheorem f = startHerbrand c s f
  where
    sigs = sig f
    consts = constants sigs
    -- If there are no constants, we must assume there is one.
    c = if consts == [] then [Fun "a constant" []] else consts
    s = if consts == [] then (("a constant", 0):sigs) else sigs

generateUniverse :: [Term] -> Signature -> [Term]
generateUniverse previous funcs = newGen
  where
    possibleArgs = [replicateM n previous | n <- [0..]]
    funcsWithArgsSet = [[Fun fun args | args <- (possibleArgs !! n)] | (fun, n) <- funcs]
    newGen = nub $ concat funcsWithArgsSet

startHerbrand :: [Term] -> Signature -> Formula -> Bool
startHerbrand consts funcs f = herbrand [] funcs f vars
  where
    vars = fv f

hasUniverseChanged :: [Term] -> [Term] -> Bool
hasUniverseChanged [] [] = False
hasUniverseChanged [] _ = True
hasUniverseChanged (_:prevs) (_:currs) = hasUniverseChanged prevs currs

herbrand :: [Term] -> Signature -> Formula -> [VarName] -> Bool
herbrand prevUniverse funcs f vars = do
    let universe = generateUniverse prevUniverse funcs
    if (hasUniverseChanged prevUniverse universe)
        then do 
            let res = checkHerbrand universe f vars
            if (not res) then True else herbrand universe funcs f vars
        else False

checkHerbrand :: [Term] -> Formula -> [VarName] -> Bool
checkHerbrand universe f vars = checkEvaluations evals f vars
  where
    evals = replicateM (length vars) universe

checkEvaluations :: [[Term]] -> Formula -> [VarName] -> Bool
checkEvaluations evals f vars = sat_DP (createConjunction evals f vars)

createConjunction :: [[Term]] -> Formula -> [VarName] -> SATFormula
createConjunction [] _ _ = Dnf.T
createConjunction (eval:evals) f vars = Dnf.And f1 f2
  where
    f1 = applyEval eval f vars
    f2 = createConjunction evals f vars

applyEval :: [Term] -> Formula -> [VarName] -> SATFormula
applyEval eval f vars = convertToSAT $ applyEvalToVars eval f vars undefined

applyEvalToVars :: [Term] -> Formula -> [VarName] -> Substitution -> Formula
applyEvalToVars [] f [] subs = apply subs f
applyEvalToVars (t:ts) f (v:vs) subs = applyEvalToVars ts f vs (update subs v t)

convertToSAT :: Formula -> SATFormula
convertToSAT Formula.T = Dnf.T 
convertToSAT Formula.F = Dnf.F 
convertToSAT (Formula.Not f) = Dnf.Not $ convertToSAT f
convertToSAT (Formula.Or f1 f2) = Dnf.Or (convertToSAT f1) (convertToSAT f2)
convertToSAT (Formula.And f1 f2) = Dnf.And (convertToSAT f1) (convertToSAT f2)
convertToSAT (Formula.Forall v f) = convertToSAT f
convertToSAT (Formula.Exists v f) = convertToSAT f
convertToSAT (Formula.Implies f1 f2) = Dnf.Implies (convertToSAT f1) (convertToSAT f2)
convertToSAT (Formula.Iff f1 f2) = Dnf.Iff (convertToSAT f1) (convertToSAT f2)
convertToSAT (Formula.Rel name terms) = (Dnf.Prop $ (showString name . showString "[]" . (termsToShows terms))"]")

termsToShows :: [Term] -> ShowS
termsToShows [] = showString ""
termsToShows [t] = termToShows t
termsToShows (t:ts) = termToShows t . showString " " . (termsToShows ts)

termToShows :: Term -> ShowS
termToShows (Var v) = showString v 
termToShows (Fun f ts) = showString f . showString "(" . termsToShows ts . showString ")"
