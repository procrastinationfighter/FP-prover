{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

module Main where

import Data.List

import System.IO
import System.Random
import System.Timeout

import Text.Printf

import Control.Monad.State

import Test.QuickCheck hiding (Fun, (===))

import Formula
import Parser hiding (one)

import FirstOrder
import Herbrand

removeQuants :: Formula -> Formula
removeQuants (Forall _ f) = removeQuants f 
removeQuants (Exists _ f) = removeQuants f 
removeQuants f = f

prover :: Formula -> Bool
prover f = useHerbrandTheorem $ removeQuants skolem
  where
    skolem = skolemise (Not f)

main :: IO ()
main = do
    eof <- hIsEOF stdin
    if eof
        then return ()
        else do
                line <- getLine -- read the input
                let phi = parseString line -- call the parser
                let res = prover phi -- call the prover
                if res
                  then putStrLn "1" -- write 1 if the formula is a tautology
                  else putStrLn "0" -- write 0 if the formula is not a tautology