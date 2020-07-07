module Main(main) where

import HML.Logic.Predicates.PredicatesServer

import HML.Logic.Predicates.Axioms.Base
import HML.Logic.Predicates.Axioms.Set

import HML.Logic.Predicates.PrettyPrintLaTeX

import System.IO

main :: IO ()
main = do hSetBuffering stdout NoBuffering
          --putStrLn "Starting PropProver"
          startHPAServer (standardAxioms ++ setAxioms) (updatePrintFunction printSetFn defaultContext)
          return ()