{--
 -- Base.hs
 -- :l ./HML/Logic/PredicateLogic/Axioms/Base.hs from devel directory
 -- Basic axioms derived from the logic laws
 --}
module HML.Logic.Predicates.Axioms.Set where

import HML.Logic.Predicates.Predicates
--import HML.Logic.PredicateLogic.PredicateCursors
--import HML.Logic.PredicateLogic.PredicateMatching
--import HML.Logic.PredicateLogic.PredicateLogicLaws
import HML.Logic.Predicates.PredicateProofGraph
--import HML.Logic.PredicateLogic.PredicatesPrettyPrint

--import Data.List(intercalate, intersect)
--import Control.Monad(mplus,liftM,liftM2)
--import Control.Monad.State

--data NamedPredicate = NP String Predicate deriving (Show)


--namePredicate :: Predicate -> String -> NamedPredicate
{- ---------- Some set axioms ------------ -}

setAxioms :: [NamedPredicate]
setAxioms = [ subsetAxiom
            , unionAxiom]

unionAxiom :: NamedPredicate
unionAxiom = namePredicate (forall_ varX (iffP (expP $ inSet expX (union setA setB)) 
                                               ((expP $ inSet expX setA) `orP` (expP $ inSet expX setB))))
                           "unionAxiom"
    where setA = patternExp "A"
          setB = patternExp "B"
          
          varX = patternN "x"
          expX = namedExp varX

subsetAxiom :: NamedPredicate
-- TODO: should the variable be a pattern as well?
-- probably not necessary as we can instantiate to a specific variable name
-- but then again, using a pattern allows for more flexibility in naming
subsetAxiom = namePredicate (iffP (expP $ (setA `subset` setB))
                                  (forall_ varX ((expP $ inSet expX setA) `impP` (expP $ inSet expX setB))))
                            "subsetAxiom"
    where setA = patternExp "A"
          setB = patternExp "B"

          varX = patternN "x"
          expX = namedExp varX

