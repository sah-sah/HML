{--
 -- Base.hs
 -- :l ./HML/Logic/PredicateLogic/Axioms/Base.hs from devel directory
 -- Basic axioms derived from the logic laws
 --}
module HML.Logic.Predicates.Axioms.Base where

--import HML.Logic.PredicateLogic.Predicates
--import HML.Logic.PredicateLogic.PredicateCursors
--import HML.Logic.PredicateLogic.PredicateMatching
import HML.Logic.Predicates.PredicateLogicLaws
import HML.Logic.Predicates.PredicateProofGraph
--import HML.Logic.PredicateLogic.PredicatesPrettyPrint

--import Data.List(intercalate, intersect)
--import Control.Monad(mplus,liftM,liftM2)
--import Control.Monad.State

--data NamedPredicate = NP String Predicate deriving (Show)


--namePredicate :: Predicate -> String -> NamedPredicate
{- ---------- Some set axioms ------------ -}
{-
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
-}
{- ---------- Some standard axioms ---------- -}


standardAxioms :: [NamedPredicate]
standardAxioms = [ equivalenceAxiom
                  ,implicationAxiom
                  ,doubleNegationAxiom
                  ,idempotentAndAxiom
                  ,idempotentOrAxiom
                  ,commutativeAndAxiom
                  ,commutativeOrAxiom
                  ,associativeAndAxiom
                  ,associativeOrAxiom
                  ,distributiveAndAxiom
                  ,distributiveOrAxiom
                  ,deMorgansAndAxiom
                  ,deMorgansOrAxiom
                  ,identityAndAxiom
                  ,identityOrAxiom
                  ,annihilationAndAxiom
                  ,annihilationOrAxiom
                  ,inverseAndAxiom
                  ,inverseOrAxiom
                  ,absorptionAndAxiom
                  ,absorptionOrAxiom
                  ,deMorgansForallAxiom
                  ,deMorgansExistsAxiom
                  ,swapForallAxiom
                  ,swapExistsAxiom]

equivalenceAxiom = namePredicate equivalenceLaw "equivalence"

implicationAxiom = namePredicate implicationLaw "implication"

doubleNegationAxiom = namePredicate doubleNegationLaw "doubleNegation"

idempotentAndAxiom = namePredicate idempotentAndLaw "idempotentAnd"

idempotentOrAxiom = namePredicate idempotentOrLaw "idempotentOr"

commutativeAndAxiom = namePredicate commutativeAndLaw "commutativeAnd"

commutativeOrAxiom = namePredicate commutativeOrLaw "commutativeOr"

associativeAndAxiom = namePredicate associativeAndLaw "associativeAnd"

associativeOrAxiom = namePredicate associativeOrLaw "associativeOr"

distributiveAndAxiom = namePredicate distributiveAndLaw "distributiveAnd"

distributiveOrAxiom = namePredicate distributiveOrLaw "distributiveOr"

deMorgansAndAxiom = namePredicate deMorgansAndLaw "deMorgansAnd"

deMorgansOrAxiom = namePredicate deMorgansOrLaw "deMorgansOr"

identityAndAxiom = namePredicate identityAndLaw "identityAnd"

identityOrAxiom = namePredicate identityOrLaw "identityOr"

annihilationAndAxiom = namePredicate annihilationAndLaw "annihilationAnd"

annihilationOrAxiom = namePredicate annihilationOrLaw "annihilationOr"

inverseAndAxiom = namePredicate inverseAndLaw "inverseAnd"

inverseOrAxiom = namePredicate inverseOrLaw "inverseOr"

absorptionAndAxiom = namePredicate absorptionAndLaw "absorptionAnd"

absorptionOrAxiom = namePredicate absorptionOrLaw "absorptionOr"

deMorgansForallAxiom = namePredicate deMorgansForallLaw "deMorgansForall"

deMorgansExistsAxiom = namePredicate deMorgansExistsLaw "deMorgansExists"

swapForallAxiom = namePredicate swapForallLaw "swapForall"

swapExistsAxiom = namePredicate swapExistsLaw "swapExists"


