{--
 -- PredicateProofs.hs
 -- :l ./HML/Logic/PredicateLogic/PredicateProofs.hs from devel directory
 -- A module for proofs in predicate logic
 --}
module HML.Logic.Predicates.Example where

import HML.Logic.Predicates.Predicates
import HML.Logic.Predicates.PredicateCursors
import HML.Logic.Predicates.PredicateMatching
import HML.Logic.Predicates.PredicateLogicLaws
import HML.Logic.Predicates.PredicatesPrettyPrint
import HML.Logic.Predicates.PredicateProofGraph
import HML.Logic.Predicates.PredicateProofs
import HML.Logic.Predicates.Axioms.Base
import HML.Logic.Predicates.Axioms.Set

import Data.Either(fromRight)
--import Data.List(intercalate, intersect)
--import Control.Monad(mplus,liftM,liftM2)
--import Control.Monad.State


{- ---------- Proof Example ------------ -}

{-
(A \union B) \subset B
=> forall x. x \in (A \union B) -> x \in B -- defn of subset
=> y \in (A \union B) -> y \in B -- universal instantiation
=> forall x. x \in (A \union B) <-> x \in A | x \in B -- defn of union
=> y \in (A \union B) <-> y \in A | y \in B
=> (y \in (A \union B) -> y \in A | y \in B) & (y \in A | y \in B -> y \in (A \union B))
=> y \in A -> y \in A \union B & y \in B -> y \in A \union B
=> 
-}

test1 = startProof (standardAxioms)
test2 = fromRight (error "Step failed") $ assume ("A1",p) test1
    where p = expP $ namedExp $ varN "P"
test3 = fromRight (error "Step failed") $ assume ("A2",q) test2
    where q = expP $ namedExp $ varN "Q"
test4 = fromRight (error "Step failed") $ joinAnd "R1" ("A1","A2") test3
test5 = fromRight (error "Step failed") $ joinOr "R2" "R1" (expP $ namedExp $ varN "R") test4
test6 = fromRight (error "Step failed") $ assume ("A3",(p `orP` q) `impP` r) test5
    where p = expP $ namedExp $ varN "P"
          q = expP $ namedExp $ varN "Q"
          r = expP $ namedExp $ varN "R"
test7 = fromRight (error "Step failed") $ modusPonensGen "R3" ["A1"] "A3" test6
test8 = fromRight (error "Step failed") $ assume ("A4",p) test7
    where p = expP $ namedExp $ varN "x"
test9 = fromRight (error "Step failed") $ renameFreeVariableInResult "R4" "A4" "x" "y" test8
test10 = fromRight (error "Step failed") $ liftResult "R5" "R3" "A3" test9
test11 = fromRight (error "Step failed") $ liftResult "R6" "R5" "A1" test10
test12 = fromRight (error "Step failed") $ createSchema "S1" "R6" test11

-- TODO: need to test rename functions and modus ponens under FA

-- start the proof
egProof = startProof (standardAxioms ++ setAxioms)

-- first we need to start a new subproof for A \union B \subset B -> A \subset B
-- we assume A \union B \subset B
egProof2 = fromRight (error "Step failed") $ assume ("A1",asp) egProof
    where setA = namedExp $ varN "A"
          setB = namedExp $ varN "B"

          asp = expP $ ((setA `union` setB) `subset` setB)

-- get axiom from schema
--TODO: we need to check we are not capturing an names or variables when we 
-- do the substitution
--subset and union axioms should use Expression patterns
--Expression patterns are used where expressions go
-- Need more checking when instantiating a schema
egProof3 = fromRight (error "Step failed") $ instantiateSchema "R1" "subsetAxiom" pm egProof2
    where pm = createMatching [] [("A",setAB),("B",setB)] [("x",varN "x")]

          setA = namedExp $ varN "A"
          setB = namedExp $ varN "B"

          setAB = setA `union` setB


egProof4 = fromRight (error "Step failed") $ modusPonens "R2" "A1" "R1" egProof3

egProof5 = fromRight (error "Step failed") $ instantiateSchema "R3" "unionAxiom" pm egProof4
    where pm = createMatching [] [("A",setA),("B",setB)] [("x",varN "x")]
          setA = namedExp $ varN "A"
          setB = namedExp $ varN "B"


egProof6 = fromRight (error "Step failed") $ instantiateAt "R4" "R2" "y" egProof5

egProof7 = fromRight (error "Step failed") $ instantiateAt "R5" "R3" "y" egProof6

egProof8 = fromRight (error "Step failed") $ modusPonens "R6" "R5" "equivalence" egProof7

egProof9 = fromRight (error "Step failed") $ splitAnd ("R7","R8") "R6" egProof8

egProof10 = fromRight (error "Step failed") $ modusPonens "R9" "R8" "implication" egProof9


egProof11 = fromRight (error "Step failed") $ focusOn "R9" egProof10

egProof12 = fromRight (error "Step failed") $ moveFocus [DLeft] egProof11

egProof13 = fromRight (error "Step failed") $ transformFocus "deMorgansOr" egProof12

egProof14 = fromRight (error "Step failed") $ moveFocus [DUp] egProof13

egProof15 = fromRight (error "Step failed") $ transformFocus "commutativeOr" egProof14
egProof16 = fromRight (error "Step failed") $ transformFocus "distributiveOr" egProof15
egProof17 = fromRight (error "Step failed") $ moveFocus [DLeft] egProof16
egProof18 = fromRight (error "Step failed") $ transformFocus "commutativeOr" egProof17
egProof19 = fromRight (error "Step failed") $ transformFocus "implication" egProof18
egProof20 = fromRight (error "Step failed") $ moveFocus [DUp,DRight] egProof19
egProof21 = fromRight (error "Step failed") $ transformFocus "commutativeOr" egProof20
egProof22 = fromRight (error "Step failed") $ transformFocus "implication" egProof21


egProof23 = fromRight (error "Step failed") $ recordFocus "R10" egProof22

egProof24 = clearFocus egProof23


egProof25 = fromRight (error "Step failed") $ splitAnd ("R11","R12") "R10" egProof24


egProof26 = fromRight (error "Step failed") $ generaliseWith "R13" "R11" "y" egProof25

egProof27 = fromRight (error "Step failed") $ instantiateSchema "R14" "subsetAxiom" pm egProof26
    where pm = createMatching [] [("A",setA),("B",setAB)] [("x",varN "y")]
          setA = namedExp $ varN "A"
          setB = namedExp $ varN "B"
          setAB = setA `union` setB

egProof28 = fromRight (error "Step failed") $ modusPonens "R15" "R13" "R14" egProof27

egProof29 = fromRight (error "Step failed") $ assume ("A2",asp) egProof28
    where setA = namedExp $ varN "A"

          asp = expP $ inSet (namedExp $ varN "y") setA

egProof30 = fromRight (error "Step failed") $ modusPonens "R16" "A2" "R11" egProof29

egProof31 = fromRight (error "Step failed") $ modusPonens "R17" "R16" "R4" egProof30


-- now we need to get out of the subproof

egProof32 = fromRight (error "Step failed") $ liftResult "R18" "R17" "A2" egProof31

egProof33 = fromRight (error "Step failed") $ instantiateSchema "R19" "subsetAxiom" pm egProof32
    where pm = createMatching [] [("A",setA),("B",setB)] [("x",varN "y")]
          setA = namedExp $ varN "A"
          setB = namedExp $ varN "B"

egProof34 = fromRight (error "Step failed") $ generaliseWith "R20" "R18" "y" egProof33

egProof35 = fromRight (error "Step failed") $ modusPonens "R21" "R20" "R19" egProof34

egProof36 = fromRight (error "Step failed") $ liftResult "R22" "R21" "A1" egProof35

egProof37 = fromRight (error "Step failed") $ createSchema "S1" "R22" egProof36
