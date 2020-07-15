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

{- ---------- Building Set Expressions ----------- -}
{- TODO: these should be in Axioms.Set -}
emptySet :: Expression
emptySet = namedExp $ constN "0"

isASet :: PName -> Predicate
isASet n = typedExpP (namedExp n) AbstractSetT

intersection, union, subset, equalSet, symDiff, diff, cross :: Expression -> Expression -> Expression
intersection a b = ExpF "setIntersection" [a,b]
union a b = ExpF "setUnion" [a,b]
subset a b = ExpF "setSubset" [a,b]
equalSet a b = ExpF "setEqual" [a,b]
symDiff a b = ExpF "setSymmetricDifference" [a,b]
diff a b = ExpF "setDifference" [a,b]
cross a b = ExpF "setCrossProduct" [a,b]

complement :: Expression -> Expression
complement a = ExpF "setComplement" [a]

inSet :: Expression -> Expression -> Expression
inSet e se = ExpF "setElem" [e,se]



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

{- ---------- Examples ---------- -}

-- definition of subset
subsetDefn :: Predicate
-- note: we will need extra predicates to make this useful
-- e.g. setA is a Set, setB is a Set,
-- then these imply that setA `subset` setB has type PredicateT (Bool)
-- A logic law will involve matching at least one, but maybe more, predicates
-- e.g. to use subsetDefn we need to match A is a Set, B is a Set, A subset B
subsetDefn = iffP (expP $ (setA `subset` setB))
                  (forall_ nameX ((expP $ inSet varX setA) `impP` (expP $ inSet varX setB)))
    where setA = namedExp $ varN "A"
          setB = namedExp $ varN "B"

          nameX = varN "x"
          varX = namedExp nameX

setEqDefn :: Predicate
setEqDefn = iffP (expP $ (setA `equalSet` setB))
                 (andP (expP $ (setA `subset` setB))
                       (expP $ (setB `subset` setA)))
    where setA = namedExp $ varN "A"
          setB = namedExp $ varN "B"

{- ------ Examples of set proofs we should be able to do -------- -}
{-
Finite Sets
How to define a finite set
A is a finite set <-> exists n s.t. n in Z+. exists x1,...,xn. forall y. y \in A -> y = x1 | y = x2 | ... | y = xn
A is a finite set <-> exists n s.t. n in Z+. exists x1,...,xn s.t. xi's are distinct. A = { x1,...,xn }

Need special sets Z, Z+, Z+\{0}, Z_n = [0...n-1], [1..n] for arbitrary n
Need to be able to index variables by these sets x_Z represents x_i for i \in Z
Predicate bindings need to take x_Z rather than single x
But we need to be able to refer to an individual variable in x_Z, e.g. x_1

Then { x1,...,xn } can just be a function {}(x*Zn+1) say

We will need x_(1,2), x_(1,2,3) etc

So a variable has a name x,y, etc, and an index which is an expression
We also have variable sets and a name and a set of indexes

If A is a set and B is a finite set and A \subseteq B, then A is a finite set


A is a finite set -> A = { x1,...,xn } where xi are distinct

If A,B are finite sets, the A u B is finite


If |A| = n, then |P(A)| = 2^n

If A, B are finite sets, the A \subseteq B -> |A| \le |B|

If A,B are finite sets, then |A u B| = |A| + |B| - |A n B|

If A,B are finite sets and A n B = 0, then |A u B| = |A| + |B|
A = { x1,...,xn } s.t. forall i in [1,n]. forall j in [1,n]. xi = xj -> i=j
B = { y1,...,ym } s.t. forall i in [1,m]. forall j in [1,m]. yi = yj -> i=j
We want to show A u B = { x1,...,xn,y1,...,ym }




axiom :: isAFiniteSet(A) -> \exists n \exists (x1,...,xn) . A = { x1,...,xn }
or
axiom :: isAFiniteSet(A) -> \exists n \exists (x1,...,xn) . forall y. y \in A <-> (y = x1 | y = x2 | ... | y = xn)

maybe instead of types we just have functions e.g. isASet(A), isAFiniteSet(A)

composition of relations is associative


-}