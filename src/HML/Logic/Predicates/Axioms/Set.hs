{--
 -- Set.hs
 -- Basic axioms derived from the logic laws
 --}
module HML.Logic.Predicates.Axioms.Set where

import HML.Logic.Predicates.Predicates
import HML.Logic.Predicates.PredicateProofGraph

{- ---------- Some set axioms ------------ -}

setAxioms :: [AxiomSchema]
setAxioms = [ subsetAxiom
            , unionAxiom
            , setEqAxiom ]

unionAxiom :: AxiomSchema
unionAxiom = AxiomSchema { schemaName = "unionAxiom"
                         , schemaGroup = "Set"
                         , schemaDescription = ""
                         , schema = PredicateSchema unionSchema }
    where unionSchema = PBinding Forall varX (PIff (PExp $ ExpFn "setElem" [expX,unionAB])
                                                   (POr (PExp $ ExpFn "setElem" [expX,setA])
                                                        (PExp $ ExpFn "setElem" [expX,setB])))

          setA = ExpPatVar "A"
          setB = ExpPatVar "B"
          unionAB = ExpFn "setUnion" [setA,setB]
          
          varX = VPatVar "x"
          expX = ExpN $ Var varX

subsetAxiom :: AxiomSchema
-- TODO: should the variable be a pattern as well?
-- probably not necessary as we can instantiate to a specific variable name
-- but then again, using a pattern allows for more flexibility in naming
subsetAxiom = AxiomSchema { schemaName = "subsetAxiom"
                          , schemaGroup = "Set"
                          , schemaDescription = ""
                          , schema = PredicateSchema subsetSchema }
    where subsetSchema = PIff (PExp $ ExpFn "setSubset" [setA,setB])
                              (PBinding Forall varX (PImp (PExp $ ExpFn "setElem" [expX,setA])
                                                          (PExp $ ExpFn "setElem" [expX,setB])))

          setA = ExpPatVar "A"
          setB = ExpPatVar "B"

          varX = VPatVar "x"
          expX = ExpN $ Var varX

setEqAxiom :: AxiomSchema
setEqAxiom = AxiomSchema { schemaName = "setEqAxiom"
                         , schemaGroup = "Set"
                         , schemaDescription = ""
                         , schema = PredicateSchema setEqSchema }
    where setEqSchema = PIff (PExp $ ExpFn "setEquals" [setA,setB])
                             (PAnd (PExp $ ExpFn "setSubset" [setA,setB])
                                   (PExp $ ExpFn "setSubset" [setB,setA]))

          setA = ExpPatVar "A"
          setB = ExpPatVar "B"

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