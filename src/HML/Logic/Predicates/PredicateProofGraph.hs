{--
 -- Proofs should be represented as directed graphs, a root node representing the standard axioms etc
 -- keep data about what deduction step was used
 -- add backedges if the deducation step is equivalence etc
 -- Should have a separate data structure (an array) to describe how to display proof
 -- allow printing to HTML, LaTeX, text
 -- allow steps to be hidden or visible etc  
 --}
 {--
 -- PredicateProofs.hs
 -- :l ./HML/Logic/PredicateLogic/PredicateProofs.hs from devel directory
 -- A module for proofs in predicate logic
 --}
module HML.Logic.Predicates.PredicateProofGraph where

{-
 - TODO: Write some helper functions and  instances (e.g. Functor) for the data types
-}

import HML.Logic.Predicates.Predicates
import HML.Logic.Predicates.PredicateCursors
import HML.Utils.Utils

import Data.Graph.Inductive.Graph(mkGraph, insNode, insEdges, ufold, match, (&), lab)
import Data.Graph.Inductive.PatriciaTree(Gr) -- the graph type, implemented as a patricia tree
import Data.Graph.Inductive.Query.DFS(dfs)

import Data.Function(on)
import Data.List(sortBy, nub, null, (\\))
import Data.Maybe(isJust, isNothing, fromJust, catMaybes)
import Control.Monad(mplus)
{-

Proof type

Each node needs an id

Each node represents a result, with a special root node to represent axioms
  -- needs a unique identifier that we use to refer to it
  -- needs a unique int for the graph data type, maybe use this as the identifier
  --   (wont work if we have special root type)
  -- edges linking it to needed results, might be more than one way to derive it
  -- so need a way to label edges
  -- code for the deduction technique used
  -- code if it is -> or <->

Need a focus, separate from the graph

-}
-- should this be in logic laws ?
type NamedPredicate = (String, Predicate)
-- this is currently in PredicateProofs (but should be moved here)
--type NamedPredicate = (String, Predicate)

-- nodes are labelled with Result type, edges labelled with [Int]
-- graph
-- size, the number of nodes which start from 0
-- NOTE: we could replae nextNode with a function in the fgl library
-- that will give a valid new node id
data ProofGraph = ProofGraph { proofGraph :: Gr ProofNode ()
                             , nextNode :: Int }
    deriving (Show)

-- a node is either the root node with the axioms, or a result of a proof step
-- an assumption type, which has deductions = []
data ProofNode = Axiom Result
               | ProofStep Result
    deriving (Show)

-- a result is predicate with a name to identify it
-- and a mapping from Int to a Deduction type
-- the int identifies the edges pointing to the results needed for the deduction
-- NOTE: allow at most one deduction otherwise it creates problems searching through graphs
-- which path should we pick etc if there are multiple
data Result = Result { resultName :: String
                     , resultPredicate :: Predicate
                     , deductions :: [Deduction]
                     , assumptions :: [Int] }
    deriving (Show)

-- Deduction is list of nodes of source predicates and a deduction type
type Deduction = ([Int],DeductionType)

-- hard code the deduction types (I don't think we want this to be extendable, but
-- could add a UserDefined String option
-- need to redo this: DeductionType = DT DeductionName DeductionDirection
-- then have helper functions, rather than use Constructors explicitly
data DeductionType = InstantiateSchema
                   | ModusPonens DeductionDirection
                   | UniversalInstantiation
                   | SplitAnd
                   | LogicLaw [FocusStep]
                   | UniversalGeneralisation
                   | LiftResult
    deriving (Show)

data FocusStep = Transform String
               | Move Direction
    deriving (Show)

-- we need a function DeductionType -> DeductionDirection
data DeductionDirection = DDImp | DDIff
    deriving (Show, Eq)



{- Contructing a proof graph -}

{- ---------- Helper functions for NamedPredicates ---------- -}

namePredicate :: Predicate -> String -> NamedPredicate
namePredicate p s = (s,p)

nameOfPredicate :: NamedPredicate -> String
nameOfPredicate = fst

justPredicate :: NamedPredicate -> Predicate
justPredicate = snd

-- TODO: make a node for each axiom
startProofGraph :: [NamedPredicate] -> ProofGraph
startProofGraph as = ProofGraph { proofGraph = mkGraph aNodes []
                                , nextNode = 1 }
    where aNodes = zip [0,-1..] (map mkAxiom' as)
          mkAxiom' (n,p) = Axiom (Result { resultName = n
                                         , resultPredicate = p
                                         , deductions = []
                                         , assumptions = [] })

getPredicateM :: String -> ProofGraph -> Maybe Predicate
-- getPredicateM n pg returns the predicate named n in pg, if it exists
-- assumes names are unique in graph (enforced by the construction functions)
getPredicateM n pg = ufold getP' Nothing (proofGraph pg)
    where getP' (_,_,pn,_) mp = mp `mplus` lookup n [(nodeName pn, nodePredicate pn)]

addResult :: NamedPredicate -> [String] -> DeductionType -> ProofGraph -> Either String ProofGraph
-- addResult np sns dt pg adds a result to the proof graph
-- assumes: the result is not already in the graph
addResult (n,p) sns dt pg = do -- check name is not in use
                               failOn (isJust $ getNodeN n pg) "Error(addResult): name already in use"
                               -- get source nodes
                               sNodes  <- fromMaybe (sequence $ map (flip getNodeN pg) sns)
                                                    "Error(addResult): unable to find source names"
                               -- get ids of source nodes
                               let sNids = map fst sNodes
                               -- get id for new node
                               let nNode = nextNode pg
                               -- inherit assumptions from source nodes
                               let nAssumptions = inheritAssumptions sNodes
                               -- get new node label
                               let label = ProofStep (Result { resultName = n
                                                             , resultPredicate = p
                                                             , assumptions = nAssumptions
                                                             , deductions = [(sNids,dt)]})
                               -- get the new proof graph
                               let nPG = insEdges (map (\sn -> (nNode, sn, ())) sNids) $
                                            insNode (nNode,label) $ proofGraph pg
                               -- return the new proof graph
                               return (pg { proofGraph = nPG, nextNode = nNode + 1 })

addLiftedResult :: NamedPredicate -> String -> String -> ProofGraph -> Either String ProofGraph
addLiftedResult (n,p) resN assN pg = do -- check name is not in use
                                        failOn (isJust $ getNodeN n pg) "Error(addLiftedResult): name already in use"
                                        -- get node of result to be lifted
                                        resNode <- fromMaybe (getNodeN resN pg)
                                                             "Error(addLiftedResult): unable to find result name"
                                        -- get assumption node
                                        assNode <- fromMaybe (getNodeN assN pg)
                                                             "Error(addLiftedResult): unable to find assumption name"
                                        -- check assNode is an assumption
                                        failOn (not $ isAssumption $ snd assNode)
                                               "Error(addLiftedResult): not lifted over an assumption"
                                        -- check resN depends on assN
                                        failOn (not $ (fst assNode) `elem` nodeAssumptions (snd resNode))
                                               "Error(addLiftedResult): result does not depend on assumption"
                                        -- construct result
                                        -- get id for next node
                                        let nNode = nextNode pg
                                        -- inherit assumptions
                                        let nAssumptions = inheritAssumptions [resNode] \\ [fst assNode]
                                        -- get the source node ids
                                        let sNids = [fst resNode, fst assNode]
                                        -- new node label
                                        let label = ProofStep (Result { resultName = n
                                                                      , resultPredicate = p
                                                                      , assumptions = nAssumptions
                                                                      , deductions = [(sNids,LiftResult)]})
                                        -- get the new proof graph
                                        let nPG = insEdges (map (\sn -> (nNode, sn, ())) sNids) $
                                                     insNode (nNode,label) $ proofGraph pg
                                        -- return the new proof graph
                                        return (pg { proofGraph = nPG, nextNode = nNode + 1 })

addAssumption :: NamedPredicate -> ProofGraph -> Either String ProofGraph
--addAssumption np pg adds the assumption np to the proof graph
addAssumption (n,p) pg = do -- check name is not in use
                            failOn (isJust $ getNodeN n pg) "Error(addAssumption): name already in use"
                            -- check p is not already in graph
                            failOn (isJust $ getNodeP p pg) "Error(addAssumption): predicate already in proof graph"
                            -- get new node id
                            let nNode = nextNode pg
                            -- the label for the new node
                            let label = ProofStep (Result { resultName = n
                                                          , resultPredicate = p
                                                          , assumptions = []
                                                          , deductions = [] })
                            -- return the new proof graph
                            return (pg { proofGraph = insNode (nNode,label) $ proofGraph pg
                                       , nextNode = nNode + 1 })

mergeAssumption :: String -> String -> ProofGraph -> Either String ProofGraph
-- assumes the merge is valid
mergeAssumption an rn pg = do -- get assumption node
                              assNode <- fromMaybe (getNodeN an pg)
                                                   "Error(mergeAssumption): unable to find assumption name"
                              -- check it is an assumption node
                              failOn (not $ isAssumption $ snd assNode)
                                     "Error(mergeAssumption): can only merge assumptions"
                              -- get merging node
                              resNode <- fromMaybe (getNodeN rn pg)
                                                   "Error(mergeAssumption): unable to find result name"
                              -- get context for assumption node
                              (aCon,rest) <- fromMaybe (match' (fst assNode) pg)
                                                       "Error(mergeAssumption): unable to match assumption node"
                              -- get in edges to assumption node
                              let (inNs,_,_,_) = aCon
                              -- redirect edges
                              let nEs = map (\nid -> (nid, fst resNode, ())) (map snd inNs)
                              -- move those edges to point to result
                              let pg' = insEdges nEs rest
                              -- return new proof graph
                              return $ pg { proofGraph = pg' }
    where match' n pg = case (match n (proofGraph pg)) of
                          (Just c,r)  -> Just (c,r)
                          (Nothing,r) -> Nothing
-- Allow merging of an assumption with a result (if they are the same predicate)
-- But do not allow merging in other circumstances
-- We would have to write new deduction functions that use this otherwise
{-
updateResult :: NamedPredicate -> [String] -> DeductionType -> ProofGraph -> Either String ProofGraph
updateResult (n,p) sns dt pg = do -- get node with name n
                                  nNode <- fromMaybe (getNodeN n pg) "Error(updateResult): name is not in proof"
                                  -- get context for the node
                                  (nCon,rest) <- fromMaybe (match' nNode pg) "Error(updateResult):unable to find node"
                                  -- get data from context
                                  let (inE,_,pn,outE) = nCon
                                  -- check predicates match
                                  failOn (p /= nodePredicate pn) "Error(updateResult):predicates do not match"
                                  -- get source nodes
                                  sNodes  <- fromMaybe (sequence $ map (flip getNodeN pg) sns)
                                                       "Error(updateResult): unable to find source names"
                                  -- get updated context
                                  let uCon = (inE  -- the same in edges
                                             ,nNode -- the same node id
                                             ,addDeduction' (sNodes,dt) pn -- add the deduction
                                             , nub $ outE ++ map ((,) ()) sNodes) -- add the new out edges
                                  -- return the new proof graph
                                  return $ pg { proofGraph = uCon & rest }


          addDeduction' d (ProofStep r) = ProofStep (r { deductions = d:(deductions r)})
          addDeduction' d (Axiom r)     = Axiom (r { deductions = d:(deductions r)})
-}

getProofNames :: ProofGraph -> [String]
getProofNames = map (nodeName . snd) . filter (isProofStep . snd) . getProofNodes

getAxiomNames :: ProofGraph -> [String]
getAxiomNames = map (nodeName . snd) . filter (not . isProofStep . snd) . getProofNodes

getProofNodes :: ProofGraph -> [(Int,ProofNode)]
getProofNodes pg = ufold addNL' [] (proofGraph pg)
    where addNL' (_,n,nl,_) nls = (n,nl):nls

isProofStep, isAssumption :: ProofNode -> Bool
isProofStep (ProofStep _) = True
isProofStep _             = False

-- an assumption is a result with no deductions
-- NOTE: deductions could be added later
isAssumption (ProofStep r) = null $ deductions r
isAssumption _             = False

getNodeN :: String -> ProofGraph -> Maybe (Int,ProofNode)
-- getNodeN n pg returns the int id of the n
-- returns Nothing if n cannot be found
-- returns the first found occurrence (but there should only be one)
getNodeN n pg = ufold findN' Nothing (proofGraph pg)
    where findN' (_,nid,pn,_) res = res `mplus` ((nid,pn) `ifM` (n == nodeName pn))

getNodeP :: Predicate -> ProofGraph -> Maybe (Int,ProofNode)
getNodeP p pg = ufold findP' Nothing (proofGraph pg)
    where findP' (_,nid,pn,_) res = res `mplus` ((nid,pn) `ifM` (p == nodePredicate pn))

{- Utility functions -}

nodeName :: ProofNode -> String
nodeName = resultName . getResult

nodePredicate :: ProofNode -> Predicate
nodePredicate = resultPredicate . getResult

nodeAssumptions :: ProofNode -> [Int]
nodeAssumptions = assumptions . getResult

getResult :: ProofNode -> Result
getResult (Axiom r)     = r
getResult (ProofStep r) = r

inheritAssumptions :: [(Int,ProofNode)] -> [Int]
inheritAssumptions = nub . concatMap getAs'
    where getAs' (nid,pn) | isProofStep pn = if isAssumption pn then [nid] else nodeAssumptions pn
                          | otherwise      = []

-- add this to a module of utility functions for whole project
{-
ifM :: a -> Bool -> Maybe a
ifM x True  = Just x
ifM x False = Nothing

failOn :: Bool -> String -> Either String ()
failOn True  str = Left str
failOn False str = Right ()

check :: (a -> Bool) -> String -> Either String a -> Either String a
check cf str ef = do { x <- ef; if cf x then Left str else Right x }

fromMaybe :: Maybe a -> String -> Either String a
fromMaybe (Just a)  str = Right a
fromMaybe (Nothing) str = Left str
-}
{-
We need functions to
- start a proof graph
- add a result (add a node, add edges, update edges)
- add an assumption
- find a result by name
-
- functions for generating new ints, names etc Use a state monad ?
-}

{-
type LNode a = (Int, a)
type LEdge b = (Int, Int, b)

type Adj b = [(b, Node)] -- links to or from a node
type Context a b = (Adj b, Node, a, Adj b)

mkGraph :: [LNode a] -> [LEdge b] -> Gr a b
insNodes :: [LNode a] -> gr a b -> gr a b
insEdges :: [LEdge b] -> gr a b -> gr a b
-}

{- ---------- Data Types ---------- -}

{- OLD DATA TYPES
type ProofPath = [String]

data NamedPredicate = NP String Predicate deriving (Show) -- change to record syntax?

-- TODO: we need a proof step data type, to record the proof steps
-- data ProofStep = PS { sourcesPNs :: [String], deductionType :: String }
-- then a result has a list of ProofSteps
-- What about proof steps like start sub proof, etc

data Result = Result { resultNP :: NamedPredicate
                     , sourcePNs :: [String] -- names of required predicates
                     , deductionType :: String -- the type of deduction used
                     } deriving (Show)

data Proof = Proof { proofName :: String
                   , axioms :: [NamedPredicate]
                   , assumptions :: [NamedPredicate]
                   , results :: [Result]
                   , subProofs :: [Proof] 
                   , focus :: Maybe PredicateCursor
                   , focusName :: Maybe String -- should we record the focus moves, transformations etc
                   } deriving (Show)

-}