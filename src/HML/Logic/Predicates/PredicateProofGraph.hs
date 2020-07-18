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

import Data.Graph.Inductive.Graph(mkGraph, insNode, insNodes, insEdges, ufold, match, (&), lab, newNodes, labNodes)
import Data.Graph.Inductive.PatriciaTree(Gr) -- the graph type, implemented as a patricia tree
import Data.Graph.Inductive.Query.DFS(dfs)

import Data.Function(on)
import Data.List(sortBy, nub, null, (\\))
import Data.Maybe(isJust, isNothing, fromJust, catMaybes)
import Control.Monad(mplus, liftM)

{- ----- Data Types ----- -}

type NamedPredicate = (String, Predicate)

type ProofGraph = Gr ProofNode ()

data ProofNode = ProofStep Result | Axiom AxiomSchema
    deriving (Show)

data AxiomSchema = AxiomSchema { schemaName :: String
                               , schemaGroup :: String -- for namespacing
                               , schemaDescription :: String -- how to use the schema
                               , schema :: Schema }
     deriving (Show)

-- this is to allow for other types of schema, e.g. ones based on functions
-- a + b = c (where c is the evaluation of a + b)
data Schema = PredicateSchema Predicate
     deriving (Show)

data Result = Result { resultName :: String
                     , resultPredicate :: Predicate
                     , deductions :: [Deduction]
                     , assumptions :: [Int] }
    deriving (Show)

-- a version of Result for sending as a JSON object
data ResultStr = ResultStr { rsName :: String
                           , rsPredicate :: Predicate
                           , rsDeductions :: [([String],String)]
                           , rsAssumptions :: [String]
                           }
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
                   | JoinAnd
                   | JoinOr
                   | RenameFreeVariable
                   | MakeSchema
    deriving (Show)

data FocusStep = Transform String
               | Move Direction
    deriving (Show)

-- we need a function DeductionType -> DeductionDirection
data DeductionDirection = DDImp | DDIff
    deriving (Show, Eq)

{- ----- Querying proof graphs ----- -}

getProofNames :: ProofGraph -> [String]
getProofNames = map (nameOfNode . snd) . filter (isProofStep . snd) . getProofNodes

getAxiomNames :: ProofGraph -> [String]
getAxiomNames = map (nameOfNode . snd) . filter (not . isProofStep . snd) . getProofNodes

isProofStep :: ProofNode -> Bool
isProofStep (ProofStep _) = True
isProofStep (Axiom _)     = False

getResultByName :: String -> ProofGraph -> Maybe Result
getResultByName n pg = do pn <- getNodeByName n pg
                          case pn of
                            (_,ProofStep r) -> Just r
                            (_,Axiom _)     -> Nothing

getSchemaByName :: String -> ProofGraph -> Maybe AxiomSchema
getSchemaByName n pg = do pn <- getNodeByName n pg
                          case pn of
                            (_,ProofStep _) -> Nothing
                            (_,Axiom as)    -> Just as

isPredicateSchema :: AxiomSchema -> Bool
isPredicateSchema as = case schema as of
                         PredicateSchema _ -> True
--                         _                 -> False

predicateOfSchema :: AxiomSchema -> Maybe Predicate
predicateOfSchema as = case schema as of
                         PredicateSchema p -> Just p

hasAssumptions :: Result -> Bool
hasAssumptions = not . null . assumptions

{--
getPredicateM :: String -> ProofGraph -> Maybe Predicate
-- getPredicateM n pg returns the predicate named n in pg, if it exists
-- assumes names are unique in graph (enforced by the construction functions)
getPredicateM n pg = getResultM n pg >>= \r -> return $ resultPredicate r
-}

isAssumption :: Result -> Bool
isAssumption = null . deductions

mkResultStr :: ProofGraph -> Result -> ResultStr
mkResultStr pg r = ResultStr { rsName = resultName r
                             , rsPredicate = resultPredicate r
                             , rsDeductions = maybe [(["error"],"error")] id (sequence $ map mkDStr (deductions r))
                             , rsAssumptions = maybe ["error"] id asM }
    where pns = getProofNodes pg

          asM = do asPN <- sequence $ map (flip lookup pns) (assumptions r)
                   return $ map nameOfNode asPN

          mkDStr (rs,dt) = do nsPN <- sequence $ map (flip lookup pns) rs
                              let ns = map nameOfNode nsPN
                              return (ns, show dt)

{- ----- Contructing proof graphs ----- -}

-- TODO: make a node for each axiom
startProofGraph :: [AxiomSchema] -> ProofGraph
startProofGraph as = insNodes (zip [0..] $ map Axiom as) (mkGraph [] [])

addResult :: NamedPredicate -> [String] -> DeductionType -> ProofGraph -> Either String ProofGraph
-- addResult np sns dt pg adds a result to the proof graph
-- assumes: the result is not already in the graph
addResult (n,p) sns dt pg = do -- check name is not in use
                               failOn (isJust $ getNodeByName n pg) "Error(addResult): name already in use"
                               -- get source nodes
                               sNodes  <- fromMaybe (sequence $ map (flip getNodeByName pg) sns)
                                                    "Error(addResult): unable to find source names"
                               -- get ids of source nodes
                               let sNids = map fst sNodes
                               -- get id for new node
                               let nNode = head $ newNodes 1 pg
                               -- inherit assumptions from source nodes
                               let nAssumptions = inheritAssumptions sNodes
                               -- get new node label
                               let label = ProofStep (Result { resultName = n
                                                             , resultPredicate = p
                                                             , assumptions = nAssumptions
                                                             , deductions = [(sNids,dt)]})
                               -- get the new proof graph
                               let nPG = insEdges (map (\sn -> (nNode, sn, ())) sNids) $
                                            insNode (nNode,label) pg
                               -- return the new proof graph
                               return nPG

addLiftedResult :: NamedPredicate -> String -> String -> ProofGraph -> Either String ProofGraph
-- addLiftedResult np resN assN pg adds the result np which the obtained by lifting resN by assN
addLiftedResult (n,p) resN assN pg = do -- check name is not in use
                                        failOn (isJust $ getNodeByName n pg) "Error(addLiftedResult): name already in use"
                                        -- get node of result to be lifted
                                        resNode <- fromMaybe (getNodeByName resN pg)
                                                             "Error(addLiftedResult): unable to find result name"
                                        -- get assumption node
                                        assNode <- fromMaybe (getNodeByName assN pg)
                                                             "Error(addLiftedResult): unable to find assumption name"
                                        -- check assNode is an assumption
                                        failOn (case snd assNode of { ProofStep r -> not $ isAssumption r; Axiom _ -> True })
                                               "Error(addLiftedResult): not lifted over an assumption"
                                        -- check resN depends on assN
                                        failOn (not $ (fst assNode) `elem` nodeAssumptions (snd resNode))
                                               "Error(addLiftedResult): result does not depend on assumption"
                                        -- construct result
                                        -- get id for next node
                                        let nNode = head $ newNodes 1 pg
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
                                                     insNode (nNode,label) pg
                                        -- return the new proof graph
                                        return nPG

addAssumption :: NamedPredicate -> ProofGraph -> Either String ProofGraph
--addAssumption np pg adds the assumption np to the proof graph
addAssumption (n,p) pg = do -- check name is not in use
                            failOn (isJust $ getNodeByName n pg) "Error(addAssumption): name already in use"
                            -- check p is not already in graph?
                            --failOn (isJust $ getResultByPredicate p pg) "Error(addAssumption): predicate already in proof graph"
                            -- get new node id
                            let nNode = head $ newNodes 1 pg
                            -- the label for the new node
                            let label = ProofStep (Result { resultName = n
                                                          , resultPredicate = p
                                                          , assumptions = []
                                                          , deductions = [] })
                            -- return the new proof graph
                            return (insNode (nNode,label) pg)

mergeAssumption :: String -> String -> ProofGraph -> Either String ProofGraph
-- assumes the merge is valid
mergeAssumption an rn pg = do -- get assumption node
                              assNode <- fromMaybe (getNodeByName an pg)
                                                   "Error(mergeAssumption): unable to find assumption name"
                              -- check it is an assumption node
                              failOn (case snd assNode of { ProofStep r -> not $ isAssumption r; Axiom _ -> True })
                                     "Error(mergeAssumption): can only merge assumptions"
                              -- get merging node
                              resNode <- fromMaybe (getNodeByName rn pg)
                                                   "Error(mergeAssumption): unable to find result name"
                              -- get context for assumption node
                              (aCon,rest) <- fromMaybe (match' (fst assNode) pg)
                                                       "Error(mergeAssumption): unable to match assumption node"
                              -- get in edges to assumption node
                              let (inNs,_,_,_) = aCon
                              -- redirect edges
                              let nEs = map (\nid -> (nid, fst resNode, ())) (map snd inNs)
                              -- return new proof graph
                              return (insEdges nEs rest)
    where match' n pg = case match n pg of
                          (Just c,r)  -> Just (c,r)
                          (Nothing,r) -> Nothing

{- ----- Helper functions ----- -}

getProofNodes :: ProofGraph -> [(Int,ProofNode)]
getProofNodes = labNodes

getNodeByName :: String -> ProofGraph -> Maybe (Int,ProofNode)
-- getNodeByName n pg returns the node with name n from pg
-- returns Nothing if n cannot be found
-- returns the first found occurrence (but there should only be one)
getNodeByName n pg = ufold findN Nothing pg
    where findN (_,nid,pn,_) res = res `mplus` ((nid,pn) `ifM` (nameOfNode pn == n))

getResultByPredicate :: Predicate -> ProofGraph -> Maybe (Int,Result)
getResultByPredicate p pg = ufold findP Nothing pg
    where findP (_,nid,ProofStep r,_) res = res `mplus` ((nid,r) `ifM` (resultPredicate r == p))
          findP (_,nid,Axiom _,_)     res = res

nameOfNode :: ProofNode -> String
nameOfNode (ProofStep r) = resultName r
nameOfNode (Axiom as)    = schemaName as

inheritAssumptions :: [(Int,ProofNode)] -> [Int]
inheritAssumptions = nub . concatMap getAs
    where getAs (nid,ProofStep r) = if isAssumption r then [nid] else assumptions r
          getAs (nid,Axiom _)     = []

nodeAssumptions :: ProofNode -> [Int]
nodeAssumptions (ProofStep r) = assumptions r
nodeAssumptions (Axiom _)     = []

{--


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



{- Utility functions -}

{- ---------- Helper functions for NamedPredicates ---------- -}

namePredicate :: Predicate -> String -> NamedPredicate
namePredicate p s = (s,p)

nameOfPredicate :: NamedPredicate -> String
nameOfPredicate = fst

justPredicate :: NamedPredicate -> Predicate
justPredicate = snd

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

-}
