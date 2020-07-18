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
module HML.Logic.Predicates.PredicateProofs where

import HML.Logic.Predicates.Predicates
import HML.Logic.Predicates.PredicateCursors
import HML.Logic.Predicates.PredicateMatching
import HML.Logic.Predicates.PredicateLogicLaws
import HML.Logic.Predicates.PredicatesPrettyPrint
import HML.Logic.Predicates.PredicateProofGraph

import HML.Utils.Utils

import Control.Monad(mplus,liftM,liftM2)

import Data.Either()
import Data.Function(on)
import Data.List(intercalate, intersect, sortBy, null)
import Data.Maybe(isNothing, fromJust, isJust)

import Control.Monad(guard, liftM, liftM2)

--import Control.Monad.State

{-
Proofs is a set of axioms T and set of results R (T => R means R are derivable from T)
The axioms include definitions (like defn of a subset)
Need proof techniques that introduce new results (from T or previous results) e.g. P and Q, P, Q
Need subproofs, T+A => B, then return to get T => A -> B for example
    But we might need to go from T => R to T+A => R,B to T => R, A->B
Need to be able to refer the previous statements and the axioms

data Proof = TP [Axiom] [Result] [SubProof]
data SubProof = SP [Assumption] [Result]
   (use arrays or maps instead of lists)
data Axiom = A String [Predicate] [Predicate] 
  (A id ps qs) id is a unique identifier, then if ps \in R, we can add qs to R
  if ps==[] then we have an axiom in the traditional sense, if ps/=[] then we have a logic law, or an inference law
  Note that this definition is one-way, for reversible laws we would need two axioms
Assumption and Result are just Predicates with unique identifiers
SubProofs inherit the axioms and add assumptions, then if we have (PP axs rs [PP as bs]) we get (TP axs (rs++(as->bs)) [SP as bs]) and similar with nested subproofs

We will need a separate module for pretty printing 
Need a context to describe how to show functions and the like
See MathJax for latex in webpages
standalone document class in latex
use a font that supports math symbols

-- TODO: add joinAnd given results P1,P2 get P1 & P2 DONE
--           joinOr given a result P and any predicate Q, get P | Q DONE
--           more general modusPonens given P -> Q and P1,...,Pn DONE
--              check whether P1,...,Pn show that P is true
--           modusPonens under the forall forall x s.t. P(x). Q(x) -> R(x)
--               and P(y) & Q(y), deduce R(y), need to specify a name matching x = y
--           renaming variables DONE
--           create schema, given P return P with variables converted to patterns DONE
-}

{- ---------- Data Types ---------- -}

data Focus = Focus { focus :: PredicateCursor
                   , focusHistory :: [FocusStep]
                   , focusName :: String
                   } deriving (Show)

data Proof = Proof { proofGraph :: ProofGraph
                   , proofFocus :: Maybe Focus
                   -- add in printing information etc
                   } deriving (Show)



{- ---------- Show instances ---------- -}

printProof :: Proof -> String
printProof prf = intercalate "\n" $ (map print' pnsOrd) ++ printF' (proofFocus prf)
    where pns = getProofNodes (proofGraph prf)
          pnsOrd = sortBy (compare `on` fst) (filter (isProofStep . snd) pns)

          print' (nid,Axiom a) = "Axioms..." -- this should not occur
          print' (nid,ProofStep r) = let n = resultName r
                                         p = resultPredicate r
                                         ds = deductions r
                                         as = assumptions r
                                         asStr = if as == [] then "" else "(" ++ (intercalate " " (getNames' as)) ++ ")=> "
                                         psStr = show nid ++ " (" ++ n ++ "): " ++ asStr ++ prettyPrint p
                                         dsStr = if null ds then "Assumed..."
                                                            else intercalate "\n" (map printD' ds)
                                     in psStr ++ "\n" ++ (indent 4 dsStr)

          -- print deduction, need to get names for deduction
          getNames' ns = case sequence $ map (flip lookup pns) ns of
                           Just dns -> map nameOfNode dns
                           Nothing  -> error "Invalid nodes in graph"

          printD' (ns,dt) = show dt ++ ": " ++ intercalate " " (getNames' ns)

          printF' (Nothing) = []
          printF' (Just f)  = ["FOCUS: " ++ prettyPrintPC (focus f)]

indent :: Int -> String -> String
indent n str = sps ++ indent' str
    where sps = take n $ repeat ' '

          indent' []     = []
          indent' (c:cs) = if c == '\n' then (c:sps) ++ indent' cs
                                        else c:(indent' cs)

{- ---------- Creating new proofs and sub proofs ---------- -}

startProof :: [AxiomSchema] -> Proof
startProof axs = Proof { proofGraph = startProofGraph axs, proofFocus = Nothing }

namesInProof :: Proof -> [String]
-- returns the names used in the proof
namesInProof = getProofNames . proofGraph

axiomsInProof :: Proof -> [String]
axiomsInProof = getAxiomNames . proofGraph


--getNamedPredicate :: String -> Proof -> Maybe Predicate
--getNamedPredicate n prf = do (nid,pn) <- getNodeN n (proofGraph prf)
--                             return $ nodePredicate pn

--getPredicateByNameM :: String -> Proof -> Maybe Predicate
--getPredicateByNameM n prf = getPredicateM n (proofGraph prf)

{- Deduction Steps -}

assume :: NamedPredicate -> Proof -> Either String Proof
assume np prf = case addAssumption np (proofGraph prf) of
                  Left errMsg -> Left errMsg
                  Right pg    -> Right prf { proofGraph = pg }

instantiateSchema :: String -> String -> PredicateMatching -> Proof -> Either String Proof
--Don't allow new variable names to appear in the schema (we could allow them
--to be the same if they are bound but it would get confusing)
instantiateSchema n sn pmat prf = do -- get schema
                                     as <- fromMaybe (getSchemaByName sn (proofGraph prf))
                                                     "Error(instantiateSchema): unable to find schema"
                                     -- check schema is of the right form
                                     failOn (not $ isPredicateSchema as)
                                            "Error(instantiateSchema): can only instantiate predicate schemas"
                                     -- get predicate of schema
                                     p <- fromMaybe (predicateOfSchema as)
                                                    "Error(instantiateSchema): unable to get predicate from schema"
                                     -- get variable names in schema
                                     let pVars = maybe [] id (mapM variableString (getVariables p))
                                     -- get variable names in matching
                                     let mVars = maybe [] id (mapM variableString $ concatMap (getVariables . (PExp . ExpN . Var) . snd) (variablePatterns pmat))
                                     -- check there are no overlapping variable names
                                     failOn (pVars `intersect` mVars /= [])
                                            "Error(instantiateSchema): overlapping variable names"
                                     -- apply matching
                                     inst <- fromMaybe (apMatchingM pmat p)
                                                       "Error(instantiateSchema): unable to apply matching to schema"
                                     -- get new proof graph
                                     pg <- addResult (n,inst) [sn] InstantiateSchema (proofGraph prf)
                                     -- add result to proof
                                     return $ prf { proofGraph = pg }

-- NOTE: sequence $ map can be replaced by mapM
modusPonensUnderFA :: String -> [String] -> String -> String -> Proof -> Either String Proof
modusPonensUnderFA n pns pimpqn varn prf =
        do -- get predicate P
           rs <- fromMaybe (sequence $ map (\pn -> getResultByName pn (proofGraph prf)) pns)
                           "Error(modusPonensUnderFA): unable to find predicates"
           let ps = map resultPredicate rs
           -- get predicate P -> Q/P <-> Q
           pimpqR <- fromMaybe (getResultByName pimpqn (proofGraph prf))
                               "Error(modusPonensUnderFA): unable to find predicate P->Q"
           let pimpq = resultPredicate pimpqR
           -- check P->Q predicate has the correct form
           failOn (not (isFAImp pimpq || isFAIff pimpq))
                  "Error(modusPonensUnderFA): P -> Q is not an implication or equivalence"
           -- split into imp and iff cases
           if isFAImp pimpq then modusPonensUnderFAImp n (pimpqn:pns) False ps pimpq varn prf
                            else modusPonensUnderFAIff n (pimpqn:pns) ps pimpq varn prf
    where isFAImp (PBinding Forall _ (PImp _ _)) = True
          isFAImp _                              = False

          isFAIff (PBinding Forall _ (PIff _ _)) = True
          isFAIff _                              = False

modusPonensUnderFAIff :: String -> [String] -> [Predicate] -> Predicate -> String -> Proof -> Either String Proof
modusPonensUnderFAIff n sns ps piffq varn prf =
        modusPonensUnderFAImp n sns True ps (pimpq piffq) varn prf `eplus` modusPonensUnderFAImp n sns True ps (qimpp piffq) varn prf
                                                                   `eplus` (Left "Error(modusPonenUnderFAIff): unable to apply in either direction")
    where pimpq (PBinding Forall v (PIff p q)) = (PBinding Forall v (PImp p q))
          qimpp (PBinding Forall v (PIff p q)) = (PBinding Forall v (PImp q p))

          eplus e@(Left _)  f = f
          eplus e@(Right _) f = e

modusPonensUnderFAImp :: String -> [String] -> Bool -> [Predicate] -> Predicate -> String -> Proof -> Either String Proof
-- we assume there are no patterns in the predicates so we can just check for equality
modusPonensUnderFAImp n sns isIff ps pimpq nvar prf =
        do -- match pimpq to forall x. P(x) -> Q(x)
           impM <- fromMaybe (bindToForm impForm pimpq)
                             "Error(modusPonensUnderFAImp): unable to bind to forall x. P(x) -> Q(x)"
           -- get P from matching
           p <- fromMaybe (getPMatch "P" impM)
                          "Error(modusPonensUnderFAImp): unable to extract P from forall x. P(x) -> Q(x)"
           -- get x from matching
           xv <- fromMaybe (getVMatch "x" impM)
                           "Error(modusPonensUnderFAImp): unable to extract x from forall x. P(x) -> Q(x)"
           xStr <- fromMaybe (variableString xv)
                  "Error(modusPonensUnderFAImp): invalid form of x in forall x. P(x) -> Q(x)"
           -- rename to new variable
           psub <- fromMaybe (renameFreeVariable xStr nvar p)
                             "Error(modusPonensUnderFAImp): variable name already used in P(x) of forall x. P(x) -> Q(x)"
           -- can we use ps to satisfy psub?
           failOn (maybe True not (satisfyM ps psub))
                  "Error(modusPonensUnderFAImp): unable to satisfy P(x) from forall x. P(x) -> Q(x)"
           -- get Q from matching
           q <- fromMaybe (getPMatch "Q" impM)
                "Error(modusPonensUnderFAImp): unable to extract Q(x) from forall x. P(x) -> Q(x)"
           -- rename to new variable
           qsub <- fromMaybe (renameFreeVariable xStr nvar q)
                             "Error(modusPonensUnderFAImp): variable name already used in Q(x) of forall x. P(x) -> Q(x)"
           -- get deduction type
           let dt = ModusPonens (if isIff then DDIff else DDImp)
           -- add the result to the proof graph
           pg <- addResult (n,qsub) sns dt (proofGraph prf)
           -- return the proof
           return $ prf { proofGraph = pg }
    where impForm = PBinding Forall (VPatVar "x") (PImp (PPatVar "P") (PPatVar "Q"))

          satisfyM :: [Predicate] -> Predicate -> Maybe Bool
          satisfyM ps p | p `elem` ps = Just True
                        | otherwise   = case p of
                                          PAnd x y -> liftM2 (&&) (satisfyM ps x) (satisfyM ps y)
                                          POr  x y -> case (satisfyM ps x, satisfyM ps y) of
                                                        (Just True,  _         ) -> Just True
                                                        (_         , Just True ) -> Just True
                                                        (Just False, Just False) -> Just False
                                                        _                        -> Nothing
                                          PImp x y -> case (satisfyM ps x, satisfyM ps y) of
                                                        (Just True,  Just True ) -> Just True
                                                        (Just False, _         ) -> Just True
                                                        (Just True,  Just False) -> Just False
                                                        _                        -> Nothing
                                          PIff x y -> liftM2 (==) (satisfyM ps x) (satisfyM ps y)
                                          PNot x   -> liftM not (satisfyM ps x)
                                          _        -> Nothing

{-
modusPonens :: String -> String -> String -> Proof -> Either String Proof
-- modusPonens (pns,prf) pn pimpqn tries to apply modus ponens
-- where pn is the name of predicate P, and pimpqn is the name of
-- the predicate P -> Q (or P <-> Q)
-- Do separate functions for using P -> Q and P <-> Q
modusPonens n pn pimpqn prf = do -- get predicate P
                                 p <- fromMaybe (getPredicateM pn (proofGraph prf))
                                                "Error(modusPonens): unable to find predicate P"
                                 -- get predicate P -> Q/P <-> Q
                                 pimpq <- fromMaybe (getPredicateM pimpqn (proofGraph prf))
                                                    "Error(modusPonens): unable to find predicate P->Q"
                                 -- check P->Q predicate has the correct form
                                 failOn (not (isImp pimpq || isIff pimpq))
                                        "Error(modusPonens): P -> Q is not an implication or equivalence"
                                 -- split into imp and iff cases
                                 if isImp pimpq then modusPonensImp n [pn,pimpqn] False p pimpq prf
                                                else modusPonensIff n [pn,pimpqn] p pimpq prf
    where isImp (PBinary PImp _ _) = True
          isImp _                  = False

          isIff (PBinary PIff _ _) = True
          isIff _                  = False

-- given p <-> q we try p -> q first, then q -> p
-- and return the first that succeeds, or Nothing if neither succeed
modusPonensIff :: String -> [String] -> Predicate -> Predicate -> Proof -> Either String Proof
modusPonensIff n sns p piffq prf =
        modusPonensImp n sns True p (pimpq piffq) prf `eplus` modusPonensImp n sns True p (qimpp piffq) prf
                                                      `eplus` (Left "Error(modusPonenIff): unable to apply in either direction")
    where pimpq (PBinary PIff p q) = PBinary PImp p q
          qimpp (PBinary PIff p q) = PBinary PImp q p

          eplus e@(Left _)  f = f
          eplus e@(Right _) f = e

-- NOTE: I think this is too general, we should just check whether p in pimpq is equal to p (not whether it can be bound)
-- we can use the focus to more general transformations
modusPonensImp :: String -> [String] -> Bool -> Predicate -> Predicate -> Proof -> Either String Proof
modusPonensImp n sns isIff p pimpq prf = do -- match pimpq to P -> Q
                                            imp <- fromMaybe (bindToForm impForm pimpq)
                                                             "Error(modusPonensImp): unable to bind P->Q"
                                            -- get P from matching
                                            pForm <- fromMaybe (getPMatch "P" imp)
                                                               "Error(modusPonensImp): unable to extract P from P -> Q"
                                            -- get Q from matching
                                            qForm <- fromMaybe (getPMatch "Q" imp)
                                                               "Error(modusPonensImp): unable to extract Q from P -> Q"
                                            -- match p to P
                                            pM <- fromMaybe (bindToForm pForm p)
                                                            "Error(modusPonensImp): unable to bind P"
                                            -- apply matching to qForm
                                            q <- fromMaybe (apMatchingM pM qForm)
                                                           "Error(modusPonensImp): unable to apply matching of P"
                                            -- get deduction type
                                            let dt = ModusPonens (if isIff then DDIff else DDImp)
                                            -- add the result to the proof graph
                                            pg <- addResult (n,q) sns dt (proofGraph prf)
                                            -- return the proof
                                            return $ prf { proofGraph = pg }

    where impForm = patternP "P" `impP` patternP "Q"
-}

modusPonensGen :: String -> [String] -> String -> Proof -> Either String Proof
-- modusPonens n pns pimpqn prf tries to apply modus ponens
-- where pns are names of predicates to satisfy P, and pimpqn is the name of
-- the predicate P -> Q (or P <-> Q)
modusPonensGen n pns pimpqn prf = do -- get predicates for P
                                    rs <- fromMaybe (sequence $ map (flip getResultByName (proofGraph prf)) pns)
                                                    "Error(modusPonensGen): unable to find predicates"
                                    let ps = map resultPredicate rs
                                    -- get predicate P -> Q/P <-> Q
                                    pimpqR <- fromMaybe (getResultByName pimpqn (proofGraph prf))
                                                        "Error(modusPonensGen): unable to find predicate P->Q"
                                    let pimpq = resultPredicate pimpqR
                                    -- check P->Q predicate has the correct form
                                    failOn (not (isImp pimpq || isIff pimpq))
                                           "Error(modusPonensGen): P -> Q is not an implication or equivalence"
                                    -- split into imp and iff cases
                                    if isImp pimpq then modusPonensGenImp n (pimpqn:pns) False ps pimpq prf
                                                   else modusPonensGenIff n (pimpqn:pns) ps pimpq prf
    where isImp (PImp _ _) = True
          isImp _          = False

          isIff (PIff _ _) = True
          isIff _          = False

modusPonensGenIff :: String -> [String] -> [Predicate] -> Predicate -> Proof -> Either String Proof
modusPonensGenIff n sns ps piffq prf =
        modusPonensGenImp n sns True ps (pimpq piffq) prf `eplus` modusPonensGenImp n sns True ps (qimpp piffq) prf
                                                          `eplus` (Left "Error(modusPonenGenIff): unable to apply in either direction")
    where pimpq (PIff p q) = PImp p q
          qimpp (PIff p q) = PImp q p

          eplus e@(Left _)  f = f
          eplus e@(Right _) f = e

modusPonensGenImp :: String -> [String] -> Bool -> [Predicate] -> Predicate -> Proof -> Either String Proof
-- we assume there are no patterns in the predicates so we can just check for equality
modusPonensGenImp n sns isIff ps pimpq prf = do -- match pimpq to P -> Q
                                               impM <- fromMaybe (bindToForm impForm pimpq)
                                                                "Error(modusPonensGen): unable to bind P->Q"
                                               -- get P from matching
                                               p <- fromMaybe (getPMatch "P" impM)
                                                              "Error(modusPonensGen): unable to extract P from P -> Q"
                                               -- can we use ps to satisfy p?
                                               failOn (maybe True not (satisfyM ps p))
                                                      "Error(modusPonensGen): unable to satisfy P of P -> Q"
                                               -- get Q from matching
                                               q <- fromMaybe (getPMatch "Q" impM)
                                                              "Error(modusPonensGen): unable to extract Q from P -> Q"
                                               -- get deduction type
                                               let dt = ModusPonens (if isIff then DDIff else DDImp)
                                               -- add the result to the proof graph
                                               pg <- addResult (n,q) sns dt (proofGraph prf)
                                               -- return the proof
                                               return $ prf { proofGraph = pg }
    where impForm = PImp (PPatVar "P") (PPatVar "Q")

          satisfyM :: [Predicate] -> Predicate -> Maybe Bool
          satisfyM ps p | p `elem` ps = Just True
                        | otherwise   = case p of
                                          PAnd x y -> liftM2 (&&) (satisfyM ps x) (satisfyM ps y)
                                          POr  x y -> case (satisfyM ps x, satisfyM ps y) of
                                                        (Just True,  _         ) -> Just True
                                                        (_         , Just True ) -> Just True
                                                        (Just False, Just False) -> Just False
                                                        _                        -> Nothing
                                          PImp x y -> case (satisfyM ps x, satisfyM ps y) of
                                                        (Just True,  Just True ) -> Just True
                                                        (Just False, _         ) -> Just True
                                                        (Just True,  Just False) -> Just False
                                                        _                        -> Nothing
                                          PIff x y -> liftM2 (==) (satisfyM ps x) (satisfyM ps y)
                                          PNot x   -> liftM not (satisfyM ps x)
                                          _        -> Nothing

-- TODO: from here
instantiateAt :: String -> String -> String -> Proof -> Either String Proof
-- instantiateAt (pp,prf) fan vn instantiates a predicate of
-- the form forall x. P(x) at vn (to P(vn))
instantiateAt n fan vn prf = do -- get the predicate to instantiate
                                faR <- fromMaybe (getResultByName fan (proofGraph prf))
                                                "Error(instantiateAt): cannot find predicate to instantiate"
                                let fa = resultPredicate faR
                                -- check it has the right form
                                failOn (not $ isFA fa) "Error(instantiateAt): predicate cannot be instantiated"
                                -- instantiate
                                genInstantiation n fan vn fa prf
    where isFA (PBinding Forall _ _) = True
          isFA _                     = False

genInstantiation :: String -> String -> String -> Predicate -> Proof -> Either String Proof
genInstantiation n fan vn fa prf =
        do -- bind predicate to forall form
           faM <- fromMaybe (bindToForm faForm fa)
                            "Error(genInstantiation): cannot bind to forall form"
           -- get P from forall x. P
           pP <- fromMaybe (getPMatch "P" faM)
                           "Error(genInstantiation): unable to extract P from forall x. P"
           -- get variable matching
           xv <- fromMaybe (getVMatch "x" faM)
                           "Error(genInstantiation): unable to extract x from forall x. P"
           xStr <- fromMaybe (case xv of { (SimpleVar n) -> Just n; (IndexedVar n _) -> Just n; _ -> Nothing })
                             "Error(genInstantiation): bound variable does not have correct form"
           -- rename variables to desired name
           instY <- fromMaybe (renameFreeVariable xStr vn pP)
                              "Error(genInstantiation): variable name already in use in predicate"
           -- get the new proof graph
           pg <- addResult (n,instY) [fan] UniversalInstantiation (proofGraph prf)
           -- return the new proof
           return $ prf { proofGraph = pg }
    where faForm = PBinding Forall (VPatVar "x") (PPatVar "P")

splitAnd :: (String,String) -> String -> Proof -> Either String Proof
splitAnd (pn,qn) andn prf = do -- check it has the right form
                               failOn (pn == qn) "Error(splitAnd): names must be different"
                               -- get predicate to split
                               andR <- fromMaybe (getResultByName andn (proofGraph prf))
                                                 "Error(splitAnd): unable to find predicate"
                               let andP = resultPredicate andR
                               -- bind to and form
                               andM <- fromMaybe (bindToForm andForm andP)
                                                 "Error(splitAnd): predicate has the wrong form"
                               -- get P from P & Q
                               p <- fromMaybe (getPMatch "P" andM)
                                              "Error(splitAnd): unable to extract P from P & Q"
                               -- get Q from P & Q
                               q <- fromMaybe (getPMatch "Q" andM)
                                              "Error(splitAnd): unable to extract Q from P & Q"
                               -- add p to proof graph
                               pg <- addResult (pn,p) [andn] SplitAnd (proofGraph prf)
                               pg' <- addResult (qn,q) [andn] SplitAnd pg
                               -- return the new proof
                               return $ prf { proofGraph = pg' }
    where andForm = PAnd (PPatVar "P") (PPatVar "Q")

joinAnd :: String -> (String,String) -> Proof -> Either String Proof
-- | joinAnd n (pn,qn) updates result with new result p&q with name n
joinAnd n (pn,qn) prf = do -- get predicates
                           pR <- fromMaybe (getResultByName pn (proofGraph prf))
                                           "Error(joinAnd): unable to find predicate"
                           let pP = resultPredicate pR
                           qR <- fromMaybe (getResultByName qn (proofGraph prf))
                                           "Error(joinAnd): unable to find predicate"
                           let qP = resultPredicate qR
                           -- add p&q to graph
                           pg <- addResult (n,PAnd pP qP) [pn,qn] JoinAnd (proofGraph prf)
                           -- return the new proof
                           return $ prf { proofGraph = pg }

joinOr :: String -> String -> Predicate -> Proof -> Either String Proof
-- | joinOr n pn q prf returns new proof with result p | q named n
joinOr n pn q prf = do pR <- fromMaybe (getResultByName pn (proofGraph prf))
                                       "Error(joinOr): unable to find predicate"
                       let pP = resultPredicate pR
                       -- add the new result
                       pg <- addResult (n,POr pP q) [pn] JoinOr (proofGraph prf)
                       -- return the new proof
                       return $ prf { proofGraph = pg }

focusOn :: String -> Proof -> Either String Proof
focusOn pn prf = do -- get predicate
                    pR <- fromMaybe (getResultByName pn (proofGraph prf))
                                    "Error(focusOn): unable to find predicate"
                    -- set the focus
                    return $ setFocus (pn,resultPredicate pR) prf

setFocus :: NamedPredicate -> Proof -> Proof
-- NOTE: we can always cut a predicate at the root ([])
-- NOTE: over writes current focus
setFocus (n,p) prf = prf { proofFocus = Just $ Focus { focus = cutPredicate p []
                                                     , focusHistory = []
                                                     , focusName = n }}

clearFocus :: Proof -> Proof
clearFocus prf = prf { proofFocus = Nothing }

moveFocus :: [Direction] -> Proof -> Either String Proof
moveFocus ds prf = do -- get the focus
                      f <- fromMaybe (proofFocus prf)
                                     "Error(moveFocus): no focus"
                      -- try to move the focus
                      npc <- fromMaybe (moveCursorM (focus f) ds)
                                       "Error(moveFocus): invalid directions"
                      -- record the steps
                      let fh = focusHistory f ++ map Move ds
                      -- return the new focus
                      return $ prf { proofFocus = Just $ f { focus = npc
                                                           , focusHistory = fh }}

transformFocus :: String  -> Proof -> Either String Proof
transformFocus eqn prf = do -- get predicate
                            eqAS <- fromMaybe (getSchemaByName eqn (proofGraph prf))
                                              "Error(transformFocus): unable to find axiom schema"
                            eqP <- fromMaybe (predicateOfSchema eqAS)
                                             "Error(transformFocus): schema is of the wrong type"
                            -- get focus
                            f <- fromMaybe (proofFocus prf)
                                           "Error(transformFocus): no focus"
                            -- try to apply logic law
                            npc <- fromMaybe (apLogicLawM eqP (focus f))
                                             "Error(transformFocus): unable to apply logic law"
                            -- update the focus history
                            let fh = focusHistory f ++ [Transform eqn]
                            -- update the focus and return
                            return $ prf { proofFocus = Just $ f { focus = npc
                                                                 , focusHistory = fh }}

-- Not sure about this one
renameBoundVariableInFocus :: String -> String -> Proof -> Either String Proof
renameBoundVariableInFocus xn yn prf = do f <- fromMaybe (proofFocus prf)
                                               "Error(renameBoundVariableInFocus): no focus"
                                          -- try to rename variables at the cut
                                          npc <- fromMaybe (renameBoundVariableAtCut xn yn (focus f))
                                                           "Error(renameBoundVariableInFocus): unable to rename variable"
                                          -- update focus
                                          let nf = f { focus = npc }
                                          -- update proof
                                          return $ prf { proofFocus = Just nf }

recordFocus :: String -> Proof -> Either String Proof
-- TODO: need to record the name of the result used in the focus
recordFocus n prf = do -- get the focus
                       f <- fromMaybe (proofFocus prf)
                                      "Error(recordFocus): no focus"
                       -- try to add the result
                       pg <- addResult (n,healPredicate $ focus f)
                                       [focusName f]
                                       (LogicLaw $ focusHistory f)
                                       (proofGraph prf)
                       -- return the new proof graph
                       return $ prf { proofGraph = pg }

generaliseWith :: String -> String -> Variable -> Proof -> Either String Proof
generaliseWith n pn v prf = do -- get predicate to generalise
                                pR <- fromMaybe (getResultByName pn (proofGraph prf))
                                               "Error(generaliseWith): unable to find predicate"
                                -- generalise the predicate
                                let genp = PBinding Forall v (resultPredicate pR)
                                -- add the result
                                pg <- addResult (n,genp) [pn] UniversalGeneralisation (proofGraph prf)
                                -- return the new proof
                                return $ prf { proofGraph = pg }

liftResult :: String -> String -> String -> Proof -> Either String Proof
liftResult n rn an prf = do -- get predicate to lift
                            rR <- fromMaybe (getResultByName rn (proofGraph prf))
                                           "Error(liftResult): unable to find result"
                            -- get assumption for result
                            aR <- fromMaybe (getResultByName an (proofGraph prf))
                                           "Error(liftResult): unable to find assumption"
                            -- add the result to the proof graph (NOTE: addLiftedResult checks that an is an assumption of rn)
                            pg <- addLiftedResult (n,PImp (resultPredicate aR) (resultPredicate rR)) rn an (proofGraph prf)
                            -- return the new proof
                            return $ prf { proofGraph = pg }

-- TODO: we need a separate addSchema function
createSchema :: String -> String -> Proof -> Either String Proof
createSchema n rn prf = do -- get result to use
                           rR <- fromMaybe (getResultByName rn (proofGraph prf))
                                           "Error(createSchema): unable to find result"
                           -- check it has no assumptions
                           failOn (hasAssumptions rR)
                                  "Error(createSchema): cannot create schema from result with assumptions"
                           -- get predicate
                           let rP = resultPredicate rR
                           -- change var names to patterns
                           sp <- fromMaybe (mkPatterns $ resultPredicate rR)
                                           "Error(createSchema): cannot create schema with indexed variables"
                           -- check there were patterns
                           failOn (rP == sp) "Error(createSchema): no names to generalise over"
                           -- add the result (TODO: we will need to change this to addSchema when we have figured out how to deal with schemas)
                           pg <- addResult (n,sp) [rn] MakeSchema (proofGraph prf)
                           -- return the new proof
                           return $ prf { proofGraph = pg }

proveAssumption :: String -> String -> Proof -> Either String Proof
proveAssumption an rn prf = do -- get assumption for to prove
                               aR <- fromMaybe (getResultByName an (proofGraph prf))
                                              "Error(proveAssumption): unable to find assumption"
                               -- get proof of assumption
                               rR <- fromMaybe (getResultByName rn (proofGraph prf))
                                              "Error(proveAssumption): unable to find result"
                               -- check the predicates match
                               failOn (not $ resultPredicate aR == resultPredicate rR)
                                      "Error(proveAssumption): result does not prove assumption"
                               -- update the proof graph
                               pg <- mergeAssumption an rn (proofGraph prf)
                               -- return the new proof
                               return $ prf { proofGraph = pg }

