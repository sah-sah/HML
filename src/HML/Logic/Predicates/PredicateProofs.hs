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
import HML.Logic.Predicates.PredicateProofGraph hiding (proofGraph)

import HML.Utils.Utils

import Control.Monad(mplus,liftM,liftM2)

import Data.Either()
import Data.Function(on)
import Data.List(intercalate, intersect, sortBy, null)
import Data.Maybe(isNothing, fromJust, isJust)

import Control.Monad(guard)

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
                           Just dns -> map nodeName dns
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

{-
{- ---------- Moving through proofs data types ---------- -}

-- NOTE: there are two reasons we could get Nothing, the proof path is incorrect
-- or the passed function returns Nothing
atSubProof' :: ProofPath -> (Proof -> Maybe a) -> Proof -> Maybe a
atSubProof' []     fn prf = Nothing
atSubProof' [n]    fn prf = if n == proofName prf then fn prf else Nothing
atSubProof' (n:ns) fn prf = if n == proofName prf then foldl1 mplus $ map (atSubProof' ns fn) (subProofs prf) else Nothing

untilSubProof' :: ProofPath -> (Proof -> [a]) -> Proof -> [a]
untilSubProof' []     fn prf = []
untilSubProof' [n]    fn prf = if n == proofName prf then fn prf else []
untilSubProof' (n:ns) fn prf = if n == proofName prf then (fn prf) ++ concatMap (untilSubProof' ns fn) (subProofs prf) else [] 

updateSubProof' :: ProofPath -> (Proof -> Maybe Proof) -> Proof -> Maybe Proof
-- returns Nothing if the update fails, returns unchanged proof if the proof path is invalid
updateSubProof' pp fn prf = case update' pp fn prf of
                              (False,_) -> Nothing
                              (True,prf') -> prf'
    where update' []     fn prf = (False,Just prf)
          update' [n]    fn prf = if n == proofName prf then (True,fn prf) else (False,Just prf)
          update' (n:ns) fn prf = if n == proofName prf then let sps = map (update' ns fn) (subProofs prf)
                                                             in (any fst sps 
                                                                ,do sps' <- sequence $ map snd sps
                                                                    return $ prf { subProofs = sps' })
                                                        else (False,Just prf) 
-}
{- ---------- Creating new proofs and sub proofs ---------- -}

startProof :: [NamedPredicate] -> Proof
startProof axs = Proof { proofGraph = startProofGraph axs, proofFocus = Nothing }

namesInProof :: Proof -> [String]
-- returns the names used in the proof
namesInProof = getProofNames . proofGraph

axiomsInProof :: Proof -> [String]
axiomsInProof = getAxiomNames . proofGraph

getNamedPredicate :: String -> Proof -> Maybe Predicate
getNamedPredicate n prf = do (nid,pn) <- getNodeN n (proofGraph prf)
                             return $ nodePredicate pn

assume :: NamedPredicate -> Proof -> Either String Proof
assume np prf = case addAssumption np (proofGraph prf) of
                  Left errMsg -> Left errMsg
                  Right pg     -> Right prf { proofGraph = pg }

{- Deduction Steps -}
instantiateSchema :: String -> String -> PredicateMatching -> Proof -> Either String Proof
--Don't allow new variable names to appear in the schema (we could allow them
--to be the same if they are bound but it would get confusing)
instantiateSchema n sn pmat prf = do -- get schema
                                     p <- fromMaybe (getPredicateM sn (proofGraph prf))
                                                    "Error(instantiateSchema): unable to find schema"
                                     -- get variable names in schema
                                     let pVars = getVariableNames p
                                     -- get variable names in matching
                                     let mVars = concatMap (getVarN' . snd) (namePatterns pmat)
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
    where getVarN' (PVar n) = [n]
          getVarN' _        = []


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

modusPonensImp :: String -> [String] -> Bool -> Predicate -> Predicate -> Proof -> Either String Proof
modusPonensImp n sns isIff p pimpq prf = do -- match pimpq to P -> Q
                                            imp <- fromMaybe (bindToForm impForm pimpq)
                                                             "Error(modusPonensImp): upable to bind P->Q"
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
          pForm   = patternP "P"

instantiateAt :: String -> String -> String -> Proof -> Either String Proof
-- instantiateAt (pp,prf) fan vn instantiates a predicate of
-- the form forall x s.t. P(x). Q(x) at vn (to P(vn) -> Q(vn))
instantiateAt n fan vn prf = do -- get the predicate to instantiate
                                fa <- fromMaybe (getPredicateM fan (proofGraph prf))
                                                "Error(instantiateAt): cannot find predicate to instantiate"
                                -- check it has the right form
                                failOn (not $ isFA fa) "Error(instantiateAt): predicate cannot be instantiated"
                                -- instantiate
                                genInstantiation n fan vn fa prf
    where isFA (PBinding (Forall _ _) _) = True
          isFA _                         = False

genInstantiation :: String -> String -> String -> Predicate -> Proof -> Either String Proof
genInstantiation n fan vn fa prf = do -- bind predicate to forall form
                                      faM <- fromMaybe (bindToForm faForm fa)
                                                       "Error(genInstantiation): cannot bind to forall form"
                                      -- get P from forall x s.t. P. Q
                                      pP <- fromMaybe (getPMatch "P" faM)
                                                      "Error(genInstantiation): unable to extract P from forall x s.t. P. Q"
                                      -- get variable matching
                                      xN <- fromMaybe (getNMatch "x" faM)
                                                      "Error(genInstantiation): unable to extract x from forall x s.t. P. Q"
                                      -- get new predicate
                                      inst <- fromMaybe (if isEmptyP pP
                                                         then apMatchingM faM simpForm
                                                         else apMatchingM faM instForm)
                                                         "Error(genInstantiation): unable to apply matching"
                                      -- rename variables to desired name
                                      let instY = renameFreeVariables (\pn -> if pn==xN then (varN vn) else pn) inst
                                      -- get the new proof graph
                                      pg <- addResult (n,instY) [fan] UniversalInstantiation (proofGraph prf)
                                      -- return the new proof
                                      return $ prf { proofGraph = pg }
    where faForm = forall (patternN "x") (patternP "P") (patternP "Q")
          instForm = (patternP "P") `impP` (patternP "Q")
          simpForm = patternP "Q"

splitAnd :: (String,String) -> String -> Proof -> Either String Proof
splitAnd (pn,qn) andn prf = do -- get predicate to split
                               andP <- fromMaybe (getPredicateM andn (proofGraph prf))
                                                 "Error(splitAnd): unable to find predicate"
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
    where andForm = (patternP "P") `andP` (patternP "Q")

focusOn :: String -> Proof -> Either String Proof
focusOn pn prf = do -- get predicate
                    p <- fromMaybe (getPredicateM pn (proofGraph prf))
                                   "Error(focusOn): unable to find predicate"
                    -- set the focus
                    return $ setFocus (pn,p) prf

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
                            eq <- fromMaybe (getPredicateM eqn (proofGraph prf))
                                            "Error(transformFocus): unable to find predicate"
                            -- get focus
                            f <- fromMaybe (proofFocus prf)
                                           "Error(transformFocus): no focus"
                            -- try to apply logic law
                            npc <- fromMaybe (apLogicLawM eq (focus f))
                                             "Error(transformFocus): unable to apply logic law"
                            -- update the focus history
                            let fh = focusHistory f ++ [Transform eqn]
                            -- update the focus and return
                            return $ prf { proofFocus = Just $ f { focus = npc
                                                                 , focusHistory = fh }}

recordFocus :: String -> Proof -> Either String Proof
-- TODO: need to record the name of the result used in the focus
recordFocus n prf = do -- get the focus
                       f <- fromMaybe (proofFocus prf)
                                      "Error(transformFocus): no focus"
                       -- try to add the result
                       pg <- addResult (n,healPredicate $ focus f)
                                       [focusName f]
                                       (LogicLaw $ focusHistory f)
                                       (proofGraph prf)
                       -- return the new proof graph
                       return $ prf { proofGraph = pg }


generaliseWith :: String -> String -> String -> Proof -> Either String Proof
generaliseWith n pn vn prf = do -- get predicate to generalise
                                p <- fromMaybe (getPredicateM pn (proofGraph prf))
                                               "Error(generaliseWith): unable to find predicate"
                                -- check new variable is not bound in predicate
                                failOn (isBound (varN vn) p)
                                       "Error(generaliseWith): variable cannot be bound in predicate"
                                -- generalise the predicate
                                let genp = forall_ (varN vn) p
                                -- add the result
                                pg <- addResult (n,genp) [pn] UniversalGeneralisation (proofGraph prf)
                                -- return the new proof
                                return $ prf { proofGraph = pg }

liftResult :: String -> String -> String -> Proof -> Either String Proof
liftResult n rn an prf = do -- get predicate to lift
                            r <- fromMaybe (getPredicateM rn (proofGraph prf))
                                           "Error(liftResult): unable to find result"
                            -- get assumption for result
                            a <- fromMaybe (getPredicateM an (proofGraph prf))
                                           "Error(liftResult): unable to find assumption"
                            -- add the result to the proof graph
                            pg <- addLiftedResult (n,a `impP` r) rn an (proofGraph prf)
                            -- return the new proof
                            return $ prf { proofGraph = pg }


proveAssumption :: String -> String -> Proof -> Either String Proof
proveAssumption an rn prf = do -- get assumption for to prove
                               a <- fromMaybe (getPredicateM an (proofGraph prf))
                                              "Error(proveAssumption): unable to find assumption"
                               -- get proof of assumption
                               r <- fromMaybe (getPredicateM rn (proofGraph prf))
                                              "Error(proveAssumption): unable to find result"
                               -- check the predicates match
                               failOn (not $ a == r) "Error(proveAssumption): result does not prove assumption"
                               -- update the proof graph
                               pg <- mergeAssumption an rn (proofGraph prf)
                               -- return the new proof
                               return $ prf { proofGraph = pg }
