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

-- a version of Result for sending as a JSON object
data ResultStr = ResultStr { rsType :: String
                           , rsName :: String
                           , rsPredicate :: Predicate
                           , rsDeductions :: [([String],String)]
                           , rsAssumptions :: [String]
                           }
    deriving (Show)

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

getResultString :: String -> Proof -> Maybe ResultStr
getResultString n prf = do (nid,pn) <- getNodeN n (proofGraph prf)
                           case pn of
                             Axiom r     -> mkResultStr "axiom" r
                             ProofStep r -> mkResultStr "proofstep" r
    where pns = getProofNodes (proofGraph prf)

          mkResultStr t r = do -- get deductions
                               dsStr <- sequence $ map mkDStr (deductions r)
                               -- get assumptions
                               asPN <- sequence $ map (flip lookup pns) (assumptions r)
                               let as = map nodeName asPN
                               -- return ResultStr
                               return $ ResultStr { rsType = t
                                                  , rsName = resultName r
                                                  , rsPredicate = resultPredicate r
                                                  , rsDeductions = dsStr
                                                  , rsAssumptions = as
                                                  }
          mkDStr (rs,dt) = do nsPN <- sequence $ map (flip lookup pns) rs
                              let ns = map nodeName nsPN
                              return (ns, show dt)

assume :: NamedPredicate -> Proof -> Either String Proof
assume np prf = case addAssumption np (proofGraph prf) of
                  Left errMsg -> Left errMsg
                  Right pg     -> Right prf { proofGraph = pg }

getPredicateByNameM :: String -> Proof -> Maybe Predicate
getPredicateByNameM n prf = getPredicateM n (proofGraph prf)

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


modusPonensUnderFA :: String -> [String] -> String -> String -> Proof -> Either String Proof
modusPonensUnderFA n pns pimpqn varn prf = do -- get predicate P
                                              ps <- fromMaybe (sequence $ map (\pn -> getPredicateM pn (proofGraph prf)) pns)
                                                              "Error(modusPonensUnderFA): unable to find predicates"
                                              -- get predicate P -> Q/P <-> Q
                                              pimpq <- fromMaybe (getPredicateM pimpqn (proofGraph prf))
                                                                 "Error(modusPonensUnderFA): unable to find predicate P->Q"
                                              -- check P->Q predicate has the correct form
                                              failOn (not (isFAImp pimpq || isFAIff pimpq))
                                                     "Error(modusPonensUnderFA): P -> Q is not an implication or equivalence"
                                              -- split into imp and iff cases
                                              if isFAImp pimpq then modusPonensUnderFAImp n (pimpqn:pns) False ps pimpq varn prf
                                                               else modusPonensUnderFAIff n (pimpqn:pns) ps pimpq varn prf
    where isFAImp (PBinding (Forall _ _) (PBinary PImp _ _)) = True
          isFAImp _                                          = False

          isFAIff (PBinding (Forall _ _) (PBinary PIff _ _)) = True
          isFAIff _                                          = False

modusPonensUnderFAIff :: String -> [String] -> [Predicate] -> Predicate -> String -> Proof -> Either String Proof
modusPonensUnderFAIff n sns ps piffq varn prf =
        modusPonensUnderFAImp n sns True ps (pimpq piffq) varn prf `eplus` modusPonensUnderFAImp n sns True ps (qimpp piffq) varn prf
                                                                   `eplus` (Left "Error(modusPonenUnderFAIff): unable to apply in either direction")
    where pimpq (PBinding pb (PBinary PIff p q)) = (PBinding pb (PBinary PImp p q))
          qimpp (PBinding pb (PBinary PIff p q)) = (PBinding pb (PBinary PImp q p))

          eplus e@(Left _)  f = f
          eplus e@(Right _) f = e

modusPonensUnderFAImp :: String -> [String] -> Bool -> [Predicate] -> Predicate -> String -> Proof -> Either String Proof
-- we assume there are no patterns in the predicates so we can just check for equality
modusPonensUnderFAImp n sns isIff ps pimpq varn prf = do -- match pimpq to forall x s.t. R(x). P(x) -> Q(x)
                                                         imp <- fromMaybe (bindToForm impForm pimpq)
                                                                          "Error(modusPonensUnderFAImp): unable to bind to forall x s.t. R(x). P(x) -> Q(x)"
                                                         -- get such that predicate from matching
                                                         r <- fromMaybe (getPMatch "R" imp)
                                                                        "Error(modusPonensUnderFAImp): unable to extract R from forall x s.t. R(x). P(x) -> Q(x)"
                                                         -- get P from matching
                                                         p <- fromMaybe (getPMatch "P" imp)
                                                                        "Error(modusPonensUnderFAImp): unable to extract P from forall x s.t. R(x). P(x) -> Q(x)"
                                                         -- get x from matching
                                                         xPN <- fromMaybe (getNMatch "x" imp)
                                                                          "Error(modusPonensUnderFAImp): unable to extract x from forall x s.t. R(x). P(x) -> Q(x)"
                                                         xn <- fromMaybe (case xPN of { PVar n -> Just n; _ -> Nothing })
                                                                         "Error(modusPonensUnderFAImp): invalid form of x in forall x s.t. R(x). P(x) -> Q(x)"
                                                         -- what are we required to satisfy
                                                         let req = if r == PEmpty then p else r `andP` p
                                                         -- rename to new variable
                                                         rsub <- fromMaybe (renameFreeVariable xn varn req)
                                                                           "Error(modusPonensUnderFAImp): variable name already used in forall x s.t. R(x). P(x) -> Q(x)"
                                                         -- can we use ps to satisfy rsub?
                                                         failOn (not $ satisfy ps rsub)
                                                                "Error(modusPonensUnderFAImp): unable to satisfy R(x) & P(x) from forall x s.t. R(x). P(x) -> Q(x)"
                                                         -- get Q from matching
                                                         q <- fromMaybe (getPMatch "Q" imp)
                                                                        "Error(modusPonensUnderFAImp): unable to extract Q(x) from forall x s.t. R(x). P(x) -> Q(x)"
                                                         -- rename to new variable
                                                         qsub <- fromMaybe (renameFreeVariable xn varn q)
                                                                           "Error(modusPonensUnderFAImp): variable name already used in forall x s.t. R(x). P(x) -> Q(x)"
                                                         -- get deduction type
                                                         let dt = ModusPonens (if isIff then DDIff else DDImp)
                                                         -- add the result to the proof graph
                                                         pg <- addResult (n,qsub) sns dt (proofGraph prf)
                                                         -- return the proof
                                                         return $ prf { proofGraph = pg }
    where impForm = forall (patternN "x") (patternP "R") (patternP "P" `impP` patternP "Q")

          satisfy :: [Predicate] -> Predicate -> Bool
          satisfy ps p | p `elem` ps = True
                       | otherwise   = case p of
                                         PBinary op x y -> let bx = satisfy ps x
                                                               by = satisfy ps y
                                                           in evalBOp op bx by
                                         PUnary op x    -> let bx = satisfy ps x
                                                           in evalUOp op bx
                                         _              -> False

          evalBOp PAnd x y = x && y
          evalBOp POr  x y = x || y
          evalBOp PXOr x y = (x && not y) || (not x && y)
          evalBOp PImp x y = not x || y
          evalBOp PIff x y = x == y

          evalUOp PNot x = not x

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

modusPonensGen :: String -> [String] -> String -> Proof -> Either String Proof
-- modusPonens (pns,prf) pn pimpqn tries to apply modus ponens
-- where pn is the name of predicate P, and pimpqn is the name of
-- the predicate P -> Q (or P <-> Q)
-- Do separate functions for using P -> Q and P <-> Q
modusPonensGen n pns pimpqn prf = do -- get predicate P
                                    ps <- fromMaybe (sequence $ map (\pn -> getPredicateM pn (proofGraph prf)) pns)
                                                   "Error(modusPonensGen): unable to find predicates"
                                    -- get predicate P -> Q/P <-> Q
                                    pimpq <- fromMaybe (getPredicateM pimpqn (proofGraph prf))
                                                       "Error(modusPonensGen): unable to find predicate P->Q"
                                    -- check P->Q predicate has the correct form
                                    failOn (not (isImp pimpq || isIff pimpq))
                                           "Error(modusPonensGen): P -> Q is not an implication or equivalence"
                                    -- split into imp and iff cases
                                    if isImp pimpq then modusPonensGenImp n (pimpqn:pns) False ps pimpq prf
                                                   else modusPonensGenIff n (pimpqn:pns) ps pimpq prf
    where isImp (PBinary PImp _ _) = True
          isImp _                  = False

          isIff (PBinary PIff _ _) = True
          isIff _                  = False

modusPonensGenIff :: String -> [String] -> [Predicate] -> Predicate -> Proof -> Either String Proof
modusPonensGenIff n sns ps piffq prf =
        modusPonensGenImp n sns True ps (pimpq piffq) prf `eplus` modusPonensGenImp n sns True ps (qimpp piffq) prf
                                                          `eplus` (Left "Error(modusPonenGenIff): unable to apply in either direction")
    where pimpq (PBinary PIff p q) = PBinary PImp p q
          qimpp (PBinary PIff p q) = PBinary PImp q p

          eplus e@(Left _)  f = f
          eplus e@(Right _) f = e

modusPonensGenImp :: String -> [String] -> Bool -> [Predicate] -> Predicate -> Proof -> Either String Proof
-- we assume there are no patterns in the predicates so we can just check for equality
modusPonensGenImp n sns isIff ps pimpq prf = do -- match pimpq to P -> Q
                                               imp <- fromMaybe (bindToForm impForm pimpq)
                                                                "Error(modusPonensGen): unable to bind P->Q"
                                               -- get P from matching
                                               p <- fromMaybe (getPMatch "P" imp)
                                                              "Error(modusPonensGen): unable to extract P from P -> Q"
                                               -- can we use ps to satisfy p?
                                               failOn (not $ satisfy ps p)
                                                      "Error(modusPonensGen): unable to satisfy P of P -> Q"
                                               -- get Q from matching
                                               q <- fromMaybe (getPMatch "Q" imp)
                                                              "Error(modusPonensGen): unable to extract Q from P -> Q"
                                               -- get deduction type
                                               let dt = ModusPonens (if isIff then DDIff else DDImp)
                                               -- add the result to the proof graph
                                               pg <- addResult (n,q) sns dt (proofGraph prf)
                                               -- return the proof
                                               return $ prf { proofGraph = pg }
    where impForm = patternP "P" `impP` patternP "Q"

          satisfy :: [Predicate] -> Predicate -> Bool
          satisfy ps p | p `elem` ps = True
                       | otherwise   = case p of
                                         PBinary op x y -> let bx = satisfy ps x
                                                               by = satisfy ps y
                                                           in evalBOp op bx by
                                         PUnary op x    -> let bx = satisfy ps x
                                                           in evalUOp op bx
                                         _              -> False

          evalBOp PAnd x y = x && y
          evalBOp POr  x y = x || y
          evalBOp PXOr x y = (x && not y) || (not x && y)
          evalBOp PImp x y = not x || y
          evalBOp PIff x y = x == y

          evalUOp PNot x = not x

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
                                      x <- fromMaybe (case xN of { (PVar n) -> Just n; _ -> Nothing })
                                                     "Error(genInstantiation): error getting bound form of variable"
                                      -- get new predicate
                                      inst <- fromMaybe (if isEmptyP pP
                                                         then apMatchingM faM simpForm
                                                         else apMatchingM faM instForm)
                                                         "Error(genInstantiation): unable to apply matching"
                                      -- rename variables to desired name
                                      instY <- fromMaybe (renameFreeVariable x vn inst)
                                                         "Error(genInstantiation): variable name already in use in predicate"
                                      -- get the new proof graph
                                      pg <- addResult (n,instY) [fan] UniversalInstantiation (proofGraph prf)
                                      -- return the new proof
                                      return $ prf { proofGraph = pg }
    where faForm = forall (patternN "x") (patternP "P") (patternP "Q")
          instForm = (patternP "P") `impP` (patternP "Q")
          simpForm = patternP "Q"

splitAnd :: (String,String) -> String -> Proof -> Either String Proof
splitAnd (pn,qn) andn prf = do -- check it has the right form
                               failOn (pn == qn) "Error(splitAnd): names must be different"
                               -- get predicate to split
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

joinAnd :: String -> (String,String) -> Proof -> Either String Proof
-- | joinAnd n (pn,qn) updates result with new result p&q with name n
joinAnd n (pn,qn) prf = do -- get predicates
                           p <- fromMaybe (getPredicateM pn (proofGraph prf))
                                          "Error(joinAnd): unable to find predicate"
                           q <- fromMaybe (getPredicateM qn (proofGraph prf))
                                          "Error(joinAnd): unable to find predicate"
                           -- add p&q to graph
                           pg <- addResult (n,p `andP` q) [pn,qn] JoinAnd (proofGraph prf)
                           -- return the new proof
                           return $ prf { proofGraph = pg }

joinOr :: String -> String -> Predicate -> Proof -> Either String Proof
-- | joinOr n pn q prf returns new proof with result p | q named n
joinOr n pn q prf = do p <- fromMaybe (getPredicateM pn (proofGraph prf))
                                      "Error(joinOr): unable to find predicate"
                       pg <- addResult (n,p `orP` q) [pn] JoinOr (proofGraph prf)
                       -- return the new proof
                       return $ prf { proofGraph = pg }

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


renameFreeVariableInResult :: String -> String -> String -> String -> Proof -> Either String Proof
renameFreeVariableInResult n pn xn yn prf = do -- get predicate to rename
                                               p <- fromMaybe (getPredicateM pn (proofGraph prf))
                                                              "Error(renameFreeVariableInResult): unable to find predicate"
                                               -- rename the variable
                                               p' <- fromMaybe (renameFreeVariable xn yn p)
                                                               "Error(renameFreeVariableInResult): new variable name already used in predicate"
                                               -- check we have actually renamed something
                                               failOn (p == p')
                                                      "Error(renameFreeVariableInResult): no variable renamed"
                                               -- add the result
                                               pg <- addResult (n,p') [pn] RenameFreeVariable (proofGraph prf)
                                               -- return the new proof
                                               return $ prf { proofGraph = pg }

generaliseWith :: String -> String -> String -> Proof -> Either String Proof
generaliseWith n pn vn prf = do -- get predicate to generalise
                                p <- fromMaybe (getPredicateM pn (proofGraph prf))
                                               "Error(generaliseWith): unable to find predicate"
                                -- check new variable is not bound in predicate -- TODO: is this needed???
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


createSchema :: String -> String -> Proof -> Either String Proof
createSchema n rn prf = do -- get result to use
                           (_,pn) <- fromMaybe (getNodeN rn (proofGraph prf))
                                               "Error(createSchema): unable to find result"
                           -- check it has no assumptions
                           failOn (length (nodeAssumptions pn) > 0)
                                  "Error(createSchema): cannot create schema from result with assumptions"
                           -- get predicate
                           let p = nodePredicate pn
                           -- change var names to patterns
                           let sp = varToPatterns p
                           -- check there were patterns
                           failOn (p == sp) "Error(createSchema): no names to generalise over"
                           -- add the result (TODO: we will need to change this to addSchema when we have figured out how to deal with schemas)
                           pg <- addResult (n,sp) [rn] MakeSchema (proofGraph prf)
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

