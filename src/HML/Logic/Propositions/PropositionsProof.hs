{--
 -- Propositions.hs
 -- :l ./HML/Logic/Propositions.hs from devel directory
 -- A module for propositional logic
 --}
-- TODO: applying the laws of logic to a proposition
-- need to add a cursor to the Proposition
-- so we have a way to move through it
-- TODO: for proofs in more sophisticated domains, need functions that generate axioms
-- e.g. we can have a function (+) that generates axioms of the form (a+b=c), given 
-- inputs a b
-- TODO: we will also need defns, like, if x in Z then what is +
-- we might need to specify that x in (Z,+) etc, or x in (R,+,*)
-- Basic predicate logic should be relatively simple, but then need sophisticated
-- ways to manage definitions and axioms
{-
Split into different modules
-- Basic module
--     Main definition of proposition
--     Useful instances Show, Eq (derived), Functor
--     Truth tables
--     Basic functions: isTautology etc
-- Cursor module
--     Cursor definition
-- LogicLaw module
--     Data definitions and functions etc
-- Proof module
--     For proofs with propositions
-}
module HML.Logic.Propositions.PropositionsProof where

import HML.Logic.Propositions.Propositions
import HML.Logic.Propositions.PropositionsCursor
import HML.Logic.Propositions.PropositionsLogicLaws


import Data.List
import Control.Monad
import Control.Monad.State

{- ---------- Data Types ---------- -}

data ProofStep = PS [Direction] String deriving (Show)
-- PS ds n
-- ds is directions to location to apply logic law
-- n is name of logic law to apply and must correspond to an element of the LawList in 
-- a corresponding proof

data Proof = PF LogicLawList [Proposition] [(ProofStep,Proposition)]
-- PF lls as pss fp
-- lls is list of logic laws available for the proof
-- as is a set of axioms
-- pss is a list of proof steps, paired with the resulting proposition
-- fp is the final proposition

-- fn: logic law from proof

getLogicLaws :: Proof -> LogicLawList
getLogicLaws (PF ll _ _) = ll

{- ---------- Show instances ---------- -}

instance Show Proof where
    show (PF lls as pss) = axStr ++ "\n" ++ stepsStr
        where axStr = concat $ intersperse "\n" $ zipWith (\n a -> "Axiom " ++ show n ++ ": " ++ show a) [1..] as
              stepsStr = concat $ intersperse "\n" $ zipWith (\n (PS ds nll,p) -> show n ++ ": " ++ show p ++ "\t\t\t" ++ nll) [1..] pss
-- TODO: pretty print: determine maximum width of propositions, then pad to put logic law names
-- also use CursorProp to show where the logic law was applied??

{- ---------- Making proofs ---------- -}

startProof :: LogicLawList -> [Proposition] -> Proof
--startProof ps starts a proof with ps as the axioms
startProof lls [] = error "startProof: must have at least one starting proposition"
startProof lls ps = PF lls ps [(PS [] "Combine axioms",foldl1 andP ps)]

step :: [Direction] -> String -> ProofStep
step = PS

stepCP :: CursorProp -> String -> ProofStep
stepCP (CP mt ds st) str = PS ds str

addProofStepM :: Proof -> ProofStep -> Maybe Proof
addProofStepM (PF lls as pss) (PS ds nll) = do let p = snd $ last pss
                                               cp <- cutPropositionM p ds
                                               ll <- lookup nll lls
                                               cp' <- apLogicLawM ll cp
                                               return (PF lls as (pss++[(PS ds nll, healProposition cp')]))

addProofStep pf ps = maybe (error "addProofStep failed") id $ addProofStepM pf ps

currentProp :: Proof -> Proposition
currentProp (PF lls as pss) = if length pss == 0 then foldl1 andP as
                                                 else snd $ last pss

type IProof = StateT (Proof,CursorProp) IO

interactiveProof :: [Proposition] -> IO ((), (Proof,CursorProp))
-- TODO: leave the cursor at the same point after applying a law
--       delete step option
--       better input and output
interactiveProof ps = runStateT interactProof (pf,tp)
    where pf = startProof logicLaws ps
          tp = cutProposition (foldl1 andP ps) []

interactProof :: IProof ()
interactProof = do (pf,cp) <- get
                   liftIO (putStrLn $ show pf)
                   -- read input 
                   runProof
                   -- update state (then continue or exit)

runProof :: IProof ()
runProof = do (pf,cp) <- get
              liftIO $ putStrLn $ "\n" ++ show cp
              liftIO $ putStr ">"
              str <- liftIO getLine
              if str /= [] && head str == 'q' 
                 then return ()
                 else do b <- exeCommand str
                         when (not b) (liftIO (putStrLn "Error: unable to complete command"))
                         runProof
              
exeCommand :: String -> IProof Bool
-- exeCommand str executes the command in str and returns True if it succeeds
-- otherwise does nothing an returns False
exeCommand str = case str of
                     "m: DLeft"  -> moveIP DLeft
                     "m: DRight" -> moveIP DRight
                     "m: DDown"  -> moveIP DDown
                     "m: DUp"    -> moveIP DUp
                     "sp"        -> putProof
                     "lll"       -> putLogicLaws
                     ('a':'p':str) -> apLaw str
                     _           -> return False

apLaw :: String -> IProof Bool
apLaw str = do let ws = words str
               if (length ws > 0) 
                 then (do let law = head ws
                          liftIO $ putStrLn $ "Applying " ++ law ++ "..."
                          (pf,cp) <- get
                          let mpf = addProofStepM pf (stepCP cp law)
                          let ds = getDirections cp
                          case mpf of 
                            Just pf' -> do { put (pf',cutProposition (currentProp pf') ds); return True }
                            Nothing  -> return False)
                 else return False

moveIP :: Direction -> IProof Bool
moveIP d = do (pf,cp) <- get
              let mcp = moveCursorM cp d
              case mcp of
                Just cp' -> do { put (pf,cp'); return True }
                Nothing  -> return False

putProof :: IProof Bool
putProof = do (pf,cp) <- get
              liftIO $ putStrLn $ show pf
              return True

putLogicLaws :: IProof Bool
putLogicLaws = do (pf,cp) <- get
                  liftIO $ putStrLn $ show (map fst $ getLogicLaws pf)
                  return True

exA = [p `orP` (notP q), q `orP` (notP p)]
    where p = varP "p"
          q = varP "q"

exB = [(((p `orP` q) `impP` r) `andP` (p `andP` q)) `impP` r]
    where p = varP "p"
          q = varP "q"
          r = varP "r"

-- equivalent to (p & q) -> r
exC = [p `impP` (q `impP` r)]
    where p = varP "p"
          q = varP "q"
          r = varP "r"

-- equivalent to (~p -> r) & (q -> r)
exD = [(p `impP` q) `impP` r]
    where p = varP "p"
          q = varP "q"
          r = varP "r"

{-
Axiom 1: (((p | q) -> r) & (p & q)) -> r
1: (((p | q) -> r) & (p & q)) -> r			Combine axioms
2: ((~(p | q) | r) & (p & q)) -> r			implication
3: (((~p & ~q) | r) & (p & q)) -> r			deMorgansOr
4: ((r | (~p & ~q)) & (p & q)) -> r			commutativeOr
5: (((r | ~p) & (r | ~q)) & (p & q)) -> r			distributiveOr
6: (((r | ~q) & (r | ~p)) & (p & q)) -> r			commutativeAnd
7: ((((r | ~q) & (r | ~p)) & p) & q) -> r			associativeAnd
8: ((p & ((r | ~q) & (r | ~p))) & q) -> r			commutativeAnd
9: ((((r | ~q) & (r | ~p)) & p) & q) -> r			commutativeAnd
10: (((r | ~q) & ((r | ~p) & p)) & q) -> r			associativeAnd
11: (((r | ~q) & (p & (r | ~p))) & q) -> r			commutativeAnd
12: (((r | ~q) & ((p & r) | (p & ~p))) & q) -> r			distributiveAnd
13: (((r | ~q) & ((p & r) | F)) & q) -> r			inverseAnd
14: (((r | ~q) & (p & r)) & q) -> r			identityOr
15: ((((r | ~q) & p) & r) & q) -> r			associativeAnd
16: (((r | ~q) & p) & (r & q)) -> r			associativeAnd
17: ((p & (r | ~q)) & (r & q)) -> r			commutativeAnd
18: ((p & (r | ~q)) & (q & r)) -> r			commutativeAnd
19: (((p & (r | ~q)) & q) & r) -> r			associativeAnd
20: ((p & ((r | ~q) & q)) & r) -> r			associativeAnd
21: ((p & (q & (r | ~q))) & r) -> r			commutativeAnd
22: ((p & ((q & r) | (q & ~q))) & r) -> r			distributiveAnd
23: ((p & ((q & r) | F)) & r) -> r			inverseAnd
24: ((p & (q & r)) & r) -> r			identityOr
25: (p & ((q & r) & r)) -> r			associativeAnd
26: (p & (q & (r & r))) -> r			associativeAnd
27: (p & (q & r)) -> r			idempotentAnd
28: ~(p & (q & r)) | r			implication
29: (~p | ~(q & r)) | r			deMorgansAnd
30: (~p | (~q | ~r)) | r			deMorgansAnd
31: ((~p | ~q) | ~r) | r			associativeOr
32: (~p | ~q) | (~r | r)			associativeOr
33: (~p | ~q) | (r | ~r)			commutativeOr
34: (~p | ~q) | T			inverseOr
35: ~p | (~q | T)			associativeOr
36: ~p | T			annihilationOr
37: T			annihilationOr
-}

{-
type EGStateIO = StateT Int IO

-- use runStateT (action) (initial state)
-- to return the result of the action, and the current state in the IO monad
-- runStateT :: StateT s m a -> s -> m (a,s)
-- so, runStateT (a::EGStateIO t) (b::Int) returns an IO (t,Int)
-- runStateT gets us out of the State monad and into the IO monad
retState :: EGStateIO Int
retState = do i <- get
              return i

printState :: EGStateIO ()
-- here we access IO 
-- runStateT printState i 
-- prints i 
printState = do i <- get
                liftIO (putStrLn $ show i)

printYourInt :: EGStateIO ()
printYourInt = do i <- get
                  liftIO (putStr "What is your int? ")
                  yi <- liftIO getLine
                  liftIO (putStrLn $ "Your int is: " ++ yi ++ ", mine is " ++ show i)
-}
{- ---------- Example proofs ---------- -}
                                            
proofA = startProof logicLaws [statementA, statementB]                                            
proofA1 = addProofStep proofA (step [] "inverseAnd")

proofB = startProof logicLaws [(varP "p" `impP` varP "q") `impP` varP "r"]
proofB1 = addProofStep proofB (step [DLeft] "implication")
proofB2 = addProofStep proofB1 (step [] "implication")
proofB3 = addProofStep proofB2 (step [DLeft] "deMorgansOr")
proofB4 = addProofStep proofB3 (step [DLeft,DLeft] "doubleNegation")
proofB5 = addProofStep proofB4 (step [] "commutativeOr")
proofB6 = addProofStep proofB5 (step [] "distributiveOr")

proofC = startProof logicLaws [p `orP` (notP q), q `orP` (notP p)]
    where p = varP "p"
          q = varP "q"
proofC1 = addProofStep proofC (step [] "distributiveAnd")
proofC2 = addProofStep proofC1 (step [DLeft] "commutativeAnd")
proofC3 = addProofStep proofC2 (step [DLeft] "distributiveAnd")
proofC4 = addProofStep proofC3 (step [DLeft,DRight] "inverseAnd")
proofC5 = addProofStep proofC4 (step [DLeft] "identityOr")
proofC6 = addProofStep proofC5 (step [DLeft] "commutativeAnd")
proofC7 = addProofStep proofC6 (step [DRight] "commutativeAnd")
proofC8 = addProofStep proofC7 (step [DRight] "distributiveAnd")
proofC9 = addProofStep proofC8 (step [DRight,DLeft] "commutativeAnd")
proofC10 = addProofStep proofC9 (step [DRight,DLeft] "inverseAnd")
proofC11 = addProofStep proofC10 (step [DRight] "commutativeOr")
proofC12 = addProofStep proofC11 (step [DRight] "identityOr")

printPF :: Proof -> IO ()
printPF = putStrLn . show

setProp = (pa `impP` pb) `impP` ((pa `orP` pb) `impP` pb)
    where pa = varP "Pa"
          pb = varP "Pb"