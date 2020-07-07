{--
 -- PredicateMatching.hs
 -- :l ./HML/Logic/PredicateLogic/PredicateMatching.hs from devel directory
 -- A module for matching predicates to specified forms
 --}
module HML.Logic.Predicates.PredicateMatching where

import HML.Logic.Predicates.Predicates
import HML.Logic.Predicates.PredicateCursors

import Data.List(sortBy)
import Control.Monad

{- Some examples of matching that we want to do -}
{-
((setSubset A B)<->forall x. ((setElem x A) -> (setElem x B))

((setEqual A B)<->((setSubset A B)&(setSubset B A)))

Match on the expression setEqual A B, bind to A and B and replace by (setSubset A B)&(setSubset B A)

-- we will need to be able to generate new variable names
match on forall x. P(x) to P(y)
match on forall x s.t. P(x). Q(x) to P(y), Q(y)
match on P(y), Q(y) to get forall x s.t. P(x). Q(x) (How do we tell apart P(y) and Q(y)?)
match on P(x) and P(x) -> Q(x) to get Q(x)


forall x s.t. x \in Z & x > 2. x is prime -> x is odd
=> y \in Z & y > 2, y is prime -> y is odd
=> y is even -> y is not prime
=> forall x s.t. x \in Z & x > 2. x is even -> x is not prime
OR
forall x s.t. (x is even -> x is not prime). x \in Z & x > 2
I guess either is possible, although the second is unusual
Note p -> (q -> r) is equivalent to p&q -> r
-}

--data PredicateMatching = PMatching [(String,Predicate)] [(String,PName)] deriving (Show)
data PredicateMatching = PMatching { predicatePatterns :: [(String,Predicate)]
                                   , expressionPatterns :: [(String,Expression)]
                                   , namePatterns :: [(String,PName)]
                                   } deriving (Show)

-- Note: LogicLaws will not capture all the deductions we need to make
-- Logic laws just transform one predicate to an equivalent predicate
-- Proof steps map one or more predicates to one or more new predicates [Predicate] -> [Predicate]
-- under certain conditions
--type LogicLaw = (Predicate,Predicate)
--LogicLaw is a predicate of the form P <-> Q


joinMatching :: PredicateMatching -> PredicateMatching -> PredicateMatching
joinMatching (PMatching pPats1 ePats1 nPats1) (PMatching pPats2 ePats2 nPats2) = PMatching (pPats1++pPats2) (ePats1++ePats2) (nPats1++nPats2)

getPMatch :: String -> PredicateMatching -> Maybe Predicate
getPMatch n pm = lookup n (predicatePatterns pm)

getEMatch :: String -> PredicateMatching -> Maybe Expression
getEMatch n pm = lookup n (expressionPatterns pm)

getNMatch :: String -> PredicateMatching -> Maybe PName
getNMatch n pm = lookup n (namePatterns pm)

createMatching :: [(String,Predicate)] -> [(String,Expression)] -> [(String,PName)] -> PredicateMatching
createMatching = PMatching

--NOTE: I don't think this is needed
--renameNMatch :: String -> PName -> PredicateMatching -> PredicateMatching
--renameNMatch n npn (PMatching ps ns) = PMatching ps (map update' ns)
--    where update' (m,pm) | n == m    = (m,npn)
--                         | otherwise = (m,pm)

bindToForm :: Predicate -> Predicate -> Maybe PredicateMatching
--bindToForm f p returns Just b where b is the matching of p to f (if p has the same form as f),
--and returns Nothing otherwise 
bindToForm (PPatVar s)         p                   = Just (PMatching [(s,p)] [] [])
bindToForm (PBinary op1 p1 q1) (PBinary op2 p2 q2) = do b1 <- bindToForm p1 p2
                                                        b2 <- bindToForm q1 q2
                                                        if op1==op2 then return (joinMatching b1 b2) else Nothing
bindToForm (PUnary op1 p1)     (PUnary op2 p2)     = if op1==op2 then bindToForm p1 p2 else Nothing
bindToForm (PBinding pb1 p1)   (PBinding pb2 p2)   = do m1 <- bindToFormPB pb1 pb2
                                                        m2 <- bindToForm p1 p2
                                                        return (joinMatching m1 m2)
bindToForm (PExp e1)           (PExp e2)           = bindToFormExp e1 e2
bindToForm (PExpT e1 t1)       (PExpT e2 t2)       = if t1==t2 then bindToFormExp e1 e2 else Nothing
bindToForm (PEmpty)            (PEmpty)            = Just (PMatching [] [] [])
bindToForm _                   _                   = Nothing

bindToFormExp :: Expression -> Expression -> Maybe PredicateMatching
bindToFormExp (ExpPatVar s) e             = Just (PMatching [] [(s,e)] [])
bindToFormExp (ExpN pn1)    (ExpN pn2)    = bindToFormPN pn1 pn2
bindToFormExp (ExpF n1 es1) (ExpF n2 es2) = if n1==n2 then (foldl1 joinMatching) `liftM` (zipWithM bindToFormExp es1 es2)
                                                      else Nothing 
bindToFormExp _             _             = Nothing

bindToFormPB :: PredicateBinding -> PredicateBinding -> Maybe PredicateMatching
bindToFormPB (Forall pn1 p1) (Forall pn2 p2) = do m1 <- bindToFormPN pn1 pn2
                                                  m2 <- bindToForm p1 p2
                                                  return (joinMatching m1 m2)
bindToFormPB (Exists pn1 p1) (Exists pn2 p2) = do m1 <- bindToFormPN pn1 pn2
                                                  m2 <- bindToForm p1 p2
                                                  return (joinMatching m1 m2)
bindToFormPB _               _               = Nothing

bindToFormPN :: PName -> PName -> Maybe PredicateMatching
bindToFormPN (NPatVar s) pn          = Just (PMatching [] [] [(s,pn)])
bindToFormPN (PVar s1)   (PVar s2)   = if s1==s2 then Just (PMatching [] [] []) else Nothing
bindToFormPN (PConst s1) (PConst s2) = if s1==s2 then Just (PMatching [] [] []) else Nothing
bindToFormPN _           _           = Nothing

consistent :: PredicateMatching -> Bool
--consistent pm returns True if pm is consistent (i.e. if a string is bound to 
-- multiple predicates, those propositions are structurally equal),
--otherwise returns False
consistent (PMatching pPats ePats nPats) =    (check' $ sortBy compareFst pPats) 
                                           && (check' $ sortBy compareFst ePats)
                                           && (check' $ sortBy compareFst nPats)
    where compareFst a b = compare (fst a) (fst b)

          check' []       = True
          check' [x]      = True
          check' (x:y:xs) = if fst x == fst y then snd x == snd y && check' (y:xs)
                                              else check' (y:xs)


apMatchingM :: PredicateMatching -> Predicate -> Maybe Predicate
--apBinding pm p applies the matching pm to p, i.e., for each pattern variable in p
--makes the substitution defined in pm
--If the matching does not cover the pattern variables in p, nothing is returned
apMatchingM pm p = apP' p
    where apP' :: Predicate -> Maybe Predicate
          apP' (PExp e)         = do e' <- apE' e
                                     return (PExp e')
          apP' (PExpT e t)      = do e' <- apE' e
                                     return (PExpT e' t)
          apP' (PBinary op p q) = do p' <- apP' p
                                     q' <- apP' q
                                     return (PBinary op p' q')
          apP' (PUnary op p)    = do p' <- apP' p
                                     return (PUnary op p')
          apP' (PBinding pb p)  = do pb' <- apPB' pb
                                     p' <- apP' p
                                     return (PBinding pb' p')
          apP' (PPatVar pv)     = getPMatch pv pm
          apP' p                = Just p

          apE' :: Expression -> Maybe Expression
          apE' (ExpN pn)      = do pn' <- apPN' pn
                                   return (ExpN pn')
          apE' (ExpF n es)    = do es' <- mapM apE' es
                                   return (ExpF n es')
          apE' (ExpPatVar pv) = getEMatch pv pm
          apE' e              = Just e 

          apPB' :: PredicateBinding -> Maybe PredicateBinding
          apPB' (Forall pn p) = do pn' <- apPN' pn
                                   p' <- apP' p
                                   return (Forall pn' p')
          apPB' (Exists pn p) = do pn' <- apPN' pn
                                   p' <- apP' p
                                   return (Exists pn' p')

          apPN' :: PName -> Maybe PName
          apPN' (NPatVar s) = getNMatch s pm
          apPN' pn          = Just pn

renameFreeVariables :: (PName -> PName) -> Predicate -> Predicate
--renameFreeVariables rnf p renames the free variables in p using
--the function rnf, i.e. applies rnf to each free variable in p
--Assumes that the renaming doesn't capture any variables
renameFreeVariables rnf p = rfvP' [] p
    where rfvP' :: [PName] -> Predicate -> Predicate
          rfvP' bv (PExp e)         = PExp (rfvE' bv e)
          rfvP' bv (PExpT e t)      = (PExpT (rfvE' bv e) t)
          rfvP' bv (PBinary op p q) = PBinary op (rfvP' bv p) (rfvP' bv q)
          rfvP' bv (PUnary op p)    = PUnary op (rfvP' bv p)
          rfvP' bv (PBinding pb p)  = let bv' = (boundVariable pb):bv in PBinding (rfvPB' bv' pb) (rfvP' bv' p)
          rfvP' bv p                = p

          rfvE' :: [PName] -> Expression -> Expression
          rfvE' bv (ExpN pn)      = if pn `elem` bv then ExpN pn else ExpN (rnf pn)
          rfvE' bv (ExpF n es)    = ExpF n (map (rfvE' bv) es)
          rfvE' bv e              = e 

          rfvPB' :: [PName] -> PredicateBinding -> PredicateBinding
          rfvPB' bv (Forall pn p) = Forall pn (rfvP' bv p)
          rfvPB' bv (Exists pn p) = Exists pn (rfvP' bv p)

{- Examples -}

egP1 = expP $ (setA `union` setB) `subset` setB
    where setA = namedExp $ varN "A"
          setB = namedExp $ varN "B"

formP1 = expP $ setP `subset` setQ
    where setP = patternExp "P"
          setQ = patternExp "Q"

toFormP1 = forall_ nameX ((expP $ inSet varX setP) `impP` (expP $ inSet varX setQ))
    where setP = patternExp "P"
          setQ = patternExp "Q"

          nameX = varN "x"
          varX = namedExp nameX

matchingP1 = bindToForm formP1 egP1
afterMatchingP1 = do pm <- matchingP1
                     apMatchingM pm toFormP1

egP2 = forall_ nameX ((expP $ inSet varX (setA `union` setB)) `impP` (expP $ inSet varX setB))
    where setA = namedExp $ varN "A"
          setB = namedExp $ varN "B"

          nameX = varN "x"
          varX = namedExp nameX

formP2 = forall_ nameZ ((expP $ inSet varZ setP) `impP` (expP $ inSet varZ setQ))
    where setP = patternExp "P"
          setQ = patternExp "Q"

          nameZ = patternN "z"
          varZ = namedExp nameZ

toFormP2 = expP $ (setP `subset` setQ)
    where setP = patternExp "P"
          setQ = patternExp "Q"

matchingP2 = bindToForm formP2 egP2
afterMatchingP2 = do pm <- matchingP2
                     apMatchingM pm toFormP2

