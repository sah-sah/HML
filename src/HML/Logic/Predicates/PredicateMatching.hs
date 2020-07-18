{--
 -- PredicateMatching.hs
 -- :l ./HML/Logic/PredicateLogic/PredicateMatching.hs from devel directory
 -- A module for matching predicates to specified forms
 --}
module HML.Logic.Predicates.PredicateMatching where

import HML.Logic.Predicates.Predicates
import HML.Logic.Predicates.PredicateCursors
import HML.Logic.Predicates.PredicatesPrettyPrint(prettyPrint)

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
                                   , variablePatterns :: [(String,Variable)]
                                   } deriving (Show)

-- Note: LogicLaws will not capture all the deductions we need to make
-- Logic laws just transform one predicate to an equivalent predicate
-- Proof steps map one or more predicates to one or more new predicates [Predicate] -> [Predicate]
-- under certain conditions
--type LogicLaw = (Predicate,Predicate)
--LogicLaw is a predicate of the form P <-> Q


joinMatching :: PredicateMatching -> PredicateMatching -> PredicateMatching
joinMatching (PMatching pPats1 ePats1 vPats1) (PMatching pPats2 ePats2 vPats2) = PMatching (pPats1++pPats2) (ePats1++ePats2) (vPats1++vPats2)

getPMatch :: String -> PredicateMatching -> Maybe Predicate
getPMatch n pm = lookup n (predicatePatterns pm)

getEMatch :: String -> PredicateMatching -> Maybe Expression
getEMatch n pm = lookup n (expressionPatterns pm)

getVMatch :: String -> PredicateMatching -> Maybe Variable
getVMatch n pm = lookup n (variablePatterns pm)

createMatching :: [(String,Predicate)] -> [(String,Expression)] -> [(String,Variable)] -> PredicateMatching
createMatching = PMatching

bindToForm :: Predicate -> Predicate -> Maybe PredicateMatching
--bindToForm f p returns Just b where b is the matching of p to f (if p has the same form as f),
--and returns Nothing otherwise 
bindToForm (PPatVar s)         p                   = Just (PMatching [(s,p)] [] [])
bindToForm (PAnd p1 q1)        (PAnd p2 q2)        = do b1 <- bindToForm p1 p2
                                                        b2 <- bindToForm q1 q2
                                                        return (joinMatching b1 b2)
bindToForm (POr p1 q1)         (POr p2 q2)         = do b1 <- bindToForm p1 p2
                                                        b2 <- bindToForm q1 q2
                                                        return (joinMatching b1 b2)
bindToForm (PImp p1 q1)        (PImp p2 q2)        = do b1 <- bindToForm p1 p2
                                                        b2 <- bindToForm q1 q2
                                                        return (joinMatching b1 b2)
bindToForm (PIff p1 q1)        (PIff p2 q2)        = do b1 <- bindToForm p1 p2
                                                        b2 <- bindToForm q1 q2
                                                        return (joinMatching b1 b2)
bindToForm (PNot p1)           (PNot p2)           = bindToForm p1 p2
bindToForm (PBinding t1 v1 p1) (PBinding t2 v2 p2) = if t1 == t2 then do m1 <- bindToFormV v1 v2
                                                                         m2 <- bindToForm p1 p2
                                                                         return (joinMatching m1 m2)
                                                                 else Nothing
bindToForm (PExp e1)           (PExp e2)           = bindToFormExp e1 e2
bindToForm _                   _                   = Nothing

bindToFormExp :: Expression -> Expression -> Maybe PredicateMatching
bindToFormExp (ExpPatVar s)     e                 = Just (PMatching [] [(s,e)] [])
bindToFormExp (ExpN n1)         (ExpN n2)         = bindToFormN n1 n2
bindToFormExp (ExpFn n1 es1)    (ExpFn n2 es2)    = if n1==n2 then (foldl1 joinMatching) `liftM` (zipWithM bindToFormExp es1 es2)
                                                              else Nothing
bindToFormExp (ExpEquals e1 f1) (ExpEquals e2 f2) = do b1 <- bindToFormExp e1 e2
                                                       b2 <- bindToFormExp f1 f2
                                                       return (joinMatching b1 b2)
bindToFormExp _                 _             = Nothing

bindToFormN :: Name -> Name -> Maybe PredicateMatching
bindToFormN (Var v1)      (Var v2)      = bindToFormV v1 v2
bindToFormN (Constant c1) (Constant c2) = bindToFormS c1 c2
bindToFormN _             _             = Nothing

bindToFormV :: Variable -> Variable -> Maybe PredicateMatching
bindToFormV (VPatVar s)        v                  = Just (PMatching [] [] [(s,v)])
bindToFormV (SimpleVar s1)     (SimpleVar s2)     = if s1==s2 then Just (PMatching [] [] []) else Nothing
bindToFormV (IndexedVar s1 e1) (IndexedVar s2 e2) = if s1==s2 then bindToFormExp e1 e2 else Nothing
bindToFormV _                  _                  = Nothing

bindToFormS :: Special -> Special -> Maybe PredicateMatching
bindToFormS (SInt n1)    (SInt n2)    = if n1==n2 then Just (PMatching [] [] []) else Nothing
bindToFormS (SBool b1)   (SBool b2)   = if b1==b2 then Just (PMatching [] [] []) else Nothing
bindToFormS (SEmptySet)  (SEmptySet)  = Just (PMatching [] [] [])
bindToFormS (SZ)         (SZ)         = Just (PMatching [] [] [])
bindToFormS (SZplus)     (SZplus)     = Just (PMatching [] [] [])
bindToFormS (SZn e1)     (SZn e2)     = bindToFormExp e1 e2
bindToFormS (SFinite e1) (SFinite e2) = bindToFormExp e1 e2
bindToFormS _            _            = Nothing

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
-- could be written in applicative style
apMatchingM pm p = apP p
    where apP :: Predicate -> Maybe Predicate
          apP (PExp e)         = do e' <- apE e
                                    return (PExp e')
          apP (PAnd p q)       = do p' <- apP p
                                    q' <- apP q
                                    return (PAnd p' q')
          apP (POr p q)        = do p' <- apP p
                                    q' <- apP q
                                    return (POr p' q')
          apP (PImp p q)       = do p' <- apP p
                                    q' <- apP q
                                    return (PImp p' q')
          apP (PIff p q)       = do p' <- apP p
                                    q' <- apP q
                                    return (PIff p' q')
          apP (PNot p)         = do p' <- apP p
                                    return (PNot p')
          apP (PBinding t v p) = do v' <- apV v
                                    p' <- apP p
                                    return (PBinding t v' p')
          apP (PPatVar pv)     = getPMatch pv pm
          apP p                = Just p

          apE :: Expression -> Maybe Expression
          apE (ExpN n)        = do n' <- apN n
                                   return (ExpN n')
          apE (ExpFn n es)    = do es' <- mapM apE es
                                   return (ExpFn n es')
          apE (ExpEquals e f) = do e' <- apE e
                                   f' <- apE f
                                   return (ExpEquals e' f')
          apE (ExpPatVar pv)  = getEMatch pv pm
          apE e               = Just e

          apN :: Name -> Maybe Name
          apN (Var v)      = do v' <- apV v
                                return (Var v')
          apN (Constant s) = do s' <- apS s
                                return (Constant s')

          apV :: Variable -> Maybe Variable
          apV (IndexedVar s e) = do e' <- apE e
                                    return (IndexedVar s e')
          apV (VPatVar s)      = getVMatch s pm
          apV v                = Just v

          apS :: Special -> Maybe Special
          apS (SZn e)     = do e' <- apE e
                               return (SZn e')
          apS (SFinite e) = do e' <- apE e
                               return (SFinite e')
          apS s           = Just s


{- Examples -}

egP1 = PExp $ (ExpFn "setSubset" [(ExpFn "setUnion" [setA,setB]),setB])
    where setA = ExpN $ Var $ SimpleVar "A"
          setB = ExpN $ Var $ SimpleVar "B"

formP1 = PExp $ (ExpFn "setSubset" [setP,setQ])
    where setP = ExpPatVar "P"
          setQ = ExpPatVar "Q"

toFormP1 = PBinding Forall (SimpleVar "x") (PImp (PExp $ ExpFn "setElem" [varX,setP]) (PExp $ ExpFn "setElem" [varX,setQ]))
    where setP = ExpPatVar "P"
          setQ = ExpPatVar "Q"

          varX = ExpN $ Var $ SimpleVar "x"

matchingP1 = bindToForm formP1 egP1
afterMatchingP1 = do pm <- matchingP1
                     apMatchingM pm toFormP1

egP2 = PBinding Forall (SimpleVar "x") (PImp (PExp $ ExpFn "setElem" [varX,ExpFn "setUnion" [setA,setB]])
                                             (PExp $ ExpFn "setElem" [varX,setB]))
    where setA = ExpN $ Var $ SimpleVar "A"
          setB = ExpN $ Var $ SimpleVar "B"

          varX = ExpN $ Var $ SimpleVar "x"

formP2 = PBinding Forall (VPatVar "z") (PImp (PExp $ ExpFn "setElem" [varZ,setP]) (PExp $ ExpFn "setElem" [varZ,setQ]))
    where setP = ExpPatVar "P"
          setQ = ExpPatVar "Q"

          varZ = ExpN $ Var $ VPatVar "z"

toFormP2 = PExp (ExpFn "setSubset" [setP,setQ])
    where setP = ExpPatVar "P"
          setQ = ExpPatVar "Q"

matchingP2 = bindToForm formP2 egP2
afterMatchingP2 = do pm <- matchingP2
                     apMatchingM pm toFormP2
