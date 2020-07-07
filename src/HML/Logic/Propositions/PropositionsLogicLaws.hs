{--
 -- Propositions.hs
 -- :l ./HML/Logic/Propositions.hs from devel directory
 -- A module for propositional logic
 --}
-- TODO: applying the laws of logic to a proposition
-- need to add a cursor to the Proposition
-- so we have a way to move through it
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
module HML.Logic.Propositions.PropositionsLogicLaws where

import HML.Logic.Propositions.Propositions
import HML.Logic.Propositions.PropositionsCursor

import Data.List
import Control.Monad

{- ---------- Data Types ---------- -}

-- NOTE: we could change these to newtypes and then make them instances of show
-- TODO: we might need to add a name component
type LogicLaw = (Proposition,Proposition)

type PBinding = [(String,Proposition)]

type LogicLawList = [(String,LogicLaw)]

--type NamedLogicLaw = (String,LogicLaw) -- or just add this to the type above, and use newtype for show instances
--type ProofStep = ([Direction], NamedLogicLaw) 
--type Proof = ([Axiom],[ProofStep])
--type Axiom = Propositions
-- fn: logic law from proof

{- ---------- Show instances ---------- -}

showLogicLaw :: LogicLaw -> String
showLogicLaw (p,q) = show p ++ " == " ++ show q

showPBinding :: PBinding -> String
showPBinding bs = concat $ intersperse "\n" $ map showB' bs
    where showB' (s,p) = s ++ " :: " ++ show p

{- ---------- Applying Logic Laws ---------- -}

bindToForm :: Proposition -> Proposition -> Maybe PBinding
--bindToForm f p returns Just b where b is the binding of p to f (if p has the same form as f),
--and returns Nothing otherwise 
bindToForm (Name s)           p                  = Just [(s,p)]
bindToForm (Binary op1 p1 q1) (Binary op2 p2 q2) = do b1 <- bindToForm p1 p2
                                                      b2 <- bindToForm q1 q2
                                                      if op1==op2 then return (b1++b2) else mzero
bindToForm (Unary op1 p1)     (Unary op2 p2)     = do b1 <- bindToForm p1 p2
                                                      if op1==op2 then return b1 else mzero
bindToForm (Constant b1)      (Constant b2)      = if b1==b2 then return [] else mzero
bindToForm (Cut)              (Cut)              = return []
bindToForm _                  _                  = mzero

consistent :: PBinding -> Bool
--consistent b returns True if b is consistent (i.e. if a string is bound to 
-- multiple propositions, those propositions are structurally equal),
--otherwise returns False
consistent = check' . sortBy compareFst
    where compareFst a b = compare (fst a) (fst b)

          check' []       = True
          check' [x]      = True
          check' (x:y:xs) = if fst x == fst y then snd x == snd y && check' (y:xs)
                                              else check' (y:xs)

apBinding :: PBinding -> Proposition -> Maybe Proposition
--apBinding pb p applies the binding pb to p, i.e., for each variable in p
--makes the substitution defined in pb
--If the binding does not cover the variables in p, nothing is returned
apBinding bs (Name s)        = lookup s bs
apBinding bs (Binary op p q) = do p' <- apBinding bs p
                                  q' <- apBinding bs q
                                  return (Binary op p' q')
apBinding bs (Unary op p)    = do p' <- apBinding bs p
                                  return (Unary op p')
apBinding bs p               = return p

matchLogicLaw :: LogicLaw -> CursorProp -> Bool
--matchLogicLaw ll cp returns true if the logic law
--matches (in either direction) cp at the cut
matchLogicLaw ll cp = matchF ll cp || matchB ll cp

matchF, matchB :: LogicLaw -> CursorProp -> Bool
--matchF (p,q) cp returns True if p matches cp at the cursor point
matchF (p,q) (CP mt ds st) = maybe False consistent (bindToForm p st)
--matchB (p,q) cp returns True if q matches cp at the cursor point
matchB (p,q) (CP mt ds st) = maybe False consistent (bindToForm q st)

apF_M, apB_M :: LogicLaw -> CursorProp -> Maybe CursorProp
--apF_M (p,q) cp returns proposition obtained by replacing p with q at the cursor point
apF_M (p,q) (CP mt ds st) = do pb <- bindToForm p st
                               st' <- apBinding pb q
                               return (CP mt ds st')
--apB_M (p,q) cp returns proposition obtained by replacing q with p at the cursor point
apB_M (p,q) (CP mt ds st) = do pb <- bindToForm q st
                               st' <- apBinding pb p
                               return (CP mt ds st')

apLogicLawM :: LogicLaw -> CursorProp -> Maybe CursorProp
--apLogicLawM (p,q) cp applies the logic law at the cursor point
--it will preferentially perform p->q over q->p (if both are possible)
apLogicLawM ll cp = apF_M ll cp `mplus` apB_M ll cp

apF, apB, apLogicLaw :: LogicLaw -> CursorProp -> CursorProp
--apF is an unsafe version of apF_M
apF ll cp = maybe (error "apF: cannot apply logic law") id (apF_M ll cp)
--apB is an unsafe version of apB_M
apB ll cp = maybe (error "apB: cannot apply logic law") id (apB_M ll cp)
--apF is an unsafe version of apF_M
apLogicLaw ll cp = maybe (error "apLogicLaw: cannot apply logic law") id (apLogicLawM ll cp)

{- ---------- Logic Laws ---------- -}

equivalenceLaw = (p `iffP` q, (p `impP` q) `andP` (q `impP` p))
    where p = varP "p"
          q = varP "q"

implicationLaw = (p `impP` q, (notP p) `orP` q)
    where p = varP "p"
          q = varP "q"

doubleNegationLaw = (notP (notP p), p)
    where p = varP "p"

idempotentAndLaw = (p `andP` p, p)
    where p = varP "p"

idempotentOrLaw = (p `orP` p, p)
    where p = varP "p"

commutativeAndLaw = (p `andP` q, q `andP` p)
    where p = varP "p"
          q = varP "q"

commutativeOrLaw = (p `orP` q, q `orP` p)
    where p = varP "p"
          q = varP "q"

associativeAndLaw = (p `andP` (q `andP` r), (p `andP` q) `andP` r)
    where p = varP "p"
          q = varP "q"
          r = varP "r"

associativeOrLaw = (p `orP` (q `orP` r), (p `orP` q) `orP` r)
    where p = varP "p"
          q = varP "q"
          r = varP "r"

distributiveAndLaw = (p `andP` (q `orP` r), (p `andP` q) `orP` (p `andP` r))
    where p = varP "p"
          q = varP "q"
          r = varP "r"

distributiveOrLaw =  (p `orP` (q `andP` r), (p `orP` q) `andP` (p `orP` r))
    where p = varP "p"
          q = varP "q"
          r = varP "r"

deMorgansAndLaw = (notP (p `andP` q), (notP p) `orP` (notP q))
    where p = varP "p"
          q = varP "q"

deMorgansOrLaw = (notP (p `orP` q), (notP p) `andP` (notP q))
    where p = varP "p"
          q = varP "q"

identityAndLaw = (p `andP` (constP True), p)
    where p = varP "p"

identityOrLaw = (p `orP` (constP False), p)
    where p = varP "p"

annihilationAndLaw = (p `andP` (constP False), constP False)
    where p = varP "p"

annihilationOrLaw = (p `orP` (constP True), constP True)
    where p = varP "p"

inverseAndLaw = (p `andP` (notP p), constP False)
    where p = varP "p"

inverseOrLaw = (p `orP` (notP p), constP True)
    where p = varP "p"

absorptionAndLaw = (p `andP` (p `orP` q), p)
    where p = varP "p"
          q = varP "q"

absorptionOrLaw = (p `orP` (p `andP` q), p)
    where p = varP "p"
          q = varP "q"

logicLaws :: LogicLawList
logicLaws = [("equivalence", equivalenceLaw),
             ("implication",implicationLaw),
             ("doubleNegation", doubleNegationLaw),
             ("idempotentAnd", idempotentAndLaw),
             ("idempotentOr", idempotentOrLaw),
             ("commutativeAnd", commutativeAndLaw),
             ("commutativeOr", commutativeOrLaw),
             ("associativeAnd", associativeAndLaw),
             ("associativeOr", associativeOrLaw),
             ("distributiveAnd", distributiveAndLaw),
             ("distributiveOr", distributiveOrLaw),
             ("deMorgansAnd", deMorgansAndLaw),
             ("deMorgansOr", deMorgansOrLaw),
             ("identityAnd", identityAndLaw),
             ("identityOr", identityOrLaw),
             ("annihilationAnd", annihilationAndLaw),
             ("annihilationOr", annihilationOrLaw),
             ("inverseAnd", inverseAndLaw),
             ("inverseOr", inverseOrLaw),
             ("absorptionAnd", absorptionAndLaw),
             ("absorptionOr", absorptionOrLaw)]

{- ---------- Old Stuff ---------- 

apLogicLaw :: (Proposition -> Proposition) -> CursorProp -> CursorProp
apLogicLaw law (CP mt ds st) = CP mt ds (law st)

matchLogicLaw :: (Proposition -> Bool) -> CursorProp -> Bool
matchLogicLaw law (CP mt ds st) = law st
-- how to represent a logic law???
-- Proposition -> Proposition
-- maybe need a function Proposition -> Bool as well 
-- or Proposition -> Maybe Proposition 

-- TODO: add a name field?
data LogicLaw = LL { canApplyLL :: Proposition -> Bool, applyLL :: Proposition -> Proposition }
-- TODO: how to add a custom LogicLaw??
--       maybe need a Pattern datatype, then a logic law
--       is a pair of patterns, with constraints?
--       Need a function Proposition -> PropPattern
--       A proposition matches a pattern if there is
--       a mapping between the names of the proposition
--       A proposition matches the pattern iff a mapping
--       can be constructed
--       This is not quite right, say we want to match p & p
--       then we try to match the &, then check the subtrees match
--       need to bind the subtrees, and get [(p,stleft),(p,stright)]
--       and check stleft == stright, as they are both bound to p
--       need a function hasForm :: Proposition -> Proposition -> Bool
--       matchForm :: Proposition -> Proposition -> [(String,Proposition)]

-- implication law (p -> q) == ~p or q
impLL :: Proposition -> Proposition
impLL (Binary Imp p q)            = Binary Or (notP p) q
impLL (Binary Or (Unary Not p) q) = Binary Imp p q
impLL _                           = error "implicationLL: cannot be applied"

impM :: Proposition -> Bool
impM (Binary Imp _ _)            = True
impM (Binary Or (Unary Not _) _) = True
impM _                           = False

implicationLL :: LogicLaw
implicationLL = LL { canApplyLL=impM, applyLL=impLL }

equivLL :: Proposition -> Proposition
equivLL (Binary Iff p q) = Binary And (Binary Imp p q) (Binary Imp q p)
equivLL (Binary And (Binary Imp p q) (Binary Imp r s)) | p==s && q==r = (Binary Iff p q)
                                                             | otherwise    = error "equivalenceLL: cannot be applied"
equivLL _ = error "equivalenceLL: cannot be applied"

equivM :: Proposition -> Bool
equivM (Binary Iff p q) = True
equivM (Binary And (Binary Imp p q) (Binary Imp r s)) = p==s && q==r

equivalenceLL :: LogicLaw
equivalenceLL = LL { canApplyLL=equivM, applyLL=equivLL }

-}


