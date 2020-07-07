{--
 -- PredicateLogicLaws.hs
 -- :l ./HML/Logic/PredicateLogic/PredicateLogicLaws.hs from devel directory
 -- Logic laws for predicate logic
 -- Logic laws allow us to manipulate compound predicates (and, or, etc)
 --}
module HML.Logic.Predicates.PredicateLogicLaws where

import HML.Logic.Predicates.Predicates
import HML.Logic.Predicates.PredicateCursors
import HML.Logic.Predicates.PredicateMatching

--import Data.List(sortBy)
import Control.Monad(mplus)

matchLogicLaw, matchF, matchB :: Predicate -> PredicateCursor -> Bool
--matchLogicLaw ll pc returns true if the logic law
--matches (in either direction) the predicate (represented by) pc at the cut
--ll must be of the form: p <-> q
--matchF matches in the forward direction (p -> q)
--matchB matches in the reverse direction (q -> p)
matchLogicLaw ll pc = matchF ll pc || matchB ll pc

--matchF ll pc returns True if p matches cp at the cursor point
matchF ll (PC mp ds sp) = case ll of
                            PBinary PIff pForm qForm -> maybe False consistent (bindToForm pForm sp)
                            _                        -> False

--matchB ll pc returns True if q matches cp at the cursor point
matchB ll (PC mp ds sp) = case ll of
                            PBinary PIff pForm qForm -> maybe False consistent (bindToForm qForm sp)
                            _                        -> False

apF_M, apB_M, apLogicLawM :: Predicate -> PredicateCursor -> Maybe PredicateCursor
--apF_M ll pc returns proposition obtained by replacing p with q at the cursor point
apF_M ll (PC mp ds sp) = do (p,q) <- getForms'
                            pm <- bindToForm p sp
                            sp' <- apMatchingM pm q
                            return (PC mp ds sp')
    where getForms' = case ll of
                        PBinary PIff pForm qForm -> Just (pForm, qForm)
                        _                        -> Nothing
--apB_M (p,q) cp returns proposition obtained by replacing q with p at the cursor point
apB_M ll (PC mp ds sp) = do (p,q) <- getForms'
                            pm <- bindToForm q sp
                            sp' <- apMatchingM pm p
                            return (PC mp ds sp')
    where getForms' = case ll of
                        PBinary PIff pForm qForm -> Just (pForm, qForm)
                        _                        -> Nothing
--apLogicLawM (p,q) cp applies the logic law at the cursor point
--it will preferentially perform p->q over q->p (if both are possible)
-- mplus takes the first result not equal to Nothing
apLogicLawM ll pc = apF_M ll pc `mplus` apB_M ll pc

apF, apB, apLogicLaw :: Predicate -> PredicateCursor -> PredicateCursor
--apF is an unsafe version of apF_M
apF ll cp = maybe (error "apF: cannot apply logic law") id (apF_M ll cp)
--apB is an unsafe version of apB_M
apB ll cp = maybe (error "apB: cannot apply logic law") id (apB_M ll cp)
--apF is an unsafe version of apF_M
apLogicLaw ll cp = maybe (error "apLogicLaw: cannot apply logic law") id (apLogicLawM ll cp)

{- ---------- Logic Laws ---------- -}
-- the standard logic laws for predicate logic

equivalenceLaw = (p `iffP` q) `iffP` ((p `impP` q) `andP` (q `impP` p))
    where p = patternP "P"
          q = patternP "Q"

implicationLaw = (p `impP` q) `iffP` ((notP p) `orP` q)
    where p = patternP "P"
          q = patternP "Q"

doubleNegationLaw = (notP (notP p)) `iffP` p
    where p = patternP "P"

idempotentAndLaw = (p `andP` p) `iffP` p
    where p = patternP "P"

idempotentOrLaw = (p `orP` p) `iffP` p
    where p = patternP "P"

commutativeAndLaw = (p `andP` q) `iffP` (q `andP` p)
    where p = patternP "P"
          q = patternP "Q"

commutativeOrLaw = (p `orP` q) `iffP` (q `orP` p)
    where p = patternP "P"
          q = patternP "Q"

associativeAndLaw = (p `andP` (q `andP` r)) `iffP` ((p `andP` q) `andP` r)
    where p = patternP "P"
          q = patternP "Q"
          r = patternP "R"

associativeOrLaw = (p `orP` (q `orP` r)) `iffP` ((p `orP` q) `orP` r)
    where p = patternP "P"
          q = patternP "Q"
          r = patternP "R"

distributiveAndLaw = (p `andP` (q `orP` r)) `iffP` ((p `andP` q) `orP` (p `andP` r))
    where p = patternP "P"
          q = patternP "Q"
          r = patternP "R"

distributiveOrLaw =  (p `orP` (q `andP` r)) `iffP` ((p `orP` q) `andP` (p `orP` r))
    where p = patternP "P"
          q = patternP "Q"
          r = patternP "R"

deMorgansAndLaw = (notP (p `andP` q)) `iffP` ((notP p) `orP` (notP q))
    where p = patternP "P"
          q = patternP "Q"

deMorgansOrLaw = (notP (p `orP` q)) `iffP` ((notP p) `andP` (notP q))
    where p = patternP "P"
          q = patternP "Q"

identityAndLaw = (p `andP` trueP) `iffP` p
    where p = patternP "P"

identityOrLaw = (p `orP` falseP) `iffP` p
    where p = patternP "P"

annihilationAndLaw = (p `andP` falseP) `iffP` falseP
    where p = patternP "P"

annihilationOrLaw = (p `orP` trueP) `iffP` trueP
    where p = patternP "P"

inverseAndLaw = (p `andP` (notP p)) `iffP` falseP
    where p = patternP "P"

inverseOrLaw = (p `orP` (notP p)) `iffP` trueP
    where p = patternP "P"

absorptionAndLaw = (p `andP` (p `orP` q)) `iffP` p
    where p = patternP "P"
          q = patternP "Q"

absorptionOrLaw = (p `orP` (p `andP` q)) `iffP` p
    where p = patternP "P"
          q = patternP "Q"

-- deMorgans laws for predicates (not forall etc)
-- forall x. forall y. = forall y. forall x.
deMorgansForallLaw = (notP (forall x t p)) `iffP` (exists x t (notP p))
    where p = patternP "P"
          t = patternP "T"
          x = patternN "x"

deMorgansExistsLaw = (notP (exists x t p)) `iffP` (forall x t (notP p))
    where p = patternP "P"
          t = patternP "T"
          x = patternN "x"

swapForallLaw = (forall x t (forall y s p)) `iffP` (forall y s (forall x t p))
    where p = patternP "P"
          t = patternP "T"
          s = patternP "S"
          x = patternN "x"
          y = patternN "y"
         
swapExistsLaw = (exists x t (exists y s p)) `iffP` (exists y s (exists x t p))
    where p = patternP "P"
          t = patternP "T"
          s = patternP "S"
          x = patternN "x"
          y = patternN "y"
