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
import HML.Logic.Predicates.PredicatesPrettyPrint(prettyPrint)

--import Data.List(sortBy)
import Control.Monad(mplus)
import Control.Applicative((<$>))

matchLogicLaw, matchF, matchB :: Predicate -> PredicateCursor -> Bool
--matchLogicLaw ll pc returns true if the logic law
--matches (in either direction) the predicate (represented by) pc at the cut
--ll must be of the form: p <-> q
--matchF matches in the forward direction (p -> q)
--matchB matches in the reverse direction (q -> p)
matchLogicLaw ll pc = matchF ll pc || matchB ll pc

--matchF ll pc returns True if p matches cp at the cursor point
matchF ll (PC mp ds sp) = case ll of
                            PIff pForm qForm -> maybe False consistent (bindToForm pForm sp)
                            _                -> False

--matchB ll pc returns True if q matches cp at the cursor point
matchB ll (PC mp ds sp) = case ll of
                            PIff pForm qForm -> maybe False consistent (bindToForm qForm sp)
                            _                -> False

apF_M, apB_M, apLogicLawM :: Predicate -> PredicateCursor -> Maybe PredicateCursor
--apF_M ll pc returns proposition obtained by replacing p with q at the cursor point
apF_M ll (PC mp ds sp) = do (p,q) <- getForms'
                            pm <- bindToForm p sp
                            sp' <- apMatchingM pm q
                            return (PC mp ds sp')
    where getForms' = case ll of
                        PIff pForm qForm -> Just (pForm, qForm)
                        _                -> Nothing
--apB_M (p,q) cp returns proposition obtained by replacing q with p at the cursor point
apB_M ll (PC mp ds sp) = do (p,q) <- getForms'
                            pm <- bindToForm q sp
                            sp' <- apMatchingM pm p
                            return (PC mp ds sp')
    where getForms' = case ll of
                        PIff pForm qForm -> Just (pForm, qForm)
                        _                -> Nothing
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

{- UPDATE THIS WHEN NEEDED
renameBoundVariableAtCut :: String -> String -> PredicateCursor -> Maybe PredicateCursor
renameBoundVariableAtCut xn yn (PC mp ds sp) = if yn `elem` (getVariableNames mp ++ getVariableNames sp)
                                               then Nothing
                                               else (PC mp ds) <$> sp'
    where sp' = case sp of
                  PBinding (Forall (PVar bv) bp) p -> do bp' <- renameFreeVariable xn yn bp
                                                         p' <- renameFreeVariable xn yn p
                                                         if bv == xn then Just (PBinding (Forall (PVar yn) bp') p')
                                                                     else Nothing
                  PBinding (Exists (PVar bv) bp) p -> do bp' <- renameFreeVariable xn yn bp
                                                         p' <- renameFreeVariable xn yn p
                                                         if bv == xn then Just (PBinding (Exists (PVar yn) bp') p')
                                                                     else Nothing
                  _                                -> Nothing
-}
{- ---------- Logic Laws ---------- -}
-- the standard logic laws for predicate logic

equivalenceLaw = PIff (PIff p q) (PAnd (PImp p q) (PImp q p))
    where p = PPatVar "P"
          q = PPatVar "Q"

implicationLaw = PIff (PImp p q) (POr (PNot p) q)
    where p = PPatVar "P"
          q = PPatVar "Q"

doubleNegationLaw = PIff (PNot (PNot p)) p
    where p = PPatVar "P"

idempotentAndLaw = PIff (PAnd p p) p
    where p = PPatVar "P"

idempotentOrLaw = PIff (POr p p) p
    where p = PPatVar "P"

commutativeAndLaw = PIff (PAnd p q) (PAnd q p)
    where p = PPatVar "P"
          q = PPatVar "Q"

commutativeOrLaw = PIff (POr p q) (POr q p)
    where p = PPatVar "P"
          q = PPatVar "Q"

associativeAndLaw = PIff (PAnd p (PAnd q r))  (PAnd (PAnd p q) r)
    where p = PPatVar "P"
          q = PPatVar "Q"
          r = PPatVar "R"

associativeOrLaw = PIff (POr p (POr q r))  (POr (POr p q) r)
    where p = PPatVar "P"
          q = PPatVar "Q"
          r = PPatVar "R"

distributiveAndLaw = PIff (PAnd p (POr q r))  (POr (PAnd p q) (PAnd p r))
    where p = PPatVar "P"
          q = PPatVar "Q"
          r = PPatVar "R"

distributiveOrLaw = PIff (POr p (PAnd q r))  (PAnd (POr p q) (POr p r))
    where p = PPatVar "P"
          q = PPatVar "Q"
          r = PPatVar "R"

deMorgansAndLaw = PIff (PNot (PAnd p q)) (POr (PNot p) (PNot  q))
    where p = PPatVar "P"
          q = PPatVar "Q"

deMorgansOrLaw = PIff (PNot (POr p q)) (PAnd (PNot p) (PNot q))
    where p = PPatVar "P"
          q = PPatVar "Q"

identityAndLaw = PIff (PAnd p (PExp $ ExpN $ Constant $ SBool True)) p
    where p = PPatVar "P"

identityOrLaw = PIff (POr p (PExp $ ExpN $ Constant $ SBool False)) p
    where p = PPatVar "P"

annihilationAndLaw = PIff (PAnd p (PExp $ ExpN $ Constant $ SBool False)) (PExp $ ExpN $ Constant $ SBool False)
    where p = PPatVar "P"

annihilationOrLaw = PIff (POr p (PExp $ ExpN $ Constant $ SBool True)) (PExp $ ExpN $ Constant $ SBool True)
    where p = PPatVar "P"

inverseAndLaw = PIff (PAnd p (PNot  p)) (PExp $ ExpN $ Constant $ SBool False)
    where p = PPatVar "P"

inverseOrLaw = PIff (POr p (PNot  p)) (PExp $ ExpN $ Constant $ SBool True)
    where p = PPatVar "P"

absorptionAndLaw = PIff (PAnd p (POr p q))  p
    where p = PPatVar "P"
          q = PPatVar "Q"

absorptionOrLaw = PIff (POr p (PAnd p q))  p
    where p = PPatVar "P"
          q = PPatVar "Q"

-- deMorgans laws for predicates (not forall etc)
-- forall x. forall y. = forall y. forall x.
deMorgansForallLaw = PIff (PNot (PBinding Forall x p))  (PBinding Exists x (PNot p))
    where p = PPatVar "P"
          x = VPatVar "x"

deMorgansExistsLaw = PIff (PNot (PBinding Exists x p)) (PBinding Forall x (PNot p))
    where p = PPatVar "P"
          x = VPatVar "x"

swapForallLaw = PIff (PBinding Forall x (PBinding Forall y p)) (PBinding Forall y (PBinding Forall x p))
    where p = PPatVar "P"
          x = VPatVar "x"
          y = VPatVar "y"
         
swapExistsLaw = PIff (PBinding Exists x (PBinding Exists y p)) (PBinding Exists y (PBinding Exists x p))
    where p = PPatVar "P"
          x = VPatVar "x"
          y = VPatVar "y"