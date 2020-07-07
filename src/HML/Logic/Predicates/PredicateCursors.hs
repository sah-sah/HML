{--
 -- PredicateCursors.hs
 -- :l ./HML/Logic/PredicateLogic/PredicateCursors.hs from devel directory
 -- A module for moving through predicate expressions
 --}

module HML.Logic.Predicates.PredicateCursors where

import HML.Logic.Predicates.Predicates

import Data.List
import Control.Monad

{- ---------- Data Types ---------- -}

data Direction = DLeft | DRight | DDown | DUp | DBranch Int
    deriving (Show, Eq)

{- ---------- Predicate Expression Cursors ---------- -}

data PredicateCursor = PC Predicate [Direction] Predicate

{- ---------- Show instances ---------- -}

instance Show PredicateCursor where
    show (PC mt ds st) = replaceCut' (show mt)
        where replaceCut' (a:b:c:str) | [a,b,c] == "(@)" = ("[" ++ show st ++ "]") ++ str
                                      | otherwise        = a:replaceCut' (b:c:str)

{- ---------- Construction Functions ---------- -}

cutPredicateM :: Predicate -> [Direction] -> Maybe PredicateCursor
-- cutPredicateM p ds cuts the predicate p into a main tree and subtree
-- at the point specified by ds
-- if the directions are invalid, it returns Nothing
cutPredicateM p ds = do cds <- cleanDs' (ds, [])
                        (mp,sp) <- splitP' p cds 
                        return (PC mp cds sp) -- return the original ds? or cds? 
    where splitP' :: Predicate -> [Direction] -> Maybe (Predicate, Predicate)
          splitP' p                []          = Just (PCut,p)
          splitP' (PBinary op p q) (d:ds) = case d of
                                               DBranch 1 -> do (mp,sp) <- splitP' p ds
                                                               return (PBinary op mp q, sp)
                                               DBranch 2 -> do (mp,sp) <- splitP' q ds
                                                               return (PBinary op p mp, sp)
                                               _         -> Nothing
          splitP' (PUnary op p)    (d:ds)  = case d of
                                               DBranch 1 -> do (mp, sp) <- splitP' p ds
                                                               return (PUnary op mp, sp)
                                               _         -> Nothing
          splitP' (PBinding pb p)  (d:ds)  = case d of
                                               DBranch 1 -> do (mp, sp) <- splitP' p ds
                                                               return (PBinding pb mp, sp)
                                               _         -> Nothing
          splitP' (PExp e)         ds      = do (me, sp) <- splitE' e ds
                                                return (PExp me, sp)
          splitP' (PExpT e t)      ds      = do (ms, sp) <- splitE' e ds
                                                return (PExpT ms t, sp)
          splitP' _                _           = Nothing

          splitE' :: Expression -> [Direction] -> Maybe (Expression, Predicate)
          splitE' e           []               = Just (ExpCut, PExp e)
          splitE' (ExpF n es) ((DBranch i):ds) = if i >= 1 && i <= length es
                                                   then let (es1,es2) = splitAt (i-1) es
                                                        in do (me, sp) <- splitE' (head es2) ds
                                                              return (ExpF n (es1++(me:tail es2)), sp)
                                                   else Nothing

          splitE' _           _                = Nothing

          -- remove DUp's if needed, return Nothing if the DUp's cannot be removed
          cleanDs' ([],st) = Just (reverse st)
          cleanDs' (d:ds,st) | d == DUp && st==[] = Nothing
                             | d == DUp && st/=[] = cleanDs' (ds,tail st)
                             | otherwise          = cleanDs' (ds,convert' d:st)

          -- convert DLeft, DRight, DDown to a DBranch
          convert' DLeft  = DBranch 1
          convert' DRight = DBranch 2
          convert' DDown  = DBranch 1
          convert' d      = d


cutPredicate :: Predicate -> [Direction] -> PredicateCursor
-- an unsafe version of cutPredicateM
cutPredicate p ds = maybe (error "cutPredicate: invalid directions") id (cutPredicateM p ds)

healPredicate :: PredicateCursor -> Predicate
-- healPredicate pc returns the original, uncut predicate underlying pc
-- NOTE: it assumes that the directions are valid, which will be true if
-- pc was generated from cutPredicateM/cutPredicate
healPredicate (PC mp ds sp) = healP' mp ds
    where healP' :: Predicate -> [Direction] -> Predicate
          healP' PCut              []    = sp
          healP' (PBinary op p q) (d:ds) = case d of
                                             DBranch 1 -> PBinary op (healP' p ds) q
                                             DBranch 2 -> PBinary op p (healP' q ds)
                                             _         -> errorMsg
          healP' (PUnary op p)    (d:ds) = case d of
                                             DBranch 1 -> PUnary op (healP' p ds)
                                             _         -> errorMsg
          healP' (PBinding pb p)  (d:ds) = case d of
                                             DBranch 1 -> PBinding pb (healP' p ds) 
                                             _         -> errorMsg
          healP' (PExp e)         ds     = PExp (healE' e ds)
          healP' (PExpT e t)      ds     = PExpT (healE' e ds) t
          healP' _                _      = errorMsg

          healE' :: Expression -> [Direction] -> Expression
          healE' ExpCut      []               = case sp of
                                                  (PExp e) -> e
                                                  _        -> errorMsg
          healE' (ExpF n es) ((DBranch i):ds) = if i >= 1 && i <= length es
                                                then let (es1,es2) = splitAt (i-1) es
                                                         e' = healE' (head es2) ds
                                                     in ExpF n (es1++(e':tail es2))
                                                else errorMsg
          healE' _           _      = errorMsg

          errorMsg = error "HealPredicate: invalid directions in cursor"

cursorDirections :: PredicateCursor -> [Direction]
-- cursorDirections pc returns the directions of the predicate cursor pc
cursorDirections (PC _ ds _) = ds

moveCursorM :: PredicateCursor -> [Direction] -> Maybe PredicateCursor
-- moveCursorM pc ds moves the cursor pc in the directions ds
-- returns Nothing if the directions are invalid
moveCursorM pc@(PC mp ds sp) ds' = cutPredicateM (healPredicate pc) (ds++ds')

moveCursor :: PredicateCursor -> [Direction] -> PredicateCursor
-- an unsafe version of moveCursorM
moveCursor pc ds = maybe (error "moveCursor: invalid directions") id (moveCursorM pc ds)

availableDirections :: PredicateCursor -> [Direction]
-- availableDirections pc returns the list of possible directions the cursor can take
-- some directions are synonyms (e.g. DLeft==DBranch 1)
availableDirections (PC mp ds sp) = if ds==[] then dirsP' sp else dirsP' sp ++ [DUp]
    where dirsP' (PBinary _ _ _) = [DLeft, DRight, DBranch 1, DBranch 2]
          dirsP' (PUnary _ _)    = [DDown, DBranch 1]
          dirsP' (PBinding _ _)  = [DDown, DBranch 1]
          dirsP' (PExp e)        = dirsE' e
          dirsP' (PExpT e t)     = dirsE' e
          dirsP' _               = []

          dirsE' (ExpF _ es) = map DBranch [1..length es]
          dirsE' _           = []

{- ---------- Some example cursors ---------- -} 


