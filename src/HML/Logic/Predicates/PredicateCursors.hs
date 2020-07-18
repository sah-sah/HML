{--
 -- PredicateCursors.hs
 -- A module for moving through predicate expressions
 --}

module HML.Logic.Predicates.PredicateCursors where

import HML.Logic.Predicates.Predicates

--import Data.List
--import Control.Monad

{- ---------- Data Types ---------- -}

data Direction = DLeft | DRight | DDown | DUp | DBranch Int
    deriving (Show, Eq)

{- ---------- Predicate Expression Cursors ---------- -}

data PredicateCursor = PC Predicate [Direction] Predicate
    deriving (Show, Eq)

{- ---------- Show instances ---------- -}
{-
instance Show PredicateCursor where
    show (PC mt ds st) = replaceCut' (show mt)
        where replaceCut' (a:b:c:str) | [a,b,c] == "(@)" = ("[" ++ show st ++ "]") ++ str
                                      | otherwise        = a:replaceCut' (b:c:str)
-}
{- ---------- Construction Functions ---------- -}

cutPredicateM :: Predicate -> [Direction] -> Maybe PredicateCursor
-- cutPredicateM p ds cuts the predicate p into a main tree and subtree
-- at the point specified by ds
-- if the directions are invalid, it returns Nothing
cutPredicateM p ds = do cds <- cleanDs' (ds, [])
                        (mp,sp) <- splitP' p cds 
                        return (PC mp cds sp) -- return the original ds? or cds? 
    where splitP' :: Predicate -> [Direction] -> Maybe (Predicate, Predicate)
          splitP' p                []     = Just (PCut,p)
          splitP' (PExp e)         ds     = do (me, sp) <- splitE' e ds
                                               return (PExp me, sp)
          splitP' (PAnd p q)       (d:ds) = case d of
                                              DBranch 1 -> do (mp, sp) <- splitP' p ds
                                                              return (PAnd mp q, sp)
                                              DBranch 2 -> do (mq, sq) <- splitP' q ds
                                                              return (PAnd p mq, sq)
                                              _        -> Nothing
          splitP' (POr p q)        (d:ds) = case d of
                                              DBranch 1 -> do (mp, sp) <- splitP' p ds
                                                              return (POr mp q, sp)
                                              DBranch 2 -> do (mq, sq) <- splitP' q ds
                                                              return (POr p mq, sq)
                                              _        -> Nothing
          splitP' (PImp p q)       (d:ds) = case d of
                                              DBranch 1 -> do (mp, sp) <- splitP' p ds
                                                              return (PImp mp q, sp)
                                              DBranch 2 -> do (mq, sq) <- splitP' q ds
                                                              return (PImp p mq, sq)
                                              _        -> Nothing
          splitP' (PIff p q)       (d:ds) = case d of
                                              DBranch 1 -> do (mp, sp) <- splitP' p ds
                                                              return (PIff mp q, sp)
                                              DBranch 2 -> do (mq, sq) <- splitP' q ds
                                                              return (PIff p mq, sq)
                                              _        -> Nothing
          splitP' (PNot p)         (d:ds) = case d of
                                              DBranch 1 -> do (mp,sp) <- splitP' p ds
                                                              return (PNot mp, sp)
                                              _        -> Nothing
          splitP' (PBinding t v p) (d:ds) = case d of
                                              DBranch 1 -> do (mv, sv) <- splitV' v ds
                                                              return (PBinding t mv p, sv)
                                              DBranch 2 -> do (mp,sp) <- splitP' p ds
                                                              return (PBinding t v mp, sp)
                                              _         -> Nothing
          splitP' _                _           = Nothing

          splitE' :: Expression -> [Direction] -> Maybe (Expression, Predicate)
          splitE' e               []               = Just (ExpCut, PExp e)
          splitE' (ExpN n)        ds               = do (mn, sn) <- splitN' n ds
                                                        return (ExpN mn, sn)
          splitE' (ExpFn n es)    ((DBranch i):ds) = if i >= 1 && i <= length es
                                                       then let (es1,es2) = splitAt (i-1) es
                                                            in do (me, sp) <- splitE' (head es2) ds
                                                                  return (ExpFn n (es1++(me:tail es2)), sp)
                                                       else Nothing
          splitE' (ExpEquals e f) (d:ds)           = case d of
                                                       DBranch 1 -> do (me,se) <- splitE' e ds
                                                                       return (ExpEquals me f, se)
                                                       DBranch 2 -> do (mf,sf) <- splitE' f ds
                                                                       return (ExpEquals e mf, sf)
                                                       _         -> Nothing
          splitE' _               _                = Nothing

          splitN' :: Name -> [Direction] -> Maybe (Name, Predicate)
          splitN' (Var v)      ds = do (mv,sv) <- splitV' v ds
                                       return (Var mv, sv)
          splitN' (Constant s) ds = do (ms,ss) <- splitS' s ds
                                       return (Constant ms, ss)

          splitV' :: Variable -> [Direction] -> Maybe (Variable, Predicate)
          splitV' v                []     = Just (VCut, PExp (ExpN (Var v)))
          splitV' (IndexedVar s e) (d:ds) = case d of
                                              DBranch 1 -> do (me,se) <- splitE' e ds
                                                              return (IndexedVar s me,se)
                                              _         -> Nothing
          splitV' _                (d:ds) = Nothing

          splitS' :: Special -> [Direction] -> Maybe (Special, Predicate)
          splitS' (SZn e)     ds = do (me,se) <- splitE' e ds
                                      return (SZn me, se)
          splitS' (SFinite e) ds = do (me,se) <- splitE' e ds
                                      return (SFinite me, se)
          splitS' _           ds = Nothing

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
healPredicate (PC mp ds sp) = healP mp ds
    where healP :: Predicate -> [Direction] -> Predicate
          healP (PCut)          []      = sp
          healP (PExp e)         ds     = PExp (healE e ds)
          healP (PAnd p q)       (d:ds) = case d of
                                            DBranch 1 -> PAnd (healP p ds) q
                                            DBranch 2 -> PAnd p (healP q ds)
                                            _         -> errorMsg
          healP (POr p q)        (d:ds) = case d of
                                            DBranch 1 -> POr (healP p ds) q
                                            DBranch 2 -> POr p (healP q ds)
                                            _         -> errorMsg
          healP (PImp p q)       (d:ds) = case d of
                                            DBranch 1 -> PImp (healP p ds) q
                                            DBranch 2 -> PImp p (healP q ds)
                                            _         -> errorMsg
          healP (PIff p q)       (d:ds) = case d of
                                            DBranch 1 -> PIff (healP p ds) q
                                            DBranch 2 -> PIff p (healP q ds)
                                            _         -> errorMsg
          healP (PNot p)         (d:ds) = case d of
                                            DBranch 1 -> PNot (healP p ds)
                                            _         -> errorMsg
          healP (PBinding t v p) (d:ds) = case d of
                                            DBranch 1 -> PBinding t (healV v ds) p
                                            DBranch 2 -> PBinding t v (healP p ds)
                                            _         -> errorMsg
          healP _                _      = errorMsg

          healE :: Expression -> [Direction] -> Expression
          healE (ExpCut)        [] = case sp of
                                       (PExp e) -> e
                                       _        -> errorMsg
          healE (ExpFn n es)    ((DBranch i):ds) = if i >= 1 && i <= length es
                                                     then let (es1,es2) = splitAt (i-1) es
                                                              e' = healE (head es2) ds
                                                          in ExpFn n (es1++(e':tail es2))
                                                     else errorMsg
          healE (ExpEquals e f) (d:ds)           = case d of
                                                     DBranch 1 -> ExpEquals (healE e ds) f
                                                     DBranch 2 -> ExpEquals e (healE f ds)
                                                     _         -> errorMsg
          healE _               _                = errorMsg

          healN :: Name -> [Direction] -> Name
          healN (Var v)      ds = Var (healV v ds)
          healN (Constant s) ds = Constant (healS s ds)

          healV :: Variable -> [Direction] -> Variable
          healV (VCut)           []     = case sp of
                                            PExp (ExpN (Var v)) -> v
                                            _                   -> errorMsg
          healV (IndexedVar s e) (d:ds) = case d of
                                            DBranch 1 -> IndexedVar s (healE e ds)
                                            _         -> errorMsg
          healV _                (d:ds) = errorMsg

          healS :: Special -> [Direction] -> Special
          healS (SZn e)     ds = SZn (healE e ds)
          healS (SFinite e) ds = SFinite (healE e ds)
          healS _           ds = errorMsg

          errorMsg = error "PredicateCursors(healPredicate): invalid directions in cursor"

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

renameBoundVariableAtCut :: String -> String -> PredicateCursor -> Maybe PredicateCursor
renameBoundVariableAtCut xn yn (PC mp ds sp) = do sp' <- renameBoundVariable xn yn sp
                                                  return $ PC mp ds sp'

{-
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
-}
{- ---------- Some example cursors ---------- -} 


