{--
 -- PropositionsCursor.hs
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
--
-- We should restructure and rename the modules
-- HML.Logic.Propositions.Propositions
-- HML.Logic.Propositions.Cursor
-- HML.Logic.Propositions.LogicLaws
-- HML.Logic.Propositions.Proof
-}
module HML.Logic.Propositions.PropositionsCursor where

import HML.Logic.Propositions.Propositions

import Data.List
import Control.Monad

{- ---------- Data types ---------- -}

data Direction = DLeft | DRight | DDown | DUp
    deriving (Show, Eq)

data CursorProp = CP Proposition [Direction] Proposition

{- ---------- Typeclass instances ---------- -}

instance Show CursorProp where
    show (CP mt ds st) = replaceCut' (show mt)
        where replaceCut' (a:b:c:str) | [a,b,c] == "(@)" = ("[" ++ show st ++ "]") ++ str
                                      | otherwise        = a:replaceCut' (b:c:str)

{-
showCursor :: CursorProp -> String
--showCursor (CP mt ds st) = "Cursor: " ++ showP mt ++ " " ++ show ds ++ " " ++ showP st
showCursor (CP mt ds st) = showC' False mt
    where showC' b (Name n)        = n
          -- TODO: replaces the True's below with values that depend on op
          showC' b (Binary op p q) = bracket b (showC' (sb op) p ++ showBOp op ++ showC' (sb op) q)
          showC' b (Unary op p)    = showUOp op ++ showC' True p
          showC' b (Constant bool) = take 1 $ show bool
          showC' b (Cut)           = "[" ++ showC' False st ++ "]"

          -- should bracket?
          sb Imp = False
          sb Iff = False
          sb _   = True

          bracket :: Bool -> String -> String
          bracket b str | b         = "(" ++ str ++ ")"
                        | otherwise = str
-}

{- ---------- Creating cursors ---------- -} 

cutPropositionM :: Proposition -> [Direction] -> Maybe CursorProp
-- cutProposition p ds cuts the proposition into a main tree and subtree
-- at the point specified by ds
cutPropositionM p ds = do cds <- cleanDs' (ds, [])
                          (mt,st) <- splitTree' p cds 
                          return (CP mt ds st) -- return the original ds? or cds? 
    where splitTree' p               []          = Just (Cut,p)
          splitTree' (Binary op p q) (DLeft:ds)  = do (mt',st) <- splitTree' p ds
                                                      return (Binary op mt' q, st)
          splitTree' (Binary op p q) (DRight:ds) = do (mt',st) <- splitTree' q ds
                                                      return (Binary op p mt', st)
          splitTree' (Unary op p)    (DDown:ds)  = do (mt', st) <- splitTree' p ds
                                                      return (Unary op mt', st)
          splitTree' _               _           = Nothing

          -- remove DUp's if needed, return Nothing if the DUp's cannot be removed
          cleanDs' ([],st) = Just (reverse st)
          cleanDs' (d:ds,st) | d == DUp && st==[] = Nothing
                             | d == DUp && st/=[] = cleanDs' (ds,tail st)
                             | otherwise          = cleanDs' (ds,d:st)

cutProposition :: Proposition -> [Direction] -> CursorProp
-- an unsafe version of cutPropositionM
cutProposition p ds = case cutPropositionM p ds of
                        (Just cp) -> cp
                        Nothing   -> error "cutProposition: invalid directions"

healProposition :: CursorProp -> Proposition
-- healProposition cp returns the original, uncut proposition underlying cp
-- NOTE: it assumes that the directions are valid
healProposition (CP mt ds st) = heal mt ds
    where heal Cut             []          = st
          heal (Binary op p q) (DLeft:ds)  = Binary op (heal p ds) q
          heal (Binary op p q) (DRight:ds) = Binary op p (heal q ds)
          heal (Unary op p)    (DDown:ds)  = Unary op (heal p ds)
          heal _               _           = error "healProposition: invalid directions in cursor"

getDirections :: CursorProp -> [Direction]
getDirections (CP mt ds st) = ds

moveCursorM :: CursorProp -> Direction -> Maybe CursorProp
-- moveCursor cp d moves the cursor cp in direction d
moveCursorM cp@(CP mt ds st) d | d == DUp  = if ds==[] 
                                             then Nothing
                                             else cutPropositionM p (init ds)
                               | otherwise = cutPropositionM p (ds++[d])
    where p = healProposition cp

moveCursor :: CursorProp -> Direction -> CursorProp
-- an unsafe version of moveCursorM
moveCursor cp d = case moveCursorM cp d of
                    (Just cp) -> cp
                    Nothing   -> error "moveCursor: invalid direction"

runCursorM :: CursorProp -> [Direction] -> Maybe CursorProp
-- runCursorM cp ds performs a sequence of moveCursorM's
runCursorM = foldM moveCursorM

runCursor :: CursorProp -> [Direction] -> CursorProp
-- an unsafe version of runCursorM
runCursor = foldl moveCursor

cursorDirections :: CursorProp -> [Direction]
-- cursorDirections cp returns the list of possible directions the cursor can take
cursorDirections (CP mt ds st) = if ds==[] then dirs' st else dirs' st ++ [DUp]
    where dirs' (Binary op p q) = [DLeft, DRight]
          dirs' (Unary op p)    = [DDown]
          dirs' _               = []


{- ---------- Some example cursors ---------- -} 

cpA = cutProposition statementA []