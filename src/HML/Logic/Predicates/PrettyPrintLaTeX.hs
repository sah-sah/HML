{-# LANGUAGE OverloadedStrings #-}
{--
 -- PrettyPrintLaTeX.hs
 -- Convert Predicates into LaTeX expressions
 --}
module HML.Logic.Predicates.PrettyPrintLaTeX where

-- TODO: (1) precedence etc
--       (2) printing context
--       (3) could we add printing information to the Predicate data type
--           without having to change the actual data type??
--       (4) Can we use PredicateCursors to edit LaTeXContext to allow user
--           to play with the latex output (So LaTeXContext would need
--           functions like printPredicate :: Predicate -> Maybe LaTeX
--                          printExpression :: Expression -> Maybe LaTex
--           Such functions might be more useful than printFunction below
--           We would need default functions that could be updated with specific cases

import Data.List(intercalate)
import Data.Text(pack, unpack, replace, cons, snoc)

--import Control.Monad
import HML.Logic.Predicates.Predicates
import HML.Logic.Predicates.PredicateCursors

import Text.LaTeX
import Text.LaTeX.Base.Class(comm1)
import Text.LaTeX.Base.Syntax(LaTeX(..))
import qualified Text.LaTeX.Base.Math as M
import Text.LaTeX.Packages.AMSMath(thinspace, quad)
--import Text.LaTeX.Packages.Color

import Control.Monad(mplus)
import Control.Monad.State(State, evalState, get, put)

type LaTeXPP = State LaTeXContext

-- can we define a function printExp :: Expression -> LaTeX, then update it?
-- or, have a list of [(Expression,Latex)] which we check first, otherwise use toLaTeX
data LaTeXContext = LCon { printFunction :: String -> [LaTeX] -> Maybe LaTeX }

defaultContext :: LaTeXContext
defaultContext = LCon { printFunction = (\s ls -> Nothing) }

setLaTeXContext :: LaTeXContext
setLaTeXContext = updatePrintFunction printSetFn defaultContext

updatePrintFunction :: (String -> [LaTeX] -> Maybe LaTeX) -> LaTeXContext -> LaTeXContext
updatePrintFunction f lcon = lcon { printFunction = newPrintFunction }
    where newPrintFunction n args = (f n args) `mplus` (printFunction lcon n args)

{- Printing set functions (NOTE this should go in Axioms.Set) -}
printSetFn :: String -> [LaTeX] -> Maybe LaTeX
printSetFn "setElem"   [a,b] = Just $ M.in_ a b
printSetFn "setSubset" [a,b] = Just $ M.subset a b
printSetFn "setEqual"  [a,b] = Just $ (M.=:) a b
printSetFn "setUnion"  [a,b] = Just $ M.cup a b
printSetFn _           _     = Nothing

latexPPinContext :: LaTeXContext -> Predicate -> String
latexPPinContext lcon p = unpack $ render $ evalState (toLaTeXPred p) lcon

latexPPinContextCursor :: LaTeXContext -> PredicateCursor -> String
latexPPinContextCursor lcon (PC mp ds sp) = unpack $ replace "(@)" spL mpL
    where mpL = pack (latexPPinContext lcon mp)
          spL = pack ("\\left[" ++ latexPPinContext lcon sp ++ "\\right]")

latexPrettyPrint :: Predicate -> String
latexPrettyPrint p = unpack $ render $ evalState (toLaTeXPred p) lcon
    where lcon = updatePrintFunction printSetFn defaultContext

{- LaTeX pretty printing predicates -}

toLaTeXPatVar :: String -> LaTeX -> LaTeXPP LaTeX
toLaTeXPatVar t l = return $ textrm (raw $ pack t) <> between l (raw "\\{") (raw "\\}")

-- | pretty prints a predicate in LaTeX
toLaTeXPred :: Predicate -> LaTeXPP LaTeX
toLaTeXPred (PExp e)          = toLaTeXExp e
toLaTeXPred (PAnd p q)        = toLaTeXBinPred "PAnd" p q
toLaTeXPred (POr p q)         = toLaTeXBinPred "POr" p q
toLaTeXPred (PImp p q)        = toLaTeXBinPred "PImp" p q
toLaTeXPred (PIff p q)        = toLaTeXBinPred "PIff" p q
toLaTeXPred (PNot p)          = do pL <- bracketLPP (isCompoundP p) (toLaTeXPred p)
                                   return $ comm1 "lnot" pL
toLaTeXPred (PBinding bt v p) = do vL <- toLaTeXVar v
                                   pL <- toLaTeXPred p
                                   return $ qual <> thinspace <> thinspace <> vL <> raw "." <> pL
    where qual = if bt == Forall then M.forall else M.exists
toLaTeXPred (PPatVar s)       = toLaTeXPatVar "P" (raw $ pack s)
toLaTeXPred (PCut)            = return $ raw "(@)"


toLaTeXBinPred :: String -> Predicate -> Predicate -> LaTeXPP LaTeX
toLaTeXBinPred bop p q = do pL <- bracketLPP (shouldBracketBinaryL bop p) (toLaTeXPred p)
                            opL <- toLaTeXBOp bop
                            qL <- bracketLPP (shouldBracketBinaryR bop q) (toLaTeXPred q)
                            return $ opL pL qL

toLaTeXBOp :: String -> LaTeXPP (LaTeX -> LaTeX -> LaTeX)
toLaTeXBOp "PAnd" = return wedge
toLaTeXBOp "POr"  = return vee
toLaTeXBOp "PXOr" = return oplus
toLaTeXBOp "PImp" = return $ between rightarrow
toLaTeXBOp "PIff" = return equiv

{- Precedence -}

-- | shouldBracketBinaryL op p
-- | determines whether we should bracket p in p op q
shouldBracketBinaryL :: String -> Predicate -> Bool
shouldBracketBinaryL op (PAnd _ _) =    (precedenceBOp "PAnd" <= precedenceBOp op)
                                     && (op /= "PAnd" || (not $ assocBOp op))
shouldBracketBinaryL op (POr  _ _) =    (precedenceBOp "POr" <= precedenceBOp op)
                                     && (op /= "POr" || (not $ assocBOp op))
shouldBracketBinaryL op (PImp _ _) =    (precedenceBOp "PImp" <= precedenceBOp op)
                                     && (op /= "PImp" || (not $ assocBOp op))
shouldBracketBinaryL op (PIff _ _) =    (precedenceBOp "PIff" <= precedenceBOp op)
                                     && (op /= "PIff" || (not $ assocBOp op))
shouldBracketBinaryL op p          = precedenceP p <= precedenceBOp op

shouldBracketBinaryR = shouldBracketBinaryL

precedenceP :: Predicate -> Int
-- 10 is max and indicates that they never need brackets
-- 0 is the minimum and indicates that they always need brackets (unless they are the top level statement)
precedenceP (PExp _)         = 10
precedenceP (PAnd _ _)       = precedenceBOp "PAnd"
precedenceP (POr _ _)        = precedenceBOp "POr"
precedenceP (PImp _ _)       = precedenceBOp "PImp"
precedenceP (PIff _ _)       = precedenceBOp "PIff"
precedenceP (PNot _)         = 8
precedenceP (PBinding _ _ _) = 10
precedenceP (PPatVar _)      = 10
precedenceP (PCut)           = 10

precedenceBOp :: String -> Int
precedenceBOp "PAnd" = 6
precedenceBOp "POr"  = 6
precedenceBOp "PImp" = 3
precedenceBOp "PIff" = 3

assocBOp :: String -> Bool
assocBOp "PAnd" = True
assocBOp "POr"  = True
assocBOp "PImp" = False
assocBOp "PIff" = True

{- LaTeX pretty printing expressions -}

-- | pretty prints an expression in LaTeX
toLaTeXExp :: Expression -> LaTeXPP LaTeX
toLaTeXExp (ExpN pn)    = toLaTeXPN pn
toLaTeXExp (ExpFn n es) = do lcon <- get
                             -- get args in LaTeX
                             esL <- sequence $ map toLaTeXExp es
                             let args = foldl1 (\l1 l2 -> l1 <> (raw ",") <> l2) esL
                             -- try printFunction from lcon
                             let fnM = (printFunction lcon) n esL
                             case fnM of
                               (Just l) -> return l
                               Nothing  -> return $ textrm (raw $ pack n) <> autoParens args
toLaTeXExp (ExpEquals e f) = do eL <- toLaTeXExp e
                                fL <- toLaTeXExp f
                                return $ eL <> raw "=" <> fL
toLaTeXExp (ExpPatVar s) = toLaTeXPatVar "E" (raw $ pack s)
toLaTeXExp (ExpCut) = return $ raw "(@)"

{- LaTeX pretty printing Names -}

toLaTeXPN :: Name -> LaTeXPP LaTeX
toLaTeXPN (Var v)      = toLaTeXVar v
toLaTeXPN (Constant s) = toLaTeXSpecial s

toLaTeXVar :: Variable -> LaTeXPP LaTeX
toLaTeXVar (SimpleVar s)    = return $ raw (pack s)
toLaTeXVar (IndexedVar s e) = do eL <- toLaTeXExp e
                                 return $ raw (pack s) <> raw "_{" <> eL <> raw "}"
toLaTeXVar (VPatVar s)      = toLaTeXPatVar "V" (raw $ pack s)
toLaTeXVar (VCut)           = return $ raw "(@)"

toLaTeXSpecial :: Special -> LaTeXPP LaTeX
toLaTeXSpecial (SInt n)    = return $ raw (pack $ show n) 
toLaTeXSpecial (SBool b)   = return $ raw (pack $ show b) 
toLaTeXSpecial (SEmptySet) = return $ raw "0" 
toLaTeXSpecial (SZ)        = return $ raw "Z"
toLaTeXSpecial (SZplus)    = return $ raw "Z+"
toLaTeXSpecial (SZn e)     = do eL <- toLaTeXExp e
                                return $ raw "Z_{" <> eL <> raw "}"
toLaTeXSpecial (SFinite e) = do eL <- toLaTeXExp e
                                return $ raw "\\{1,\\cdots," <> eL <> raw "\\}"

{- Helper functions -}

bracketLPP :: Bool -> LaTeXPP LaTeX -> LaTeXPP LaTeX
bracketLPP False ls = ls
bracketLPP True  ls = do l <- ls
                         -- TODO: check whether we need auto brackets
                         -- OR: should we always use auto brackets
                         return $ M.autoParens l

