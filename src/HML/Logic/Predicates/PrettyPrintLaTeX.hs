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

updatePrintFunction :: (String -> [LaTeX] -> Maybe LaTeX) -> LaTeXContext -> LaTeXContext
updatePrintFunction f lcon = lcon { printFunction = newPrintFunction }
    where newPrintFunction n args = (f n args) `mplus` (printFunction lcon n args)

{- Printing set functions (NOTE this should go in Axioms.Set) -}
printSetFn :: String -> [LaTeX] -> Maybe LaTeX
printSetFn "setElem"   [a,b] = Just $ M.in_ a b
printSetFn "setSubset" [a,b] = Just $ M.subset a b
printSetFn "setEqual"  [a,b] = Just $ (M.=:) a b
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
toLaTeXPred (PEmpty)         = return TeXEmpty
toLaTeXPred (PExp e)         = toLaTeXExp e
toLaTeXPred (PExpT e t)      = do eL <- toLaTeXExp e
                                  tL <- toLaTeXType t
                                  return $ eL <> textrm (raw " :: ") <> tL
toLaTeXPred (PBinary op p q) = do pL <- bracketLPP (shouldBracketBinaryL op p) (toLaTeXPred p)
                                  opL <- toLaTeXBOp op
                                  qL <- bracketLPP (shouldBracketBinaryR op q) (toLaTeXPred q)
                                  return $ opL pL qL
toLaTeXPred (PUnary op p)    = do opL <- toLaTeXUOp op
                                  pL <- bracketLPP (isCompoundP p) (toLaTeXPred p)
                                  return $ opL pL
toLaTeXPred (PBinding pb p)  = do pbL <- toLaTeXPB pb
                                  pL <- toLaTeXPred p
                                  return $ pbL <> pL
toLaTeXPred (PPatVar s)      = toLaTeXPatVar "P" (raw $ pack s)
toLaTeXPred (PCut)           = return $ raw "(@)"

toLaTeXBOp :: PBOp -> LaTeXPP (LaTeX -> LaTeX -> LaTeX)
toLaTeXBOp (PAnd) = return wedge
toLaTeXBOp (POr)  = return vee
toLaTeXBOp (PXOr) = return oplus
toLaTeXBOp (PImp) = return $ between rightarrow
toLaTeXBOp (PIff) = return equiv

toLaTeXUOp :: PUOp -> LaTeXPP (LaTeX -> LaTeX)
toLaTeXUOp PNot = return $ comm1 "lnot"

{- Precedence -}

-- | shouldBracketBinaryL op p
-- | determines whether we should brack p in p op q
shouldBracketBinaryL :: PBOp -> Predicate -> Bool
shouldBracketBinaryL op (PBinary opP _ _) =    (precOpP <= precOp)
                                            && (op /= opP || (not $ assocBOp op))
    where precOp = precedenceBOp op
          precOpP = precedenceBOp opP
shouldBracketBinaryL op p                 = precP <= precOp
    where precOp = precedenceBOp op
          precP = precedenceP p

shouldBracketBinaryR = shouldBracketBinaryL

precedenceP :: Predicate -> Int
-- 10 is max and indicates that they never need brackets
-- 0 is the minimum and indicates that they always need brackets (unless they are the top level statement)
precedenceP (PEmpty)         = 10
precedenceP (PExp _)         = 10
precedenceP (PExpT _ _)      = 0
precedenceP (PBinary op _ _) = precedenceBOp op
precedenceP (PUnary op _)    = precedenceUOp op
precedenceP (PBinding _ _)   = 10
precedenceP (PPatVar _)      = 10
precedenceP (PCut)           = 10

precedenceBOp :: PBOp -> Int
precedenceBOp (PAnd) = 6
precedenceBOp (POr)  = 6
precedenceBOp (PXOr) = 6
precedenceBOp (PImp) = 3
precedenceBOp (PIff) = 3

assocBOp :: PBOp -> Bool
assocBOp (PAnd) = True
assocBOp (POr)  = True
assocBOp (PXOr) = False -- ??? Check this
assocBOp (PImp) = False
assocBOp (PIff) = True

precedenceUOp :: PUOp -> Int
precedenceUOp (PNot) = 8

{- LaTeX pretty printing predicate bindings -}

toLaTeXPB :: PredicateBinding -> LaTeXPP LaTeX
-- TODO: usually we need \,\, after the forall, exists
toLaTeXPB (Forall pn p) = do pnL <- toLaTeXPN pn
                             pL <- toLaTeXPred p
                             let st = if p == PEmpty then TeXEmpty
                                                     else textrm " s.t. " <> pL <> raw "."
                             return $ M.forall <> thinspace <> thinspace <> pnL <> st <> quad
toLaTeXPB (Exists pn p) = do pnL <- toLaTeXPN pn
                             pL <- toLaTeXPred p
                             let st = if p == PEmpty then TeXEmpty
                                                     else textrm " s.t. " <> pL <> raw "."
                             return $ M.exists <> thinspace <> thinspace <> pnL <> st <> quad

{- LaTeX pretty printing expressions -}

-- | pretty prints an expression in LaTeX
toLaTeXExp :: Expression -> LaTeXPP LaTeX
toLaTeXExp (ExpN pn) = toLaTeXPN pn
toLaTeXExp (ExpF n es) = do lcon <- get
                            -- get args in LaTeX
                            esL <- sequence $ map toLaTeXExp es
                            let args = foldl1 (\l1 l2 -> l1 <> (raw ",") <> l2) esL
                            -- try printFunction from lcon
                            let fnM = (printFunction lcon) n esL
                            case fnM of
                              (Just l) -> return l
                              Nothing  -> return $ textrm (raw $ pack n) <> autoParens args
toLaTeXExp (ExpPatVar s) = toLaTeXPatVar "E" (raw $ pack s)
toLaTeXExp (ExpCut) = return $ raw "(@)"

{- LaTeX pretty printing types -}

-- | pretty prints types in LaTeX
toLaTeXType :: Type -> LaTeXPP LaTeX
toLaTeXType t = return $ raw "type"

{- LaTeX pretty printing PNames -}

toLaTeXPN :: PName -> LaTeXPP LaTeX
toLaTeXPN (PVar s)    = return $ raw (pack s)
toLaTeXPN (PConst s)  = return $ raw (pack s)
toLaTeXPN (PInt n)    = return $ raw (pack $ show n)
toLaTeXPN (PTrue)     = return $ raw ("T")
toLaTeXPN (PFalse)    = return $ raw ("F")
toLaTeXPN (NPatVar s) = toLaTeXPatVar "N" (raw $ pack s)

{- Helper functions -}

bracketLPP :: Bool -> LaTeXPP LaTeX -> LaTeXPP LaTeX
bracketLPP False ls = ls
bracketLPP True  ls = do l <- ls
                         -- TODO: check whether we need auto brackets
                         -- OR: should we always use auto brackets
                         return $ M.autoParens l

