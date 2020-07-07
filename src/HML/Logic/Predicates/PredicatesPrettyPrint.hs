{-# LANGUAGE OverloadedStrings #-}
{--
 -- PredicatesPrettyPrint.hs
 -- :l ./HML/Logic/PredicateLogic/PredicatesPrettyPrint.hs from devel directory
 -- A module for pretty printing predicatesPrettyPrint
 --}
module HML.Logic.Predicates.PredicatesPrettyPrint where

-- TODO: might need to make it more general
-- prettyPrintP :: (Doc a) => Predicate -> a
-- where Doc a has function like a -> String
-- if we want to print to LaTeX e.g. 

import Data.List(intercalate)
import Data.Text(pack, unpack, replace, cons, snoc)

--import Control.Monad
import HML.Logic.Predicates.Predicates
import HML.Logic.Predicates.PredicateCursors

-- can add extra printing functions as needed, e.g. printPName
data PrintContext = PCon { printFunction :: String -> [String] -> Maybe String
                         }

noContext :: PrintContext
noContext = PCon { printFunction = \_ _ -> Nothing
                 }

printSetFn :: String -> [String] -> Maybe String
printSetFn n args | n == "setSubset" && length args == 2 = Just (intercalate " " [args!!0,"\\subset",args!!1])
                  | n == "setElem"   && length args == 2 = Just (intercalate " " [args!!0,"\\in",args!!1])
                  | n == "setEqual"  && length args == 2 = Just (intercalate " " [args!!0,"=",args!!1])
                  | otherwise = Nothing

stdContext :: PrintContext
stdContext = PCon { printFunction = printSetFn }

bracketPP :: Bool -> String -> String
bracketPP (True)  str = "("++str++")"
bracketPP (False) str = str

prettyPrintT :: PrintContext -> Type -> String
prettyPrintT pc (AbstractSetT) = "SET"
prettyPrintT pc (PredicateT)   = "BOOL"
prettyPrintT pc (EmptyT)       = "()"

prettyPrintPN :: PrintContext -> PName -> String
prettyPrintPN pc (PVar n)    = n
prettyPrintPN pc (PConst n)  = n
prettyPrintPN pc (PTrue)     = "T"
prettyPrintPN pc (PFalse)    = "F"
prettyPrintpN pc (NPatVar n) = "N{"++n++"}"

--prettyPrintExp :: Bool -> Expression -> String
prettyPrintExp pc (ExpN pn)     = prettyPrintPN pc pn
-- we could use precedence here 
prettyPrintExp pc (ExpF n es)   = maybe def id ((printFunction pc) n (map ppE' es))
    where ppE' e = bracketPP (isCompoundExp e) $ prettyPrintExp pc e
          def    = intercalate " " (n:map ppE' es) -- default
prettyPrintExp pc (ExpPatVar n) = "E{"++n++"}"
prettyPrintExp pc (ExpCut)      = "(@)"

prettyPrintPB pc (Forall pn p) | p == PEmpty = "forall " ++ prettyPrintPN pc pn ++"."
                               | otherwise   = "forall " ++ prettyPrintPN pc pn ++ " s.t. " ++ prettyPrintP pc p ++ "."
prettyPrintPB pc (Exists pn p) | p == PEmpty = "exists " ++ prettyPrintPN pc pn ++"."
                               | otherwise   = "exists " ++ prettyPrintPN pc pn ++ " s.t. " ++ prettyPrintP pc p ++ "."

prettyPrintBOp pc (PAnd) = "&"
prettyPrintBOp pc (POr) = "|"
prettyPrintBOp pc (PXOr) = "x|"
prettyPrintBOp pc (PImp) = "->"
prettyPrintBOp pc (PIff) = "<->"

prettyPrintUOp pc (PNot) = "~" 

prettyPrintP pc (PEmpty)         = "()"
prettyPrintP pc (PExp e)         = prettyPrintExp pc e
prettyPrintP pc (PExpT e t)      = prettyPrintExp pc e ++ " :: " ++ prettyPrintT pc t
prettyPrintP pc (PBinary op p q) = let prec  = precedenceP (PBinary op p q)
                                       precP = precedenceP p
                                       precQ = precedenceP q
                                   in intercalate " " [bracketPP (precP <= prec) $ prettyPrintP pc p
                                                      ,prettyPrintBOp pc op
                                                      ,bracketPP (precQ <= prec) $ prettyPrintP pc q]
prettyPrintP pc (PUnary op p)    = intercalate " " [prettyPrintUOp pc op, bracketPP (isCompoundP p) $ prettyPrintP pc p]
prettyPrintP pc (PBinding pb p)  = intercalate " " [prettyPrintPB pc pb, prettyPrintP pc p]
prettyPrintP pc (PPatVar n)      = "P{"++n++"}"
prettyPrintP pc (PCut)           = "(@)"

precedenceP :: Predicate -> Int
-- 10 is max and indicates that they never need brackets
-- 0 is the minimum and indicates that they always need brackets (unless they are the top level statement)
precedenceP (PEmpty)         = 10
precedenceP (PExp _)         = 10
precedenceP (PExpT _ _)      = 0
precedenceP (PBinary op _ _) = precedenceBOp op
precedenceP (PUnary op _)    = precedenceUOp op
precedenceP (PBinding _ _)   = 0
precedenceP (PPatVar _)      = 10 
precedenceP (PCut)           = 10

precedenceBOp :: PBOp -> Int
precedenceBOp (PAnd) = 6
precedenceBOp (POr)  = 6
precedenceBOp (PXOr) = 6
precedenceBOp (PImp) = 3
precedenceBOp (PIff) = 3

precedenceUOp :: PUOp -> Int
precedenceUOp (PNot) = 8

prettyPrint = prettyPrintP stdContext

prettyPrintPC (PC mt ds st) = unpack $ replace "(@)" stT mtT
    where mtT = pack $ prettyPrint mt
          stT = snoc (cons '[' (pack $ prettyPrint st)) ']'
{-
Each call has responsibility of bracketing its parts, 
therefore, prettyPrint should never bracket the entire string, only its subexpressions/subpredicates
At each level, we need to inspect the subparts and determine whether or not to bracket them, the default
is to bracket them, so we only really need to determine whether to not bracket them

Bracketing rules
PEmpty : never bracket
PExp : never bracket, expressions always have higher precedence than predicate expressions
PExpT : bracket unless it is the top level expression (make the limit of the type clear)
PBinary op p q : depends on precedence 
   &, |, x|
   Imp, Iff

  Consider & 
   A & B, if A = _ & _, then no bracket, 
          if A = _ | _, then bracket
          if A = _ x| _, then bracket
          if A = _ -> _, then bracket
          if A = _ <-> _, then bracket
   (A op B) -> C
Don't need to bracket A in A op B if A has a higher precedence
Order of precedence is 
Simple expressions
not
&, |, x|
->, <->
compound expressions
type expressions

-}