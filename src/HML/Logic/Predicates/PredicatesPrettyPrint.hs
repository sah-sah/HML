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
-- how to print, also precedence for using functions in expressions

data Fixty = Prefix | Infix | Nofix
    deriving (Show, Eq)

type PrintInfo = (String,(Fixty,Int,String))

data PrintContext = PCon { printFunction :: [PrintInfo]
                         }

-- TODO: fix up the printing contexts
-- change function to association lists and use lookup

noContext :: PrintContext
noContext = PCon { printFunction = []
                 }

-- todo: add < + etc
stdPrintInfo :: [PrintInfo]
stdPrintInfo = [("setSubset",       (Infix,4,"\\subseteq"))
               ,("setElem",         (Infix,2,"\\in"))
               ,("setEqual",        (Infix,4,"\\="))
               ,("setUnion",        (Infix,8,"\\union"))
               ,("setIntersection", (Infix,8,"\\intersect"))
               -- arithmetic operations
               ,("arithmeticPlus", (Infix,4,"+"))
               ,("arithmeticSub",  (Infix,4,"-"))
               ,("arithmeticMul",  (Infix,6,"*"))
               ,("arithmeticDiv",  (Infix,6,"/"))
               ,("arithmeticNeg",  (Prefix,8,"-"))
               -- numeric comparison operations
               ,("numLTEQ", (Infix,2,"<="))
               ,("numLT",   (Infix,2,"<"))
               ,("numMTEQ", (Infix,2,">="))
               ,("numMT",   (Infix,2,">"))
               ,("numEQ",   (Infix,2,"="))
               ]

stdContext :: PrintContext
stdContext = PCon { printFunction = stdPrintInfo }

prettyPrint = prettyPrintP (noContext { printFunction = stdPrintInfo })

prettyPrintFn :: PrintContext -> String -> [Expression] -> String
prettyPrintFn pc n es = case lookup n (printFunction pc) of
                          Nothing       -> defaultStr n
                          Just (f,p,n') -> case f of
                                             Prefix -> if length es == 1 then let e = head es
                                                                                  eStr = prettyPrintE pc e
                                                                              in n' ++ bracketPP (isCompoundE e) eStr
                                                                         else defaultStr n'
                                             Infix -> if length es == 2 then let e = head es
                                                                                 f = last es
                                                                                 eStr = prettyPrintE pc e
                                                                                 fStr = prettyPrintE pc f
                                                                                 precE = precedenceE pc e
                                                                                 precF = precedenceE pc f
                                                                             in intercalate " " [bracketPP (precE <= p) eStr
                                                                                                ,n'
                                                                                                ,bracketPP (precF <= p) fStr]
                                                                        else defaultStr n'
                                             Nofix -> defaultStr n'
    where defaultStr s = let es' = intercalate "," (map (prettyPrintE pc) es) in s++"("++es'++")"

precedenceE :: PrintContext -> Expression -> Int
-- 10 never needs brackets, 0 always needs brackets
precedenceE pc (ExpN _)        = 10
precedenceE pc (ExpFn n _)     = case lookup n (printFunction pc) of
                                   Nothing       -> 10
                                   Just (f,p,n') -> p
precedenceE pc (ExpEquals _ _) = 0
precedenceE pc (ExpPatVar _)   = 10
precedenceE pc (ExpCut)        = 10

bracketPP :: Bool -> String -> String
bracketPP (True)  str = "("++str++")"
bracketPP (False) str = str

prettyPrintV :: PrintContext -> Variable -> String
prettyPrintV pc (SimpleVar s)    = s
prettyPrintV pc (IndexedVar s e) = s++"_"++bracketPP (isCompoundE e) (prettyPrintE pc e)
prettyPrintV pc (VPatVar s)      = "V{"++s++"}"
prettyPrintV pc (VCut)           = "(@)"

prettyPrintN :: PrintContext -> Name -> String
prettyPrintN pc (Var v)      = prettyPrintV pc v
prettyPrintN pc (Constant s) = prettyPrintS pc s

prettyPrintS :: PrintContext -> Special -> String
prettyPrintS pc (SInt n)    = show n
prettyPrintS pc (SBool b)   = take 1 $ show b
prettyPrintS pc (SZ)        = "Z"
prettyPrintS pc (SZplus)    = "Z+"
prettyPrintS pc (SZn e)     = "Zn(" ++ (prettyPrintE pc e) ++ ")"
prettyPrintS pc (SFinite e) = "{1,...,"++(prettyPrintE pc e)++"}"

prettyPrintE :: PrintContext -> Expression -> String
prettyPrintE pc (ExpN n)        = prettyPrintN pc n
prettyPrintE pc (ExpFn f es)    = prettyPrintFn pc f es
prettyPrintE pc (ExpEquals e f) = (prettyPrintE pc e) ++ " = " ++ (prettyPrintE pc f)
prettyPrintE pc (ExpPatVar s)   = "E{"++s++"}"
prettyPrintE pc (ExpCut)        = "(@)"

prettyPrintP :: PrintContext -> Predicate -> String
prettyPrintP pc (PExp e)         = prettyPrintE pc e
prettyPrintP pc (PAnd p q)       = prettyPrintBinaryP pc ("&",precedenceP pc (PAnd p q)) p q
prettyPrintP pc (POr p q)        = prettyPrintBinaryP pc ("|",precedenceP pc (POr p q)) p q
prettyPrintP pc (PImp p q)       = prettyPrintBinaryP pc ("->",precedenceP pc (PImp p q)) p q
prettyPrintP pc (PIff p q)       = prettyPrintBinaryP pc ("<->",precedenceP pc (PIff p q)) p q
prettyPrintP pc (PNot p)         = let p' = bracketPP (isCompoundP p) (prettyPrintP pc p)
                                   in "~"++p'
prettyPrintP pc (PBinding t v p) = bs ++ (prettyPrintV pc v) ++ ". " ++ (prettyPrintP pc p)
    where bs = if t == Forall then "forall " else "exists "
prettyPrintP pc (PPatVar s)      = "P{"++s++"}"
prettyPrintP pc (PCut)           = "(@)"

prettyPrintBinaryP :: PrintContext -> (String,Int) -> Predicate -> Predicate -> String
prettyPrintBinaryP pc (op,precOp) p q = let precP = precedenceP pc p
                                            precQ = precedenceP pc q
                                        in intercalate " " [bracketPP (precP <= precOp) $ prettyPrintP pc p
                                                           ,op
                                                           ,bracketPP (precQ <= precOp) $ prettyPrintP pc q]

precedenceP :: PrintContext -> Predicate -> Int
-- 10 is max and indicates that they never need brackets
-- 0 is the minimum and indicates that they always need brackets (unless they are the top level statement)
precedenceP pc (PExp _)         = 10
precedenceP pc (PAnd _ _)       = 6
precedenceP pc (POr _ _)        = 6
precedenceP pc (PImp _ _)       = 3
precedenceP pc (PIff _ _)       = 3
precedenceP pc (PNot _)         = 8
precedenceP pc (PBinding _ _ _) = 0
precedenceP pc (PPatVar _)      = 10
precedenceP pc (PCut)           = 10

{-
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

          -}
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