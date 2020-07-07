{-# LANGUAGE OverloadedStrings #-}
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
module HML.Logic.Propositions.PropositionsLaTeX where

import HML.Logic.Propositions.Propositions
import HML.Logic.Propositions.PropositionsCursor

import Text.LaTeX
import Text.LaTeX.Base.Class(comm1)
import Text.LaTeX.Packages.Color

import Data.Text(pack,unpack)

{- ---------- Data types ---------- -}

toString :: LaTeX -> String
toString = unpack . render

-- make a type class with function toLaTeX
toLaTeXCP :: CursorProp -> LaTeX
toLaTeXCP (CP mp ds sp) = toLaTeX' sp' mp
    where sp' = between (toLaTeX sp) (raw "\\{") (raw "\\}")
          -- the one below needs extra brackets
          --sp' = colorbox (DefColor Yellow) $ between (toLaTeX sp) (raw "\\(") (raw "\\)")

toLaTeX' :: LaTeX -> Proposition -> LaTeX
toLaTeX' ac (Name n)        = raw $ pack n
toLaTeX' ac (Constant b)    = if b then raw "T" else raw "F"
toLaTeX' ac (Unary op p)    = toLaTeXUOp op $ bracketLaTeX (isCompound p) (toLaTeX' ac p)
toLaTeX' ac (Binary op p q) = let p' = bracketLaTeX (isCompound p) (toLaTeX' ac p)
                                  q' = bracketLaTeX (isCompound q) (toLaTeX' ac q)
                              in toLaTeXBOp op p' q'
toLaTeX' ac (Cut)           = ac


toLaTeX :: Proposition -> LaTeX
toLaTeX (Name n)        = raw $ pack n
toLaTeX (Constant b)    = if b then raw "T" else raw "F"
toLaTeX (Unary op p)    = toLaTeXUOp op $ bracketLaTeX (isCompound p) (toLaTeX p)
toLaTeX (Binary op p q) = let p' = bracketLaTeX (isCompound p) (toLaTeX p)
                              q' = bracketLaTeX (isCompound q) (toLaTeX q)
                          in toLaTeXBOp op p' q'
toLaTeX (Cut)           = raw "(@)"

isCompound :: Proposition -> Bool
isCompound (Binary _ _ _) = True
isCompound (Unary _ p)    = isCompound p
isCompound _              = False

bracketLaTeX :: Bool -> LaTeX -> LaTeX
bracketLaTeX b l = if b then between l (raw "(") (raw ")") else l

toLaTeXBOp :: BOp -> LaTeX -> LaTeX -> LaTeX
toLaTeXBOp And = wedge
toLaTeXBOp Or = vee
toLaTeXBOp XOr = oplus
toLaTeXBOp Imp = between rightarrow
toLaTeXBOp Iff = equiv

toLaTeXUOp :: UOp -> LaTeX -> LaTeX
toLaTeXUOp Not = comm1 "lnot"

egA = toLaTeX statementA
egB = toLaTeX statementB
egC = toLaTeX statementC
egD = toLaTeX statementD




{- ---------- Show instances ---------- -}
{-
instance Show BOp where
    show And = "&"
    show Or  = "|"
    show XOr = "x|"
    show Imp = "->"
    show Iff = "<->"

instance Show UOp where
    show Not = "~"

-- TODO: should we bracket p -> q -> r
-- TODO: should we not bracket (p&q)&r
instance Show Proposition where
    show = showP' False
        where showP' b (Name n)        = n
              showP' b (Binary op p q) = bracket b (showP' (sbB op) p ++ " " ++ show op ++ " " ++ showP' (sbB op) q)
              showP' b (Unary op p)    = show op ++ showP' (sbU p) p
              showP' b (Constant bool) = take 1 $ show bool
              showP' b (Cut)           = bracket True "@"

              -- should bracket?
              sbB Imp = True
              sbB Iff = True
              sbB _   = True

              sbU (Name _)     = False
              sbU (Constant _) = False
              sbU _            = True

              bracket :: Bool -> String -> String
              bracket b str | b         = "(" ++ str ++ ")"
                            | otherwise = str

-}
