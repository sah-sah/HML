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
module HML.Logic.Propositions.Propositions where

import Data.Functor.Identity(Identity)
import Data.List
import Control.Monad

-- NOTE: this is a legacy library and will need to be replaced on new systems
import Text.Parsec

{- ---------- Data types ---------- -}

data Proposition = Name String 
                 | Binary BOp Proposition Proposition
                 | Unary UOp Proposition
                 | Constant Bool
                 | Cut
    deriving (Eq)

data BOp = And | Or | XOr | Imp | Iff deriving (Eq)
data UOp = Not deriving (Eq)

type TruthAssignment = [(String, Bool)]

{- ---------- Show instances ---------- -}

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

{- ---------- Construction functions ---------- -}

varP :: String -> Proposition
-- varP str returns a proposition consisting of a single variable named str
varP = Name

andP, orP, xorP, impP :: Proposition -> Proposition -> Proposition
-- andP p q returns the proposition p and q
andP = Binary And 
-- orP p q returns the proposition p or q
orP  = Binary Or 
-- xorP p q returns the proposition p xor q
xorP = Binary XOr 
-- impP p q returns the proposition p implies q
impP = Binary Imp 
-- iffP p q returns the proposition p if and only if q
iffP = Binary Iff 

notP :: Proposition -> Proposition
-- notP p returns a proposition that is the negation of p
notP = Unary Not

constP :: Bool -> Proposition
-- constP b returns the constant proposition b
constP = Constant

contrapositive, converse :: Proposition -> Proposition
-- contrapositive p returns the contrapositive of p if p = q -> r (~r -> ~q)
-- otherwise returns p
contrapositive (Binary Imp p q) = Binary Imp (notP q) (notP p)
contrapositive p                = p
-- converse p returns the converse of p if p = q -> r (r -> q)
-- otherwise returns p
converse (Binary Imp p q) = Binary Imp q p
converse p                = p

{- ---------- Truth Tables ---------- -}

getVars :: Proposition -> [String]
-- getVars p returns a (sorted) list of the variable names in p
getVars = sortBy compare . nub . allVars'
    where allVars' (Name n)        = [n]
          allVars' (Binary op p q) = allVars' p ++ allVars' q
          allVars' (Unary op p)    = allVars' p
          allVars' (Constant b)    = []

coversTA :: TruthAssignment -> Proposition -> Bool
-- coversTA ta p returns True if ta covers p (i.e. every var in p is in ta)
coversTA ta p = all (\v -> v `elem` taVars) $ getVars p
    where taVars = map fst ta

apTA ::  Proposition -> TruthAssignment -> Bool
-- apTA p ta applies the truth assignment ta to p and returns the result
-- NOTE: it assumes that ta covers the variables in p
apTA (Name n)        ta = let Just val = lookup n ta in val -- assume n is in ta
apTA (Binary op p q) ta = (getBOp op) (apTA p ta) (apTA q ta)
apTA (Unary op p)    ta = (getUOp op) (apTA p ta)
apTA (Constant b)    ta = b

getBOp :: BOp -> (Bool -> Bool -> Bool)
-- getBOp op returns the function that op represents
getBOp And = (&&)
getBOp Or  = (||)
getBOp XOr = (\a b -> (a && not b) || (not a && b)) 
getBOp Imp = (\a b -> (not a) || b)
getBOp Iff = (\a b -> a == b)

getUOp :: UOp -> (Bool -> Bool)
-- getUOp op returns the function that op represents
getUOp Not = not

allTruthAssignments :: Proposition -> [TruthAssignment]
-- allTruthAssignments p returns all possible truth assignments for p
allTruthAssignments = getTAs . getVars
    where getTAs []     = [[]]
          getTAs (n:ns) = concat [[(n,True):ta,(n,False):ta] | ta <- getTAs ns]

truthTable :: Proposition -> [(TruthAssignment,Bool)]
-- truthTable p returns the truth table for p (all truth assigments and the resulting truth value)
truthTable p = map (\ta -> (ta,apTA p ta)) $ allTruthAssignments p

showTruthTable :: Proposition -> String
-- showTruthTable p returns a string depicting the truth table of p
showTruthTable p =    (concat $ intersperse " " (ns ++ ["|", show p])) ++ "\n"
                   ++ (concat $ intersperse "\n" $ map showLine tt)
    where ns = getVars p
          tt = truthTable p

          showLine (ta,b) = concat $ intersperse " " $ map (take 1 . show . snd) ta ++ ["|",take 1 (show b)]

equivalent, equivalent' :: Proposition -> Proposition -> Bool
-- equivalent p q returns True if p and q have same truth value for all truth assignments
equivalent p q = all (\ta -> apTA p ta == apTA q ta) $ allTruthAssignments (p `orP` q)
-- equivalent' is an alternative implementation of equivalent
equivalent' p q = tautology (p `iffP` q)

tautology, contradiction :: Proposition -> Bool
-- tautology p returns True if p is true for all truth assignments
tautology     p = all (apTA p)         $ allTruthAssignments p
contradiction p = all (not . (apTA p)) $ allTruthAssignments p

{- ---------- Some example propositions ---------- -}
-- TODO: put better names for these
statementA :: Proposition
statementA = varP "A"
statementB = notP statementA
statementC = notP (statementA `andP` statementB)
statementD = varP "A" `andP` varP "B"
statementE = varP "C" `impP` (statementA `xorP` statementD)
statementF = (Constant False) `impP` statementE
statementG = varP "A" `impP` varP "B"
statementH = (notP (varP "A")) `orP` varP "B"
statementI = (varP "p" `impP` varP "q") `orP` notP (varP "p" `andP` varP "q")
statementJ = (varP "p" `iffP` varP "q")
statementJ' = (p `impP` q) `andP` (q `impP` p)
    where p = varP "p"
          q = varP "q"
statementK = (p `impP` (q `orP` (notP r))) `impP` (p `andP` r)
    where p = varP "p"
          q = varP "q"
          r = varP "r"
statementL = (p `andP` (p `impP` q)) `impP` q
    where p = varP "p"
          q = varP "q"
statementM = (p `impP` q) `orP` notP (p `andP` q)
    where p = varP "p"
          q = varP "q"
statementN = ((p `orP` q) `andP` ((p `impP` (notP r)) `andP` r)) `impP` q
    where p = varP "p"
          q = varP "q"
          r = varP "r"

{- --------- Logic Laws as Propositions --------- -}

equivalenceLawP = (p `iffP` q) `iffP` ((p `impP` q) `andP` (q `impP` p))
    where p = varP "p"
          q = varP "q"

implicationLawP = (p `impP` q) `iffP` ((notP p) `orP` q)
    where p = varP "p"
          q = varP "q"

doubleNegationLawP = (notP (notP p)) `iffP` p
    where p = varP "p"

idempotentLawP = ((p `andP` p) `iffP` p) `andP` ((p `orP` p) `iffP` p)
    where p = varP "p"

commutativeLawP = ((p `andP` q) `iffP` (q `andP` p)) `andP` ((p `orP` q) `iffP` (q `orP` p))
    where p = varP "p"
          q = varP "q"

associativeLawP = andP ((p `andP` (q `andP` r)) `iffP` ((p `andP` q) `andP` r)) 
                       ((p `orP` (q `orP` r)) `iffP` ((p `orP` q) `orP` r))
    where p = varP "p"
          q = varP "q"
          r = varP "r"

distributiveLawP = andP ((p `andP` (q `orP` r)) `iffP` ((p `andP` q) `orP` (p `andP` r)))
                        ((p `orP` (q `andP` r)) `iffP` ((p `orP` q) `andP` (p `orP` r)))
    where p = varP "p"
          q = varP "q"
          r = varP "r"

deMorgansLawP = andP ((notP (p `andP` q)) `iffP` ((notP p) `orP` (notP q)))
                     ((notP (p `orP` q)) `iffP` ((notP p) `andP` (notP q)))
    where p = varP "p"
          q = varP "q"

identityLawP = andP ((p `andP` (constP True)) `iffP` p)
                    ((p `orP` (constP False)) `iffP` p)
    where p = varP "p"

annihilationLawP = andP ((p `andP` (constP False)) `iffP` (constP False))
                        ((p `orP` (constP True)) `iffP` (constP True))
    where p = varP "p"

inverseLawP = andP ((p `andP` (notP p)) `iffP` (constP False))
                   ((p `orP` (notP p)) `iffP` (constP True))
    where p = varP "p"

absorptionLawP = andP ((p `andP` (p `orP` q)) `iffP` p)
                      ((p `orP` (p `andP` q)) `iffP` p)
    where p = varP "p"
          q = varP "q"


{- ---------- Parsing Propositions ------------- -}

-- parser types
type PropParser = ParsecT String () Identity Proposition
type BOpParser = ParsecT String () Identity BOp
type UOpParser = ParsecT String () Identity UOp

--parseExp :: String -> Either ParseError [[String]]
readProp str = parse parseTop "(unknown)" (filter (\c -> c /= ' ') str)

parseTop :: PropParser
parseTop = do p <- parseProp
              eof
              return p

parseProp :: PropParser
parseProp = parseUExp <|> parseBExp <|> parseName

parseSimpleProp :: PropParser
parseSimpleProp = parseUExp <|> parseName

parseName :: PropParser
parseName = do n <- many1 letter
               case n of
                 "T" -> return (Constant True)
                 "F" -> return (Constant False)
                 _   -> return (Name n)

parseBExp :: PropParser
parseBExp = do p <- parens parseProp <|> parseSimpleProp
               op <- parseBOp
               q <- parens parseProp <|> parseSimpleProp
               return (Binary op p q)

parseUExp :: PropParser
parseUExp = do op <- parseUOp
               p <- parens parseProp <|> parseSimpleProp
               return (Unary op p)

parseBOp :: BOpParser
parseBOp = do op <- choice (map string ["&","|","x|","->","<->"])
              let bop = case op of
                          "&" -> And
                          "|" -> Or
                          "x|" -> XOr
                          "->" -> Imp
                          "<->" -> Iff
              return bop

parseUOp :: UOpParser
parseUOp = do char '~'
              return Not

parens :: PropParser -> PropParser
parens = between (char '(') (char ')')

