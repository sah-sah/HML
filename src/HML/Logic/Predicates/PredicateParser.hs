{-# LANGUAGE OverloadedStrings #-}

{--
 -- Predicates.hs
 -- :l ./HML/Logic/PredicateLogic/Predicates.hs from devel directory
 -- A module for predicate logic
 --
 -- Gives basic data types for predicate logic, show instances, construction functions
 -- and some examples.
 --}
module HML.Logic.Predicates.PredicateParser where

import HML.Logic.Predicates.Predicates

import Data.Char(isLetter, isDigit, isLower, isUpper)
import Data.List
import Control.Applicative((<$>), (<*>), (<*), (*>), (<|>), (<$))
import Control.Monad

--import Text.LaTeX.Base.Parser hiding (Parser)

import Text.Parsec hiding ((<|>))
import Text.Parsec.Expr
import Text.Parsec.String(Parser)

{-
 - Need to define what input we want
 -
 - Can have built in infix operators & | x| ~ => <-> etc
 - Can have user defined functions f(..) etc
 - How can we make it extensible?
 -   We want to be able to add operators later
 -   bind certain function names to more convenient names
 - Need to be able to define functions (maybe separately from Predicates, but using
 - the predicate parser)
 -
 - NOTE: we use try a lot as the data types are not the most useful for parsing
 - it might be better to use an intermediate AST
 -
 - TODO: (1) a parser for latex expressions (maybe it already exists, it is in HaTeX)
 -       (2) We will need if expressions, case expressions e.g. gcd(m,n) = m if m==n, m-n if m > n, n-m if n > m
 -           These could be done at a level higher than predicates, rather than within predicates
 -
 -}



testP :: Parser a -> String -> Either ParseError a
testP p str = parse (whitespace >> p) "(fail)" str

{- ----- helper functions ----- -}

whitespace :: Parser ()
whitespace = void $ spaces --many $ oneOf " \n\t"

lexeme :: Parser a -> Parser a
lexeme p = p <* whitespace

parens :: Parser a -> Parser a
parens p = lexeme (char '(') *> p <* lexeme (char ')')

{- ----- general parsers ----- -}

-- | parses a variable name - one or more (upper or lower case) letters
-- Note: this accepts forall and exists so predicate binding must be tried first
varname :: Parser String
varname = lexeme (many1 letter)

-- | parses a pattern variable for names
patvarStr :: Char -> Parser String
patvarStr t = lexeme (string (t:"{") *> patname <* char '}')

-- | parses a pattern variable name - a letter (upper- or lowercase) followed by one or more letters or digits
patname :: Parser String
patname = (:) <$> letter <*> many (letter <|> digit)

{- ----- parsing Variable ----- -}

-- TODO: should we make the variable parsers fail if the varname is followed by (
parseSimpleVar :: Parser Variable
parseSimpleVar = SimpleVar <$> varname

--parseIndexedVar :: Parser Variable
parseIndexedVar = IndexedVar <$> varname <*> (char '_' *> ix)
    where ix =     try (parens expression)
               <|> try (do { n <- parseName; return $ ExpN n })
               <?> "index"

parseVPatVar :: Parser Variable
parseVPatVar = VPatVar <$> patvarStr 'V'

parseVariable :: Parser Variable
parseVariable = try parseIndexedVar <|> try parseVPatVar <|> try parseSimpleVar <?> "variable"

--parseVar :: Parser Variable
--parseVar = do vn <- many1 letter
--              c <- lookAhead anyChar
--              if c == '_' then do { void $ char '_'; string "exp"; return $ IndexedVar vn (ExpN (Constant SZ)) }
--                          else return $ SimpleVar vn

{- ----- parse Special ----- -}

parseInt :: Parser Special
parseInt = (SInt . read) <$> lexeme (many1 digit)

parseBool :: Parser Special
parseBool = do b <- oneOf "TF"
               if b == 'T' then return $ SBool True
                           else return $ SBool False

parseZ :: Parser Special
parseZ = do void $ char 'Z'
            notFollowedBy (letter <|> oneOf "_+")
            return SZ

parseZplus :: Parser Special
parseZplus = do void $ string "Z+"
                return SZplus

parseZn :: Parser Special
parseZn = do void $ string "Zn"
             e <- parens expression
             return $ SZn e

parseFinite :: Parser Special
parseFinite = do void $ string "{1,...,"
                 e <- expression
                 void $ char '}'
                 return $ SFinite e

parseSpecial :: Parser Special
parseSpecial =     try parseFinite
               <|> try parseZn
               <|> try parseZplus
               <|> try parseZ
               <|> try parseBool
               <|> try parseInt
               <?> "constant"

{- ----- parse Name ----- -}

parseName :: Parser Name
parseName =     try (Constant <$> parseSpecial)
            <|> try (Var <$> parseVariable)
            <?> "name"

{- ----- parse Expression ----- -}

expression :: Parser Expression
expression = buildExpressionParser optableExp expressionTerm <?> "expression"

expressionTerm :: Parser Expression
expressionTerm =     try parseEPatVar
                 <|> try parseFn
                 <|> try parseExpName
                 <|> try (parens expression)
                 <?> "expression term"

parseExpName :: Parser Expression
parseExpName = ExpN <$> parseName

parseFn :: Parser Expression
parseFn = ExpFn <$> varname <*> lexeme args
    where args = between (char '(') (char ')') $ sepBy1 expression (char ',')

parseEPatVar :: Parser Expression
parseEPatVar = ExpPatVar <$> patvarStr 'E'

-- | parses a function written in infix style
infixfn :: Parser String
infixfn = (char '\\' *> lexeme varname) <|> try operatorfn

operatorfn :: Parser String
operatorfn = do op <- lexeme (many1 $ oneOf "!@#$%&*-+=|<>?/:~")
                if op `elem` reservedOps then parserFail "reserved op"
                                         else return op
    where reservedOps = ["=","&","|","~","->","<->","+","-","/","*"]


-- constructing the operator table for expressions
binaryE op assoc = Infix ((mkBinaryFn . ExpFn) <$> expBOp op) assoc
unaryE op = Prefix ((mkUnaryFn . ExpFn) <$> expUOp op)

mkBinaryFn :: ([Expression] -> Expression) -> Expression -> Expression -> Expression
mkBinaryFn expCon e f = expCon [e,f]

mkUnaryFn :: ([Expression] -> Expression) -> Expression -> Expression
mkUnaryFn expCon e = expCon [e]

optableExp = [ [Infix ((mkBinaryFn . ExpFn) <$> infixfn) AssocNone]
             , [unaryE "-"]
             , [binaryE "*" AssocLeft, binaryE "/" AssocLeft]
             , [binaryE "+" AssocLeft, binaryE "-" AssocLeft]
             , [Infix (do { lexeme $ void $ char '='; return ExpEquals }) AssocNone]
             ]

expBOp, expUOp :: String -> Parser String
expBOp "+" = lexeme (char '+') *> pure "addNum"
expBOp "-" = lexeme minus *> pure "subtractNum"
expBOp "/" = lexeme (char '/') *> pure "divideNum"
expBOp "*" = lexeme (char '*') *> pure "multipleNum"
expBOp "=" = lexeme (char '=') *> pure "equals"

expUOp "-" = (char '-') *> pure "negateNum"

minus :: Parser ()
minus = try (do { void $ char '-'; notFollowedBy (char '>') })

{- ----- parsing Predicates ----- -}

predexp :: Parser Predicate
predexp = PExp <$> expression

ppatvar :: Parser Predicate
ppatvar = PPatVar <$> patvarStr 'P'

predicateTerm :: Parser Predicate
predicateTerm =     try boundpred
                <|> try predexp
                <|> try ppatvar
                <|> try (parens predicate)
                <?> "predicate term"
-- NOTE: we need to try boundpred first so forall and exists aren't read as variable names

predicate :: Parser Predicate
predicate = buildExpressionParser optableP predicateTerm <?> "predicate expression"

-- constructing the operator table
binary op assoc = Infix (bop op) assoc
unary op = Prefix (uop op)

optableP = [ [unary "not"]
           , [binary "and" AssocLeft, binary "or" AssocLeft]
           , [binary "imp" AssocNone, binary "iff" AssocLeft]]

bop :: String -> Parser (Predicate -> Predicate -> Predicate)
bop "and" = lexeme (char '&') *> pure PAnd
bop "or"  = lexeme (char '|') *> pure POr
bop "imp" = lexeme (string "->") *> pure PImp
bop "iff" = lexeme (string "<->") *> pure PIff

uop :: String -> Parser (Predicate -> Predicate)
uop "not" = lexeme (char '~') *> pure PNot

boundpred :: Parser Predicate
boundpred = do pb <- lexeme (forallPB <|> existsPB)
               p <- predicate
               return $ pb p

-- | parser forall <pname>. or forall <pname> s.t. <predicate>.
forallPB, existsPB :: Parser (Predicate -> Predicate)
forallPB = do void $ lexeme $ string "forall"
              v <- lexeme parseVariable
              char '.'
              return $ (PBinding Forall v)

existsPB = do void $ lexeme $ string "exists"
              v <- lexeme parseVariable
              char '.'
              return $ (PBinding Exists v)

{- ----- parsing expressions ----- -}
{-
-- | parses an expression pattern variable
epatvar :: Parser Expression
epatvar = ExpPatVar <$> patvarStr 'E'

-- | parses a PName into an expression
ename :: Parser Expression
ename = ExpN <$> pname

-- | parses a function expression - <name>(<exp1>,<exp2>,..)
-- NOTE: we need to expand this to allow operators etc
-- use a similar strategy to Haskell in requiring operators
-- to be written in a different form/using different characters
fnexp :: Parser Expression
fnexp = ExpF <$> varname <*> lexeme args
    where args = between (char '(') (char ')') $ sepBy1 expression (char ',')

-- | parses a function written in infix style
infixfn :: Parser String
infixfn = char '\\' *> lexeme varname

-- | parses an expression
eterm :: Parser Expression
eterm = try fnexp <|> ename <|> epatvar <|> parens expression
-- need a try on fnexp as a function name is the same as a variable name
-- functions are differentiated from variables by args

expression :: Parser Expression
expression = buildExpressionParser optableE eterm <?> "expression"

-- constructing the operator table for expressions
binaryE op assoc = Infix ((mkBinaryFn . ExpF) <$> expBOp op) assoc
unaryE op = Prefix ((mkUnaryFn . ExpF) <$> expUOp op)

mkBinaryFn :: ([Expression] -> Expression) -> Expression -> Expression -> Expression
mkBinaryFn expCon e f = expCon [e,f]

mkUnaryFn :: ([Expression] -> Expression) -> Expression -> Expression
mkUnaryFn expCon e = expCon [e]

optableE = [ [Infix ((mkBinaryFn . ExpF) <$> infixfn) AssocNone]
           , [unaryE "-"]
           , [binaryE "*" AssocLeft, binaryE "/" AssocLeft]
           , [binaryE "+" AssocLeft, binaryE "-" AssocLeft]
           ]

expBOp, expUOp :: String -> Parser String
expBOp "+" = lexeme (char '+') *> pure "addNum"
expBOp "-" = lexeme minus *> pure "subtractNum"
expBOp "/" = lexeme (char '/') *> pure "divideNum"
expBOp "*" = lexeme (char '*') *> pure "multipleNum"

expUOp "-" = (char '-') *> pure "negateNum"

minus :: Parser ()
minus = try (do { void $ char '-'; notFollowedBy (char '>') })

{- ----- parsing PNames ----- -}

-- | parses a PName
pname :: Parser PName
pname = npatvar <|> const' <|> var <|> int'

-- | parses a PName integer
int' :: Parser PName
int' = (PInt . read) <$> lexeme (many1 digit)

-- | parses a PName variable
var :: Parser PName
var = PVar <$> varname

-- | parses a PName constant
const' :: Parser PName
const' = checkConsts <$> constname
    where checkConsts c = case lookup c reservedConst of
                            Just pn -> pn
                            Nothing -> PConst c

          reservedConst = [("T", PTrue), ("True", PTrue), ("False", PFalse), ("F", PFalse)]

npatvar :: Parser PName
npatvar = NPatVar <$> patvarStr 'N'

-- | parses a pattern variable for names
patvarStr :: Char -> Parser String
patvarStr t = lexeme (string (t:"{") *> patname <* char '}')

{- ----- general parsing functions ----- -}

-- | parses a pattern variable name - a letter (upper- or lowercase) followed by one or more letters or digits
patname :: Parser String
patname = (:) <$> letter <*> many (letter <|> digit)

-- | parses a variable name - a lowercase letter followed by zero or more letters or digits
-- NOTE: x| is parsed as xor not as x followed by |
-- NOTE: forall and exists may cause problems
-- NOTE: how do we parse greek characters etc (could try parsing \alpha by parse \varname
-- then check whether varname is in a list of special names
varname :: Parser String
varname = xvarname <|> lexeme ((:) <$> first <*> many rest)
    where first = satisfy (\c -> isLetter c && isLower c && c /= 'x')
          rest = letter <|> digit

xvarname :: Parser String
xvarname = try $ lexeme $ do void $ char 'x'
                             notFollowedBy (char '|')
                             str <- many (letter <|> digit)
                             return ('x':str)




-- | parses the name of a constant - an uppercase letter followed by zero or more letters or digits
constname :: Parser String
constname = lexeme ((:) <$> first <*> many rest)
    where first = satisfy (\c -> isLetter c && isUpper c)
          rest = letter <|> digit



{- ---------- Data types ---------- -}
{-
-- variables, constants, and functions can have multiple types 
data Type = AbstractSetT -- for abstract sets
          | PredicateT   -- essentially a boolean
          | EmptyT       -- no type information
    deriving (Eq)

-- the types of variables are given as predicates (i.e. A :: AbstractSetT is a predicate
-- which we use for matching, e.g., from x :: Integer and y=x^2 we can derive y :: Integer)
-- This datatype will need to be expanded, e.g. to (String,String) where the first
-- string is a unique identifier, and the second is how to display it
data PName = PVar String     -- variables x, A, etc
           | PConst String   -- constants 1, Z, True etc
           | PTrue
           | PFalse
           | NPatVar String  -- for matching
    deriving (Eq)

-- an expression is either a type expression (x :: Integer) or a function expression (x + y)
data Expression = ExpN PName
                | ExpF String [Expression]
                | ExpPatVar String
                | ExpCut
    deriving (Eq)

-- binding a variable in a predicate
-- forall x s.t. P(x). Q(x) 
-- note: name must be a PVar
data PredicateBinding = Forall PName Predicate | Exists PName Predicate
    deriving (Eq)

data PBOp = PAnd | POr | PXOr | PImp | PIff
    deriving (Eq)

data PUOp = PNot
    deriving (Eq)

data Predicate = PEmpty
               | PExp Expression
               | PExpT Expression Type
               | PBinary PBOp Predicate Predicate
               | PUnary PUOp Predicate 
               | PBinding PredicateBinding Predicate
               | PPatVar String -- for forming logic laws
               | PCut
    deriving (Eq)

-}
-}