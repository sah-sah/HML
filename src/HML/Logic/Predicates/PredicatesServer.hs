{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{--
 -- Propositions.hs
 -- :l ./HML/Logic/Propositions.hs from devel directory
 -- A module for propositional logic
 --}
-- TODO: applying the laws of logic to a proposition
-- need to add a cursor to the Proposition
-- so we have a way to move through it
-- TODO: for proofs in more sophisticated domains, need functions that generate axioms
-- e.g. we can have a function (+) that generates axioms of the form (a+b=c), given 
-- inputs a b
-- TODO: we will also need defns, like, if x in Z then what is +
-- we might need to specify that x in (Z,+) etc, or x in (R,+,*)
-- Basic predicate logic should be relatively simple, but then need sophisticated
-- ways to manage definitions and axioms
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
module HML.Logic.Predicates.PredicatesServer where

import HML.Logic.Predicates.Predicates
import HML.Logic.Predicates.PredicateProofs
import HML.Logic.Predicates.PredicateProofGraph
import HML.Logic.Predicates.PredicateParser(predicate)
import HML.Logic.Predicates.PredicateMatching(PredicateMatching(..))

import HML.Logic.Predicates.PrettyPrintLaTeX

--import Data.List
--import Control.Monad
import Control.Monad.State(StateT, evalStateT, liftIO, get, put)

{- For parsing commands -}
import Data.Char(isLetter, isDigit, isLower, isUpper)
import Data.List
import Control.Applicative((<$>), (<*>), (<*), (*>), (<|>), (<$))
import Control.Monad

--import Text.LaTeX.Base.Parser hiding (Parser)

import Text.Parsec hiding ((<|>))
import Text.Parsec.Expr
import Text.Parsec.String(Parser)

-- for JSON data
import GHC.Generics
import Data.Aeson
import qualified Data.ByteString.Lazy.Char8 as C
import qualified Data.Map.Strict as Map
import qualified Data.Text as T

{-
testEncode = encode ((("cmd","axioms"),("status","OK"),("result","A1,A2")) :: ((String,String),(String,String),(String,String)) )
testObj = encode $ object ["cmd" .= ("axioms" :: String)] --,"status".="OK","result".="A1,A2"]
-}
{- TO RUN: stack exec HML-exe
 - TODO: it might be better to implement this as a html server
 -       so I don't have to worry about handling the input and output
 -       reading a line is a bit limiting
 -       OR use a streams library like io-streams
-}

{- ---------- Data Types ---------- -}

type HPA = StateT (Proof,LaTeXContext) IO

-- all requests should be pairs of strings (field = value)
-- (maybe will should change this to a more useful data structure?)
type HPARequest = Map.Map String String

data Command = CQuit -- quit
             | CErr  -- error
             | CNames -- get names in the proof
             | CAxioms
             | CRead String
             | CAssume String String
             | CPrint String
             | CDetails String
             | CInstantiateSchema String String
    deriving (Show, Eq)

-- | starts a Haskell Proof Assistant server
startHPAServer :: [NamedPredicate] -> LaTeXContext -> IO ()
startHPAServer axs lcon = evalStateT runHPAServer (prf,lcon)
    where prf = startProof axs

runHPAServer :: HPA ()
runHPAServer = do str <- liftIO getLine
                  -- try to decode string to a JSON object
                  let jsonM = decode (C.pack str) :: Maybe HPARequest
                  -- execute command
                  b <- execCommand jsonM
                  if b then runHPAServer else return ()

execCommand :: Maybe HPARequest -> HPA Bool
execCommand (Nothing)   = do liftIO $ putStrLn "Error: expecting json object"
                             return True
execCommand (Just cmap) = do cmd <- readCommand cmap
                             case cmd of
                               CQuit         -> return ()
                               CRead str     -> readPredicate cmap str
                               CAssume n str -> assumePredicate cmap n str
                               CNames        -> getNames cmap
                               CAxioms       -> getAxioms cmap
                               CPrint n      -> printName cmap n
                               CDetails n    -> getDetails cmap n
                               CInstantiateSchema n sn -> instSchema cmap n sn
                               CErr   -> liftIO $ putStrLn "Unknown command"
                             return (cmd /= CQuit)

returnUpdatedRequest :: HPARequest -> [(String,String)] -> HPA ()
returnUpdatedRequest cmap kvs = liftIO $ C.putStrLn $ encode $ updateRequest cmap kvs

updateRequest :: HPARequest -> [(String,String)] -> HPARequest
updateRequest = foldl (flip (uncurry Map.insert))

ok', fail' :: (String,String)
ok'  = ("status","OK")
fail' = ("status","FAIL")
error', result' :: String -> (String,String)
error' msg = ("error",msg)
result' res = ("result",res)

readPredicate :: HPARequest -> String -> HPA ()
readPredicate cmap str = case parse predicate "(unknown predicate)" str of
                           Left pe -> returnUpdatedRequest cmap [fail'] -- should add error msg
                           Right p -> do (prf,lcon) <- get
                                         returnUpdatedRequest cmap [ok',result' $ latexPPinContext lcon p]

-- TODO: we should make a function assume' (n,p) prf
-- that returns Right (prf',np) where np holds the details of the new predicate
assumePredicate :: HPARequest -> String -> String -> HPA ()
assumePredicate cmap n str = case parse predicate "(unknown predicate)" str of
                               Left pe -> returnUpdatedRequest cmap [fail', error' "Unable to read predicate"]
                               Right p -> do (prf,lcon) <- get
                                             case assume (n,p) prf of
                                               Left str   -> returnUpdatedRequest cmap [fail',error' str]
                                               Right prf' -> do put (prf',lcon)
                                                                returnUpdatedRequest cmap [ok']

instSchema :: HPARequest -> String -> String -> HPA ()
instSchema cmap n sn = do -- get proof
                          (prf,lcon) <- get
                          -- get pattern matching from input
                          case pmM prf of
                            Nothing -> returnUpdatedRequest cmap [fail', error' "Unable to parse matching"]
                            Just pm -> case instantiateSchema n sn pm prf of
                                         Left str -> returnUpdatedRequest cmap [fail', error' str]
                                         Right prf' -> do put (prf',lcon)
                                                          returnUpdatedRequest cmap [ok']
    where pmM prf = do p <- getPredicateByNameM sn prf
                       -- get patvars
                       let (ps,es,ns) = getPatterns p
                       -- try to read each patvar from the JSON object
                       psPR <- sequence $ map (\(PPatVar n) -> Map.lookup ("P{"++n++"}") cmap) ps
                       esPR <- sequence $ map (\(ExpPatVar n) -> Map.lookup ("E{"++n++"}") cmap) es
                       nsPR <- sequence $ map (\(NPatVar n) -> Map.lookup ("N{"++n++"}") cmap) ns
                       -- try to parse the raw predicates
                       psP <- sequence $ map parse' psPR
                       esP <- sequence $ map parse' esPR
                       nsP <- sequence $ map parse' nsPR
                       -- get expressions and names from predicates
                       esE <- sequence $ map getE' esP
                       nsN <- sequence $ map getN' nsP
                       -- construct a PredicateMatching
                       return $ PMatching { predicatePatterns = zip (map (\(PPatVar n) -> n) ps) psP
                                          , expressionPatterns = zip (map (\(ExpPatVar n) -> n) es) esE
                                          , namePatterns = zip (map (\(NPatVar n) -> n) ns) nsN
                                          }

          parse' s = case parse predicate "(unknown predicate)" s of
                       Left _  -> Nothing
                       Right p -> Just p

          getE' (PExp e)    = Just e
          getE' (PExpT e _) = Just e
          getE' _           = Nothing

          getN' p = (getE' p) >>= \e ->
                       case e of
                         ExpN n -> Just n
                         _      -> Nothing

getDetails :: HPARequest -> String -> HPA ()
getDetails cmap str = do (prf,lcon) <- get
                         case getResultString str prf of
                           Nothing -> returnUpdatedRequest cmap [fail']
                           Just rs -> do -- update request with what we have
                                         let cmap' = updateRequest cmap [ok'
                                                                        ,("type",rsType rs)
                                                                        ,(result' $ latexPPinContext lcon (rsPredicate rs))]
                                         -- unpack the updated cmap
                                         let currPairs = map (\(f,v) -> T.pack f .= v) (Map.toList cmap')
                                         -- add in deductions ourselves
                                         let morePairs = ["deductions" .= (map show $ rsDeductions rs)
                                                         ,"assumptions" .= rsAssumptions rs]
                                         -- return the response
                                         liftIO $ C.putStrLn (encode $ object (currPairs++morePairs))

-- TODO: we should update and return the original JSON object
printName :: HPARequest -> String -> HPA ()
printName cmap n = do (prf,lcon) <- get
                      case getNamedPredicate n prf of
                        Nothing -> returnUpdatedRequest cmap [fail']
                        Just p  -> returnUpdatedRequest cmap [ok', result' $ latexPPinContext lcon p]

getNames :: HPARequest -> HPA ()
getNames cmap = do (prf,lcon) <- get
                   -- we have to build the JSON object ourselves
                   let reqPairs = map (\(f,v) -> T.pack f .= v) (Map.toList cmap)
                   -- in order to add a list item to it
                   let respPairs = ["status" .= ("OK" :: String), "result" .= namesInProof prf]
                   -- print out the list of axiom names
                   liftIO $ C.putStrLn (encode $ object (reqPairs ++ respPairs))

getAxioms :: HPARequest -> HPA ()
getAxioms cmap = do (prf,lcon) <- get
                    -- we have to build the JSON object ourselves
                    let reqPairs = map (\(f,v) -> T.pack f .= v) (Map.toList cmap)
                    -- in order to add a list item to it
                    let respPairs = ["status" .= ("OK" :: String), "result" .= axiomsInProof prf]
                    -- print out the list of axiom names
                    liftIO $ C.putStrLn (encode $ object (reqPairs ++ respPairs))

readCommand :: HPARequest -> HPA Command
readCommand cmap = return $ maybe (CErr) id cmdM
    where cmdM = do cmd <- Map.lookup "cmd" cmap
                    readArgs cmd cmap

readArgs :: String -> HPARequest -> Maybe Command
readArgs "quit"    cmap = Just CQuit
readArgs "read"    cmap = CRead <$> Map.lookup "predicate" cmap
readArgs "names"   cmap = Just CNames
readArgs "axioms"  cmap = Just CAxioms
readArgs "assume"  cmap = CAssume <$> Map.lookup "name" cmap <*> Map.lookup "predicate" cmap
readArgs "print"   cmap = CPrint <$> Map.lookup "name" cmap
readArgs "details" cmap = CDetails <$> Map.lookup "name" cmap
readArgs "instantiateSchema" cmap = CInstantiateSchema <$> Map.lookup "name" cmap <*> Map.lookup "schema" cmap
readArgs _         _    = Just CErr

cmdParser :: Parser Command
cmdParser =     try quitCmd
            <|> try readCmd
            <|> try assumeCmd
            <|> try namesCmd
            <|> try axiomsCmd
            <|> try printCmd
            <|> (return CErr)

quitCmd :: Parser Command
quitCmd = string "quit" >> return CQuit

readCmd :: Parser Command
readCmd = CRead <$> (string "read " *> many1 anyChar)

assumeCmd :: Parser Command
assumeCmd = CAssume <$> (string "assume " *> nameParser) <*> many1 anyChar

namesCmd :: Parser Command
namesCmd = CNames <$ string "names"

axiomsCmd :: Parser Command
axiomsCmd = CAxioms <$ string "axioms"

printCmd :: Parser Command
printCmd = CPrint <$> (string "print " *> nameParser)

nameParser :: Parser String
nameParser = do n <- many1 (satisfy (\c -> c /= ' '))
                spaces
                return n

testP :: Parser a -> String -> Either ParseError a
testP p str = parse p "(fail)" str
{-
getCommand :: String -> Command
getCommand str =

getCommand :: String -> Maybe (String,[String])
getCommand str = let ws = words str
                 in if length ws == 0 then Nothing
                                      else argsByCommand (head ws) (tail ws)

transCommand ::
argsByCommand :: String -> [String] -> (String,[String])
argsByCommand "read" args = ("read", unwords args)
argsByCommand cmd    args = (cmd, args)

-}

