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
module HML.Logic.Propositions.PropositionsHtml where

import Control.Monad(forM_)
import Control.Monad.State

import HML.Logic.Propositions.Propositions
import HML.Logic.Propositions.PropositionsCursor
import HML.Logic.Propositions.PropositionsProof
import HML.Logic.Propositions.PropositionsLaTeX
import HML.Logic.Propositions.PropositionsLogicLaws

import Text.Blaze.Html
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Text.Blaze.Html.Renderer.String(renderHtml)

-- for JSON data
import GHC.Generics
import Data.Aeson
import Data.ByteString.Lazy.Char8(unpack)

-- TODO: use a writer monad to deal with the messaging? it would need to be
-- on top of the IO monad to do the actual sending

{- types for returning data -}
data Package = Package { status :: String, cmd :: String, result :: String }
    deriving (Generic, Show)

instance ToJSON Package where
    -- No need to provide a toJSON implementation.

    -- For efficiency, we write a simple toEncoding implementation, as
    -- the default version uses toJSON.
    toEncoding = genericToEncoding defaultOptions

instance FromJSON Package
    -- No need to provide a parseJSON implementation.

packageOK, packageFAIL :: String -> String -> String
packageOK c r = unpack $ encode (Package { status = "OK", cmd = c, result = r })
packageFAIL c r = unpack $ encode (Package { status = "FAIL", cmd = c, result = "" })

{- Generate HTML files from Proof types -}

proofToHtml :: Proof -> H.Html
proofToHtml (PF lll as pss) = do H.p "Axioms"
                                 H.ol $ forM_ as (H.li . pToHtml)
                                 H.p "Proof Steps"
                                 H.ol $ forM_ pss (H.li . pToHtml . snd)
    where pToHtml = H.toHtml . inline . toString . toLaTeX
          inline mstr = "\\(" ++ mstr ++ "\\)"

--type IProof = StateT (Proof,CursorProp) IO

interactiveProofHtml :: [Proposition] -> IO ((), (Proof,CursorProp))
-- TODO: leave the cursor at the same point after applying a law
--       delete step option
--       better input and output
interactiveProofHtml ps = runStateT runProofHtml (pf,tp)
    where pf = startProof logicLaws ps
          tp = cutProposition (foldl1 andP ps) []

runProofHtml :: IProof ()
runProofHtml = do str <- liftIO getLine
                  if str /= [] && head str == 'q'
                      then return ()
                      else do b <- exeCommandHtml str
                              when (not b) (liftIO (putStrLn $ packageFAIL str ""))
                              runProofHtml
              
exeCommandHtml :: String -> IProof Bool
-- exeCommand str executes the command in str and returns True if it succeeds
-- otherwise does nothing an returns False
exeCommandHtml str = case str of
                         "m: DLeft"  -> moveIPHtml DLeft
                         "m: DRight" -> moveIPHtml DRight
                         "m: DDown"  -> moveIPHtml DDown
                         "m: DUp"    -> moveIPHtml DUp
                         "sp"        -> putProofHtml
                         "cp"        -> putCursorPropHtml
                         ('a':'p':str) -> apLawHtml str
                         _           -> return False

apLawHtml :: String -> IProof Bool
apLawHtml str = do let ws = words str
                   if (length ws > 0)
                     then (do let law = head ws
                              (pf,cp) <- get
                              let mpf = addProofStepM pf (stepCP cp law)
                              let ds = getDirections cp
                              case mpf of
                                Just pf' -> do put (pf',cutProposition (currentProp pf') ds)
                                               liftIO $ putStrLn $ packageOK "ap" ""
                                               return True
                                Nothing  -> return False)
                     else return False

moveIPHtml :: Direction -> IProof Bool
moveIPHtml d = do (pf,cp) <- get
                  let mcp = moveCursorM cp d
                  case mcp of
                    Just cp' -> do put (pf,cp');
                                   liftIO $ putStrLn $ packageOK "m" ""
                                   return True
                    Nothing  -> return False

putProofHtml :: IProof Bool
putProofHtml = do (pf,cp) <- get
                  liftIO $ putStrLn $ pass $ renderHtml $ proofToHtml pf
                  return True
    where pass str = packageOK "sp" str

putCursorPropHtml :: IProof Bool
putCursorPropHtml = do (pf,cp) <- get
                       liftIO $ putStrLn $ pass $ inline $ toString $ toLaTeXCP cp
                       return True
    where inline mstr = "\\(" ++ mstr ++ "\\)"
          pass str = packageOK "cp" str


exAHtml = [p `orP` (notP q), q `orP` (notP p)]
    where p = varP "p"
          q = varP "q"


{-
exB = [(((p `orP` q) `impP` r) `andP` (p `andP` q)) `impP` r]
    where p = varP "p"
          q = varP "q"
          r = varP "r"

-- equivalent to (p & q) -> r
exC = [p `impP` (q `impP` r)]
    where p = varP "p"
          q = varP "q"
          r = varP "r"

-- equivalent to (~p -> r) & (q -> r)
exD = [(p `impP` q) `impP` r]
    where p = varP "p"
          q = varP "q"
          r = varP "r"
-}
