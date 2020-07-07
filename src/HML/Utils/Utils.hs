 {--
 -- Utils.hs
 -- Some useful utility functions
 --}
module HML.Utils.Utils where

{-
import Data.Function(on)
import Data.List(sortBy, nub, null)
import Data.Maybe(isJust, isNothing, fromJust, catMaybes)
import Control.Monad(mplus)
-}
-- add this to a module of utility functions for whole project
ifM :: a -> Bool -> Maybe a
ifM x True  = Just x
ifM x False = Nothing

failOn :: Bool -> String -> Either String ()
failOn True  str = Left str
failOn False str = Right ()

check :: (a -> Bool) -> String -> Either String a -> Either String a
check cf str ef = do { x <- ef; if cf x then Left str else Right x }

fromMaybe :: Maybe a -> String -> Either String a
-- change fromMaybe to an operator <|>
-- maybeVal <|> error message
fromMaybe (Just a)  str = Right a
fromMaybe (Nothing) str = Left str

