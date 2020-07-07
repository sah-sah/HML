module HML.Misc.TakeAwayTriangles where

import Control.Monad(mplus)

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.BCC

import Data.Maybe(isJust, fromJust)

type Triangle = (Integer,Integer,Integer)

next :: Triangle -> Triangle
next (a,b,c) = (abs (b - a), abs (c - b), abs (c - a))

run :: Triangle -> [Triangle]
run t = t:(run $ next t)

-- build a large graph
allRuns :: Integer -> TGraph
allRuns n = foldr (addRun (fromInteger n)) emptyTG allTs
    where allTs = [(x,y,z) | x <- [0..n], y <- [0..n], z <- [0..n]]

findCycle steps t = findCycle' sNid runG
    where runG = addRun steps t emptyTG
          sNid = fromJust $ getNodeTG t runG

          findCycle' n tg | indeg tg n > 1 = sequence $ map (lab tg) $ getCycle' n tg
                          | otherwise      = let ms = suc tg n
                                             in if ms == [] then Nothing
                                                            else findCycle' (head ms) tg

          getCycle' n tg = n:(takeWhile (\m -> m /= n) (sucs' n tg))

          sucs' n tg = let [m] = suc tg n
                       in m:(sucs' m tg)


type TGraph = Gr Triangle ()

emptyTG :: TGraph
emptyTG = empty

addTriangle :: Triangle -> TGraph -> (Int, TGraph)
addTriangle t tg = case getNodeTG t tg of
                     Just nid -> (nid, tg)
                     Nothing  -> (nNid, insNode (nNid, t) tg)
    where nNid = head $ newNodes 1 tg

addStep :: Triangle -> TGraph -> TGraph
addStep t tg = let (tNid,tg') = addTriangle t tg
                   (sNid,tg'') = addTriangle (next t) tg'
               in if not $ hasEdge tg'' (tNid,sNid) then insEdge (tNid,sNid,()) tg'' else tg''

addRun :: Int -> Triangle -> TGraph -> TGraph
-- adds a run of length upto n
addRun 0 t tg = tg
addRun n t tg = addStep t (addRun (n-1) (next t) tg)

getNodeTG :: Triangle -> TGraph -> Maybe Int
getNodeTG t tg = ufold find' Nothing tg
    where find' (_,nid,nl,_) n | t == nl   = Just nid `mplus` n
                               | otherwise = n