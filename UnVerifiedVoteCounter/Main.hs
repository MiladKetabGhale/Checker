module Main where

import Lib
import System.IO
import Data.Ratio
import Data.List.Split

main :: IO ()
main = do
 c <- readFile "ACTM1.txt" 
 mapM_ print $ 
   countingTrace (((toInteger (length $ lines c)) % (toInteger (st  + 1 ))) 
    + (1 % 1), st,cand_all) 
        [] 
        (NonFinal (Prelude.map makePair $ 
        Prelude.map ((map (read :: String -> Cand)) . (splitOn ",")) $ lines c)
        tally 
        pile 
        [] 
        [] 
        cand_all)



--quota :: [a] -> Ratio Integer
--quota c = ((toInteger (length c)) % (toInteger (st  + 1 ))) + (1 % 1)

st = 7


makePair :: [Cand] -> ([Cand], Ratio Integer)
makePair l = (l, 1 % 1)
