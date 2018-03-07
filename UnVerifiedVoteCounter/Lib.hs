{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

module Lib where

import Data.Ratio
import Data.List



{--candidates--}
data Cand =
  RAS
 |KEA
 |LEC
 |SIA
 |JHT
 |GAK
 |BAA
 |COS
 |DRA
 |GAI
 |FIM
 |MAD
 |KUM
 |DIS
 |BOT
 |BIS
 |HAJ
 |DOS
 |LEE
 |JOG
 |MIJ
 |SET
 |GOM
 |CUM
 |CUD
 |POP deriving (Show,Eq,Ord,Read)


{--list of all candidates--}
cand_all :: [Cand]
cand_all =
  [RAS,KEA,LEC,SIA,JHT,GAK,BAA,COS,DRA,GAI,FIM,MAD,KUM,DIS,BOT,BIS,HAJ,DOS,LEE,JOG,MIJ,SET,GOM,CUM,CUD,POP]



 




{--
data Cand = 
 |A
 |C
 |D deriving (Show,Eq,Read,Ord)
 

cand_all = [A,B,C,D]
--}

type Parameters = (Ratio Integer, Int, [Cand])

type Ballot = [([Cand], Ratio Integer)] 

type Tally = Cand -> Ratio Integer

type Pile = Cand -> Ballot 

data Judgement =  NonFinal 
                          Ballot 
                          Tally 
                          Pile 
                          [Cand] 
                          [Cand] 
                          [Cand]
                | Final [Cand] 

 
instance Show (Judgement) where
 show (NonFinal a b c d e f) = (show a) ++ "; " ++
                               (show b) ++ "; " ++
                               (show c) ++ "; " ++
                               (show d) ++ "; " ++
                               (show e) ++ "; " ++
                               (show f)
 show (Final l) = show l

instance (Show a) => Show (Cand -> a) where
  show f = show_l cand_all where
    show_l [] = ""
    show_l [c] = (show c) ++ "{" ++ (show (f c)) ++ "}"
    show_l (c:cs) = (show c) ++ "{" ++ (show (f c)) ++ "} " ++ (show_l cs)

isWeakestCand :: Tally -> [Cand] -> Maybe Cand 
isWeakestCand t h = case h of
                         [] -> Nothing
                         h0:hs -> if (t h0 <= (minimum $ map t h)) then Just h0 else isWeakestCand t hs  


removeJust :: Maybe Cand -> Cand
removeJust Nothing = error "nothing to return"
removeJust (Just c) = c


                                                                              
tally :: Tally
tally = \c -> 0 % 1

pile :: Pile
pile = \c -> []


 


repeatFunction 0 f a = a
repeatFunction n f a = f $ repeatFunction (n -1) f a

ordOnce :: Tally -> [Cand] -> [Cand]
ordOnce t [] = []
ordOnce t [x] = [x]
ordOnce t (x:y:ys) = if (t x) <= (t y) then x: (ordOnce t (y:ys)) else y:(ordOnce t (x:ys))

updatePiles :: Ratio Integer -> Pile -> Tally -> [Cand] -> Pile
updatePiles qu p t l1 = \d -> if elem d l1 then 
                                    map (\b -> 
                                              (fst b, (snd b) * 
                                              ((1 % 1) - ((qu * 
                                              (denominator (t d) % 1)) * 
                                              (1 % (numerator (t d))))))) (p d)
                              else p d  

firstContinuingCand :: Cand -> [Cand] -> [Cand] -> Bool
firstContinuingCand c h [] = False
firstContinuingCand c h (b0:bs) = if (c == b0) then True
                                   else (notElem b0 h) && firstContinuingCand c h bs  


elimRule :: Parameters -> Judgement -> Judgement
elimRule (qu,st,l) (NonFinal [] t p [] e h) =
          --    if (length $ e ++ h) > st &&
                if (all ( < qu) $ map t h)
                   then let c = removeJust $ isWeakestCand t h
                        in NonFinal
                            (p c) t
                            (\d -> if d /= c then p d else []) [] e
                            (delete c h)
                 else (error "invalid elimRule app")
elimRule (qu,st,l) _ = error "invalid state reached"

electRule :: Parameters -> Judgement -> Judgement
electRule (qu,st,l) (NonFinal [] t p bl e h) =
              let l1 = filter (\c -> qu <= (t c)) h
              in
                let l2 = reverse $ (repeatFunction (length l1 - 1) (ordOnce t) l1)
                in
                  let l3 = take (st - (length e)) l2
                  in NonFinal
                       [] t
                       (updatePiles qu p t l3)
                       (bl ++ l3)
                       (e ++ l3)
                       (h \\ l3)
electRule (qu,st,l) _ = error "invalid electRule app"


countRule :: Parameters -> Judgement -> Judgement
countRule (qu,st,l) (NonFinal ba t p bl e h) =
    if not (null ba) then
      let  f = (\c -> if elem c h then 
                         let l' = filter (\b -> firstContinuingCand c h (fst b)) ba
                         in  ((t c) + (sum $ map snd l'), (p c) ++ l') 
                      else (t c, p c))
      in NonFinal [] (fst . f) (snd . f) bl e h
    else (error "invalid countRule app")                                                       
countRule (qu,st,l) _ = error "invalid countRule app"


transferRule :: Parameters -> Judgement -> Judgement
transferRule (qu,st,l) (NonFinal [] t p (bl0:bls) e h) =
   if all ( < qu) (map t h) then NonFinal (p bl0) t 
                                          (\c -> if (c /= bl0) then (p c) else [])
                                          bls e h
   else (error "invalid transferRule app")
transferRule (qu,st,l) _ = error "invalid transferRule app"


hwinRule :: Parameters -> Judgement -> Judgement
hwinRule (qu,st,l) (NonFinal ba t p bl e h) = Final $ e ++ h
hwinRule (qu,st,l) _ = error "invalid hwinRule app"

ewinRule :: Parameters -> Judgement -> Judgement
ewinRule (qu,st,l) (NonFinal ba t p bl e h) = Final e
ewinRule (qu,st,l) _ = error "invalid ewinRule app"

 
voteCounting :: Parameters -> Judgement -> Judgement
voteCounting (qu,st,l) (NonFinal ba t p bl e h) = 
  if (length $ e ++ h) <= st then hwinRule (qu,st,l) (NonFinal ba t p bl e h)
   else if (length e == st) then ewinRule (qu,st,l) (NonFinal ba t p bl e h)
         else if not (null ba) then voteCounting (qu,st,l) $ 
                                      countRule (qu,st,l) (NonFinal ba t p bl e h)
               else if any (qu <= ) (map t h) then voteCounting (qu,st,l) $
                                                    electRule (qu,st,l) (NonFinal ba t p bl e h)
                     else if null bl then voteCounting (qu,st,l) $
                                            elimRule (qu,st,l) (NonFinal ba t p bl e h)
                            else voteCounting (qu,st,l) $ 
                                   transferRule (qu,st,l) (NonFinal ba t p bl e h)
voteCounting (qu,st,l) _ = error "invalid state reached"



countingTrace (qu,st,l) acc (NonFinal ba t p bl e h) =  
   if (length $ e ++ h) <= st then (hwinRule (qu,st,l) (NonFinal ba t p bl e h)):(NonFinal ba t p bl e h):acc
    else if (length e == st) then (ewinRule (qu,st,l) (NonFinal ba t p bl e h)):(NonFinal ba t p bl e h):acc
           else if not (null ba) then countingTrace (qu,st,l) ((NonFinal ba t p bl e h):acc) $
                                      countRule (qu,st,l) (NonFinal ba t p bl e h)
               else if any (qu <= ) (map t h) then countingTrace (qu,st,l) ((NonFinal ba t p bl e h):acc) $
                                                    electRule (qu,st,l) (NonFinal ba t p bl e h)
                     else if null bl then countingTrace (qu,st,l) ((NonFinal ba t p bl e h):acc) $
                                            elimRule (qu,st,l) (NonFinal ba t p bl e h)
                                     else  countingTrace (qu,st,l) ((NonFinal ba t p bl e h):acc) $
                                               transferRule (qu,st,l) (NonFinal ba t p bl e h)
                                 

--printTrace (qu,st,l) ba = mapM_ print (countingTrace (qu,st,l) [] (NonFinal ba tally pile [] [] cand_all)) 
 
