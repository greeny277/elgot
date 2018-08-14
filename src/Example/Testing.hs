{-#  LANGUAGE FlexibleContexts #-}

module Example.Testing where

import Algebra.ProcessAlgebra
import Control.Monad.ElgotMonad
import Data.ElgotList
import Data.Probability

{- Some example processes -}
data Action = A | B | C | Coffee | Tea | Coin | Pub deriving (Show, Eq, Ord, Read)

{- Simple unguarded process -}
unguardedEx :: (ElgotMonad r, TossMonad t r) => t -> () -> Process String r (Either () ())
unguardedEx t () = choice t (inAct "a" >> resume ()) (resume ())

unguardedList :: Process String [] ()
unguardedList = iteration (unguardedEx ()) ()

unguardedEL :: Process String ElgotList ()
unguardedEL = iterationEq (unguardedEx ()) ()

{- Example for list vs set in Haskell -}
exampleSetVsList :: (ElgotMonad r, TossMonad t r) => t -> String -> Process String r (Either String String)
exampleSetVsList _ "R" = done "R"
exampleSetVsList t "P" = choice t (outAct "Valid" >> resume "P") (outAct "Error" >> resume "R")
exampleSetVsList _ "Q" =  inAct  "Valid" >> resume "R"
exampleSetVsList _ _ =  nil ()

testSetListEl :: Process String ElgotList (Either String String)
testSetListEl =  hidingEq ["Valid"] (comCoproductEq () (iterationEq (exampleSetVsList ()) "P", iterationEq (exampleSetVsList ()) "Q"))

testSetList :: Process String [] (Either String String)
testSetList = hiding ["Valid"] (comCoproduct () (iteration(exampleSetVsList ()) "P", iteration(exampleSetVsList ()) "Q"))


{- Simplest Probability example for testing purposes -}
evalSimpleProb :: [a] -> Process a Probability b -> [(Double, [ProcHelp a b])]
evalSimpleProb inputs proc = runProb $ eval inputs proc

simpleProb :: Process () Probability ()
simpleProb = iterationEq simpleProbProcess ()

simpleEL :: Process () ElgotList ()
simpleEL = iterationEq simpleELProcess ()

simpleProbProcess :: (Fractional t, ElgotMonad m, TossMonad t m) => () -> m (Either () ())
simpleProbProcess () = choice 0.5 (done ()) (resume ())

simpleELProcess :: (ElgotMonad m, TossMonad () m) => () -> m (Either () ())
simpleELProcess () = choice () (done ()) (resume ())

simplePar :: (ElgotMonad r) => String -> Process String r (Either String String)
simplePar "P" = inAct "foo" >> done "P"
simplePar "R" = outAct "foo" >> done "R"
simplePar _ = nil ()

testSimplePar :: Process String Probability (Either String String)
testSimplePar = comCoproductEq 0.5 (iterationEq simplePar "P", iterationEq simplePar "R")

testSimpleParList :: Process String [] (Either String String)
testSimpleParList = comCoproduct () (iteration simplePar "P", iteration simplePar "R")

testSimpleParEl :: Process String ElgotList (Either String String)
testSimpleParEl = comCoproduct () (iterationEq simplePar "P", iterationEq simplePar "R")

{- Process p is defined as follows:
 - PX = 0.3x + 0.3y + 0.4z
 - PY = 0.3 False + 0.3y + 0.4z
 - PZ = 0.3x + 0.3y + 0.4 True -}
p :: (TossMonad r m, Monad m, Fractional r) =>
     String -> m (Either Bool String)
p "Y" = do
        coin <- toss 0.3
        if coin
            then done False
            else do
                coin2 <- toss (0.3/0.7)
                if coin2
                    then resume "Y"
                    else resume "Z"
p "Z" = do
        coin <- toss 0.3
        if coin
            then resume "X"
            else do
                coin2 <- toss (0.3/0.7)
                if coin2
                    then resume "Y"
                    else done True
p _ = do
        coin <- toss 0.3
        if coin
            then resume "X"
            else do
                coin2 <- toss (0.3/0.7)
                if coin2
                    then resume "Y"
                    else resume "Z"

runP :: Probability Bool
runP = iterationEq p "X"


elgotTest :: Int -> [Either Int Int]
elgotTest n
    | n <= 0 = [Left 0]
    | otherwise = [Right $ n-1, Left n]
