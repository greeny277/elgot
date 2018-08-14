{-#  LANGUAGE GADTs  #-}
{-#  LANGUAGE MultiParamTypeClasses #-}

{-|
Module      : Data.Probability
Description : List-like datatype which stores the probability for each element.
Copyright   : (c) Christian Bay, 2017
License     : BSD-3
Maintainer  : christian.bay@fau.de
Stability   : experimental

-}
module Data.Probability (
                        Probability(..),
                        -- * Helper functions used for iteration.
                        History,
                        probIteration,
                        sumProbs,
                        rightProb,
                        leftProb,
                        findProb,
                        getProb,
                        removeProb,
                        substProb
                        ) where


import Control.Monad.ElgotMonad
import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad
import Control.Monad.State
import Data.Either
import Data.Maybe

-- | A simple list wrapper which assigns a probability to each element.
newtype Probability a = Probability {
                        runProb :: [(Double, a)]
                        }

instance Functor Probability where
        fmap f Probability { runProb = xs} = Probability $ fmap (second f) xs

instance Traversable Probability where
    traverse f xs = foldr cons_f (pure $ Probability []) (runProb xs)
                          where cons_f (r, x) ys = (\a b -> Probability [(r,a)] `mplus` b) <$> f x <*> ys

instance Applicative Probability where
        pure = return
        (<*>) = ap

instance Monad Probability where
        return x = Probability [(1, x)]
        Probability { runProb = xs } >>= k = Probability $
            xs >>= (\(r,x) -> case k x of
                                  Probability {runProb = ys} ->
                                      ys >>= (\(s, y) -> return (r*s,y))
                                      )

instance MonadPlus Probability where
        mzero = Probability []
        mplus a b = Probability $ runProb a ++ runProb b

instance ElgotMonad Probability where
        nil _ = Probability []

instance Alternative Probability where
        empty = Probability []
        a <|> b = Probability $ runProb a ++ runProb b

instance ElgotMonadEq Probability where
        iterationEq f a = evalState (probIteration f a) ([], [])

-- | List of substitutions for @'probIteration'@.
type History a b = [ (a, [(Double, Either b a)]) ]

{-|
This helper function is used for iteration. It uses a Gauß like algorithm to figure out
whether the process determinates and which probabilities the determining states
have.
This process can be imagined as an equation system, where each equation
represents a subprocess. The coefficients of the variables represent the
probability they are to be called next and the variables itself represent
the subprocesses. For example:

@X = 0.3X + 0.3Y + 0.4Z@

@Y = 0.3 False + 0.3Y + 0.4Z@

@Z = 0.3X + 0.3Y + 0.4 True@

The algorithm keeps track of all already called subprocesses
and the substitution of each subprocess.
In each step the probabilities for all selfreferencing calls are summed up and
distributed on each other subprocess accordingly to their relative probability.
The resulting equation serves as substitution for the current process.
The already tracked substitutions get traversed and each occurrence of current process
will be substituted again relative to their probability.
Then each subprocess left will be called if not already visited. This process continues until
all possible paths are traversed or the behaviour of each subprocess is
evaluated.
-}
probIteration :: Eq a => (a -> Probability (Either b a)) -> a -> State ([a], History a b) (Probability b)
probIteration f a = do (visited, varHist) <- get
                       let sumComp   = sumProbs $ f a       -- :: Probability (Either b a)
                           -- Filtering resuming computations
                           sumRightComp = rightProb sumComp -- :: Probability a
                           -- List of variables known from History only
                           vars       = fmap fst varHist         --  :: [a]
                           newL = sumProbs $ foldr (\resumeVar currentList ->
                                               if resumeVar `elem` vars
                                                   then substProb resumeVar (Probability $ fromJust $ lookup resumeVar varHist) currentList
                                                   else currentList) sumComp sumRightComp
                           -- Cut out every Resume variable known from history
                           containsA  = findProb a newL   -- :: Bool
                           -- When selfreferencing calls are happening, look for their summed Probability
                           probA     = if containsA         -- :: Double
                                           then getProb a newL
                                           else 0
                           -- The resulting list does neither contain the current variable nor variables which are already known from history
                           restList  = if containsA
                                           then removeProb a newL
                                           else newL
                           hasResume = foldr (\x acc -> isRight x || acc) False restList -- :: Bool
                       if null restList || a `elem` visited
                               then return $ nil ()
                               else
                                    if hasResume
                                       then let -- Distribute the probability of selfreferencing calls on other processes
                                                dependenciesA = fmap (\(r, rest) -> (r/(1-probA), rest)) (runProb restList)  -- :: [(r, Either b a )]
                                                -- Traverse history and substitute each occurence of 'a' with 'dependenciesA'
                                                representA = (a, dependenciesA) : fmap (\(var, depList) -> (var, runProb (sumProbs $ substProb a (Probability dependenciesA) (Probability depList)))) varHist  -- :: History
                                                resumeComp = rightProb restList -- :: Probability a
                                            in  do
                                                   -- Update state
                                                   put (a:visited, representA)
                                                   -- Make recursively calls. The result doesn't matter. The history state is important only
                                                   forM_ resumeComp (probIteration f)
                                                   if null varHist
                                                       then do
                                                          (_, endHist) <- get
                                                          return . leftProb . Probability $ join [hist | (var, hist) <- endHist, var == a]
                                                       else return mzero
                                       else let ls = runProb $ leftProb restList -- :: [b]
                                                sumProbLs = foldr (\(r,_) acc -> r+acc) 0 ls -- :: Double
                                                result = fmap (\(r,y) -> (r + (r/sumProbLs) * probA, Left y)) ls
                                                -- Traverse history and substitute each occurence of 'a' with 'dependenciesA'
                                                representA = (a, result) : fmap (\(v, depList) -> (v, runProb (sumProbs $ substProb a (Probability result) (Probability depList)))) varHist  -- :: History
                                            in if null varHist
                                                   then return $ leftProb $ Probability result
                                                   else do
                                                           put (a:visited, representA)
                                                           return mzero

instance TossMonad Double Probability where
        toss r = Probability [(r, True), (1-r, False)]

instance (Eq a) => Eq (Probability a) where
        Probability {runProb = xs} == Probability {runProb = ys } = xs == ys

instance (Show a) => Show (Probability a) where
        show Probability {runProb = xs} = "Probability (" ++ show xs ++ ")"

instance Foldable Probability where
        foldr f acc Probability {runProb = xs} = foldr (\(_, x) a -> f x a)  acc xs

-- | Find duplicates and sum up their probabilities
sumProbs :: (Eq a) => Probability (Either b a) -> Probability (Either b a)
sumProbs Probability {runProb = xs} =
        let rs = rightProb $ Probability xs
            ls = leftProb $ Probability xs
            newRs = Probability $ foldr (\(r, x) acc ->
                            if x `elem` map snd acc
                                then map (\(r2, x2) ->
                                    if x == x2
                                        then (r+r2, x)
                                        else (r2, x2)
                                        ) acc
                                else (r,x) : acc
                                    ) [] $ runProb rs
            in fmap Left ls `mplus` fmap Right newRs

-- | Collect all elements of type @a@.
rightProb :: Probability (Either b a) -> Probability a
rightProb Probability {runProb = xs} = Probability $
        foldr (\(r,x) acc -> case x of
                             Left _ -> acc
                             Right inner -> (r,inner):acc
                             ) [] xs

-- | Collect all elements of type @b@.
leftProb :: Probability (Either b a) -> Probability b
leftProb Probability {runProb = xs} = Probability $
        foldr (\(r,x) acc -> case x of
                             Left inner -> (r,inner):acc
                             Right _ -> acc
                             ) [] xs

-- | Search for a specific element.
findProb :: Eq a => a -> Probability (Either b a) -> Bool
findProb a Probability {runProb = xs} =
        foldr (\(_,x) acc -> case x of
                                 Left _ -> acc;
                                 Right res -> (res == a) || acc)
                                 False xs

-- | Get the probability of an element. If it doesn't exist return 0.
getProb :: Eq a => a -> Probability (Either b a) -> Double
getProb a Probability {runProb = xs} =
        foldr (\(r,x) acc -> case x of
                                 Left _ -> acc;
                                 Right res -> if res == a
                                                then r+acc
                                                else acc) 0 xs

-- | Remove an element if it exists.
removeProb :: Eq a => a -> Probability (Either b a) -> Probability (Either b a)
removeProb a Probability {runProb = xs} = Probability $
        foldr (\(r,x) acc -> case x of
                                 Left y -> (r, Left y):acc;
                                 Right res -> if res /= a
                                                then (r, Right res):acc
                                                else acc) [] xs

-- | Substitute an element with a probability.
substProb :: Eq a => a -> Probability (Either b a) -> Probability (Either b a) -> Probability (Either b a)
substProb old new prob =
        if findProb old prob
             then let probOld = getProb old prob -- :: Double
                      cleaned = removeProb old prob -- :: Probability (Either b a)
                      in cleaned `mplus` Probability (first (probOld *) <$> runProb new)
             else prob
