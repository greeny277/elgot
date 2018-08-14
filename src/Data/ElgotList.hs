{-#  LANGUAGE MultiParamTypeClasses #-}

{-|
Module      : Data.ElgotList
Description : A structure of a list which imitates the behaviour of a set.
Copyright   : (c) Christian Bay, 2017
License     : BSD-3
Maintainer  : christian.bay@fau.de
Stability   : experimental

A simple list-like structure which stops iterations after recurrence of arguments.
-}

module Data.ElgotList (
                      ElgotList (..),
                      ) where

import Control.Applicative
import Control.Monad
import Control.Monad.ElgotMonad

-- | Data type for an alternative list implementation.
newtype ElgotList a = EL {
                      runEL :: [a]
}

instance Monad ElgotList where
        return a = EL [a]
        r >>= k = EL (runEL r >>= \e -> runEL (k e))

instance Applicative ElgotList where
        pure = return
        (<*>) = ap

instance Functor ElgotList where
        fmap f (EL l) = EL (fmap f l)

instance Alternative ElgotList where
        empty = EL []
        a <|> b = EL $ runEL a ++ runEL b

instance MonadPlus ElgotList where
        mzero = EL []
        mplus a b = EL $ runEL a ++ runEL b

instance (Show a) => Show (ElgotList a) where
        show (EL l) = "EL " ++ show l

instance ElgotMonad ElgotList where
        nil _ = EL []

instance (Eq a) => Eq (ElgotList a) where
        EL a == EL b = a == b

instance ElgotMonadEq ElgotList where
        -- | Behave as a set and stop iteration after first recurrence.
        iterationEq = emulateSet []

instance TossMonad () ElgotList where
        toss _ = EL [True, False]

emulateSet :: (Eq a, ElgotMonad m) => [a] -> (a -> m (Either b a)) -> a -> m b
emulateSet prevArgs f a =
        if a `elem` prevArgs
                   then f a >>= either return (const $ nil ())
                   else f a >>= either return (emulateSet (a:prevArgs) f)
