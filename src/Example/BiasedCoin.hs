{-|
Module      : Example.BiasedCoin
Description : A fair coin flipping procedure with a biased coin.
Copyright   : (c) Christian Bay, 2017
License     : BSD-3
Maintainer  : christian.bay@fau.de
Stability   : experimental

A process which implements von Neumanns (see <https://en.wikipedia.org/wiki/Fair_coin>) procedure
to flip a coin in a fair way if it's biased.

-}
module Example.BiasedCoin (
                          biasedCoin,
                          biasedCoinEval
                          ) where
import Algebra.ProcessAlgebra
import Control.Monad.ElgotMonad
import Data.Probability

-- | The biased coin procedure implemented in an iterative way.
biasedCoin :: (TossMonad a m, ElgotMonad m) => a -> () -> m (Either Bool ())
biasedCoin p () = do
        a <- toss p
        b <- toss p
        if a == b
            then resume ()
            else done a

-- | Compute biased coin if it runs infinitely.
biasedCoinEval :: Double -> Process String Probability Bool
biasedCoinEval biased = iterationEq (biasedCoin biased) ()
