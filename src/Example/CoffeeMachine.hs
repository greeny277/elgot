{-#  LANGUAGE KindSignatures #-}
{-#  LANGUAGE Rank2Types #-}
{-|
Module      : Example.CoffeeMachine
Description : The standard example of process algebra. A student interacting with a coffee machine to produce papers.
Copyright   : (c) Christian Bay, 2017
License     : BSD-3
Maintainer  : christian.bay@fau.de
Stability   : experimental

The standard example for communication processes. A computer science student
does request a coffee from a coffee machine and publishes a paper whenever he
gets one. Two different coffee machines are implemented.

-}
module Example.CoffeeMachine (
                             -- * Introduce processes
                             coffeeMachine,
                             coffeeMachine2,
                             computerStudent,
                             university,
                             university2,
                             universityEq,
                             university2Eq,
                             -- * Tests
                             testUni,
                             testUni2,
                             testUniEL,
                             testUni2EL,
                             testUniProb,
                             testUni2Prob
                             )
                             where

import Algebra.ProcessAlgebra
import Control.Monad.ElgotMonad
import Data.ElgotList
import Data.Probability

-- | A coffee machine which chooses its output before entering the coin.
--
-- @
-- CM = (coin.¬coffee.CM) + (coin.¬tea.CM)
-- @
coffeeMachine :: (ElgotMonad r, TossMonad t r) => t -> () -> IterFT (Step String) r (Either () ())
coffeeMachine t () = choice t (inAct "Coin" >> outAct "Coffee" >> resume ()) (inAct "Coin" >> outAct "Tea" >> resume ())

-- | A coffee machine which chooses its output after entering the coin.
--
-- @
-- CM2 = coin.(¬coffee + ¬tea).CM2
-- @
coffeeMachine2 :: (ElgotMonad r, TossMonad t r) => t -> () -> IterFT (Step String) r (Either () ())
coffeeMachine2 t () = inAct "Coin" >> choice t (outAct "Coffee" >> resume ()) (outAct "Tea" >> resume ())

-- | The computer student publishes after drinking his coffee:
--
-- @
-- CS = ¬coin.coffee.¬pub.CS
-- @
computerStudent :: ElgotMonad r => () -> IterFT (Step String) r (Either () ())
computerStudent () = outAct "Pub" >> outAct "Coin" >> inAct "Coffee" >> resume ()

-- | The @'computerStudent'@ is parallelized with @'coffeeMachine'@ and
-- hides every action except @pub@. The first value for tossing is used for
-- parallelization and the second one for the choice.
--
-- @(CS | CM)\\{Coffee, Coin, Tea}@
university :: (ElgotMonad m, TossMonad t m) => t -> t -> IterFT (Step String) m (Either () ())
university parallelToss choiceToss = hiding ["Coffee", "Coin", "Tea"] (comCoproduct parallelToss (iteration computerStudent (), iteration (coffeeMachine choiceToss) ()))

-- | Same as @'university'@ except with equality constraint by
-- implication of @'ElgotMonadEq'@.
universityEq :: forall (r :: * -> *) t.
                (ElgotMonadEq r, TossMonad t r,
                 Eq (r (StepEither (Step String) () (IterFT (Step String) r ()))),
                 Eq
                   (r (StepEither
                         (Step String)
                         (Either () ())
                         (IterFT (Step String) r (Either () ()))))) =>
                t -> t -> IterFT (Step String) r (Either () ())
universityEq parallelToss choiceToss = hidingEq ["Coffee", "Coin", "Tea"] (comCoproductEq parallelToss (iterationEq computerStudent (), iterationEq (coffeeMachine choiceToss) ()))

-- | The @'computerStudent'@ is parallelized with @'coffeeMachine2'@ and
-- hides every action except @pub@.
--
-- @(CS | CM2)\\{Coffee, Coin, Tea}@
university2 :: (ElgotMonad m, TossMonad t m) => t -> t -> IterFT (Step String) m (Either () ())
university2 parallelToss choiceToss = hiding ["Coffee", "Coin", "Tea"] (comCoproduct parallelToss (iteration computerStudent (), iteration (coffeeMachine2 choiceToss) ()))

-- | Same as @'university2'@ except with equality constraint by implication
-- of @'ElgotMonadEq'@.
university2Eq :: forall (r :: * -> *) t.
                (ElgotMonadEq r, TossMonad t r,
                 Eq (r (StepEither (Step String) () (IterFT (Step String) r ()))),
                 Eq
                   (r (StepEither
                         (Step String)
                         (Either () ())
                         (IterFT (Step String) r (Either () ()))))) =>
                t -> t -> IterFT (Step String) r (Either () ())
university2Eq parallelToss choiceToss = hidingEq ["Coffee", "Coin", "Tea"] (comCoproductEq parallelToss (iterationEq computerStudent (), iterationEq (coffeeMachine2 choiceToss) ()))

-- | Test @'university'@ with list monad.
testUni :: IterFT (Step String) [] (Either () ())
testUni = university () ()

-- | Test @'university2'@ with list monad.
testUni2 :: IterFT (Step String) [] (Either () ())
testUni2 = university2 () ()

-- | Test @'universityEq'@ with @'ElgotList'@ monad.
testUniEL :: IterFT (Step String) ElgotList (Either () ())
testUniEL = universityEq () ()

-- | Test @'university2Eq'@ with @'ElgotList'@ monad.
testUni2EL :: IterFT (Step String) ElgotList (Either () ())
testUni2EL = university2Eq () ()

-- | Test @'university'@ with @'Probability'@ monad. Pass a value between
-- 0 and 1 to specify with which probability the coffeemachine produces
-- coffee.
testUniProb :: Double -> IterFT (Step String) Probability (Either () ())
testUniProb = universityEq 0.5

-- | Test @'university2'@ with @'Probability'@ monad. Pass a value between
-- 0 and 1 to specify with which probability the coffeemachine produces
-- coffee.
testUni2Prob :: Double -> IterFT (Step String) Probability (Either () ())
testUni2Prob = university2Eq 0.5
