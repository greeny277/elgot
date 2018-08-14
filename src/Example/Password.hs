{-|
Module      : Example.Password
Description : An exemplary process which checks passwords.
Copyright   : (c) Christian Bay, 2017
License     : BSD-3
Maintainer  : christian.bay@fau.de
Stability   : experimental

-}
module Example.Password (
                        checkPassword,
                        testPasswordList,
                        testPasswordEL,
                        testPasswordProb
                        ) where

import Algebra.ProcessAlgebra
import Control.Monad.ElgotMonad
import Data.ElgotList
import Data.Probability

-- | An example process representing a password checker
checkPassword :: (ElgotMonad r, TossMonad t r) => t -> String -> Process String r (Either String String)
checkPassword _ "Prompt" = inAct "password" >> outAct "startCheck" >> inAct "invalid" >> resume "Prompt"
checkPassword _ "Verify" = inAct "startCheck" >> resume "Evaluate"
checkPassword t "Evaluate" = choice t (outAct "invalid" >> resume "Verify") (resume "Login")
checkPassword _ "Login" =  outAct "correct" >> done "Login"
checkPassword _ _ =  nil ()

-- | Test the password process with normal list behaviour.
testPasswordList :: Process String [] (Either String String)
testPasswordList = hiding ["startCheck", "invalid"] (comCoproduct () (iteration(checkPassword ()) "Prompt", iteration(checkPassword ()) "Verify"))

-- | Test the password process with set-like behaviour.
testPasswordEL :: Process String ElgotList (Either String String)
testPasswordEL = hidingEq ["startCheck", "invalid"] (comCoproductEq () (iterationEq (checkPassword ()) "Prompt", iterationEq (checkPassword ()) "Verify"))

-- | Test the password process with probabilities
--
-- To get the possible final states of the process with their probabilities run the following:
--
-- >>> sumDuplicates $ evalProb ["password"] testPasswordProb
-- Probability ([(0.5,["password",τ,τ]),(0.5,["password",τ,¬"correct",Right "Login"])])
--
-- Accordingly the outgoing actions with their probabilities can be
-- evaluated:
--
-- >>> sumDuplicates $ evalOutProb ["password"] testPasswordProb
-- Probability ([(0.5,[]),(0.5,[¬"correct"])])
testPasswordProb :: Process String Probability (Either String String)
testPasswordProb = hidingEq ["startCheck", "invalid"] $ comCoproductEq 0.5 (iterationEq (checkPassword 0.5) "Prompt", iterationEq (checkPassword 0.5) "Verify")
