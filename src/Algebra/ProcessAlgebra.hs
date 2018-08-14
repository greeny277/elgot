{-#  LANGUAGE MultiParamTypeClasses #-}
{-#  LANGUAGE FlexibleContexts #-}
{-#  LANGUAGE FlexibleInstances  #-}

{-|
Module      : Algebra.ProcessAlgebra
Description : A module which implements the process algebra 'calculus of communication sytems' (CCS) introduced by Robin Milner.
Copyright   : (c) Christian Bay, 2017
License     : BSD-3
Maintainer  : christian.bay@fau.de
Stability   : experimental

This module allows to create processes in terms of Robin Milners 'calculus
of communicating systems' (<https://en.wikipedia.org/wiki/Calculus_of_communicating_systems>) which
has following syntax and semantic:

* Syntax;
  \[
     P, Q ::= K \bigm\vert \emptyset \bigm\vert \alpha.P \bigm\vert \sum_{i \in I} P_i \bigm\vert P \mid Q \bigm\vert P[f] \bigm\vert P\backslash L
  \]

    *  \(\mathscr{A}\) is the set of possible input-action names. \(\overline{\mathscr{A}}\) contains the corresponding
    output-actions.
    * \(Act = \mathscr{A} \cup \overline{\mathscr{A}} \cup{\tau}\).
    * @K@ is a process-name from the set of all process-names and serves as an identifier.
    * \(L\) is a subsetset of \(\mathscr{A}\).
    * \(\alpha\) is a action from \(Act\).
    * \(I\) is an arbitrary set of indices.
    * \(f: InAct \rightarrow InAct\) is a  renaming function which satisfies \(f(\tau) = \tau\) and \(f(\overline{a}) = \overline{f(a)}\).

* Semantic:

    * \(\emptyset\): No further action possible. It may be worth mentioning that the deadlock can be represented
    through __choice__ with \(I = \{\}\) but for clarification it is explicitly listed in the grammar.
    * \(\alpha.P\): Performs any action \(\alpha\) and proceed as process \(P\).
    * \(\sum_{i \in I} P_i\): This process has a choice as which process it continues. This module
    allows to attach probabilities \(p_i\) to each \(P_i\) with \(\sum_{i \in I}p_i = 1\).
    * \(P \mid Q\): The process consist of two processes which do simultaneously exist. Two different
    behaviours are possible:

          - Interleaving: \(P\) or \(Q\) can make steps on their own in any order.
          - Synchronisation: If one process can perform any input-action \(a\) and the other one
            the corresponding output-action \(\overline{a}\), then both can make a step together, symbolized with the \(\tau\) action.
            For example
            \[
                  P\mid Q \overset{\tau}{\rightarrow} P'\mid Q' \Leftrightarrow
                  \exists a. (P \overset{a}{\rightarrow} P') \wedge  (Q \overset{\overline{a}}{\rightarrow} Q')
             \]

    * \(P[f]\): A process that behaves like process \(P\) but has its actions renamed with the function \(f\).
    * \(P\backslash L\): A process \(P\) without any actions from \(L\).

* Implementation:
    The behaviour of Robin Milner processes can be imagined as a big DAG or Tree where each node represents a process
    and each branche describes the action which turns one process into another.
    Therefore processes are fitting well in the structure of the @'IterFT'@ datatype because it spans a computation tree.
    The @'Step'@ functor models input-actions and output-actions of processes as well as synchronization amongst each other.

* Probabilities in process behavior:
    This module extends Robin Milners process-algebra by allowing __probabilities__ at each
    process when there is a choice (\(+\)-Operation) between processes. Therefore the
    @'Probability'@ monad can be used.

-}
module Algebra.ProcessAlgebra(
                     -- * Process operations
                     Step(..),
                     Process,
                     inAct,
                     outAct,
                     choice,
                     comCoproduct,
                     comCoproductEq,
                     renaming,
                     renamingEq,
                     hiding,
                     hidingEq,
                     -- * Process evaluation
                     ProcHelp(..),
                     eval,
                     evalOut,
                     evalProb,
                     evalOutProb,
                     evalIO,
                     evalOutIO,
                     sumDuplicates,
                     ) where

import Control.Monad.ElgotMonad
import Data.Probability

import Control.Monad
import Data.Char (toLower)
import Data.Maybe (fromJust, listToMaybe)
import Text.Read (readMaybe)


-- | A functor which is used to represent the different process actions.
data Step a x =
        -- | The process can perform an outgoing action 'a' und continues
        -- with process 'x'
        Out a x
        -- | @In@ takes a function which returns an empty process for
        -- unknown ingoing actions and a resulting process otherwise
        | In (a -> x)
        -- | Different processes can be synchronized via parallelism. If
        -- one process expects an ingoing action which another process
        -- performs as outgoing action they can step together to their
        -- following process.
        | Tau x

instance Functor (Step a) where
        (fmap f) (Out a x) = Out a (f x)
        (fmap f) (In g)    = In (f . g)
        (fmap f) (Tau x)   = Tau (f x)
-- | The equality condition has been introduced to support instances of
-- @'ElgotMonadEq'@. In each case where an @'In'@ constructor is involved
-- the equality can't be determined any more because their argument is
-- a function. Thus relying on those equality relations can't be
-- recommended and when possible this instance should be removed.
instance (Eq a, Eq x) => Eq (Step a x) where
        Out a x == Out b y = a == b && x == y
        Tau x   == Tau y   = x == y
        (==) _ _ = False

-- | A process alias
type Process a = IterFT (Step a)

-- | Creates a process based on input-action @a@. The resulting process
-- expects an input-action (represented through @'In'@) and returns @()@ if
-- the ingoing action is @a@ and deadlock otherwise.
inAct :: (Eq a, ElgotMonad r) => a -> Process a r ()
inAct a = IterFT $ return (Resume (In (\b -> unless (b == a) $
              IterFT $ nil ()
              )))

-- | Create a process based on output-action @a@. The resulting
-- process produces this outgoing action (represented through @'Out'@) and
-- ends afterwards.
outAct :: (ElgotMonad r) => a -> Process a r ()
outAct a = IterFT . return $  Resume (Out a (return ()))

-- | Build sum of two processes.
choice :: (ElgotMonad m, TossMonad t m) => t -> m b -> m b -> m b
choice prob p q = do
        coin <- toss prob
        if coin
            then p
            else q

-- | Parallelize two processes
comCoproduct :: (ElgotMonad r, TossMonad t r) => t -> (Process a r x, Process a r y) -> Process a r (Either x y)
comCoproduct t (p,q) = iteration (comCoproductIter t) (p,q)

-- | Parallelize two processes
comCoproductEq :: (ElgotMonadEq r, TossMonad t r, Eq (r (StepEither (Step a) x (Process a r x))), Eq (r (StepEither (Step a) y (Process a r y)))) => t -> (Process a r x, Process a r y) -> Process a r (Either x y)
comCoproductEq t (p,q) = iterationEq (comCoproductIter t) (p,q)

comCoproductIter :: (TossMonad t r, ElgotMonad r) => t -> (Process a r x, Process a r y) -> Process a r (Either (Either x y) (Process a r x, Process a r y))
comCoproductIter t (p,q) = IterFT $ do
    p' <- runIterFT p
    q' <- runIterFT q
    case (p', q') of
        (Done x, Done y) -> do coin <- toss t
                               if coin
                                   then return (Done (Left (Left x)))
                                   else return (Done (Left (Right y)))
        (Done _, Resume (Out q_out q_inner)) -> return (Resume (Out q_out (IterFT . return $ Done (Right (p, q_inner)))))
        (Done x, Resume (In f)) ->
            do coin <- toss t
               if coin
                   then return (Done (Left (Left x)))
                   else return (Resume (In (\input -> IterFT (return (Done (Right (p, f input)))))))
        (Done _, Resume (Tau q_inner)) -> return (Resume (Tau (IterFT . return $ Done (Right (p, q_inner)))))

        (Resume (Out p_out p_inner), Done _) -> return $ Resume (Out p_out (IterFT . return $ Done (Right (p_inner, q))))
        (Resume (Out p_out p_inner), Resume (Out q_out q_inner)) ->
            do coin <- toss t
               if coin
                   then return (Resume (Out p_out (IterFT . return $ Done (Right (p_inner, q)))))
                   else return (Resume (Out q_out (IterFT . return $ Done (Right (p, q_inner)))))
        (Resume (Out p_out p_inner), Resume (In f)) ->
            do coin1 <- toss t
               coin2 <- toss t
               if coin1
                   then return (Resume (Tau (IterFT ( return ( Done (Right (p_inner, f p_out)))))))
                   else if coin2
                               then return (Resume (Out p_out (IterFT ( return ( Done (Right (p_inner, q)))))))
                               else return (Resume (In (\input -> IterFT (return ( Done (Right (p, f input)))))))
        (Resume (Out p_out p_inner), Resume (Tau q_inner)) ->
            do coin <- toss t
               if coin
                   then return (Resume (Out p_out (IterFT . return $ Done (Right (p_inner, q)))))
                   else return (Resume (Tau (IterFT . return $ Done (Right (p, q_inner)))))
        (Resume (In f), Done y) ->
            do coin <- toss t
               if coin
                   then return (Done (Left (Right y)))
                   else return (Resume (In (\input -> IterFT (return (Done (Right (f input, q)))))))
        (Resume (In f), Resume (Out q_out q_inner)) ->
            do coin1 <- toss t
               coin2 <- toss t
               if coin1
                   then return (Resume (In (\input -> IterFT (return (Done (Right (f input,q)))))))
                   else if coin2
                               then return (Resume (Out q_out (IterFT (return (Done (Right (p, q_inner)))))))
                               else return (Resume (Tau (IterFT (return (Done (Right (f q_out, q_inner)))))))

        (Resume (In f), Resume (In g)) ->
            do coin <- toss t
               if coin
                   then return (Resume (In (\input -> IterFT (return (Done (Right (f input, q)))))))
                   else return (Resume (In (\input -> IterFT (return (Done (Right (p, g input)))))))
        (Resume (In f), Resume (Tau q_inner)) ->
            do coin <- toss t
               if coin
                   then return (Resume (Tau (IterFT (return (Done (Right (p, q_inner)))))))
                   else return (Resume (In (\input -> IterFT (return (Done (Right (f input,q)))))))
        (Resume (Tau p_inner), Done _) -> return (Resume (Tau (IterFT . return $ Done (Right (p_inner, q)))))
        (Resume (Tau p_inner), Resume (Tau q_inner)) ->
            do coin <- toss t
               if coin
                   then return (Resume (Tau (IterFT . return $ Done (Right (p_inner, q)))))
                   else return (Resume (Tau (IterFT . return $ Done (Right (p, q_inner)))))
        (Resume (Tau p_inner), Resume (Out q_out q_inner)) ->
            do coin <- toss t
               if coin
                   then return (Resume (Tau (IterFT . return $ Done (Right (p_inner, q)))))
                   else return (Resume (Out q_out (IterFT . return $ Done (Right (p, q_inner)))))
        (Resume (Tau p_inner), Resume (In f)) ->
            do coin <- toss t
               if coin
                   then return (Resume (Tau (IterFT (return (Done (Right (p_inner, q)))))))
                   else return (Resume (In (\input -> IterFT (return (Done (Right (p, f input)))))))

-- | Renames actions of a process.
-- The rename function 'f' has to satisfy following condition for each @a@:
--
--   > f a = f (f a)
renaming :: ElgotMonad r => (a -> a) -> Process a r x -> Process a r x
renaming rename = iteration (renamingIter rename)

-- | Same as for @'renaming'@.
renamingEq :: (ElgotMonadEq r, Eq (r (StepEither (Step a) x (Process a r x)))) => (a -> a) -> Process a r x -> Process a r x
renamingEq f = iterationEq (renamingIter f)

renamingIter :: (ElgotMonad r) => (a -> a) -> Process a r x -> Process a r (Either x (Process a r x))
renamingIter rename p = IterFT $ runIterFT p >>= \p_rec ->
        case p_rec of
            Done x -> return (Done (Left x))
            Resume (Out p_out p_inner) -> return $ Resume (Out (rename p_out) (IterFT . return $ Done (Right p_inner)))
            Resume (Tau p_inner) -> return $ Resume (Tau (IterFT . return $ Done (Right p_inner)))
            Resume (In f) -> return $ Resume (In (IterFT . return . Done . Right . f . rename ))


-- | Hide actions in a process.
hiding :: (Eq a, ElgotMonad r) => [a] -> Process a r x -> Process a r x
hiding hiddens = iteration (hidingIter hiddens)

-- | Same as for @'hiding'@.
hidingEq :: (Eq a, ElgotMonadEq r, Eq (r (StepEither (Step a) x (Process a r x)))) => [a] -> Process a r x -> Process a r x
hidingEq hiddens = iterationEq (hidingIter hiddens)

hidingIter :: (Eq a, ElgotMonad r) => [a] -> Process a r x -> Process a r (Either x (Process a r x))
hidingIter hiddens p = IterFT $ runIterFT p >>= \p_rec -> case p_rec of
                                     Done x -> return (Done (Left x))
                                     Resume (Out p_out p_inner) -> if p_out `elem` hiddens
                                                    then nil ()
                                                    else return $ Resume (Out p_out (IterFT . return $ Done (Right p_inner)))
                                     Resume (Tau p_inner) -> return $ Resume (Tau (IterFT . return $ Done (Right p_inner)))
                                     Resume (In f) -> return $ Resume (In (\input -> if input `elem` hiddens
                                            then IterFT $ nil ()
                                            else IterFT (return (Done (Right (f input))))
                                            ))

-- | Datatype which is used to represent behaviour of evaluated processes.
data ProcHelp a s =
        -- | Process has performed an outgoing action @a@.
        OutAct a
        -- | Process has performed an ingoing action @a@.
        | InAct a
        -- | The synchronize operation between to processes has been performed.
        | Synchronize
        -- | The ending of a process.
        | PName s
        deriving (Eq, Ord)
instance (Show a, Show s) => Show (ProcHelp a s) where
        show (OutAct s) = "¬" ++ fmap toLower (show s)
        show (InAct s) = fmap toLower (show s)
        show Synchronize = "τ"
        show (PName s) = show s

-- | Evaluate a process with a list of sequencing ingoing actions. The
-- process is evaluated until it terminates and returns a list of
-- all possible process behaviours.
eval :: ElgotMonad r => [a] -> Process a r x -> r [ProcHelp a x]
eval [] r     = runIterFT r >>= \inner -> case inner of Done x -> return [PName x]; Resume (Out o p) -> fmap (OutAct o:)  (eval [] p); Resume (In _) -> return []; Resume (Tau p) -> fmap (Synchronize:) (eval [] p)
eval inputs@(a:as) r = runIterFT r >>= \inner -> case inner of Done x -> return [PName x]; Resume (Out o p) -> fmap (OutAct o:)  (eval inputs p); Resume (In f) -> fmap (InAct a:) (eval as (f a)); Resume (Tau p) -> fmap (Synchronize :)  (eval inputs p)

-- | Evaluate a process with a list of sequencing ingoing actions. The
-- process is evaluated until it terminates and returns a list of
-- outgoing actions for each possible process.
evalOut :: ElgotMonad r => [a] -> Process a r x -> r [ProcHelp a x]
evalOut [] r     = runIterFT r >>= \inner -> case inner of Done _ -> return []; Resume (Out o p) -> fmap (OutAct o:) (evalOut [] p); Resume (In _) -> return []; Resume (Tau p) -> evalOut [] p
evalOut inputs@(a:as) r = runIterFT r >>= \inner -> case inner of Done _ -> return []; Resume (Out o p) -> fmap (OutAct o:) (evalOut inputs p); Resume (In f) -> evalOut as (f a); Resume (Tau p) -> evalOut inputs p;

-- | An explicit evaluation for processes using the @'Probability'@ monad.
-- The input-actions have to be an @'Eq'@ instance and in addition
-- after each evaluation step the probabilities need to be renormalized.
evalProb :: Eq a => [a] -> Process a Probability x -> Probability [ProcHelp a x]
evalProb [] r = renormalize [] (runIterFT r) >>= \inner -> case inner of Done x -> return [PName x]; Resume (Out o p) -> fmap (OutAct o:)  (evalProb [] p); Resume (In _) -> return []; Resume (Tau p) -> fmap (Synchronize:) (evalProb [] p)
evalProb inputs@(a:as) r = renormalize inputs (runIterFT r) >>= \inner -> case inner of Done x -> return [PName x]; Resume (Out o p) -> fmap (OutAct o:)  (evalProb inputs p); Resume (In f) -> fmap (InAct a:) (evalProb as (f a)); Resume (Tau p) -> fmap (Synchronize :)  (evalProb inputs p)

-- | Same as @'evalProb'@ but collecting the outgoing-actions only.
evalOutProb :: Eq a => [a] -> Process a Probability x -> Probability [ProcHelp a x]
evalOutProb [] r     = renormalize [] (runIterFT r) >>= \inner -> case inner of Done _ -> return []; Resume (Out o p) -> fmap (OutAct o:) (evalOutProb [] p); Resume (In _) -> return []; Resume (Tau p) -> evalOutProb [] p
evalOutProb inputs@(a:as) r = renormalize inputs (runIterFT r) >>= \inner -> case inner of Done _ -> return []; Resume (Out o p) -> fmap (OutAct o:) (evalOutProb inputs p); Resume (In f) -> evalOutProb as (f a); Resume (Tau p) -> evalOutProb inputs p;

-- | Read in input-actions for a process, evaluate it and print to the end.
evalIO :: (Read a, Show (r [ProcHelp a b]), ElgotMonad r) => Process a r b -> IO ()
evalIO example = do
        inActs <- prompt
        if any null inActs
            then putStrLn "Action can't be parsed. If actions are of type 'String' they need to be enclosed by \". Try again:" >> evalIO example
            else do
                   let inActs' = map fromJust inActs
                   let trace = eval inActs' example
                   print trace

-- | Read in input-actions for a process and evaluate it to the end.
evalOutIO :: (Read a, Show (r [ProcHelp a b]), ElgotMonad r) => Process a r b -> IO ()
evalOutIO example = do
        inActs <- prompt
        if any null inActs
            then putStrLn "Action can't be parsed. If actions are of type 'String' they need to be enclosed by \". Try again:" >> evalOutIO example
            else do
                   let inActs' = map fromJust inActs
                   let trace = evalOut inActs' example
                   print trace

{- Perform an IO-action to read in the list of incoming process-actions -}
prompt :: Read a => IO [Maybe a]
prompt = do
        putStrLn "Please enter the ingoing actions for your process"
        putStrLn "Format: act1 act2 ... actN"
        fmap (fmap readMaybe . words) getLine

-- | Sum-up probabilities of equal processes.
sumDuplicates ::  Eq (f a) => Probability (f a) -> Probability (f a)
sumDuplicates procRes = Probability $ foldr (\(r,x) acc -> let processes = fmap snd acc
                                                    in if x `elem` processes
                                                           then fmap (\(p, y) -> if y == x
                                                                                     then (p+r, x)
                                                                                     else (p, y)) acc
                                                           else (r,x):acc) [] (runProb procRes)

-- |  TODO: What does this function? Why ends it up in an infinite loop for
-- the Coffee Machine process?
renormalize :: [a] -> Probability (StepEither (Step a) x (Process a Probability x)) -> Probability (StepEither (Step a) x (Process a Probability x))
renormalize inputs inner = let    e   = runProb $ fmap (helper inputs) inner
                                  valids = not $ null [True | (_, Right _) <- e]
                                  probAllLefts  = sum [r | (r, Left _) <- e]
                                  probAllRights = sum [r | (r, Right _) <- e]
                                  probAll = probAllRights + probAllLefts
                                  rs  = [(r, r_inner) | (r, Right r_inner) <- e]
                        in if valids
                               then Probability $ fmap (\(r,x) -> ((r+((r/probAllRights)*probAllLefts)) / probAll, x)) rs
                               else inner
                        where
                            helper :: [a] -> StepEither (Step a) x (Process a Probability x) -> Either (StepEither (Step a) x (Process a Probability x)) (StepEither (Step a) x (Process a Probability x))
                            helper _ (Done x) = Right (Done x)
                            helper [] (Resume (In f)) = Left (Resume (In f))
                            helper (y:_) (Resume (In f))
                                |  null $ runIterFT (f y) = Left (Resume (In f))
                                |  otherwise              = Right (Resume (In f))
                            helper _ (Resume (Tau p)) = case  listToMaybe (runProb $ runIterFT p) of-- runIterFT causes infinit loop for some processes
                                                            Nothing -> Left (Resume (Tau p))
                                                            _       -> Right (Resume (Tau p))
                            helper _  (Resume (Out o p)) = Right (Resume (Out o p))
