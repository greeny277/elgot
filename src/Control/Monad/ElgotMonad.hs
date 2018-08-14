{-#  LANGUAGE FlexibleInstances  #-}
{-#  LANGUAGE FunctionalDependencies #-}
{-#  LANGUAGE MultiParamTypeClasses #-}
{-#  LANGUAGE Rank2Types #-}
{-#  LANGUAGE StandaloneDeriving #-}
{-#  LANGUAGE UndecidableInstances  #-}

{-|
Module      : Control.Monad.ElgotMonad
Description : A module for iterative computations in a monadic context.
Copyright   : (c) Christian Bay, 2017
License     : BSD-3
Maintainer  : christian.bay@fau.de
Stability   : experimental

This module defines a monad-class for iterative computations in two variants. One without
any restrictions and the other one which requires equality.

-}
module Control.Monad.ElgotMonad (
                  ElgotMonad(..),
                  ElgotMonadEq(..),
                  TossMonad(..),
                  IterFT(..),
                  StepEither(..),
                  resume,
                  done,
                  out,
                  tuo,
                  hoistIterFT,
                  transIterF,
                  transIterT,
                  cutOff,
                  ) where

import Control.Applicative
import Control.Monad hiding (guard)
import Control.Monad.Except hiding (guard)
import Control.Monad.Free.Class
import Control.Monad.Reader hiding (guard)
import Control.Monad.State hiding (guard)
import Data.Bifunctor

-- | Class for iterative monadic computations.
class Monad m => ElgotMonad m where
       -- | Default implementation as the least fixpoint.
       iteration ::  (a -> m (Either b a)) -> a -> m b
       iteration f a = f a >>= either return (iteration f)

       -- | Divergent computation which must be overloaded.
       nil :: a -> m b
       nil = iteration $ return . Right

instance ElgotMonad Maybe where
       nil _ = Nothing

instance ElgotMonad [] where
       nil _ = []

-- | A subclass of @'ElgotMonad'@ which has an @'Eq'@ constraint in the argument which is applied to the iterative function.
-- This constraint allows to check if same arguments are recurring and therefore prevent infinite iterations if fixpoints
-- are found.
class ElgotMonad m => ElgotMonadEq m where
       iterationEq :: Eq a => (a -> m (Either b a)) -> a -> m b
       iterationEq f a = f a >>= either return (iterationEq f)

-- | A class which can be used to formalize non-determination in a monadic
-- computation.
class TossMonad a m | m -> a where
        -- | Perform a computation which returns a boolean value for any
        -- value of type @a@.
        toss :: a -> m Bool

instance TossMonad () [] where
        toss _ = [True, False]

-- | A structure which spans an monadic computation tree. Leafs are values of type
-- type @a@. The subtrees are applied to the functor @f@. @'IterFT'@ ~ @'FreeT'@ (see http://hackage.haskell.org/package/free-4.12.4/docs/Control-Monad-Trans-Free.html).
newtype IterFT f m a = IterFT {
                       runIterFT ::  m (StepEither f a (IterFT f m a))
                       }

-- | A bifunctor which either returns an instance of type @a@ or applies the functor to some instance of type @b@.
data StepEither f a b = Done a | Resume (f b)

instance (ElgotMonad m, Functor f) => ElgotMonad (IterFT f m) where
       iteration f = iteration' (guard f)
                     where iteration' :: ElgotMonad m => (a -> m (Either b a)) -> a -> m b
                           iteration' g a = g a >>= either return (iteration g)
       nil x = IterFT (nil x)

instance (Functor f, ElgotMonadEq m) => ElgotMonadEq (IterFT f m) where
       iterationEq f = iteration' (guardEq f)
                     where iteration' :: (ElgotMonadEq m, Eq a) => (a -> m (Either b a)) -> a -> m b
                           iteration' g a = g a >>= either return (iterationEq g)

instance (TossMonad a m, ElgotMonad m) => TossMonad a (IterFT f m) where
        toss x = IterFT $ fmap Done (toss x)

guard :: ElgotMonad m => (a -> IterFT f m (Either b a)) -> a -> IterFT f m (Either b a)
guard f x = tuo $ do z <- iteration (w f) x
                     case z of
                         Left l  -> return . Left . Left $ l
                         Right r -> return . Right $ r

guardEq :: (ElgotMonadEq m, Eq a) => (a -> IterFT f m (Either b a)) -> a -> IterFT f m (Either b a)
guardEq f x = tuo $ do z <- iterationEq (w f) x
                       case z of
                           Left l  -> return . Left . Left $ l
                           Right r -> return . Right $ r

w :: ElgotMonad m => (a -> IterFT f m (Either b a)) -> a -> m (Either (Either b (f (IterFT f m (Either b a)))) a)
w h = fmap (either (either (Left . Left) Right) (Left . Right)) . out . h

deriving instance Eq (m (StepEither f a (IterFT f m a))) => Eq (IterFT f m a)
deriving instance (Eq (f (IterFT f m a)), Eq a) => Eq (StepEither f a (IterFT f m a))

deriving instance Ord (m (StepEither f a (IterFT f m a))) => Ord (IterFT f m a)
deriving instance (Ord (f (IterFT f m a)), Ord a) => Ord (StepEither f a (IterFT f m a))

deriving instance Show (m (StepEither f a (IterFT f m a))) => Show (IterFT f m a)
deriving instance (Show (f (IterFT f m a)), Show a) => Show (StepEither f a (IterFT f m a))

deriving instance Read (m (StepEither f a (IterFT f m a))) => Read (IterFT f m a)
deriving instance (Read (f (IterFT f m a)), Read a) => Read (StepEither f a (IterFT f m a))

instance (Functor f, Monad m) => Functor (IterFT f m) where
        fmap f (IterFT c) = IterFT (fmap f' c) where
            f' (Done a) =    Done (f a)
            f' (Resume as) = Resume  (fmap (fmap f) as)

instance (Monad m, Functor f) => Applicative (IterFT f m) where
        pure = IterFT . return . Done
        (<*>) = ap

instance (Monad m, Functor f) => Monad (IterFT f m) where
        return a = IterFT (return (Done a))
        c >>= k = IterFT (runIterFT c >>= \x -> case x of Done result -> runIterFT (k result); Resume r -> (return . Resume . fmap (>>= k)) r)

instance (Monad m, Functor f, MonadPlus m) => Alternative (IterFT f m) where
        empty = mzero
        (<|>) = mplus

instance (Monad m, MonadPlus m, Functor f) => MonadPlus (IterFT f m) where
        mzero = IterFT mzero
        a `mplus` b = IterFT $ runIterFT a `mplus` runIterFT b

instance MonadTrans (IterFT f) where
        lift = IterFT . fmap Done

instance (ElgotMonad m, Functor f) => MonadFree f (IterFT f m) where
    wrap = IterFT . return . Resume

instance (ElgotMonad m, Functor f, Applicative f, Monoid a, Semigroup (IterFT f m a)) => Monoid (IterFT f m a) where
    mempty = return mempty
    x `mappend` y = IterFT $ do
            x' <- runIterFT x
            y' <- runIterFT y
            case (x', y') of
              ( Done a, Done b)  -> return . Done  $ a `mappend` b
              ( Done a, Resume b) -> return . Resume $ fmap (fmap (a `mappend`)) b
              ( Resume a, Done b) -> return . Resume $ fmap (fmap (`mappend` b)) a
              ( Resume a, Resume b) -> return . Resume $ fmap mappend a <*> b

instance (Functor f, MonadIO m) => MonadIO (IterFT f m) where
    liftIO = lift . liftIO

instance (Functor f, MonadError e m) => MonadError e (IterFT f m) where
    throwError = lift . throwError
    --IterFT m `catchError` f  = undefined
    p `catchError` f  = (IterFT $ do
        x <- runIterFT p
        case x of
            Done a -> return (Done a)
            Resume b -> return . Resume $ fmap (`catchError` f) b
            ) `catchError` f -- TODO Is the unfolding of f necessary?

instance (MonadState s m, ElgotMonad m, Functor f) => MonadState s (IterFT f m) where
    get = lift get
    {-# INLINE get #-}
    put s = lift (put s)
    {-# INLINE put #-}

instance (MonadReader r m, ElgotMonad m, Functor f) => MonadReader r (IterFT f m) where
    ask = lift ask
    {-# INLINE ask #-}
    local f = hoistIterFT (local f)
    {-# INLINE local #-}

instance Functor f => Functor (StepEither f a) where
        fmap _ (Done a) = Done a
        fmap f (Resume as) = Resume (fmap f as)

instance Functor f => Bifunctor (StepEither f) where
        bimap f _ (Done x) = Done $ f x
        bimap _ g (Resume xs) = Resume (fmap g xs)

-- | Performs the first step of an iterative computation
out :: (Monad m) => IterFT f m a -> m (Either a (f (IterFT f m a)))
out r = runIterFT r >>= \x -> case x of
                                   Done b   -> return (Left b)
                                   Resume a -> return (Right a)

-- | Build an iterative computation from one first step
tuo :: (Monad m) => m (Either a (f (IterFT f m a))) -> IterFT f m a
tuo r = IterFT $ r >>= either (return . Done) (return . Resume)

-- | Lift any value in a way that an iterative computation will resume.
resume :: Monad m => b -> m (Either a b)
resume b = return $ Right b

-- | Lift any value in a way that an iterative computation will be finished.
done :: Monad m => a -> m (Either a b)
done a = return $ Left a

-- | Lift a monad homomorphism from @m@ to @n@ into a Monad homomorphism from @'IterFT' f m@ to @'IterFT' f n@.
hoistIterFT :: (ElgotMonad m, ElgotMonad n, Functor f) => (forall a . m a -> n a) -> IterFT f m b -> IterFT f n b
hoistIterFT f (IterFT as) = IterFT $ do
       x <- f as
       case x of
           Done a   -> return $ Done a
           Resume b -> return $ Resume (fmap (hoistIterFT f) b)

-- | Apply a natural transformation the coinductive generalized
-- resumption transformer.
transIterT :: (Monad m, Functor g) => (forall a. f a -> g a) -> IterFT f m b -> IterFT g m b
transIterT nat (IterFT inner) = IterFT $ fmap (fmap (transIterT nat) . transIterF nat) inner

transIterF :: (forall c. f c -> g c) -> StepEither f a b -> StepEither g a b
transIterF _ (Done x) = Done x
transIterF nat (Resume y) = Resume (nat y)

-- | Stop computation after 'n' steps.
cutOff :: (ElgotMonad m, Functor f) => Integer -> IterFT f m a -> IterFT f m (Maybe a)
cutOff n (IterFT m) | n <= 0    = return Nothing
                    | otherwise = IterFT $ fmap (bimap Just (cutOff (n-1))) m
