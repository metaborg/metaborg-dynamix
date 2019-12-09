{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ExistentialQuantification #-}

module Free where

import Control.Exception
import Data.Typeable
import System.IO.Unsafe


--------------------
--- a free monad ---
--------------------

data Free c a = Stop a
              | forall b. Step (c b) (b -> Free c a)

instance Functor (Free c) where
  fmap :: (a -> b) -> Free c a -> Free c b
  fmap g (Stop a)   = Stop (g a)
  fmap g (Step c k) = Step c (fmap g . k)

instance Applicative (Free c) where
  pure :: a -> Free c a
  pure = Stop

  (<*>) :: Free c (a -> b) -> Free c a -> Free c b
  Stop g     <*> f = fmap g f
  (Step c k) <*> f = Step c (\ x -> k x <*> f)

instance Monad (Free c) where
  (>>=) :: Free c a -> (a -> Free c b) -> Free c b
  Stop a   >>= k = k a
  Step c f >>= k = Step c (\ x -> f x >>= k)

liftF :: c a -> Free c a
liftF c = Step c Stop


-------------
--- folds ---
-------------

-- monad morphism
foldF :: Monad m =>
         (forall b. c b -> m b) ->
         Free c a -> m a
foldF _ (Stop x) = return x
foldF f (Step c k) = f c >>= foldF f . k

-- deep handler
foldK :: Monad m =>
         (forall b. c b -> (b -> m a) -> m a) ->
         Free c a -> m a
foldK _ (Stop x) = return x
foldK f (Step c k) = f c (foldK f . k)

-- shallow handler
foldS :: Monad m =>
         (forall b. c b -> (b -> Free c a) -> m a) ->
         Free c a -> m a
foldS _ (Stop x) = return x
foldS f (Step c k) = f c k


----------------------
--- pretty-printer ---
----------------------

newtype FVar = FVar Int
             deriving (Typeable, Show)

instance Exception FVar

fromFree :: (forall b. Show (c b), Show a) => Int -> Free c a -> String
fromFree free xOrVar = unsafePerformIO $ do
  ex <- evaluate xOrVar
  case ex of
    Stop x -> do
      x' <- evaluate x
      return $ "(Stop " ++ show x' ++ ")"
    Step c k -> do
      c' <- evaluate c
      k'  <- evaluate k
      return $ "(Step " ++ show c' ++ " (\\ x" ++ show free ++ " -> " ++ fromFree (free + 1) (k' (throw (FVar free))) ++ "))"
  `catch` \ (FVar i) -> return $ "x" ++ show i
