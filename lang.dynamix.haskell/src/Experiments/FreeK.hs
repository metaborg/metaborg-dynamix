{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ExistentialQuantification #-}

module FreeK where

import Control.Exception
import Data.Typeable
import System.IO.Unsafe


--------------------
--- a free monad ---
--------------------

data Free cmd bch a = Stop a
                    | forall b. Step (cmd b) (b -> Free cmd bch a)
                    | forall f. Functor f => Branch (bch f) (f (Free cmd bch a))

instance Functor (Free cmd bch) where
  fmap :: (a -> b) -> Free cmd bch a -> Free cmd bch b
  fmap g (Stop a)      = Stop (g a)
  fmap g (Step c k)    = Step c (fmap g . k)
  fmap g (Branch b fs) = Branch b (fmap (fmap g) fs)

instance Applicative (Free cmd bch) where
  pure :: a -> Free cmd bch a
  pure = Stop

  (<*>) :: Free cmd bch (a -> b) -> Free cmd bch a -> Free cmd bch b
  Stop g        <*> f = fmap g f
  (Step c k)    <*> f = Step c (\ x -> k x <*> f)
  (Branch b fs) <*> f = Branch b (fmap (\ k -> k <*> f) fs)

instance Monad (Free cmd bch) where
  (>>=) :: Free cmd bch a -> (a -> Free cmd bch b) -> Free cmd bch b
  Stop a      >>= k = k a
  Step c f    >>= k = Step c (\ x -> f x >>= k)
  Branch b fs >>= k = Branch b (fmap (\ m -> m >>= k) fs)

liftF :: cmd a -> Free cmd bch a
liftF c = Step c Stop


------------
--- fold ---
------------

-- monad morphism
foldF :: Monad m =>
         (forall b. cmd b -> m b) ->
         (forall f. Functor f => bch f -> f (m a) -> m a) ->
         Free cmd bch a -> m a
foldF _  _  (Stop x) = return x
foldF fc fb (Step c k) = fc c >>= foldF fc fb . k
foldF fc fb (Branch b fs) = fb b (fmap (foldF fc fb) fs)


-- ----------------------
-- --- pretty-printer ---
-- ----------------------

-- newtype FVar = FVar Int
--              deriving (Typeable, Show)

-- instance Exception FVar

-- fromFree :: (forall b. Show (c b), Show a) => Int -> Free c a -> String
-- fromFree free xOrVar = unsafePerformIO $ do
--   ex <- evaluate xOrVar
--   case ex of
--     Stop x -> do
--       x' <- evaluate x
--       return $ "(Stop " ++ show x' ++ ")"
--     Step c k -> do
--       c' <- evaluate c
--       k'  <- evaluate k
--       return $ "(Step " ++ show c' ++ " (\\ x" ++ show free ++ " -> " ++ fromFree (free + 1) (k' (throw (FVar free))) ++ "))"
--   `catch` \ (FVar i) -> return $ "x" ++ show i
