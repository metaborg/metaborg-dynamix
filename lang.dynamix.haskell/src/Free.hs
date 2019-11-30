{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wall #-}


--------------------
--- a free monad ---
--------------------

module Free where

data Free c a = Stop a
              | forall b. Step (c b) (b -> Free c a)

instance Show (Free c a) where
  show (Step _ _) = "step"
  show (Stop _)   = "stop"

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


