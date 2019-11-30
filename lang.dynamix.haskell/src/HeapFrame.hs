{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}

module HeapFrame where

import Data.Map.Strict
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader


------------------------
--- heaps and frames ---
------------------------

type Heap val m = [HeapFrame val m]

data HeapFrame :: ((* -> *) -> *) -> (* -> *) -> * where
  HF :: (Map Label Frame) -> Map Name (val m) -> HeapFrame val m

links :: HeapFrame val m -> Map Label Frame
links (HF links _) = links

slots :: HeapFrame val m -> Map Name (val m)
slots (HF _ slots) = slots

type Frame = Int


----------------------------
--- paths, labels, names ---
----------------------------

data Path = PStep Label Path
          | PPos Name
          deriving Show
          deriving Eq

data Label = P
           deriving Eq
           deriving Ord
           deriving Show


-- names are slot positions

type Name = Int


-----------
--- aux ---
-----------

update' :: [a] -> Int -> a -> [a]
update' []       i x = error $ "bad update at " ++ show i
update' (_ : xs) 0 x = x : xs
update' (x : xs) i y = x : update' xs (i - 1) y


------------------------------------
--- heap/frame monad transformer ---
------------------------------------

type HFT val m a = ReaderT Frame (StateT [HeapFrame val m] Identity) a

getHeap :: Monad m => HFT val m (Heap val m)
getHeap = get

putHeap :: Monad m => Heap val m -> HFT val m ()
putHeap = put

getFrame :: Monad m => Frame -> HFT val m (HeapFrame val m)
getFrame i = do
  h <- getHeap
  return (h !! i)

putFrame :: Monad m => Frame -> HeapFrame val m -> HFT val m ()
putFrame i hf = do
  h <- getHeap
  putHeap (update' h i hf)

setLink :: Monad m => Frame -> Label -> Frame -> HFT val m ()
setLink f l f' = do
  (HF links slots) <- getFrame f
  putFrame f (HF (insert l f' links) slots)

getLink :: Monad m => Frame -> Label -> HFT val m Frame
getLink f l = do
  hf <- getFrame f
  return (links hf ! l)

setValue :: Monad m => Frame -> Name -> val m -> HFT val m ()
setValue f n v = do
  (HF links slots) <- getFrame f
  putFrame f (HF links (insert n v slots))
  return ()

getValue :: Monad m => Frame -> Name -> HFT val m (val m)
getValue f n = do
  hf <- getFrame f
  return (slots hf ! n)

curFrame :: Monad m => HFT val m Frame
curFrame = ask

withFrame :: Monad m => Frame -> HFT val m a -> HFT val m a
withFrame f m = local (\_ -> f) m

followPath :: Monad m => Frame -> Path -> HFT val m (val m)
followPath f (PPos n) = do
  getValue f n
followPath f (PStep l p) = do
  f' <- getLink f l
  followPath f' p

followLinks :: Monad m => Frame -> [Label] -> HFT val m Frame
followLinks f [] = do
  return f
followLinks f (l : ls) = do
  f' <- getLink f l
  followLinks f' ls

allocFrame :: Monad m => HFT val m Frame
allocFrame = do
  h <- getHeap
  putHeap (h ++ [HF (fromList []) (fromList [])])
  return (length h)

