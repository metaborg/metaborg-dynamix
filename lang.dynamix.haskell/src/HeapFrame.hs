{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}

module HeapFrame where

import Data.Map.Strict
import Control.Monad.State (StateT, get, put, runStateT)
import Control.Monad.Reader (ReaderT, local, ask, runReaderT)
import Control.Monad.Except (Except, runExcept)
import Data.Either.HT (mapRight)


------------------------
--- heaps and frames ---
------------------------

type Heap val = [HeapFrame val]

data HeapFrame val = HF (Map Label Frame) (Map Name val)

links :: HeapFrame val -> Map Label Frame
links (HF links _) = links

slots :: HeapFrame val -> Map Name val
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


------------------------
--- heap/frame monad ---
------------------------

type HFT val a = ReaderT Frame (StateT [HeapFrame val] (Except String)) a

getHeap :: HFT val (Heap val)
getHeap = get

putHeap :: Heap val -> HFT val ()
putHeap = put

getFrame :: Frame -> HFT val (HeapFrame val)
getFrame i = do
  h <- getHeap
  return (h !! i)

putFrame :: Frame -> HeapFrame val -> HFT val ()
putFrame i hf = do
  h <- getHeap
  putHeap (update' h i hf)

setLink :: Frame -> Label -> Frame -> HFT val ()
setLink f l f' = do
  (HF links slots) <- getFrame f
  putFrame f (HF (insert l f' links) slots)

getLink :: Frame -> Label -> HFT val Frame
getLink f l = do
  hf <- getFrame f
  return (links hf ! l)

setValue :: Frame -> Name -> val -> HFT val ()
setValue f n v = do
  (HF links slots) <- getFrame f
  putFrame f (HF links (insert n v slots))
  return ()

getValue :: Frame -> Name -> HFT val val
getValue f n = do
  hf <- getFrame f
  return (slots hf ! n)

curFrame :: HFT val Frame
curFrame = ask

withFrame :: Frame -> HFT val a -> HFT val a
withFrame f m = local (\_ -> f) m

followPath :: Frame -> Path -> HFT val val
followPath f (PPos n) = do
  getValue f n
followPath f (PStep l p) = do
  f' <- getLink f l
  followPath f' p

followLinks :: Frame -> [Label] -> HFT val Frame
followLinks f [] = do
  return f
followLinks f (l : ls) = do
  f' <- getLink f l
  followLinks f' ls

allocFrame :: HFT val Frame
allocFrame = do
  h <- getHeap
  putHeap (h ++ [HF (fromList []) (fromList [])])
  return (length h)


-----------
--- run ---
-----------

runHFT :: HFT val a -> Either String a
runHFT e = mapRight fst $
           runExcept (runStateT (runReaderT e 0)
                                [HF (fromList []) (fromList [])])
