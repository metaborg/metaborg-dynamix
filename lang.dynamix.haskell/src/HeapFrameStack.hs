{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}

module HeapFrameStack where

import Data.Map.Strict
import Control.Monad.State (runStateT, StateT, get, put)
import Control.Monad.Reader (runReaderT, ReaderT, local, ask)
import Control.Monad.Except (runExcept, Except)
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


------------------------------
--- stacks and stack slots ---
------------------------------

type Stack val code slots = ([(val -> code val)], slots)


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

type HFT val code slots a = ReaderT (Frame, Stack val code slots)
                                    (StateT [HeapFrame val] (Except String)) a

getHeap :: HFT val code sslots (Heap val)
getHeap = get

putHeap :: Heap val -> HFT val code sslots ()
putHeap = put

getFrame :: Frame -> HFT val code sslots (HeapFrame val)
getFrame i = do
  h <- getHeap
  return (h !! i)

putFrame :: Frame -> HeapFrame val -> HFT val code slots ()
putFrame i hf = do
  h <- getHeap
  putHeap (update' h i hf)

setLink :: Frame -> Label -> Frame -> HFT val code slots ()
setLink f l f' = do
  (HF links slots) <- getFrame f
  putFrame f (HF (insert l f' links) slots)

getLink :: Frame -> Label -> HFT val code slots Frame
getLink f l = do
  hf <- getFrame f
  return (links hf ! l)

setValue :: Frame -> Name -> val -> HFT val code slots ()
setValue f n v = do
  (HF links slots) <- getFrame f
  putFrame f (HF links (insert n v slots))
  return ()

getValue :: Frame -> Name -> HFT val code slots val
getValue f n = do
  hf <- getFrame f
  return (slots hf ! n)

curFrame :: HFT val code slots Frame
curFrame = do
  (f , _) <- ask
  return f

withFrame :: Frame -> HFT val code slots a -> HFT val code slots a
withFrame f m = local (\ (_ , s) -> (f , s)) m

followPath :: Frame -> Path -> HFT val code slots val
followPath f (PPos n) = do
  getValue f n
followPath f (PStep l p) = do
  f' <- getLink f l
  followPath f' p

followLinks :: Frame -> [Label] -> HFT val code slots Frame
followLinks f [] = do
  return f
followLinks f (l : ls) = do
  f' <- getLink f l
  followLinks f' ls

allocFrame :: HFT val code slots Frame
allocFrame = do
  h <- getHeap
  putHeap (h ++ [HF (fromList []) (fromList [])])
  return (length h)

pushCont :: (val -> code val) -> HFT val code slots a -> HFT val code slots a
pushCont k m = local (\ (f , (s , sslots)) -> (f , (k : s , sslots))) m

localS :: (slots -> slots) -> HFT val code slots a -> HFT val code slots a
localS g m = local (\ (f , (s , sslots)) -> (f , (s , g sslots))) m

curConts :: HFT val code slots [(val -> code val)]
curConts = do
  (_ , (s , _)) <- ask
  return s

withConts :: [(val -> code val)] -> HFT val code slots a -> HFT val code slots a
withConts s m = local (\ (f , (_ , sslots)) -> (f , (s , sslots))) m

withFrameCont :: Frame -> (val -> code val) -> HFT val code slots a ->
                 HFT val code slots a
withFrameCont f k m = local (\ (_ , (ks , ss)) -> (f , (k : ks , ss))) m


-----------
--- run ---
-----------

runHFT :: HFT val code slots a -> slots -> Either String a
runHFT e ss = mapRight fst $
              runExcept (runStateT (runReaderT e (0 , ([] , ss)))
                                   [HF (fromList []) (fromList [])])
