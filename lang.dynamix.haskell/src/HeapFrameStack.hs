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


------------------------------
--- stacks and stack slots ---
------------------------------

type Stack val m sslots = ([(val m -> m (val m))], sslots)


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

type HFT val m sslots a = ReaderT (Frame, Stack val m sslots)
                                  (StateT [HeapFrame val m] (Except String)) a

getHeap :: Monad m => HFT val m sslots (Heap val m)
getHeap = get

putHeap :: Monad m => Heap val m -> HFT val m sslots ()
putHeap = put

getFrame :: Monad m => Frame -> HFT val m sslots (HeapFrame val m)
getFrame i = do
  h <- getHeap
  return (h !! i)

putFrame :: Monad m => Frame -> HeapFrame val m -> HFT val m sslots ()
putFrame i hf = do
  h <- getHeap
  putHeap (update' h i hf)

setLink :: Monad m => Frame -> Label -> Frame -> HFT val m sslots ()
setLink f l f' = do
  (HF links slots) <- getFrame f
  putFrame f (HF (insert l f' links) slots)

getLink :: Monad m => Frame -> Label -> HFT val m sslots Frame
getLink f l = do
  hf <- getFrame f
  return (links hf ! l)

setValue :: Monad m => Frame -> Name -> val m -> HFT val m sslots ()
setValue f n v = do
  (HF links slots) <- getFrame f
  putFrame f (HF links (insert n v slots))
  return ()

getValue :: Monad m => Frame -> Name -> HFT val m sslots (val m)
getValue f n = do
  hf <- getFrame f
  return (slots hf ! n)

curFrame :: Monad m => HFT val m sslots Frame
curFrame = do
  (f , _) <- ask
  return f

withFrame :: Monad m => Frame -> HFT val m sslots a -> HFT val m sslots a
withFrame f m = local (\ (_ , s) -> (f , s)) m

followPath :: Monad m => Frame -> Path -> HFT val m sslots (val m)
followPath f (PPos n) = do
  getValue f n
followPath f (PStep l p) = do
  f' <- getLink f l
  followPath f' p

followLinks :: Monad m => Frame -> [Label] -> HFT val m sslots Frame
followLinks f [] = do
  return f
followLinks f (l : ls) = do
  f' <- getLink f l
  followLinks f' ls

allocFrame :: Monad m => HFT val m sslots Frame
allocFrame = do
  h <- getHeap
  putHeap (h ++ [HF (fromList []) (fromList [])])
  return (length h)

pushCont :: Monad m => (val m -> m (val m)) -> HFT val m sslots a -> HFT val m sslots a
pushCont k m = local (\ (f , (s , sslots)) -> (f , (k : s , sslots))) m

localS :: Monad m => (sslots -> sslots) -> HFT val m sslots a -> HFT val m sslots a
localS g m = local (\ (f , (s , sslots)) -> (f , (s , g sslots))) m

curConts :: Monad m => HFT val m sslots [(val m -> m (val m))]
curConts = do
  (_ , (s , _)) <- ask
  return s

withConts :: Monad m =>
             [(val m -> m (val m))] -> HFT val m sslots a -> HFT val m sslots a
withConts s m = local (\ (f , (_ , sslots)) -> (f , (s , sslots))) m

withFrameCont :: Monad m =>
                 Frame -> (val m -> m (val m)) -> HFT val m sslots a ->
                 HFT val m sslots a
withFrameCont f k m = local (\ (_ , (ks , ss)) -> (f , (k : ks , ss))) m


-----------
--- run ---
-----------

runHFT :: HFT val m sslots a -> sslots -> Either String a
runHFT e ss = mapRight fst $
              runExcept (runStateT (runReaderT e (0 , ([] , ss)))
                                   [HF (fromList []) (fromList [])])
