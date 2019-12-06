{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}

module HeapFrameStack where

import Data.Map.Strict
import Control.Monad.State (runStateT, StateT, get, modify)
import Control.Monad.Reader (runReaderT, ReaderT, local, ask)
import Control.Monad.Except (runExcept, Except, throwError)
import Control.Monad.Fail (MonadFail, fail)
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

data StackFrame val code slots = SF { frm :: Frame
                                    , knt :: val -> code val
                                    , lns :: [Point]
                                    , sls :: slots
                                    }

type Stack val code slots = [StackFrame val code slots]

type Point = Int


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

type HFT val code slots =
  ReaderT Point (StateT (Heap val, Stack val code slots) (Except String))

instance {-# OVERLAPPING #-} MonadFail (HFT val code slots) where
  fail = throwError


-----------------------------
--- heap/frame operations ---
-----------------------------

getHeap :: HFT val code sslots (Heap val)
getHeap = do
  (h , _) <- get
  return h

modifyHeap :: (Heap val -> Heap val) -> HFT val code sslots ()
modifyHeap g = do
  modify (\ (h , s) -> (g h , s))

getFrame :: Frame -> HFT val code sslots (HeapFrame val)
getFrame i = do
  h <- getHeap
  return (h !! i)

putFrame :: Frame -> HeapFrame val -> HFT val code slots ()
putFrame i hf = do
  modifyHeap (\ h -> update' h i hf)

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
  modifyHeap (\ h -> h ++ [HF (fromList []) (fromList [])])
  return (length h)


------------------------
--- stack operations ---
------------------------

curPoint :: HFT val code slots Point
curPoint = ask

getStack :: HFT val code slots (Stack val code slots)
getStack = do
  (_ , s) <- get
  return s

modifyStack :: (Stack val code slots -> Stack val code slots) ->
               HFT val code slots ()
modifyStack g =
  modify (\ (h , s) -> (h , g s))

pushStack :: Frame -> (val -> code val) -> slots -> HFT val code slots Point
pushStack f k sls = do
  p <- curPoint
  s <- getStack
  modifyStack (\ s -> s ++ [SF f k [p] sls])
  return (length s)

curFrame :: HFT val code slots Frame
curFrame = do
  p <- curPoint
  s <- getStack
  return (frm (s !! p))

curSlots :: HFT val code slots slots
curSlots = do
  p <- curPoint
  s <- getStack
  return (sls (s !! p))



-----------
--- run ---
-----------

runHFT :: HFT val code slots a -> (val -> code val) -> slots -> Either String a
runHFT e ctx ss = mapRight fst $
                  runExcept (runStateT (runReaderT e 0)
                                       ([HF (fromList []) (fromList [])],
                                        [SF 0 ctx [] ss]))
