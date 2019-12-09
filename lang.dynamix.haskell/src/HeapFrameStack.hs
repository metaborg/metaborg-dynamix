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

data HeapFrame val = HF { links :: (Map Label Frame)
                        , slots :: (Map Name val) }

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


--------------
--- stacks ---
--------------

data StackFrame val code marks = SF { frame :: Frame
                                    , knt :: val -> code val
                                    , coupling :: Maybe Point
                                    , marks :: marks
                                    }

type Stack val code marks = [StackFrame val code marks]

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

type HFT val code marks =
  StateT (Heap val, Stack val code marks, Point) (Except String)

instance {-# OVERLAPPING #-} MonadFail (HFT val code marks) where
  fail = throwError


-----------------------------
--- heap/frame operations ---
-----------------------------

getHeap :: HFT val code smarks (Heap val)
getHeap = do
  (h , _, _) <- get
  return h

modifyHeap :: (Heap val -> Heap val) -> HFT val code smarks ()
modifyHeap g = do
  modify (\ (h , s, p) -> (g h , s, p))

getFrame :: Frame -> HFT val code smarks (HeapFrame val)
getFrame i = do
  h <- getHeap
  return (h !! i)

putFrame :: Frame -> HeapFrame val -> HFT val code marks ()
putFrame i hf = do
  modifyHeap (\ h -> update' h i hf)

setLink :: Frame -> Label -> Frame -> HFT val code marks ()
setLink f l f' = do
  (HF links marks) <- getFrame f
  putFrame f (HF (insert l f' links) marks)

getLink :: Frame -> Label -> HFT val code marks Frame
getLink f l = do
  hf <- getFrame f
  return (links hf ! l)

setValue :: Frame -> Name -> val -> HFT val code marks ()
setValue f n v = do
  (HF links marks) <- getFrame f
  putFrame f (HF links (insert n v marks))
  return ()

getValue :: Frame -> Name -> HFT val code marks val
getValue f n = do
  hf <- getFrame f
  return (slots hf ! n)

followPath :: Frame -> Path -> HFT val code marks val
followPath f (PPos n) = do
  getValue f n
followPath f (PStep l p) = do
  f' <- getLink f l
  followPath f' p

followLinks :: Frame -> [Label] -> HFT val code marks Frame
followLinks f [] = do
  return f
followLinks f (l : ls) = do
  f' <- getLink f l
  followLinks f' ls

allocFrame :: HFT val code marks Frame
allocFrame = do
  h <- getHeap
  modifyHeap (\ h -> h ++ [HF (fromList []) (fromList [])])
  return (length h)


------------------------
--- stack operations ---
------------------------

curPoint :: HFT val code marks Point
curPoint = do
  (_ , _ , p) <- get
  return p

getStack :: HFT val code marks (Stack val code marks)
getStack = do
  (_ , s, _) <- get
  return s

getStackFrame :: Point -> HFT val code marks (StackFrame val code marks)
getStackFrame p = do
  s <- getStack
  return (s !! p)

modifyStack :: (Stack val code marks -> Stack val code marks) ->
               HFT val code marks ()
modifyStack g =
  modify (\ (h , s , p) -> (h , g s , p))

pushStack :: Frame -> (val -> code val) -> marks -> HFT val code marks Point
pushStack f k mrks = do
  p <- curPoint
  s <- getStack
  modifyStack (\ s -> s ++ [SF f k (Just p) mrks])
  return (length s)

allocStack :: Frame -> (val -> code val) -> Maybe Point -> marks -> HFT val code marks Point
allocStack f k p mrks = do
  s <- getStack
  modifyStack (\ s -> s ++ [SF f k p mrks])
  return (length s)

curFrame :: HFT val code marks Frame
curFrame = do
  p <- curPoint
  sf <- getStackFrame p
  return (frame sf)

curMarks :: HFT val code marks marks
curMarks = do
  p <- curPoint
  s <- getStack
  return (marks (s !! p))

curCoupling :: HFT val code marks (Maybe Point)
curCoupling = do
  p <- curPoint
  s <- getStack
  return (coupling (s !! p))

setPoint :: Point -> HFT val code marks ()
setPoint p =
  modify (\ (h , s , _) -> (h , s , p))

foldLinksUntil :: Point -> b ->
                  (marks -> Bool) ->
                  (Point -> b -> HFT val code marks b) ->
                  HFT val code marks b
foldLinksUntil p b c f = do
  s <- getStack
  let sf = s !! p
  case coupling sf of
    Just p' ->
      if (c (marks sf))
      then f p' b
      else do
        x <- foldLinksUntil p' b c f
        f p x
    Nothing ->
      f p b
    
copyAndLink :: Point -> Point ->
               HFT val code marks Point
copyAndLink p cpl = do
  sf <- getStackFrame p
  s <- getStack
  modifyStack (\ s -> s ++ [sf { coupling = Just cpl }])
  return (length s)

-----------
--- run ---
-----------

runHFT :: HFT val code marks a -> (val -> code val) -> marks -> Either String a
runHFT e ctx ss = mapRight fst $
                  runExcept (runStateT e
                                       ([HF (fromList []) (fromList [])],
                                        [SF 0 ctx Nothing ss],
                                        0))
