{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}

module Dynamix where

import Debug.Trace

import Test.HUnit hiding (Path)
import Control.Monad.Fail
import Free
import HeapFrameStack
import Control.Monad.Except (throwError)
import Control.Monad.Reader (local, ask)


---------------------------------------
--- meta-language commands and code ---
---------------------------------------

type Code val = Free (Cmd val)

type Cont val = (Point , val -> Code val val)

data Cmd val :: * -> * where
  -- heap frame fragment
  SetL  :: Frame -> Label -> Frame -> Cmd val ()
  SetV  :: Frame -> Name -> val -> Cmd val ()
  Get   :: Path -> Cmd val val
  GetV  :: Frame -> Name -> Cmd val val
  New   :: Cmd val Frame
  CurF  :: Cmd val Frame
  WithF :: Frame -> Code val val -> Cmd val val

  -- control fragment
  Mark  :: (Cont val -> Code val val) -> Cmd val val
  Invk  :: Cont val -> val -> Cmd val val

  -- failure fragment
  Err   :: String -> Cmd val a

instance MonadFail (Free (Cmd val)) where
  fail = liftF . Err

instance (Show val) => Show (Cmd val a) where
  show (SetL f l f') = "(SetL " ++ show f ++ " " ++ show l ++ " " ++ show f' ++ ")"
  show (SetV f n v) = "(SetV " ++ show f ++ " " ++ show n ++ " " ++ show v ++ ")"
  show (Get p) = "(Get " ++ show p ++ ")"
  show (GetV f n) = "(GetV " ++ show f ++ " " ++ show n ++ ")"
  show New = "New"
  show CurF = "CurF"
  show (WithF f c) = "(WithF " ++ show f ++ " " ++ fromFree 0 c ++ ")"
  show (Mark f) = "(Mark <...>)"
  show (Invk k v) = "(Invk <...> <...>)"
  show (Err s) = "(Err " ++ s ++ ")"

instance (Show a, Show val) => Show (Code val a) where
  show x = fromFree 0 x


----------------------------
--- boilerplate liftings ---
----------------------------

setl :: Frame -> Label -> Frame -> Code val ()
setl f l f' = liftF (SetL f l f')

setv :: Frame -> Name -> val -> Code val ()
setv f n v = liftF (SetV f n v)

get :: Path -> Code val val
get = liftF . Get

getv :: Frame -> Name -> Code val val
getv f n = liftF (GetV f n)

new :: Code val Frame
new = liftF New

curf :: Code val Frame
curf = liftF CurF

withf :: Frame -> Code val val -> Code val val
withf f c = liftF (WithF f c)

err :: String -> Code val a
err = liftF . Err

mark :: (Cont val -> Code val val) -> Code val val
mark = liftF . Mark

invk :: Cont val -> val -> Code val val
invk κ v = liftF (Invk κ v)


---------------------------------
--- meta-language interpreter ---
---------------------------------

type M val slots a = HFT val (Code val) slots a

handler :: Cmd val a -> (a -> Code val val) -> M val slots val
handler (SetL f l f') k = do
  setLink f l f'
  handle (k ())
handler (SetV f n v) k = do
  setValue f n v
  handle (k ())
handler (Get p) k = do
  f <- curFrame
  v <- followPath f p
  handle (k v)
handler (GetV f n) k = do
  v <- getValue f n
  handle (k v)
handler New k = do
  f <- allocFrame
  handle (k f)
handler CurF k = do
  f <- curFrame
  handle (k f)
handler (WithF f c) k = do
  sls <- curSlots
  p <- pushStack f k sls
  local (\ _ -> p) (handle c)
handler (Err m) _ =
  throwError m
handler (Mark f) k = do
  p <- curPoint
  handle (do v <- f (p , k); k v)
handler (Invk (p , k) v) _ = do
  local (\ _ -> p) (handle (k v))


handle :: Code val val -> M val slots val
handle (Stop x) = do
  p <- curPoint
  s <- getStack
  case lns (s !! p) of
    [] -> return x
    (p' : _) -> do
      local (\ _ -> p') (handle (knt (s !! p) x))
handle (Step x k) = handler x k


-----------
--- run ---
-----------

runM :: M val slots val -> slots -> Either String val
runM m sls = runHFT m Stop sls
