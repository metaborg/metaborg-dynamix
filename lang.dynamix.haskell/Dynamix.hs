{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ExistentialQuantification #-}

module Dynamix where

import Control.Monad.Fail as Fail

---------------------
--- preliminaries ---
---------------------

type Frame = Int

type CFrame = Int
 
data Label = P
           deriving Eq
           deriving Ord
           deriving Show

data Name = Pos Int
          deriving Eq
          deriving Ord
          deriving Show

data Value m where
  NumV :: Int -> Value m
  FrameV :: Frame -> Value m
  CodeV :: m (Value m) -> Value m

instance Show (Value m) where
  show (NumV n) = show n
  show (FrameV f) = "#" ++ show f
  show (CodeV _) = "<code>"
  
data Path = PStep Label Path
          | PPos Name

data ControlSlot :: * -> * where
  Ret       :: ControlSlot CFrame -- return address
  DF        :: ControlSlot Frame        -- data frame

data Register m :: * -> * where
  CallArg   :: Register m (Value m) -- for passing arg value info from call site context to function call
  CallRet   :: Register m (Value m) -- for passing return value from functioncall to call site context

  
-----------------------------------
--- object language expressions ---
-----------------------------------

data Expr = Num Int
          | Plus Expr Expr
          | Var Path
          | Let Name Expr Expr
          | If Expr Expr Expr
          | Lam Name Expr
          | App Expr Expr


-------------
--- monad ---
-------------

class Monad m => MonadPrimitive m where
  addi :: Value m -> Value m -> m (Value m)

class Monad m => MonadHeapFrames m where
  setl :: Frame -> Label -> Frame -> m ()
  setv :: Frame -> Name -> Value m -> m ()
  get  :: Path -> m (Value m)
  getv :: Frame -> Name -> m (Value m)       -- getSlot, really
  new  :: Int -> m Frame
  getl :: [Label] -> m Frame

class Monad m => MonadControlFrames m where
  quote   :: m a -> m (m a)

  jumpz   :: Value m -> m (Value m) -> m (Value m) -> m (Value m)
  
  curcf   :: m CFrame
--  mkcurcf :: CFrame -> m ()

  call    :: CFrame -> m ()

  setcv   :: CFrame -> ControlSlot a -> a -> m ()
  getcv   :: CFrame -> ControlSlot a -> m a

  setrv   :: CFrame -> Register m a -> a -> m ()
  getrv   :: CFrame -> Register m a -> m a

  newcf   :: m (Value m) -> CFrame -> Frame -> m CFrame


------------------
--- shorthands ---
------------------

getcur :: MonadControlFrames m => m Frame
getcur = do
  cf <- curcf
  getcv cf DF

mkcur :: MonadControlFrames m => Frame -> m ()
mkcur f = do
  cf <- curcf
  setcv cf DF f


-------------------
--- interpreter ---
-------------------

eval :: (MonadPrimitive m,
         MonadHeapFrames m,
         MonadControlFrames m,
         MonadFail m) =>
        Expr -> m (Value m)
eval (Num n) = do
  return (NumV n)
eval (Plus e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  addi v1 v2
eval (Var x) = do
  get x
eval (Let x e1 e2) = do
  v1 <- eval e1
  f <- new 1
  fcur <- getcur
  setl f P fcur
  setv f x v1
  v2 <- eval e2
  mkcur fcur
  return v2
eval (If e1 e2 e3) = do
  v1 <- eval e1
  c2 <- quote (eval e2)
  c3 <- quote (eval e3)
  jumpz v1 c2 c3
eval (Lam x e) = do
  c <- quote (do
         f     <- new 1
         cf    <- curcf
         pf    <- getcur
         argv  <- getrv cf CallArg
         setl f P pf
         setv f x argv
         mkcur f
         v     <- eval e
         retcf <- getcv cf Ret
         setrv retcf CallRet v
         call retcf
         Fail.fail "Unreachable code") -- unreachable
  clos <- new 2
  setv clos (Pos 0) (CodeV c)
  df <- getcur
  setv clos (Pos 1) (FrameV df)
  return (FrameV clos)
eval (App e1 e2) = do
  FrameV clos <- eval e1
  v2 <- eval e2
  CodeV instrs <- getv clos (Pos 0)
  FrameV pf <- getv clos (Pos 1)
  cfc <- curcf
  cf <- newcf instrs cfc pf
  setrv cf CallArg v2
  call cf
  getrv cfc CallRet





