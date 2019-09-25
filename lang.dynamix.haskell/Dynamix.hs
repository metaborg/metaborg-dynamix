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
  UnitV   :: Value m
  NumV    :: Int -> Value m
  FrameV  :: Frame -> Value m
  CodeV   :: m (Value m) -> Value m

instance Show (Value m) where
  show UnitV      = "unit"
  show (NumV n)   = show n
  show (FrameV f) = "#" ++ show f
  show (CodeV _)  = "<code>"
  
data Path = PStep Label Path
          | PPos Name
          deriving Show

data ControlSlot :: * -> * where
  Ret  :: ControlSlot CFrame -- return address
  ExcH :: ControlSlot CFrame -- exception handler
  DF   :: ControlSlot Frame  -- data frame

instance Show (ControlSlot a) where
  show Ret = "Ret"
  show ExcH = "ExcH"
  show DF = "DF"

data Register m :: * -> * where
  CallArg   :: Register m (Value m) -- for passing arg value info from call site context to function call
  CallRet   :: Register m (Value m) -- for passing return value from functioncall to call site context

instance Show (Register m a) where
  show CallArg = "CallArg"
  show CallRet = "CallRet"


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
          | Try Expr Expr
          | Throw


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

  call    :: CFrame -> m ()

  setcv   :: Show a => CFrame -> ControlSlot a -> a -> m ()
  getcv   :: CFrame -> ControlSlot a -> m a

  setrv   :: Show a => CFrame -> Register m a -> a -> m ()
  getrv   :: CFrame -> Register m a -> m a

  newcf   :: m (Value m) -> CFrame -> Frame -> m CFrame

  curpc   :: m (Value m)


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

returnTo :: (MonadControlFrames m,
             MonadFail m) => Value m -> CFrame -> m (Value m)
returnTo v cf = do
  setrv cf CallRet v
  call cf
  Fail.fail "Unreachable code"

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
         returnTo v retcf) -- unreachable
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
  ecf <- getcv cfc ExcH
  setcv cf ExcH ecf
  setrv cf CallArg v2
  call cf
  getrv cfc CallRet
eval (Try e1 e2) = do
  c1 <- quote (do
          v1 <- eval e1
          cf <- curcf
          rcf <- getcv cf Ret
          returnTo v1 rcf)
  c2 <- quote (do
          v2 <- eval e2
          cf <- curcf
          rcf <- getcv cf Ret
          returnTo v2 rcf)

  cf <- curcf
  df <- getcur

  exch <- getcv cf ExcH
  cf2 <- newcf c2 cf df
  setcv cf2 ExcH exch

  cf1 <- newcf c1 cf df
  setcv cf1 ExcH cf2

  call cf1
  getrv cf CallRet
eval Throw = do
  cf <- curcf
  ecf <- getcv cf ExcH
  call ecf
  Fail.fail "Unreachable"

