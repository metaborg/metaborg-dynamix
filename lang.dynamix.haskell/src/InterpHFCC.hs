{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}

module InterpHFCC where

import Debug.Trace

import Test.HUnit hiding (Path)
import Data.Map.Strict
import Control.Monad.Identity (runIdentity)
import Control.Monad.Reader (runReaderT)
import Control.Monad.State (runStateT)
import Control.Monad.Fail
import Free
import HeapFrame


------------------------------
--- object language syntax ---
------------------------------

data Expr = Num Int | Fun Expr | App Expr Expr | Var Path
          | CallCC Expr
          deriving Show
          deriving Eq

-- syntactic sugar

lete :: Expr -> Expr -> Expr
lete e body = App (Fun body) e


------------------------------
--- object language values ---
------------------------------

data Val m = NumV Int | ClosV Expr Frame | ContV (Val m -> m (Val m))

instance Eq (Val m) where
  NumV i1 == NumV i2 = i1 == i2
  ClosV e1 f1 == ClosV e2 f2 = e1 == e2 && f1 == f2
  _ == _ = False

instance Show (Val m) where
  show (NumV i) = show i
  show (ClosV e f) = show $ "<" ++ show e ++ ", " ++ show f ++ ">"
  show (ContV _) = "<cont>"
 
type Value = Val (Free Cmd)


---------------------------------------
--- meta-language commands and code ---
---------------------------------------

type Code  = Free Cmd

data Cmd :: * -> * where
  -- heap frame fragment
  SetL  :: Frame -> Label -> Frame -> Cmd ()
  SetV  :: Frame -> Name -> Value -> Cmd ()
  Get   :: Path -> Cmd Value
  GetV  :: Frame -> Name -> Cmd Value
  New   :: Cmd Frame
  GetL  :: [Label] -> Cmd Frame
  CurF  :: Cmd Frame
  WithF :: Frame -> Code Value -> Cmd Value

  -- continuation fragment
  CCC   :: Code Value -> Cmd Value
  Abort :: Code Value -> Cmd Value

  -- failure fragment
  Err   :: String -> Cmd a

instance MonadFail (Free Cmd) where
  fail = liftF . Err


----------------------------
--- boilerplate liftings ---
----------------------------

setl :: Frame -> Label -> Frame -> Code ()
setl f l f' = liftF (SetL f l f')

setv :: Frame -> Name -> Value -> Code ()
setv f n v = liftF (SetV f n v)

get :: Path -> Code Value
get = liftF . Get

getv :: Frame -> Name -> Code Value
getv f n = liftF (GetV f n)

new :: Code Frame
new = liftF New

getl :: [Label] -> Code Frame
getl = liftF . GetL

curf :: Code Frame
curf = liftF CurF

withf :: Frame -> Code Value -> Code Value
withf f c = liftF (WithF f c)

err :: String -> Code a
err = liftF . Err

callcc :: Code Value -> Code Value
callcc = liftF . CCC

abort :: Code Value -> Code Value
abort = liftF . Abort


-----------------------------------
--- object language interpreter ---
-----------------------------------

interp :: Expr -> Code Value
interp (Num i) = return (NumV i)
interp (Fun e) = do
  f <- curf
  return (ClosV e f)
interp (App e1 e2) = do
  v <- interp e1
  v2 <- interp e2
  case v of
    ClosV e f -> do
      f' <- new
      setl f' P f
      setv f' 0 v2
      withf f' (interp e)
    ContV k ->
      k v2
    _ -> err $ "cannot apply non-function value: " ++ show v
interp (Var p) = do
  get p
interp (CallCC e) = do
  callcc (interp e)


---------------------------------
--- meta-language interpreter ---
---------------------------------

data Result a = Final a
              | Cont (Code a)
              | Disco (Code a)
              | Stuck String
              deriving Show

step :: Code Value -> HFT Val Code (Result Value)
step (Stop a)   = trace "stopping" $ return (Final a)
step (Step (SetL f l f') k) = trace "setl" $ do
  setLink f l f'
  return (Cont (k ()))
step (Step (SetV f n v) k) = trace "set" $ do
  setValue f n v
  return (Cont (k ()))
step (Step (Get p) k) = trace "get" $ do
  f <- curFrame
  v <- followPath f p
  return (Cont (k v))
step (Step (GetV f n) k) = trace "getv" $ do
  v <- getValue f n
  return (Cont (k v))
step (Step New k) = trace "new" $ do
  f <- allocFrame
  return (Cont (k f))
step (Step (GetL ls) k) = trace "getl" $ do
  f  <- curFrame
  f' <- followLinks f ls
  return (Cont (k f'))
step (Step CurF k) = trace "curf" $ do
  f <- curFrame
  return (Cont (k f))
step (Step (WithF f c) k) = trace "withf" $ do
  r <- withFrame f (step c)
  case r of
    Final a  -> return $ Cont (k a)
    Stuck s  -> return $ Stuck s
    Disco cd -> return $ Disco cd
    Cont c'  -> return $ Cont (Step (WithF f c') k)
step (Step (Err s) _) = trace "err" $ do
  return (Stuck s)
step (Step (CCC c) k) = trace "cc" $ do
  f  <- curFrame
  f' <- allocFrame
  setLink f' P f
  setValue f' 0 (ContV (abort . k))
  return (Cont (Step (WithF f' c) k))
step (Step (Abort c) _) =
  return (Disco c)

  
steps :: Code Value -> HFT Val Code (Either Value String)
steps c = do
  r <- step c
  case r of
    Final a ->
      return (Left a)
    Cont cd ->
      steps cd
    Disco cd -> 
      steps cd
    Stuck s ->
      return (Right s)


run :: Expr -> Either Value String
run e = fst $
        runIdentity (runStateT (runReaderT (steps (interp e)) 0)
                               [HF (fromList []) (fromList [])])


-------------
--- tests ---
-------------

-- TODO: more...

testcc_simple :: Expr
testcc_simple = CallCC (App (Var (PPos 0)) (Num 42))

testcc_app :: Expr
testcc_app = lete (Fun (CallCC (App (Var (PPos 0)) (Var (PStep P (PPos 0))))))
                  (App (App (App (Var (PPos 0)) (Num 42)) (Num 0)) (Num (- 1)))

tests :: Test
tests = test [ "test1" ~: "cc simple" ~: Left (NumV 42) ~=? run testcc_simple
             , "test2" ~: "cc app" ~: Left (NumV 42) ~=? run testcc_app ]

