{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}

module InterpHFCCHM where

import Debug.Trace

import Test.HUnit hiding (Path)
import Control.Monad.Fail
import Free
import HeapFrameStack
import Control.Monad.Except (throwError)


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
  CurF  :: Cmd Frame
  WithF :: Frame -> Code Value -> Cmd Value

  -- continuation fragment
  CCC   :: Code Value -> Cmd Value
  Abort :: Code Value -> Cmd Value

  -- failure fragment
  Err   :: String -> Cmd a

instance MonadFail (Free Cmd) where
  fail = liftF . Err

instance Show (Cmd a) where
  show (SetL f l f') = "(SetL " ++ show f ++ " " ++ show l ++ " " ++ show f' ++ ")"
  show (SetV f n v) = "(SetV " ++ show f ++ " " ++ show n ++ " " ++ show v ++ ")"
  show (Get p) = "(Get " ++ show p ++ ")"
  show (GetV f n) = "(GetV " ++ show f ++ " " ++ show n ++ ")"
  show New = "New"
  show CurF = "CurF"
  show (WithF f c) = "(WithF " ++ show f ++ " " ++ fromFree 0 c ++ ")"
  show (CCC c) = "(CCC " ++ fromFree 0 c ++ ")"
  show (Abort c) = "(Abort " ++ fromFree 0 c ++ ")"
  show (Err s) = "(Err " ++ s ++ ")"

instance Show a => Show (Code a) where
  show x = fromFree 0 x


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

type M a = HFT Val Code () a

handler :: Cmd a -> (a -> Code Value) -> M Value
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
  withFrameCont f k (handle c)
handler (Err m) _ =
  throwError m
handler (CCC c) k = do
  f  <- curFrame
  f' <- allocFrame
  setLink f' P f
  setValue f' 0 (ContV (abort . k))
  handle (do v <- withf f' c; k v)
handler (Abort c) _ = do
  withConts [] (handle c)


handle :: Code Value -> M Value
handle x = do
  s <- curConts
  foldC (\ c k s' -> withConts s' (handler c k)) s x


-------------
--- tests ---
-------------

test_app0 :: Expr
test_app0 = App (Fun (Var (PPos 0))) (Num 19)

test_app1 :: Expr
test_app1 = App (App (Fun (Fun (Var (PStep P (PPos 0))))) (Num 123)) (Num 0)


run :: Expr -> Either String Value
run e = runHFT (handle (interp e)) ()

-- TODO: more...
testcc_simple :: Expr
testcc_simple = CallCC (App (Var (PPos 0)) (Num 3))

-- let x = \ y -> callcc (\ k -> k y) in
-- (((x 42) 0) -1)
testcc_app :: Expr
testcc_app = lete (Fun (CallCC (App (Var (PPos 0)) (Var (PStep P (PPos 0))))))
                  (App (App (App (Var (PPos 0)) (Num 42)) (Num 0)) (Num (- 1)))

tests :: Test
tests = test [ "test_app0" ~: "simple app" ~: Right (NumV 19) ~=? run test_app0
             , "test_app1" ~: "nested app" ~: Right (NumV 123) ~=? run test_app1
             , "test_cc1" ~: "cc simple" ~: Right (NumV 3) ~=? run testcc_simple
             , "test_cc2" ~: "cc app" ~: Right (NumV 42) ~=? run testcc_app ]

