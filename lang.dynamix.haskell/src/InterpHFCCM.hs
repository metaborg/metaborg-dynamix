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

data Expr = Num Int | Plus Expr Expr | Fun Expr | App Expr Expr | Var Path
          | CallCC Expr
          deriving Show
          deriving Eq

-- syntactic sugar

lete :: Expr -> Expr -> Expr
lete e body = App (Fun body) e


------------------------------
--- object language values ---
------------------------------

data Val = NumV Int | ClosV Expr Frame | ContV (Val -> Code Val)

instance Eq Val where
  NumV i1 == NumV i2 = i1 == i2
  ClosV e1 f1 == ClosV e2 f2 = e1 == e2 && f1 == f2
  _ == _ = False

instance Show Val where
  show (NumV i) = show i
  show (ClosV e f) = show $ "<" ++ show e ++ ", " ++ show f ++ ">"
  show (ContV _) = "<cont>"
 

---------------------------------------
--- meta-language commands and code ---
---------------------------------------

type Code  = Free Cmd

data Cmd :: * -> * where
  -- heap frame fragment
  SetL  :: Frame -> Label -> Frame -> Cmd ()
  SetV  :: Frame -> Name -> Val -> Cmd ()
  Get   :: Path -> Cmd Val
  GetV  :: Frame -> Name -> Cmd Val
  New   :: Cmd Frame
  CurF  :: Cmd Frame
  WithF :: Frame -> Code Val -> Cmd Val

  -- continuation fragment
  CCC   :: Code Val -> Cmd Val
  Abort :: Code Val -> Cmd Val

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

setv :: Frame -> Name -> Val -> Code ()
setv f n v = liftF (SetV f n v)

get :: Path -> Code Val
get = liftF . Get

getv :: Frame -> Name -> Code Val
getv f n = liftF (GetV f n)

new :: Code Frame
new = liftF New

curf :: Code Frame
curf = liftF CurF

withf :: Frame -> Code Val -> Code Val
withf f c = liftF (WithF f c)

err :: String -> Code a
err = liftF . Err

callcc :: Code Val -> Code Val
callcc = liftF . CCC

abort :: Code Val -> Code Val
abort = liftF . Abort


-----------------------------------
--- object language interpreter ---
-----------------------------------

interp :: Expr -> Code Val
interp (Num i) = return (NumV i)
interp (Plus e1 e2) = do
  (NumV i1) <- interp e1
  (NumV i2) <- interp e2
  return (NumV (i1 + i2))
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

handler :: Cmd a -> (a -> Code Val) -> M Val
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

-- object language effects --

handler (CCC c) k = do
  f  <- curFrame
  f' <- allocFrame
  setLink f' P f
  setValue f' 0 (ContV (abort . k))
  handle (do v <- withf f' c; k v)
handler (Abort c) _ = do
  withConts [] (handle c)


handle :: Code Val -> M Val
handle x = do
  s <- curConts
  foldC (\ c k s' -> withConts s' (handler c k)) s x


-----------
--- run ---
-----------

run :: Expr -> Either String Val
run e = runHFT (handle (interp e)) ()


-------------
--- tests ---
-------------

test_app0 :: Expr
test_app0 = App (Fun (Var (PPos 0))) (Num 19)

test_app1 :: Expr
test_app1 = App (App (Fun (Fun (Var (PStep P (PPos 0))))) (Num 123)) (Num 0)


-- TODO: more...
testcc_simple :: Expr
testcc_simple = CallCC (App (Var (PPos 0)) (Num 3))

-- let x = \ y -> callcc (\ k -> k y) in
-- (((x 42) 0) -1)
testcc_app :: Expr
testcc_app = lete (Fun (CallCC (App (Var (PPos 0)) (Var (PStep P (PPos 0))))))
                  (App (App (App (Var (PPos 0)) (Num 42)) (Num 0)) (Num (- 1)))

-- (+ 5 (call/cc 
--  (lambda (k) (+ 6 (k 7)))))) ; answer: 12
testcc_add1 :: Expr
testcc_add1 =
  Plus (Num 5)
       (CallCC (Plus (Num 6) (App (Var (PPos 0)) (Num 7))))

-- (+ 3 (call/cc (lambda (k) (+ 2 5)))))  ; answer: 10
testcc_add2 :: Expr
testcc_add2 =
  Plus (Num 3)
       (CallCC (Plus (Num 2) (Num 5)))


tests :: Test
tests = test [ "test_app0" ~: "simple app" ~: Right (NumV 19) ~=? run test_app0
             , "test_app1" ~: "nested app" ~: Right (NumV 123) ~=? run test_app1
             , "test_cc1" ~: "cc simple" ~: Right (NumV 3) ~=? run testcc_simple
             , "test_cc2" ~: "cc app" ~: Right (NumV 42) ~=? run testcc_app
             , "test_cc3" ~: "cc add 1" ~: Right (NumV 12) ~=? run testcc_add1
             , "test_cc4" ~: "cc add 2" ~: Right (NumV 10) ~=? run testcc_add2 ]

