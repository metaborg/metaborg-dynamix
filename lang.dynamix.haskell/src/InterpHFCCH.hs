{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}

module InterpHFCCH where

import Debug.Trace

import Test.HUnit hiding (Path)
import Data.Map.Strict (fromList)
import Control.Monad.Reader (runReaderT)
import Control.Monad.State (runStateT)
import Control.Monad.Except (throwError, runExcept)
import Data.Either.HT (mapRight)
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

-- MODUS OPERANDI:
--
-- - Implement a handler for effects without continuation fragment
-- - Observe that WithF is not tail-recursive
-- - CPS+Defunct.
-- - Stack-transform

handle0' :: Cmd b -> (b -> Code Value) -> HFT Val Code Value
handle0' (SetL f l f') k = trace ("setl " ++ show f ++ " " ++ show l ++ " " ++ show f') $ do
  setLink f l f'
  handle0 (k ())
handle0' (SetV f n v) k = trace ("setv " ++ show f ++ " " ++ show n ++ " " ++ show v) $ do
  setValue f n v
  handle0 (k ())
handle0' (Get p) k = trace (show (Step (Get p) k)) $ do
  f <- curFrame
  v <- followPath f p
  trace ("got: " ++ show v) $ handle0 (k v)
handle0' (GetV f n) k = trace (show (Step (GetV f n) k)) $ do
  v <- getValue f n
  handle0 (k v)
handle0' New k = trace "new" $ do
  f <- allocFrame
  handle0 (k f)
handle0' CurF k = trace "curf" $ do
  f <- curFrame
  handle0 (k f)
handle0' (WithF f c) k = trace ("withf " ++ show f) $ do
  v <- withFrame f (handle0 c)
  handle0 (k v)
handle0' (Err s) _ = trace "err" $
  throwError s

handle0 :: Code Value -> HFT Val Code Value
handle0 (Stop x) = return x
handle0 (Step x k) = handle0' x k


-- inlining

handle1 :: Code Value -> HFT Val Code Value
handle1 (Stop x) = return x
handle1 (Step (SetL f l f') k) = trace ("setl " ++ show f ++ " " ++ show l ++ " " ++ show f') $ do
  setLink f l f'
  handle1 (k ())
handle1 (Step (SetV f n v) k) = trace ("setv " ++ show f ++ " " ++ show n ++ " " ++ show v) $ do
  setValue f n v
  handle1 (k ())
handle1 (Step (Get p) k) = trace (show (Step (Get p) k)) $ do
  f <- curFrame
  v <- followPath f p
  trace ("got: " ++ show v) $ handle1 (k v)
handle1 (Step (GetV f n) k) = trace (show (Step (GetV f n) k)) $ do
  v <- getValue f n
  handle1 (k v)
handle1 (Step New k) = trace "new" $ do
  f <- allocFrame
  handle1 (k f)
handle1 (Step CurF k) = trace "curf" $ do
  f <- curFrame
  handle1 (k f)
handle1 (Step (WithF f c) k) = trace ("withf " ++ show f) $ do
  v <- withFrame f (handle1 c)
  handle1 (k v)
handle1 (Step (Err s) _) = trace "err" $
  throwError s


-- cps

handle2 :: Code Value -> (Value -> HFT Val Code Value) -> HFT Val Code Value
handle2 (Stop x) c = c x
handle2 (Step (SetL f l f') k) c = trace ("setl " ++ show f ++ " " ++ show l ++ " " ++ show f') $ do
  setLink f l f'
  handle2 (k ()) c
handle2 (Step (SetV f n v) k) c = trace ("setv " ++ show f ++ " " ++ show n ++ " " ++ show v) $ do
  setValue f n v
  handle2 (k ()) c
handle2 (Step (Get p) k) c = trace (show (Step (Get p) k)) $ do
  f <- curFrame
  v <- followPath f p
  trace ("got: " ++ show v) $ handle2 (k v) c
handle2 (Step (GetV f n) k) c = trace (show (Step (GetV f n) k)) $ do
  v <- getValue f n
  handle2 (k v) c
handle2 (Step New k) c = trace "new" $ do
  f <- allocFrame
  handle2 (k f) c
handle2 (Step CurF k) c = trace "curf" $ do
  f <- curFrame
  handle2 (k f) c
handle2 (Step (WithF f cmd) k) c = trace ("withf " ++ show f) $ do
  withFrame f (handle2 cmd (\ v -> handle2 (k v) c))
handle2 (Step (Err s) _) _ = trace "err" $
  throwError s


-- defunctionalize

data Ctx = MT
         | WITHF (Value -> Code Value) Ctx

handle3 :: Code Value -> Ctx -> HFT Val Code Value
handle3 (Stop x) c = apply_cont c x
handle3 (Step (SetL f l f') k) c = trace ("setl " ++ show f ++ " " ++ show l ++ " " ++ show f') $ do
  setLink f l f'
  handle3 (k ()) c
handle3 (Step (SetV f n v) k) c = trace ("setv " ++ show f ++ " " ++ show n ++ " " ++ show v) $ do
  setValue f n v
  handle3 (k ()) c
handle3 (Step (Get p) k) c = trace (show (Step (Get p) k)) $ do
  f <- curFrame
  v <- followPath f p
  trace ("got: " ++ show v) $ handle3 (k v) c
handle3 (Step (GetV f n) k) c = trace (show (Step (GetV f n) k)) $ do
  v <- getValue f n
  handle3 (k v) c
handle3 (Step New k) c = trace "new" $ do
  f <- allocFrame
  handle3 (k f) c
handle3 (Step CurF k) c = trace "curf" $ do
  f <- curFrame
  handle3 (k f) c
handle3 (Step (WithF f cmd) k) c = trace ("withf " ++ show f) $ do
  withFrame f (handle3 cmd (WITHF k c))
handle3 (Step (Err s) _) _ = trace "err" $
  throwError s

apply_cont :: Ctx -> Value -> HFT Val Code Value
apply_cont MT v = return v
apply_cont (WITHF k c) v = handle3 (k v) c


-- list transform and inline

handle4 :: Code Value -> [(Value -> Code Value)] -> HFT Val Code Value
handle4 (Stop x) [] = return x
handle4 (Stop x) (c : cs) = handle4 (c x) cs
handle4 (Step (SetL f l f') k) c = trace ("setl " ++ show f ++ " " ++ show l ++ " " ++ show f') $ do
  setLink f l f'
  handle4 (k ()) c
handle4 (Step (SetV f n v) k) c = trace ("setv " ++ show f ++ " " ++ show n ++ " " ++ show v) $ do
  setValue f n v
  handle4 (k ()) c
handle4 (Step (Get p) k) c = trace (show (Step (Get p) k)) $ do
  f <- curFrame
  v <- followPath f p
  trace ("got: " ++ show v) $ handle4 (k v) c
handle4 (Step (GetV f n) k) c = trace (show (Step (GetV f n) k)) $ do
  v <- getValue f n
  handle4 (k v) c
handle4 (Step New k) c = trace "new" $ do
  f <- allocFrame
  handle4 (k f) c
handle4 (Step CurF k) c = trace "curf" $ do
  f <- curFrame
  handle4 (k f) c
handle4 (Step (WithF f cmd) k) c = trace ("withf " ++ show f) $ do
  withFrame f (handle4 cmd (k:c))
handle4 (Step (Err s) _) _ = trace "err" $
  throwError s


-- factor the fold

type Stack = [(Value -> Code Value)]

handler5 :: Cmd a -> (a -> Code Value) -> Stack -> HFT Val Code Value
handler5 (SetL f l f') k s = trace ("setl " ++ show f ++ " " ++ show l ++ " " ++ show f') $ do
  setLink f l f'
  handle5 (k ()) s
handler5 (SetV f n v) k s = trace ("setv " ++ show f ++ " " ++ show n ++ " " ++ show v) $ do
  setValue f n v
  handle5 (k ()) s
handler5 (Get p) k s = trace (show (Step (Get p) k)) $ do
  f <- curFrame
  v <- followPath f p
  trace ("got: " ++ show v) $ handle5 (k v) s
handler5 (GetV f n) k s = trace (show (Step (GetV f n) k)) $ do
  v <- getValue f n
  handle5 (k v) s
handler5 New k s = trace "new" $ do
  f <- allocFrame
  handle5 (k f) s
handler5 CurF k s = trace "curf" $ do
  f <- curFrame
  handle5 (k f) s
handler5 (WithF f c) k s = trace ("withf " ++ show f) $ do
  withFrame f (handle5 c (k : s))
handler5 (Err m) _ s = trace "err" $
  throwError m
handler5 (CCC c) k s = do
  f  <- curFrame
  f' <- allocFrame
  setLink f' P f
  setValue f' 0 (ContV (abort . k))
  handle5 (do v <- withf f' c; k v) s
handler5 (Abort c) _ _ = do
  handle5 c []


handle5 :: Code Value -> Stack -> HFT Val Code Value
handle5 x s = foldC handler5 s x


-------------
--- tests ---
-------------

test_app0 :: Expr
test_app0 = App (Fun (Var (PPos 0))) (Num 19)

test_app1 :: Expr
test_app1 = App (App (Fun (Fun (Var (PStep P (PPos 0))))) (Num 123)) (Num 0)


run :: Expr -> Either String Value
run e = runHFT (handle5 (interp e) [])

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

