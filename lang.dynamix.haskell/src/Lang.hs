{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE DerivingStrategies #-}

module Lang where

-- import Debug.Trace

import Test.HUnit hiding (Path)
import Dynamix
import HeapFrameStack

------------------------------
--- object language syntax ---
------------------------------

data Expr = Num Int | Plus Expr Expr | Fun Expr | App Expr Expr | Var Path
          | CallCC Expr
          | Prompt Expr
          | Control Expr
          deriving Show
          deriving Eq

-- syntactic sugar

lete :: Expr -> Expr -> Expr
lete e body = App (Fun body) e


------------------------------
--- object language values ---
------------------------------

type Slots = Bool

data Val = NumV Int | ClosV Expr Frame
         | ContV (Cont Val Slots)
         | DelimContV (Cont Val Slots)

instance Eq Val where
  NumV i1 == NumV i2 = i1 == i2
  ClosV e1 f1 == ClosV e2 f2 = e1 == e2 && f1 == f2
  _ == _ = False

instance Show Val where
  show (NumV i) = show i
  show (ClosV e f) = show $ "<" ++ show e ++ ", " ++ show f ++ ">"
  show (ContV _) = "<cont>"
  show (DelimContV _) = "<delimcont>"


-----------------------------------
--- object language interpreter ---
-----------------------------------

interp :: Expr -> Code Val Slots Val
interp (Num i) =
  return (NumV i)
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
    ContV k -> do
      invk k v2
    DelimContV (p , k) -> do -- E[(λ x . C[x]) v] -> E[C[v]]
      pcur <- curpoint
      p' <- recouple id p pcur
      invk0 (p' , k) v2
    _ -> err $ "cannot apply non-function value: " ++ show v
interp (Var p) = do
  get p
interp (CallCC e) = do
  label (\ k -> do
    f  <- curf
    f' <- new
    setl f' P f
    setv f' 0 (ContV k)
    withf f' (interp e))
interp (Prompt e) = do
  withmarks True (interp e)
interp (Control e) = do -- control (λ k . c)
  label0 (\ k -> do
    f  <- curf
    f' <- new
    setl f' P f
    setv f' 0 (DelimContV k)
    p' <- unwind id
    setpoint p'
    withf f' (interp e))


-----------
--- run ---
-----------

run :: Expr -> Either String Val
run e = runM (handle (interp e)) False


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

testcc_app2 :: Expr
testcc_app2 = (App (Fun (App (CallCC (App (Var (PPos 0)) (Fun (Var (PPos 0))))) (Var (PPos 0)))) (Num 2))


-- (+ 5 (call/cc 
--   (lambda (k) (+ 6 (k 7))))) ; answer: 12
testcc_add1 :: Expr
testcc_add1 =
  Plus (Num 5)
       (CallCC (Plus (Num 6) (App (Var (PPos 0)) (Num 7))))

-- (+ 3 (call/cc (lambda (k) (+ 2 5))))  ; answer: 10
testcc_add2 :: Expr
testcc_add2 =
  Plus (Num 3)
       (CallCC (Plus (Num 2) (Num 5)))


testdl_add1 :: Expr
testdl_add1 =
  Plus (Num 1)
       (Prompt (Plus (Num 2) (Control (App (Var (PPos 0)) (Num 7)))))

testdl_add2 :: Expr
testdl_add2 =
  Plus (Num 1)
       (Prompt (Plus (Num 2) (Control (App (Var (PPos 0)) (App (Var (PPos 0)) (Num 7))))))


-- 1 + prompt(2 + control(λ k . 7))
testdl_abort :: Expr
testdl_abort =
  Plus (Num 1)
       (Prompt (Plus (Num 2) (Control (Num 7))))


-- prompt ( (prompt ( (control (function f -> f))
--                    (control (function g -> g (g 0))) ))
--          (function x -> 1 + x)
--        ) ;;
testdl_doublepromptwrapped :: Expr
testdl_doublepromptwrapped =
  Prompt (App (Prompt (App (Control (Var (PPos 0)))
                           (Control (App (Var (PPos 0)) (App (Var (PPos 0)) (Num 0))))))
              (Fun (Plus (Num 1) (Var (PPos 0)))))


-- prompt ( (function x -> control (function d -> x))
--          (control (function l -> 1 + l 0))
--        ) ;;
testdl_promptwrapped :: Expr
testdl_promptwrapped =
  Prompt (App (Fun (Control (Var (PStep P (PPos 0)))))
              (Control (Plus (Num 1) (App (Var (PPos 0)) (Num 0)))))

tests :: Test
tests = test [ "test_app0" ~: "simple app" ~: Right (NumV 19) ~=? run test_app0
             , "test_app1" ~: "nested app" ~: Right (NumV 123) ~=? run test_app1
             , "test_cc1" ~: "cc simple" ~: Right (NumV 3) ~=? run testcc_simple
             , "test_cc2" ~: "cc app2" ~: Right (NumV 2) ~=? run testcc_app2
             , "test_cc3" ~: "cc add 1" ~: Right (NumV 12) ~=? run testcc_add1
             , "test_cc4" ~: "cc add 2" ~: Right (NumV 10) ~=? run testcc_add2
             , "test_dl1" ~: "dl add 1" ~: Right (NumV 10) ~=? run testdl_add1
             , "test_dl2" ~: "dl add 2" ~: Right (NumV 12) ~=? run testdl_add2
             , "test_dl3" ~: "dl abort" ~: Right (NumV 8) ~=? run testdl_abort
             , "test_dl4" ~: "dl double prompt wrapped" ~: Right (NumV 2) ~=? run testdl_doublepromptwrapped
             , "test_dl5" ~: "dl prompt wrapped" ~: Right (NumV 0) ~=? run testdl_promptwrapped ]

