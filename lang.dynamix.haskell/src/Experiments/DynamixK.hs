{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}

module DynamixK where

-- import Debug.Trace

-- import Test.HUnit hiding (Path)
import Control.Monad.Fail
import FreeK
import HeapFrameStack
import Control.Monad.Except (throwError)


---------------------------------------
--- meta-language commands and code ---
---------------------------------------

type Code val marks bch = Free (Cmd val marks) bch

type Cont val marks = (Point , val -> Code val marks val)

data Cmd val marks :: * -> * where
  -- heap frame fragment
  SetL  :: Frame -> Label -> Frame -> Cmd val marks ()
  SetV  :: Frame -> Name -> val -> Cmd val marks ()
  Get   :: Path -> Cmd val marks val
  GetV  :: Frame -> Name -> Cmd val marks val
  New   :: Cmd val marks Frame
  CurF  :: Cmd val marks Frame

  -- control fragment
  Recouple :: (marks -> Bool) -> Point -> Point -> Cmd val marks Point
  Invk  :: Cont val marks -> val -> Cmd val marks val
  Invk0 :: Cont val marks -> val -> Cmd val marks val
  CurPoint :: Cmd val marks Point
  Unwind :: (marks -> Bool) -> Cmd val marks Point
  SetPoint :: Point -> Cmd val marks ()

  WithMarks :: marks -> Code val marks val -> Cmd val marks val
  WithF :: Frame -> Code val marks val -> Cmd val marks val

--   -- failure fragment
--   Err   :: String -> Cmd val marks a

-- instance MonadFail (Free (Cmd val marks)) where
--   fail = liftF . Err

-- instance (Show val, Show marks) => Show (Cmd val marks a) where
--   show (SetL f l f') = "(SetL " ++ show f ++ " " ++ show l ++ " " ++ show f' ++ ")"
--   show (SetV f n v) = "(SetV " ++ show f ++ " " ++ show n ++ " " ++ show v ++ ")"
--   show (Get p) = "(Get " ++ show p ++ ")"
--   show (GetV f n) = "(GetV " ++ show f ++ " " ++ show n ++ ")"
--   show New = "New"
--   show CurF = "CurF"
--   show (WithF f c) = "(WithF " ++ show f ++ " " ++ fromFree 0 c ++ ")"
--   show (Mark _) = "(Mark <...>)"
--   show (Mark0 _) = "(Mark0 <...>)"
--   show (Recouple _ pcur pk) = "(CopyUpto <...> " ++ show pcur ++ " " ++ show pk ++ ")"
--   show (Invk _ v) = "(Invk <...> (" ++ show v ++ "))"
--   show (Invk0 _ v) = "(Invk0 <...> (" ++ show v ++ "))"
--   show (WithMarks mrks f) = "(WithMarks " ++ show mrks ++ " " ++ show f ++ ")"
--   show (Unwind _) = "(Unwind <...> <...>)"
--   show CurPoint = "CurPoint"
--   show (SetPoint p) = "(SetPoint " ++ show p ++ ")"
--   show (Err s) = "(Err " ++ s ++ ")"

-- instance (Show a, Show val, Show marks) => Show (Code val marks a) where
--   show x = fromFree 0 x


-- ----------------------------
-- --- boilerplate liftings ---
-- ----------------------------

-- setl :: Frame -> Label -> Frame -> Code val marks ()
-- setl f l f' = liftF (SetL f l f')

-- setv :: Frame -> Name -> val -> Code val marks ()
-- setv f n v = liftF (SetV f n v)

-- get :: Path -> Code val marks val
-- get = liftF . Get

-- getv :: Frame -> Name -> Code val marks val
-- getv f n = liftF (GetV f n)

-- new :: Code val marks Frame
-- new = liftF New

-- curf :: Code val marks Frame
-- curf = liftF CurF

-- withf :: Frame -> Code val marks val -> Code val marks val
-- withf f c = liftF (WithF f c)

-- err :: String -> Code val marks a
-- err = liftF . Err

-- mark :: (Cont val marks -> Code val marks val) -> Code val marks val
-- mark = liftF . Mark

-- mark0 :: (Cont val marks -> Code val marks val) -> Code val marks val
-- mark0 = liftF . Mark0

-- recouple :: (marks -> Bool) -> Point -> Point -> Code val marks Point
-- recouple f pcur pk = liftF (Recouple f pcur pk)

-- markuntil :: (Cont val marks -> Code val marks val) -> Code val marks val
-- markuntil = liftF . Mark

-- invk :: Cont val marks -> val -> Code val marks val
-- invk κ v = liftF (Invk κ v)

-- invk0 :: Cont val marks -> val -> Code val marks val
-- invk0 κ v = liftF (Invk0 κ v)

-- withmarks :: marks -> Code val marks val -> Code val marks val
-- withmarks mrks m = liftF (WithMarks mrks m)

-- unwind :: (marks -> Bool) -> Code val marks Point
-- unwind = liftF . Unwind

-- curpoint :: Code val marks Point
-- curpoint = liftF CurPoint

-- setpoint :: Point -> Code val marks ()
-- setpoint = liftF . SetPoint


-- ---------------------------------
-- --- meta-language interpreter ---
-- ---------------------------------

-- type M val marks a = HFT val (Code val marks) marks a

-- handler :: (Show val, Show marks) => Cmd val marks a -> (a -> Code val marks val) -> M val marks val
-- handler (SetL f l f') k = do
--   setLink f l f'
--   handle (k ())
-- handler (SetV f n v) k = do
--   setValue f n v
--   handle (k ())
-- handler (Get p) k = do
--   f <- curFrame
--   v <- followPath f p
--   handle (k v)
-- handler (GetV f n) k = do
--   v <- getValue f n
--   handle (k v)
-- handler New k = do
--   f <- allocFrame
--   handle (k f)
-- handler CurF k = do
--   f <- curFrame
--   handle (k f)
-- handler (WithF f c) k = do
--   mrks <- curMarks
--   p <- pushStack f k mrks
--   setPoint p
--   handle c
-- handler (Err m) _ =
--   throwError m
-- handler (Mark f) k = do
--   p <- curPoint
--   handle (do v <- f (p , k); k v)
-- handler (Mark0 f) k = do
--   p <- curPoint
--   handle (f (p , k))
-- handler (Recouple f pcur pk) k = do
--   x <- foldLinksUntil pcur pk f copyAndLink
--   handle (k x)
-- handler (Unwind f) k = do
--   p <- curPoint
--   p' <- unwindUntil p
--   handle (k p')
--   where
--     unwindUntil p0 = do
--       sf <- getStackFrame p0
--       if f (marks sf)
--       then return p0
--       else case coupling sf of
--              Just p' -> unwindUntil p'
--              Nothing -> return p0
-- handler (Invk (p , k) v) _ = do
--   setPoint p
--   handle (k v)
-- handler (Invk0 (p , k) v) k' = do
--   setPoint p
--   handle (k v >>= k')
-- handler (WithMarks mrks c) k = do
--   f <- curFrame
--   p <- pushStack f k mrks
--   setPoint p
--   handle c
-- handler CurPoint k = do
--   p <- curPoint
--   handle (k p)
-- handler (SetPoint p) k = do
--   setPoint p
--   handle (k ())

-- handle :: (Show val, Show marks) => Code val marks val -> M val marks val
-- handle (Stop x) = do
--   p <- curPoint
--   sf <- getStackFrame p
--   case coupling sf of
--     Nothing -> return x
--     Just p' -> do
--       setPoint p'
--       handle (knt sf x)
-- handle (Step x k) = handler x k


-- -----------
-- --- run ---
-- -----------

-- runM :: M val marks val -> marks -> Either String val
-- runM m mrks = runHFT m Stop mrks
