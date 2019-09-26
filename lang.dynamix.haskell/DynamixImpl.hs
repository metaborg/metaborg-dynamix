{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ExistentialQuantification #-}

module DynamixImpl where

import Dynamix
import Control.Monad.State as State
import Control.Monad.Fail
import Data.Map.Strict as Map
import Data.Maybe

import Debug.Trace

------------------
--- free monad ---
------------------

data Free c a = Stop a
              | forall b. Step (c b) (b -> Free c a)

instance Show (Free c a) where
  show (Step _ _) = "step"
  show (Stop _)   = "stop"

instance Functor (Free c) where
  fmap :: (a -> b) -> Free c a -> Free c b
  fmap g (Stop a)   = Stop (g a)
  fmap g (Step c k) = Step c (fmap g . k)

instance Applicative (Free c) where
  pure :: a -> Free c a
  pure = Stop

  (<*>) :: Free c (a -> b) -> Free c a -> Free c b
  Stop g     <*> f = fmap g f
  (Step c k) <*> f = Step c (\ x -> k x <*> f)

instance Monad (Free c) where
  (>>=) :: Free c a -> (a -> Free c b) -> Free c b
  Stop a   >>= k = k a
  Step c f >>= k = Step c (\ x -> f x >>= k)

liftF :: c a -> Free c a
liftF c = Step c Stop


----------------
--- commands ---
----------------

type Code = Free Cmd
type Val  = Value Code
type Reg  = Register Code
type Suspension = Val -> Code Val

data Cmd :: * -> * where
  -- primitive fragment
  AddI :: Val -> Val -> Cmd Val

  -- heap frame fragment
  SetL :: Frame -> Label -> Frame -> Cmd ()
  SetV :: Frame -> Name -> Val -> Cmd ()
  Get  :: Path -> Cmd Val
  GetV :: Frame -> Name -> Cmd Val
  New  :: Int -> Cmd Frame
  GetL :: [Label] -> Cmd Frame

  -- control frame fragment
  JumpZ   :: Val -> Code Val -> Code Val -> Cmd Val
  CurCF   :: Cmd CFrame
  Call    :: CFrame -> Cmd ()
  SetCV   :: Show a => CFrame -> ControlSlot a -> a -> Cmd ()
  GetCV   :: CFrame -> ControlSlot a -> Cmd a
  SetRV   :: Show a => CFrame -> Reg a -> a -> Cmd ()
  GetRV   :: CFrame -> Reg a -> Cmd a
  NewCF   :: Code Val -> CFrame -> Frame -> Cmd CFrame
  LabelC  :: ((Val -> Code Val) -> Code Val) -> Cmd Val

  -- failure fragment
  Fail    :: String -> Cmd a

instance Show (Cmd a) where
  show (AddI v1 v2) = "AddI " ++ show v1 ++ " " ++ show v2
  show (SetL f n f') = "SetL " ++ show f ++ " " ++ show n ++ " " ++ show f'
  show (SetV f n v) = "SetV " ++ show f ++ " " ++ show n ++ " " ++ show v
  show (Get p) = "Get " ++ show p
  show (GetV f n) = "GetV " ++ show f ++ " " ++ show n
  show (New i) = "New " ++ show i
  show (GetL ls) = "GetL " ++ show ls
  show (JumpZ v c1 c2) = "JumpZ " ++ show v ++ " " ++ show c1 ++ " " ++ show c2
  show CurCF = "CurCF"
  show (Call cf) = "Call " ++ show cf
  show (SetCV cf cs a) = "SetCV " ++ show cf ++ " " ++ show cs ++ " " ++ show a
  show (GetCV cf cs) = "GetCV " ++ show cf ++ " " ++ show cs
  show (SetRV cf r a) = "SetRV " ++ show cf ++ " " ++ show r ++ " " ++ show a
  show (GetRV cf r) = "GetRV " ++ show cf ++ " " ++ show r
  show (NewCF cd cf f) = "NewCF " ++ show cd ++ " " ++ show cf ++ " " ++ show f
  show (LabelC _) = "LabelC"
  show (Fail s) = "Fail " ++ s

-----------------------
--- monad instances ---
-----------------------

-- boilerplate

instance MonadPrimitive Code where
  addi v1 v2 = liftF (AddI v1 v2)

instance MonadHeapFrames Code where
  setl f l f' = liftF (SetL f l f')
  setv f n v  = liftF (SetV f n v)
  get p       = liftF (Get p)
  getv f n    = liftF (GetV f n)
  new i       = liftF (New i)
  getl ls     = liftF (GetL ls)

instance MonadControlFrames Code where
  jumpz v c1 c2 = liftF (JumpZ v c1 c2)
  curcf         = liftF  CurCF
  -- mkcurcf cf    = liftF (MkCurCF cf)
  call cf       = liftF (Call cf)
  setcv cf cs a = liftF (SetCV cf cs a)
  getcv cf cs   = liftF (GetCV cf cs)
  setrv cf r a  = liftF (SetRV cf r a)
  getrv cf r    = liftF (GetRV cf r)
  newcf cd cf f = liftF (NewCF cd cf f)
  labelc k      = liftF (LabelC k)

instance MonadFail Code where
  fail s = liftF (Fail s)


-------------------
--- data layout ---
-------------------

data HeapFrame = HF { links :: Map Label Frame
                    , slots :: Map Name Val    }
               deriving Show

type Heap = [HeapFrame]

data Regs = Regs { argvalue  :: Maybe Val
                 , callret   :: Maybe Val    }
          deriving Show

data ControlFrame = CF { pc   :: Code Val
                       , ret  :: CFrame
                       , df   :: Frame
                       , exch :: Maybe CFrame
                       , regs :: Regs     }
                  deriving Show

type Stack = [ControlFrame]


-----------
--- aux ---
-----------

update' :: Show a => [a] -> Int -> a -> [a]
update' []       i x = error $ "bad update of " ++ show i ++ " with " ++ show x
update' (_ : xs) 0 x = x : xs
update' (x : xs) i y = x : update' xs (i - 1) y


-----------------------
--- dynamix effects ---
-----------------------

type M = State (Heap, Stack, CFrame)

getHeap :: M Heap
getHeap = do
  (h, _, _) <- State.get
  return h

putHeap :: Heap -> M ()
putHeap h = do
  (_, s, cf) <- State.get
  put (h, s, cf)

getStack :: M Stack
getStack = do
  (_, s, _) <- State.get
  return s

putStack :: Stack -> M ()
putStack s = do
  (h, _, cf) <- State.get
  put (h, s, cf)

getCurCF :: M CFrame
getCurCF = do
  (_, _, cf) <- State.get
  return cf

setCurCF :: CFrame -> M ()
setCurCF cf = do
  (h, s, _) <- State.get
  put (h, s, cf)

getFrame :: Frame -> M HeapFrame
getFrame i = do
  h <- getHeap
  return (h !! i)

putFrame :: Frame -> HeapFrame -> M ()
putFrame i hf = do
  h <- getHeap
  putHeap (update' h i hf)

setLink :: Frame -> Label -> Frame -> M ()
setLink f l f' = do
  hf <- getFrame f
  putFrame f (hf { links = insert l f' (links hf) })

getLink :: Frame -> Label -> M Frame
getLink f l = do
  hf <- getFrame f
  return (links hf ! l)

setValue :: Frame -> Name -> Val -> M ()
setValue f n v = do
  hf <- getFrame f
  putFrame f (hf { slots = insert n v (slots hf) })
  return ()

getValue :: Frame -> Name -> M Val
getValue f n = do
  hf <- getFrame f
  return (slots hf ! n)

getCFrame :: CFrame -> M ControlFrame
getCFrame cf = do
  s <- getStack
  return (s !! cf)

getCurDF :: M Frame
getCurDF = do
  c  <- getCurCF
  cf <- getCFrame c
  return (df cf)

followPath :: Frame -> Path -> M Val
followPath f (PPos n) = do
  getValue f n
followPath f (PStep l p) = do
  f' <- getLink f l
  followPath f' p

followLinks :: Frame -> [Label] -> M Frame
followLinks f [] = do
  return f
followLinks f (l : ls) = do
  f' <- getLink f l
  followLinks f' ls

allocFrame :: Int -> M Frame
allocFrame _ = do
  h <- getHeap
  putHeap (h ++ [HF (fromList []) (fromList [])])
  return (length h)

allocCFrame :: Code Val -> CFrame -> Frame -> M CFrame
allocCFrame cd cf f = do
  s <- getStack
  putStack (s ++ [CF cd cf f Nothing (Regs Nothing Nothing)])
  return (length s)

getPC :: CFrame -> M (Code Val)
getPC c = do
  s <- getStack
  return (pc (s !! c))

setPC :: CFrame -> Code Val -> M ()
setPC c cd = do
  s <- getStack
  cfc <- getCFrame c
  putStack (update' s c (cfc { pc = cd }))

setControlSlot :: CFrame -> ControlSlot a -> a -> M ()
setControlSlot cf cs a = do
  s <- getStack
  cfc <- getCFrame cf
  case cs of
    Ret ->
      putStack (update' s cf (cfc { ret = a }))
    DF ->
      putStack (update' s cf (cfc { df = a }))
    ExcH ->
      trace (show $ (update' s cf (cfc { exch = Just a }))) $ putStack (update' s cf (cfc { exch = Just a }))

getControlSlot :: CFrame -> ControlSlot a -> M a
getControlSlot cf cs = do
  cfc <- getCFrame cf
  case cs of
    Ret ->
      return (ret cfc)
    DF ->
      return (df cfc)
    ExcH ->
      return (fromJust (exch cfc))

getRegs :: CFrame -> M Regs
getRegs cf = do
  cfc <- getCFrame cf
  return (regs cfc)


setRegister :: CFrame -> Reg a -> a -> M ()
setRegister cf r a = do
  s <- getStack
  cfc <- getCFrame cf
  rs <- getRegs cf
  case r of
    CallArg ->
      putStack (update' s cf (cfc { regs = rs { argvalue = Just a } }))
    CallRet ->
      putStack (update' s cf (cfc { regs = rs { callret = Just a } }))

getRegister :: CFrame -> Reg a -> M a
getRegister cf r = do
  rs <- getRegs cf
  case r of
    CallArg ->
      return (fromJust (argvalue rs))
    CallRet ->
      return (fromJust (callret rs))


-------------------------
--- dynamix semantics ---
-------------------------

data Result a = Final a
              | Cont (Code a)
              | Ctrl (Code a) CFrame
              | Stuck String
              deriving Show

step :: Code Val -> M (Result Val)
step (Stop a)   = return (Final a)
step (Step (AddI v1 v2) k) = 
  case (v1, v2) of
    (NumV i1, NumV i2) ->
      return (Cont (k (NumV (i1 + i2))))
    _ ->
      return (Stuck "Could not add non-integers")
step (Step (SetL f l f') k) = do
  setLink f l f'
  return (Cont (k ()))
step (Step (SetV f n v) k) = do
  setValue f n v
  return (Cont (k ()))
step (Step (Get p) k) = do
  f <- getCurDF
  v <- followPath f p
  return (Cont (k v))
step (Step (GetV f n) k) = do
  v <- getValue f n
  return (Cont (k v))
step (Step (New i) k) = do
  f <- allocFrame i
  return (Cont (k f))
step (Step (GetL ls) k) = do
  f  <- getCurDF
  f' <- followLinks f ls
  return (Cont (k f'))
step (Step (JumpZ v c1 c2) _) = do
  case v of
    NumV 0 ->
      return (Cont c1)
    NumV _ ->
      return (Cont c2)
    _ ->
      return (Stuck "Cannot branch on non-number value")
step (Step CurCF k) = do
  c <- getCurCF
  return (Cont (k c))
step (Step (LabelC k') k) =
  return (Cont (k' k))
step (Step (Call cf) k) = do
  return (Ctrl (k ()) cf)
step (Step (SetCV cf cs x) k) = do
  setControlSlot cf cs x
  return (Cont (k ()))
step (Step (GetCV cf cs) k) = do
  x <- getControlSlot cf cs
  return (Cont (k x))
step (Step (SetRV cf r x) k) = do
  setRegister cf r x
  return (Cont (k ()))
step (Step (GetRV cf r) k) = do
  x <- getRegister cf r
  return (Cont (k x))
step (Step (NewCF cd cfp f) k) = do
  cf <- allocCFrame cd cfp f
  return (Cont (k cf))
step (Step (Fail s) _) = do
  return (Stuck s)

steps :: Code Val -> M (Either Val String)
steps c = trace "stepping ..." $ do
  cf <- getCurCF
  case c of
    Step c' _ ->
     trace (show c') $ return ()
    _ ->
     trace (show c) $ return ()
  r <- step c
  case r of
    Final a ->
      return (Left a)
    Cont cd -> do
      setPC cf cd
      steps cd
    Ctrl cd cf' -> do
      setPC cf cd
      setCurCF cf'
      cd' <- getPC cf'
      steps cd'
    Stuck s ->
      return (Right s)

ev :: Expr -> Code Val
ev = eval

interp :: Expr -> M (Either Val String)
interp e = do
  cfcur <- getCurCF
  dfcur <- getCurDF
  cf    <- allocCFrame (eval e) cfcur dfcur
  setControlSlot cf ExcH 0
  steps (Step (Call cf) (\_ -> Stop (NumV (-2)))) -- should probably be fail
  
run :: Expr -> Either Val String
run e =
  fst $ runState (interp e)
                 ([],
                  [CF (Stop (NumV (- 2))) (-1) (-1) (Just 0) (Regs Nothing Nothing)],
                  0)
