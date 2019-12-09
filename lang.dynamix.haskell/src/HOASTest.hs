{-# LANGUAGE BangPatterns #-}

module HOASTest where

import Control.Exception
import Data.Typeable
import System.IO.Unsafe

data Term = Lam (Term -> Term) | App Term Term

data FOAS = FVar Int | FLam Int FOAS | FApp FOAS FOAS
  deriving Show

newtype HOASVar = HOASVar Int
  deriving (Typeable,Show)
instance Exception HOASVar

fromHOAS :: Int -> Term -> String
fromHOAS !free xOrVar = unsafePerformIO $
  do
    ex <- evaluate xOrVar
    return $ case ex of
      Lam f -> "FLam" ++ show free ++ (fromHOAS (free + 1) (f (throw (HOASVar free))))
      App x y -> "FApp" ++ (fromHOAS free x) ++ (fromHOAS free y)
  `catch` \(HOASVar i) -> return $ "FVar" ++ show i
