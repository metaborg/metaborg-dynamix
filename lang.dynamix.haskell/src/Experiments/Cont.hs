import Control.Monad.Cont

test_add1 :: Cont r Int
test_add1 = do
  five <- return 5
  v <- callCC (\ k -> do
                  n2 <- return 6
                  n1 <- k 7
                  return (n1 + n2))
  return (v + 5)


