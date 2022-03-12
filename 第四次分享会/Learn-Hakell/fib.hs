fib :: (Integral a) => a -> a
fib 0 = 0
fib 1 = 1
fib n = fib (n -1) + fib (n -2)

fibs = 0 : 1 : zipWith (+) fibs (tail fibs)

main = do
  putStrLn "Enter a number:"
  num <- readLn
  print (fibs !! num)
