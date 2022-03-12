guessNumber :: (Integral a) => a -> String
guessNumber 5 = "你猜对了！"
guessNumber x = "两眼一黑啦！"

main = do
  k <- readLn
  putStrLn $ guessNumber k
