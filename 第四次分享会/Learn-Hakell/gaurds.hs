examples :: (Integral a) => a -> String
examples num =
  if num > 100
    then "It is a big number."
    else "It is a small number."

examples' :: (Integral a) => a -> String
examples' num
  | num > 100 = "It is a big number."
  | otherwise = "It is a small number."

main = do
  num <- readLn
  putStrLn $ examples num
  putStrLn $ examples' num
