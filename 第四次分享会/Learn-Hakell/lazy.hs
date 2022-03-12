doubleMe :: (Num a) => [a] -> [a]
doubleMe [] = []
doubleMe (x : xs) = x + x : doubleMe xs

main = do
  print $ show $ take 5 $ doubleMe $ repeat 5
