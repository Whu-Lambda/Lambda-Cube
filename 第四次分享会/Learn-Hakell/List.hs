data MyList t = EmptyList | ListNode t (MyList t) deriving (Show)

listt = ListNode 7 (ListNode 3 (ListNode 5 (ListNode 8 EmptyList)))

isEmpty :: MyList a -> Bool
isEmpty EmptyList = True
isEmpty _ = False

take'' :: Int -> MyList a -> MyList a
take'' n _
  | n <= 0 = EmptyList
take'' _ EmptyList = EmptyList
take'' n (ListNode first rest) = ListNode first (take'' (n -1) rest)

repeat' :: a -> MyList a
repeat' x = ListNode x (repeat' x)

sum' :: (Num a) => MyList a -> a
sum' EmptyList = 0
sum' (ListNode first rest) = first + sum' rest

product' :: (Num a) => MyList a -> a
product' EmptyList = 0
product' (ListNode first rest) = first * product' rest

appendRight :: a -> MyList a -> MyList a
appendRight element EmptyList = ListNode element EmptyList
appendRight element (ListNode first rest) = ListNode first (appendRight element rest)

appendLeft :: a -> MyList a -> MyList a
appendLeft = ListNode

filter'' :: (a -> Bool) -> MyList a -> MyList a
filter'' _ EmptyList = EmptyList
filter'' judge (ListNode first rest)
  | judge first = ListNode first (filter'' judge rest)
  | otherwise = filter'' judge rest

zipWith'' :: (a -> a -> a) -> MyList a -> MyList a -> MyList a
zipWith'' _ EmptyList _ = EmptyList
zipWith'' _ _ EmptyList = EmptyList
zipWith'' func (ListNode first1 rest1) (ListNode first2 rest2) = ListNode (func first1 first2) (zipWith'' func rest1 rest2)

addList :: MyList a -> MyList a -> MyList a
addList l EmptyList = l
addList EmptyList l = l
addList l1 (ListNode first rest) = addList (appendRight first l1) rest

quickSort :: (Ord a) => MyList a -> MyList a
quickSort EmptyList = EmptyList
quickSort (ListNode first rest) =
  let small = quickSort (filter'' (<= first) rest)
      big = quickSort (filter'' (> first) rest)
   in small `addList` (ListNode first EmptyList) `addList` big

createList :: [t] -> MyList t
createList [] = EmptyList
createList (x : xs) = ListNode x $ createList xs

list1 = createList [2, 4, 1, 0, 7, 4]

main = do
  print list1
  print $ quickSort list1
