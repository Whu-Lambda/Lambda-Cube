data MyList t = EmptyList | ListNode t (MyList t) deriving (Show)

myList = ListNode 6 (ListNode 4 (ListNode 2 (ListNode 0 EmptyList)))

empty = EmptyList

isEmpty :: MyList t -> Bool
isEmpty EmptyList = True
isEmpty _ = False

sum'' :: (Num a) => MyList a -> a
sum'' EmptyList = 0
sum'' (ListNode first rest) = first + sum'' rest

appendLeft :: MyList t -> t -> MyList t
appendLeft ls element = ListNode element ls

appendLeft' :: t -> MyList t -> MyList t
appendLeft' = ListNode

appendRight :: MyList t -> t -> MyList t
appendRight EmptyList element = (ListNode element EmptyList)
appendRight (ListNode first rest) element = ListNode first (appendRight rest element)

createList :: [t] -> MyList t
createList [] = EmptyList
createList (x : xs) = ListNode x $ createList xs

list2 = createList [1, 3 .. 20]

addList :: MyList a -> MyList a -> MyList a
addList l EmptyList = l
addList EmptyList l = l
addList l1 (ListNode first rest) = addList (appendRight l1 first) rest

filter'' :: (a -> Bool) -> MyList a -> MyList a
filter'' _ EmptyList = EmptyList
filter'' judge (ListNode first rest)
  | judge first = ListNode first (filter'' judge rest)
  | otherwise = filter'' judge rest



main = do
  -- print myList
  -- print $ appendLeft myList 9
  -- print $ appendLeft' 9 myList
  -- print $ appendRight myList 10
  print $ addList list2 myList
