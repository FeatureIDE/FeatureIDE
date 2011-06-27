module Data.Graph.Inductive.Internal.Heap
       (Heap(..), empty, unit, insert, merge, mergeAll, isEmpty, findMin,
        deleteMin, splitMin, build, toList, heapsort)
       where
{  
  data (Ord a) => Heap a b = Empty
                           | Node a b [Heap a b]
                           deriving Eq;
   
  showsHeap :: (Show a, Ord a, Show b) => Heap a b -> ShowS;
  showsHeap (Empty) = id;
  showsHeap (Node key val []) = shows key . (": " ++) . shows val;
  showsHeap (Node key val hs)
    = shows key . (": " ++) . shows val . (' ' :) . shows hs;
   
  instance (Show a, Ord a, Show b) => Show (Heap a b) where
          { showsPrec _ d = showsHeap d};
   
  empty :: (Ord a) => Heap a b;
  empty = Empty;
   
  unit :: (Ord a) => a -> b -> Heap a b;
  unit key val = Node key val [];
   
  insert :: (Ord a) => (a, b) -> Heap a b -> Heap a b;
  insert (key, val) h = merge (unit key val) h;
   
  merge :: (Ord a) => Heap a b -> Heap a b -> Heap a b;
  merge h (Empty) = h;
  merge (Empty) h = h;
  merge h@(Node key1 val1 hs) h'@(Node key2 val2 hs')
    | key1 < key2 = Node key1 val1 (h' : hs)
    | otherwise = Node key2 val2 (h : hs');
   
  mergeAll :: (Ord a) => [Heap a b] -> Heap a b;
  mergeAll [] = Empty;
  mergeAll [h] = h;
  mergeAll (h : h' : hs) = merge (merge h h') (mergeAll hs);
   
  isEmpty :: (Ord a) => Heap a b -> Bool;
  isEmpty (Empty) = True;
  isEmpty _ = False;
   
  findMin :: (Ord a) => Heap a b -> (a, b);
  findMin (Empty) = error "Heap.findMin: empty heap";
  findMin (Node key val _) = (key, val);
   
  deleteMin :: (Ord a) => Heap a b -> Heap a b;
  deleteMin (Empty) = Empty;
  deleteMin (Node _ _ hs) = mergeAll hs;
   
  splitMin :: (Ord a) => Heap a b -> (a, b, Heap a b);
  splitMin (Empty) = error "Heap.splitMin: empty heap";
  splitMin (Node key val hs) = (key, val, mergeAll hs);
   
  build :: (Ord a) => [(a, b)] -> Heap a b;
  build = foldr insert Empty;
   
  toList :: (Ord a) => Heap a b -> [(a, b)];
  toList (Empty) = [];
  toList h = x : toList r
    where { (x, r) = (findMin h, deleteMin h)};
   
  heapsort :: (Ord a) => [a] -> [a];
  heapsort = (map fst) . toList . build . map (\ x -> (x, x))}
