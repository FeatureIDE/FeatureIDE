module Data.Graph.Inductive.Internal.RootPath
       (RTree, LRTree, getPath, getLPath, getDistance, getLPathNodes)
       where
{ import Data.Graph.Inductive.Graph;
   
  instance (Eq a) => Eq (LPath a) where
          { (LP []) == (LP []) = True;
            (LP ((_, x) : _)) == (LP ((_, y) : _)) = x == y;
            (LP _) == (LP _) = False};
   
  instance (Ord a) => Ord (LPath a) where
          { compare (LP []) (LP []) = EQ;
            compare (LP ((_, x) : _)) (LP ((_, y) : _)) = compare x y;
            compare _ _ = error "LPath: cannot compare to empty paths"};
   
  type LRTree a = [LPath a];
   
  type RTree = [Path];
   
  first :: ([a] -> Bool) -> [[a]] -> [a];
  first p xss
    = case filter p xss of
          { [] -> [];
            x : _ -> x};
   
  findP :: Node -> LRTree a -> [LNode a];
  findP _ [] = [];
  findP v ((LP []) : ps) = findP v ps;
  findP v ((LP (p@((w, _) : _))) : ps)
    | v == w = p
    | otherwise = findP v ps;
   
  getPath :: Node -> RTree -> Path;
  getPath v = reverse . first (\ (w : _) -> w == v);
   
  getLPath :: Node -> LRTree a -> LPath a;
  getLPath v = LP . reverse . findP v;
   
  getDistance :: Node -> LRTree a -> a;
  getDistance v = snd . head . findP v;
   
  getLPathNodes :: Node -> LRTree a -> Path;
  getLPathNodes v = (\ (LP p) -> map fst p) . getLPath v}
