module Data.Graph.Inductive.Query.BFS
       (bfs, bfsn, bfsWith, bfsnWith, level, leveln, bfe, bfen, bft, lbft,
        esp, lesp)
       where
{ import Data.Graph.Inductive.Graph;
  import Data.Graph.Inductive.Internal.Queue;
  import Data.Graph.Inductive.Internal.RootPath;
   
  bfsnInternal ::
               (Graph gr) => (Context a b -> c) -> Queue Node -> gr a b -> [c];
  bfsnInternal f q g
    | queueEmpty q || isEmpty g = []
    | otherwise =
      case match v g of
          { (Just c, g')
              -> f c : bfsnInternal f (queuePutList (suc' c) q') g';
            (Nothing, g') -> bfsnInternal f q' g'}
    where { (v, q') = queueGet q};
   
  bfsnWith ::
           (Graph gr) => (Context a b -> c) -> [Node] -> gr a b -> [c];
  bfsnWith f vs = bfsnInternal f (queuePutList vs mkQueue);
   
  bfsn :: (Graph gr) => [Node] -> gr a b -> [Node];
  bfsn = bfsnWith node';
   
  bfsWith ::
          (Graph gr) => (Context a b -> c) -> Node -> gr a b -> [c];
  bfsWith f v = bfsnInternal f (queuePut v mkQueue);
   
  bfs :: (Graph gr) => Node -> gr a b -> [Node];
  bfs = bfsWith node';
   
  level :: (Graph gr) => Node -> gr a b -> [(Node, Int)];
  level v = leveln [(v, 0)];
  suci c i = zip (suc' c) (repeat i);
   
  leveln :: (Graph gr) => [(Node, Int)] -> gr a b -> [(Node, Int)];
  leveln [] _ = [];
  leveln _ g | isEmpty g = [];
  leveln ((v, j) : vs) g
    = case match v g of
          { (Just c, g') -> (v, j) : leveln (vs ++ suci c (j + 1)) g';
            (Nothing, g') -> leveln vs g'};
   
  bfenInternal :: (Graph gr) => Queue Edge -> gr a b -> [Edge];
  bfenInternal q g
    | queueEmpty q || isEmpty g = []
    | otherwise =
      case match v g of
          { (Just c, g')
              -> (u, v) : bfenInternal (queuePutList (outU c) q') g';
            (Nothing, g') -> bfenInternal q' g'}
    where { ((u, v), q') = queueGet q};
   
  bfen :: (Graph gr) => [Edge] -> gr a b -> [Edge];
  bfen vs g = bfenInternal (queuePutList vs mkQueue) g;
   
  bfe :: (Graph gr) => Node -> gr a b -> [Edge];
  bfe v = bfen [(v, v)];
  outU c = map (\ (v, w, _) -> (v, w)) (out' c);
   
  bft :: (Graph gr) => Node -> gr a b -> RTree;
  bft v = bf (queuePut [v] mkQueue);
   
  bf :: (Graph gr) => Queue Path -> gr a b -> RTree;
  bf q g
    | queueEmpty q || isEmpty g = []
    | otherwise =
      case match v g of
          { (Just c, g') -> p : bf (queuePutList (map (: p) (suc' c)) q') g';
            (Nothing, g') -> bf q' g'}
    where { (p@(v : _), q') = queueGet q};
   
  esp :: (Graph gr) => Node -> Node -> gr a b -> Path;
  esp s t = getPath t . bft s;
   
  lbft :: (Graph gr) => Node -> gr a b -> LRTree b;
  lbft v g
    = case (out g v) of
          { [] -> [LP []];
            (v', _, l) : _ -> lbf (queuePut (LP [(v', l)]) mkQueue) g};
   
  lbf :: (Graph gr) => Queue (LPath b) -> gr a b -> LRTree b;
  lbf q g
    | queueEmpty q || isEmpty g = []
    | otherwise =
      case match v g of
          { (Just c, g')
              -> LP p :
                   lbf (queuePutList (map (\ v' -> LP (v' : p)) (lsuc' c)) q') g';
            (Nothing, g') -> lbf q' g'}
    where { ((LP (p@((v, _) : _))), q') = queueGet q};
   
  lesp :: (Graph gr) => Node -> Node -> gr a b -> LPath b;
  lesp s t = getLPath t . lbft s}
