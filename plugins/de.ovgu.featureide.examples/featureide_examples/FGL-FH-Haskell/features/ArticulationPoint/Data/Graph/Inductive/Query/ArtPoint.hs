module Data.Graph.Inductive.Query.ArtPoint (ap) where
{ import Data.Graph.Inductive.Graph;
   
  data DFSTree a = B (a, a, [(a, a)]) [DFSTree a]
                 deriving Eq;
   
  data LOWTree a = Brc (a, a, a) [LOWTree a]
                 deriving Eq;
   
  getBackEdges :: Node -> [[(Node, Int)]] -> [(Node, Int)];
  getBackEdges _ [] = [];
  getBackEdges v ls = map head (filter (elem (v, 0)) (tail ls));
   
  dfsTree ::
          (Graph gr) =>
            Int ->
              Node ->
                [Node] ->
                  [[(Node, Int)]] -> gr a b -> ([DFSTree Int], gr a b, Int);
  dfsTree n _ [] _ g = ([], g, n);
  dfsTree n _ _ _ g | isEmpty g = ([], g, n);
  dfsTree n u (v : vs) ls g
    = case match v g of
          { (Nothing, g1) -> dfsTree n u vs ls g1;
            (Just c, g1) -> (B (v, n + 1, bck) ts : ts', g3, k)
              where { bck = getBackEdges v ls;
                      (ts, g2, m) = dfsTree (n + 1) v sc ls' g1;
                      (ts', g3, k) = dfsTree m v vs ls g2;
                      ls' = ((v, n + 1) : sc') : ls;
                      sc' = map (\ x -> (x, 0)) sc;
                      sc = suc' c}};
   
  minbckEdge :: Int -> [(Node, Int)] -> Int;
  minbckEdge n [] = n;
  minbckEdge n bs = min n (minimum (map snd bs));
   
  getLow :: LOWTree Int -> Int;
  getLow (Brc (_, _, l) _) = l;
   
  lowTree :: DFSTree Int -> LOWTree Int;
  lowTree (B (v, n, []) []) = Brc (v, n, n) [];
  lowTree (B (v, n, bcks) []) = Brc (v, n, minbckEdge n bcks) [];
  lowTree (B (v, n, bcks) trs) = Brc (v, n, lowv) ts
    where { lowv = min (minbckEdge n bcks) lowChild;
            lowChild = minimum (map getLow ts);
            ts = map lowTree trs};
   
  getLowTree :: (Graph gr) => gr a b -> Node -> LOWTree Int;
  getLowTree g v = lowTree (head dfsf)
    where { (dfsf, _, _) = dfsTree 0 0 [v] [] g};
   
  isap :: LOWTree Int -> Bool;
  isap (Brc (_, _, _) []) = False;
  isap (Brc (_, 1, _) ts) = length ts > 1;
  isap (Brc (_, n, _) ts) = length ch >= 1
    where { ch = filter (>= n) (map getLow ts)};
   
  arp :: LOWTree Int -> [Node];
  arp (Brc (v, 1, _) ts)
    | length ts > 1 = v : concatMap arp ts
    | otherwise = concatMap arp ts;
  arp (Brc (v, n, l) ts)
    | isap (Brc (v, n, l) ts) = v : concatMap arp ts
    | otherwise = concatMap arp ts;
   
  artpoints :: (Graph gr) => gr a b -> Node -> [Node];
  artpoints g v = arp (getLowTree g v);
   
  ap :: (Graph gr) => gr a b -> [Node];
  ap g = artpoints g v
    where { ((_, v, _, _), _) = matchAny g}}
