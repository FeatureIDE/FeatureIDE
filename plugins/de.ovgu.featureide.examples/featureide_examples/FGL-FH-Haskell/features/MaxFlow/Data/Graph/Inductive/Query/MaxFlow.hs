module Data.Graph.Inductive.Query.MaxFlow
       (getRevEdges, augmentGraph, updAdjList, updateFlow, mfmg, mf,
        maxFlowgraph, maxFlow)
       where
{ import Data.List;
  import Data.Graph.Inductive.Basic;
  import Data.Graph.Inductive.Graph;
  import Data.Graph.Inductive.Query.BFS;
   
  getRevEdges ::
              (Num b, Ord b) => [(Node, Node)] -> [(Node, Node, b)];
  getRevEdges [] = [];
  getRevEdges ((u, v) : es)
    | notElem (v, u) es = (v, u, 0) : getRevEdges es
    | otherwise = getRevEdges (delete (v, u) es);
   
  augmentGraph ::
               (DynGraph gr, Num b, Ord b) => gr a b -> gr a (b, b, b);
  augmentGraph g
    = emap (\ i -> (i, 0, i)) (insEdges (getRevEdges (edges g)) g);
   
  updAdjList ::
             (Num b, Ord b) =>
               [((b, b, b), Node)] -> Node -> b -> Bool -> [((b, b, b), Node)];
  updAdjList s v cf fwd
    | fwd == True = ((x, y + cf, z - cf), w) : rs
    | otherwise = ((x, y - cf, z + cf), w) : rs
    where { ((x, y, z), w) = head (filter (\ (_, w') -> v == w') s);
            rs = filter (\ (_, w') -> v /= w') s};
   
  updateFlow ::
             (DynGraph gr, Num b, Ord b) =>
               Path -> b -> gr a (b, b, b) -> gr a (b, b, b);
  updateFlow [] _ g = g;
  updateFlow [_] _ g = g;
  updateFlow (u : v : vs) cf g
    = case match u g of
          { (Nothing, g') -> g';
            (Just (p, u', l, s), g') -> (p', u', l, s') & g2
              where { g2 = updateFlow (v : vs) cf g';
                      s' = updAdjList s v cf True;
                      p' = updAdjList p v cf False}};
   
  mfmg ::
       (DynGraph gr, Num b, Ord b) =>
         gr a (b, b, b) -> Node -> Node -> gr a (b, b, b);
  mfmg g s t
    | augPath == [] = g
    | otherwise = mfmg (updateFlow augPath minC g) s t
    where { minC
              = minimum (map ((\ (_, _, z) -> z) . snd) (tail augLPath));
            augPath = map fst augLPath;
            LP augLPath = lesp s t gf;
            gf = elfilter (\ (_, _, z) -> z /= 0) g};
   
  mf ::
     (DynGraph gr, Num b, Ord b) =>
       gr a b -> Node -> Node -> gr a (b, b, b);
  mf g s t = mfmg (augmentGraph g) s t;
   
  maxFlowgraph ::
               (DynGraph gr, Num b, Ord b) =>
                 gr a b -> Node -> Node -> gr a (b, b);
  maxFlowgraph g s t = emap (\ (u, v, _) -> (v, u)) g2
    where { g2 = elfilter (\ (x, _, _) -> x /= 0) g1;
            g1 = mf g s t};
   
  maxFlow ::
          (DynGraph gr, Num b, Ord b) => gr a b -> Node -> Node -> b;
  maxFlow g s t
    = foldr (+) 0
        (map (\ (_, _, (x, _)) -> x) (out (maxFlowgraph g s t) s))}
