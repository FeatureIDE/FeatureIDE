module Data.Graph.Inductive.Graph
       (DynGraph(..), gmap, nmap, emap, insNode, insEdge, delEdge, delLEdge,
        insNodes, insEdges, delEdges, buildGr)
       where
{ import Data.List (sortBy);
  
  class (Graph gr) => DynGraph gr where
          {  
            (&) :: Context a b -> gr a b -> gr a b};
   
  gmap ::
       (DynGraph gr) => (Context a b -> Context c d) -> gr a b -> gr c d;
  gmap f = ufold (\ c -> (f c &)) empty;
   
  nmap :: (DynGraph gr) => (a -> c) -> gr a b -> gr c b;
  nmap f = gmap (\ (p, v, l, s) -> (p, v, f l, s));
   
  emap :: (DynGraph gr) => (b -> c) -> gr a b -> gr a c;
  emap f = gmap (\ (p, v, l, s) -> (map1 f p, v, l, map1 f s))
    where { map1 g = map (\ (l, v) -> (g l, v))};
   
  insNode :: (DynGraph gr) => LNode a -> gr a b -> gr a b;
  insNode (v, l) = (([], v, l, []) &);
   
  insEdge :: (DynGraph gr) => LEdge b -> gr a b -> gr a b;
  insEdge (v, w, l) g = (pr, v, la, (l, w) : su) & g'
    where { (Just (pr, _, la, su), g') = match v g};
   
  delEdge :: (DynGraph gr) => Edge -> gr a b -> gr a b;
  delEdge (v, w) g
    = case match v g of
          { (Nothing, _) -> g;
            (Just (p, v', l, s), g')
              -> (p, v', l, filter ((/= w) . snd) s) & g'};
   
  delLEdge :: (DynGraph gr, Eq b) => LEdge b -> gr a b -> gr a b;
  delLEdge (v, w, b) g
    = case match v g of
          { (Nothing, _) -> g;
            (Just (p, v', l, s), g')
              -> (p, v', l, filter (\ (x, n) -> x /= b || n /= w) s) & g'};
   
  insNodes :: (DynGraph gr) => [LNode a] -> gr a b -> gr a b;
  insNodes vs g = foldr insNode g vs;
   
  insEdges :: (DynGraph gr) => [LEdge b] -> gr a b -> gr a b;
  insEdges es g = foldr insEdge g es;
   
  delEdges :: (DynGraph gr) => [Edge] -> gr a b -> gr a b;
  delEdges es g = foldr delEdge g es;
   
  buildGr :: (DynGraph gr) => [Context a b] -> gr a b;
  buildGr = foldr (&) empty
 }
