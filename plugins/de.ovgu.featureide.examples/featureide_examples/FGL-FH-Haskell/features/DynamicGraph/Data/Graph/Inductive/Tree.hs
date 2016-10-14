module Data.Graph.Inductive.Tree (Gr, UGr) where
{ import Data.List (foldl');
  import Data.Graph.Inductive.Graph;
  import Data.Graph.Inductive.Internal.FiniteMap;
  import Data.Maybe (fromJust);
   
 
  instance DynGraph Gr where
          { (p, v, l, s) & (Gr g)
              | elemFM g v = error ("Node Exception, Node: " ++ show v)
              | otherwise = Gr g3
              where { g1 = addToFM g v (p, l, s);
                      g2 = updAdj g1 p (addSucc v);
                      g3 = updAdj g2 s (addPred v)}};
  addSucc v l (p, l', s) = (p, l', (l, v) : s);
  addPred v l (p, l', s) = ((l, v) : p, l', s);
  clearSucc v _ (p, l, s) = (p, l, filter ((/= v) . snd) s);
  clearPred v _ (p, l, s) = (filter ((/= v) . snd) p, l, s)
   
}
