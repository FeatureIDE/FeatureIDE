module Data.Graph.Inductive.Basic
       (grev, undir, unlab, efilter, elfilter)
       where
{ import Data.Graph.Inductive.Graph;
  import Data.Graph.Inductive.Internal.Thread (threadMaybe,
                                               threadList);
  import Data.List (nub);
  import Data.Tree;
   
  grev :: (DynGraph gr) => gr a b -> gr a b;
  grev = gmap (\ (p, v, l, s) -> (s, v, l, p));
   
  undir :: (Eq b, DynGraph gr) => gr a b -> gr a b;
  undir
    = gmap
        (\ (p, v, l, s) -> let { ps = nub (p ++ s)} in (ps, v, l, ps));
   
  unlab :: (DynGraph gr) => gr a b -> gr () ();
  unlab = gmap (\ (p, v, _, s) -> (unlabAdj p, v, (), unlabAdj s))
    where { unlabAdj = map (\ (_, v) -> ((), v))};
   
  efilter :: (DynGraph gr) => (LEdge b -> Bool) -> gr a b -> gr a b;
  efilter f = ufold cfilter empty
    where { cfilter (p, v, l, s) g = (p', v, l, s') & g
              where { p' = filter (\ (b, u) -> f (u, v, b)) p;
                      s' = filter (\ (b, w) -> f (v, w, b)) s}};
   
  elfilter :: (DynGraph gr) => (b -> Bool) -> gr a b -> gr a b;
  elfilter f = efilter (\ (_, _, b) -> f b)
}
