module Data.Graph.Inductive.Query.TransClos (trc) where
{ import Data.Graph.Inductive.Graph;
  import Data.Graph.Inductive.Query.DFS (reachable);
   
  getNewEdges :: (DynGraph gr) => [LNode a] -> gr a b -> [LEdge ()];
  getNewEdges vs g = concatMap (\ (u, _) -> r u g) vs
    where { r = \ u g' -> map (\ v -> (u, v, ())) (reachable u g')};
   
  trc :: (DynGraph gr) => gr a b -> gr a ();
  trc g = insEdges (getNewEdges ln g) (insNodes ln empty)
    where { ln = labNodes g}}
