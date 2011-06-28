module Data.Graph.Inductive.NodeMap
       (NodeMap, new, fromGraph, mkNode, mkNode_, mkNodes, mkNodes_,
        mkEdge, mkEdges, insMapNode, insMapNode_, insMapEdge, delMapNode,
        delMapEdge, insMapNodes, insMapNodes_, insMapEdges, delMapNodes,
        delMapEdges, mkMapGraph, NodeMapM, run, run_, mkNodeM, mkNodesM,
        mkEdgeM, mkEdgesM, insMapNodeM, insMapEdgeM, delMapNodeM,
        delMapEdgeM, insMapNodesM, insMapEdgesM, delMapNodesM,
        delMapEdgesM)
       where
{ import Prelude hiding (map);
  import qualified Prelude as P (map);
  import Control.Monad.State;
  import Data.Graph.Inductive.Graph;
  import Data.Graph.Inductive.Internal.FiniteMap;
   
  data (Ord a) => NodeMap a = NodeMap{map :: FiniteMap a Node,
                                      key :: Int}
                            deriving Show;
   
  new :: (Ord a) => NodeMap a;
  new = NodeMap{map = emptyFM, key = 0};
   
  fromGraph :: (Ord a, Graph g) => g a b -> NodeMap a;
  fromGraph g
    = let { ns = labNodes g;
            aux (n, a) (m', k') = (addToFM m' a n, max n k');
            (m, k) = foldr aux (emptyFM, 0) ns}
        in NodeMap{map = m, key = k + 1};
   
  mkNode :: (Ord a) => NodeMap a -> a -> (LNode a, NodeMap a);
  mkNode m@(NodeMap mp k) a
    = case lookupFM mp a of
          { Just i -> ((i, a), m);
            Nothing
              -> let { m' = NodeMap{map = addToFM mp a k, key = k + 1}} in
                   ((k, a), m')};
   
  mkNode_ :: (Ord a) => NodeMap a -> a -> LNode a;
  mkNode_ m a = fst $ mkNode m a;
   
  mkEdge :: (Ord a) => NodeMap a -> (a, a, b) -> Maybe (LEdge b);
  mkEdge (NodeMap m _) (a1, a2, b)
    = do { n1 <- lookupFM m a1;
           n2 <- lookupFM m a2;
           return (n1, n2, b)};
   
  mkEdges :: (Ord a) => NodeMap a -> [(a, a, b)] -> Maybe [LEdge b];
  mkEdges m es = mapM (mkEdge m) es;
   
  mkNodes :: (Ord a) => NodeMap a -> [a] -> ([LNode a], NodeMap a);
  mkNodes = map' mkNode;
   
  map' :: (a -> b -> (c, a)) -> a -> [b] -> ([c], a);
  map' _ a [] = ([], a);
  map' f a (b : bs)
    = let { (c, a') = f a b;
            (cs, a'') = map' f a' bs}
        in (c : cs, a'');
   
  mkNodes_ :: (Ord a) => NodeMap a -> [a] -> [LNode a];
  mkNodes_ m asx = fst $ mkNodes m asx;
   
  insMapNode ::
             (Ord a, DynGraph g) =>
               NodeMap a -> a -> g a b -> (g a b, NodeMap a, LNode a);
  insMapNode m a g
    = let { (n, m') = mkNode m a} in (insNode n g, m', n);
   
  insMapNode_ ::
              (Ord a, DynGraph g) => NodeMap a -> a -> g a b -> g a b;
  insMapNode_ m a g = let { (g', _, _) = insMapNode m a g} in g';
   
  insMapEdge ::
             (Ord a, DynGraph g) => NodeMap a -> (a, a, b) -> g a b -> g a b;
  insMapEdge m e g = let { (Just e') = mkEdge m e} in insEdge e' g;
   
  delMapNode ::
             (Ord a, DynGraph g) => NodeMap a -> a -> g a b -> g a b;
  delMapNode m a g = let { (n, _) = mkNode_ m a} in delNode n g;
   
  delMapEdge ::
             (Ord a, DynGraph g) => NodeMap a -> (a, a) -> g a b -> g a b;
  delMapEdge m (n1, n2) g
    = let { Just (n1', n2', _) = mkEdge m (n1, n2, ())} in
        delEdge (n1', n2') g;
   
  insMapNodes ::
              (Ord a, DynGraph g) =>
                NodeMap a -> [a] -> g a b -> (g a b, NodeMap a, [LNode a]);
  insMapNodes m asx g
    = let { (ns, m') = mkNodes m asx} in (insNodes ns g, m', ns);
   
  insMapNodes_ ::
               (Ord a, DynGraph g) => NodeMap a -> [a] -> g a b -> g a b;
  insMapNodes_ m asx g = let { (g', _, _) = insMapNodes m asx g} in g';
   
  insMapEdges ::
              (Ord a, DynGraph g) => NodeMap a -> [(a, a, b)] -> g a b -> g a b;
  insMapEdges m es g
    = let { Just es' = mkEdges m es} in insEdges es' g;
   
  delMapNodes ::
              (Ord a, DynGraph g) => NodeMap a -> [a] -> g a b -> g a b;
  delMapNodes m asx g
    = let { ns = P.map fst $ mkNodes_ m asx} in delNodes ns g;
   
  delMapEdges ::
              (Ord a, DynGraph g) => NodeMap a -> [(a, a)] -> g a b -> g a b;
  delMapEdges m ns g
    = let { Just ns' = mkEdges m $ P.map (\ (a, b) -> (a, b, ())) ns;
            ns'' = P.map (\ (a, b, _) -> (a, b)) ns'}
        in delEdges ns'' g;
   
  mkMapGraph ::
             (Ord a, DynGraph g) => [a] -> [(a, a, b)] -> (g a b, NodeMap a);
  mkMapGraph ns es
    = let { (ns', m') = mkNodes new ns;
            Just es' = mkEdges m' es}
        in (mkGraph ns' es', m');
   
  type NodeMapM a b g r = State (NodeMap a, g a b) r;
   
  run ::
      (DynGraph g, Ord a) =>
        g a b -> NodeMapM a b g r -> (r, (NodeMap a, g a b));
  run g m = runState m (fromGraph g, g);
   
  run_ :: (DynGraph g, Ord a) => g a b -> NodeMapM a b g r -> g a b;
  run_ g m = snd . snd $ run g m;
   
  liftN2 ::
         (Ord a, DynGraph g) =>
           (NodeMap a -> c -> (d, NodeMap a)) -> c -> NodeMapM a b g d;
  liftN2 f c
    = do { (m, g) <- get;
           let { (r, m') = f m c};
           put (m', g);
           return r};
   
  liftN2' ::
          (Ord a, DynGraph g) =>
            (NodeMap a -> c -> d) -> c -> NodeMapM a b g d;
  liftN2' f c
    = do { (m, _) <- get;
           return $ f m c};
   
  liftM1 ::
         (Ord a, DynGraph g) =>
           (NodeMap a -> c -> g a b -> g a b) -> c -> NodeMapM a b g ();
  liftM1 f c
    = do { (m, g) <- get;
           let { g' = f m c g};
           put (m, g')};
   
  liftM1' ::
          (Ord a, DynGraph g) =>
            (NodeMap a -> c -> g a b -> (g a b, NodeMap a, d)) ->
              c -> NodeMapM a b g d;
  liftM1' f c
    = do { (m, g) <- get;
           let { (g', m', r) = f m c g};
           put (m', g');
           return r};
   
  mkNodeM :: (Ord a, DynGraph g) => a -> NodeMapM a b g (LNode a);
  mkNodeM = liftN2 mkNode;
   
  mkNodesM :: (Ord a, DynGraph g) => [a] -> NodeMapM a b g [LNode a];
  mkNodesM = liftN2 mkNodes;
   
  mkEdgeM ::
          (Ord a, DynGraph g) =>
            (a, a, b) -> NodeMapM a b g (Maybe (LEdge b));
  mkEdgeM = liftN2' mkEdge;
   
  mkEdgesM ::
           (Ord a, DynGraph g) =>
             [(a, a, b)] -> NodeMapM a b g (Maybe [LEdge b]);
  mkEdgesM = liftN2' mkEdges;
   
  insMapNodeM ::
              (Ord a, DynGraph g) => a -> NodeMapM a b g (LNode a);
  insMapNodeM = liftM1' insMapNode;
   
  insMapEdgeM ::
              (Ord a, DynGraph g) => (a, a, b) -> NodeMapM a b g ();
  insMapEdgeM = liftM1 insMapEdge;
   
  delMapNodeM :: (Ord a, DynGraph g) => a -> NodeMapM a b g ();
  delMapNodeM = liftM1 delMapNode;
   
  delMapEdgeM :: (Ord a, DynGraph g) => (a, a) -> NodeMapM a b g ();
  delMapEdgeM = liftM1 delMapEdge;
   
  insMapNodesM ::
               (Ord a, DynGraph g) => [a] -> NodeMapM a b g [LNode a];
  insMapNodesM = liftM1' insMapNodes;
   
  insMapEdgesM ::
               (Ord a, DynGraph g) => [(a, a, b)] -> NodeMapM a b g ();
  insMapEdgesM = liftM1 insMapEdges;
   
  delMapNodesM :: (Ord a, DynGraph g) => [a] -> NodeMapM a b g ();
  delMapNodesM = liftM1 delMapNodes;
   
  delMapEdgesM ::
               (Ord a, DynGraph g) => [(a, a)] -> NodeMapM a b g ();
  delMapEdgesM = liftM1 delMapEdges}
