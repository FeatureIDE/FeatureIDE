module Data.Graph.Inductive.Monad
       (GraphM(..), ufoldM, nodesM, edgesM, newNodesM, delNodeM,
        delNodesM, mkUGraphM, contextM, labM)
       where
{ import Data.Graph.Inductive.Graph;
   
  class (Monad m) => GraphM m gr where
          {  
            emptyM :: m (gr a b);
             
            isEmptyM :: m (gr a b) -> m Bool;
             
            matchM :: Node -> m (gr a b) -> m (Decomp gr a b);
             
            mkGraphM :: [LNode a] -> [LEdge b] -> m (gr a b);
             
            labNodesM :: m (gr a b) -> m [LNode a];
             
            matchAnyM :: m (gr a b) -> m (GDecomp gr a b);
             
            noNodesM :: m (gr a b) -> m Int;
             
            nodeRangeM :: m (gr a b) -> m (Node, Node);
             
            labEdgesM :: m (gr a b) -> m [LEdge b];
            matchAnyM g
              = do { vs <- labNodesM g;
                     case vs of
                         { [] -> error "Match Exception, Empty Graph";
                           (v, _) : _
                             -> do { (Just c, g') <- matchM v g;
                                     return (c, g')}}};
            noNodesM = labNodesM >>. length;
            nodeRangeM g
              = do { vs <- labNodesM g;
                     let { vs' = map fst vs};
                     return (minimum vs', maximum vs')};
            labEdgesM
              = ufoldM (\ (p, v, _, s) -> (((map (i v) p) ++ (map (o v) s)) ++))
                  []
              where { o v = \ (l, w) -> (v, w, l);
                      i v = \ (l, w) -> (w, v, l)}};
   
  (>>.) :: (Monad m) => (m a -> m b) -> (b -> c) -> m a -> m c;
  f >>. g = (>>= return . g) . f;
   
  ufoldM ::
         (GraphM m gr) => (Context a b -> c -> c) -> c -> m (gr a b) -> m c;
  ufoldM f u g
    = do { b <- isEmptyM g;
           if b then return u else
             do { (c, g') <- matchAnyM g;
                  x <- ufoldM f u (return g');
                  return (f c x)}};
   
  nodesM :: (GraphM m gr) => m (gr a b) -> m [Node];
  nodesM = labNodesM >>. map fst;
   
  edgesM :: (GraphM m gr) => m (gr a b) -> m [Edge];
  edgesM = labEdgesM >>. map (\ (v, w, _) -> (v, w));
   
  newNodesM :: (GraphM m gr) => Int -> m (gr a b) -> m [Node];
  newNodesM i g
    = do { (_, n) <- nodeRangeM g;
           return [n + 1 .. n + i]};
   
  delNodeM :: (GraphM m gr) => Node -> m (gr a b) -> m (gr a b);
  delNodeM v = delNodesM [v];
   
  delNodesM :: (GraphM m gr) => [Node] -> m (gr a b) -> m (gr a b);
  delNodesM [] g = g;
  delNodesM (v : vs) g
    = do { (_, g') <- matchM v g;
           delNodesM vs (return g')};
   
  mkUGraphM :: (GraphM m gr) => [Node] -> [Edge] -> m (gr () ());
  mkUGraphM vs es = mkGraphM (labUNodes vs) (labUEdges es);
  labUEdges = map (\ (v, w) -> (v, w, ()));
  labUNodes = map (\ v -> (v, ()));
   
  onMatch ::
          (GraphM m gr) =>
            (Context a b -> c) -> c -> m (gr a b) -> Node -> m c;
  onMatch f u g v
    = do { (x, _) <- matchM v g;
           return
             (case x of
                  { Nothing -> u;
                    Just c -> f c})};
   
  contextM :: (GraphM m gr) => m (gr a b) -> Node -> m (Context a b);
  contextM g v
    = onMatch id (error ("Match Exception, Node: " ++ show v)) g v;
   
  labM :: (GraphM m gr) => m (gr a b) -> Node -> m (Maybe a);
  labM = onMatch (Just . lab') Nothing}
