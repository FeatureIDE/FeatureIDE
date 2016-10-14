module Data.Graph.Inductive.Graph
       (Node, LNode, Edge, LEdge, Adj, Context, MContext,
        Decomp, GDecomp, Path, LPath(..), Graph(..), ufold, nodes, edges,
        newNodes, gelem, delNode, delNodes, mkUGraph, context,
        lab, neighbors, suc, pre, lsuc, lpre, out, inn, outdeg, indeg, deg,
        equal, node', lab', labNode', neighbors', suc', pre', lpre', lsuc',
        out', inn', outdeg', indeg', deg')
       where
{ import Data.List (sortBy);
   
  type Node = Int;
   
  type LNode a = (Node, a);
   
  type Edge = (Node, Node);
   
  type LEdge b = (Node, Node, b);
   
  type Path = [Node];
   
  newtype LPath a = LP [LNode a];
   
  instance (Show a) => Show (LPath a) where
          { show (LP xs) = show xs};
   
  type Adj b = [(b, Node)];
   
  type Context a b = (Adj b, Node, a, Adj b);
   
  type MContext a b = Maybe (Context a b);
   
  type Decomp g a b = (MContext a b, g a b);
   
  type GDecomp g a b = (Context a b, g a b);
   
  class Graph gr where
          {  
            empty :: gr a b;
             
            isEmpty :: gr a b -> Bool;
             
            match :: Node -> gr a b -> Decomp gr a b;
             
            mkGraph :: [LNode a] -> [LEdge b] -> gr a b;
             
            labNodes :: gr a b -> [LNode a];
             
            matchAny :: gr a b -> GDecomp gr a b;
             
            noNodes :: gr a b -> Int;
             
            nodeRange :: gr a b -> (Node, Node);
             
            labEdges :: gr a b -> [LEdge b];
            matchAny g
              = case labNodes g of
                    { [] -> error "Match Exception, Empty Graph";
                      (v, _) : _ -> (c, g')
                        where { (Just c, g') = match v g}};
            noNodes = length . labNodes;
            nodeRange g = (minimum vs, maximum vs)
              where { vs = map fst (labNodes g)};
            labEdges
              = ufold (\ (_, v, _, s) -> ((map (\ (l, w) -> (v, w, l)) s) ++))
                  []};
   
  ufold :: (Graph gr) => (Context a b -> c -> c) -> c -> gr a b -> c;
  ufold f u g
    | isEmpty g = u
    | otherwise = f c (ufold f u g')
    where { (c, g') = matchAny g};
   
  nodes :: (Graph gr) => gr a b -> [Node];
  nodes = map fst . labNodes;
   
  edges :: (Graph gr) => gr a b -> [Edge];
  edges = map (\ (v, w, _) -> (v, w)) . labEdges;
   
  newNodes :: (Graph gr) => Int -> gr a b -> [Node];
  newNodes i g = [n + 1 .. n + i]
    where { (_, n) = nodeRange g};
   
  gelem :: (Graph gr) => Node -> gr a b -> Bool;
  gelem v g
    = case match v g of
          { (Just _, _) -> True;
            _ -> False};
   
  delNode :: (Graph gr) => Node -> gr a b -> gr a b;
  delNode v = delNodes [v];

  delNodes :: (Graph gr) => [Node] -> gr a b -> gr a b;
  delNodes [] g = g;
  delNodes (v : vs) g = delNodes vs (snd (match v g));
   
  mkUGraph :: (Graph gr) => [Node] -> [Edge] -> gr () ();
  mkUGraph vs es = mkGraph (labUNodes vs) (labUEdges es)
    where { labUEdges = map (\ (v, w) -> (v, w, ()));
            labUNodes = map (\ v -> (v, ()))};
   
  context :: (Graph gr) => gr a b -> Node -> Context a b;
  context g v
    = case match v g of
          { (Nothing, _) -> error ("Match Exception, Node: " ++ show v);
            (Just c, _) -> c};
   
  lab :: (Graph gr) => gr a b -> Node -> Maybe a;
  lab g v = fst (match v g) >>= return . lab';
   
  neighbors :: (Graph gr) => gr a b -> Node -> [Node];
  neighbors = (\ (p, _, _, s) -> map snd (p ++ s)) .: context;
   
  suc :: (Graph gr) => gr a b -> Node -> [Node];
  suc = map snd .: context4l;
   
  pre :: (Graph gr) => gr a b -> Node -> [Node];
  pre = map snd .: context1l;
   
  lsuc :: (Graph gr) => gr a b -> Node -> [(Node, b)];
  lsuc = map flip2 .: context4l;
   
  lpre :: (Graph gr) => gr a b -> Node -> [(Node, b)];
  lpre = map flip2 .: context1l;
   
  out :: (Graph gr) => gr a b -> Node -> [LEdge b];
  out g v = map (\ (l, w) -> (v, w, l)) (context4l g v);
   
  inn :: (Graph gr) => gr a b -> Node -> [LEdge b];
  inn g v = map (\ (l, w) -> (w, v, l)) (context1l g v);
   
  outdeg :: (Graph gr) => gr a b -> Node -> Int;
  outdeg = length .: context4l;
   
  indeg :: (Graph gr) => gr a b -> Node -> Int;
  indeg = length .: context1l;
   
  deg :: (Graph gr) => gr a b -> Node -> Int;
  deg = (\ (p, _, _, s) -> length p + length s) .: context;
   
  node' :: Context a b -> Node;
  node' (_, v, _, _) = v;
   
  lab' :: Context a b -> a;
  lab' (_, _, l, _) = l;
   
  labNode' :: Context a b -> LNode a;
  labNode' (_, v, l, _) = (v, l);
   
  neighbors' :: Context a b -> [Node];
  neighbors' (p, _, _, s) = map snd p ++ map snd s;
   
  suc' :: Context a b -> [Node];
  suc' = map snd . context4l';
   
  pre' :: Context a b -> [Node];
  pre' = map snd . context1l';
   
  lsuc' :: Context a b -> [(Node, b)];
  lsuc' = map flip2 . context4l';
   
  lpre' :: Context a b -> [(Node, b)];
  lpre' = map flip2 . context1l';
   
  out' :: Context a b -> [LEdge b];
  out' c@(_, v, _, _) = map (\ (l, w) -> (v, w, l)) (context4l' c);
   
  inn' :: Context a b -> [LEdge b];
  inn' c@(_, v, _, _) = map (\ (l, w) -> (w, v, l)) (context1l' c);
   
  outdeg' :: Context a b -> Int;
  outdeg' = length . context4l';
   
  indeg' :: Context a b -> Int;
  indeg' = length . context1l';
   
  deg' :: Context a b -> Int;
  deg' (p, _, _, s) = length p + length s;
   
  nodeComp :: (Eq b) => LNode b -> LNode b -> Ordering;
  nodeComp n@(v, _) n'@(w, _)
    | n == n' = EQ
    | v < w = LT
    | otherwise = GT;
   
  slabNodes :: (Eq a, Graph gr) => gr a b -> [LNode a];
  slabNodes = sortBy nodeComp . labNodes;
   
  edgeComp :: (Eq b) => LEdge b -> LEdge b -> Ordering;
  edgeComp e@(v, w, _) e'@(x, y, _)
    | e == e' = EQ
    | v < x || (v == x && w < y) = LT
    | otherwise = GT;
   
  slabEdges :: (Eq b, Graph gr) => gr a b -> [LEdge b];
  slabEdges = sortBy edgeComp . labEdges;
   
  equal :: (Eq a, Eq b, Graph gr) => gr a b -> gr a b -> Bool;
  equal g g'
    = slabNodes g == slabNodes g' && slabEdges g == slabEdges g';
   
  (.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d;
  (.:) = (.) . (.);
   
  flip2 :: (a, b) -> (b, a);
  flip2 (x, y) = (y, x);
   
  context1l :: (Graph gr) => gr a b -> Node -> Adj b;
  context1l = context1l' .: context;
   
  context4l :: (Graph gr) => gr a b -> Node -> Adj b;
  context4l = context4l' .: context;
   
  context1l' :: Context a b -> Adj b;
  context1l' (p, v, _, s) = p ++ filter ((== v) . snd) s;
   
  context4l' :: Context a b -> Adj b;
  context4l' (p, v, _, s) = s ++ filter ((== v) . snd) p}
