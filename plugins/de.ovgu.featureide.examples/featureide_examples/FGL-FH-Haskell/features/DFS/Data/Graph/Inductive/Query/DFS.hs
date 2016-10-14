module Data.Graph.Inductive.Query.DFS
       (CFun, dfs, dfs', dff, dff', dfsWith, dfsWith', dffWith, dffWith',
        xdfsWith, xdfWith, xdffWith, udfs, udfs', udff, udff', rdff, rdff',
        rdfs, rdfs', topsort, topsort', scc, reachable, components,
        noComponents, isConnected)
       where
{ import Data.Tree;
  import Data.Graph.Inductive.Graph;
  import Data.Graph.Inductive.Basic;
   
  fixNodes :: (Graph gr) => ([Node] -> gr a b -> c) -> gr a b -> c;
  fixNodes f g = f (nodes g) g;
   
  type CFun a b c = Context a b -> c;
   
  xdfsWith ::
           (Graph gr) =>
             CFun a b [Node] -> CFun a b c -> [Node] -> gr a b -> [c];
  xdfsWith _ _ [] _ = [];
  xdfsWith _ _ _ g | isEmpty g = [];
  xdfsWith d f (v : vs) g
    = case match v g of
          { (Just c, g') -> f c : xdfsWith d f (d c ++ vs) g';
            (Nothing, g') -> xdfsWith d f vs g'};
   
  dfsWith :: (Graph gr) => CFun a b c -> [Node] -> gr a b -> [c];
  dfsWith = xdfsWith suc';
   
  dfsWith' :: (Graph gr) => CFun a b c -> gr a b -> [c];
  dfsWith' f = fixNodes (dfsWith f);
   
  dfs :: (Graph gr) => [Node] -> gr a b -> [Node];
  dfs = dfsWith node';
   
  dfs' :: (Graph gr) => gr a b -> [Node];
  dfs' = dfsWith' node';
   
  udfs :: (Graph gr) => [Node] -> gr a b -> [Node];
  udfs = xdfsWith neighbors' node';
   
  udfs' :: (Graph gr) => gr a b -> [Node];
  udfs' = fixNodes udfs;
   
  rdfs :: (Graph gr) => [Node] -> gr a b -> [Node];
  rdfs = xdfsWith pre' node';
   
  rdfs' :: (Graph gr) => gr a b -> [Node];
  rdfs' = fixNodes rdfs;
   
  xdfWith ::
          (Graph gr) =>
            CFun a b [Node] ->
              CFun a b c -> [Node] -> gr a b -> ([Tree c], gr a b);
  xdfWith _ _ [] g = ([], g);
  xdfWith _ _ _ g | isEmpty g = ([], g);
  xdfWith d f (v : vs) g
    = case match v g of
          { (Nothing, g1) -> xdfWith d f vs g1;
            (Just c, g1) -> (Node (f c) ts : ts', g3)
              where { (ts, g2) = xdfWith d f (d c) g1;
                      (ts', g3) = xdfWith d f vs g2}};
   
  xdffWith ::
           (Graph gr) =>
             CFun a b [Node] -> CFun a b c -> [Node] -> gr a b -> [Tree c];
  xdffWith d f vs g = fst (xdfWith d f vs g);
   
  dffWith ::
          (Graph gr) => CFun a b c -> [Node] -> gr a b -> [Tree c];
  dffWith = xdffWith suc';
   
  dffWith' :: (Graph gr) => CFun a b c -> gr a b -> [Tree c];
  dffWith' f = fixNodes (dffWith f);
   
  dff :: (Graph gr) => [Node] -> gr a b -> [Tree Node];
  dff = dffWith node';
   
  dff' :: (Graph gr) => gr a b -> [Tree Node];
  dff' = dffWith' node';
   
  udff :: (Graph gr) => [Node] -> gr a b -> [Tree Node];
  udff = xdffWith neighbors' node';
   
  udff' :: (Graph gr) => gr a b -> [Tree Node];
  udff' = fixNodes udff;
   
  rdff :: (Graph gr) => [Node] -> gr a b -> [Tree Node];
  rdff = xdffWith pre' node';
   
  rdff' :: (Graph gr) => gr a b -> [Tree Node];
  rdff' = fixNodes rdff;
   
  components :: (Graph gr) => gr a b -> [[Node]];
  components = (map preorder) . udff';
   
  noComponents :: (Graph gr) => gr a b -> Int;
  noComponents = length . components;
   
  isConnected :: (Graph gr) => gr a b -> Bool;
  isConnected = (== 1) . noComponents;
   
  postflatten :: Tree a -> [a];
  postflatten (Node v ts) = postflattenF ts ++ [v];
   
  postflattenF :: [Tree a] -> [a];
  postflattenF = concatMap postflatten;
   
  topsort :: (Graph gr) => gr a b -> [Node];
  topsort = reverse . postflattenF . dff';
   
  topsort' :: (Graph gr) => gr a b -> [a];
  topsort' = reverse . postorderF . (dffWith' lab');
   
  scc :: (Graph gr) => gr a b -> [[Node]];
  scc g = map preorder (rdff (topsort g) g);
   
  reachable :: (Graph gr) => Node -> gr a b -> [Node];
  reachable v g = preorderF (dff [v] g)}
