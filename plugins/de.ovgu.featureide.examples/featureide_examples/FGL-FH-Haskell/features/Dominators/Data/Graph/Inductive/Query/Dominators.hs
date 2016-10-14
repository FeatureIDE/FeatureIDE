module Data.Graph.Inductive.Query.Dominators (dom, iDom) where
{ import Data.Graph.Inductive.Graph;
  import Data.Graph.Inductive.Query.DFS;
  import Data.Tree (Tree(..));
  import qualified Data.Tree as T;
  import Data.Array;
  import Data.IntMap (IntMap);
  import qualified Data.IntMap as I;
   
  iDom :: (Graph gr) => gr a b -> Node -> [(Node, Node)];
  iDom g root
    = let { (result, toNode, _) = idomWork g root} in
        map (\ (a, b) -> (toNode ! a, toNode ! b)) (assocs result);
   
  dom :: (Graph gr) => gr a b -> Node -> [(Node, [Node])];
  dom g root
    = let { (iDom, toNode, fromNode) = idomWork g root;
            dom' = getDom toNode iDom;
            nodes' = nodes g;
            rest = I.keys (I.filter (- 1 ==) fromNode)}
        in
        [(toNode ! i, dom' ! i) | i <- range (bounds dom')] ++
          [(n, nodes') | n <- rest];
   
  type Node' = Int;
   
  type IDom = Array Node' Node';
   
  type Preds = Array Node' [Node'];
   
  type ToNode = Array Node' Node;
   
  type FromNode = IntMap Node';
   
  idomWork ::
           (Graph gr) => gr a b -> Node -> (IDom, ToNode, FromNode);
  idomWork g root
    = let { trees@(~[tree]) = dff [root] g;
            (s, ntree) = numberTree 0 tree;
            iDom0 = array (1, s - 1) (tail $ treeEdges (- 1) ntree);
            fromNode
              = I.unionWith const
                  (I.fromList (zip (T.flatten tree) (T.flatten ntree)))
                  (I.fromList (zip (nodes g) (repeat (- 1))));
            toNode = array (0, s - 1) (zip (T.flatten ntree) (T.flatten tree));
            preds
              = array (1, s - 1)
                  [(i, filter (/= - 1) (map (fromNode I.!) (pre g (toNode ! i)))) |
                   i <- [1 .. s - 1]];
            iDom = fixEq (refineIDom preds) iDom0}
        in
        if null trees then error "Dominators.idomWork: root not in graph"
          else (iDom, toNode, fromNode);
   
  refineIDom :: Preds -> IDom -> IDom;
  refineIDom preds iDom = fmap (foldl1 (intersect iDom)) preds;
   
  intersect :: IDom -> Node' -> Node' -> Node';
  intersect iDom a b
    = case a `compare` b of
          { LT -> intersect iDom a (iDom ! b);
            EQ -> a;
            GT -> intersect iDom (iDom ! a) b};
   
  getDom :: ToNode -> IDom -> Array Node' [Node];
  getDom toNode iDom
    = let { res
              = array (0, snd (bounds iDom))
                  ((0, [toNode ! 0]) :
                     [(i, toNode ! i : res ! (iDom ! i)) | i <- range (bounds iDom)])}
        in res;
   
  numberTree :: Node' -> Tree a -> (Node', Tree Node');
  numberTree n (Node _ ts)
    = let { (n', ts') = numberForest (n + 1) ts} in (n', Node n ts');
   
  numberForest :: Node' -> [Tree a] -> (Node', [Tree Node']);
  numberForest n [] = (n, []);
  numberForest n (t : ts)
    = let { (n', t') = numberTree n t;
            (n'', ts') = numberForest n' ts}
        in (n'', t' : ts');
   
  treeEdges :: a -> Tree a -> [(a, a)];
  treeEdges a (Node b ts) = (b, a) : concatMap (treeEdges b) ts;
   
  fixEq :: (Eq a) => (a -> a) -> a -> a;
  fixEq f v
    | v' == v = v
    | otherwise = fixEq f v'
    where { v' = f v}}
