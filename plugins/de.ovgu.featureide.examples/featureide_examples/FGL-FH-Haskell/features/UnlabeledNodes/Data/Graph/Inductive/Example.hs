module Data.Graph.Inductive.Example
       (genUNodes, e3)
       where
{ import Data.Graph.Inductive;
  import Data.Graph.Inductive.Tree;
   
  genUNodes :: Int -> [UNode];
  genUNodes n = zip [1 .. n] (repeat ());
   
  e3 = mkGraph (genUNodes 2) [(1, 2, "a"), (1, 2, "b"), (1, 2, "a")]
}
