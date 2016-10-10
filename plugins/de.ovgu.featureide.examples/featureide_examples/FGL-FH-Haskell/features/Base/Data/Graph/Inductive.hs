module Data.Graph.Inductive
       (module Data.Graph.Inductive.Graph,
        module Data.Graph.Inductive.Tree,
        module Data.Graph.Inductive.Basic,
        module Data.Graph.Inductive.Query,
        module Data.Graph.Inductive.Graphviz,
        module Data.Graph.Inductive.NodeMap, version)
       where
{ import Data.Graph.Inductive.Graph;
  import Data.Graph.Inductive.Tree;
  import Data.Graph.Inductive.Basic;
  import Data.Graph.Inductive.Query;
  import Data.Graph.Inductive.Graphviz;
  import Data.Graph.Inductive.NodeMap;
   
  version :: IO ();
  version = putStrLn "\nFGL - Functional Graph Library, April 2007"}
