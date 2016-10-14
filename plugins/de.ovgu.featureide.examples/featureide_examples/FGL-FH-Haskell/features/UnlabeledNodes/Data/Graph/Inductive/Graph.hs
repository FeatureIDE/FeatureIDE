module Data.Graph.Inductive.Graph
       (UNode, UContext, UDecomp, UPath)
       where
{ 
   
  type UNode = LNode ();
   
  type UPath = [UNode];
   
  type UContext = ([Node], Node, [Node]);
   
  type UDecomp g = (Maybe UContext, g)
}
