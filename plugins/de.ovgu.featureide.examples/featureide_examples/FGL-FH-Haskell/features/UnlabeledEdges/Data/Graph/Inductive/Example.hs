module Data.Graph.Inductive.Example
       (labUEdges, noEdges, b, c, dag3, dag4, clr479, clr489, clr486, kin248)
       where
{ import Data.Graph.Inductive;
  import Data.Graph.Inductive.Tree;
   
  labUEdges :: [Edge] -> [UEdge];
  labUEdges = map (\ (i, j) -> (i, j, ()));
   
  noEdges :: [UEdge];
  noEdges = [];
   
  b = mkGraph (zip [1 .. 2] "ab") noEdges;
  c = mkGraph (zip [1 .. 3] "abc") noEdges;

  dag3 = mkGraph (zip [1 .. 3] "abc") (labUEdges [(1, 3)]);
  dag4
    = mkGraph (genLNodes 1 4)
        (labUEdges [(1, 2), (1, 4), (2, 3), (2, 4), (4, 3)]);
  clr479
    = mkGraph (genLNodes 'u' 6)
        (labUEdges
           [(1, 2), (1, 4), (2, 5), (3, 5), (3, 6), (4, 2), (5, 4), (6, 6)]);
  clr486
    = mkGraph
        (zip [1 .. 9]
           ["shorts", "socks", "watch", "pants", "shoes", "shirt", "belt",
            "tie", "jacket"])
        (labUEdges
           [(1, 4), (1, 5), (2, 5), (4, 5), (4, 7), (6, 7), (6, 8), (7, 9),
            (8, 9)]);
  clr489
    = mkGraph (genLNodes 'a' 8)
        (labUEdges
           [(1, 2), (2, 3), (2, 5), (2, 6), (3, 4), (3, 7), (4, 3), (4, 8),
            (5, 1), (5, 6), (6, 7), (7, 6), (7, 8), (8, 8)]);

  kin248
    = mkGraph (genLNodes 1 10)
        (labUEdges
           [(1, 2), (1, 4), (1, 7), (2, 4), (2, 5), (3, 4), (3, 10), (4, 5),
            (4, 8), (5, 2), (5, 3), (6, 7), (7, 6), (7, 8), (8, 10), (9, 9),
            (9, 10), (10, 8), (10, 9)])
}
