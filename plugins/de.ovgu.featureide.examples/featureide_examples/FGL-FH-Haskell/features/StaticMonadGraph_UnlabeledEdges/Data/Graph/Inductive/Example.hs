module Data.Graph.Inductive.Example
       (abb', dag3', clr479', clr489', clr486')
       where
{  

  a' = mkGraphM [(1, 'a')] noEdges;
  b' = mkGraphM (zip [1 .. 2] "ab") noEdges;
  c' = mkGraphM (zip [1 .. 3] "abc") noEdges;
  abb' = mkGraphM (zip [1 .. 2] "ab") (labUEdges [(2, 2)]);
  dag3' = mkGraphM (zip [1 .. 3] "abc") (labUEdges [(1, 3)]);
  clr479'
    = mkGraphM (genLNodes 'u' 6)
        (labUEdges
           [(1, 2), (1, 4), (2, 5), (3, 5), (3, 6), (4, 2), (5, 4), (6, 6)]);
  clr486'
    = mkGraphM
        (zip [1 .. 9]
           ["shorts", "socks", "watch", "pants", "shoes", "shirt", "belt",
            "tie", "jacket"])
        (labUEdges
           [(1, 4), (1, 5), (2, 5), (4, 5), (4, 7), (6, 7), (6, 8), (7, 9),
            (8, 9)]);
  clr489'
    = mkGraphM (genLNodes 'a' 8)
        (labUEdges
           [(1, 2), (2, 3), (2, 5), (2, 6), (3, 4), (3, 7), (4, 3), (4, 8),
            (5, 1), (5, 6), (6, 7), (7, 6), (7, 8), (8, 8)])
}
