module Data.Graph.Inductive.Example
       (genLNodes, a, e, loop, ab,
        cyc3, g3, g3b, d1, d3, ucycle, star, clr508, clr528, clr595, gr1, vor)
       where
{ import Data.Graph.Inductive;
  import Data.Graph.Inductive.Tree;
   
  genLNodes :: (Enum a) => a -> Int -> [LNode a];
  genLNodes q i = take i (zip [1 ..] [q ..]);
   
  a, b, c, e, loop, ab, dag3 :: Gr Char ();
   
  e3 :: Gr () String;
   
  cyc3, g3, g3b :: Gr Char String;
   
  dag4 :: Gr Int ();
   
  d1, d3 :: Gr Int Int;
  a = ([], 1, 'a', []) & empty;
  e = ([((), 1)], 2, 'b', []) & a;
 
  loop = ([], 1, 'a', [((), 1)]) & empty;
  ab = ([((), 1)], 2, 'b', [((), 1)]) & a;
  cyc3
    = buildGr
        [([("ca", 3)], 1, 'a', [("ab", 2)]), ([], 2, 'b', [("bc", 3)]),
         ([], 3, 'c', [])];

  d1 = mkGraph (genLNodes 1 2) [(1, 2, 1)];
  d3 = mkGraph (genLNodes 1 3) [(1, 2, 1), (1, 3, 4), (2, 3, 2)];
  g3
    = ([("left", 2), ("up", 3)], 1, 'a', [("right", 2)]) &
        (([], 2, 'b', [("down", 3)]) & (([], 3, 'c', []) & empty));
  g3b
    = ([("down", 2)], 3, 'c', [("up", 1)]) &
        (([("right", 1)], 2, 'b', [("left", 1)]) &
           (([], 1, 'a', []) & empty));

  ucycle :: (Graph gr) => Int -> gr () ();
  ucycle n = mkUGraph vs (map (\ v -> (v, v `mod` n + 1)) vs)
    where { vs = [1 .. n]};
   
  star :: (Graph gr) => Int -> gr () ();
  star n = mkUGraph [1 .. n] (map (\ v -> (1, v)) [2 .. n]);
   
  clr479, clr489 :: Gr Char ();
   
  clr486 :: Gr String ();
   
  clr508, clr528 :: Gr Char Int;
   
  clr595, gr1 :: Gr Int Int;
   
  kin248 :: Gr Int ();
   
  vor :: Gr String Int;
 
  clr508
    = mkGraph (genLNodes 'a' 9)
        [(1, 2, 4), (1, 8, 8), (2, 3, 8), (2, 8, 11), (3, 4, 7), (3, 6, 4),
         (3, 9, 2), (4, 5, 9), (4, 6, 14), (5, 6, 10), (6, 7, 2), (7, 8, 1),
         (7, 9, 6), (8, 9, 7)];
  clr528
    = mkGraph [(1, 's'), (2, 'u'), (3, 'v'), (4, 'x'), (5, 'y')]
        [(1, 2, 10), (1, 4, 5), (2, 3, 1), (2, 4, 2), (3, 5, 4), (4, 2, 3),
         (4, 3, 9), (4, 5, 2), (5, 1, 7), (5, 3, 6)];
  clr595
    = mkGraph (zip [1 .. 6] [1 .. 6])
        [(1, 2, 16), (1, 3, 13), (2, 3, 10), (2, 4, 12), (3, 2, 4),
         (3, 5, 14), (4, 3, 9), (4, 6, 20), (5, 4, 7), (5, 6, 4)];
  gr1
    = mkGraph (zip [1 .. 10] [1 .. 10])
        [(1, 2, 12), (1, 3, 1), (1, 4, 2), (2, 3, 1), (2, 5, 7), (2, 6, 5),
         (3, 6, 1), (3, 7, 7), (4, 3, 3), (4, 6, 2), (4, 7, 5), (5, 3, 2),
         (5, 6, 3), (5, 8, 3), (6, 7, 2), (6, 8, 3), (6, 9, 1), (7, 9, 9),
         (8, 9, 1), (8, 10, 4), (9, 10, 11)];

  vor
    = mkGraph (zip [1 .. 8] ["A", "B", "C", "H1", "H2", "D", "E", "F"])
        [(1, 4, 3), (2, 3, 3), (2, 4, 3), (4, 2, 4), (4, 6, 2), (5, 2, 5),
         (5, 3, 6), (5, 7, 5), (5, 8, 6), (6, 5, 3), (6, 7, 2), (7, 8, 3),
         (8, 7, 3)]
}
