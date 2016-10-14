module Data.Graph.Inductive.Example
       (e', loop',
        ab', dag4', d1', d3', ucycleM,
        starM, clr508', clr528', kin248', vor')
       where
{ import Data.Graph.Inductive.Monad;
  import Data.Graph.Inductive.Monad.IOArray;
   
  a', b', c', e', loop', ab', abb', dag3' :: IO (SGr Char ());
   
  e3' :: IO (SGr () String);
   
  dag4' :: IO (SGr Int ());
   
  d1', d3' :: IO (SGr Int Int);

  e' = mkGraphM (zip [1 .. 2] "ab") [(1, 2, ())];

  loop' = mkGraphM [(1, 'a')] [(1, 1, ())];
  ab' = mkGraphM (zip [1 .. 2] "ab") [(1, 2, ()), (2, 1, ())];

  dag4'
    = mkGraphM (genLNodes 1 4)
        (labUEdges [(1, 2), (1, 4), (2, 3), (2, 4), (4, 3)]);
  d1' = mkGraphM (genLNodes 1 2) [(1, 2, 1)];
  d3' = mkGraphM (genLNodes 1 3) [(1, 2, 1), (1, 3, 4), (2, 3, 2)];
   
  ucycleM :: (GraphM m gr) => Int -> m (gr () ());
  ucycleM n = mkUGraphM vs (map (\ v -> (v, v `mod` n + 1)) vs)
    where { vs = [1 .. n]};
   
  starM :: (GraphM m gr) => Int -> m (gr () ());
  starM n = mkUGraphM [1 .. n] (map (\ v -> (1, v)) [2 .. n]);
   
  clr479', clr489' :: IO (SGr Char ());
   
  clr486' :: IO (SGr String ());
   
  clr508', clr528' :: IO (SGr Char Int);
   
  kin248' :: IO (SGr Int ());
   
  vor' :: IO (SGr String Int);

  clr508'
    = mkGraphM (genLNodes 'a' 9)
        [(1, 2, 4), (1, 8, 8), (2, 3, 8), (2, 8, 11), (3, 4, 7), (3, 6, 4),
         (3, 9, 2), (4, 5, 9), (4, 6, 14), (5, 6, 10), (6, 7, 2), (7, 8, 1),
         (7, 9, 6), (8, 9, 7)];
  clr528'
    = mkGraphM [(1, 's'), (2, 'u'), (3, 'v'), (4, 'x'), (5, 'y')]
        [(1, 2, 10), (1, 4, 5), (2, 3, 1), (2, 4, 2), (3, 5, 4), (4, 2, 3),
         (4, 3, 9), (4, 5, 2), (5, 1, 7), (5, 3, 6)];
  kin248'
    = mkGraphM (genLNodes 1 10)
        (labUEdges
           [(1, 2), (1, 4), (1, 7), (2, 4), (2, 5), (3, 4), (3, 10), (4, 5),
            (4, 8), (5, 2), (5, 3), (6, 7), (7, 6), (7, 8), (8, 10), (9, 9),
            (9, 10), (10, 8), (10, 9)]);
  vor'
    = mkGraphM
        (zip [1 .. 8] ["A", "B", "C", "H1", "H2", "D", "E", "F"])
        [(1, 4, 3), (2, 3, 3), (2, 4, 3), (4, 2, 4), (4, 6, 2), (5, 2, 5),
         (5, 3, 6), (5, 7, 5), (5, 8, 6), (6, 5, 3), (6, 7, 2), (7, 8, 3),
         (8, 7, 3)]}
