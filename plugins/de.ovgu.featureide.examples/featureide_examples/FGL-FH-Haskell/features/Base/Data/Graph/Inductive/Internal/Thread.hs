module Data.Graph.Inductive.Internal.Thread
       (Split, SplitM, Thread, Collect, threadList', threadList,
        threadMaybe', threadMaybe, splitPar, splitParM)
       where
{  
  type Split t i r = i -> t -> (r, t);
   
  type Thread t i r = (t, Split t i r);
   
  type Collect r c = (r -> c -> c, c);
   
  threadList' :: Collect r c -> Split t i r -> [i] -> t -> (c, t);
  threadList' (_, c) _ [] t = (c, t);
  threadList' (f, c) split (i : is) t
    = threadList' (f, f r c) split is t'
    where { (r, t') = split i t};
   
  threadList :: Collect r c -> Split t i r -> [i] -> t -> (c, t);
  threadList (_, c) _ [] t = (c, t);
  threadList (f, c) split (i : is) t = (f r c', t'')
    where { (r, t') = split i t;
            (c', t'') = threadList (f, c) split is t'};
   
  type SplitM t i r = Split t i (Maybe r);
   
  threadMaybe' ::
                 (r -> a) ->
                   Split t i r -> Split t j (Maybe i) -> Split t j (Maybe a);
  threadMaybe' f cont split j t
    = case mi of
          { Just i -> (Just (f r), t'')
              where { (r, t'') = cont i t'};
            Nothing -> (Nothing, t')}
    where { (mi, t') = split j t};
   
  threadMaybe ::
                (i -> r -> a) -> Split t i r -> SplitM t j i -> SplitM t j a;
  threadMaybe f cont split j t
    = case mi of
          { Just i -> (Just (f i r), t'')
              where { (r, t'') = cont i t'};
            Nothing -> (Nothing, t')}
    where { (mi, t') = split j t};
   
  splitPar ::
             Split t i r -> Split u j s -> Split (t, u) (i, j) (r, s);
  splitPar split split' (i, j) (t, u) = ((r, s), (t', u'))
    where { (r, t') = split i t;
            (s, u') = split' j u};
   
  splitParM ::
              SplitM t i r -> Split u j s -> SplitM (t, u) (i, j) (r, s);
  splitParM splitm split (i, j) (t, u)
    = case mr of
          { Just r -> (Just (r, s), (t', u'));
            Nothing -> (Nothing, (t', u))}
    where { (mr, t') = splitm i t;
            (s, u') = split j u}}
