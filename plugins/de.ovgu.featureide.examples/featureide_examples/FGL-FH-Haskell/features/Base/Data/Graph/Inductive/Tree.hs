module Data.Graph.Inductive.Tree (Gr, UGr) where
{ import Data.List (foldl');
  import Data.Graph.Inductive.Graph;
  import Data.Graph.Inductive.Internal.FiniteMap;
  import Data.Maybe (fromJust);
   
  data Gr a b = Gr (GraphRep a b);
   
  type GraphRep a b = FiniteMap Node (Context' a b);
   
  type Context' a b = (Adj b, a, Adj b);
   
  type UGr = Gr () ();
   
  showsGraph :: (Show a, Show b) => GraphRep a b -> ShowS;
  showsGraph (Empty) = id;
  showsGraph (Node _ l (v, (_, l', s)) r)
    = showsGraph l . ('\n' :) . shows v . (':' :) . shows l' .
        ("->" ++)
        . shows s
        . showsGraph r;
   
  instance (Show a, Show b) => Show (Gr a b) where
          { showsPrec _ (Gr g) = showsGraph g};
   
  instance Graph Gr where
          { empty = Gr emptyFM;
            isEmpty (Gr g)
              = case g of
                    { Empty -> True;
                      _ -> False};
            match = matchGr;
            mkGraph vs es = (insEdges' . insNodes vs) empty
              where { insEdges' g = foldl' (flip insEdge) g es};
            labNodes (Gr g) = map (\ (v, (_, l, _)) -> (v, l)) (fmToList g);
            matchAny (Gr Empty) = error "Match Exception, Empty Graph";
            matchAny g@(Gr (Node _ _ (v, _) _)) = (c, g')
              where { (Just c, g') = matchGr v g};
            noNodes (Gr g) = sizeFM g;
            nodeRange (Gr Empty) = (0, 0);
            nodeRange (Gr g) = (ix (minFM g), ix (maxFM g))
              where { ix = fst . fromJust};
            labEdges (Gr g)
              = concatMap (\ (v, (_, _, s)) -> map (\ (l, w) -> (v, w, l)) s)
                  (fmToList g)};
  matchGr v (Gr g)
    = case splitFM g v of
          { Nothing -> (Nothing, Gr g);
            Just (g', (_, (p, l, s))) -> (Just (p', v, l, s), Gr g2)
              where { s' = filter ((/= v) . snd) s;
                      p' = filter ((/= v) . snd) p;
                      g1 = updAdj g' s' (clearPred v);
                      g2 = updAdj g1 p' (clearSucc v)}};

   
  updAdj ::
           GraphRep a b ->
             Adj b -> (b -> Context' a b -> Context' a b) -> GraphRep a b;
  updAdj g [] _ = g;
  updAdj g ((l, v) : vs) f
    | elemFM g v = updAdj (updFM g v (f l)) vs f
    | otherwise = error ("Edge Exception, Node: " ++ show v)}
