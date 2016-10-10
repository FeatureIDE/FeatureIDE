module Data.Graph.Inductive.Basic
       (gsel, gfold, hasLoop,
        isSimple, postorder, postorderF, preorder, preorderF)
       where
{ import Data.Graph.Inductive.Graph;
  import Data.Graph.Inductive.Internal.Thread (threadMaybe,
                                               threadList);
  import Data.List (nub);
  import Data.Tree;
   
 
  gsel ::
       (Graph gr) => (Context a b -> Bool) -> gr a b -> [Context a b];
  gsel p = ufold (\ c cs -> if p c then c : cs else cs) [];
   
  hasLoop :: (Graph gr) => gr a b -> Bool;
  hasLoop = not . null . (gsel (\ c -> (node' c `elem` suc' c)));
   
  isSimple :: (Graph gr) => gr a b -> Bool;
  isSimple = not . hasLoop;
  threadGraph f c = threadMaybe f c match;
  gfold1 f d b = threadGraph d (\ c -> gfoldn f d b (f c));
  gfoldn f d b = threadList b (gfold1 f d b);
   
  gfold ::
        (Graph gr) =>
          (Context a b -> [Node]) ->
            (Context a b -> c -> d) ->
              (Maybe d -> c -> c, c) -> [Node] -> gr a b -> c;
  gfold f d b l g = fst (gfoldn f d b l g);
   
  postorder :: Tree a -> [a];
  postorder (Node v ts) = postorderF ts ++ [v];
   
  postorderF :: [Tree a] -> [a];
  postorderF = concatMap postorder;
   
  preorder :: Tree a -> [a];
  preorder = flatten;
   
  preorderF :: [Tree a] -> [a];
  preorderF = concatMap preorder}
