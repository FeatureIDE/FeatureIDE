module Main where
{ import Data.Graph.Inductive;
  import Data.Graph.Inductive.Example;
   
  main :: IO ();
  main = return ();
  
  myTleer :: Gr String String;
  myTleer = empty;
   
  myT1 :: Gr String String;
  myT1 = mkGraph [(1,"Eins"),(2,"Zwei"),(3,"Drei")] [(1,2,"Kante1"),(3,1,"Kante2")];
  
  myT2 :: Gr String String;
  myT2 = mkGraph [(1,"Eins"),(2,"Zwei"),(3,"Drei"),(4,"Vier")] [(1,2,"12"),(3,1,"31"),(2,4,"24"),(4,1,"41"),(3,2,"32")];  
  
  myFunk :: Context a b -> Int -> Int; 
  myFunk (_,x,_,_) y = x + y ;-- zur Verwendung mit ufold; addiert alle Knoten
  
  myT3 :: Gr Char ();
  myT3 = mkGraph (genLNodes 'a' 5) (labUEdges [(1,2),(2,3),(3,4),(4,5),(5,2),(3,1)])
  
}