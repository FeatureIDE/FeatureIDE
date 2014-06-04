//NoAbstractFeatures

GraphLibrary : Edges [Algorithms] :: _GraphLibrary ;

Edges : Directed
	| Undirected ;

Directed : [Cycle] :: _Directed ;

Algorithms : [Number] :: _Algorithms ;

%%

(Cycle implies Algorithms) and (Algorithms implies Number or Cycle) ;

