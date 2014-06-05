//NoAbstractFeatures

GraphLibrary : Edges Algorithms* :: _GraphLibrary ;

Edges : Directed
	| Undirected ;

Algorithms : Number
	| Cycle ;

%%

Cycle implies Directed ;

