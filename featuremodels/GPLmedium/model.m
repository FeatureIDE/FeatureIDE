//* GPL domain model March 2006 */
// grammar of feature model
// implementation constraints 
// domain constraints
// formatting

GPL : TestProg Alg+ [Src] HiddenWgt Wgt HiddenGtp Gtp Implementation Base :: MainGpl ;

Alg : Number
	| Connected
	| Transpose StronglyConnected :: StrongC
	| Cycle
	| MSTPrim
	| MSTKruskal ;

Src : BFS
	| DFS ;

HiddenWgt : [WeightedWithEdges] [WeightedWithNeighbors] [WeightedOnlyVertices] :: WeightOptions ;

Wgt : Weighted
	| Unweighted ;

HiddenGtp : DirectedWithEdges
	| DirectedWithNeighbors
	| DirectedOnlyVertices
	| UndirectedWithEdges
	| UndirectedWithNeighbors
	| UndirectedOnlyVertices ;

Gtp : Directed
	| Undirected ;

Implementation : OnlyVertices
	| WithNeighbors
	| WithEdges ;

%%
Number implies Gtp and Src ;
Connected implies Undirected and Src;
StrongC implies Directed and DFS ;
Cycle implies Gtp and DFS;
MSTKruskal or MSTPrim implies Undirected and Weighted ;
MSTKruskal or MSTPrim implies not (MSTKruskal and MSTPrim) ;



OnlyVertices and Weighted implies WeightedOnlyVertices;
WithNeighbors and Weighted implies WeightedWithNeighbors;
WithEdges and Weighted implies WeightedWithEdges;
OnlyVertices and Directed implies DirectedOnlyVertices;
WithNeighbors and Directed implies DirectedWithNeighbors;
WithEdges and Directed implies DirectedWithEdges;
OnlyVertices and Undirected implies UndirectedOnlyVertices;
WithNeighbors and Undirected implies UndirectedWithNeighbors;
WithEdges and Undirected implies UndirectedWithEdges;

##
HiddenGtp { hidden }
HiddenWgt { hidden }

