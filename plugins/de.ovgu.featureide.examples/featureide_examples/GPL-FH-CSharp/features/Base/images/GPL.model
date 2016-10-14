/* GPL domain model March 2006 */

// grammar of feature model

GPL : TestProg Alg+ Src HiddenWgt Wgt HiddenGtp
      Gtp Implementation Base :: MainGpl ;

Implementation : OnlyVertices | WithNeighbors | WithEdges ;

Gtp : Directed | Undirected ;

HiddenGtp : DirectedWithEdges | DirectedWithNeighbors | DirectedOnlyVertices
          | UndirectedWithEdges  | UndirectedWithNeighbors | UndirectedOnlyVertices ;

Wgt : Weighted | Unweighted ;

HiddenWgt : [WeightedWithEdges] [WeightedWithNeighbors] [WeightedOnlyVertices] :: WeightOptions ;

Src : BFS | DFS ;

Alg : Number | Connected |  StronglyConnected Transpose :: StrongC
    | Cycle | MSTPrim | MSTKruskal ;

%% // domain constraints

Number implies Gtp and Src ;
Connected implies Undirected and Src;
StrongC implies Directed and DFS ;
Cycle implies Gtp and DFS;
MSTKruskal or MSTPrim implies Undirected and Weighted ;
MSTKruskal or MSTPrim implies not (MSTKruskal and MSTPrim) ;
MSTKruskal implies WithEdges ;

// implementation constraints

OnlyVertices and Weighted implies WeightedOnlyVertices;
WithNeighbors and Weighted implies WeightedWithNeighbors;
WithEdges and Weighted implies WeightedWithEdges;
OnlyVertices and Directed implies DirectedOnlyVertices;
WithNeighbors and Directed implies DirectedWithNeighbors;
WithEdges and Directed implies DirectedWithEdges;
OnlyVertices and Undirected implies UndirectedOnlyVertices;
WithNeighbors and Undirected implies UndirectedWithNeighbors;
WithEdges and Undirected implies UndirectedWithEdges;

## // formatting

HiddenGtp { hidden }
HiddenWgt { hidden }
