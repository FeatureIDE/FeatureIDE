//* GPL domain model February 2005 */

// grammar

GPL : Driver Alg+ [Src] Wgt Gtp :: MainGpl ;

Gtp : Directed | Undirected ;

Wgt : Weighted | Unweighted ;

Src : BFS | DFS ;

Alg : Number | Connected | Transpose StronglyConnected :: StrongConnect
    | Cycle | MSTPrim | MSTKruskal | ShortestPath ;

Driver : Prog Benchmark :: DriverProg ;

%% // constraints

Number implies Gtp and Src ;
Connected implies Undirected and Src;
StrongConnect implies Directed and DFS ;
Cycle implies Gtp and DFS;
MSTKruskal or MSTPrim implies Undirected and Weighted ;
MSTKruskal or MSTPrim implies not (MSTKruskal and MSTPrim) ;
ShortestPath implies Directed and Weighted ;

## // formatting

Driver { hidden }
ShortestPath { out="Shortest" }
Unweighted { out="" }

