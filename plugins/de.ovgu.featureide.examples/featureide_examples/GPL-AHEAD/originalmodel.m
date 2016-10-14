Gpl : Test [Implementation] [GraphType] [GraphTypeReal] [Weight] [WeightReal] [SearchCommon] [Search] Alg* :: MainGpl ;

Test : Base [Benchmark] [Prog] :: StartHere ;

Implementation : NoEdges
	| OnlyNeighbors
	| Edges ;

GraphType : Directed
	| Undirected ;

GraphTypeReal : DirectedCommon Dir :: DirType
	| UndirectedCommon Undir :: UndirType ;

Dir : DirectedGR
	| DirectedGnR
	| DirectedGenR ;

Undir : UndirectedGR
	| UndirectedGnR
	| UndirectedGenR ;

Weight : Weighted [WeightedCommon] [dProgdWeightedCommon] :: Wgt
	| UnWeighted ;

WeightReal : WeightedGR
	| WeightedGnR
	| WeightedGenR ;

Search : DFS
	| BFS ;

Alg : Number [dProgdNumber] :: Num
	| Connected [dProgdConnected] :: Conn
	| [Transpose] StronglyConnected [dProgdStronglyConnected] :: StrongC
	| Cycle [dProgdCycle] :: Cyc
	| [MSTPrimPrepGnR] [MSTPrimPrepGR] MSTPrim [dProgdMSTPrim] :: MPrim
	| [MSTKruskalPrepGnR] [MSTKruskalPrepGR] MSTKruskal [dProgdMSTKruskal] :: MKrus
	| Shortest ;

%%

Number implies GraphType and Search ;
Connected implies Undirected and Search ;
StronglyConnected implies Directed and DFS and Transpose ;
Cycle implies GraphType and DFS ;
MSTKruskal or MSTPrim implies Undirected and Weighted ;
Shortest implies Directed and Weighted ;
MSTKruskal or MSTPrim implies not (MSTKruskal and MSTPrim) ;
Directed and NoEdges implies DirectedGR ;
Directed and OnlyNeighbors implies DirectedGnR ;
Directed and Edges implies DirectedGenR ;
Undirected and NoEdges implies UndirectedGR ;
Undirected and OnlyNeighbors implies UndirectedGnR ;
Undirected and Edges implies UndirectedGenR ;
Weighted implies WeightedCommon ;
Weighted and NoEdges implies WeightedGR ;
Weighted and OnlyNeighbors implies WeightedGnR ;
Weighted and Edges implies WeightedGenR ;
Prog implies Benchmark ;
Prog and Weighted implies dProgdWeightedCommon ;
Prog and Number implies dProgdNumber ;
Prog and Connected implies dProgdConnected ;
Prog and StronglyConnected implies dProgdStronglyConnected ;
Prog and Cycle implies dProgdCycle ;
Prog and MSTPrim implies dProgdMSTPrim ;
MSTPrim and NoEdges implies MSTPrimPrepGR ;
MSTPrim and OnlyNeighbors implies MSTPrimPrepGnR ;
Prog and MSTPrim implies dProgdMSTPrim ;
Prog and MSTKruskal implies dProgdMSTKruskal ;
MSTKruskal and NoEdges implies MSTKruskalPrepGR ;
MSTKruskal and OnlyNeighbors implies MSTKruskalPrepGnR ;
Search implies SearchCommon ;
Prog implies Benchmark ;

##
Benchmark { hidden }
SearchCommon { hidden }
Transpose { hidden  }
GraphTypeReal { hidden }
WeightReal { hidden  }
Directed { out="" }
Weighted { out="" }
WeightedCommon { hidden }
UnWeighted { out="" }
Undirected { out="" }
NoEdges { out = "" }
OnlyNeighbors { out = "" }
Edges { out = "" }
dProgdNumber { hidden }
dProgdCycle { hidden }
dProgdMSTKruskal { hidden }
dProgdMSTPrim { hidden }
dProgdStronglyConnected { hidden }
dProgdConnected { hidden }
dProgdWeightedCommon { hidden }
MSTPrimPrepGR { hidden }
MSTKruskalPrepGR { hidden }
MSTKruskalPrepGnR { hidden }
MSTPrimPrepGnR { hidden }
Num { disp="Number" }
Conn { disp="Connected" }
StrongC { disp="StronglyConnected" }
Cyc { disp="Cycle" }
MPrim { disp="MSTPrim" }
MKrus { disp="MSTKruskal" }
Wgt { disp="Weighted" }
Prog { disp="Program" }

