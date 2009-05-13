// GPL domain

Gpl : Alg+ [Search] [SearchCommon] [WeightReal] [Weight] GraphTypeReal GraphType Implementation Test :: MainGpl ;

Alg : [dProgdNumber] Number :: Num
	| [dProgdConnected] Connected :: Conn
	| [dProgdStronglyConnected] StronglyConnected [Transpose] :: StrongC
	| [dProgdCycle] Cycle :: Cyc
	| [dProgdMstPrim] MstPrim [MstPrimPrepGR] [MstPrimPrepGnR] :: MPrim
	| [dProgdMstKruskal] MstKruskal [MstKruskalPrepGR] [MstKruskalPrepGnR] :: MKrus
	| Shortest ;

Search : DFS
	| BFS ;

WeightReal : WeightedGR
	| WeightedGNR
	| WeightedGENR ;

Weight : [dProgdWeightedCommon] Weighted [WeightedCommon] :: Wgt
	| UnWeighted ;

GraphTypeReal : Dir DirectedCommon :: DirType
	| Undir UndirectedCommon :: UndirType ;

Dir : DirectedGR
	| DirectedGnR
	| DirectedGenR ;

Undir : UndirectedGR
	| UndirectedGNR
	| UndirectedGENR ;

GraphType : Directed
	| Undirected ;

Implementation : NoEdges
	| OnlyNeighbors
	| Edges ;

Test : [Prog] [Benchmark] Base :: StartHere ;

%%
Number implies GraphType and Search;
Connected implies Undirected and Search;
StronglyConnected implies Directed and DFS and Transpose;
Cycle implies GraphType and DFS;
MstKruskal or MstPrim implies Undirected and Weighted;
Shortest implies Directed and Weighted;
MstKruskal or MstPrim implies not (MstKruskal and MstPrim);

Directed and NoEdges implies DirectedGR;
Directed and OnlyNeighbors implies DirectedGnR;
Directed and Edges implies DirectedGenR;
Undirected and NoEdges implies UndirectedGR;
Undirected and OnlyNeighbors implies UndirectedGNR;
Undirected and Edges implies UndirectedGENR;

Weighted implies WeightedCommon;
Weighted and NoEdges implies WeightedGR;
Weighted and OnlyNeighbors implies WeightedGNR;
Weighted and Edges implies WeightedGENR;

Prog implies Benchmark;
Prog and Weighted implies dProgdWeightedCommon;
Prog and Number implies dProgdNumber;
Prog and Connected implies dProgdConnected;
Prog and StronglyConnected implies dProgdStronglyConnected;
Prog and Cycle implies dProgdCycle;
Prog and MstPrim implies dProgdMstPrim;
MstPrim and NoEdges implies MstPrimPrepGR;
MstPrim and OnlyNeighbors implies MstPrimPrepGnR;
Prog and MstPrim implies dProgdMstPrim;
Prog and MstKruskal implies dProgdMstKruskal;
MstKruskal and NoEdges implies MstKruskalPrepGR;
MstKruskal and OnlyNeighbors implies MstKruskalPrepGnR;
Search implies SearchCommon;
Prog implies Benchmark;

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
dProgdMstKruskal { hidden }
dProgdMstPrim { hidden }
dProgdStronglyConnected { hidden }
dProgdConnected { hidden }
dProgdWeightedCommon { hidden }
MstPrimPrepGR { hidden }
MstKruskalPrepGR { hidden }
MstKruskalPrepGnR { hidden }
MstPrimPrepGnR { hidden }
Num { disp="Number" }
Conn { disp="Connected" }
StrongC { disp="StronglyConnected" }
Cyc { disp="Cycle" }
MPrim { disp="MstPrim" }
MKrus { disp="MstKruskal" }
Wgt { disp="Weighted" }
Prog { disp="Program" }

