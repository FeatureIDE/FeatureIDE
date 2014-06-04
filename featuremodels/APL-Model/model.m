
SvgMapApp : [L2Build] Layers Legends USStates Base :: _SvgMapApp ;

Layers : [ColorRegion] [Relief] [Rivers] [Lakes] [PopCircle] :: _Layers ;

Legends : [Controls] [Stats1] [Stats2] [Legend] :: _Legends ;

Controls : [Navigator] [ReliefControls] [RiverControls] [LakeControls] [PopCircleControls] [CoordinateDisplay] :: _Controls ;

Stats1 : [AgeChart] [StatsMedianAge] [EthnicBarChart] [EthnicPieChart] :: _Stats1 ;

Stats2 : [StatsSex] [StatsHouseholds] [StatsPopulation] :: _Stats2 ;

%%
PopCircleControls implies PopCircle;
ReliefControls implies Relief;
RiverControls implies Rivers;
LakeControls implies Lakes;
Controls implies Legend;
Stats1 implies Legend;
Stats2 implies Legend;
L2Build implies not EthnicBarChart;

##
Legend { hidden }   // this turns panel a off
USStates { hidden }   // this turns panel a off
Layers { tab }
Legends { out="" }
Controls { tab }
Stats1 { tab }
Stats2 { tab }

