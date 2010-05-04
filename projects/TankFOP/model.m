//NoAbstractFeatures

TankWar : Platform Tools* [explodieren] GUI [Record] [Soundeffekt] Language Tanks+ AI :: _TankWar ;

Platform : PC
	| Handy ;

Tools : Beschleunigung
	| einfrieren
	| Bombe
	| Energie
	| Feuerkraft
	| Mars ;

GUI : Map [Image] :: _GUI ;

Map : M_240
	| M_600
	| M_780 ;

Image : [fuer_PC] [fuer_Handy] [IMG_tool] :: _Image ;

Record : Re_fuer_PC
	| Re_fuer_Handy ;

Soundeffekt : Sound_fuer_pc
	| Sound_fuer_Handy ;

Language : EN
	| DE ;

Tanks : USA_M1Abrams
	| Germany_Leopard
	| China_Type99 ;

AI : Easy
	| Hard ;

%%

fuer_PC or Re_fuer_PC or Sound_fuer_pc implies PC ;
fuer_Handy or Re_fuer_Handy or Sound_fuer_Handy implies Handy ;
IMG_tool iff Tools ;
IMG_tool implies fuer_Handy or fuer_PC ;

