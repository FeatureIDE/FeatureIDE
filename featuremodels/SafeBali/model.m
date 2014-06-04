
Bali : Tool codegen Base :: _Bali ;

Tool : [requireBali2jak] bali2jak :: A
	| [requireBali2jcc] bali2jcc :: B
	| [requireComposer] composer :: C
	| bali2layerGUI bali2layer bali2layerOptions :: D ;

Base : [require] [requireSyntax] collect visitor bali syntax kernel :: _Base ;





