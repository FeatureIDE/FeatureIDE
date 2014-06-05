//NoAbstractFeatures

Chat : [Benutzerprofile] Raeume [Archiv] Nachricht :: _Chat ;

Benutzerprofile : [Bild] Rechte [Termine] ID [DefaultFarbe] :: _Benutzerprofile ;

ID : Nickname
	| UserDB
	| Extern ;

Raeume : NonSepare [Separe] :: _Raeume ;

NonSepare : Single
	| Multi ;

Nachricht : [Smiley] [FT] [Rechtschreibung] [Farbe] Verschluesselung* :: _Nachricht ;

Verschluesselung : RSA
	| ROT13
	| Rueckwaerts ;

%%

DefaultFarbe implies Farbe ;

