// non-grammar constraints
// annotations

VncViewer : Type Base :: VncViewerMain ;

Type : Opt+ :: Opt_ ;

Opt : MOpt* OptionsFeat :: OptionsMenuFeatures
	| BOpt+ :: BOpt_
	| ClipboardFeat
	| RecordingFeat ;

MOpt : OpEncodingFeat
	| OpCompressionFeat
	| OpJPEGqualityFeat
	| OpCursorShapeFeat
	| OpCopyRectFeat
	| OpRestrictedColorsFeat
	| OpMouse23Feat
	| OpViewFeat
	| OpShareFeat ;

BOpt : AboutButtonFeat
	| AltTabButtonFeat
	| RefreshButtonFeat
	| CtrlAltDelButtonFeat
	| RecordButtonFeat
	| ClipboardButtonFeat
	| OptionsButtonFeat
	| DisconnectButtonFeat ;

%%
RecordButtonFeat implies RecordingFeat;
OptionsButtonFeat implies OptionsFeat;
ClipboardButtonFeat implies ClipboardFeat;

##
Type { disp="TightVNC" }
Opt { disp="Options" }
MOpt { disp="Menu Option" }
BOpt { disp="Button Option" }
OpSubFeat { disp="Hidden" }

