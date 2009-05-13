//NoAbstractFeatures

FM_Core : [FM_UI] [Core] :: _FM_Core ;

FM_UI : [UI] :: _FM_UI ;

UI : AheadUI :: _UI ;

AheadUI : [JakRefactoring] :: _AheadUI ;

Core : [AheadCore] [FeatureCppCore] [FeatureHouseCore] :: _Core ;

%%

UI implies Core ;

