//* Violet Model File */
// constraints
// formatting

Violet : Additional* Help* [HelpMenu] Window* [WindowMenu] View* [ViewMenu] Edit* [EditMenu] ClassDiagram* [ClassD] SequenceDiagram* [SequenceD] StateDiagram* [StateD] ObjectDiagram* [ObjectD] UseCaseDiagram* [UseCaseD] [DiagramSupport] File* [NewFile] [FileMenu] [Read] [InternalFrame] [FileUtility] [ExtensionFilter] [GraphUtility] [MenuResources] base :: VioletDef ;

Additional : CommandLine | VersionChecker | VioletFilter | ImageFilter | SetTitle | Preferences ;

Help : About | License ;

Window : CloseWindow | RestoreWindow | MaximizeWindow | PreviousWindow | NextWindow ;

View : LookAndFeel | ZoomOut | ZoomIn | GrowDrawingArea | ClipDrawingArea | SmallerGrid | LargerGrid | HideGrid ;

Edit : EditProperties | DeleteItem | SelectNext | SelectPrevious ;

ClassDiagram : ClassNode | InterfaceNode | PackageNode | ClassNoteNode | ClassDependencyEdge | ClassInheritanceEdge | ClassAggregationEdge | ClassAssociationEdge | ClassCompositionEdge | ClassInterfaceEdge | ClassNoteEdge ;

SequenceDiagram : SequenceParameterNode | SequenceCallNode | SequenceNoteNode | SequenceCallEdge | SequenceReturnEdge | SequenceNoteEdge ;

StateDiagram : StateNode | InitialStateNode | FinalStateNode | StateNoteNode | StateTransitionEdge | StateNoteEdge ;

ObjectDiagram : ObjectNode | ObjectFieldNode | ObjectNoteNode | ObjectReferenceEdge | ObjectAssociationEdge | ObjectNoteEdge ;

UseCaseDiagram : Actor | UseCaseNode | UseCaseNoteNode | UseCaseAssociationEdge | ExtendRelationshipEdge | IncludeRelationshipEdge | UseCaseGeneralizationEdge | UseCaseNoteEdge ;

File : Exit | Print | ExportImage | SaveFile | SaveAs | RecentFile | OpenFile ;

%%
File or NewFile or Edit or View or Window or Help or Additional implies MenuResources and GraphUtility and ExtensionFilter and FileUtility and InternalFrame and Read ;
File or NewFile implies FileMenu ;
Edit implies EditMenu ;
View implies ViewMenu ;
Window implies WindowMenu ;
Help implies HelpMenu ;
ClassDiagram or SequenceDiagram or StateDiagram or ObjectDiagram or UseCaseDiagram implies DiagramSupport and NewFile ;
ClassDiagram implies ClassD ;
SequenceDiagram implies SequenceD ;
StateDiagram implies StateD ;
ObjectDiagram implies ObjectD ;
UseCaseDiagram implies UseCaseD ;
RecentFile implies OpenFile;
SaveFile implies SaveAs ;
ImageFilter implies ExtensionFilter and ExportImage ;
VioletFilter implies ExtensionFilter ; 
CommandLine implies OpenFile;
ClassDependencyEdge or ClassInheritanceEdge or ClassAggregationEdge or ClassAssociationEdge or ClassCompositionEdge or ClassInterfaceEdge implies ClassNode ;
ClassNoteEdge implies ClassNoteNode ;
SequenceCallEdge or SequenceReturnEdge implies SequenceCallNode ;
SequenceNoteEdge implies SequenceNoteNode ;
StateTransitionEdge implies StateNode ;
StateNoteEdge implies StateNoteNode ;
ObjectReferenceEdge or ObjectAssociationEdge implies ObjectNode ;
ObjectNoteEdge implies ObjectNoteNode ;
UseCaseAssociationEdge or ExtendRelationshipEdge or IncludeRelationshipEdge or UseCaseGeneralizationEdge implies Actor ;
UseCaseNoteEdge implies UseCaseNoteNode ;

##
FileMenu {hidden}
EditMenu {hidden}
ViewMenu {hidden}
WindowMenu {hidden}
HelpMenu {hidden}
ClassD {hidden}
SequenceD {hidden}
StateD {hidden}
ObjectD {hidden}
UseCaseD {hidden}
MenuResources {hidden}
GraphUtility {hidden}
ExtensionFilter {hidden}
FileUtility {hidden}
InternalFrame {hidden}
Read {hidden}
DiagramSupport {hidden}
NewFile {hidden}
Exit {out="ExitV"}
ClassD {out="ClassDiagram"}
SequenceD {out="SequenceDiagram"}
StateD {out="StateDiagram"}
ObjectD {out="ObjectDiagram"}
UseCaseD {out="UseCaseDiagram"}
ImageFilter {out="ExportFilter"}
SequenceParameterNode {out="SequenceImplicitParameterNode"}
Actor {out="UseCaseActorNode"}
ExtendRelationshipEdge {out="UseCaseExtendRelationEdge"}
IncludeRelationshipEdge {out="UseCaseIncludeRelationEdge"}

