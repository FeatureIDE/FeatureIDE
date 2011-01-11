lexer grammar InternalDJ;
@header {
package org.xtext.example.ui.contentassist.antlr.internal;

// Hack: Use our own Lexer superclass by means of import. 
// Currently there is no other way to specify the superclass for the lexer.
import org.eclipse.xtext.ui.editor.contentassist.antlr.internal.Lexer;
}

T12 : '&&' ;
T13 : '||' ;
T14 : '->' ;
T15 : '<->' ;
T16 : 'void' ;
T17 : 'int' ;
T18 : 'boolean' ;
T19 : 'import' ;
T20 : 'features' ;
T21 : 'configurations' ;
T22 : ',' ;
T23 : '{' ;
T24 : '}' ;
T25 : 'class' ;
T26 : 'extends' ;
T27 : '(' ;
T28 : ')' ;
T29 : 'super' ;
T30 : ';' ;
T31 : 'this' ;
T32 : '.' ;
T33 : '=' ;
T34 : 'when' ;
T35 : 'after' ;
T36 : 'extending' ;
T37 : 'remove' ;
T38 : 'modifies' ;
T39 : 'adds' ;
T40 : '<' ;
T41 : '>' ;
T42 : 'new' ;
T43 : 'original' ;
T44 : 'core' ;
T45 : 'delta' ;
T46 : 'return' ;
T47 : '!' ;
T48 : 'null' ;

// $ANTLR src "../org.xtext.example.dj.ui/src-gen/org/xtext/example/ui/contentassist/antlr/internal/InternalDJ.g" 10459
RULE_ALL : '**Java:' ( options {greedy=false;} : . )*':Java**';

// $ANTLR src "../org.xtext.example.dj.ui/src-gen/org/xtext/example/ui/contentassist/antlr/internal/InternalDJ.g" 10461
RULE_ID : '^'? ('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'_'|'0'..'9')*;

// $ANTLR src "../org.xtext.example.dj.ui/src-gen/org/xtext/example/ui/contentassist/antlr/internal/InternalDJ.g" 10463
RULE_INT : ('0'..'9')+;

// $ANTLR src "../org.xtext.example.dj.ui/src-gen/org/xtext/example/ui/contentassist/antlr/internal/InternalDJ.g" 10465
RULE_STRING : ('"' ('\\' ('b'|'t'|'n'|'f'|'r'|'"'|'\''|'\\')|~(('\\'|'"')))* '"'|'\'' ('\\' ('b'|'t'|'n'|'f'|'r'|'"'|'\''|'\\')|~(('\\'|'\'')))* '\'');

// $ANTLR src "../org.xtext.example.dj.ui/src-gen/org/xtext/example/ui/contentassist/antlr/internal/InternalDJ.g" 10467
RULE_ML_COMMENT : '/*' ( options {greedy=false;} : . )*'*/';

// $ANTLR src "../org.xtext.example.dj.ui/src-gen/org/xtext/example/ui/contentassist/antlr/internal/InternalDJ.g" 10469
RULE_SL_COMMENT : '//' ~(('\n'|'\r'))* ('\r'? '\n')?;

// $ANTLR src "../org.xtext.example.dj.ui/src-gen/org/xtext/example/ui/contentassist/antlr/internal/InternalDJ.g" 10471
RULE_WS : (' '|'\t'|'\r'|'\n')+;

// $ANTLR src "../org.xtext.example.dj.ui/src-gen/org/xtext/example/ui/contentassist/antlr/internal/InternalDJ.g" 10473
RULE_ANY_OTHER : .;


