lexer grammar InternalDJ;
@header {
package org.xtext.example.parser.antlr.internal;

// Hack: Use our own Lexer superclass by means of import. 
// Currently there is no other way to specify the superclass for the lexer.
import org.eclipse.xtext.parser.antlr.Lexer;
}

T12 : 'import' ;
T13 : 'features' ;
T14 : ',' ;
T15 : 'configurations' ;
T16 : 'core' ;
T17 : 'delta' ;
T18 : '{' ;
T19 : '}' ;
T20 : 'class' ;
T21 : 'extends' ;
T22 : '(' ;
T23 : ')' ;
T24 : 'super' ;
T25 : ';' ;
T26 : 'this' ;
T27 : '.' ;
T28 : '=' ;
T29 : 'return' ;
T30 : 'after' ;
T31 : 'when' ;
T32 : '&&' ;
T33 : '||' ;
T34 : '->' ;
T35 : '<->' ;
T36 : '!' ;
T37 : 'modifies' ;
T38 : 'adds' ;
T39 : 'remove' ;
T40 : 'extending' ;
T41 : 'void' ;
T42 : 'int' ;
T43 : 'boolean' ;
T44 : '<' ;
T45 : '>' ;
T46 : 'new' ;
T47 : 'original' ;
T48 : 'null' ;

// $ANTLR src "../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g" 4233
RULE_ALL : '**Java:' ( options {greedy=false;} : . )*':Java**';

// $ANTLR src "../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g" 4235
RULE_ID : '^'? ('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'_'|'0'..'9')*;

// $ANTLR src "../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g" 4237
RULE_INT : ('0'..'9')+;

// $ANTLR src "../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g" 4239
RULE_STRING : ('"' ('\\' ('b'|'t'|'n'|'f'|'r'|'"'|'\''|'\\')|~(('\\'|'"')))* '"'|'\'' ('\\' ('b'|'t'|'n'|'f'|'r'|'"'|'\''|'\\')|~(('\\'|'\'')))* '\'');

// $ANTLR src "../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g" 4241
RULE_ML_COMMENT : '/*' ( options {greedy=false;} : . )*'*/';

// $ANTLR src "../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g" 4243
RULE_SL_COMMENT : '//' ~(('\n'|'\r'))* ('\r'? '\n')?;

// $ANTLR src "../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g" 4245
RULE_WS : (' '|'\t'|'\r'|'\n')+;

// $ANTLR src "../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g" 4247
RULE_ANY_OTHER : .;


