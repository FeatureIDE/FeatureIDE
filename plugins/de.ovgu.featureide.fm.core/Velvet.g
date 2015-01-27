grammar Velvet;

options {
	ASTLabelType = Tree;
	output = AST;
}

tokens {
	MANDATORY		='mandatory';
	ABSTRACT		='abstract';
	SOMEOF			='someOf';
	ONEOF 			='oneOf';
	CONCEPT 		='concept';
	CINTERFACE		='cinterface';
	CONSTRAINT 		='constraint';
	FEATURE 		='feature';
	USE				='use';
	IMPORTINSTANCE	='instance';
	IMPORTINTERFACE	='interface';
	DESCRIPTION		='description';

	VAR_INT 	='int';
	VAR_FLOAT 	='float';
	VAR_STRING 	='string';
	VAR_BOOL 	='bool';

	SEMI		=';';
	START_C 	='{';
	END_C 		='}';
	START_R 	='(';
	END_R 		=')';
	EQ 			='=';
	COMMA 		=',';
	COLON 		=':';
	PLUS 		='+';
	MINUS 		='-';

	OP_NOT	      	='!';
	OP_AND        	='&&'; 
	OP_OR 	      	='||'; 
	OP_XOR	      	='xor'; 
	OP_IMPLIES    	='->';
	OP_EQUIVALENT 	='<->';

	ATTR_OP_EQUALS     ='==';
	ATTR_OP_NOT_EQUALS ='!='; 
	ATTR_OP_GREATER    ='>';
	ATTR_OP_LESS       ='<';
	ATTR_OP_GREATER_EQ ='>='; 
	ATTR_OP_LESS_EQ    ='<=';
	
	EMPTY;
	CONSTR;
	ACONSTR;
	BASEEXT;
	DEF;
	GROUP;
	ATTR;
	UNARYOP;
	OPERAND;
}

@lexer::header {package de.ovgu.featureide.fm.core.io.velvet;}
@header {
package de.ovgu.featureide.fm.core.io.velvet;

import de.ovgu.featureide.fm.core.FMCorePlugin;}

@members {
@Override    
public void emitErrorMessage(String msg) {
	FMCorePlugin.getDefault().logError(new Exception(msg));
}
}

velvetModel
	: (concept|cinterface) EOF
	;
	
concept 
	: CONCEPT ID  
		(COLON conceptBaseExt)? (instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports)? 
		definitions?
	-> ^(CONCEPT ID conceptBaseExt? instanceImports? interfaceImports? definitions?)
	;
	
cinterface : CINTERFACE ID  (COLON conceptBaseExt)? definitions 
	-> ^(CINTERFACE ID conceptBaseExt? definitions)
	;
	
conceptBaseExt
	: ID (COMMA ID)* 
	-> ^(BASEEXT ID+)
	;
	
instanceImports
	: IMPORTINSTANCE ID name (COMMA ID name)* 
	-> ^(IMPORTINSTANCE (ID name)+)
	;
	
interfaceImports
	: IMPORTINTERFACE ID name (COMMA ID name)* 
	-> ^(IMPORTINTERFACE (ID name)+)
	;

name: ID 
	| IDPath
	;
	
definitions
	: START_C definition END_C
	-> ^(DEF definition? EMPTY)
	;

definition 
	: nonFeatureDefinition* (
		(featureGroup nonFeatureDefinition*) | (feature (feature | nonFeatureDefinition)*)
	)?
	;			
	
nonFeatureDefinition
	: constraint
	| use
	| attribute 
	| description
	;
	
use : USE name SEMI
	-> ^(USE name)
	;

feature
	: (MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT)?
	  FEATURE name (definitions | SEMI) 
	-> ^(FEATURE name MANDATORY? ABSTRACT? definitions?)
	;

featureGroup
	: groupType START_C feature+ END_C
	-> ^(GROUP groupType feature+)
	;

groupType
	: SOMEOF 
	| ONEOF 
	;
	
description
	: DESCRIPTION STRING SEMI
	-> ^(DESCRIPTION STRING)
	;
	
constraint
	: CONSTRAINT^ (ID EQ!)? (constraintDefinition | attributeConstraint) SEMI!
	;
	
constraintDefinition
	: constraintOperand (binaryOp constraintOperand)* 
	-> ^(CONSTR constraintOperand+ binaryOp*)
	;
	
constraintOperand : unaryOp* (START_R constraintDefinition END_R | name )
	-> constraintDefinition? ^(UNARYOP unaryOp)* ^(OPERAND name)? 
	;
	
attribute
	: (intAttribute | floatAttribute | stringAttribute | boolAttribute) SEMI
	-> ^(ATTR intAttribute? floatAttribute? stringAttribute? boolAttribute?)
	;
	
attributeConstraint
	: attribConstraint
	-> ^(ACONSTR attribConstraint)
	;

attribConstraint
	: attribNumInstance (attribOperator attribNumInstance)* 
	  attribRelation 
	  attribNumInstance (attribOperator attribNumInstance)*
	;
	
attribOperator
	: PLUS
	| MINUS
	;	
	
attribNumInstance
	: INT 
//	| FLOAT
	| name
	;

intAttribute:		VAR_INT!	name (EQ! INT)?;
floatAttribute:		VAR_FLOAT!	name (EQ! FLOAT)?;
stringAttribute:	VAR_STRING!	name (EQ! STRING)?;
boolAttribute:		VAR_BOOL!	name (EQ! BOOLEAN)?;

unaryOp 
	: OP_NOT
	;
	
binaryOp
	: OP_AND
	| OP_OR
	| OP_XOR
	| OP_IMPLIES
	| OP_EQUIVALENT
	;

attribRelation
	: ATTR_OP_EQUALS
//	| ATTR_OP_NOT_EQUALS
//	| ATTR_OP_GREATER
//	| ATTR_OP_LESS
	| ATTR_OP_GREATER_EQ
	| ATTR_OP_LESS_EQ
	;

BOOLEAN	: 'true' 
	| 'false'
	;
		
ID  :	('a'..'z'|'A'..'Z'|'_'|'-') ('a'..'z'|'A'..'Z'|'0'..'9'|'_'|'-')*
    ;
	
IDPath	: ID ('.' ID)+
	;

INT :	'0'..'9'+
    ;

FLOAT
    :   ('0'..'9')+ '.' ('0'..'9')* EXPONENT?
    |   '.' ('0'..'9')+ EXPONENT?
    |   ('0'..'9')+ EXPONENT
    ;

STRING
    :  '"' ( ESC_SEQ | ~('\\'|'"') )* '"'
    ;

fragment
EXPONENT : ('e'|'E') ('+'|'-')? ('0'..'9')+ ;

fragment
HEX_DIGIT : ('0'..'9'|'a'..'f'|'A'..'F') ;

fragment
ESC_SEQ
    :   '\\' ('b'|'t'|'n'|'f'|'r'|'\"'|'\''|'\\')
    |   UNICODE_ESC
    |   OCTAL_ESC
    ;

fragment
OCTAL_ESC
    :   '\\' ('0'..'3') ('0'..'7') ('0'..'7')
    |   '\\' ('0'..'7') ('0'..'7')
    |   '\\' ('0'..'7')
    ;

fragment
UNICODE_ESC
    :   '\\' 'u' HEX_DIGIT HEX_DIGIT HEX_DIGIT HEX_DIGIT
    ;
     
WS  : ( ' '
    | '\t'
    | '\r'
    | '\n'
    ) {$channel=HIDDEN;}
    ;

SL_COMMENT : ('//' ~('\r'|'\n')*) {skip();};  

ML_COMMENT : ('/*' ~('*/')*) {skip();};

