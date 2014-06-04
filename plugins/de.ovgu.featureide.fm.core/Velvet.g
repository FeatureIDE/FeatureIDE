grammar Velvet;

options {
	ASTLabelType = Tree;
	output = AST;
}

tokens {
	MANDATORY	='mandatory';
	ABSTRACT	='abstract';
	SOMEOF		='someOf';
	ONEOF 		='oneOf';
	IMPORT 		='import';
	REFINES 	='refines';
	CONCEPT 	='concept';
	CONSTRAINT 	='constraint';
	FEATURE 	='feature';

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

	IMP;
	CONSTR;
	ACONSTR;
	BASEEXT;
	DEF;
	FEAT;
	GROUP;
	INSTANCE;
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
	: imports? concept EOF
	;
	
imports : (IMPORT name SEMI)+
	-> ^(IMP name+)
	;
	
concept : REFINES? CONCEPT ID  (COLON conceptBaseExt)? definitions 
	-> ^(CONCEPT ID REFINES? conceptBaseExt? definitions)
	;
	
conceptBaseExt
	: ID (COMMA ID)* 
	-> ^(BASEEXT ID+)
	;

name: ID 
	| IDPath
	;
	
definitions
	: START_C def END_C
	-> ^(DEF def)
	;

def	: nonFeatureDefinition* (
		(featureGroup nonFeatureDefinition*) |
		(feature (feature | nonFeatureDefinition)*))?
	;			
	
nonFeatureDefinition
	: constraint 
	| instance 
	| attribute 
	;
	
instance: ID name SEMI //conceptName
	-> INSTANCE ID name
	;

feature
	: (MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT)?
	  FEATURE name (definitions | SEMI) 
	-> ^(FEAT name MANDATORY? ABSTRACT? definitions?)
	;

featureGroup
	: groupType START_C feature feature+ END_C
	-> ^(GROUP groupType feature feature+)
	;

groupType
	: SOMEOF 
	| ONEOF 
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

attribute
	: (intAttribute | floatAttribute | stringAttribute | boolAttribute) SEMI
	-> ^(ATTR intAttribute? floatAttribute? stringAttribute? boolAttribute?)
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
	
ID  :	('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'0'..'9'|'_')*
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