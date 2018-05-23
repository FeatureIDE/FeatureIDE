grammar Objective;

tokens {
    SEMICOLON=';';
    NEGATIVE='~';
    ATTRIBUTE='.';
    ATTRIBUTE_SUM='#';
}

@parser::header {
package de.ovgu.featureide.fm.extended.ui.io.objective;

import de.ovgu.featureide.fm.extended.ui.io.constraint.Reference;
import de.ovgu.featureide.fm.extended.ui.io.constraint.ReferenceType;
import de.ovgu.featureide.fm.extended.ui.io.constraint.WeightedTerm; 
}

@lexer::header {
package de.ovgu.featureide.fm.extended.ui.io.objective;
}

@parser::members {
	private boolean error = false;

	@Override
	public void reportError(RecognitionException e) {
		this.error = true;
		//super.reportError(e);
	}

	public boolean hadError() {
		return error;
	}
}

@lexer::members {
	private boolean error = false;

	@Override
	public void reportError(RecognitionException e) {
		this.error = true;
		//super.reportError(e);
	}

	public boolean hadError() {
		return error;
	}
}

objective returns [List<WeightedTerm> value]
@init {
List<WeightedTerm> wTerms = new ArrayList<WeightedTerm>();
}
	: sum[wTerms] SEMICOLON EOF {$value = wTerms;};
	
sum [List<WeightedTerm> wTerms]
	: weightedTermFirst sumTail[wTerms]? {wTerms.add($weightedTermFirst.value);}
	| weightedTerm sumTail[wTerms]? {wTerms.add($weightedTerm.value);};

sumTail [List<WeightedTerm> wTerms]
	: weightedTerm sumTail[wTerms]? {wTerms.add($weightedTerm.value);};

weightedTermFirst returns [WeightedTerm value] 
	: unsigned reference {$value = new WeightedTerm(Integer.parseInt($unsigned.text), true, $reference.value);}
	| reference {$value = new WeightedTerm(1, true, $reference.value);}
	| unsigned NEGATIVE reference {$value = new WeightedTerm(Integer.parseInt($unsigned.text), false, $reference.value);}
	| NEGATIVE reference {$value = new WeightedTerm(1, false, $reference.value);};

weightedTerm returns [WeightedTerm value] 
	: sign unsigned reference {$value = new WeightedTerm($sign.value*Integer.parseInt($unsigned.text), true, $reference.value);}
	| sign reference {$value = new WeightedTerm($sign.value, true, $reference.value);}
	| sign unsigned NEGATIVE reference {$value = new WeightedTerm($sign.value*Integer.parseInt($unsigned.text), false, $reference.value);}
	| sign NEGATIVE reference {$value = new WeightedTerm($sign.value, false, $reference.value);};

reference returns [Reference value]
	: feature {$value = new Reference($feature.value);}
	| feature ATTRIBUTE attribute {$value = new Reference($feature.value, ReferenceType.ATTRIBUTE, $attribute.value);}
	| feature ATTRIBUTE_SUM attribute {$value = new Reference($feature.value, ReferenceType.ATTRIBUTE_SUM, $attribute.value);};

feature returns [String value]
	: IDENTIFIER {$value = $IDENTIFIER.text;};
attribute returns [String value]
	: IDENTIFIER {$value = $IDENTIFIER.text;};

sign returns [int value]
	: '-' {$value = -1;}
	|'+'  {$value = 1;};

unsigned returns [int value]
	: NUMBER {$value = Integer.parseInt($NUMBER.text);};

NUMBER	: '0' | ('1'..'9') ('0'..'9')*;

IDENTIFIER	: ('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'0'..'9'|'_')*;

WS	: (' '|'\t'|'\f'|'\n'|'\r'){ $channel=HIDDEN; };