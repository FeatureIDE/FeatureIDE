/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
// $ANTLR 3.4 Velvet.g 2012-12-02 13:17:21
package de.ovgu.featureide.fm.core.io.velvet;

import org.antlr.runtime.BaseRecognizer;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.DFA;
import org.antlr.runtime.EarlyExitException;
import org.antlr.runtime.Lexer;
import org.antlr.runtime.MismatchedSetException;
import org.antlr.runtime.NoViableAltException;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.RecognizerSharedState;

@SuppressWarnings({"all", "warnings", "unchecked"})
public class VelvetLexer extends Lexer {
    public static final int EOF=-1;
    public static final int ABSTRACT=4;
    public static final int ACONSTR=5;
    public static final int ATTR=6;
    public static final int ATTR_OP_EQUALS=7;
    public static final int ATTR_OP_GREATER=8;
    public static final int ATTR_OP_GREATER_EQ=9;
    public static final int ATTR_OP_LESS=10;
    public static final int ATTR_OP_LESS_EQ=11;
    public static final int ATTR_OP_NOT_EQUALS=12;
    public static final int BASEEXT=13;
    public static final int BOOLEAN=14;
    public static final int COLON=15;
    public static final int COMMA=16;
    public static final int CONCEPT=17;
    public static final int CONSTR=18;
    public static final int CONSTRAINT=19;
    public static final int DEF=20;
    public static final int END_C=21;
    public static final int END_R=22;
    public static final int EQ=23;
    public static final int ESC_SEQ=24;
    public static final int EXPONENT=25;
    public static final int FEAT=26;
    public static final int FEATURE=27;
    public static final int FLOAT=28;
    public static final int GROUP=29;
    public static final int HEX_DIGIT=30;
    public static final int ID=31;
    public static final int IDPath=32;
    public static final int IMP=33;
    public static final int IMPORT=34;
    public static final int INSTANCE=35;
    public static final int INT=36;
    public static final int MANDATORY=37;
    public static final int MINUS=38;
    public static final int OCTAL_ESC=39;
    public static final int ONEOF=40;
    public static final int OPERAND=41;
    public static final int OP_AND=42;
    public static final int OP_EQUIVALENT=43;
    public static final int OP_IMPLIES=44;
    public static final int OP_NOT=45;
    public static final int OP_OR=46;
    public static final int OP_XOR=47;
    public static final int PLUS=48;
    public static final int REFINES=49;
    public static final int SEMI=50;
    public static final int SOMEOF=51;
    public static final int START_C=52;
    public static final int START_R=53;
    public static final int STRING=54;
    public static final int UNARYOP=55;
    public static final int UNICODE_ESC=56;
    public static final int VAR_BOOL=57;
    public static final int VAR_FLOAT=58;
    public static final int VAR_INT=59;
    public static final int VAR_STRING=60;
    public static final int WS=61;

    // delegates
    // delegators
    public Lexer[] getDelegates() {
        return new Lexer[] {};
    }

    public VelvetLexer() {} 
    public VelvetLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public VelvetLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);
    }
    public String getGrammarFileName() { return "Velvet.g"; }

    // $ANTLR start "ABSTRACT"
    public final void mABSTRACT() throws RecognitionException {
        try {
            int _type = ABSTRACT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:4:10: ( 'abstract' )
            // Velvet.g:4:12: 'abstract'
            {
            match("abstract"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "ABSTRACT"

    // $ANTLR start "ATTR_OP_EQUALS"
    public final void mATTR_OP_EQUALS() throws RecognitionException {
        try {
            int _type = ATTR_OP_EQUALS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:5:16: ( '==' )
            // Velvet.g:5:18: '=='
            {
            match("=="); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "ATTR_OP_EQUALS"

    // $ANTLR start "ATTR_OP_GREATER"
    public final void mATTR_OP_GREATER() throws RecognitionException {
        try {
            int _type = ATTR_OP_GREATER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:6:17: ( '>' )
            // Velvet.g:6:19: '>'
            {
            match('>'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "ATTR_OP_GREATER"

    // $ANTLR start "ATTR_OP_GREATER_EQ"
    public final void mATTR_OP_GREATER_EQ() throws RecognitionException {
        try {
            int _type = ATTR_OP_GREATER_EQ;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:7:20: ( '>=' )
            // Velvet.g:7:22: '>='
            {
            match(">="); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "ATTR_OP_GREATER_EQ"

    // $ANTLR start "ATTR_OP_LESS"
    public final void mATTR_OP_LESS() throws RecognitionException {
        try {
            int _type = ATTR_OP_LESS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:8:14: ( '<' )
            // Velvet.g:8:16: '<'
            {
            match('<'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "ATTR_OP_LESS"

    // $ANTLR start "ATTR_OP_LESS_EQ"
    public final void mATTR_OP_LESS_EQ() throws RecognitionException {
        try {
            int _type = ATTR_OP_LESS_EQ;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:9:17: ( '<=' )
            // Velvet.g:9:19: '<='
            {
            match("<="); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "ATTR_OP_LESS_EQ"

    // $ANTLR start "ATTR_OP_NOT_EQUALS"
    public final void mATTR_OP_NOT_EQUALS() throws RecognitionException {
        try {
            int _type = ATTR_OP_NOT_EQUALS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:10:20: ( '!=' )
            // Velvet.g:10:22: '!='
            {
            match("!="); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "ATTR_OP_NOT_EQUALS"

    // $ANTLR start "COLON"
    public final void mCOLON() throws RecognitionException {
        try {
            int _type = COLON;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:11:7: ( ':' )
            // Velvet.g:11:9: ':'
            {
            match(':'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "COLON"

    // $ANTLR start "COMMA"
    public final void mCOMMA() throws RecognitionException {
        try {
            int _type = COMMA;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:12:7: ( ',' )
            // Velvet.g:12:9: ','
            {
            match(','); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "COMMA"

    // $ANTLR start "CONCEPT"
    public final void mCONCEPT() throws RecognitionException {
        try {
            int _type = CONCEPT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:13:9: ( 'concept' )
            // Velvet.g:13:11: 'concept'
            {
            match("concept"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "CONCEPT"

    // $ANTLR start "CONSTRAINT"
    public final void mCONSTRAINT() throws RecognitionException {
        try {
            int _type = CONSTRAINT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:14:12: ( 'constraint' )
            // Velvet.g:14:14: 'constraint'
            {
            match("constraint"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "CONSTRAINT"

    // $ANTLR start "END_C"
    public final void mEND_C() throws RecognitionException {
        try {
            int _type = END_C;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:15:7: ( '}' )
            // Velvet.g:15:9: '}'
            {
            match('}'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "END_C"

    // $ANTLR start "END_R"
    public final void mEND_R() throws RecognitionException {
        try {
            int _type = END_R;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:16:7: ( ')' )
            // Velvet.g:16:9: ')'
            {
            match(')'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "END_R"

    // $ANTLR start "EQ"
    public final void mEQ() throws RecognitionException {
        try {
            int _type = EQ;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:17:4: ( '=' )
            // Velvet.g:17:6: '='
            {
            match('='); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "EQ"

    // $ANTLR start "FEATURE"
    public final void mFEATURE() throws RecognitionException {
        try {
            int _type = FEATURE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:18:9: ( 'feature' )
            // Velvet.g:18:11: 'feature'
            {
            match("feature"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "FEATURE"

    // $ANTLR start "IMPORT"
    public final void mIMPORT() throws RecognitionException {
        try {
            int _type = IMPORT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:19:8: ( 'import' )
            // Velvet.g:19:10: 'import'
            {
            match("import"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "IMPORT"

    // $ANTLR start "MANDATORY"
    public final void mMANDATORY() throws RecognitionException {
        try {
            int _type = MANDATORY;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:20:11: ( 'mandatory' )
            // Velvet.g:20:13: 'mandatory'
            {
            match("mandatory"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "MANDATORY"

    // $ANTLR start "MINUS"
    public final void mMINUS() throws RecognitionException {
        try {
            int _type = MINUS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:21:7: ( '-' )
            // Velvet.g:21:9: '-'
            {
            match('-'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "MINUS"

    // $ANTLR start "ONEOF"
    public final void mONEOF() throws RecognitionException {
        try {
            int _type = ONEOF;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:22:7: ( 'oneOf' )
            // Velvet.g:22:9: 'oneOf'
            {
            match("oneOf"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "ONEOF"

    // $ANTLR start "OP_AND"
    public final void mOP_AND() throws RecognitionException {
        try {
            int _type = OP_AND;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:23:8: ( '&&' )
            // Velvet.g:23:10: '&&'
            {
            match("&&"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "OP_AND"

    // $ANTLR start "OP_EQUIVALENT"
    public final void mOP_EQUIVALENT() throws RecognitionException {
        try {
            int _type = OP_EQUIVALENT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:24:15: ( '<->' )
            // Velvet.g:24:17: '<->'
            {
            match("<->"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "OP_EQUIVALENT"

    // $ANTLR start "OP_IMPLIES"
    public final void mOP_IMPLIES() throws RecognitionException {
        try {
            int _type = OP_IMPLIES;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:25:12: ( '->' )
            // Velvet.g:25:14: '->'
            {
            match("->"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "OP_IMPLIES"

    // $ANTLR start "OP_NOT"
    public final void mOP_NOT() throws RecognitionException {
        try {
            int _type = OP_NOT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:26:8: ( '!' )
            // Velvet.g:26:10: '!'
            {
            match('!'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "OP_NOT"

    // $ANTLR start "OP_OR"
    public final void mOP_OR() throws RecognitionException {
        try {
            int _type = OP_OR;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:27:7: ( '||' )
            // Velvet.g:27:9: '||'
            {
            match("||"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "OP_OR"

    // $ANTLR start "OP_XOR"
    public final void mOP_XOR() throws RecognitionException {
        try {
            int _type = OP_XOR;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:28:8: ( 'xor' )
            // Velvet.g:28:10: 'xor'
            {
            match("xor"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "OP_XOR"

    // $ANTLR start "PLUS"
    public final void mPLUS() throws RecognitionException {
        try {
            int _type = PLUS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:29:6: ( '+' )
            // Velvet.g:29:8: '+'
            {
            match('+'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "PLUS"

    // $ANTLR start "REFINES"
    public final void mREFINES() throws RecognitionException {
        try {
            int _type = REFINES;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:30:9: ( 'refines' )
            // Velvet.g:30:11: 'refines'
            {
            match("refines"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "REFINES"

    // $ANTLR start "SEMI"
    public final void mSEMI() throws RecognitionException {
        try {
            int _type = SEMI;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:31:6: ( ';' )
            // Velvet.g:31:8: ';'
            {
            match(';'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "SEMI"

    // $ANTLR start "SOMEOF"
    public final void mSOMEOF() throws RecognitionException {
        try {
            int _type = SOMEOF;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:32:8: ( 'someOf' )
            // Velvet.g:32:10: 'someOf'
            {
            match("someOf"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "SOMEOF"

    // $ANTLR start "START_C"
    public final void mSTART_C() throws RecognitionException {
        try {
            int _type = START_C;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:33:9: ( '{' )
            // Velvet.g:33:11: '{'
            {
            match('{'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "START_C"

    // $ANTLR start "START_R"
    public final void mSTART_R() throws RecognitionException {
        try {
            int _type = START_R;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:34:9: ( '(' )
            // Velvet.g:34:11: '('
            {
            match('('); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "START_R"

    // $ANTLR start "VAR_BOOL"
    public final void mVAR_BOOL() throws RecognitionException {
        try {
            int _type = VAR_BOOL;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:35:10: ( 'bool' )
            // Velvet.g:35:12: 'bool'
            {
            match("bool"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "VAR_BOOL"

    // $ANTLR start "VAR_FLOAT"
    public final void mVAR_FLOAT() throws RecognitionException {
        try {
            int _type = VAR_FLOAT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:36:11: ( 'float' )
            // Velvet.g:36:13: 'float'
            {
            match("float"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "VAR_FLOAT"

    // $ANTLR start "VAR_INT"
    public final void mVAR_INT() throws RecognitionException {
        try {
            int _type = VAR_INT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:37:9: ( 'int' )
            // Velvet.g:37:11: 'int'
            {
            match("int"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "VAR_INT"

    // $ANTLR start "VAR_STRING"
    public final void mVAR_STRING() throws RecognitionException {
        try {
            int _type = VAR_STRING;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:38:12: ( 'string' )
            // Velvet.g:38:14: 'string'
            {
            match("string"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "VAR_STRING"

    // $ANTLR start "BOOLEAN"
    public final void mBOOLEAN() throws RecognitionException {
        try {
            int _type = BOOLEAN;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:198:9: ( 'true' | 'false' )
            int alt1=2;
            int LA1_0 = input.LA(1);

            if ( (LA1_0=='t') ) {
                alt1=1;
            }
            else if ( (LA1_0=='f') ) {
                alt1=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 1, 0, input);

                throw nvae;

            }
            switch (alt1) {
                case 1 :
                    // Velvet.g:198:11: 'true'
                    {
                    match("true"); 



                    }
                    break;
                case 2 :
                    // Velvet.g:199:4: 'false'
                    {
                    match("false"); 



                    }
                    break;

            }
            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "BOOLEAN"

    // $ANTLR start "ID"
    public final void mID() throws RecognitionException {
        try {
            int _type = ID;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:202:5: ( ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )* )
            // Velvet.g:202:7: ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )*
            {
            if ( (input.LA(1) >= 'A' && input.LA(1) <= 'Z')||input.LA(1)=='_'||(input.LA(1) >= 'a' && input.LA(1) <= 'z') ) {
                input.consume();
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;
            }


            // Velvet.g:202:31: ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )*
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( ((LA2_0 >= '0' && LA2_0 <= '9')||(LA2_0 >= 'A' && LA2_0 <= 'Z')||LA2_0=='_'||(LA2_0 >= 'a' && LA2_0 <= 'z')) ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // Velvet.g:
            	    {
            	    if ( (input.LA(1) >= '0' && input.LA(1) <= '9')||(input.LA(1) >= 'A' && input.LA(1) <= 'Z')||input.LA(1)=='_'||(input.LA(1) >= 'a' && input.LA(1) <= 'z') ) {
            	        input.consume();
            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;
            	    }


            	    }
            	    break;

            	default :
            	    break loop2;
                }
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "ID"

    // $ANTLR start "IDPath"
    public final void mIDPath() throws RecognitionException {
        try {
            int _type = IDPath;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:205:8: ( ID ( '.' ID )+ )
            // Velvet.g:205:10: ID ( '.' ID )+
            {
            mID(); 


            // Velvet.g:205:13: ( '.' ID )+
            int cnt3=0;
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( (LA3_0=='.') ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // Velvet.g:205:14: '.' ID
            	    {
            	    match('.'); 

            	    mID(); 


            	    }
            	    break;

            	default :
            	    if ( cnt3 >= 1 ) break loop3;
                        EarlyExitException eee =
                            new EarlyExitException(3, input);
                        throw eee;
                }
                cnt3++;
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "IDPath"

    // $ANTLR start "INT"
    public final void mINT() throws RecognitionException {
        try {
            int _type = INT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:208:5: ( ( '0' .. '9' )+ )
            // Velvet.g:208:7: ( '0' .. '9' )+
            {
            // Velvet.g:208:7: ( '0' .. '9' )+
            int cnt4=0;
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( ((LA4_0 >= '0' && LA4_0 <= '9')) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // Velvet.g:
            	    {
            	    if ( (input.LA(1) >= '0' && input.LA(1) <= '9') ) {
            	        input.consume();
            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;
            	    }


            	    }
            	    break;

            	default :
            	    if ( cnt4 >= 1 ) break loop4;
                        EarlyExitException eee =
                            new EarlyExitException(4, input);
                        throw eee;
                }
                cnt4++;
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "INT"

    // $ANTLR start "FLOAT"
    public final void mFLOAT() throws RecognitionException {
        try {
            int _type = FLOAT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:212:5: ( ( '0' .. '9' )+ '.' ( '0' .. '9' )* ( EXPONENT )? | '.' ( '0' .. '9' )+ ( EXPONENT )? | ( '0' .. '9' )+ EXPONENT )
            int alt11=3;
            alt11 = dfa11.predict(input);
            switch (alt11) {
                case 1 :
                    // Velvet.g:212:9: ( '0' .. '9' )+ '.' ( '0' .. '9' )* ( EXPONENT )?
                    {
                    // Velvet.g:212:9: ( '0' .. '9' )+
                    int cnt5=0;
                    loop5:
                    do {
                        int alt5=2;
                        int LA5_0 = input.LA(1);

                        if ( ((LA5_0 >= '0' && LA5_0 <= '9')) ) {
                            alt5=1;
                        }


                        switch (alt5) {
                    	case 1 :
                    	    // Velvet.g:
                    	    {
                    	    if ( (input.LA(1) >= '0' && input.LA(1) <= '9') ) {
                    	        input.consume();
                    	    }
                    	    else {
                    	        MismatchedSetException mse = new MismatchedSetException(null,input);
                    	        recover(mse);
                    	        throw mse;
                    	    }


                    	    }
                    	    break;

                    	default :
                    	    if ( cnt5 >= 1 ) break loop5;
                                EarlyExitException eee =
                                    new EarlyExitException(5, input);
                                throw eee;
                        }
                        cnt5++;
                    } while (true);


                    match('.'); 

                    // Velvet.g:212:25: ( '0' .. '9' )*
                    loop6:
                    do {
                        int alt6=2;
                        int LA6_0 = input.LA(1);

                        if ( ((LA6_0 >= '0' && LA6_0 <= '9')) ) {
                            alt6=1;
                        }


                        switch (alt6) {
                    	case 1 :
                    	    // Velvet.g:
                    	    {
                    	    if ( (input.LA(1) >= '0' && input.LA(1) <= '9') ) {
                    	        input.consume();
                    	    }
                    	    else {
                    	        MismatchedSetException mse = new MismatchedSetException(null,input);
                    	        recover(mse);
                    	        throw mse;
                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop6;
                        }
                    } while (true);


                    // Velvet.g:212:37: ( EXPONENT )?
                    int alt7=2;
                    int LA7_0 = input.LA(1);

                    if ( (LA7_0=='E'||LA7_0=='e') ) {
                        alt7=1;
                    }
                    switch (alt7) {
                        case 1 :
                            // Velvet.g:212:37: EXPONENT
                            {
                            mEXPONENT(); 


                            }
                            break;

                    }


                    }
                    break;
                case 2 :
                    // Velvet.g:213:9: '.' ( '0' .. '9' )+ ( EXPONENT )?
                    {
                    match('.'); 

                    // Velvet.g:213:13: ( '0' .. '9' )+
                    int cnt8=0;
                    loop8:
                    do {
                        int alt8=2;
                        int LA8_0 = input.LA(1);

                        if ( ((LA8_0 >= '0' && LA8_0 <= '9')) ) {
                            alt8=1;
                        }


                        switch (alt8) {
                    	case 1 :
                    	    // Velvet.g:
                    	    {
                    	    if ( (input.LA(1) >= '0' && input.LA(1) <= '9') ) {
                    	        input.consume();
                    	    }
                    	    else {
                    	        MismatchedSetException mse = new MismatchedSetException(null,input);
                    	        recover(mse);
                    	        throw mse;
                    	    }


                    	    }
                    	    break;

                    	default :
                    	    if ( cnt8 >= 1 ) break loop8;
                                EarlyExitException eee =
                                    new EarlyExitException(8, input);
                                throw eee;
                        }
                        cnt8++;
                    } while (true);


                    // Velvet.g:213:25: ( EXPONENT )?
                    int alt9=2;
                    int LA9_0 = input.LA(1);

                    if ( (LA9_0=='E'||LA9_0=='e') ) {
                        alt9=1;
                    }
                    switch (alt9) {
                        case 1 :
                            // Velvet.g:213:25: EXPONENT
                            {
                            mEXPONENT(); 


                            }
                            break;

                    }


                    }
                    break;
                case 3 :
                    // Velvet.g:214:9: ( '0' .. '9' )+ EXPONENT
                    {
                    // Velvet.g:214:9: ( '0' .. '9' )+
                    int cnt10=0;
                    loop10:
                    do {
                        int alt10=2;
                        int LA10_0 = input.LA(1);

                        if ( ((LA10_0 >= '0' && LA10_0 <= '9')) ) {
                            alt10=1;
                        }


                        switch (alt10) {
                    	case 1 :
                    	    // Velvet.g:
                    	    {
                    	    if ( (input.LA(1) >= '0' && input.LA(1) <= '9') ) {
                    	        input.consume();
                    	    }
                    	    else {
                    	        MismatchedSetException mse = new MismatchedSetException(null,input);
                    	        recover(mse);
                    	        throw mse;
                    	    }


                    	    }
                    	    break;

                    	default :
                    	    if ( cnt10 >= 1 ) break loop10;
                                EarlyExitException eee =
                                    new EarlyExitException(10, input);
                                throw eee;
                        }
                        cnt10++;
                    } while (true);


                    mEXPONENT(); 


                    }
                    break;

            }
            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "FLOAT"

    // $ANTLR start "STRING"
    public final void mSTRING() throws RecognitionException {
        try {
            int _type = STRING;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:218:5: ( '\"' ( ESC_SEQ |~ ( '\\\\' | '\"' ) )* '\"' )
            // Velvet.g:218:8: '\"' ( ESC_SEQ |~ ( '\\\\' | '\"' ) )* '\"'
            {
            match('\"'); 

            // Velvet.g:218:12: ( ESC_SEQ |~ ( '\\\\' | '\"' ) )*
            loop12:
            do {
                int alt12=3;
                int LA12_0 = input.LA(1);

                if ( (LA12_0=='\\') ) {
                    alt12=1;
                }
                else if ( ((LA12_0 >= '\u0000' && LA12_0 <= '!')||(LA12_0 >= '#' && LA12_0 <= '[')||(LA12_0 >= ']' && LA12_0 <= '\uFFFF')) ) {
                    alt12=2;
                }


                switch (alt12) {
            	case 1 :
            	    // Velvet.g:218:14: ESC_SEQ
            	    {
            	    mESC_SEQ(); 


            	    }
            	    break;
            	case 2 :
            	    // Velvet.g:218:24: ~ ( '\\\\' | '\"' )
            	    {
            	    if ( (input.LA(1) >= '\u0000' && input.LA(1) <= '!')||(input.LA(1) >= '#' && input.LA(1) <= '[')||(input.LA(1) >= ']' && input.LA(1) <= '\uFFFF') ) {
            	        input.consume();
            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;
            	    }


            	    }
            	    break;

            	default :
            	    break loop12;
                }
            } while (true);


            match('\"'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "STRING"

    // $ANTLR start "EXPONENT"
    public final void mEXPONENT() throws RecognitionException {
        try {
            // Velvet.g:223:10: ( ( 'e' | 'E' ) ( '+' | '-' )? ( '0' .. '9' )+ )
            // Velvet.g:223:12: ( 'e' | 'E' ) ( '+' | '-' )? ( '0' .. '9' )+
            {
            if ( input.LA(1)=='E'||input.LA(1)=='e' ) {
                input.consume();
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;
            }


            // Velvet.g:223:22: ( '+' | '-' )?
            int alt13=2;
            int LA13_0 = input.LA(1);

            if ( (LA13_0=='+'||LA13_0=='-') ) {
                alt13=1;
            }
            switch (alt13) {
                case 1 :
                    // Velvet.g:
                    {
                    if ( input.LA(1)=='+'||input.LA(1)=='-' ) {
                        input.consume();
                    }
                    else {
                        MismatchedSetException mse = new MismatchedSetException(null,input);
                        recover(mse);
                        throw mse;
                    }


                    }
                    break;

            }


            // Velvet.g:223:33: ( '0' .. '9' )+
            int cnt14=0;
            loop14:
            do {
                int alt14=2;
                int LA14_0 = input.LA(1);

                if ( ((LA14_0 >= '0' && LA14_0 <= '9')) ) {
                    alt14=1;
                }


                switch (alt14) {
            	case 1 :
            	    // Velvet.g:
            	    {
            	    if ( (input.LA(1) >= '0' && input.LA(1) <= '9') ) {
            	        input.consume();
            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;
            	    }


            	    }
            	    break;

            	default :
            	    if ( cnt14 >= 1 ) break loop14;
                        EarlyExitException eee =
                            new EarlyExitException(14, input);
                        throw eee;
                }
                cnt14++;
            } while (true);


            }


        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "EXPONENT"

    // $ANTLR start "HEX_DIGIT"
    public final void mHEX_DIGIT() throws RecognitionException {
        try {
            // Velvet.g:226:11: ( ( '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' ) )
            // Velvet.g:
            {
            if ( (input.LA(1) >= '0' && input.LA(1) <= '9')||(input.LA(1) >= 'A' && input.LA(1) <= 'F')||(input.LA(1) >= 'a' && input.LA(1) <= 'f') ) {
                input.consume();
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;
            }


            }


        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "HEX_DIGIT"

    // $ANTLR start "ESC_SEQ"
    public final void mESC_SEQ() throws RecognitionException {
        try {
            // Velvet.g:230:5: ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\\\"' | '\\'' | '\\\\' ) | UNICODE_ESC | OCTAL_ESC )
            int alt15=3;
            int LA15_0 = input.LA(1);

            if ( (LA15_0=='\\') ) {
                switch ( input.LA(2) ) {
                case '\"':
                case '\'':
                case '\\':
                case 'b':
                case 'f':
                case 'n':
                case 'r':
                case 't':
                    {
                    alt15=1;
                    }
                    break;
                case 'u':
                    {
                    alt15=2;
                    }
                    break;
                case '0':
                case '1':
                case '2':
                case '3':
                case '4':
                case '5':
                case '6':
                case '7':
                    {
                    alt15=3;
                    }
                    break;
                default:
                    NoViableAltException nvae =
                        new NoViableAltException("", 15, 1, input);

                    throw nvae;

                }

            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 15, 0, input);

                throw nvae;

            }
            switch (alt15) {
                case 1 :
                    // Velvet.g:230:9: '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\\\"' | '\\'' | '\\\\' )
                    {
                    match('\\'); 

                    if ( input.LA(1)=='\"'||input.LA(1)=='\''||input.LA(1)=='\\'||input.LA(1)=='b'||input.LA(1)=='f'||input.LA(1)=='n'||input.LA(1)=='r'||input.LA(1)=='t' ) {
                        input.consume();
                    }
                    else {
                        MismatchedSetException mse = new MismatchedSetException(null,input);
                        recover(mse);
                        throw mse;
                    }


                    }
                    break;
                case 2 :
                    // Velvet.g:231:9: UNICODE_ESC
                    {
                    mUNICODE_ESC(); 


                    }
                    break;
                case 3 :
                    // Velvet.g:232:9: OCTAL_ESC
                    {
                    mOCTAL_ESC(); 


                    }
                    break;

            }

        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "ESC_SEQ"

    // $ANTLR start "OCTAL_ESC"
    public final void mOCTAL_ESC() throws RecognitionException {
        try {
            // Velvet.g:237:5: ( '\\\\' ( '0' .. '3' ) ( '0' .. '7' ) ( '0' .. '7' ) | '\\\\' ( '0' .. '7' ) ( '0' .. '7' ) | '\\\\' ( '0' .. '7' ) )
            int alt16=3;
            int LA16_0 = input.LA(1);

            if ( (LA16_0=='\\') ) {
                int LA16_1 = input.LA(2);

                if ( ((LA16_1 >= '0' && LA16_1 <= '3')) ) {
                    int LA16_2 = input.LA(3);

                    if ( ((LA16_2 >= '0' && LA16_2 <= '7')) ) {
                        int LA16_4 = input.LA(4);

                        if ( ((LA16_4 >= '0' && LA16_4 <= '7')) ) {
                            alt16=1;
                        }
                        else {
                            alt16=2;
                        }
                    }
                    else {
                        alt16=3;
                    }
                }
                else if ( ((LA16_1 >= '4' && LA16_1 <= '7')) ) {
                    int LA16_3 = input.LA(3);

                    if ( ((LA16_3 >= '0' && LA16_3 <= '7')) ) {
                        alt16=2;
                    }
                    else {
                        alt16=3;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 16, 1, input);

                    throw nvae;

                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 16, 0, input);

                throw nvae;

            }
            switch (alt16) {
                case 1 :
                    // Velvet.g:237:9: '\\\\' ( '0' .. '3' ) ( '0' .. '7' ) ( '0' .. '7' )
                    {
                    match('\\'); 

                    if ( (input.LA(1) >= '0' && input.LA(1) <= '3') ) {
                        input.consume();
                    }
                    else {
                        MismatchedSetException mse = new MismatchedSetException(null,input);
                        recover(mse);
                        throw mse;
                    }


                    if ( (input.LA(1) >= '0' && input.LA(1) <= '7') ) {
                        input.consume();
                    }
                    else {
                        MismatchedSetException mse = new MismatchedSetException(null,input);
                        recover(mse);
                        throw mse;
                    }


                    if ( (input.LA(1) >= '0' && input.LA(1) <= '7') ) {
                        input.consume();
                    }
                    else {
                        MismatchedSetException mse = new MismatchedSetException(null,input);
                        recover(mse);
                        throw mse;
                    }


                    }
                    break;
                case 2 :
                    // Velvet.g:238:9: '\\\\' ( '0' .. '7' ) ( '0' .. '7' )
                    {
                    match('\\'); 

                    if ( (input.LA(1) >= '0' && input.LA(1) <= '7') ) {
                        input.consume();
                    }
                    else {
                        MismatchedSetException mse = new MismatchedSetException(null,input);
                        recover(mse);
                        throw mse;
                    }


                    if ( (input.LA(1) >= '0' && input.LA(1) <= '7') ) {
                        input.consume();
                    }
                    else {
                        MismatchedSetException mse = new MismatchedSetException(null,input);
                        recover(mse);
                        throw mse;
                    }


                    }
                    break;
                case 3 :
                    // Velvet.g:239:9: '\\\\' ( '0' .. '7' )
                    {
                    match('\\'); 

                    if ( (input.LA(1) >= '0' && input.LA(1) <= '7') ) {
                        input.consume();
                    }
                    else {
                        MismatchedSetException mse = new MismatchedSetException(null,input);
                        recover(mse);
                        throw mse;
                    }


                    }
                    break;

            }

        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "OCTAL_ESC"

    // $ANTLR start "UNICODE_ESC"
    public final void mUNICODE_ESC() throws RecognitionException {
        try {
            // Velvet.g:244:5: ( '\\\\' 'u' HEX_DIGIT HEX_DIGIT HEX_DIGIT HEX_DIGIT )
            // Velvet.g:244:9: '\\\\' 'u' HEX_DIGIT HEX_DIGIT HEX_DIGIT HEX_DIGIT
            {
            match('\\'); 

            match('u'); 

            mHEX_DIGIT(); 


            mHEX_DIGIT(); 


            mHEX_DIGIT(); 


            mHEX_DIGIT(); 


            }


        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "UNICODE_ESC"

    // $ANTLR start "WS"
    public final void mWS() throws RecognitionException {
        try {
            int _type = WS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:246:5: ( ( ' ' | '\\t' | '\\r' | '\\n' ) )
            // Velvet.g:246:7: ( ' ' | '\\t' | '\\r' | '\\n' )
            {
            if ( (input.LA(1) >= '\t' && input.LA(1) <= '\n')||input.LA(1)=='\r'||input.LA(1)==' ' ) {
                input.consume();
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;
            }


            _channel=HIDDEN;

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "WS"

    public void mTokens() throws RecognitionException {
        // Velvet.g:1:8: ( ABSTRACT | ATTR_OP_EQUALS | ATTR_OP_GREATER | ATTR_OP_GREATER_EQ | ATTR_OP_LESS | ATTR_OP_LESS_EQ | ATTR_OP_NOT_EQUALS | COLON | COMMA | CONCEPT | CONSTRAINT | END_C | END_R | EQ | FEATURE | IMPORT | MANDATORY | MINUS | ONEOF | OP_AND | OP_EQUIVALENT | OP_IMPLIES | OP_NOT | OP_OR | OP_XOR | PLUS | REFINES | SEMI | SOMEOF | START_C | START_R | VAR_BOOL | VAR_FLOAT | VAR_INT | VAR_STRING | BOOLEAN | ID | IDPath | INT | FLOAT | STRING | WS )
        int alt17=42;
        alt17 = dfa17.predict(input);
        switch (alt17) {
            case 1 :
                // Velvet.g:1:10: ABSTRACT
                {
                mABSTRACT(); 


                }
                break;
            case 2 :
                // Velvet.g:1:19: ATTR_OP_EQUALS
                {
                mATTR_OP_EQUALS(); 


                }
                break;
            case 3 :
                // Velvet.g:1:34: ATTR_OP_GREATER
                {
                mATTR_OP_GREATER(); 


                }
                break;
            case 4 :
                // Velvet.g:1:50: ATTR_OP_GREATER_EQ
                {
                mATTR_OP_GREATER_EQ(); 


                }
                break;
            case 5 :
                // Velvet.g:1:69: ATTR_OP_LESS
                {
                mATTR_OP_LESS(); 


                }
                break;
            case 6 :
                // Velvet.g:1:82: ATTR_OP_LESS_EQ
                {
                mATTR_OP_LESS_EQ(); 


                }
                break;
            case 7 :
                // Velvet.g:1:98: ATTR_OP_NOT_EQUALS
                {
                mATTR_OP_NOT_EQUALS(); 


                }
                break;
            case 8 :
                // Velvet.g:1:117: COLON
                {
                mCOLON(); 


                }
                break;
            case 9 :
                // Velvet.g:1:123: COMMA
                {
                mCOMMA(); 


                }
                break;
            case 10 :
                // Velvet.g:1:129: CONCEPT
                {
                mCONCEPT(); 


                }
                break;
            case 11 :
                // Velvet.g:1:137: CONSTRAINT
                {
                mCONSTRAINT(); 


                }
                break;
            case 12 :
                // Velvet.g:1:148: END_C
                {
                mEND_C(); 


                }
                break;
            case 13 :
                // Velvet.g:1:154: END_R
                {
                mEND_R(); 


                }
                break;
            case 14 :
                // Velvet.g:1:160: EQ
                {
                mEQ(); 


                }
                break;
            case 15 :
                // Velvet.g:1:163: FEATURE
                {
                mFEATURE(); 


                }
                break;
            case 16 :
                // Velvet.g:1:171: IMPORT
                {
                mIMPORT(); 


                }
                break;
            case 17 :
                // Velvet.g:1:178: MANDATORY
                {
                mMANDATORY(); 


                }
                break;
            case 18 :
                // Velvet.g:1:188: MINUS
                {
                mMINUS(); 


                }
                break;
            case 19 :
                // Velvet.g:1:194: ONEOF
                {
                mONEOF(); 


                }
                break;
            case 20 :
                // Velvet.g:1:200: OP_AND
                {
                mOP_AND(); 


                }
                break;
            case 21 :
                // Velvet.g:1:207: OP_EQUIVALENT
                {
                mOP_EQUIVALENT(); 


                }
                break;
            case 22 :
                // Velvet.g:1:221: OP_IMPLIES
                {
                mOP_IMPLIES(); 


                }
                break;
            case 23 :
                // Velvet.g:1:232: OP_NOT
                {
                mOP_NOT(); 


                }
                break;
            case 24 :
                // Velvet.g:1:239: OP_OR
                {
                mOP_OR(); 


                }
                break;
            case 25 :
                // Velvet.g:1:245: OP_XOR
                {
                mOP_XOR(); 


                }
                break;
            case 26 :
                // Velvet.g:1:252: PLUS
                {
                mPLUS(); 


                }
                break;
            case 27 :
                // Velvet.g:1:257: REFINES
                {
                mREFINES(); 


                }
                break;
            case 28 :
                // Velvet.g:1:265: SEMI
                {
                mSEMI(); 


                }
                break;
            case 29 :
                // Velvet.g:1:270: SOMEOF
                {
                mSOMEOF(); 


                }
                break;
            case 30 :
                // Velvet.g:1:277: START_C
                {
                mSTART_C(); 


                }
                break;
            case 31 :
                // Velvet.g:1:285: START_R
                {
                mSTART_R(); 


                }
                break;
            case 32 :
                // Velvet.g:1:293: VAR_BOOL
                {
                mVAR_BOOL(); 


                }
                break;
            case 33 :
                // Velvet.g:1:302: VAR_FLOAT
                {
                mVAR_FLOAT(); 


                }
                break;
            case 34 :
                // Velvet.g:1:312: VAR_INT
                {
                mVAR_INT(); 


                }
                break;
            case 35 :
                // Velvet.g:1:320: VAR_STRING
                {
                mVAR_STRING(); 


                }
                break;
            case 36 :
                // Velvet.g:1:331: BOOLEAN
                {
                mBOOLEAN(); 


                }
                break;
            case 37 :
                // Velvet.g:1:339: ID
                {
                mID(); 


                }
                break;
            case 38 :
                // Velvet.g:1:342: IDPath
                {
                mIDPath(); 


                }
                break;
            case 39 :
                // Velvet.g:1:349: INT
                {
                mINT(); 


                }
                break;
            case 40 :
                // Velvet.g:1:353: FLOAT
                {
                mFLOAT(); 


                }
                break;
            case 41 :
                // Velvet.g:1:359: STRING
                {
                mSTRING(); 


                }
                break;
            case 42 :
                // Velvet.g:1:366: WS
                {
                mWS(); 


                }
                break;

        }

    }


    protected DFA11 dfa11 = new DFA11(this);
    protected DFA17 dfa17 = new DFA17(this);
    static final String DFA11_eotS =
        "\5\uffff";
    static final String DFA11_eofS =
        "\5\uffff";
    static final String DFA11_minS =
        "\2\56\3\uffff";
    static final String DFA11_maxS =
        "\1\71\1\145\3\uffff";
    static final String DFA11_acceptS =
        "\2\uffff\1\2\1\1\1\3";
    static final String DFA11_specialS =
        "\5\uffff}>";
    static final String[] DFA11_transitionS = {
            "\1\2\1\uffff\12\1",
            "\1\3\1\uffff\12\1\13\uffff\1\4\37\uffff\1\4",
            "",
            "",
            ""
    };

    static final short[] DFA11_eot = DFA.unpackEncodedString(DFA11_eotS);
    static final short[] DFA11_eof = DFA.unpackEncodedString(DFA11_eofS);
    static final char[] DFA11_min = DFA.unpackEncodedStringToUnsignedChars(DFA11_minS);
    static final char[] DFA11_max = DFA.unpackEncodedStringToUnsignedChars(DFA11_maxS);
    static final short[] DFA11_accept = DFA.unpackEncodedString(DFA11_acceptS);
    static final short[] DFA11_special = DFA.unpackEncodedString(DFA11_specialS);
    static final short[][] DFA11_transition;

    static {
        int numStates = DFA11_transitionS.length;
        DFA11_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA11_transition[i] = DFA.unpackEncodedString(DFA11_transitionS[i]);
        }
    }

    class DFA11 extends DFA {

        public DFA11(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 11;
            this.eot = DFA11_eot;
            this.eof = DFA11_eof;
            this.min = DFA11_min;
            this.max = DFA11_max;
            this.accept = DFA11_accept;
            this.special = DFA11_special;
            this.transition = DFA11_transition;
        }
        public String getDescription() {
            return "211:1: FLOAT : ( ( '0' .. '9' )+ '.' ( '0' .. '9' )* ( EXPONENT )? | '.' ( '0' .. '9' )+ ( EXPONENT )? | ( '0' .. '9' )+ EXPONENT );";
        }
    }
    static final String DFA17_eotS =
        "\1\uffff\1\42\1\45\1\47\1\52\1\54\2\uffff\1\42\2\uffff\3\42\1\65"+
        "\1\42\2\uffff\1\42\1\uffff\1\42\1\uffff\1\42\2\uffff\3\42\1\75\3"+
        "\uffff\2\42\13\uffff\7\42\2\uffff\7\42\1\uffff\6\42\1\124\2\42\1"+
        "\127\14\42\1\uffff\2\42\1\uffff\3\42\1\151\1\152\4\42\1\157\1\152"+
        "\2\42\1\162\3\42\2\uffff\4\42\1\uffff\1\172\1\42\1\uffff\1\42\1"+
        "\175\1\176\1\42\1\u0080\1\42\1\u0082\1\uffff\1\42\1\u0084\2\uffff"+
        "\1\u0085\1\uffff\1\42\1\uffff\1\42\2\uffff\1\42\1\u0089\1\u008a"+
        "\2\uffff";
    static final String DFA17_eofS =
        "\u008b\uffff";
    static final String DFA17_minS =
        "\1\11\1\56\2\75\1\55\1\75\2\uffff\1\56\2\uffff\3\56\1\76\1\56\2"+
        "\uffff\1\56\1\uffff\1\56\1\uffff\1\56\2\uffff\4\56\3\uffff\2\56"+
        "\13\uffff\7\56\2\uffff\7\56\1\uffff\26\56\1\uffff\2\56\1\uffff\21"+
        "\56\2\uffff\4\56\1\uffff\2\56\1\uffff\7\56\1\uffff\2\56\2\uffff"+
        "\1\56\1\uffff\1\56\1\uffff\1\56\2\uffff\3\56\2\uffff";
    static final String DFA17_maxS =
        "\1\175\1\172\4\75\2\uffff\1\172\2\uffff\3\172\1\76\1\172\2\uffff"+
        "\1\172\1\uffff\1\172\1\uffff\1\172\2\uffff\3\172\1\145\3\uffff\2"+
        "\172\13\uffff\7\172\2\uffff\7\172\1\uffff\26\172\1\uffff\2\172\1"+
        "\uffff\21\172\2\uffff\4\172\1\uffff\2\172\1\uffff\7\172\1\uffff"+
        "\2\172\2\uffff\1\172\1\uffff\1\172\1\uffff\1\172\2\uffff\3\172\2"+
        "\uffff";
    static final String DFA17_acceptS =
        "\6\uffff\1\10\1\11\1\uffff\1\14\1\15\5\uffff\1\24\1\30\1\uffff\1"+
        "\32\1\uffff\1\34\1\uffff\1\36\1\37\4\uffff\1\50\1\51\1\52\2\uffff"+
        "\1\45\1\46\1\2\1\16\1\4\1\3\1\6\1\25\1\5\1\7\1\27\7\uffff\1\26\1"+
        "\22\7\uffff\1\47\26\uffff\1\42\2\uffff\1\31\21\uffff\1\40\1\44\4"+
        "\uffff\1\41\2\uffff\1\23\7\uffff\1\20\2\uffff\1\35\1\43\1\uffff"+
        "\1\12\1\uffff\1\17\1\uffff\1\33\1\1\3\uffff\1\21\1\13";
    static final String DFA17_specialS =
        "\u008b\uffff}>";
    static final String[] DFA17_transitionS = {
            "\2\37\2\uffff\1\37\22\uffff\1\37\1\5\1\36\3\uffff\1\20\1\uffff"+
            "\1\30\1\12\1\uffff\1\23\1\7\1\16\1\35\1\uffff\12\34\1\6\1\25"+
            "\1\4\1\2\1\3\2\uffff\32\33\4\uffff\1\33\1\uffff\1\1\1\31\1\10"+
            "\2\33\1\13\2\33\1\14\3\33\1\15\1\33\1\17\2\33\1\24\1\26\1\32"+
            "\3\33\1\22\2\33\1\27\1\21\1\11",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\1\41"+
            "\1\40\30\41",
            "\1\44",
            "\1\46",
            "\1\51\17\uffff\1\50",
            "\1\53",
            "",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\16\41"+
            "\1\55\13\41",
            "",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\1\60"+
            "\3\41\1\56\6\41\1\57\16\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\14\41"+
            "\1\61\1\62\14\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\1\63"+
            "\31\41",
            "\1\64",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\15\41"+
            "\1\66\14\41",
            "",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\16\41"+
            "\1\67\13\41",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\4\41"+
            "\1\70\25\41",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\16\41"+
            "\1\71\4\41\1\72\6\41",
            "",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\16\41"+
            "\1\73\13\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\21\41"+
            "\1\74\10\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\35\1\uffff\12\34\13\uffff\1\35\37\uffff\1\35",
            "",
            "",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\22\41"+
            "\1\76\7\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\15\41"+
            "\1\77\14\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\1\100"+
            "\31\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\16\41"+
            "\1\101\13\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\13\41"+
            "\1\102\16\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\17\41"+
            "\1\103\12\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\23\41"+
            "\1\104\6\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\15\41"+
            "\1\105\14\41",
            "",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\4\41"+
            "\1\106\25\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\21\41"+
            "\1\107\10\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\5\41"+
            "\1\110\24\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\14\41"+
            "\1\111\15\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\21\41"+
            "\1\112\10\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\16\41"+
            "\1\113\13\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\24\41"+
            "\1\114\5\41",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\23\41"+
            "\1\115\6\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\2\41"+
            "\1\116\17\41\1\117\7\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\23\41"+
            "\1\120\6\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\1\121"+
            "\31\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\22\41"+
            "\1\122\7\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\16\41"+
            "\1\123\13\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\3\41"+
            "\1\125\26\41",
            "\1\43\1\uffff\12\41\7\uffff\16\41\1\126\13\41\4\uffff\1\41"+
            "\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\10\41"+
            "\1\130\21\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\4\41"+
            "\1\131\25\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\10\41"+
            "\1\132\21\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\13\41"+
            "\1\133\16\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\4\41"+
            "\1\134\25\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\21\41"+
            "\1\135\10\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\4\41"+
            "\1\136\25\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\23\41"+
            "\1\137\6\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\24\41"+
            "\1\140\5\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\23\41"+
            "\1\141\6\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\4\41"+
            "\1\142\25\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\21\41"+
            "\1\143\10\41",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\1\144"+
            "\31\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\5\41"+
            "\1\145\24\41",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\15\41"+
            "\1\146\14\41",
            "\1\43\1\uffff\12\41\7\uffff\16\41\1\147\13\41\4\uffff\1\41"+
            "\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\15\41"+
            "\1\150\14\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\1\153"+
            "\31\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\17\41"+
            "\1\154\12\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\21\41"+
            "\1\155\10\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\21\41"+
            "\1\156\10\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\23\41"+
            "\1\160\6\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\23\41"+
            "\1\161\6\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\4\41"+
            "\1\163\25\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\5\41"+
            "\1\164\24\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\6\41"+
            "\1\165\23\41",
            "",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\2\41"+
            "\1\166\27\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\23\41"+
            "\1\167\6\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\1\170"+
            "\31\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\4\41"+
            "\1\171\25\41",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\16\41"+
            "\1\173\13\41",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\22\41"+
            "\1\174\7\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\23\41"+
            "\1\177\6\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\10\41"+
            "\1\u0081\21\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\21\41"+
            "\1\u0083\10\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\15\41"+
            "\1\u0086\14\41",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\30\41"+
            "\1\u0087\1\41",
            "",
            "",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\23\41"+
            "\1\u0088\6\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "\1\43\1\uffff\12\41\7\uffff\32\41\4\uffff\1\41\1\uffff\32\41",
            "",
            ""
    };

    static final short[] DFA17_eot = DFA.unpackEncodedString(DFA17_eotS);
    static final short[] DFA17_eof = DFA.unpackEncodedString(DFA17_eofS);
    static final char[] DFA17_min = DFA.unpackEncodedStringToUnsignedChars(DFA17_minS);
    static final char[] DFA17_max = DFA.unpackEncodedStringToUnsignedChars(DFA17_maxS);
    static final short[] DFA17_accept = DFA.unpackEncodedString(DFA17_acceptS);
    static final short[] DFA17_special = DFA.unpackEncodedString(DFA17_specialS);
    static final short[][] DFA17_transition;

    static {
        int numStates = DFA17_transitionS.length;
        DFA17_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA17_transition[i] = DFA.unpackEncodedString(DFA17_transitionS[i]);
        }
    }

    class DFA17 extends DFA {

        public DFA17(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 17;
            this.eot = DFA17_eot;
            this.eof = DFA17_eof;
            this.min = DFA17_min;
            this.max = DFA17_max;
            this.accept = DFA17_accept;
            this.special = DFA17_special;
            this.transition = DFA17_transition;
        }
        public String getDescription() {
            return "1:1: Tokens : ( ABSTRACT | ATTR_OP_EQUALS | ATTR_OP_GREATER | ATTR_OP_GREATER_EQ | ATTR_OP_LESS | ATTR_OP_LESS_EQ | ATTR_OP_NOT_EQUALS | COLON | COMMA | CONCEPT | CONSTRAINT | END_C | END_R | EQ | FEATURE | IMPORT | MANDATORY | MINUS | ONEOF | OP_AND | OP_EQUIVALENT | OP_IMPLIES | OP_NOT | OP_OR | OP_XOR | PLUS | REFINES | SEMI | SOMEOF | START_C | START_R | VAR_BOOL | VAR_FLOAT | VAR_INT | VAR_STRING | BOOLEAN | ID | IDPath | INT | FLOAT | STRING | WS );";
        }
    }
 

}