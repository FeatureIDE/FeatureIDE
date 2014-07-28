// $ANTLR 3.4 Velvet.g 2014-06-16 14:59:51
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
    public static final int CINTERFACE=15;
    public static final int COLON=16;
    public static final int COMMA=17;
    public static final int CONCEPT=18;
    public static final int CONSTR=19;
    public static final int CONSTRAINT=20;
    public static final int DEF=21;
    public static final int EMPTY=22;
    public static final int END_C=23;
    public static final int END_R=24;
    public static final int EQ=25;
    public static final int ESC_SEQ=26;
    public static final int EXPONENT=27;
    public static final int FEAT=28;
    public static final int FEATURE=29;
    public static final int FLOAT=30;
    public static final int GROUP=31;
    public static final int HEX_DIGIT=32;
    public static final int ID=33;
    public static final int IDPath=34;
    public static final int IMPORTINSTANCE=35;
    public static final int IMPORTINTERFACE=36;
    public static final int INST=37;
    public static final int INT=38;
    public static final int INTF=39;
    public static final int MANDATORY=40;
    public static final int MINUS=41;
    public static final int ML_COMMENT=42;
    public static final int OCTAL_ESC=43;
    public static final int ONEOF=44;
    public static final int OPERAND=45;
    public static final int OP_AND=46;
    public static final int OP_EQUIVALENT=47;
    public static final int OP_IMPLIES=48;
    public static final int OP_NOT=49;
    public static final int OP_OR=50;
    public static final int OP_XOR=51;
    public static final int PLUS=52;
    public static final int SEMI=53;
    public static final int SL_COMMENT=54;
    public static final int SOMEOF=55;
    public static final int START_C=56;
    public static final int START_R=57;
    public static final int STRING=58;
    public static final int UNARYOP=59;
    public static final int UNICODE_ESC=60;
    public static final int USE=61;
    public static final int USES=62;
    public static final int VAR_BOOL=63;
    public static final int VAR_FLOAT=64;
    public static final int VAR_INT=65;
    public static final int VAR_STRING=66;
    public static final int WS=67;

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

    // $ANTLR start "CINTERFACE"
    public final void mCINTERFACE() throws RecognitionException {
        try {
            int _type = CINTERFACE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:11:12: ( 'cinterface' )
            // Velvet.g:11:14: 'cinterface'
            {
            match("cinterface"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "CINTERFACE"

    // $ANTLR start "COLON"
    public final void mCOLON() throws RecognitionException {
        try {
            int _type = COLON;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:12:7: ( ':' )
            // Velvet.g:12:9: ':'
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
            // Velvet.g:13:7: ( ',' )
            // Velvet.g:13:9: ','
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
            // Velvet.g:14:9: ( 'concept' )
            // Velvet.g:14:11: 'concept'
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
            // Velvet.g:15:12: ( 'constraint' )
            // Velvet.g:15:14: 'constraint'
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
            // Velvet.g:16:7: ( '}' )
            // Velvet.g:16:9: '}'
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
            // Velvet.g:17:7: ( ')' )
            // Velvet.g:17:9: ')'
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
            // Velvet.g:18:4: ( '=' )
            // Velvet.g:18:6: '='
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
            // Velvet.g:19:9: ( 'feature' )
            // Velvet.g:19:11: 'feature'
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

    // $ANTLR start "IMPORTINSTANCE"
    public final void mIMPORTINSTANCE() throws RecognitionException {
        try {
            int _type = IMPORTINSTANCE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:20:16: ( 'instance' )
            // Velvet.g:20:18: 'instance'
            {
            match("instance"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "IMPORTINSTANCE"

    // $ANTLR start "IMPORTINTERFACE"
    public final void mIMPORTINTERFACE() throws RecognitionException {
        try {
            int _type = IMPORTINTERFACE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:21:17: ( 'interface' )
            // Velvet.g:21:19: 'interface'
            {
            match("interface"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "IMPORTINTERFACE"

    // $ANTLR start "MANDATORY"
    public final void mMANDATORY() throws RecognitionException {
        try {
            int _type = MANDATORY;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:22:11: ( 'mandatory' )
            // Velvet.g:22:13: 'mandatory'
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
            // Velvet.g:23:7: ( '-' )
            // Velvet.g:23:9: '-'
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
            // Velvet.g:24:7: ( 'oneOf' )
            // Velvet.g:24:9: 'oneOf'
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
            // Velvet.g:25:8: ( '&&' )
            // Velvet.g:25:10: '&&'
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
            // Velvet.g:26:15: ( '<->' )
            // Velvet.g:26:17: '<->'
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
            // Velvet.g:27:12: ( '->' )
            // Velvet.g:27:14: '->'
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
            // Velvet.g:28:8: ( '!' )
            // Velvet.g:28:10: '!'
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
            // Velvet.g:29:7: ( '||' )
            // Velvet.g:29:9: '||'
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
            // Velvet.g:30:8: ( 'xor' )
            // Velvet.g:30:10: 'xor'
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
            // Velvet.g:31:6: ( '+' )
            // Velvet.g:31:8: '+'
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

    // $ANTLR start "SEMI"
    public final void mSEMI() throws RecognitionException {
        try {
            int _type = SEMI;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:32:6: ( ';' )
            // Velvet.g:32:8: ';'
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
            // Velvet.g:33:8: ( 'someOf' )
            // Velvet.g:33:10: 'someOf'
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
            // Velvet.g:34:9: ( '{' )
            // Velvet.g:34:11: '{'
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
            // Velvet.g:35:9: ( '(' )
            // Velvet.g:35:11: '('
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

    // $ANTLR start "USE"
    public final void mUSE() throws RecognitionException {
        try {
            int _type = USE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:36:5: ( 'use' )
            // Velvet.g:36:7: 'use'
            {
            match("use"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "USE"

    // $ANTLR start "VAR_BOOL"
    public final void mVAR_BOOL() throws RecognitionException {
        try {
            int _type = VAR_BOOL;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:37:10: ( 'bool' )
            // Velvet.g:37:12: 'bool'
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
            // Velvet.g:38:11: ( 'float' )
            // Velvet.g:38:13: 'float'
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
            // Velvet.g:39:9: ( 'int' )
            // Velvet.g:39:11: 'int'
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
            // Velvet.g:40:12: ( 'string' )
            // Velvet.g:40:14: 'string'
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
            // Velvet.g:222:9: ( 'true' | 'false' )
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
                    // Velvet.g:222:11: 'true'
                    {
                    match("true"); 



                    }
                    break;
                case 2 :
                    // Velvet.g:223:4: 'false'
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
            // Velvet.g:226:5: ( ( 'a' .. 'z' | 'A' .. 'Z' | '_' | '-' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-' )* )
            // Velvet.g:226:7: ( 'a' .. 'z' | 'A' .. 'Z' | '_' | '-' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-' )*
            {
            if ( input.LA(1)=='-'||(input.LA(1) >= 'A' && input.LA(1) <= 'Z')||input.LA(1)=='_'||(input.LA(1) >= 'a' && input.LA(1) <= 'z') ) {
                input.consume();
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;
            }


            // Velvet.g:226:35: ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-' )*
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( (LA2_0=='-'||(LA2_0 >= '0' && LA2_0 <= '9')||(LA2_0 >= 'A' && LA2_0 <= 'Z')||LA2_0=='_'||(LA2_0 >= 'a' && LA2_0 <= 'z')) ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // Velvet.g:
            	    {
            	    if ( input.LA(1)=='-'||(input.LA(1) >= '0' && input.LA(1) <= '9')||(input.LA(1) >= 'A' && input.LA(1) <= 'Z')||input.LA(1)=='_'||(input.LA(1) >= 'a' && input.LA(1) <= 'z') ) {
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
            // Velvet.g:229:8: ( ID ( '.' ID )+ )
            // Velvet.g:229:10: ID ( '.' ID )+
            {
            mID(); 


            // Velvet.g:229:13: ( '.' ID )+
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
            	    // Velvet.g:229:14: '.' ID
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
            // Velvet.g:232:5: ( ( '0' .. '9' )+ )
            // Velvet.g:232:7: ( '0' .. '9' )+
            {
            // Velvet.g:232:7: ( '0' .. '9' )+
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
            // Velvet.g:236:5: ( ( '0' .. '9' )+ '.' ( '0' .. '9' )* ( EXPONENT )? | '.' ( '0' .. '9' )+ ( EXPONENT )? | ( '0' .. '9' )+ EXPONENT )
            int alt11=3;
            alt11 = dfa11.predict(input);
            switch (alt11) {
                case 1 :
                    // Velvet.g:236:9: ( '0' .. '9' )+ '.' ( '0' .. '9' )* ( EXPONENT )?
                    {
                    // Velvet.g:236:9: ( '0' .. '9' )+
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

                    // Velvet.g:236:25: ( '0' .. '9' )*
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


                    // Velvet.g:236:37: ( EXPONENT )?
                    int alt7=2;
                    int LA7_0 = input.LA(1);

                    if ( (LA7_0=='E'||LA7_0=='e') ) {
                        alt7=1;
                    }
                    switch (alt7) {
                        case 1 :
                            // Velvet.g:236:37: EXPONENT
                            {
                            mEXPONENT(); 


                            }
                            break;

                    }


                    }
                    break;
                case 2 :
                    // Velvet.g:237:9: '.' ( '0' .. '9' )+ ( EXPONENT )?
                    {
                    match('.'); 

                    // Velvet.g:237:13: ( '0' .. '9' )+
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


                    // Velvet.g:237:25: ( EXPONENT )?
                    int alt9=2;
                    int LA9_0 = input.LA(1);

                    if ( (LA9_0=='E'||LA9_0=='e') ) {
                        alt9=1;
                    }
                    switch (alt9) {
                        case 1 :
                            // Velvet.g:237:25: EXPONENT
                            {
                            mEXPONENT(); 


                            }
                            break;

                    }


                    }
                    break;
                case 3 :
                    // Velvet.g:238:9: ( '0' .. '9' )+ EXPONENT
                    {
                    // Velvet.g:238:9: ( '0' .. '9' )+
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
            // Velvet.g:242:5: ( '\"' ( ESC_SEQ |~ ( '\\\\' | '\"' ) )* '\"' )
            // Velvet.g:242:8: '\"' ( ESC_SEQ |~ ( '\\\\' | '\"' ) )* '\"'
            {
            match('\"'); 

            // Velvet.g:242:12: ( ESC_SEQ |~ ( '\\\\' | '\"' ) )*
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
            	    // Velvet.g:242:14: ESC_SEQ
            	    {
            	    mESC_SEQ(); 


            	    }
            	    break;
            	case 2 :
            	    // Velvet.g:242:24: ~ ( '\\\\' | '\"' )
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
            // Velvet.g:247:10: ( ( 'e' | 'E' ) ( '+' | '-' )? ( '0' .. '9' )+ )
            // Velvet.g:247:12: ( 'e' | 'E' ) ( '+' | '-' )? ( '0' .. '9' )+
            {
            if ( input.LA(1)=='E'||input.LA(1)=='e' ) {
                input.consume();
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;
            }


            // Velvet.g:247:22: ( '+' | '-' )?
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


            // Velvet.g:247:33: ( '0' .. '9' )+
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
            // Velvet.g:250:11: ( ( '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' ) )
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
            // Velvet.g:254:5: ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\\\"' | '\\'' | '\\\\' ) | UNICODE_ESC | OCTAL_ESC )
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
                    // Velvet.g:254:9: '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\\\"' | '\\'' | '\\\\' )
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
                    // Velvet.g:255:9: UNICODE_ESC
                    {
                    mUNICODE_ESC(); 


                    }
                    break;
                case 3 :
                    // Velvet.g:256:9: OCTAL_ESC
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
            // Velvet.g:261:5: ( '\\\\' ( '0' .. '3' ) ( '0' .. '7' ) ( '0' .. '7' ) | '\\\\' ( '0' .. '7' ) ( '0' .. '7' ) | '\\\\' ( '0' .. '7' ) )
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
                    // Velvet.g:261:9: '\\\\' ( '0' .. '3' ) ( '0' .. '7' ) ( '0' .. '7' )
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
                    // Velvet.g:262:9: '\\\\' ( '0' .. '7' ) ( '0' .. '7' )
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
                    // Velvet.g:263:9: '\\\\' ( '0' .. '7' )
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
            // Velvet.g:268:5: ( '\\\\' 'u' HEX_DIGIT HEX_DIGIT HEX_DIGIT HEX_DIGIT )
            // Velvet.g:268:9: '\\\\' 'u' HEX_DIGIT HEX_DIGIT HEX_DIGIT HEX_DIGIT
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
            // Velvet.g:270:5: ( ( ' ' | '\\t' | '\\r' | '\\n' ) )
            // Velvet.g:270:7: ( ' ' | '\\t' | '\\r' | '\\n' )
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

    // $ANTLR start "SL_COMMENT"
    public final void mSL_COMMENT() throws RecognitionException {
        try {
            int _type = SL_COMMENT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:277:12: ( ( '//' (~ ( '\\r' | '\\n' ) )* ) )
            // Velvet.g:277:14: ( '//' (~ ( '\\r' | '\\n' ) )* )
            {
            // Velvet.g:277:14: ( '//' (~ ( '\\r' | '\\n' ) )* )
            // Velvet.g:277:15: '//' (~ ( '\\r' | '\\n' ) )*
            {
            match("//"); 



            // Velvet.g:277:20: (~ ( '\\r' | '\\n' ) )*
            loop17:
            do {
                int alt17=2;
                int LA17_0 = input.LA(1);

                if ( ((LA17_0 >= '\u0000' && LA17_0 <= '\t')||(LA17_0 >= '\u000B' && LA17_0 <= '\f')||(LA17_0 >= '\u000E' && LA17_0 <= '\uFFFF')) ) {
                    alt17=1;
                }


                switch (alt17) {
            	case 1 :
            	    // Velvet.g:
            	    {
            	    if ( (input.LA(1) >= '\u0000' && input.LA(1) <= '\t')||(input.LA(1) >= '\u000B' && input.LA(1) <= '\f')||(input.LA(1) >= '\u000E' && input.LA(1) <= '\uFFFF') ) {
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
            	    break loop17;
                }
            } while (true);


            }


            skip();

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "SL_COMMENT"

    // $ANTLR start "ML_COMMENT"
    public final void mML_COMMENT() throws RecognitionException {
        try {
            int _type = ML_COMMENT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Velvet.g:279:12: ( ( '/*' (~ ( '*/' ) )* ) )
            // Velvet.g:279:14: ( '/*' (~ ( '*/' ) )* )
            {
            // Velvet.g:279:14: ( '/*' (~ ( '*/' ) )* )
            // Velvet.g:279:15: '/*' (~ ( '*/' ) )*
            {
            match("/*"); 



            // Velvet.g:279:20: (~ ( '*/' ) )*
            loop18:
            do {
                int alt18=2;
                int LA18_0 = input.LA(1);

                if ( ((LA18_0 >= '\u0000' && LA18_0 <= '\uFFFF')) ) {
                    alt18=1;
                }


                switch (alt18) {
            	case 1 :
            	    // Velvet.g:279:20: ~ ( '*/' )
            	    {
            	    if ( (input.LA(1) >= '\u0000' && input.LA(1) <= '\uFFFF') ) {
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
            	    break loop18;
                }
            } while (true);


            }


            skip();

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "ML_COMMENT"

    public void mTokens() throws RecognitionException {
        // Velvet.g:1:8: ( ABSTRACT | ATTR_OP_EQUALS | ATTR_OP_GREATER | ATTR_OP_GREATER_EQ | ATTR_OP_LESS | ATTR_OP_LESS_EQ | ATTR_OP_NOT_EQUALS | CINTERFACE | COLON | COMMA | CONCEPT | CONSTRAINT | END_C | END_R | EQ | FEATURE | IMPORTINSTANCE | IMPORTINTERFACE | MANDATORY | MINUS | ONEOF | OP_AND | OP_EQUIVALENT | OP_IMPLIES | OP_NOT | OP_OR | OP_XOR | PLUS | SEMI | SOMEOF | START_C | START_R | USE | VAR_BOOL | VAR_FLOAT | VAR_INT | VAR_STRING | BOOLEAN | ID | IDPath | INT | FLOAT | STRING | WS | SL_COMMENT | ML_COMMENT )
        int alt19=46;
        alt19 = dfa19.predict(input);
        switch (alt19) {
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
                // Velvet.g:1:117: CINTERFACE
                {
                mCINTERFACE(); 


                }
                break;
            case 9 :
                // Velvet.g:1:128: COLON
                {
                mCOLON(); 


                }
                break;
            case 10 :
                // Velvet.g:1:134: COMMA
                {
                mCOMMA(); 


                }
                break;
            case 11 :
                // Velvet.g:1:140: CONCEPT
                {
                mCONCEPT(); 


                }
                break;
            case 12 :
                // Velvet.g:1:148: CONSTRAINT
                {
                mCONSTRAINT(); 


                }
                break;
            case 13 :
                // Velvet.g:1:159: END_C
                {
                mEND_C(); 


                }
                break;
            case 14 :
                // Velvet.g:1:165: END_R
                {
                mEND_R(); 


                }
                break;
            case 15 :
                // Velvet.g:1:171: EQ
                {
                mEQ(); 


                }
                break;
            case 16 :
                // Velvet.g:1:174: FEATURE
                {
                mFEATURE(); 


                }
                break;
            case 17 :
                // Velvet.g:1:182: IMPORTINSTANCE
                {
                mIMPORTINSTANCE(); 


                }
                break;
            case 18 :
                // Velvet.g:1:197: IMPORTINTERFACE
                {
                mIMPORTINTERFACE(); 


                }
                break;
            case 19 :
                // Velvet.g:1:213: MANDATORY
                {
                mMANDATORY(); 


                }
                break;
            case 20 :
                // Velvet.g:1:223: MINUS
                {
                mMINUS(); 


                }
                break;
            case 21 :
                // Velvet.g:1:229: ONEOF
                {
                mONEOF(); 


                }
                break;
            case 22 :
                // Velvet.g:1:235: OP_AND
                {
                mOP_AND(); 


                }
                break;
            case 23 :
                // Velvet.g:1:242: OP_EQUIVALENT
                {
                mOP_EQUIVALENT(); 


                }
                break;
            case 24 :
                // Velvet.g:1:256: OP_IMPLIES
                {
                mOP_IMPLIES(); 


                }
                break;
            case 25 :
                // Velvet.g:1:267: OP_NOT
                {
                mOP_NOT(); 


                }
                break;
            case 26 :
                // Velvet.g:1:274: OP_OR
                {
                mOP_OR(); 


                }
                break;
            case 27 :
                // Velvet.g:1:280: OP_XOR
                {
                mOP_XOR(); 


                }
                break;
            case 28 :
                // Velvet.g:1:287: PLUS
                {
                mPLUS(); 


                }
                break;
            case 29 :
                // Velvet.g:1:292: SEMI
                {
                mSEMI(); 


                }
                break;
            case 30 :
                // Velvet.g:1:297: SOMEOF
                {
                mSOMEOF(); 


                }
                break;
            case 31 :
                // Velvet.g:1:304: START_C
                {
                mSTART_C(); 


                }
                break;
            case 32 :
                // Velvet.g:1:312: START_R
                {
                mSTART_R(); 


                }
                break;
            case 33 :
                // Velvet.g:1:320: USE
                {
                mUSE(); 


                }
                break;
            case 34 :
                // Velvet.g:1:324: VAR_BOOL
                {
                mVAR_BOOL(); 


                }
                break;
            case 35 :
                // Velvet.g:1:333: VAR_FLOAT
                {
                mVAR_FLOAT(); 


                }
                break;
            case 36 :
                // Velvet.g:1:343: VAR_INT
                {
                mVAR_INT(); 


                }
                break;
            case 37 :
                // Velvet.g:1:351: VAR_STRING
                {
                mVAR_STRING(); 


                }
                break;
            case 38 :
                // Velvet.g:1:362: BOOLEAN
                {
                mBOOLEAN(); 


                }
                break;
            case 39 :
                // Velvet.g:1:370: ID
                {
                mID(); 


                }
                break;
            case 40 :
                // Velvet.g:1:373: IDPath
                {
                mIDPath(); 


                }
                break;
            case 41 :
                // Velvet.g:1:380: INT
                {
                mINT(); 


                }
                break;
            case 42 :
                // Velvet.g:1:384: FLOAT
                {
                mFLOAT(); 


                }
                break;
            case 43 :
                // Velvet.g:1:390: STRING
                {
                mSTRING(); 


                }
                break;
            case 44 :
                // Velvet.g:1:397: WS
                {
                mWS(); 


                }
                break;
            case 45 :
                // Velvet.g:1:400: SL_COMMENT
                {
                mSL_COMMENT(); 


                }
                break;
            case 46 :
                // Velvet.g:1:411: ML_COMMENT
                {
                mML_COMMENT(); 


                }
                break;

        }

    }


    protected DFA11 dfa11 = new DFA11(this);
    protected DFA19 dfa19 = new DFA19(this);
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
            return "235:1: FLOAT : ( ( '0' .. '9' )+ '.' ( '0' .. '9' )* ( EXPONENT )? | '.' ( '0' .. '9' )+ ( EXPONENT )? | ( '0' .. '9' )+ EXPONENT );";
        }
    }
    static final String DFA19_eotS =
        "\1\uffff\1\43\1\46\1\50\1\53\1\55\1\43\4\uffff\3\43\1\66\1\43\2"+
        "\uffff\1\43\2\uffff\1\43\2\uffff\4\43\1\76\4\uffff\2\43\13\uffff"+
        "\7\43\2\uffff\7\43\3\uffff\7\43\1\132\2\43\1\135\2\43\1\140\13\43"+
        "\1\uffff\2\43\1\uffff\2\43\1\uffff\1\160\1\161\5\43\1\167\1\161"+
        "\3\43\1\173\2\43\2\uffff\5\43\1\uffff\3\43\1\uffff\1\u0086\1\u0087"+
        "\2\43\1\u008a\1\43\1\u008c\3\43\2\uffff\1\u0090\1\43\1\uffff\1\43"+
        "\1\uffff\1\u0093\2\43\1\uffff\2\43\1\uffff\1\u0098\1\u0099\1\u009a"+
        "\1\u009b\4\uffff";
    static final String DFA19_eofS =
        "\u009c\uffff";
    static final String DFA19_minS =
        "\1\11\1\55\2\75\1\55\1\75\1\55\4\uffff\5\55\2\uffff\1\55\2\uffff"+
        "\1\55\2\uffff\4\55\1\56\3\uffff\1\52\2\55\13\uffff\7\55\2\uffff"+
        "\7\55\3\uffff\31\55\1\uffff\2\55\1\uffff\2\55\1\uffff\17\55\2\uffff"+
        "\5\55\1\uffff\3\55\1\uffff\12\55\2\uffff\2\55\1\uffff\1\55\1\uffff"+
        "\3\55\1\uffff\2\55\1\uffff\4\55\4\uffff";
    static final String DFA19_maxS =
        "\1\175\1\172\4\75\1\172\4\uffff\5\172\2\uffff\1\172\2\uffff\1\172"+
        "\2\uffff\4\172\1\145\3\uffff\1\57\2\172\13\uffff\7\172\2\uffff\7"+
        "\172\3\uffff\31\172\1\uffff\2\172\1\uffff\2\172\1\uffff\17\172\2"+
        "\uffff\5\172\1\uffff\3\172\1\uffff\12\172\2\uffff\2\172\1\uffff"+
        "\1\172\1\uffff\3\172\1\uffff\2\172\1\uffff\4\172\4\uffff";
    static final String DFA19_acceptS =
        "\7\uffff\1\11\1\12\1\15\1\16\5\uffff\1\26\1\32\1\uffff\1\34\1\35"+
        "\1\uffff\1\37\1\40\5\uffff\1\52\1\53\1\54\3\uffff\1\47\1\50\1\2"+
        "\1\17\1\4\1\3\1\6\1\27\1\5\1\7\1\31\7\uffff\1\30\1\24\7\uffff\1"+
        "\51\1\55\1\56\31\uffff\1\44\2\uffff\1\33\2\uffff\1\41\17\uffff\1"+
        "\42\1\46\5\uffff\1\43\3\uffff\1\25\12\uffff\1\36\1\45\2\uffff\1"+
        "\13\1\uffff\1\20\3\uffff\1\1\2\uffff\1\21\4\uffff\1\22\1\23\1\10"+
        "\1\14";
    static final String DFA19_specialS =
        "\u009c\uffff}>";
    static final String[] DFA19_transitionS = {
            "\2\37\2\uffff\1\37\22\uffff\1\37\1\5\1\36\3\uffff\1\20\1\uffff"+
            "\1\27\1\12\1\uffff\1\23\1\10\1\16\1\35\1\40\12\34\1\7\1\24\1"+
            "\4\1\2\1\3\2\uffff\32\33\4\uffff\1\33\1\uffff\1\1\1\31\1\6\2"+
            "\33\1\13\2\33\1\14\3\33\1\15\1\33\1\17\3\33\1\25\1\32\1\30\2"+
            "\33\1\22\2\33\1\26\1\21\1\11",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\1\42\1\41\30\42",
            "\1\45",
            "\1\47",
            "\1\52\17\uffff\1\51",
            "\1\54",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\10\42\1\56\5\42\1\57\13\42",
            "",
            "",
            "",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\1\62\3\42\1\60\6\42\1\61\16\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\15\42\1\63\14\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\1\64\31\42",
            "\1\42\1\44\1\uffff\12\42\4\uffff\1\65\2\uffff\32\42\4\uffff"+
            "\1\42\1\uffff\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\15\42\1\67\14\42",
            "",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\16\42\1\70\13\42",
            "",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\16\42\1\71\4\42\1\72\6\42",
            "",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\22\42\1\73\7\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\16\42\1\74\13\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\21\42\1\75\10\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\35\1\uffff\12\34\13\uffff\1\35\37\uffff\1\35",
            "",
            "",
            "",
            "\1\100\4\uffff\1\77",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\22\42\1\101\7\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
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
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\15\42\1\102\14\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\15\42\1\103\14\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\1\104\31\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\16\42\1\105\13\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\13\42\1\106\16\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\22\42\1\107\1\110\6\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\15\42\1\111\14\42",
            "",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\4\42\1\112\25\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\21\42\1\113\10\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\14\42\1\114\15\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\21\42\1\115\10\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\4\42\1\116\25\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\16\42\1\117\13\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\24\42\1\120\5\42",
            "",
            "",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\23\42\1\121\6\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\23\42\1\122\6\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\2\42\1\123\17\42\1\124\7\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\23\42\1\125\6\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\1\126\31\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\22\42\1\127\7\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\23\42\1\130\6\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\4\42\1\131\25\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\3\42\1\133\26\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\16\42\1\134\13\42\4\uffff"+
            "\1\42\1\uffff\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\4\42\1\136\25\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\10\42\1\137\21\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\13\42\1\141\16\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\4\42\1\142\25\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\21\42\1\143\10\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\4\42\1\144\25\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\4\42\1\145\25\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\23\42\1\146\6\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\24\42\1\147\5\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\23\42\1\150\6\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\4\42\1\151\25\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\1\152\31\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\21\42\1\153\10\42",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\1\154\31\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\5\42\1\155\24\42",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\16\42\1\156\13\42\4\uffff"+
            "\1\42\1\uffff\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\15\42\1\157\14\42",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\1\162\31\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\21\42\1\163\10\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\17\42\1\164\12\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\21\42\1\165\10\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\21\42\1\166\10\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\15\42\1\170\14\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\5\42\1\171\24\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\23\42\1\172\6\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\5\42\1\174\24\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\6\42\1\175\23\42",
            "",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\2\42\1\176\27\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\5\42\1\177\24\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\23\42\1\u0080\6\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\1\u0081\31\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\4\42\1\u0082\25\42",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\2\42\1\u0083\27\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\1\u0084\31\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\16\42\1\u0085\13\42",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\23\42\1\u0088\6\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\1\u0089\31\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\10\42\1\u008b\21\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\4\42\1\u008d\25\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\2\42\1\u008e\27\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\21\42\1\u008f\10\42",
            "",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\2\42\1\u0091\27\42",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\15\42\1\u0092\14\42",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\4\42\1\u0094\25\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\30\42\1\u0095\1\42",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\4\42\1\u0096\25\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\23\42\1\u0097\6\42",
            "",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "\1\42\1\44\1\uffff\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff"+
            "\32\42",
            "",
            "",
            "",
            ""
    };

    static final short[] DFA19_eot = DFA.unpackEncodedString(DFA19_eotS);
    static final short[] DFA19_eof = DFA.unpackEncodedString(DFA19_eofS);
    static final char[] DFA19_min = DFA.unpackEncodedStringToUnsignedChars(DFA19_minS);
    static final char[] DFA19_max = DFA.unpackEncodedStringToUnsignedChars(DFA19_maxS);
    static final short[] DFA19_accept = DFA.unpackEncodedString(DFA19_acceptS);
    static final short[] DFA19_special = DFA.unpackEncodedString(DFA19_specialS);
    static final short[][] DFA19_transition;

    static {
        int numStates = DFA19_transitionS.length;
        DFA19_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA19_transition[i] = DFA.unpackEncodedString(DFA19_transitionS[i]);
        }
    }

    class DFA19 extends DFA {

        public DFA19(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 19;
            this.eot = DFA19_eot;
            this.eof = DFA19_eof;
            this.min = DFA19_min;
            this.max = DFA19_max;
            this.accept = DFA19_accept;
            this.special = DFA19_special;
            this.transition = DFA19_transition;
        }
        public String getDescription() {
            return "1:1: Tokens : ( ABSTRACT | ATTR_OP_EQUALS | ATTR_OP_GREATER | ATTR_OP_GREATER_EQ | ATTR_OP_LESS | ATTR_OP_LESS_EQ | ATTR_OP_NOT_EQUALS | CINTERFACE | COLON | COMMA | CONCEPT | CONSTRAINT | END_C | END_R | EQ | FEATURE | IMPORTINSTANCE | IMPORTINTERFACE | MANDATORY | MINUS | ONEOF | OP_AND | OP_EQUIVALENT | OP_IMPLIES | OP_NOT | OP_OR | OP_XOR | PLUS | SEMI | SOMEOF | START_C | START_R | USE | VAR_BOOL | VAR_FLOAT | VAR_INT | VAR_STRING | BOOLEAN | ID | IDPath | INT | FLOAT | STRING | WS | SL_COMMENT | ML_COMMENT );";
        }
    }
 

}