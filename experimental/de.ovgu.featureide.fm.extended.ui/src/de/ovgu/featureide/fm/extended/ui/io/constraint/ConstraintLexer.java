/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
// $ANTLR 3.3 Nov 30, 2010 12:45:30 /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g 2011-04-19 18:20:42

package de.ovgu.featureide.fm.extended.ui.io.constraint;


import org.antlr.runtime.CharStream;
import org.antlr.runtime.Lexer;
import org.antlr.runtime.MismatchedSetException;
import org.antlr.runtime.NoViableAltException;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.RecognizerSharedState;

public class ConstraintLexer extends Lexer {
    public static final int EOF=-1;
    public static final int T__12=12;
    public static final int T__13=13;
    public static final int SEMICOLON=4;
    public static final int NEGATIVE=5;
    public static final int ATTRIBUTE=6;
    public static final int ATTRIBUTE_SUM=7;
    public static final int RELATION=8;
    public static final int IDENTIFIER=9;
    public static final int NUMBER=10;
    public static final int WS=11;

    	private boolean error = false;

    	@Override
    	public void reportError(RecognitionException e) {
    		this.error = true;
    		//super.reportError(e);
    	}

    	public boolean hadError() {
    		return error;
    	}


    // delegates
    // delegators

    public ConstraintLexer() {;} 
    public ConstraintLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public ConstraintLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);

    }
    public String getGrammarFileName() { return "/home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g"; }

    // $ANTLR start "SEMICOLON"
    public final void mSEMICOLON() throws RecognitionException {
        try {
            int _type = SEMICOLON;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:20:11: ( ';' )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:20:13: ';'
            {
            match(';'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SEMICOLON"

    // $ANTLR start "NEGATIVE"
    public final void mNEGATIVE() throws RecognitionException {
        try {
            int _type = NEGATIVE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:21:10: ( '~' )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:21:12: '~'
            {
            match('~'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "NEGATIVE"

    // $ANTLR start "ATTRIBUTE"
    public final void mATTRIBUTE() throws RecognitionException {
        try {
            int _type = ATTRIBUTE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:22:11: ( '.' )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:22:13: '.'
            {
            match('.'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ATTRIBUTE"

    // $ANTLR start "ATTRIBUTE_SUM"
    public final void mATTRIBUTE_SUM() throws RecognitionException {
        try {
            int _type = ATTRIBUTE_SUM;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:23:15: ( '#' )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:23:17: '#'
            {
            match('#'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ATTRIBUTE_SUM"

    // $ANTLR start "T__12"
    public final void mT__12() throws RecognitionException {
        try {
            int _type = T__12;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:24:7: ( '-' )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:24:9: '-'
            {
            match('-'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__12"

    // $ANTLR start "T__13"
    public final void mT__13() throws RecognitionException {
        try {
            int _type = T__13;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:25:7: ( '+' )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:25:9: '+'
            {
            match('+'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__13"

    // $ANTLR start "RELATION"
    public final void mRELATION() throws RecognitionException {
        try {
            int _type = RELATION;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:81:10: ( '>=' | '=' | '<=' )
            int alt1=3;
            switch ( input.LA(1) ) {
            case '>':
                {
                alt1=1;
                }
                break;
            case '=':
                {
                alt1=2;
                }
                break;
            case '<':
                {
                alt1=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 1, 0, input);

                throw nvae;
            }

            switch (alt1) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:81:12: '>='
                    {
                    match(">="); 


                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:81:19: '='
                    {
                    match('='); 

                    }
                    break;
                case 3 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:81:25: '<='
                    {
                    match("<="); 


                    }
                    break;

            }
            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RELATION"

    // $ANTLR start "NUMBER"
    public final void mNUMBER() throws RecognitionException {
        try {
            int _type = NUMBER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:94:8: ( '0' | ( '1' .. '9' ) ( '0' .. '9' )* )
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0=='0') ) {
                alt3=1;
            }
            else if ( ((LA3_0>='1' && LA3_0<='9')) ) {
                alt3=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;
            }
            switch (alt3) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:94:10: '0'
                    {
                    match('0'); 

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:94:16: ( '1' .. '9' ) ( '0' .. '9' )*
                    {
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:94:16: ( '1' .. '9' )
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:94:17: '1' .. '9'
                    {
                    matchRange('1','9'); 

                    }

                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:94:27: ( '0' .. '9' )*
                    loop2:
                    do {
                        int alt2=2;
                        int LA2_0 = input.LA(1);

                        if ( ((LA2_0>='0' && LA2_0<='9')) ) {
                            alt2=1;
                        }


                        switch (alt2) {
                    	case 1 :
                    	    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:94:28: '0' .. '9'
                    	    {
                    	    matchRange('0','9'); 

                    	    }
                    	    break;

                    	default :
                    	    break loop2;
                        }
                    } while (true);


                    }
                    break;

            }
            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "NUMBER"

    // $ANTLR start "IDENTIFIER"
    public final void mIDENTIFIER() throws RecognitionException {
        try {
            int _type = IDENTIFIER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:96:12: ( ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )* )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:96:14: ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )*
            {
            if ( (input.LA(1)>='A' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}

            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:96:38: ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )*
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( ((LA4_0>='0' && LA4_0<='9')||(LA4_0>='A' && LA4_0<='Z')||LA4_0=='_'||(LA4_0>='a' && LA4_0<='z')) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:
            	    {
            	    if ( (input.LA(1)>='0' && input.LA(1)<='9')||(input.LA(1)>='A' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    break loop4;
                }
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "IDENTIFIER"

    // $ANTLR start "WS"
    public final void mWS() throws RecognitionException {
        try {
            int _type = WS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:98:4: ( ( ' ' | '\\t' | '\\f' | '\\n' | '\\r' ) )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:98:6: ( ' ' | '\\t' | '\\f' | '\\n' | '\\r' )
            {
            if ( (input.LA(1)>='\t' && input.LA(1)<='\n')||(input.LA(1)>='\f' && input.LA(1)<='\r')||input.LA(1)==' ' ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}

             _channel=HIDDEN; 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "WS"

    public void mTokens() throws RecognitionException {
        // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:1:8: ( SEMICOLON | NEGATIVE | ATTRIBUTE | ATTRIBUTE_SUM | T__12 | T__13 | RELATION | NUMBER | IDENTIFIER | WS )
        int alt5=10;
        switch ( input.LA(1) ) {
        case ';':
            {
            alt5=1;
            }
            break;
        case '~':
            {
            alt5=2;
            }
            break;
        case '.':
            {
            alt5=3;
            }
            break;
        case '#':
            {
            alt5=4;
            }
            break;
        case '-':
            {
            alt5=5;
            }
            break;
        case '+':
            {
            alt5=6;
            }
            break;
        case '<':
        case '=':
        case '>':
            {
            alt5=7;
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
        case '8':
        case '9':
            {
            alt5=8;
            }
            break;
        case 'A':
        case 'B':
        case 'C':
        case 'D':
        case 'E':
        case 'F':
        case 'G':
        case 'H':
        case 'I':
        case 'J':
        case 'K':
        case 'L':
        case 'M':
        case 'N':
        case 'O':
        case 'P':
        case 'Q':
        case 'R':
        case 'S':
        case 'T':
        case 'U':
        case 'V':
        case 'W':
        case 'X':
        case 'Y':
        case 'Z':
        case '_':
        case 'a':
        case 'b':
        case 'c':
        case 'd':
        case 'e':
        case 'f':
        case 'g':
        case 'h':
        case 'i':
        case 'j':
        case 'k':
        case 'l':
        case 'm':
        case 'n':
        case 'o':
        case 'p':
        case 'q':
        case 'r':
        case 's':
        case 't':
        case 'u':
        case 'v':
        case 'w':
        case 'x':
        case 'y':
        case 'z':
            {
            alt5=9;
            }
            break;
        case '\t':
        case '\n':
        case '\f':
        case '\r':
        case ' ':
            {
            alt5=10;
            }
            break;
        default:
            NoViableAltException nvae =
                new NoViableAltException("", 5, 0, input);

            throw nvae;
        }

        switch (alt5) {
            case 1 :
                // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:1:10: SEMICOLON
                {
                mSEMICOLON(); 

                }
                break;
            case 2 :
                // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:1:20: NEGATIVE
                {
                mNEGATIVE(); 

                }
                break;
            case 3 :
                // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:1:29: ATTRIBUTE
                {
                mATTRIBUTE(); 

                }
                break;
            case 4 :
                // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:1:39: ATTRIBUTE_SUM
                {
                mATTRIBUTE_SUM(); 

                }
                break;
            case 5 :
                // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:1:53: T__12
                {
                mT__12(); 

                }
                break;
            case 6 :
                // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:1:59: T__13
                {
                mT__13(); 

                }
                break;
            case 7 :
                // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:1:65: RELATION
                {
                mRELATION(); 

                }
                break;
            case 8 :
                // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:1:74: NUMBER
                {
                mNUMBER(); 

                }
                break;
            case 9 :
                // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:1:81: IDENTIFIER
                {
                mIDENTIFIER(); 

                }
                break;
            case 10 :
                // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:1:92: WS
                {
                mWS(); 

                }
                break;

        }

    }


 

}
