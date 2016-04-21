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
// $ANTLR 3.3 Nov 30, 2010 12:45:30 /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g 2011-04-19 19:07:18

package de.ovgu.featureide.fm.extended.ui.io.objective;


import org.antlr.runtime.CharStream;
import org.antlr.runtime.Lexer;
import org.antlr.runtime.MismatchedSetException;
import org.antlr.runtime.NoViableAltException;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.RecognizerSharedState;

public class ObjectiveLexer extends Lexer {
    public static final int EOF=-1;
    public static final int T__11=11;
    public static final int T__12=12;
    public static final int SEMICOLON=4;
    public static final int NEGATIVE=5;
    public static final int ATTRIBUTE=6;
    public static final int ATTRIBUTE_SUM=7;
    public static final int IDENTIFIER=8;
    public static final int NUMBER=9;
    public static final int WS=10;

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

    public ObjectiveLexer() {;} 
    public ObjectiveLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public ObjectiveLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);

    }
    public String getGrammarFileName() { return "/home/sibi/workspace_old/Utilities/src/io/objective/Objective.g"; }

    // $ANTLR start "SEMICOLON"
    public final void mSEMICOLON() throws RecognitionException {
        try {
            int _type = SEMICOLON;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:20:11: ( ';' )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:20:13: ';'
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
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:21:10: ( '~' )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:21:12: '~'
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
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:22:11: ( '.' )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:22:13: '.'
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
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:23:15: ( '#' )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:23:17: '#'
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

    // $ANTLR start "T__11"
    public final void mT__11() throws RecognitionException {
        try {
            int _type = T__11;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:24:7: ( '-' )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:24:9: '-'
            {
            match('-'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__11"

    // $ANTLR start "T__12"
    public final void mT__12() throws RecognitionException {
        try {
            int _type = T__12;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:25:7: ( '+' )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:25:9: '+'
            {
            match('+'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__12"

    // $ANTLR start "NUMBER"
    public final void mNUMBER() throws RecognitionException {
        try {
            int _type = NUMBER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:92:8: ( '0' | ( '1' .. '9' ) ( '0' .. '9' )* )
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0=='0') ) {
                alt2=1;
            }
            else if ( ((LA2_0>='1' && LA2_0<='9')) ) {
                alt2=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 2, 0, input);

                throw nvae;
            }
            switch (alt2) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:92:10: '0'
                    {
                    match('0'); 

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:92:16: ( '1' .. '9' ) ( '0' .. '9' )*
                    {
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:92:16: ( '1' .. '9' )
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:92:17: '1' .. '9'
                    {
                    matchRange('1','9'); 

                    }

                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:92:27: ( '0' .. '9' )*
                    loop1:
                    do {
                        int alt1=2;
                        int LA1_0 = input.LA(1);

                        if ( ((LA1_0>='0' && LA1_0<='9')) ) {
                            alt1=1;
                        }


                        switch (alt1) {
                    	case 1 :
                    	    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:92:28: '0' .. '9'
                    	    {
                    	    matchRange('0','9'); 

                    	    }
                    	    break;

                    	default :
                    	    break loop1;
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
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:94:12: ( ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )* )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:94:14: ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )*
            {
            if ( (input.LA(1)>='A' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}

            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:94:38: ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( ((LA3_0>='0' && LA3_0<='9')||(LA3_0>='A' && LA3_0<='Z')||LA3_0=='_'||(LA3_0>='a' && LA3_0<='z')) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:
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
            	    break loop3;
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
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:96:4: ( ( ' ' | '\\t' | '\\f' | '\\n' | '\\r' ) )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:96:6: ( ' ' | '\\t' | '\\f' | '\\n' | '\\r' )
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
        // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:1:8: ( SEMICOLON | NEGATIVE | ATTRIBUTE | ATTRIBUTE_SUM | T__11 | T__12 | NUMBER | IDENTIFIER | WS )
        int alt4=9;
        switch ( input.LA(1) ) {
        case ';':
            {
            alt4=1;
            }
            break;
        case '~':
            {
            alt4=2;
            }
            break;
        case '.':
            {
            alt4=3;
            }
            break;
        case '#':
            {
            alt4=4;
            }
            break;
        case '-':
            {
            alt4=5;
            }
            break;
        case '+':
            {
            alt4=6;
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
            alt4=7;
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
            alt4=8;
            }
            break;
        case '\t':
        case '\n':
        case '\f':
        case '\r':
        case ' ':
            {
            alt4=9;
            }
            break;
        default:
            NoViableAltException nvae =
                new NoViableAltException("", 4, 0, input);

            throw nvae;
        }

        switch (alt4) {
            case 1 :
                // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:1:10: SEMICOLON
                {
                mSEMICOLON(); 

                }
                break;
            case 2 :
                // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:1:20: NEGATIVE
                {
                mNEGATIVE(); 

                }
                break;
            case 3 :
                // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:1:29: ATTRIBUTE
                {
                mATTRIBUTE(); 

                }
                break;
            case 4 :
                // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:1:39: ATTRIBUTE_SUM
                {
                mATTRIBUTE_SUM(); 

                }
                break;
            case 5 :
                // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:1:53: T__11
                {
                mT__11(); 

                }
                break;
            case 6 :
                // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:1:59: T__12
                {
                mT__12(); 

                }
                break;
            case 7 :
                // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:1:65: NUMBER
                {
                mNUMBER(); 

                }
                break;
            case 8 :
                // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:1:72: IDENTIFIER
                {
                mIDENTIFIER(); 

                }
                break;
            case 9 :
                // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:1:83: WS
                {
                mWS(); 

                }
                break;

        }

    }


 

}
