package org.deltaj.parser.antlr.internal;

// Hack: Use our own Lexer superclass by means of import. 
// Currently there is no other way to specify the superclass for the lexer.
import org.eclipse.xtext.parser.antlr.Lexer;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

@SuppressWarnings("all")
public class InternalDeltaJLexer extends Lexer {
    public static final int RULE_ID=5;
    public static final int T__64=64;
    public static final int T__29=29;
    public static final int T__28=28;
    public static final int T__27=27;
    public static final int T__62=62;
    public static final int T__26=26;
    public static final int T__63=63;
    public static final int T__25=25;
    public static final int T__24=24;
    public static final int T__23=23;
    public static final int T__22=22;
    public static final int T__21=21;
    public static final int RULE_ANY_OTHER=11;
    public static final int T__20=20;
    public static final int T__61=61;
    public static final int EOF=-1;
    public static final int T__60=60;
    public static final int T__55=55;
    public static final int T__56=56;
    public static final int T__19=19;
    public static final int T__57=57;
    public static final int T__58=58;
    public static final int T__16=16;
    public static final int T__51=51;
    public static final int T__52=52;
    public static final int T__15=15;
    public static final int T__53=53;
    public static final int T__18=18;
    public static final int T__54=54;
    public static final int T__17=17;
    public static final int T__12=12;
    public static final int T__14=14;
    public static final int T__13=13;
    public static final int T__59=59;
    public static final int RULE_INT=4;
    public static final int T__50=50;
    public static final int T__42=42;
    public static final int T__43=43;
    public static final int T__40=40;
    public static final int T__41=41;
    public static final int T__46=46;
    public static final int T__47=47;
    public static final int T__44=44;
    public static final int T__45=45;
    public static final int T__48=48;
    public static final int T__49=49;
    public static final int RULE_SL_COMMENT=9;
    public static final int RULE_ML_COMMENT=8;
    public static final int T__30=30;
    public static final int T__31=31;
    public static final int T__32=32;
    public static final int RULE_STRING=7;
    public static final int T__33=33;
    public static final int T__34=34;
    public static final int T__35=35;
    public static final int T__36=36;
    public static final int T__37=37;
    public static final int T__38=38;
    public static final int T__39=39;
    public static final int RULE_WS=10;
    public static final int RULE_JAVAVERBATIM=6;

    // delegates
    // delegators

    public InternalDeltaJLexer() {;} 
    public InternalDeltaJLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public InternalDeltaJLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);

    }
    public String getGrammarFileName() { return "../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g"; }

    // $ANTLR start "T__12"
    public final void mT__12() throws RecognitionException {
        try {
            int _type = T__12;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:11:7: ( '<' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:11:9: '<'
            {
            match('<'); 

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
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:12:7: ( '>' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:12:9: '>'
            {
            match('>'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__13"

    // $ANTLR start "T__14"
    public final void mT__14() throws RecognitionException {
        try {
            int _type = T__14;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:13:7: ( 'void' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:13:9: 'void'
            {
            match("void"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__14"

    // $ANTLR start "T__15"
    public final void mT__15() throws RecognitionException {
        try {
            int _type = T__15;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:14:7: ( 'int' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:14:9: 'int'
            {
            match("int"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__15"

    // $ANTLR start "T__16"
    public final void mT__16() throws RecognitionException {
        try {
            int _type = T__16;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:15:7: ( 'boolean' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:15:9: 'boolean'
            {
            match("boolean"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__16"

    // $ANTLR start "T__17"
    public final void mT__17() throws RecognitionException {
        try {
            int _type = T__17;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:16:7: ( 'String' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:16:9: 'String'
            {
            match("String"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__17"

    // $ANTLR start "T__18"
    public final void mT__18() throws RecognitionException {
        try {
            int _type = T__18;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:17:7: ( 'class' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:17:9: 'class'
            {
            match("class"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__18"

    // $ANTLR start "T__19"
    public final void mT__19() throws RecognitionException {
        try {
            int _type = T__19;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:18:7: ( 'extends' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:18:9: 'extends'
            {
            match("extends"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__19"

    // $ANTLR start "T__20"
    public final void mT__20() throws RecognitionException {
        try {
            int _type = T__20;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:19:7: ( '{' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:19:9: '{'
            {
            match('{'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__20"

    // $ANTLR start "T__21"
    public final void mT__21() throws RecognitionException {
        try {
            int _type = T__21;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:20:7: ( '}' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:20:9: '}'
            {
            match('}'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__21"

    // $ANTLR start "T__22"
    public final void mT__22() throws RecognitionException {
        try {
            int _type = T__22;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:21:7: ( ';' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:21:9: ';'
            {
            match(';'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__22"

    // $ANTLR start "T__23"
    public final void mT__23() throws RecognitionException {
        try {
            int _type = T__23;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:22:7: ( '(' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:22:9: '('
            {
            match('('); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__23"

    // $ANTLR start "T__24"
    public final void mT__24() throws RecognitionException {
        try {
            int _type = T__24;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:23:7: ( ',' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:23:9: ','
            {
            match(','); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__24"

    // $ANTLR start "T__25"
    public final void mT__25() throws RecognitionException {
        try {
            int _type = T__25;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:24:7: ( ')' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:24:9: ')'
            {
            match(')'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__25"

    // $ANTLR start "T__26"
    public final void mT__26() throws RecognitionException {
        try {
            int _type = T__26;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:25:7: ( 'return' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:25:9: 'return'
            {
            match("return"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__26"

    // $ANTLR start "T__27"
    public final void mT__27() throws RecognitionException {
        try {
            int _type = T__27;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:26:7: ( '=' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:26:9: '='
            {
            match('='); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__27"

    // $ANTLR start "T__28"
    public final void mT__28() throws RecognitionException {
        try {
            int _type = T__28;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:27:7: ( 'if' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:27:9: 'if'
            {
            match("if"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__28"

    // $ANTLR start "T__29"
    public final void mT__29() throws RecognitionException {
        try {
            int _type = T__29;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:28:7: ( 'else' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:28:9: 'else'
            {
            match("else"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__29"

    // $ANTLR start "T__30"
    public final void mT__30() throws RecognitionException {
        try {
            int _type = T__30;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:29:7: ( '+' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:29:9: '+'
            {
            match('+'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__30"

    // $ANTLR start "T__31"
    public final void mT__31() throws RecognitionException {
        try {
            int _type = T__31;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:30:7: ( '-' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:30:9: '-'
            {
            match('-'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__31"

    // $ANTLR start "T__32"
    public final void mT__32() throws RecognitionException {
        try {
            int _type = T__32;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:31:7: ( '*' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:31:9: '*'
            {
            match('*'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__32"

    // $ANTLR start "T__33"
    public final void mT__33() throws RecognitionException {
        try {
            int _type = T__33;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:32:7: ( '/' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:32:9: '/'
            {
            match('/'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__33"

    // $ANTLR start "T__34"
    public final void mT__34() throws RecognitionException {
        try {
            int _type = T__34;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:33:7: ( '>=' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:33:9: '>='
            {
            match(">="); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__34"

    // $ANTLR start "T__35"
    public final void mT__35() throws RecognitionException {
        try {
            int _type = T__35;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:34:7: ( '<=' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:34:9: '<='
            {
            match("<="); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__35"

    // $ANTLR start "T__36"
    public final void mT__36() throws RecognitionException {
        try {
            int _type = T__36;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:35:7: ( '==' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:35:9: '=='
            {
            match("=="); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__36"

    // $ANTLR start "T__37"
    public final void mT__37() throws RecognitionException {
        try {
            int _type = T__37;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:36:7: ( '!=' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:36:9: '!='
            {
            match("!="); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__37"

    // $ANTLR start "T__38"
    public final void mT__38() throws RecognitionException {
        try {
            int _type = T__38;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:37:7: ( '||' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:37:9: '||'
            {
            match("||"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__38"

    // $ANTLR start "T__39"
    public final void mT__39() throws RecognitionException {
        try {
            int _type = T__39;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:38:7: ( '&&' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:38:9: '&&'
            {
            match("&&"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__39"

    // $ANTLR start "T__40"
    public final void mT__40() throws RecognitionException {
        try {
            int _type = T__40;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:39:7: ( '!' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:39:9: '!'
            {
            match('!'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__40"

    // $ANTLR start "T__41"
    public final void mT__41() throws RecognitionException {
        try {
            int _type = T__41;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:40:7: ( '.' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:40:9: '.'
            {
            match('.'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__41"

    // $ANTLR start "T__42"
    public final void mT__42() throws RecognitionException {
        try {
            int _type = T__42;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:41:7: ( 'null' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:41:9: 'null'
            {
            match("null"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__42"

    // $ANTLR start "T__43"
    public final void mT__43() throws RecognitionException {
        try {
            int _type = T__43;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:42:7: ( 'this' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:42:9: 'this'
            {
            match("this"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__43"

    // $ANTLR start "T__44"
    public final void mT__44() throws RecognitionException {
        try {
            int _type = T__44;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:43:7: ( 'original' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:43:9: 'original'
            {
            match("original"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__44"

    // $ANTLR start "T__45"
    public final void mT__45() throws RecognitionException {
        try {
            int _type = T__45;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:44:7: ( 'new' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:44:9: 'new'
            {
            match("new"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__45"

    // $ANTLR start "T__46"
    public final void mT__46() throws RecognitionException {
        try {
            int _type = T__46;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:45:7: ( 'true' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:45:9: 'true'
            {
            match("true"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__46"

    // $ANTLR start "T__47"
    public final void mT__47() throws RecognitionException {
        try {
            int _type = T__47;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:46:7: ( 'false' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:46:9: 'false'
            {
            match("false"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__47"

    // $ANTLR start "T__48"
    public final void mT__48() throws RecognitionException {
        try {
            int _type = T__48;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:47:7: ( 'delta' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:47:9: 'delta'
            {
            match("delta"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__48"

    // $ANTLR start "T__49"
    public final void mT__49() throws RecognitionException {
        try {
            int _type = T__49;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:48:7: ( 'adds' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:48:9: 'adds'
            {
            match("adds"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__49"

    // $ANTLR start "T__50"
    public final void mT__50() throws RecognitionException {
        try {
            int _type = T__50;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:49:7: ( 'removes' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:49:9: 'removes'
            {
            match("removes"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__50"

    // $ANTLR start "T__51"
    public final void mT__51() throws RecognitionException {
        try {
            int _type = T__51;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:50:7: ( 'modifies' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:50:9: 'modifies'
            {
            match("modifies"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__51"

    // $ANTLR start "T__52"
    public final void mT__52() throws RecognitionException {
        try {
            int _type = T__52;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:51:7: ( 'extending' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:51:9: 'extending'
            {
            match("extending"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__52"

    // $ANTLR start "T__53"
    public final void mT__53() throws RecognitionException {
        try {
            int _type = T__53;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:52:7: ( 'removesField' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:52:9: 'removesField'
            {
            match("removesField"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__53"

    // $ANTLR start "T__54"
    public final void mT__54() throws RecognitionException {
        try {
            int _type = T__54;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:53:7: ( 'removesMethod' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:53:9: 'removesMethod'
            {
            match("removesMethod"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__54"

    // $ANTLR start "T__55"
    public final void mT__55() throws RecognitionException {
        try {
            int _type = T__55;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:54:7: ( 'spl' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:54:9: 'spl'
            {
            match("spl"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__55"

    // $ANTLR start "T__56"
    public final void mT__56() throws RecognitionException {
        try {
            int _type = T__56;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:55:7: ( 'features' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:55:9: 'features'
            {
            match("features"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__56"

    // $ANTLR start "T__57"
    public final void mT__57() throws RecognitionException {
        try {
            int _type = T__57;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:56:7: ( 'configurations' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:56:9: 'configurations'
            {
            match("configurations"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__57"

    // $ANTLR start "T__58"
    public final void mT__58() throws RecognitionException {
        try {
            int _type = T__58;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:57:7: ( 'deltas' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:57:9: 'deltas'
            {
            match("deltas"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__58"

    // $ANTLR start "T__59"
    public final void mT__59() throws RecognitionException {
        try {
            int _type = T__59;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:58:7: ( '[' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:58:9: '['
            {
            match('['); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__59"

    // $ANTLR start "T__60"
    public final void mT__60() throws RecognitionException {
        try {
            int _type = T__60;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:59:7: ( ']' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:59:9: ']'
            {
            match(']'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__60"

    // $ANTLR start "T__61"
    public final void mT__61() throws RecognitionException {
        try {
            int _type = T__61;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:60:7: ( 'when' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:60:9: 'when'
            {
            match("when"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__61"

    // $ANTLR start "T__62"
    public final void mT__62() throws RecognitionException {
        try {
            int _type = T__62;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:61:7: ( 'product' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:61:9: 'product'
            {
            match("product"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__62"

    // $ANTLR start "T__63"
    public final void mT__63() throws RecognitionException {
        try {
            int _type = T__63;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:62:7: ( 'from' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:62:9: 'from'
            {
            match("from"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__63"

    // $ANTLR start "T__64"
    public final void mT__64() throws RecognitionException {
        try {
            int _type = T__64;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:63:7: ( ':' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:63:9: ':'
            {
            match(':'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__64"

    // $ANTLR start "RULE_JAVAVERBATIM"
    public final void mRULE_JAVAVERBATIM() throws RecognitionException {
        try {
            int _type = RULE_JAVAVERBATIM;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4447:19: ( '**Java:' ( options {greedy=false; } : . )* ':Java**' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4447:21: '**Java:' ( options {greedy=false; } : . )* ':Java**'
            {
            match("**Java:"); 

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4447:31: ( options {greedy=false; } : . )*
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( (LA1_0==':') ) {
                    int LA1_1 = input.LA(2);

                    if ( (LA1_1=='J') ) {
                        int LA1_3 = input.LA(3);

                        if ( (LA1_3=='a') ) {
                            int LA1_4 = input.LA(4);

                            if ( (LA1_4=='v') ) {
                                int LA1_5 = input.LA(5);

                                if ( (LA1_5=='a') ) {
                                    int LA1_6 = input.LA(6);

                                    if ( (LA1_6=='*') ) {
                                        int LA1_7 = input.LA(7);

                                        if ( (LA1_7=='*') ) {
                                            alt1=2;
                                        }
                                        else if ( ((LA1_7>='\u0000' && LA1_7<=')')||(LA1_7>='+' && LA1_7<='\uFFFF')) ) {
                                            alt1=1;
                                        }


                                    }
                                    else if ( ((LA1_6>='\u0000' && LA1_6<=')')||(LA1_6>='+' && LA1_6<='\uFFFF')) ) {
                                        alt1=1;
                                    }


                                }
                                else if ( ((LA1_5>='\u0000' && LA1_5<='`')||(LA1_5>='b' && LA1_5<='\uFFFF')) ) {
                                    alt1=1;
                                }


                            }
                            else if ( ((LA1_4>='\u0000' && LA1_4<='u')||(LA1_4>='w' && LA1_4<='\uFFFF')) ) {
                                alt1=1;
                            }


                        }
                        else if ( ((LA1_3>='\u0000' && LA1_3<='`')||(LA1_3>='b' && LA1_3<='\uFFFF')) ) {
                            alt1=1;
                        }


                    }
                    else if ( ((LA1_1>='\u0000' && LA1_1<='I')||(LA1_1>='K' && LA1_1<='\uFFFF')) ) {
                        alt1=1;
                    }


                }
                else if ( ((LA1_0>='\u0000' && LA1_0<='9')||(LA1_0>=';' && LA1_0<='\uFFFF')) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4447:59: .
            	    {
            	    matchAny(); 

            	    }
            	    break;

            	default :
            	    break loop1;
                }
            } while (true);

            match(":Java**"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_JAVAVERBATIM"

    // $ANTLR start "RULE_ID"
    public final void mRULE_ID() throws RecognitionException {
        try {
            int _type = RULE_ID;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4449:9: ( ( '^' )? ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9' )* )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4449:11: ( '^' )? ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9' )*
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4449:11: ( '^' )?
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0=='^') ) {
                alt2=1;
            }
            switch (alt2) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4449:11: '^'
                    {
                    match('^'); 

                    }
                    break;

            }

            if ( (input.LA(1)>='A' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4449:40: ( 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9' )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( ((LA3_0>='0' && LA3_0<='9')||(LA3_0>='A' && LA3_0<='Z')||LA3_0=='_'||(LA3_0>='a' && LA3_0<='z')) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:
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
    // $ANTLR end "RULE_ID"

    // $ANTLR start "RULE_INT"
    public final void mRULE_INT() throws RecognitionException {
        try {
            int _type = RULE_INT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4451:10: ( ( '0' .. '9' )+ )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4451:12: ( '0' .. '9' )+
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4451:12: ( '0' .. '9' )+
            int cnt4=0;
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( ((LA4_0>='0' && LA4_0<='9')) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4451:13: '0' .. '9'
            	    {
            	    matchRange('0','9'); 

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
        }
    }
    // $ANTLR end "RULE_INT"

    // $ANTLR start "RULE_STRING"
    public final void mRULE_STRING() throws RecognitionException {
        try {
            int _type = RULE_STRING;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4453:13: ( ( '\"' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | 'u' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\"' ) ) )* '\"' | '\\'' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | 'u' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\\'' ) ) )* '\\'' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4453:15: ( '\"' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | 'u' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\"' ) ) )* '\"' | '\\'' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | 'u' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\\'' ) ) )* '\\'' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4453:15: ( '\"' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | 'u' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\"' ) ) )* '\"' | '\\'' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | 'u' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\\'' ) ) )* '\\'' )
            int alt7=2;
            int LA7_0 = input.LA(1);

            if ( (LA7_0=='\"') ) {
                alt7=1;
            }
            else if ( (LA7_0=='\'') ) {
                alt7=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 7, 0, input);

                throw nvae;
            }
            switch (alt7) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4453:16: '\"' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | 'u' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\"' ) ) )* '\"'
                    {
                    match('\"'); 
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4453:20: ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | 'u' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\"' ) ) )*
                    loop5:
                    do {
                        int alt5=3;
                        int LA5_0 = input.LA(1);

                        if ( (LA5_0=='\\') ) {
                            alt5=1;
                        }
                        else if ( ((LA5_0>='\u0000' && LA5_0<='!')||(LA5_0>='#' && LA5_0<='[')||(LA5_0>=']' && LA5_0<='\uFFFF')) ) {
                            alt5=2;
                        }


                        switch (alt5) {
                    	case 1 :
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4453:21: '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | 'u' | '\"' | '\\'' | '\\\\' )
                    	    {
                    	    match('\\'); 
                    	    if ( input.LA(1)=='\"'||input.LA(1)=='\''||input.LA(1)=='\\'||input.LA(1)=='b'||input.LA(1)=='f'||input.LA(1)=='n'||input.LA(1)=='r'||(input.LA(1)>='t' && input.LA(1)<='u') ) {
                    	        input.consume();

                    	    }
                    	    else {
                    	        MismatchedSetException mse = new MismatchedSetException(null,input);
                    	        recover(mse);
                    	        throw mse;}


                    	    }
                    	    break;
                    	case 2 :
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4453:66: ~ ( ( '\\\\' | '\"' ) )
                    	    {
                    	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='!')||(input.LA(1)>='#' && input.LA(1)<='[')||(input.LA(1)>=']' && input.LA(1)<='\uFFFF') ) {
                    	        input.consume();

                    	    }
                    	    else {
                    	        MismatchedSetException mse = new MismatchedSetException(null,input);
                    	        recover(mse);
                    	        throw mse;}


                    	    }
                    	    break;

                    	default :
                    	    break loop5;
                        }
                    } while (true);

                    match('\"'); 

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4453:86: '\\'' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | 'u' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\\'' ) ) )* '\\''
                    {
                    match('\''); 
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4453:91: ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | 'u' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\\'' ) ) )*
                    loop6:
                    do {
                        int alt6=3;
                        int LA6_0 = input.LA(1);

                        if ( (LA6_0=='\\') ) {
                            alt6=1;
                        }
                        else if ( ((LA6_0>='\u0000' && LA6_0<='&')||(LA6_0>='(' && LA6_0<='[')||(LA6_0>=']' && LA6_0<='\uFFFF')) ) {
                            alt6=2;
                        }


                        switch (alt6) {
                    	case 1 :
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4453:92: '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | 'u' | '\"' | '\\'' | '\\\\' )
                    	    {
                    	    match('\\'); 
                    	    if ( input.LA(1)=='\"'||input.LA(1)=='\''||input.LA(1)=='\\'||input.LA(1)=='b'||input.LA(1)=='f'||input.LA(1)=='n'||input.LA(1)=='r'||(input.LA(1)>='t' && input.LA(1)<='u') ) {
                    	        input.consume();

                    	    }
                    	    else {
                    	        MismatchedSetException mse = new MismatchedSetException(null,input);
                    	        recover(mse);
                    	        throw mse;}


                    	    }
                    	    break;
                    	case 2 :
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4453:137: ~ ( ( '\\\\' | '\\'' ) )
                    	    {
                    	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='&')||(input.LA(1)>='(' && input.LA(1)<='[')||(input.LA(1)>=']' && input.LA(1)<='\uFFFF') ) {
                    	        input.consume();

                    	    }
                    	    else {
                    	        MismatchedSetException mse = new MismatchedSetException(null,input);
                    	        recover(mse);
                    	        throw mse;}


                    	    }
                    	    break;

                    	default :
                    	    break loop6;
                        }
                    } while (true);

                    match('\''); 

                    }
                    break;

            }


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_STRING"

    // $ANTLR start "RULE_ML_COMMENT"
    public final void mRULE_ML_COMMENT() throws RecognitionException {
        try {
            int _type = RULE_ML_COMMENT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4455:17: ( '/*' ( options {greedy=false; } : . )* '*/' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4455:19: '/*' ( options {greedy=false; } : . )* '*/'
            {
            match("/*"); 

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4455:24: ( options {greedy=false; } : . )*
            loop8:
            do {
                int alt8=2;
                int LA8_0 = input.LA(1);

                if ( (LA8_0=='*') ) {
                    int LA8_1 = input.LA(2);

                    if ( (LA8_1=='/') ) {
                        alt8=2;
                    }
                    else if ( ((LA8_1>='\u0000' && LA8_1<='.')||(LA8_1>='0' && LA8_1<='\uFFFF')) ) {
                        alt8=1;
                    }


                }
                else if ( ((LA8_0>='\u0000' && LA8_0<=')')||(LA8_0>='+' && LA8_0<='\uFFFF')) ) {
                    alt8=1;
                }


                switch (alt8) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4455:52: .
            	    {
            	    matchAny(); 

            	    }
            	    break;

            	default :
            	    break loop8;
                }
            } while (true);

            match("*/"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_ML_COMMENT"

    // $ANTLR start "RULE_SL_COMMENT"
    public final void mRULE_SL_COMMENT() throws RecognitionException {
        try {
            int _type = RULE_SL_COMMENT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4457:17: ( '//' (~ ( ( '\\n' | '\\r' ) ) )* ( ( '\\r' )? '\\n' )? )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4457:19: '//' (~ ( ( '\\n' | '\\r' ) ) )* ( ( '\\r' )? '\\n' )?
            {
            match("//"); 

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4457:24: (~ ( ( '\\n' | '\\r' ) ) )*
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( ((LA9_0>='\u0000' && LA9_0<='\t')||(LA9_0>='\u000B' && LA9_0<='\f')||(LA9_0>='\u000E' && LA9_0<='\uFFFF')) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4457:24: ~ ( ( '\\n' | '\\r' ) )
            	    {
            	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='\t')||(input.LA(1)>='\u000B' && input.LA(1)<='\f')||(input.LA(1)>='\u000E' && input.LA(1)<='\uFFFF') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    break loop9;
                }
            } while (true);

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4457:40: ( ( '\\r' )? '\\n' )?
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0=='\n'||LA11_0=='\r') ) {
                alt11=1;
            }
            switch (alt11) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4457:41: ( '\\r' )? '\\n'
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4457:41: ( '\\r' )?
                    int alt10=2;
                    int LA10_0 = input.LA(1);

                    if ( (LA10_0=='\r') ) {
                        alt10=1;
                    }
                    switch (alt10) {
                        case 1 :
                            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4457:41: '\\r'
                            {
                            match('\r'); 

                            }
                            break;

                    }

                    match('\n'); 

                    }
                    break;

            }


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_SL_COMMENT"

    // $ANTLR start "RULE_WS"
    public final void mRULE_WS() throws RecognitionException {
        try {
            int _type = RULE_WS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4459:9: ( ( ' ' | '\\t' | '\\r' | '\\n' )+ )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4459:11: ( ' ' | '\\t' | '\\r' | '\\n' )+
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4459:11: ( ' ' | '\\t' | '\\r' | '\\n' )+
            int cnt12=0;
            loop12:
            do {
                int alt12=2;
                int LA12_0 = input.LA(1);

                if ( ((LA12_0>='\t' && LA12_0<='\n')||LA12_0=='\r'||LA12_0==' ') ) {
                    alt12=1;
                }


                switch (alt12) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:
            	    {
            	    if ( (input.LA(1)>='\t' && input.LA(1)<='\n')||input.LA(1)=='\r'||input.LA(1)==' ' ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    if ( cnt12 >= 1 ) break loop12;
                        EarlyExitException eee =
                            new EarlyExitException(12, input);
                        throw eee;
                }
                cnt12++;
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_WS"

    // $ANTLR start "RULE_ANY_OTHER"
    public final void mRULE_ANY_OTHER() throws RecognitionException {
        try {
            int _type = RULE_ANY_OTHER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4461:16: ( . )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4461:18: .
            {
            matchAny(); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RULE_ANY_OTHER"

    public void mTokens() throws RecognitionException {
        // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:8: ( T__12 | T__13 | T__14 | T__15 | T__16 | T__17 | T__18 | T__19 | T__20 | T__21 | T__22 | T__23 | T__24 | T__25 | T__26 | T__27 | T__28 | T__29 | T__30 | T__31 | T__32 | T__33 | T__34 | T__35 | T__36 | T__37 | T__38 | T__39 | T__40 | T__41 | T__42 | T__43 | T__44 | T__45 | T__46 | T__47 | T__48 | T__49 | T__50 | T__51 | T__52 | T__53 | T__54 | T__55 | T__56 | T__57 | T__58 | T__59 | T__60 | T__61 | T__62 | T__63 | T__64 | RULE_JAVAVERBATIM | RULE_ID | RULE_INT | RULE_STRING | RULE_ML_COMMENT | RULE_SL_COMMENT | RULE_WS | RULE_ANY_OTHER )
        int alt13=61;
        alt13 = dfa13.predict(input);
        switch (alt13) {
            case 1 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:10: T__12
                {
                mT__12(); 

                }
                break;
            case 2 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:16: T__13
                {
                mT__13(); 

                }
                break;
            case 3 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:22: T__14
                {
                mT__14(); 

                }
                break;
            case 4 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:28: T__15
                {
                mT__15(); 

                }
                break;
            case 5 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:34: T__16
                {
                mT__16(); 

                }
                break;
            case 6 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:40: T__17
                {
                mT__17(); 

                }
                break;
            case 7 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:46: T__18
                {
                mT__18(); 

                }
                break;
            case 8 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:52: T__19
                {
                mT__19(); 

                }
                break;
            case 9 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:58: T__20
                {
                mT__20(); 

                }
                break;
            case 10 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:64: T__21
                {
                mT__21(); 

                }
                break;
            case 11 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:70: T__22
                {
                mT__22(); 

                }
                break;
            case 12 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:76: T__23
                {
                mT__23(); 

                }
                break;
            case 13 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:82: T__24
                {
                mT__24(); 

                }
                break;
            case 14 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:88: T__25
                {
                mT__25(); 

                }
                break;
            case 15 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:94: T__26
                {
                mT__26(); 

                }
                break;
            case 16 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:100: T__27
                {
                mT__27(); 

                }
                break;
            case 17 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:106: T__28
                {
                mT__28(); 

                }
                break;
            case 18 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:112: T__29
                {
                mT__29(); 

                }
                break;
            case 19 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:118: T__30
                {
                mT__30(); 

                }
                break;
            case 20 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:124: T__31
                {
                mT__31(); 

                }
                break;
            case 21 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:130: T__32
                {
                mT__32(); 

                }
                break;
            case 22 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:136: T__33
                {
                mT__33(); 

                }
                break;
            case 23 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:142: T__34
                {
                mT__34(); 

                }
                break;
            case 24 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:148: T__35
                {
                mT__35(); 

                }
                break;
            case 25 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:154: T__36
                {
                mT__36(); 

                }
                break;
            case 26 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:160: T__37
                {
                mT__37(); 

                }
                break;
            case 27 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:166: T__38
                {
                mT__38(); 

                }
                break;
            case 28 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:172: T__39
                {
                mT__39(); 

                }
                break;
            case 29 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:178: T__40
                {
                mT__40(); 

                }
                break;
            case 30 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:184: T__41
                {
                mT__41(); 

                }
                break;
            case 31 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:190: T__42
                {
                mT__42(); 

                }
                break;
            case 32 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:196: T__43
                {
                mT__43(); 

                }
                break;
            case 33 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:202: T__44
                {
                mT__44(); 

                }
                break;
            case 34 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:208: T__45
                {
                mT__45(); 

                }
                break;
            case 35 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:214: T__46
                {
                mT__46(); 

                }
                break;
            case 36 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:220: T__47
                {
                mT__47(); 

                }
                break;
            case 37 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:226: T__48
                {
                mT__48(); 

                }
                break;
            case 38 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:232: T__49
                {
                mT__49(); 

                }
                break;
            case 39 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:238: T__50
                {
                mT__50(); 

                }
                break;
            case 40 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:244: T__51
                {
                mT__51(); 

                }
                break;
            case 41 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:250: T__52
                {
                mT__52(); 

                }
                break;
            case 42 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:256: T__53
                {
                mT__53(); 

                }
                break;
            case 43 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:262: T__54
                {
                mT__54(); 

                }
                break;
            case 44 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:268: T__55
                {
                mT__55(); 

                }
                break;
            case 45 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:274: T__56
                {
                mT__56(); 

                }
                break;
            case 46 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:280: T__57
                {
                mT__57(); 

                }
                break;
            case 47 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:286: T__58
                {
                mT__58(); 

                }
                break;
            case 48 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:292: T__59
                {
                mT__59(); 

                }
                break;
            case 49 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:298: T__60
                {
                mT__60(); 

                }
                break;
            case 50 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:304: T__61
                {
                mT__61(); 

                }
                break;
            case 51 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:310: T__62
                {
                mT__62(); 

                }
                break;
            case 52 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:316: T__63
                {
                mT__63(); 

                }
                break;
            case 53 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:322: T__64
                {
                mT__64(); 

                }
                break;
            case 54 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:328: RULE_JAVAVERBATIM
                {
                mRULE_JAVAVERBATIM(); 

                }
                break;
            case 55 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:346: RULE_ID
                {
                mRULE_ID(); 

                }
                break;
            case 56 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:354: RULE_INT
                {
                mRULE_INT(); 

                }
                break;
            case 57 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:363: RULE_STRING
                {
                mRULE_STRING(); 

                }
                break;
            case 58 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:375: RULE_ML_COMMENT
                {
                mRULE_ML_COMMENT(); 

                }
                break;
            case 59 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:391: RULE_SL_COMMENT
                {
                mRULE_SL_COMMENT(); 

                }
                break;
            case 60 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:407: RULE_WS
                {
                mRULE_WS(); 

                }
                break;
            case 61 :
                // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1:415: RULE_ANY_OTHER
                {
                mRULE_ANY_OTHER(); 

                }
                break;

        }

    }


    protected DFA13 dfa13 = new DFA13(this);
    static final String DFA13_eotS =
        "\1\uffff\1\56\1\60\6\62\6\uffff\1\62\1\103\2\uffff\1\107\1\112\1"+
        "\114\2\54\1\uffff\10\62\2\uffff\2\62\1\uffff\1\54\2\uffff\2\54\6"+
        "\uffff\1\62\1\uffff\1\62\1\146\6\62\6\uffff\1\62\16\uffff\14\62"+
        "\2\uffff\2\62\4\uffff\1\62\1\176\1\uffff\11\62\1\u0088\11\62\1\u0092"+
        "\2\62\1\u0095\1\uffff\5\62\1\u009b\2\62\1\u009e\1\uffff\1\u009f"+
        "\1\u00a0\3\62\1\u00a4\1\62\1\u00a6\1\62\1\uffff\1\u00a8\1\62\1\uffff"+
        "\2\62\1\u00ac\2\62\1\uffff\2\62\3\uffff\1\62\1\u00b2\1\62\1\uffff"+
        "\1\u00b5\1\uffff\1\62\1\uffff\2\62\1\u00b9\1\uffff\2\62\1\u00bd"+
        "\2\62\1\uffff\1\62\1\u00c1\1\uffff\2\62\1\u00c4\1\uffff\1\62\1\u00c6"+
        "\1\62\1\uffff\1\u00ca\2\62\1\uffff\1\62\1\u00ce\1\uffff\1\62\1\uffff"+
        "\3\62\1\uffff\1\u00d3\1\u00d4\1\u00d5\1\uffff\1\62\1\u00d7\2\62"+
        "\3\uffff\1\62\1\uffff\6\62\1\u00e1\2\62\1\uffff\1\u00e4\1\u00e5"+
        "\2\uffff";
    static final String DFA13_eofS =
        "\u00e6\uffff";
    static final String DFA13_minS =
        "\1\0\2\75\1\157\1\146\1\157\1\164\2\154\6\uffff\1\145\1\75\2\uffff"+
        "\2\52\1\75\1\174\1\46\1\uffff\1\145\1\150\1\162\1\141\1\145\1\144"+
        "\1\157\1\160\2\uffff\1\150\1\162\1\uffff\1\101\2\uffff\2\0\6\uffff"+
        "\1\151\1\uffff\1\164\1\60\1\157\1\162\1\141\1\156\1\164\1\163\6"+
        "\uffff\1\155\16\uffff\1\154\1\167\1\151\1\165\1\151\1\154\1\141"+
        "\1\157\1\154\2\144\1\154\2\uffff\1\145\1\157\4\uffff\1\144\1\60"+
        "\1\uffff\1\154\1\151\1\163\1\146\2\145\1\165\1\157\1\154\1\60\1"+
        "\163\1\145\1\147\1\163\1\164\1\155\1\164\1\163\1\151\1\60\1\156"+
        "\1\144\1\60\1\uffff\1\145\1\156\1\163\1\151\1\156\1\60\1\162\1\166"+
        "\1\60\1\uffff\2\60\1\151\1\145\1\165\1\60\1\141\1\60\1\146\1\uffff"+
        "\1\60\1\165\1\uffff\1\141\1\147\1\60\1\147\1\144\1\uffff\1\156\1"+
        "\145\3\uffff\1\156\1\60\1\162\1\uffff\1\60\1\uffff\1\151\1\uffff"+
        "\1\143\1\156\1\60\1\uffff\1\165\1\151\1\60\1\163\1\141\1\uffff\1"+
        "\145\1\60\1\uffff\1\145\1\164\1\60\1\uffff\1\162\1\60\1\156\1\uffff"+
        "\1\60\1\154\1\163\1\uffff\1\163\1\60\1\uffff\1\141\1\uffff\1\147"+
        "\1\151\1\145\1\uffff\3\60\1\uffff\1\164\1\60\1\145\1\164\3\uffff"+
        "\1\151\1\uffff\1\154\1\150\1\157\1\144\1\157\1\156\1\60\1\144\1"+
        "\163\1\uffff\2\60\2\uffff";
    static final String DFA13_maxS =
        "\1\uffff\2\75\1\157\1\156\1\157\1\164\1\157\1\170\6\uffff\1\145"+
        "\1\75\2\uffff\1\52\1\57\1\75\1\174\1\46\1\uffff\1\165\3\162\1\145"+
        "\1\144\1\157\1\160\2\uffff\1\150\1\162\1\uffff\1\172\2\uffff\2\uffff"+
        "\6\uffff\1\151\1\uffff\1\164\1\172\1\157\1\162\1\141\1\156\1\164"+
        "\1\163\6\uffff\1\164\16\uffff\1\154\1\167\1\151\1\165\1\151\1\154"+
        "\1\141\1\157\1\154\2\144\1\154\2\uffff\1\145\1\157\4\uffff\1\144"+
        "\1\172\1\uffff\1\154\1\151\1\163\1\146\2\145\1\165\1\157\1\154\1"+
        "\172\1\163\1\145\1\147\1\163\1\164\1\155\1\164\1\163\1\151\1\172"+
        "\1\156\1\144\1\172\1\uffff\1\145\1\156\1\163\1\151\1\156\1\172\1"+
        "\162\1\166\1\172\1\uffff\2\172\1\151\1\145\1\165\1\172\1\141\1\172"+
        "\1\146\1\uffff\1\172\1\165\1\uffff\1\141\1\147\1\172\1\147\1\144"+
        "\1\uffff\1\156\1\145\3\uffff\1\156\1\172\1\162\1\uffff\1\172\1\uffff"+
        "\1\151\1\uffff\1\143\1\156\1\172\1\uffff\1\165\1\163\1\172\1\163"+
        "\1\141\1\uffff\1\145\1\172\1\uffff\1\145\1\164\1\172\1\uffff\1\162"+
        "\1\172\1\156\1\uffff\1\172\1\154\1\163\1\uffff\1\163\1\172\1\uffff"+
        "\1\141\1\uffff\1\147\1\151\1\145\1\uffff\3\172\1\uffff\1\164\1\172"+
        "\1\145\1\164\3\uffff\1\151\1\uffff\1\154\1\150\1\157\1\144\1\157"+
        "\1\156\1\172\1\144\1\163\1\uffff\2\172\2\uffff";
    static final String DFA13_acceptS =
        "\11\uffff\1\11\1\12\1\13\1\14\1\15\1\16\2\uffff\1\23\1\24\5\uffff"+
        "\1\36\10\uffff\1\60\1\61\2\uffff\1\65\1\uffff\1\67\1\70\2\uffff"+
        "\1\74\1\75\1\30\1\1\1\27\1\2\1\uffff\1\67\10\uffff\1\11\1\12\1\13"+
        "\1\14\1\15\1\16\1\uffff\1\31\1\20\1\23\1\24\1\66\1\25\1\72\1\73"+
        "\1\26\1\32\1\35\1\33\1\34\1\36\14\uffff\1\60\1\61\2\uffff\1\65\1"+
        "\70\1\71\1\74\2\uffff\1\21\27\uffff\1\4\11\uffff\1\42\11\uffff\1"+
        "\54\2\uffff\1\3\5\uffff\1\22\2\uffff\1\37\1\40\1\43\3\uffff\1\64"+
        "\1\uffff\1\46\1\uffff\1\62\3\uffff\1\7\5\uffff\1\44\2\uffff\1\45"+
        "\3\uffff\1\6\3\uffff\1\17\3\uffff\1\57\2\uffff\1\5\1\uffff\1\10"+
        "\3\uffff\1\47\3\uffff\1\63\4\uffff\1\41\1\55\1\50\1\uffff\1\51\11"+
        "\uffff\1\52\2\uffff\1\53\1\56";
    static final String DFA13_specialS =
        "\1\2\50\uffff\1\1\1\0\u00bb\uffff}>";
    static final String[] DFA13_transitionS = {
            "\11\54\2\53\2\54\1\53\22\54\1\53\1\25\1\51\3\54\1\27\1\52\1"+
            "\14\1\16\1\23\1\21\1\15\1\22\1\30\1\24\12\50\1\45\1\13\1\1\1"+
            "\20\1\2\2\54\22\47\1\6\7\47\1\41\1\54\1\42\1\46\1\47\1\54\1"+
            "\36\1\5\1\7\1\35\1\10\1\34\2\47\1\4\3\47\1\37\1\31\1\33\1\44"+
            "\1\47\1\17\1\40\1\32\1\47\1\3\1\43\3\47\1\11\1\26\1\12\uff82"+
            "\54",
            "\1\55",
            "\1\57",
            "\1\61",
            "\1\64\7\uffff\1\63",
            "\1\65",
            "\1\66",
            "\1\67\2\uffff\1\70",
            "\1\72\13\uffff\1\71",
            "",
            "",
            "",
            "",
            "",
            "",
            "\1\101",
            "\1\102",
            "",
            "",
            "\1\106",
            "\1\110\4\uffff\1\111",
            "\1\113",
            "\1\115",
            "\1\116",
            "",
            "\1\121\17\uffff\1\120",
            "\1\122\11\uffff\1\123",
            "\1\124",
            "\1\125\3\uffff\1\126\14\uffff\1\127",
            "\1\130",
            "\1\131",
            "\1\132",
            "\1\133",
            "",
            "",
            "\1\136",
            "\1\137",
            "",
            "\32\62\4\uffff\1\62\1\uffff\32\62",
            "",
            "",
            "\0\142",
            "\0\142",
            "",
            "",
            "",
            "",
            "",
            "",
            "\1\144",
            "",
            "\1\145",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\147",
            "\1\150",
            "\1\151",
            "\1\152",
            "\1\153",
            "\1\154",
            "",
            "",
            "",
            "",
            "",
            "",
            "\1\156\6\uffff\1\155",
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
            "",
            "",
            "",
            "\1\157",
            "\1\160",
            "\1\161",
            "\1\162",
            "\1\163",
            "\1\164",
            "\1\165",
            "\1\166",
            "\1\167",
            "\1\170",
            "\1\171",
            "\1\172",
            "",
            "",
            "\1\173",
            "\1\174",
            "",
            "",
            "",
            "",
            "\1\175",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "",
            "\1\177",
            "\1\u0080",
            "\1\u0081",
            "\1\u0082",
            "\1\u0083",
            "\1\u0084",
            "\1\u0085",
            "\1\u0086",
            "\1\u0087",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u0089",
            "\1\u008a",
            "\1\u008b",
            "\1\u008c",
            "\1\u008d",
            "\1\u008e",
            "\1\u008f",
            "\1\u0090",
            "\1\u0091",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u0093",
            "\1\u0094",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "",
            "\1\u0096",
            "\1\u0097",
            "\1\u0098",
            "\1\u0099",
            "\1\u009a",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u009c",
            "\1\u009d",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u00a1",
            "\1\u00a2",
            "\1\u00a3",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u00a5",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u00a7",
            "",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u00a9",
            "",
            "\1\u00aa",
            "\1\u00ab",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u00ad",
            "\1\u00ae",
            "",
            "\1\u00af",
            "\1\u00b0",
            "",
            "",
            "",
            "\1\u00b1",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u00b3",
            "",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\22\62\1\u00b4\7\62",
            "",
            "\1\u00b6",
            "",
            "\1\u00b7",
            "\1\u00b8",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "",
            "\1\u00ba",
            "\1\u00bc\11\uffff\1\u00bb",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u00be",
            "\1\u00bf",
            "",
            "\1\u00c0",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "",
            "\1\u00c2",
            "\1\u00c3",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "",
            "\1\u00c5",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u00c7",
            "",
            "\12\62\7\uffff\5\62\1\u00c8\6\62\1\u00c9\15\62\4\uffff\1\62"+
            "\1\uffff\32\62",
            "\1\u00cb",
            "\1\u00cc",
            "",
            "\1\u00cd",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "",
            "\1\u00cf",
            "",
            "\1\u00d0",
            "\1\u00d1",
            "\1\u00d2",
            "",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "",
            "\1\u00d6",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u00d8",
            "\1\u00d9",
            "",
            "",
            "",
            "\1\u00da",
            "",
            "\1\u00db",
            "\1\u00dc",
            "\1\u00dd",
            "\1\u00de",
            "\1\u00df",
            "\1\u00e0",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\1\u00e2",
            "\1\u00e3",
            "",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "\12\62\7\uffff\32\62\4\uffff\1\62\1\uffff\32\62",
            "",
            ""
    };

    static final short[] DFA13_eot = DFA.unpackEncodedString(DFA13_eotS);
    static final short[] DFA13_eof = DFA.unpackEncodedString(DFA13_eofS);
    static final char[] DFA13_min = DFA.unpackEncodedStringToUnsignedChars(DFA13_minS);
    static final char[] DFA13_max = DFA.unpackEncodedStringToUnsignedChars(DFA13_maxS);
    static final short[] DFA13_accept = DFA.unpackEncodedString(DFA13_acceptS);
    static final short[] DFA13_special = DFA.unpackEncodedString(DFA13_specialS);
    static final short[][] DFA13_transition;

    static {
        int numStates = DFA13_transitionS.length;
        DFA13_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA13_transition[i] = DFA.unpackEncodedString(DFA13_transitionS[i]);
        }
    }

    class DFA13 extends DFA {

        public DFA13(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 13;
            this.eot = DFA13_eot;
            this.eof = DFA13_eof;
            this.min = DFA13_min;
            this.max = DFA13_max;
            this.accept = DFA13_accept;
            this.special = DFA13_special;
            this.transition = DFA13_transition;
        }
        public String getDescription() {
            return "1:1: Tokens : ( T__12 | T__13 | T__14 | T__15 | T__16 | T__17 | T__18 | T__19 | T__20 | T__21 | T__22 | T__23 | T__24 | T__25 | T__26 | T__27 | T__28 | T__29 | T__30 | T__31 | T__32 | T__33 | T__34 | T__35 | T__36 | T__37 | T__38 | T__39 | T__40 | T__41 | T__42 | T__43 | T__44 | T__45 | T__46 | T__47 | T__48 | T__49 | T__50 | T__51 | T__52 | T__53 | T__54 | T__55 | T__56 | T__57 | T__58 | T__59 | T__60 | T__61 | T__62 | T__63 | T__64 | RULE_JAVAVERBATIM | RULE_ID | RULE_INT | RULE_STRING | RULE_ML_COMMENT | RULE_SL_COMMENT | RULE_WS | RULE_ANY_OTHER );";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            IntStream input = _input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA13_42 = input.LA(1);

                        s = -1;
                        if ( ((LA13_42>='\u0000' && LA13_42<='\uFFFF')) ) {s = 98;}

                        else s = 44;

                        if ( s>=0 ) return s;
                        break;
                    case 1 : 
                        int LA13_41 = input.LA(1);

                        s = -1;
                        if ( ((LA13_41>='\u0000' && LA13_41<='\uFFFF')) ) {s = 98;}

                        else s = 44;

                        if ( s>=0 ) return s;
                        break;
                    case 2 : 
                        int LA13_0 = input.LA(1);

                        s = -1;
                        if ( (LA13_0=='<') ) {s = 1;}

                        else if ( (LA13_0=='>') ) {s = 2;}

                        else if ( (LA13_0=='v') ) {s = 3;}

                        else if ( (LA13_0=='i') ) {s = 4;}

                        else if ( (LA13_0=='b') ) {s = 5;}

                        else if ( (LA13_0=='S') ) {s = 6;}

                        else if ( (LA13_0=='c') ) {s = 7;}

                        else if ( (LA13_0=='e') ) {s = 8;}

                        else if ( (LA13_0=='{') ) {s = 9;}

                        else if ( (LA13_0=='}') ) {s = 10;}

                        else if ( (LA13_0==';') ) {s = 11;}

                        else if ( (LA13_0=='(') ) {s = 12;}

                        else if ( (LA13_0==',') ) {s = 13;}

                        else if ( (LA13_0==')') ) {s = 14;}

                        else if ( (LA13_0=='r') ) {s = 15;}

                        else if ( (LA13_0=='=') ) {s = 16;}

                        else if ( (LA13_0=='+') ) {s = 17;}

                        else if ( (LA13_0=='-') ) {s = 18;}

                        else if ( (LA13_0=='*') ) {s = 19;}

                        else if ( (LA13_0=='/') ) {s = 20;}

                        else if ( (LA13_0=='!') ) {s = 21;}

                        else if ( (LA13_0=='|') ) {s = 22;}

                        else if ( (LA13_0=='&') ) {s = 23;}

                        else if ( (LA13_0=='.') ) {s = 24;}

                        else if ( (LA13_0=='n') ) {s = 25;}

                        else if ( (LA13_0=='t') ) {s = 26;}

                        else if ( (LA13_0=='o') ) {s = 27;}

                        else if ( (LA13_0=='f') ) {s = 28;}

                        else if ( (LA13_0=='d') ) {s = 29;}

                        else if ( (LA13_0=='a') ) {s = 30;}

                        else if ( (LA13_0=='m') ) {s = 31;}

                        else if ( (LA13_0=='s') ) {s = 32;}

                        else if ( (LA13_0=='[') ) {s = 33;}

                        else if ( (LA13_0==']') ) {s = 34;}

                        else if ( (LA13_0=='w') ) {s = 35;}

                        else if ( (LA13_0=='p') ) {s = 36;}

                        else if ( (LA13_0==':') ) {s = 37;}

                        else if ( (LA13_0=='^') ) {s = 38;}

                        else if ( ((LA13_0>='A' && LA13_0<='R')||(LA13_0>='T' && LA13_0<='Z')||LA13_0=='_'||(LA13_0>='g' && LA13_0<='h')||(LA13_0>='j' && LA13_0<='l')||LA13_0=='q'||LA13_0=='u'||(LA13_0>='x' && LA13_0<='z')) ) {s = 39;}

                        else if ( ((LA13_0>='0' && LA13_0<='9')) ) {s = 40;}

                        else if ( (LA13_0=='\"') ) {s = 41;}

                        else if ( (LA13_0=='\'') ) {s = 42;}

                        else if ( ((LA13_0>='\t' && LA13_0<='\n')||LA13_0=='\r'||LA13_0==' ') ) {s = 43;}

                        else if ( ((LA13_0>='\u0000' && LA13_0<='\b')||(LA13_0>='\u000B' && LA13_0<='\f')||(LA13_0>='\u000E' && LA13_0<='\u001F')||(LA13_0>='#' && LA13_0<='%')||(LA13_0>='?' && LA13_0<='@')||LA13_0=='\\'||LA13_0=='`'||(LA13_0>='~' && LA13_0<='\uFFFF')) ) {s = 44;}

                        if ( s>=0 ) return s;
                        break;
            }
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 13, _s, input);
            error(nvae);
            throw nvae;
        }
    }
 

}