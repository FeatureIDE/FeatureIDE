package org.xtext.example.parser.antlr.internal;

// Hack: Use our own Lexer superclass by means of import. 
// Currently there is no other way to specify the superclass for the lexer.
import org.eclipse.xtext.parser.antlr.Lexer;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

@SuppressWarnings("all")
public class InternalDJLexer extends Lexer {
    public static final int RULE_ID=5;
    public static final int RULE_ANY_OTHER=11;
    public static final int T29=29;
    public static final int T28=28;
    public static final int T27=27;
    public static final int T26=26;
    public static final int T25=25;
    public static final int EOF=-1;
    public static final int T24=24;
    public static final int T23=23;
    public static final int T22=22;
    public static final int T21=21;
    public static final int T20=20;
    public static final int RULE_INT=7;
    public static final int T38=38;
    public static final int T37=37;
    public static final int T39=39;
    public static final int T34=34;
    public static final int T33=33;
    public static final int T36=36;
    public static final int T35=35;
    public static final int T30=30;
    public static final int T32=32;
    public static final int T31=31;
    public static final int T48=48;
    public static final int T43=43;
    public static final int Tokens=49;
    public static final int RULE_SL_COMMENT=9;
    public static final int T42=42;
    public static final int RULE_ALL=6;
    public static final int T41=41;
    public static final int T40=40;
    public static final int T47=47;
    public static final int T46=46;
    public static final int T45=45;
    public static final int RULE_ML_COMMENT=8;
    public static final int T44=44;
    public static final int RULE_STRING=4;
    public static final int T12=12;
    public static final int T13=13;
    public static final int T14=14;
    public static final int T15=15;
    public static final int RULE_WS=10;
    public static final int T16=16;
    public static final int T17=17;
    public static final int T18=18;
    public static final int T19=19;
    public InternalDJLexer() {;} 
    public InternalDJLexer(CharStream input) {
        super(input);
    }
    public String getGrammarFileName() { return "../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g"; }

    // $ANTLR start T12
    public final void mT12() throws RecognitionException {
        try {
            int _type = T12;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:10:5: ( 'import' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:10:7: 'import'
            {
            match("import"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T12

    // $ANTLR start T13
    public final void mT13() throws RecognitionException {
        try {
            int _type = T13;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:11:5: ( 'features' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:11:7: 'features'
            {
            match("features"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T13

    // $ANTLR start T14
    public final void mT14() throws RecognitionException {
        try {
            int _type = T14;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:12:5: ( ',' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:12:7: ','
            {
            match(','); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T14

    // $ANTLR start T15
    public final void mT15() throws RecognitionException {
        try {
            int _type = T15;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:13:5: ( 'configurations' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:13:7: 'configurations'
            {
            match("configurations"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T15

    // $ANTLR start T16
    public final void mT16() throws RecognitionException {
        try {
            int _type = T16;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:14:5: ( 'core' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:14:7: 'core'
            {
            match("core"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T16

    // $ANTLR start T17
    public final void mT17() throws RecognitionException {
        try {
            int _type = T17;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:15:5: ( 'delta' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:15:7: 'delta'
            {
            match("delta"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T17

    // $ANTLR start T18
    public final void mT18() throws RecognitionException {
        try {
            int _type = T18;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:16:5: ( '{' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:16:7: '{'
            {
            match('{'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T18

    // $ANTLR start T19
    public final void mT19() throws RecognitionException {
        try {
            int _type = T19;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:17:5: ( '}' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:17:7: '}'
            {
            match('}'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T19

    // $ANTLR start T20
    public final void mT20() throws RecognitionException {
        try {
            int _type = T20;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:18:5: ( 'class' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:18:7: 'class'
            {
            match("class"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T20

    // $ANTLR start T21
    public final void mT21() throws RecognitionException {
        try {
            int _type = T21;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:19:5: ( 'extends' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:19:7: 'extends'
            {
            match("extends"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T21

    // $ANTLR start T22
    public final void mT22() throws RecognitionException {
        try {
            int _type = T22;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:20:5: ( '(' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:20:7: '('
            {
            match('('); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T22

    // $ANTLR start T23
    public final void mT23() throws RecognitionException {
        try {
            int _type = T23;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:21:5: ( ')' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:21:7: ')'
            {
            match(')'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T23

    // $ANTLR start T24
    public final void mT24() throws RecognitionException {
        try {
            int _type = T24;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:22:5: ( 'super' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:22:7: 'super'
            {
            match("super"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T24

    // $ANTLR start T25
    public final void mT25() throws RecognitionException {
        try {
            int _type = T25;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:23:5: ( ';' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:23:7: ';'
            {
            match(';'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T25

    // $ANTLR start T26
    public final void mT26() throws RecognitionException {
        try {
            int _type = T26;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:24:5: ( 'this' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:24:7: 'this'
            {
            match("this"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T26

    // $ANTLR start T27
    public final void mT27() throws RecognitionException {
        try {
            int _type = T27;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:25:5: ( '.' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:25:7: '.'
            {
            match('.'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T27

    // $ANTLR start T28
    public final void mT28() throws RecognitionException {
        try {
            int _type = T28;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:26:5: ( '=' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:26:7: '='
            {
            match('='); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T28

    // $ANTLR start T29
    public final void mT29() throws RecognitionException {
        try {
            int _type = T29;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:27:5: ( 'return' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:27:7: 'return'
            {
            match("return"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T29

    // $ANTLR start T30
    public final void mT30() throws RecognitionException {
        try {
            int _type = T30;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:28:5: ( 'after' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:28:7: 'after'
            {
            match("after"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T30

    // $ANTLR start T31
    public final void mT31() throws RecognitionException {
        try {
            int _type = T31;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:29:5: ( 'when' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:29:7: 'when'
            {
            match("when"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T31

    // $ANTLR start T32
    public final void mT32() throws RecognitionException {
        try {
            int _type = T32;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:30:5: ( '&&' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:30:7: '&&'
            {
            match("&&"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T32

    // $ANTLR start T33
    public final void mT33() throws RecognitionException {
        try {
            int _type = T33;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:31:5: ( '||' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:31:7: '||'
            {
            match("||"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T33

    // $ANTLR start T34
    public final void mT34() throws RecognitionException {
        try {
            int _type = T34;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:32:5: ( '->' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:32:7: '->'
            {
            match("->"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T34

    // $ANTLR start T35
    public final void mT35() throws RecognitionException {
        try {
            int _type = T35;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:33:5: ( '<->' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:33:7: '<->'
            {
            match("<->"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T35

    // $ANTLR start T36
    public final void mT36() throws RecognitionException {
        try {
            int _type = T36;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:34:5: ( '!' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:34:7: '!'
            {
            match('!'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T36

    // $ANTLR start T37
    public final void mT37() throws RecognitionException {
        try {
            int _type = T37;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:35:5: ( 'modifies' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:35:7: 'modifies'
            {
            match("modifies"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T37

    // $ANTLR start T38
    public final void mT38() throws RecognitionException {
        try {
            int _type = T38;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:36:5: ( 'adds' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:36:7: 'adds'
            {
            match("adds"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T38

    // $ANTLR start T39
    public final void mT39() throws RecognitionException {
        try {
            int _type = T39;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:37:5: ( 'remove' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:37:7: 'remove'
            {
            match("remove"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T39

    // $ANTLR start T40
    public final void mT40() throws RecognitionException {
        try {
            int _type = T40;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:38:5: ( 'extending' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:38:7: 'extending'
            {
            match("extending"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T40

    // $ANTLR start T41
    public final void mT41() throws RecognitionException {
        try {
            int _type = T41;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:39:5: ( 'void' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:39:7: 'void'
            {
            match("void"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T41

    // $ANTLR start T42
    public final void mT42() throws RecognitionException {
        try {
            int _type = T42;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:40:5: ( 'int' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:40:7: 'int'
            {
            match("int"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T42

    // $ANTLR start T43
    public final void mT43() throws RecognitionException {
        try {
            int _type = T43;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:41:5: ( 'boolean' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:41:7: 'boolean'
            {
            match("boolean"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T43

    // $ANTLR start T44
    public final void mT44() throws RecognitionException {
        try {
            int _type = T44;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:42:5: ( '<' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:42:7: '<'
            {
            match('<'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T44

    // $ANTLR start T45
    public final void mT45() throws RecognitionException {
        try {
            int _type = T45;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:43:5: ( '>' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:43:7: '>'
            {
            match('>'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T45

    // $ANTLR start T46
    public final void mT46() throws RecognitionException {
        try {
            int _type = T46;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:44:5: ( 'new' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:44:7: 'new'
            {
            match("new"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T46

    // $ANTLR start T47
    public final void mT47() throws RecognitionException {
        try {
            int _type = T47;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:45:5: ( 'original' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:45:7: 'original'
            {
            match("original"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T47

    // $ANTLR start T48
    public final void mT48() throws RecognitionException {
        try {
            int _type = T48;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:46:5: ( 'null' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:46:7: 'null'
            {
            match("null"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T48

    // $ANTLR start RULE_ALL
    public final void mRULE_ALL() throws RecognitionException {
        try {
            int _type = RULE_ALL;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4233:10: ( '**Java:' ( options {greedy=false; } : . )* ':Java**' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4233:12: '**Java:' ( options {greedy=false; } : . )* ':Java**'
            {
            match("**Java:"); 

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4233:22: ( options {greedy=false; } : . )*
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
                                        else if ( ((LA1_7>='\u0000' && LA1_7<=')')||(LA1_7>='+' && LA1_7<='\uFFFE')) ) {
                                            alt1=1;
                                        }


                                    }
                                    else if ( ((LA1_6>='\u0000' && LA1_6<=')')||(LA1_6>='+' && LA1_6<='\uFFFE')) ) {
                                        alt1=1;
                                    }


                                }
                                else if ( ((LA1_5>='\u0000' && LA1_5<='`')||(LA1_5>='b' && LA1_5<='\uFFFE')) ) {
                                    alt1=1;
                                }


                            }
                            else if ( ((LA1_4>='\u0000' && LA1_4<='u')||(LA1_4>='w' && LA1_4<='\uFFFE')) ) {
                                alt1=1;
                            }


                        }
                        else if ( ((LA1_3>='\u0000' && LA1_3<='`')||(LA1_3>='b' && LA1_3<='\uFFFE')) ) {
                            alt1=1;
                        }


                    }
                    else if ( ((LA1_1>='\u0000' && LA1_1<='I')||(LA1_1>='K' && LA1_1<='\uFFFE')) ) {
                        alt1=1;
                    }


                }
                else if ( ((LA1_0>='\u0000' && LA1_0<='9')||(LA1_0>=';' && LA1_0<='\uFFFE')) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4233:50: .
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

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end RULE_ALL

    // $ANTLR start RULE_ID
    public final void mRULE_ID() throws RecognitionException {
        try {
            int _type = RULE_ID;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4235:9: ( ( '^' )? ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9' )* )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4235:11: ( '^' )? ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9' )*
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4235:11: ( '^' )?
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0=='^') ) {
                alt2=1;
            }
            switch (alt2) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4235:11: '^'
                    {
                    match('^'); 

                    }
                    break;

            }

            if ( (input.LA(1)>='A' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse =
                    new MismatchedSetException(null,input);
                recover(mse);    throw mse;
            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4235:40: ( 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9' )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( ((LA3_0>='0' && LA3_0<='9')||(LA3_0>='A' && LA3_0<='Z')||LA3_0=='_'||(LA3_0>='a' && LA3_0<='z')) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:
            	    {
            	    if ( (input.LA(1)>='0' && input.LA(1)<='9')||(input.LA(1)>='A' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse =
            	            new MismatchedSetException(null,input);
            	        recover(mse);    throw mse;
            	    }


            	    }
            	    break;

            	default :
            	    break loop3;
                }
            } while (true);


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end RULE_ID

    // $ANTLR start RULE_INT
    public final void mRULE_INT() throws RecognitionException {
        try {
            int _type = RULE_INT;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4237:10: ( ( '0' .. '9' )+ )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4237:12: ( '0' .. '9' )+
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4237:12: ( '0' .. '9' )+
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
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4237:13: '0' .. '9'
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

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end RULE_INT

    // $ANTLR start RULE_STRING
    public final void mRULE_STRING() throws RecognitionException {
        try {
            int _type = RULE_STRING;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4239:13: ( ( '\"' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\"' ) ) )* '\"' | '\\'' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\\'' ) ) )* '\\'' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4239:15: ( '\"' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\"' ) ) )* '\"' | '\\'' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\\'' ) ) )* '\\'' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4239:15: ( '\"' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\"' ) ) )* '\"' | '\\'' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\\'' ) ) )* '\\'' )
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
                    new NoViableAltException("4239:15: ( '\"' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\"' ) ) )* '\"' | '\\'' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\\'' ) ) )* '\\'' )", 7, 0, input);

                throw nvae;
            }
            switch (alt7) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4239:16: '\"' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\"' ) ) )* '\"'
                    {
                    match('\"'); 
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4239:20: ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\"' ) ) )*
                    loop5:
                    do {
                        int alt5=3;
                        int LA5_0 = input.LA(1);

                        if ( (LA5_0=='\\') ) {
                            alt5=1;
                        }
                        else if ( ((LA5_0>='\u0000' && LA5_0<='!')||(LA5_0>='#' && LA5_0<='[')||(LA5_0>=']' && LA5_0<='\uFFFE')) ) {
                            alt5=2;
                        }


                        switch (alt5) {
                    	case 1 :
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4239:21: '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' )
                    	    {
                    	    match('\\'); 
                    	    if ( input.LA(1)=='\"'||input.LA(1)=='\''||input.LA(1)=='\\'||input.LA(1)=='b'||input.LA(1)=='f'||input.LA(1)=='n'||input.LA(1)=='r'||input.LA(1)=='t' ) {
                    	        input.consume();

                    	    }
                    	    else {
                    	        MismatchedSetException mse =
                    	            new MismatchedSetException(null,input);
                    	        recover(mse);    throw mse;
                    	    }


                    	    }
                    	    break;
                    	case 2 :
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4239:62: ~ ( ( '\\\\' | '\"' ) )
                    	    {
                    	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='!')||(input.LA(1)>='#' && input.LA(1)<='[')||(input.LA(1)>=']' && input.LA(1)<='\uFFFE') ) {
                    	        input.consume();

                    	    }
                    	    else {
                    	        MismatchedSetException mse =
                    	            new MismatchedSetException(null,input);
                    	        recover(mse);    throw mse;
                    	    }


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
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4239:82: '\\'' ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\\'' ) ) )* '\\''
                    {
                    match('\''); 
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4239:87: ( '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' ) | ~ ( ( '\\\\' | '\\'' ) ) )*
                    loop6:
                    do {
                        int alt6=3;
                        int LA6_0 = input.LA(1);

                        if ( (LA6_0=='\\') ) {
                            alt6=1;
                        }
                        else if ( ((LA6_0>='\u0000' && LA6_0<='&')||(LA6_0>='(' && LA6_0<='[')||(LA6_0>=']' && LA6_0<='\uFFFE')) ) {
                            alt6=2;
                        }


                        switch (alt6) {
                    	case 1 :
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4239:88: '\\\\' ( 'b' | 't' | 'n' | 'f' | 'r' | '\"' | '\\'' | '\\\\' )
                    	    {
                    	    match('\\'); 
                    	    if ( input.LA(1)=='\"'||input.LA(1)=='\''||input.LA(1)=='\\'||input.LA(1)=='b'||input.LA(1)=='f'||input.LA(1)=='n'||input.LA(1)=='r'||input.LA(1)=='t' ) {
                    	        input.consume();

                    	    }
                    	    else {
                    	        MismatchedSetException mse =
                    	            new MismatchedSetException(null,input);
                    	        recover(mse);    throw mse;
                    	    }


                    	    }
                    	    break;
                    	case 2 :
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4239:129: ~ ( ( '\\\\' | '\\'' ) )
                    	    {
                    	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='&')||(input.LA(1)>='(' && input.LA(1)<='[')||(input.LA(1)>=']' && input.LA(1)<='\uFFFE') ) {
                    	        input.consume();

                    	    }
                    	    else {
                    	        MismatchedSetException mse =
                    	            new MismatchedSetException(null,input);
                    	        recover(mse);    throw mse;
                    	    }


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

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end RULE_STRING

    // $ANTLR start RULE_ML_COMMENT
    public final void mRULE_ML_COMMENT() throws RecognitionException {
        try {
            int _type = RULE_ML_COMMENT;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4241:17: ( '/*' ( options {greedy=false; } : . )* '*/' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4241:19: '/*' ( options {greedy=false; } : . )* '*/'
            {
            match("/*"); 

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4241:24: ( options {greedy=false; } : . )*
            loop8:
            do {
                int alt8=2;
                int LA8_0 = input.LA(1);

                if ( (LA8_0=='*') ) {
                    int LA8_1 = input.LA(2);

                    if ( (LA8_1=='/') ) {
                        alt8=2;
                    }
                    else if ( ((LA8_1>='\u0000' && LA8_1<='.')||(LA8_1>='0' && LA8_1<='\uFFFE')) ) {
                        alt8=1;
                    }


                }
                else if ( ((LA8_0>='\u0000' && LA8_0<=')')||(LA8_0>='+' && LA8_0<='\uFFFE')) ) {
                    alt8=1;
                }


                switch (alt8) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4241:52: .
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

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end RULE_ML_COMMENT

    // $ANTLR start RULE_SL_COMMENT
    public final void mRULE_SL_COMMENT() throws RecognitionException {
        try {
            int _type = RULE_SL_COMMENT;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4243:17: ( '//' (~ ( ( '\\n' | '\\r' ) ) )* ( ( '\\r' )? '\\n' )? )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4243:19: '//' (~ ( ( '\\n' | '\\r' ) ) )* ( ( '\\r' )? '\\n' )?
            {
            match("//"); 

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4243:24: (~ ( ( '\\n' | '\\r' ) ) )*
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( ((LA9_0>='\u0000' && LA9_0<='\t')||(LA9_0>='\u000B' && LA9_0<='\f')||(LA9_0>='\u000E' && LA9_0<='\uFFFE')) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4243:24: ~ ( ( '\\n' | '\\r' ) )
            	    {
            	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='\t')||(input.LA(1)>='\u000B' && input.LA(1)<='\f')||(input.LA(1)>='\u000E' && input.LA(1)<='\uFFFE') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse =
            	            new MismatchedSetException(null,input);
            	        recover(mse);    throw mse;
            	    }


            	    }
            	    break;

            	default :
            	    break loop9;
                }
            } while (true);

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4243:40: ( ( '\\r' )? '\\n' )?
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0=='\n'||LA11_0=='\r') ) {
                alt11=1;
            }
            switch (alt11) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4243:41: ( '\\r' )? '\\n'
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4243:41: ( '\\r' )?
                    int alt10=2;
                    int LA10_0 = input.LA(1);

                    if ( (LA10_0=='\r') ) {
                        alt10=1;
                    }
                    switch (alt10) {
                        case 1 :
                            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4243:41: '\\r'
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

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end RULE_SL_COMMENT

    // $ANTLR start RULE_WS
    public final void mRULE_WS() throws RecognitionException {
        try {
            int _type = RULE_WS;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4245:9: ( ( ' ' | '\\t' | '\\r' | '\\n' )+ )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4245:11: ( ' ' | '\\t' | '\\r' | '\\n' )+
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4245:11: ( ' ' | '\\t' | '\\r' | '\\n' )+
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
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:
            	    {
            	    if ( (input.LA(1)>='\t' && input.LA(1)<='\n')||input.LA(1)=='\r'||input.LA(1)==' ' ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse =
            	            new MismatchedSetException(null,input);
            	        recover(mse);    throw mse;
            	    }


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

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end RULE_WS

    // $ANTLR start RULE_ANY_OTHER
    public final void mRULE_ANY_OTHER() throws RecognitionException {
        try {
            int _type = RULE_ANY_OTHER;
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4247:16: ( . )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4247:18: .
            {
            matchAny(); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end RULE_ANY_OTHER

    public void mTokens() throws RecognitionException {
        // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:8: ( T12 | T13 | T14 | T15 | T16 | T17 | T18 | T19 | T20 | T21 | T22 | T23 | T24 | T25 | T26 | T27 | T28 | T29 | T30 | T31 | T32 | T33 | T34 | T35 | T36 | T37 | T38 | T39 | T40 | T41 | T42 | T43 | T44 | T45 | T46 | T47 | T48 | RULE_ALL | RULE_ID | RULE_INT | RULE_STRING | RULE_ML_COMMENT | RULE_SL_COMMENT | RULE_WS | RULE_ANY_OTHER )
        int alt13=45;
        int LA13_0 = input.LA(1);

        if ( (LA13_0=='i') ) {
            switch ( input.LA(2) ) {
            case 'n':
                {
                int LA13_39 = input.LA(3);

                if ( (LA13_39=='t') ) {
                    int LA13_80 = input.LA(4);

                    if ( ((LA13_80>='0' && LA13_80<='9')||(LA13_80>='A' && LA13_80<='Z')||LA13_80=='_'||(LA13_80>='a' && LA13_80<='z')) ) {
                        alt13=39;
                    }
                    else {
                        alt13=31;}
                }
                else {
                    alt13=39;}
                }
                break;
            case 'm':
                {
                int LA13_40 = input.LA(3);

                if ( (LA13_40=='p') ) {
                    int LA13_81 = input.LA(4);

                    if ( (LA13_81=='o') ) {
                        int LA13_102 = input.LA(5);

                        if ( (LA13_102=='r') ) {
                            int LA13_122 = input.LA(6);

                            if ( (LA13_122=='t') ) {
                                int LA13_141 = input.LA(7);

                                if ( ((LA13_141>='0' && LA13_141<='9')||(LA13_141>='A' && LA13_141<='Z')||LA13_141=='_'||(LA13_141>='a' && LA13_141<='z')) ) {
                                    alt13=39;
                                }
                                else {
                                    alt13=1;}
                            }
                            else {
                                alt13=39;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
                }
                break;
            default:
                alt13=39;}

        }
        else if ( (LA13_0=='f') ) {
            int LA13_2 = input.LA(2);

            if ( (LA13_2=='e') ) {
                int LA13_42 = input.LA(3);

                if ( (LA13_42=='a') ) {
                    int LA13_82 = input.LA(4);

                    if ( (LA13_82=='t') ) {
                        int LA13_103 = input.LA(5);

                        if ( (LA13_103=='u') ) {
                            int LA13_123 = input.LA(6);

                            if ( (LA13_123=='r') ) {
                                int LA13_142 = input.LA(7);

                                if ( (LA13_142=='e') ) {
                                    int LA13_155 = input.LA(8);

                                    if ( (LA13_155=='s') ) {
                                        int LA13_164 = input.LA(9);

                                        if ( ((LA13_164>='0' && LA13_164<='9')||(LA13_164>='A' && LA13_164<='Z')||LA13_164=='_'||(LA13_164>='a' && LA13_164<='z')) ) {
                                            alt13=39;
                                        }
                                        else {
                                            alt13=2;}
                                    }
                                    else {
                                        alt13=39;}
                                }
                                else {
                                    alt13=39;}
                            }
                            else {
                                alt13=39;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
            }
            else {
                alt13=39;}
        }
        else if ( (LA13_0==',') ) {
            alt13=3;
        }
        else if ( (LA13_0=='c') ) {
            switch ( input.LA(2) ) {
            case 'o':
                {
                switch ( input.LA(3) ) {
                case 'r':
                    {
                    int LA13_83 = input.LA(4);

                    if ( (LA13_83=='e') ) {
                        int LA13_104 = input.LA(5);

                        if ( ((LA13_104>='0' && LA13_104<='9')||(LA13_104>='A' && LA13_104<='Z')||LA13_104=='_'||(LA13_104>='a' && LA13_104<='z')) ) {
                            alt13=39;
                        }
                        else {
                            alt13=5;}
                    }
                    else {
                        alt13=39;}
                    }
                    break;
                case 'n':
                    {
                    int LA13_84 = input.LA(4);

                    if ( (LA13_84=='f') ) {
                        int LA13_105 = input.LA(5);

                        if ( (LA13_105=='i') ) {
                            int LA13_125 = input.LA(6);

                            if ( (LA13_125=='g') ) {
                                int LA13_143 = input.LA(7);

                                if ( (LA13_143=='u') ) {
                                    int LA13_156 = input.LA(8);

                                    if ( (LA13_156=='r') ) {
                                        int LA13_165 = input.LA(9);

                                        if ( (LA13_165=='a') ) {
                                            int LA13_172 = input.LA(10);

                                            if ( (LA13_172=='t') ) {
                                                int LA13_176 = input.LA(11);

                                                if ( (LA13_176=='i') ) {
                                                    int LA13_178 = input.LA(12);

                                                    if ( (LA13_178=='o') ) {
                                                        int LA13_179 = input.LA(13);

                                                        if ( (LA13_179=='n') ) {
                                                            int LA13_180 = input.LA(14);

                                                            if ( (LA13_180=='s') ) {
                                                                int LA13_181 = input.LA(15);

                                                                if ( ((LA13_181>='0' && LA13_181<='9')||(LA13_181>='A' && LA13_181<='Z')||LA13_181=='_'||(LA13_181>='a' && LA13_181<='z')) ) {
                                                                    alt13=39;
                                                                }
                                                                else {
                                                                    alt13=4;}
                                                            }
                                                            else {
                                                                alt13=39;}
                                                        }
                                                        else {
                                                            alt13=39;}
                                                    }
                                                    else {
                                                        alt13=39;}
                                                }
                                                else {
                                                    alt13=39;}
                                            }
                                            else {
                                                alt13=39;}
                                        }
                                        else {
                                            alt13=39;}
                                    }
                                    else {
                                        alt13=39;}
                                }
                                else {
                                    alt13=39;}
                            }
                            else {
                                alt13=39;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                    }
                    break;
                default:
                    alt13=39;}

                }
                break;
            case 'l':
                {
                int LA13_45 = input.LA(3);

                if ( (LA13_45=='a') ) {
                    int LA13_85 = input.LA(4);

                    if ( (LA13_85=='s') ) {
                        int LA13_106 = input.LA(5);

                        if ( (LA13_106=='s') ) {
                            int LA13_126 = input.LA(6);

                            if ( ((LA13_126>='0' && LA13_126<='9')||(LA13_126>='A' && LA13_126<='Z')||LA13_126=='_'||(LA13_126>='a' && LA13_126<='z')) ) {
                                alt13=39;
                            }
                            else {
                                alt13=9;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
                }
                break;
            default:
                alt13=39;}

        }
        else if ( (LA13_0=='d') ) {
            int LA13_5 = input.LA(2);

            if ( (LA13_5=='e') ) {
                int LA13_46 = input.LA(3);

                if ( (LA13_46=='l') ) {
                    int LA13_86 = input.LA(4);

                    if ( (LA13_86=='t') ) {
                        int LA13_107 = input.LA(5);

                        if ( (LA13_107=='a') ) {
                            int LA13_127 = input.LA(6);

                            if ( ((LA13_127>='0' && LA13_127<='9')||(LA13_127>='A' && LA13_127<='Z')||LA13_127=='_'||(LA13_127>='a' && LA13_127<='z')) ) {
                                alt13=39;
                            }
                            else {
                                alt13=6;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
            }
            else {
                alt13=39;}
        }
        else if ( (LA13_0=='{') ) {
            alt13=7;
        }
        else if ( (LA13_0=='}') ) {
            alt13=8;
        }
        else if ( (LA13_0=='e') ) {
            int LA13_8 = input.LA(2);

            if ( (LA13_8=='x') ) {
                int LA13_49 = input.LA(3);

                if ( (LA13_49=='t') ) {
                    int LA13_87 = input.LA(4);

                    if ( (LA13_87=='e') ) {
                        int LA13_108 = input.LA(5);

                        if ( (LA13_108=='n') ) {
                            int LA13_128 = input.LA(6);

                            if ( (LA13_128=='d') ) {
                                switch ( input.LA(7) ) {
                                case 'i':
                                    {
                                    int LA13_157 = input.LA(8);

                                    if ( (LA13_157=='n') ) {
                                        int LA13_166 = input.LA(9);

                                        if ( (LA13_166=='g') ) {
                                            int LA13_173 = input.LA(10);

                                            if ( ((LA13_173>='0' && LA13_173<='9')||(LA13_173>='A' && LA13_173<='Z')||LA13_173=='_'||(LA13_173>='a' && LA13_173<='z')) ) {
                                                alt13=39;
                                            }
                                            else {
                                                alt13=29;}
                                        }
                                        else {
                                            alt13=39;}
                                    }
                                    else {
                                        alt13=39;}
                                    }
                                    break;
                                case 's':
                                    {
                                    int LA13_158 = input.LA(8);

                                    if ( ((LA13_158>='0' && LA13_158<='9')||(LA13_158>='A' && LA13_158<='Z')||LA13_158=='_'||(LA13_158>='a' && LA13_158<='z')) ) {
                                        alt13=39;
                                    }
                                    else {
                                        alt13=10;}
                                    }
                                    break;
                                default:
                                    alt13=39;}

                            }
                            else {
                                alt13=39;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
            }
            else {
                alt13=39;}
        }
        else if ( (LA13_0=='(') ) {
            alt13=11;
        }
        else if ( (LA13_0==')') ) {
            alt13=12;
        }
        else if ( (LA13_0=='s') ) {
            int LA13_11 = input.LA(2);

            if ( (LA13_11=='u') ) {
                int LA13_52 = input.LA(3);

                if ( (LA13_52=='p') ) {
                    int LA13_88 = input.LA(4);

                    if ( (LA13_88=='e') ) {
                        int LA13_109 = input.LA(5);

                        if ( (LA13_109=='r') ) {
                            int LA13_129 = input.LA(6);

                            if ( ((LA13_129>='0' && LA13_129<='9')||(LA13_129>='A' && LA13_129<='Z')||LA13_129=='_'||(LA13_129>='a' && LA13_129<='z')) ) {
                                alt13=39;
                            }
                            else {
                                alt13=13;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
            }
            else {
                alt13=39;}
        }
        else if ( (LA13_0==';') ) {
            alt13=14;
        }
        else if ( (LA13_0=='t') ) {
            int LA13_13 = input.LA(2);

            if ( (LA13_13=='h') ) {
                int LA13_54 = input.LA(3);

                if ( (LA13_54=='i') ) {
                    int LA13_89 = input.LA(4);

                    if ( (LA13_89=='s') ) {
                        int LA13_110 = input.LA(5);

                        if ( ((LA13_110>='0' && LA13_110<='9')||(LA13_110>='A' && LA13_110<='Z')||LA13_110=='_'||(LA13_110>='a' && LA13_110<='z')) ) {
                            alt13=39;
                        }
                        else {
                            alt13=15;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
            }
            else {
                alt13=39;}
        }
        else if ( (LA13_0=='.') ) {
            alt13=16;
        }
        else if ( (LA13_0=='=') ) {
            alt13=17;
        }
        else if ( (LA13_0=='r') ) {
            int LA13_16 = input.LA(2);

            if ( (LA13_16=='e') ) {
                switch ( input.LA(3) ) {
                case 'm':
                    {
                    int LA13_90 = input.LA(4);

                    if ( (LA13_90=='o') ) {
                        int LA13_111 = input.LA(5);

                        if ( (LA13_111=='v') ) {
                            int LA13_131 = input.LA(6);

                            if ( (LA13_131=='e') ) {
                                int LA13_148 = input.LA(7);

                                if ( ((LA13_148>='0' && LA13_148<='9')||(LA13_148>='A' && LA13_148<='Z')||LA13_148=='_'||(LA13_148>='a' && LA13_148<='z')) ) {
                                    alt13=39;
                                }
                                else {
                                    alt13=28;}
                            }
                            else {
                                alt13=39;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                    }
                    break;
                case 't':
                    {
                    int LA13_91 = input.LA(4);

                    if ( (LA13_91=='u') ) {
                        int LA13_112 = input.LA(5);

                        if ( (LA13_112=='r') ) {
                            int LA13_132 = input.LA(6);

                            if ( (LA13_132=='n') ) {
                                int LA13_149 = input.LA(7);

                                if ( ((LA13_149>='0' && LA13_149<='9')||(LA13_149>='A' && LA13_149<='Z')||LA13_149=='_'||(LA13_149>='a' && LA13_149<='z')) ) {
                                    alt13=39;
                                }
                                else {
                                    alt13=18;}
                            }
                            else {
                                alt13=39;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                    }
                    break;
                default:
                    alt13=39;}

            }
            else {
                alt13=39;}
        }
        else if ( (LA13_0=='a') ) {
            switch ( input.LA(2) ) {
            case 'd':
                {
                int LA13_58 = input.LA(3);

                if ( (LA13_58=='d') ) {
                    int LA13_92 = input.LA(4);

                    if ( (LA13_92=='s') ) {
                        int LA13_113 = input.LA(5);

                        if ( ((LA13_113>='0' && LA13_113<='9')||(LA13_113>='A' && LA13_113<='Z')||LA13_113=='_'||(LA13_113>='a' && LA13_113<='z')) ) {
                            alt13=39;
                        }
                        else {
                            alt13=27;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
                }
                break;
            case 'f':
                {
                int LA13_59 = input.LA(3);

                if ( (LA13_59=='t') ) {
                    int LA13_93 = input.LA(4);

                    if ( (LA13_93=='e') ) {
                        int LA13_114 = input.LA(5);

                        if ( (LA13_114=='r') ) {
                            int LA13_134 = input.LA(6);

                            if ( ((LA13_134>='0' && LA13_134<='9')||(LA13_134>='A' && LA13_134<='Z')||LA13_134=='_'||(LA13_134>='a' && LA13_134<='z')) ) {
                                alt13=39;
                            }
                            else {
                                alt13=19;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
                }
                break;
            default:
                alt13=39;}

        }
        else if ( (LA13_0=='w') ) {
            int LA13_18 = input.LA(2);

            if ( (LA13_18=='h') ) {
                int LA13_60 = input.LA(3);

                if ( (LA13_60=='e') ) {
                    int LA13_94 = input.LA(4);

                    if ( (LA13_94=='n') ) {
                        int LA13_115 = input.LA(5);

                        if ( ((LA13_115>='0' && LA13_115<='9')||(LA13_115>='A' && LA13_115<='Z')||LA13_115=='_'||(LA13_115>='a' && LA13_115<='z')) ) {
                            alt13=39;
                        }
                        else {
                            alt13=20;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
            }
            else {
                alt13=39;}
        }
        else if ( (LA13_0=='&') ) {
            int LA13_19 = input.LA(2);

            if ( (LA13_19=='&') ) {
                alt13=21;
            }
            else {
                alt13=45;}
        }
        else if ( (LA13_0=='|') ) {
            int LA13_20 = input.LA(2);

            if ( (LA13_20=='|') ) {
                alt13=22;
            }
            else {
                alt13=45;}
        }
        else if ( (LA13_0=='-') ) {
            int LA13_21 = input.LA(2);

            if ( (LA13_21=='>') ) {
                alt13=23;
            }
            else {
                alt13=45;}
        }
        else if ( (LA13_0=='<') ) {
            int LA13_22 = input.LA(2);

            if ( (LA13_22=='-') ) {
                alt13=24;
            }
            else {
                alt13=33;}
        }
        else if ( (LA13_0=='!') ) {
            alt13=25;
        }
        else if ( (LA13_0=='m') ) {
            int LA13_24 = input.LA(2);

            if ( (LA13_24=='o') ) {
                int LA13_67 = input.LA(3);

                if ( (LA13_67=='d') ) {
                    int LA13_95 = input.LA(4);

                    if ( (LA13_95=='i') ) {
                        int LA13_116 = input.LA(5);

                        if ( (LA13_116=='f') ) {
                            int LA13_136 = input.LA(6);

                            if ( (LA13_136=='i') ) {
                                int LA13_151 = input.LA(7);

                                if ( (LA13_151=='e') ) {
                                    int LA13_161 = input.LA(8);

                                    if ( (LA13_161=='s') ) {
                                        int LA13_168 = input.LA(9);

                                        if ( ((LA13_168>='0' && LA13_168<='9')||(LA13_168>='A' && LA13_168<='Z')||LA13_168=='_'||(LA13_168>='a' && LA13_168<='z')) ) {
                                            alt13=39;
                                        }
                                        else {
                                            alt13=26;}
                                    }
                                    else {
                                        alt13=39;}
                                }
                                else {
                                    alt13=39;}
                            }
                            else {
                                alt13=39;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
            }
            else {
                alt13=39;}
        }
        else if ( (LA13_0=='v') ) {
            int LA13_25 = input.LA(2);

            if ( (LA13_25=='o') ) {
                int LA13_68 = input.LA(3);

                if ( (LA13_68=='i') ) {
                    int LA13_96 = input.LA(4);

                    if ( (LA13_96=='d') ) {
                        int LA13_117 = input.LA(5);

                        if ( ((LA13_117>='0' && LA13_117<='9')||(LA13_117>='A' && LA13_117<='Z')||LA13_117=='_'||(LA13_117>='a' && LA13_117<='z')) ) {
                            alt13=39;
                        }
                        else {
                            alt13=30;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
            }
            else {
                alt13=39;}
        }
        else if ( (LA13_0=='b') ) {
            int LA13_26 = input.LA(2);

            if ( (LA13_26=='o') ) {
                int LA13_69 = input.LA(3);

                if ( (LA13_69=='o') ) {
                    int LA13_97 = input.LA(4);

                    if ( (LA13_97=='l') ) {
                        int LA13_118 = input.LA(5);

                        if ( (LA13_118=='e') ) {
                            int LA13_138 = input.LA(6);

                            if ( (LA13_138=='a') ) {
                                int LA13_152 = input.LA(7);

                                if ( (LA13_152=='n') ) {
                                    int LA13_162 = input.LA(8);

                                    if ( ((LA13_162>='0' && LA13_162<='9')||(LA13_162>='A' && LA13_162<='Z')||LA13_162=='_'||(LA13_162>='a' && LA13_162<='z')) ) {
                                        alt13=39;
                                    }
                                    else {
                                        alt13=32;}
                                }
                                else {
                                    alt13=39;}
                            }
                            else {
                                alt13=39;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
            }
            else {
                alt13=39;}
        }
        else if ( (LA13_0=='>') ) {
            alt13=34;
        }
        else if ( (LA13_0=='n') ) {
            switch ( input.LA(2) ) {
            case 'u':
                {
                int LA13_71 = input.LA(3);

                if ( (LA13_71=='l') ) {
                    int LA13_98 = input.LA(4);

                    if ( (LA13_98=='l') ) {
                        int LA13_119 = input.LA(5);

                        if ( ((LA13_119>='0' && LA13_119<='9')||(LA13_119>='A' && LA13_119<='Z')||LA13_119=='_'||(LA13_119>='a' && LA13_119<='z')) ) {
                            alt13=39;
                        }
                        else {
                            alt13=37;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
                }
                break;
            case 'e':
                {
                int LA13_72 = input.LA(3);

                if ( (LA13_72=='w') ) {
                    int LA13_99 = input.LA(4);

                    if ( ((LA13_99>='0' && LA13_99<='9')||(LA13_99>='A' && LA13_99<='Z')||LA13_99=='_'||(LA13_99>='a' && LA13_99<='z')) ) {
                        alt13=39;
                    }
                    else {
                        alt13=35;}
                }
                else {
                    alt13=39;}
                }
                break;
            default:
                alt13=39;}

        }
        else if ( (LA13_0=='o') ) {
            int LA13_29 = input.LA(2);

            if ( (LA13_29=='r') ) {
                int LA13_73 = input.LA(3);

                if ( (LA13_73=='i') ) {
                    int LA13_100 = input.LA(4);

                    if ( (LA13_100=='g') ) {
                        int LA13_121 = input.LA(5);

                        if ( (LA13_121=='i') ) {
                            int LA13_140 = input.LA(6);

                            if ( (LA13_140=='n') ) {
                                int LA13_153 = input.LA(7);

                                if ( (LA13_153=='a') ) {
                                    int LA13_163 = input.LA(8);

                                    if ( (LA13_163=='l') ) {
                                        int LA13_170 = input.LA(9);

                                        if ( ((LA13_170>='0' && LA13_170<='9')||(LA13_170>='A' && LA13_170<='Z')||LA13_170=='_'||(LA13_170>='a' && LA13_170<='z')) ) {
                                            alt13=39;
                                        }
                                        else {
                                            alt13=36;}
                                    }
                                    else {
                                        alt13=39;}
                                }
                                else {
                                    alt13=39;}
                            }
                            else {
                                alt13=39;}
                        }
                        else {
                            alt13=39;}
                    }
                    else {
                        alt13=39;}
                }
                else {
                    alt13=39;}
            }
            else {
                alt13=39;}
        }
        else if ( (LA13_0=='*') ) {
            int LA13_30 = input.LA(2);

            if ( (LA13_30=='*') ) {
                alt13=38;
            }
            else {
                alt13=45;}
        }
        else if ( (LA13_0=='^') ) {
            int LA13_31 = input.LA(2);

            if ( ((LA13_31>='A' && LA13_31<='Z')||LA13_31=='_'||(LA13_31>='a' && LA13_31<='z')) ) {
                alt13=39;
            }
            else {
                alt13=45;}
        }
        else if ( ((LA13_0>='A' && LA13_0<='Z')||LA13_0=='_'||(LA13_0>='g' && LA13_0<='h')||(LA13_0>='j' && LA13_0<='l')||(LA13_0>='p' && LA13_0<='q')||LA13_0=='u'||(LA13_0>='x' && LA13_0<='z')) ) {
            alt13=39;
        }
        else if ( ((LA13_0>='0' && LA13_0<='9')) ) {
            alt13=40;
        }
        else if ( (LA13_0=='\"') ) {
            int LA13_34 = input.LA(2);

            if ( ((LA13_34>='\u0000' && LA13_34<='\uFFFE')) ) {
                alt13=41;
            }
            else {
                alt13=45;}
        }
        else if ( (LA13_0=='\'') ) {
            int LA13_35 = input.LA(2);

            if ( ((LA13_35>='\u0000' && LA13_35<='\uFFFE')) ) {
                alt13=41;
            }
            else {
                alt13=45;}
        }
        else if ( (LA13_0=='/') ) {
            switch ( input.LA(2) ) {
            case '/':
                {
                alt13=43;
                }
                break;
            case '*':
                {
                alt13=42;
                }
                break;
            default:
                alt13=45;}

        }
        else if ( ((LA13_0>='\t' && LA13_0<='\n')||LA13_0=='\r'||LA13_0==' ') ) {
            alt13=44;
        }
        else if ( ((LA13_0>='\u0000' && LA13_0<='\b')||(LA13_0>='\u000B' && LA13_0<='\f')||(LA13_0>='\u000E' && LA13_0<='\u001F')||(LA13_0>='#' && LA13_0<='%')||LA13_0=='+'||LA13_0==':'||(LA13_0>='?' && LA13_0<='@')||(LA13_0>='[' && LA13_0<=']')||LA13_0=='`'||(LA13_0>='~' && LA13_0<='\uFFFE')) ) {
            alt13=45;
        }
        else {
            NoViableAltException nvae =
                new NoViableAltException("1:1: Tokens : ( T12 | T13 | T14 | T15 | T16 | T17 | T18 | T19 | T20 | T21 | T22 | T23 | T24 | T25 | T26 | T27 | T28 | T29 | T30 | T31 | T32 | T33 | T34 | T35 | T36 | T37 | T38 | T39 | T40 | T41 | T42 | T43 | T44 | T45 | T46 | T47 | T48 | RULE_ALL | RULE_ID | RULE_INT | RULE_STRING | RULE_ML_COMMENT | RULE_SL_COMMENT | RULE_WS | RULE_ANY_OTHER );", 13, 0, input);

            throw nvae;
        }
        switch (alt13) {
            case 1 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:10: T12
                {
                mT12(); 

                }
                break;
            case 2 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:14: T13
                {
                mT13(); 

                }
                break;
            case 3 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:18: T14
                {
                mT14(); 

                }
                break;
            case 4 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:22: T15
                {
                mT15(); 

                }
                break;
            case 5 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:26: T16
                {
                mT16(); 

                }
                break;
            case 6 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:30: T17
                {
                mT17(); 

                }
                break;
            case 7 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:34: T18
                {
                mT18(); 

                }
                break;
            case 8 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:38: T19
                {
                mT19(); 

                }
                break;
            case 9 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:42: T20
                {
                mT20(); 

                }
                break;
            case 10 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:46: T21
                {
                mT21(); 

                }
                break;
            case 11 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:50: T22
                {
                mT22(); 

                }
                break;
            case 12 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:54: T23
                {
                mT23(); 

                }
                break;
            case 13 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:58: T24
                {
                mT24(); 

                }
                break;
            case 14 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:62: T25
                {
                mT25(); 

                }
                break;
            case 15 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:66: T26
                {
                mT26(); 

                }
                break;
            case 16 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:70: T27
                {
                mT27(); 

                }
                break;
            case 17 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:74: T28
                {
                mT28(); 

                }
                break;
            case 18 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:78: T29
                {
                mT29(); 

                }
                break;
            case 19 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:82: T30
                {
                mT30(); 

                }
                break;
            case 20 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:86: T31
                {
                mT31(); 

                }
                break;
            case 21 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:90: T32
                {
                mT32(); 

                }
                break;
            case 22 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:94: T33
                {
                mT33(); 

                }
                break;
            case 23 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:98: T34
                {
                mT34(); 

                }
                break;
            case 24 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:102: T35
                {
                mT35(); 

                }
                break;
            case 25 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:106: T36
                {
                mT36(); 

                }
                break;
            case 26 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:110: T37
                {
                mT37(); 

                }
                break;
            case 27 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:114: T38
                {
                mT38(); 

                }
                break;
            case 28 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:118: T39
                {
                mT39(); 

                }
                break;
            case 29 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:122: T40
                {
                mT40(); 

                }
                break;
            case 30 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:126: T41
                {
                mT41(); 

                }
                break;
            case 31 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:130: T42
                {
                mT42(); 

                }
                break;
            case 32 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:134: T43
                {
                mT43(); 

                }
                break;
            case 33 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:138: T44
                {
                mT44(); 

                }
                break;
            case 34 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:142: T45
                {
                mT45(); 

                }
                break;
            case 35 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:146: T46
                {
                mT46(); 

                }
                break;
            case 36 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:150: T47
                {
                mT47(); 

                }
                break;
            case 37 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:154: T48
                {
                mT48(); 

                }
                break;
            case 38 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:158: RULE_ALL
                {
                mRULE_ALL(); 

                }
                break;
            case 39 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:167: RULE_ID
                {
                mRULE_ID(); 

                }
                break;
            case 40 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:175: RULE_INT
                {
                mRULE_INT(); 

                }
                break;
            case 41 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:184: RULE_STRING
                {
                mRULE_STRING(); 

                }
                break;
            case 42 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:196: RULE_ML_COMMENT
                {
                mRULE_ML_COMMENT(); 

                }
                break;
            case 43 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:212: RULE_SL_COMMENT
                {
                mRULE_SL_COMMENT(); 

                }
                break;
            case 44 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:228: RULE_WS
                {
                mRULE_WS(); 

                }
                break;
            case 45 :
                // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1:236: RULE_ANY_OTHER
                {
                mRULE_ANY_OTHER(); 

                }
                break;

        }

    }


 

}