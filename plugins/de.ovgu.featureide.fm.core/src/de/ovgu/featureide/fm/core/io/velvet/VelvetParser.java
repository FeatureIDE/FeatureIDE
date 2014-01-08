// $ANTLR 3.4 Velvet.g 2014-01-08 20:51:08

package de.ovgu.featureide.fm.core.io.velvet;

import de.ovgu.featureide.fm.core.FMCorePlugin;

import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

import org.antlr.runtime.tree.*;


@SuppressWarnings({"all", "warnings", "unchecked"})
public class VelvetParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "ABSTRACT", "ACONSTR", "ATTR", "ATTR_OP_EQUALS", "ATTR_OP_GREATER", "ATTR_OP_GREATER_EQ", "ATTR_OP_LESS", "ATTR_OP_LESS_EQ", "ATTR_OP_NOT_EQUALS", "BASEEXT", "BASEPARAM", "BOOLEAN", "CINTERFACE", "COLON", "COMMA", "CONCEPT", "CONSTR", "CONSTRAINT", "DEF", "END_C", "END_R", "EQ", "ESC_SEQ", "EXPONENT", "FEAT", "FEATURE", "FLOAT", "GROUP", "HEX_DIGIT", "ID", "IDPath", "IMP", "IMPORT", "INSTANCE", "INSTANCEDEF", "INT", "INTER", "MANDATORY", "MINUS", "OCTAL_ESC", "ONEOF", "OPERAND", "OP_AND", "OP_EQUIVALENT", "OP_IMPLIES", "OP_NOT", "OP_OR", "OP_XOR", "PLUS", "REFINES", "SEMI", "SOMEOF", "START_C", "START_R", "STRING", "UNARYOP", "UNICODE_ESC", "VAR_BOOL", "VAR_FLOAT", "VAR_INT", "VAR_STRING", "WS"
    };

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
    public static final int BASEPARAM=14;
    public static final int BOOLEAN=15;
    public static final int CINTERFACE=16;
    public static final int COLON=17;
    public static final int COMMA=18;
    public static final int CONCEPT=19;
    public static final int CONSTR=20;
    public static final int CONSTRAINT=21;
    public static final int DEF=22;
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
    public static final int IMP=35;
    public static final int IMPORT=36;
    public static final int INSTANCE=37;
    public static final int INSTANCEDEF=38;
    public static final int INT=39;
    public static final int INTER=40;
    public static final int MANDATORY=41;
    public static final int MINUS=42;
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
    public static final int REFINES=53;
    public static final int SEMI=54;
    public static final int SOMEOF=55;
    public static final int START_C=56;
    public static final int START_R=57;
    public static final int STRING=58;
    public static final int UNARYOP=59;
    public static final int UNICODE_ESC=60;
    public static final int VAR_BOOL=61;
    public static final int VAR_FLOAT=62;
    public static final int VAR_INT=63;
    public static final int VAR_STRING=64;
    public static final int WS=65;

    // delegates
    public Parser[] getDelegates() {
        return new Parser[] {};
    }

    // delegators


    public VelvetParser(TokenStream input) {
        this(input, new RecognizerSharedState());
    }
    public VelvetParser(TokenStream input, RecognizerSharedState state) {
        super(input, state);
    }

protected TreeAdaptor adaptor = new CommonTreeAdaptor();

public void setTreeAdaptor(TreeAdaptor adaptor) {
    this.adaptor = adaptor;
}
public TreeAdaptor getTreeAdaptor() {
    return adaptor;
}
    public String[] getTokenNames() { return VelvetParser.tokenNames; }
    public String getGrammarFileName() { return "Velvet.g"; }


    @Override    
    public void emitErrorMessage(String msg) {
    	FMCorePlugin.getDefault().logError(new Exception(msg));
    }


    public static class velvetModel_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "velvetModel"
    // Velvet.g:80:1: velvetModel : ( imports )? ( instancedef )* ( concept | cinterface ) EOF ;
    public final VelvetParser.velvetModel_return velvetModel() throws RecognitionException {
        VelvetParser.velvetModel_return retval = new VelvetParser.velvetModel_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token EOF5=null;
        VelvetParser.imports_return imports1 =null;

        VelvetParser.instancedef_return instancedef2 =null;

        VelvetParser.concept_return concept3 =null;

        VelvetParser.cinterface_return cinterface4 =null;


        Tree EOF5_tree=null;

        try {
            // Velvet.g:81:2: ( ( imports )? ( instancedef )* ( concept | cinterface ) EOF )
            // Velvet.g:81:4: ( imports )? ( instancedef )* ( concept | cinterface ) EOF
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:81:4: ( imports )?
            int alt1=2;
            int LA1_0 = input.LA(1);

            if ( (LA1_0==IMPORT) ) {
                alt1=1;
            }
            switch (alt1) {
                case 1 :
                    // Velvet.g:81:4: imports
                    {
                    pushFollow(FOLLOW_imports_in_velvetModel459);
                    imports1=imports();

                    state._fsp--;

                    adaptor.addChild(root_0, imports1.getTree());

                    }
                    break;

            }


            // Velvet.g:81:13: ( instancedef )*
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( (LA2_0==ID) ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // Velvet.g:81:13: instancedef
            	    {
            	    pushFollow(FOLLOW_instancedef_in_velvetModel462);
            	    instancedef2=instancedef();

            	    state._fsp--;

            	    adaptor.addChild(root_0, instancedef2.getTree());

            	    }
            	    break;

            	default :
            	    break loop2;
                }
            } while (true);


            // Velvet.g:81:26: ( concept | cinterface )
            int alt3=2;
            switch ( input.LA(1) ) {
            case REFINES:
                {
                int LA3_1 = input.LA(2);

                if ( (LA3_1==CONCEPT) ) {
                    alt3=1;
                }
                else if ( (LA3_1==CINTERFACE) ) {
                    alt3=2;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 3, 1, input);

                    throw nvae;

                }
                }
                break;
            case CONCEPT:
                {
                alt3=1;
                }
                break;
            case CINTERFACE:
                {
                alt3=2;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;

            }

            switch (alt3) {
                case 1 :
                    // Velvet.g:81:27: concept
                    {
                    pushFollow(FOLLOW_concept_in_velvetModel466);
                    concept3=concept();

                    state._fsp--;

                    adaptor.addChild(root_0, concept3.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:81:35: cinterface
                    {
                    pushFollow(FOLLOW_cinterface_in_velvetModel468);
                    cinterface4=cinterface();

                    state._fsp--;

                    adaptor.addChild(root_0, cinterface4.getTree());

                    }
                    break;

            }


            EOF5=(Token)match(input,EOF,FOLLOW_EOF_in_velvetModel471); 
            EOF5_tree = 
            (Tree)adaptor.create(EOF5)
            ;
            adaptor.addChild(root_0, EOF5_tree);


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "velvetModel"


    public static class instancedef_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "instancedef"
    // Velvet.g:84:1: instancedef : ID name SEMI -> ^( INSTANCEDEF ID name ) ;
    public final VelvetParser.instancedef_return instancedef() throws RecognitionException {
        VelvetParser.instancedef_return retval = new VelvetParser.instancedef_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID6=null;
        Token SEMI8=null;
        VelvetParser.name_return name7 =null;


        Tree ID6_tree=null;
        Tree SEMI8_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:85:2: ( ID name SEMI -> ^( INSTANCEDEF ID name ) )
            // Velvet.g:85:4: ID name SEMI
            {
            ID6=(Token)match(input,ID,FOLLOW_ID_in_instancedef483);  
            stream_ID.add(ID6);


            pushFollow(FOLLOW_name_in_instancedef485);
            name7=name();

            state._fsp--;

            stream_name.add(name7.getTree());

            SEMI8=(Token)match(input,SEMI,FOLLOW_SEMI_in_instancedef487);  
            stream_SEMI.add(SEMI8);


            // AST REWRITE
            // elements: ID, name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 86:2: -> ^( INSTANCEDEF ID name )
            {
                // Velvet.g:86:5: ^( INSTANCEDEF ID name )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(INSTANCEDEF, "INSTANCEDEF")
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                adaptor.addChild(root_1, stream_name.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "instancedef"


    public static class imports_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "imports"
    // Velvet.g:89:1: imports : ( IMPORT name SEMI )+ -> ^( IMP ( name )+ ) ;
    public final VelvetParser.imports_return imports() throws RecognitionException {
        VelvetParser.imports_return retval = new VelvetParser.imports_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token IMPORT9=null;
        Token SEMI11=null;
        VelvetParser.name_return name10 =null;


        Tree IMPORT9_tree=null;
        Tree SEMI11_tree=null;
        RewriteRuleTokenStream stream_IMPORT=new RewriteRuleTokenStream(adaptor,"token IMPORT");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:89:9: ( ( IMPORT name SEMI )+ -> ^( IMP ( name )+ ) )
            // Velvet.g:89:11: ( IMPORT name SEMI )+
            {
            // Velvet.g:89:11: ( IMPORT name SEMI )+
            int cnt4=0;
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( (LA4_0==IMPORT) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // Velvet.g:89:12: IMPORT name SEMI
            	    {
            	    IMPORT9=(Token)match(input,IMPORT,FOLLOW_IMPORT_in_imports509);  
            	    stream_IMPORT.add(IMPORT9);


            	    pushFollow(FOLLOW_name_in_imports511);
            	    name10=name();

            	    state._fsp--;

            	    stream_name.add(name10.getTree());

            	    SEMI11=(Token)match(input,SEMI,FOLLOW_SEMI_in_imports513);  
            	    stream_SEMI.add(SEMI11);


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


            // AST REWRITE
            // elements: name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 90:2: -> ^( IMP ( name )+ )
            {
                // Velvet.g:90:5: ^( IMP ( name )+ )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(IMP, "IMP")
                , root_1);

                if ( !(stream_name.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_name.hasNext() ) {
                    adaptor.addChild(root_1, stream_name.nextTree());

                }
                stream_name.reset();

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "imports"


    public static class concept_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "concept"
    // Velvet.g:93:1: concept : ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )? definitions -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? ( conceptInterExt )* definitions ) ;
    public final VelvetParser.concept_return concept() throws RecognitionException {
        VelvetParser.concept_return retval = new VelvetParser.concept_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token REFINES12=null;
        Token CONCEPT13=null;
        Token ID14=null;
        Token COLON15=null;
        Token START_R17=null;
        Token COMMA19=null;
        Token END_R21=null;
        VelvetParser.conceptBaseExt_return conceptBaseExt16 =null;

        VelvetParser.conceptInterExt_return conceptInterExt18 =null;

        VelvetParser.conceptInterExt_return conceptInterExt20 =null;

        VelvetParser.definitions_return definitions22 =null;


        Tree REFINES12_tree=null;
        Tree CONCEPT13_tree=null;
        Tree ID14_tree=null;
        Tree COLON15_tree=null;
        Tree START_R17_tree=null;
        Tree COMMA19_tree=null;
        Tree END_R21_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_END_R=new RewriteRuleTokenStream(adaptor,"token END_R");
        RewriteRuleTokenStream stream_REFINES=new RewriteRuleTokenStream(adaptor,"token REFINES");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
        RewriteRuleTokenStream stream_START_R=new RewriteRuleTokenStream(adaptor,"token START_R");
        RewriteRuleTokenStream stream_CONCEPT=new RewriteRuleTokenStream(adaptor,"token CONCEPT");
        RewriteRuleSubtreeStream stream_conceptInterExt=new RewriteRuleSubtreeStream(adaptor,"rule conceptInterExt");
        RewriteRuleSubtreeStream stream_conceptBaseExt=new RewriteRuleSubtreeStream(adaptor,"rule conceptBaseExt");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:94:2: ( ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )? definitions -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? ( conceptInterExt )* definitions ) )
            // Velvet.g:94:4: ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )? definitions
            {
            // Velvet.g:94:4: ( REFINES )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==REFINES) ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // Velvet.g:94:4: REFINES
                    {
                    REFINES12=(Token)match(input,REFINES,FOLLOW_REFINES_in_concept538);  
                    stream_REFINES.add(REFINES12);


                    }
                    break;

            }


            CONCEPT13=(Token)match(input,CONCEPT,FOLLOW_CONCEPT_in_concept541);  
            stream_CONCEPT.add(CONCEPT13);


            ID14=(Token)match(input,ID,FOLLOW_ID_in_concept543);  
            stream_ID.add(ID14);


            // Velvet.g:94:25: ( COLON conceptBaseExt )?
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==COLON) ) {
                alt6=1;
            }
            switch (alt6) {
                case 1 :
                    // Velvet.g:94:26: COLON conceptBaseExt
                    {
                    COLON15=(Token)match(input,COLON,FOLLOW_COLON_in_concept547);  
                    stream_COLON.add(COLON15);


                    pushFollow(FOLLOW_conceptBaseExt_in_concept549);
                    conceptBaseExt16=conceptBaseExt();

                    state._fsp--;

                    stream_conceptBaseExt.add(conceptBaseExt16.getTree());

                    }
                    break;

            }


            // Velvet.g:94:49: ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )?
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==START_R) ) {
                alt8=1;
            }
            switch (alt8) {
                case 1 :
                    // Velvet.g:95:3: START_R conceptInterExt ( COMMA conceptInterExt )* END_R
                    {
                    START_R17=(Token)match(input,START_R,FOLLOW_START_R_in_concept557);  
                    stream_START_R.add(START_R17);


                    pushFollow(FOLLOW_conceptInterExt_in_concept559);
                    conceptInterExt18=conceptInterExt();

                    state._fsp--;

                    stream_conceptInterExt.add(conceptInterExt18.getTree());

                    // Velvet.g:95:27: ( COMMA conceptInterExt )*
                    loop7:
                    do {
                        int alt7=2;
                        int LA7_0 = input.LA(1);

                        if ( (LA7_0==COMMA) ) {
                            alt7=1;
                        }


                        switch (alt7) {
                    	case 1 :
                    	    // Velvet.g:95:28: COMMA conceptInterExt
                    	    {
                    	    COMMA19=(Token)match(input,COMMA,FOLLOW_COMMA_in_concept562);  
                    	    stream_COMMA.add(COMMA19);


                    	    pushFollow(FOLLOW_conceptInterExt_in_concept564);
                    	    conceptInterExt20=conceptInterExt();

                    	    state._fsp--;

                    	    stream_conceptInterExt.add(conceptInterExt20.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop7;
                        }
                    } while (true);


                    END_R21=(Token)match(input,END_R,FOLLOW_END_R_in_concept568);  
                    stream_END_R.add(END_R21);


                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_concept575);
            definitions22=definitions();

            state._fsp--;

            stream_definitions.add(definitions22.getTree());

            // AST REWRITE
            // elements: conceptBaseExt, conceptInterExt, REFINES, CONCEPT, definitions, ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 97:2: -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? ( conceptInterExt )* definitions )
            {
                // Velvet.g:97:5: ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? ( conceptInterExt )* definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CONCEPT.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:97:18: ( REFINES )?
                if ( stream_REFINES.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_REFINES.nextNode()
                    );

                }
                stream_REFINES.reset();

                // Velvet.g:97:27: ( conceptBaseExt )?
                if ( stream_conceptBaseExt.hasNext() ) {
                    adaptor.addChild(root_1, stream_conceptBaseExt.nextTree());

                }
                stream_conceptBaseExt.reset();

                // Velvet.g:97:43: ( conceptInterExt )*
                while ( stream_conceptInterExt.hasNext() ) {
                    adaptor.addChild(root_1, stream_conceptInterExt.nextTree());

                }
                stream_conceptInterExt.reset();

                adaptor.addChild(root_1, stream_definitions.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "concept"


    public static class conceptBaseExt_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "conceptBaseExt"
    // Velvet.g:100:1: conceptBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
    public final VelvetParser.conceptBaseExt_return conceptBaseExt() throws RecognitionException {
        VelvetParser.conceptBaseExt_return retval = new VelvetParser.conceptBaseExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID23=null;
        Token COMMA24=null;
        Token ID25=null;

        Tree ID23_tree=null;
        Tree COMMA24_tree=null;
        Tree ID25_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

        try {
            // Velvet.g:101:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:101:4: ID ( COMMA ID )*
            {
            ID23=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt608);  
            stream_ID.add(ID23);


            // Velvet.g:101:7: ( COMMA ID )*
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( (LA9_0==COMMA) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // Velvet.g:101:8: COMMA ID
            	    {
            	    COMMA24=(Token)match(input,COMMA,FOLLOW_COMMA_in_conceptBaseExt611);  
            	    stream_COMMA.add(COMMA24);


            	    ID25=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt613);  
            	    stream_ID.add(ID25);


            	    }
            	    break;

            	default :
            	    break loop9;
                }
            } while (true);


            // AST REWRITE
            // elements: ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 102:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:102:5: ^( BASEEXT ( ID )+ )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(BASEEXT, "BASEEXT")
                , root_1);

                if ( !(stream_ID.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_ID.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ID.nextNode()
                    );

                }
                stream_ID.reset();

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "conceptBaseExt"


    public static class conceptInterExt_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "conceptInterExt"
    // Velvet.g:105:1: conceptInterExt : ID name -> ^( BASEPARAM ID name ) ;
    public final VelvetParser.conceptInterExt_return conceptInterExt() throws RecognitionException {
        VelvetParser.conceptInterExt_return retval = new VelvetParser.conceptInterExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID26=null;
        VelvetParser.name_return name27 =null;


        Tree ID26_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:106:2: ( ID name -> ^( BASEPARAM ID name ) )
            // Velvet.g:106:4: ID name
            {
            ID26=(Token)match(input,ID,FOLLOW_ID_in_conceptInterExt637);  
            stream_ID.add(ID26);


            pushFollow(FOLLOW_name_in_conceptInterExt639);
            name27=name();

            state._fsp--;

            stream_name.add(name27.getTree());

            // AST REWRITE
            // elements: ID, name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 107:2: -> ^( BASEPARAM ID name )
            {
                // Velvet.g:107:5: ^( BASEPARAM ID name )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(BASEPARAM, "BASEPARAM")
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                adaptor.addChild(root_1, stream_name.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "conceptInterExt"


    public static class cinterface_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "cinterface"
    // Velvet.g:111:1: cinterface : ( REFINES )? CINTERFACE ID ( COLON interfaceBaseExt )? definitions -> ^( CINTERFACE ID ( REFINES )? ( interfaceBaseExt )? definitions ) ;
    public final VelvetParser.cinterface_return cinterface() throws RecognitionException {
        VelvetParser.cinterface_return retval = new VelvetParser.cinterface_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token REFINES28=null;
        Token CINTERFACE29=null;
        Token ID30=null;
        Token COLON31=null;
        VelvetParser.interfaceBaseExt_return interfaceBaseExt32 =null;

        VelvetParser.definitions_return definitions33 =null;


        Tree REFINES28_tree=null;
        Tree CINTERFACE29_tree=null;
        Tree ID30_tree=null;
        Tree COLON31_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_REFINES=new RewriteRuleTokenStream(adaptor,"token REFINES");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_CINTERFACE=new RewriteRuleTokenStream(adaptor,"token CINTERFACE");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        RewriteRuleSubtreeStream stream_interfaceBaseExt=new RewriteRuleSubtreeStream(adaptor,"rule interfaceBaseExt");
        try {
            // Velvet.g:111:12: ( ( REFINES )? CINTERFACE ID ( COLON interfaceBaseExt )? definitions -> ^( CINTERFACE ID ( REFINES )? ( interfaceBaseExt )? definitions ) )
            // Velvet.g:111:14: ( REFINES )? CINTERFACE ID ( COLON interfaceBaseExt )? definitions
            {
            // Velvet.g:111:14: ( REFINES )?
            int alt10=2;
            int LA10_0 = input.LA(1);

            if ( (LA10_0==REFINES) ) {
                alt10=1;
            }
            switch (alt10) {
                case 1 :
                    // Velvet.g:111:14: REFINES
                    {
                    REFINES28=(Token)match(input,REFINES,FOLLOW_REFINES_in_cinterface661);  
                    stream_REFINES.add(REFINES28);


                    }
                    break;

            }


            CINTERFACE29=(Token)match(input,CINTERFACE,FOLLOW_CINTERFACE_in_cinterface664);  
            stream_CINTERFACE.add(CINTERFACE29);


            ID30=(Token)match(input,ID,FOLLOW_ID_in_cinterface666);  
            stream_ID.add(ID30);


            // Velvet.g:111:38: ( COLON interfaceBaseExt )?
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==COLON) ) {
                alt11=1;
            }
            switch (alt11) {
                case 1 :
                    // Velvet.g:111:39: COLON interfaceBaseExt
                    {
                    COLON31=(Token)match(input,COLON,FOLLOW_COLON_in_cinterface670);  
                    stream_COLON.add(COLON31);


                    pushFollow(FOLLOW_interfaceBaseExt_in_cinterface672);
                    interfaceBaseExt32=interfaceBaseExt();

                    state._fsp--;

                    stream_interfaceBaseExt.add(interfaceBaseExt32.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_cinterface676);
            definitions33=definitions();

            state._fsp--;

            stream_definitions.add(definitions33.getTree());

            // AST REWRITE
            // elements: ID, definitions, CINTERFACE, interfaceBaseExt, REFINES
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 112:2: -> ^( CINTERFACE ID ( REFINES )? ( interfaceBaseExt )? definitions )
            {
                // Velvet.g:112:5: ^( CINTERFACE ID ( REFINES )? ( interfaceBaseExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CINTERFACE.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:112:21: ( REFINES )?
                if ( stream_REFINES.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_REFINES.nextNode()
                    );

                }
                stream_REFINES.reset();

                // Velvet.g:112:30: ( interfaceBaseExt )?
                if ( stream_interfaceBaseExt.hasNext() ) {
                    adaptor.addChild(root_1, stream_interfaceBaseExt.nextTree());

                }
                stream_interfaceBaseExt.reset();

                adaptor.addChild(root_1, stream_definitions.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "cinterface"


    public static class interfaceBaseExt_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "interfaceBaseExt"
    // Velvet.g:115:1: interfaceBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
    public final VelvetParser.interfaceBaseExt_return interfaceBaseExt() throws RecognitionException {
        VelvetParser.interfaceBaseExt_return retval = new VelvetParser.interfaceBaseExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID34=null;
        Token COMMA35=null;
        Token ID36=null;

        Tree ID34_tree=null;
        Tree COMMA35_tree=null;
        Tree ID36_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

        try {
            // Velvet.g:116:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:116:4: ID ( COMMA ID )*
            {
            ID34=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt706);  
            stream_ID.add(ID34);


            // Velvet.g:116:7: ( COMMA ID )*
            loop12:
            do {
                int alt12=2;
                int LA12_0 = input.LA(1);

                if ( (LA12_0==COMMA) ) {
                    alt12=1;
                }


                switch (alt12) {
            	case 1 :
            	    // Velvet.g:116:8: COMMA ID
            	    {
            	    COMMA35=(Token)match(input,COMMA,FOLLOW_COMMA_in_interfaceBaseExt709);  
            	    stream_COMMA.add(COMMA35);


            	    ID36=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt711);  
            	    stream_ID.add(ID36);


            	    }
            	    break;

            	default :
            	    break loop12;
                }
            } while (true);


            // AST REWRITE
            // elements: ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 117:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:117:5: ^( BASEEXT ( ID )+ )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(BASEEXT, "BASEEXT")
                , root_1);

                if ( !(stream_ID.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_ID.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ID.nextNode()
                    );

                }
                stream_ID.reset();

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "interfaceBaseExt"


    public static class name_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "name"
    // Velvet.g:120:1: name : ( ID | IDPath );
    public final VelvetParser.name_return name() throws RecognitionException {
        VelvetParser.name_return retval = new VelvetParser.name_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set37=null;

        Tree set37_tree=null;

        try {
            // Velvet.g:120:5: ( ID | IDPath )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set37=(Token)input.LT(1);

            if ( (input.LA(1) >= ID && input.LA(1) <= IDPath) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set37)
                );
                state.errorRecovery=false;
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "name"


    public static class definitions_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "definitions"
    // Velvet.g:124:1: definitions : START_C def END_C -> ^( DEF def ) ;
    public final VelvetParser.definitions_return definitions() throws RecognitionException {
        VelvetParser.definitions_return retval = new VelvetParser.definitions_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C38=null;
        Token END_C40=null;
        VelvetParser.def_return def39 =null;


        Tree START_C38_tree=null;
        Tree END_C40_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_def=new RewriteRuleSubtreeStream(adaptor,"rule def");
        try {
            // Velvet.g:125:2: ( START_C def END_C -> ^( DEF def ) )
            // Velvet.g:125:4: START_C def END_C
            {
            START_C38=(Token)match(input,START_C,FOLLOW_START_C_in_definitions751);  
            stream_START_C.add(START_C38);


            pushFollow(FOLLOW_def_in_definitions753);
            def39=def();

            state._fsp--;

            stream_def.add(def39.getTree());

            END_C40=(Token)match(input,END_C,FOLLOW_END_C_in_definitions755);  
            stream_END_C.add(END_C40);


            // AST REWRITE
            // elements: def
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 126:2: -> ^( DEF def )
            {
                // Velvet.g:126:5: ^( DEF def )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(DEF, "DEF")
                , root_1);

                adaptor.addChild(root_1, stream_def.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "definitions"


    public static class def_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "def"
    // Velvet.g:129:1: def : ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? ;
    public final VelvetParser.def_return def() throws RecognitionException {
        VelvetParser.def_return retval = new VelvetParser.def_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition41 =null;

        VelvetParser.featureGroup_return featureGroup42 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition43 =null;

        VelvetParser.feature_return feature44 =null;

        VelvetParser.feature_return feature45 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition46 =null;



        try {
            // Velvet.g:129:5: ( ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? )
            // Velvet.g:129:7: ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:129:7: ( nonFeatureDefinition )*
            loop13:
            do {
                int alt13=2;
                int LA13_0 = input.LA(1);

                if ( (LA13_0==CONSTRAINT||LA13_0==ID||(LA13_0 >= VAR_BOOL && LA13_0 <= VAR_STRING)) ) {
                    alt13=1;
                }


                switch (alt13) {
            	case 1 :
            	    // Velvet.g:129:7: nonFeatureDefinition
            	    {
            	    pushFollow(FOLLOW_nonFeatureDefinition_in_def774);
            	    nonFeatureDefinition41=nonFeatureDefinition();

            	    state._fsp--;

            	    adaptor.addChild(root_0, nonFeatureDefinition41.getTree());

            	    }
            	    break;

            	default :
            	    break loop13;
                }
            } while (true);


            // Velvet.g:129:29: ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            int alt16=3;
            int LA16_0 = input.LA(1);

            if ( (LA16_0==ONEOF||LA16_0==SOMEOF) ) {
                alt16=1;
            }
            else if ( (LA16_0==ABSTRACT||LA16_0==FEATURE||LA16_0==MANDATORY) ) {
                alt16=2;
            }
            switch (alt16) {
                case 1 :
                    // Velvet.g:130:3: ( featureGroup ( nonFeatureDefinition )* )
                    {
                    // Velvet.g:130:3: ( featureGroup ( nonFeatureDefinition )* )
                    // Velvet.g:130:4: featureGroup ( nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_featureGroup_in_def782);
                    featureGroup42=featureGroup();

                    state._fsp--;

                    adaptor.addChild(root_0, featureGroup42.getTree());

                    // Velvet.g:130:17: ( nonFeatureDefinition )*
                    loop14:
                    do {
                        int alt14=2;
                        int LA14_0 = input.LA(1);

                        if ( (LA14_0==CONSTRAINT||LA14_0==ID||(LA14_0 >= VAR_BOOL && LA14_0 <= VAR_STRING)) ) {
                            alt14=1;
                        }


                        switch (alt14) {
                    	case 1 :
                    	    // Velvet.g:130:17: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def784);
                    	    nonFeatureDefinition43=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition43.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop14;
                        }
                    } while (true);


                    }


                    }
                    break;
                case 2 :
                    // Velvet.g:131:3: ( feature ( feature | nonFeatureDefinition )* )
                    {
                    // Velvet.g:131:3: ( feature ( feature | nonFeatureDefinition )* )
                    // Velvet.g:131:4: feature ( feature | nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_feature_in_def793);
                    feature44=feature();

                    state._fsp--;

                    adaptor.addChild(root_0, feature44.getTree());

                    // Velvet.g:131:12: ( feature | nonFeatureDefinition )*
                    loop15:
                    do {
                        int alt15=3;
                        int LA15_0 = input.LA(1);

                        if ( (LA15_0==ABSTRACT||LA15_0==FEATURE||LA15_0==MANDATORY) ) {
                            alt15=1;
                        }
                        else if ( (LA15_0==CONSTRAINT||LA15_0==ID||(LA15_0 >= VAR_BOOL && LA15_0 <= VAR_STRING)) ) {
                            alt15=2;
                        }


                        switch (alt15) {
                    	case 1 :
                    	    // Velvet.g:131:13: feature
                    	    {
                    	    pushFollow(FOLLOW_feature_in_def796);
                    	    feature45=feature();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, feature45.getTree());

                    	    }
                    	    break;
                    	case 2 :
                    	    // Velvet.g:131:23: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def800);
                    	    nonFeatureDefinition46=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition46.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop15;
                        }
                    } while (true);


                    }


                    }
                    break;

            }


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "def"


    public static class nonFeatureDefinition_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "nonFeatureDefinition"
    // Velvet.g:134:1: nonFeatureDefinition : ( constraint | instance | attribute );
    public final VelvetParser.nonFeatureDefinition_return nonFeatureDefinition() throws RecognitionException {
        VelvetParser.nonFeatureDefinition_return retval = new VelvetParser.nonFeatureDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraint_return constraint47 =null;

        VelvetParser.instance_return instance48 =null;

        VelvetParser.attribute_return attribute49 =null;



        try {
            // Velvet.g:135:2: ( constraint | instance | attribute )
            int alt17=3;
            switch ( input.LA(1) ) {
            case CONSTRAINT:
                {
                alt17=1;
                }
                break;
            case ID:
                {
                alt17=2;
                }
                break;
            case VAR_BOOL:
            case VAR_FLOAT:
            case VAR_INT:
            case VAR_STRING:
                {
                alt17=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 17, 0, input);

                throw nvae;

            }

            switch (alt17) {
                case 1 :
                    // Velvet.g:135:4: constraint
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_constraint_in_nonFeatureDefinition820);
                    constraint47=constraint();

                    state._fsp--;

                    adaptor.addChild(root_0, constraint47.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:136:4: instance
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_instance_in_nonFeatureDefinition826);
                    instance48=instance();

                    state._fsp--;

                    adaptor.addChild(root_0, instance48.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:137:4: attribute
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_attribute_in_nonFeatureDefinition832);
                    attribute49=attribute();

                    state._fsp--;

                    adaptor.addChild(root_0, attribute49.getTree());

                    }
                    break;

            }
            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "nonFeatureDefinition"


    public static class instance_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "instance"
    // Velvet.g:140:1: instance : ID name SEMI -> INSTANCE ID name ;
    public final VelvetParser.instance_return instance() throws RecognitionException {
        VelvetParser.instance_return retval = new VelvetParser.instance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID50=null;
        Token SEMI52=null;
        VelvetParser.name_return name51 =null;


        Tree ID50_tree=null;
        Tree SEMI52_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:140:9: ( ID name SEMI -> INSTANCE ID name )
            // Velvet.g:140:11: ID name SEMI
            {
            ID50=(Token)match(input,ID,FOLLOW_ID_in_instance843);  
            stream_ID.add(ID50);


            pushFollow(FOLLOW_name_in_instance845);
            name51=name();

            state._fsp--;

            stream_name.add(name51.getTree());

            SEMI52=(Token)match(input,SEMI,FOLLOW_SEMI_in_instance847);  
            stream_SEMI.add(SEMI52);


            // AST REWRITE
            // elements: name, ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 141:2: -> INSTANCE ID name
            {
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(INSTANCE, "INSTANCE")
                );

                adaptor.addChild(root_0, 
                stream_ID.nextNode()
                );

                adaptor.addChild(root_0, stream_name.nextTree());

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "instance"


    public static class feature_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "feature"
    // Velvet.g:144:1: feature : ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) ;
    public final VelvetParser.feature_return feature() throws RecognitionException {
        VelvetParser.feature_return retval = new VelvetParser.feature_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token MANDATORY53=null;
        Token ABSTRACT54=null;
        Token ABSTRACT55=null;
        Token MANDATORY56=null;
        Token MANDATORY57=null;
        Token ABSTRACT58=null;
        Token FEATURE59=null;
        Token SEMI62=null;
        VelvetParser.name_return name60 =null;

        VelvetParser.definitions_return definitions61 =null;


        Tree MANDATORY53_tree=null;
        Tree ABSTRACT54_tree=null;
        Tree ABSTRACT55_tree=null;
        Tree MANDATORY56_tree=null;
        Tree MANDATORY57_tree=null;
        Tree ABSTRACT58_tree=null;
        Tree FEATURE59_tree=null;
        Tree SEMI62_tree=null;
        RewriteRuleTokenStream stream_ABSTRACT=new RewriteRuleTokenStream(adaptor,"token ABSTRACT");
        RewriteRuleTokenStream stream_MANDATORY=new RewriteRuleTokenStream(adaptor,"token MANDATORY");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleTokenStream stream_FEATURE=new RewriteRuleTokenStream(adaptor,"token FEATURE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:145:2: ( ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) )
            // Velvet.g:145:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI )
            {
            // Velvet.g:145:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )?
            int alt18=5;
            int LA18_0 = input.LA(1);

            if ( (LA18_0==MANDATORY) ) {
                int LA18_1 = input.LA(2);

                if ( (LA18_1==ABSTRACT) ) {
                    alt18=1;
                }
                else if ( (LA18_1==FEATURE) ) {
                    alt18=3;
                }
            }
            else if ( (LA18_0==ABSTRACT) ) {
                int LA18_2 = input.LA(2);

                if ( (LA18_2==MANDATORY) ) {
                    alt18=2;
                }
                else if ( (LA18_2==FEATURE) ) {
                    alt18=4;
                }
            }
            switch (alt18) {
                case 1 :
                    // Velvet.g:145:5: MANDATORY ABSTRACT
                    {
                    MANDATORY53=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature869);  
                    stream_MANDATORY.add(MANDATORY53);


                    ABSTRACT54=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature871);  
                    stream_ABSTRACT.add(ABSTRACT54);


                    }
                    break;
                case 2 :
                    // Velvet.g:145:26: ABSTRACT MANDATORY
                    {
                    ABSTRACT55=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature875);  
                    stream_ABSTRACT.add(ABSTRACT55);


                    MANDATORY56=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature877);  
                    stream_MANDATORY.add(MANDATORY56);


                    }
                    break;
                case 3 :
                    // Velvet.g:145:47: MANDATORY
                    {
                    MANDATORY57=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature881);  
                    stream_MANDATORY.add(MANDATORY57);


                    }
                    break;
                case 4 :
                    // Velvet.g:145:59: ABSTRACT
                    {
                    ABSTRACT58=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature885);  
                    stream_ABSTRACT.add(ABSTRACT58);


                    }
                    break;

            }


            FEATURE59=(Token)match(input,FEATURE,FOLLOW_FEATURE_in_feature892);  
            stream_FEATURE.add(FEATURE59);


            pushFollow(FOLLOW_name_in_feature894);
            name60=name();

            state._fsp--;

            stream_name.add(name60.getTree());

            // Velvet.g:146:17: ( definitions | SEMI )
            int alt19=2;
            int LA19_0 = input.LA(1);

            if ( (LA19_0==START_C) ) {
                alt19=1;
            }
            else if ( (LA19_0==SEMI) ) {
                alt19=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 19, 0, input);

                throw nvae;

            }
            switch (alt19) {
                case 1 :
                    // Velvet.g:146:18: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_feature897);
                    definitions61=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions61.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:146:32: SEMI
                    {
                    SEMI62=(Token)match(input,SEMI,FOLLOW_SEMI_in_feature901);  
                    stream_SEMI.add(SEMI62);


                    }
                    break;

            }


            // AST REWRITE
            // elements: ABSTRACT, name, definitions, MANDATORY
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 147:2: -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
            {
                // Velvet.g:147:5: ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(FEAT, "FEAT")
                , root_1);

                adaptor.addChild(root_1, stream_name.nextTree());

                // Velvet.g:147:17: ( MANDATORY )?
                if ( stream_MANDATORY.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_MANDATORY.nextNode()
                    );

                }
                stream_MANDATORY.reset();

                // Velvet.g:147:28: ( ABSTRACT )?
                if ( stream_ABSTRACT.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ABSTRACT.nextNode()
                    );

                }
                stream_ABSTRACT.reset();

                // Velvet.g:147:38: ( definitions )?
                if ( stream_definitions.hasNext() ) {
                    adaptor.addChild(root_1, stream_definitions.nextTree());

                }
                stream_definitions.reset();

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "feature"


    public static class featureGroup_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "featureGroup"
    // Velvet.g:150:1: featureGroup : groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) ;
    public final VelvetParser.featureGroup_return featureGroup() throws RecognitionException {
        VelvetParser.featureGroup_return retval = new VelvetParser.featureGroup_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C64=null;
        Token END_C67=null;
        VelvetParser.groupType_return groupType63 =null;

        VelvetParser.feature_return feature65 =null;

        VelvetParser.feature_return feature66 =null;


        Tree START_C64_tree=null;
        Tree END_C67_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_groupType=new RewriteRuleSubtreeStream(adaptor,"rule groupType");
        RewriteRuleSubtreeStream stream_feature=new RewriteRuleSubtreeStream(adaptor,"rule feature");
        try {
            // Velvet.g:151:2: ( groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) )
            // Velvet.g:151:4: groupType START_C feature ( feature )+ END_C
            {
            pushFollow(FOLLOW_groupType_in_featureGroup932);
            groupType63=groupType();

            state._fsp--;

            stream_groupType.add(groupType63.getTree());

            START_C64=(Token)match(input,START_C,FOLLOW_START_C_in_featureGroup934);  
            stream_START_C.add(START_C64);


            pushFollow(FOLLOW_feature_in_featureGroup936);
            feature65=feature();

            state._fsp--;

            stream_feature.add(feature65.getTree());

            // Velvet.g:151:30: ( feature )+
            int cnt20=0;
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( (LA20_0==ABSTRACT||LA20_0==FEATURE||LA20_0==MANDATORY) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // Velvet.g:151:30: feature
            	    {
            	    pushFollow(FOLLOW_feature_in_featureGroup938);
            	    feature66=feature();

            	    state._fsp--;

            	    stream_feature.add(feature66.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt20 >= 1 ) break loop20;
                        EarlyExitException eee =
                            new EarlyExitException(20, input);
                        throw eee;
                }
                cnt20++;
            } while (true);


            END_C67=(Token)match(input,END_C,FOLLOW_END_C_in_featureGroup941);  
            stream_END_C.add(END_C67);


            // AST REWRITE
            // elements: feature, feature, groupType
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 152:2: -> ^( GROUP groupType feature ( feature )+ )
            {
                // Velvet.g:152:5: ^( GROUP groupType feature ( feature )+ )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(GROUP, "GROUP")
                , root_1);

                adaptor.addChild(root_1, stream_groupType.nextTree());

                adaptor.addChild(root_1, stream_feature.nextTree());

                if ( !(stream_feature.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_feature.hasNext() ) {
                    adaptor.addChild(root_1, stream_feature.nextTree());

                }
                stream_feature.reset();

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "featureGroup"


    public static class groupType_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "groupType"
    // Velvet.g:155:1: groupType : ( SOMEOF | ONEOF );
    public final VelvetParser.groupType_return groupType() throws RecognitionException {
        VelvetParser.groupType_return retval = new VelvetParser.groupType_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set68=null;

        Tree set68_tree=null;

        try {
            // Velvet.g:156:2: ( SOMEOF | ONEOF )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set68=(Token)input.LT(1);

            if ( input.LA(1)==ONEOF||input.LA(1)==SOMEOF ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set68)
                );
                state.errorRecovery=false;
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "groupType"


    public static class constraint_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "constraint"
    // Velvet.g:160:1: constraint : CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !;
    public final VelvetParser.constraint_return constraint() throws RecognitionException {
        VelvetParser.constraint_return retval = new VelvetParser.constraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token CONSTRAINT69=null;
        Token ID70=null;
        Token EQ71=null;
        Token SEMI74=null;
        VelvetParser.constraintDefinition_return constraintDefinition72 =null;

        VelvetParser.attributeConstraint_return attributeConstraint73 =null;


        Tree CONSTRAINT69_tree=null;
        Tree ID70_tree=null;
        Tree EQ71_tree=null;
        Tree SEMI74_tree=null;

        try {
            // Velvet.g:161:2: ( CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !)
            // Velvet.g:161:4: CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !
            {
            root_0 = (Tree)adaptor.nil();


            CONSTRAINT69=(Token)match(input,CONSTRAINT,FOLLOW_CONSTRAINT_in_constraint984); 
            CONSTRAINT69_tree = 
            (Tree)adaptor.create(CONSTRAINT69)
            ;
            root_0 = (Tree)adaptor.becomeRoot(CONSTRAINT69_tree, root_0);


            // Velvet.g:161:16: ( ID EQ !)?
            int alt21=2;
            int LA21_0 = input.LA(1);

            if ( (LA21_0==ID) ) {
                int LA21_1 = input.LA(2);

                if ( (LA21_1==EQ) ) {
                    alt21=1;
                }
            }
            switch (alt21) {
                case 1 :
                    // Velvet.g:161:17: ID EQ !
                    {
                    ID70=(Token)match(input,ID,FOLLOW_ID_in_constraint988); 
                    ID70_tree = 
                    (Tree)adaptor.create(ID70)
                    ;
                    adaptor.addChild(root_0, ID70_tree);


                    EQ71=(Token)match(input,EQ,FOLLOW_EQ_in_constraint990); 

                    }
                    break;

            }


            // Velvet.g:161:26: ( constraintDefinition | attributeConstraint )
            int alt22=2;
            switch ( input.LA(1) ) {
            case OP_NOT:
            case START_R:
                {
                alt22=1;
                }
                break;
            case ID:
            case IDPath:
                {
                int LA22_2 = input.LA(2);

                if ( ((LA22_2 >= OP_AND && LA22_2 <= OP_IMPLIES)||(LA22_2 >= OP_OR && LA22_2 <= OP_XOR)||LA22_2==SEMI) ) {
                    alt22=1;
                }
                else if ( (LA22_2==ATTR_OP_EQUALS||LA22_2==ATTR_OP_GREATER_EQ||LA22_2==ATTR_OP_LESS_EQ||LA22_2==MINUS||LA22_2==PLUS) ) {
                    alt22=2;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 22, 2, input);

                    throw nvae;

                }
                }
                break;
            case INT:
                {
                alt22=2;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 22, 0, input);

                throw nvae;

            }

            switch (alt22) {
                case 1 :
                    // Velvet.g:161:27: constraintDefinition
                    {
                    pushFollow(FOLLOW_constraintDefinition_in_constraint996);
                    constraintDefinition72=constraintDefinition();

                    state._fsp--;

                    adaptor.addChild(root_0, constraintDefinition72.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:161:50: attributeConstraint
                    {
                    pushFollow(FOLLOW_attributeConstraint_in_constraint1000);
                    attributeConstraint73=attributeConstraint();

                    state._fsp--;

                    adaptor.addChild(root_0, attributeConstraint73.getTree());

                    }
                    break;

            }


            SEMI74=(Token)match(input,SEMI,FOLLOW_SEMI_in_constraint1003); 

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "constraint"


    public static class constraintDefinition_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "constraintDefinition"
    // Velvet.g:164:1: constraintDefinition : constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) ;
    public final VelvetParser.constraintDefinition_return constraintDefinition() throws RecognitionException {
        VelvetParser.constraintDefinition_return retval = new VelvetParser.constraintDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraintOperand_return constraintOperand75 =null;

        VelvetParser.binaryOp_return binaryOp76 =null;

        VelvetParser.constraintOperand_return constraintOperand77 =null;


        RewriteRuleSubtreeStream stream_constraintOperand=new RewriteRuleSubtreeStream(adaptor,"rule constraintOperand");
        RewriteRuleSubtreeStream stream_binaryOp=new RewriteRuleSubtreeStream(adaptor,"rule binaryOp");
        try {
            // Velvet.g:165:2: ( constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) )
            // Velvet.g:165:4: constraintOperand ( binaryOp constraintOperand )*
            {
            pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1016);
            constraintOperand75=constraintOperand();

            state._fsp--;

            stream_constraintOperand.add(constraintOperand75.getTree());

            // Velvet.g:165:22: ( binaryOp constraintOperand )*
            loop23:
            do {
                int alt23=2;
                int LA23_0 = input.LA(1);

                if ( ((LA23_0 >= OP_AND && LA23_0 <= OP_IMPLIES)||(LA23_0 >= OP_OR && LA23_0 <= OP_XOR)) ) {
                    alt23=1;
                }


                switch (alt23) {
            	case 1 :
            	    // Velvet.g:165:23: binaryOp constraintOperand
            	    {
            	    pushFollow(FOLLOW_binaryOp_in_constraintDefinition1019);
            	    binaryOp76=binaryOp();

            	    state._fsp--;

            	    stream_binaryOp.add(binaryOp76.getTree());

            	    pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1021);
            	    constraintOperand77=constraintOperand();

            	    state._fsp--;

            	    stream_constraintOperand.add(constraintOperand77.getTree());

            	    }
            	    break;

            	default :
            	    break loop23;
                }
            } while (true);


            // AST REWRITE
            // elements: binaryOp, constraintOperand
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 166:2: -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
            {
                // Velvet.g:166:5: ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(CONSTR, "CONSTR")
                , root_1);

                if ( !(stream_constraintOperand.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_constraintOperand.hasNext() ) {
                    adaptor.addChild(root_1, stream_constraintOperand.nextTree());

                }
                stream_constraintOperand.reset();

                // Velvet.g:166:33: ( binaryOp )*
                while ( stream_binaryOp.hasNext() ) {
                    adaptor.addChild(root_1, stream_binaryOp.nextTree());

                }
                stream_binaryOp.reset();

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "constraintDefinition"


    public static class constraintOperand_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "constraintOperand"
    // Velvet.g:169:1: constraintOperand : ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? ;
    public final VelvetParser.constraintOperand_return constraintOperand() throws RecognitionException {
        VelvetParser.constraintOperand_return retval = new VelvetParser.constraintOperand_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_R79=null;
        Token END_R81=null;
        VelvetParser.unaryOp_return unaryOp78 =null;

        VelvetParser.constraintDefinition_return constraintDefinition80 =null;

        VelvetParser.name_return name82 =null;


        Tree START_R79_tree=null;
        Tree END_R81_tree=null;
        RewriteRuleTokenStream stream_END_R=new RewriteRuleTokenStream(adaptor,"token END_R");
        RewriteRuleTokenStream stream_START_R=new RewriteRuleTokenStream(adaptor,"token START_R");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_unaryOp=new RewriteRuleSubtreeStream(adaptor,"rule unaryOp");
        RewriteRuleSubtreeStream stream_constraintDefinition=new RewriteRuleSubtreeStream(adaptor,"rule constraintDefinition");
        try {
            // Velvet.g:169:19: ( ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? )
            // Velvet.g:169:21: ( unaryOp )* ( START_R constraintDefinition END_R | name )
            {
            // Velvet.g:169:21: ( unaryOp )*
            loop24:
            do {
                int alt24=2;
                int LA24_0 = input.LA(1);

                if ( (LA24_0==OP_NOT) ) {
                    alt24=1;
                }


                switch (alt24) {
            	case 1 :
            	    // Velvet.g:169:21: unaryOp
            	    {
            	    pushFollow(FOLLOW_unaryOp_in_constraintOperand1048);
            	    unaryOp78=unaryOp();

            	    state._fsp--;

            	    stream_unaryOp.add(unaryOp78.getTree());

            	    }
            	    break;

            	default :
            	    break loop24;
                }
            } while (true);


            // Velvet.g:169:30: ( START_R constraintDefinition END_R | name )
            int alt25=2;
            int LA25_0 = input.LA(1);

            if ( (LA25_0==START_R) ) {
                alt25=1;
            }
            else if ( ((LA25_0 >= ID && LA25_0 <= IDPath)) ) {
                alt25=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 25, 0, input);

                throw nvae;

            }
            switch (alt25) {
                case 1 :
                    // Velvet.g:169:31: START_R constraintDefinition END_R
                    {
                    START_R79=(Token)match(input,START_R,FOLLOW_START_R_in_constraintOperand1052);  
                    stream_START_R.add(START_R79);


                    pushFollow(FOLLOW_constraintDefinition_in_constraintOperand1054);
                    constraintDefinition80=constraintDefinition();

                    state._fsp--;

                    stream_constraintDefinition.add(constraintDefinition80.getTree());

                    END_R81=(Token)match(input,END_R,FOLLOW_END_R_in_constraintOperand1056);  
                    stream_END_R.add(END_R81);


                    }
                    break;
                case 2 :
                    // Velvet.g:169:68: name
                    {
                    pushFollow(FOLLOW_name_in_constraintOperand1060);
                    name82=name();

                    state._fsp--;

                    stream_name.add(name82.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: name, constraintDefinition, unaryOp
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 170:2: -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )?
            {
                // Velvet.g:170:5: ( constraintDefinition )?
                if ( stream_constraintDefinition.hasNext() ) {
                    adaptor.addChild(root_0, stream_constraintDefinition.nextTree());

                }
                stream_constraintDefinition.reset();

                // Velvet.g:170:27: ( ^( UNARYOP unaryOp ) )*
                while ( stream_unaryOp.hasNext() ) {
                    // Velvet.g:170:27: ^( UNARYOP unaryOp )
                    {
                    Tree root_1 = (Tree)adaptor.nil();
                    root_1 = (Tree)adaptor.becomeRoot(
                    (Tree)adaptor.create(UNARYOP, "UNARYOP")
                    , root_1);

                    adaptor.addChild(root_1, stream_unaryOp.nextTree());

                    adaptor.addChild(root_0, root_1);
                    }

                }
                stream_unaryOp.reset();

                // Velvet.g:170:47: ( ^( OPERAND name ) )?
                if ( stream_name.hasNext() ) {
                    // Velvet.g:170:47: ^( OPERAND name )
                    {
                    Tree root_1 = (Tree)adaptor.nil();
                    root_1 = (Tree)adaptor.becomeRoot(
                    (Tree)adaptor.create(OPERAND, "OPERAND")
                    , root_1);

                    adaptor.addChild(root_1, stream_name.nextTree());

                    adaptor.addChild(root_0, root_1);
                    }

                }
                stream_name.reset();

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "constraintOperand"


    public static class attributeConstraint_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "attributeConstraint"
    // Velvet.g:173:1: attributeConstraint : attribConstraint -> ^( ACONSTR attribConstraint ) ;
    public final VelvetParser.attributeConstraint_return attributeConstraint() throws RecognitionException {
        VelvetParser.attributeConstraint_return retval = new VelvetParser.attributeConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribConstraint_return attribConstraint83 =null;


        RewriteRuleSubtreeStream stream_attribConstraint=new RewriteRuleSubtreeStream(adaptor,"rule attribConstraint");
        try {
            // Velvet.g:174:2: ( attribConstraint -> ^( ACONSTR attribConstraint ) )
            // Velvet.g:174:4: attribConstraint
            {
            pushFollow(FOLLOW_attribConstraint_in_attributeConstraint1095);
            attribConstraint83=attribConstraint();

            state._fsp--;

            stream_attribConstraint.add(attribConstraint83.getTree());

            // AST REWRITE
            // elements: attribConstraint
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 175:2: -> ^( ACONSTR attribConstraint )
            {
                // Velvet.g:175:5: ^( ACONSTR attribConstraint )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(ACONSTR, "ACONSTR")
                , root_1);

                adaptor.addChild(root_1, stream_attribConstraint.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "attributeConstraint"


    public static class attribConstraint_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "attribConstraint"
    // Velvet.g:178:1: attribConstraint : attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* ;
    public final VelvetParser.attribConstraint_return attribConstraint() throws RecognitionException {
        VelvetParser.attribConstraint_return retval = new VelvetParser.attribConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribNumInstance_return attribNumInstance84 =null;

        VelvetParser.attribOperator_return attribOperator85 =null;

        VelvetParser.attribNumInstance_return attribNumInstance86 =null;

        VelvetParser.attribRelation_return attribRelation87 =null;

        VelvetParser.attribNumInstance_return attribNumInstance88 =null;

        VelvetParser.attribOperator_return attribOperator89 =null;

        VelvetParser.attribNumInstance_return attribNumInstance90 =null;



        try {
            // Velvet.g:179:2: ( attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* )
            // Velvet.g:179:4: attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )*
            {
            root_0 = (Tree)adaptor.nil();


            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1115);
            attribNumInstance84=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance84.getTree());

            // Velvet.g:179:22: ( attribOperator attribNumInstance )*
            loop26:
            do {
                int alt26=2;
                int LA26_0 = input.LA(1);

                if ( (LA26_0==MINUS||LA26_0==PLUS) ) {
                    alt26=1;
                }


                switch (alt26) {
            	case 1 :
            	    // Velvet.g:179:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1118);
            	    attribOperator85=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator85.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1120);
            	    attribNumInstance86=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance86.getTree());

            	    }
            	    break;

            	default :
            	    break loop26;
                }
            } while (true);


            pushFollow(FOLLOW_attribRelation_in_attribConstraint1128);
            attribRelation87=attribRelation();

            state._fsp--;

            adaptor.addChild(root_0, attribRelation87.getTree());

            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1134);
            attribNumInstance88=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance88.getTree());

            // Velvet.g:181:22: ( attribOperator attribNumInstance )*
            loop27:
            do {
                int alt27=2;
                int LA27_0 = input.LA(1);

                if ( (LA27_0==MINUS||LA27_0==PLUS) ) {
                    alt27=1;
                }


                switch (alt27) {
            	case 1 :
            	    // Velvet.g:181:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1137);
            	    attribOperator89=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator89.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1139);
            	    attribNumInstance90=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance90.getTree());

            	    }
            	    break;

            	default :
            	    break loop27;
                }
            } while (true);


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "attribConstraint"


    public static class attribOperator_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "attribOperator"
    // Velvet.g:184:1: attribOperator : ( PLUS | MINUS );
    public final VelvetParser.attribOperator_return attribOperator() throws RecognitionException {
        VelvetParser.attribOperator_return retval = new VelvetParser.attribOperator_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set91=null;

        Tree set91_tree=null;

        try {
            // Velvet.g:185:2: ( PLUS | MINUS )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set91=(Token)input.LT(1);

            if ( input.LA(1)==MINUS||input.LA(1)==PLUS ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set91)
                );
                state.errorRecovery=false;
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "attribOperator"


    public static class attribNumInstance_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "attribNumInstance"
    // Velvet.g:189:1: attribNumInstance : ( INT | name );
    public final VelvetParser.attribNumInstance_return attribNumInstance() throws RecognitionException {
        VelvetParser.attribNumInstance_return retval = new VelvetParser.attribNumInstance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token INT92=null;
        VelvetParser.name_return name93 =null;


        Tree INT92_tree=null;

        try {
            // Velvet.g:190:2: ( INT | name )
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==INT) ) {
                alt28=1;
            }
            else if ( ((LA28_0 >= ID && LA28_0 <= IDPath)) ) {
                alt28=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 28, 0, input);

                throw nvae;

            }
            switch (alt28) {
                case 1 :
                    // Velvet.g:190:4: INT
                    {
                    root_0 = (Tree)adaptor.nil();


                    INT92=(Token)match(input,INT,FOLLOW_INT_in_attribNumInstance1171); 
                    INT92_tree = 
                    (Tree)adaptor.create(INT92)
                    ;
                    adaptor.addChild(root_0, INT92_tree);


                    }
                    break;
                case 2 :
                    // Velvet.g:192:4: name
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_name_in_attribNumInstance1178);
                    name93=name();

                    state._fsp--;

                    adaptor.addChild(root_0, name93.getTree());

                    }
                    break;

            }
            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "attribNumInstance"


    public static class attribute_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "attribute"
    // Velvet.g:195:1: attribute : ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) ;
    public final VelvetParser.attribute_return attribute() throws RecognitionException {
        VelvetParser.attribute_return retval = new VelvetParser.attribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token SEMI98=null;
        VelvetParser.intAttribute_return intAttribute94 =null;

        VelvetParser.floatAttribute_return floatAttribute95 =null;

        VelvetParser.stringAttribute_return stringAttribute96 =null;

        VelvetParser.boolAttribute_return boolAttribute97 =null;


        Tree SEMI98_tree=null;
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_intAttribute=new RewriteRuleSubtreeStream(adaptor,"rule intAttribute");
        RewriteRuleSubtreeStream stream_stringAttribute=new RewriteRuleSubtreeStream(adaptor,"rule stringAttribute");
        RewriteRuleSubtreeStream stream_floatAttribute=new RewriteRuleSubtreeStream(adaptor,"rule floatAttribute");
        RewriteRuleSubtreeStream stream_boolAttribute=new RewriteRuleSubtreeStream(adaptor,"rule boolAttribute");
        try {
            // Velvet.g:196:2: ( ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) )
            // Velvet.g:196:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI
            {
            // Velvet.g:196:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute )
            int alt29=4;
            switch ( input.LA(1) ) {
            case VAR_INT:
                {
                alt29=1;
                }
                break;
            case VAR_FLOAT:
                {
                alt29=2;
                }
                break;
            case VAR_STRING:
                {
                alt29=3;
                }
                break;
            case VAR_BOOL:
                {
                alt29=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 29, 0, input);

                throw nvae;

            }

            switch (alt29) {
                case 1 :
                    // Velvet.g:196:5: intAttribute
                    {
                    pushFollow(FOLLOW_intAttribute_in_attribute1190);
                    intAttribute94=intAttribute();

                    state._fsp--;

                    stream_intAttribute.add(intAttribute94.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:196:20: floatAttribute
                    {
                    pushFollow(FOLLOW_floatAttribute_in_attribute1194);
                    floatAttribute95=floatAttribute();

                    state._fsp--;

                    stream_floatAttribute.add(floatAttribute95.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:196:37: stringAttribute
                    {
                    pushFollow(FOLLOW_stringAttribute_in_attribute1198);
                    stringAttribute96=stringAttribute();

                    state._fsp--;

                    stream_stringAttribute.add(stringAttribute96.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:196:55: boolAttribute
                    {
                    pushFollow(FOLLOW_boolAttribute_in_attribute1202);
                    boolAttribute97=boolAttribute();

                    state._fsp--;

                    stream_boolAttribute.add(boolAttribute97.getTree());

                    }
                    break;

            }


            SEMI98=(Token)match(input,SEMI,FOLLOW_SEMI_in_attribute1205);  
            stream_SEMI.add(SEMI98);


            // AST REWRITE
            // elements: floatAttribute, boolAttribute, stringAttribute, intAttribute
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 197:2: -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
            {
                // Velvet.g:197:5: ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(ATTR, "ATTR")
                , root_1);

                // Velvet.g:197:12: ( intAttribute )?
                if ( stream_intAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_intAttribute.nextTree());

                }
                stream_intAttribute.reset();

                // Velvet.g:197:26: ( floatAttribute )?
                if ( stream_floatAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_floatAttribute.nextTree());

                }
                stream_floatAttribute.reset();

                // Velvet.g:197:42: ( stringAttribute )?
                if ( stream_stringAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_stringAttribute.nextTree());

                }
                stream_stringAttribute.reset();

                // Velvet.g:197:59: ( boolAttribute )?
                if ( stream_boolAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_boolAttribute.nextTree());

                }
                stream_boolAttribute.reset();

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "attribute"


    public static class intAttribute_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "intAttribute"
    // Velvet.g:200:1: intAttribute : VAR_INT ! name ( EQ ! INT )? ;
    public final VelvetParser.intAttribute_return intAttribute() throws RecognitionException {
        VelvetParser.intAttribute_return retval = new VelvetParser.intAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_INT99=null;
        Token EQ101=null;
        Token INT102=null;
        VelvetParser.name_return name100 =null;


        Tree VAR_INT99_tree=null;
        Tree EQ101_tree=null;
        Tree INT102_tree=null;

        try {
            // Velvet.g:200:13: ( VAR_INT ! name ( EQ ! INT )? )
            // Velvet.g:200:16: VAR_INT ! name ( EQ ! INT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_INT99=(Token)match(input,VAR_INT,FOLLOW_VAR_INT_in_intAttribute1234); 

            pushFollow(FOLLOW_name_in_intAttribute1237);
            name100=name();

            state._fsp--;

            adaptor.addChild(root_0, name100.getTree());

            // Velvet.g:200:30: ( EQ ! INT )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==EQ) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // Velvet.g:200:31: EQ ! INT
                    {
                    EQ101=(Token)match(input,EQ,FOLLOW_EQ_in_intAttribute1240); 

                    INT102=(Token)match(input,INT,FOLLOW_INT_in_intAttribute1243); 
                    INT102_tree = 
                    (Tree)adaptor.create(INT102)
                    ;
                    adaptor.addChild(root_0, INT102_tree);


                    }
                    break;

            }


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "intAttribute"


    public static class floatAttribute_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "floatAttribute"
    // Velvet.g:201:1: floatAttribute : VAR_FLOAT ! name ( EQ ! FLOAT )? ;
    public final VelvetParser.floatAttribute_return floatAttribute() throws RecognitionException {
        VelvetParser.floatAttribute_return retval = new VelvetParser.floatAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_FLOAT103=null;
        Token EQ105=null;
        Token FLOAT106=null;
        VelvetParser.name_return name104 =null;


        Tree VAR_FLOAT103_tree=null;
        Tree EQ105_tree=null;
        Tree FLOAT106_tree=null;

        try {
            // Velvet.g:201:15: ( VAR_FLOAT ! name ( EQ ! FLOAT )? )
            // Velvet.g:201:18: VAR_FLOAT ! name ( EQ ! FLOAT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_FLOAT103=(Token)match(input,VAR_FLOAT,FOLLOW_VAR_FLOAT_in_floatAttribute1252); 

            pushFollow(FOLLOW_name_in_floatAttribute1255);
            name104=name();

            state._fsp--;

            adaptor.addChild(root_0, name104.getTree());

            // Velvet.g:201:34: ( EQ ! FLOAT )?
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( (LA31_0==EQ) ) {
                alt31=1;
            }
            switch (alt31) {
                case 1 :
                    // Velvet.g:201:35: EQ ! FLOAT
                    {
                    EQ105=(Token)match(input,EQ,FOLLOW_EQ_in_floatAttribute1258); 

                    FLOAT106=(Token)match(input,FLOAT,FOLLOW_FLOAT_in_floatAttribute1261); 
                    FLOAT106_tree = 
                    (Tree)adaptor.create(FLOAT106)
                    ;
                    adaptor.addChild(root_0, FLOAT106_tree);


                    }
                    break;

            }


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "floatAttribute"


    public static class stringAttribute_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "stringAttribute"
    // Velvet.g:202:1: stringAttribute : VAR_STRING ! name ( EQ ! STRING )? ;
    public final VelvetParser.stringAttribute_return stringAttribute() throws RecognitionException {
        VelvetParser.stringAttribute_return retval = new VelvetParser.stringAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_STRING107=null;
        Token EQ109=null;
        Token STRING110=null;
        VelvetParser.name_return name108 =null;


        Tree VAR_STRING107_tree=null;
        Tree EQ109_tree=null;
        Tree STRING110_tree=null;

        try {
            // Velvet.g:202:16: ( VAR_STRING ! name ( EQ ! STRING )? )
            // Velvet.g:202:18: VAR_STRING ! name ( EQ ! STRING )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_STRING107=(Token)match(input,VAR_STRING,FOLLOW_VAR_STRING_in_stringAttribute1269); 

            pushFollow(FOLLOW_name_in_stringAttribute1272);
            name108=name();

            state._fsp--;

            adaptor.addChild(root_0, name108.getTree());

            // Velvet.g:202:35: ( EQ ! STRING )?
            int alt32=2;
            int LA32_0 = input.LA(1);

            if ( (LA32_0==EQ) ) {
                alt32=1;
            }
            switch (alt32) {
                case 1 :
                    // Velvet.g:202:36: EQ ! STRING
                    {
                    EQ109=(Token)match(input,EQ,FOLLOW_EQ_in_stringAttribute1275); 

                    STRING110=(Token)match(input,STRING,FOLLOW_STRING_in_stringAttribute1278); 
                    STRING110_tree = 
                    (Tree)adaptor.create(STRING110)
                    ;
                    adaptor.addChild(root_0, STRING110_tree);


                    }
                    break;

            }


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "stringAttribute"


    public static class boolAttribute_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "boolAttribute"
    // Velvet.g:203:1: boolAttribute : VAR_BOOL ! name ( EQ ! BOOLEAN )? ;
    public final VelvetParser.boolAttribute_return boolAttribute() throws RecognitionException {
        VelvetParser.boolAttribute_return retval = new VelvetParser.boolAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_BOOL111=null;
        Token EQ113=null;
        Token BOOLEAN114=null;
        VelvetParser.name_return name112 =null;


        Tree VAR_BOOL111_tree=null;
        Tree EQ113_tree=null;
        Tree BOOLEAN114_tree=null;

        try {
            // Velvet.g:203:14: ( VAR_BOOL ! name ( EQ ! BOOLEAN )? )
            // Velvet.g:203:17: VAR_BOOL ! name ( EQ ! BOOLEAN )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_BOOL111=(Token)match(input,VAR_BOOL,FOLLOW_VAR_BOOL_in_boolAttribute1287); 

            pushFollow(FOLLOW_name_in_boolAttribute1290);
            name112=name();

            state._fsp--;

            adaptor.addChild(root_0, name112.getTree());

            // Velvet.g:203:32: ( EQ ! BOOLEAN )?
            int alt33=2;
            int LA33_0 = input.LA(1);

            if ( (LA33_0==EQ) ) {
                alt33=1;
            }
            switch (alt33) {
                case 1 :
                    // Velvet.g:203:33: EQ ! BOOLEAN
                    {
                    EQ113=(Token)match(input,EQ,FOLLOW_EQ_in_boolAttribute1293); 

                    BOOLEAN114=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_boolAttribute1296); 
                    BOOLEAN114_tree = 
                    (Tree)adaptor.create(BOOLEAN114)
                    ;
                    adaptor.addChild(root_0, BOOLEAN114_tree);


                    }
                    break;

            }


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "boolAttribute"


    public static class unaryOp_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "unaryOp"
    // Velvet.g:205:1: unaryOp : OP_NOT ;
    public final VelvetParser.unaryOp_return unaryOp() throws RecognitionException {
        VelvetParser.unaryOp_return retval = new VelvetParser.unaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token OP_NOT115=null;

        Tree OP_NOT115_tree=null;

        try {
            // Velvet.g:206:2: ( OP_NOT )
            // Velvet.g:206:4: OP_NOT
            {
            root_0 = (Tree)adaptor.nil();


            OP_NOT115=(Token)match(input,OP_NOT,FOLLOW_OP_NOT_in_unaryOp1308); 
            OP_NOT115_tree = 
            (Tree)adaptor.create(OP_NOT115)
            ;
            adaptor.addChild(root_0, OP_NOT115_tree);


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "unaryOp"


    public static class binaryOp_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "binaryOp"
    // Velvet.g:209:1: binaryOp : ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT );
    public final VelvetParser.binaryOp_return binaryOp() throws RecognitionException {
        VelvetParser.binaryOp_return retval = new VelvetParser.binaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set116=null;

        Tree set116_tree=null;

        try {
            // Velvet.g:210:2: ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set116=(Token)input.LT(1);

            if ( (input.LA(1) >= OP_AND && input.LA(1) <= OP_IMPLIES)||(input.LA(1) >= OP_OR && input.LA(1) <= OP_XOR) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set116)
                );
                state.errorRecovery=false;
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "binaryOp"


    public static class attribRelation_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "attribRelation"
    // Velvet.g:217:1: attribRelation : ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ );
    public final VelvetParser.attribRelation_return attribRelation() throws RecognitionException {
        VelvetParser.attribRelation_return retval = new VelvetParser.attribRelation_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set117=null;

        Tree set117_tree=null;

        try {
            // Velvet.g:218:2: ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set117=(Token)input.LT(1);

            if ( input.LA(1)==ATTR_OP_EQUALS||input.LA(1)==ATTR_OP_GREATER_EQ||input.LA(1)==ATTR_OP_LESS_EQ ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set117)
                );
                state.errorRecovery=false;
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }


            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Tree)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "attribRelation"

    // Delegated rules


 

    public static final BitSet FOLLOW_imports_in_velvetModel459 = new BitSet(new long[]{0x0020000200090000L});
    public static final BitSet FOLLOW_instancedef_in_velvetModel462 = new BitSet(new long[]{0x0020000200090000L});
    public static final BitSet FOLLOW_concept_in_velvetModel466 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_cinterface_in_velvetModel468 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_velvetModel471 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_instancedef483 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_instancedef485 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_SEMI_in_instancedef487 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IMPORT_in_imports509 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_imports511 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_SEMI_in_imports513 = new BitSet(new long[]{0x0000001000000002L});
    public static final BitSet FOLLOW_REFINES_in_concept538 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_CONCEPT_in_concept541 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_concept543 = new BitSet(new long[]{0x0300000000020000L});
    public static final BitSet FOLLOW_COLON_in_concept547 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_conceptBaseExt_in_concept549 = new BitSet(new long[]{0x0300000000000000L});
    public static final BitSet FOLLOW_START_R_in_concept557 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_conceptInterExt_in_concept559 = new BitSet(new long[]{0x0000000001040000L});
    public static final BitSet FOLLOW_COMMA_in_concept562 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_conceptInterExt_in_concept564 = new BitSet(new long[]{0x0000000001040000L});
    public static final BitSet FOLLOW_END_R_in_concept568 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_definitions_in_concept575 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt608 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_COMMA_in_conceptBaseExt611 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt613 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_ID_in_conceptInterExt637 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_conceptInterExt639 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_REFINES_in_cinterface661 = new BitSet(new long[]{0x0000000000010000L});
    public static final BitSet FOLLOW_CINTERFACE_in_cinterface664 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_cinterface666 = new BitSet(new long[]{0x0100000000020000L});
    public static final BitSet FOLLOW_COLON_in_cinterface670 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_interfaceBaseExt_in_cinterface672 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_definitions_in_cinterface676 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt706 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_COMMA_in_interfaceBaseExt709 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt711 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_START_C_in_definitions751 = new BitSet(new long[]{0xE080120220A00010L,0x0000000000000001L});
    public static final BitSet FOLLOW_def_in_definitions753 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_END_C_in_definitions755 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def774 = new BitSet(new long[]{0xE080120220200012L,0x0000000000000001L});
    public static final BitSet FOLLOW_featureGroup_in_def782 = new BitSet(new long[]{0xE000000200200002L,0x0000000000000001L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def784 = new BitSet(new long[]{0xE000000200200002L,0x0000000000000001L});
    public static final BitSet FOLLOW_feature_in_def793 = new BitSet(new long[]{0xE000020220200012L,0x0000000000000001L});
    public static final BitSet FOLLOW_feature_in_def796 = new BitSet(new long[]{0xE000020220200012L,0x0000000000000001L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def800 = new BitSet(new long[]{0xE000020220200012L,0x0000000000000001L});
    public static final BitSet FOLLOW_constraint_in_nonFeatureDefinition820 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_instance_in_nonFeatureDefinition826 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribute_in_nonFeatureDefinition832 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_instance843 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_instance845 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_SEMI_in_instance847 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANDATORY_in_feature869 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature871 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature875 = new BitSet(new long[]{0x0000020000000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature877 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature881 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature885 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_FEATURE_in_feature892 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_feature894 = new BitSet(new long[]{0x0140000000000000L});
    public static final BitSet FOLLOW_definitions_in_feature897 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SEMI_in_feature901 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_groupType_in_featureGroup932 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_START_C_in_featureGroup934 = new BitSet(new long[]{0x0000020020000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup936 = new BitSet(new long[]{0x0000020020000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup938 = new BitSet(new long[]{0x0000020020800010L});
    public static final BitSet FOLLOW_END_C_in_featureGroup941 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONSTRAINT_in_constraint984 = new BitSet(new long[]{0x0202008600000000L});
    public static final BitSet FOLLOW_ID_in_constraint988 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_EQ_in_constraint990 = new BitSet(new long[]{0x0202008600000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraint996 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_attributeConstraint_in_constraint1000 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_SEMI_in_constraint1003 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1016 = new BitSet(new long[]{0x000DC00000000002L});
    public static final BitSet FOLLOW_binaryOp_in_constraintDefinition1019 = new BitSet(new long[]{0x0202000600000000L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1021 = new BitSet(new long[]{0x000DC00000000002L});
    public static final BitSet FOLLOW_unaryOp_in_constraintOperand1048 = new BitSet(new long[]{0x0202000600000000L});
    public static final BitSet FOLLOW_START_R_in_constraintOperand1052 = new BitSet(new long[]{0x0202000600000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraintOperand1054 = new BitSet(new long[]{0x0000000001000000L});
    public static final BitSet FOLLOW_END_R_in_constraintOperand1056 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_constraintOperand1060 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribConstraint_in_attributeConstraint1095 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1115 = new BitSet(new long[]{0x0010040000000A80L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1118 = new BitSet(new long[]{0x0000008600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1120 = new BitSet(new long[]{0x0010040000000A80L});
    public static final BitSet FOLLOW_attribRelation_in_attribConstraint1128 = new BitSet(new long[]{0x0000008600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1134 = new BitSet(new long[]{0x0010040000000002L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1137 = new BitSet(new long[]{0x0000008600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1139 = new BitSet(new long[]{0x0010040000000002L});
    public static final BitSet FOLLOW_INT_in_attribNumInstance1171 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_attribNumInstance1178 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_intAttribute_in_attribute1190 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_floatAttribute_in_attribute1194 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_stringAttribute_in_attribute1198 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_boolAttribute_in_attribute1202 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_SEMI_in_attribute1205 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_INT_in_intAttribute1234 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_intAttribute1237 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_intAttribute1240 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_INT_in_intAttribute1243 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_FLOAT_in_floatAttribute1252 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_floatAttribute1255 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_floatAttribute1258 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_FLOAT_in_floatAttribute1261 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_STRING_in_stringAttribute1269 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_stringAttribute1272 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_stringAttribute1275 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_STRING_in_stringAttribute1278 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_BOOL_in_boolAttribute1287 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_boolAttribute1290 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_boolAttribute1293 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_BOOLEAN_in_boolAttribute1296 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_OP_NOT_in_unaryOp1308 = new BitSet(new long[]{0x0000000000000002L});

}