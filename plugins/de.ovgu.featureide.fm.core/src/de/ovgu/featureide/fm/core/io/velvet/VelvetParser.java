// $ANTLR 3.4 Velvet.g 2013-12-10 23:46:03

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
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "ABSTRACT", "ACONSTR", "ATTR", "ATTR_OP_EQUALS", "ATTR_OP_GREATER", "ATTR_OP_GREATER_EQ", "ATTR_OP_LESS", "ATTR_OP_LESS_EQ", "ATTR_OP_NOT_EQUALS", "BASEEXT", "BOOLEAN", "COLON", "COMMA", "CONCEPT", "CONSTR", "CONSTRAINT", "DEF", "END_C", "END_R", "EQ", "ESC_SEQ", "EXPONENT", "FEAT", "FEATURE", "FLOAT", "GROUP", "HEX_DIGIT", "ID", "IDPath", "IMP", "IMPORT", "INSTANCE", "INT", "INTER", "INTERFACEG", "MANDATORY", "MINUS", "OCTAL_ESC", "ONEOF", "OPERAND", "OP_AND", "OP_EQUIVALENT", "OP_IMPLIES", "OP_NOT", "OP_OR", "OP_XOR", "PLUS", "REFINES", "SEMI", "SOMEOF", "START_C", "START_R", "STRING", "UNARYOP", "UNICODE_ESC", "VAR_BOOL", "VAR_FLOAT", "VAR_INT", "VAR_STRING", "WS"
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
    public static final int INTER=37;
    public static final int INTERFACEG=38;
    public static final int MANDATORY=39;
    public static final int MINUS=40;
    public static final int OCTAL_ESC=41;
    public static final int ONEOF=42;
    public static final int OPERAND=43;
    public static final int OP_AND=44;
    public static final int OP_EQUIVALENT=45;
    public static final int OP_IMPLIES=46;
    public static final int OP_NOT=47;
    public static final int OP_OR=48;
    public static final int OP_XOR=49;
    public static final int PLUS=50;
    public static final int REFINES=51;
    public static final int SEMI=52;
    public static final int SOMEOF=53;
    public static final int START_C=54;
    public static final int START_R=55;
    public static final int STRING=56;
    public static final int UNARYOP=57;
    public static final int UNICODE_ESC=58;
    public static final int VAR_BOOL=59;
    public static final int VAR_FLOAT=60;
    public static final int VAR_INT=61;
    public static final int VAR_STRING=62;
    public static final int WS=63;

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
    // Velvet.g:78:1: velvetModel : ( imports )? ( concept | interfaceg ) EOF ;
    public final VelvetParser.velvetModel_return velvetModel() throws RecognitionException {
        VelvetParser.velvetModel_return retval = new VelvetParser.velvetModel_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token EOF4=null;
        VelvetParser.imports_return imports1 =null;

        VelvetParser.concept_return concept2 =null;

        VelvetParser.interfaceg_return interfaceg3 =null;


        Tree EOF4_tree=null;

        try {
            // Velvet.g:79:2: ( ( imports )? ( concept | interfaceg ) EOF )
            // Velvet.g:79:4: ( imports )? ( concept | interfaceg ) EOF
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:79:4: ( imports )?
            int alt1=2;
            int LA1_0 = input.LA(1);

            if ( (LA1_0==IMPORT) ) {
                alt1=1;
            }
            switch (alt1) {
                case 1 :
                    // Velvet.g:79:4: imports
                    {
                    pushFollow(FOLLOW_imports_in_velvetModel451);
                    imports1=imports();

                    state._fsp--;

                    adaptor.addChild(root_0, imports1.getTree());

                    }
                    break;

            }


            // Velvet.g:79:13: ( concept | interfaceg )
            int alt2=2;
            switch ( input.LA(1) ) {
            case REFINES:
                {
                int LA2_1 = input.LA(2);

                if ( (LA2_1==CONCEPT) ) {
                    alt2=1;
                }
                else if ( (LA2_1==INTERFACEG) ) {
                    alt2=2;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 2, 1, input);

                    throw nvae;

                }
                }
                break;
            case CONCEPT:
                {
                alt2=1;
                }
                break;
            case INTERFACEG:
                {
                alt2=2;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 2, 0, input);

                throw nvae;

            }

            switch (alt2) {
                case 1 :
                    // Velvet.g:79:14: concept
                    {
                    pushFollow(FOLLOW_concept_in_velvetModel455);
                    concept2=concept();

                    state._fsp--;

                    adaptor.addChild(root_0, concept2.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:79:22: interfaceg
                    {
                    pushFollow(FOLLOW_interfaceg_in_velvetModel457);
                    interfaceg3=interfaceg();

                    state._fsp--;

                    adaptor.addChild(root_0, interfaceg3.getTree());

                    }
                    break;

            }


            EOF4=(Token)match(input,EOF,FOLLOW_EOF_in_velvetModel460); 
            EOF4_tree = 
            (Tree)adaptor.create(EOF4)
            ;
            adaptor.addChild(root_0, EOF4_tree);


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


    public static class imports_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "imports"
    // Velvet.g:82:1: imports : ( IMPORT name SEMI )+ -> ^( IMP ( name )+ ) ;
    public final VelvetParser.imports_return imports() throws RecognitionException {
        VelvetParser.imports_return retval = new VelvetParser.imports_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token IMPORT5=null;
        Token SEMI7=null;
        VelvetParser.name_return name6 =null;


        Tree IMPORT5_tree=null;
        Tree SEMI7_tree=null;
        RewriteRuleTokenStream stream_IMPORT=new RewriteRuleTokenStream(adaptor,"token IMPORT");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:82:9: ( ( IMPORT name SEMI )+ -> ^( IMP ( name )+ ) )
            // Velvet.g:82:11: ( IMPORT name SEMI )+
            {
            // Velvet.g:82:11: ( IMPORT name SEMI )+
            int cnt3=0;
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( (LA3_0==IMPORT) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // Velvet.g:82:12: IMPORT name SEMI
            	    {
            	    IMPORT5=(Token)match(input,IMPORT,FOLLOW_IMPORT_in_imports472);  
            	    stream_IMPORT.add(IMPORT5);


            	    pushFollow(FOLLOW_name_in_imports474);
            	    name6=name();

            	    state._fsp--;

            	    stream_name.add(name6.getTree());

            	    SEMI7=(Token)match(input,SEMI,FOLLOW_SEMI_in_imports476);  
            	    stream_SEMI.add(SEMI7);


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
            // 83:2: -> ^( IMP ( name )+ )
            {
                // Velvet.g:83:5: ^( IMP ( name )+ )
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
    // Velvet.g:86:1: concept : ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )? definitions -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? definitions ) ;
    public final VelvetParser.concept_return concept() throws RecognitionException {
        VelvetParser.concept_return retval = new VelvetParser.concept_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token REFINES8=null;
        Token CONCEPT9=null;
        Token ID10=null;
        Token COLON11=null;
        Token START_R13=null;
        Token COMMA15=null;
        Token END_R17=null;
        VelvetParser.conceptBaseExt_return conceptBaseExt12 =null;

        VelvetParser.conceptInterExt_return conceptInterExt14 =null;

        VelvetParser.conceptInterExt_return conceptInterExt16 =null;

        VelvetParser.definitions_return definitions18 =null;


        Tree REFINES8_tree=null;
        Tree CONCEPT9_tree=null;
        Tree ID10_tree=null;
        Tree COLON11_tree=null;
        Tree START_R13_tree=null;
        Tree COMMA15_tree=null;
        Tree END_R17_tree=null;
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
            // Velvet.g:87:2: ( ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )? definitions -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? definitions ) )
            // Velvet.g:87:4: ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )? definitions
            {
            // Velvet.g:87:4: ( REFINES )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0==REFINES) ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // Velvet.g:87:4: REFINES
                    {
                    REFINES8=(Token)match(input,REFINES,FOLLOW_REFINES_in_concept501);  
                    stream_REFINES.add(REFINES8);


                    }
                    break;

            }


            CONCEPT9=(Token)match(input,CONCEPT,FOLLOW_CONCEPT_in_concept504);  
            stream_CONCEPT.add(CONCEPT9);


            ID10=(Token)match(input,ID,FOLLOW_ID_in_concept506);  
            stream_ID.add(ID10);


            // Velvet.g:87:25: ( COLON conceptBaseExt )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==COLON) ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // Velvet.g:87:26: COLON conceptBaseExt
                    {
                    COLON11=(Token)match(input,COLON,FOLLOW_COLON_in_concept510);  
                    stream_COLON.add(COLON11);


                    pushFollow(FOLLOW_conceptBaseExt_in_concept512);
                    conceptBaseExt12=conceptBaseExt();

                    state._fsp--;

                    stream_conceptBaseExt.add(conceptBaseExt12.getTree());

                    }
                    break;

            }


            // Velvet.g:87:49: ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )?
            int alt7=2;
            int LA7_0 = input.LA(1);

            if ( (LA7_0==START_R) ) {
                alt7=1;
            }
            switch (alt7) {
                case 1 :
                    // Velvet.g:88:3: START_R conceptInterExt ( COMMA conceptInterExt )* END_R
                    {
                    START_R13=(Token)match(input,START_R,FOLLOW_START_R_in_concept520);  
                    stream_START_R.add(START_R13);


                    pushFollow(FOLLOW_conceptInterExt_in_concept522);
                    conceptInterExt14=conceptInterExt();

                    state._fsp--;

                    stream_conceptInterExt.add(conceptInterExt14.getTree());

                    // Velvet.g:88:27: ( COMMA conceptInterExt )*
                    loop6:
                    do {
                        int alt6=2;
                        int LA6_0 = input.LA(1);

                        if ( (LA6_0==COMMA) ) {
                            alt6=1;
                        }


                        switch (alt6) {
                    	case 1 :
                    	    // Velvet.g:88:28: COMMA conceptInterExt
                    	    {
                    	    COMMA15=(Token)match(input,COMMA,FOLLOW_COMMA_in_concept525);  
                    	    stream_COMMA.add(COMMA15);


                    	    pushFollow(FOLLOW_conceptInterExt_in_concept527);
                    	    conceptInterExt16=conceptInterExt();

                    	    state._fsp--;

                    	    stream_conceptInterExt.add(conceptInterExt16.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop6;
                        }
                    } while (true);


                    END_R17=(Token)match(input,END_R,FOLLOW_END_R_in_concept531);  
                    stream_END_R.add(END_R17);


                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_concept538);
            definitions18=definitions();

            state._fsp--;

            stream_definitions.add(definitions18.getTree());

            // AST REWRITE
            // elements: CONCEPT, conceptBaseExt, definitions, REFINES, ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 90:2: -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? definitions )
            {
                // Velvet.g:90:5: ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CONCEPT.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:90:18: ( REFINES )?
                if ( stream_REFINES.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_REFINES.nextNode()
                    );

                }
                stream_REFINES.reset();

                // Velvet.g:90:27: ( conceptBaseExt )?
                if ( stream_conceptBaseExt.hasNext() ) {
                    adaptor.addChild(root_1, stream_conceptBaseExt.nextTree());

                }
                stream_conceptBaseExt.reset();

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
    // Velvet.g:93:1: conceptBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
    public final VelvetParser.conceptBaseExt_return conceptBaseExt() throws RecognitionException {
        VelvetParser.conceptBaseExt_return retval = new VelvetParser.conceptBaseExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID19=null;
        Token COMMA20=null;
        Token ID21=null;

        Tree ID19_tree=null;
        Tree COMMA20_tree=null;
        Tree ID21_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

        try {
            // Velvet.g:94:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:94:4: ID ( COMMA ID )*
            {
            ID19=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt568);  
            stream_ID.add(ID19);


            // Velvet.g:94:7: ( COMMA ID )*
            loop8:
            do {
                int alt8=2;
                int LA8_0 = input.LA(1);

                if ( (LA8_0==COMMA) ) {
                    alt8=1;
                }


                switch (alt8) {
            	case 1 :
            	    // Velvet.g:94:8: COMMA ID
            	    {
            	    COMMA20=(Token)match(input,COMMA,FOLLOW_COMMA_in_conceptBaseExt571);  
            	    stream_COMMA.add(COMMA20);


            	    ID21=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt573);  
            	    stream_ID.add(ID21);


            	    }
            	    break;

            	default :
            	    break loop8;
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
            // 95:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:95:5: ^( BASEEXT ( ID )+ )
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
    // Velvet.g:98:1: conceptInterExt : interfaceclass ID ;
    public final VelvetParser.conceptInterExt_return conceptInterExt() throws RecognitionException {
        VelvetParser.conceptInterExt_return retval = new VelvetParser.conceptInterExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID23=null;
        VelvetParser.interfaceclass_return interfaceclass22 =null;


        Tree ID23_tree=null;

        try {
            // Velvet.g:99:2: ( interfaceclass ID )
            // Velvet.g:99:4: interfaceclass ID
            {
            root_0 = (Tree)adaptor.nil();


            pushFollow(FOLLOW_interfaceclass_in_conceptInterExt597);
            interfaceclass22=interfaceclass();

            state._fsp--;

            adaptor.addChild(root_0, interfaceclass22.getTree());

            ID23=(Token)match(input,ID,FOLLOW_ID_in_conceptInterExt599); 
            ID23_tree = 
            (Tree)adaptor.create(ID23)
            ;
            adaptor.addChild(root_0, ID23_tree);


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


    public static class interfaceclass_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "interfaceclass"
    // Velvet.g:102:1: interfaceclass : ID ;
    public final VelvetParser.interfaceclass_return interfaceclass() throws RecognitionException {
        VelvetParser.interfaceclass_return retval = new VelvetParser.interfaceclass_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID24=null;

        Tree ID24_tree=null;

        try {
            // Velvet.g:102:16: ( ID )
            // Velvet.g:102:18: ID
            {
            root_0 = (Tree)adaptor.nil();


            ID24=(Token)match(input,ID,FOLLOW_ID_in_interfaceclass609); 
            ID24_tree = 
            (Tree)adaptor.create(ID24)
            ;
            adaptor.addChild(root_0, ID24_tree);


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
    // $ANTLR end "interfaceclass"


    public static class interfaceg_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "interfaceg"
    // Velvet.g:105:1: interfaceg : ( REFINES )? INTERFACEG ID ( COLON interfaceBaseExt )? definitions -> ^( INTERFACEG ID ( REFINES )? ( interfaceBaseExt )? definitions ) ;
    public final VelvetParser.interfaceg_return interfaceg() throws RecognitionException {
        VelvetParser.interfaceg_return retval = new VelvetParser.interfaceg_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token REFINES25=null;
        Token INTERFACEG26=null;
        Token ID27=null;
        Token COLON28=null;
        VelvetParser.interfaceBaseExt_return interfaceBaseExt29 =null;

        VelvetParser.definitions_return definitions30 =null;


        Tree REFINES25_tree=null;
        Tree INTERFACEG26_tree=null;
        Tree ID27_tree=null;
        Tree COLON28_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_INTERFACEG=new RewriteRuleTokenStream(adaptor,"token INTERFACEG");
        RewriteRuleTokenStream stream_REFINES=new RewriteRuleTokenStream(adaptor,"token REFINES");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        RewriteRuleSubtreeStream stream_interfaceBaseExt=new RewriteRuleSubtreeStream(adaptor,"rule interfaceBaseExt");
        try {
            // Velvet.g:105:12: ( ( REFINES )? INTERFACEG ID ( COLON interfaceBaseExt )? definitions -> ^( INTERFACEG ID ( REFINES )? ( interfaceBaseExt )? definitions ) )
            // Velvet.g:105:14: ( REFINES )? INTERFACEG ID ( COLON interfaceBaseExt )? definitions
            {
            // Velvet.g:105:14: ( REFINES )?
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==REFINES) ) {
                alt9=1;
            }
            switch (alt9) {
                case 1 :
                    // Velvet.g:105:14: REFINES
                    {
                    REFINES25=(Token)match(input,REFINES,FOLLOW_REFINES_in_interfaceg619);  
                    stream_REFINES.add(REFINES25);


                    }
                    break;

            }


            INTERFACEG26=(Token)match(input,INTERFACEG,FOLLOW_INTERFACEG_in_interfaceg622);  
            stream_INTERFACEG.add(INTERFACEG26);


            ID27=(Token)match(input,ID,FOLLOW_ID_in_interfaceg624);  
            stream_ID.add(ID27);


            // Velvet.g:105:38: ( COLON interfaceBaseExt )?
            int alt10=2;
            int LA10_0 = input.LA(1);

            if ( (LA10_0==COLON) ) {
                alt10=1;
            }
            switch (alt10) {
                case 1 :
                    // Velvet.g:105:39: COLON interfaceBaseExt
                    {
                    COLON28=(Token)match(input,COLON,FOLLOW_COLON_in_interfaceg628);  
                    stream_COLON.add(COLON28);


                    pushFollow(FOLLOW_interfaceBaseExt_in_interfaceg630);
                    interfaceBaseExt29=interfaceBaseExt();

                    state._fsp--;

                    stream_interfaceBaseExt.add(interfaceBaseExt29.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_interfaceg634);
            definitions30=definitions();

            state._fsp--;

            stream_definitions.add(definitions30.getTree());

            // AST REWRITE
            // elements: interfaceBaseExt, INTERFACEG, REFINES, ID, definitions
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 106:2: -> ^( INTERFACEG ID ( REFINES )? ( interfaceBaseExt )? definitions )
            {
                // Velvet.g:106:5: ^( INTERFACEG ID ( REFINES )? ( interfaceBaseExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_INTERFACEG.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:106:21: ( REFINES )?
                if ( stream_REFINES.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_REFINES.nextNode()
                    );

                }
                stream_REFINES.reset();

                // Velvet.g:106:30: ( interfaceBaseExt )?
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
    // $ANTLR end "interfaceg"


    public static class interfaceBaseExt_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "interfaceBaseExt"
    // Velvet.g:109:1: interfaceBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
    public final VelvetParser.interfaceBaseExt_return interfaceBaseExt() throws RecognitionException {
        VelvetParser.interfaceBaseExt_return retval = new VelvetParser.interfaceBaseExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID31=null;
        Token COMMA32=null;
        Token ID33=null;

        Tree ID31_tree=null;
        Tree COMMA32_tree=null;
        Tree ID33_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

        try {
            // Velvet.g:110:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:110:4: ID ( COMMA ID )*
            {
            ID31=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt664);  
            stream_ID.add(ID31);


            // Velvet.g:110:7: ( COMMA ID )*
            loop11:
            do {
                int alt11=2;
                int LA11_0 = input.LA(1);

                if ( (LA11_0==COMMA) ) {
                    alt11=1;
                }


                switch (alt11) {
            	case 1 :
            	    // Velvet.g:110:8: COMMA ID
            	    {
            	    COMMA32=(Token)match(input,COMMA,FOLLOW_COMMA_in_interfaceBaseExt667);  
            	    stream_COMMA.add(COMMA32);


            	    ID33=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt669);  
            	    stream_ID.add(ID33);


            	    }
            	    break;

            	default :
            	    break loop11;
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
            // 111:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:111:5: ^( BASEEXT ( ID )+ )
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
    // Velvet.g:114:1: name : ( ID | IDPath );
    public final VelvetParser.name_return name() throws RecognitionException {
        VelvetParser.name_return retval = new VelvetParser.name_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set34=null;

        Tree set34_tree=null;

        try {
            // Velvet.g:114:5: ( ID | IDPath )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set34=(Token)input.LT(1);

            if ( (input.LA(1) >= ID && input.LA(1) <= IDPath) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set34)
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
    // Velvet.g:118:1: definitions : START_C def END_C -> ^( DEF def ) ;
    public final VelvetParser.definitions_return definitions() throws RecognitionException {
        VelvetParser.definitions_return retval = new VelvetParser.definitions_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C35=null;
        Token END_C37=null;
        VelvetParser.def_return def36 =null;


        Tree START_C35_tree=null;
        Tree END_C37_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_def=new RewriteRuleSubtreeStream(adaptor,"rule def");
        try {
            // Velvet.g:119:2: ( START_C def END_C -> ^( DEF def ) )
            // Velvet.g:119:4: START_C def END_C
            {
            START_C35=(Token)match(input,START_C,FOLLOW_START_C_in_definitions709);  
            stream_START_C.add(START_C35);


            pushFollow(FOLLOW_def_in_definitions711);
            def36=def();

            state._fsp--;

            stream_def.add(def36.getTree());

            END_C37=(Token)match(input,END_C,FOLLOW_END_C_in_definitions713);  
            stream_END_C.add(END_C37);


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
            // 120:2: -> ^( DEF def )
            {
                // Velvet.g:120:5: ^( DEF def )
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
    // Velvet.g:123:1: def : ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? ;
    public final VelvetParser.def_return def() throws RecognitionException {
        VelvetParser.def_return retval = new VelvetParser.def_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition38 =null;

        VelvetParser.featureGroup_return featureGroup39 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition40 =null;

        VelvetParser.feature_return feature41 =null;

        VelvetParser.feature_return feature42 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition43 =null;



        try {
            // Velvet.g:123:5: ( ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? )
            // Velvet.g:123:7: ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:123:7: ( nonFeatureDefinition )*
            loop12:
            do {
                int alt12=2;
                int LA12_0 = input.LA(1);

                if ( (LA12_0==CONSTRAINT||LA12_0==ID||(LA12_0 >= VAR_BOOL && LA12_0 <= VAR_STRING)) ) {
                    alt12=1;
                }


                switch (alt12) {
            	case 1 :
            	    // Velvet.g:123:7: nonFeatureDefinition
            	    {
            	    pushFollow(FOLLOW_nonFeatureDefinition_in_def732);
            	    nonFeatureDefinition38=nonFeatureDefinition();

            	    state._fsp--;

            	    adaptor.addChild(root_0, nonFeatureDefinition38.getTree());

            	    }
            	    break;

            	default :
            	    break loop12;
                }
            } while (true);


            // Velvet.g:123:29: ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            int alt15=3;
            int LA15_0 = input.LA(1);

            if ( (LA15_0==ONEOF||LA15_0==SOMEOF) ) {
                alt15=1;
            }
            else if ( (LA15_0==ABSTRACT||LA15_0==FEATURE||LA15_0==MANDATORY) ) {
                alt15=2;
            }
            switch (alt15) {
                case 1 :
                    // Velvet.g:124:3: ( featureGroup ( nonFeatureDefinition )* )
                    {
                    // Velvet.g:124:3: ( featureGroup ( nonFeatureDefinition )* )
                    // Velvet.g:124:4: featureGroup ( nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_featureGroup_in_def740);
                    featureGroup39=featureGroup();

                    state._fsp--;

                    adaptor.addChild(root_0, featureGroup39.getTree());

                    // Velvet.g:124:17: ( nonFeatureDefinition )*
                    loop13:
                    do {
                        int alt13=2;
                        int LA13_0 = input.LA(1);

                        if ( (LA13_0==CONSTRAINT||LA13_0==ID||(LA13_0 >= VAR_BOOL && LA13_0 <= VAR_STRING)) ) {
                            alt13=1;
                        }


                        switch (alt13) {
                    	case 1 :
                    	    // Velvet.g:124:17: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def742);
                    	    nonFeatureDefinition40=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition40.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop13;
                        }
                    } while (true);


                    }


                    }
                    break;
                case 2 :
                    // Velvet.g:125:3: ( feature ( feature | nonFeatureDefinition )* )
                    {
                    // Velvet.g:125:3: ( feature ( feature | nonFeatureDefinition )* )
                    // Velvet.g:125:4: feature ( feature | nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_feature_in_def751);
                    feature41=feature();

                    state._fsp--;

                    adaptor.addChild(root_0, feature41.getTree());

                    // Velvet.g:125:12: ( feature | nonFeatureDefinition )*
                    loop14:
                    do {
                        int alt14=3;
                        int LA14_0 = input.LA(1);

                        if ( (LA14_0==ABSTRACT||LA14_0==FEATURE||LA14_0==MANDATORY) ) {
                            alt14=1;
                        }
                        else if ( (LA14_0==CONSTRAINT||LA14_0==ID||(LA14_0 >= VAR_BOOL && LA14_0 <= VAR_STRING)) ) {
                            alt14=2;
                        }


                        switch (alt14) {
                    	case 1 :
                    	    // Velvet.g:125:13: feature
                    	    {
                    	    pushFollow(FOLLOW_feature_in_def754);
                    	    feature42=feature();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, feature42.getTree());

                    	    }
                    	    break;
                    	case 2 :
                    	    // Velvet.g:125:23: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def758);
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
    // Velvet.g:128:1: nonFeatureDefinition : ( constraint | instance | attribute );
    public final VelvetParser.nonFeatureDefinition_return nonFeatureDefinition() throws RecognitionException {
        VelvetParser.nonFeatureDefinition_return retval = new VelvetParser.nonFeatureDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraint_return constraint44 =null;

        VelvetParser.instance_return instance45 =null;

        VelvetParser.attribute_return attribute46 =null;



        try {
            // Velvet.g:129:2: ( constraint | instance | attribute )
            int alt16=3;
            switch ( input.LA(1) ) {
            case CONSTRAINT:
                {
                alt16=1;
                }
                break;
            case ID:
                {
                alt16=2;
                }
                break;
            case VAR_BOOL:
            case VAR_FLOAT:
            case VAR_INT:
            case VAR_STRING:
                {
                alt16=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 16, 0, input);

                throw nvae;

            }

            switch (alt16) {
                case 1 :
                    // Velvet.g:129:4: constraint
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_constraint_in_nonFeatureDefinition778);
                    constraint44=constraint();

                    state._fsp--;

                    adaptor.addChild(root_0, constraint44.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:130:4: instance
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_instance_in_nonFeatureDefinition784);
                    instance45=instance();

                    state._fsp--;

                    adaptor.addChild(root_0, instance45.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:131:4: attribute
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_attribute_in_nonFeatureDefinition790);
                    attribute46=attribute();

                    state._fsp--;

                    adaptor.addChild(root_0, attribute46.getTree());

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
    // Velvet.g:134:1: instance : ID name SEMI -> INSTANCE ID name ;
    public final VelvetParser.instance_return instance() throws RecognitionException {
        VelvetParser.instance_return retval = new VelvetParser.instance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID47=null;
        Token SEMI49=null;
        VelvetParser.name_return name48 =null;


        Tree ID47_tree=null;
        Tree SEMI49_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:134:9: ( ID name SEMI -> INSTANCE ID name )
            // Velvet.g:134:11: ID name SEMI
            {
            ID47=(Token)match(input,ID,FOLLOW_ID_in_instance801);  
            stream_ID.add(ID47);


            pushFollow(FOLLOW_name_in_instance803);
            name48=name();

            state._fsp--;

            stream_name.add(name48.getTree());

            SEMI49=(Token)match(input,SEMI,FOLLOW_SEMI_in_instance805);  
            stream_SEMI.add(SEMI49);


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
            // 135:2: -> INSTANCE ID name
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
    // Velvet.g:138:1: feature : ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) ;
    public final VelvetParser.feature_return feature() throws RecognitionException {
        VelvetParser.feature_return retval = new VelvetParser.feature_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token MANDATORY50=null;
        Token ABSTRACT51=null;
        Token ABSTRACT52=null;
        Token MANDATORY53=null;
        Token MANDATORY54=null;
        Token ABSTRACT55=null;
        Token FEATURE56=null;
        Token SEMI59=null;
        VelvetParser.name_return name57 =null;

        VelvetParser.definitions_return definitions58 =null;


        Tree MANDATORY50_tree=null;
        Tree ABSTRACT51_tree=null;
        Tree ABSTRACT52_tree=null;
        Tree MANDATORY53_tree=null;
        Tree MANDATORY54_tree=null;
        Tree ABSTRACT55_tree=null;
        Tree FEATURE56_tree=null;
        Tree SEMI59_tree=null;
        RewriteRuleTokenStream stream_ABSTRACT=new RewriteRuleTokenStream(adaptor,"token ABSTRACT");
        RewriteRuleTokenStream stream_MANDATORY=new RewriteRuleTokenStream(adaptor,"token MANDATORY");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleTokenStream stream_FEATURE=new RewriteRuleTokenStream(adaptor,"token FEATURE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:139:2: ( ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) )
            // Velvet.g:139:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI )
            {
            // Velvet.g:139:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )?
            int alt17=5;
            int LA17_0 = input.LA(1);

            if ( (LA17_0==MANDATORY) ) {
                int LA17_1 = input.LA(2);

                if ( (LA17_1==ABSTRACT) ) {
                    alt17=1;
                }
                else if ( (LA17_1==FEATURE) ) {
                    alt17=3;
                }
            }
            else if ( (LA17_0==ABSTRACT) ) {
                int LA17_2 = input.LA(2);

                if ( (LA17_2==MANDATORY) ) {
                    alt17=2;
                }
                else if ( (LA17_2==FEATURE) ) {
                    alt17=4;
                }
            }
            switch (alt17) {
                case 1 :
                    // Velvet.g:139:5: MANDATORY ABSTRACT
                    {
                    MANDATORY50=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature827);  
                    stream_MANDATORY.add(MANDATORY50);


                    ABSTRACT51=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature829);  
                    stream_ABSTRACT.add(ABSTRACT51);


                    }
                    break;
                case 2 :
                    // Velvet.g:139:26: ABSTRACT MANDATORY
                    {
                    ABSTRACT52=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature833);  
                    stream_ABSTRACT.add(ABSTRACT52);


                    MANDATORY53=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature835);  
                    stream_MANDATORY.add(MANDATORY53);


                    }
                    break;
                case 3 :
                    // Velvet.g:139:47: MANDATORY
                    {
                    MANDATORY54=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature839);  
                    stream_MANDATORY.add(MANDATORY54);


                    }
                    break;
                case 4 :
                    // Velvet.g:139:59: ABSTRACT
                    {
                    ABSTRACT55=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature843);  
                    stream_ABSTRACT.add(ABSTRACT55);


                    }
                    break;

            }


            FEATURE56=(Token)match(input,FEATURE,FOLLOW_FEATURE_in_feature850);  
            stream_FEATURE.add(FEATURE56);


            pushFollow(FOLLOW_name_in_feature852);
            name57=name();

            state._fsp--;

            stream_name.add(name57.getTree());

            // Velvet.g:140:17: ( definitions | SEMI )
            int alt18=2;
            int LA18_0 = input.LA(1);

            if ( (LA18_0==START_C) ) {
                alt18=1;
            }
            else if ( (LA18_0==SEMI) ) {
                alt18=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 18, 0, input);

                throw nvae;

            }
            switch (alt18) {
                case 1 :
                    // Velvet.g:140:18: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_feature855);
                    definitions58=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions58.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:140:32: SEMI
                    {
                    SEMI59=(Token)match(input,SEMI,FOLLOW_SEMI_in_feature859);  
                    stream_SEMI.add(SEMI59);


                    }
                    break;

            }


            // AST REWRITE
            // elements: MANDATORY, ABSTRACT, name, definitions
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 141:2: -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
            {
                // Velvet.g:141:5: ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(FEAT, "FEAT")
                , root_1);

                adaptor.addChild(root_1, stream_name.nextTree());

                // Velvet.g:141:17: ( MANDATORY )?
                if ( stream_MANDATORY.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_MANDATORY.nextNode()
                    );

                }
                stream_MANDATORY.reset();

                // Velvet.g:141:28: ( ABSTRACT )?
                if ( stream_ABSTRACT.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ABSTRACT.nextNode()
                    );

                }
                stream_ABSTRACT.reset();

                // Velvet.g:141:38: ( definitions )?
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
    // Velvet.g:144:1: featureGroup : groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) ;
    public final VelvetParser.featureGroup_return featureGroup() throws RecognitionException {
        VelvetParser.featureGroup_return retval = new VelvetParser.featureGroup_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C61=null;
        Token END_C64=null;
        VelvetParser.groupType_return groupType60 =null;

        VelvetParser.feature_return feature62 =null;

        VelvetParser.feature_return feature63 =null;


        Tree START_C61_tree=null;
        Tree END_C64_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_groupType=new RewriteRuleSubtreeStream(adaptor,"rule groupType");
        RewriteRuleSubtreeStream stream_feature=new RewriteRuleSubtreeStream(adaptor,"rule feature");
        try {
            // Velvet.g:145:2: ( groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) )
            // Velvet.g:145:4: groupType START_C feature ( feature )+ END_C
            {
            pushFollow(FOLLOW_groupType_in_featureGroup890);
            groupType60=groupType();

            state._fsp--;

            stream_groupType.add(groupType60.getTree());

            START_C61=(Token)match(input,START_C,FOLLOW_START_C_in_featureGroup892);  
            stream_START_C.add(START_C61);


            pushFollow(FOLLOW_feature_in_featureGroup894);
            feature62=feature();

            state._fsp--;

            stream_feature.add(feature62.getTree());

            // Velvet.g:145:30: ( feature )+
            int cnt19=0;
            loop19:
            do {
                int alt19=2;
                int LA19_0 = input.LA(1);

                if ( (LA19_0==ABSTRACT||LA19_0==FEATURE||LA19_0==MANDATORY) ) {
                    alt19=1;
                }


                switch (alt19) {
            	case 1 :
            	    // Velvet.g:145:30: feature
            	    {
            	    pushFollow(FOLLOW_feature_in_featureGroup896);
            	    feature63=feature();

            	    state._fsp--;

            	    stream_feature.add(feature63.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt19 >= 1 ) break loop19;
                        EarlyExitException eee =
                            new EarlyExitException(19, input);
                        throw eee;
                }
                cnt19++;
            } while (true);


            END_C64=(Token)match(input,END_C,FOLLOW_END_C_in_featureGroup899);  
            stream_END_C.add(END_C64);


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
            // 146:2: -> ^( GROUP groupType feature ( feature )+ )
            {
                // Velvet.g:146:5: ^( GROUP groupType feature ( feature )+ )
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
    // Velvet.g:149:1: groupType : ( SOMEOF | ONEOF );
    public final VelvetParser.groupType_return groupType() throws RecognitionException {
        VelvetParser.groupType_return retval = new VelvetParser.groupType_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set65=null;

        Tree set65_tree=null;

        try {
            // Velvet.g:150:2: ( SOMEOF | ONEOF )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set65=(Token)input.LT(1);

            if ( input.LA(1)==ONEOF||input.LA(1)==SOMEOF ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set65)
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
    // Velvet.g:154:1: constraint : CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !;
    public final VelvetParser.constraint_return constraint() throws RecognitionException {
        VelvetParser.constraint_return retval = new VelvetParser.constraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token CONSTRAINT66=null;
        Token ID67=null;
        Token EQ68=null;
        Token SEMI71=null;
        VelvetParser.constraintDefinition_return constraintDefinition69 =null;

        VelvetParser.attributeConstraint_return attributeConstraint70 =null;


        Tree CONSTRAINT66_tree=null;
        Tree ID67_tree=null;
        Tree EQ68_tree=null;
        Tree SEMI71_tree=null;

        try {
            // Velvet.g:155:2: ( CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !)
            // Velvet.g:155:4: CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !
            {
            root_0 = (Tree)adaptor.nil();


            CONSTRAINT66=(Token)match(input,CONSTRAINT,FOLLOW_CONSTRAINT_in_constraint942); 
            CONSTRAINT66_tree = 
            (Tree)adaptor.create(CONSTRAINT66)
            ;
            root_0 = (Tree)adaptor.becomeRoot(CONSTRAINT66_tree, root_0);


            // Velvet.g:155:16: ( ID EQ !)?
            int alt20=2;
            int LA20_0 = input.LA(1);

            if ( (LA20_0==ID) ) {
                int LA20_1 = input.LA(2);

                if ( (LA20_1==EQ) ) {
                    alt20=1;
                }
            }
            switch (alt20) {
                case 1 :
                    // Velvet.g:155:17: ID EQ !
                    {
                    ID67=(Token)match(input,ID,FOLLOW_ID_in_constraint946); 
                    ID67_tree = 
                    (Tree)adaptor.create(ID67)
                    ;
                    adaptor.addChild(root_0, ID67_tree);


                    EQ68=(Token)match(input,EQ,FOLLOW_EQ_in_constraint948); 

                    }
                    break;

            }


            // Velvet.g:155:26: ( constraintDefinition | attributeConstraint )
            int alt21=2;
            switch ( input.LA(1) ) {
            case OP_NOT:
            case START_R:
                {
                alt21=1;
                }
                break;
            case ID:
            case IDPath:
                {
                int LA21_2 = input.LA(2);

                if ( ((LA21_2 >= OP_AND && LA21_2 <= OP_IMPLIES)||(LA21_2 >= OP_OR && LA21_2 <= OP_XOR)||LA21_2==SEMI) ) {
                    alt21=1;
                }
                else if ( (LA21_2==ATTR_OP_EQUALS||LA21_2==ATTR_OP_GREATER_EQ||LA21_2==ATTR_OP_LESS_EQ||LA21_2==MINUS||LA21_2==PLUS) ) {
                    alt21=2;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 21, 2, input);

                    throw nvae;

                }
                }
                break;
            case INT:
                {
                alt21=2;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 21, 0, input);

                throw nvae;

            }

            switch (alt21) {
                case 1 :
                    // Velvet.g:155:27: constraintDefinition
                    {
                    pushFollow(FOLLOW_constraintDefinition_in_constraint954);
                    constraintDefinition69=constraintDefinition();

                    state._fsp--;

                    adaptor.addChild(root_0, constraintDefinition69.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:155:50: attributeConstraint
                    {
                    pushFollow(FOLLOW_attributeConstraint_in_constraint958);
                    attributeConstraint70=attributeConstraint();

                    state._fsp--;

                    adaptor.addChild(root_0, attributeConstraint70.getTree());

                    }
                    break;

            }


            SEMI71=(Token)match(input,SEMI,FOLLOW_SEMI_in_constraint961); 

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
    // Velvet.g:158:1: constraintDefinition : constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) ;
    public final VelvetParser.constraintDefinition_return constraintDefinition() throws RecognitionException {
        VelvetParser.constraintDefinition_return retval = new VelvetParser.constraintDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraintOperand_return constraintOperand72 =null;

        VelvetParser.binaryOp_return binaryOp73 =null;

        VelvetParser.constraintOperand_return constraintOperand74 =null;


        RewriteRuleSubtreeStream stream_constraintOperand=new RewriteRuleSubtreeStream(adaptor,"rule constraintOperand");
        RewriteRuleSubtreeStream stream_binaryOp=new RewriteRuleSubtreeStream(adaptor,"rule binaryOp");
        try {
            // Velvet.g:159:2: ( constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) )
            // Velvet.g:159:4: constraintOperand ( binaryOp constraintOperand )*
            {
            pushFollow(FOLLOW_constraintOperand_in_constraintDefinition974);
            constraintOperand72=constraintOperand();

            state._fsp--;

            stream_constraintOperand.add(constraintOperand72.getTree());

            // Velvet.g:159:22: ( binaryOp constraintOperand )*
            loop22:
            do {
                int alt22=2;
                int LA22_0 = input.LA(1);

                if ( ((LA22_0 >= OP_AND && LA22_0 <= OP_IMPLIES)||(LA22_0 >= OP_OR && LA22_0 <= OP_XOR)) ) {
                    alt22=1;
                }


                switch (alt22) {
            	case 1 :
            	    // Velvet.g:159:23: binaryOp constraintOperand
            	    {
            	    pushFollow(FOLLOW_binaryOp_in_constraintDefinition977);
            	    binaryOp73=binaryOp();

            	    state._fsp--;

            	    stream_binaryOp.add(binaryOp73.getTree());

            	    pushFollow(FOLLOW_constraintOperand_in_constraintDefinition979);
            	    constraintOperand74=constraintOperand();

            	    state._fsp--;

            	    stream_constraintOperand.add(constraintOperand74.getTree());

            	    }
            	    break;

            	default :
            	    break loop22;
                }
            } while (true);


            // AST REWRITE
            // elements: constraintOperand, binaryOp
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 160:2: -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
            {
                // Velvet.g:160:5: ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
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

                // Velvet.g:160:33: ( binaryOp )*
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
    // Velvet.g:163:1: constraintOperand : ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? ;
    public final VelvetParser.constraintOperand_return constraintOperand() throws RecognitionException {
        VelvetParser.constraintOperand_return retval = new VelvetParser.constraintOperand_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_R76=null;
        Token END_R78=null;
        VelvetParser.unaryOp_return unaryOp75 =null;

        VelvetParser.constraintDefinition_return constraintDefinition77 =null;

        VelvetParser.name_return name79 =null;


        Tree START_R76_tree=null;
        Tree END_R78_tree=null;
        RewriteRuleTokenStream stream_END_R=new RewriteRuleTokenStream(adaptor,"token END_R");
        RewriteRuleTokenStream stream_START_R=new RewriteRuleTokenStream(adaptor,"token START_R");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_unaryOp=new RewriteRuleSubtreeStream(adaptor,"rule unaryOp");
        RewriteRuleSubtreeStream stream_constraintDefinition=new RewriteRuleSubtreeStream(adaptor,"rule constraintDefinition");
        try {
            // Velvet.g:163:19: ( ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? )
            // Velvet.g:163:21: ( unaryOp )* ( START_R constraintDefinition END_R | name )
            {
            // Velvet.g:163:21: ( unaryOp )*
            loop23:
            do {
                int alt23=2;
                int LA23_0 = input.LA(1);

                if ( (LA23_0==OP_NOT) ) {
                    alt23=1;
                }


                switch (alt23) {
            	case 1 :
            	    // Velvet.g:163:21: unaryOp
            	    {
            	    pushFollow(FOLLOW_unaryOp_in_constraintOperand1006);
            	    unaryOp75=unaryOp();

            	    state._fsp--;

            	    stream_unaryOp.add(unaryOp75.getTree());

            	    }
            	    break;

            	default :
            	    break loop23;
                }
            } while (true);


            // Velvet.g:163:30: ( START_R constraintDefinition END_R | name )
            int alt24=2;
            int LA24_0 = input.LA(1);

            if ( (LA24_0==START_R) ) {
                alt24=1;
            }
            else if ( ((LA24_0 >= ID && LA24_0 <= IDPath)) ) {
                alt24=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 24, 0, input);

                throw nvae;

            }
            switch (alt24) {
                case 1 :
                    // Velvet.g:163:31: START_R constraintDefinition END_R
                    {
                    START_R76=(Token)match(input,START_R,FOLLOW_START_R_in_constraintOperand1010);  
                    stream_START_R.add(START_R76);


                    pushFollow(FOLLOW_constraintDefinition_in_constraintOperand1012);
                    constraintDefinition77=constraintDefinition();

                    state._fsp--;

                    stream_constraintDefinition.add(constraintDefinition77.getTree());

                    END_R78=(Token)match(input,END_R,FOLLOW_END_R_in_constraintOperand1014);  
                    stream_END_R.add(END_R78);


                    }
                    break;
                case 2 :
                    // Velvet.g:163:68: name
                    {
                    pushFollow(FOLLOW_name_in_constraintOperand1018);
                    name79=name();

                    state._fsp--;

                    stream_name.add(name79.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: constraintDefinition, name, unaryOp
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 164:2: -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )?
            {
                // Velvet.g:164:5: ( constraintDefinition )?
                if ( stream_constraintDefinition.hasNext() ) {
                    adaptor.addChild(root_0, stream_constraintDefinition.nextTree());

                }
                stream_constraintDefinition.reset();

                // Velvet.g:164:27: ( ^( UNARYOP unaryOp ) )*
                while ( stream_unaryOp.hasNext() ) {
                    // Velvet.g:164:27: ^( UNARYOP unaryOp )
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

                // Velvet.g:164:47: ( ^( OPERAND name ) )?
                if ( stream_name.hasNext() ) {
                    // Velvet.g:164:47: ^( OPERAND name )
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
    // Velvet.g:167:1: attributeConstraint : attribConstraint -> ^( ACONSTR attribConstraint ) ;
    public final VelvetParser.attributeConstraint_return attributeConstraint() throws RecognitionException {
        VelvetParser.attributeConstraint_return retval = new VelvetParser.attributeConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribConstraint_return attribConstraint80 =null;


        RewriteRuleSubtreeStream stream_attribConstraint=new RewriteRuleSubtreeStream(adaptor,"rule attribConstraint");
        try {
            // Velvet.g:168:2: ( attribConstraint -> ^( ACONSTR attribConstraint ) )
            // Velvet.g:168:4: attribConstraint
            {
            pushFollow(FOLLOW_attribConstraint_in_attributeConstraint1053);
            attribConstraint80=attribConstraint();

            state._fsp--;

            stream_attribConstraint.add(attribConstraint80.getTree());

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
            // 169:2: -> ^( ACONSTR attribConstraint )
            {
                // Velvet.g:169:5: ^( ACONSTR attribConstraint )
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
    // Velvet.g:172:1: attribConstraint : attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* ;
    public final VelvetParser.attribConstraint_return attribConstraint() throws RecognitionException {
        VelvetParser.attribConstraint_return retval = new VelvetParser.attribConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribNumInstance_return attribNumInstance81 =null;

        VelvetParser.attribOperator_return attribOperator82 =null;

        VelvetParser.attribNumInstance_return attribNumInstance83 =null;

        VelvetParser.attribRelation_return attribRelation84 =null;

        VelvetParser.attribNumInstance_return attribNumInstance85 =null;

        VelvetParser.attribOperator_return attribOperator86 =null;

        VelvetParser.attribNumInstance_return attribNumInstance87 =null;



        try {
            // Velvet.g:173:2: ( attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* )
            // Velvet.g:173:4: attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )*
            {
            root_0 = (Tree)adaptor.nil();


            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1073);
            attribNumInstance81=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance81.getTree());

            // Velvet.g:173:22: ( attribOperator attribNumInstance )*
            loop25:
            do {
                int alt25=2;
                int LA25_0 = input.LA(1);

                if ( (LA25_0==MINUS||LA25_0==PLUS) ) {
                    alt25=1;
                }


                switch (alt25) {
            	case 1 :
            	    // Velvet.g:173:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1076);
            	    attribOperator82=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator82.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1078);
            	    attribNumInstance83=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance83.getTree());

            	    }
            	    break;

            	default :
            	    break loop25;
                }
            } while (true);


            pushFollow(FOLLOW_attribRelation_in_attribConstraint1086);
            attribRelation84=attribRelation();

            state._fsp--;

            adaptor.addChild(root_0, attribRelation84.getTree());

            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1092);
            attribNumInstance85=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance85.getTree());

            // Velvet.g:175:22: ( attribOperator attribNumInstance )*
            loop26:
            do {
                int alt26=2;
                int LA26_0 = input.LA(1);

                if ( (LA26_0==MINUS||LA26_0==PLUS) ) {
                    alt26=1;
                }


                switch (alt26) {
            	case 1 :
            	    // Velvet.g:175:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1095);
            	    attribOperator86=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator86.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1097);
            	    attribNumInstance87=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance87.getTree());

            	    }
            	    break;

            	default :
            	    break loop26;
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
    // Velvet.g:178:1: attribOperator : ( PLUS | MINUS );
    public final VelvetParser.attribOperator_return attribOperator() throws RecognitionException {
        VelvetParser.attribOperator_return retval = new VelvetParser.attribOperator_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set88=null;

        Tree set88_tree=null;

        try {
            // Velvet.g:179:2: ( PLUS | MINUS )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set88=(Token)input.LT(1);

            if ( input.LA(1)==MINUS||input.LA(1)==PLUS ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set88)
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
    // Velvet.g:183:1: attribNumInstance : ( INT | name );
    public final VelvetParser.attribNumInstance_return attribNumInstance() throws RecognitionException {
        VelvetParser.attribNumInstance_return retval = new VelvetParser.attribNumInstance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token INT89=null;
        VelvetParser.name_return name90 =null;


        Tree INT89_tree=null;

        try {
            // Velvet.g:184:2: ( INT | name )
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==INT) ) {
                alt27=1;
            }
            else if ( ((LA27_0 >= ID && LA27_0 <= IDPath)) ) {
                alt27=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 27, 0, input);

                throw nvae;

            }
            switch (alt27) {
                case 1 :
                    // Velvet.g:184:4: INT
                    {
                    root_0 = (Tree)adaptor.nil();


                    INT89=(Token)match(input,INT,FOLLOW_INT_in_attribNumInstance1129); 
                    INT89_tree = 
                    (Tree)adaptor.create(INT89)
                    ;
                    adaptor.addChild(root_0, INT89_tree);


                    }
                    break;
                case 2 :
                    // Velvet.g:186:4: name
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_name_in_attribNumInstance1136);
                    name90=name();

                    state._fsp--;

                    adaptor.addChild(root_0, name90.getTree());

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
    // Velvet.g:189:1: attribute : ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) ;
    public final VelvetParser.attribute_return attribute() throws RecognitionException {
        VelvetParser.attribute_return retval = new VelvetParser.attribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token SEMI95=null;
        VelvetParser.intAttribute_return intAttribute91 =null;

        VelvetParser.floatAttribute_return floatAttribute92 =null;

        VelvetParser.stringAttribute_return stringAttribute93 =null;

        VelvetParser.boolAttribute_return boolAttribute94 =null;


        Tree SEMI95_tree=null;
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_intAttribute=new RewriteRuleSubtreeStream(adaptor,"rule intAttribute");
        RewriteRuleSubtreeStream stream_stringAttribute=new RewriteRuleSubtreeStream(adaptor,"rule stringAttribute");
        RewriteRuleSubtreeStream stream_floatAttribute=new RewriteRuleSubtreeStream(adaptor,"rule floatAttribute");
        RewriteRuleSubtreeStream stream_boolAttribute=new RewriteRuleSubtreeStream(adaptor,"rule boolAttribute");
        try {
            // Velvet.g:190:2: ( ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) )
            // Velvet.g:190:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI
            {
            // Velvet.g:190:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute )
            int alt28=4;
            switch ( input.LA(1) ) {
            case VAR_INT:
                {
                alt28=1;
                }
                break;
            case VAR_FLOAT:
                {
                alt28=2;
                }
                break;
            case VAR_STRING:
                {
                alt28=3;
                }
                break;
            case VAR_BOOL:
                {
                alt28=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 28, 0, input);

                throw nvae;

            }

            switch (alt28) {
                case 1 :
                    // Velvet.g:190:5: intAttribute
                    {
                    pushFollow(FOLLOW_intAttribute_in_attribute1148);
                    intAttribute91=intAttribute();

                    state._fsp--;

                    stream_intAttribute.add(intAttribute91.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:190:20: floatAttribute
                    {
                    pushFollow(FOLLOW_floatAttribute_in_attribute1152);
                    floatAttribute92=floatAttribute();

                    state._fsp--;

                    stream_floatAttribute.add(floatAttribute92.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:190:37: stringAttribute
                    {
                    pushFollow(FOLLOW_stringAttribute_in_attribute1156);
                    stringAttribute93=stringAttribute();

                    state._fsp--;

                    stream_stringAttribute.add(stringAttribute93.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:190:55: boolAttribute
                    {
                    pushFollow(FOLLOW_boolAttribute_in_attribute1160);
                    boolAttribute94=boolAttribute();

                    state._fsp--;

                    stream_boolAttribute.add(boolAttribute94.getTree());

                    }
                    break;

            }


            SEMI95=(Token)match(input,SEMI,FOLLOW_SEMI_in_attribute1163);  
            stream_SEMI.add(SEMI95);


            // AST REWRITE
            // elements: stringAttribute, boolAttribute, floatAttribute, intAttribute
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 191:2: -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
            {
                // Velvet.g:191:5: ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(ATTR, "ATTR")
                , root_1);

                // Velvet.g:191:12: ( intAttribute )?
                if ( stream_intAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_intAttribute.nextTree());

                }
                stream_intAttribute.reset();

                // Velvet.g:191:26: ( floatAttribute )?
                if ( stream_floatAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_floatAttribute.nextTree());

                }
                stream_floatAttribute.reset();

                // Velvet.g:191:42: ( stringAttribute )?
                if ( stream_stringAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_stringAttribute.nextTree());

                }
                stream_stringAttribute.reset();

                // Velvet.g:191:59: ( boolAttribute )?
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
    // Velvet.g:194:1: intAttribute : VAR_INT ! name ( EQ ! INT )? ;
    public final VelvetParser.intAttribute_return intAttribute() throws RecognitionException {
        VelvetParser.intAttribute_return retval = new VelvetParser.intAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_INT96=null;
        Token EQ98=null;
        Token INT99=null;
        VelvetParser.name_return name97 =null;


        Tree VAR_INT96_tree=null;
        Tree EQ98_tree=null;
        Tree INT99_tree=null;

        try {
            // Velvet.g:194:13: ( VAR_INT ! name ( EQ ! INT )? )
            // Velvet.g:194:16: VAR_INT ! name ( EQ ! INT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_INT96=(Token)match(input,VAR_INT,FOLLOW_VAR_INT_in_intAttribute1192); 

            pushFollow(FOLLOW_name_in_intAttribute1195);
            name97=name();

            state._fsp--;

            adaptor.addChild(root_0, name97.getTree());

            // Velvet.g:194:30: ( EQ ! INT )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==EQ) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // Velvet.g:194:31: EQ ! INT
                    {
                    EQ98=(Token)match(input,EQ,FOLLOW_EQ_in_intAttribute1198); 

                    INT99=(Token)match(input,INT,FOLLOW_INT_in_intAttribute1201); 
                    INT99_tree = 
                    (Tree)adaptor.create(INT99)
                    ;
                    adaptor.addChild(root_0, INT99_tree);


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
    // Velvet.g:195:1: floatAttribute : VAR_FLOAT ! name ( EQ ! FLOAT )? ;
    public final VelvetParser.floatAttribute_return floatAttribute() throws RecognitionException {
        VelvetParser.floatAttribute_return retval = new VelvetParser.floatAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_FLOAT100=null;
        Token EQ102=null;
        Token FLOAT103=null;
        VelvetParser.name_return name101 =null;


        Tree VAR_FLOAT100_tree=null;
        Tree EQ102_tree=null;
        Tree FLOAT103_tree=null;

        try {
            // Velvet.g:195:15: ( VAR_FLOAT ! name ( EQ ! FLOAT )? )
            // Velvet.g:195:18: VAR_FLOAT ! name ( EQ ! FLOAT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_FLOAT100=(Token)match(input,VAR_FLOAT,FOLLOW_VAR_FLOAT_in_floatAttribute1210); 

            pushFollow(FOLLOW_name_in_floatAttribute1213);
            name101=name();

            state._fsp--;

            adaptor.addChild(root_0, name101.getTree());

            // Velvet.g:195:34: ( EQ ! FLOAT )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==EQ) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // Velvet.g:195:35: EQ ! FLOAT
                    {
                    EQ102=(Token)match(input,EQ,FOLLOW_EQ_in_floatAttribute1216); 

                    FLOAT103=(Token)match(input,FLOAT,FOLLOW_FLOAT_in_floatAttribute1219); 
                    FLOAT103_tree = 
                    (Tree)adaptor.create(FLOAT103)
                    ;
                    adaptor.addChild(root_0, FLOAT103_tree);


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
    // Velvet.g:196:1: stringAttribute : VAR_STRING ! name ( EQ ! STRING )? ;
    public final VelvetParser.stringAttribute_return stringAttribute() throws RecognitionException {
        VelvetParser.stringAttribute_return retval = new VelvetParser.stringAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_STRING104=null;
        Token EQ106=null;
        Token STRING107=null;
        VelvetParser.name_return name105 =null;


        Tree VAR_STRING104_tree=null;
        Tree EQ106_tree=null;
        Tree STRING107_tree=null;

        try {
            // Velvet.g:196:16: ( VAR_STRING ! name ( EQ ! STRING )? )
            // Velvet.g:196:18: VAR_STRING ! name ( EQ ! STRING )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_STRING104=(Token)match(input,VAR_STRING,FOLLOW_VAR_STRING_in_stringAttribute1227); 

            pushFollow(FOLLOW_name_in_stringAttribute1230);
            name105=name();

            state._fsp--;

            adaptor.addChild(root_0, name105.getTree());

            // Velvet.g:196:35: ( EQ ! STRING )?
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( (LA31_0==EQ) ) {
                alt31=1;
            }
            switch (alt31) {
                case 1 :
                    // Velvet.g:196:36: EQ ! STRING
                    {
                    EQ106=(Token)match(input,EQ,FOLLOW_EQ_in_stringAttribute1233); 

                    STRING107=(Token)match(input,STRING,FOLLOW_STRING_in_stringAttribute1236); 
                    STRING107_tree = 
                    (Tree)adaptor.create(STRING107)
                    ;
                    adaptor.addChild(root_0, STRING107_tree);


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
    // Velvet.g:197:1: boolAttribute : VAR_BOOL ! name ( EQ ! BOOLEAN )? ;
    public final VelvetParser.boolAttribute_return boolAttribute() throws RecognitionException {
        VelvetParser.boolAttribute_return retval = new VelvetParser.boolAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_BOOL108=null;
        Token EQ110=null;
        Token BOOLEAN111=null;
        VelvetParser.name_return name109 =null;


        Tree VAR_BOOL108_tree=null;
        Tree EQ110_tree=null;
        Tree BOOLEAN111_tree=null;

        try {
            // Velvet.g:197:14: ( VAR_BOOL ! name ( EQ ! BOOLEAN )? )
            // Velvet.g:197:17: VAR_BOOL ! name ( EQ ! BOOLEAN )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_BOOL108=(Token)match(input,VAR_BOOL,FOLLOW_VAR_BOOL_in_boolAttribute1245); 

            pushFollow(FOLLOW_name_in_boolAttribute1248);
            name109=name();

            state._fsp--;

            adaptor.addChild(root_0, name109.getTree());

            // Velvet.g:197:32: ( EQ ! BOOLEAN )?
            int alt32=2;
            int LA32_0 = input.LA(1);

            if ( (LA32_0==EQ) ) {
                alt32=1;
            }
            switch (alt32) {
                case 1 :
                    // Velvet.g:197:33: EQ ! BOOLEAN
                    {
                    EQ110=(Token)match(input,EQ,FOLLOW_EQ_in_boolAttribute1251); 

                    BOOLEAN111=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_boolAttribute1254); 
                    BOOLEAN111_tree = 
                    (Tree)adaptor.create(BOOLEAN111)
                    ;
                    adaptor.addChild(root_0, BOOLEAN111_tree);


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
    // Velvet.g:199:1: unaryOp : OP_NOT ;
    public final VelvetParser.unaryOp_return unaryOp() throws RecognitionException {
        VelvetParser.unaryOp_return retval = new VelvetParser.unaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token OP_NOT112=null;

        Tree OP_NOT112_tree=null;

        try {
            // Velvet.g:200:2: ( OP_NOT )
            // Velvet.g:200:4: OP_NOT
            {
            root_0 = (Tree)adaptor.nil();


            OP_NOT112=(Token)match(input,OP_NOT,FOLLOW_OP_NOT_in_unaryOp1266); 
            OP_NOT112_tree = 
            (Tree)adaptor.create(OP_NOT112)
            ;
            adaptor.addChild(root_0, OP_NOT112_tree);


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
    // Velvet.g:203:1: binaryOp : ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT );
    public final VelvetParser.binaryOp_return binaryOp() throws RecognitionException {
        VelvetParser.binaryOp_return retval = new VelvetParser.binaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set113=null;

        Tree set113_tree=null;

        try {
            // Velvet.g:204:2: ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set113=(Token)input.LT(1);

            if ( (input.LA(1) >= OP_AND && input.LA(1) <= OP_IMPLIES)||(input.LA(1) >= OP_OR && input.LA(1) <= OP_XOR) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set113)
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
    // Velvet.g:211:1: attribRelation : ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ );
    public final VelvetParser.attribRelation_return attribRelation() throws RecognitionException {
        VelvetParser.attribRelation_return retval = new VelvetParser.attribRelation_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set114=null;

        Tree set114_tree=null;

        try {
            // Velvet.g:212:2: ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set114=(Token)input.LT(1);

            if ( input.LA(1)==ATTR_OP_EQUALS||input.LA(1)==ATTR_OP_GREATER_EQ||input.LA(1)==ATTR_OP_LESS_EQ ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set114)
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


 

    public static final BitSet FOLLOW_imports_in_velvetModel451 = new BitSet(new long[]{0x0008004000020000L});
    public static final BitSet FOLLOW_concept_in_velvetModel455 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_interfaceg_in_velvetModel457 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_velvetModel460 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IMPORT_in_imports472 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_imports474 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_SEMI_in_imports476 = new BitSet(new long[]{0x0000000400000002L});
    public static final BitSet FOLLOW_REFINES_in_concept501 = new BitSet(new long[]{0x0000000000020000L});
    public static final BitSet FOLLOW_CONCEPT_in_concept504 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_concept506 = new BitSet(new long[]{0x00C0000000008000L});
    public static final BitSet FOLLOW_COLON_in_concept510 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_conceptBaseExt_in_concept512 = new BitSet(new long[]{0x00C0000000000000L});
    public static final BitSet FOLLOW_START_R_in_concept520 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_conceptInterExt_in_concept522 = new BitSet(new long[]{0x0000000000410000L});
    public static final BitSet FOLLOW_COMMA_in_concept525 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_conceptInterExt_in_concept527 = new BitSet(new long[]{0x0000000000410000L});
    public static final BitSet FOLLOW_END_R_in_concept531 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_definitions_in_concept538 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt568 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_COMMA_in_conceptBaseExt571 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt573 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_interfaceclass_in_conceptInterExt597 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_conceptInterExt599 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_interfaceclass609 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_REFINES_in_interfaceg619 = new BitSet(new long[]{0x0000004000000000L});
    public static final BitSet FOLLOW_INTERFACEG_in_interfaceg622 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_interfaceg624 = new BitSet(new long[]{0x0040000000008000L});
    public static final BitSet FOLLOW_COLON_in_interfaceg628 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_interfaceBaseExt_in_interfaceg630 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_definitions_in_interfaceg634 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt664 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_COMMA_in_interfaceBaseExt667 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt669 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_START_C_in_definitions709 = new BitSet(new long[]{0x7820048088280010L});
    public static final BitSet FOLLOW_def_in_definitions711 = new BitSet(new long[]{0x0000000000200000L});
    public static final BitSet FOLLOW_END_C_in_definitions713 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def732 = new BitSet(new long[]{0x7820048088080012L});
    public static final BitSet FOLLOW_featureGroup_in_def740 = new BitSet(new long[]{0x7800000080080002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def742 = new BitSet(new long[]{0x7800000080080002L});
    public static final BitSet FOLLOW_feature_in_def751 = new BitSet(new long[]{0x7800008088080012L});
    public static final BitSet FOLLOW_feature_in_def754 = new BitSet(new long[]{0x7800008088080012L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def758 = new BitSet(new long[]{0x7800008088080012L});
    public static final BitSet FOLLOW_constraint_in_nonFeatureDefinition778 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_instance_in_nonFeatureDefinition784 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribute_in_nonFeatureDefinition790 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_instance801 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_instance803 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_SEMI_in_instance805 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANDATORY_in_feature827 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature829 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature833 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature835 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature839 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature843 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_FEATURE_in_feature850 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_feature852 = new BitSet(new long[]{0x0050000000000000L});
    public static final BitSet FOLLOW_definitions_in_feature855 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SEMI_in_feature859 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_groupType_in_featureGroup890 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_START_C_in_featureGroup892 = new BitSet(new long[]{0x0000008008000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup894 = new BitSet(new long[]{0x0000008008000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup896 = new BitSet(new long[]{0x0000008008200010L});
    public static final BitSet FOLLOW_END_C_in_featureGroup899 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONSTRAINT_in_constraint942 = new BitSet(new long[]{0x0080801180000000L});
    public static final BitSet FOLLOW_ID_in_constraint946 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_EQ_in_constraint948 = new BitSet(new long[]{0x0080801180000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraint954 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_attributeConstraint_in_constraint958 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_SEMI_in_constraint961 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition974 = new BitSet(new long[]{0x0003700000000002L});
    public static final BitSet FOLLOW_binaryOp_in_constraintDefinition977 = new BitSet(new long[]{0x0080800180000000L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition979 = new BitSet(new long[]{0x0003700000000002L});
    public static final BitSet FOLLOW_unaryOp_in_constraintOperand1006 = new BitSet(new long[]{0x0080800180000000L});
    public static final BitSet FOLLOW_START_R_in_constraintOperand1010 = new BitSet(new long[]{0x0080800180000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraintOperand1012 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_END_R_in_constraintOperand1014 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_constraintOperand1018 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribConstraint_in_attributeConstraint1053 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1073 = new BitSet(new long[]{0x0004010000000A80L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1076 = new BitSet(new long[]{0x0000001180000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1078 = new BitSet(new long[]{0x0004010000000A80L});
    public static final BitSet FOLLOW_attribRelation_in_attribConstraint1086 = new BitSet(new long[]{0x0000001180000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1092 = new BitSet(new long[]{0x0004010000000002L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1095 = new BitSet(new long[]{0x0000001180000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1097 = new BitSet(new long[]{0x0004010000000002L});
    public static final BitSet FOLLOW_INT_in_attribNumInstance1129 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_attribNumInstance1136 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_intAttribute_in_attribute1148 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_floatAttribute_in_attribute1152 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_stringAttribute_in_attribute1156 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_boolAttribute_in_attribute1160 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_SEMI_in_attribute1163 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_INT_in_intAttribute1192 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_intAttribute1195 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_EQ_in_intAttribute1198 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_intAttribute1201 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_FLOAT_in_floatAttribute1210 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_floatAttribute1213 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_EQ_in_floatAttribute1216 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_FLOAT_in_floatAttribute1219 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_STRING_in_stringAttribute1227 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_stringAttribute1230 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_EQ_in_stringAttribute1233 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_STRING_in_stringAttribute1236 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_BOOL_in_boolAttribute1245 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_boolAttribute1248 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_EQ_in_boolAttribute1251 = new BitSet(new long[]{0x0000000000004000L});
    public static final BitSet FOLLOW_BOOLEAN_in_boolAttribute1254 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_OP_NOT_in_unaryOp1266 = new BitSet(new long[]{0x0000000000000002L});

}