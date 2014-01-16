// $ANTLR 3.4 Velvet.g 2014-01-15 21:44:56

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
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "ABSTRACT", "ACONSTR", "ATTR", "ATTR_OP_EQUALS", "ATTR_OP_GREATER", "ATTR_OP_GREATER_EQ", "ATTR_OP_LESS", "ATTR_OP_LESS_EQ", "ATTR_OP_NOT_EQUALS", "BASEEXT", "BASEPARAM", "BOOLEAN", "CINTERFACE", "COLON", "COMMA", "CONCEPT", "CONSTR", "CONSTRAINT", "DEF", "END_C", "END_R", "EQ", "ESC_SEQ", "EXPONENT", "FEAT", "FEATURE", "FLOAT", "GROUP", "HEX_DIGIT", "ID", "IDPath", "IMP", "IMPL", "IMPLEMENT", "IMPORT", "INSTANCE", "INSTANCEDEF", "INT", "INTER", "MANDATORY", "MINUS", "OCTAL_ESC", "ONEOF", "OPERAND", "OP_AND", "OP_EQUIVALENT", "OP_IMPLIES", "OP_NOT", "OP_OR", "OP_XOR", "PLUS", "REFINES", "SEMI", "SOMEOF", "START_C", "START_R", "STRING", "UNARYOP", "UNICODE_ESC", "VAR_BOOL", "VAR_FLOAT", "VAR_INT", "VAR_STRING", "WS"
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
    public static final int IMPL=36;
    public static final int IMPLEMENT=37;
    public static final int IMPORT=38;
    public static final int INSTANCE=39;
    public static final int INSTANCEDEF=40;
    public static final int INT=41;
    public static final int INTER=42;
    public static final int MANDATORY=43;
    public static final int MINUS=44;
    public static final int OCTAL_ESC=45;
    public static final int ONEOF=46;
    public static final int OPERAND=47;
    public static final int OP_AND=48;
    public static final int OP_EQUIVALENT=49;
    public static final int OP_IMPLIES=50;
    public static final int OP_NOT=51;
    public static final int OP_OR=52;
    public static final int OP_XOR=53;
    public static final int PLUS=54;
    public static final int REFINES=55;
    public static final int SEMI=56;
    public static final int SOMEOF=57;
    public static final int START_C=58;
    public static final int START_R=59;
    public static final int STRING=60;
    public static final int UNARYOP=61;
    public static final int UNICODE_ESC=62;
    public static final int VAR_BOOL=63;
    public static final int VAR_FLOAT=64;
    public static final int VAR_INT=65;
    public static final int VAR_STRING=66;
    public static final int WS=67;

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
    // Velvet.g:82:1: velvetModel : ( imports )? ( instancedef )* ( concept | cinterface ) EOF ;
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
            // Velvet.g:83:2: ( ( imports )? ( instancedef )* ( concept | cinterface ) EOF )
            // Velvet.g:83:4: ( imports )? ( instancedef )* ( concept | cinterface ) EOF
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:83:4: ( imports )?
            int alt1=2;
            int LA1_0 = input.LA(1);

            if ( (LA1_0==IMPORT) ) {
                alt1=1;
            }
            switch (alt1) {
                case 1 :
                    // Velvet.g:83:4: imports
                    {
                    pushFollow(FOLLOW_imports_in_velvetModel471);
                    imports1=imports();

                    state._fsp--;

                    adaptor.addChild(root_0, imports1.getTree());

                    }
                    break;

            }


            // Velvet.g:83:13: ( instancedef )*
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( (LA2_0==ID) ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // Velvet.g:83:13: instancedef
            	    {
            	    pushFollow(FOLLOW_instancedef_in_velvetModel474);
            	    instancedef2=instancedef();

            	    state._fsp--;

            	    adaptor.addChild(root_0, instancedef2.getTree());

            	    }
            	    break;

            	default :
            	    break loop2;
                }
            } while (true);


            // Velvet.g:83:26: ( concept | cinterface )
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
                    // Velvet.g:83:27: concept
                    {
                    pushFollow(FOLLOW_concept_in_velvetModel478);
                    concept3=concept();

                    state._fsp--;

                    adaptor.addChild(root_0, concept3.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:83:35: cinterface
                    {
                    pushFollow(FOLLOW_cinterface_in_velvetModel480);
                    cinterface4=cinterface();

                    state._fsp--;

                    adaptor.addChild(root_0, cinterface4.getTree());

                    }
                    break;

            }


            EOF5=(Token)match(input,EOF,FOLLOW_EOF_in_velvetModel483); 
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
    // Velvet.g:86:1: instancedef : ID name SEMI -> ^( INSTANCEDEF ID name ) ;
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
            // Velvet.g:87:2: ( ID name SEMI -> ^( INSTANCEDEF ID name ) )
            // Velvet.g:87:4: ID name SEMI
            {
            ID6=(Token)match(input,ID,FOLLOW_ID_in_instancedef495);  
            stream_ID.add(ID6);


            pushFollow(FOLLOW_name_in_instancedef497);
            name7=name();

            state._fsp--;

            stream_name.add(name7.getTree());

            SEMI8=(Token)match(input,SEMI,FOLLOW_SEMI_in_instancedef499);  
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
            // 88:2: -> ^( INSTANCEDEF ID name )
            {
                // Velvet.g:88:5: ^( INSTANCEDEF ID name )
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
    // Velvet.g:91:1: imports : ( IMPORT name SEMI )+ -> ^( IMP ( name )+ ) ;
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
            // Velvet.g:91:9: ( ( IMPORT name SEMI )+ -> ^( IMP ( name )+ ) )
            // Velvet.g:91:11: ( IMPORT name SEMI )+
            {
            // Velvet.g:91:11: ( IMPORT name SEMI )+
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
            	    // Velvet.g:91:12: IMPORT name SEMI
            	    {
            	    IMPORT9=(Token)match(input,IMPORT,FOLLOW_IMPORT_in_imports521);  
            	    stream_IMPORT.add(IMPORT9);


            	    pushFollow(FOLLOW_name_in_imports523);
            	    name10=name();

            	    state._fsp--;

            	    stream_name.add(name10.getTree());

            	    SEMI11=(Token)match(input,SEMI,FOLLOW_SEMI_in_imports525);  
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
            // 92:2: -> ^( IMP ( name )+ )
            {
                // Velvet.g:92:5: ^( IMP ( name )+ )
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
    // Velvet.g:95:1: concept : ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )? ( IMPL implExt )? definitions -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? ( conceptInterExt )* ( implExt )? definitions ) ;
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
        Token IMPL22=null;
        VelvetParser.conceptBaseExt_return conceptBaseExt16 =null;

        VelvetParser.conceptInterExt_return conceptInterExt18 =null;

        VelvetParser.conceptInterExt_return conceptInterExt20 =null;

        VelvetParser.implExt_return implExt23 =null;

        VelvetParser.definitions_return definitions24 =null;


        Tree REFINES12_tree=null;
        Tree CONCEPT13_tree=null;
        Tree ID14_tree=null;
        Tree COLON15_tree=null;
        Tree START_R17_tree=null;
        Tree COMMA19_tree=null;
        Tree END_R21_tree=null;
        Tree IMPL22_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_END_R=new RewriteRuleTokenStream(adaptor,"token END_R");
        RewriteRuleTokenStream stream_REFINES=new RewriteRuleTokenStream(adaptor,"token REFINES");
        RewriteRuleTokenStream stream_IMPL=new RewriteRuleTokenStream(adaptor,"token IMPL");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
        RewriteRuleTokenStream stream_START_R=new RewriteRuleTokenStream(adaptor,"token START_R");
        RewriteRuleTokenStream stream_CONCEPT=new RewriteRuleTokenStream(adaptor,"token CONCEPT");
        RewriteRuleSubtreeStream stream_conceptInterExt=new RewriteRuleSubtreeStream(adaptor,"rule conceptInterExt");
        RewriteRuleSubtreeStream stream_conceptBaseExt=new RewriteRuleSubtreeStream(adaptor,"rule conceptBaseExt");
        RewriteRuleSubtreeStream stream_implExt=new RewriteRuleSubtreeStream(adaptor,"rule implExt");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:96:2: ( ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )? ( IMPL implExt )? definitions -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? ( conceptInterExt )* ( implExt )? definitions ) )
            // Velvet.g:96:4: ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )? ( IMPL implExt )? definitions
            {
            // Velvet.g:96:4: ( REFINES )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==REFINES) ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // Velvet.g:96:4: REFINES
                    {
                    REFINES12=(Token)match(input,REFINES,FOLLOW_REFINES_in_concept550);  
                    stream_REFINES.add(REFINES12);


                    }
                    break;

            }


            CONCEPT13=(Token)match(input,CONCEPT,FOLLOW_CONCEPT_in_concept553);  
            stream_CONCEPT.add(CONCEPT13);


            ID14=(Token)match(input,ID,FOLLOW_ID_in_concept555);  
            stream_ID.add(ID14);


            // Velvet.g:97:3: ( COLON conceptBaseExt )?
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==COLON) ) {
                alt6=1;
            }
            switch (alt6) {
                case 1 :
                    // Velvet.g:97:4: COLON conceptBaseExt
                    {
                    COLON15=(Token)match(input,COLON,FOLLOW_COLON_in_concept562);  
                    stream_COLON.add(COLON15);


                    pushFollow(FOLLOW_conceptBaseExt_in_concept564);
                    conceptBaseExt16=conceptBaseExt();

                    state._fsp--;

                    stream_conceptBaseExt.add(conceptBaseExt16.getTree());

                    }
                    break;

            }


            // Velvet.g:98:3: ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )?
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==START_R) ) {
                alt8=1;
            }
            switch (alt8) {
                case 1 :
                    // Velvet.g:98:4: START_R conceptInterExt ( COMMA conceptInterExt )* END_R
                    {
                    START_R17=(Token)match(input,START_R,FOLLOW_START_R_in_concept572);  
                    stream_START_R.add(START_R17);


                    pushFollow(FOLLOW_conceptInterExt_in_concept574);
                    conceptInterExt18=conceptInterExt();

                    state._fsp--;

                    stream_conceptInterExt.add(conceptInterExt18.getTree());

                    // Velvet.g:98:28: ( COMMA conceptInterExt )*
                    loop7:
                    do {
                        int alt7=2;
                        int LA7_0 = input.LA(1);

                        if ( (LA7_0==COMMA) ) {
                            alt7=1;
                        }


                        switch (alt7) {
                    	case 1 :
                    	    // Velvet.g:98:29: COMMA conceptInterExt
                    	    {
                    	    COMMA19=(Token)match(input,COMMA,FOLLOW_COMMA_in_concept577);  
                    	    stream_COMMA.add(COMMA19);


                    	    pushFollow(FOLLOW_conceptInterExt_in_concept579);
                    	    conceptInterExt20=conceptInterExt();

                    	    state._fsp--;

                    	    stream_conceptInterExt.add(conceptInterExt20.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop7;
                        }
                    } while (true);


                    END_R21=(Token)match(input,END_R,FOLLOW_END_R_in_concept583);  
                    stream_END_R.add(END_R21);


                    }
                    break;

            }


            // Velvet.g:99:3: ( IMPL implExt )?
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==IMPL) ) {
                alt9=1;
            }
            switch (alt9) {
                case 1 :
                    // Velvet.g:99:4: IMPL implExt
                    {
                    IMPL22=(Token)match(input,IMPL,FOLLOW_IMPL_in_concept591);  
                    stream_IMPL.add(IMPL22);


                    pushFollow(FOLLOW_implExt_in_concept593);
                    implExt23=implExt();

                    state._fsp--;

                    stream_implExt.add(implExt23.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_concept600);
            definitions24=definitions();

            state._fsp--;

            stream_definitions.add(definitions24.getTree());

            // AST REWRITE
            // elements: ID, REFINES, CONCEPT, conceptInterExt, definitions, conceptBaseExt, implExt
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 101:2: -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? ( conceptInterExt )* ( implExt )? definitions )
            {
                // Velvet.g:101:5: ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? ( conceptInterExt )* ( implExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CONCEPT.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:101:18: ( REFINES )?
                if ( stream_REFINES.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_REFINES.nextNode()
                    );

                }
                stream_REFINES.reset();

                // Velvet.g:101:27: ( conceptBaseExt )?
                if ( stream_conceptBaseExt.hasNext() ) {
                    adaptor.addChild(root_1, stream_conceptBaseExt.nextTree());

                }
                stream_conceptBaseExt.reset();

                // Velvet.g:101:43: ( conceptInterExt )*
                while ( stream_conceptInterExt.hasNext() ) {
                    adaptor.addChild(root_1, stream_conceptInterExt.nextTree());

                }
                stream_conceptInterExt.reset();

                // Velvet.g:101:60: ( implExt )?
                if ( stream_implExt.hasNext() ) {
                    adaptor.addChild(root_1, stream_implExt.nextTree());

                }
                stream_implExt.reset();

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


    public static class implExt_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "implExt"
    // Velvet.g:104:1: implExt : ID -> ^( IMPLEMENT ID ) ;
    public final VelvetParser.implExt_return implExt() throws RecognitionException {
        VelvetParser.implExt_return retval = new VelvetParser.implExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID25=null;

        Tree ID25_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");

        try {
            // Velvet.g:104:9: ( ID -> ^( IMPLEMENT ID ) )
            // Velvet.g:104:11: ID
            {
            ID25=(Token)match(input,ID,FOLLOW_ID_in_implExt635);  
            stream_ID.add(ID25);


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
            // 105:2: -> ^( IMPLEMENT ID )
            {
                // Velvet.g:105:5: ^( IMPLEMENT ID )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(IMPLEMENT, "IMPLEMENT")
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

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
    // $ANTLR end "implExt"


    public static class conceptBaseExt_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "conceptBaseExt"
    // Velvet.g:108:1: conceptBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
    public final VelvetParser.conceptBaseExt_return conceptBaseExt() throws RecognitionException {
        VelvetParser.conceptBaseExt_return retval = new VelvetParser.conceptBaseExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID26=null;
        Token COMMA27=null;
        Token ID28=null;

        Tree ID26_tree=null;
        Tree COMMA27_tree=null;
        Tree ID28_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

        try {
            // Velvet.g:109:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:109:4: ID ( COMMA ID )*
            {
            ID26=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt655);  
            stream_ID.add(ID26);


            // Velvet.g:109:7: ( COMMA ID )*
            loop10:
            do {
                int alt10=2;
                int LA10_0 = input.LA(1);

                if ( (LA10_0==COMMA) ) {
                    alt10=1;
                }


                switch (alt10) {
            	case 1 :
            	    // Velvet.g:109:8: COMMA ID
            	    {
            	    COMMA27=(Token)match(input,COMMA,FOLLOW_COMMA_in_conceptBaseExt658);  
            	    stream_COMMA.add(COMMA27);


            	    ID28=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt660);  
            	    stream_ID.add(ID28);


            	    }
            	    break;

            	default :
            	    break loop10;
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
            // 110:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:110:5: ^( BASEEXT ( ID )+ )
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
    // Velvet.g:113:1: conceptInterExt : ID name -> ^( BASEPARAM ID name ) ;
    public final VelvetParser.conceptInterExt_return conceptInterExt() throws RecognitionException {
        VelvetParser.conceptInterExt_return retval = new VelvetParser.conceptInterExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID29=null;
        VelvetParser.name_return name30 =null;


        Tree ID29_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:114:2: ( ID name -> ^( BASEPARAM ID name ) )
            // Velvet.g:114:4: ID name
            {
            ID29=(Token)match(input,ID,FOLLOW_ID_in_conceptInterExt684);  
            stream_ID.add(ID29);


            pushFollow(FOLLOW_name_in_conceptInterExt686);
            name30=name();

            state._fsp--;

            stream_name.add(name30.getTree());

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
            // 115:2: -> ^( BASEPARAM ID name )
            {
                // Velvet.g:115:5: ^( BASEPARAM ID name )
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
    // Velvet.g:119:1: cinterface : ( REFINES )? CINTERFACE ID ( COLON interfaceBaseExt )? definitions -> ^( CINTERFACE ID ( REFINES )? ( interfaceBaseExt )? definitions ) ;
    public final VelvetParser.cinterface_return cinterface() throws RecognitionException {
        VelvetParser.cinterface_return retval = new VelvetParser.cinterface_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token REFINES31=null;
        Token CINTERFACE32=null;
        Token ID33=null;
        Token COLON34=null;
        VelvetParser.interfaceBaseExt_return interfaceBaseExt35 =null;

        VelvetParser.definitions_return definitions36 =null;


        Tree REFINES31_tree=null;
        Tree CINTERFACE32_tree=null;
        Tree ID33_tree=null;
        Tree COLON34_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_REFINES=new RewriteRuleTokenStream(adaptor,"token REFINES");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_CINTERFACE=new RewriteRuleTokenStream(adaptor,"token CINTERFACE");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        RewriteRuleSubtreeStream stream_interfaceBaseExt=new RewriteRuleSubtreeStream(adaptor,"rule interfaceBaseExt");
        try {
            // Velvet.g:119:12: ( ( REFINES )? CINTERFACE ID ( COLON interfaceBaseExt )? definitions -> ^( CINTERFACE ID ( REFINES )? ( interfaceBaseExt )? definitions ) )
            // Velvet.g:119:14: ( REFINES )? CINTERFACE ID ( COLON interfaceBaseExt )? definitions
            {
            // Velvet.g:119:14: ( REFINES )?
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==REFINES) ) {
                alt11=1;
            }
            switch (alt11) {
                case 1 :
                    // Velvet.g:119:14: REFINES
                    {
                    REFINES31=(Token)match(input,REFINES,FOLLOW_REFINES_in_cinterface708);  
                    stream_REFINES.add(REFINES31);


                    }
                    break;

            }


            CINTERFACE32=(Token)match(input,CINTERFACE,FOLLOW_CINTERFACE_in_cinterface711);  
            stream_CINTERFACE.add(CINTERFACE32);


            ID33=(Token)match(input,ID,FOLLOW_ID_in_cinterface713);  
            stream_ID.add(ID33);


            // Velvet.g:119:38: ( COLON interfaceBaseExt )?
            int alt12=2;
            int LA12_0 = input.LA(1);

            if ( (LA12_0==COLON) ) {
                alt12=1;
            }
            switch (alt12) {
                case 1 :
                    // Velvet.g:119:39: COLON interfaceBaseExt
                    {
                    COLON34=(Token)match(input,COLON,FOLLOW_COLON_in_cinterface717);  
                    stream_COLON.add(COLON34);


                    pushFollow(FOLLOW_interfaceBaseExt_in_cinterface719);
                    interfaceBaseExt35=interfaceBaseExt();

                    state._fsp--;

                    stream_interfaceBaseExt.add(interfaceBaseExt35.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_cinterface723);
            definitions36=definitions();

            state._fsp--;

            stream_definitions.add(definitions36.getTree());

            // AST REWRITE
            // elements: definitions, REFINES, ID, CINTERFACE, interfaceBaseExt
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 120:2: -> ^( CINTERFACE ID ( REFINES )? ( interfaceBaseExt )? definitions )
            {
                // Velvet.g:120:5: ^( CINTERFACE ID ( REFINES )? ( interfaceBaseExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CINTERFACE.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:120:21: ( REFINES )?
                if ( stream_REFINES.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_REFINES.nextNode()
                    );

                }
                stream_REFINES.reset();

                // Velvet.g:120:30: ( interfaceBaseExt )?
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
    // Velvet.g:123:1: interfaceBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
    public final VelvetParser.interfaceBaseExt_return interfaceBaseExt() throws RecognitionException {
        VelvetParser.interfaceBaseExt_return retval = new VelvetParser.interfaceBaseExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID37=null;
        Token COMMA38=null;
        Token ID39=null;

        Tree ID37_tree=null;
        Tree COMMA38_tree=null;
        Tree ID39_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

        try {
            // Velvet.g:124:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:124:4: ID ( COMMA ID )*
            {
            ID37=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt753);  
            stream_ID.add(ID37);


            // Velvet.g:124:7: ( COMMA ID )*
            loop13:
            do {
                int alt13=2;
                int LA13_0 = input.LA(1);

                if ( (LA13_0==COMMA) ) {
                    alt13=1;
                }


                switch (alt13) {
            	case 1 :
            	    // Velvet.g:124:8: COMMA ID
            	    {
            	    COMMA38=(Token)match(input,COMMA,FOLLOW_COMMA_in_interfaceBaseExt756);  
            	    stream_COMMA.add(COMMA38);


            	    ID39=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt758);  
            	    stream_ID.add(ID39);


            	    }
            	    break;

            	default :
            	    break loop13;
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
            // 125:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:125:5: ^( BASEEXT ( ID )+ )
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
    // Velvet.g:128:1: name : ( ID | IDPath );
    public final VelvetParser.name_return name() throws RecognitionException {
        VelvetParser.name_return retval = new VelvetParser.name_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set40=null;

        Tree set40_tree=null;

        try {
            // Velvet.g:128:5: ( ID | IDPath )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set40=(Token)input.LT(1);

            if ( (input.LA(1) >= ID && input.LA(1) <= IDPath) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set40)
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
    // Velvet.g:132:1: definitions : START_C def END_C -> ^( DEF def ) ;
    public final VelvetParser.definitions_return definitions() throws RecognitionException {
        VelvetParser.definitions_return retval = new VelvetParser.definitions_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C41=null;
        Token END_C43=null;
        VelvetParser.def_return def42 =null;


        Tree START_C41_tree=null;
        Tree END_C43_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_def=new RewriteRuleSubtreeStream(adaptor,"rule def");
        try {
            // Velvet.g:133:2: ( START_C def END_C -> ^( DEF def ) )
            // Velvet.g:133:4: START_C def END_C
            {
            START_C41=(Token)match(input,START_C,FOLLOW_START_C_in_definitions798);  
            stream_START_C.add(START_C41);


            pushFollow(FOLLOW_def_in_definitions800);
            def42=def();

            state._fsp--;

            stream_def.add(def42.getTree());

            END_C43=(Token)match(input,END_C,FOLLOW_END_C_in_definitions802);  
            stream_END_C.add(END_C43);


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
            // 134:2: -> ^( DEF def )
            {
                // Velvet.g:134:5: ^( DEF def )
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
    // Velvet.g:137:1: def : ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? ;
    public final VelvetParser.def_return def() throws RecognitionException {
        VelvetParser.def_return retval = new VelvetParser.def_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition44 =null;

        VelvetParser.featureGroup_return featureGroup45 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition46 =null;

        VelvetParser.feature_return feature47 =null;

        VelvetParser.feature_return feature48 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition49 =null;



        try {
            // Velvet.g:137:5: ( ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? )
            // Velvet.g:137:7: ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:137:7: ( nonFeatureDefinition )*
            loop14:
            do {
                int alt14=2;
                int LA14_0 = input.LA(1);

                if ( (LA14_0==CONSTRAINT||LA14_0==ID||(LA14_0 >= VAR_BOOL && LA14_0 <= VAR_STRING)) ) {
                    alt14=1;
                }


                switch (alt14) {
            	case 1 :
            	    // Velvet.g:137:7: nonFeatureDefinition
            	    {
            	    pushFollow(FOLLOW_nonFeatureDefinition_in_def821);
            	    nonFeatureDefinition44=nonFeatureDefinition();

            	    state._fsp--;

            	    adaptor.addChild(root_0, nonFeatureDefinition44.getTree());

            	    }
            	    break;

            	default :
            	    break loop14;
                }
            } while (true);


            // Velvet.g:137:29: ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            int alt17=3;
            int LA17_0 = input.LA(1);

            if ( (LA17_0==ONEOF||LA17_0==SOMEOF) ) {
                alt17=1;
            }
            else if ( (LA17_0==ABSTRACT||LA17_0==FEATURE||LA17_0==MANDATORY) ) {
                alt17=2;
            }
            switch (alt17) {
                case 1 :
                    // Velvet.g:138:3: ( featureGroup ( nonFeatureDefinition )* )
                    {
                    // Velvet.g:138:3: ( featureGroup ( nonFeatureDefinition )* )
                    // Velvet.g:138:4: featureGroup ( nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_featureGroup_in_def829);
                    featureGroup45=featureGroup();

                    state._fsp--;

                    adaptor.addChild(root_0, featureGroup45.getTree());

                    // Velvet.g:138:17: ( nonFeatureDefinition )*
                    loop15:
                    do {
                        int alt15=2;
                        int LA15_0 = input.LA(1);

                        if ( (LA15_0==CONSTRAINT||LA15_0==ID||(LA15_0 >= VAR_BOOL && LA15_0 <= VAR_STRING)) ) {
                            alt15=1;
                        }


                        switch (alt15) {
                    	case 1 :
                    	    // Velvet.g:138:17: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def831);
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
                case 2 :
                    // Velvet.g:139:3: ( feature ( feature | nonFeatureDefinition )* )
                    {
                    // Velvet.g:139:3: ( feature ( feature | nonFeatureDefinition )* )
                    // Velvet.g:139:4: feature ( feature | nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_feature_in_def840);
                    feature47=feature();

                    state._fsp--;

                    adaptor.addChild(root_0, feature47.getTree());

                    // Velvet.g:139:12: ( feature | nonFeatureDefinition )*
                    loop16:
                    do {
                        int alt16=3;
                        int LA16_0 = input.LA(1);

                        if ( (LA16_0==ABSTRACT||LA16_0==FEATURE||LA16_0==MANDATORY) ) {
                            alt16=1;
                        }
                        else if ( (LA16_0==CONSTRAINT||LA16_0==ID||(LA16_0 >= VAR_BOOL && LA16_0 <= VAR_STRING)) ) {
                            alt16=2;
                        }


                        switch (alt16) {
                    	case 1 :
                    	    // Velvet.g:139:13: feature
                    	    {
                    	    pushFollow(FOLLOW_feature_in_def843);
                    	    feature48=feature();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, feature48.getTree());

                    	    }
                    	    break;
                    	case 2 :
                    	    // Velvet.g:139:23: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def847);
                    	    nonFeatureDefinition49=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition49.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop16;
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
    // Velvet.g:142:1: nonFeatureDefinition : ( constraint | instance | attribute );
    public final VelvetParser.nonFeatureDefinition_return nonFeatureDefinition() throws RecognitionException {
        VelvetParser.nonFeatureDefinition_return retval = new VelvetParser.nonFeatureDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraint_return constraint50 =null;

        VelvetParser.instance_return instance51 =null;

        VelvetParser.attribute_return attribute52 =null;



        try {
            // Velvet.g:143:2: ( constraint | instance | attribute )
            int alt18=3;
            switch ( input.LA(1) ) {
            case CONSTRAINT:
                {
                alt18=1;
                }
                break;
            case ID:
                {
                alt18=2;
                }
                break;
            case VAR_BOOL:
            case VAR_FLOAT:
            case VAR_INT:
            case VAR_STRING:
                {
                alt18=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 18, 0, input);

                throw nvae;

            }

            switch (alt18) {
                case 1 :
                    // Velvet.g:143:4: constraint
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_constraint_in_nonFeatureDefinition867);
                    constraint50=constraint();

                    state._fsp--;

                    adaptor.addChild(root_0, constraint50.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:144:4: instance
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_instance_in_nonFeatureDefinition873);
                    instance51=instance();

                    state._fsp--;

                    adaptor.addChild(root_0, instance51.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:145:4: attribute
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_attribute_in_nonFeatureDefinition879);
                    attribute52=attribute();

                    state._fsp--;

                    adaptor.addChild(root_0, attribute52.getTree());

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
    // Velvet.g:148:1: instance : ID name SEMI -> ^( INSTANCE ID name ) ;
    public final VelvetParser.instance_return instance() throws RecognitionException {
        VelvetParser.instance_return retval = new VelvetParser.instance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID53=null;
        Token SEMI55=null;
        VelvetParser.name_return name54 =null;


        Tree ID53_tree=null;
        Tree SEMI55_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:148:9: ( ID name SEMI -> ^( INSTANCE ID name ) )
            // Velvet.g:148:11: ID name SEMI
            {
            ID53=(Token)match(input,ID,FOLLOW_ID_in_instance890);  
            stream_ID.add(ID53);


            pushFollow(FOLLOW_name_in_instance892);
            name54=name();

            state._fsp--;

            stream_name.add(name54.getTree());

            SEMI55=(Token)match(input,SEMI,FOLLOW_SEMI_in_instance894);  
            stream_SEMI.add(SEMI55);


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
            // 149:2: -> ^( INSTANCE ID name )
            {
                // Velvet.g:149:5: ^( INSTANCE ID name )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(INSTANCE, "INSTANCE")
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
    // $ANTLR end "instance"


    public static class feature_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "feature"
    // Velvet.g:152:1: feature : ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) ;
    public final VelvetParser.feature_return feature() throws RecognitionException {
        VelvetParser.feature_return retval = new VelvetParser.feature_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token MANDATORY56=null;
        Token ABSTRACT57=null;
        Token ABSTRACT58=null;
        Token MANDATORY59=null;
        Token MANDATORY60=null;
        Token ABSTRACT61=null;
        Token FEATURE62=null;
        Token SEMI65=null;
        VelvetParser.name_return name63 =null;

        VelvetParser.definitions_return definitions64 =null;


        Tree MANDATORY56_tree=null;
        Tree ABSTRACT57_tree=null;
        Tree ABSTRACT58_tree=null;
        Tree MANDATORY59_tree=null;
        Tree MANDATORY60_tree=null;
        Tree ABSTRACT61_tree=null;
        Tree FEATURE62_tree=null;
        Tree SEMI65_tree=null;
        RewriteRuleTokenStream stream_ABSTRACT=new RewriteRuleTokenStream(adaptor,"token ABSTRACT");
        RewriteRuleTokenStream stream_MANDATORY=new RewriteRuleTokenStream(adaptor,"token MANDATORY");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleTokenStream stream_FEATURE=new RewriteRuleTokenStream(adaptor,"token FEATURE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:153:2: ( ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) )
            // Velvet.g:153:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI )
            {
            // Velvet.g:153:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )?
            int alt19=5;
            int LA19_0 = input.LA(1);

            if ( (LA19_0==MANDATORY) ) {
                int LA19_1 = input.LA(2);

                if ( (LA19_1==ABSTRACT) ) {
                    alt19=1;
                }
                else if ( (LA19_1==FEATURE) ) {
                    alt19=3;
                }
            }
            else if ( (LA19_0==ABSTRACT) ) {
                int LA19_2 = input.LA(2);

                if ( (LA19_2==MANDATORY) ) {
                    alt19=2;
                }
                else if ( (LA19_2==FEATURE) ) {
                    alt19=4;
                }
            }
            switch (alt19) {
                case 1 :
                    // Velvet.g:153:5: MANDATORY ABSTRACT
                    {
                    MANDATORY56=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature918);  
                    stream_MANDATORY.add(MANDATORY56);


                    ABSTRACT57=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature920);  
                    stream_ABSTRACT.add(ABSTRACT57);


                    }
                    break;
                case 2 :
                    // Velvet.g:153:26: ABSTRACT MANDATORY
                    {
                    ABSTRACT58=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature924);  
                    stream_ABSTRACT.add(ABSTRACT58);


                    MANDATORY59=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature926);  
                    stream_MANDATORY.add(MANDATORY59);


                    }
                    break;
                case 3 :
                    // Velvet.g:153:47: MANDATORY
                    {
                    MANDATORY60=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature930);  
                    stream_MANDATORY.add(MANDATORY60);


                    }
                    break;
                case 4 :
                    // Velvet.g:153:59: ABSTRACT
                    {
                    ABSTRACT61=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature934);  
                    stream_ABSTRACT.add(ABSTRACT61);


                    }
                    break;

            }


            FEATURE62=(Token)match(input,FEATURE,FOLLOW_FEATURE_in_feature941);  
            stream_FEATURE.add(FEATURE62);


            pushFollow(FOLLOW_name_in_feature943);
            name63=name();

            state._fsp--;

            stream_name.add(name63.getTree());

            // Velvet.g:154:17: ( definitions | SEMI )
            int alt20=2;
            int LA20_0 = input.LA(1);

            if ( (LA20_0==START_C) ) {
                alt20=1;
            }
            else if ( (LA20_0==SEMI) ) {
                alt20=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 20, 0, input);

                throw nvae;

            }
            switch (alt20) {
                case 1 :
                    // Velvet.g:154:18: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_feature946);
                    definitions64=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions64.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:154:32: SEMI
                    {
                    SEMI65=(Token)match(input,SEMI,FOLLOW_SEMI_in_feature950);  
                    stream_SEMI.add(SEMI65);


                    }
                    break;

            }


            // AST REWRITE
            // elements: ABSTRACT, MANDATORY, name, definitions
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 155:2: -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
            {
                // Velvet.g:155:5: ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(FEAT, "FEAT")
                , root_1);

                adaptor.addChild(root_1, stream_name.nextTree());

                // Velvet.g:155:17: ( MANDATORY )?
                if ( stream_MANDATORY.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_MANDATORY.nextNode()
                    );

                }
                stream_MANDATORY.reset();

                // Velvet.g:155:28: ( ABSTRACT )?
                if ( stream_ABSTRACT.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ABSTRACT.nextNode()
                    );

                }
                stream_ABSTRACT.reset();

                // Velvet.g:155:38: ( definitions )?
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
    // Velvet.g:158:1: featureGroup : groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) ;
    public final VelvetParser.featureGroup_return featureGroup() throws RecognitionException {
        VelvetParser.featureGroup_return retval = new VelvetParser.featureGroup_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C67=null;
        Token END_C70=null;
        VelvetParser.groupType_return groupType66 =null;

        VelvetParser.feature_return feature68 =null;

        VelvetParser.feature_return feature69 =null;


        Tree START_C67_tree=null;
        Tree END_C70_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_groupType=new RewriteRuleSubtreeStream(adaptor,"rule groupType");
        RewriteRuleSubtreeStream stream_feature=new RewriteRuleSubtreeStream(adaptor,"rule feature");
        try {
            // Velvet.g:159:2: ( groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) )
            // Velvet.g:159:4: groupType START_C feature ( feature )+ END_C
            {
            pushFollow(FOLLOW_groupType_in_featureGroup981);
            groupType66=groupType();

            state._fsp--;

            stream_groupType.add(groupType66.getTree());

            START_C67=(Token)match(input,START_C,FOLLOW_START_C_in_featureGroup983);  
            stream_START_C.add(START_C67);


            pushFollow(FOLLOW_feature_in_featureGroup985);
            feature68=feature();

            state._fsp--;

            stream_feature.add(feature68.getTree());

            // Velvet.g:159:30: ( feature )+
            int cnt21=0;
            loop21:
            do {
                int alt21=2;
                int LA21_0 = input.LA(1);

                if ( (LA21_0==ABSTRACT||LA21_0==FEATURE||LA21_0==MANDATORY) ) {
                    alt21=1;
                }


                switch (alt21) {
            	case 1 :
            	    // Velvet.g:159:30: feature
            	    {
            	    pushFollow(FOLLOW_feature_in_featureGroup987);
            	    feature69=feature();

            	    state._fsp--;

            	    stream_feature.add(feature69.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt21 >= 1 ) break loop21;
                        EarlyExitException eee =
                            new EarlyExitException(21, input);
                        throw eee;
                }
                cnt21++;
            } while (true);


            END_C70=(Token)match(input,END_C,FOLLOW_END_C_in_featureGroup990);  
            stream_END_C.add(END_C70);


            // AST REWRITE
            // elements: groupType, feature, feature
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 160:2: -> ^( GROUP groupType feature ( feature )+ )
            {
                // Velvet.g:160:5: ^( GROUP groupType feature ( feature )+ )
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
    // Velvet.g:163:1: groupType : ( SOMEOF | ONEOF );
    public final VelvetParser.groupType_return groupType() throws RecognitionException {
        VelvetParser.groupType_return retval = new VelvetParser.groupType_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set71=null;

        Tree set71_tree=null;

        try {
            // Velvet.g:164:2: ( SOMEOF | ONEOF )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set71=(Token)input.LT(1);

            if ( input.LA(1)==ONEOF||input.LA(1)==SOMEOF ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set71)
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
    // Velvet.g:168:1: constraint : CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !;
    public final VelvetParser.constraint_return constraint() throws RecognitionException {
        VelvetParser.constraint_return retval = new VelvetParser.constraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token CONSTRAINT72=null;
        Token ID73=null;
        Token EQ74=null;
        Token SEMI77=null;
        VelvetParser.constraintDefinition_return constraintDefinition75 =null;

        VelvetParser.attributeConstraint_return attributeConstraint76 =null;


        Tree CONSTRAINT72_tree=null;
        Tree ID73_tree=null;
        Tree EQ74_tree=null;
        Tree SEMI77_tree=null;

        try {
            // Velvet.g:169:2: ( CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !)
            // Velvet.g:169:4: CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !
            {
            root_0 = (Tree)adaptor.nil();


            CONSTRAINT72=(Token)match(input,CONSTRAINT,FOLLOW_CONSTRAINT_in_constraint1033); 
            CONSTRAINT72_tree = 
            (Tree)adaptor.create(CONSTRAINT72)
            ;
            root_0 = (Tree)adaptor.becomeRoot(CONSTRAINT72_tree, root_0);


            // Velvet.g:169:16: ( ID EQ !)?
            int alt22=2;
            int LA22_0 = input.LA(1);

            if ( (LA22_0==ID) ) {
                int LA22_1 = input.LA(2);

                if ( (LA22_1==EQ) ) {
                    alt22=1;
                }
            }
            switch (alt22) {
                case 1 :
                    // Velvet.g:169:17: ID EQ !
                    {
                    ID73=(Token)match(input,ID,FOLLOW_ID_in_constraint1037); 
                    ID73_tree = 
                    (Tree)adaptor.create(ID73)
                    ;
                    adaptor.addChild(root_0, ID73_tree);


                    EQ74=(Token)match(input,EQ,FOLLOW_EQ_in_constraint1039); 

                    }
                    break;

            }


            // Velvet.g:169:26: ( constraintDefinition | attributeConstraint )
            int alt23=2;
            switch ( input.LA(1) ) {
            case OP_NOT:
            case START_R:
                {
                alt23=1;
                }
                break;
            case ID:
            case IDPath:
                {
                int LA23_2 = input.LA(2);

                if ( ((LA23_2 >= OP_AND && LA23_2 <= OP_IMPLIES)||(LA23_2 >= OP_OR && LA23_2 <= OP_XOR)||LA23_2==SEMI) ) {
                    alt23=1;
                }
                else if ( (LA23_2==ATTR_OP_EQUALS||LA23_2==ATTR_OP_GREATER_EQ||LA23_2==ATTR_OP_LESS_EQ||LA23_2==MINUS||LA23_2==PLUS) ) {
                    alt23=2;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 23, 2, input);

                    throw nvae;

                }
                }
                break;
            case INT:
                {
                alt23=2;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 23, 0, input);

                throw nvae;

            }

            switch (alt23) {
                case 1 :
                    // Velvet.g:169:27: constraintDefinition
                    {
                    pushFollow(FOLLOW_constraintDefinition_in_constraint1045);
                    constraintDefinition75=constraintDefinition();

                    state._fsp--;

                    adaptor.addChild(root_0, constraintDefinition75.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:169:50: attributeConstraint
                    {
                    pushFollow(FOLLOW_attributeConstraint_in_constraint1049);
                    attributeConstraint76=attributeConstraint();

                    state._fsp--;

                    adaptor.addChild(root_0, attributeConstraint76.getTree());

                    }
                    break;

            }


            SEMI77=(Token)match(input,SEMI,FOLLOW_SEMI_in_constraint1052); 

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
    // Velvet.g:172:1: constraintDefinition : constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) ;
    public final VelvetParser.constraintDefinition_return constraintDefinition() throws RecognitionException {
        VelvetParser.constraintDefinition_return retval = new VelvetParser.constraintDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraintOperand_return constraintOperand78 =null;

        VelvetParser.binaryOp_return binaryOp79 =null;

        VelvetParser.constraintOperand_return constraintOperand80 =null;


        RewriteRuleSubtreeStream stream_constraintOperand=new RewriteRuleSubtreeStream(adaptor,"rule constraintOperand");
        RewriteRuleSubtreeStream stream_binaryOp=new RewriteRuleSubtreeStream(adaptor,"rule binaryOp");
        try {
            // Velvet.g:173:2: ( constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) )
            // Velvet.g:173:4: constraintOperand ( binaryOp constraintOperand )*
            {
            pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1065);
            constraintOperand78=constraintOperand();

            state._fsp--;

            stream_constraintOperand.add(constraintOperand78.getTree());

            // Velvet.g:173:22: ( binaryOp constraintOperand )*
            loop24:
            do {
                int alt24=2;
                int LA24_0 = input.LA(1);

                if ( ((LA24_0 >= OP_AND && LA24_0 <= OP_IMPLIES)||(LA24_0 >= OP_OR && LA24_0 <= OP_XOR)) ) {
                    alt24=1;
                }


                switch (alt24) {
            	case 1 :
            	    // Velvet.g:173:23: binaryOp constraintOperand
            	    {
            	    pushFollow(FOLLOW_binaryOp_in_constraintDefinition1068);
            	    binaryOp79=binaryOp();

            	    state._fsp--;

            	    stream_binaryOp.add(binaryOp79.getTree());

            	    pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1070);
            	    constraintOperand80=constraintOperand();

            	    state._fsp--;

            	    stream_constraintOperand.add(constraintOperand80.getTree());

            	    }
            	    break;

            	default :
            	    break loop24;
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
            // 174:2: -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
            {
                // Velvet.g:174:5: ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
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

                // Velvet.g:174:33: ( binaryOp )*
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
    // Velvet.g:177:1: constraintOperand : ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? ;
    public final VelvetParser.constraintOperand_return constraintOperand() throws RecognitionException {
        VelvetParser.constraintOperand_return retval = new VelvetParser.constraintOperand_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_R82=null;
        Token END_R84=null;
        VelvetParser.unaryOp_return unaryOp81 =null;

        VelvetParser.constraintDefinition_return constraintDefinition83 =null;

        VelvetParser.name_return name85 =null;


        Tree START_R82_tree=null;
        Tree END_R84_tree=null;
        RewriteRuleTokenStream stream_END_R=new RewriteRuleTokenStream(adaptor,"token END_R");
        RewriteRuleTokenStream stream_START_R=new RewriteRuleTokenStream(adaptor,"token START_R");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_unaryOp=new RewriteRuleSubtreeStream(adaptor,"rule unaryOp");
        RewriteRuleSubtreeStream stream_constraintDefinition=new RewriteRuleSubtreeStream(adaptor,"rule constraintDefinition");
        try {
            // Velvet.g:177:19: ( ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? )
            // Velvet.g:177:21: ( unaryOp )* ( START_R constraintDefinition END_R | name )
            {
            // Velvet.g:177:21: ( unaryOp )*
            loop25:
            do {
                int alt25=2;
                int LA25_0 = input.LA(1);

                if ( (LA25_0==OP_NOT) ) {
                    alt25=1;
                }


                switch (alt25) {
            	case 1 :
            	    // Velvet.g:177:21: unaryOp
            	    {
            	    pushFollow(FOLLOW_unaryOp_in_constraintOperand1097);
            	    unaryOp81=unaryOp();

            	    state._fsp--;

            	    stream_unaryOp.add(unaryOp81.getTree());

            	    }
            	    break;

            	default :
            	    break loop25;
                }
            } while (true);


            // Velvet.g:177:30: ( START_R constraintDefinition END_R | name )
            int alt26=2;
            int LA26_0 = input.LA(1);

            if ( (LA26_0==START_R) ) {
                alt26=1;
            }
            else if ( ((LA26_0 >= ID && LA26_0 <= IDPath)) ) {
                alt26=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 26, 0, input);

                throw nvae;

            }
            switch (alt26) {
                case 1 :
                    // Velvet.g:177:31: START_R constraintDefinition END_R
                    {
                    START_R82=(Token)match(input,START_R,FOLLOW_START_R_in_constraintOperand1101);  
                    stream_START_R.add(START_R82);


                    pushFollow(FOLLOW_constraintDefinition_in_constraintOperand1103);
                    constraintDefinition83=constraintDefinition();

                    state._fsp--;

                    stream_constraintDefinition.add(constraintDefinition83.getTree());

                    END_R84=(Token)match(input,END_R,FOLLOW_END_R_in_constraintOperand1105);  
                    stream_END_R.add(END_R84);


                    }
                    break;
                case 2 :
                    // Velvet.g:177:68: name
                    {
                    pushFollow(FOLLOW_name_in_constraintOperand1109);
                    name85=name();

                    state._fsp--;

                    stream_name.add(name85.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: name, unaryOp, constraintDefinition
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 178:2: -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )?
            {
                // Velvet.g:178:5: ( constraintDefinition )?
                if ( stream_constraintDefinition.hasNext() ) {
                    adaptor.addChild(root_0, stream_constraintDefinition.nextTree());

                }
                stream_constraintDefinition.reset();

                // Velvet.g:178:27: ( ^( UNARYOP unaryOp ) )*
                while ( stream_unaryOp.hasNext() ) {
                    // Velvet.g:178:27: ^( UNARYOP unaryOp )
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

                // Velvet.g:178:47: ( ^( OPERAND name ) )?
                if ( stream_name.hasNext() ) {
                    // Velvet.g:178:47: ^( OPERAND name )
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
    // Velvet.g:181:1: attributeConstraint : attribConstraint -> ^( ACONSTR attribConstraint ) ;
    public final VelvetParser.attributeConstraint_return attributeConstraint() throws RecognitionException {
        VelvetParser.attributeConstraint_return retval = new VelvetParser.attributeConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribConstraint_return attribConstraint86 =null;


        RewriteRuleSubtreeStream stream_attribConstraint=new RewriteRuleSubtreeStream(adaptor,"rule attribConstraint");
        try {
            // Velvet.g:182:2: ( attribConstraint -> ^( ACONSTR attribConstraint ) )
            // Velvet.g:182:4: attribConstraint
            {
            pushFollow(FOLLOW_attribConstraint_in_attributeConstraint1144);
            attribConstraint86=attribConstraint();

            state._fsp--;

            stream_attribConstraint.add(attribConstraint86.getTree());

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
            // 183:2: -> ^( ACONSTR attribConstraint )
            {
                // Velvet.g:183:5: ^( ACONSTR attribConstraint )
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
    // Velvet.g:186:1: attribConstraint : attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* ;
    public final VelvetParser.attribConstraint_return attribConstraint() throws RecognitionException {
        VelvetParser.attribConstraint_return retval = new VelvetParser.attribConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribNumInstance_return attribNumInstance87 =null;

        VelvetParser.attribOperator_return attribOperator88 =null;

        VelvetParser.attribNumInstance_return attribNumInstance89 =null;

        VelvetParser.attribRelation_return attribRelation90 =null;

        VelvetParser.attribNumInstance_return attribNumInstance91 =null;

        VelvetParser.attribOperator_return attribOperator92 =null;

        VelvetParser.attribNumInstance_return attribNumInstance93 =null;



        try {
            // Velvet.g:187:2: ( attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* )
            // Velvet.g:187:4: attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )*
            {
            root_0 = (Tree)adaptor.nil();


            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1164);
            attribNumInstance87=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance87.getTree());

            // Velvet.g:187:22: ( attribOperator attribNumInstance )*
            loop27:
            do {
                int alt27=2;
                int LA27_0 = input.LA(1);

                if ( (LA27_0==MINUS||LA27_0==PLUS) ) {
                    alt27=1;
                }


                switch (alt27) {
            	case 1 :
            	    // Velvet.g:187:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1167);
            	    attribOperator88=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator88.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1169);
            	    attribNumInstance89=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance89.getTree());

            	    }
            	    break;

            	default :
            	    break loop27;
                }
            } while (true);


            pushFollow(FOLLOW_attribRelation_in_attribConstraint1177);
            attribRelation90=attribRelation();

            state._fsp--;

            adaptor.addChild(root_0, attribRelation90.getTree());

            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1183);
            attribNumInstance91=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance91.getTree());

            // Velvet.g:189:22: ( attribOperator attribNumInstance )*
            loop28:
            do {
                int alt28=2;
                int LA28_0 = input.LA(1);

                if ( (LA28_0==MINUS||LA28_0==PLUS) ) {
                    alt28=1;
                }


                switch (alt28) {
            	case 1 :
            	    // Velvet.g:189:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1186);
            	    attribOperator92=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator92.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1188);
            	    attribNumInstance93=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance93.getTree());

            	    }
            	    break;

            	default :
            	    break loop28;
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
    // Velvet.g:192:1: attribOperator : ( PLUS | MINUS );
    public final VelvetParser.attribOperator_return attribOperator() throws RecognitionException {
        VelvetParser.attribOperator_return retval = new VelvetParser.attribOperator_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set94=null;

        Tree set94_tree=null;

        try {
            // Velvet.g:193:2: ( PLUS | MINUS )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set94=(Token)input.LT(1);

            if ( input.LA(1)==MINUS||input.LA(1)==PLUS ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set94)
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
    // Velvet.g:197:1: attribNumInstance : ( INT | name );
    public final VelvetParser.attribNumInstance_return attribNumInstance() throws RecognitionException {
        VelvetParser.attribNumInstance_return retval = new VelvetParser.attribNumInstance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token INT95=null;
        VelvetParser.name_return name96 =null;


        Tree INT95_tree=null;

        try {
            // Velvet.g:198:2: ( INT | name )
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==INT) ) {
                alt29=1;
            }
            else if ( ((LA29_0 >= ID && LA29_0 <= IDPath)) ) {
                alt29=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 29, 0, input);

                throw nvae;

            }
            switch (alt29) {
                case 1 :
                    // Velvet.g:198:4: INT
                    {
                    root_0 = (Tree)adaptor.nil();


                    INT95=(Token)match(input,INT,FOLLOW_INT_in_attribNumInstance1220); 
                    INT95_tree = 
                    (Tree)adaptor.create(INT95)
                    ;
                    adaptor.addChild(root_0, INT95_tree);


                    }
                    break;
                case 2 :
                    // Velvet.g:200:4: name
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_name_in_attribNumInstance1227);
                    name96=name();

                    state._fsp--;

                    adaptor.addChild(root_0, name96.getTree());

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
    // Velvet.g:203:1: attribute : ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) ;
    public final VelvetParser.attribute_return attribute() throws RecognitionException {
        VelvetParser.attribute_return retval = new VelvetParser.attribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token SEMI101=null;
        VelvetParser.intAttribute_return intAttribute97 =null;

        VelvetParser.floatAttribute_return floatAttribute98 =null;

        VelvetParser.stringAttribute_return stringAttribute99 =null;

        VelvetParser.boolAttribute_return boolAttribute100 =null;


        Tree SEMI101_tree=null;
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_intAttribute=new RewriteRuleSubtreeStream(adaptor,"rule intAttribute");
        RewriteRuleSubtreeStream stream_stringAttribute=new RewriteRuleSubtreeStream(adaptor,"rule stringAttribute");
        RewriteRuleSubtreeStream stream_floatAttribute=new RewriteRuleSubtreeStream(adaptor,"rule floatAttribute");
        RewriteRuleSubtreeStream stream_boolAttribute=new RewriteRuleSubtreeStream(adaptor,"rule boolAttribute");
        try {
            // Velvet.g:204:2: ( ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) )
            // Velvet.g:204:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI
            {
            // Velvet.g:204:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute )
            int alt30=4;
            switch ( input.LA(1) ) {
            case VAR_INT:
                {
                alt30=1;
                }
                break;
            case VAR_FLOAT:
                {
                alt30=2;
                }
                break;
            case VAR_STRING:
                {
                alt30=3;
                }
                break;
            case VAR_BOOL:
                {
                alt30=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 30, 0, input);

                throw nvae;

            }

            switch (alt30) {
                case 1 :
                    // Velvet.g:204:5: intAttribute
                    {
                    pushFollow(FOLLOW_intAttribute_in_attribute1239);
                    intAttribute97=intAttribute();

                    state._fsp--;

                    stream_intAttribute.add(intAttribute97.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:204:20: floatAttribute
                    {
                    pushFollow(FOLLOW_floatAttribute_in_attribute1243);
                    floatAttribute98=floatAttribute();

                    state._fsp--;

                    stream_floatAttribute.add(floatAttribute98.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:204:37: stringAttribute
                    {
                    pushFollow(FOLLOW_stringAttribute_in_attribute1247);
                    stringAttribute99=stringAttribute();

                    state._fsp--;

                    stream_stringAttribute.add(stringAttribute99.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:204:55: boolAttribute
                    {
                    pushFollow(FOLLOW_boolAttribute_in_attribute1251);
                    boolAttribute100=boolAttribute();

                    state._fsp--;

                    stream_boolAttribute.add(boolAttribute100.getTree());

                    }
                    break;

            }


            SEMI101=(Token)match(input,SEMI,FOLLOW_SEMI_in_attribute1254);  
            stream_SEMI.add(SEMI101);


            // AST REWRITE
            // elements: stringAttribute, floatAttribute, intAttribute, boolAttribute
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 205:2: -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
            {
                // Velvet.g:205:5: ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(ATTR, "ATTR")
                , root_1);

                // Velvet.g:205:12: ( intAttribute )?
                if ( stream_intAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_intAttribute.nextTree());

                }
                stream_intAttribute.reset();

                // Velvet.g:205:26: ( floatAttribute )?
                if ( stream_floatAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_floatAttribute.nextTree());

                }
                stream_floatAttribute.reset();

                // Velvet.g:205:42: ( stringAttribute )?
                if ( stream_stringAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_stringAttribute.nextTree());

                }
                stream_stringAttribute.reset();

                // Velvet.g:205:59: ( boolAttribute )?
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
    // Velvet.g:208:1: intAttribute : VAR_INT ! name ( EQ ! INT )? ;
    public final VelvetParser.intAttribute_return intAttribute() throws RecognitionException {
        VelvetParser.intAttribute_return retval = new VelvetParser.intAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_INT102=null;
        Token EQ104=null;
        Token INT105=null;
        VelvetParser.name_return name103 =null;


        Tree VAR_INT102_tree=null;
        Tree EQ104_tree=null;
        Tree INT105_tree=null;

        try {
            // Velvet.g:208:13: ( VAR_INT ! name ( EQ ! INT )? )
            // Velvet.g:208:16: VAR_INT ! name ( EQ ! INT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_INT102=(Token)match(input,VAR_INT,FOLLOW_VAR_INT_in_intAttribute1283); 

            pushFollow(FOLLOW_name_in_intAttribute1286);
            name103=name();

            state._fsp--;

            adaptor.addChild(root_0, name103.getTree());

            // Velvet.g:208:30: ( EQ ! INT )?
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( (LA31_0==EQ) ) {
                alt31=1;
            }
            switch (alt31) {
                case 1 :
                    // Velvet.g:208:31: EQ ! INT
                    {
                    EQ104=(Token)match(input,EQ,FOLLOW_EQ_in_intAttribute1289); 

                    INT105=(Token)match(input,INT,FOLLOW_INT_in_intAttribute1292); 
                    INT105_tree = 
                    (Tree)adaptor.create(INT105)
                    ;
                    adaptor.addChild(root_0, INT105_tree);


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
    // Velvet.g:209:1: floatAttribute : VAR_FLOAT ! name ( EQ ! FLOAT )? ;
    public final VelvetParser.floatAttribute_return floatAttribute() throws RecognitionException {
        VelvetParser.floatAttribute_return retval = new VelvetParser.floatAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_FLOAT106=null;
        Token EQ108=null;
        Token FLOAT109=null;
        VelvetParser.name_return name107 =null;


        Tree VAR_FLOAT106_tree=null;
        Tree EQ108_tree=null;
        Tree FLOAT109_tree=null;

        try {
            // Velvet.g:209:15: ( VAR_FLOAT ! name ( EQ ! FLOAT )? )
            // Velvet.g:209:18: VAR_FLOAT ! name ( EQ ! FLOAT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_FLOAT106=(Token)match(input,VAR_FLOAT,FOLLOW_VAR_FLOAT_in_floatAttribute1301); 

            pushFollow(FOLLOW_name_in_floatAttribute1304);
            name107=name();

            state._fsp--;

            adaptor.addChild(root_0, name107.getTree());

            // Velvet.g:209:34: ( EQ ! FLOAT )?
            int alt32=2;
            int LA32_0 = input.LA(1);

            if ( (LA32_0==EQ) ) {
                alt32=1;
            }
            switch (alt32) {
                case 1 :
                    // Velvet.g:209:35: EQ ! FLOAT
                    {
                    EQ108=(Token)match(input,EQ,FOLLOW_EQ_in_floatAttribute1307); 

                    FLOAT109=(Token)match(input,FLOAT,FOLLOW_FLOAT_in_floatAttribute1310); 
                    FLOAT109_tree = 
                    (Tree)adaptor.create(FLOAT109)
                    ;
                    adaptor.addChild(root_0, FLOAT109_tree);


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
    // Velvet.g:210:1: stringAttribute : VAR_STRING ! name ( EQ ! STRING )? ;
    public final VelvetParser.stringAttribute_return stringAttribute() throws RecognitionException {
        VelvetParser.stringAttribute_return retval = new VelvetParser.stringAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_STRING110=null;
        Token EQ112=null;
        Token STRING113=null;
        VelvetParser.name_return name111 =null;


        Tree VAR_STRING110_tree=null;
        Tree EQ112_tree=null;
        Tree STRING113_tree=null;

        try {
            // Velvet.g:210:16: ( VAR_STRING ! name ( EQ ! STRING )? )
            // Velvet.g:210:18: VAR_STRING ! name ( EQ ! STRING )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_STRING110=(Token)match(input,VAR_STRING,FOLLOW_VAR_STRING_in_stringAttribute1318); 

            pushFollow(FOLLOW_name_in_stringAttribute1321);
            name111=name();

            state._fsp--;

            adaptor.addChild(root_0, name111.getTree());

            // Velvet.g:210:35: ( EQ ! STRING )?
            int alt33=2;
            int LA33_0 = input.LA(1);

            if ( (LA33_0==EQ) ) {
                alt33=1;
            }
            switch (alt33) {
                case 1 :
                    // Velvet.g:210:36: EQ ! STRING
                    {
                    EQ112=(Token)match(input,EQ,FOLLOW_EQ_in_stringAttribute1324); 

                    STRING113=(Token)match(input,STRING,FOLLOW_STRING_in_stringAttribute1327); 
                    STRING113_tree = 
                    (Tree)adaptor.create(STRING113)
                    ;
                    adaptor.addChild(root_0, STRING113_tree);


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
    // Velvet.g:211:1: boolAttribute : VAR_BOOL ! name ( EQ ! BOOLEAN )? ;
    public final VelvetParser.boolAttribute_return boolAttribute() throws RecognitionException {
        VelvetParser.boolAttribute_return retval = new VelvetParser.boolAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_BOOL114=null;
        Token EQ116=null;
        Token BOOLEAN117=null;
        VelvetParser.name_return name115 =null;


        Tree VAR_BOOL114_tree=null;
        Tree EQ116_tree=null;
        Tree BOOLEAN117_tree=null;

        try {
            // Velvet.g:211:14: ( VAR_BOOL ! name ( EQ ! BOOLEAN )? )
            // Velvet.g:211:17: VAR_BOOL ! name ( EQ ! BOOLEAN )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_BOOL114=(Token)match(input,VAR_BOOL,FOLLOW_VAR_BOOL_in_boolAttribute1336); 

            pushFollow(FOLLOW_name_in_boolAttribute1339);
            name115=name();

            state._fsp--;

            adaptor.addChild(root_0, name115.getTree());

            // Velvet.g:211:32: ( EQ ! BOOLEAN )?
            int alt34=2;
            int LA34_0 = input.LA(1);

            if ( (LA34_0==EQ) ) {
                alt34=1;
            }
            switch (alt34) {
                case 1 :
                    // Velvet.g:211:33: EQ ! BOOLEAN
                    {
                    EQ116=(Token)match(input,EQ,FOLLOW_EQ_in_boolAttribute1342); 

                    BOOLEAN117=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_boolAttribute1345); 
                    BOOLEAN117_tree = 
                    (Tree)adaptor.create(BOOLEAN117)
                    ;
                    adaptor.addChild(root_0, BOOLEAN117_tree);


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
    // Velvet.g:213:1: unaryOp : OP_NOT ;
    public final VelvetParser.unaryOp_return unaryOp() throws RecognitionException {
        VelvetParser.unaryOp_return retval = new VelvetParser.unaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token OP_NOT118=null;

        Tree OP_NOT118_tree=null;

        try {
            // Velvet.g:214:2: ( OP_NOT )
            // Velvet.g:214:4: OP_NOT
            {
            root_0 = (Tree)adaptor.nil();


            OP_NOT118=(Token)match(input,OP_NOT,FOLLOW_OP_NOT_in_unaryOp1357); 
            OP_NOT118_tree = 
            (Tree)adaptor.create(OP_NOT118)
            ;
            adaptor.addChild(root_0, OP_NOT118_tree);


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
    // Velvet.g:217:1: binaryOp : ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT );
    public final VelvetParser.binaryOp_return binaryOp() throws RecognitionException {
        VelvetParser.binaryOp_return retval = new VelvetParser.binaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set119=null;

        Tree set119_tree=null;

        try {
            // Velvet.g:218:2: ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set119=(Token)input.LT(1);

            if ( (input.LA(1) >= OP_AND && input.LA(1) <= OP_IMPLIES)||(input.LA(1) >= OP_OR && input.LA(1) <= OP_XOR) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set119)
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
    // Velvet.g:225:1: attribRelation : ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ );
    public final VelvetParser.attribRelation_return attribRelation() throws RecognitionException {
        VelvetParser.attribRelation_return retval = new VelvetParser.attribRelation_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set120=null;

        Tree set120_tree=null;

        try {
            // Velvet.g:226:2: ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set120=(Token)input.LT(1);

            if ( input.LA(1)==ATTR_OP_EQUALS||input.LA(1)==ATTR_OP_GREATER_EQ||input.LA(1)==ATTR_OP_LESS_EQ ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set120)
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


 

    public static final BitSet FOLLOW_imports_in_velvetModel471 = new BitSet(new long[]{0x0080000200090000L});
    public static final BitSet FOLLOW_instancedef_in_velvetModel474 = new BitSet(new long[]{0x0080000200090000L});
    public static final BitSet FOLLOW_concept_in_velvetModel478 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_cinterface_in_velvetModel480 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_velvetModel483 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_instancedef495 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_instancedef497 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_SEMI_in_instancedef499 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IMPORT_in_imports521 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_imports523 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_SEMI_in_imports525 = new BitSet(new long[]{0x0000004000000002L});
    public static final BitSet FOLLOW_REFINES_in_concept550 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_CONCEPT_in_concept553 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_concept555 = new BitSet(new long[]{0x0C00001000020000L});
    public static final BitSet FOLLOW_COLON_in_concept562 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_conceptBaseExt_in_concept564 = new BitSet(new long[]{0x0C00001000000000L});
    public static final BitSet FOLLOW_START_R_in_concept572 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_conceptInterExt_in_concept574 = new BitSet(new long[]{0x0000000001040000L});
    public static final BitSet FOLLOW_COMMA_in_concept577 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_conceptInterExt_in_concept579 = new BitSet(new long[]{0x0000000001040000L});
    public static final BitSet FOLLOW_END_R_in_concept583 = new BitSet(new long[]{0x0400001000000000L});
    public static final BitSet FOLLOW_IMPL_in_concept591 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_implExt_in_concept593 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_definitions_in_concept600 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_implExt635 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt655 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_COMMA_in_conceptBaseExt658 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt660 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_ID_in_conceptInterExt684 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_conceptInterExt686 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_REFINES_in_cinterface708 = new BitSet(new long[]{0x0000000000010000L});
    public static final BitSet FOLLOW_CINTERFACE_in_cinterface711 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_cinterface713 = new BitSet(new long[]{0x0400000000020000L});
    public static final BitSet FOLLOW_COLON_in_cinterface717 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_interfaceBaseExt_in_cinterface719 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_definitions_in_cinterface723 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt753 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_COMMA_in_interfaceBaseExt756 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt758 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_START_C_in_definitions798 = new BitSet(new long[]{0x8200480220A00010L,0x0000000000000007L});
    public static final BitSet FOLLOW_def_in_definitions800 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_END_C_in_definitions802 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def821 = new BitSet(new long[]{0x8200480220200012L,0x0000000000000007L});
    public static final BitSet FOLLOW_featureGroup_in_def829 = new BitSet(new long[]{0x8000000200200002L,0x0000000000000007L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def831 = new BitSet(new long[]{0x8000000200200002L,0x0000000000000007L});
    public static final BitSet FOLLOW_feature_in_def840 = new BitSet(new long[]{0x8000080220200012L,0x0000000000000007L});
    public static final BitSet FOLLOW_feature_in_def843 = new BitSet(new long[]{0x8000080220200012L,0x0000000000000007L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def847 = new BitSet(new long[]{0x8000080220200012L,0x0000000000000007L});
    public static final BitSet FOLLOW_constraint_in_nonFeatureDefinition867 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_instance_in_nonFeatureDefinition873 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribute_in_nonFeatureDefinition879 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_instance890 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_instance892 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_SEMI_in_instance894 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANDATORY_in_feature918 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature920 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature924 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature926 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature930 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature934 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_FEATURE_in_feature941 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_feature943 = new BitSet(new long[]{0x0500000000000000L});
    public static final BitSet FOLLOW_definitions_in_feature946 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SEMI_in_feature950 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_groupType_in_featureGroup981 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_START_C_in_featureGroup983 = new BitSet(new long[]{0x0000080020000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup985 = new BitSet(new long[]{0x0000080020000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup987 = new BitSet(new long[]{0x0000080020800010L});
    public static final BitSet FOLLOW_END_C_in_featureGroup990 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONSTRAINT_in_constraint1033 = new BitSet(new long[]{0x0808020600000000L});
    public static final BitSet FOLLOW_ID_in_constraint1037 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_EQ_in_constraint1039 = new BitSet(new long[]{0x0808020600000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraint1045 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_attributeConstraint_in_constraint1049 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_SEMI_in_constraint1052 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1065 = new BitSet(new long[]{0x0037000000000002L});
    public static final BitSet FOLLOW_binaryOp_in_constraintDefinition1068 = new BitSet(new long[]{0x0808000600000000L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1070 = new BitSet(new long[]{0x0037000000000002L});
    public static final BitSet FOLLOW_unaryOp_in_constraintOperand1097 = new BitSet(new long[]{0x0808000600000000L});
    public static final BitSet FOLLOW_START_R_in_constraintOperand1101 = new BitSet(new long[]{0x0808000600000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraintOperand1103 = new BitSet(new long[]{0x0000000001000000L});
    public static final BitSet FOLLOW_END_R_in_constraintOperand1105 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_constraintOperand1109 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribConstraint_in_attributeConstraint1144 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1164 = new BitSet(new long[]{0x0040100000000A80L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1167 = new BitSet(new long[]{0x0000020600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1169 = new BitSet(new long[]{0x0040100000000A80L});
    public static final BitSet FOLLOW_attribRelation_in_attribConstraint1177 = new BitSet(new long[]{0x0000020600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1183 = new BitSet(new long[]{0x0040100000000002L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1186 = new BitSet(new long[]{0x0000020600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1188 = new BitSet(new long[]{0x0040100000000002L});
    public static final BitSet FOLLOW_INT_in_attribNumInstance1220 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_attribNumInstance1227 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_intAttribute_in_attribute1239 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_floatAttribute_in_attribute1243 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_stringAttribute_in_attribute1247 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_boolAttribute_in_attribute1251 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_SEMI_in_attribute1254 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_INT_in_intAttribute1283 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_intAttribute1286 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_intAttribute1289 = new BitSet(new long[]{0x0000020000000000L});
    public static final BitSet FOLLOW_INT_in_intAttribute1292 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_FLOAT_in_floatAttribute1301 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_floatAttribute1304 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_floatAttribute1307 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_FLOAT_in_floatAttribute1310 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_STRING_in_stringAttribute1318 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_stringAttribute1321 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_stringAttribute1324 = new BitSet(new long[]{0x1000000000000000L});
    public static final BitSet FOLLOW_STRING_in_stringAttribute1327 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_BOOL_in_boolAttribute1336 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_boolAttribute1339 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_boolAttribute1342 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_BOOLEAN_in_boolAttribute1345 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_OP_NOT_in_unaryOp1357 = new BitSet(new long[]{0x0000000000000002L});

}