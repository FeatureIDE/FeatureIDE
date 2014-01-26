// $ANTLR 3.4 Velvet.g 2014-01-26 20:43:49

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
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "ABSTRACT", "ACONSTR", "ATTR", "ATTR_OP_EQUALS", "ATTR_OP_GREATER", "ATTR_OP_GREATER_EQ", "ATTR_OP_LESS", "ATTR_OP_LESS_EQ", "ATTR_OP_NOT_EQUALS", "BASEEXT", "BASEPARAM", "BOOLEAN", "CINTERFACE", "COLON", "COMMA", "CONCEPT", "CONSTR", "CONSTRAINT", "DEF", "END_C", "END_R", "EQ", "ESC_SEQ", "EXPONENT", "FEAT", "FEATURE", "FLOAT", "GROUP", "HEX_DIGIT", "ID", "IDPath", "IMP", "IMPL", "IMPLEMENT", "IMPORT", "INSTANCE", "INSTANCEDEF", "INT", "INTER", "MANDATORY", "MINUS", "OCTAL_ESC", "ONEOF", "OPERAND", "OP_AND", "OP_EQUIVALENT", "OP_IMPLIES", "OP_NOT", "OP_OR", "OP_XOR", "PLUS", "REFINES", "SEMI", "SOMEOF", "START_C", "START_R", "STRING", "UNARYOP", "UNICODE_ESC", "USE", "USES", "VAR_BOOL", "VAR_FLOAT", "VAR_INT", "VAR_STRING", "WS"
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
    public static final int USE=63;
    public static final int USES=64;
    public static final int VAR_BOOL=65;
    public static final int VAR_FLOAT=66;
    public static final int VAR_INT=67;
    public static final int VAR_STRING=68;
    public static final int WS=69;

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
    // Velvet.g:84:1: velvetModel : ( imports )? ( instancedef )* ( concept | cinterface ) EOF ;
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
            // Velvet.g:85:2: ( ( imports )? ( instancedef )* ( concept | cinterface ) EOF )
            // Velvet.g:85:4: ( imports )? ( instancedef )* ( concept | cinterface ) EOF
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:85:4: ( imports )?
            int alt1=2;
            int LA1_0 = input.LA(1);

            if ( (LA1_0==IMPORT) ) {
                alt1=1;
            }
            switch (alt1) {
                case 1 :
                    // Velvet.g:85:4: imports
                    {
                    pushFollow(FOLLOW_imports_in_velvetModel484);
                    imports1=imports();

                    state._fsp--;

                    adaptor.addChild(root_0, imports1.getTree());

                    }
                    break;

            }


            // Velvet.g:85:13: ( instancedef )*
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( (LA2_0==ID) ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // Velvet.g:85:13: instancedef
            	    {
            	    pushFollow(FOLLOW_instancedef_in_velvetModel487);
            	    instancedef2=instancedef();

            	    state._fsp--;

            	    adaptor.addChild(root_0, instancedef2.getTree());

            	    }
            	    break;

            	default :
            	    break loop2;
                }
            } while (true);


            // Velvet.g:85:26: ( concept | cinterface )
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
                    // Velvet.g:85:27: concept
                    {
                    pushFollow(FOLLOW_concept_in_velvetModel491);
                    concept3=concept();

                    state._fsp--;

                    adaptor.addChild(root_0, concept3.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:85:35: cinterface
                    {
                    pushFollow(FOLLOW_cinterface_in_velvetModel493);
                    cinterface4=cinterface();

                    state._fsp--;

                    adaptor.addChild(root_0, cinterface4.getTree());

                    }
                    break;

            }


            EOF5=(Token)match(input,EOF,FOLLOW_EOF_in_velvetModel496); 
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
    // Velvet.g:88:1: instancedef : ID name SEMI -> ^( INSTANCEDEF ID name ) ;
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
            // Velvet.g:89:2: ( ID name SEMI -> ^( INSTANCEDEF ID name ) )
            // Velvet.g:89:4: ID name SEMI
            {
            ID6=(Token)match(input,ID,FOLLOW_ID_in_instancedef508);  
            stream_ID.add(ID6);


            pushFollow(FOLLOW_name_in_instancedef510);
            name7=name();

            state._fsp--;

            stream_name.add(name7.getTree());

            SEMI8=(Token)match(input,SEMI,FOLLOW_SEMI_in_instancedef512);  
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
            // 90:2: -> ^( INSTANCEDEF ID name )
            {
                // Velvet.g:90:5: ^( INSTANCEDEF ID name )
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
    // Velvet.g:93:1: imports : ( IMPORT name SEMI )+ -> ^( IMP ( name )+ ) ;
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
            // Velvet.g:93:9: ( ( IMPORT name SEMI )+ -> ^( IMP ( name )+ ) )
            // Velvet.g:93:11: ( IMPORT name SEMI )+
            {
            // Velvet.g:93:11: ( IMPORT name SEMI )+
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
            	    // Velvet.g:93:12: IMPORT name SEMI
            	    {
            	    IMPORT9=(Token)match(input,IMPORT,FOLLOW_IMPORT_in_imports534);  
            	    stream_IMPORT.add(IMPORT9);


            	    pushFollow(FOLLOW_name_in_imports536);
            	    name10=name();

            	    state._fsp--;

            	    stream_name.add(name10.getTree());

            	    SEMI11=(Token)match(input,SEMI,FOLLOW_SEMI_in_imports538);  
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
            // 94:2: -> ^( IMP ( name )+ )
            {
                // Velvet.g:94:5: ^( IMP ( name )+ )
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
    // Velvet.g:97:1: concept : ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )? ( IMPL implExt )? definitions -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? ( conceptInterExt )* ( implExt )? definitions ) ;
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
            // Velvet.g:98:2: ( ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )? ( IMPL implExt )? definitions -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? ( conceptInterExt )* ( implExt )? definitions ) )
            // Velvet.g:98:4: ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )? ( IMPL implExt )? definitions
            {
            // Velvet.g:98:4: ( REFINES )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==REFINES) ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // Velvet.g:98:4: REFINES
                    {
                    REFINES12=(Token)match(input,REFINES,FOLLOW_REFINES_in_concept563);  
                    stream_REFINES.add(REFINES12);


                    }
                    break;

            }


            CONCEPT13=(Token)match(input,CONCEPT,FOLLOW_CONCEPT_in_concept566);  
            stream_CONCEPT.add(CONCEPT13);


            ID14=(Token)match(input,ID,FOLLOW_ID_in_concept568);  
            stream_ID.add(ID14);


            // Velvet.g:99:3: ( COLON conceptBaseExt )?
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==COLON) ) {
                alt6=1;
            }
            switch (alt6) {
                case 1 :
                    // Velvet.g:99:4: COLON conceptBaseExt
                    {
                    COLON15=(Token)match(input,COLON,FOLLOW_COLON_in_concept575);  
                    stream_COLON.add(COLON15);


                    pushFollow(FOLLOW_conceptBaseExt_in_concept577);
                    conceptBaseExt16=conceptBaseExt();

                    state._fsp--;

                    stream_conceptBaseExt.add(conceptBaseExt16.getTree());

                    }
                    break;

            }


            // Velvet.g:100:3: ( START_R conceptInterExt ( COMMA conceptInterExt )* END_R )?
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==START_R) ) {
                alt8=1;
            }
            switch (alt8) {
                case 1 :
                    // Velvet.g:100:4: START_R conceptInterExt ( COMMA conceptInterExt )* END_R
                    {
                    START_R17=(Token)match(input,START_R,FOLLOW_START_R_in_concept585);  
                    stream_START_R.add(START_R17);


                    pushFollow(FOLLOW_conceptInterExt_in_concept587);
                    conceptInterExt18=conceptInterExt();

                    state._fsp--;

                    stream_conceptInterExt.add(conceptInterExt18.getTree());

                    // Velvet.g:100:28: ( COMMA conceptInterExt )*
                    loop7:
                    do {
                        int alt7=2;
                        int LA7_0 = input.LA(1);

                        if ( (LA7_0==COMMA) ) {
                            alt7=1;
                        }


                        switch (alt7) {
                    	case 1 :
                    	    // Velvet.g:100:29: COMMA conceptInterExt
                    	    {
                    	    COMMA19=(Token)match(input,COMMA,FOLLOW_COMMA_in_concept590);  
                    	    stream_COMMA.add(COMMA19);


                    	    pushFollow(FOLLOW_conceptInterExt_in_concept592);
                    	    conceptInterExt20=conceptInterExt();

                    	    state._fsp--;

                    	    stream_conceptInterExt.add(conceptInterExt20.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop7;
                        }
                    } while (true);


                    END_R21=(Token)match(input,END_R,FOLLOW_END_R_in_concept596);  
                    stream_END_R.add(END_R21);


                    }
                    break;

            }


            // Velvet.g:101:3: ( IMPL implExt )?
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==IMPL) ) {
                alt9=1;
            }
            switch (alt9) {
                case 1 :
                    // Velvet.g:101:4: IMPL implExt
                    {
                    IMPL22=(Token)match(input,IMPL,FOLLOW_IMPL_in_concept604);  
                    stream_IMPL.add(IMPL22);


                    pushFollow(FOLLOW_implExt_in_concept606);
                    implExt23=implExt();

                    state._fsp--;

                    stream_implExt.add(implExt23.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_concept613);
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
            // 103:2: -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? ( conceptInterExt )* ( implExt )? definitions )
            {
                // Velvet.g:103:5: ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? ( conceptInterExt )* ( implExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CONCEPT.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:103:18: ( REFINES )?
                if ( stream_REFINES.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_REFINES.nextNode()
                    );

                }
                stream_REFINES.reset();

                // Velvet.g:103:27: ( conceptBaseExt )?
                if ( stream_conceptBaseExt.hasNext() ) {
                    adaptor.addChild(root_1, stream_conceptBaseExt.nextTree());

                }
                stream_conceptBaseExt.reset();

                // Velvet.g:103:43: ( conceptInterExt )*
                while ( stream_conceptInterExt.hasNext() ) {
                    adaptor.addChild(root_1, stream_conceptInterExt.nextTree());

                }
                stream_conceptInterExt.reset();

                // Velvet.g:103:60: ( implExt )?
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
    // Velvet.g:106:1: implExt : ID -> ^( IMPLEMENT ID ) ;
    public final VelvetParser.implExt_return implExt() throws RecognitionException {
        VelvetParser.implExt_return retval = new VelvetParser.implExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID25=null;

        Tree ID25_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");

        try {
            // Velvet.g:106:9: ( ID -> ^( IMPLEMENT ID ) )
            // Velvet.g:106:11: ID
            {
            ID25=(Token)match(input,ID,FOLLOW_ID_in_implExt648);  
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
            // 107:2: -> ^( IMPLEMENT ID )
            {
                // Velvet.g:107:5: ^( IMPLEMENT ID )
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
    // Velvet.g:110:1: conceptBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
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
            // Velvet.g:111:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:111:4: ID ( COMMA ID )*
            {
            ID26=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt668);  
            stream_ID.add(ID26);


            // Velvet.g:111:7: ( COMMA ID )*
            loop10:
            do {
                int alt10=2;
                int LA10_0 = input.LA(1);

                if ( (LA10_0==COMMA) ) {
                    alt10=1;
                }


                switch (alt10) {
            	case 1 :
            	    // Velvet.g:111:8: COMMA ID
            	    {
            	    COMMA27=(Token)match(input,COMMA,FOLLOW_COMMA_in_conceptBaseExt671);  
            	    stream_COMMA.add(COMMA27);


            	    ID28=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt673);  
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
            // 112:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:112:5: ^( BASEEXT ( ID )+ )
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
    // Velvet.g:115:1: conceptInterExt : ID name -> ^( BASEPARAM ID name ) ;
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
            // Velvet.g:116:2: ( ID name -> ^( BASEPARAM ID name ) )
            // Velvet.g:116:4: ID name
            {
            ID29=(Token)match(input,ID,FOLLOW_ID_in_conceptInterExt697);  
            stream_ID.add(ID29);


            pushFollow(FOLLOW_name_in_conceptInterExt699);
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
            // 117:2: -> ^( BASEPARAM ID name )
            {
                // Velvet.g:117:5: ^( BASEPARAM ID name )
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
    // Velvet.g:121:1: cinterface : ( REFINES )? CINTERFACE ID ( COLON interfaceBaseExt )? definitions -> ^( CINTERFACE ID ( REFINES )? ( interfaceBaseExt )? definitions ) ;
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
            // Velvet.g:121:12: ( ( REFINES )? CINTERFACE ID ( COLON interfaceBaseExt )? definitions -> ^( CINTERFACE ID ( REFINES )? ( interfaceBaseExt )? definitions ) )
            // Velvet.g:121:14: ( REFINES )? CINTERFACE ID ( COLON interfaceBaseExt )? definitions
            {
            // Velvet.g:121:14: ( REFINES )?
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==REFINES) ) {
                alt11=1;
            }
            switch (alt11) {
                case 1 :
                    // Velvet.g:121:14: REFINES
                    {
                    REFINES31=(Token)match(input,REFINES,FOLLOW_REFINES_in_cinterface721);  
                    stream_REFINES.add(REFINES31);


                    }
                    break;

            }


            CINTERFACE32=(Token)match(input,CINTERFACE,FOLLOW_CINTERFACE_in_cinterface724);  
            stream_CINTERFACE.add(CINTERFACE32);


            ID33=(Token)match(input,ID,FOLLOW_ID_in_cinterface726);  
            stream_ID.add(ID33);


            // Velvet.g:121:38: ( COLON interfaceBaseExt )?
            int alt12=2;
            int LA12_0 = input.LA(1);

            if ( (LA12_0==COLON) ) {
                alt12=1;
            }
            switch (alt12) {
                case 1 :
                    // Velvet.g:121:39: COLON interfaceBaseExt
                    {
                    COLON34=(Token)match(input,COLON,FOLLOW_COLON_in_cinterface730);  
                    stream_COLON.add(COLON34);


                    pushFollow(FOLLOW_interfaceBaseExt_in_cinterface732);
                    interfaceBaseExt35=interfaceBaseExt();

                    state._fsp--;

                    stream_interfaceBaseExt.add(interfaceBaseExt35.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_cinterface736);
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
            // 122:2: -> ^( CINTERFACE ID ( REFINES )? ( interfaceBaseExt )? definitions )
            {
                // Velvet.g:122:5: ^( CINTERFACE ID ( REFINES )? ( interfaceBaseExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CINTERFACE.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:122:21: ( REFINES )?
                if ( stream_REFINES.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_REFINES.nextNode()
                    );

                }
                stream_REFINES.reset();

                // Velvet.g:122:30: ( interfaceBaseExt )?
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
    // Velvet.g:125:1: interfaceBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
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
            // Velvet.g:126:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:126:4: ID ( COMMA ID )*
            {
            ID37=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt766);  
            stream_ID.add(ID37);


            // Velvet.g:126:7: ( COMMA ID )*
            loop13:
            do {
                int alt13=2;
                int LA13_0 = input.LA(1);

                if ( (LA13_0==COMMA) ) {
                    alt13=1;
                }


                switch (alt13) {
            	case 1 :
            	    // Velvet.g:126:8: COMMA ID
            	    {
            	    COMMA38=(Token)match(input,COMMA,FOLLOW_COMMA_in_interfaceBaseExt769);  
            	    stream_COMMA.add(COMMA38);


            	    ID39=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt771);  
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
            // 127:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:127:5: ^( BASEEXT ( ID )+ )
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
    // Velvet.g:130:1: name : ( ID | IDPath );
    public final VelvetParser.name_return name() throws RecognitionException {
        VelvetParser.name_return retval = new VelvetParser.name_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set40=null;

        Tree set40_tree=null;

        try {
            // Velvet.g:130:5: ( ID | IDPath )
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
    // Velvet.g:134:1: definitions : START_C def END_C -> ^( DEF def ) ;
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
            // Velvet.g:135:2: ( START_C def END_C -> ^( DEF def ) )
            // Velvet.g:135:4: START_C def END_C
            {
            START_C41=(Token)match(input,START_C,FOLLOW_START_C_in_definitions811);  
            stream_START_C.add(START_C41);


            pushFollow(FOLLOW_def_in_definitions813);
            def42=def();

            state._fsp--;

            stream_def.add(def42.getTree());

            END_C43=(Token)match(input,END_C,FOLLOW_END_C_in_definitions815);  
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
            // 136:2: -> ^( DEF def )
            {
                // Velvet.g:136:5: ^( DEF def )
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
    // Velvet.g:139:1: def : ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( USE use ) | ( feature ( feature | nonFeatureDefinition )* ) )? ;
    public final VelvetParser.def_return def() throws RecognitionException {
        VelvetParser.def_return retval = new VelvetParser.def_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token USE47=null;
        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition44 =null;

        VelvetParser.featureGroup_return featureGroup45 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition46 =null;

        VelvetParser.use_return use48 =null;

        VelvetParser.feature_return feature49 =null;

        VelvetParser.feature_return feature50 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition51 =null;


        Tree USE47_tree=null;

        try {
            // Velvet.g:139:5: ( ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( USE use ) | ( feature ( feature | nonFeatureDefinition )* ) )? )
            // Velvet.g:139:7: ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( USE use ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:139:7: ( nonFeatureDefinition )*
            loop14:
            do {
                int alt14=2;
                int LA14_0 = input.LA(1);

                if ( (LA14_0==CONSTRAINT||LA14_0==ID||(LA14_0 >= VAR_BOOL && LA14_0 <= VAR_STRING)) ) {
                    alt14=1;
                }


                switch (alt14) {
            	case 1 :
            	    // Velvet.g:139:7: nonFeatureDefinition
            	    {
            	    pushFollow(FOLLOW_nonFeatureDefinition_in_def834);
            	    nonFeatureDefinition44=nonFeatureDefinition();

            	    state._fsp--;

            	    adaptor.addChild(root_0, nonFeatureDefinition44.getTree());

            	    }
            	    break;

            	default :
            	    break loop14;
                }
            } while (true);


            // Velvet.g:139:29: ( ( featureGroup ( nonFeatureDefinition )* ) | ( USE use ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            int alt17=4;
            switch ( input.LA(1) ) {
                case ONEOF:
                case SOMEOF:
                    {
                    alt17=1;
                    }
                    break;
                case USE:
                    {
                    alt17=2;
                    }
                    break;
                case ABSTRACT:
                case FEATURE:
                case MANDATORY:
                    {
                    alt17=3;
                    }
                    break;
            }

            switch (alt17) {
                case 1 :
                    // Velvet.g:140:3: ( featureGroup ( nonFeatureDefinition )* )
                    {
                    // Velvet.g:140:3: ( featureGroup ( nonFeatureDefinition )* )
                    // Velvet.g:140:4: featureGroup ( nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_featureGroup_in_def842);
                    featureGroup45=featureGroup();

                    state._fsp--;

                    adaptor.addChild(root_0, featureGroup45.getTree());

                    // Velvet.g:140:17: ( nonFeatureDefinition )*
                    loop15:
                    do {
                        int alt15=2;
                        int LA15_0 = input.LA(1);

                        if ( (LA15_0==CONSTRAINT||LA15_0==ID||(LA15_0 >= VAR_BOOL && LA15_0 <= VAR_STRING)) ) {
                            alt15=1;
                        }


                        switch (alt15) {
                    	case 1 :
                    	    // Velvet.g:140:17: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def844);
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
                    // Velvet.g:141:3: ( USE use )
                    {
                    // Velvet.g:141:3: ( USE use )
                    // Velvet.g:141:4: USE use
                    {
                    USE47=(Token)match(input,USE,FOLLOW_USE_in_def853); 
                    USE47_tree = 
                    (Tree)adaptor.create(USE47)
                    ;
                    adaptor.addChild(root_0, USE47_tree);


                    pushFollow(FOLLOW_use_in_def855);
                    use48=use();

                    state._fsp--;

                    adaptor.addChild(root_0, use48.getTree());

                    }


                    }
                    break;
                case 3 :
                    // Velvet.g:142:3: ( feature ( feature | nonFeatureDefinition )* )
                    {
                    // Velvet.g:142:3: ( feature ( feature | nonFeatureDefinition )* )
                    // Velvet.g:142:4: feature ( feature | nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_feature_in_def863);
                    feature49=feature();

                    state._fsp--;

                    adaptor.addChild(root_0, feature49.getTree());

                    // Velvet.g:142:12: ( feature | nonFeatureDefinition )*
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
                    	    // Velvet.g:142:13: feature
                    	    {
                    	    pushFollow(FOLLOW_feature_in_def866);
                    	    feature50=feature();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, feature50.getTree());

                    	    }
                    	    break;
                    	case 2 :
                    	    // Velvet.g:142:23: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def870);
                    	    nonFeatureDefinition51=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition51.getTree());

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
    // Velvet.g:145:1: nonFeatureDefinition : ( constraint | instance | attribute );
    public final VelvetParser.nonFeatureDefinition_return nonFeatureDefinition() throws RecognitionException {
        VelvetParser.nonFeatureDefinition_return retval = new VelvetParser.nonFeatureDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraint_return constraint52 =null;

        VelvetParser.instance_return instance53 =null;

        VelvetParser.attribute_return attribute54 =null;



        try {
            // Velvet.g:146:2: ( constraint | instance | attribute )
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
                    // Velvet.g:146:4: constraint
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_constraint_in_nonFeatureDefinition890);
                    constraint52=constraint();

                    state._fsp--;

                    adaptor.addChild(root_0, constraint52.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:147:4: instance
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_instance_in_nonFeatureDefinition896);
                    instance53=instance();

                    state._fsp--;

                    adaptor.addChild(root_0, instance53.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:148:4: attribute
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_attribute_in_nonFeatureDefinition902);
                    attribute54=attribute();

                    state._fsp--;

                    adaptor.addChild(root_0, attribute54.getTree());

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


    public static class use_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "use"
    // Velvet.g:151:1: use : ID SEMI -> ^( USES ID ) ;
    public final VelvetParser.use_return use() throws RecognitionException {
        VelvetParser.use_return retval = new VelvetParser.use_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID55=null;
        Token SEMI56=null;

        Tree ID55_tree=null;
        Tree SEMI56_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");

        try {
            // Velvet.g:151:5: ( ID SEMI -> ^( USES ID ) )
            // Velvet.g:151:7: ID SEMI
            {
            ID55=(Token)match(input,ID,FOLLOW_ID_in_use914);  
            stream_ID.add(ID55);


            SEMI56=(Token)match(input,SEMI,FOLLOW_SEMI_in_use916);  
            stream_SEMI.add(SEMI56);


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
            // 152:2: -> ^( USES ID )
            {
                // Velvet.g:152:5: ^( USES ID )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(USES, "USES")
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
    // $ANTLR end "use"


    public static class instance_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "instance"
    // Velvet.g:155:1: instance : ID name SEMI -> ^( INSTANCE ID name ) ;
    public final VelvetParser.instance_return instance() throws RecognitionException {
        VelvetParser.instance_return retval = new VelvetParser.instance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID57=null;
        Token SEMI59=null;
        VelvetParser.name_return name58 =null;


        Tree ID57_tree=null;
        Tree SEMI59_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:155:9: ( ID name SEMI -> ^( INSTANCE ID name ) )
            // Velvet.g:155:11: ID name SEMI
            {
            ID57=(Token)match(input,ID,FOLLOW_ID_in_instance935);  
            stream_ID.add(ID57);


            pushFollow(FOLLOW_name_in_instance937);
            name58=name();

            state._fsp--;

            stream_name.add(name58.getTree());

            SEMI59=(Token)match(input,SEMI,FOLLOW_SEMI_in_instance939);  
            stream_SEMI.add(SEMI59);


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
            // 156:2: -> ^( INSTANCE ID name )
            {
                // Velvet.g:156:5: ^( INSTANCE ID name )
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
    // Velvet.g:159:1: feature : ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) ;
    public final VelvetParser.feature_return feature() throws RecognitionException {
        VelvetParser.feature_return retval = new VelvetParser.feature_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token MANDATORY60=null;
        Token ABSTRACT61=null;
        Token ABSTRACT62=null;
        Token MANDATORY63=null;
        Token MANDATORY64=null;
        Token ABSTRACT65=null;
        Token FEATURE66=null;
        Token SEMI69=null;
        VelvetParser.name_return name67 =null;

        VelvetParser.definitions_return definitions68 =null;


        Tree MANDATORY60_tree=null;
        Tree ABSTRACT61_tree=null;
        Tree ABSTRACT62_tree=null;
        Tree MANDATORY63_tree=null;
        Tree MANDATORY64_tree=null;
        Tree ABSTRACT65_tree=null;
        Tree FEATURE66_tree=null;
        Tree SEMI69_tree=null;
        RewriteRuleTokenStream stream_ABSTRACT=new RewriteRuleTokenStream(adaptor,"token ABSTRACT");
        RewriteRuleTokenStream stream_MANDATORY=new RewriteRuleTokenStream(adaptor,"token MANDATORY");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleTokenStream stream_FEATURE=new RewriteRuleTokenStream(adaptor,"token FEATURE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:160:2: ( ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) )
            // Velvet.g:160:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI )
            {
            // Velvet.g:160:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )?
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
                    // Velvet.g:160:5: MANDATORY ABSTRACT
                    {
                    MANDATORY60=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature963);  
                    stream_MANDATORY.add(MANDATORY60);


                    ABSTRACT61=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature965);  
                    stream_ABSTRACT.add(ABSTRACT61);


                    }
                    break;
                case 2 :
                    // Velvet.g:160:26: ABSTRACT MANDATORY
                    {
                    ABSTRACT62=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature969);  
                    stream_ABSTRACT.add(ABSTRACT62);


                    MANDATORY63=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature971);  
                    stream_MANDATORY.add(MANDATORY63);


                    }
                    break;
                case 3 :
                    // Velvet.g:160:47: MANDATORY
                    {
                    MANDATORY64=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature975);  
                    stream_MANDATORY.add(MANDATORY64);


                    }
                    break;
                case 4 :
                    // Velvet.g:160:59: ABSTRACT
                    {
                    ABSTRACT65=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature979);  
                    stream_ABSTRACT.add(ABSTRACT65);


                    }
                    break;

            }


            FEATURE66=(Token)match(input,FEATURE,FOLLOW_FEATURE_in_feature986);  
            stream_FEATURE.add(FEATURE66);


            pushFollow(FOLLOW_name_in_feature988);
            name67=name();

            state._fsp--;

            stream_name.add(name67.getTree());

            // Velvet.g:161:17: ( definitions | SEMI )
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
                    // Velvet.g:161:18: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_feature991);
                    definitions68=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions68.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:161:32: SEMI
                    {
                    SEMI69=(Token)match(input,SEMI,FOLLOW_SEMI_in_feature995);  
                    stream_SEMI.add(SEMI69);


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
            // 162:2: -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
            {
                // Velvet.g:162:5: ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(FEAT, "FEAT")
                , root_1);

                adaptor.addChild(root_1, stream_name.nextTree());

                // Velvet.g:162:17: ( MANDATORY )?
                if ( stream_MANDATORY.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_MANDATORY.nextNode()
                    );

                }
                stream_MANDATORY.reset();

                // Velvet.g:162:28: ( ABSTRACT )?
                if ( stream_ABSTRACT.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ABSTRACT.nextNode()
                    );

                }
                stream_ABSTRACT.reset();

                // Velvet.g:162:38: ( definitions )?
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
    // Velvet.g:165:1: featureGroup : groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) ;
    public final VelvetParser.featureGroup_return featureGroup() throws RecognitionException {
        VelvetParser.featureGroup_return retval = new VelvetParser.featureGroup_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C71=null;
        Token END_C74=null;
        VelvetParser.groupType_return groupType70 =null;

        VelvetParser.feature_return feature72 =null;

        VelvetParser.feature_return feature73 =null;


        Tree START_C71_tree=null;
        Tree END_C74_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_groupType=new RewriteRuleSubtreeStream(adaptor,"rule groupType");
        RewriteRuleSubtreeStream stream_feature=new RewriteRuleSubtreeStream(adaptor,"rule feature");
        try {
            // Velvet.g:166:2: ( groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) )
            // Velvet.g:166:4: groupType START_C feature ( feature )+ END_C
            {
            pushFollow(FOLLOW_groupType_in_featureGroup1026);
            groupType70=groupType();

            state._fsp--;

            stream_groupType.add(groupType70.getTree());

            START_C71=(Token)match(input,START_C,FOLLOW_START_C_in_featureGroup1028);  
            stream_START_C.add(START_C71);


            pushFollow(FOLLOW_feature_in_featureGroup1030);
            feature72=feature();

            state._fsp--;

            stream_feature.add(feature72.getTree());

            // Velvet.g:166:30: ( feature )+
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
            	    // Velvet.g:166:30: feature
            	    {
            	    pushFollow(FOLLOW_feature_in_featureGroup1032);
            	    feature73=feature();

            	    state._fsp--;

            	    stream_feature.add(feature73.getTree());

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


            END_C74=(Token)match(input,END_C,FOLLOW_END_C_in_featureGroup1035);  
            stream_END_C.add(END_C74);


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
            // 167:2: -> ^( GROUP groupType feature ( feature )+ )
            {
                // Velvet.g:167:5: ^( GROUP groupType feature ( feature )+ )
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
    // Velvet.g:170:1: groupType : ( SOMEOF | ONEOF );
    public final VelvetParser.groupType_return groupType() throws RecognitionException {
        VelvetParser.groupType_return retval = new VelvetParser.groupType_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set75=null;

        Tree set75_tree=null;

        try {
            // Velvet.g:171:2: ( SOMEOF | ONEOF )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set75=(Token)input.LT(1);

            if ( input.LA(1)==ONEOF||input.LA(1)==SOMEOF ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set75)
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
    // Velvet.g:175:1: constraint : CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !;
    public final VelvetParser.constraint_return constraint() throws RecognitionException {
        VelvetParser.constraint_return retval = new VelvetParser.constraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token CONSTRAINT76=null;
        Token ID77=null;
        Token EQ78=null;
        Token SEMI81=null;
        VelvetParser.constraintDefinition_return constraintDefinition79 =null;

        VelvetParser.attributeConstraint_return attributeConstraint80 =null;


        Tree CONSTRAINT76_tree=null;
        Tree ID77_tree=null;
        Tree EQ78_tree=null;
        Tree SEMI81_tree=null;

        try {
            // Velvet.g:176:2: ( CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !)
            // Velvet.g:176:4: CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !
            {
            root_0 = (Tree)adaptor.nil();


            CONSTRAINT76=(Token)match(input,CONSTRAINT,FOLLOW_CONSTRAINT_in_constraint1078); 
            CONSTRAINT76_tree = 
            (Tree)adaptor.create(CONSTRAINT76)
            ;
            root_0 = (Tree)adaptor.becomeRoot(CONSTRAINT76_tree, root_0);


            // Velvet.g:176:16: ( ID EQ !)?
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
                    // Velvet.g:176:17: ID EQ !
                    {
                    ID77=(Token)match(input,ID,FOLLOW_ID_in_constraint1082); 
                    ID77_tree = 
                    (Tree)adaptor.create(ID77)
                    ;
                    adaptor.addChild(root_0, ID77_tree);


                    EQ78=(Token)match(input,EQ,FOLLOW_EQ_in_constraint1084); 

                    }
                    break;

            }


            // Velvet.g:176:26: ( constraintDefinition | attributeConstraint )
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
                    // Velvet.g:176:27: constraintDefinition
                    {
                    pushFollow(FOLLOW_constraintDefinition_in_constraint1090);
                    constraintDefinition79=constraintDefinition();

                    state._fsp--;

                    adaptor.addChild(root_0, constraintDefinition79.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:176:50: attributeConstraint
                    {
                    pushFollow(FOLLOW_attributeConstraint_in_constraint1094);
                    attributeConstraint80=attributeConstraint();

                    state._fsp--;

                    adaptor.addChild(root_0, attributeConstraint80.getTree());

                    }
                    break;

            }


            SEMI81=(Token)match(input,SEMI,FOLLOW_SEMI_in_constraint1097); 

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
    // Velvet.g:179:1: constraintDefinition : constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) ;
    public final VelvetParser.constraintDefinition_return constraintDefinition() throws RecognitionException {
        VelvetParser.constraintDefinition_return retval = new VelvetParser.constraintDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraintOperand_return constraintOperand82 =null;

        VelvetParser.binaryOp_return binaryOp83 =null;

        VelvetParser.constraintOperand_return constraintOperand84 =null;


        RewriteRuleSubtreeStream stream_constraintOperand=new RewriteRuleSubtreeStream(adaptor,"rule constraintOperand");
        RewriteRuleSubtreeStream stream_binaryOp=new RewriteRuleSubtreeStream(adaptor,"rule binaryOp");
        try {
            // Velvet.g:180:2: ( constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) )
            // Velvet.g:180:4: constraintOperand ( binaryOp constraintOperand )*
            {
            pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1110);
            constraintOperand82=constraintOperand();

            state._fsp--;

            stream_constraintOperand.add(constraintOperand82.getTree());

            // Velvet.g:180:22: ( binaryOp constraintOperand )*
            loop24:
            do {
                int alt24=2;
                int LA24_0 = input.LA(1);

                if ( ((LA24_0 >= OP_AND && LA24_0 <= OP_IMPLIES)||(LA24_0 >= OP_OR && LA24_0 <= OP_XOR)) ) {
                    alt24=1;
                }


                switch (alt24) {
            	case 1 :
            	    // Velvet.g:180:23: binaryOp constraintOperand
            	    {
            	    pushFollow(FOLLOW_binaryOp_in_constraintDefinition1113);
            	    binaryOp83=binaryOp();

            	    state._fsp--;

            	    stream_binaryOp.add(binaryOp83.getTree());

            	    pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1115);
            	    constraintOperand84=constraintOperand();

            	    state._fsp--;

            	    stream_constraintOperand.add(constraintOperand84.getTree());

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
            // 181:2: -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
            {
                // Velvet.g:181:5: ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
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

                // Velvet.g:181:33: ( binaryOp )*
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
    // Velvet.g:184:1: constraintOperand : ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? ;
    public final VelvetParser.constraintOperand_return constraintOperand() throws RecognitionException {
        VelvetParser.constraintOperand_return retval = new VelvetParser.constraintOperand_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_R86=null;
        Token END_R88=null;
        VelvetParser.unaryOp_return unaryOp85 =null;

        VelvetParser.constraintDefinition_return constraintDefinition87 =null;

        VelvetParser.name_return name89 =null;


        Tree START_R86_tree=null;
        Tree END_R88_tree=null;
        RewriteRuleTokenStream stream_END_R=new RewriteRuleTokenStream(adaptor,"token END_R");
        RewriteRuleTokenStream stream_START_R=new RewriteRuleTokenStream(adaptor,"token START_R");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_unaryOp=new RewriteRuleSubtreeStream(adaptor,"rule unaryOp");
        RewriteRuleSubtreeStream stream_constraintDefinition=new RewriteRuleSubtreeStream(adaptor,"rule constraintDefinition");
        try {
            // Velvet.g:184:19: ( ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? )
            // Velvet.g:184:21: ( unaryOp )* ( START_R constraintDefinition END_R | name )
            {
            // Velvet.g:184:21: ( unaryOp )*
            loop25:
            do {
                int alt25=2;
                int LA25_0 = input.LA(1);

                if ( (LA25_0==OP_NOT) ) {
                    alt25=1;
                }


                switch (alt25) {
            	case 1 :
            	    // Velvet.g:184:21: unaryOp
            	    {
            	    pushFollow(FOLLOW_unaryOp_in_constraintOperand1142);
            	    unaryOp85=unaryOp();

            	    state._fsp--;

            	    stream_unaryOp.add(unaryOp85.getTree());

            	    }
            	    break;

            	default :
            	    break loop25;
                }
            } while (true);


            // Velvet.g:184:30: ( START_R constraintDefinition END_R | name )
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
                    // Velvet.g:184:31: START_R constraintDefinition END_R
                    {
                    START_R86=(Token)match(input,START_R,FOLLOW_START_R_in_constraintOperand1146);  
                    stream_START_R.add(START_R86);


                    pushFollow(FOLLOW_constraintDefinition_in_constraintOperand1148);
                    constraintDefinition87=constraintDefinition();

                    state._fsp--;

                    stream_constraintDefinition.add(constraintDefinition87.getTree());

                    END_R88=(Token)match(input,END_R,FOLLOW_END_R_in_constraintOperand1150);  
                    stream_END_R.add(END_R88);


                    }
                    break;
                case 2 :
                    // Velvet.g:184:68: name
                    {
                    pushFollow(FOLLOW_name_in_constraintOperand1154);
                    name89=name();

                    state._fsp--;

                    stream_name.add(name89.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: unaryOp, name, constraintDefinition
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 185:2: -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )?
            {
                // Velvet.g:185:5: ( constraintDefinition )?
                if ( stream_constraintDefinition.hasNext() ) {
                    adaptor.addChild(root_0, stream_constraintDefinition.nextTree());

                }
                stream_constraintDefinition.reset();

                // Velvet.g:185:27: ( ^( UNARYOP unaryOp ) )*
                while ( stream_unaryOp.hasNext() ) {
                    // Velvet.g:185:27: ^( UNARYOP unaryOp )
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

                // Velvet.g:185:47: ( ^( OPERAND name ) )?
                if ( stream_name.hasNext() ) {
                    // Velvet.g:185:47: ^( OPERAND name )
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
    // Velvet.g:188:1: attributeConstraint : attribConstraint -> ^( ACONSTR attribConstraint ) ;
    public final VelvetParser.attributeConstraint_return attributeConstraint() throws RecognitionException {
        VelvetParser.attributeConstraint_return retval = new VelvetParser.attributeConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribConstraint_return attribConstraint90 =null;


        RewriteRuleSubtreeStream stream_attribConstraint=new RewriteRuleSubtreeStream(adaptor,"rule attribConstraint");
        try {
            // Velvet.g:189:2: ( attribConstraint -> ^( ACONSTR attribConstraint ) )
            // Velvet.g:189:4: attribConstraint
            {
            pushFollow(FOLLOW_attribConstraint_in_attributeConstraint1189);
            attribConstraint90=attribConstraint();

            state._fsp--;

            stream_attribConstraint.add(attribConstraint90.getTree());

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
            // 190:2: -> ^( ACONSTR attribConstraint )
            {
                // Velvet.g:190:5: ^( ACONSTR attribConstraint )
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
    // Velvet.g:193:1: attribConstraint : attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* ;
    public final VelvetParser.attribConstraint_return attribConstraint() throws RecognitionException {
        VelvetParser.attribConstraint_return retval = new VelvetParser.attribConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribNumInstance_return attribNumInstance91 =null;

        VelvetParser.attribOperator_return attribOperator92 =null;

        VelvetParser.attribNumInstance_return attribNumInstance93 =null;

        VelvetParser.attribRelation_return attribRelation94 =null;

        VelvetParser.attribNumInstance_return attribNumInstance95 =null;

        VelvetParser.attribOperator_return attribOperator96 =null;

        VelvetParser.attribNumInstance_return attribNumInstance97 =null;



        try {
            // Velvet.g:194:2: ( attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* )
            // Velvet.g:194:4: attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )*
            {
            root_0 = (Tree)adaptor.nil();


            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1209);
            attribNumInstance91=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance91.getTree());

            // Velvet.g:194:22: ( attribOperator attribNumInstance )*
            loop27:
            do {
                int alt27=2;
                int LA27_0 = input.LA(1);

                if ( (LA27_0==MINUS||LA27_0==PLUS) ) {
                    alt27=1;
                }


                switch (alt27) {
            	case 1 :
            	    // Velvet.g:194:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1212);
            	    attribOperator92=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator92.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1214);
            	    attribNumInstance93=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance93.getTree());

            	    }
            	    break;

            	default :
            	    break loop27;
                }
            } while (true);


            pushFollow(FOLLOW_attribRelation_in_attribConstraint1222);
            attribRelation94=attribRelation();

            state._fsp--;

            adaptor.addChild(root_0, attribRelation94.getTree());

            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1228);
            attribNumInstance95=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance95.getTree());

            // Velvet.g:196:22: ( attribOperator attribNumInstance )*
            loop28:
            do {
                int alt28=2;
                int LA28_0 = input.LA(1);

                if ( (LA28_0==MINUS||LA28_0==PLUS) ) {
                    alt28=1;
                }


                switch (alt28) {
            	case 1 :
            	    // Velvet.g:196:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1231);
            	    attribOperator96=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator96.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1233);
            	    attribNumInstance97=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance97.getTree());

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
    // Velvet.g:199:1: attribOperator : ( PLUS | MINUS );
    public final VelvetParser.attribOperator_return attribOperator() throws RecognitionException {
        VelvetParser.attribOperator_return retval = new VelvetParser.attribOperator_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set98=null;

        Tree set98_tree=null;

        try {
            // Velvet.g:200:2: ( PLUS | MINUS )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set98=(Token)input.LT(1);

            if ( input.LA(1)==MINUS||input.LA(1)==PLUS ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set98)
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
    // Velvet.g:204:1: attribNumInstance : ( INT | name );
    public final VelvetParser.attribNumInstance_return attribNumInstance() throws RecognitionException {
        VelvetParser.attribNumInstance_return retval = new VelvetParser.attribNumInstance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token INT99=null;
        VelvetParser.name_return name100 =null;


        Tree INT99_tree=null;

        try {
            // Velvet.g:205:2: ( INT | name )
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
                    // Velvet.g:205:4: INT
                    {
                    root_0 = (Tree)adaptor.nil();


                    INT99=(Token)match(input,INT,FOLLOW_INT_in_attribNumInstance1265); 
                    INT99_tree = 
                    (Tree)adaptor.create(INT99)
                    ;
                    adaptor.addChild(root_0, INT99_tree);


                    }
                    break;
                case 2 :
                    // Velvet.g:207:4: name
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_name_in_attribNumInstance1272);
                    name100=name();

                    state._fsp--;

                    adaptor.addChild(root_0, name100.getTree());

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
    // Velvet.g:210:1: attribute : ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) ;
    public final VelvetParser.attribute_return attribute() throws RecognitionException {
        VelvetParser.attribute_return retval = new VelvetParser.attribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token SEMI105=null;
        VelvetParser.intAttribute_return intAttribute101 =null;

        VelvetParser.floatAttribute_return floatAttribute102 =null;

        VelvetParser.stringAttribute_return stringAttribute103 =null;

        VelvetParser.boolAttribute_return boolAttribute104 =null;


        Tree SEMI105_tree=null;
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_intAttribute=new RewriteRuleSubtreeStream(adaptor,"rule intAttribute");
        RewriteRuleSubtreeStream stream_stringAttribute=new RewriteRuleSubtreeStream(adaptor,"rule stringAttribute");
        RewriteRuleSubtreeStream stream_floatAttribute=new RewriteRuleSubtreeStream(adaptor,"rule floatAttribute");
        RewriteRuleSubtreeStream stream_boolAttribute=new RewriteRuleSubtreeStream(adaptor,"rule boolAttribute");
        try {
            // Velvet.g:211:2: ( ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) )
            // Velvet.g:211:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI
            {
            // Velvet.g:211:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute )
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
                    // Velvet.g:211:5: intAttribute
                    {
                    pushFollow(FOLLOW_intAttribute_in_attribute1284);
                    intAttribute101=intAttribute();

                    state._fsp--;

                    stream_intAttribute.add(intAttribute101.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:211:20: floatAttribute
                    {
                    pushFollow(FOLLOW_floatAttribute_in_attribute1288);
                    floatAttribute102=floatAttribute();

                    state._fsp--;

                    stream_floatAttribute.add(floatAttribute102.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:211:37: stringAttribute
                    {
                    pushFollow(FOLLOW_stringAttribute_in_attribute1292);
                    stringAttribute103=stringAttribute();

                    state._fsp--;

                    stream_stringAttribute.add(stringAttribute103.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:211:55: boolAttribute
                    {
                    pushFollow(FOLLOW_boolAttribute_in_attribute1296);
                    boolAttribute104=boolAttribute();

                    state._fsp--;

                    stream_boolAttribute.add(boolAttribute104.getTree());

                    }
                    break;

            }


            SEMI105=(Token)match(input,SEMI,FOLLOW_SEMI_in_attribute1299);  
            stream_SEMI.add(SEMI105);


            // AST REWRITE
            // elements: intAttribute, floatAttribute, stringAttribute, boolAttribute
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 212:2: -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
            {
                // Velvet.g:212:5: ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(ATTR, "ATTR")
                , root_1);

                // Velvet.g:212:12: ( intAttribute )?
                if ( stream_intAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_intAttribute.nextTree());

                }
                stream_intAttribute.reset();

                // Velvet.g:212:26: ( floatAttribute )?
                if ( stream_floatAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_floatAttribute.nextTree());

                }
                stream_floatAttribute.reset();

                // Velvet.g:212:42: ( stringAttribute )?
                if ( stream_stringAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_stringAttribute.nextTree());

                }
                stream_stringAttribute.reset();

                // Velvet.g:212:59: ( boolAttribute )?
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
    // Velvet.g:215:1: intAttribute : VAR_INT ! name ( EQ ! INT )? ;
    public final VelvetParser.intAttribute_return intAttribute() throws RecognitionException {
        VelvetParser.intAttribute_return retval = new VelvetParser.intAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_INT106=null;
        Token EQ108=null;
        Token INT109=null;
        VelvetParser.name_return name107 =null;


        Tree VAR_INT106_tree=null;
        Tree EQ108_tree=null;
        Tree INT109_tree=null;

        try {
            // Velvet.g:215:13: ( VAR_INT ! name ( EQ ! INT )? )
            // Velvet.g:215:16: VAR_INT ! name ( EQ ! INT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_INT106=(Token)match(input,VAR_INT,FOLLOW_VAR_INT_in_intAttribute1328); 

            pushFollow(FOLLOW_name_in_intAttribute1331);
            name107=name();

            state._fsp--;

            adaptor.addChild(root_0, name107.getTree());

            // Velvet.g:215:30: ( EQ ! INT )?
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( (LA31_0==EQ) ) {
                alt31=1;
            }
            switch (alt31) {
                case 1 :
                    // Velvet.g:215:31: EQ ! INT
                    {
                    EQ108=(Token)match(input,EQ,FOLLOW_EQ_in_intAttribute1334); 

                    INT109=(Token)match(input,INT,FOLLOW_INT_in_intAttribute1337); 
                    INT109_tree = 
                    (Tree)adaptor.create(INT109)
                    ;
                    adaptor.addChild(root_0, INT109_tree);


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
    // Velvet.g:216:1: floatAttribute : VAR_FLOAT ! name ( EQ ! FLOAT )? ;
    public final VelvetParser.floatAttribute_return floatAttribute() throws RecognitionException {
        VelvetParser.floatAttribute_return retval = new VelvetParser.floatAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_FLOAT110=null;
        Token EQ112=null;
        Token FLOAT113=null;
        VelvetParser.name_return name111 =null;


        Tree VAR_FLOAT110_tree=null;
        Tree EQ112_tree=null;
        Tree FLOAT113_tree=null;

        try {
            // Velvet.g:216:15: ( VAR_FLOAT ! name ( EQ ! FLOAT )? )
            // Velvet.g:216:18: VAR_FLOAT ! name ( EQ ! FLOAT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_FLOAT110=(Token)match(input,VAR_FLOAT,FOLLOW_VAR_FLOAT_in_floatAttribute1346); 

            pushFollow(FOLLOW_name_in_floatAttribute1349);
            name111=name();

            state._fsp--;

            adaptor.addChild(root_0, name111.getTree());

            // Velvet.g:216:34: ( EQ ! FLOAT )?
            int alt32=2;
            int LA32_0 = input.LA(1);

            if ( (LA32_0==EQ) ) {
                alt32=1;
            }
            switch (alt32) {
                case 1 :
                    // Velvet.g:216:35: EQ ! FLOAT
                    {
                    EQ112=(Token)match(input,EQ,FOLLOW_EQ_in_floatAttribute1352); 

                    FLOAT113=(Token)match(input,FLOAT,FOLLOW_FLOAT_in_floatAttribute1355); 
                    FLOAT113_tree = 
                    (Tree)adaptor.create(FLOAT113)
                    ;
                    adaptor.addChild(root_0, FLOAT113_tree);


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
    // Velvet.g:217:1: stringAttribute : VAR_STRING ! name ( EQ ! STRING )? ;
    public final VelvetParser.stringAttribute_return stringAttribute() throws RecognitionException {
        VelvetParser.stringAttribute_return retval = new VelvetParser.stringAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_STRING114=null;
        Token EQ116=null;
        Token STRING117=null;
        VelvetParser.name_return name115 =null;


        Tree VAR_STRING114_tree=null;
        Tree EQ116_tree=null;
        Tree STRING117_tree=null;

        try {
            // Velvet.g:217:16: ( VAR_STRING ! name ( EQ ! STRING )? )
            // Velvet.g:217:18: VAR_STRING ! name ( EQ ! STRING )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_STRING114=(Token)match(input,VAR_STRING,FOLLOW_VAR_STRING_in_stringAttribute1363); 

            pushFollow(FOLLOW_name_in_stringAttribute1366);
            name115=name();

            state._fsp--;

            adaptor.addChild(root_0, name115.getTree());

            // Velvet.g:217:35: ( EQ ! STRING )?
            int alt33=2;
            int LA33_0 = input.LA(1);

            if ( (LA33_0==EQ) ) {
                alt33=1;
            }
            switch (alt33) {
                case 1 :
                    // Velvet.g:217:36: EQ ! STRING
                    {
                    EQ116=(Token)match(input,EQ,FOLLOW_EQ_in_stringAttribute1369); 

                    STRING117=(Token)match(input,STRING,FOLLOW_STRING_in_stringAttribute1372); 
                    STRING117_tree = 
                    (Tree)adaptor.create(STRING117)
                    ;
                    adaptor.addChild(root_0, STRING117_tree);


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
    // Velvet.g:218:1: boolAttribute : VAR_BOOL ! name ( EQ ! BOOLEAN )? ;
    public final VelvetParser.boolAttribute_return boolAttribute() throws RecognitionException {
        VelvetParser.boolAttribute_return retval = new VelvetParser.boolAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_BOOL118=null;
        Token EQ120=null;
        Token BOOLEAN121=null;
        VelvetParser.name_return name119 =null;


        Tree VAR_BOOL118_tree=null;
        Tree EQ120_tree=null;
        Tree BOOLEAN121_tree=null;

        try {
            // Velvet.g:218:14: ( VAR_BOOL ! name ( EQ ! BOOLEAN )? )
            // Velvet.g:218:17: VAR_BOOL ! name ( EQ ! BOOLEAN )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_BOOL118=(Token)match(input,VAR_BOOL,FOLLOW_VAR_BOOL_in_boolAttribute1381); 

            pushFollow(FOLLOW_name_in_boolAttribute1384);
            name119=name();

            state._fsp--;

            adaptor.addChild(root_0, name119.getTree());

            // Velvet.g:218:32: ( EQ ! BOOLEAN )?
            int alt34=2;
            int LA34_0 = input.LA(1);

            if ( (LA34_0==EQ) ) {
                alt34=1;
            }
            switch (alt34) {
                case 1 :
                    // Velvet.g:218:33: EQ ! BOOLEAN
                    {
                    EQ120=(Token)match(input,EQ,FOLLOW_EQ_in_boolAttribute1387); 

                    BOOLEAN121=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_boolAttribute1390); 
                    BOOLEAN121_tree = 
                    (Tree)adaptor.create(BOOLEAN121)
                    ;
                    adaptor.addChild(root_0, BOOLEAN121_tree);


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
    // Velvet.g:220:1: unaryOp : OP_NOT ;
    public final VelvetParser.unaryOp_return unaryOp() throws RecognitionException {
        VelvetParser.unaryOp_return retval = new VelvetParser.unaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token OP_NOT122=null;

        Tree OP_NOT122_tree=null;

        try {
            // Velvet.g:221:2: ( OP_NOT )
            // Velvet.g:221:4: OP_NOT
            {
            root_0 = (Tree)adaptor.nil();


            OP_NOT122=(Token)match(input,OP_NOT,FOLLOW_OP_NOT_in_unaryOp1402); 
            OP_NOT122_tree = 
            (Tree)adaptor.create(OP_NOT122)
            ;
            adaptor.addChild(root_0, OP_NOT122_tree);


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
    // Velvet.g:224:1: binaryOp : ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT );
    public final VelvetParser.binaryOp_return binaryOp() throws RecognitionException {
        VelvetParser.binaryOp_return retval = new VelvetParser.binaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set123=null;

        Tree set123_tree=null;

        try {
            // Velvet.g:225:2: ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set123=(Token)input.LT(1);

            if ( (input.LA(1) >= OP_AND && input.LA(1) <= OP_IMPLIES)||(input.LA(1) >= OP_OR && input.LA(1) <= OP_XOR) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set123)
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
    // Velvet.g:232:1: attribRelation : ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ );
    public final VelvetParser.attribRelation_return attribRelation() throws RecognitionException {
        VelvetParser.attribRelation_return retval = new VelvetParser.attribRelation_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set124=null;

        Tree set124_tree=null;

        try {
            // Velvet.g:233:2: ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set124=(Token)input.LT(1);

            if ( input.LA(1)==ATTR_OP_EQUALS||input.LA(1)==ATTR_OP_GREATER_EQ||input.LA(1)==ATTR_OP_LESS_EQ ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set124)
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


 

    public static final BitSet FOLLOW_imports_in_velvetModel484 = new BitSet(new long[]{0x0080000200090000L});
    public static final BitSet FOLLOW_instancedef_in_velvetModel487 = new BitSet(new long[]{0x0080000200090000L});
    public static final BitSet FOLLOW_concept_in_velvetModel491 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_cinterface_in_velvetModel493 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_velvetModel496 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_instancedef508 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_instancedef510 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_SEMI_in_instancedef512 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IMPORT_in_imports534 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_imports536 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_SEMI_in_imports538 = new BitSet(new long[]{0x0000004000000002L});
    public static final BitSet FOLLOW_REFINES_in_concept563 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_CONCEPT_in_concept566 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_concept568 = new BitSet(new long[]{0x0C00001000020000L});
    public static final BitSet FOLLOW_COLON_in_concept575 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_conceptBaseExt_in_concept577 = new BitSet(new long[]{0x0C00001000000000L});
    public static final BitSet FOLLOW_START_R_in_concept585 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_conceptInterExt_in_concept587 = new BitSet(new long[]{0x0000000001040000L});
    public static final BitSet FOLLOW_COMMA_in_concept590 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_conceptInterExt_in_concept592 = new BitSet(new long[]{0x0000000001040000L});
    public static final BitSet FOLLOW_END_R_in_concept596 = new BitSet(new long[]{0x0400001000000000L});
    public static final BitSet FOLLOW_IMPL_in_concept604 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_implExt_in_concept606 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_definitions_in_concept613 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_implExt648 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt668 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_COMMA_in_conceptBaseExt671 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt673 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_ID_in_conceptInterExt697 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_conceptInterExt699 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_REFINES_in_cinterface721 = new BitSet(new long[]{0x0000000000010000L});
    public static final BitSet FOLLOW_CINTERFACE_in_cinterface724 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_cinterface726 = new BitSet(new long[]{0x0400000000020000L});
    public static final BitSet FOLLOW_COLON_in_cinterface730 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_interfaceBaseExt_in_cinterface732 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_definitions_in_cinterface736 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt766 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_COMMA_in_interfaceBaseExt769 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt771 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_START_C_in_definitions811 = new BitSet(new long[]{0x8200480220A00010L,0x000000000000001EL});
    public static final BitSet FOLLOW_def_in_definitions813 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_END_C_in_definitions815 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def834 = new BitSet(new long[]{0x8200480220200012L,0x000000000000001EL});
    public static final BitSet FOLLOW_featureGroup_in_def842 = new BitSet(new long[]{0x0000000200200002L,0x000000000000001EL});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def844 = new BitSet(new long[]{0x0000000200200002L,0x000000000000001EL});
    public static final BitSet FOLLOW_USE_in_def853 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_use_in_def855 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_in_def863 = new BitSet(new long[]{0x0000080220200012L,0x000000000000001EL});
    public static final BitSet FOLLOW_feature_in_def866 = new BitSet(new long[]{0x0000080220200012L,0x000000000000001EL});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def870 = new BitSet(new long[]{0x0000080220200012L,0x000000000000001EL});
    public static final BitSet FOLLOW_constraint_in_nonFeatureDefinition890 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_instance_in_nonFeatureDefinition896 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribute_in_nonFeatureDefinition902 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_use914 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_SEMI_in_use916 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_instance935 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_instance937 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_SEMI_in_instance939 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANDATORY_in_feature963 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature965 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature969 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature971 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature975 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature979 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_FEATURE_in_feature986 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_feature988 = new BitSet(new long[]{0x0500000000000000L});
    public static final BitSet FOLLOW_definitions_in_feature991 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SEMI_in_feature995 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_groupType_in_featureGroup1026 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_START_C_in_featureGroup1028 = new BitSet(new long[]{0x0000080020000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup1030 = new BitSet(new long[]{0x0000080020000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup1032 = new BitSet(new long[]{0x0000080020800010L});
    public static final BitSet FOLLOW_END_C_in_featureGroup1035 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONSTRAINT_in_constraint1078 = new BitSet(new long[]{0x0808020600000000L});
    public static final BitSet FOLLOW_ID_in_constraint1082 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_EQ_in_constraint1084 = new BitSet(new long[]{0x0808020600000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraint1090 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_attributeConstraint_in_constraint1094 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_SEMI_in_constraint1097 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1110 = new BitSet(new long[]{0x0037000000000002L});
    public static final BitSet FOLLOW_binaryOp_in_constraintDefinition1113 = new BitSet(new long[]{0x0808000600000000L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1115 = new BitSet(new long[]{0x0037000000000002L});
    public static final BitSet FOLLOW_unaryOp_in_constraintOperand1142 = new BitSet(new long[]{0x0808000600000000L});
    public static final BitSet FOLLOW_START_R_in_constraintOperand1146 = new BitSet(new long[]{0x0808000600000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraintOperand1148 = new BitSet(new long[]{0x0000000001000000L});
    public static final BitSet FOLLOW_END_R_in_constraintOperand1150 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_constraintOperand1154 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribConstraint_in_attributeConstraint1189 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1209 = new BitSet(new long[]{0x0040100000000A80L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1212 = new BitSet(new long[]{0x0000020600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1214 = new BitSet(new long[]{0x0040100000000A80L});
    public static final BitSet FOLLOW_attribRelation_in_attribConstraint1222 = new BitSet(new long[]{0x0000020600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1228 = new BitSet(new long[]{0x0040100000000002L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1231 = new BitSet(new long[]{0x0000020600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1233 = new BitSet(new long[]{0x0040100000000002L});
    public static final BitSet FOLLOW_INT_in_attribNumInstance1265 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_attribNumInstance1272 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_intAttribute_in_attribute1284 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_floatAttribute_in_attribute1288 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_stringAttribute_in_attribute1292 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_boolAttribute_in_attribute1296 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_SEMI_in_attribute1299 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_INT_in_intAttribute1328 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_intAttribute1331 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_intAttribute1334 = new BitSet(new long[]{0x0000020000000000L});
    public static final BitSet FOLLOW_INT_in_intAttribute1337 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_FLOAT_in_floatAttribute1346 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_floatAttribute1349 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_floatAttribute1352 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_FLOAT_in_floatAttribute1355 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_STRING_in_stringAttribute1363 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_stringAttribute1366 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_stringAttribute1369 = new BitSet(new long[]{0x1000000000000000L});
    public static final BitSet FOLLOW_STRING_in_stringAttribute1372 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_BOOL_in_boolAttribute1381 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_boolAttribute1384 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_boolAttribute1387 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_BOOLEAN_in_boolAttribute1390 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_OP_NOT_in_unaryOp1402 = new BitSet(new long[]{0x0000000000000002L});

}