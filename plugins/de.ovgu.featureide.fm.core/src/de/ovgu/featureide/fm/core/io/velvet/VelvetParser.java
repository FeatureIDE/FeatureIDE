// $ANTLR 3.4 Velvet.g 2014-06-04 17:11:44

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
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "ABSTRACT", "ACONSTR", "ATTR", "ATTR_OP_EQUALS", "ATTR_OP_GREATER", "ATTR_OP_GREATER_EQ", "ATTR_OP_LESS", "ATTR_OP_LESS_EQ", "ATTR_OP_NOT_EQUALS", "BASEEXT", "BOOLEAN", "CINTERFACE", "COLON", "COMMA", "CONCEPT", "CONSTR", "CONSTRAINT", "DEF", "END_C", "END_R", "EQ", "ESC_SEQ", "EXPONENT", "FEAT", "FEATURE", "FLOAT", "GROUP", "HEX_DIGIT", "ID", "IDPath", "IMPORTINSTANCE", "IMPORTINTERFACE", "INST", "INT", "INTF", "MANDATORY", "MINUS", "OCTAL_ESC", "ONEOF", "OPERAND", "OP_AND", "OP_EQUIVALENT", "OP_IMPLIES", "OP_NOT", "OP_OR", "OP_XOR", "PLUS", "SEMI", "SOMEOF", "START_C", "START_R", "STRING", "UNARYOP", "UNICODE_ESC", "USE", "USES", "VAR_BOOL", "VAR_FLOAT", "VAR_INT", "VAR_STRING", "WS"
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
    public static final int CINTERFACE=15;
    public static final int COLON=16;
    public static final int COMMA=17;
    public static final int CONCEPT=18;
    public static final int CONSTR=19;
    public static final int CONSTRAINT=20;
    public static final int DEF=21;
    public static final int END_C=22;
    public static final int END_R=23;
    public static final int EQ=24;
    public static final int ESC_SEQ=25;
    public static final int EXPONENT=26;
    public static final int FEAT=27;
    public static final int FEATURE=28;
    public static final int FLOAT=29;
    public static final int GROUP=30;
    public static final int HEX_DIGIT=31;
    public static final int ID=32;
    public static final int IDPath=33;
    public static final int IMPORTINSTANCE=34;
    public static final int IMPORTINTERFACE=35;
    public static final int INST=36;
    public static final int INT=37;
    public static final int INTF=38;
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
    public static final int SEMI=51;
    public static final int SOMEOF=52;
    public static final int START_C=53;
    public static final int START_R=54;
    public static final int STRING=55;
    public static final int UNARYOP=56;
    public static final int UNICODE_ESC=57;
    public static final int USE=58;
    public static final int USES=59;
    public static final int VAR_BOOL=60;
    public static final int VAR_FLOAT=61;
    public static final int VAR_INT=62;
    public static final int VAR_STRING=63;
    public static final int WS=64;

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
    // Velvet.g:78:1: velvetModel : ( concept | cinterface ) EOF ;
    public final VelvetParser.velvetModel_return velvetModel() throws RecognitionException {
        VelvetParser.velvetModel_return retval = new VelvetParser.velvetModel_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token EOF3=null;
        VelvetParser.concept_return concept1 =null;

        VelvetParser.cinterface_return cinterface2 =null;


        Tree EOF3_tree=null;

        try {
            // Velvet.g:79:2: ( ( concept | cinterface ) EOF )
            // Velvet.g:79:4: ( concept | cinterface ) EOF
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:79:4: ( concept | cinterface )
            int alt1=2;
            int LA1_0 = input.LA(1);

            if ( (LA1_0==CONCEPT) ) {
                alt1=1;
            }
            else if ( (LA1_0==CINTERFACE) ) {
                alt1=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 1, 0, input);

                throw nvae;

            }
            switch (alt1) {
                case 1 :
                    // Velvet.g:79:5: concept
                    {
                    pushFollow(FOLLOW_concept_in_velvetModel466);
                    concept1=concept();

                    state._fsp--;

                    adaptor.addChild(root_0, concept1.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:79:13: cinterface
                    {
                    pushFollow(FOLLOW_cinterface_in_velvetModel468);
                    cinterface2=cinterface();

                    state._fsp--;

                    adaptor.addChild(root_0, cinterface2.getTree());

                    }
                    break;

            }


            EOF3=(Token)match(input,EOF,FOLLOW_EOF_in_velvetModel471); 
            EOF3_tree = 
            (Tree)adaptor.create(EOF3)
            ;
            adaptor.addChild(root_0, EOF3_tree);


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


    public static class concept_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "concept"
    // Velvet.g:82:1: concept : CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports )? ( interfaceImports )? definitions -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? definitions ) ;
    public final VelvetParser.concept_return concept() throws RecognitionException {
        VelvetParser.concept_return retval = new VelvetParser.concept_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token CONCEPT4=null;
        Token ID5=null;
        Token COLON6=null;
        VelvetParser.conceptBaseExt_return conceptBaseExt7 =null;

        VelvetParser.instanceImports_return instanceImports8 =null;

        VelvetParser.interfaceImports_return interfaceImports9 =null;

        VelvetParser.definitions_return definitions10 =null;


        Tree CONCEPT4_tree=null;
        Tree ID5_tree=null;
        Tree COLON6_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_CONCEPT=new RewriteRuleTokenStream(adaptor,"token CONCEPT");
        RewriteRuleSubtreeStream stream_conceptBaseExt=new RewriteRuleSubtreeStream(adaptor,"rule conceptBaseExt");
        RewriteRuleSubtreeStream stream_instanceImports=new RewriteRuleSubtreeStream(adaptor,"rule instanceImports");
        RewriteRuleSubtreeStream stream_interfaceImports=new RewriteRuleSubtreeStream(adaptor,"rule interfaceImports");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:83:2: ( CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports )? ( interfaceImports )? definitions -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? definitions ) )
            // Velvet.g:83:4: CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports )? ( interfaceImports )? definitions
            {
            CONCEPT4=(Token)match(input,CONCEPT,FOLLOW_CONCEPT_in_concept484);  
            stream_CONCEPT.add(CONCEPT4);


            ID5=(Token)match(input,ID,FOLLOW_ID_in_concept486);  
            stream_ID.add(ID5);


            // Velvet.g:84:3: ( COLON conceptBaseExt )?
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0==COLON) ) {
                alt2=1;
            }
            switch (alt2) {
                case 1 :
                    // Velvet.g:84:4: COLON conceptBaseExt
                    {
                    COLON6=(Token)match(input,COLON,FOLLOW_COLON_in_concept493);  
                    stream_COLON.add(COLON6);


                    pushFollow(FOLLOW_conceptBaseExt_in_concept495);
                    conceptBaseExt7=conceptBaseExt();

                    state._fsp--;

                    stream_conceptBaseExt.add(conceptBaseExt7.getTree());

                    }
                    break;

            }


            // Velvet.g:84:27: ( instanceImports )?
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0==IMPORTINSTANCE) ) {
                alt3=1;
            }
            switch (alt3) {
                case 1 :
                    // Velvet.g:84:28: instanceImports
                    {
                    pushFollow(FOLLOW_instanceImports_in_concept500);
                    instanceImports8=instanceImports();

                    state._fsp--;

                    stream_instanceImports.add(instanceImports8.getTree());

                    }
                    break;

            }


            // Velvet.g:84:46: ( interfaceImports )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0==IMPORTINTERFACE) ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // Velvet.g:84:47: interfaceImports
                    {
                    pushFollow(FOLLOW_interfaceImports_in_concept505);
                    interfaceImports9=interfaceImports();

                    state._fsp--;

                    stream_interfaceImports.add(interfaceImports9.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_concept512);
            definitions10=definitions();

            state._fsp--;

            stream_definitions.add(definitions10.getTree());

            // AST REWRITE
            // elements: CONCEPT, instanceImports, interfaceImports, ID, definitions, conceptBaseExt
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 86:2: -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? definitions )
            {
                // Velvet.g:86:5: ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CONCEPT.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:86:18: ( conceptBaseExt )?
                if ( stream_conceptBaseExt.hasNext() ) {
                    adaptor.addChild(root_1, stream_conceptBaseExt.nextTree());

                }
                stream_conceptBaseExt.reset();

                // Velvet.g:86:34: ( instanceImports )?
                if ( stream_instanceImports.hasNext() ) {
                    adaptor.addChild(root_1, stream_instanceImports.nextTree());

                }
                stream_instanceImports.reset();

                // Velvet.g:86:51: ( interfaceImports )?
                if ( stream_interfaceImports.hasNext() ) {
                    adaptor.addChild(root_1, stream_interfaceImports.nextTree());

                }
                stream_interfaceImports.reset();

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
    // Velvet.g:89:1: conceptBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
    public final VelvetParser.conceptBaseExt_return conceptBaseExt() throws RecognitionException {
        VelvetParser.conceptBaseExt_return retval = new VelvetParser.conceptBaseExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID11=null;
        Token COMMA12=null;
        Token ID13=null;

        Tree ID11_tree=null;
        Tree COMMA12_tree=null;
        Tree ID13_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

        try {
            // Velvet.g:90:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:90:4: ID ( COMMA ID )*
            {
            ID11=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt544);  
            stream_ID.add(ID11);


            // Velvet.g:90:7: ( COMMA ID )*
            loop5:
            do {
                int alt5=2;
                int LA5_0 = input.LA(1);

                if ( (LA5_0==COMMA) ) {
                    alt5=1;
                }


                switch (alt5) {
            	case 1 :
            	    // Velvet.g:90:8: COMMA ID
            	    {
            	    COMMA12=(Token)match(input,COMMA,FOLLOW_COMMA_in_conceptBaseExt547);  
            	    stream_COMMA.add(COMMA12);


            	    ID13=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt549);  
            	    stream_ID.add(ID13);


            	    }
            	    break;

            	default :
            	    break loop5;
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
            // 91:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:91:5: ^( BASEEXT ( ID )+ )
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


    public static class instanceImports_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "instanceImports"
    // Velvet.g:94:1: instanceImports : IMPORTINSTANCE ID name ( COMMA ID name )* -> ^( INST ( ID name )+ ) ;
    public final VelvetParser.instanceImports_return instanceImports() throws RecognitionException {
        VelvetParser.instanceImports_return retval = new VelvetParser.instanceImports_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token IMPORTINSTANCE14=null;
        Token ID15=null;
        Token COMMA17=null;
        Token ID18=null;
        VelvetParser.name_return name16 =null;

        VelvetParser.name_return name19 =null;


        Tree IMPORTINSTANCE14_tree=null;
        Tree ID15_tree=null;
        Tree COMMA17_tree=null;
        Tree ID18_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
        RewriteRuleTokenStream stream_IMPORTINSTANCE=new RewriteRuleTokenStream(adaptor,"token IMPORTINSTANCE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:95:2: ( IMPORTINSTANCE ID name ( COMMA ID name )* -> ^( INST ( ID name )+ ) )
            // Velvet.g:95:4: IMPORTINSTANCE ID name ( COMMA ID name )*
            {
            IMPORTINSTANCE14=(Token)match(input,IMPORTINSTANCE,FOLLOW_IMPORTINSTANCE_in_instanceImports574);  
            stream_IMPORTINSTANCE.add(IMPORTINSTANCE14);


            ID15=(Token)match(input,ID,FOLLOW_ID_in_instanceImports576);  
            stream_ID.add(ID15);


            pushFollow(FOLLOW_name_in_instanceImports578);
            name16=name();

            state._fsp--;

            stream_name.add(name16.getTree());

            // Velvet.g:95:27: ( COMMA ID name )*
            loop6:
            do {
                int alt6=2;
                int LA6_0 = input.LA(1);

                if ( (LA6_0==COMMA) ) {
                    alt6=1;
                }


                switch (alt6) {
            	case 1 :
            	    // Velvet.g:95:28: COMMA ID name
            	    {
            	    COMMA17=(Token)match(input,COMMA,FOLLOW_COMMA_in_instanceImports581);  
            	    stream_COMMA.add(COMMA17);


            	    ID18=(Token)match(input,ID,FOLLOW_ID_in_instanceImports583);  
            	    stream_ID.add(ID18);


            	    pushFollow(FOLLOW_name_in_instanceImports585);
            	    name19=name();

            	    state._fsp--;

            	    stream_name.add(name19.getTree());

            	    }
            	    break;

            	default :
            	    break loop6;
                }
            } while (true);


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
            // 96:2: -> ^( INST ( ID name )+ )
            {
                // Velvet.g:96:5: ^( INST ( ID name )+ )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(INST, "INST")
                , root_1);

                if ( !(stream_ID.hasNext()||stream_name.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_ID.hasNext()||stream_name.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ID.nextNode()
                    );

                    adaptor.addChild(root_1, stream_name.nextTree());

                }
                stream_ID.reset();
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
    // $ANTLR end "instanceImports"


    public static class interfaceImports_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "interfaceImports"
    // Velvet.g:99:1: interfaceImports : IMPORTINTERFACE ID name ( COMMA ID name )* -> ^( INTF ( ID name )+ ) ;
    public final VelvetParser.interfaceImports_return interfaceImports() throws RecognitionException {
        VelvetParser.interfaceImports_return retval = new VelvetParser.interfaceImports_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token IMPORTINTERFACE20=null;
        Token ID21=null;
        Token COMMA23=null;
        Token ID24=null;
        VelvetParser.name_return name22 =null;

        VelvetParser.name_return name25 =null;


        Tree IMPORTINTERFACE20_tree=null;
        Tree ID21_tree=null;
        Tree COMMA23_tree=null;
        Tree ID24_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
        RewriteRuleTokenStream stream_IMPORTINTERFACE=new RewriteRuleTokenStream(adaptor,"token IMPORTINTERFACE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:100:2: ( IMPORTINTERFACE ID name ( COMMA ID name )* -> ^( INTF ( ID name )+ ) )
            // Velvet.g:100:4: IMPORTINTERFACE ID name ( COMMA ID name )*
            {
            IMPORTINTERFACE20=(Token)match(input,IMPORTINTERFACE,FOLLOW_IMPORTINTERFACE_in_interfaceImports614);  
            stream_IMPORTINTERFACE.add(IMPORTINTERFACE20);


            ID21=(Token)match(input,ID,FOLLOW_ID_in_interfaceImports616);  
            stream_ID.add(ID21);


            pushFollow(FOLLOW_name_in_interfaceImports618);
            name22=name();

            state._fsp--;

            stream_name.add(name22.getTree());

            // Velvet.g:100:28: ( COMMA ID name )*
            loop7:
            do {
                int alt7=2;
                int LA7_0 = input.LA(1);

                if ( (LA7_0==COMMA) ) {
                    alt7=1;
                }


                switch (alt7) {
            	case 1 :
            	    // Velvet.g:100:29: COMMA ID name
            	    {
            	    COMMA23=(Token)match(input,COMMA,FOLLOW_COMMA_in_interfaceImports621);  
            	    stream_COMMA.add(COMMA23);


            	    ID24=(Token)match(input,ID,FOLLOW_ID_in_interfaceImports623);  
            	    stream_ID.add(ID24);


            	    pushFollow(FOLLOW_name_in_interfaceImports625);
            	    name25=name();

            	    state._fsp--;

            	    stream_name.add(name25.getTree());

            	    }
            	    break;

            	default :
            	    break loop7;
                }
            } while (true);


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
            // 101:2: -> ^( INTF ( ID name )+ )
            {
                // Velvet.g:101:5: ^( INTF ( ID name )+ )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(INTF, "INTF")
                , root_1);

                if ( !(stream_name.hasNext()||stream_ID.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_name.hasNext()||stream_ID.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ID.nextNode()
                    );

                    adaptor.addChild(root_1, stream_name.nextTree());

                }
                stream_name.reset();
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
    // $ANTLR end "interfaceImports"


    public static class cinterface_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "cinterface"
    // Velvet.g:104:1: cinterface : CINTERFACE ID ( COLON interfaceBaseExt )? definitions -> ^( CINTERFACE ID ( interfaceBaseExt )? definitions ) ;
    public final VelvetParser.cinterface_return cinterface() throws RecognitionException {
        VelvetParser.cinterface_return retval = new VelvetParser.cinterface_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token CINTERFACE26=null;
        Token ID27=null;
        Token COLON28=null;
        VelvetParser.interfaceBaseExt_return interfaceBaseExt29 =null;

        VelvetParser.definitions_return definitions30 =null;


        Tree CINTERFACE26_tree=null;
        Tree ID27_tree=null;
        Tree COLON28_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_CINTERFACE=new RewriteRuleTokenStream(adaptor,"token CINTERFACE");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        RewriteRuleSubtreeStream stream_interfaceBaseExt=new RewriteRuleSubtreeStream(adaptor,"rule interfaceBaseExt");
        try {
            // Velvet.g:104:12: ( CINTERFACE ID ( COLON interfaceBaseExt )? definitions -> ^( CINTERFACE ID ( interfaceBaseExt )? definitions ) )
            // Velvet.g:104:14: CINTERFACE ID ( COLON interfaceBaseExt )? definitions
            {
            CINTERFACE26=(Token)match(input,CINTERFACE,FOLLOW_CINTERFACE_in_cinterface652);  
            stream_CINTERFACE.add(CINTERFACE26);


            ID27=(Token)match(input,ID,FOLLOW_ID_in_cinterface654);  
            stream_ID.add(ID27);


            // Velvet.g:104:29: ( COLON interfaceBaseExt )?
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==COLON) ) {
                alt8=1;
            }
            switch (alt8) {
                case 1 :
                    // Velvet.g:104:30: COLON interfaceBaseExt
                    {
                    COLON28=(Token)match(input,COLON,FOLLOW_COLON_in_cinterface658);  
                    stream_COLON.add(COLON28);


                    pushFollow(FOLLOW_interfaceBaseExt_in_cinterface660);
                    interfaceBaseExt29=interfaceBaseExt();

                    state._fsp--;

                    stream_interfaceBaseExt.add(interfaceBaseExt29.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_cinterface664);
            definitions30=definitions();

            state._fsp--;

            stream_definitions.add(definitions30.getTree());

            // AST REWRITE
            // elements: interfaceBaseExt, ID, definitions, CINTERFACE
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 105:2: -> ^( CINTERFACE ID ( interfaceBaseExt )? definitions )
            {
                // Velvet.g:105:5: ^( CINTERFACE ID ( interfaceBaseExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CINTERFACE.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:105:21: ( interfaceBaseExt )?
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
    // Velvet.g:108:1: interfaceBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
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
            // Velvet.g:109:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:109:4: ID ( COMMA ID )*
            {
            ID31=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt691);  
            stream_ID.add(ID31);


            // Velvet.g:109:7: ( COMMA ID )*
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( (LA9_0==COMMA) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // Velvet.g:109:8: COMMA ID
            	    {
            	    COMMA32=(Token)match(input,COMMA,FOLLOW_COMMA_in_interfaceBaseExt694);  
            	    stream_COMMA.add(COMMA32);


            	    ID33=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt696);  
            	    stream_ID.add(ID33);


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
    // $ANTLR end "interfaceBaseExt"


    public static class name_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "name"
    // Velvet.g:113:1: name : ( ID | IDPath );
    public final VelvetParser.name_return name() throws RecognitionException {
        VelvetParser.name_return retval = new VelvetParser.name_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set34=null;

        Tree set34_tree=null;

        try {
            // Velvet.g:113:5: ( ID | IDPath )
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
    // Velvet.g:117:1: definitions : START_C def END_C -> ^( DEF def ) ;
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
            // Velvet.g:118:2: ( START_C def END_C -> ^( DEF def ) )
            // Velvet.g:118:4: START_C def END_C
            {
            START_C35=(Token)match(input,START_C,FOLLOW_START_C_in_definitions736);  
            stream_START_C.add(START_C35);


            pushFollow(FOLLOW_def_in_definitions738);
            def36=def();

            state._fsp--;

            stream_def.add(def36.getTree());

            END_C37=(Token)match(input,END_C,FOLLOW_END_C_in_definitions740);  
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
            // 119:2: -> ^( DEF def )
            {
                // Velvet.g:119:5: ^( DEF def )
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
    // Velvet.g:122:1: def : ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? ;
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
            // Velvet.g:122:5: ( ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? )
            // Velvet.g:122:7: ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:122:7: ( nonFeatureDefinition )*
            loop10:
            do {
                int alt10=2;
                int LA10_0 = input.LA(1);

                if ( (LA10_0==CONSTRAINT||LA10_0==USE||(LA10_0 >= VAR_BOOL && LA10_0 <= VAR_STRING)) ) {
                    alt10=1;
                }


                switch (alt10) {
            	case 1 :
            	    // Velvet.g:122:7: nonFeatureDefinition
            	    {
            	    pushFollow(FOLLOW_nonFeatureDefinition_in_def759);
            	    nonFeatureDefinition38=nonFeatureDefinition();

            	    state._fsp--;

            	    adaptor.addChild(root_0, nonFeatureDefinition38.getTree());

            	    }
            	    break;

            	default :
            	    break loop10;
                }
            } while (true);


            // Velvet.g:122:29: ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            int alt13=3;
            int LA13_0 = input.LA(1);

            if ( (LA13_0==ONEOF||LA13_0==SOMEOF) ) {
                alt13=1;
            }
            else if ( (LA13_0==ABSTRACT||LA13_0==FEATURE||LA13_0==MANDATORY) ) {
                alt13=2;
            }
            switch (alt13) {
                case 1 :
                    // Velvet.g:123:3: ( featureGroup ( nonFeatureDefinition )* )
                    {
                    // Velvet.g:123:3: ( featureGroup ( nonFeatureDefinition )* )
                    // Velvet.g:123:4: featureGroup ( nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_featureGroup_in_def767);
                    featureGroup39=featureGroup();

                    state._fsp--;

                    adaptor.addChild(root_0, featureGroup39.getTree());

                    // Velvet.g:123:17: ( nonFeatureDefinition )*
                    loop11:
                    do {
                        int alt11=2;
                        int LA11_0 = input.LA(1);

                        if ( (LA11_0==CONSTRAINT||LA11_0==USE||(LA11_0 >= VAR_BOOL && LA11_0 <= VAR_STRING)) ) {
                            alt11=1;
                        }


                        switch (alt11) {
                    	case 1 :
                    	    // Velvet.g:123:17: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def769);
                    	    nonFeatureDefinition40=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition40.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop11;
                        }
                    } while (true);


                    }


                    }
                    break;
                case 2 :
                    // Velvet.g:124:3: ( feature ( feature | nonFeatureDefinition )* )
                    {
                    // Velvet.g:124:3: ( feature ( feature | nonFeatureDefinition )* )
                    // Velvet.g:124:4: feature ( feature | nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_feature_in_def778);
                    feature41=feature();

                    state._fsp--;

                    adaptor.addChild(root_0, feature41.getTree());

                    // Velvet.g:124:12: ( feature | nonFeatureDefinition )*
                    loop12:
                    do {
                        int alt12=3;
                        int LA12_0 = input.LA(1);

                        if ( (LA12_0==ABSTRACT||LA12_0==FEATURE||LA12_0==MANDATORY) ) {
                            alt12=1;
                        }
                        else if ( (LA12_0==CONSTRAINT||LA12_0==USE||(LA12_0 >= VAR_BOOL && LA12_0 <= VAR_STRING)) ) {
                            alt12=2;
                        }


                        switch (alt12) {
                    	case 1 :
                    	    // Velvet.g:124:13: feature
                    	    {
                    	    pushFollow(FOLLOW_feature_in_def781);
                    	    feature42=feature();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, feature42.getTree());

                    	    }
                    	    break;
                    	case 2 :
                    	    // Velvet.g:124:23: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def785);
                    	    nonFeatureDefinition43=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition43.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop12;
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
    // Velvet.g:127:1: nonFeatureDefinition : ( constraint | use | attribute );
    public final VelvetParser.nonFeatureDefinition_return nonFeatureDefinition() throws RecognitionException {
        VelvetParser.nonFeatureDefinition_return retval = new VelvetParser.nonFeatureDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraint_return constraint44 =null;

        VelvetParser.use_return use45 =null;

        VelvetParser.attribute_return attribute46 =null;



        try {
            // Velvet.g:128:2: ( constraint | use | attribute )
            int alt14=3;
            switch ( input.LA(1) ) {
            case CONSTRAINT:
                {
                alt14=1;
                }
                break;
            case USE:
                {
                alt14=2;
                }
                break;
            case VAR_BOOL:
            case VAR_FLOAT:
            case VAR_INT:
            case VAR_STRING:
                {
                alt14=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 14, 0, input);

                throw nvae;

            }

            switch (alt14) {
                case 1 :
                    // Velvet.g:128:4: constraint
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_constraint_in_nonFeatureDefinition805);
                    constraint44=constraint();

                    state._fsp--;

                    adaptor.addChild(root_0, constraint44.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:129:4: use
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_use_in_nonFeatureDefinition810);
                    use45=use();

                    state._fsp--;

                    adaptor.addChild(root_0, use45.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:130:4: attribute
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_attribute_in_nonFeatureDefinition815);
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


    public static class use_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "use"
    // Velvet.g:133:1: use : USE name SEMI -> ^( USES name ) ;
    public final VelvetParser.use_return use() throws RecognitionException {
        VelvetParser.use_return retval = new VelvetParser.use_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token USE47=null;
        Token SEMI49=null;
        VelvetParser.name_return name48 =null;


        Tree USE47_tree=null;
        Tree SEMI49_tree=null;
        RewriteRuleTokenStream stream_USE=new RewriteRuleTokenStream(adaptor,"token USE");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:133:5: ( USE name SEMI -> ^( USES name ) )
            // Velvet.g:133:7: USE name SEMI
            {
            USE47=(Token)match(input,USE,FOLLOW_USE_in_use827);  
            stream_USE.add(USE47);


            pushFollow(FOLLOW_name_in_use829);
            name48=name();

            state._fsp--;

            stream_name.add(name48.getTree());

            SEMI49=(Token)match(input,SEMI,FOLLOW_SEMI_in_use831);  
            stream_SEMI.add(SEMI49);


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
            // 134:2: -> ^( USES name )
            {
                // Velvet.g:134:5: ^( USES name )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(USES, "USES")
                , root_1);

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
    // $ANTLR end "use"


    public static class feature_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "feature"
    // Velvet.g:137:1: feature : ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) ;
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
            // Velvet.g:138:2: ( ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) )
            // Velvet.g:138:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI )
            {
            // Velvet.g:138:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )?
            int alt15=5;
            int LA15_0 = input.LA(1);

            if ( (LA15_0==MANDATORY) ) {
                int LA15_1 = input.LA(2);

                if ( (LA15_1==ABSTRACT) ) {
                    alt15=1;
                }
                else if ( (LA15_1==FEATURE) ) {
                    alt15=3;
                }
            }
            else if ( (LA15_0==ABSTRACT) ) {
                int LA15_2 = input.LA(2);

                if ( (LA15_2==MANDATORY) ) {
                    alt15=2;
                }
                else if ( (LA15_2==FEATURE) ) {
                    alt15=4;
                }
            }
            switch (alt15) {
                case 1 :
                    // Velvet.g:138:5: MANDATORY ABSTRACT
                    {
                    MANDATORY50=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature852);  
                    stream_MANDATORY.add(MANDATORY50);


                    ABSTRACT51=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature854);  
                    stream_ABSTRACT.add(ABSTRACT51);


                    }
                    break;
                case 2 :
                    // Velvet.g:138:26: ABSTRACT MANDATORY
                    {
                    ABSTRACT52=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature858);  
                    stream_ABSTRACT.add(ABSTRACT52);


                    MANDATORY53=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature860);  
                    stream_MANDATORY.add(MANDATORY53);


                    }
                    break;
                case 3 :
                    // Velvet.g:138:47: MANDATORY
                    {
                    MANDATORY54=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature864);  
                    stream_MANDATORY.add(MANDATORY54);


                    }
                    break;
                case 4 :
                    // Velvet.g:138:59: ABSTRACT
                    {
                    ABSTRACT55=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature868);  
                    stream_ABSTRACT.add(ABSTRACT55);


                    }
                    break;

            }


            FEATURE56=(Token)match(input,FEATURE,FOLLOW_FEATURE_in_feature875);  
            stream_FEATURE.add(FEATURE56);


            pushFollow(FOLLOW_name_in_feature877);
            name57=name();

            state._fsp--;

            stream_name.add(name57.getTree());

            // Velvet.g:139:17: ( definitions | SEMI )
            int alt16=2;
            int LA16_0 = input.LA(1);

            if ( (LA16_0==START_C) ) {
                alt16=1;
            }
            else if ( (LA16_0==SEMI) ) {
                alt16=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 16, 0, input);

                throw nvae;

            }
            switch (alt16) {
                case 1 :
                    // Velvet.g:139:18: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_feature880);
                    definitions58=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions58.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:139:32: SEMI
                    {
                    SEMI59=(Token)match(input,SEMI,FOLLOW_SEMI_in_feature884);  
                    stream_SEMI.add(SEMI59);


                    }
                    break;

            }


            // AST REWRITE
            // elements: name, definitions, ABSTRACT, MANDATORY
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 140:2: -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
            {
                // Velvet.g:140:5: ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(FEAT, "FEAT")
                , root_1);

                adaptor.addChild(root_1, stream_name.nextTree());

                // Velvet.g:140:17: ( MANDATORY )?
                if ( stream_MANDATORY.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_MANDATORY.nextNode()
                    );

                }
                stream_MANDATORY.reset();

                // Velvet.g:140:28: ( ABSTRACT )?
                if ( stream_ABSTRACT.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ABSTRACT.nextNode()
                    );

                }
                stream_ABSTRACT.reset();

                // Velvet.g:140:38: ( definitions )?
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
    // Velvet.g:143:1: featureGroup : groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) ;
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
            // Velvet.g:144:2: ( groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) )
            // Velvet.g:144:4: groupType START_C feature ( feature )+ END_C
            {
            pushFollow(FOLLOW_groupType_in_featureGroup915);
            groupType60=groupType();

            state._fsp--;

            stream_groupType.add(groupType60.getTree());

            START_C61=(Token)match(input,START_C,FOLLOW_START_C_in_featureGroup917);  
            stream_START_C.add(START_C61);


            pushFollow(FOLLOW_feature_in_featureGroup919);
            feature62=feature();

            state._fsp--;

            stream_feature.add(feature62.getTree());

            // Velvet.g:144:30: ( feature )+
            int cnt17=0;
            loop17:
            do {
                int alt17=2;
                int LA17_0 = input.LA(1);

                if ( (LA17_0==ABSTRACT||LA17_0==FEATURE||LA17_0==MANDATORY) ) {
                    alt17=1;
                }


                switch (alt17) {
            	case 1 :
            	    // Velvet.g:144:30: feature
            	    {
            	    pushFollow(FOLLOW_feature_in_featureGroup921);
            	    feature63=feature();

            	    state._fsp--;

            	    stream_feature.add(feature63.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt17 >= 1 ) break loop17;
                        EarlyExitException eee =
                            new EarlyExitException(17, input);
                        throw eee;
                }
                cnt17++;
            } while (true);


            END_C64=(Token)match(input,END_C,FOLLOW_END_C_in_featureGroup924);  
            stream_END_C.add(END_C64);


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
            // 145:2: -> ^( GROUP groupType feature ( feature )+ )
            {
                // Velvet.g:145:5: ^( GROUP groupType feature ( feature )+ )
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
    // Velvet.g:148:1: groupType : ( SOMEOF | ONEOF );
    public final VelvetParser.groupType_return groupType() throws RecognitionException {
        VelvetParser.groupType_return retval = new VelvetParser.groupType_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set65=null;

        Tree set65_tree=null;

        try {
            // Velvet.g:149:2: ( SOMEOF | ONEOF )
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
    // Velvet.g:153:1: constraint : CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !;
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
            // Velvet.g:154:2: ( CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !)
            // Velvet.g:154:4: CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !
            {
            root_0 = (Tree)adaptor.nil();


            CONSTRAINT66=(Token)match(input,CONSTRAINT,FOLLOW_CONSTRAINT_in_constraint967); 
            CONSTRAINT66_tree = 
            (Tree)adaptor.create(CONSTRAINT66)
            ;
            root_0 = (Tree)adaptor.becomeRoot(CONSTRAINT66_tree, root_0);


            // Velvet.g:154:16: ( ID EQ !)?
            int alt18=2;
            int LA18_0 = input.LA(1);

            if ( (LA18_0==ID) ) {
                int LA18_1 = input.LA(2);

                if ( (LA18_1==EQ) ) {
                    alt18=1;
                }
            }
            switch (alt18) {
                case 1 :
                    // Velvet.g:154:17: ID EQ !
                    {
                    ID67=(Token)match(input,ID,FOLLOW_ID_in_constraint971); 
                    ID67_tree = 
                    (Tree)adaptor.create(ID67)
                    ;
                    adaptor.addChild(root_0, ID67_tree);


                    EQ68=(Token)match(input,EQ,FOLLOW_EQ_in_constraint973); 

                    }
                    break;

            }


            // Velvet.g:154:26: ( constraintDefinition | attributeConstraint )
            int alt19=2;
            switch ( input.LA(1) ) {
            case OP_NOT:
            case START_R:
                {
                alt19=1;
                }
                break;
            case ID:
            case IDPath:
                {
                int LA19_2 = input.LA(2);

                if ( ((LA19_2 >= OP_AND && LA19_2 <= OP_IMPLIES)||(LA19_2 >= OP_OR && LA19_2 <= OP_XOR)||LA19_2==SEMI) ) {
                    alt19=1;
                }
                else if ( (LA19_2==ATTR_OP_EQUALS||LA19_2==ATTR_OP_GREATER_EQ||LA19_2==ATTR_OP_LESS_EQ||LA19_2==MINUS||LA19_2==PLUS) ) {
                    alt19=2;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 19, 2, input);

                    throw nvae;

                }
                }
                break;
            case INT:
                {
                alt19=2;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 19, 0, input);

                throw nvae;

            }

            switch (alt19) {
                case 1 :
                    // Velvet.g:154:27: constraintDefinition
                    {
                    pushFollow(FOLLOW_constraintDefinition_in_constraint979);
                    constraintDefinition69=constraintDefinition();

                    state._fsp--;

                    adaptor.addChild(root_0, constraintDefinition69.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:154:50: attributeConstraint
                    {
                    pushFollow(FOLLOW_attributeConstraint_in_constraint983);
                    attributeConstraint70=attributeConstraint();

                    state._fsp--;

                    adaptor.addChild(root_0, attributeConstraint70.getTree());

                    }
                    break;

            }


            SEMI71=(Token)match(input,SEMI,FOLLOW_SEMI_in_constraint986); 

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
    // Velvet.g:157:1: constraintDefinition : constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) ;
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
            // Velvet.g:158:2: ( constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) )
            // Velvet.g:158:4: constraintOperand ( binaryOp constraintOperand )*
            {
            pushFollow(FOLLOW_constraintOperand_in_constraintDefinition999);
            constraintOperand72=constraintOperand();

            state._fsp--;

            stream_constraintOperand.add(constraintOperand72.getTree());

            // Velvet.g:158:22: ( binaryOp constraintOperand )*
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( ((LA20_0 >= OP_AND && LA20_0 <= OP_IMPLIES)||(LA20_0 >= OP_OR && LA20_0 <= OP_XOR)) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // Velvet.g:158:23: binaryOp constraintOperand
            	    {
            	    pushFollow(FOLLOW_binaryOp_in_constraintDefinition1002);
            	    binaryOp73=binaryOp();

            	    state._fsp--;

            	    stream_binaryOp.add(binaryOp73.getTree());

            	    pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1004);
            	    constraintOperand74=constraintOperand();

            	    state._fsp--;

            	    stream_constraintOperand.add(constraintOperand74.getTree());

            	    }
            	    break;

            	default :
            	    break loop20;
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
            // 159:2: -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
            {
                // Velvet.g:159:5: ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
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

                // Velvet.g:159:33: ( binaryOp )*
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
    // Velvet.g:162:1: constraintOperand : ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? ;
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
            // Velvet.g:162:19: ( ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? )
            // Velvet.g:162:21: ( unaryOp )* ( START_R constraintDefinition END_R | name )
            {
            // Velvet.g:162:21: ( unaryOp )*
            loop21:
            do {
                int alt21=2;
                int LA21_0 = input.LA(1);

                if ( (LA21_0==OP_NOT) ) {
                    alt21=1;
                }


                switch (alt21) {
            	case 1 :
            	    // Velvet.g:162:21: unaryOp
            	    {
            	    pushFollow(FOLLOW_unaryOp_in_constraintOperand1031);
            	    unaryOp75=unaryOp();

            	    state._fsp--;

            	    stream_unaryOp.add(unaryOp75.getTree());

            	    }
            	    break;

            	default :
            	    break loop21;
                }
            } while (true);


            // Velvet.g:162:30: ( START_R constraintDefinition END_R | name )
            int alt22=2;
            int LA22_0 = input.LA(1);

            if ( (LA22_0==START_R) ) {
                alt22=1;
            }
            else if ( ((LA22_0 >= ID && LA22_0 <= IDPath)) ) {
                alt22=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 22, 0, input);

                throw nvae;

            }
            switch (alt22) {
                case 1 :
                    // Velvet.g:162:31: START_R constraintDefinition END_R
                    {
                    START_R76=(Token)match(input,START_R,FOLLOW_START_R_in_constraintOperand1035);  
                    stream_START_R.add(START_R76);


                    pushFollow(FOLLOW_constraintDefinition_in_constraintOperand1037);
                    constraintDefinition77=constraintDefinition();

                    state._fsp--;

                    stream_constraintDefinition.add(constraintDefinition77.getTree());

                    END_R78=(Token)match(input,END_R,FOLLOW_END_R_in_constraintOperand1039);  
                    stream_END_R.add(END_R78);


                    }
                    break;
                case 2 :
                    // Velvet.g:162:68: name
                    {
                    pushFollow(FOLLOW_name_in_constraintOperand1043);
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
            // 163:2: -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )?
            {
                // Velvet.g:163:5: ( constraintDefinition )?
                if ( stream_constraintDefinition.hasNext() ) {
                    adaptor.addChild(root_0, stream_constraintDefinition.nextTree());

                }
                stream_constraintDefinition.reset();

                // Velvet.g:163:27: ( ^( UNARYOP unaryOp ) )*
                while ( stream_unaryOp.hasNext() ) {
                    // Velvet.g:163:27: ^( UNARYOP unaryOp )
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

                // Velvet.g:163:47: ( ^( OPERAND name ) )?
                if ( stream_name.hasNext() ) {
                    // Velvet.g:163:47: ^( OPERAND name )
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
    // Velvet.g:166:1: attributeConstraint : attribConstraint -> ^( ACONSTR attribConstraint ) ;
    public final VelvetParser.attributeConstraint_return attributeConstraint() throws RecognitionException {
        VelvetParser.attributeConstraint_return retval = new VelvetParser.attributeConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribConstraint_return attribConstraint80 =null;


        RewriteRuleSubtreeStream stream_attribConstraint=new RewriteRuleSubtreeStream(adaptor,"rule attribConstraint");
        try {
            // Velvet.g:167:2: ( attribConstraint -> ^( ACONSTR attribConstraint ) )
            // Velvet.g:167:4: attribConstraint
            {
            pushFollow(FOLLOW_attribConstraint_in_attributeConstraint1078);
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
            // 168:2: -> ^( ACONSTR attribConstraint )
            {
                // Velvet.g:168:5: ^( ACONSTR attribConstraint )
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
    // Velvet.g:171:1: attribConstraint : attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* ;
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
            // Velvet.g:172:2: ( attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* )
            // Velvet.g:172:4: attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )*
            {
            root_0 = (Tree)adaptor.nil();


            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1098);
            attribNumInstance81=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance81.getTree());

            // Velvet.g:172:22: ( attribOperator attribNumInstance )*
            loop23:
            do {
                int alt23=2;
                int LA23_0 = input.LA(1);

                if ( (LA23_0==MINUS||LA23_0==PLUS) ) {
                    alt23=1;
                }


                switch (alt23) {
            	case 1 :
            	    // Velvet.g:172:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1101);
            	    attribOperator82=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator82.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1103);
            	    attribNumInstance83=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance83.getTree());

            	    }
            	    break;

            	default :
            	    break loop23;
                }
            } while (true);


            pushFollow(FOLLOW_attribRelation_in_attribConstraint1111);
            attribRelation84=attribRelation();

            state._fsp--;

            adaptor.addChild(root_0, attribRelation84.getTree());

            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1117);
            attribNumInstance85=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance85.getTree());

            // Velvet.g:174:22: ( attribOperator attribNumInstance )*
            loop24:
            do {
                int alt24=2;
                int LA24_0 = input.LA(1);

                if ( (LA24_0==MINUS||LA24_0==PLUS) ) {
                    alt24=1;
                }


                switch (alt24) {
            	case 1 :
            	    // Velvet.g:174:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1120);
            	    attribOperator86=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator86.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1122);
            	    attribNumInstance87=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance87.getTree());

            	    }
            	    break;

            	default :
            	    break loop24;
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
    // Velvet.g:177:1: attribOperator : ( PLUS | MINUS );
    public final VelvetParser.attribOperator_return attribOperator() throws RecognitionException {
        VelvetParser.attribOperator_return retval = new VelvetParser.attribOperator_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set88=null;

        Tree set88_tree=null;

        try {
            // Velvet.g:178:2: ( PLUS | MINUS )
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
    // Velvet.g:182:1: attribNumInstance : ( INT | name );
    public final VelvetParser.attribNumInstance_return attribNumInstance() throws RecognitionException {
        VelvetParser.attribNumInstance_return retval = new VelvetParser.attribNumInstance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token INT89=null;
        VelvetParser.name_return name90 =null;


        Tree INT89_tree=null;

        try {
            // Velvet.g:183:2: ( INT | name )
            int alt25=2;
            int LA25_0 = input.LA(1);

            if ( (LA25_0==INT) ) {
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
                    // Velvet.g:183:4: INT
                    {
                    root_0 = (Tree)adaptor.nil();


                    INT89=(Token)match(input,INT,FOLLOW_INT_in_attribNumInstance1154); 
                    INT89_tree = 
                    (Tree)adaptor.create(INT89)
                    ;
                    adaptor.addChild(root_0, INT89_tree);


                    }
                    break;
                case 2 :
                    // Velvet.g:185:4: name
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_name_in_attribNumInstance1161);
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
    // Velvet.g:188:1: attribute : ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) ;
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
            // Velvet.g:189:2: ( ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) )
            // Velvet.g:189:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI
            {
            // Velvet.g:189:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute )
            int alt26=4;
            switch ( input.LA(1) ) {
            case VAR_INT:
                {
                alt26=1;
                }
                break;
            case VAR_FLOAT:
                {
                alt26=2;
                }
                break;
            case VAR_STRING:
                {
                alt26=3;
                }
                break;
            case VAR_BOOL:
                {
                alt26=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 26, 0, input);

                throw nvae;

            }

            switch (alt26) {
                case 1 :
                    // Velvet.g:189:5: intAttribute
                    {
                    pushFollow(FOLLOW_intAttribute_in_attribute1173);
                    intAttribute91=intAttribute();

                    state._fsp--;

                    stream_intAttribute.add(intAttribute91.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:189:20: floatAttribute
                    {
                    pushFollow(FOLLOW_floatAttribute_in_attribute1177);
                    floatAttribute92=floatAttribute();

                    state._fsp--;

                    stream_floatAttribute.add(floatAttribute92.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:189:37: stringAttribute
                    {
                    pushFollow(FOLLOW_stringAttribute_in_attribute1181);
                    stringAttribute93=stringAttribute();

                    state._fsp--;

                    stream_stringAttribute.add(stringAttribute93.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:189:55: boolAttribute
                    {
                    pushFollow(FOLLOW_boolAttribute_in_attribute1185);
                    boolAttribute94=boolAttribute();

                    state._fsp--;

                    stream_boolAttribute.add(boolAttribute94.getTree());

                    }
                    break;

            }


            SEMI95=(Token)match(input,SEMI,FOLLOW_SEMI_in_attribute1188);  
            stream_SEMI.add(SEMI95);


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
            // 190:2: -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
            {
                // Velvet.g:190:5: ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(ATTR, "ATTR")
                , root_1);

                // Velvet.g:190:12: ( intAttribute )?
                if ( stream_intAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_intAttribute.nextTree());

                }
                stream_intAttribute.reset();

                // Velvet.g:190:26: ( floatAttribute )?
                if ( stream_floatAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_floatAttribute.nextTree());

                }
                stream_floatAttribute.reset();

                // Velvet.g:190:42: ( stringAttribute )?
                if ( stream_stringAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_stringAttribute.nextTree());

                }
                stream_stringAttribute.reset();

                // Velvet.g:190:59: ( boolAttribute )?
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
    // Velvet.g:193:1: intAttribute : VAR_INT ! name ( EQ ! INT )? ;
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
            // Velvet.g:193:13: ( VAR_INT ! name ( EQ ! INT )? )
            // Velvet.g:193:16: VAR_INT ! name ( EQ ! INT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_INT96=(Token)match(input,VAR_INT,FOLLOW_VAR_INT_in_intAttribute1217); 

            pushFollow(FOLLOW_name_in_intAttribute1220);
            name97=name();

            state._fsp--;

            adaptor.addChild(root_0, name97.getTree());

            // Velvet.g:193:30: ( EQ ! INT )?
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==EQ) ) {
                alt27=1;
            }
            switch (alt27) {
                case 1 :
                    // Velvet.g:193:31: EQ ! INT
                    {
                    EQ98=(Token)match(input,EQ,FOLLOW_EQ_in_intAttribute1223); 

                    INT99=(Token)match(input,INT,FOLLOW_INT_in_intAttribute1226); 
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
    // Velvet.g:194:1: floatAttribute : VAR_FLOAT ! name ( EQ ! FLOAT )? ;
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
            // Velvet.g:194:15: ( VAR_FLOAT ! name ( EQ ! FLOAT )? )
            // Velvet.g:194:18: VAR_FLOAT ! name ( EQ ! FLOAT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_FLOAT100=(Token)match(input,VAR_FLOAT,FOLLOW_VAR_FLOAT_in_floatAttribute1235); 

            pushFollow(FOLLOW_name_in_floatAttribute1238);
            name101=name();

            state._fsp--;

            adaptor.addChild(root_0, name101.getTree());

            // Velvet.g:194:34: ( EQ ! FLOAT )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==EQ) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // Velvet.g:194:35: EQ ! FLOAT
                    {
                    EQ102=(Token)match(input,EQ,FOLLOW_EQ_in_floatAttribute1241); 

                    FLOAT103=(Token)match(input,FLOAT,FOLLOW_FLOAT_in_floatAttribute1244); 
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
    // Velvet.g:195:1: stringAttribute : VAR_STRING ! name ( EQ ! STRING )? ;
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
            // Velvet.g:195:16: ( VAR_STRING ! name ( EQ ! STRING )? )
            // Velvet.g:195:18: VAR_STRING ! name ( EQ ! STRING )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_STRING104=(Token)match(input,VAR_STRING,FOLLOW_VAR_STRING_in_stringAttribute1252); 

            pushFollow(FOLLOW_name_in_stringAttribute1255);
            name105=name();

            state._fsp--;

            adaptor.addChild(root_0, name105.getTree());

            // Velvet.g:195:35: ( EQ ! STRING )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==EQ) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // Velvet.g:195:36: EQ ! STRING
                    {
                    EQ106=(Token)match(input,EQ,FOLLOW_EQ_in_stringAttribute1258); 

                    STRING107=(Token)match(input,STRING,FOLLOW_STRING_in_stringAttribute1261); 
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
    // Velvet.g:196:1: boolAttribute : VAR_BOOL ! name ( EQ ! BOOLEAN )? ;
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
            // Velvet.g:196:14: ( VAR_BOOL ! name ( EQ ! BOOLEAN )? )
            // Velvet.g:196:17: VAR_BOOL ! name ( EQ ! BOOLEAN )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_BOOL108=(Token)match(input,VAR_BOOL,FOLLOW_VAR_BOOL_in_boolAttribute1270); 

            pushFollow(FOLLOW_name_in_boolAttribute1273);
            name109=name();

            state._fsp--;

            adaptor.addChild(root_0, name109.getTree());

            // Velvet.g:196:32: ( EQ ! BOOLEAN )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==EQ) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // Velvet.g:196:33: EQ ! BOOLEAN
                    {
                    EQ110=(Token)match(input,EQ,FOLLOW_EQ_in_boolAttribute1276); 

                    BOOLEAN111=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_boolAttribute1279); 
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
    // Velvet.g:198:1: unaryOp : OP_NOT ;
    public final VelvetParser.unaryOp_return unaryOp() throws RecognitionException {
        VelvetParser.unaryOp_return retval = new VelvetParser.unaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token OP_NOT112=null;

        Tree OP_NOT112_tree=null;

        try {
            // Velvet.g:199:2: ( OP_NOT )
            // Velvet.g:199:4: OP_NOT
            {
            root_0 = (Tree)adaptor.nil();


            OP_NOT112=(Token)match(input,OP_NOT,FOLLOW_OP_NOT_in_unaryOp1291); 
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
    // Velvet.g:202:1: binaryOp : ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT );
    public final VelvetParser.binaryOp_return binaryOp() throws RecognitionException {
        VelvetParser.binaryOp_return retval = new VelvetParser.binaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set113=null;

        Tree set113_tree=null;

        try {
            // Velvet.g:203:2: ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT )
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
    // Velvet.g:210:1: attribRelation : ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ );
    public final VelvetParser.attribRelation_return attribRelation() throws RecognitionException {
        VelvetParser.attribRelation_return retval = new VelvetParser.attribRelation_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set114=null;

        Tree set114_tree=null;

        try {
            // Velvet.g:211:2: ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ )
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


 

    public static final BitSet FOLLOW_concept_in_velvetModel466 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_cinterface_in_velvetModel468 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_velvetModel471 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONCEPT_in_concept484 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_concept486 = new BitSet(new long[]{0x0020000C00010000L});
    public static final BitSet FOLLOW_COLON_in_concept493 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_conceptBaseExt_in_concept495 = new BitSet(new long[]{0x0020000C00000000L});
    public static final BitSet FOLLOW_instanceImports_in_concept500 = new BitSet(new long[]{0x0020000800000000L});
    public static final BitSet FOLLOW_interfaceImports_in_concept505 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_definitions_in_concept512 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt544 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_conceptBaseExt547 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt549 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_IMPORTINSTANCE_in_instanceImports574 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_instanceImports576 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_instanceImports578 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_instanceImports581 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_instanceImports583 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_instanceImports585 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_IMPORTINTERFACE_in_interfaceImports614 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_interfaceImports616 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_interfaceImports618 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_interfaceImports621 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_interfaceImports623 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_interfaceImports625 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_CINTERFACE_in_cinterface652 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_cinterface654 = new BitSet(new long[]{0x0020000000010000L});
    public static final BitSet FOLLOW_COLON_in_cinterface658 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_interfaceBaseExt_in_cinterface660 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_definitions_in_cinterface664 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt691 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_interfaceBaseExt694 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt696 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_START_C_in_definitions736 = new BitSet(new long[]{0xF410048010500010L});
    public static final BitSet FOLLOW_def_in_definitions738 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_END_C_in_definitions740 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def759 = new BitSet(new long[]{0xF410048010100012L});
    public static final BitSet FOLLOW_featureGroup_in_def767 = new BitSet(new long[]{0xF400000000100002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def769 = new BitSet(new long[]{0xF400000000100002L});
    public static final BitSet FOLLOW_feature_in_def778 = new BitSet(new long[]{0xF400008010100012L});
    public static final BitSet FOLLOW_feature_in_def781 = new BitSet(new long[]{0xF400008010100012L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def785 = new BitSet(new long[]{0xF400008010100012L});
    public static final BitSet FOLLOW_constraint_in_nonFeatureDefinition805 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_use_in_nonFeatureDefinition810 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribute_in_nonFeatureDefinition815 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_USE_in_use827 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_use829 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_use831 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANDATORY_in_feature852 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature854 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature858 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature860 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature864 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature868 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_FEATURE_in_feature875 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_feature877 = new BitSet(new long[]{0x0028000000000000L});
    public static final BitSet FOLLOW_definitions_in_feature880 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SEMI_in_feature884 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_groupType_in_featureGroup915 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_START_C_in_featureGroup917 = new BitSet(new long[]{0x0000008010000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup919 = new BitSet(new long[]{0x0000008010000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup921 = new BitSet(new long[]{0x0000008010400010L});
    public static final BitSet FOLLOW_END_C_in_featureGroup924 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONSTRAINT_in_constraint967 = new BitSet(new long[]{0x0040802300000000L});
    public static final BitSet FOLLOW_ID_in_constraint971 = new BitSet(new long[]{0x0000000001000000L});
    public static final BitSet FOLLOW_EQ_in_constraint973 = new BitSet(new long[]{0x0040802300000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraint979 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_attributeConstraint_in_constraint983 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_constraint986 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition999 = new BitSet(new long[]{0x0003700000000002L});
    public static final BitSet FOLLOW_binaryOp_in_constraintDefinition1002 = new BitSet(new long[]{0x0040800300000000L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1004 = new BitSet(new long[]{0x0003700000000002L});
    public static final BitSet FOLLOW_unaryOp_in_constraintOperand1031 = new BitSet(new long[]{0x0040800300000000L});
    public static final BitSet FOLLOW_START_R_in_constraintOperand1035 = new BitSet(new long[]{0x0040800300000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraintOperand1037 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_END_R_in_constraintOperand1039 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_constraintOperand1043 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribConstraint_in_attributeConstraint1078 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1098 = new BitSet(new long[]{0x0004010000000A80L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1101 = new BitSet(new long[]{0x0000002300000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1103 = new BitSet(new long[]{0x0004010000000A80L});
    public static final BitSet FOLLOW_attribRelation_in_attribConstraint1111 = new BitSet(new long[]{0x0000002300000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1117 = new BitSet(new long[]{0x0004010000000002L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1120 = new BitSet(new long[]{0x0000002300000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1122 = new BitSet(new long[]{0x0004010000000002L});
    public static final BitSet FOLLOW_INT_in_attribNumInstance1154 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_attribNumInstance1161 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_intAttribute_in_attribute1173 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_floatAttribute_in_attribute1177 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_stringAttribute_in_attribute1181 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_boolAttribute_in_attribute1185 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_attribute1188 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_INT_in_intAttribute1217 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_intAttribute1220 = new BitSet(new long[]{0x0000000001000002L});
    public static final BitSet FOLLOW_EQ_in_intAttribute1223 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_INT_in_intAttribute1226 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_FLOAT_in_floatAttribute1235 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_floatAttribute1238 = new BitSet(new long[]{0x0000000001000002L});
    public static final BitSet FOLLOW_EQ_in_floatAttribute1241 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_FLOAT_in_floatAttribute1244 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_STRING_in_stringAttribute1252 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_stringAttribute1255 = new BitSet(new long[]{0x0000000001000002L});
    public static final BitSet FOLLOW_EQ_in_stringAttribute1258 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_STRING_in_stringAttribute1261 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_BOOL_in_boolAttribute1270 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_boolAttribute1273 = new BitSet(new long[]{0x0000000001000002L});
    public static final BitSet FOLLOW_EQ_in_boolAttribute1276 = new BitSet(new long[]{0x0000000000004000L});
    public static final BitSet FOLLOW_BOOLEAN_in_boolAttribute1279 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_OP_NOT_in_unaryOp1291 = new BitSet(new long[]{0x0000000000000002L});

}