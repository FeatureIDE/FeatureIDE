// $ANTLR 3.4 Velvet.g 2014-06-06 14:56:29

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
    // Velvet.g:82:1: concept : CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )? ( definitions )? -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? ) ;
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

        VelvetParser.interfaceImports_return interfaceImports10 =null;

        VelvetParser.instanceImports_return instanceImports11 =null;

        VelvetParser.interfaceImports_return interfaceImports12 =null;

        VelvetParser.instanceImports_return instanceImports13 =null;

        VelvetParser.definitions_return definitions14 =null;


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
            // Velvet.g:83:2: ( CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )? ( definitions )? -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? ) )
            // Velvet.g:83:4: CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )? ( definitions )?
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


            // Velvet.g:84:27: ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )?
            int alt3=5;
            alt3 = dfa3.predict(input);
            switch (alt3) {
                case 1 :
                    // Velvet.g:84:28: instanceImports interfaceImports
                    {
                    pushFollow(FOLLOW_instanceImports_in_concept500);
                    instanceImports8=instanceImports();

                    state._fsp--;

                    stream_instanceImports.add(instanceImports8.getTree());

                    pushFollow(FOLLOW_interfaceImports_in_concept502);
                    interfaceImports9=interfaceImports();

                    state._fsp--;

                    stream_interfaceImports.add(interfaceImports9.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:84:63: interfaceImports instanceImports
                    {
                    pushFollow(FOLLOW_interfaceImports_in_concept506);
                    interfaceImports10=interfaceImports();

                    state._fsp--;

                    stream_interfaceImports.add(interfaceImports10.getTree());

                    pushFollow(FOLLOW_instanceImports_in_concept508);
                    instanceImports11=instanceImports();

                    state._fsp--;

                    stream_instanceImports.add(instanceImports11.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:84:98: interfaceImports
                    {
                    pushFollow(FOLLOW_interfaceImports_in_concept512);
                    interfaceImports12=interfaceImports();

                    state._fsp--;

                    stream_interfaceImports.add(interfaceImports12.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:84:117: instanceImports
                    {
                    pushFollow(FOLLOW_instanceImports_in_concept516);
                    instanceImports13=instanceImports();

                    state._fsp--;

                    stream_instanceImports.add(instanceImports13.getTree());

                    }
                    break;

            }


            // Velvet.g:85:3: ( definitions )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0==START_C) ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // Velvet.g:85:3: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_concept523);
                    definitions14=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions14.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: definitions, interfaceImports, instanceImports, CONCEPT, ID, conceptBaseExt
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 86:2: -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? )
            {
                // Velvet.g:86:5: ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? )
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

                // Velvet.g:86:69: ( definitions )?
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

        Token ID15=null;
        Token COMMA16=null;
        Token ID17=null;

        Tree ID15_tree=null;
        Tree COMMA16_tree=null;
        Tree ID17_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

        try {
            // Velvet.g:90:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:90:4: ID ( COMMA ID )*
            {
            ID15=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt556);  
            stream_ID.add(ID15);


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
            	    COMMA16=(Token)match(input,COMMA,FOLLOW_COMMA_in_conceptBaseExt559);  
            	    stream_COMMA.add(COMMA16);


            	    ID17=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt561);  
            	    stream_ID.add(ID17);


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

        Token IMPORTINSTANCE18=null;
        Token ID19=null;
        Token COMMA21=null;
        Token ID22=null;
        VelvetParser.name_return name20 =null;

        VelvetParser.name_return name23 =null;


        Tree IMPORTINSTANCE18_tree=null;
        Tree ID19_tree=null;
        Tree COMMA21_tree=null;
        Tree ID22_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
        RewriteRuleTokenStream stream_IMPORTINSTANCE=new RewriteRuleTokenStream(adaptor,"token IMPORTINSTANCE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:95:2: ( IMPORTINSTANCE ID name ( COMMA ID name )* -> ^( INST ( ID name )+ ) )
            // Velvet.g:95:4: IMPORTINSTANCE ID name ( COMMA ID name )*
            {
            IMPORTINSTANCE18=(Token)match(input,IMPORTINSTANCE,FOLLOW_IMPORTINSTANCE_in_instanceImports586);  
            stream_IMPORTINSTANCE.add(IMPORTINSTANCE18);


            ID19=(Token)match(input,ID,FOLLOW_ID_in_instanceImports588);  
            stream_ID.add(ID19);


            pushFollow(FOLLOW_name_in_instanceImports590);
            name20=name();

            state._fsp--;

            stream_name.add(name20.getTree());

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
            	    COMMA21=(Token)match(input,COMMA,FOLLOW_COMMA_in_instanceImports593);  
            	    stream_COMMA.add(COMMA21);


            	    ID22=(Token)match(input,ID,FOLLOW_ID_in_instanceImports595);  
            	    stream_ID.add(ID22);


            	    pushFollow(FOLLOW_name_in_instanceImports597);
            	    name23=name();

            	    state._fsp--;

            	    stream_name.add(name23.getTree());

            	    }
            	    break;

            	default :
            	    break loop6;
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
            // 96:2: -> ^( INST ( ID name )+ )
            {
                // Velvet.g:96:5: ^( INST ( ID name )+ )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(INST, "INST")
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

        Token IMPORTINTERFACE24=null;
        Token ID25=null;
        Token COMMA27=null;
        Token ID28=null;
        VelvetParser.name_return name26 =null;

        VelvetParser.name_return name29 =null;


        Tree IMPORTINTERFACE24_tree=null;
        Tree ID25_tree=null;
        Tree COMMA27_tree=null;
        Tree ID28_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
        RewriteRuleTokenStream stream_IMPORTINTERFACE=new RewriteRuleTokenStream(adaptor,"token IMPORTINTERFACE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:100:2: ( IMPORTINTERFACE ID name ( COMMA ID name )* -> ^( INTF ( ID name )+ ) )
            // Velvet.g:100:4: IMPORTINTERFACE ID name ( COMMA ID name )*
            {
            IMPORTINTERFACE24=(Token)match(input,IMPORTINTERFACE,FOLLOW_IMPORTINTERFACE_in_interfaceImports626);  
            stream_IMPORTINTERFACE.add(IMPORTINTERFACE24);


            ID25=(Token)match(input,ID,FOLLOW_ID_in_interfaceImports628);  
            stream_ID.add(ID25);


            pushFollow(FOLLOW_name_in_interfaceImports630);
            name26=name();

            state._fsp--;

            stream_name.add(name26.getTree());

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
            	    COMMA27=(Token)match(input,COMMA,FOLLOW_COMMA_in_interfaceImports633);  
            	    stream_COMMA.add(COMMA27);


            	    ID28=(Token)match(input,ID,FOLLOW_ID_in_interfaceImports635);  
            	    stream_ID.add(ID28);


            	    pushFollow(FOLLOW_name_in_interfaceImports637);
            	    name29=name();

            	    state._fsp--;

            	    stream_name.add(name29.getTree());

            	    }
            	    break;

            	default :
            	    break loop7;
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
            // 101:2: -> ^( INTF ( ID name )+ )
            {
                // Velvet.g:101:5: ^( INTF ( ID name )+ )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(INTF, "INTF")
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

        Token CINTERFACE30=null;
        Token ID31=null;
        Token COLON32=null;
        VelvetParser.interfaceBaseExt_return interfaceBaseExt33 =null;

        VelvetParser.definitions_return definitions34 =null;


        Tree CINTERFACE30_tree=null;
        Tree ID31_tree=null;
        Tree COLON32_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_CINTERFACE=new RewriteRuleTokenStream(adaptor,"token CINTERFACE");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        RewriteRuleSubtreeStream stream_interfaceBaseExt=new RewriteRuleSubtreeStream(adaptor,"rule interfaceBaseExt");
        try {
            // Velvet.g:104:12: ( CINTERFACE ID ( COLON interfaceBaseExt )? definitions -> ^( CINTERFACE ID ( interfaceBaseExt )? definitions ) )
            // Velvet.g:104:14: CINTERFACE ID ( COLON interfaceBaseExt )? definitions
            {
            CINTERFACE30=(Token)match(input,CINTERFACE,FOLLOW_CINTERFACE_in_cinterface664);  
            stream_CINTERFACE.add(CINTERFACE30);


            ID31=(Token)match(input,ID,FOLLOW_ID_in_cinterface666);  
            stream_ID.add(ID31);


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
                    COLON32=(Token)match(input,COLON,FOLLOW_COLON_in_cinterface670);  
                    stream_COLON.add(COLON32);


                    pushFollow(FOLLOW_interfaceBaseExt_in_cinterface672);
                    interfaceBaseExt33=interfaceBaseExt();

                    state._fsp--;

                    stream_interfaceBaseExt.add(interfaceBaseExt33.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_cinterface676);
            definitions34=definitions();

            state._fsp--;

            stream_definitions.add(definitions34.getTree());

            // AST REWRITE
            // elements: ID, definitions, interfaceBaseExt, CINTERFACE
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

        Token ID35=null;
        Token COMMA36=null;
        Token ID37=null;

        Tree ID35_tree=null;
        Tree COMMA36_tree=null;
        Tree ID37_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

        try {
            // Velvet.g:109:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:109:4: ID ( COMMA ID )*
            {
            ID35=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt703);  
            stream_ID.add(ID35);


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
            	    COMMA36=(Token)match(input,COMMA,FOLLOW_COMMA_in_interfaceBaseExt706);  
            	    stream_COMMA.add(COMMA36);


            	    ID37=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt708);  
            	    stream_ID.add(ID37);


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

        Token set38=null;

        Tree set38_tree=null;

        try {
            // Velvet.g:113:5: ( ID | IDPath )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set38=(Token)input.LT(1);

            if ( (input.LA(1) >= ID && input.LA(1) <= IDPath) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set38)
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
    // Velvet.g:117:1: definitions : START_C definition END_C -> ^( DEF definition ) ;
    public final VelvetParser.definitions_return definitions() throws RecognitionException {
        VelvetParser.definitions_return retval = new VelvetParser.definitions_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C39=null;
        Token END_C41=null;
        VelvetParser.definition_return definition40 =null;


        Tree START_C39_tree=null;
        Tree END_C41_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_definition=new RewriteRuleSubtreeStream(adaptor,"rule definition");
        try {
            // Velvet.g:118:2: ( START_C definition END_C -> ^( DEF definition ) )
            // Velvet.g:118:4: START_C definition END_C
            {
            START_C39=(Token)match(input,START_C,FOLLOW_START_C_in_definitions748);  
            stream_START_C.add(START_C39);


            pushFollow(FOLLOW_definition_in_definitions750);
            definition40=definition();

            state._fsp--;

            stream_definition.add(definition40.getTree());

            END_C41=(Token)match(input,END_C,FOLLOW_END_C_in_definitions752);  
            stream_END_C.add(END_C41);


            // AST REWRITE
            // elements: definition
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 119:2: -> ^( DEF definition )
            {
                // Velvet.g:119:5: ^( DEF definition )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(DEF, "DEF")
                , root_1);

                adaptor.addChild(root_1, stream_definition.nextTree());

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


    public static class definition_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "definition"
    // Velvet.g:122:1: definition : ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? ;
    public final VelvetParser.definition_return definition() throws RecognitionException {
        VelvetParser.definition_return retval = new VelvetParser.definition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition42 =null;

        VelvetParser.featureGroup_return featureGroup43 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition44 =null;

        VelvetParser.feature_return feature45 =null;

        VelvetParser.feature_return feature46 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition47 =null;



        try {
            // Velvet.g:123:2: ( ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? )
            // Velvet.g:123:4: ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:123:4: ( nonFeatureDefinition )*
            loop10:
            do {
                int alt10=2;
                int LA10_0 = input.LA(1);

                if ( (LA10_0==CONSTRAINT||LA10_0==USE||(LA10_0 >= VAR_BOOL && LA10_0 <= VAR_STRING)) ) {
                    alt10=1;
                }


                switch (alt10) {
            	case 1 :
            	    // Velvet.g:123:4: nonFeatureDefinition
            	    {
            	    pushFollow(FOLLOW_nonFeatureDefinition_in_definition773);
            	    nonFeatureDefinition42=nonFeatureDefinition();

            	    state._fsp--;

            	    adaptor.addChild(root_0, nonFeatureDefinition42.getTree());

            	    }
            	    break;

            	default :
            	    break loop10;
                }
            } while (true);


            // Velvet.g:123:26: ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
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
                    // Velvet.g:124:3: ( featureGroup ( nonFeatureDefinition )* )
                    {
                    // Velvet.g:124:3: ( featureGroup ( nonFeatureDefinition )* )
                    // Velvet.g:124:4: featureGroup ( nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_featureGroup_in_definition781);
                    featureGroup43=featureGroup();

                    state._fsp--;

                    adaptor.addChild(root_0, featureGroup43.getTree());

                    // Velvet.g:124:17: ( nonFeatureDefinition )*
                    loop11:
                    do {
                        int alt11=2;
                        int LA11_0 = input.LA(1);

                        if ( (LA11_0==CONSTRAINT||LA11_0==USE||(LA11_0 >= VAR_BOOL && LA11_0 <= VAR_STRING)) ) {
                            alt11=1;
                        }


                        switch (alt11) {
                    	case 1 :
                    	    // Velvet.g:124:17: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_definition783);
                    	    nonFeatureDefinition44=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition44.getTree());

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
                    // Velvet.g:125:3: ( feature ( feature | nonFeatureDefinition )* )
                    {
                    // Velvet.g:125:3: ( feature ( feature | nonFeatureDefinition )* )
                    // Velvet.g:125:4: feature ( feature | nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_feature_in_definition792);
                    feature45=feature();

                    state._fsp--;

                    adaptor.addChild(root_0, feature45.getTree());

                    // Velvet.g:125:12: ( feature | nonFeatureDefinition )*
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
                    	    // Velvet.g:125:13: feature
                    	    {
                    	    pushFollow(FOLLOW_feature_in_definition795);
                    	    feature46=feature();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, feature46.getTree());

                    	    }
                    	    break;
                    	case 2 :
                    	    // Velvet.g:125:23: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_definition799);
                    	    nonFeatureDefinition47=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition47.getTree());

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
    // $ANTLR end "definition"


    public static class nonFeatureDefinition_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "nonFeatureDefinition"
    // Velvet.g:129:1: nonFeatureDefinition : ( constraint | use | attribute );
    public final VelvetParser.nonFeatureDefinition_return nonFeatureDefinition() throws RecognitionException {
        VelvetParser.nonFeatureDefinition_return retval = new VelvetParser.nonFeatureDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraint_return constraint48 =null;

        VelvetParser.use_return use49 =null;

        VelvetParser.attribute_return attribute50 =null;



        try {
            // Velvet.g:130:2: ( constraint | use | attribute )
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
                    // Velvet.g:130:4: constraint
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_constraint_in_nonFeatureDefinition821);
                    constraint48=constraint();

                    state._fsp--;

                    adaptor.addChild(root_0, constraint48.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:131:4: use
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_use_in_nonFeatureDefinition826);
                    use49=use();

                    state._fsp--;

                    adaptor.addChild(root_0, use49.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:132:4: attribute
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_attribute_in_nonFeatureDefinition831);
                    attribute50=attribute();

                    state._fsp--;

                    adaptor.addChild(root_0, attribute50.getTree());

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
    // Velvet.g:135:1: use : USE name SEMI -> ^( USES name ) ;
    public final VelvetParser.use_return use() throws RecognitionException {
        VelvetParser.use_return retval = new VelvetParser.use_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token USE51=null;
        Token SEMI53=null;
        VelvetParser.name_return name52 =null;


        Tree USE51_tree=null;
        Tree SEMI53_tree=null;
        RewriteRuleTokenStream stream_USE=new RewriteRuleTokenStream(adaptor,"token USE");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:135:5: ( USE name SEMI -> ^( USES name ) )
            // Velvet.g:135:7: USE name SEMI
            {
            USE51=(Token)match(input,USE,FOLLOW_USE_in_use843);  
            stream_USE.add(USE51);


            pushFollow(FOLLOW_name_in_use845);
            name52=name();

            state._fsp--;

            stream_name.add(name52.getTree());

            SEMI53=(Token)match(input,SEMI,FOLLOW_SEMI_in_use847);  
            stream_SEMI.add(SEMI53);


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
            // 136:2: -> ^( USES name )
            {
                // Velvet.g:136:5: ^( USES name )
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
    // Velvet.g:139:1: feature : ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) ;
    public final VelvetParser.feature_return feature() throws RecognitionException {
        VelvetParser.feature_return retval = new VelvetParser.feature_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token MANDATORY54=null;
        Token ABSTRACT55=null;
        Token ABSTRACT56=null;
        Token MANDATORY57=null;
        Token MANDATORY58=null;
        Token ABSTRACT59=null;
        Token FEATURE60=null;
        Token SEMI63=null;
        VelvetParser.name_return name61 =null;

        VelvetParser.definitions_return definitions62 =null;


        Tree MANDATORY54_tree=null;
        Tree ABSTRACT55_tree=null;
        Tree ABSTRACT56_tree=null;
        Tree MANDATORY57_tree=null;
        Tree MANDATORY58_tree=null;
        Tree ABSTRACT59_tree=null;
        Tree FEATURE60_tree=null;
        Tree SEMI63_tree=null;
        RewriteRuleTokenStream stream_ABSTRACT=new RewriteRuleTokenStream(adaptor,"token ABSTRACT");
        RewriteRuleTokenStream stream_MANDATORY=new RewriteRuleTokenStream(adaptor,"token MANDATORY");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleTokenStream stream_FEATURE=new RewriteRuleTokenStream(adaptor,"token FEATURE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:140:2: ( ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) )
            // Velvet.g:140:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI )
            {
            // Velvet.g:140:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )?
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
                    // Velvet.g:140:5: MANDATORY ABSTRACT
                    {
                    MANDATORY54=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature868);  
                    stream_MANDATORY.add(MANDATORY54);


                    ABSTRACT55=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature870);  
                    stream_ABSTRACT.add(ABSTRACT55);


                    }
                    break;
                case 2 :
                    // Velvet.g:140:26: ABSTRACT MANDATORY
                    {
                    ABSTRACT56=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature874);  
                    stream_ABSTRACT.add(ABSTRACT56);


                    MANDATORY57=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature876);  
                    stream_MANDATORY.add(MANDATORY57);


                    }
                    break;
                case 3 :
                    // Velvet.g:140:47: MANDATORY
                    {
                    MANDATORY58=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature880);  
                    stream_MANDATORY.add(MANDATORY58);


                    }
                    break;
                case 4 :
                    // Velvet.g:140:59: ABSTRACT
                    {
                    ABSTRACT59=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature884);  
                    stream_ABSTRACT.add(ABSTRACT59);


                    }
                    break;

            }


            FEATURE60=(Token)match(input,FEATURE,FOLLOW_FEATURE_in_feature891);  
            stream_FEATURE.add(FEATURE60);


            pushFollow(FOLLOW_name_in_feature893);
            name61=name();

            state._fsp--;

            stream_name.add(name61.getTree());

            // Velvet.g:141:17: ( definitions | SEMI )
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
                    // Velvet.g:141:18: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_feature896);
                    definitions62=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions62.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:141:32: SEMI
                    {
                    SEMI63=(Token)match(input,SEMI,FOLLOW_SEMI_in_feature900);  
                    stream_SEMI.add(SEMI63);


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
            // 142:2: -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
            {
                // Velvet.g:142:5: ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(FEAT, "FEAT")
                , root_1);

                adaptor.addChild(root_1, stream_name.nextTree());

                // Velvet.g:142:17: ( MANDATORY )?
                if ( stream_MANDATORY.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_MANDATORY.nextNode()
                    );

                }
                stream_MANDATORY.reset();

                // Velvet.g:142:28: ( ABSTRACT )?
                if ( stream_ABSTRACT.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ABSTRACT.nextNode()
                    );

                }
                stream_ABSTRACT.reset();

                // Velvet.g:142:38: ( definitions )?
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
    // Velvet.g:145:1: featureGroup : groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) ;
    public final VelvetParser.featureGroup_return featureGroup() throws RecognitionException {
        VelvetParser.featureGroup_return retval = new VelvetParser.featureGroup_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C65=null;
        Token END_C68=null;
        VelvetParser.groupType_return groupType64 =null;

        VelvetParser.feature_return feature66 =null;

        VelvetParser.feature_return feature67 =null;


        Tree START_C65_tree=null;
        Tree END_C68_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_groupType=new RewriteRuleSubtreeStream(adaptor,"rule groupType");
        RewriteRuleSubtreeStream stream_feature=new RewriteRuleSubtreeStream(adaptor,"rule feature");
        try {
            // Velvet.g:146:2: ( groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) )
            // Velvet.g:146:4: groupType START_C feature ( feature )+ END_C
            {
            pushFollow(FOLLOW_groupType_in_featureGroup931);
            groupType64=groupType();

            state._fsp--;

            stream_groupType.add(groupType64.getTree());

            START_C65=(Token)match(input,START_C,FOLLOW_START_C_in_featureGroup933);  
            stream_START_C.add(START_C65);


            pushFollow(FOLLOW_feature_in_featureGroup935);
            feature66=feature();

            state._fsp--;

            stream_feature.add(feature66.getTree());

            // Velvet.g:146:30: ( feature )+
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
            	    // Velvet.g:146:30: feature
            	    {
            	    pushFollow(FOLLOW_feature_in_featureGroup937);
            	    feature67=feature();

            	    state._fsp--;

            	    stream_feature.add(feature67.getTree());

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


            END_C68=(Token)match(input,END_C,FOLLOW_END_C_in_featureGroup940);  
            stream_END_C.add(END_C68);


            // AST REWRITE
            // elements: feature, groupType, feature
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 147:2: -> ^( GROUP groupType feature ( feature )+ )
            {
                // Velvet.g:147:5: ^( GROUP groupType feature ( feature )+ )
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
    // Velvet.g:150:1: groupType : ( SOMEOF | ONEOF );
    public final VelvetParser.groupType_return groupType() throws RecognitionException {
        VelvetParser.groupType_return retval = new VelvetParser.groupType_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set69=null;

        Tree set69_tree=null;

        try {
            // Velvet.g:151:2: ( SOMEOF | ONEOF )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set69=(Token)input.LT(1);

            if ( input.LA(1)==ONEOF||input.LA(1)==SOMEOF ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set69)
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
    // Velvet.g:155:1: constraint : CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !;
    public final VelvetParser.constraint_return constraint() throws RecognitionException {
        VelvetParser.constraint_return retval = new VelvetParser.constraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token CONSTRAINT70=null;
        Token ID71=null;
        Token EQ72=null;
        Token SEMI75=null;
        VelvetParser.constraintDefinition_return constraintDefinition73 =null;

        VelvetParser.attributeConstraint_return attributeConstraint74 =null;


        Tree CONSTRAINT70_tree=null;
        Tree ID71_tree=null;
        Tree EQ72_tree=null;
        Tree SEMI75_tree=null;

        try {
            // Velvet.g:156:2: ( CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !)
            // Velvet.g:156:4: CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !
            {
            root_0 = (Tree)adaptor.nil();


            CONSTRAINT70=(Token)match(input,CONSTRAINT,FOLLOW_CONSTRAINT_in_constraint983); 
            CONSTRAINT70_tree = 
            (Tree)adaptor.create(CONSTRAINT70)
            ;
            root_0 = (Tree)adaptor.becomeRoot(CONSTRAINT70_tree, root_0);


            // Velvet.g:156:16: ( ID EQ !)?
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
                    // Velvet.g:156:17: ID EQ !
                    {
                    ID71=(Token)match(input,ID,FOLLOW_ID_in_constraint987); 
                    ID71_tree = 
                    (Tree)adaptor.create(ID71)
                    ;
                    adaptor.addChild(root_0, ID71_tree);


                    EQ72=(Token)match(input,EQ,FOLLOW_EQ_in_constraint989); 

                    }
                    break;

            }


            // Velvet.g:156:26: ( constraintDefinition | attributeConstraint )
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
                    // Velvet.g:156:27: constraintDefinition
                    {
                    pushFollow(FOLLOW_constraintDefinition_in_constraint995);
                    constraintDefinition73=constraintDefinition();

                    state._fsp--;

                    adaptor.addChild(root_0, constraintDefinition73.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:156:50: attributeConstraint
                    {
                    pushFollow(FOLLOW_attributeConstraint_in_constraint999);
                    attributeConstraint74=attributeConstraint();

                    state._fsp--;

                    adaptor.addChild(root_0, attributeConstraint74.getTree());

                    }
                    break;

            }


            SEMI75=(Token)match(input,SEMI,FOLLOW_SEMI_in_constraint1002); 

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
    // Velvet.g:159:1: constraintDefinition : constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) ;
    public final VelvetParser.constraintDefinition_return constraintDefinition() throws RecognitionException {
        VelvetParser.constraintDefinition_return retval = new VelvetParser.constraintDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraintOperand_return constraintOperand76 =null;

        VelvetParser.binaryOp_return binaryOp77 =null;

        VelvetParser.constraintOperand_return constraintOperand78 =null;


        RewriteRuleSubtreeStream stream_constraintOperand=new RewriteRuleSubtreeStream(adaptor,"rule constraintOperand");
        RewriteRuleSubtreeStream stream_binaryOp=new RewriteRuleSubtreeStream(adaptor,"rule binaryOp");
        try {
            // Velvet.g:160:2: ( constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) )
            // Velvet.g:160:4: constraintOperand ( binaryOp constraintOperand )*
            {
            pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1015);
            constraintOperand76=constraintOperand();

            state._fsp--;

            stream_constraintOperand.add(constraintOperand76.getTree());

            // Velvet.g:160:22: ( binaryOp constraintOperand )*
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( ((LA20_0 >= OP_AND && LA20_0 <= OP_IMPLIES)||(LA20_0 >= OP_OR && LA20_0 <= OP_XOR)) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // Velvet.g:160:23: binaryOp constraintOperand
            	    {
            	    pushFollow(FOLLOW_binaryOp_in_constraintDefinition1018);
            	    binaryOp77=binaryOp();

            	    state._fsp--;

            	    stream_binaryOp.add(binaryOp77.getTree());

            	    pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1020);
            	    constraintOperand78=constraintOperand();

            	    state._fsp--;

            	    stream_constraintOperand.add(constraintOperand78.getTree());

            	    }
            	    break;

            	default :
            	    break loop20;
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
            // 161:2: -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
            {
                // Velvet.g:161:5: ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
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

                // Velvet.g:161:33: ( binaryOp )*
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
    // Velvet.g:164:1: constraintOperand : ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? ;
    public final VelvetParser.constraintOperand_return constraintOperand() throws RecognitionException {
        VelvetParser.constraintOperand_return retval = new VelvetParser.constraintOperand_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_R80=null;
        Token END_R82=null;
        VelvetParser.unaryOp_return unaryOp79 =null;

        VelvetParser.constraintDefinition_return constraintDefinition81 =null;

        VelvetParser.name_return name83 =null;


        Tree START_R80_tree=null;
        Tree END_R82_tree=null;
        RewriteRuleTokenStream stream_END_R=new RewriteRuleTokenStream(adaptor,"token END_R");
        RewriteRuleTokenStream stream_START_R=new RewriteRuleTokenStream(adaptor,"token START_R");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_unaryOp=new RewriteRuleSubtreeStream(adaptor,"rule unaryOp");
        RewriteRuleSubtreeStream stream_constraintDefinition=new RewriteRuleSubtreeStream(adaptor,"rule constraintDefinition");
        try {
            // Velvet.g:164:19: ( ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? )
            // Velvet.g:164:21: ( unaryOp )* ( START_R constraintDefinition END_R | name )
            {
            // Velvet.g:164:21: ( unaryOp )*
            loop21:
            do {
                int alt21=2;
                int LA21_0 = input.LA(1);

                if ( (LA21_0==OP_NOT) ) {
                    alt21=1;
                }


                switch (alt21) {
            	case 1 :
            	    // Velvet.g:164:21: unaryOp
            	    {
            	    pushFollow(FOLLOW_unaryOp_in_constraintOperand1047);
            	    unaryOp79=unaryOp();

            	    state._fsp--;

            	    stream_unaryOp.add(unaryOp79.getTree());

            	    }
            	    break;

            	default :
            	    break loop21;
                }
            } while (true);


            // Velvet.g:164:30: ( START_R constraintDefinition END_R | name )
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
                    // Velvet.g:164:31: START_R constraintDefinition END_R
                    {
                    START_R80=(Token)match(input,START_R,FOLLOW_START_R_in_constraintOperand1051);  
                    stream_START_R.add(START_R80);


                    pushFollow(FOLLOW_constraintDefinition_in_constraintOperand1053);
                    constraintDefinition81=constraintDefinition();

                    state._fsp--;

                    stream_constraintDefinition.add(constraintDefinition81.getTree());

                    END_R82=(Token)match(input,END_R,FOLLOW_END_R_in_constraintOperand1055);  
                    stream_END_R.add(END_R82);


                    }
                    break;
                case 2 :
                    // Velvet.g:164:68: name
                    {
                    pushFollow(FOLLOW_name_in_constraintOperand1059);
                    name83=name();

                    state._fsp--;

                    stream_name.add(name83.getTree());

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
            // 165:2: -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )?
            {
                // Velvet.g:165:5: ( constraintDefinition )?
                if ( stream_constraintDefinition.hasNext() ) {
                    adaptor.addChild(root_0, stream_constraintDefinition.nextTree());

                }
                stream_constraintDefinition.reset();

                // Velvet.g:165:27: ( ^( UNARYOP unaryOp ) )*
                while ( stream_unaryOp.hasNext() ) {
                    // Velvet.g:165:27: ^( UNARYOP unaryOp )
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

                // Velvet.g:165:47: ( ^( OPERAND name ) )?
                if ( stream_name.hasNext() ) {
                    // Velvet.g:165:47: ^( OPERAND name )
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
    // Velvet.g:168:1: attributeConstraint : attribConstraint -> ^( ACONSTR attribConstraint ) ;
    public final VelvetParser.attributeConstraint_return attributeConstraint() throws RecognitionException {
        VelvetParser.attributeConstraint_return retval = new VelvetParser.attributeConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribConstraint_return attribConstraint84 =null;


        RewriteRuleSubtreeStream stream_attribConstraint=new RewriteRuleSubtreeStream(adaptor,"rule attribConstraint");
        try {
            // Velvet.g:169:2: ( attribConstraint -> ^( ACONSTR attribConstraint ) )
            // Velvet.g:169:4: attribConstraint
            {
            pushFollow(FOLLOW_attribConstraint_in_attributeConstraint1094);
            attribConstraint84=attribConstraint();

            state._fsp--;

            stream_attribConstraint.add(attribConstraint84.getTree());

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
            // 170:2: -> ^( ACONSTR attribConstraint )
            {
                // Velvet.g:170:5: ^( ACONSTR attribConstraint )
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
    // Velvet.g:173:1: attribConstraint : attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* ;
    public final VelvetParser.attribConstraint_return attribConstraint() throws RecognitionException {
        VelvetParser.attribConstraint_return retval = new VelvetParser.attribConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribNumInstance_return attribNumInstance85 =null;

        VelvetParser.attribOperator_return attribOperator86 =null;

        VelvetParser.attribNumInstance_return attribNumInstance87 =null;

        VelvetParser.attribRelation_return attribRelation88 =null;

        VelvetParser.attribNumInstance_return attribNumInstance89 =null;

        VelvetParser.attribOperator_return attribOperator90 =null;

        VelvetParser.attribNumInstance_return attribNumInstance91 =null;



        try {
            // Velvet.g:174:2: ( attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* )
            // Velvet.g:174:4: attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )*
            {
            root_0 = (Tree)adaptor.nil();


            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1114);
            attribNumInstance85=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance85.getTree());

            // Velvet.g:174:22: ( attribOperator attribNumInstance )*
            loop23:
            do {
                int alt23=2;
                int LA23_0 = input.LA(1);

                if ( (LA23_0==MINUS||LA23_0==PLUS) ) {
                    alt23=1;
                }


                switch (alt23) {
            	case 1 :
            	    // Velvet.g:174:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1117);
            	    attribOperator86=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator86.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1119);
            	    attribNumInstance87=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance87.getTree());

            	    }
            	    break;

            	default :
            	    break loop23;
                }
            } while (true);


            pushFollow(FOLLOW_attribRelation_in_attribConstraint1127);
            attribRelation88=attribRelation();

            state._fsp--;

            adaptor.addChild(root_0, attribRelation88.getTree());

            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1133);
            attribNumInstance89=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance89.getTree());

            // Velvet.g:176:22: ( attribOperator attribNumInstance )*
            loop24:
            do {
                int alt24=2;
                int LA24_0 = input.LA(1);

                if ( (LA24_0==MINUS||LA24_0==PLUS) ) {
                    alt24=1;
                }


                switch (alt24) {
            	case 1 :
            	    // Velvet.g:176:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1136);
            	    attribOperator90=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator90.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1138);
            	    attribNumInstance91=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance91.getTree());

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
    // Velvet.g:179:1: attribOperator : ( PLUS | MINUS );
    public final VelvetParser.attribOperator_return attribOperator() throws RecognitionException {
        VelvetParser.attribOperator_return retval = new VelvetParser.attribOperator_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set92=null;

        Tree set92_tree=null;

        try {
            // Velvet.g:180:2: ( PLUS | MINUS )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set92=(Token)input.LT(1);

            if ( input.LA(1)==MINUS||input.LA(1)==PLUS ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set92)
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
    // Velvet.g:184:1: attribNumInstance : ( INT | name );
    public final VelvetParser.attribNumInstance_return attribNumInstance() throws RecognitionException {
        VelvetParser.attribNumInstance_return retval = new VelvetParser.attribNumInstance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token INT93=null;
        VelvetParser.name_return name94 =null;


        Tree INT93_tree=null;

        try {
            // Velvet.g:185:2: ( INT | name )
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
                    // Velvet.g:185:4: INT
                    {
                    root_0 = (Tree)adaptor.nil();


                    INT93=(Token)match(input,INT,FOLLOW_INT_in_attribNumInstance1170); 
                    INT93_tree = 
                    (Tree)adaptor.create(INT93)
                    ;
                    adaptor.addChild(root_0, INT93_tree);


                    }
                    break;
                case 2 :
                    // Velvet.g:187:4: name
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_name_in_attribNumInstance1177);
                    name94=name();

                    state._fsp--;

                    adaptor.addChild(root_0, name94.getTree());

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
    // Velvet.g:190:1: attribute : ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) ;
    public final VelvetParser.attribute_return attribute() throws RecognitionException {
        VelvetParser.attribute_return retval = new VelvetParser.attribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token SEMI99=null;
        VelvetParser.intAttribute_return intAttribute95 =null;

        VelvetParser.floatAttribute_return floatAttribute96 =null;

        VelvetParser.stringAttribute_return stringAttribute97 =null;

        VelvetParser.boolAttribute_return boolAttribute98 =null;


        Tree SEMI99_tree=null;
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_intAttribute=new RewriteRuleSubtreeStream(adaptor,"rule intAttribute");
        RewriteRuleSubtreeStream stream_stringAttribute=new RewriteRuleSubtreeStream(adaptor,"rule stringAttribute");
        RewriteRuleSubtreeStream stream_floatAttribute=new RewriteRuleSubtreeStream(adaptor,"rule floatAttribute");
        RewriteRuleSubtreeStream stream_boolAttribute=new RewriteRuleSubtreeStream(adaptor,"rule boolAttribute");
        try {
            // Velvet.g:191:2: ( ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) )
            // Velvet.g:191:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI
            {
            // Velvet.g:191:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute )
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
                    // Velvet.g:191:5: intAttribute
                    {
                    pushFollow(FOLLOW_intAttribute_in_attribute1189);
                    intAttribute95=intAttribute();

                    state._fsp--;

                    stream_intAttribute.add(intAttribute95.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:191:20: floatAttribute
                    {
                    pushFollow(FOLLOW_floatAttribute_in_attribute1193);
                    floatAttribute96=floatAttribute();

                    state._fsp--;

                    stream_floatAttribute.add(floatAttribute96.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:191:37: stringAttribute
                    {
                    pushFollow(FOLLOW_stringAttribute_in_attribute1197);
                    stringAttribute97=stringAttribute();

                    state._fsp--;

                    stream_stringAttribute.add(stringAttribute97.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:191:55: boolAttribute
                    {
                    pushFollow(FOLLOW_boolAttribute_in_attribute1201);
                    boolAttribute98=boolAttribute();

                    state._fsp--;

                    stream_boolAttribute.add(boolAttribute98.getTree());

                    }
                    break;

            }


            SEMI99=(Token)match(input,SEMI,FOLLOW_SEMI_in_attribute1204);  
            stream_SEMI.add(SEMI99);


            // AST REWRITE
            // elements: intAttribute, boolAttribute, stringAttribute, floatAttribute
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 192:2: -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
            {
                // Velvet.g:192:5: ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(ATTR, "ATTR")
                , root_1);

                // Velvet.g:192:12: ( intAttribute )?
                if ( stream_intAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_intAttribute.nextTree());

                }
                stream_intAttribute.reset();

                // Velvet.g:192:26: ( floatAttribute )?
                if ( stream_floatAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_floatAttribute.nextTree());

                }
                stream_floatAttribute.reset();

                // Velvet.g:192:42: ( stringAttribute )?
                if ( stream_stringAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_stringAttribute.nextTree());

                }
                stream_stringAttribute.reset();

                // Velvet.g:192:59: ( boolAttribute )?
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
    // Velvet.g:195:1: intAttribute : VAR_INT ! name ( EQ ! INT )? ;
    public final VelvetParser.intAttribute_return intAttribute() throws RecognitionException {
        VelvetParser.intAttribute_return retval = new VelvetParser.intAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_INT100=null;
        Token EQ102=null;
        Token INT103=null;
        VelvetParser.name_return name101 =null;


        Tree VAR_INT100_tree=null;
        Tree EQ102_tree=null;
        Tree INT103_tree=null;

        try {
            // Velvet.g:195:13: ( VAR_INT ! name ( EQ ! INT )? )
            // Velvet.g:195:16: VAR_INT ! name ( EQ ! INT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_INT100=(Token)match(input,VAR_INT,FOLLOW_VAR_INT_in_intAttribute1233); 

            pushFollow(FOLLOW_name_in_intAttribute1236);
            name101=name();

            state._fsp--;

            adaptor.addChild(root_0, name101.getTree());

            // Velvet.g:195:30: ( EQ ! INT )?
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==EQ) ) {
                alt27=1;
            }
            switch (alt27) {
                case 1 :
                    // Velvet.g:195:31: EQ ! INT
                    {
                    EQ102=(Token)match(input,EQ,FOLLOW_EQ_in_intAttribute1239); 

                    INT103=(Token)match(input,INT,FOLLOW_INT_in_intAttribute1242); 
                    INT103_tree = 
                    (Tree)adaptor.create(INT103)
                    ;
                    adaptor.addChild(root_0, INT103_tree);


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
    // Velvet.g:196:1: floatAttribute : VAR_FLOAT ! name ( EQ ! FLOAT )? ;
    public final VelvetParser.floatAttribute_return floatAttribute() throws RecognitionException {
        VelvetParser.floatAttribute_return retval = new VelvetParser.floatAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_FLOAT104=null;
        Token EQ106=null;
        Token FLOAT107=null;
        VelvetParser.name_return name105 =null;


        Tree VAR_FLOAT104_tree=null;
        Tree EQ106_tree=null;
        Tree FLOAT107_tree=null;

        try {
            // Velvet.g:196:15: ( VAR_FLOAT ! name ( EQ ! FLOAT )? )
            // Velvet.g:196:18: VAR_FLOAT ! name ( EQ ! FLOAT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_FLOAT104=(Token)match(input,VAR_FLOAT,FOLLOW_VAR_FLOAT_in_floatAttribute1251); 

            pushFollow(FOLLOW_name_in_floatAttribute1254);
            name105=name();

            state._fsp--;

            adaptor.addChild(root_0, name105.getTree());

            // Velvet.g:196:34: ( EQ ! FLOAT )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==EQ) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // Velvet.g:196:35: EQ ! FLOAT
                    {
                    EQ106=(Token)match(input,EQ,FOLLOW_EQ_in_floatAttribute1257); 

                    FLOAT107=(Token)match(input,FLOAT,FOLLOW_FLOAT_in_floatAttribute1260); 
                    FLOAT107_tree = 
                    (Tree)adaptor.create(FLOAT107)
                    ;
                    adaptor.addChild(root_0, FLOAT107_tree);


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
    // Velvet.g:197:1: stringAttribute : VAR_STRING ! name ( EQ ! STRING )? ;
    public final VelvetParser.stringAttribute_return stringAttribute() throws RecognitionException {
        VelvetParser.stringAttribute_return retval = new VelvetParser.stringAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_STRING108=null;
        Token EQ110=null;
        Token STRING111=null;
        VelvetParser.name_return name109 =null;


        Tree VAR_STRING108_tree=null;
        Tree EQ110_tree=null;
        Tree STRING111_tree=null;

        try {
            // Velvet.g:197:16: ( VAR_STRING ! name ( EQ ! STRING )? )
            // Velvet.g:197:18: VAR_STRING ! name ( EQ ! STRING )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_STRING108=(Token)match(input,VAR_STRING,FOLLOW_VAR_STRING_in_stringAttribute1268); 

            pushFollow(FOLLOW_name_in_stringAttribute1271);
            name109=name();

            state._fsp--;

            adaptor.addChild(root_0, name109.getTree());

            // Velvet.g:197:35: ( EQ ! STRING )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==EQ) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // Velvet.g:197:36: EQ ! STRING
                    {
                    EQ110=(Token)match(input,EQ,FOLLOW_EQ_in_stringAttribute1274); 

                    STRING111=(Token)match(input,STRING,FOLLOW_STRING_in_stringAttribute1277); 
                    STRING111_tree = 
                    (Tree)adaptor.create(STRING111)
                    ;
                    adaptor.addChild(root_0, STRING111_tree);


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
    // Velvet.g:198:1: boolAttribute : VAR_BOOL ! name ( EQ ! BOOLEAN )? ;
    public final VelvetParser.boolAttribute_return boolAttribute() throws RecognitionException {
        VelvetParser.boolAttribute_return retval = new VelvetParser.boolAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_BOOL112=null;
        Token EQ114=null;
        Token BOOLEAN115=null;
        VelvetParser.name_return name113 =null;


        Tree VAR_BOOL112_tree=null;
        Tree EQ114_tree=null;
        Tree BOOLEAN115_tree=null;

        try {
            // Velvet.g:198:14: ( VAR_BOOL ! name ( EQ ! BOOLEAN )? )
            // Velvet.g:198:17: VAR_BOOL ! name ( EQ ! BOOLEAN )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_BOOL112=(Token)match(input,VAR_BOOL,FOLLOW_VAR_BOOL_in_boolAttribute1286); 

            pushFollow(FOLLOW_name_in_boolAttribute1289);
            name113=name();

            state._fsp--;

            adaptor.addChild(root_0, name113.getTree());

            // Velvet.g:198:32: ( EQ ! BOOLEAN )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==EQ) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // Velvet.g:198:33: EQ ! BOOLEAN
                    {
                    EQ114=(Token)match(input,EQ,FOLLOW_EQ_in_boolAttribute1292); 

                    BOOLEAN115=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_boolAttribute1295); 
                    BOOLEAN115_tree = 
                    (Tree)adaptor.create(BOOLEAN115)
                    ;
                    adaptor.addChild(root_0, BOOLEAN115_tree);


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
    // Velvet.g:200:1: unaryOp : OP_NOT ;
    public final VelvetParser.unaryOp_return unaryOp() throws RecognitionException {
        VelvetParser.unaryOp_return retval = new VelvetParser.unaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token OP_NOT116=null;

        Tree OP_NOT116_tree=null;

        try {
            // Velvet.g:201:2: ( OP_NOT )
            // Velvet.g:201:4: OP_NOT
            {
            root_0 = (Tree)adaptor.nil();


            OP_NOT116=(Token)match(input,OP_NOT,FOLLOW_OP_NOT_in_unaryOp1307); 
            OP_NOT116_tree = 
            (Tree)adaptor.create(OP_NOT116)
            ;
            adaptor.addChild(root_0, OP_NOT116_tree);


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
    // Velvet.g:204:1: binaryOp : ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT );
    public final VelvetParser.binaryOp_return binaryOp() throws RecognitionException {
        VelvetParser.binaryOp_return retval = new VelvetParser.binaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set117=null;

        Tree set117_tree=null;

        try {
            // Velvet.g:205:2: ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set117=(Token)input.LT(1);

            if ( (input.LA(1) >= OP_AND && input.LA(1) <= OP_IMPLIES)||(input.LA(1) >= OP_OR && input.LA(1) <= OP_XOR) ) {
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
    // $ANTLR end "binaryOp"


    public static class attribRelation_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "attribRelation"
    // Velvet.g:212:1: attribRelation : ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ );
    public final VelvetParser.attribRelation_return attribRelation() throws RecognitionException {
        VelvetParser.attribRelation_return retval = new VelvetParser.attribRelation_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set118=null;

        Tree set118_tree=null;

        try {
            // Velvet.g:213:2: ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set118=(Token)input.LT(1);

            if ( input.LA(1)==ATTR_OP_EQUALS||input.LA(1)==ATTR_OP_GREATER_EQ||input.LA(1)==ATTR_OP_LESS_EQ ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set118)
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


    protected DFA3 dfa3 = new DFA3(this);
    static final String DFA3_eotS =
        "\22\uffff";
    static final String DFA3_eofS =
        "\1\3\5\uffff\1\12\1\15\10\uffff\1\12\1\15";
    static final String DFA3_minS =
        "\1\42\2\40\1\uffff\2\40\2\21\1\40\2\uffff\1\40\2\uffff\2\40\2\21";
    static final String DFA3_maxS =
        "\1\65\2\40\1\uffff\2\41\2\65\1\40\2\uffff\1\40\2\uffff\2\41\2\65";
    static final String DFA3_acceptS =
        "\3\uffff\1\5\5\uffff\1\1\1\4\1\uffff\1\2\1\3\4\uffff";
    static final String DFA3_specialS =
        "\22\uffff}>";
    static final String[] DFA3_transitionS = {
            "\1\1\1\2\21\uffff\1\3",
            "\1\4",
            "\1\5",
            "",
            "\2\6",
            "\2\7",
            "\1\10\21\uffff\1\11\21\uffff\1\12",
            "\1\13\20\uffff\1\14\22\uffff\1\15",
            "\1\16",
            "",
            "",
            "\1\17",
            "",
            "",
            "\2\20",
            "\2\21",
            "\1\10\21\uffff\1\11\21\uffff\1\12",
            "\1\13\20\uffff\1\14\22\uffff\1\15"
    };

    static final short[] DFA3_eot = DFA.unpackEncodedString(DFA3_eotS);
    static final short[] DFA3_eof = DFA.unpackEncodedString(DFA3_eofS);
    static final char[] DFA3_min = DFA.unpackEncodedStringToUnsignedChars(DFA3_minS);
    static final char[] DFA3_max = DFA.unpackEncodedStringToUnsignedChars(DFA3_maxS);
    static final short[] DFA3_accept = DFA.unpackEncodedString(DFA3_acceptS);
    static final short[] DFA3_special = DFA.unpackEncodedString(DFA3_specialS);
    static final short[][] DFA3_transition;

    static {
        int numStates = DFA3_transitionS.length;
        DFA3_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA3_transition[i] = DFA.unpackEncodedString(DFA3_transitionS[i]);
        }
    }

    class DFA3 extends DFA {

        public DFA3(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 3;
            this.eot = DFA3_eot;
            this.eof = DFA3_eof;
            this.min = DFA3_min;
            this.max = DFA3_max;
            this.accept = DFA3_accept;
            this.special = DFA3_special;
            this.transition = DFA3_transition;
        }
        public String getDescription() {
            return "84:27: ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )?";
        }
    }
 

    public static final BitSet FOLLOW_concept_in_velvetModel466 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_cinterface_in_velvetModel468 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_velvetModel471 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONCEPT_in_concept484 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_concept486 = new BitSet(new long[]{0x0020000C00010002L});
    public static final BitSet FOLLOW_COLON_in_concept493 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_conceptBaseExt_in_concept495 = new BitSet(new long[]{0x0020000C00000002L});
    public static final BitSet FOLLOW_instanceImports_in_concept500 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_interfaceImports_in_concept502 = new BitSet(new long[]{0x0020000000000002L});
    public static final BitSet FOLLOW_interfaceImports_in_concept506 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_instanceImports_in_concept508 = new BitSet(new long[]{0x0020000000000002L});
    public static final BitSet FOLLOW_interfaceImports_in_concept512 = new BitSet(new long[]{0x0020000000000002L});
    public static final BitSet FOLLOW_instanceImports_in_concept516 = new BitSet(new long[]{0x0020000000000002L});
    public static final BitSet FOLLOW_definitions_in_concept523 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt556 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_conceptBaseExt559 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt561 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_IMPORTINSTANCE_in_instanceImports586 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_instanceImports588 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_instanceImports590 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_instanceImports593 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_instanceImports595 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_instanceImports597 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_IMPORTINTERFACE_in_interfaceImports626 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_interfaceImports628 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_interfaceImports630 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_interfaceImports633 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_interfaceImports635 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_interfaceImports637 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_CINTERFACE_in_cinterface664 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_cinterface666 = new BitSet(new long[]{0x0020000000010000L});
    public static final BitSet FOLLOW_COLON_in_cinterface670 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_interfaceBaseExt_in_cinterface672 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_definitions_in_cinterface676 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt703 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_interfaceBaseExt706 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt708 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_START_C_in_definitions748 = new BitSet(new long[]{0xF410048010500010L});
    public static final BitSet FOLLOW_definition_in_definitions750 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_END_C_in_definitions752 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_definition773 = new BitSet(new long[]{0xF410048010100012L});
    public static final BitSet FOLLOW_featureGroup_in_definition781 = new BitSet(new long[]{0xF400000000100002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_definition783 = new BitSet(new long[]{0xF400000000100002L});
    public static final BitSet FOLLOW_feature_in_definition792 = new BitSet(new long[]{0xF400008010100012L});
    public static final BitSet FOLLOW_feature_in_definition795 = new BitSet(new long[]{0xF400008010100012L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_definition799 = new BitSet(new long[]{0xF400008010100012L});
    public static final BitSet FOLLOW_constraint_in_nonFeatureDefinition821 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_use_in_nonFeatureDefinition826 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribute_in_nonFeatureDefinition831 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_USE_in_use843 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_use845 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_use847 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANDATORY_in_feature868 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature870 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature874 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature876 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature880 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature884 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_FEATURE_in_feature891 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_feature893 = new BitSet(new long[]{0x0028000000000000L});
    public static final BitSet FOLLOW_definitions_in_feature896 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SEMI_in_feature900 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_groupType_in_featureGroup931 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_START_C_in_featureGroup933 = new BitSet(new long[]{0x0000008010000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup935 = new BitSet(new long[]{0x0000008010000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup937 = new BitSet(new long[]{0x0000008010400010L});
    public static final BitSet FOLLOW_END_C_in_featureGroup940 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONSTRAINT_in_constraint983 = new BitSet(new long[]{0x0040802300000000L});
    public static final BitSet FOLLOW_ID_in_constraint987 = new BitSet(new long[]{0x0000000001000000L});
    public static final BitSet FOLLOW_EQ_in_constraint989 = new BitSet(new long[]{0x0040802300000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraint995 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_attributeConstraint_in_constraint999 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_constraint1002 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1015 = new BitSet(new long[]{0x0003700000000002L});
    public static final BitSet FOLLOW_binaryOp_in_constraintDefinition1018 = new BitSet(new long[]{0x0040800300000000L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1020 = new BitSet(new long[]{0x0003700000000002L});
    public static final BitSet FOLLOW_unaryOp_in_constraintOperand1047 = new BitSet(new long[]{0x0040800300000000L});
    public static final BitSet FOLLOW_START_R_in_constraintOperand1051 = new BitSet(new long[]{0x0040800300000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraintOperand1053 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_END_R_in_constraintOperand1055 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_constraintOperand1059 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribConstraint_in_attributeConstraint1094 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1114 = new BitSet(new long[]{0x0004010000000A80L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1117 = new BitSet(new long[]{0x0000002300000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1119 = new BitSet(new long[]{0x0004010000000A80L});
    public static final BitSet FOLLOW_attribRelation_in_attribConstraint1127 = new BitSet(new long[]{0x0000002300000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1133 = new BitSet(new long[]{0x0004010000000002L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1136 = new BitSet(new long[]{0x0000002300000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1138 = new BitSet(new long[]{0x0004010000000002L});
    public static final BitSet FOLLOW_INT_in_attribNumInstance1170 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_attribNumInstance1177 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_intAttribute_in_attribute1189 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_floatAttribute_in_attribute1193 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_stringAttribute_in_attribute1197 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_boolAttribute_in_attribute1201 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_attribute1204 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_INT_in_intAttribute1233 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_intAttribute1236 = new BitSet(new long[]{0x0000000001000002L});
    public static final BitSet FOLLOW_EQ_in_intAttribute1239 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_INT_in_intAttribute1242 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_FLOAT_in_floatAttribute1251 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_floatAttribute1254 = new BitSet(new long[]{0x0000000001000002L});
    public static final BitSet FOLLOW_EQ_in_floatAttribute1257 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_FLOAT_in_floatAttribute1260 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_STRING_in_stringAttribute1268 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_stringAttribute1271 = new BitSet(new long[]{0x0000000001000002L});
    public static final BitSet FOLLOW_EQ_in_stringAttribute1274 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_STRING_in_stringAttribute1277 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_BOOL_in_boolAttribute1286 = new BitSet(new long[]{0x0000000300000000L});
    public static final BitSet FOLLOW_name_in_boolAttribute1289 = new BitSet(new long[]{0x0000000001000002L});
    public static final BitSet FOLLOW_EQ_in_boolAttribute1292 = new BitSet(new long[]{0x0000000000004000L});
    public static final BitSet FOLLOW_BOOLEAN_in_boolAttribute1295 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_OP_NOT_in_unaryOp1307 = new BitSet(new long[]{0x0000000000000002L});

}