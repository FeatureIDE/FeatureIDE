// $ANTLR 3.4 Velvet.g 2014-06-16 14:59:51

package de.ovgu.featureide.fm.core.io.velvet;

import org.antlr.runtime.BaseRecognizer;
import org.antlr.runtime.BitSet;
import org.antlr.runtime.DFA;
import org.antlr.runtime.EarlyExitException;
import org.antlr.runtime.MismatchedSetException;
import org.antlr.runtime.NoViableAltException;
import org.antlr.runtime.Parser;
import org.antlr.runtime.ParserRuleReturnScope;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.RecognizerSharedState;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenStream;
import org.antlr.runtime.tree.CommonTreeAdaptor;
import org.antlr.runtime.tree.RewriteEarlyExitException;
import org.antlr.runtime.tree.RewriteRuleSubtreeStream;
import org.antlr.runtime.tree.RewriteRuleTokenStream;
import org.antlr.runtime.tree.Tree;
import org.antlr.runtime.tree.TreeAdaptor;

import de.ovgu.featureide.fm.core.FMCorePlugin;


@SuppressWarnings({"all", "warnings", "unchecked"})
public class VelvetParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "ABSTRACT", "ACONSTR", "ATTR", "ATTR_OP_EQUALS", "ATTR_OP_GREATER", "ATTR_OP_GREATER_EQ", "ATTR_OP_LESS", "ATTR_OP_LESS_EQ", "ATTR_OP_NOT_EQUALS", "BASEEXT", "BOOLEAN", "CINTERFACE", "COLON", "COMMA", "CONCEPT", "CONSTR", "CONSTRAINT", "DEF", "EMPTY", "END_C", "END_R", "EQ", "ESC_SEQ", "EXPONENT", "FEAT", "FEATURE", "FLOAT", "GROUP", "HEX_DIGIT", "ID", "IDPath", "IMPORTINSTANCE", "IMPORTINTERFACE", "INST", "INT", "INTF", "MANDATORY", "MINUS", "ML_COMMENT", "OCTAL_ESC", "ONEOF", "OPERAND", "OP_AND", "OP_EQUIVALENT", "OP_IMPLIES", "OP_NOT", "OP_OR", "OP_XOR", "PLUS", "SEMI", "SL_COMMENT", "SOMEOF", "START_C", "START_R", "STRING", "UNARYOP", "UNICODE_ESC", "USE", "USES", "VAR_BOOL", "VAR_FLOAT", "VAR_INT", "VAR_STRING", "WS"
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
    public static final int EMPTY=22;
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
    public static final int IMPORTINSTANCE=35;
    public static final int IMPORTINTERFACE=36;
    public static final int INST=37;
    public static final int INT=38;
    public static final int INTF=39;
    public static final int MANDATORY=40;
    public static final int MINUS=41;
    public static final int ML_COMMENT=42;
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
    public static final int SEMI=53;
    public static final int SL_COMMENT=54;
    public static final int SOMEOF=55;
    public static final int START_C=56;
    public static final int START_R=57;
    public static final int STRING=58;
    public static final int UNARYOP=59;
    public static final int UNICODE_ESC=60;
    public static final int USE=61;
    public static final int USES=62;
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
    // Velvet.g:79:1: velvetModel : ( concept | cinterface ) EOF ;
    public final VelvetParser.velvetModel_return velvetModel() throws RecognitionException {
        VelvetParser.velvetModel_return retval = new VelvetParser.velvetModel_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token EOF3=null;
        VelvetParser.concept_return concept1 =null;

        VelvetParser.cinterface_return cinterface2 =null;


        Tree EOF3_tree=null;

        try {
            // Velvet.g:80:2: ( ( concept | cinterface ) EOF )
            // Velvet.g:80:4: ( concept | cinterface ) EOF
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:80:4: ( concept | cinterface )
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
                    // Velvet.g:80:5: concept
                    {
                    pushFollow(FOLLOW_concept_in_velvetModel470);
                    concept1=concept();

                    state._fsp--;

                    adaptor.addChild(root_0, concept1.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:80:13: cinterface
                    {
                    pushFollow(FOLLOW_cinterface_in_velvetModel472);
                    cinterface2=cinterface();

                    state._fsp--;

                    adaptor.addChild(root_0, cinterface2.getTree());

                    }
                    break;

            }


            EOF3=(Token)match(input,EOF,FOLLOW_EOF_in_velvetModel475); 
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
    // Velvet.g:83:1: concept : CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )? ( definitions )? -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? ) ;
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
            // Velvet.g:84:2: ( CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )? ( definitions )? -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? ) )
            // Velvet.g:84:4: CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )? ( definitions )?
            {
            CONCEPT4=(Token)match(input,CONCEPT,FOLLOW_CONCEPT_in_concept488);  
            stream_CONCEPT.add(CONCEPT4);


            ID5=(Token)match(input,ID,FOLLOW_ID_in_concept490);  
            stream_ID.add(ID5);


            // Velvet.g:85:3: ( COLON conceptBaseExt )?
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0==COLON) ) {
                alt2=1;
            }
            switch (alt2) {
                case 1 :
                    // Velvet.g:85:4: COLON conceptBaseExt
                    {
                    COLON6=(Token)match(input,COLON,FOLLOW_COLON_in_concept497);  
                    stream_COLON.add(COLON6);


                    pushFollow(FOLLOW_conceptBaseExt_in_concept499);
                    conceptBaseExt7=conceptBaseExt();

                    state._fsp--;

                    stream_conceptBaseExt.add(conceptBaseExt7.getTree());

                    }
                    break;

            }


            // Velvet.g:85:27: ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )?
            int alt3=5;
            alt3 = dfa3.predict(input);
            switch (alt3) {
                case 1 :
                    // Velvet.g:85:28: instanceImports interfaceImports
                    {
                    pushFollow(FOLLOW_instanceImports_in_concept504);
                    instanceImports8=instanceImports();

                    state._fsp--;

                    stream_instanceImports.add(instanceImports8.getTree());

                    pushFollow(FOLLOW_interfaceImports_in_concept506);
                    interfaceImports9=interfaceImports();

                    state._fsp--;

                    stream_interfaceImports.add(interfaceImports9.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:85:63: interfaceImports instanceImports
                    {
                    pushFollow(FOLLOW_interfaceImports_in_concept510);
                    interfaceImports10=interfaceImports();

                    state._fsp--;

                    stream_interfaceImports.add(interfaceImports10.getTree());

                    pushFollow(FOLLOW_instanceImports_in_concept512);
                    instanceImports11=instanceImports();

                    state._fsp--;

                    stream_instanceImports.add(instanceImports11.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:85:98: interfaceImports
                    {
                    pushFollow(FOLLOW_interfaceImports_in_concept516);
                    interfaceImports12=interfaceImports();

                    state._fsp--;

                    stream_interfaceImports.add(interfaceImports12.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:85:117: instanceImports
                    {
                    pushFollow(FOLLOW_instanceImports_in_concept520);
                    instanceImports13=instanceImports();

                    state._fsp--;

                    stream_instanceImports.add(instanceImports13.getTree());

                    }
                    break;

            }


            // Velvet.g:86:3: ( definitions )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0==START_C) ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // Velvet.g:86:3: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_concept527);
                    definitions14=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions14.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: conceptBaseExt, definitions, interfaceImports, ID, instanceImports, CONCEPT
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 87:2: -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? )
            {
                // Velvet.g:87:5: ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CONCEPT.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:87:18: ( conceptBaseExt )?
                if ( stream_conceptBaseExt.hasNext() ) {
                    adaptor.addChild(root_1, stream_conceptBaseExt.nextTree());

                }
                stream_conceptBaseExt.reset();

                // Velvet.g:87:34: ( instanceImports )?
                if ( stream_instanceImports.hasNext() ) {
                    adaptor.addChild(root_1, stream_instanceImports.nextTree());

                }
                stream_instanceImports.reset();

                // Velvet.g:87:51: ( interfaceImports )?
                if ( stream_interfaceImports.hasNext() ) {
                    adaptor.addChild(root_1, stream_interfaceImports.nextTree());

                }
                stream_interfaceImports.reset();

                // Velvet.g:87:69: ( definitions )?
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
    // Velvet.g:90:1: conceptBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
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
            // Velvet.g:91:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:91:4: ID ( COMMA ID )*
            {
            ID15=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt560);  
            stream_ID.add(ID15);


            // Velvet.g:91:7: ( COMMA ID )*
            loop5:
            do {
                int alt5=2;
                int LA5_0 = input.LA(1);

                if ( (LA5_0==COMMA) ) {
                    alt5=1;
                }


                switch (alt5) {
            	case 1 :
            	    // Velvet.g:91:8: COMMA ID
            	    {
            	    COMMA16=(Token)match(input,COMMA,FOLLOW_COMMA_in_conceptBaseExt563);  
            	    stream_COMMA.add(COMMA16);


            	    ID17=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt565);  
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
            // 92:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:92:5: ^( BASEEXT ( ID )+ )
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
    // Velvet.g:95:1: instanceImports : IMPORTINSTANCE ID name ( COMMA ID name )* -> ^( INST ( ID name )+ ) ;
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
            // Velvet.g:96:2: ( IMPORTINSTANCE ID name ( COMMA ID name )* -> ^( INST ( ID name )+ ) )
            // Velvet.g:96:4: IMPORTINSTANCE ID name ( COMMA ID name )*
            {
            IMPORTINSTANCE18=(Token)match(input,IMPORTINSTANCE,FOLLOW_IMPORTINSTANCE_in_instanceImports590);  
            stream_IMPORTINSTANCE.add(IMPORTINSTANCE18);


            ID19=(Token)match(input,ID,FOLLOW_ID_in_instanceImports592);  
            stream_ID.add(ID19);


            pushFollow(FOLLOW_name_in_instanceImports594);
            name20=name();

            state._fsp--;

            stream_name.add(name20.getTree());

            // Velvet.g:96:27: ( COMMA ID name )*
            loop6:
            do {
                int alt6=2;
                int LA6_0 = input.LA(1);

                if ( (LA6_0==COMMA) ) {
                    alt6=1;
                }


                switch (alt6) {
            	case 1 :
            	    // Velvet.g:96:28: COMMA ID name
            	    {
            	    COMMA21=(Token)match(input,COMMA,FOLLOW_COMMA_in_instanceImports597);  
            	    stream_COMMA.add(COMMA21);


            	    ID22=(Token)match(input,ID,FOLLOW_ID_in_instanceImports599);  
            	    stream_ID.add(ID22);


            	    pushFollow(FOLLOW_name_in_instanceImports601);
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
            // 97:2: -> ^( INST ( ID name )+ )
            {
                // Velvet.g:97:5: ^( INST ( ID name )+ )
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
    // Velvet.g:100:1: interfaceImports : IMPORTINTERFACE ID name ( COMMA ID name )* -> ^( INTF ( ID name )+ ) ;
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
            // Velvet.g:101:2: ( IMPORTINTERFACE ID name ( COMMA ID name )* -> ^( INTF ( ID name )+ ) )
            // Velvet.g:101:4: IMPORTINTERFACE ID name ( COMMA ID name )*
            {
            IMPORTINTERFACE24=(Token)match(input,IMPORTINTERFACE,FOLLOW_IMPORTINTERFACE_in_interfaceImports630);  
            stream_IMPORTINTERFACE.add(IMPORTINTERFACE24);


            ID25=(Token)match(input,ID,FOLLOW_ID_in_interfaceImports632);  
            stream_ID.add(ID25);


            pushFollow(FOLLOW_name_in_interfaceImports634);
            name26=name();

            state._fsp--;

            stream_name.add(name26.getTree());

            // Velvet.g:101:28: ( COMMA ID name )*
            loop7:
            do {
                int alt7=2;
                int LA7_0 = input.LA(1);

                if ( (LA7_0==COMMA) ) {
                    alt7=1;
                }


                switch (alt7) {
            	case 1 :
            	    // Velvet.g:101:29: COMMA ID name
            	    {
            	    COMMA27=(Token)match(input,COMMA,FOLLOW_COMMA_in_interfaceImports637);  
            	    stream_COMMA.add(COMMA27);


            	    ID28=(Token)match(input,ID,FOLLOW_ID_in_interfaceImports639);  
            	    stream_ID.add(ID28);


            	    pushFollow(FOLLOW_name_in_interfaceImports641);
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
            // elements: name, ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 102:2: -> ^( INTF ( ID name )+ )
            {
                // Velvet.g:102:5: ^( INTF ( ID name )+ )
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
    // Velvet.g:105:1: cinterface : CINTERFACE ID ( COLON interfaceBaseExt )? definitions -> ^( CINTERFACE ID ( interfaceBaseExt )? definitions ) ;
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
            // Velvet.g:105:12: ( CINTERFACE ID ( COLON interfaceBaseExt )? definitions -> ^( CINTERFACE ID ( interfaceBaseExt )? definitions ) )
            // Velvet.g:105:14: CINTERFACE ID ( COLON interfaceBaseExt )? definitions
            {
            CINTERFACE30=(Token)match(input,CINTERFACE,FOLLOW_CINTERFACE_in_cinterface668);  
            stream_CINTERFACE.add(CINTERFACE30);


            ID31=(Token)match(input,ID,FOLLOW_ID_in_cinterface670);  
            stream_ID.add(ID31);


            // Velvet.g:105:29: ( COLON interfaceBaseExt )?
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==COLON) ) {
                alt8=1;
            }
            switch (alt8) {
                case 1 :
                    // Velvet.g:105:30: COLON interfaceBaseExt
                    {
                    COLON32=(Token)match(input,COLON,FOLLOW_COLON_in_cinterface674);  
                    stream_COLON.add(COLON32);


                    pushFollow(FOLLOW_interfaceBaseExt_in_cinterface676);
                    interfaceBaseExt33=interfaceBaseExt();

                    state._fsp--;

                    stream_interfaceBaseExt.add(interfaceBaseExt33.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_cinterface680);
            definitions34=definitions();

            state._fsp--;

            stream_definitions.add(definitions34.getTree());

            // AST REWRITE
            // elements: interfaceBaseExt, CINTERFACE, definitions, ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 106:2: -> ^( CINTERFACE ID ( interfaceBaseExt )? definitions )
            {
                // Velvet.g:106:5: ^( CINTERFACE ID ( interfaceBaseExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CINTERFACE.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:106:21: ( interfaceBaseExt )?
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
    // Velvet.g:109:1: interfaceBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
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
            // Velvet.g:110:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:110:4: ID ( COMMA ID )*
            {
            ID35=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt707);  
            stream_ID.add(ID35);


            // Velvet.g:110:7: ( COMMA ID )*
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( (LA9_0==COMMA) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // Velvet.g:110:8: COMMA ID
            	    {
            	    COMMA36=(Token)match(input,COMMA,FOLLOW_COMMA_in_interfaceBaseExt710);  
            	    stream_COMMA.add(COMMA36);


            	    ID37=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt712);  
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

        Token set38=null;

        Tree set38_tree=null;

        try {
            // Velvet.g:114:5: ( ID | IDPath )
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
    // Velvet.g:118:1: definitions : START_C definition END_C -> ^( DEF ( definition )? EMPTY ) ;
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
            // Velvet.g:119:2: ( START_C definition END_C -> ^( DEF ( definition )? EMPTY ) )
            // Velvet.g:119:4: START_C definition END_C
            {
            START_C39=(Token)match(input,START_C,FOLLOW_START_C_in_definitions752);  
            stream_START_C.add(START_C39);


            pushFollow(FOLLOW_definition_in_definitions754);
            definition40=definition();

            state._fsp--;

            stream_definition.add(definition40.getTree());

            END_C41=(Token)match(input,END_C,FOLLOW_END_C_in_definitions756);  
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
            // 120:2: -> ^( DEF ( definition )? EMPTY )
            {
                // Velvet.g:120:5: ^( DEF ( definition )? EMPTY )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(DEF, "DEF")
                , root_1);

                // Velvet.g:120:11: ( definition )?
                if ( stream_definition.hasNext() ) {
                    adaptor.addChild(root_1, stream_definition.nextTree());

                }
                stream_definition.reset();

                adaptor.addChild(root_1, 
                (Tree)adaptor.create(EMPTY, "EMPTY")
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
    // $ANTLR end "definitions"


    public static class definition_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "definition"
    // Velvet.g:123:1: definition : ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? ;
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
            // Velvet.g:124:2: ( ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? )
            // Velvet.g:124:4: ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:124:4: ( nonFeatureDefinition )*
            loop10:
            do {
                int alt10=2;
                int LA10_0 = input.LA(1);

                if ( (LA10_0==CONSTRAINT||LA10_0==USE||(LA10_0 >= VAR_BOOL && LA10_0 <= VAR_STRING)) ) {
                    alt10=1;
                }


                switch (alt10) {
            	case 1 :
            	    // Velvet.g:124:4: nonFeatureDefinition
            	    {
            	    pushFollow(FOLLOW_nonFeatureDefinition_in_definition780);
            	    nonFeatureDefinition42=nonFeatureDefinition();

            	    state._fsp--;

            	    adaptor.addChild(root_0, nonFeatureDefinition42.getTree());

            	    }
            	    break;

            	default :
            	    break loop10;
                }
            } while (true);


            // Velvet.g:124:26: ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
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
                    // Velvet.g:125:3: ( featureGroup ( nonFeatureDefinition )* )
                    {
                    // Velvet.g:125:3: ( featureGroup ( nonFeatureDefinition )* )
                    // Velvet.g:125:4: featureGroup ( nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_featureGroup_in_definition788);
                    featureGroup43=featureGroup();

                    state._fsp--;

                    adaptor.addChild(root_0, featureGroup43.getTree());

                    // Velvet.g:125:17: ( nonFeatureDefinition )*
                    loop11:
                    do {
                        int alt11=2;
                        int LA11_0 = input.LA(1);

                        if ( (LA11_0==CONSTRAINT||LA11_0==USE||(LA11_0 >= VAR_BOOL && LA11_0 <= VAR_STRING)) ) {
                            alt11=1;
                        }


                        switch (alt11) {
                    	case 1 :
                    	    // Velvet.g:125:17: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_definition790);
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
                    // Velvet.g:126:3: ( feature ( feature | nonFeatureDefinition )* )
                    {
                    // Velvet.g:126:3: ( feature ( feature | nonFeatureDefinition )* )
                    // Velvet.g:126:4: feature ( feature | nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_feature_in_definition799);
                    feature45=feature();

                    state._fsp--;

                    adaptor.addChild(root_0, feature45.getTree());

                    // Velvet.g:126:12: ( feature | nonFeatureDefinition )*
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
                    	    // Velvet.g:126:13: feature
                    	    {
                    	    pushFollow(FOLLOW_feature_in_definition802);
                    	    feature46=feature();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, feature46.getTree());

                    	    }
                    	    break;
                    	case 2 :
                    	    // Velvet.g:126:23: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_definition806);
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
    // Velvet.g:130:1: nonFeatureDefinition : ( constraint | use | attribute );
    public final VelvetParser.nonFeatureDefinition_return nonFeatureDefinition() throws RecognitionException {
        VelvetParser.nonFeatureDefinition_return retval = new VelvetParser.nonFeatureDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraint_return constraint48 =null;

        VelvetParser.use_return use49 =null;

        VelvetParser.attribute_return attribute50 =null;



        try {
            // Velvet.g:131:2: ( constraint | use | attribute )
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
                    // Velvet.g:131:4: constraint
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_constraint_in_nonFeatureDefinition828);
                    constraint48=constraint();

                    state._fsp--;

                    adaptor.addChild(root_0, constraint48.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:132:4: use
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_use_in_nonFeatureDefinition833);
                    use49=use();

                    state._fsp--;

                    adaptor.addChild(root_0, use49.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:133:4: attribute
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_attribute_in_nonFeatureDefinition838);
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
    // Velvet.g:136:1: use : USE name SEMI -> ^( USES name ) ;
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
            // Velvet.g:136:5: ( USE name SEMI -> ^( USES name ) )
            // Velvet.g:136:7: USE name SEMI
            {
            USE51=(Token)match(input,USE,FOLLOW_USE_in_use850);  
            stream_USE.add(USE51);


            pushFollow(FOLLOW_name_in_use852);
            name52=name();

            state._fsp--;

            stream_name.add(name52.getTree());

            SEMI53=(Token)match(input,SEMI,FOLLOW_SEMI_in_use854);  
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
            // 137:2: -> ^( USES name )
            {
                // Velvet.g:137:5: ^( USES name )
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
    // Velvet.g:140:1: feature : ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) ;
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
            // Velvet.g:141:2: ( ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) )
            // Velvet.g:141:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI )
            {
            // Velvet.g:141:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )?
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
                    // Velvet.g:141:5: MANDATORY ABSTRACT
                    {
                    MANDATORY54=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature875);  
                    stream_MANDATORY.add(MANDATORY54);


                    ABSTRACT55=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature877);  
                    stream_ABSTRACT.add(ABSTRACT55);


                    }
                    break;
                case 2 :
                    // Velvet.g:141:26: ABSTRACT MANDATORY
                    {
                    ABSTRACT56=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature881);  
                    stream_ABSTRACT.add(ABSTRACT56);


                    MANDATORY57=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature883);  
                    stream_MANDATORY.add(MANDATORY57);


                    }
                    break;
                case 3 :
                    // Velvet.g:141:47: MANDATORY
                    {
                    MANDATORY58=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature887);  
                    stream_MANDATORY.add(MANDATORY58);


                    }
                    break;
                case 4 :
                    // Velvet.g:141:59: ABSTRACT
                    {
                    ABSTRACT59=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature891);  
                    stream_ABSTRACT.add(ABSTRACT59);


                    }
                    break;

            }


            FEATURE60=(Token)match(input,FEATURE,FOLLOW_FEATURE_in_feature898);  
            stream_FEATURE.add(FEATURE60);


            pushFollow(FOLLOW_name_in_feature900);
            name61=name();

            state._fsp--;

            stream_name.add(name61.getTree());

            // Velvet.g:142:17: ( definitions | SEMI )
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
                    // Velvet.g:142:18: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_feature903);
                    definitions62=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions62.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:142:32: SEMI
                    {
                    SEMI63=(Token)match(input,SEMI,FOLLOW_SEMI_in_feature907);  
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
            // 143:2: -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
            {
                // Velvet.g:143:5: ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(FEAT, "FEAT")
                , root_1);

                adaptor.addChild(root_1, stream_name.nextTree());

                // Velvet.g:143:17: ( MANDATORY )?
                if ( stream_MANDATORY.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_MANDATORY.nextNode()
                    );

                }
                stream_MANDATORY.reset();

                // Velvet.g:143:28: ( ABSTRACT )?
                if ( stream_ABSTRACT.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ABSTRACT.nextNode()
                    );

                }
                stream_ABSTRACT.reset();

                // Velvet.g:143:38: ( definitions )?
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
    // Velvet.g:146:1: featureGroup : groupType START_C ( feature )+ END_C -> ^( GROUP groupType ( feature )+ ) ;
    public final VelvetParser.featureGroup_return featureGroup() throws RecognitionException {
        VelvetParser.featureGroup_return retval = new VelvetParser.featureGroup_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C65=null;
        Token END_C67=null;
        VelvetParser.groupType_return groupType64 =null;

        VelvetParser.feature_return feature66 =null;


        Tree START_C65_tree=null;
        Tree END_C67_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_groupType=new RewriteRuleSubtreeStream(adaptor,"rule groupType");
        RewriteRuleSubtreeStream stream_feature=new RewriteRuleSubtreeStream(adaptor,"rule feature");
        try {
            // Velvet.g:147:2: ( groupType START_C ( feature )+ END_C -> ^( GROUP groupType ( feature )+ ) )
            // Velvet.g:147:4: groupType START_C ( feature )+ END_C
            {
            pushFollow(FOLLOW_groupType_in_featureGroup938);
            groupType64=groupType();

            state._fsp--;

            stream_groupType.add(groupType64.getTree());

            START_C65=(Token)match(input,START_C,FOLLOW_START_C_in_featureGroup940);  
            stream_START_C.add(START_C65);


            // Velvet.g:147:22: ( feature )+
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
            	    // Velvet.g:147:22: feature
            	    {
            	    pushFollow(FOLLOW_feature_in_featureGroup942);
            	    feature66=feature();

            	    state._fsp--;

            	    stream_feature.add(feature66.getTree());

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


            END_C67=(Token)match(input,END_C,FOLLOW_END_C_in_featureGroup945);  
            stream_END_C.add(END_C67);


            // AST REWRITE
            // elements: feature, groupType
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 148:2: -> ^( GROUP groupType ( feature )+ )
            {
                // Velvet.g:148:5: ^( GROUP groupType ( feature )+ )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(GROUP, "GROUP")
                , root_1);

                adaptor.addChild(root_1, stream_groupType.nextTree());

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
    // Velvet.g:151:1: groupType : ( SOMEOF | ONEOF );
    public final VelvetParser.groupType_return groupType() throws RecognitionException {
        VelvetParser.groupType_return retval = new VelvetParser.groupType_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set68=null;

        Tree set68_tree=null;

        try {
            // Velvet.g:152:2: ( SOMEOF | ONEOF )
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
    // Velvet.g:156:1: constraint : CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !;
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
            // Velvet.g:157:2: ( CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !)
            // Velvet.g:157:4: CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !
            {
            root_0 = (Tree)adaptor.nil();


            CONSTRAINT69=(Token)match(input,CONSTRAINT,FOLLOW_CONSTRAINT_in_constraint986); 
            CONSTRAINT69_tree = 
            (Tree)adaptor.create(CONSTRAINT69)
            ;
            root_0 = (Tree)adaptor.becomeRoot(CONSTRAINT69_tree, root_0);


            // Velvet.g:157:16: ( ID EQ !)?
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
                    // Velvet.g:157:17: ID EQ !
                    {
                    ID70=(Token)match(input,ID,FOLLOW_ID_in_constraint990); 
                    ID70_tree = 
                    (Tree)adaptor.create(ID70)
                    ;
                    adaptor.addChild(root_0, ID70_tree);


                    EQ71=(Token)match(input,EQ,FOLLOW_EQ_in_constraint992); 

                    }
                    break;

            }


            // Velvet.g:157:26: ( constraintDefinition | attributeConstraint )
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
                    // Velvet.g:157:27: constraintDefinition
                    {
                    pushFollow(FOLLOW_constraintDefinition_in_constraint998);
                    constraintDefinition72=constraintDefinition();

                    state._fsp--;

                    adaptor.addChild(root_0, constraintDefinition72.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:157:50: attributeConstraint
                    {
                    pushFollow(FOLLOW_attributeConstraint_in_constraint1002);
                    attributeConstraint73=attributeConstraint();

                    state._fsp--;

                    adaptor.addChild(root_0, attributeConstraint73.getTree());

                    }
                    break;

            }


            SEMI74=(Token)match(input,SEMI,FOLLOW_SEMI_in_constraint1005); 

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
    // Velvet.g:160:1: constraintDefinition : constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) ;
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
            // Velvet.g:161:2: ( constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) )
            // Velvet.g:161:4: constraintOperand ( binaryOp constraintOperand )*
            {
            pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1018);
            constraintOperand75=constraintOperand();

            state._fsp--;

            stream_constraintOperand.add(constraintOperand75.getTree());

            // Velvet.g:161:22: ( binaryOp constraintOperand )*
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( ((LA20_0 >= OP_AND && LA20_0 <= OP_IMPLIES)||(LA20_0 >= OP_OR && LA20_0 <= OP_XOR)) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // Velvet.g:161:23: binaryOp constraintOperand
            	    {
            	    pushFollow(FOLLOW_binaryOp_in_constraintDefinition1021);
            	    binaryOp76=binaryOp();

            	    state._fsp--;

            	    stream_binaryOp.add(binaryOp76.getTree());

            	    pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1023);
            	    constraintOperand77=constraintOperand();

            	    state._fsp--;

            	    stream_constraintOperand.add(constraintOperand77.getTree());

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
            // 162:2: -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
            {
                // Velvet.g:162:5: ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
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

                // Velvet.g:162:33: ( binaryOp )*
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
    // Velvet.g:165:1: constraintOperand : ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? ;
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
            // Velvet.g:165:19: ( ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? )
            // Velvet.g:165:21: ( unaryOp )* ( START_R constraintDefinition END_R | name )
            {
            // Velvet.g:165:21: ( unaryOp )*
            loop21:
            do {
                int alt21=2;
                int LA21_0 = input.LA(1);

                if ( (LA21_0==OP_NOT) ) {
                    alt21=1;
                }


                switch (alt21) {
            	case 1 :
            	    // Velvet.g:165:21: unaryOp
            	    {
            	    pushFollow(FOLLOW_unaryOp_in_constraintOperand1050);
            	    unaryOp78=unaryOp();

            	    state._fsp--;

            	    stream_unaryOp.add(unaryOp78.getTree());

            	    }
            	    break;

            	default :
            	    break loop21;
                }
            } while (true);


            // Velvet.g:165:30: ( START_R constraintDefinition END_R | name )
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
                    // Velvet.g:165:31: START_R constraintDefinition END_R
                    {
                    START_R79=(Token)match(input,START_R,FOLLOW_START_R_in_constraintOperand1054);  
                    stream_START_R.add(START_R79);


                    pushFollow(FOLLOW_constraintDefinition_in_constraintOperand1056);
                    constraintDefinition80=constraintDefinition();

                    state._fsp--;

                    stream_constraintDefinition.add(constraintDefinition80.getTree());

                    END_R81=(Token)match(input,END_R,FOLLOW_END_R_in_constraintOperand1058);  
                    stream_END_R.add(END_R81);


                    }
                    break;
                case 2 :
                    // Velvet.g:165:68: name
                    {
                    pushFollow(FOLLOW_name_in_constraintOperand1062);
                    name82=name();

                    state._fsp--;

                    stream_name.add(name82.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: unaryOp, constraintDefinition, name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 166:2: -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )?
            {
                // Velvet.g:166:5: ( constraintDefinition )?
                if ( stream_constraintDefinition.hasNext() ) {
                    adaptor.addChild(root_0, stream_constraintDefinition.nextTree());

                }
                stream_constraintDefinition.reset();

                // Velvet.g:166:27: ( ^( UNARYOP unaryOp ) )*
                while ( stream_unaryOp.hasNext() ) {
                    // Velvet.g:166:27: ^( UNARYOP unaryOp )
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

                // Velvet.g:166:47: ( ^( OPERAND name ) )?
                if ( stream_name.hasNext() ) {
                    // Velvet.g:166:47: ^( OPERAND name )
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
    // Velvet.g:169:1: attributeConstraint : attribConstraint -> ^( ACONSTR attribConstraint ) ;
    public final VelvetParser.attributeConstraint_return attributeConstraint() throws RecognitionException {
        VelvetParser.attributeConstraint_return retval = new VelvetParser.attributeConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribConstraint_return attribConstraint83 =null;


        RewriteRuleSubtreeStream stream_attribConstraint=new RewriteRuleSubtreeStream(adaptor,"rule attribConstraint");
        try {
            // Velvet.g:170:2: ( attribConstraint -> ^( ACONSTR attribConstraint ) )
            // Velvet.g:170:4: attribConstraint
            {
            pushFollow(FOLLOW_attribConstraint_in_attributeConstraint1097);
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
            // 171:2: -> ^( ACONSTR attribConstraint )
            {
                // Velvet.g:171:5: ^( ACONSTR attribConstraint )
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
    // Velvet.g:174:1: attribConstraint : attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* ;
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
            // Velvet.g:175:2: ( attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* )
            // Velvet.g:175:4: attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )*
            {
            root_0 = (Tree)adaptor.nil();


            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1117);
            attribNumInstance84=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance84.getTree());

            // Velvet.g:175:22: ( attribOperator attribNumInstance )*
            loop23:
            do {
                int alt23=2;
                int LA23_0 = input.LA(1);

                if ( (LA23_0==MINUS||LA23_0==PLUS) ) {
                    alt23=1;
                }


                switch (alt23) {
            	case 1 :
            	    // Velvet.g:175:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1120);
            	    attribOperator85=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator85.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1122);
            	    attribNumInstance86=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance86.getTree());

            	    }
            	    break;

            	default :
            	    break loop23;
                }
            } while (true);


            pushFollow(FOLLOW_attribRelation_in_attribConstraint1130);
            attribRelation87=attribRelation();

            state._fsp--;

            adaptor.addChild(root_0, attribRelation87.getTree());

            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1136);
            attribNumInstance88=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance88.getTree());

            // Velvet.g:177:22: ( attribOperator attribNumInstance )*
            loop24:
            do {
                int alt24=2;
                int LA24_0 = input.LA(1);

                if ( (LA24_0==MINUS||LA24_0==PLUS) ) {
                    alt24=1;
                }


                switch (alt24) {
            	case 1 :
            	    // Velvet.g:177:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1139);
            	    attribOperator89=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator89.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1141);
            	    attribNumInstance90=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance90.getTree());

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
    // Velvet.g:180:1: attribOperator : ( PLUS | MINUS );
    public final VelvetParser.attribOperator_return attribOperator() throws RecognitionException {
        VelvetParser.attribOperator_return retval = new VelvetParser.attribOperator_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set91=null;

        Tree set91_tree=null;

        try {
            // Velvet.g:181:2: ( PLUS | MINUS )
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
    // Velvet.g:185:1: attribNumInstance : ( INT | name );
    public final VelvetParser.attribNumInstance_return attribNumInstance() throws RecognitionException {
        VelvetParser.attribNumInstance_return retval = new VelvetParser.attribNumInstance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token INT92=null;
        VelvetParser.name_return name93 =null;


        Tree INT92_tree=null;

        try {
            // Velvet.g:186:2: ( INT | name )
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
                    // Velvet.g:186:4: INT
                    {
                    root_0 = (Tree)adaptor.nil();


                    INT92=(Token)match(input,INT,FOLLOW_INT_in_attribNumInstance1173); 
                    INT92_tree = 
                    (Tree)adaptor.create(INT92)
                    ;
                    adaptor.addChild(root_0, INT92_tree);


                    }
                    break;
                case 2 :
                    // Velvet.g:188:4: name
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_name_in_attribNumInstance1180);
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
    // Velvet.g:191:1: attribute : ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) ;
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
            // Velvet.g:192:2: ( ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) )
            // Velvet.g:192:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI
            {
            // Velvet.g:192:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute )
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
                    // Velvet.g:192:5: intAttribute
                    {
                    pushFollow(FOLLOW_intAttribute_in_attribute1192);
                    intAttribute94=intAttribute();

                    state._fsp--;

                    stream_intAttribute.add(intAttribute94.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:192:20: floatAttribute
                    {
                    pushFollow(FOLLOW_floatAttribute_in_attribute1196);
                    floatAttribute95=floatAttribute();

                    state._fsp--;

                    stream_floatAttribute.add(floatAttribute95.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:192:37: stringAttribute
                    {
                    pushFollow(FOLLOW_stringAttribute_in_attribute1200);
                    stringAttribute96=stringAttribute();

                    state._fsp--;

                    stream_stringAttribute.add(stringAttribute96.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:192:55: boolAttribute
                    {
                    pushFollow(FOLLOW_boolAttribute_in_attribute1204);
                    boolAttribute97=boolAttribute();

                    state._fsp--;

                    stream_boolAttribute.add(boolAttribute97.getTree());

                    }
                    break;

            }


            SEMI98=(Token)match(input,SEMI,FOLLOW_SEMI_in_attribute1207);  
            stream_SEMI.add(SEMI98);


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
            // 193:2: -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
            {
                // Velvet.g:193:5: ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(ATTR, "ATTR")
                , root_1);

                // Velvet.g:193:12: ( intAttribute )?
                if ( stream_intAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_intAttribute.nextTree());

                }
                stream_intAttribute.reset();

                // Velvet.g:193:26: ( floatAttribute )?
                if ( stream_floatAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_floatAttribute.nextTree());

                }
                stream_floatAttribute.reset();

                // Velvet.g:193:42: ( stringAttribute )?
                if ( stream_stringAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_stringAttribute.nextTree());

                }
                stream_stringAttribute.reset();

                // Velvet.g:193:59: ( boolAttribute )?
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
    // Velvet.g:196:1: intAttribute : VAR_INT ! name ( EQ ! INT )? ;
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
            // Velvet.g:196:13: ( VAR_INT ! name ( EQ ! INT )? )
            // Velvet.g:196:16: VAR_INT ! name ( EQ ! INT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_INT99=(Token)match(input,VAR_INT,FOLLOW_VAR_INT_in_intAttribute1236); 

            pushFollow(FOLLOW_name_in_intAttribute1239);
            name100=name();

            state._fsp--;

            adaptor.addChild(root_0, name100.getTree());

            // Velvet.g:196:30: ( EQ ! INT )?
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==EQ) ) {
                alt27=1;
            }
            switch (alt27) {
                case 1 :
                    // Velvet.g:196:31: EQ ! INT
                    {
                    EQ101=(Token)match(input,EQ,FOLLOW_EQ_in_intAttribute1242); 

                    INT102=(Token)match(input,INT,FOLLOW_INT_in_intAttribute1245); 
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
    // Velvet.g:197:1: floatAttribute : VAR_FLOAT ! name ( EQ ! FLOAT )? ;
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
            // Velvet.g:197:15: ( VAR_FLOAT ! name ( EQ ! FLOAT )? )
            // Velvet.g:197:18: VAR_FLOAT ! name ( EQ ! FLOAT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_FLOAT103=(Token)match(input,VAR_FLOAT,FOLLOW_VAR_FLOAT_in_floatAttribute1254); 

            pushFollow(FOLLOW_name_in_floatAttribute1257);
            name104=name();

            state._fsp--;

            adaptor.addChild(root_0, name104.getTree());

            // Velvet.g:197:34: ( EQ ! FLOAT )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==EQ) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // Velvet.g:197:35: EQ ! FLOAT
                    {
                    EQ105=(Token)match(input,EQ,FOLLOW_EQ_in_floatAttribute1260); 

                    FLOAT106=(Token)match(input,FLOAT,FOLLOW_FLOAT_in_floatAttribute1263); 
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
    // Velvet.g:198:1: stringAttribute : VAR_STRING ! name ( EQ ! STRING )? ;
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
            // Velvet.g:198:16: ( VAR_STRING ! name ( EQ ! STRING )? )
            // Velvet.g:198:18: VAR_STRING ! name ( EQ ! STRING )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_STRING107=(Token)match(input,VAR_STRING,FOLLOW_VAR_STRING_in_stringAttribute1271); 

            pushFollow(FOLLOW_name_in_stringAttribute1274);
            name108=name();

            state._fsp--;

            adaptor.addChild(root_0, name108.getTree());

            // Velvet.g:198:35: ( EQ ! STRING )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==EQ) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // Velvet.g:198:36: EQ ! STRING
                    {
                    EQ109=(Token)match(input,EQ,FOLLOW_EQ_in_stringAttribute1277); 

                    STRING110=(Token)match(input,STRING,FOLLOW_STRING_in_stringAttribute1280); 
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
    // Velvet.g:199:1: boolAttribute : VAR_BOOL ! name ( EQ ! BOOLEAN )? ;
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
            // Velvet.g:199:14: ( VAR_BOOL ! name ( EQ ! BOOLEAN )? )
            // Velvet.g:199:17: VAR_BOOL ! name ( EQ ! BOOLEAN )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_BOOL111=(Token)match(input,VAR_BOOL,FOLLOW_VAR_BOOL_in_boolAttribute1289); 

            pushFollow(FOLLOW_name_in_boolAttribute1292);
            name112=name();

            state._fsp--;

            adaptor.addChild(root_0, name112.getTree());

            // Velvet.g:199:32: ( EQ ! BOOLEAN )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==EQ) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // Velvet.g:199:33: EQ ! BOOLEAN
                    {
                    EQ113=(Token)match(input,EQ,FOLLOW_EQ_in_boolAttribute1295); 

                    BOOLEAN114=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_boolAttribute1298); 
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
    // Velvet.g:201:1: unaryOp : OP_NOT ;
    public final VelvetParser.unaryOp_return unaryOp() throws RecognitionException {
        VelvetParser.unaryOp_return retval = new VelvetParser.unaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token OP_NOT115=null;

        Tree OP_NOT115_tree=null;

        try {
            // Velvet.g:202:2: ( OP_NOT )
            // Velvet.g:202:4: OP_NOT
            {
            root_0 = (Tree)adaptor.nil();


            OP_NOT115=(Token)match(input,OP_NOT,FOLLOW_OP_NOT_in_unaryOp1310); 
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
    // Velvet.g:205:1: binaryOp : ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT );
    public final VelvetParser.binaryOp_return binaryOp() throws RecognitionException {
        VelvetParser.binaryOp_return retval = new VelvetParser.binaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set116=null;

        Tree set116_tree=null;

        try {
            // Velvet.g:206:2: ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT )
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
    // Velvet.g:213:1: attribRelation : ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ );
    public final VelvetParser.attribRelation_return attribRelation() throws RecognitionException {
        VelvetParser.attribRelation_return retval = new VelvetParser.attribRelation_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set117=null;

        Tree set117_tree=null;

        try {
            // Velvet.g:214:2: ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ )
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


    protected DFA3 dfa3 = new DFA3(this);
    static final String DFA3_eotS =
        "\22\uffff";
    static final String DFA3_eofS =
        "\1\3\5\uffff\1\12\1\15\10\uffff\1\12\1\15";
    static final String DFA3_minS =
        "\1\43\2\41\1\uffff\2\41\2\21\1\41\2\uffff\1\41\2\uffff\2\41\2\21";
    static final String DFA3_maxS =
        "\1\70\2\41\1\uffff\2\42\2\70\1\41\2\uffff\1\41\2\uffff\2\42\2\70";
    static final String DFA3_acceptS =
        "\3\uffff\1\5\5\uffff\1\1\1\4\1\uffff\1\2\1\3\4\uffff";
    static final String DFA3_specialS =
        "\22\uffff}>";
    static final String[] DFA3_transitionS = {
            "\1\1\1\2\23\uffff\1\3",
            "\1\4",
            "\1\5",
            "",
            "\2\6",
            "\2\7",
            "\1\10\22\uffff\1\11\23\uffff\1\12",
            "\1\13\21\uffff\1\14\24\uffff\1\15",
            "\1\16",
            "",
            "",
            "\1\17",
            "",
            "",
            "\2\20",
            "\2\21",
            "\1\10\22\uffff\1\11\23\uffff\1\12",
            "\1\13\21\uffff\1\14\24\uffff\1\15"
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
            return "85:27: ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )?";
        }
    }
 

    public static final BitSet FOLLOW_concept_in_velvetModel470 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_cinterface_in_velvetModel472 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_velvetModel475 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONCEPT_in_concept488 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_concept490 = new BitSet(new long[]{0x0100001800010002L});
    public static final BitSet FOLLOW_COLON_in_concept497 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_conceptBaseExt_in_concept499 = new BitSet(new long[]{0x0100001800000002L});
    public static final BitSet FOLLOW_instanceImports_in_concept504 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_interfaceImports_in_concept506 = new BitSet(new long[]{0x0100000000000002L});
    public static final BitSet FOLLOW_interfaceImports_in_concept510 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_instanceImports_in_concept512 = new BitSet(new long[]{0x0100000000000002L});
    public static final BitSet FOLLOW_interfaceImports_in_concept516 = new BitSet(new long[]{0x0100000000000002L});
    public static final BitSet FOLLOW_instanceImports_in_concept520 = new BitSet(new long[]{0x0100000000000002L});
    public static final BitSet FOLLOW_definitions_in_concept527 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt560 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_conceptBaseExt563 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt565 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_IMPORTINSTANCE_in_instanceImports590 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_instanceImports592 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_instanceImports594 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_instanceImports597 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_instanceImports599 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_instanceImports601 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_IMPORTINTERFACE_in_interfaceImports630 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_interfaceImports632 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_interfaceImports634 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_interfaceImports637 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_interfaceImports639 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_interfaceImports641 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_CINTERFACE_in_cinterface668 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_cinterface670 = new BitSet(new long[]{0x0100000000010000L});
    public static final BitSet FOLLOW_COLON_in_cinterface674 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_interfaceBaseExt_in_cinterface676 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_definitions_in_cinterface680 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt707 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_interfaceBaseExt710 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt712 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_START_C_in_definitions752 = new BitSet(new long[]{0xA080110020900010L,0x0000000000000007L});
    public static final BitSet FOLLOW_definition_in_definitions754 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_END_C_in_definitions756 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_definition780 = new BitSet(new long[]{0xA080110020100012L,0x0000000000000007L});
    public static final BitSet FOLLOW_featureGroup_in_definition788 = new BitSet(new long[]{0xA000000000100002L,0x0000000000000007L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_definition790 = new BitSet(new long[]{0xA000000000100002L,0x0000000000000007L});
    public static final BitSet FOLLOW_feature_in_definition799 = new BitSet(new long[]{0xA000010020100012L,0x0000000000000007L});
    public static final BitSet FOLLOW_feature_in_definition802 = new BitSet(new long[]{0xA000010020100012L,0x0000000000000007L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_definition806 = new BitSet(new long[]{0xA000010020100012L,0x0000000000000007L});
    public static final BitSet FOLLOW_constraint_in_nonFeatureDefinition828 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_use_in_nonFeatureDefinition833 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribute_in_nonFeatureDefinition838 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_USE_in_use850 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_use852 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_SEMI_in_use854 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANDATORY_in_feature875 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature877 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature881 = new BitSet(new long[]{0x0000010000000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature883 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature887 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature891 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_FEATURE_in_feature898 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_feature900 = new BitSet(new long[]{0x0120000000000000L});
    public static final BitSet FOLLOW_definitions_in_feature903 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SEMI_in_feature907 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_groupType_in_featureGroup938 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_START_C_in_featureGroup940 = new BitSet(new long[]{0x0000010020000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup942 = new BitSet(new long[]{0x0000010020800010L});
    public static final BitSet FOLLOW_END_C_in_featureGroup945 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONSTRAINT_in_constraint986 = new BitSet(new long[]{0x0202004600000000L});
    public static final BitSet FOLLOW_ID_in_constraint990 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_EQ_in_constraint992 = new BitSet(new long[]{0x0202004600000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraint998 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_attributeConstraint_in_constraint1002 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_SEMI_in_constraint1005 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1018 = new BitSet(new long[]{0x000DC00000000002L});
    public static final BitSet FOLLOW_binaryOp_in_constraintDefinition1021 = new BitSet(new long[]{0x0202000600000000L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1023 = new BitSet(new long[]{0x000DC00000000002L});
    public static final BitSet FOLLOW_unaryOp_in_constraintOperand1050 = new BitSet(new long[]{0x0202000600000000L});
    public static final BitSet FOLLOW_START_R_in_constraintOperand1054 = new BitSet(new long[]{0x0202000600000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraintOperand1056 = new BitSet(new long[]{0x0000000001000000L});
    public static final BitSet FOLLOW_END_R_in_constraintOperand1058 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_constraintOperand1062 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribConstraint_in_attributeConstraint1097 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1117 = new BitSet(new long[]{0x0010020000000A80L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1120 = new BitSet(new long[]{0x0000004600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1122 = new BitSet(new long[]{0x0010020000000A80L});
    public static final BitSet FOLLOW_attribRelation_in_attribConstraint1130 = new BitSet(new long[]{0x0000004600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1136 = new BitSet(new long[]{0x0010020000000002L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1139 = new BitSet(new long[]{0x0000004600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1141 = new BitSet(new long[]{0x0010020000000002L});
    public static final BitSet FOLLOW_INT_in_attribNumInstance1173 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_attribNumInstance1180 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_intAttribute_in_attribute1192 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_floatAttribute_in_attribute1196 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_stringAttribute_in_attribute1200 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_boolAttribute_in_attribute1204 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_SEMI_in_attribute1207 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_INT_in_intAttribute1236 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_intAttribute1239 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_intAttribute1242 = new BitSet(new long[]{0x0000004000000000L});
    public static final BitSet FOLLOW_INT_in_intAttribute1245 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_FLOAT_in_floatAttribute1254 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_floatAttribute1257 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_floatAttribute1260 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_FLOAT_in_floatAttribute1263 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_STRING_in_stringAttribute1271 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_stringAttribute1274 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_stringAttribute1277 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_STRING_in_stringAttribute1280 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_BOOL_in_boolAttribute1289 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_boolAttribute1292 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_EQ_in_boolAttribute1295 = new BitSet(new long[]{0x0000000000004000L});
    public static final BitSet FOLLOW_BOOLEAN_in_boolAttribute1298 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_OP_NOT_in_unaryOp1310 = new BitSet(new long[]{0x0000000000000002L});

}