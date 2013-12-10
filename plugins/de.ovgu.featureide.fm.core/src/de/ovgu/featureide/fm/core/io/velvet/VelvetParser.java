// $ANTLR 3.4 Velvet.g 2013-12-10 20:34:38

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
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "ABSTRACT", "ACONSTR", "ATTR", "ATTR_OP_EQUALS", "ATTR_OP_GREATER", "ATTR_OP_GREATER_EQ", "ATTR_OP_LESS", "ATTR_OP_LESS_EQ", "ATTR_OP_NOT_EQUALS", "BASEEXT", "BOOLEAN", "COLON", "COMMA", "CONCEPT", "CONSTR", "CONSTRAINT", "DEF", "END_C", "END_R", "EQ", "ESC_SEQ", "EXPONENT", "FEAT", "FEATURE", "FLOAT", "GROUP", "HEX_DIGIT", "ID", "IDPath", "IMP", "IMPORT", "INSTANCE", "INT", "INTERFACEG", "MANDATORY", "MINUS", "OCTAL_ESC", "ONEOF", "OPERAND", "OP_AND", "OP_EQUIVALENT", "OP_IMPLIES", "OP_NOT", "OP_OR", "OP_XOR", "PLUS", "REFINES", "SEMI", "SOMEOF", "START_C", "START_R", "STRING", "UNARYOP", "UNICODE_ESC", "VAR_BOOL", "VAR_FLOAT", "VAR_INT", "VAR_STRING", "WS"
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
    public static final int INTERFACEG=37;
    public static final int MANDATORY=38;
    public static final int MINUS=39;
    public static final int OCTAL_ESC=40;
    public static final int ONEOF=41;
    public static final int OPERAND=42;
    public static final int OP_AND=43;
    public static final int OP_EQUIVALENT=44;
    public static final int OP_IMPLIES=45;
    public static final int OP_NOT=46;
    public static final int OP_OR=47;
    public static final int OP_XOR=48;
    public static final int PLUS=49;
    public static final int REFINES=50;
    public static final int SEMI=51;
    public static final int SOMEOF=52;
    public static final int START_C=53;
    public static final int START_R=54;
    public static final int STRING=55;
    public static final int UNARYOP=56;
    public static final int UNICODE_ESC=57;
    public static final int VAR_BOOL=58;
    public static final int VAR_FLOAT=59;
    public static final int VAR_INT=60;
    public static final int VAR_STRING=61;
    public static final int WS=62;

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
    // Velvet.g:76:1: velvetModel : ( imports )? ( concept | interfaceg ) EOF ;
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
            // Velvet.g:77:2: ( ( imports )? ( concept | interfaceg ) EOF )
            // Velvet.g:77:4: ( imports )? ( concept | interfaceg ) EOF
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:77:4: ( imports )?
            int alt1=2;
            int LA1_0 = input.LA(1);

            if ( (LA1_0==IMPORT) ) {
                alt1=1;
            }
            switch (alt1) {
                case 1 :
                    // Velvet.g:77:4: imports
                    {
                    pushFollow(FOLLOW_imports_in_velvetModel445);
                    imports1=imports();

                    state._fsp--;

                    adaptor.addChild(root_0, imports1.getTree());

                    }
                    break;

            }


            // Velvet.g:77:13: ( concept | interfaceg )
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
                    // Velvet.g:77:14: concept
                    {
                    pushFollow(FOLLOW_concept_in_velvetModel449);
                    concept2=concept();

                    state._fsp--;

                    adaptor.addChild(root_0, concept2.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:77:22: interfaceg
                    {
                    pushFollow(FOLLOW_interfaceg_in_velvetModel451);
                    interfaceg3=interfaceg();

                    state._fsp--;

                    adaptor.addChild(root_0, interfaceg3.getTree());

                    }
                    break;

            }


            EOF4=(Token)match(input,EOF,FOLLOW_EOF_in_velvetModel454); 
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
    // Velvet.g:80:1: imports : ( IMPORT name SEMI )+ -> ^( IMP ( name )+ ) ;
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
            // Velvet.g:80:9: ( ( IMPORT name SEMI )+ -> ^( IMP ( name )+ ) )
            // Velvet.g:80:11: ( IMPORT name SEMI )+
            {
            // Velvet.g:80:11: ( IMPORT name SEMI )+
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
            	    // Velvet.g:80:12: IMPORT name SEMI
            	    {
            	    IMPORT5=(Token)match(input,IMPORT,FOLLOW_IMPORT_in_imports466);  
            	    stream_IMPORT.add(IMPORT5);


            	    pushFollow(FOLLOW_name_in_imports468);
            	    name6=name();

            	    state._fsp--;

            	    stream_name.add(name6.getTree());

            	    SEMI7=(Token)match(input,SEMI,FOLLOW_SEMI_in_imports470);  
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
            // 81:2: -> ^( IMP ( name )+ )
            {
                // Velvet.g:81:5: ^( IMP ( name )+ )
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
    // Velvet.g:84:1: concept : ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? definitions -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? definitions ) ;
    public final VelvetParser.concept_return concept() throws RecognitionException {
        VelvetParser.concept_return retval = new VelvetParser.concept_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token REFINES8=null;
        Token CONCEPT9=null;
        Token ID10=null;
        Token COLON11=null;
        VelvetParser.conceptBaseExt_return conceptBaseExt12 =null;

        VelvetParser.definitions_return definitions13 =null;


        Tree REFINES8_tree=null;
        Tree CONCEPT9_tree=null;
        Tree ID10_tree=null;
        Tree COLON11_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_REFINES=new RewriteRuleTokenStream(adaptor,"token REFINES");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_CONCEPT=new RewriteRuleTokenStream(adaptor,"token CONCEPT");
        RewriteRuleSubtreeStream stream_conceptBaseExt=new RewriteRuleSubtreeStream(adaptor,"rule conceptBaseExt");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:84:9: ( ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? definitions -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? definitions ) )
            // Velvet.g:84:11: ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? definitions
            {
            // Velvet.g:84:11: ( REFINES )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0==REFINES) ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // Velvet.g:84:11: REFINES
                    {
                    REFINES8=(Token)match(input,REFINES,FOLLOW_REFINES_in_concept493);  
                    stream_REFINES.add(REFINES8);


                    }
                    break;

            }


            CONCEPT9=(Token)match(input,CONCEPT,FOLLOW_CONCEPT_in_concept496);  
            stream_CONCEPT.add(CONCEPT9);


            ID10=(Token)match(input,ID,FOLLOW_ID_in_concept498);  
            stream_ID.add(ID10);


            // Velvet.g:84:32: ( COLON conceptBaseExt )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==COLON) ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // Velvet.g:84:33: COLON conceptBaseExt
                    {
                    COLON11=(Token)match(input,COLON,FOLLOW_COLON_in_concept502);  
                    stream_COLON.add(COLON11);


                    pushFollow(FOLLOW_conceptBaseExt_in_concept504);
                    conceptBaseExt12=conceptBaseExt();

                    state._fsp--;

                    stream_conceptBaseExt.add(conceptBaseExt12.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_concept508);
            definitions13=definitions();

            state._fsp--;

            stream_definitions.add(definitions13.getTree());

            // AST REWRITE
            // elements: REFINES, ID, definitions, conceptBaseExt, CONCEPT
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 85:2: -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? definitions )
            {
                // Velvet.g:85:5: ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CONCEPT.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:85:18: ( REFINES )?
                if ( stream_REFINES.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_REFINES.nextNode()
                    );

                }
                stream_REFINES.reset();

                // Velvet.g:85:27: ( conceptBaseExt )?
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
    // Velvet.g:88:1: conceptBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
    public final VelvetParser.conceptBaseExt_return conceptBaseExt() throws RecognitionException {
        VelvetParser.conceptBaseExt_return retval = new VelvetParser.conceptBaseExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID14=null;
        Token COMMA15=null;
        Token ID16=null;

        Tree ID14_tree=null;
        Tree COMMA15_tree=null;
        Tree ID16_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

        try {
            // Velvet.g:89:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:89:4: ID ( COMMA ID )*
            {
            ID14=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt538);  
            stream_ID.add(ID14);


            // Velvet.g:89:7: ( COMMA ID )*
            loop6:
            do {
                int alt6=2;
                int LA6_0 = input.LA(1);

                if ( (LA6_0==COMMA) ) {
                    alt6=1;
                }


                switch (alt6) {
            	case 1 :
            	    // Velvet.g:89:8: COMMA ID
            	    {
            	    COMMA15=(Token)match(input,COMMA,FOLLOW_COMMA_in_conceptBaseExt541);  
            	    stream_COMMA.add(COMMA15);


            	    ID16=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt543);  
            	    stream_ID.add(ID16);


            	    }
            	    break;

            	default :
            	    break loop6;
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
            // 90:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:90:5: ^( BASEEXT ( ID )+ )
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


    public static class interfaceg_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "interfaceg"
    // Velvet.g:93:1: interfaceg : ( REFINES )? INTERFACEG ID ( COLON interfaceBaseExt )? definitions -> ^( INTERFACEG ID ( REFINES )? ( interfaceBaseExt )? definitions ) ;
    public final VelvetParser.interfaceg_return interfaceg() throws RecognitionException {
        VelvetParser.interfaceg_return retval = new VelvetParser.interfaceg_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token REFINES17=null;
        Token INTERFACEG18=null;
        Token ID19=null;
        Token COLON20=null;
        VelvetParser.interfaceBaseExt_return interfaceBaseExt21 =null;

        VelvetParser.definitions_return definitions22 =null;


        Tree REFINES17_tree=null;
        Tree INTERFACEG18_tree=null;
        Tree ID19_tree=null;
        Tree COLON20_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_INTERFACEG=new RewriteRuleTokenStream(adaptor,"token INTERFACEG");
        RewriteRuleTokenStream stream_REFINES=new RewriteRuleTokenStream(adaptor,"token REFINES");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        RewriteRuleSubtreeStream stream_interfaceBaseExt=new RewriteRuleSubtreeStream(adaptor,"rule interfaceBaseExt");
        try {
            // Velvet.g:93:12: ( ( REFINES )? INTERFACEG ID ( COLON interfaceBaseExt )? definitions -> ^( INTERFACEG ID ( REFINES )? ( interfaceBaseExt )? definitions ) )
            // Velvet.g:93:14: ( REFINES )? INTERFACEG ID ( COLON interfaceBaseExt )? definitions
            {
            // Velvet.g:93:14: ( REFINES )?
            int alt7=2;
            int LA7_0 = input.LA(1);

            if ( (LA7_0==REFINES) ) {
                alt7=1;
            }
            switch (alt7) {
                case 1 :
                    // Velvet.g:93:14: REFINES
                    {
                    REFINES17=(Token)match(input,REFINES,FOLLOW_REFINES_in_interfaceg567);  
                    stream_REFINES.add(REFINES17);


                    }
                    break;

            }


            INTERFACEG18=(Token)match(input,INTERFACEG,FOLLOW_INTERFACEG_in_interfaceg570);  
            stream_INTERFACEG.add(INTERFACEG18);


            ID19=(Token)match(input,ID,FOLLOW_ID_in_interfaceg572);  
            stream_ID.add(ID19);


            // Velvet.g:93:38: ( COLON interfaceBaseExt )?
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==COLON) ) {
                alt8=1;
            }
            switch (alt8) {
                case 1 :
                    // Velvet.g:93:39: COLON interfaceBaseExt
                    {
                    COLON20=(Token)match(input,COLON,FOLLOW_COLON_in_interfaceg576);  
                    stream_COLON.add(COLON20);


                    pushFollow(FOLLOW_interfaceBaseExt_in_interfaceg578);
                    interfaceBaseExt21=interfaceBaseExt();

                    state._fsp--;

                    stream_interfaceBaseExt.add(interfaceBaseExt21.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_interfaceg582);
            definitions22=definitions();

            state._fsp--;

            stream_definitions.add(definitions22.getTree());

            // AST REWRITE
            // elements: INTERFACEG, REFINES, definitions, ID, interfaceBaseExt
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 94:2: -> ^( INTERFACEG ID ( REFINES )? ( interfaceBaseExt )? definitions )
            {
                // Velvet.g:94:5: ^( INTERFACEG ID ( REFINES )? ( interfaceBaseExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_INTERFACEG.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:94:21: ( REFINES )?
                if ( stream_REFINES.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_REFINES.nextNode()
                    );

                }
                stream_REFINES.reset();

                // Velvet.g:94:30: ( interfaceBaseExt )?
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
    // Velvet.g:97:1: interfaceBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
    public final VelvetParser.interfaceBaseExt_return interfaceBaseExt() throws RecognitionException {
        VelvetParser.interfaceBaseExt_return retval = new VelvetParser.interfaceBaseExt_return();
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
            // Velvet.g:98:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:98:4: ID ( COMMA ID )*
            {
            ID23=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt612);  
            stream_ID.add(ID23);


            // Velvet.g:98:7: ( COMMA ID )*
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( (LA9_0==COMMA) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // Velvet.g:98:8: COMMA ID
            	    {
            	    COMMA24=(Token)match(input,COMMA,FOLLOW_COMMA_in_interfaceBaseExt615);  
            	    stream_COMMA.add(COMMA24);


            	    ID25=(Token)match(input,ID,FOLLOW_ID_in_interfaceBaseExt617);  
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
            // 99:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:99:5: ^( BASEEXT ( ID )+ )
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
    // Velvet.g:102:1: name : ( ID | IDPath );
    public final VelvetParser.name_return name() throws RecognitionException {
        VelvetParser.name_return retval = new VelvetParser.name_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set26=null;

        Tree set26_tree=null;

        try {
            // Velvet.g:102:5: ( ID | IDPath )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set26=(Token)input.LT(1);

            if ( (input.LA(1) >= ID && input.LA(1) <= IDPath) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set26)
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
    // Velvet.g:106:1: definitions : START_C def END_C -> ^( DEF def ) ;
    public final VelvetParser.definitions_return definitions() throws RecognitionException {
        VelvetParser.definitions_return retval = new VelvetParser.definitions_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C27=null;
        Token END_C29=null;
        VelvetParser.def_return def28 =null;


        Tree START_C27_tree=null;
        Tree END_C29_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_def=new RewriteRuleSubtreeStream(adaptor,"rule def");
        try {
            // Velvet.g:107:2: ( START_C def END_C -> ^( DEF def ) )
            // Velvet.g:107:4: START_C def END_C
            {
            START_C27=(Token)match(input,START_C,FOLLOW_START_C_in_definitions657);  
            stream_START_C.add(START_C27);


            pushFollow(FOLLOW_def_in_definitions659);
            def28=def();

            state._fsp--;

            stream_def.add(def28.getTree());

            END_C29=(Token)match(input,END_C,FOLLOW_END_C_in_definitions661);  
            stream_END_C.add(END_C29);


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
            // 108:2: -> ^( DEF def )
            {
                // Velvet.g:108:5: ^( DEF def )
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
    // Velvet.g:111:1: def : ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? ;
    public final VelvetParser.def_return def() throws RecognitionException {
        VelvetParser.def_return retval = new VelvetParser.def_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition30 =null;

        VelvetParser.featureGroup_return featureGroup31 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition32 =null;

        VelvetParser.feature_return feature33 =null;

        VelvetParser.feature_return feature34 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition35 =null;



        try {
            // Velvet.g:111:5: ( ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? )
            // Velvet.g:111:7: ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:111:7: ( nonFeatureDefinition )*
            loop10:
            do {
                int alt10=2;
                int LA10_0 = input.LA(1);

                if ( (LA10_0==CONSTRAINT||LA10_0==ID||(LA10_0 >= VAR_BOOL && LA10_0 <= VAR_STRING)) ) {
                    alt10=1;
                }


                switch (alt10) {
            	case 1 :
            	    // Velvet.g:111:7: nonFeatureDefinition
            	    {
            	    pushFollow(FOLLOW_nonFeatureDefinition_in_def680);
            	    nonFeatureDefinition30=nonFeatureDefinition();

            	    state._fsp--;

            	    adaptor.addChild(root_0, nonFeatureDefinition30.getTree());

            	    }
            	    break;

            	default :
            	    break loop10;
                }
            } while (true);


            // Velvet.g:111:29: ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
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
                    // Velvet.g:112:3: ( featureGroup ( nonFeatureDefinition )* )
                    {
                    // Velvet.g:112:3: ( featureGroup ( nonFeatureDefinition )* )
                    // Velvet.g:112:4: featureGroup ( nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_featureGroup_in_def688);
                    featureGroup31=featureGroup();

                    state._fsp--;

                    adaptor.addChild(root_0, featureGroup31.getTree());

                    // Velvet.g:112:17: ( nonFeatureDefinition )*
                    loop11:
                    do {
                        int alt11=2;
                        int LA11_0 = input.LA(1);

                        if ( (LA11_0==CONSTRAINT||LA11_0==ID||(LA11_0 >= VAR_BOOL && LA11_0 <= VAR_STRING)) ) {
                            alt11=1;
                        }


                        switch (alt11) {
                    	case 1 :
                    	    // Velvet.g:112:17: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def690);
                    	    nonFeatureDefinition32=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition32.getTree());

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
                    // Velvet.g:113:3: ( feature ( feature | nonFeatureDefinition )* )
                    {
                    // Velvet.g:113:3: ( feature ( feature | nonFeatureDefinition )* )
                    // Velvet.g:113:4: feature ( feature | nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_feature_in_def699);
                    feature33=feature();

                    state._fsp--;

                    adaptor.addChild(root_0, feature33.getTree());

                    // Velvet.g:113:12: ( feature | nonFeatureDefinition )*
                    loop12:
                    do {
                        int alt12=3;
                        int LA12_0 = input.LA(1);

                        if ( (LA12_0==ABSTRACT||LA12_0==FEATURE||LA12_0==MANDATORY) ) {
                            alt12=1;
                        }
                        else if ( (LA12_0==CONSTRAINT||LA12_0==ID||(LA12_0 >= VAR_BOOL && LA12_0 <= VAR_STRING)) ) {
                            alt12=2;
                        }


                        switch (alt12) {
                    	case 1 :
                    	    // Velvet.g:113:13: feature
                    	    {
                    	    pushFollow(FOLLOW_feature_in_def702);
                    	    feature34=feature();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, feature34.getTree());

                    	    }
                    	    break;
                    	case 2 :
                    	    // Velvet.g:113:23: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def706);
                    	    nonFeatureDefinition35=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition35.getTree());

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
    // Velvet.g:116:1: nonFeatureDefinition : ( constraint | instance | attribute );
    public final VelvetParser.nonFeatureDefinition_return nonFeatureDefinition() throws RecognitionException {
        VelvetParser.nonFeatureDefinition_return retval = new VelvetParser.nonFeatureDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraint_return constraint36 =null;

        VelvetParser.instance_return instance37 =null;

        VelvetParser.attribute_return attribute38 =null;



        try {
            // Velvet.g:117:2: ( constraint | instance | attribute )
            int alt14=3;
            switch ( input.LA(1) ) {
            case CONSTRAINT:
                {
                alt14=1;
                }
                break;
            case ID:
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
                    // Velvet.g:117:4: constraint
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_constraint_in_nonFeatureDefinition726);
                    constraint36=constraint();

                    state._fsp--;

                    adaptor.addChild(root_0, constraint36.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:118:4: instance
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_instance_in_nonFeatureDefinition732);
                    instance37=instance();

                    state._fsp--;

                    adaptor.addChild(root_0, instance37.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:119:4: attribute
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_attribute_in_nonFeatureDefinition738);
                    attribute38=attribute();

                    state._fsp--;

                    adaptor.addChild(root_0, attribute38.getTree());

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
    // Velvet.g:122:1: instance : ID name SEMI -> INSTANCE ID name ;
    public final VelvetParser.instance_return instance() throws RecognitionException {
        VelvetParser.instance_return retval = new VelvetParser.instance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID39=null;
        Token SEMI41=null;
        VelvetParser.name_return name40 =null;


        Tree ID39_tree=null;
        Tree SEMI41_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:122:9: ( ID name SEMI -> INSTANCE ID name )
            // Velvet.g:122:11: ID name SEMI
            {
            ID39=(Token)match(input,ID,FOLLOW_ID_in_instance749);  
            stream_ID.add(ID39);


            pushFollow(FOLLOW_name_in_instance751);
            name40=name();

            state._fsp--;

            stream_name.add(name40.getTree());

            SEMI41=(Token)match(input,SEMI,FOLLOW_SEMI_in_instance753);  
            stream_SEMI.add(SEMI41);


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
            // 123:2: -> INSTANCE ID name
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
    // Velvet.g:126:1: feature : ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) ;
    public final VelvetParser.feature_return feature() throws RecognitionException {
        VelvetParser.feature_return retval = new VelvetParser.feature_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token MANDATORY42=null;
        Token ABSTRACT43=null;
        Token ABSTRACT44=null;
        Token MANDATORY45=null;
        Token MANDATORY46=null;
        Token ABSTRACT47=null;
        Token FEATURE48=null;
        Token SEMI51=null;
        VelvetParser.name_return name49 =null;

        VelvetParser.definitions_return definitions50 =null;


        Tree MANDATORY42_tree=null;
        Tree ABSTRACT43_tree=null;
        Tree ABSTRACT44_tree=null;
        Tree MANDATORY45_tree=null;
        Tree MANDATORY46_tree=null;
        Tree ABSTRACT47_tree=null;
        Tree FEATURE48_tree=null;
        Tree SEMI51_tree=null;
        RewriteRuleTokenStream stream_ABSTRACT=new RewriteRuleTokenStream(adaptor,"token ABSTRACT");
        RewriteRuleTokenStream stream_MANDATORY=new RewriteRuleTokenStream(adaptor,"token MANDATORY");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleTokenStream stream_FEATURE=new RewriteRuleTokenStream(adaptor,"token FEATURE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:127:2: ( ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) )
            // Velvet.g:127:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI )
            {
            // Velvet.g:127:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )?
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
                    // Velvet.g:127:5: MANDATORY ABSTRACT
                    {
                    MANDATORY42=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature775);  
                    stream_MANDATORY.add(MANDATORY42);


                    ABSTRACT43=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature777);  
                    stream_ABSTRACT.add(ABSTRACT43);


                    }
                    break;
                case 2 :
                    // Velvet.g:127:26: ABSTRACT MANDATORY
                    {
                    ABSTRACT44=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature781);  
                    stream_ABSTRACT.add(ABSTRACT44);


                    MANDATORY45=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature783);  
                    stream_MANDATORY.add(MANDATORY45);


                    }
                    break;
                case 3 :
                    // Velvet.g:127:47: MANDATORY
                    {
                    MANDATORY46=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature787);  
                    stream_MANDATORY.add(MANDATORY46);


                    }
                    break;
                case 4 :
                    // Velvet.g:127:59: ABSTRACT
                    {
                    ABSTRACT47=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature791);  
                    stream_ABSTRACT.add(ABSTRACT47);


                    }
                    break;

            }


            FEATURE48=(Token)match(input,FEATURE,FOLLOW_FEATURE_in_feature798);  
            stream_FEATURE.add(FEATURE48);


            pushFollow(FOLLOW_name_in_feature800);
            name49=name();

            state._fsp--;

            stream_name.add(name49.getTree());

            // Velvet.g:128:17: ( definitions | SEMI )
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
                    // Velvet.g:128:18: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_feature803);
                    definitions50=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions50.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:128:32: SEMI
                    {
                    SEMI51=(Token)match(input,SEMI,FOLLOW_SEMI_in_feature807);  
                    stream_SEMI.add(SEMI51);


                    }
                    break;

            }


            // AST REWRITE
            // elements: definitions, ABSTRACT, name, MANDATORY
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 129:2: -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
            {
                // Velvet.g:129:5: ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(FEAT, "FEAT")
                , root_1);

                adaptor.addChild(root_1, stream_name.nextTree());

                // Velvet.g:129:17: ( MANDATORY )?
                if ( stream_MANDATORY.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_MANDATORY.nextNode()
                    );

                }
                stream_MANDATORY.reset();

                // Velvet.g:129:28: ( ABSTRACT )?
                if ( stream_ABSTRACT.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ABSTRACT.nextNode()
                    );

                }
                stream_ABSTRACT.reset();

                // Velvet.g:129:38: ( definitions )?
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
    // Velvet.g:132:1: featureGroup : groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) ;
    public final VelvetParser.featureGroup_return featureGroup() throws RecognitionException {
        VelvetParser.featureGroup_return retval = new VelvetParser.featureGroup_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C53=null;
        Token END_C56=null;
        VelvetParser.groupType_return groupType52 =null;

        VelvetParser.feature_return feature54 =null;

        VelvetParser.feature_return feature55 =null;


        Tree START_C53_tree=null;
        Tree END_C56_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_groupType=new RewriteRuleSubtreeStream(adaptor,"rule groupType");
        RewriteRuleSubtreeStream stream_feature=new RewriteRuleSubtreeStream(adaptor,"rule feature");
        try {
            // Velvet.g:133:2: ( groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) )
            // Velvet.g:133:4: groupType START_C feature ( feature )+ END_C
            {
            pushFollow(FOLLOW_groupType_in_featureGroup838);
            groupType52=groupType();

            state._fsp--;

            stream_groupType.add(groupType52.getTree());

            START_C53=(Token)match(input,START_C,FOLLOW_START_C_in_featureGroup840);  
            stream_START_C.add(START_C53);


            pushFollow(FOLLOW_feature_in_featureGroup842);
            feature54=feature();

            state._fsp--;

            stream_feature.add(feature54.getTree());

            // Velvet.g:133:30: ( feature )+
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
            	    // Velvet.g:133:30: feature
            	    {
            	    pushFollow(FOLLOW_feature_in_featureGroup844);
            	    feature55=feature();

            	    state._fsp--;

            	    stream_feature.add(feature55.getTree());

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


            END_C56=(Token)match(input,END_C,FOLLOW_END_C_in_featureGroup847);  
            stream_END_C.add(END_C56);


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
            // 134:2: -> ^( GROUP groupType feature ( feature )+ )
            {
                // Velvet.g:134:5: ^( GROUP groupType feature ( feature )+ )
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
    // Velvet.g:137:1: groupType : ( SOMEOF | ONEOF );
    public final VelvetParser.groupType_return groupType() throws RecognitionException {
        VelvetParser.groupType_return retval = new VelvetParser.groupType_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set57=null;

        Tree set57_tree=null;

        try {
            // Velvet.g:138:2: ( SOMEOF | ONEOF )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set57=(Token)input.LT(1);

            if ( input.LA(1)==ONEOF||input.LA(1)==SOMEOF ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set57)
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
    // Velvet.g:142:1: constraint : CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !;
    public final VelvetParser.constraint_return constraint() throws RecognitionException {
        VelvetParser.constraint_return retval = new VelvetParser.constraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token CONSTRAINT58=null;
        Token ID59=null;
        Token EQ60=null;
        Token SEMI63=null;
        VelvetParser.constraintDefinition_return constraintDefinition61 =null;

        VelvetParser.attributeConstraint_return attributeConstraint62 =null;


        Tree CONSTRAINT58_tree=null;
        Tree ID59_tree=null;
        Tree EQ60_tree=null;
        Tree SEMI63_tree=null;

        try {
            // Velvet.g:143:2: ( CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !)
            // Velvet.g:143:4: CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !
            {
            root_0 = (Tree)adaptor.nil();


            CONSTRAINT58=(Token)match(input,CONSTRAINT,FOLLOW_CONSTRAINT_in_constraint890); 
            CONSTRAINT58_tree = 
            (Tree)adaptor.create(CONSTRAINT58)
            ;
            root_0 = (Tree)adaptor.becomeRoot(CONSTRAINT58_tree, root_0);


            // Velvet.g:143:16: ( ID EQ !)?
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
                    // Velvet.g:143:17: ID EQ !
                    {
                    ID59=(Token)match(input,ID,FOLLOW_ID_in_constraint894); 
                    ID59_tree = 
                    (Tree)adaptor.create(ID59)
                    ;
                    adaptor.addChild(root_0, ID59_tree);


                    EQ60=(Token)match(input,EQ,FOLLOW_EQ_in_constraint896); 

                    }
                    break;

            }


            // Velvet.g:143:26: ( constraintDefinition | attributeConstraint )
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
                    // Velvet.g:143:27: constraintDefinition
                    {
                    pushFollow(FOLLOW_constraintDefinition_in_constraint902);
                    constraintDefinition61=constraintDefinition();

                    state._fsp--;

                    adaptor.addChild(root_0, constraintDefinition61.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:143:50: attributeConstraint
                    {
                    pushFollow(FOLLOW_attributeConstraint_in_constraint906);
                    attributeConstraint62=attributeConstraint();

                    state._fsp--;

                    adaptor.addChild(root_0, attributeConstraint62.getTree());

                    }
                    break;

            }


            SEMI63=(Token)match(input,SEMI,FOLLOW_SEMI_in_constraint909); 

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
    // Velvet.g:146:1: constraintDefinition : constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) ;
    public final VelvetParser.constraintDefinition_return constraintDefinition() throws RecognitionException {
        VelvetParser.constraintDefinition_return retval = new VelvetParser.constraintDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraintOperand_return constraintOperand64 =null;

        VelvetParser.binaryOp_return binaryOp65 =null;

        VelvetParser.constraintOperand_return constraintOperand66 =null;


        RewriteRuleSubtreeStream stream_constraintOperand=new RewriteRuleSubtreeStream(adaptor,"rule constraintOperand");
        RewriteRuleSubtreeStream stream_binaryOp=new RewriteRuleSubtreeStream(adaptor,"rule binaryOp");
        try {
            // Velvet.g:147:2: ( constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) )
            // Velvet.g:147:4: constraintOperand ( binaryOp constraintOperand )*
            {
            pushFollow(FOLLOW_constraintOperand_in_constraintDefinition922);
            constraintOperand64=constraintOperand();

            state._fsp--;

            stream_constraintOperand.add(constraintOperand64.getTree());

            // Velvet.g:147:22: ( binaryOp constraintOperand )*
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( ((LA20_0 >= OP_AND && LA20_0 <= OP_IMPLIES)||(LA20_0 >= OP_OR && LA20_0 <= OP_XOR)) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // Velvet.g:147:23: binaryOp constraintOperand
            	    {
            	    pushFollow(FOLLOW_binaryOp_in_constraintDefinition925);
            	    binaryOp65=binaryOp();

            	    state._fsp--;

            	    stream_binaryOp.add(binaryOp65.getTree());

            	    pushFollow(FOLLOW_constraintOperand_in_constraintDefinition927);
            	    constraintOperand66=constraintOperand();

            	    state._fsp--;

            	    stream_constraintOperand.add(constraintOperand66.getTree());

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
            // 148:2: -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
            {
                // Velvet.g:148:5: ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
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

                // Velvet.g:148:33: ( binaryOp )*
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
    // Velvet.g:151:1: constraintOperand : ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? ;
    public final VelvetParser.constraintOperand_return constraintOperand() throws RecognitionException {
        VelvetParser.constraintOperand_return retval = new VelvetParser.constraintOperand_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_R68=null;
        Token END_R70=null;
        VelvetParser.unaryOp_return unaryOp67 =null;

        VelvetParser.constraintDefinition_return constraintDefinition69 =null;

        VelvetParser.name_return name71 =null;


        Tree START_R68_tree=null;
        Tree END_R70_tree=null;
        RewriteRuleTokenStream stream_END_R=new RewriteRuleTokenStream(adaptor,"token END_R");
        RewriteRuleTokenStream stream_START_R=new RewriteRuleTokenStream(adaptor,"token START_R");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_unaryOp=new RewriteRuleSubtreeStream(adaptor,"rule unaryOp");
        RewriteRuleSubtreeStream stream_constraintDefinition=new RewriteRuleSubtreeStream(adaptor,"rule constraintDefinition");
        try {
            // Velvet.g:151:19: ( ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? )
            // Velvet.g:151:21: ( unaryOp )* ( START_R constraintDefinition END_R | name )
            {
            // Velvet.g:151:21: ( unaryOp )*
            loop21:
            do {
                int alt21=2;
                int LA21_0 = input.LA(1);

                if ( (LA21_0==OP_NOT) ) {
                    alt21=1;
                }


                switch (alt21) {
            	case 1 :
            	    // Velvet.g:151:21: unaryOp
            	    {
            	    pushFollow(FOLLOW_unaryOp_in_constraintOperand954);
            	    unaryOp67=unaryOp();

            	    state._fsp--;

            	    stream_unaryOp.add(unaryOp67.getTree());

            	    }
            	    break;

            	default :
            	    break loop21;
                }
            } while (true);


            // Velvet.g:151:30: ( START_R constraintDefinition END_R | name )
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
                    // Velvet.g:151:31: START_R constraintDefinition END_R
                    {
                    START_R68=(Token)match(input,START_R,FOLLOW_START_R_in_constraintOperand958);  
                    stream_START_R.add(START_R68);


                    pushFollow(FOLLOW_constraintDefinition_in_constraintOperand960);
                    constraintDefinition69=constraintDefinition();

                    state._fsp--;

                    stream_constraintDefinition.add(constraintDefinition69.getTree());

                    END_R70=(Token)match(input,END_R,FOLLOW_END_R_in_constraintOperand962);  
                    stream_END_R.add(END_R70);


                    }
                    break;
                case 2 :
                    // Velvet.g:151:68: name
                    {
                    pushFollow(FOLLOW_name_in_constraintOperand966);
                    name71=name();

                    state._fsp--;

                    stream_name.add(name71.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: constraintDefinition, unaryOp, name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 152:2: -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )?
            {
                // Velvet.g:152:5: ( constraintDefinition )?
                if ( stream_constraintDefinition.hasNext() ) {
                    adaptor.addChild(root_0, stream_constraintDefinition.nextTree());

                }
                stream_constraintDefinition.reset();

                // Velvet.g:152:27: ( ^( UNARYOP unaryOp ) )*
                while ( stream_unaryOp.hasNext() ) {
                    // Velvet.g:152:27: ^( UNARYOP unaryOp )
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

                // Velvet.g:152:47: ( ^( OPERAND name ) )?
                if ( stream_name.hasNext() ) {
                    // Velvet.g:152:47: ^( OPERAND name )
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
    // Velvet.g:155:1: attributeConstraint : attribConstraint -> ^( ACONSTR attribConstraint ) ;
    public final VelvetParser.attributeConstraint_return attributeConstraint() throws RecognitionException {
        VelvetParser.attributeConstraint_return retval = new VelvetParser.attributeConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribConstraint_return attribConstraint72 =null;


        RewriteRuleSubtreeStream stream_attribConstraint=new RewriteRuleSubtreeStream(adaptor,"rule attribConstraint");
        try {
            // Velvet.g:156:2: ( attribConstraint -> ^( ACONSTR attribConstraint ) )
            // Velvet.g:156:4: attribConstraint
            {
            pushFollow(FOLLOW_attribConstraint_in_attributeConstraint1001);
            attribConstraint72=attribConstraint();

            state._fsp--;

            stream_attribConstraint.add(attribConstraint72.getTree());

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
            // 157:2: -> ^( ACONSTR attribConstraint )
            {
                // Velvet.g:157:5: ^( ACONSTR attribConstraint )
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
    // Velvet.g:160:1: attribConstraint : attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* ;
    public final VelvetParser.attribConstraint_return attribConstraint() throws RecognitionException {
        VelvetParser.attribConstraint_return retval = new VelvetParser.attribConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribNumInstance_return attribNumInstance73 =null;

        VelvetParser.attribOperator_return attribOperator74 =null;

        VelvetParser.attribNumInstance_return attribNumInstance75 =null;

        VelvetParser.attribRelation_return attribRelation76 =null;

        VelvetParser.attribNumInstance_return attribNumInstance77 =null;

        VelvetParser.attribOperator_return attribOperator78 =null;

        VelvetParser.attribNumInstance_return attribNumInstance79 =null;



        try {
            // Velvet.g:161:2: ( attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* )
            // Velvet.g:161:4: attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )*
            {
            root_0 = (Tree)adaptor.nil();


            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1021);
            attribNumInstance73=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance73.getTree());

            // Velvet.g:161:22: ( attribOperator attribNumInstance )*
            loop23:
            do {
                int alt23=2;
                int LA23_0 = input.LA(1);

                if ( (LA23_0==MINUS||LA23_0==PLUS) ) {
                    alt23=1;
                }


                switch (alt23) {
            	case 1 :
            	    // Velvet.g:161:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1024);
            	    attribOperator74=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator74.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1026);
            	    attribNumInstance75=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance75.getTree());

            	    }
            	    break;

            	default :
            	    break loop23;
                }
            } while (true);


            pushFollow(FOLLOW_attribRelation_in_attribConstraint1034);
            attribRelation76=attribRelation();

            state._fsp--;

            adaptor.addChild(root_0, attribRelation76.getTree());

            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1040);
            attribNumInstance77=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance77.getTree());

            // Velvet.g:163:22: ( attribOperator attribNumInstance )*
            loop24:
            do {
                int alt24=2;
                int LA24_0 = input.LA(1);

                if ( (LA24_0==MINUS||LA24_0==PLUS) ) {
                    alt24=1;
                }


                switch (alt24) {
            	case 1 :
            	    // Velvet.g:163:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1043);
            	    attribOperator78=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator78.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1045);
            	    attribNumInstance79=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance79.getTree());

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
    // Velvet.g:166:1: attribOperator : ( PLUS | MINUS );
    public final VelvetParser.attribOperator_return attribOperator() throws RecognitionException {
        VelvetParser.attribOperator_return retval = new VelvetParser.attribOperator_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set80=null;

        Tree set80_tree=null;

        try {
            // Velvet.g:167:2: ( PLUS | MINUS )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set80=(Token)input.LT(1);

            if ( input.LA(1)==MINUS||input.LA(1)==PLUS ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set80)
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
    // Velvet.g:171:1: attribNumInstance : ( INT | name );
    public final VelvetParser.attribNumInstance_return attribNumInstance() throws RecognitionException {
        VelvetParser.attribNumInstance_return retval = new VelvetParser.attribNumInstance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token INT81=null;
        VelvetParser.name_return name82 =null;


        Tree INT81_tree=null;

        try {
            // Velvet.g:172:2: ( INT | name )
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
                    // Velvet.g:172:4: INT
                    {
                    root_0 = (Tree)adaptor.nil();


                    INT81=(Token)match(input,INT,FOLLOW_INT_in_attribNumInstance1077); 
                    INT81_tree = 
                    (Tree)adaptor.create(INT81)
                    ;
                    adaptor.addChild(root_0, INT81_tree);


                    }
                    break;
                case 2 :
                    // Velvet.g:174:4: name
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_name_in_attribNumInstance1084);
                    name82=name();

                    state._fsp--;

                    adaptor.addChild(root_0, name82.getTree());

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
    // Velvet.g:177:1: attribute : ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) ;
    public final VelvetParser.attribute_return attribute() throws RecognitionException {
        VelvetParser.attribute_return retval = new VelvetParser.attribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token SEMI87=null;
        VelvetParser.intAttribute_return intAttribute83 =null;

        VelvetParser.floatAttribute_return floatAttribute84 =null;

        VelvetParser.stringAttribute_return stringAttribute85 =null;

        VelvetParser.boolAttribute_return boolAttribute86 =null;


        Tree SEMI87_tree=null;
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_intAttribute=new RewriteRuleSubtreeStream(adaptor,"rule intAttribute");
        RewriteRuleSubtreeStream stream_stringAttribute=new RewriteRuleSubtreeStream(adaptor,"rule stringAttribute");
        RewriteRuleSubtreeStream stream_floatAttribute=new RewriteRuleSubtreeStream(adaptor,"rule floatAttribute");
        RewriteRuleSubtreeStream stream_boolAttribute=new RewriteRuleSubtreeStream(adaptor,"rule boolAttribute");
        try {
            // Velvet.g:178:2: ( ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) )
            // Velvet.g:178:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI
            {
            // Velvet.g:178:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute )
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
                    // Velvet.g:178:5: intAttribute
                    {
                    pushFollow(FOLLOW_intAttribute_in_attribute1096);
                    intAttribute83=intAttribute();

                    state._fsp--;

                    stream_intAttribute.add(intAttribute83.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:178:20: floatAttribute
                    {
                    pushFollow(FOLLOW_floatAttribute_in_attribute1100);
                    floatAttribute84=floatAttribute();

                    state._fsp--;

                    stream_floatAttribute.add(floatAttribute84.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:178:37: stringAttribute
                    {
                    pushFollow(FOLLOW_stringAttribute_in_attribute1104);
                    stringAttribute85=stringAttribute();

                    state._fsp--;

                    stream_stringAttribute.add(stringAttribute85.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:178:55: boolAttribute
                    {
                    pushFollow(FOLLOW_boolAttribute_in_attribute1108);
                    boolAttribute86=boolAttribute();

                    state._fsp--;

                    stream_boolAttribute.add(boolAttribute86.getTree());

                    }
                    break;

            }


            SEMI87=(Token)match(input,SEMI,FOLLOW_SEMI_in_attribute1111);  
            stream_SEMI.add(SEMI87);


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
            // 179:2: -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
            {
                // Velvet.g:179:5: ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(ATTR, "ATTR")
                , root_1);

                // Velvet.g:179:12: ( intAttribute )?
                if ( stream_intAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_intAttribute.nextTree());

                }
                stream_intAttribute.reset();

                // Velvet.g:179:26: ( floatAttribute )?
                if ( stream_floatAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_floatAttribute.nextTree());

                }
                stream_floatAttribute.reset();

                // Velvet.g:179:42: ( stringAttribute )?
                if ( stream_stringAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_stringAttribute.nextTree());

                }
                stream_stringAttribute.reset();

                // Velvet.g:179:59: ( boolAttribute )?
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
    // Velvet.g:182:1: intAttribute : VAR_INT ! name ( EQ ! INT )? ;
    public final VelvetParser.intAttribute_return intAttribute() throws RecognitionException {
        VelvetParser.intAttribute_return retval = new VelvetParser.intAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_INT88=null;
        Token EQ90=null;
        Token INT91=null;
        VelvetParser.name_return name89 =null;


        Tree VAR_INT88_tree=null;
        Tree EQ90_tree=null;
        Tree INT91_tree=null;

        try {
            // Velvet.g:182:13: ( VAR_INT ! name ( EQ ! INT )? )
            // Velvet.g:182:16: VAR_INT ! name ( EQ ! INT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_INT88=(Token)match(input,VAR_INT,FOLLOW_VAR_INT_in_intAttribute1140); 

            pushFollow(FOLLOW_name_in_intAttribute1143);
            name89=name();

            state._fsp--;

            adaptor.addChild(root_0, name89.getTree());

            // Velvet.g:182:30: ( EQ ! INT )?
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==EQ) ) {
                alt27=1;
            }
            switch (alt27) {
                case 1 :
                    // Velvet.g:182:31: EQ ! INT
                    {
                    EQ90=(Token)match(input,EQ,FOLLOW_EQ_in_intAttribute1146); 

                    INT91=(Token)match(input,INT,FOLLOW_INT_in_intAttribute1149); 
                    INT91_tree = 
                    (Tree)adaptor.create(INT91)
                    ;
                    adaptor.addChild(root_0, INT91_tree);


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
    // Velvet.g:183:1: floatAttribute : VAR_FLOAT ! name ( EQ ! FLOAT )? ;
    public final VelvetParser.floatAttribute_return floatAttribute() throws RecognitionException {
        VelvetParser.floatAttribute_return retval = new VelvetParser.floatAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_FLOAT92=null;
        Token EQ94=null;
        Token FLOAT95=null;
        VelvetParser.name_return name93 =null;


        Tree VAR_FLOAT92_tree=null;
        Tree EQ94_tree=null;
        Tree FLOAT95_tree=null;

        try {
            // Velvet.g:183:15: ( VAR_FLOAT ! name ( EQ ! FLOAT )? )
            // Velvet.g:183:18: VAR_FLOAT ! name ( EQ ! FLOAT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_FLOAT92=(Token)match(input,VAR_FLOAT,FOLLOW_VAR_FLOAT_in_floatAttribute1158); 

            pushFollow(FOLLOW_name_in_floatAttribute1161);
            name93=name();

            state._fsp--;

            adaptor.addChild(root_0, name93.getTree());

            // Velvet.g:183:34: ( EQ ! FLOAT )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==EQ) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // Velvet.g:183:35: EQ ! FLOAT
                    {
                    EQ94=(Token)match(input,EQ,FOLLOW_EQ_in_floatAttribute1164); 

                    FLOAT95=(Token)match(input,FLOAT,FOLLOW_FLOAT_in_floatAttribute1167); 
                    FLOAT95_tree = 
                    (Tree)adaptor.create(FLOAT95)
                    ;
                    adaptor.addChild(root_0, FLOAT95_tree);


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
    // Velvet.g:184:1: stringAttribute : VAR_STRING ! name ( EQ ! STRING )? ;
    public final VelvetParser.stringAttribute_return stringAttribute() throws RecognitionException {
        VelvetParser.stringAttribute_return retval = new VelvetParser.stringAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_STRING96=null;
        Token EQ98=null;
        Token STRING99=null;
        VelvetParser.name_return name97 =null;


        Tree VAR_STRING96_tree=null;
        Tree EQ98_tree=null;
        Tree STRING99_tree=null;

        try {
            // Velvet.g:184:16: ( VAR_STRING ! name ( EQ ! STRING )? )
            // Velvet.g:184:18: VAR_STRING ! name ( EQ ! STRING )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_STRING96=(Token)match(input,VAR_STRING,FOLLOW_VAR_STRING_in_stringAttribute1175); 

            pushFollow(FOLLOW_name_in_stringAttribute1178);
            name97=name();

            state._fsp--;

            adaptor.addChild(root_0, name97.getTree());

            // Velvet.g:184:35: ( EQ ! STRING )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==EQ) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // Velvet.g:184:36: EQ ! STRING
                    {
                    EQ98=(Token)match(input,EQ,FOLLOW_EQ_in_stringAttribute1181); 

                    STRING99=(Token)match(input,STRING,FOLLOW_STRING_in_stringAttribute1184); 
                    STRING99_tree = 
                    (Tree)adaptor.create(STRING99)
                    ;
                    adaptor.addChild(root_0, STRING99_tree);


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
    // Velvet.g:185:1: boolAttribute : VAR_BOOL ! name ( EQ ! BOOLEAN )? ;
    public final VelvetParser.boolAttribute_return boolAttribute() throws RecognitionException {
        VelvetParser.boolAttribute_return retval = new VelvetParser.boolAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_BOOL100=null;
        Token EQ102=null;
        Token BOOLEAN103=null;
        VelvetParser.name_return name101 =null;


        Tree VAR_BOOL100_tree=null;
        Tree EQ102_tree=null;
        Tree BOOLEAN103_tree=null;

        try {
            // Velvet.g:185:14: ( VAR_BOOL ! name ( EQ ! BOOLEAN )? )
            // Velvet.g:185:17: VAR_BOOL ! name ( EQ ! BOOLEAN )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_BOOL100=(Token)match(input,VAR_BOOL,FOLLOW_VAR_BOOL_in_boolAttribute1193); 

            pushFollow(FOLLOW_name_in_boolAttribute1196);
            name101=name();

            state._fsp--;

            adaptor.addChild(root_0, name101.getTree());

            // Velvet.g:185:32: ( EQ ! BOOLEAN )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==EQ) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // Velvet.g:185:33: EQ ! BOOLEAN
                    {
                    EQ102=(Token)match(input,EQ,FOLLOW_EQ_in_boolAttribute1199); 

                    BOOLEAN103=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_boolAttribute1202); 
                    BOOLEAN103_tree = 
                    (Tree)adaptor.create(BOOLEAN103)
                    ;
                    adaptor.addChild(root_0, BOOLEAN103_tree);


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
    // Velvet.g:187:1: unaryOp : OP_NOT ;
    public final VelvetParser.unaryOp_return unaryOp() throws RecognitionException {
        VelvetParser.unaryOp_return retval = new VelvetParser.unaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token OP_NOT104=null;

        Tree OP_NOT104_tree=null;

        try {
            // Velvet.g:188:2: ( OP_NOT )
            // Velvet.g:188:4: OP_NOT
            {
            root_0 = (Tree)adaptor.nil();


            OP_NOT104=(Token)match(input,OP_NOT,FOLLOW_OP_NOT_in_unaryOp1214); 
            OP_NOT104_tree = 
            (Tree)adaptor.create(OP_NOT104)
            ;
            adaptor.addChild(root_0, OP_NOT104_tree);


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
    // Velvet.g:191:1: binaryOp : ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT );
    public final VelvetParser.binaryOp_return binaryOp() throws RecognitionException {
        VelvetParser.binaryOp_return retval = new VelvetParser.binaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set105=null;

        Tree set105_tree=null;

        try {
            // Velvet.g:192:2: ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set105=(Token)input.LT(1);

            if ( (input.LA(1) >= OP_AND && input.LA(1) <= OP_IMPLIES)||(input.LA(1) >= OP_OR && input.LA(1) <= OP_XOR) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set105)
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
    // Velvet.g:199:1: attribRelation : ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ );
    public final VelvetParser.attribRelation_return attribRelation() throws RecognitionException {
        VelvetParser.attribRelation_return retval = new VelvetParser.attribRelation_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set106=null;

        Tree set106_tree=null;

        try {
            // Velvet.g:200:2: ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set106=(Token)input.LT(1);

            if ( input.LA(1)==ATTR_OP_EQUALS||input.LA(1)==ATTR_OP_GREATER_EQ||input.LA(1)==ATTR_OP_LESS_EQ ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set106)
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


 

    public static final BitSet FOLLOW_imports_in_velvetModel445 = new BitSet(new long[]{0x0004002000020000L});
    public static final BitSet FOLLOW_concept_in_velvetModel449 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_interfaceg_in_velvetModel451 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_velvetModel454 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IMPORT_in_imports466 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_imports468 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_imports470 = new BitSet(new long[]{0x0000000400000002L});
    public static final BitSet FOLLOW_REFINES_in_concept493 = new BitSet(new long[]{0x0000000000020000L});
    public static final BitSet FOLLOW_CONCEPT_in_concept496 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_concept498 = new BitSet(new long[]{0x0020000000008000L});
    public static final BitSet FOLLOW_COLON_in_concept502 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_conceptBaseExt_in_concept504 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_definitions_in_concept508 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt538 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_COMMA_in_conceptBaseExt541 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt543 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_REFINES_in_interfaceg567 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_INTERFACEG_in_interfaceg570 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_interfaceg572 = new BitSet(new long[]{0x0020000000008000L});
    public static final BitSet FOLLOW_COLON_in_interfaceg576 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_interfaceBaseExt_in_interfaceg578 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_definitions_in_interfaceg582 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt612 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_COMMA_in_interfaceBaseExt615 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_interfaceBaseExt617 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_START_C_in_definitions657 = new BitSet(new long[]{0x3C10024088280010L});
    public static final BitSet FOLLOW_def_in_definitions659 = new BitSet(new long[]{0x0000000000200000L});
    public static final BitSet FOLLOW_END_C_in_definitions661 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def680 = new BitSet(new long[]{0x3C10024088080012L});
    public static final BitSet FOLLOW_featureGroup_in_def688 = new BitSet(new long[]{0x3C00000080080002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def690 = new BitSet(new long[]{0x3C00000080080002L});
    public static final BitSet FOLLOW_feature_in_def699 = new BitSet(new long[]{0x3C00004088080012L});
    public static final BitSet FOLLOW_feature_in_def702 = new BitSet(new long[]{0x3C00004088080012L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def706 = new BitSet(new long[]{0x3C00004088080012L});
    public static final BitSet FOLLOW_constraint_in_nonFeatureDefinition726 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_instance_in_nonFeatureDefinition732 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribute_in_nonFeatureDefinition738 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_instance749 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_instance751 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_instance753 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANDATORY_in_feature775 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature777 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature781 = new BitSet(new long[]{0x0000004000000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature783 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature787 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature791 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_FEATURE_in_feature798 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_feature800 = new BitSet(new long[]{0x0028000000000000L});
    public static final BitSet FOLLOW_definitions_in_feature803 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SEMI_in_feature807 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_groupType_in_featureGroup838 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_START_C_in_featureGroup840 = new BitSet(new long[]{0x0000004008000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup842 = new BitSet(new long[]{0x0000004008000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup844 = new BitSet(new long[]{0x0000004008200010L});
    public static final BitSet FOLLOW_END_C_in_featureGroup847 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONSTRAINT_in_constraint890 = new BitSet(new long[]{0x0040401180000000L});
    public static final BitSet FOLLOW_ID_in_constraint894 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_EQ_in_constraint896 = new BitSet(new long[]{0x0040401180000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraint902 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_attributeConstraint_in_constraint906 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_constraint909 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition922 = new BitSet(new long[]{0x0001B80000000002L});
    public static final BitSet FOLLOW_binaryOp_in_constraintDefinition925 = new BitSet(new long[]{0x0040400180000000L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition927 = new BitSet(new long[]{0x0001B80000000002L});
    public static final BitSet FOLLOW_unaryOp_in_constraintOperand954 = new BitSet(new long[]{0x0040400180000000L});
    public static final BitSet FOLLOW_START_R_in_constraintOperand958 = new BitSet(new long[]{0x0040400180000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraintOperand960 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_END_R_in_constraintOperand962 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_constraintOperand966 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribConstraint_in_attributeConstraint1001 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1021 = new BitSet(new long[]{0x0002008000000A80L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1024 = new BitSet(new long[]{0x0000001180000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1026 = new BitSet(new long[]{0x0002008000000A80L});
    public static final BitSet FOLLOW_attribRelation_in_attribConstraint1034 = new BitSet(new long[]{0x0000001180000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1040 = new BitSet(new long[]{0x0002008000000002L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1043 = new BitSet(new long[]{0x0000001180000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1045 = new BitSet(new long[]{0x0002008000000002L});
    public static final BitSet FOLLOW_INT_in_attribNumInstance1077 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_attribNumInstance1084 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_intAttribute_in_attribute1096 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_floatAttribute_in_attribute1100 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_stringAttribute_in_attribute1104 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_boolAttribute_in_attribute1108 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_attribute1111 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_INT_in_intAttribute1140 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_intAttribute1143 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_EQ_in_intAttribute1146 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_intAttribute1149 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_FLOAT_in_floatAttribute1158 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_floatAttribute1161 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_EQ_in_floatAttribute1164 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_FLOAT_in_floatAttribute1167 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_STRING_in_stringAttribute1175 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_stringAttribute1178 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_EQ_in_stringAttribute1181 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_STRING_in_stringAttribute1184 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_BOOL_in_boolAttribute1193 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_boolAttribute1196 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_EQ_in_boolAttribute1199 = new BitSet(new long[]{0x0000000000004000L});
    public static final BitSet FOLLOW_BOOLEAN_in_boolAttribute1202 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_OP_NOT_in_unaryOp1214 = new BitSet(new long[]{0x0000000000000002L});

}