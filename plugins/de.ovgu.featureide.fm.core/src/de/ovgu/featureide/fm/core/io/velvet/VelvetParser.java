/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
// $ANTLR 3.4 Velvet.g 2012-12-02 13:17:20
package de.ovgu.featureide.fm.core.io.velvet;

import org.antlr.runtime.BitSet;
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
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "ABSTRACT", "ACONSTR", "ATTR", "ATTR_OP_EQUALS", "ATTR_OP_GREATER", "ATTR_OP_GREATER_EQ", "ATTR_OP_LESS", "ATTR_OP_LESS_EQ", "ATTR_OP_NOT_EQUALS", "BASEEXT", "BOOLEAN", "COLON", "COMMA", "CONCEPT", "CONSTR", "CONSTRAINT", "DEF", "END_C", "END_R", "EQ", "ESC_SEQ", "EXPONENT", "FEAT", "FEATURE", "FLOAT", "GROUP", "HEX_DIGIT", "ID", "IDPath", "IMP", "IMPORT", "INSTANCE", "INT", "MANDATORY", "MINUS", "OCTAL_ESC", "ONEOF", "OPERAND", "OP_AND", "OP_EQUIVALENT", "OP_IMPLIES", "OP_NOT", "OP_OR", "OP_XOR", "PLUS", "REFINES", "SEMI", "SOMEOF", "START_C", "START_R", "STRING", "UNARYOP", "UNICODE_ESC", "VAR_BOOL", "VAR_FLOAT", "VAR_INT", "VAR_STRING", "WS"
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
    public static final int MANDATORY=37;
    public static final int MINUS=38;
    public static final int OCTAL_ESC=39;
    public static final int ONEOF=40;
    public static final int OPERAND=41;
    public static final int OP_AND=42;
    public static final int OP_EQUIVALENT=43;
    public static final int OP_IMPLIES=44;
    public static final int OP_NOT=45;
    public static final int OP_OR=46;
    public static final int OP_XOR=47;
    public static final int PLUS=48;
    public static final int REFINES=49;
    public static final int SEMI=50;
    public static final int SOMEOF=51;
    public static final int START_C=52;
    public static final int START_R=53;
    public static final int STRING=54;
    public static final int UNARYOP=55;
    public static final int UNICODE_ESC=56;
    public static final int VAR_BOOL=57;
    public static final int VAR_FLOAT=58;
    public static final int VAR_INT=59;
    public static final int VAR_STRING=60;
    public static final int WS=61;

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
    // Velvet.g:75:1: velvetModel : ( imports )? concept EOF ;
    public final VelvetParser.velvetModel_return velvetModel() throws RecognitionException {
        VelvetParser.velvetModel_return retval = new VelvetParser.velvetModel_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token EOF3=null;
        VelvetParser.imports_return imports1 =null;

        VelvetParser.concept_return concept2 =null;


        Tree EOF3_tree=null;

        try {
            // Velvet.g:76:2: ( ( imports )? concept EOF )
            // Velvet.g:76:4: ( imports )? concept EOF
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:76:4: ( imports )?
            int alt1=2;
            int LA1_0 = input.LA(1);

            if ( (LA1_0==IMPORT) ) {
                alt1=1;
            }
            switch (alt1) {
                case 1 :
                    // Velvet.g:76:4: imports
                    {
                    pushFollow(FOLLOW_imports_in_velvetModel438);
                    imports1=imports();

                    state._fsp--;

                    adaptor.addChild(root_0, imports1.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_concept_in_velvetModel441);
            concept2=concept();

            state._fsp--;

            adaptor.addChild(root_0, concept2.getTree());

            EOF3=(Token)match(input,EOF,FOLLOW_EOF_in_velvetModel443); 
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


    public static class imports_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "imports"
    // Velvet.g:79:1: imports : ( IMPORT name SEMI )+ -> ^( IMP ( name )+ ) ;
    public final VelvetParser.imports_return imports() throws RecognitionException {
        VelvetParser.imports_return retval = new VelvetParser.imports_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token IMPORT4=null;
        Token SEMI6=null;
        VelvetParser.name_return name5 =null;


        Tree IMPORT4_tree=null;
        Tree SEMI6_tree=null;
        RewriteRuleTokenStream stream_IMPORT=new RewriteRuleTokenStream(adaptor,"token IMPORT");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:79:9: ( ( IMPORT name SEMI )+ -> ^( IMP ( name )+ ) )
            // Velvet.g:79:11: ( IMPORT name SEMI )+
            {
            // Velvet.g:79:11: ( IMPORT name SEMI )+
            int cnt2=0;
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( (LA2_0==IMPORT) ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // Velvet.g:79:12: IMPORT name SEMI
            	    {
            	    IMPORT4=(Token)match(input,IMPORT,FOLLOW_IMPORT_in_imports455);  
            	    stream_IMPORT.add(IMPORT4);


            	    pushFollow(FOLLOW_name_in_imports457);
            	    name5=name();

            	    state._fsp--;

            	    stream_name.add(name5.getTree());

            	    SEMI6=(Token)match(input,SEMI,FOLLOW_SEMI_in_imports459);  
            	    stream_SEMI.add(SEMI6);


            	    }
            	    break;

            	default :
            	    if ( cnt2 >= 1 ) break loop2;
                        EarlyExitException eee =
                            new EarlyExitException(2, input);
                        throw eee;
                }
                cnt2++;
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
            // 80:2: -> ^( IMP ( name )+ )
            {
                // Velvet.g:80:5: ^( IMP ( name )+ )
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
    // Velvet.g:83:1: concept : ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? definitions -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? definitions ) ;
    public final VelvetParser.concept_return concept() throws RecognitionException {
        VelvetParser.concept_return retval = new VelvetParser.concept_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token REFINES7=null;
        Token CONCEPT8=null;
        Token ID9=null;
        Token COLON10=null;
        VelvetParser.conceptBaseExt_return conceptBaseExt11 =null;

        VelvetParser.definitions_return definitions12 =null;


        Tree REFINES7_tree=null;
        Tree CONCEPT8_tree=null;
        Tree ID9_tree=null;
        Tree COLON10_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_REFINES=new RewriteRuleTokenStream(adaptor,"token REFINES");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_CONCEPT=new RewriteRuleTokenStream(adaptor,"token CONCEPT");
        RewriteRuleSubtreeStream stream_conceptBaseExt=new RewriteRuleSubtreeStream(adaptor,"rule conceptBaseExt");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:83:9: ( ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? definitions -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? definitions ) )
            // Velvet.g:83:11: ( REFINES )? CONCEPT ID ( COLON conceptBaseExt )? definitions
            {
            // Velvet.g:83:11: ( REFINES )?
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0==REFINES) ) {
                alt3=1;
            }
            switch (alt3) {
                case 1 :
                    // Velvet.g:83:11: REFINES
                    {
                    REFINES7=(Token)match(input,REFINES,FOLLOW_REFINES_in_concept482);  
                    stream_REFINES.add(REFINES7);


                    }
                    break;

            }


            CONCEPT8=(Token)match(input,CONCEPT,FOLLOW_CONCEPT_in_concept485);  
            stream_CONCEPT.add(CONCEPT8);


            ID9=(Token)match(input,ID,FOLLOW_ID_in_concept487);  
            stream_ID.add(ID9);


            // Velvet.g:83:32: ( COLON conceptBaseExt )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0==COLON) ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // Velvet.g:83:33: COLON conceptBaseExt
                    {
                    COLON10=(Token)match(input,COLON,FOLLOW_COLON_in_concept491);  
                    stream_COLON.add(COLON10);


                    pushFollow(FOLLOW_conceptBaseExt_in_concept493);
                    conceptBaseExt11=conceptBaseExt();

                    state._fsp--;

                    stream_conceptBaseExt.add(conceptBaseExt11.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_concept497);
            definitions12=definitions();

            state._fsp--;

            stream_definitions.add(definitions12.getTree());

            // AST REWRITE
            // elements: conceptBaseExt, CONCEPT, definitions, REFINES, ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 84:2: -> ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? definitions )
            {
                // Velvet.g:84:5: ^( CONCEPT ID ( REFINES )? ( conceptBaseExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CONCEPT.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:84:18: ( REFINES )?
                if ( stream_REFINES.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_REFINES.nextNode()
                    );

                }
                stream_REFINES.reset();

                // Velvet.g:84:27: ( conceptBaseExt )?
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
    // Velvet.g:87:1: conceptBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
    public final VelvetParser.conceptBaseExt_return conceptBaseExt() throws RecognitionException {
        VelvetParser.conceptBaseExt_return retval = new VelvetParser.conceptBaseExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID13=null;
        Token COMMA14=null;
        Token ID15=null;

        Tree ID13_tree=null;
        Tree COMMA14_tree=null;
        Tree ID15_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

        try {
            // Velvet.g:88:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:88:4: ID ( COMMA ID )*
            {
            ID13=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt527);  
            stream_ID.add(ID13);


            // Velvet.g:88:7: ( COMMA ID )*
            loop5:
            do {
                int alt5=2;
                int LA5_0 = input.LA(1);

                if ( (LA5_0==COMMA) ) {
                    alt5=1;
                }


                switch (alt5) {
            	case 1 :
            	    // Velvet.g:88:8: COMMA ID
            	    {
            	    COMMA14=(Token)match(input,COMMA,FOLLOW_COMMA_in_conceptBaseExt530);  
            	    stream_COMMA.add(COMMA14);


            	    ID15=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt532);  
            	    stream_ID.add(ID15);


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
            // 89:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:89:5: ^( BASEEXT ( ID )+ )
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


    public static class name_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "name"
    // Velvet.g:92:1: name : ( ID | IDPath );
    public final VelvetParser.name_return name() throws RecognitionException {
        VelvetParser.name_return retval = new VelvetParser.name_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set16=null;

        Tree set16_tree=null;

        try {
            // Velvet.g:92:5: ( ID | IDPath )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set16=(Token)input.LT(1);

            if ( (input.LA(1) >= ID && input.LA(1) <= IDPath) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set16)
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
    // Velvet.g:96:1: definitions : START_C def END_C -> ^( DEF def ) ;
    public final VelvetParser.definitions_return definitions() throws RecognitionException {
        VelvetParser.definitions_return retval = new VelvetParser.definitions_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C17=null;
        Token END_C19=null;
        VelvetParser.def_return def18 =null;


        Tree START_C17_tree=null;
        Tree END_C19_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_def=new RewriteRuleSubtreeStream(adaptor,"rule def");
        try {
            // Velvet.g:97:2: ( START_C def END_C -> ^( DEF def ) )
            // Velvet.g:97:4: START_C def END_C
            {
            START_C17=(Token)match(input,START_C,FOLLOW_START_C_in_definitions572);  
            stream_START_C.add(START_C17);


            pushFollow(FOLLOW_def_in_definitions574);
            def18=def();

            state._fsp--;

            stream_def.add(def18.getTree());

            END_C19=(Token)match(input,END_C,FOLLOW_END_C_in_definitions576);  
            stream_END_C.add(END_C19);


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
            // 98:2: -> ^( DEF def )
            {
                // Velvet.g:98:5: ^( DEF def )
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
    // Velvet.g:101:1: def : ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? ;
    public final VelvetParser.def_return def() throws RecognitionException {
        VelvetParser.def_return retval = new VelvetParser.def_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition20 =null;

        VelvetParser.featureGroup_return featureGroup21 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition22 =null;

        VelvetParser.feature_return feature23 =null;

        VelvetParser.feature_return feature24 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition25 =null;



        try {
            // Velvet.g:101:5: ( ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? )
            // Velvet.g:101:7: ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:101:7: ( nonFeatureDefinition )*
            loop6:
            do {
                int alt6=2;
                int LA6_0 = input.LA(1);

                if ( (LA6_0==CONSTRAINT||LA6_0==ID||(LA6_0 >= VAR_BOOL && LA6_0 <= VAR_STRING)) ) {
                    alt6=1;
                }


                switch (alt6) {
            	case 1 :
            	    // Velvet.g:101:7: nonFeatureDefinition
            	    {
            	    pushFollow(FOLLOW_nonFeatureDefinition_in_def595);
            	    nonFeatureDefinition20=nonFeatureDefinition();

            	    state._fsp--;

            	    adaptor.addChild(root_0, nonFeatureDefinition20.getTree());

            	    }
            	    break;

            	default :
            	    break loop6;
                }
            } while (true);


            // Velvet.g:101:29: ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            int alt9=3;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==ONEOF||LA9_0==SOMEOF) ) {
                alt9=1;
            }
            else if ( (LA9_0==ABSTRACT||LA9_0==FEATURE||LA9_0==MANDATORY) ) {
                alt9=2;
            }
            switch (alt9) {
                case 1 :
                    // Velvet.g:102:3: ( featureGroup ( nonFeatureDefinition )* )
                    {
                    // Velvet.g:102:3: ( featureGroup ( nonFeatureDefinition )* )
                    // Velvet.g:102:4: featureGroup ( nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_featureGroup_in_def603);
                    featureGroup21=featureGroup();

                    state._fsp--;

                    adaptor.addChild(root_0, featureGroup21.getTree());

                    // Velvet.g:102:17: ( nonFeatureDefinition )*
                    loop7:
                    do {
                        int alt7=2;
                        int LA7_0 = input.LA(1);

                        if ( (LA7_0==CONSTRAINT||LA7_0==ID||(LA7_0 >= VAR_BOOL && LA7_0 <= VAR_STRING)) ) {
                            alt7=1;
                        }


                        switch (alt7) {
                    	case 1 :
                    	    // Velvet.g:102:17: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def605);
                    	    nonFeatureDefinition22=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition22.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop7;
                        }
                    } while (true);


                    }


                    }
                    break;
                case 2 :
                    // Velvet.g:103:3: ( feature ( feature | nonFeatureDefinition )* )
                    {
                    // Velvet.g:103:3: ( feature ( feature | nonFeatureDefinition )* )
                    // Velvet.g:103:4: feature ( feature | nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_feature_in_def614);
                    feature23=feature();

                    state._fsp--;

                    adaptor.addChild(root_0, feature23.getTree());

                    // Velvet.g:103:12: ( feature | nonFeatureDefinition )*
                    loop8:
                    do {
                        int alt8=3;
                        int LA8_0 = input.LA(1);

                        if ( (LA8_0==ABSTRACT||LA8_0==FEATURE||LA8_0==MANDATORY) ) {
                            alt8=1;
                        }
                        else if ( (LA8_0==CONSTRAINT||LA8_0==ID||(LA8_0 >= VAR_BOOL && LA8_0 <= VAR_STRING)) ) {
                            alt8=2;
                        }


                        switch (alt8) {
                    	case 1 :
                    	    // Velvet.g:103:13: feature
                    	    {
                    	    pushFollow(FOLLOW_feature_in_def617);
                    	    feature24=feature();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, feature24.getTree());

                    	    }
                    	    break;
                    	case 2 :
                    	    // Velvet.g:103:23: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_def621);
                    	    nonFeatureDefinition25=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition25.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop8;
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
    // Velvet.g:106:1: nonFeatureDefinition : ( constraint | instance | attribute );
    public final VelvetParser.nonFeatureDefinition_return nonFeatureDefinition() throws RecognitionException {
        VelvetParser.nonFeatureDefinition_return retval = new VelvetParser.nonFeatureDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraint_return constraint26 =null;

        VelvetParser.instance_return instance27 =null;

        VelvetParser.attribute_return attribute28 =null;



        try {
            // Velvet.g:107:2: ( constraint | instance | attribute )
            int alt10=3;
            switch ( input.LA(1) ) {
            case CONSTRAINT:
                {
                alt10=1;
                }
                break;
            case ID:
                {
                alt10=2;
                }
                break;
            case VAR_BOOL:
            case VAR_FLOAT:
            case VAR_INT:
            case VAR_STRING:
                {
                alt10=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 10, 0, input);

                throw nvae;

            }

            switch (alt10) {
                case 1 :
                    // Velvet.g:107:4: constraint
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_constraint_in_nonFeatureDefinition641);
                    constraint26=constraint();

                    state._fsp--;

                    adaptor.addChild(root_0, constraint26.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:108:4: instance
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_instance_in_nonFeatureDefinition647);
                    instance27=instance();

                    state._fsp--;

                    adaptor.addChild(root_0, instance27.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:109:4: attribute
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_attribute_in_nonFeatureDefinition653);
                    attribute28=attribute();

                    state._fsp--;

                    adaptor.addChild(root_0, attribute28.getTree());

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
    // Velvet.g:112:1: instance : ID name SEMI -> INSTANCE ID name ;
    public final VelvetParser.instance_return instance() throws RecognitionException {
        VelvetParser.instance_return retval = new VelvetParser.instance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID29=null;
        Token SEMI31=null;
        VelvetParser.name_return name30 =null;


        Tree ID29_tree=null;
        Tree SEMI31_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:112:9: ( ID name SEMI -> INSTANCE ID name )
            // Velvet.g:112:11: ID name SEMI
            {
            ID29=(Token)match(input,ID,FOLLOW_ID_in_instance664);  
            stream_ID.add(ID29);


            pushFollow(FOLLOW_name_in_instance666);
            name30=name();

            state._fsp--;

            stream_name.add(name30.getTree());

            SEMI31=(Token)match(input,SEMI,FOLLOW_SEMI_in_instance668);  
            stream_SEMI.add(SEMI31);


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
            // 113:2: -> INSTANCE ID name
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
    // Velvet.g:116:1: feature : ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) ;
    public final VelvetParser.feature_return feature() throws RecognitionException {
        VelvetParser.feature_return retval = new VelvetParser.feature_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token MANDATORY32=null;
        Token ABSTRACT33=null;
        Token ABSTRACT34=null;
        Token MANDATORY35=null;
        Token MANDATORY36=null;
        Token ABSTRACT37=null;
        Token FEATURE38=null;
        Token SEMI41=null;
        VelvetParser.name_return name39 =null;

        VelvetParser.definitions_return definitions40 =null;


        Tree MANDATORY32_tree=null;
        Tree ABSTRACT33_tree=null;
        Tree ABSTRACT34_tree=null;
        Tree MANDATORY35_tree=null;
        Tree MANDATORY36_tree=null;
        Tree ABSTRACT37_tree=null;
        Tree FEATURE38_tree=null;
        Tree SEMI41_tree=null;
        RewriteRuleTokenStream stream_ABSTRACT=new RewriteRuleTokenStream(adaptor,"token ABSTRACT");
        RewriteRuleTokenStream stream_MANDATORY=new RewriteRuleTokenStream(adaptor,"token MANDATORY");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleTokenStream stream_FEATURE=new RewriteRuleTokenStream(adaptor,"token FEATURE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:117:2: ( ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) )
            // Velvet.g:117:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI )
            {
            // Velvet.g:117:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )?
            int alt11=5;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==MANDATORY) ) {
                int LA11_1 = input.LA(2);

                if ( (LA11_1==ABSTRACT) ) {
                    alt11=1;
                }
                else if ( (LA11_1==FEATURE) ) {
                    alt11=3;
                }
            }
            else if ( (LA11_0==ABSTRACT) ) {
                int LA11_2 = input.LA(2);

                if ( (LA11_2==MANDATORY) ) {
                    alt11=2;
                }
                else if ( (LA11_2==FEATURE) ) {
                    alt11=4;
                }
            }
            switch (alt11) {
                case 1 :
                    // Velvet.g:117:5: MANDATORY ABSTRACT
                    {
                    MANDATORY32=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature690);  
                    stream_MANDATORY.add(MANDATORY32);


                    ABSTRACT33=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature692);  
                    stream_ABSTRACT.add(ABSTRACT33);


                    }
                    break;
                case 2 :
                    // Velvet.g:117:26: ABSTRACT MANDATORY
                    {
                    ABSTRACT34=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature696);  
                    stream_ABSTRACT.add(ABSTRACT34);


                    MANDATORY35=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature698);  
                    stream_MANDATORY.add(MANDATORY35);


                    }
                    break;
                case 3 :
                    // Velvet.g:117:47: MANDATORY
                    {
                    MANDATORY36=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature702);  
                    stream_MANDATORY.add(MANDATORY36);


                    }
                    break;
                case 4 :
                    // Velvet.g:117:59: ABSTRACT
                    {
                    ABSTRACT37=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature706);  
                    stream_ABSTRACT.add(ABSTRACT37);


                    }
                    break;

            }


            FEATURE38=(Token)match(input,FEATURE,FOLLOW_FEATURE_in_feature713);  
            stream_FEATURE.add(FEATURE38);


            pushFollow(FOLLOW_name_in_feature715);
            name39=name();

            state._fsp--;

            stream_name.add(name39.getTree());

            // Velvet.g:118:17: ( definitions | SEMI )
            int alt12=2;
            int LA12_0 = input.LA(1);

            if ( (LA12_0==START_C) ) {
                alt12=1;
            }
            else if ( (LA12_0==SEMI) ) {
                alt12=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 12, 0, input);

                throw nvae;

            }
            switch (alt12) {
                case 1 :
                    // Velvet.g:118:18: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_feature718);
                    definitions40=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions40.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:118:32: SEMI
                    {
                    SEMI41=(Token)match(input,SEMI,FOLLOW_SEMI_in_feature722);  
                    stream_SEMI.add(SEMI41);


                    }
                    break;

            }


            // AST REWRITE
            // elements: name, MANDATORY, definitions, ABSTRACT
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 119:2: -> ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
            {
                // Velvet.g:119:5: ^( FEAT name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(FEAT, "FEAT")
                , root_1);

                adaptor.addChild(root_1, stream_name.nextTree());

                // Velvet.g:119:17: ( MANDATORY )?
                if ( stream_MANDATORY.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_MANDATORY.nextNode()
                    );

                }
                stream_MANDATORY.reset();

                // Velvet.g:119:28: ( ABSTRACT )?
                if ( stream_ABSTRACT.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ABSTRACT.nextNode()
                    );

                }
                stream_ABSTRACT.reset();

                // Velvet.g:119:38: ( definitions )?
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
    // Velvet.g:122:1: featureGroup : groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) ;
    public final VelvetParser.featureGroup_return featureGroup() throws RecognitionException {
        VelvetParser.featureGroup_return retval = new VelvetParser.featureGroup_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C43=null;
        Token END_C46=null;
        VelvetParser.groupType_return groupType42 =null;

        VelvetParser.feature_return feature44 =null;

        VelvetParser.feature_return feature45 =null;


        Tree START_C43_tree=null;
        Tree END_C46_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_groupType=new RewriteRuleSubtreeStream(adaptor,"rule groupType");
        RewriteRuleSubtreeStream stream_feature=new RewriteRuleSubtreeStream(adaptor,"rule feature");
        try {
            // Velvet.g:123:2: ( groupType START_C feature ( feature )+ END_C -> ^( GROUP groupType feature ( feature )+ ) )
            // Velvet.g:123:4: groupType START_C feature ( feature )+ END_C
            {
            pushFollow(FOLLOW_groupType_in_featureGroup753);
            groupType42=groupType();

            state._fsp--;

            stream_groupType.add(groupType42.getTree());

            START_C43=(Token)match(input,START_C,FOLLOW_START_C_in_featureGroup755);  
            stream_START_C.add(START_C43);


            pushFollow(FOLLOW_feature_in_featureGroup757);
            feature44=feature();

            state._fsp--;

            stream_feature.add(feature44.getTree());

            // Velvet.g:123:30: ( feature )+
            int cnt13=0;
            loop13:
            do {
                int alt13=2;
                int LA13_0 = input.LA(1);

                if ( (LA13_0==ABSTRACT||LA13_0==FEATURE||LA13_0==MANDATORY) ) {
                    alt13=1;
                }


                switch (alt13) {
            	case 1 :
            	    // Velvet.g:123:30: feature
            	    {
            	    pushFollow(FOLLOW_feature_in_featureGroup759);
            	    feature45=feature();

            	    state._fsp--;

            	    stream_feature.add(feature45.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt13 >= 1 ) break loop13;
                        EarlyExitException eee =
                            new EarlyExitException(13, input);
                        throw eee;
                }
                cnt13++;
            } while (true);


            END_C46=(Token)match(input,END_C,FOLLOW_END_C_in_featureGroup762);  
            stream_END_C.add(END_C46);


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
            // 124:2: -> ^( GROUP groupType feature ( feature )+ )
            {
                // Velvet.g:124:5: ^( GROUP groupType feature ( feature )+ )
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
    // Velvet.g:127:1: groupType : ( SOMEOF | ONEOF );
    public final VelvetParser.groupType_return groupType() throws RecognitionException {
        VelvetParser.groupType_return retval = new VelvetParser.groupType_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set47=null;

        Tree set47_tree=null;

        try {
            // Velvet.g:128:2: ( SOMEOF | ONEOF )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set47=(Token)input.LT(1);

            if ( input.LA(1)==ONEOF||input.LA(1)==SOMEOF ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set47)
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
    // Velvet.g:132:1: constraint : CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !;
    public final VelvetParser.constraint_return constraint() throws RecognitionException {
        VelvetParser.constraint_return retval = new VelvetParser.constraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token CONSTRAINT48=null;
        Token ID49=null;
        Token EQ50=null;
        Token SEMI53=null;
        VelvetParser.constraintDefinition_return constraintDefinition51 =null;

        VelvetParser.attributeConstraint_return attributeConstraint52 =null;


        Tree CONSTRAINT48_tree=null;
        Tree ID49_tree=null;
        Tree EQ50_tree=null;
        Tree SEMI53_tree=null;

        try {
            // Velvet.g:133:2: ( CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !)
            // Velvet.g:133:4: CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !
            {
            root_0 = (Tree)adaptor.nil();


            CONSTRAINT48=(Token)match(input,CONSTRAINT,FOLLOW_CONSTRAINT_in_constraint805); 
            CONSTRAINT48_tree = 
            (Tree)adaptor.create(CONSTRAINT48)
            ;
            root_0 = (Tree)adaptor.becomeRoot(CONSTRAINT48_tree, root_0);


            // Velvet.g:133:16: ( ID EQ !)?
            int alt14=2;
            int LA14_0 = input.LA(1);

            if ( (LA14_0==ID) ) {
                int LA14_1 = input.LA(2);

                if ( (LA14_1==EQ) ) {
                    alt14=1;
                }
            }
            switch (alt14) {
                case 1 :
                    // Velvet.g:133:17: ID EQ !
                    {
                    ID49=(Token)match(input,ID,FOLLOW_ID_in_constraint809); 
                    ID49_tree = 
                    (Tree)adaptor.create(ID49)
                    ;
                    adaptor.addChild(root_0, ID49_tree);


                    EQ50=(Token)match(input,EQ,FOLLOW_EQ_in_constraint811); 

                    }
                    break;

            }


            // Velvet.g:133:26: ( constraintDefinition | attributeConstraint )
            int alt15=2;
            switch ( input.LA(1) ) {
            case OP_NOT:
            case START_R:
                {
                alt15=1;
                }
                break;
            case ID:
            case IDPath:
                {
                int LA15_2 = input.LA(2);

                if ( ((LA15_2 >= OP_AND && LA15_2 <= OP_IMPLIES)||(LA15_2 >= OP_OR && LA15_2 <= OP_XOR)||LA15_2==SEMI) ) {
                    alt15=1;
                }
                else if ( (LA15_2==ATTR_OP_EQUALS||LA15_2==ATTR_OP_GREATER_EQ||LA15_2==ATTR_OP_LESS_EQ||LA15_2==MINUS||LA15_2==PLUS) ) {
                    alt15=2;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 15, 2, input);

                    throw nvae;

                }
                }
                break;
            case INT:
                {
                alt15=2;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 15, 0, input);

                throw nvae;

            }

            switch (alt15) {
                case 1 :
                    // Velvet.g:133:27: constraintDefinition
                    {
                    pushFollow(FOLLOW_constraintDefinition_in_constraint817);
                    constraintDefinition51=constraintDefinition();

                    state._fsp--;

                    adaptor.addChild(root_0, constraintDefinition51.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:133:50: attributeConstraint
                    {
                    pushFollow(FOLLOW_attributeConstraint_in_constraint821);
                    attributeConstraint52=attributeConstraint();

                    state._fsp--;

                    adaptor.addChild(root_0, attributeConstraint52.getTree());

                    }
                    break;

            }


            SEMI53=(Token)match(input,SEMI,FOLLOW_SEMI_in_constraint824); 

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
    // Velvet.g:136:1: constraintDefinition : constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) ;
    public final VelvetParser.constraintDefinition_return constraintDefinition() throws RecognitionException {
        VelvetParser.constraintDefinition_return retval = new VelvetParser.constraintDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraintOperand_return constraintOperand54 =null;

        VelvetParser.binaryOp_return binaryOp55 =null;

        VelvetParser.constraintOperand_return constraintOperand56 =null;


        RewriteRuleSubtreeStream stream_constraintOperand=new RewriteRuleSubtreeStream(adaptor,"rule constraintOperand");
        RewriteRuleSubtreeStream stream_binaryOp=new RewriteRuleSubtreeStream(adaptor,"rule binaryOp");
        try {
            // Velvet.g:137:2: ( constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) )
            // Velvet.g:137:4: constraintOperand ( binaryOp constraintOperand )*
            {
            pushFollow(FOLLOW_constraintOperand_in_constraintDefinition837);
            constraintOperand54=constraintOperand();

            state._fsp--;

            stream_constraintOperand.add(constraintOperand54.getTree());

            // Velvet.g:137:22: ( binaryOp constraintOperand )*
            loop16:
            do {
                int alt16=2;
                int LA16_0 = input.LA(1);

                if ( ((LA16_0 >= OP_AND && LA16_0 <= OP_IMPLIES)||(LA16_0 >= OP_OR && LA16_0 <= OP_XOR)) ) {
                    alt16=1;
                }


                switch (alt16) {
            	case 1 :
            	    // Velvet.g:137:23: binaryOp constraintOperand
            	    {
            	    pushFollow(FOLLOW_binaryOp_in_constraintDefinition840);
            	    binaryOp55=binaryOp();

            	    state._fsp--;

            	    stream_binaryOp.add(binaryOp55.getTree());

            	    pushFollow(FOLLOW_constraintOperand_in_constraintDefinition842);
            	    constraintOperand56=constraintOperand();

            	    state._fsp--;

            	    stream_constraintOperand.add(constraintOperand56.getTree());

            	    }
            	    break;

            	default :
            	    break loop16;
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
            // 138:2: -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
            {
                // Velvet.g:138:5: ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
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

                // Velvet.g:138:33: ( binaryOp )*
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
    // Velvet.g:141:1: constraintOperand : ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? ;
    public final VelvetParser.constraintOperand_return constraintOperand() throws RecognitionException {
        VelvetParser.constraintOperand_return retval = new VelvetParser.constraintOperand_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_R58=null;
        Token END_R60=null;
        VelvetParser.unaryOp_return unaryOp57 =null;

        VelvetParser.constraintDefinition_return constraintDefinition59 =null;

        VelvetParser.name_return name61 =null;


        Tree START_R58_tree=null;
        Tree END_R60_tree=null;
        RewriteRuleTokenStream stream_END_R=new RewriteRuleTokenStream(adaptor,"token END_R");
        RewriteRuleTokenStream stream_START_R=new RewriteRuleTokenStream(adaptor,"token START_R");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_unaryOp=new RewriteRuleSubtreeStream(adaptor,"rule unaryOp");
        RewriteRuleSubtreeStream stream_constraintDefinition=new RewriteRuleSubtreeStream(adaptor,"rule constraintDefinition");
        try {
            // Velvet.g:141:19: ( ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? )
            // Velvet.g:141:21: ( unaryOp )* ( START_R constraintDefinition END_R | name )
            {
            // Velvet.g:141:21: ( unaryOp )*
            loop17:
            do {
                int alt17=2;
                int LA17_0 = input.LA(1);

                if ( (LA17_0==OP_NOT) ) {
                    alt17=1;
                }


                switch (alt17) {
            	case 1 :
            	    // Velvet.g:141:21: unaryOp
            	    {
            	    pushFollow(FOLLOW_unaryOp_in_constraintOperand869);
            	    unaryOp57=unaryOp();

            	    state._fsp--;

            	    stream_unaryOp.add(unaryOp57.getTree());

            	    }
            	    break;

            	default :
            	    break loop17;
                }
            } while (true);


            // Velvet.g:141:30: ( START_R constraintDefinition END_R | name )
            int alt18=2;
            int LA18_0 = input.LA(1);

            if ( (LA18_0==START_R) ) {
                alt18=1;
            }
            else if ( ((LA18_0 >= ID && LA18_0 <= IDPath)) ) {
                alt18=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 18, 0, input);

                throw nvae;

            }
            switch (alt18) {
                case 1 :
                    // Velvet.g:141:31: START_R constraintDefinition END_R
                    {
                    START_R58=(Token)match(input,START_R,FOLLOW_START_R_in_constraintOperand873);  
                    stream_START_R.add(START_R58);


                    pushFollow(FOLLOW_constraintDefinition_in_constraintOperand875);
                    constraintDefinition59=constraintDefinition();

                    state._fsp--;

                    stream_constraintDefinition.add(constraintDefinition59.getTree());

                    END_R60=(Token)match(input,END_R,FOLLOW_END_R_in_constraintOperand877);  
                    stream_END_R.add(END_R60);


                    }
                    break;
                case 2 :
                    // Velvet.g:141:68: name
                    {
                    pushFollow(FOLLOW_name_in_constraintOperand881);
                    name61=name();

                    state._fsp--;

                    stream_name.add(name61.getTree());

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
            // 142:2: -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )?
            {
                // Velvet.g:142:5: ( constraintDefinition )?
                if ( stream_constraintDefinition.hasNext() ) {
                    adaptor.addChild(root_0, stream_constraintDefinition.nextTree());

                }
                stream_constraintDefinition.reset();

                // Velvet.g:142:27: ( ^( UNARYOP unaryOp ) )*
                while ( stream_unaryOp.hasNext() ) {
                    // Velvet.g:142:27: ^( UNARYOP unaryOp )
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

                // Velvet.g:142:47: ( ^( OPERAND name ) )?
                if ( stream_name.hasNext() ) {
                    // Velvet.g:142:47: ^( OPERAND name )
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
    // Velvet.g:145:1: attributeConstraint : attribConstraint -> ^( ACONSTR attribConstraint ) ;
    public final VelvetParser.attributeConstraint_return attributeConstraint() throws RecognitionException {
        VelvetParser.attributeConstraint_return retval = new VelvetParser.attributeConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribConstraint_return attribConstraint62 =null;


        RewriteRuleSubtreeStream stream_attribConstraint=new RewriteRuleSubtreeStream(adaptor,"rule attribConstraint");
        try {
            // Velvet.g:146:2: ( attribConstraint -> ^( ACONSTR attribConstraint ) )
            // Velvet.g:146:4: attribConstraint
            {
            pushFollow(FOLLOW_attribConstraint_in_attributeConstraint916);
            attribConstraint62=attribConstraint();

            state._fsp--;

            stream_attribConstraint.add(attribConstraint62.getTree());

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
            // 147:2: -> ^( ACONSTR attribConstraint )
            {
                // Velvet.g:147:5: ^( ACONSTR attribConstraint )
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
    // Velvet.g:150:1: attribConstraint : attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* ;
    public final VelvetParser.attribConstraint_return attribConstraint() throws RecognitionException {
        VelvetParser.attribConstraint_return retval = new VelvetParser.attribConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribNumInstance_return attribNumInstance63 =null;

        VelvetParser.attribOperator_return attribOperator64 =null;

        VelvetParser.attribNumInstance_return attribNumInstance65 =null;

        VelvetParser.attribRelation_return attribRelation66 =null;

        VelvetParser.attribNumInstance_return attribNumInstance67 =null;

        VelvetParser.attribOperator_return attribOperator68 =null;

        VelvetParser.attribNumInstance_return attribNumInstance69 =null;



        try {
            // Velvet.g:151:2: ( attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* )
            // Velvet.g:151:4: attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )*
            {
            root_0 = (Tree)adaptor.nil();


            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint936);
            attribNumInstance63=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance63.getTree());

            // Velvet.g:151:22: ( attribOperator attribNumInstance )*
            loop19:
            do {
                int alt19=2;
                int LA19_0 = input.LA(1);

                if ( (LA19_0==MINUS||LA19_0==PLUS) ) {
                    alt19=1;
                }


                switch (alt19) {
            	case 1 :
            	    // Velvet.g:151:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint939);
            	    attribOperator64=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator64.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint941);
            	    attribNumInstance65=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance65.getTree());

            	    }
            	    break;

            	default :
            	    break loop19;
                }
            } while (true);


            pushFollow(FOLLOW_attribRelation_in_attribConstraint949);
            attribRelation66=attribRelation();

            state._fsp--;

            adaptor.addChild(root_0, attribRelation66.getTree());

            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint955);
            attribNumInstance67=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance67.getTree());

            // Velvet.g:153:22: ( attribOperator attribNumInstance )*
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( (LA20_0==MINUS||LA20_0==PLUS) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // Velvet.g:153:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint958);
            	    attribOperator68=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator68.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint960);
            	    attribNumInstance69=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance69.getTree());

            	    }
            	    break;

            	default :
            	    break loop20;
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
    // Velvet.g:156:1: attribOperator : ( PLUS | MINUS );
    public final VelvetParser.attribOperator_return attribOperator() throws RecognitionException {
        VelvetParser.attribOperator_return retval = new VelvetParser.attribOperator_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set70=null;

        Tree set70_tree=null;

        try {
            // Velvet.g:157:2: ( PLUS | MINUS )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set70=(Token)input.LT(1);

            if ( input.LA(1)==MINUS||input.LA(1)==PLUS ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set70)
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
    // Velvet.g:161:1: attribNumInstance : ( INT | name );
    public final VelvetParser.attribNumInstance_return attribNumInstance() throws RecognitionException {
        VelvetParser.attribNumInstance_return retval = new VelvetParser.attribNumInstance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token INT71=null;
        VelvetParser.name_return name72 =null;


        Tree INT71_tree=null;

        try {
            // Velvet.g:162:2: ( INT | name )
            int alt21=2;
            int LA21_0 = input.LA(1);

            if ( (LA21_0==INT) ) {
                alt21=1;
            }
            else if ( ((LA21_0 >= ID && LA21_0 <= IDPath)) ) {
                alt21=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 21, 0, input);

                throw nvae;

            }
            switch (alt21) {
                case 1 :
                    // Velvet.g:162:4: INT
                    {
                    root_0 = (Tree)adaptor.nil();


                    INT71=(Token)match(input,INT,FOLLOW_INT_in_attribNumInstance992); 
                    INT71_tree = 
                    (Tree)adaptor.create(INT71)
                    ;
                    adaptor.addChild(root_0, INT71_tree);


                    }
                    break;
                case 2 :
                    // Velvet.g:164:4: name
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_name_in_attribNumInstance999);
                    name72=name();

                    state._fsp--;

                    adaptor.addChild(root_0, name72.getTree());

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
    // Velvet.g:167:1: attribute : ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) ;
    public final VelvetParser.attribute_return attribute() throws RecognitionException {
        VelvetParser.attribute_return retval = new VelvetParser.attribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token SEMI77=null;
        VelvetParser.intAttribute_return intAttribute73 =null;

        VelvetParser.floatAttribute_return floatAttribute74 =null;

        VelvetParser.stringAttribute_return stringAttribute75 =null;

        VelvetParser.boolAttribute_return boolAttribute76 =null;


        Tree SEMI77_tree=null;
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_intAttribute=new RewriteRuleSubtreeStream(adaptor,"rule intAttribute");
        RewriteRuleSubtreeStream stream_stringAttribute=new RewriteRuleSubtreeStream(adaptor,"rule stringAttribute");
        RewriteRuleSubtreeStream stream_floatAttribute=new RewriteRuleSubtreeStream(adaptor,"rule floatAttribute");
        RewriteRuleSubtreeStream stream_boolAttribute=new RewriteRuleSubtreeStream(adaptor,"rule boolAttribute");
        try {
            // Velvet.g:168:2: ( ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) )
            // Velvet.g:168:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI
            {
            // Velvet.g:168:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute )
            int alt22=4;
            switch ( input.LA(1) ) {
            case VAR_INT:
                {
                alt22=1;
                }
                break;
            case VAR_FLOAT:
                {
                alt22=2;
                }
                break;
            case VAR_STRING:
                {
                alt22=3;
                }
                break;
            case VAR_BOOL:
                {
                alt22=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 22, 0, input);

                throw nvae;

            }

            switch (alt22) {
                case 1 :
                    // Velvet.g:168:5: intAttribute
                    {
                    pushFollow(FOLLOW_intAttribute_in_attribute1011);
                    intAttribute73=intAttribute();

                    state._fsp--;

                    stream_intAttribute.add(intAttribute73.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:168:20: floatAttribute
                    {
                    pushFollow(FOLLOW_floatAttribute_in_attribute1015);
                    floatAttribute74=floatAttribute();

                    state._fsp--;

                    stream_floatAttribute.add(floatAttribute74.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:168:37: stringAttribute
                    {
                    pushFollow(FOLLOW_stringAttribute_in_attribute1019);
                    stringAttribute75=stringAttribute();

                    state._fsp--;

                    stream_stringAttribute.add(stringAttribute75.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:168:55: boolAttribute
                    {
                    pushFollow(FOLLOW_boolAttribute_in_attribute1023);
                    boolAttribute76=boolAttribute();

                    state._fsp--;

                    stream_boolAttribute.add(boolAttribute76.getTree());

                    }
                    break;

            }


            SEMI77=(Token)match(input,SEMI,FOLLOW_SEMI_in_attribute1026);  
            stream_SEMI.add(SEMI77);


            // AST REWRITE
            // elements: stringAttribute, intAttribute, boolAttribute, floatAttribute
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 169:2: -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
            {
                // Velvet.g:169:5: ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(ATTR, "ATTR")
                , root_1);

                // Velvet.g:169:12: ( intAttribute )?
                if ( stream_intAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_intAttribute.nextTree());

                }
                stream_intAttribute.reset();

                // Velvet.g:169:26: ( floatAttribute )?
                if ( stream_floatAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_floatAttribute.nextTree());

                }
                stream_floatAttribute.reset();

                // Velvet.g:169:42: ( stringAttribute )?
                if ( stream_stringAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_stringAttribute.nextTree());

                }
                stream_stringAttribute.reset();

                // Velvet.g:169:59: ( boolAttribute )?
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
    // Velvet.g:172:1: intAttribute : VAR_INT ! name ( EQ ! INT )? ;
    public final VelvetParser.intAttribute_return intAttribute() throws RecognitionException {
        VelvetParser.intAttribute_return retval = new VelvetParser.intAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_INT78=null;
        Token EQ80=null;
        Token INT81=null;
        VelvetParser.name_return name79 =null;


        Tree VAR_INT78_tree=null;
        Tree EQ80_tree=null;
        Tree INT81_tree=null;

        try {
            // Velvet.g:172:13: ( VAR_INT ! name ( EQ ! INT )? )
            // Velvet.g:172:16: VAR_INT ! name ( EQ ! INT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_INT78=(Token)match(input,VAR_INT,FOLLOW_VAR_INT_in_intAttribute1055); 

            pushFollow(FOLLOW_name_in_intAttribute1058);
            name79=name();

            state._fsp--;

            adaptor.addChild(root_0, name79.getTree());

            // Velvet.g:172:30: ( EQ ! INT )?
            int alt23=2;
            int LA23_0 = input.LA(1);

            if ( (LA23_0==EQ) ) {
                alt23=1;
            }
            switch (alt23) {
                case 1 :
                    // Velvet.g:172:31: EQ ! INT
                    {
                    EQ80=(Token)match(input,EQ,FOLLOW_EQ_in_intAttribute1061); 

                    INT81=(Token)match(input,INT,FOLLOW_INT_in_intAttribute1064); 
                    INT81_tree = 
                    (Tree)adaptor.create(INT81)
                    ;
                    adaptor.addChild(root_0, INT81_tree);


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
    // Velvet.g:173:1: floatAttribute : VAR_FLOAT ! name ( EQ ! FLOAT )? ;
    public final VelvetParser.floatAttribute_return floatAttribute() throws RecognitionException {
        VelvetParser.floatAttribute_return retval = new VelvetParser.floatAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_FLOAT82=null;
        Token EQ84=null;
        Token FLOAT85=null;
        VelvetParser.name_return name83 =null;


        Tree VAR_FLOAT82_tree=null;
        Tree EQ84_tree=null;
        Tree FLOAT85_tree=null;

        try {
            // Velvet.g:173:15: ( VAR_FLOAT ! name ( EQ ! FLOAT )? )
            // Velvet.g:173:18: VAR_FLOAT ! name ( EQ ! FLOAT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_FLOAT82=(Token)match(input,VAR_FLOAT,FOLLOW_VAR_FLOAT_in_floatAttribute1073); 

            pushFollow(FOLLOW_name_in_floatAttribute1076);
            name83=name();

            state._fsp--;

            adaptor.addChild(root_0, name83.getTree());

            // Velvet.g:173:34: ( EQ ! FLOAT )?
            int alt24=2;
            int LA24_0 = input.LA(1);

            if ( (LA24_0==EQ) ) {
                alt24=1;
            }
            switch (alt24) {
                case 1 :
                    // Velvet.g:173:35: EQ ! FLOAT
                    {
                    EQ84=(Token)match(input,EQ,FOLLOW_EQ_in_floatAttribute1079); 

                    FLOAT85=(Token)match(input,FLOAT,FOLLOW_FLOAT_in_floatAttribute1082); 
                    FLOAT85_tree = 
                    (Tree)adaptor.create(FLOAT85)
                    ;
                    adaptor.addChild(root_0, FLOAT85_tree);


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
    // Velvet.g:174:1: stringAttribute : VAR_STRING ! name ( EQ ! STRING )? ;
    public final VelvetParser.stringAttribute_return stringAttribute() throws RecognitionException {
        VelvetParser.stringAttribute_return retval = new VelvetParser.stringAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_STRING86=null;
        Token EQ88=null;
        Token STRING89=null;
        VelvetParser.name_return name87 =null;


        Tree VAR_STRING86_tree=null;
        Tree EQ88_tree=null;
        Tree STRING89_tree=null;

        try {
            // Velvet.g:174:16: ( VAR_STRING ! name ( EQ ! STRING )? )
            // Velvet.g:174:18: VAR_STRING ! name ( EQ ! STRING )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_STRING86=(Token)match(input,VAR_STRING,FOLLOW_VAR_STRING_in_stringAttribute1090); 

            pushFollow(FOLLOW_name_in_stringAttribute1093);
            name87=name();

            state._fsp--;

            adaptor.addChild(root_0, name87.getTree());

            // Velvet.g:174:35: ( EQ ! STRING )?
            int alt25=2;
            int LA25_0 = input.LA(1);

            if ( (LA25_0==EQ) ) {
                alt25=1;
            }
            switch (alt25) {
                case 1 :
                    // Velvet.g:174:36: EQ ! STRING
                    {
                    EQ88=(Token)match(input,EQ,FOLLOW_EQ_in_stringAttribute1096); 

                    STRING89=(Token)match(input,STRING,FOLLOW_STRING_in_stringAttribute1099); 
                    STRING89_tree = 
                    (Tree)adaptor.create(STRING89)
                    ;
                    adaptor.addChild(root_0, STRING89_tree);


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
    // Velvet.g:175:1: boolAttribute : VAR_BOOL ! name ( EQ ! BOOLEAN )? ;
    public final VelvetParser.boolAttribute_return boolAttribute() throws RecognitionException {
        VelvetParser.boolAttribute_return retval = new VelvetParser.boolAttribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token VAR_BOOL90=null;
        Token EQ92=null;
        Token BOOLEAN93=null;
        VelvetParser.name_return name91 =null;


        Tree VAR_BOOL90_tree=null;
        Tree EQ92_tree=null;
        Tree BOOLEAN93_tree=null;

        try {
            // Velvet.g:175:14: ( VAR_BOOL ! name ( EQ ! BOOLEAN )? )
            // Velvet.g:175:17: VAR_BOOL ! name ( EQ ! BOOLEAN )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_BOOL90=(Token)match(input,VAR_BOOL,FOLLOW_VAR_BOOL_in_boolAttribute1108); 

            pushFollow(FOLLOW_name_in_boolAttribute1111);
            name91=name();

            state._fsp--;

            adaptor.addChild(root_0, name91.getTree());

            // Velvet.g:175:32: ( EQ ! BOOLEAN )?
            int alt26=2;
            int LA26_0 = input.LA(1);

            if ( (LA26_0==EQ) ) {
                alt26=1;
            }
            switch (alt26) {
                case 1 :
                    // Velvet.g:175:33: EQ ! BOOLEAN
                    {
                    EQ92=(Token)match(input,EQ,FOLLOW_EQ_in_boolAttribute1114); 

                    BOOLEAN93=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_boolAttribute1117); 
                    BOOLEAN93_tree = 
                    (Tree)adaptor.create(BOOLEAN93)
                    ;
                    adaptor.addChild(root_0, BOOLEAN93_tree);


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
    // Velvet.g:177:1: unaryOp : OP_NOT ;
    public final VelvetParser.unaryOp_return unaryOp() throws RecognitionException {
        VelvetParser.unaryOp_return retval = new VelvetParser.unaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token OP_NOT94=null;

        Tree OP_NOT94_tree=null;

        try {
            // Velvet.g:178:2: ( OP_NOT )
            // Velvet.g:178:4: OP_NOT
            {
            root_0 = (Tree)adaptor.nil();


            OP_NOT94=(Token)match(input,OP_NOT,FOLLOW_OP_NOT_in_unaryOp1129); 
            OP_NOT94_tree = 
            (Tree)adaptor.create(OP_NOT94)
            ;
            adaptor.addChild(root_0, OP_NOT94_tree);


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
    // Velvet.g:181:1: binaryOp : ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT );
    public final VelvetParser.binaryOp_return binaryOp() throws RecognitionException {
        VelvetParser.binaryOp_return retval = new VelvetParser.binaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set95=null;

        Tree set95_tree=null;

        try {
            // Velvet.g:182:2: ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set95=(Token)input.LT(1);

            if ( (input.LA(1) >= OP_AND && input.LA(1) <= OP_IMPLIES)||(input.LA(1) >= OP_OR && input.LA(1) <= OP_XOR) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set95)
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
    // Velvet.g:189:1: attribRelation : ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ );
    public final VelvetParser.attribRelation_return attribRelation() throws RecognitionException {
        VelvetParser.attribRelation_return retval = new VelvetParser.attribRelation_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set96=null;

        Tree set96_tree=null;

        try {
            // Velvet.g:190:2: ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set96=(Token)input.LT(1);

            if ( input.LA(1)==ATTR_OP_EQUALS||input.LA(1)==ATTR_OP_GREATER_EQ||input.LA(1)==ATTR_OP_LESS_EQ ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set96)
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


 

    public static final BitSet FOLLOW_imports_in_velvetModel438 = new BitSet(new long[]{0x0002000000020000L});
    public static final BitSet FOLLOW_concept_in_velvetModel441 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_velvetModel443 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IMPORT_in_imports455 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_imports457 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_SEMI_in_imports459 = new BitSet(new long[]{0x0000000400000002L});
    public static final BitSet FOLLOW_REFINES_in_concept482 = new BitSet(new long[]{0x0000000000020000L});
    public static final BitSet FOLLOW_CONCEPT_in_concept485 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_concept487 = new BitSet(new long[]{0x0010000000008000L});
    public static final BitSet FOLLOW_COLON_in_concept491 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_conceptBaseExt_in_concept493 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_definitions_in_concept497 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt527 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_COMMA_in_conceptBaseExt530 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt532 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_START_C_in_definitions572 = new BitSet(new long[]{0x1E08012088280010L});
    public static final BitSet FOLLOW_def_in_definitions574 = new BitSet(new long[]{0x0000000000200000L});
    public static final BitSet FOLLOW_END_C_in_definitions576 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def595 = new BitSet(new long[]{0x1E08012088080012L});
    public static final BitSet FOLLOW_featureGroup_in_def603 = new BitSet(new long[]{0x1E00000080080002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def605 = new BitSet(new long[]{0x1E00000080080002L});
    public static final BitSet FOLLOW_feature_in_def614 = new BitSet(new long[]{0x1E00002088080012L});
    public static final BitSet FOLLOW_feature_in_def617 = new BitSet(new long[]{0x1E00002088080012L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_def621 = new BitSet(new long[]{0x1E00002088080012L});
    public static final BitSet FOLLOW_constraint_in_nonFeatureDefinition641 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_instance_in_nonFeatureDefinition647 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribute_in_nonFeatureDefinition653 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_instance664 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_instance666 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_SEMI_in_instance668 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANDATORY_in_feature690 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature692 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature696 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature698 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature702 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature706 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_FEATURE_in_feature713 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_feature715 = new BitSet(new long[]{0x0014000000000000L});
    public static final BitSet FOLLOW_definitions_in_feature718 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SEMI_in_feature722 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_groupType_in_featureGroup753 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_START_C_in_featureGroup755 = new BitSet(new long[]{0x0000002008000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup757 = new BitSet(new long[]{0x0000002008000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup759 = new BitSet(new long[]{0x0000002008200010L});
    public static final BitSet FOLLOW_END_C_in_featureGroup762 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONSTRAINT_in_constraint805 = new BitSet(new long[]{0x0020201180000000L});
    public static final BitSet FOLLOW_ID_in_constraint809 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_EQ_in_constraint811 = new BitSet(new long[]{0x0020201180000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraint817 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_attributeConstraint_in_constraint821 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_SEMI_in_constraint824 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition837 = new BitSet(new long[]{0x0000DC0000000002L});
    public static final BitSet FOLLOW_binaryOp_in_constraintDefinition840 = new BitSet(new long[]{0x0020200180000000L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition842 = new BitSet(new long[]{0x0000DC0000000002L});
    public static final BitSet FOLLOW_unaryOp_in_constraintOperand869 = new BitSet(new long[]{0x0020200180000000L});
    public static final BitSet FOLLOW_START_R_in_constraintOperand873 = new BitSet(new long[]{0x0020200180000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraintOperand875 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_END_R_in_constraintOperand877 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_constraintOperand881 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribConstraint_in_attributeConstraint916 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint936 = new BitSet(new long[]{0x0001004000000A80L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint939 = new BitSet(new long[]{0x0000001180000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint941 = new BitSet(new long[]{0x0001004000000A80L});
    public static final BitSet FOLLOW_attribRelation_in_attribConstraint949 = new BitSet(new long[]{0x0000001180000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint955 = new BitSet(new long[]{0x0001004000000002L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint958 = new BitSet(new long[]{0x0000001180000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint960 = new BitSet(new long[]{0x0001004000000002L});
    public static final BitSet FOLLOW_INT_in_attribNumInstance992 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_attribNumInstance999 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_intAttribute_in_attribute1011 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_floatAttribute_in_attribute1015 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_stringAttribute_in_attribute1019 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_boolAttribute_in_attribute1023 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_SEMI_in_attribute1026 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_INT_in_intAttribute1055 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_intAttribute1058 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_EQ_in_intAttribute1061 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_intAttribute1064 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_FLOAT_in_floatAttribute1073 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_floatAttribute1076 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_EQ_in_floatAttribute1079 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_FLOAT_in_floatAttribute1082 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_STRING_in_stringAttribute1090 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_stringAttribute1093 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_EQ_in_stringAttribute1096 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_STRING_in_stringAttribute1099 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_BOOL_in_boolAttribute1108 = new BitSet(new long[]{0x0000000180000000L});
    public static final BitSet FOLLOW_name_in_boolAttribute1111 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_EQ_in_boolAttribute1114 = new BitSet(new long[]{0x0000000000004000L});
    public static final BitSet FOLLOW_BOOLEAN_in_boolAttribute1117 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_OP_NOT_in_unaryOp1129 = new BitSet(new long[]{0x0000000000000002L});

}