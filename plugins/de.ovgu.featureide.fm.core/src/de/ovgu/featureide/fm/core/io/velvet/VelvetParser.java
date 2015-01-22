/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
// $ANTLR 3.4 Velvet.g 2014-11-23 20:46:35

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
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "ABSTRACT", "ACONSTR", "ATTR", "ATTR_OP_EQUALS", "ATTR_OP_GREATER", "ATTR_OP_GREATER_EQ", "ATTR_OP_LESS", "ATTR_OP_LESS_EQ", "ATTR_OP_NOT_EQUALS", "BASEEXT", "BOOLEAN", "CINTERFACE", "COLON", "COMMA", "CONCEPT", "CONSTR", "CONSTRAINT", "DEF", "DESCRIPTION", "EMPTY", "END_C", "END_R", "EQ", "ESC_SEQ", "EXPONENT", "FEATURE", "FLOAT", "GROUP", "HEX_DIGIT", "ID", "IDPath", "IMPORTINSTANCE", "IMPORTINTERFACE", "INT", "MANDATORY", "MINUS", "ML_COMMENT", "OCTAL_ESC", "ONEOF", "OPERAND", "OP_AND", "OP_EQUIVALENT", "OP_IMPLIES", "OP_NOT", "OP_OR", "OP_XOR", "PLUS", "SEMI", "SL_COMMENT", "SOMEOF", "START_C", "START_R", "STRING", "UNARYOP", "UNICODE_ESC", "USE", "VAR_BOOL", "VAR_FLOAT", "VAR_INT", "VAR_STRING", "WS"
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
    public static final int DESCRIPTION=22;
    public static final int EMPTY=23;
    public static final int END_C=24;
    public static final int END_R=25;
    public static final int EQ=26;
    public static final int ESC_SEQ=27;
    public static final int EXPONENT=28;
    public static final int FEATURE=29;
    public static final int FLOAT=30;
    public static final int GROUP=31;
    public static final int HEX_DIGIT=32;
    public static final int ID=33;
    public static final int IDPath=34;
    public static final int IMPORTINSTANCE=35;
    public static final int IMPORTINTERFACE=36;
    public static final int INT=37;
    public static final int MANDATORY=38;
    public static final int MINUS=39;
    public static final int ML_COMMENT=40;
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
    public static final int SL_COMMENT=52;
    public static final int SOMEOF=53;
    public static final int START_C=54;
    public static final int START_R=55;
    public static final int STRING=56;
    public static final int UNARYOP=57;
    public static final int UNICODE_ESC=58;
    public static final int USE=59;
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
    // Velvet.g:76:1: velvetModel : ( concept | cinterface ) EOF ;
    public final VelvetParser.velvetModel_return velvetModel() throws RecognitionException {
        VelvetParser.velvetModel_return retval = new VelvetParser.velvetModel_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token EOF3=null;
        VelvetParser.concept_return concept1 =null;

        VelvetParser.cinterface_return cinterface2 =null;


        Tree EOF3_tree=null;

        try {
            // Velvet.g:77:2: ( ( concept | cinterface ) EOF )
            // Velvet.g:77:4: ( concept | cinterface ) EOF
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:77:4: ( concept | cinterface )
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
                    // Velvet.g:77:5: concept
                    {
                    pushFollow(FOLLOW_concept_in_velvetModel462);
                    concept1=concept();

                    state._fsp--;

                    adaptor.addChild(root_0, concept1.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:77:13: cinterface
                    {
                    pushFollow(FOLLOW_cinterface_in_velvetModel464);
                    cinterface2=cinterface();

                    state._fsp--;

                    adaptor.addChild(root_0, cinterface2.getTree());

                    }
                    break;

            }


            EOF3=(Token)match(input,EOF,FOLLOW_EOF_in_velvetModel467); 
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
    // Velvet.g:80:1: concept : CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )? ( definitions )? -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? ) ;
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
            // Velvet.g:81:2: ( CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )? ( definitions )? -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? ) )
            // Velvet.g:81:4: CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )? ( definitions )?
            {
            CONCEPT4=(Token)match(input,CONCEPT,FOLLOW_CONCEPT_in_concept480);  
            stream_CONCEPT.add(CONCEPT4);


            ID5=(Token)match(input,ID,FOLLOW_ID_in_concept482);  
            stream_ID.add(ID5);


            // Velvet.g:82:3: ( COLON conceptBaseExt )?
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0==COLON) ) {
                alt2=1;
            }
            switch (alt2) {
                case 1 :
                    // Velvet.g:82:4: COLON conceptBaseExt
                    {
                    COLON6=(Token)match(input,COLON,FOLLOW_COLON_in_concept489);  
                    stream_COLON.add(COLON6);


                    pushFollow(FOLLOW_conceptBaseExt_in_concept491);
                    conceptBaseExt7=conceptBaseExt();

                    state._fsp--;

                    stream_conceptBaseExt.add(conceptBaseExt7.getTree());

                    }
                    break;

            }


            // Velvet.g:82:27: ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )?
            int alt3=5;
            alt3 = dfa3.predict(input);
            switch (alt3) {
                case 1 :
                    // Velvet.g:82:28: instanceImports interfaceImports
                    {
                    pushFollow(FOLLOW_instanceImports_in_concept496);
                    instanceImports8=instanceImports();

                    state._fsp--;

                    stream_instanceImports.add(instanceImports8.getTree());

                    pushFollow(FOLLOW_interfaceImports_in_concept498);
                    interfaceImports9=interfaceImports();

                    state._fsp--;

                    stream_interfaceImports.add(interfaceImports9.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:82:63: interfaceImports instanceImports
                    {
                    pushFollow(FOLLOW_interfaceImports_in_concept502);
                    interfaceImports10=interfaceImports();

                    state._fsp--;

                    stream_interfaceImports.add(interfaceImports10.getTree());

                    pushFollow(FOLLOW_instanceImports_in_concept504);
                    instanceImports11=instanceImports();

                    state._fsp--;

                    stream_instanceImports.add(instanceImports11.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:82:98: interfaceImports
                    {
                    pushFollow(FOLLOW_interfaceImports_in_concept508);
                    interfaceImports12=interfaceImports();

                    state._fsp--;

                    stream_interfaceImports.add(interfaceImports12.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:82:117: instanceImports
                    {
                    pushFollow(FOLLOW_instanceImports_in_concept512);
                    instanceImports13=instanceImports();

                    state._fsp--;

                    stream_instanceImports.add(instanceImports13.getTree());

                    }
                    break;

            }


            // Velvet.g:83:3: ( definitions )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0==START_C) ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // Velvet.g:83:3: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_concept519);
                    definitions14=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions14.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: instanceImports, definitions, conceptBaseExt, interfaceImports, CONCEPT, ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 84:2: -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? )
            {
                // Velvet.g:84:5: ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CONCEPT.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:84:18: ( conceptBaseExt )?
                if ( stream_conceptBaseExt.hasNext() ) {
                    adaptor.addChild(root_1, stream_conceptBaseExt.nextTree());

                }
                stream_conceptBaseExt.reset();

                // Velvet.g:84:34: ( instanceImports )?
                if ( stream_instanceImports.hasNext() ) {
                    adaptor.addChild(root_1, stream_instanceImports.nextTree());

                }
                stream_instanceImports.reset();

                // Velvet.g:84:51: ( interfaceImports )?
                if ( stream_interfaceImports.hasNext() ) {
                    adaptor.addChild(root_1, stream_interfaceImports.nextTree());

                }
                stream_interfaceImports.reset();

                // Velvet.g:84:69: ( definitions )?
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


    public static class cinterface_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "cinterface"
    // Velvet.g:87:1: cinterface : CINTERFACE ID ( COLON conceptBaseExt )? definitions -> ^( CINTERFACE ID ( conceptBaseExt )? definitions ) ;
    public final VelvetParser.cinterface_return cinterface() throws RecognitionException {
        VelvetParser.cinterface_return retval = new VelvetParser.cinterface_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token CINTERFACE15=null;
        Token ID16=null;
        Token COLON17=null;
        VelvetParser.conceptBaseExt_return conceptBaseExt18 =null;

        VelvetParser.definitions_return definitions19 =null;


        Tree CINTERFACE15_tree=null;
        Tree ID16_tree=null;
        Tree COLON17_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_CINTERFACE=new RewriteRuleTokenStream(adaptor,"token CINTERFACE");
        RewriteRuleSubtreeStream stream_conceptBaseExt=new RewriteRuleSubtreeStream(adaptor,"rule conceptBaseExt");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:87:12: ( CINTERFACE ID ( COLON conceptBaseExt )? definitions -> ^( CINTERFACE ID ( conceptBaseExt )? definitions ) )
            // Velvet.g:87:14: CINTERFACE ID ( COLON conceptBaseExt )? definitions
            {
            CINTERFACE15=(Token)match(input,CINTERFACE,FOLLOW_CINTERFACE_in_cinterface552);  
            stream_CINTERFACE.add(CINTERFACE15);


            ID16=(Token)match(input,ID,FOLLOW_ID_in_cinterface554);  
            stream_ID.add(ID16);


            // Velvet.g:87:29: ( COLON conceptBaseExt )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==COLON) ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // Velvet.g:87:30: COLON conceptBaseExt
                    {
                    COLON17=(Token)match(input,COLON,FOLLOW_COLON_in_cinterface558);  
                    stream_COLON.add(COLON17);


                    pushFollow(FOLLOW_conceptBaseExt_in_cinterface560);
                    conceptBaseExt18=conceptBaseExt();

                    state._fsp--;

                    stream_conceptBaseExt.add(conceptBaseExt18.getTree());

                    }
                    break;

            }


            pushFollow(FOLLOW_definitions_in_cinterface564);
            definitions19=definitions();

            state._fsp--;

            stream_definitions.add(definitions19.getTree());

            // AST REWRITE
            // elements: ID, conceptBaseExt, CINTERFACE, definitions
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 88:2: -> ^( CINTERFACE ID ( conceptBaseExt )? definitions )
            {
                // Velvet.g:88:5: ^( CINTERFACE ID ( conceptBaseExt )? definitions )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_CINTERFACE.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_ID.nextNode()
                );

                // Velvet.g:88:21: ( conceptBaseExt )?
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
    // $ANTLR end "cinterface"


    public static class conceptBaseExt_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "conceptBaseExt"
    // Velvet.g:91:1: conceptBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
    public final VelvetParser.conceptBaseExt_return conceptBaseExt() throws RecognitionException {
        VelvetParser.conceptBaseExt_return retval = new VelvetParser.conceptBaseExt_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token ID20=null;
        Token COMMA21=null;
        Token ID22=null;

        Tree ID20_tree=null;
        Tree COMMA21_tree=null;
        Tree ID22_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

        try {
            // Velvet.g:92:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
            // Velvet.g:92:4: ID ( COMMA ID )*
            {
            ID20=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt591);  
            stream_ID.add(ID20);


            // Velvet.g:92:7: ( COMMA ID )*
            loop6:
            do {
                int alt6=2;
                int LA6_0 = input.LA(1);

                if ( (LA6_0==COMMA) ) {
                    alt6=1;
                }


                switch (alt6) {
            	case 1 :
            	    // Velvet.g:92:8: COMMA ID
            	    {
            	    COMMA21=(Token)match(input,COMMA,FOLLOW_COMMA_in_conceptBaseExt594);  
            	    stream_COMMA.add(COMMA21);


            	    ID22=(Token)match(input,ID,FOLLOW_ID_in_conceptBaseExt596);  
            	    stream_ID.add(ID22);


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
            // 93:2: -> ^( BASEEXT ( ID )+ )
            {
                // Velvet.g:93:5: ^( BASEEXT ( ID )+ )
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
    // Velvet.g:96:1: instanceImports : IMPORTINSTANCE ID name ( COMMA ID name )* -> ^( IMPORTINSTANCE ( ID name )+ ) ;
    public final VelvetParser.instanceImports_return instanceImports() throws RecognitionException {
        VelvetParser.instanceImports_return retval = new VelvetParser.instanceImports_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token IMPORTINSTANCE23=null;
        Token ID24=null;
        Token COMMA26=null;
        Token ID27=null;
        VelvetParser.name_return name25 =null;

        VelvetParser.name_return name28 =null;


        Tree IMPORTINSTANCE23_tree=null;
        Tree ID24_tree=null;
        Tree COMMA26_tree=null;
        Tree ID27_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
        RewriteRuleTokenStream stream_IMPORTINSTANCE=new RewriteRuleTokenStream(adaptor,"token IMPORTINSTANCE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:97:2: ( IMPORTINSTANCE ID name ( COMMA ID name )* -> ^( IMPORTINSTANCE ( ID name )+ ) )
            // Velvet.g:97:4: IMPORTINSTANCE ID name ( COMMA ID name )*
            {
            IMPORTINSTANCE23=(Token)match(input,IMPORTINSTANCE,FOLLOW_IMPORTINSTANCE_in_instanceImports621);  
            stream_IMPORTINSTANCE.add(IMPORTINSTANCE23);


            ID24=(Token)match(input,ID,FOLLOW_ID_in_instanceImports623);  
            stream_ID.add(ID24);


            pushFollow(FOLLOW_name_in_instanceImports625);
            name25=name();

            state._fsp--;

            stream_name.add(name25.getTree());

            // Velvet.g:97:27: ( COMMA ID name )*
            loop7:
            do {
                int alt7=2;
                int LA7_0 = input.LA(1);

                if ( (LA7_0==COMMA) ) {
                    alt7=1;
                }


                switch (alt7) {
            	case 1 :
            	    // Velvet.g:97:28: COMMA ID name
            	    {
            	    COMMA26=(Token)match(input,COMMA,FOLLOW_COMMA_in_instanceImports628);  
            	    stream_COMMA.add(COMMA26);


            	    ID27=(Token)match(input,ID,FOLLOW_ID_in_instanceImports630);  
            	    stream_ID.add(ID27);


            	    pushFollow(FOLLOW_name_in_instanceImports632);
            	    name28=name();

            	    state._fsp--;

            	    stream_name.add(name28.getTree());

            	    }
            	    break;

            	default :
            	    break loop7;
                }
            } while (true);


            // AST REWRITE
            // elements: ID, name, IMPORTINSTANCE
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 98:2: -> ^( IMPORTINSTANCE ( ID name )+ )
            {
                // Velvet.g:98:5: ^( IMPORTINSTANCE ( ID name )+ )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_IMPORTINSTANCE.nextNode()
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
    // Velvet.g:101:1: interfaceImports : IMPORTINTERFACE ID name ( COMMA ID name )* -> ^( IMPORTINTERFACE ( ID name )+ ) ;
    public final VelvetParser.interfaceImports_return interfaceImports() throws RecognitionException {
        VelvetParser.interfaceImports_return retval = new VelvetParser.interfaceImports_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token IMPORTINTERFACE29=null;
        Token ID30=null;
        Token COMMA32=null;
        Token ID33=null;
        VelvetParser.name_return name31 =null;

        VelvetParser.name_return name34 =null;


        Tree IMPORTINTERFACE29_tree=null;
        Tree ID30_tree=null;
        Tree COMMA32_tree=null;
        Tree ID33_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
        RewriteRuleTokenStream stream_IMPORTINTERFACE=new RewriteRuleTokenStream(adaptor,"token IMPORTINTERFACE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:102:2: ( IMPORTINTERFACE ID name ( COMMA ID name )* -> ^( IMPORTINTERFACE ( ID name )+ ) )
            // Velvet.g:102:4: IMPORTINTERFACE ID name ( COMMA ID name )*
            {
            IMPORTINTERFACE29=(Token)match(input,IMPORTINTERFACE,FOLLOW_IMPORTINTERFACE_in_interfaceImports661);  
            stream_IMPORTINTERFACE.add(IMPORTINTERFACE29);


            ID30=(Token)match(input,ID,FOLLOW_ID_in_interfaceImports663);  
            stream_ID.add(ID30);


            pushFollow(FOLLOW_name_in_interfaceImports665);
            name31=name();

            state._fsp--;

            stream_name.add(name31.getTree());

            // Velvet.g:102:28: ( COMMA ID name )*
            loop8:
            do {
                int alt8=2;
                int LA8_0 = input.LA(1);

                if ( (LA8_0==COMMA) ) {
                    alt8=1;
                }


                switch (alt8) {
            	case 1 :
            	    // Velvet.g:102:29: COMMA ID name
            	    {
            	    COMMA32=(Token)match(input,COMMA,FOLLOW_COMMA_in_interfaceImports668);  
            	    stream_COMMA.add(COMMA32);


            	    ID33=(Token)match(input,ID,FOLLOW_ID_in_interfaceImports670);  
            	    stream_ID.add(ID33);


            	    pushFollow(FOLLOW_name_in_interfaceImports672);
            	    name34=name();

            	    state._fsp--;

            	    stream_name.add(name34.getTree());

            	    }
            	    break;

            	default :
            	    break loop8;
                }
            } while (true);


            // AST REWRITE
            // elements: IMPORTINTERFACE, name, ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 103:2: -> ^( IMPORTINTERFACE ( ID name )+ )
            {
                // Velvet.g:103:5: ^( IMPORTINTERFACE ( ID name )+ )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_IMPORTINTERFACE.nextNode()
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


    public static class name_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "name"
    // Velvet.g:106:1: name : ( ID | IDPath );
    public final VelvetParser.name_return name() throws RecognitionException {
        VelvetParser.name_return retval = new VelvetParser.name_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set35=null;

        Tree set35_tree=null;

        try {
            // Velvet.g:106:5: ( ID | IDPath )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set35=(Token)input.LT(1);

            if ( (input.LA(1) >= ID && input.LA(1) <= IDPath) ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set35)
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
    // Velvet.g:110:1: definitions : START_C definition END_C -> ^( DEF ( definition )? EMPTY ) ;
    public final VelvetParser.definitions_return definitions() throws RecognitionException {
        VelvetParser.definitions_return retval = new VelvetParser.definitions_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C36=null;
        Token END_C38=null;
        VelvetParser.definition_return definition37 =null;


        Tree START_C36_tree=null;
        Tree END_C38_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_definition=new RewriteRuleSubtreeStream(adaptor,"rule definition");
        try {
            // Velvet.g:111:2: ( START_C definition END_C -> ^( DEF ( definition )? EMPTY ) )
            // Velvet.g:111:4: START_C definition END_C
            {
            START_C36=(Token)match(input,START_C,FOLLOW_START_C_in_definitions716);  
            stream_START_C.add(START_C36);


            pushFollow(FOLLOW_definition_in_definitions718);
            definition37=definition();

            state._fsp--;

            stream_definition.add(definition37.getTree());

            END_C38=(Token)match(input,END_C,FOLLOW_END_C_in_definitions720);  
            stream_END_C.add(END_C38);


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
            // 112:2: -> ^( DEF ( definition )? EMPTY )
            {
                // Velvet.g:112:5: ^( DEF ( definition )? EMPTY )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(DEF, "DEF")
                , root_1);

                // Velvet.g:112:11: ( definition )?
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
    // Velvet.g:115:1: definition : ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? ;
    public final VelvetParser.definition_return definition() throws RecognitionException {
        VelvetParser.definition_return retval = new VelvetParser.definition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition39 =null;

        VelvetParser.featureGroup_return featureGroup40 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition41 =null;

        VelvetParser.feature_return feature42 =null;

        VelvetParser.feature_return feature43 =null;

        VelvetParser.nonFeatureDefinition_return nonFeatureDefinition44 =null;



        try {
            // Velvet.g:116:2: ( ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? )
            // Velvet.g:116:4: ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            {
            root_0 = (Tree)adaptor.nil();


            // Velvet.g:116:4: ( nonFeatureDefinition )*
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( (LA9_0==CONSTRAINT||LA9_0==DESCRIPTION||(LA9_0 >= USE && LA9_0 <= VAR_STRING)) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // Velvet.g:116:4: nonFeatureDefinition
            	    {
            	    pushFollow(FOLLOW_nonFeatureDefinition_in_definition744);
            	    nonFeatureDefinition39=nonFeatureDefinition();

            	    state._fsp--;

            	    adaptor.addChild(root_0, nonFeatureDefinition39.getTree());

            	    }
            	    break;

            	default :
            	    break loop9;
                }
            } while (true);


            // Velvet.g:116:26: ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
            int alt12=3;
            int LA12_0 = input.LA(1);

            if ( (LA12_0==ONEOF||LA12_0==SOMEOF) ) {
                alt12=1;
            }
            else if ( (LA12_0==ABSTRACT||LA12_0==FEATURE||LA12_0==MANDATORY) ) {
                alt12=2;
            }
            switch (alt12) {
                case 1 :
                    // Velvet.g:117:3: ( featureGroup ( nonFeatureDefinition )* )
                    {
                    // Velvet.g:117:3: ( featureGroup ( nonFeatureDefinition )* )
                    // Velvet.g:117:4: featureGroup ( nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_featureGroup_in_definition752);
                    featureGroup40=featureGroup();

                    state._fsp--;

                    adaptor.addChild(root_0, featureGroup40.getTree());

                    // Velvet.g:117:17: ( nonFeatureDefinition )*
                    loop10:
                    do {
                        int alt10=2;
                        int LA10_0 = input.LA(1);

                        if ( (LA10_0==CONSTRAINT||LA10_0==DESCRIPTION||(LA10_0 >= USE && LA10_0 <= VAR_STRING)) ) {
                            alt10=1;
                        }


                        switch (alt10) {
                    	case 1 :
                    	    // Velvet.g:117:17: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_definition754);
                    	    nonFeatureDefinition41=nonFeatureDefinition();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, nonFeatureDefinition41.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop10;
                        }
                    } while (true);


                    }


                    }
                    break;
                case 2 :
                    // Velvet.g:117:42: ( feature ( feature | nonFeatureDefinition )* )
                    {
                    // Velvet.g:117:42: ( feature ( feature | nonFeatureDefinition )* )
                    // Velvet.g:117:43: feature ( feature | nonFeatureDefinition )*
                    {
                    pushFollow(FOLLOW_feature_in_definition761);
                    feature42=feature();

                    state._fsp--;

                    adaptor.addChild(root_0, feature42.getTree());

                    // Velvet.g:117:51: ( feature | nonFeatureDefinition )*
                    loop11:
                    do {
                        int alt11=3;
                        int LA11_0 = input.LA(1);

                        if ( (LA11_0==ABSTRACT||LA11_0==FEATURE||LA11_0==MANDATORY) ) {
                            alt11=1;
                        }
                        else if ( (LA11_0==CONSTRAINT||LA11_0==DESCRIPTION||(LA11_0 >= USE && LA11_0 <= VAR_STRING)) ) {
                            alt11=2;
                        }


                        switch (alt11) {
                    	case 1 :
                    	    // Velvet.g:117:52: feature
                    	    {
                    	    pushFollow(FOLLOW_feature_in_definition764);
                    	    feature43=feature();

                    	    state._fsp--;

                    	    adaptor.addChild(root_0, feature43.getTree());

                    	    }
                    	    break;
                    	case 2 :
                    	    // Velvet.g:117:62: nonFeatureDefinition
                    	    {
                    	    pushFollow(FOLLOW_nonFeatureDefinition_in_definition768);
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
    // Velvet.g:121:1: nonFeatureDefinition : ( constraint | use | attribute | description );
    public final VelvetParser.nonFeatureDefinition_return nonFeatureDefinition() throws RecognitionException {
        VelvetParser.nonFeatureDefinition_return retval = new VelvetParser.nonFeatureDefinition_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.constraint_return constraint45 =null;

        VelvetParser.use_return use46 =null;

        VelvetParser.attribute_return attribute47 =null;

        VelvetParser.description_return description48 =null;



        try {
            // Velvet.g:122:2: ( constraint | use | attribute | description )
            int alt13=4;
            switch ( input.LA(1) ) {
            case CONSTRAINT:
                {
                alt13=1;
                }
                break;
            case USE:
                {
                alt13=2;
                }
                break;
            case VAR_BOOL:
            case VAR_FLOAT:
            case VAR_INT:
            case VAR_STRING:
                {
                alt13=3;
                }
                break;
            case DESCRIPTION:
                {
                alt13=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 13, 0, input);

                throw nvae;

            }

            switch (alt13) {
                case 1 :
                    // Velvet.g:122:4: constraint
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_constraint_in_nonFeatureDefinition790);
                    constraint45=constraint();

                    state._fsp--;

                    adaptor.addChild(root_0, constraint45.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:123:4: use
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_use_in_nonFeatureDefinition795);
                    use46=use();

                    state._fsp--;

                    adaptor.addChild(root_0, use46.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:124:4: attribute
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_attribute_in_nonFeatureDefinition800);
                    attribute47=attribute();

                    state._fsp--;

                    adaptor.addChild(root_0, attribute47.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:125:4: description
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_description_in_nonFeatureDefinition806);
                    description48=description();

                    state._fsp--;

                    adaptor.addChild(root_0, description48.getTree());

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
    // Velvet.g:128:1: use : USE name SEMI -> ^( USE name ) ;
    public final VelvetParser.use_return use() throws RecognitionException {
        VelvetParser.use_return retval = new VelvetParser.use_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token USE49=null;
        Token SEMI51=null;
        VelvetParser.name_return name50 =null;


        Tree USE49_tree=null;
        Tree SEMI51_tree=null;
        RewriteRuleTokenStream stream_USE=new RewriteRuleTokenStream(adaptor,"token USE");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        try {
            // Velvet.g:128:5: ( USE name SEMI -> ^( USE name ) )
            // Velvet.g:128:7: USE name SEMI
            {
            USE49=(Token)match(input,USE,FOLLOW_USE_in_use817);  
            stream_USE.add(USE49);


            pushFollow(FOLLOW_name_in_use819);
            name50=name();

            state._fsp--;

            stream_name.add(name50.getTree());

            SEMI51=(Token)match(input,SEMI,FOLLOW_SEMI_in_use821);  
            stream_SEMI.add(SEMI51);


            // AST REWRITE
            // elements: name, USE
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 129:2: -> ^( USE name )
            {
                // Velvet.g:129:5: ^( USE name )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_USE.nextNode()
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
    // Velvet.g:132:1: feature : ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEATURE name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) ;
    public final VelvetParser.feature_return feature() throws RecognitionException {
        VelvetParser.feature_return retval = new VelvetParser.feature_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token MANDATORY52=null;
        Token ABSTRACT53=null;
        Token ABSTRACT54=null;
        Token MANDATORY55=null;
        Token MANDATORY56=null;
        Token ABSTRACT57=null;
        Token FEATURE58=null;
        Token SEMI61=null;
        VelvetParser.name_return name59 =null;

        VelvetParser.definitions_return definitions60 =null;


        Tree MANDATORY52_tree=null;
        Tree ABSTRACT53_tree=null;
        Tree ABSTRACT54_tree=null;
        Tree MANDATORY55_tree=null;
        Tree MANDATORY56_tree=null;
        Tree ABSTRACT57_tree=null;
        Tree FEATURE58_tree=null;
        Tree SEMI61_tree=null;
        RewriteRuleTokenStream stream_ABSTRACT=new RewriteRuleTokenStream(adaptor,"token ABSTRACT");
        RewriteRuleTokenStream stream_MANDATORY=new RewriteRuleTokenStream(adaptor,"token MANDATORY");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleTokenStream stream_FEATURE=new RewriteRuleTokenStream(adaptor,"token FEATURE");
        RewriteRuleSubtreeStream stream_name=new RewriteRuleSubtreeStream(adaptor,"rule name");
        RewriteRuleSubtreeStream stream_definitions=new RewriteRuleSubtreeStream(adaptor,"rule definitions");
        try {
            // Velvet.g:133:2: ( ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEATURE name ( MANDATORY )? ( ABSTRACT )? ( definitions )? ) )
            // Velvet.g:133:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI )
            {
            // Velvet.g:133:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )?
            int alt14=5;
            int LA14_0 = input.LA(1);

            if ( (LA14_0==MANDATORY) ) {
                int LA14_1 = input.LA(2);

                if ( (LA14_1==ABSTRACT) ) {
                    alt14=1;
                }
                else if ( (LA14_1==FEATURE) ) {
                    alt14=3;
                }
            }
            else if ( (LA14_0==ABSTRACT) ) {
                int LA14_2 = input.LA(2);

                if ( (LA14_2==MANDATORY) ) {
                    alt14=2;
                }
                else if ( (LA14_2==FEATURE) ) {
                    alt14=4;
                }
            }
            switch (alt14) {
                case 1 :
                    // Velvet.g:133:5: MANDATORY ABSTRACT
                    {
                    MANDATORY52=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature842);  
                    stream_MANDATORY.add(MANDATORY52);


                    ABSTRACT53=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature844);  
                    stream_ABSTRACT.add(ABSTRACT53);


                    }
                    break;
                case 2 :
                    // Velvet.g:133:26: ABSTRACT MANDATORY
                    {
                    ABSTRACT54=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature848);  
                    stream_ABSTRACT.add(ABSTRACT54);


                    MANDATORY55=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature850);  
                    stream_MANDATORY.add(MANDATORY55);


                    }
                    break;
                case 3 :
                    // Velvet.g:133:47: MANDATORY
                    {
                    MANDATORY56=(Token)match(input,MANDATORY,FOLLOW_MANDATORY_in_feature854);  
                    stream_MANDATORY.add(MANDATORY56);


                    }
                    break;
                case 4 :
                    // Velvet.g:133:59: ABSTRACT
                    {
                    ABSTRACT57=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_feature858);  
                    stream_ABSTRACT.add(ABSTRACT57);


                    }
                    break;

            }


            FEATURE58=(Token)match(input,FEATURE,FOLLOW_FEATURE_in_feature865);  
            stream_FEATURE.add(FEATURE58);


            pushFollow(FOLLOW_name_in_feature867);
            name59=name();

            state._fsp--;

            stream_name.add(name59.getTree());

            // Velvet.g:134:17: ( definitions | SEMI )
            int alt15=2;
            int LA15_0 = input.LA(1);

            if ( (LA15_0==START_C) ) {
                alt15=1;
            }
            else if ( (LA15_0==SEMI) ) {
                alt15=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 15, 0, input);

                throw nvae;

            }
            switch (alt15) {
                case 1 :
                    // Velvet.g:134:18: definitions
                    {
                    pushFollow(FOLLOW_definitions_in_feature870);
                    definitions60=definitions();

                    state._fsp--;

                    stream_definitions.add(definitions60.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:134:32: SEMI
                    {
                    SEMI61=(Token)match(input,SEMI,FOLLOW_SEMI_in_feature874);  
                    stream_SEMI.add(SEMI61);


                    }
                    break;

            }


            // AST REWRITE
            // elements: MANDATORY, name, FEATURE, definitions, ABSTRACT
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 135:2: -> ^( FEATURE name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
            {
                // Velvet.g:135:5: ^( FEATURE name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_FEATURE.nextNode()
                , root_1);

                adaptor.addChild(root_1, stream_name.nextTree());

                // Velvet.g:135:20: ( MANDATORY )?
                if ( stream_MANDATORY.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_MANDATORY.nextNode()
                    );

                }
                stream_MANDATORY.reset();

                // Velvet.g:135:31: ( ABSTRACT )?
                if ( stream_ABSTRACT.hasNext() ) {
                    adaptor.addChild(root_1, 
                    stream_ABSTRACT.nextNode()
                    );

                }
                stream_ABSTRACT.reset();

                // Velvet.g:135:41: ( definitions )?
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
    // Velvet.g:138:1: featureGroup : groupType START_C ( feature )+ END_C -> ^( GROUP groupType ( feature )+ ) ;
    public final VelvetParser.featureGroup_return featureGroup() throws RecognitionException {
        VelvetParser.featureGroup_return retval = new VelvetParser.featureGroup_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token START_C63=null;
        Token END_C65=null;
        VelvetParser.groupType_return groupType62 =null;

        VelvetParser.feature_return feature64 =null;


        Tree START_C63_tree=null;
        Tree END_C65_tree=null;
        RewriteRuleTokenStream stream_END_C=new RewriteRuleTokenStream(adaptor,"token END_C");
        RewriteRuleTokenStream stream_START_C=new RewriteRuleTokenStream(adaptor,"token START_C");
        RewriteRuleSubtreeStream stream_groupType=new RewriteRuleSubtreeStream(adaptor,"rule groupType");
        RewriteRuleSubtreeStream stream_feature=new RewriteRuleSubtreeStream(adaptor,"rule feature");
        try {
            // Velvet.g:139:2: ( groupType START_C ( feature )+ END_C -> ^( GROUP groupType ( feature )+ ) )
            // Velvet.g:139:4: groupType START_C ( feature )+ END_C
            {
            pushFollow(FOLLOW_groupType_in_featureGroup905);
            groupType62=groupType();

            state._fsp--;

            stream_groupType.add(groupType62.getTree());

            START_C63=(Token)match(input,START_C,FOLLOW_START_C_in_featureGroup907);  
            stream_START_C.add(START_C63);


            // Velvet.g:139:22: ( feature )+
            int cnt16=0;
            loop16:
            do {
                int alt16=2;
                int LA16_0 = input.LA(1);

                if ( (LA16_0==ABSTRACT||LA16_0==FEATURE||LA16_0==MANDATORY) ) {
                    alt16=1;
                }


                switch (alt16) {
            	case 1 :
            	    // Velvet.g:139:22: feature
            	    {
            	    pushFollow(FOLLOW_feature_in_featureGroup909);
            	    feature64=feature();

            	    state._fsp--;

            	    stream_feature.add(feature64.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt16 >= 1 ) break loop16;
                        EarlyExitException eee =
                            new EarlyExitException(16, input);
                        throw eee;
                }
                cnt16++;
            } while (true);


            END_C65=(Token)match(input,END_C,FOLLOW_END_C_in_featureGroup912);  
            stream_END_C.add(END_C65);


            // AST REWRITE
            // elements: groupType, feature
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 140:2: -> ^( GROUP groupType ( feature )+ )
            {
                // Velvet.g:140:5: ^( GROUP groupType ( feature )+ )
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
    // Velvet.g:143:1: groupType : ( SOMEOF | ONEOF );
    public final VelvetParser.groupType_return groupType() throws RecognitionException {
        VelvetParser.groupType_return retval = new VelvetParser.groupType_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set66=null;

        Tree set66_tree=null;

        try {
            // Velvet.g:144:2: ( SOMEOF | ONEOF )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set66=(Token)input.LT(1);

            if ( input.LA(1)==ONEOF||input.LA(1)==SOMEOF ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set66)
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


    public static class description_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "description"
    // Velvet.g:148:1: description : DESCRIPTION STRING SEMI -> ^( DESCRIPTION STRING ) ;
    public final VelvetParser.description_return description() throws RecognitionException {
        VelvetParser.description_return retval = new VelvetParser.description_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token DESCRIPTION67=null;
        Token STRING68=null;
        Token SEMI69=null;

        Tree DESCRIPTION67_tree=null;
        Tree STRING68_tree=null;
        Tree SEMI69_tree=null;
        RewriteRuleTokenStream stream_DESCRIPTION=new RewriteRuleTokenStream(adaptor,"token DESCRIPTION");
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleTokenStream stream_STRING=new RewriteRuleTokenStream(adaptor,"token STRING");

        try {
            // Velvet.g:149:2: ( DESCRIPTION STRING SEMI -> ^( DESCRIPTION STRING ) )
            // Velvet.g:149:4: DESCRIPTION STRING SEMI
            {
            DESCRIPTION67=(Token)match(input,DESCRIPTION,FOLLOW_DESCRIPTION_in_description954);  
            stream_DESCRIPTION.add(DESCRIPTION67);


            STRING68=(Token)match(input,STRING,FOLLOW_STRING_in_description956);  
            stream_STRING.add(STRING68);


            SEMI69=(Token)match(input,SEMI,FOLLOW_SEMI_in_description958);  
            stream_SEMI.add(SEMI69);


            // AST REWRITE
            // elements: DESCRIPTION, STRING
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 150:2: -> ^( DESCRIPTION STRING )
            {
                // Velvet.g:150:5: ^( DESCRIPTION STRING )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                stream_DESCRIPTION.nextNode()
                , root_1);

                adaptor.addChild(root_1, 
                stream_STRING.nextNode()
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
    // $ANTLR end "description"


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
            // Velvet.g:154:2: ( CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !)
            // Velvet.g:154:4: CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !
            {
            root_0 = (Tree)adaptor.nil();


            CONSTRAINT70=(Token)match(input,CONSTRAINT,FOLLOW_CONSTRAINT_in_constraint979); 
            CONSTRAINT70_tree = 
            (Tree)adaptor.create(CONSTRAINT70)
            ;
            root_0 = (Tree)adaptor.becomeRoot(CONSTRAINT70_tree, root_0);


            // Velvet.g:154:16: ( ID EQ !)?
            int alt17=2;
            int LA17_0 = input.LA(1);

            if ( (LA17_0==ID) ) {
                int LA17_1 = input.LA(2);

                if ( (LA17_1==EQ) ) {
                    alt17=1;
                }
            }
            switch (alt17) {
                case 1 :
                    // Velvet.g:154:17: ID EQ !
                    {
                    ID71=(Token)match(input,ID,FOLLOW_ID_in_constraint983); 
                    ID71_tree = 
                    (Tree)adaptor.create(ID71)
                    ;
                    adaptor.addChild(root_0, ID71_tree);


                    EQ72=(Token)match(input,EQ,FOLLOW_EQ_in_constraint985); 

                    }
                    break;

            }


            // Velvet.g:154:26: ( constraintDefinition | attributeConstraint )
            int alt18=2;
            switch ( input.LA(1) ) {
            case OP_NOT:
            case START_R:
                {
                alt18=1;
                }
                break;
            case ID:
            case IDPath:
                {
                int LA18_2 = input.LA(2);

                if ( ((LA18_2 >= OP_AND && LA18_2 <= OP_IMPLIES)||(LA18_2 >= OP_OR && LA18_2 <= OP_XOR)||LA18_2==SEMI) ) {
                    alt18=1;
                }
                else if ( (LA18_2==ATTR_OP_EQUALS||LA18_2==ATTR_OP_GREATER_EQ||LA18_2==ATTR_OP_LESS_EQ||LA18_2==MINUS||LA18_2==PLUS) ) {
                    alt18=2;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 18, 2, input);

                    throw nvae;

                }
                }
                break;
            case INT:
                {
                alt18=2;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 18, 0, input);

                throw nvae;

            }

            switch (alt18) {
                case 1 :
                    // Velvet.g:154:27: constraintDefinition
                    {
                    pushFollow(FOLLOW_constraintDefinition_in_constraint991);
                    constraintDefinition73=constraintDefinition();

                    state._fsp--;

                    adaptor.addChild(root_0, constraintDefinition73.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:154:50: attributeConstraint
                    {
                    pushFollow(FOLLOW_attributeConstraint_in_constraint995);
                    attributeConstraint74=attributeConstraint();

                    state._fsp--;

                    adaptor.addChild(root_0, attributeConstraint74.getTree());

                    }
                    break;

            }


            SEMI75=(Token)match(input,SEMI,FOLLOW_SEMI_in_constraint998); 

            }

            retval.stop = input.LT(-1);


            retval.tree = (Tree)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
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

        VelvetParser.constraintOperand_return constraintOperand76 =null;

        VelvetParser.binaryOp_return binaryOp77 =null;

        VelvetParser.constraintOperand_return constraintOperand78 =null;


        RewriteRuleSubtreeStream stream_constraintOperand=new RewriteRuleSubtreeStream(adaptor,"rule constraintOperand");
        RewriteRuleSubtreeStream stream_binaryOp=new RewriteRuleSubtreeStream(adaptor,"rule binaryOp");
        try {
            // Velvet.g:158:2: ( constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) )
            // Velvet.g:158:4: constraintOperand ( binaryOp constraintOperand )*
            {
            pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1011);
            constraintOperand76=constraintOperand();

            state._fsp--;

            stream_constraintOperand.add(constraintOperand76.getTree());

            // Velvet.g:158:22: ( binaryOp constraintOperand )*
            loop19:
            do {
                int alt19=2;
                int LA19_0 = input.LA(1);

                if ( ((LA19_0 >= OP_AND && LA19_0 <= OP_IMPLIES)||(LA19_0 >= OP_OR && LA19_0 <= OP_XOR)) ) {
                    alt19=1;
                }


                switch (alt19) {
            	case 1 :
            	    // Velvet.g:158:23: binaryOp constraintOperand
            	    {
            	    pushFollow(FOLLOW_binaryOp_in_constraintDefinition1014);
            	    binaryOp77=binaryOp();

            	    state._fsp--;

            	    stream_binaryOp.add(binaryOp77.getTree());

            	    pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1016);
            	    constraintOperand78=constraintOperand();

            	    state._fsp--;

            	    stream_constraintOperand.add(constraintOperand78.getTree());

            	    }
            	    break;

            	default :
            	    break loop19;
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
            // Velvet.g:162:19: ( ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )? )
            // Velvet.g:162:21: ( unaryOp )* ( START_R constraintDefinition END_R | name )
            {
            // Velvet.g:162:21: ( unaryOp )*
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( (LA20_0==OP_NOT) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // Velvet.g:162:21: unaryOp
            	    {
            	    pushFollow(FOLLOW_unaryOp_in_constraintOperand1043);
            	    unaryOp79=unaryOp();

            	    state._fsp--;

            	    stream_unaryOp.add(unaryOp79.getTree());

            	    }
            	    break;

            	default :
            	    break loop20;
                }
            } while (true);


            // Velvet.g:162:30: ( START_R constraintDefinition END_R | name )
            int alt21=2;
            int LA21_0 = input.LA(1);

            if ( (LA21_0==START_R) ) {
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
                    // Velvet.g:162:31: START_R constraintDefinition END_R
                    {
                    START_R80=(Token)match(input,START_R,FOLLOW_START_R_in_constraintOperand1047);  
                    stream_START_R.add(START_R80);


                    pushFollow(FOLLOW_constraintDefinition_in_constraintOperand1049);
                    constraintDefinition81=constraintDefinition();

                    state._fsp--;

                    stream_constraintDefinition.add(constraintDefinition81.getTree());

                    END_R82=(Token)match(input,END_R,FOLLOW_END_R_in_constraintOperand1051);  
                    stream_END_R.add(END_R82);


                    }
                    break;
                case 2 :
                    // Velvet.g:162:68: name
                    {
                    pushFollow(FOLLOW_name_in_constraintOperand1055);
                    name83=name();

                    state._fsp--;

                    stream_name.add(name83.getTree());

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


    public static class attribute_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "attribute"
    // Velvet.g:166:1: attribute : ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) ;
    public final VelvetParser.attribute_return attribute() throws RecognitionException {
        VelvetParser.attribute_return retval = new VelvetParser.attribute_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token SEMI88=null;
        VelvetParser.intAttribute_return intAttribute84 =null;

        VelvetParser.floatAttribute_return floatAttribute85 =null;

        VelvetParser.stringAttribute_return stringAttribute86 =null;

        VelvetParser.boolAttribute_return boolAttribute87 =null;


        Tree SEMI88_tree=null;
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_intAttribute=new RewriteRuleSubtreeStream(adaptor,"rule intAttribute");
        RewriteRuleSubtreeStream stream_stringAttribute=new RewriteRuleSubtreeStream(adaptor,"rule stringAttribute");
        RewriteRuleSubtreeStream stream_floatAttribute=new RewriteRuleSubtreeStream(adaptor,"rule floatAttribute");
        RewriteRuleSubtreeStream stream_boolAttribute=new RewriteRuleSubtreeStream(adaptor,"rule boolAttribute");
        try {
            // Velvet.g:167:2: ( ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? ) )
            // Velvet.g:167:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI
            {
            // Velvet.g:167:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute )
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
                    // Velvet.g:167:5: intAttribute
                    {
                    pushFollow(FOLLOW_intAttribute_in_attribute1091);
                    intAttribute84=intAttribute();

                    state._fsp--;

                    stream_intAttribute.add(intAttribute84.getTree());

                    }
                    break;
                case 2 :
                    // Velvet.g:167:20: floatAttribute
                    {
                    pushFollow(FOLLOW_floatAttribute_in_attribute1095);
                    floatAttribute85=floatAttribute();

                    state._fsp--;

                    stream_floatAttribute.add(floatAttribute85.getTree());

                    }
                    break;
                case 3 :
                    // Velvet.g:167:37: stringAttribute
                    {
                    pushFollow(FOLLOW_stringAttribute_in_attribute1099);
                    stringAttribute86=stringAttribute();

                    state._fsp--;

                    stream_stringAttribute.add(stringAttribute86.getTree());

                    }
                    break;
                case 4 :
                    // Velvet.g:167:55: boolAttribute
                    {
                    pushFollow(FOLLOW_boolAttribute_in_attribute1103);
                    boolAttribute87=boolAttribute();

                    state._fsp--;

                    stream_boolAttribute.add(boolAttribute87.getTree());

                    }
                    break;

            }


            SEMI88=(Token)match(input,SEMI,FOLLOW_SEMI_in_attribute1106);  
            stream_SEMI.add(SEMI88);


            // AST REWRITE
            // elements: boolAttribute, intAttribute, floatAttribute, stringAttribute
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Tree)adaptor.nil();
            // 168:2: -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
            {
                // Velvet.g:168:5: ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
                {
                Tree root_1 = (Tree)adaptor.nil();
                root_1 = (Tree)adaptor.becomeRoot(
                (Tree)adaptor.create(ATTR, "ATTR")
                , root_1);

                // Velvet.g:168:12: ( intAttribute )?
                if ( stream_intAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_intAttribute.nextTree());

                }
                stream_intAttribute.reset();

                // Velvet.g:168:26: ( floatAttribute )?
                if ( stream_floatAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_floatAttribute.nextTree());

                }
                stream_floatAttribute.reset();

                // Velvet.g:168:42: ( stringAttribute )?
                if ( stream_stringAttribute.hasNext() ) {
                    adaptor.addChild(root_1, stream_stringAttribute.nextTree());

                }
                stream_stringAttribute.reset();

                // Velvet.g:168:59: ( boolAttribute )?
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


    public static class attributeConstraint_return extends ParserRuleReturnScope {
        Tree tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "attributeConstraint"
    // Velvet.g:171:1: attributeConstraint : attribConstraint -> ^( ACONSTR attribConstraint ) ;
    public final VelvetParser.attributeConstraint_return attributeConstraint() throws RecognitionException {
        VelvetParser.attributeConstraint_return retval = new VelvetParser.attributeConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribConstraint_return attribConstraint89 =null;


        RewriteRuleSubtreeStream stream_attribConstraint=new RewriteRuleSubtreeStream(adaptor,"rule attribConstraint");
        try {
            // Velvet.g:172:2: ( attribConstraint -> ^( ACONSTR attribConstraint ) )
            // Velvet.g:172:4: attribConstraint
            {
            pushFollow(FOLLOW_attribConstraint_in_attributeConstraint1137);
            attribConstraint89=attribConstraint();

            state._fsp--;

            stream_attribConstraint.add(attribConstraint89.getTree());

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
            // 173:2: -> ^( ACONSTR attribConstraint )
            {
                // Velvet.g:173:5: ^( ACONSTR attribConstraint )
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
    // Velvet.g:176:1: attribConstraint : attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* ;
    public final VelvetParser.attribConstraint_return attribConstraint() throws RecognitionException {
        VelvetParser.attribConstraint_return retval = new VelvetParser.attribConstraint_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        VelvetParser.attribNumInstance_return attribNumInstance90 =null;

        VelvetParser.attribOperator_return attribOperator91 =null;

        VelvetParser.attribNumInstance_return attribNumInstance92 =null;

        VelvetParser.attribRelation_return attribRelation93 =null;

        VelvetParser.attribNumInstance_return attribNumInstance94 =null;

        VelvetParser.attribOperator_return attribOperator95 =null;

        VelvetParser.attribNumInstance_return attribNumInstance96 =null;



        try {
            // Velvet.g:177:2: ( attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )* )
            // Velvet.g:177:4: attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )*
            {
            root_0 = (Tree)adaptor.nil();


            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1157);
            attribNumInstance90=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance90.getTree());

            // Velvet.g:177:22: ( attribOperator attribNumInstance )*
            loop23:
            do {
                int alt23=2;
                int LA23_0 = input.LA(1);

                if ( (LA23_0==MINUS||LA23_0==PLUS) ) {
                    alt23=1;
                }


                switch (alt23) {
            	case 1 :
            	    // Velvet.g:177:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1160);
            	    attribOperator91=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator91.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1162);
            	    attribNumInstance92=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance92.getTree());

            	    }
            	    break;

            	default :
            	    break loop23;
                }
            } while (true);


            pushFollow(FOLLOW_attribRelation_in_attribConstraint1170);
            attribRelation93=attribRelation();

            state._fsp--;

            adaptor.addChild(root_0, attribRelation93.getTree());

            pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1176);
            attribNumInstance94=attribNumInstance();

            state._fsp--;

            adaptor.addChild(root_0, attribNumInstance94.getTree());

            // Velvet.g:179:22: ( attribOperator attribNumInstance )*
            loop24:
            do {
                int alt24=2;
                int LA24_0 = input.LA(1);

                if ( (LA24_0==MINUS||LA24_0==PLUS) ) {
                    alt24=1;
                }


                switch (alt24) {
            	case 1 :
            	    // Velvet.g:179:23: attribOperator attribNumInstance
            	    {
            	    pushFollow(FOLLOW_attribOperator_in_attribConstraint1179);
            	    attribOperator95=attribOperator();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribOperator95.getTree());

            	    pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1181);
            	    attribNumInstance96=attribNumInstance();

            	    state._fsp--;

            	    adaptor.addChild(root_0, attribNumInstance96.getTree());

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
    // Velvet.g:182:1: attribOperator : ( PLUS | MINUS );
    public final VelvetParser.attribOperator_return attribOperator() throws RecognitionException {
        VelvetParser.attribOperator_return retval = new VelvetParser.attribOperator_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set97=null;

        Tree set97_tree=null;

        try {
            // Velvet.g:183:2: ( PLUS | MINUS )
            // Velvet.g:
            {
            root_0 = (Tree)adaptor.nil();


            set97=(Token)input.LT(1);

            if ( input.LA(1)==MINUS||input.LA(1)==PLUS ) {
                input.consume();
                adaptor.addChild(root_0, 
                (Tree)adaptor.create(set97)
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
    // Velvet.g:187:1: attribNumInstance : ( INT | name );
    public final VelvetParser.attribNumInstance_return attribNumInstance() throws RecognitionException {
        VelvetParser.attribNumInstance_return retval = new VelvetParser.attribNumInstance_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token INT98=null;
        VelvetParser.name_return name99 =null;


        Tree INT98_tree=null;

        try {
            // Velvet.g:188:2: ( INT | name )
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
                    // Velvet.g:188:4: INT
                    {
                    root_0 = (Tree)adaptor.nil();


                    INT98=(Token)match(input,INT,FOLLOW_INT_in_attribNumInstance1213); 
                    INT98_tree = 
                    (Tree)adaptor.create(INT98)
                    ;
                    adaptor.addChild(root_0, INT98_tree);


                    }
                    break;
                case 2 :
                    // Velvet.g:190:4: name
                    {
                    root_0 = (Tree)adaptor.nil();


                    pushFollow(FOLLOW_name_in_attribNumInstance1220);
                    name99=name();

                    state._fsp--;

                    adaptor.addChild(root_0, name99.getTree());

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

        Token VAR_INT100=null;
        Token EQ102=null;
        Token INT103=null;
        VelvetParser.name_return name101 =null;


        Tree VAR_INT100_tree=null;
        Tree EQ102_tree=null;
        Tree INT103_tree=null;

        try {
            // Velvet.g:193:13: ( VAR_INT ! name ( EQ ! INT )? )
            // Velvet.g:193:16: VAR_INT ! name ( EQ ! INT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_INT100=(Token)match(input,VAR_INT,FOLLOW_VAR_INT_in_intAttribute1230); 

            pushFollow(FOLLOW_name_in_intAttribute1233);
            name101=name();

            state._fsp--;

            adaptor.addChild(root_0, name101.getTree());

            // Velvet.g:193:30: ( EQ ! INT )?
            int alt26=2;
            int LA26_0 = input.LA(1);

            if ( (LA26_0==EQ) ) {
                alt26=1;
            }
            switch (alt26) {
                case 1 :
                    // Velvet.g:193:31: EQ ! INT
                    {
                    EQ102=(Token)match(input,EQ,FOLLOW_EQ_in_intAttribute1236); 

                    INT103=(Token)match(input,INT,FOLLOW_INT_in_intAttribute1239); 
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
    // Velvet.g:194:1: floatAttribute : VAR_FLOAT ! name ( EQ ! FLOAT )? ;
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
            // Velvet.g:194:15: ( VAR_FLOAT ! name ( EQ ! FLOAT )? )
            // Velvet.g:194:18: VAR_FLOAT ! name ( EQ ! FLOAT )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_FLOAT104=(Token)match(input,VAR_FLOAT,FOLLOW_VAR_FLOAT_in_floatAttribute1248); 

            pushFollow(FOLLOW_name_in_floatAttribute1251);
            name105=name();

            state._fsp--;

            adaptor.addChild(root_0, name105.getTree());

            // Velvet.g:194:34: ( EQ ! FLOAT )?
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==EQ) ) {
                alt27=1;
            }
            switch (alt27) {
                case 1 :
                    // Velvet.g:194:35: EQ ! FLOAT
                    {
                    EQ106=(Token)match(input,EQ,FOLLOW_EQ_in_floatAttribute1254); 

                    FLOAT107=(Token)match(input,FLOAT,FOLLOW_FLOAT_in_floatAttribute1257); 
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
    // Velvet.g:195:1: stringAttribute : VAR_STRING ! name ( EQ ! STRING )? ;
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
            // Velvet.g:195:16: ( VAR_STRING ! name ( EQ ! STRING )? )
            // Velvet.g:195:18: VAR_STRING ! name ( EQ ! STRING )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_STRING108=(Token)match(input,VAR_STRING,FOLLOW_VAR_STRING_in_stringAttribute1265); 

            pushFollow(FOLLOW_name_in_stringAttribute1268);
            name109=name();

            state._fsp--;

            adaptor.addChild(root_0, name109.getTree());

            // Velvet.g:195:35: ( EQ ! STRING )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==EQ) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // Velvet.g:195:36: EQ ! STRING
                    {
                    EQ110=(Token)match(input,EQ,FOLLOW_EQ_in_stringAttribute1271); 

                    STRING111=(Token)match(input,STRING,FOLLOW_STRING_in_stringAttribute1274); 
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
    // Velvet.g:196:1: boolAttribute : VAR_BOOL ! name ( EQ ! BOOLEAN )? ;
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
            // Velvet.g:196:14: ( VAR_BOOL ! name ( EQ ! BOOLEAN )? )
            // Velvet.g:196:17: VAR_BOOL ! name ( EQ ! BOOLEAN )?
            {
            root_0 = (Tree)adaptor.nil();


            VAR_BOOL112=(Token)match(input,VAR_BOOL,FOLLOW_VAR_BOOL_in_boolAttribute1283); 

            pushFollow(FOLLOW_name_in_boolAttribute1286);
            name113=name();

            state._fsp--;

            adaptor.addChild(root_0, name113.getTree());

            // Velvet.g:196:32: ( EQ ! BOOLEAN )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==EQ) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // Velvet.g:196:33: EQ ! BOOLEAN
                    {
                    EQ114=(Token)match(input,EQ,FOLLOW_EQ_in_boolAttribute1289); 

                    BOOLEAN115=(Token)match(input,BOOLEAN,FOLLOW_BOOLEAN_in_boolAttribute1292); 
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
    // Velvet.g:198:1: unaryOp : OP_NOT ;
    public final VelvetParser.unaryOp_return unaryOp() throws RecognitionException {
        VelvetParser.unaryOp_return retval = new VelvetParser.unaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token OP_NOT116=null;

        Tree OP_NOT116_tree=null;

        try {
            // Velvet.g:199:2: ( OP_NOT )
            // Velvet.g:199:4: OP_NOT
            {
            root_0 = (Tree)adaptor.nil();


            OP_NOT116=(Token)match(input,OP_NOT,FOLLOW_OP_NOT_in_unaryOp1304); 
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
    // Velvet.g:202:1: binaryOp : ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT );
    public final VelvetParser.binaryOp_return binaryOp() throws RecognitionException {
        VelvetParser.binaryOp_return retval = new VelvetParser.binaryOp_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set117=null;

        Tree set117_tree=null;

        try {
            // Velvet.g:203:2: ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT )
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
    // Velvet.g:210:1: attribRelation : ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ );
    public final VelvetParser.attribRelation_return attribRelation() throws RecognitionException {
        VelvetParser.attribRelation_return retval = new VelvetParser.attribRelation_return();
        retval.start = input.LT(1);


        Tree root_0 = null;

        Token set118=null;

        Tree set118_tree=null;

        try {
            // Velvet.g:211:2: ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ )
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
        "\1\43\2\41\1\uffff\2\41\2\21\1\41\2\uffff\1\41\2\uffff\2\41\2\21";
    static final String DFA3_maxS =
        "\1\66\2\41\1\uffff\2\42\2\66\1\41\2\uffff\1\41\2\uffff\2\42\2\66";
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
            "\1\10\22\uffff\1\11\21\uffff\1\12",
            "\1\13\21\uffff\1\14\22\uffff\1\15",
            "\1\16",
            "",
            "",
            "\1\17",
            "",
            "",
            "\2\20",
            "\2\21",
            "\1\10\22\uffff\1\11\21\uffff\1\12",
            "\1\13\21\uffff\1\14\22\uffff\1\15"
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
            return "82:27: ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )?";
        }
    }
 

    public static final BitSet FOLLOW_concept_in_velvetModel462 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_cinterface_in_velvetModel464 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_velvetModel467 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONCEPT_in_concept480 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_concept482 = new BitSet(new long[]{0x0040001800010002L});
    public static final BitSet FOLLOW_COLON_in_concept489 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_conceptBaseExt_in_concept491 = new BitSet(new long[]{0x0040001800000002L});
    public static final BitSet FOLLOW_instanceImports_in_concept496 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_interfaceImports_in_concept498 = new BitSet(new long[]{0x0040000000000002L});
    public static final BitSet FOLLOW_interfaceImports_in_concept502 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_instanceImports_in_concept504 = new BitSet(new long[]{0x0040000000000002L});
    public static final BitSet FOLLOW_interfaceImports_in_concept508 = new BitSet(new long[]{0x0040000000000002L});
    public static final BitSet FOLLOW_instanceImports_in_concept512 = new BitSet(new long[]{0x0040000000000002L});
    public static final BitSet FOLLOW_definitions_in_concept519 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CINTERFACE_in_cinterface552 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_cinterface554 = new BitSet(new long[]{0x0040000000010000L});
    public static final BitSet FOLLOW_COLON_in_cinterface558 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_conceptBaseExt_in_cinterface560 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_definitions_in_cinterface564 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt591 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_conceptBaseExt594 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_conceptBaseExt596 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_IMPORTINSTANCE_in_instanceImports621 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_instanceImports623 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_instanceImports625 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_instanceImports628 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_instanceImports630 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_instanceImports632 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_IMPORTINTERFACE_in_interfaceImports661 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_interfaceImports663 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_interfaceImports665 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_COMMA_in_interfaceImports668 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_ID_in_interfaceImports670 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_interfaceImports672 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_START_C_in_definitions716 = new BitSet(new long[]{0xF820044021500010L});
    public static final BitSet FOLLOW_definition_in_definitions718 = new BitSet(new long[]{0x0000000001000000L});
    public static final BitSet FOLLOW_END_C_in_definitions720 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_definition744 = new BitSet(new long[]{0xF820044020500012L});
    public static final BitSet FOLLOW_featureGroup_in_definition752 = new BitSet(new long[]{0xF800000000500002L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_definition754 = new BitSet(new long[]{0xF800000000500002L});
    public static final BitSet FOLLOW_feature_in_definition761 = new BitSet(new long[]{0xF800004020500012L});
    public static final BitSet FOLLOW_feature_in_definition764 = new BitSet(new long[]{0xF800004020500012L});
    public static final BitSet FOLLOW_nonFeatureDefinition_in_definition768 = new BitSet(new long[]{0xF800004020500012L});
    public static final BitSet FOLLOW_constraint_in_nonFeatureDefinition790 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_use_in_nonFeatureDefinition795 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribute_in_nonFeatureDefinition800 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_description_in_nonFeatureDefinition806 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_USE_in_use817 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_use819 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_use821 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANDATORY_in_feature842 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature844 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature848 = new BitSet(new long[]{0x0000004000000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature850 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_MANDATORY_in_feature854 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ABSTRACT_in_feature858 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_FEATURE_in_feature865 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_feature867 = new BitSet(new long[]{0x0048000000000000L});
    public static final BitSet FOLLOW_definitions_in_feature870 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SEMI_in_feature874 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_groupType_in_featureGroup905 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_START_C_in_featureGroup907 = new BitSet(new long[]{0x0000004020000010L});
    public static final BitSet FOLLOW_feature_in_featureGroup909 = new BitSet(new long[]{0x0000004021000010L});
    public static final BitSet FOLLOW_END_C_in_featureGroup912 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_DESCRIPTION_in_description954 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_STRING_in_description956 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_description958 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONSTRAINT_in_constraint979 = new BitSet(new long[]{0x0080802600000000L});
    public static final BitSet FOLLOW_ID_in_constraint983 = new BitSet(new long[]{0x0000000004000000L});
    public static final BitSet FOLLOW_EQ_in_constraint985 = new BitSet(new long[]{0x0080802600000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraint991 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_attributeConstraint_in_constraint995 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_constraint998 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1011 = new BitSet(new long[]{0x0003700000000002L});
    public static final BitSet FOLLOW_binaryOp_in_constraintDefinition1014 = new BitSet(new long[]{0x0080800600000000L});
    public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1016 = new BitSet(new long[]{0x0003700000000002L});
    public static final BitSet FOLLOW_unaryOp_in_constraintOperand1043 = new BitSet(new long[]{0x0080800600000000L});
    public static final BitSet FOLLOW_START_R_in_constraintOperand1047 = new BitSet(new long[]{0x0080800600000000L});
    public static final BitSet FOLLOW_constraintDefinition_in_constraintOperand1049 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_END_R_in_constraintOperand1051 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_constraintOperand1055 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_intAttribute_in_attribute1091 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_floatAttribute_in_attribute1095 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_stringAttribute_in_attribute1099 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_boolAttribute_in_attribute1103 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_SEMI_in_attribute1106 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribConstraint_in_attributeConstraint1137 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1157 = new BitSet(new long[]{0x0004008000000A80L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1160 = new BitSet(new long[]{0x0000002600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1162 = new BitSet(new long[]{0x0004008000000A80L});
    public static final BitSet FOLLOW_attribRelation_in_attribConstraint1170 = new BitSet(new long[]{0x0000002600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1176 = new BitSet(new long[]{0x0004008000000002L});
    public static final BitSet FOLLOW_attribOperator_in_attribConstraint1179 = new BitSet(new long[]{0x0000002600000000L});
    public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1181 = new BitSet(new long[]{0x0004008000000002L});
    public static final BitSet FOLLOW_INT_in_attribNumInstance1213 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_in_attribNumInstance1220 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_INT_in_intAttribute1230 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_intAttribute1233 = new BitSet(new long[]{0x0000000004000002L});
    public static final BitSet FOLLOW_EQ_in_intAttribute1236 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_INT_in_intAttribute1239 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_FLOAT_in_floatAttribute1248 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_floatAttribute1251 = new BitSet(new long[]{0x0000000004000002L});
    public static final BitSet FOLLOW_EQ_in_floatAttribute1254 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_FLOAT_in_floatAttribute1257 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_STRING_in_stringAttribute1265 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_stringAttribute1268 = new BitSet(new long[]{0x0000000004000002L});
    public static final BitSet FOLLOW_EQ_in_stringAttribute1271 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_STRING_in_stringAttribute1274 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_BOOL_in_boolAttribute1283 = new BitSet(new long[]{0x0000000600000000L});
    public static final BitSet FOLLOW_name_in_boolAttribute1286 = new BitSet(new long[]{0x0000000004000002L});
    public static final BitSet FOLLOW_EQ_in_boolAttribute1289 = new BitSet(new long[]{0x0000000000004000L});
    public static final BitSet FOLLOW_BOOLEAN_in_boolAttribute1292 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_OP_NOT_in_unaryOp1304 = new BitSet(new long[]{0x0000000000000002L});

}
