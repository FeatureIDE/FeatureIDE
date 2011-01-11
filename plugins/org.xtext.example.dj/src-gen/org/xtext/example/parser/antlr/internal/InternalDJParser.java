package org.xtext.example.parser.antlr.internal; 

import java.io.InputStream;
import org.eclipse.xtext.*;
import org.eclipse.xtext.parser.*;
import org.eclipse.xtext.parser.impl.*;
import org.eclipse.xtext.parsetree.*;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.parser.antlr.AbstractInternalAntlrParser;
import org.eclipse.xtext.parser.antlr.XtextTokenStream;
import org.eclipse.xtext.parser.antlr.XtextTokenStream.HiddenTokens;
import org.eclipse.xtext.parser.antlr.AntlrDatatypeRuleToken;
import org.eclipse.xtext.conversion.ValueConverterException;
import org.xtext.example.services.DJGrammarAccess;



import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

@SuppressWarnings("all")
public class InternalDJParser extends AbstractInternalAntlrParser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "RULE_STRING", "RULE_ID", "RULE_ALL", "RULE_INT", "RULE_ML_COMMENT", "RULE_SL_COMMENT", "RULE_WS", "RULE_ANY_OTHER", "'import'", "'features'", "','", "'configurations'", "'core'", "'delta'", "'{'", "'}'", "'class'", "'extends'", "'('", "')'", "'super'", "';'", "'this'", "'.'", "'='", "'return'", "'after'", "'when'", "'&&'", "'||'", "'->'", "'<->'", "'!'", "'modifies'", "'adds'", "'remove'", "'extending'", "'void'", "'int'", "'boolean'", "'<'", "'>'", "'new'", "'original'", "'null'"
    };
    public static final int RULE_ID=5;
    public static final int RULE_STRING=4;
    public static final int RULE_ANY_OTHER=11;
    public static final int RULE_INT=7;
    public static final int RULE_WS=10;
    public static final int RULE_SL_COMMENT=9;
    public static final int EOF=-1;
    public static final int RULE_ALL=6;
    public static final int RULE_ML_COMMENT=8;

        public InternalDJParser(TokenStream input) {
            super(input);
        }
        

    public String[] getTokenNames() { return tokenNames; }
    public String getGrammarFileName() { return "../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g"; }



     	private DJGrammarAccess grammarAccess;
     	
        public InternalDJParser(TokenStream input, IAstFactory factory, DJGrammarAccess grammarAccess) {
            this(input);
            this.factory = factory;
            registerRules(grammarAccess.getGrammar());
            this.grammarAccess = grammarAccess;
        }
        
        @Override
        protected InputStream getTokenFile() {
        	ClassLoader classLoader = getClass().getClassLoader();
        	return classLoader.getResourceAsStream("org/xtext/example/parser/antlr/internal/InternalDJ.tokens");
        }
        
        @Override
        protected String getFirstRuleName() {
        	return "Program";	
       	}
       	
       	@Override
       	protected DJGrammarAccess getGrammarAccess() {
       		return grammarAccess;
       	}



    // $ANTLR start entryRuleProgram
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:77:1: entryRuleProgram returns [EObject current=null] : iv_ruleProgram= ruleProgram EOF ;
    public final EObject entryRuleProgram() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleProgram = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:78:2: (iv_ruleProgram= ruleProgram EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:79:2: iv_ruleProgram= ruleProgram EOF
            {
             currentNode = createCompositeNode(grammarAccess.getProgramRule(), currentNode); 
            pushFollow(FOLLOW_ruleProgram_in_entryRuleProgram75);
            iv_ruleProgram=ruleProgram();
            _fsp--;

             current =iv_ruleProgram; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleProgram85); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleProgram


    // $ANTLR start ruleProgram
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:86:1: ruleProgram returns [EObject current=null] : ( ( (lv_imports_0_0= ruleImport ) )* ( (lv_features_1_0= ruleFeatures ) )? ( (lv_modulesList_2_0= ruleModule ) )* ) ;
    public final EObject ruleProgram() throws RecognitionException {
        EObject current = null;

        EObject lv_imports_0_0 = null;

        EObject lv_features_1_0 = null;

        EObject lv_modulesList_2_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:91:6: ( ( ( (lv_imports_0_0= ruleImport ) )* ( (lv_features_1_0= ruleFeatures ) )? ( (lv_modulesList_2_0= ruleModule ) )* ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:92:1: ( ( (lv_imports_0_0= ruleImport ) )* ( (lv_features_1_0= ruleFeatures ) )? ( (lv_modulesList_2_0= ruleModule ) )* )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:92:1: ( ( (lv_imports_0_0= ruleImport ) )* ( (lv_features_1_0= ruleFeatures ) )? ( (lv_modulesList_2_0= ruleModule ) )* )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:92:2: ( (lv_imports_0_0= ruleImport ) )* ( (lv_features_1_0= ruleFeatures ) )? ( (lv_modulesList_2_0= ruleModule ) )*
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:92:2: ( (lv_imports_0_0= ruleImport ) )*
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( (LA1_0==12) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:93:1: (lv_imports_0_0= ruleImport )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:93:1: (lv_imports_0_0= ruleImport )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:94:3: lv_imports_0_0= ruleImport
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getProgramAccess().getImportsImportParserRuleCall_0_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleImport_in_ruleProgram131);
            	    lv_imports_0_0=ruleImport();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getProgramRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"imports",
            	    	        		lv_imports_0_0, 
            	    	        		"Import", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }
            	    break;

            	default :
            	    break loop1;
                }
            } while (true);

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:116:3: ( (lv_features_1_0= ruleFeatures ) )?
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0==13) ) {
                alt2=1;
            }
            switch (alt2) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:117:1: (lv_features_1_0= ruleFeatures )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:117:1: (lv_features_1_0= ruleFeatures )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:118:3: lv_features_1_0= ruleFeatures
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getProgramAccess().getFeaturesFeaturesParserRuleCall_1_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleFeatures_in_ruleProgram153);
                    lv_features_1_0=ruleFeatures();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getProgramRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"features",
                    	        		lv_features_1_0, 
                    	        		"Features", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }
                    break;

            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:140:3: ( (lv_modulesList_2_0= ruleModule ) )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( ((LA3_0>=16 && LA3_0<=17)) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:141:1: (lv_modulesList_2_0= ruleModule )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:141:1: (lv_modulesList_2_0= ruleModule )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:142:3: lv_modulesList_2_0= ruleModule
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getProgramAccess().getModulesListModuleParserRuleCall_2_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleModule_in_ruleProgram175);
            	    lv_modulesList_2_0=ruleModule();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getProgramRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"modulesList",
            	    	        		lv_modulesList_2_0, 
            	    	        		"Module", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }
            	    break;

            	default :
            	    break loop3;
                }
            } while (true);


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleProgram


    // $ANTLR start entryRuleImport
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:172:1: entryRuleImport returns [EObject current=null] : iv_ruleImport= ruleImport EOF ;
    public final EObject entryRuleImport() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleImport = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:173:2: (iv_ruleImport= ruleImport EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:174:2: iv_ruleImport= ruleImport EOF
            {
             currentNode = createCompositeNode(grammarAccess.getImportRule(), currentNode); 
            pushFollow(FOLLOW_ruleImport_in_entryRuleImport212);
            iv_ruleImport=ruleImport();
            _fsp--;

             current =iv_ruleImport; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleImport222); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleImport


    // $ANTLR start ruleImport
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:181:1: ruleImport returns [EObject current=null] : ( 'import' ( (lv_importURI_1_0= RULE_STRING ) ) ) ;
    public final EObject ruleImport() throws RecognitionException {
        EObject current = null;

        Token lv_importURI_1_0=null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:186:6: ( ( 'import' ( (lv_importURI_1_0= RULE_STRING ) ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:187:1: ( 'import' ( (lv_importURI_1_0= RULE_STRING ) ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:187:1: ( 'import' ( (lv_importURI_1_0= RULE_STRING ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:187:3: 'import' ( (lv_importURI_1_0= RULE_STRING ) )
            {
            match(input,12,FOLLOW_12_in_ruleImport257); 

                    createLeafNode(grammarAccess.getImportAccess().getImportKeyword_0(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:191:1: ( (lv_importURI_1_0= RULE_STRING ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:192:1: (lv_importURI_1_0= RULE_STRING )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:192:1: (lv_importURI_1_0= RULE_STRING )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:193:3: lv_importURI_1_0= RULE_STRING
            {
            lv_importURI_1_0=(Token)input.LT(1);
            match(input,RULE_STRING,FOLLOW_RULE_STRING_in_ruleImport274); 

            			createLeafNode(grammarAccess.getImportAccess().getImportURISTRINGTerminalRuleCall_1_0(), "importURI"); 
            		

            	        if (current==null) {
            	            current = factory.create(grammarAccess.getImportRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"importURI",
            	        		lv_importURI_1_0, 
            	        		"STRING", 
            	        		lastConsumedNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	    

            }


            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleImport


    // $ANTLR start entryRuleFeatures
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:223:1: entryRuleFeatures returns [EObject current=null] : iv_ruleFeatures= ruleFeatures EOF ;
    public final EObject entryRuleFeatures() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleFeatures = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:224:2: (iv_ruleFeatures= ruleFeatures EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:225:2: iv_ruleFeatures= ruleFeatures EOF
            {
             currentNode = createCompositeNode(grammarAccess.getFeaturesRule(), currentNode); 
            pushFollow(FOLLOW_ruleFeatures_in_entryRuleFeatures315);
            iv_ruleFeatures=ruleFeatures();
            _fsp--;

             current =iv_ruleFeatures; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleFeatures325); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleFeatures


    // $ANTLR start ruleFeatures
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:232:1: ruleFeatures returns [EObject current=null] : ( 'features' ( ( (lv_featuresList_1_0= ruleFeature ) ) ( ',' ( (lv_featuresList_3_0= ruleFeature ) ) )* ) 'configurations' ( (lv_configuration_5_0= ruleConfiguration ) ) ) ;
    public final EObject ruleFeatures() throws RecognitionException {
        EObject current = null;

        EObject lv_featuresList_1_0 = null;

        EObject lv_featuresList_3_0 = null;

        EObject lv_configuration_5_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:237:6: ( ( 'features' ( ( (lv_featuresList_1_0= ruleFeature ) ) ( ',' ( (lv_featuresList_3_0= ruleFeature ) ) )* ) 'configurations' ( (lv_configuration_5_0= ruleConfiguration ) ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:238:1: ( 'features' ( ( (lv_featuresList_1_0= ruleFeature ) ) ( ',' ( (lv_featuresList_3_0= ruleFeature ) ) )* ) 'configurations' ( (lv_configuration_5_0= ruleConfiguration ) ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:238:1: ( 'features' ( ( (lv_featuresList_1_0= ruleFeature ) ) ( ',' ( (lv_featuresList_3_0= ruleFeature ) ) )* ) 'configurations' ( (lv_configuration_5_0= ruleConfiguration ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:238:3: 'features' ( ( (lv_featuresList_1_0= ruleFeature ) ) ( ',' ( (lv_featuresList_3_0= ruleFeature ) ) )* ) 'configurations' ( (lv_configuration_5_0= ruleConfiguration ) )
            {
            match(input,13,FOLLOW_13_in_ruleFeatures360); 

                    createLeafNode(grammarAccess.getFeaturesAccess().getFeaturesKeyword_0(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:242:1: ( ( (lv_featuresList_1_0= ruleFeature ) ) ( ',' ( (lv_featuresList_3_0= ruleFeature ) ) )* )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:242:2: ( (lv_featuresList_1_0= ruleFeature ) ) ( ',' ( (lv_featuresList_3_0= ruleFeature ) ) )*
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:242:2: ( (lv_featuresList_1_0= ruleFeature ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:243:1: (lv_featuresList_1_0= ruleFeature )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:243:1: (lv_featuresList_1_0= ruleFeature )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:244:3: lv_featuresList_1_0= ruleFeature
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getFeaturesAccess().getFeaturesListFeatureParserRuleCall_1_0_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleFeature_in_ruleFeatures382);
            lv_featuresList_1_0=ruleFeature();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getFeaturesRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		add(
            	       			current, 
            	       			"featuresList",
            	        		lv_featuresList_1_0, 
            	        		"Feature", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:266:2: ( ',' ( (lv_featuresList_3_0= ruleFeature ) ) )*
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( (LA4_0==14) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:266:4: ',' ( (lv_featuresList_3_0= ruleFeature ) )
            	    {
            	    match(input,14,FOLLOW_14_in_ruleFeatures393); 

            	            createLeafNode(grammarAccess.getFeaturesAccess().getCommaKeyword_1_1_0(), null); 
            	        
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:270:1: ( (lv_featuresList_3_0= ruleFeature ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:271:1: (lv_featuresList_3_0= ruleFeature )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:271:1: (lv_featuresList_3_0= ruleFeature )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:272:3: lv_featuresList_3_0= ruleFeature
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getFeaturesAccess().getFeaturesListFeatureParserRuleCall_1_1_1_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleFeature_in_ruleFeatures414);
            	    lv_featuresList_3_0=ruleFeature();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getFeaturesRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"featuresList",
            	    	        		lv_featuresList_3_0, 
            	    	        		"Feature", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop4;
                }
            } while (true);


            }

            match(input,15,FOLLOW_15_in_ruleFeatures427); 

                    createLeafNode(grammarAccess.getFeaturesAccess().getConfigurationsKeyword_2(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:298:1: ( (lv_configuration_5_0= ruleConfiguration ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:299:1: (lv_configuration_5_0= ruleConfiguration )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:299:1: (lv_configuration_5_0= ruleConfiguration )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:300:3: lv_configuration_5_0= ruleConfiguration
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getFeaturesAccess().getConfigurationConfigurationParserRuleCall_3_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleConfiguration_in_ruleFeatures448);
            lv_configuration_5_0=ruleConfiguration();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getFeaturesRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"configuration",
            	        		lv_configuration_5_0, 
            	        		"Configuration", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleFeatures


    // $ANTLR start entryRuleFeature
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:330:1: entryRuleFeature returns [EObject current=null] : iv_ruleFeature= ruleFeature EOF ;
    public final EObject entryRuleFeature() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleFeature = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:331:2: (iv_ruleFeature= ruleFeature EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:332:2: iv_ruleFeature= ruleFeature EOF
            {
             currentNode = createCompositeNode(grammarAccess.getFeatureRule(), currentNode); 
            pushFollow(FOLLOW_ruleFeature_in_entryRuleFeature484);
            iv_ruleFeature=ruleFeature();
            _fsp--;

             current =iv_ruleFeature; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleFeature494); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleFeature


    // $ANTLR start ruleFeature
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:339:1: ruleFeature returns [EObject current=null] : ( (lv_name_0_0= RULE_ID ) ) ;
    public final EObject ruleFeature() throws RecognitionException {
        EObject current = null;

        Token lv_name_0_0=null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:344:6: ( ( (lv_name_0_0= RULE_ID ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:345:1: ( (lv_name_0_0= RULE_ID ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:345:1: ( (lv_name_0_0= RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:346:1: (lv_name_0_0= RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:346:1: (lv_name_0_0= RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:347:3: lv_name_0_0= RULE_ID
            {
            lv_name_0_0=(Token)input.LT(1);
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleFeature535); 

            			createLeafNode(grammarAccess.getFeatureAccess().getNameIDTerminalRuleCall_0(), "name"); 
            		

            	        if (current==null) {
            	            current = factory.create(grammarAccess.getFeatureRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"name",
            	        		lv_name_0_0, 
            	        		"ID", 
            	        		lastConsumedNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	    

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleFeature


    // $ANTLR start entryRuleModule
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:377:1: entryRuleModule returns [EObject current=null] : iv_ruleModule= ruleModule EOF ;
    public final EObject entryRuleModule() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleModule = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:378:2: (iv_ruleModule= ruleModule EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:379:2: iv_ruleModule= ruleModule EOF
            {
             currentNode = createCompositeNode(grammarAccess.getModuleRule(), currentNode); 
            pushFollow(FOLLOW_ruleModule_in_entryRuleModule575);
            iv_ruleModule=ruleModule();
            _fsp--;

             current =iv_ruleModule; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleModule585); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleModule


    // $ANTLR start ruleModule
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:386:1: ruleModule returns [EObject current=null] : ( ( () ( ( (lv_ntype_1_0= 'core' ) ) ( (lv_core_2_0= ruleCore ) ) ) ) | ( ( (lv_ntype_3_0= 'delta' ) ) ( (lv_delta_4_0= ruleDelta ) ) ) ) ;
    public final EObject ruleModule() throws RecognitionException {
        EObject current = null;

        Token lv_ntype_1_0=null;
        Token lv_ntype_3_0=null;
        EObject lv_core_2_0 = null;

        EObject lv_delta_4_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:391:6: ( ( ( () ( ( (lv_ntype_1_0= 'core' ) ) ( (lv_core_2_0= ruleCore ) ) ) ) | ( ( (lv_ntype_3_0= 'delta' ) ) ( (lv_delta_4_0= ruleDelta ) ) ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:392:1: ( ( () ( ( (lv_ntype_1_0= 'core' ) ) ( (lv_core_2_0= ruleCore ) ) ) ) | ( ( (lv_ntype_3_0= 'delta' ) ) ( (lv_delta_4_0= ruleDelta ) ) ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:392:1: ( ( () ( ( (lv_ntype_1_0= 'core' ) ) ( (lv_core_2_0= ruleCore ) ) ) ) | ( ( (lv_ntype_3_0= 'delta' ) ) ( (lv_delta_4_0= ruleDelta ) ) ) )
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==16) ) {
                alt5=1;
            }
            else if ( (LA5_0==17) ) {
                alt5=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("392:1: ( ( () ( ( (lv_ntype_1_0= 'core' ) ) ( (lv_core_2_0= ruleCore ) ) ) ) | ( ( (lv_ntype_3_0= 'delta' ) ) ( (lv_delta_4_0= ruleDelta ) ) ) )", 5, 0, input);

                throw nvae;
            }
            switch (alt5) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:392:2: ( () ( ( (lv_ntype_1_0= 'core' ) ) ( (lv_core_2_0= ruleCore ) ) ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:392:2: ( () ( ( (lv_ntype_1_0= 'core' ) ) ( (lv_core_2_0= ruleCore ) ) ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:392:3: () ( ( (lv_ntype_1_0= 'core' ) ) ( (lv_core_2_0= ruleCore ) ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:392:3: ()
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:393:5: 
                    {
                     
                            temp=factory.create(grammarAccess.getModuleAccess().getModuleAction_0_0().getType().getClassifier());
                            current = temp; 
                            temp = null;
                            CompositeNode newNode = createCompositeNode(grammarAccess.getModuleAccess().getModuleAction_0_0(), currentNode.getParent());
                        newNode.getChildren().add(currentNode);
                        moveLookaheadInfo(currentNode, newNode);
                        currentNode = newNode; 
                            associateNodeWithAstElement(currentNode, current); 
                        

                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:403:2: ( ( (lv_ntype_1_0= 'core' ) ) ( (lv_core_2_0= ruleCore ) ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:403:3: ( (lv_ntype_1_0= 'core' ) ) ( (lv_core_2_0= ruleCore ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:403:3: ( (lv_ntype_1_0= 'core' ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:404:1: (lv_ntype_1_0= 'core' )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:404:1: (lv_ntype_1_0= 'core' )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:405:3: lv_ntype_1_0= 'core'
                    {
                    lv_ntype_1_0=(Token)input.LT(1);
                    match(input,16,FOLLOW_16_in_ruleModule639); 

                            createLeafNode(grammarAccess.getModuleAccess().getNtypeCoreKeyword_0_1_0_0(), "ntype"); 
                        

                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getModuleRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                    	        
                    	        try {
                    	       		set(current, "ntype", lv_ntype_1_0, "core", lastConsumedNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:424:2: ( (lv_core_2_0= ruleCore ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:425:1: (lv_core_2_0= ruleCore )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:425:1: (lv_core_2_0= ruleCore )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:426:3: lv_core_2_0= ruleCore
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getModuleAccess().getCoreCoreParserRuleCall_0_1_1_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleCore_in_ruleModule673);
                    lv_core_2_0=ruleCore();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getModuleRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"core",
                    	        		lv_core_2_0, 
                    	        		"Core", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }


                    }


                    }
                    break;
                case 2 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:449:6: ( ( (lv_ntype_3_0= 'delta' ) ) ( (lv_delta_4_0= ruleDelta ) ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:449:6: ( ( (lv_ntype_3_0= 'delta' ) ) ( (lv_delta_4_0= ruleDelta ) ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:449:7: ( (lv_ntype_3_0= 'delta' ) ) ( (lv_delta_4_0= ruleDelta ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:449:7: ( (lv_ntype_3_0= 'delta' ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:450:1: (lv_ntype_3_0= 'delta' )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:450:1: (lv_ntype_3_0= 'delta' )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:451:3: lv_ntype_3_0= 'delta'
                    {
                    lv_ntype_3_0=(Token)input.LT(1);
                    match(input,17,FOLLOW_17_in_ruleModule700); 

                            createLeafNode(grammarAccess.getModuleAccess().getNtypeDeltaKeyword_1_0_0(), "ntype"); 
                        

                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getModuleRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                    	        
                    	        try {
                    	       		set(current, "ntype", lv_ntype_3_0, "delta", lastConsumedNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:470:2: ( (lv_delta_4_0= ruleDelta ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:471:1: (lv_delta_4_0= ruleDelta )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:471:1: (lv_delta_4_0= ruleDelta )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:472:3: lv_delta_4_0= ruleDelta
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getModuleAccess().getDeltaDeltaParserRuleCall_1_1_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleDelta_in_ruleModule734);
                    lv_delta_4_0=ruleDelta();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getModuleRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"delta",
                    	        		lv_delta_4_0, 
                    	        		"Delta", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }


                    }
                    break;

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleModule


    // $ANTLR start entryRuleCore
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:502:1: entryRuleCore returns [EObject current=null] : iv_ruleCore= ruleCore EOF ;
    public final EObject entryRuleCore() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleCore = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:503:2: (iv_ruleCore= ruleCore EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:504:2: iv_ruleCore= ruleCore EOF
            {
             currentNode = createCompositeNode(grammarAccess.getCoreRule(), currentNode); 
            pushFollow(FOLLOW_ruleCore_in_entryRuleCore771);
            iv_ruleCore=ruleCore();
            _fsp--;

             current =iv_ruleCore; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleCore781); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleCore


    // $ANTLR start ruleCore
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:511:1: ruleCore returns [EObject current=null] : ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* '{' ( (lv_classesList_4_0= ruleClass ) )* '}' ) ;
    public final EObject ruleCore() throws RecognitionException {
        EObject current = null;

        EObject lv_classesList_4_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:516:6: ( ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* '{' ( (lv_classesList_4_0= ruleClass ) )* '}' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:517:1: ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* '{' ( (lv_classesList_4_0= ruleClass ) )* '}' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:517:1: ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* '{' ( (lv_classesList_4_0= ruleClass ) )* '}' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:517:2: ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* '{' ( (lv_classesList_4_0= ruleClass ) )* '}'
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:517:2: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:518:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:518:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:519:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getCoreRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleCore824); 

            		createLeafNode(grammarAccess.getCoreAccess().getNameFeatureCrossReference_0_0(), "name"); 
            	

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:531:2: ( ',' ( ( RULE_ID ) ) )*
            loop6:
            do {
                int alt6=2;
                int LA6_0 = input.LA(1);

                if ( (LA6_0==14) ) {
                    alt6=1;
                }


                switch (alt6) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:531:4: ',' ( ( RULE_ID ) )
            	    {
            	    match(input,14,FOLLOW_14_in_ruleCore835); 

            	            createLeafNode(grammarAccess.getCoreAccess().getCommaKeyword_1_0(), null); 
            	        
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:535:1: ( ( RULE_ID ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:536:1: ( RULE_ID )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:536:1: ( RULE_ID )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:537:3: RULE_ID
            	    {

            	    			if (current==null) {
            	    	            current = factory.create(grammarAccess.getCoreRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode, current);
            	    	        }
            	            
            	    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleCore853); 

            	    		createLeafNode(grammarAccess.getCoreAccess().getNameFeatureCrossReference_1_1_0(), "name"); 
            	    	

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop6;
                }
            } while (true);

            match(input,18,FOLLOW_18_in_ruleCore865); 

                    createLeafNode(grammarAccess.getCoreAccess().getLeftCurlyBracketKeyword_2(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:553:1: ( (lv_classesList_4_0= ruleClass ) )*
            loop7:
            do {
                int alt7=2;
                int LA7_0 = input.LA(1);

                if ( (LA7_0==20) ) {
                    alt7=1;
                }


                switch (alt7) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:554:1: (lv_classesList_4_0= ruleClass )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:554:1: (lv_classesList_4_0= ruleClass )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:555:3: lv_classesList_4_0= ruleClass
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getCoreAccess().getClassesListClassParserRuleCall_3_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleClass_in_ruleCore886);
            	    lv_classesList_4_0=ruleClass();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getCoreRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"classesList",
            	    	        		lv_classesList_4_0, 
            	    	        		"Class", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }
            	    break;

            	default :
            	    break loop7;
                }
            } while (true);

            match(input,19,FOLLOW_19_in_ruleCore897); 

                    createLeafNode(grammarAccess.getCoreAccess().getRightCurlyBracketKeyword_4(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleCore


    // $ANTLR start entryRuleClass
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:589:1: entryRuleClass returns [EObject current=null] : iv_ruleClass= ruleClass EOF ;
    public final EObject entryRuleClass() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleClass = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:590:2: (iv_ruleClass= ruleClass EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:591:2: iv_ruleClass= ruleClass EOF
            {
             currentNode = createCompositeNode(grammarAccess.getClassRule(), currentNode); 
            pushFollow(FOLLOW_ruleClass_in_entryRuleClass933);
            iv_ruleClass=ruleClass();
            _fsp--;

             current =iv_ruleClass; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleClass943); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleClass


    // $ANTLR start ruleClass
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:598:1: ruleClass returns [EObject current=null] : ( 'class' ( (lv_name_1_0= RULE_ID ) ) ( 'extends' ( ( RULE_ID ) ) )? '{' ( (lv_field_5_0= ruleField ) )* ( (lv_constructor_6_0= ruleConstructor ) )? ( (lv_method_7_0= ruleMethod ) )* '}' ) ;
    public final EObject ruleClass() throws RecognitionException {
        EObject current = null;

        Token lv_name_1_0=null;
        EObject lv_field_5_0 = null;

        EObject lv_constructor_6_0 = null;

        EObject lv_method_7_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:603:6: ( ( 'class' ( (lv_name_1_0= RULE_ID ) ) ( 'extends' ( ( RULE_ID ) ) )? '{' ( (lv_field_5_0= ruleField ) )* ( (lv_constructor_6_0= ruleConstructor ) )? ( (lv_method_7_0= ruleMethod ) )* '}' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:604:1: ( 'class' ( (lv_name_1_0= RULE_ID ) ) ( 'extends' ( ( RULE_ID ) ) )? '{' ( (lv_field_5_0= ruleField ) )* ( (lv_constructor_6_0= ruleConstructor ) )? ( (lv_method_7_0= ruleMethod ) )* '}' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:604:1: ( 'class' ( (lv_name_1_0= RULE_ID ) ) ( 'extends' ( ( RULE_ID ) ) )? '{' ( (lv_field_5_0= ruleField ) )* ( (lv_constructor_6_0= ruleConstructor ) )? ( (lv_method_7_0= ruleMethod ) )* '}' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:604:3: 'class' ( (lv_name_1_0= RULE_ID ) ) ( 'extends' ( ( RULE_ID ) ) )? '{' ( (lv_field_5_0= ruleField ) )* ( (lv_constructor_6_0= ruleConstructor ) )? ( (lv_method_7_0= ruleMethod ) )* '}'
            {
            match(input,20,FOLLOW_20_in_ruleClass978); 

                    createLeafNode(grammarAccess.getClassAccess().getClassKeyword_0(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:608:1: ( (lv_name_1_0= RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:609:1: (lv_name_1_0= RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:609:1: (lv_name_1_0= RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:610:3: lv_name_1_0= RULE_ID
            {
            lv_name_1_0=(Token)input.LT(1);
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleClass995); 

            			createLeafNode(grammarAccess.getClassAccess().getNameIDTerminalRuleCall_1_0(), "name"); 
            		

            	        if (current==null) {
            	            current = factory.create(grammarAccess.getClassRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"name",
            	        		lv_name_1_0, 
            	        		"ID", 
            	        		lastConsumedNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	    

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:632:2: ( 'extends' ( ( RULE_ID ) ) )?
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==21) ) {
                alt8=1;
            }
            switch (alt8) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:632:4: 'extends' ( ( RULE_ID ) )
                    {
                    match(input,21,FOLLOW_21_in_ruleClass1011); 

                            createLeafNode(grammarAccess.getClassAccess().getExtendsKeyword_2_0(), null); 
                        
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:636:1: ( ( RULE_ID ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:637:1: ( RULE_ID )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:637:1: ( RULE_ID )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:638:3: RULE_ID
                    {

                    			if (current==null) {
                    	            current = factory.create(grammarAccess.getClassRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                            
                    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleClass1029); 

                    		createLeafNode(grammarAccess.getClassAccess().getExtendsClassCrossReference_2_1_0(), "extends"); 
                    	

                    }


                    }


                    }
                    break;

            }

            match(input,18,FOLLOW_18_in_ruleClass1041); 

                    createLeafNode(grammarAccess.getClassAccess().getLeftCurlyBracketKeyword_3(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:654:1: ( (lv_field_5_0= ruleField ) )*
            loop9:
            do {
                int alt9=2;
                switch ( input.LA(1) ) {
                case RULE_ID:
                    {
                    int LA9_1 = input.LA(2);

                    if ( (LA9_1==RULE_ID) ) {
                        int LA9_6 = input.LA(3);

                        if ( (LA9_6==25) ) {
                            alt9=1;
                        }


                    }


                    }
                    break;
                case 41:
                    {
                    int LA9_2 = input.LA(2);

                    if ( (LA9_2==RULE_ID) ) {
                        int LA9_6 = input.LA(3);

                        if ( (LA9_6==25) ) {
                            alt9=1;
                        }


                    }


                    }
                    break;
                case 42:
                    {
                    int LA9_3 = input.LA(2);

                    if ( (LA9_3==RULE_ID) ) {
                        int LA9_6 = input.LA(3);

                        if ( (LA9_6==25) ) {
                            alt9=1;
                        }


                    }


                    }
                    break;
                case 43:
                    {
                    int LA9_4 = input.LA(2);

                    if ( (LA9_4==RULE_ID) ) {
                        int LA9_6 = input.LA(3);

                        if ( (LA9_6==25) ) {
                            alt9=1;
                        }


                    }


                    }
                    break;

                }

                switch (alt9) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:655:1: (lv_field_5_0= ruleField )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:655:1: (lv_field_5_0= ruleField )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:656:3: lv_field_5_0= ruleField
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getClassAccess().getFieldFieldParserRuleCall_4_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleField_in_ruleClass1062);
            	    lv_field_5_0=ruleField();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getClassRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"field",
            	    	        		lv_field_5_0, 
            	    	        		"Field", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }
            	    break;

            	default :
            	    break loop9;
                }
            } while (true);

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:678:3: ( (lv_constructor_6_0= ruleConstructor ) )?
            int alt10=2;
            int LA10_0 = input.LA(1);

            if ( (LA10_0==RULE_ID) ) {
                int LA10_1 = input.LA(2);

                if ( (LA10_1==22) ) {
                    alt10=1;
                }
            }
            switch (alt10) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:679:1: (lv_constructor_6_0= ruleConstructor )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:679:1: (lv_constructor_6_0= ruleConstructor )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:680:3: lv_constructor_6_0= ruleConstructor
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getClassAccess().getConstructorConstructorParserRuleCall_5_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleConstructor_in_ruleClass1084);
                    lv_constructor_6_0=ruleConstructor();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getClassRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		add(
                    	       			current, 
                    	       			"constructor",
                    	        		lv_constructor_6_0, 
                    	        		"Constructor", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }
                    break;

            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:702:3: ( (lv_method_7_0= ruleMethod ) )*
            loop11:
            do {
                int alt11=2;
                int LA11_0 = input.LA(1);

                if ( (LA11_0==RULE_ID||(LA11_0>=41 && LA11_0<=43)) ) {
                    alt11=1;
                }


                switch (alt11) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:703:1: (lv_method_7_0= ruleMethod )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:703:1: (lv_method_7_0= ruleMethod )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:704:3: lv_method_7_0= ruleMethod
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getClassAccess().getMethodMethodParserRuleCall_6_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleMethod_in_ruleClass1106);
            	    lv_method_7_0=ruleMethod();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getClassRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"method",
            	    	        		lv_method_7_0, 
            	    	        		"Method", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }
            	    break;

            	default :
            	    break loop11;
                }
            } while (true);

            match(input,19,FOLLOW_19_in_ruleClass1117); 

                    createLeafNode(grammarAccess.getClassAccess().getRightCurlyBracketKeyword_7(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleClass


    // $ANTLR start entryRuleConstructor
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:738:1: entryRuleConstructor returns [EObject current=null] : iv_ruleConstructor= ruleConstructor EOF ;
    public final EObject entryRuleConstructor() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleConstructor = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:739:2: (iv_ruleConstructor= ruleConstructor EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:740:2: iv_ruleConstructor= ruleConstructor EOF
            {
             currentNode = createCompositeNode(grammarAccess.getConstructorRule(), currentNode); 
            pushFollow(FOLLOW_ruleConstructor_in_entryRuleConstructor1153);
            iv_ruleConstructor=ruleConstructor();
            _fsp--;

             current =iv_ruleConstructor; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleConstructor1163); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleConstructor


    // $ANTLR start ruleConstructor
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:747:1: ruleConstructor returns [EObject current=null] : ( ( ( RULE_ID ) ) '(' ( ( (lv_params_2_0= ruleParameter ) ) ( ',' ( (lv_params_4_0= ruleParameter ) ) )* )? ')' '{' ( (lv_constructorSuperExpression_7_0= ruleConstructorSuperExpression ) )? ( (lv_constructorFieldExpression_8_0= ruleConstructorFieldExpression ) )* '}' ) ;
    public final EObject ruleConstructor() throws RecognitionException {
        EObject current = null;

        EObject lv_params_2_0 = null;

        EObject lv_params_4_0 = null;

        EObject lv_constructorSuperExpression_7_0 = null;

        EObject lv_constructorFieldExpression_8_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:752:6: ( ( ( ( RULE_ID ) ) '(' ( ( (lv_params_2_0= ruleParameter ) ) ( ',' ( (lv_params_4_0= ruleParameter ) ) )* )? ')' '{' ( (lv_constructorSuperExpression_7_0= ruleConstructorSuperExpression ) )? ( (lv_constructorFieldExpression_8_0= ruleConstructorFieldExpression ) )* '}' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:753:1: ( ( ( RULE_ID ) ) '(' ( ( (lv_params_2_0= ruleParameter ) ) ( ',' ( (lv_params_4_0= ruleParameter ) ) )* )? ')' '{' ( (lv_constructorSuperExpression_7_0= ruleConstructorSuperExpression ) )? ( (lv_constructorFieldExpression_8_0= ruleConstructorFieldExpression ) )* '}' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:753:1: ( ( ( RULE_ID ) ) '(' ( ( (lv_params_2_0= ruleParameter ) ) ( ',' ( (lv_params_4_0= ruleParameter ) ) )* )? ')' '{' ( (lv_constructorSuperExpression_7_0= ruleConstructorSuperExpression ) )? ( (lv_constructorFieldExpression_8_0= ruleConstructorFieldExpression ) )* '}' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:753:2: ( ( RULE_ID ) ) '(' ( ( (lv_params_2_0= ruleParameter ) ) ( ',' ( (lv_params_4_0= ruleParameter ) ) )* )? ')' '{' ( (lv_constructorSuperExpression_7_0= ruleConstructorSuperExpression ) )? ( (lv_constructorFieldExpression_8_0= ruleConstructorFieldExpression ) )* '}'
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:753:2: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:754:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:754:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:755:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getConstructorRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleConstructor1206); 

            		createLeafNode(grammarAccess.getConstructorAccess().getNameClassCrossReference_0_0(), "name"); 
            	

            }


            }

            match(input,22,FOLLOW_22_in_ruleConstructor1216); 

                    createLeafNode(grammarAccess.getConstructorAccess().getLeftParenthesisKeyword_1(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:771:1: ( ( (lv_params_2_0= ruleParameter ) ) ( ',' ( (lv_params_4_0= ruleParameter ) ) )* )?
            int alt13=2;
            int LA13_0 = input.LA(1);

            if ( (LA13_0==RULE_ID||(LA13_0>=41 && LA13_0<=43)) ) {
                alt13=1;
            }
            switch (alt13) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:771:2: ( (lv_params_2_0= ruleParameter ) ) ( ',' ( (lv_params_4_0= ruleParameter ) ) )*
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:771:2: ( (lv_params_2_0= ruleParameter ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:772:1: (lv_params_2_0= ruleParameter )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:772:1: (lv_params_2_0= ruleParameter )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:773:3: lv_params_2_0= ruleParameter
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getConstructorAccess().getParamsParameterParserRuleCall_2_0_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleParameter_in_ruleConstructor1238);
                    lv_params_2_0=ruleParameter();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getConstructorRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		add(
                    	       			current, 
                    	       			"params",
                    	        		lv_params_2_0, 
                    	        		"Parameter", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:795:2: ( ',' ( (lv_params_4_0= ruleParameter ) ) )*
                    loop12:
                    do {
                        int alt12=2;
                        int LA12_0 = input.LA(1);

                        if ( (LA12_0==14) ) {
                            alt12=1;
                        }


                        switch (alt12) {
                    	case 1 :
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:795:4: ',' ( (lv_params_4_0= ruleParameter ) )
                    	    {
                    	    match(input,14,FOLLOW_14_in_ruleConstructor1249); 

                    	            createLeafNode(grammarAccess.getConstructorAccess().getCommaKeyword_2_1_0(), null); 
                    	        
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:799:1: ( (lv_params_4_0= ruleParameter ) )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:800:1: (lv_params_4_0= ruleParameter )
                    	    {
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:800:1: (lv_params_4_0= ruleParameter )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:801:3: lv_params_4_0= ruleParameter
                    	    {
                    	     
                    	    	        currentNode=createCompositeNode(grammarAccess.getConstructorAccess().getParamsParameterParserRuleCall_2_1_1_0(), currentNode); 
                    	    	    
                    	    pushFollow(FOLLOW_ruleParameter_in_ruleConstructor1270);
                    	    lv_params_4_0=ruleParameter();
                    	    _fsp--;


                    	    	        if (current==null) {
                    	    	            current = factory.create(grammarAccess.getConstructorRule().getType().getClassifier());
                    	    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	    	        }
                    	    	        try {
                    	    	       		add(
                    	    	       			current, 
                    	    	       			"params",
                    	    	        		lv_params_4_0, 
                    	    	        		"Parameter", 
                    	    	        		currentNode);
                    	    	        } catch (ValueConverterException vce) {
                    	    				handleValueConverterException(vce);
                    	    	        }
                    	    	        currentNode = currentNode.getParent();
                    	    	    

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop12;
                        }
                    } while (true);


                    }
                    break;

            }

            match(input,23,FOLLOW_23_in_ruleConstructor1284); 

                    createLeafNode(grammarAccess.getConstructorAccess().getRightParenthesisKeyword_3(), null); 
                
            match(input,18,FOLLOW_18_in_ruleConstructor1294); 

                    createLeafNode(grammarAccess.getConstructorAccess().getLeftCurlyBracketKeyword_4(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:831:1: ( (lv_constructorSuperExpression_7_0= ruleConstructorSuperExpression ) )?
            int alt14=2;
            int LA14_0 = input.LA(1);

            if ( (LA14_0==24) ) {
                alt14=1;
            }
            switch (alt14) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:832:1: (lv_constructorSuperExpression_7_0= ruleConstructorSuperExpression )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:832:1: (lv_constructorSuperExpression_7_0= ruleConstructorSuperExpression )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:833:3: lv_constructorSuperExpression_7_0= ruleConstructorSuperExpression
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getConstructorAccess().getConstructorSuperExpressionConstructorSuperExpressionParserRuleCall_5_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleConstructorSuperExpression_in_ruleConstructor1315);
                    lv_constructorSuperExpression_7_0=ruleConstructorSuperExpression();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getConstructorRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"constructorSuperExpression",
                    	        		lv_constructorSuperExpression_7_0, 
                    	        		"ConstructorSuperExpression", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }
                    break;

            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:855:3: ( (lv_constructorFieldExpression_8_0= ruleConstructorFieldExpression ) )*
            loop15:
            do {
                int alt15=2;
                int LA15_0 = input.LA(1);

                if ( (LA15_0==26) ) {
                    alt15=1;
                }


                switch (alt15) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:856:1: (lv_constructorFieldExpression_8_0= ruleConstructorFieldExpression )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:856:1: (lv_constructorFieldExpression_8_0= ruleConstructorFieldExpression )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:857:3: lv_constructorFieldExpression_8_0= ruleConstructorFieldExpression
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getConstructorAccess().getConstructorFieldExpressionConstructorFieldExpressionParserRuleCall_6_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleConstructorFieldExpression_in_ruleConstructor1337);
            	    lv_constructorFieldExpression_8_0=ruleConstructorFieldExpression();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getConstructorRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"constructorFieldExpression",
            	    	        		lv_constructorFieldExpression_8_0, 
            	    	        		"ConstructorFieldExpression", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }
            	    break;

            	default :
            	    break loop15;
                }
            } while (true);

            match(input,19,FOLLOW_19_in_ruleConstructor1348); 

                    createLeafNode(grammarAccess.getConstructorAccess().getRightCurlyBracketKeyword_7(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleConstructor


    // $ANTLR start entryRuleConstructorSuperExpression
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:891:1: entryRuleConstructorSuperExpression returns [EObject current=null] : iv_ruleConstructorSuperExpression= ruleConstructorSuperExpression EOF ;
    public final EObject entryRuleConstructorSuperExpression() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleConstructorSuperExpression = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:892:2: (iv_ruleConstructorSuperExpression= ruleConstructorSuperExpression EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:893:2: iv_ruleConstructorSuperExpression= ruleConstructorSuperExpression EOF
            {
             currentNode = createCompositeNode(grammarAccess.getConstructorSuperExpressionRule(), currentNode); 
            pushFollow(FOLLOW_ruleConstructorSuperExpression_in_entryRuleConstructorSuperExpression1384);
            iv_ruleConstructorSuperExpression=ruleConstructorSuperExpression();
            _fsp--;

             current =iv_ruleConstructorSuperExpression; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleConstructorSuperExpression1394); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleConstructorSuperExpression


    // $ANTLR start ruleConstructorSuperExpression
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:900:1: ruleConstructorSuperExpression returns [EObject current=null] : ( () ( 'super' '(' ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? ')' ';' ) ) ;
    public final EObject ruleConstructorSuperExpression() throws RecognitionException {
        EObject current = null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:905:6: ( ( () ( 'super' '(' ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? ')' ';' ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:906:1: ( () ( 'super' '(' ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? ')' ';' ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:906:1: ( () ( 'super' '(' ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? ')' ';' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:906:2: () ( 'super' '(' ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? ')' ';' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:906:2: ()
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:907:5: 
            {
             
                    temp=factory.create(grammarAccess.getConstructorSuperExpressionAccess().getConstructorSuperExpressionAction_0().getType().getClassifier());
                    current = temp; 
                    temp = null;
                    CompositeNode newNode = createCompositeNode(grammarAccess.getConstructorSuperExpressionAccess().getConstructorSuperExpressionAction_0(), currentNode.getParent());
                newNode.getChildren().add(currentNode);
                moveLookaheadInfo(currentNode, newNode);
                currentNode = newNode; 
                    associateNodeWithAstElement(currentNode, current); 
                

            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:917:2: ( 'super' '(' ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? ')' ';' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:917:4: 'super' '(' ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? ')' ';'
            {
            match(input,24,FOLLOW_24_in_ruleConstructorSuperExpression1439); 

                    createLeafNode(grammarAccess.getConstructorSuperExpressionAccess().getSuperKeyword_1_0(), null); 
                
            match(input,22,FOLLOW_22_in_ruleConstructorSuperExpression1449); 

                    createLeafNode(grammarAccess.getConstructorSuperExpressionAccess().getLeftParenthesisKeyword_1_1(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:925:1: ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )?
            int alt17=2;
            int LA17_0 = input.LA(1);

            if ( (LA17_0==RULE_ID) ) {
                alt17=1;
            }
            switch (alt17) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:925:2: ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )*
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:925:2: ( ( RULE_ID ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:926:1: ( RULE_ID )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:926:1: ( RULE_ID )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:927:3: RULE_ID
                    {

                    			if (current==null) {
                    	            current = factory.create(grammarAccess.getConstructorSuperExpressionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                            
                    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleConstructorSuperExpression1468); 

                    		createLeafNode(grammarAccess.getConstructorSuperExpressionAccess().getParSParameterCrossReference_1_2_0_0(), "parS"); 
                    	

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:939:2: ( ',' ( ( RULE_ID ) ) )*
                    loop16:
                    do {
                        int alt16=2;
                        int LA16_0 = input.LA(1);

                        if ( (LA16_0==14) ) {
                            alt16=1;
                        }


                        switch (alt16) {
                    	case 1 :
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:939:4: ',' ( ( RULE_ID ) )
                    	    {
                    	    match(input,14,FOLLOW_14_in_ruleConstructorSuperExpression1479); 

                    	            createLeafNode(grammarAccess.getConstructorSuperExpressionAccess().getCommaKeyword_1_2_1_0(), null); 
                    	        
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:943:1: ( ( RULE_ID ) )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:944:1: ( RULE_ID )
                    	    {
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:944:1: ( RULE_ID )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:945:3: RULE_ID
                    	    {

                    	    			if (current==null) {
                    	    	            current = factory.create(grammarAccess.getConstructorSuperExpressionRule().getType().getClassifier());
                    	    	            associateNodeWithAstElement(currentNode, current);
                    	    	        }
                    	            
                    	    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleConstructorSuperExpression1497); 

                    	    		createLeafNode(grammarAccess.getConstructorSuperExpressionAccess().getParSParameterCrossReference_1_2_1_1_0(), "parS"); 
                    	    	

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop16;
                        }
                    } while (true);


                    }
                    break;

            }

            match(input,23,FOLLOW_23_in_ruleConstructorSuperExpression1511); 

                    createLeafNode(grammarAccess.getConstructorSuperExpressionAccess().getRightParenthesisKeyword_1_3(), null); 
                
            match(input,25,FOLLOW_25_in_ruleConstructorSuperExpression1521); 

                    createLeafNode(grammarAccess.getConstructorSuperExpressionAccess().getSemicolonKeyword_1_4(), null); 
                

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleConstructorSuperExpression


    // $ANTLR start entryRuleConstructorFieldExpression
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:973:1: entryRuleConstructorFieldExpression returns [EObject current=null] : iv_ruleConstructorFieldExpression= ruleConstructorFieldExpression EOF ;
    public final EObject entryRuleConstructorFieldExpression() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleConstructorFieldExpression = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:974:2: (iv_ruleConstructorFieldExpression= ruleConstructorFieldExpression EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:975:2: iv_ruleConstructorFieldExpression= ruleConstructorFieldExpression EOF
            {
             currentNode = createCompositeNode(grammarAccess.getConstructorFieldExpressionRule(), currentNode); 
            pushFollow(FOLLOW_ruleConstructorFieldExpression_in_entryRuleConstructorFieldExpression1558);
            iv_ruleConstructorFieldExpression=ruleConstructorFieldExpression();
            _fsp--;

             current =iv_ruleConstructorFieldExpression; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleConstructorFieldExpression1568); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleConstructorFieldExpression


    // $ANTLR start ruleConstructorFieldExpression
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:982:1: ruleConstructorFieldExpression returns [EObject current=null] : ( 'this' '.' ( ( RULE_ID ) ) '=' ( ( RULE_ID ) ) ';' ) ;
    public final EObject ruleConstructorFieldExpression() throws RecognitionException {
        EObject current = null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:987:6: ( ( 'this' '.' ( ( RULE_ID ) ) '=' ( ( RULE_ID ) ) ';' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:988:1: ( 'this' '.' ( ( RULE_ID ) ) '=' ( ( RULE_ID ) ) ';' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:988:1: ( 'this' '.' ( ( RULE_ID ) ) '=' ( ( RULE_ID ) ) ';' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:988:3: 'this' '.' ( ( RULE_ID ) ) '=' ( ( RULE_ID ) ) ';'
            {
            match(input,26,FOLLOW_26_in_ruleConstructorFieldExpression1603); 

                    createLeafNode(grammarAccess.getConstructorFieldExpressionAccess().getThisKeyword_0(), null); 
                
            match(input,27,FOLLOW_27_in_ruleConstructorFieldExpression1613); 

                    createLeafNode(grammarAccess.getConstructorFieldExpressionAccess().getFullStopKeyword_1(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:996:1: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:997:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:997:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:998:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getConstructorFieldExpressionRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleConstructorFieldExpression1631); 

            		createLeafNode(grammarAccess.getConstructorFieldExpressionAccess().getFieldFieldRefCrossReference_2_0(), "field"); 
            	

            }


            }

            match(input,28,FOLLOW_28_in_ruleConstructorFieldExpression1641); 

                    createLeafNode(grammarAccess.getConstructorFieldExpressionAccess().getEqualsSignKeyword_3(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1014:1: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1015:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1015:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1016:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getConstructorFieldExpressionRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleConstructorFieldExpression1659); 

            		createLeafNode(grammarAccess.getConstructorFieldExpressionAccess().getParTParameterCrossReference_4_0(), "parT"); 
            	

            }


            }

            match(input,25,FOLLOW_25_in_ruleConstructorFieldExpression1669); 

                    createLeafNode(grammarAccess.getConstructorFieldExpressionAccess().getSemicolonKeyword_5(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleConstructorFieldExpression


    // $ANTLR start entryRuleField
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1040:1: entryRuleField returns [EObject current=null] : iv_ruleField= ruleField EOF ;
    public final EObject entryRuleField() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleField = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1041:2: (iv_ruleField= ruleField EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1042:2: iv_ruleField= ruleField EOF
            {
             currentNode = createCompositeNode(grammarAccess.getFieldRule(), currentNode); 
            pushFollow(FOLLOW_ruleField_in_entryRuleField1705);
            iv_ruleField=ruleField();
            _fsp--;

             current =iv_ruleField; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleField1715); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleField


    // $ANTLR start ruleField
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1049:1: ruleField returns [EObject current=null] : ( ( (lv_type_0_0= ruleType ) ) ( (lv_reference_1_0= ruleFieldRef ) ) ';' ) ;
    public final EObject ruleField() throws RecognitionException {
        EObject current = null;

        EObject lv_type_0_0 = null;

        EObject lv_reference_1_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1054:6: ( ( ( (lv_type_0_0= ruleType ) ) ( (lv_reference_1_0= ruleFieldRef ) ) ';' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1055:1: ( ( (lv_type_0_0= ruleType ) ) ( (lv_reference_1_0= ruleFieldRef ) ) ';' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1055:1: ( ( (lv_type_0_0= ruleType ) ) ( (lv_reference_1_0= ruleFieldRef ) ) ';' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1055:2: ( (lv_type_0_0= ruleType ) ) ( (lv_reference_1_0= ruleFieldRef ) ) ';'
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1055:2: ( (lv_type_0_0= ruleType ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1056:1: (lv_type_0_0= ruleType )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1056:1: (lv_type_0_0= ruleType )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1057:3: lv_type_0_0= ruleType
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getFieldAccess().getTypeTypeParserRuleCall_0_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleType_in_ruleField1761);
            lv_type_0_0=ruleType();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getFieldRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"type",
            	        		lv_type_0_0, 
            	        		"Type", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1079:2: ( (lv_reference_1_0= ruleFieldRef ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1080:1: (lv_reference_1_0= ruleFieldRef )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1080:1: (lv_reference_1_0= ruleFieldRef )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1081:3: lv_reference_1_0= ruleFieldRef
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getFieldAccess().getReferenceFieldRefParserRuleCall_1_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleFieldRef_in_ruleField1782);
            lv_reference_1_0=ruleFieldRef();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getFieldRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"reference",
            	        		lv_reference_1_0, 
            	        		"FieldRef", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            match(input,25,FOLLOW_25_in_ruleField1792); 

                    createLeafNode(grammarAccess.getFieldAccess().getSemicolonKeyword_2(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleField


    // $ANTLR start entryRuleFieldRef
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1115:1: entryRuleFieldRef returns [EObject current=null] : iv_ruleFieldRef= ruleFieldRef EOF ;
    public final EObject entryRuleFieldRef() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleFieldRef = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1116:2: (iv_ruleFieldRef= ruleFieldRef EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1117:2: iv_ruleFieldRef= ruleFieldRef EOF
            {
             currentNode = createCompositeNode(grammarAccess.getFieldRefRule(), currentNode); 
            pushFollow(FOLLOW_ruleFieldRef_in_entryRuleFieldRef1828);
            iv_ruleFieldRef=ruleFieldRef();
            _fsp--;

             current =iv_ruleFieldRef; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleFieldRef1838); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleFieldRef


    // $ANTLR start ruleFieldRef
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1124:1: ruleFieldRef returns [EObject current=null] : ( (lv_name_0_0= RULE_ID ) ) ;
    public final EObject ruleFieldRef() throws RecognitionException {
        EObject current = null;

        Token lv_name_0_0=null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1129:6: ( ( (lv_name_0_0= RULE_ID ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1130:1: ( (lv_name_0_0= RULE_ID ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1130:1: ( (lv_name_0_0= RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1131:1: (lv_name_0_0= RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1131:1: (lv_name_0_0= RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1132:3: lv_name_0_0= RULE_ID
            {
            lv_name_0_0=(Token)input.LT(1);
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleFieldRef1879); 

            			createLeafNode(grammarAccess.getFieldRefAccess().getNameIDTerminalRuleCall_0(), "name"); 
            		

            	        if (current==null) {
            	            current = factory.create(grammarAccess.getFieldRefRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"name",
            	        		lv_name_0_0, 
            	        		"ID", 
            	        		lastConsumedNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	    

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleFieldRef


    // $ANTLR start entryRuleParameter
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1162:1: entryRuleParameter returns [EObject current=null] : iv_ruleParameter= ruleParameter EOF ;
    public final EObject entryRuleParameter() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleParameter = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1163:2: (iv_ruleParameter= ruleParameter EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1164:2: iv_ruleParameter= ruleParameter EOF
            {
             currentNode = createCompositeNode(grammarAccess.getParameterRule(), currentNode); 
            pushFollow(FOLLOW_ruleParameter_in_entryRuleParameter1919);
            iv_ruleParameter=ruleParameter();
            _fsp--;

             current =iv_ruleParameter; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleParameter1929); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleParameter


    // $ANTLR start ruleParameter
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1171:1: ruleParameter returns [EObject current=null] : ( ( (lv_type_0_0= ruleType ) ) ( (lv_name_1_0= RULE_ID ) ) ) ;
    public final EObject ruleParameter() throws RecognitionException {
        EObject current = null;

        Token lv_name_1_0=null;
        EObject lv_type_0_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1176:6: ( ( ( (lv_type_0_0= ruleType ) ) ( (lv_name_1_0= RULE_ID ) ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1177:1: ( ( (lv_type_0_0= ruleType ) ) ( (lv_name_1_0= RULE_ID ) ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1177:1: ( ( (lv_type_0_0= ruleType ) ) ( (lv_name_1_0= RULE_ID ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1177:2: ( (lv_type_0_0= ruleType ) ) ( (lv_name_1_0= RULE_ID ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1177:2: ( (lv_type_0_0= ruleType ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1178:1: (lv_type_0_0= ruleType )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1178:1: (lv_type_0_0= ruleType )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1179:3: lv_type_0_0= ruleType
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getParameterAccess().getTypeTypeParserRuleCall_0_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleType_in_ruleParameter1975);
            lv_type_0_0=ruleType();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getParameterRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"type",
            	        		lv_type_0_0, 
            	        		"Type", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1201:2: ( (lv_name_1_0= RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1202:1: (lv_name_1_0= RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1202:1: (lv_name_1_0= RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1203:3: lv_name_1_0= RULE_ID
            {
            lv_name_1_0=(Token)input.LT(1);
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleParameter1992); 

            			createLeafNode(grammarAccess.getParameterAccess().getNameIDTerminalRuleCall_1_0(), "name"); 
            		

            	        if (current==null) {
            	            current = factory.create(grammarAccess.getParameterRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"name",
            	        		lv_name_1_0, 
            	        		"ID", 
            	        		lastConsumedNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	    

            }


            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleParameter


    // $ANTLR start entryRuleMethod
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1233:1: entryRuleMethod returns [EObject current=null] : iv_ruleMethod= ruleMethod EOF ;
    public final EObject entryRuleMethod() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMethod = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1234:2: (iv_ruleMethod= ruleMethod EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1235:2: iv_ruleMethod= ruleMethod EOF
            {
             currentNode = createCompositeNode(grammarAccess.getMethodRule(), currentNode); 
            pushFollow(FOLLOW_ruleMethod_in_entryRuleMethod2033);
            iv_ruleMethod=ruleMethod();
            _fsp--;

             current =iv_ruleMethod; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleMethod2043); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleMethod


    // $ANTLR start ruleMethod
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1242:1: ruleMethod returns [EObject current=null] : ( ( (lv_returntype_0_0= ruleType ) ) ( (lv_reference_1_0= ruleMethodRef ) ) '(' ( ( (lv_params_3_0= ruleParameter ) ) ( ',' ( (lv_params_5_0= ruleParameter ) ) )* )? ')' '{' ( (lv_body_8_0= ruleMethodBody ) ) '}' ) ;
    public final EObject ruleMethod() throws RecognitionException {
        EObject current = null;

        EObject lv_returntype_0_0 = null;

        EObject lv_reference_1_0 = null;

        EObject lv_params_3_0 = null;

        EObject lv_params_5_0 = null;

        EObject lv_body_8_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1247:6: ( ( ( (lv_returntype_0_0= ruleType ) ) ( (lv_reference_1_0= ruleMethodRef ) ) '(' ( ( (lv_params_3_0= ruleParameter ) ) ( ',' ( (lv_params_5_0= ruleParameter ) ) )* )? ')' '{' ( (lv_body_8_0= ruleMethodBody ) ) '}' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1248:1: ( ( (lv_returntype_0_0= ruleType ) ) ( (lv_reference_1_0= ruleMethodRef ) ) '(' ( ( (lv_params_3_0= ruleParameter ) ) ( ',' ( (lv_params_5_0= ruleParameter ) ) )* )? ')' '{' ( (lv_body_8_0= ruleMethodBody ) ) '}' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1248:1: ( ( (lv_returntype_0_0= ruleType ) ) ( (lv_reference_1_0= ruleMethodRef ) ) '(' ( ( (lv_params_3_0= ruleParameter ) ) ( ',' ( (lv_params_5_0= ruleParameter ) ) )* )? ')' '{' ( (lv_body_8_0= ruleMethodBody ) ) '}' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1248:2: ( (lv_returntype_0_0= ruleType ) ) ( (lv_reference_1_0= ruleMethodRef ) ) '(' ( ( (lv_params_3_0= ruleParameter ) ) ( ',' ( (lv_params_5_0= ruleParameter ) ) )* )? ')' '{' ( (lv_body_8_0= ruleMethodBody ) ) '}'
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1248:2: ( (lv_returntype_0_0= ruleType ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1249:1: (lv_returntype_0_0= ruleType )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1249:1: (lv_returntype_0_0= ruleType )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1250:3: lv_returntype_0_0= ruleType
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getMethodAccess().getReturntypeTypeParserRuleCall_0_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleType_in_ruleMethod2089);
            lv_returntype_0_0=ruleType();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getMethodRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"returntype",
            	        		lv_returntype_0_0, 
            	        		"Type", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1272:2: ( (lv_reference_1_0= ruleMethodRef ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1273:1: (lv_reference_1_0= ruleMethodRef )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1273:1: (lv_reference_1_0= ruleMethodRef )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1274:3: lv_reference_1_0= ruleMethodRef
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getMethodAccess().getReferenceMethodRefParserRuleCall_1_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleMethodRef_in_ruleMethod2110);
            lv_reference_1_0=ruleMethodRef();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getMethodRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"reference",
            	        		lv_reference_1_0, 
            	        		"MethodRef", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            match(input,22,FOLLOW_22_in_ruleMethod2120); 

                    createLeafNode(grammarAccess.getMethodAccess().getLeftParenthesisKeyword_2(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1300:1: ( ( (lv_params_3_0= ruleParameter ) ) ( ',' ( (lv_params_5_0= ruleParameter ) ) )* )?
            int alt19=2;
            int LA19_0 = input.LA(1);

            if ( (LA19_0==RULE_ID||(LA19_0>=41 && LA19_0<=43)) ) {
                alt19=1;
            }
            switch (alt19) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1300:2: ( (lv_params_3_0= ruleParameter ) ) ( ',' ( (lv_params_5_0= ruleParameter ) ) )*
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1300:2: ( (lv_params_3_0= ruleParameter ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1301:1: (lv_params_3_0= ruleParameter )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1301:1: (lv_params_3_0= ruleParameter )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1302:3: lv_params_3_0= ruleParameter
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getMethodAccess().getParamsParameterParserRuleCall_3_0_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleParameter_in_ruleMethod2142);
                    lv_params_3_0=ruleParameter();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getMethodRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		add(
                    	       			current, 
                    	       			"params",
                    	        		lv_params_3_0, 
                    	        		"Parameter", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1324:2: ( ',' ( (lv_params_5_0= ruleParameter ) ) )*
                    loop18:
                    do {
                        int alt18=2;
                        int LA18_0 = input.LA(1);

                        if ( (LA18_0==14) ) {
                            alt18=1;
                        }


                        switch (alt18) {
                    	case 1 :
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1324:4: ',' ( (lv_params_5_0= ruleParameter ) )
                    	    {
                    	    match(input,14,FOLLOW_14_in_ruleMethod2153); 

                    	            createLeafNode(grammarAccess.getMethodAccess().getCommaKeyword_3_1_0(), null); 
                    	        
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1328:1: ( (lv_params_5_0= ruleParameter ) )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1329:1: (lv_params_5_0= ruleParameter )
                    	    {
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1329:1: (lv_params_5_0= ruleParameter )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1330:3: lv_params_5_0= ruleParameter
                    	    {
                    	     
                    	    	        currentNode=createCompositeNode(grammarAccess.getMethodAccess().getParamsParameterParserRuleCall_3_1_1_0(), currentNode); 
                    	    	    
                    	    pushFollow(FOLLOW_ruleParameter_in_ruleMethod2174);
                    	    lv_params_5_0=ruleParameter();
                    	    _fsp--;


                    	    	        if (current==null) {
                    	    	            current = factory.create(grammarAccess.getMethodRule().getType().getClassifier());
                    	    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	    	        }
                    	    	        try {
                    	    	       		add(
                    	    	       			current, 
                    	    	       			"params",
                    	    	        		lv_params_5_0, 
                    	    	        		"Parameter", 
                    	    	        		currentNode);
                    	    	        } catch (ValueConverterException vce) {
                    	    				handleValueConverterException(vce);
                    	    	        }
                    	    	        currentNode = currentNode.getParent();
                    	    	    

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop18;
                        }
                    } while (true);


                    }
                    break;

            }

            match(input,23,FOLLOW_23_in_ruleMethod2188); 

                    createLeafNode(grammarAccess.getMethodAccess().getRightParenthesisKeyword_4(), null); 
                
            match(input,18,FOLLOW_18_in_ruleMethod2198); 

                    createLeafNode(grammarAccess.getMethodAccess().getLeftCurlyBracketKeyword_5(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1360:1: ( (lv_body_8_0= ruleMethodBody ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1361:1: (lv_body_8_0= ruleMethodBody )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1361:1: (lv_body_8_0= ruleMethodBody )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1362:3: lv_body_8_0= ruleMethodBody
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getMethodAccess().getBodyMethodBodyParserRuleCall_6_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleMethodBody_in_ruleMethod2219);
            lv_body_8_0=ruleMethodBody();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getMethodRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"body",
            	        		lv_body_8_0, 
            	        		"MethodBody", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            match(input,19,FOLLOW_19_in_ruleMethod2229); 

                    createLeafNode(grammarAccess.getMethodAccess().getRightCurlyBracketKeyword_7(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleMethod


    // $ANTLR start entryRuleMethodRef
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1396:1: entryRuleMethodRef returns [EObject current=null] : iv_ruleMethodRef= ruleMethodRef EOF ;
    public final EObject entryRuleMethodRef() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMethodRef = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1397:2: (iv_ruleMethodRef= ruleMethodRef EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1398:2: iv_ruleMethodRef= ruleMethodRef EOF
            {
             currentNode = createCompositeNode(grammarAccess.getMethodRefRule(), currentNode); 
            pushFollow(FOLLOW_ruleMethodRef_in_entryRuleMethodRef2265);
            iv_ruleMethodRef=ruleMethodRef();
            _fsp--;

             current =iv_ruleMethodRef; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleMethodRef2275); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleMethodRef


    // $ANTLR start ruleMethodRef
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1405:1: ruleMethodRef returns [EObject current=null] : ( (lv_name_0_0= RULE_ID ) ) ;
    public final EObject ruleMethodRef() throws RecognitionException {
        EObject current = null;

        Token lv_name_0_0=null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1410:6: ( ( (lv_name_0_0= RULE_ID ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1411:1: ( (lv_name_0_0= RULE_ID ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1411:1: ( (lv_name_0_0= RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1412:1: (lv_name_0_0= RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1412:1: (lv_name_0_0= RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1413:3: lv_name_0_0= RULE_ID
            {
            lv_name_0_0=(Token)input.LT(1);
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleMethodRef2316); 

            			createLeafNode(grammarAccess.getMethodRefAccess().getNameIDTerminalRuleCall_0(), "name"); 
            		

            	        if (current==null) {
            	            current = factory.create(grammarAccess.getMethodRefRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"name",
            	        		lv_name_0_0, 
            	        		"ID", 
            	        		lastConsumedNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	    

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleMethodRef


    // $ANTLR start entryRuleMethodBody
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1443:1: entryRuleMethodBody returns [EObject current=null] : iv_ruleMethodBody= ruleMethodBody EOF ;
    public final EObject entryRuleMethodBody() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMethodBody = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1444:2: (iv_ruleMethodBody= ruleMethodBody EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1445:2: iv_ruleMethodBody= ruleMethodBody EOF
            {
             currentNode = createCompositeNode(grammarAccess.getMethodBodyRule(), currentNode); 
            pushFollow(FOLLOW_ruleMethodBody_in_entryRuleMethodBody2356);
            iv_ruleMethodBody=ruleMethodBody();
            _fsp--;

             current =iv_ruleMethodBody; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleMethodBody2366); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleMethodBody


    // $ANTLR start ruleMethodBody
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1452:1: ruleMethodBody returns [EObject current=null] : ( () ( ( (lv_insertJava_1_0= ruleInsertJava ) ) | ( ( (lv_expressions_2_0= ruleExpression ) ) ';' ) )* ( ( (lv_return_4_0= 'return' ) ) ( (lv_expressionReturn_5_0= ruleExpression ) )? ';' )? ) ;
    public final EObject ruleMethodBody() throws RecognitionException {
        EObject current = null;

        Token lv_return_4_0=null;
        EObject lv_insertJava_1_0 = null;

        EObject lv_expressions_2_0 = null;

        EObject lv_expressionReturn_5_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1457:6: ( ( () ( ( (lv_insertJava_1_0= ruleInsertJava ) ) | ( ( (lv_expressions_2_0= ruleExpression ) ) ';' ) )* ( ( (lv_return_4_0= 'return' ) ) ( (lv_expressionReturn_5_0= ruleExpression ) )? ';' )? ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1458:1: ( () ( ( (lv_insertJava_1_0= ruleInsertJava ) ) | ( ( (lv_expressions_2_0= ruleExpression ) ) ';' ) )* ( ( (lv_return_4_0= 'return' ) ) ( (lv_expressionReturn_5_0= ruleExpression ) )? ';' )? )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1458:1: ( () ( ( (lv_insertJava_1_0= ruleInsertJava ) ) | ( ( (lv_expressions_2_0= ruleExpression ) ) ';' ) )* ( ( (lv_return_4_0= 'return' ) ) ( (lv_expressionReturn_5_0= ruleExpression ) )? ';' )? )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1458:2: () ( ( (lv_insertJava_1_0= ruleInsertJava ) ) | ( ( (lv_expressions_2_0= ruleExpression ) ) ';' ) )* ( ( (lv_return_4_0= 'return' ) ) ( (lv_expressionReturn_5_0= ruleExpression ) )? ';' )?
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1458:2: ()
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1459:5: 
            {
             
                    temp=factory.create(grammarAccess.getMethodBodyAccess().getMethodBodyAction_0().getType().getClassifier());
                    current = temp; 
                    temp = null;
                    CompositeNode newNode = createCompositeNode(grammarAccess.getMethodBodyAccess().getMethodBodyAction_0(), currentNode.getParent());
                newNode.getChildren().add(currentNode);
                moveLookaheadInfo(currentNode, newNode);
                currentNode = newNode; 
                    associateNodeWithAstElement(currentNode, current); 
                

            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1469:2: ( ( (lv_insertJava_1_0= ruleInsertJava ) ) | ( ( (lv_expressions_2_0= ruleExpression ) ) ';' ) )*
            loop20:
            do {
                int alt20=3;
                int LA20_0 = input.LA(1);

                if ( (LA20_0==44) ) {
                    alt20=1;
                }
                else if ( ((LA20_0>=RULE_STRING && LA20_0<=RULE_ID)||LA20_0==RULE_INT||LA20_0==22||LA20_0==26||(LA20_0>=46 && LA20_0<=48)) ) {
                    alt20=2;
                }


                switch (alt20) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1469:3: ( (lv_insertJava_1_0= ruleInsertJava ) )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1469:3: ( (lv_insertJava_1_0= ruleInsertJava ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1470:1: (lv_insertJava_1_0= ruleInsertJava )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1470:1: (lv_insertJava_1_0= ruleInsertJava )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1471:3: lv_insertJava_1_0= ruleInsertJava
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getMethodBodyAccess().getInsertJavaInsertJavaParserRuleCall_1_0_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleInsertJava_in_ruleMethodBody2422);
            	    lv_insertJava_1_0=ruleInsertJava();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getMethodBodyRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"insertJava",
            	    	        		lv_insertJava_1_0, 
            	    	        		"InsertJava", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }


            	    }
            	    break;
            	case 2 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1494:6: ( ( (lv_expressions_2_0= ruleExpression ) ) ';' )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1494:6: ( ( (lv_expressions_2_0= ruleExpression ) ) ';' )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1494:7: ( (lv_expressions_2_0= ruleExpression ) ) ';'
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1494:7: ( (lv_expressions_2_0= ruleExpression ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1495:1: (lv_expressions_2_0= ruleExpression )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1495:1: (lv_expressions_2_0= ruleExpression )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1496:3: lv_expressions_2_0= ruleExpression
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getMethodBodyAccess().getExpressionsExpressionParserRuleCall_1_1_0_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleExpression_in_ruleMethodBody2450);
            	    lv_expressions_2_0=ruleExpression();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getMethodBodyRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"expressions",
            	    	        		lv_expressions_2_0, 
            	    	        		"Expression", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }

            	    match(input,25,FOLLOW_25_in_ruleMethodBody2460); 

            	            createLeafNode(grammarAccess.getMethodBodyAccess().getSemicolonKeyword_1_1_1(), null); 
            	        

            	    }


            	    }
            	    break;

            	default :
            	    break loop20;
                }
            } while (true);

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1522:4: ( ( (lv_return_4_0= 'return' ) ) ( (lv_expressionReturn_5_0= ruleExpression ) )? ';' )?
            int alt22=2;
            int LA22_0 = input.LA(1);

            if ( (LA22_0==29) ) {
                alt22=1;
            }
            switch (alt22) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1522:5: ( (lv_return_4_0= 'return' ) ) ( (lv_expressionReturn_5_0= ruleExpression ) )? ';'
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1522:5: ( (lv_return_4_0= 'return' ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1523:1: (lv_return_4_0= 'return' )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1523:1: (lv_return_4_0= 'return' )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1524:3: lv_return_4_0= 'return'
                    {
                    lv_return_4_0=(Token)input.LT(1);
                    match(input,29,FOLLOW_29_in_ruleMethodBody2482); 

                            createLeafNode(grammarAccess.getMethodBodyAccess().getReturnReturnKeyword_2_0_0(), "return"); 
                        

                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getMethodBodyRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                    	        
                    	        try {
                    	       		set(current, "return", lv_return_4_0, "return", lastConsumedNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1543:2: ( (lv_expressionReturn_5_0= ruleExpression ) )?
                    int alt21=2;
                    int LA21_0 = input.LA(1);

                    if ( ((LA21_0>=RULE_STRING && LA21_0<=RULE_ID)||LA21_0==RULE_INT||LA21_0==22||LA21_0==26||(LA21_0>=46 && LA21_0<=48)) ) {
                        alt21=1;
                    }
                    switch (alt21) {
                        case 1 :
                            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1544:1: (lv_expressionReturn_5_0= ruleExpression )
                            {
                            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1544:1: (lv_expressionReturn_5_0= ruleExpression )
                            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1545:3: lv_expressionReturn_5_0= ruleExpression
                            {
                             
                            	        currentNode=createCompositeNode(grammarAccess.getMethodBodyAccess().getExpressionReturnExpressionParserRuleCall_2_1_0(), currentNode); 
                            	    
                            pushFollow(FOLLOW_ruleExpression_in_ruleMethodBody2516);
                            lv_expressionReturn_5_0=ruleExpression();
                            _fsp--;


                            	        if (current==null) {
                            	            current = factory.create(grammarAccess.getMethodBodyRule().getType().getClassifier());
                            	            associateNodeWithAstElement(currentNode.getParent(), current);
                            	        }
                            	        try {
                            	       		set(
                            	       			current, 
                            	       			"expressionReturn",
                            	        		lv_expressionReturn_5_0, 
                            	        		"Expression", 
                            	        		currentNode);
                            	        } catch (ValueConverterException vce) {
                            				handleValueConverterException(vce);
                            	        }
                            	        currentNode = currentNode.getParent();
                            	    

                            }


                            }
                            break;

                    }

                    match(input,25,FOLLOW_25_in_ruleMethodBody2527); 

                            createLeafNode(grammarAccess.getMethodBodyAccess().getSemicolonKeyword_2_2(), null); 
                        

                    }
                    break;

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleMethodBody


    // $ANTLR start entryRuleDelta
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1579:1: entryRuleDelta returns [EObject current=null] : iv_ruleDelta= ruleDelta EOF ;
    public final EObject entryRuleDelta() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleDelta = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1580:2: (iv_ruleDelta= ruleDelta EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1581:2: iv_ruleDelta= ruleDelta EOF
            {
             currentNode = createCompositeNode(grammarAccess.getDeltaRule(), currentNode); 
            pushFollow(FOLLOW_ruleDelta_in_entryRuleDelta2565);
            iv_ruleDelta=ruleDelta();
            _fsp--;

             current =iv_ruleDelta; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleDelta2575); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleDelta


    // $ANTLR start ruleDelta
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1588:1: ruleDelta returns [EObject current=null] : ( ( (lv_name_0_0= RULE_ID ) ) ( 'after' ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? 'when' ( (lv_condition_6_0= ruleCondition ) ) ( '&&' ( (lv_condition_8_0= ruleCondition ) ) )* '{' ( (lv_classesList_10_0= ruleClassm ) )* '}' ) ;
    public final EObject ruleDelta() throws RecognitionException {
        EObject current = null;

        Token lv_name_0_0=null;
        EObject lv_condition_6_0 = null;

        EObject lv_condition_8_0 = null;

        EObject lv_classesList_10_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1593:6: ( ( ( (lv_name_0_0= RULE_ID ) ) ( 'after' ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? 'when' ( (lv_condition_6_0= ruleCondition ) ) ( '&&' ( (lv_condition_8_0= ruleCondition ) ) )* '{' ( (lv_classesList_10_0= ruleClassm ) )* '}' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1594:1: ( ( (lv_name_0_0= RULE_ID ) ) ( 'after' ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? 'when' ( (lv_condition_6_0= ruleCondition ) ) ( '&&' ( (lv_condition_8_0= ruleCondition ) ) )* '{' ( (lv_classesList_10_0= ruleClassm ) )* '}' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1594:1: ( ( (lv_name_0_0= RULE_ID ) ) ( 'after' ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? 'when' ( (lv_condition_6_0= ruleCondition ) ) ( '&&' ( (lv_condition_8_0= ruleCondition ) ) )* '{' ( (lv_classesList_10_0= ruleClassm ) )* '}' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1594:2: ( (lv_name_0_0= RULE_ID ) ) ( 'after' ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? 'when' ( (lv_condition_6_0= ruleCondition ) ) ( '&&' ( (lv_condition_8_0= ruleCondition ) ) )* '{' ( (lv_classesList_10_0= ruleClassm ) )* '}'
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1594:2: ( (lv_name_0_0= RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1595:1: (lv_name_0_0= RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1595:1: (lv_name_0_0= RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1596:3: lv_name_0_0= RULE_ID
            {
            lv_name_0_0=(Token)input.LT(1);
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleDelta2617); 

            			createLeafNode(grammarAccess.getDeltaAccess().getNameIDTerminalRuleCall_0_0(), "name"); 
            		

            	        if (current==null) {
            	            current = factory.create(grammarAccess.getDeltaRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"name",
            	        		lv_name_0_0, 
            	        		"ID", 
            	        		lastConsumedNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	    

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1618:2: ( 'after' ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )?
            int alt24=2;
            int LA24_0 = input.LA(1);

            if ( (LA24_0==30) ) {
                alt24=1;
            }
            switch (alt24) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1618:4: 'after' ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )*
                    {
                    match(input,30,FOLLOW_30_in_ruleDelta2633); 

                            createLeafNode(grammarAccess.getDeltaAccess().getAfterKeyword_1_0(), null); 
                        
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1622:1: ( ( RULE_ID ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1623:1: ( RULE_ID )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1623:1: ( RULE_ID )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1624:3: RULE_ID
                    {

                    			if (current==null) {
                    	            current = factory.create(grammarAccess.getDeltaRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                            
                    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleDelta2651); 

                    		createLeafNode(grammarAccess.getDeltaAccess().getAfterDeltaCrossReference_1_1_0(), "after"); 
                    	

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1636:2: ( ',' ( ( RULE_ID ) ) )*
                    loop23:
                    do {
                        int alt23=2;
                        int LA23_0 = input.LA(1);

                        if ( (LA23_0==14) ) {
                            alt23=1;
                        }


                        switch (alt23) {
                    	case 1 :
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1636:4: ',' ( ( RULE_ID ) )
                    	    {
                    	    match(input,14,FOLLOW_14_in_ruleDelta2662); 

                    	            createLeafNode(grammarAccess.getDeltaAccess().getCommaKeyword_1_2_0(), null); 
                    	        
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1640:1: ( ( RULE_ID ) )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1641:1: ( RULE_ID )
                    	    {
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1641:1: ( RULE_ID )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1642:3: RULE_ID
                    	    {

                    	    			if (current==null) {
                    	    	            current = factory.create(grammarAccess.getDeltaRule().getType().getClassifier());
                    	    	            associateNodeWithAstElement(currentNode, current);
                    	    	        }
                    	            
                    	    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleDelta2680); 

                    	    		createLeafNode(grammarAccess.getDeltaAccess().getAfterDeltaCrossReference_1_2_1_0(), "after"); 
                    	    	

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop23;
                        }
                    } while (true);


                    }
                    break;

            }

            match(input,31,FOLLOW_31_in_ruleDelta2694); 

                    createLeafNode(grammarAccess.getDeltaAccess().getWhenKeyword_2(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1658:1: ( (lv_condition_6_0= ruleCondition ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1659:1: (lv_condition_6_0= ruleCondition )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1659:1: (lv_condition_6_0= ruleCondition )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1660:3: lv_condition_6_0= ruleCondition
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getDeltaAccess().getConditionConditionParserRuleCall_3_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleCondition_in_ruleDelta2715);
            lv_condition_6_0=ruleCondition();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getDeltaRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		add(
            	       			current, 
            	       			"condition",
            	        		lv_condition_6_0, 
            	        		"Condition", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1682:2: ( '&&' ( (lv_condition_8_0= ruleCondition ) ) )*
            loop25:
            do {
                int alt25=2;
                int LA25_0 = input.LA(1);

                if ( (LA25_0==32) ) {
                    alt25=1;
                }


                switch (alt25) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1682:4: '&&' ( (lv_condition_8_0= ruleCondition ) )
            	    {
            	    match(input,32,FOLLOW_32_in_ruleDelta2726); 

            	            createLeafNode(grammarAccess.getDeltaAccess().getAmpersandAmpersandKeyword_4_0(), null); 
            	        
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1686:1: ( (lv_condition_8_0= ruleCondition ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1687:1: (lv_condition_8_0= ruleCondition )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1687:1: (lv_condition_8_0= ruleCondition )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1688:3: lv_condition_8_0= ruleCondition
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getDeltaAccess().getConditionConditionParserRuleCall_4_1_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleCondition_in_ruleDelta2747);
            	    lv_condition_8_0=ruleCondition();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getDeltaRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"condition",
            	    	        		lv_condition_8_0, 
            	    	        		"Condition", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop25;
                }
            } while (true);

            match(input,18,FOLLOW_18_in_ruleDelta2759); 

                    createLeafNode(grammarAccess.getDeltaAccess().getLeftCurlyBracketKeyword_5(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1714:1: ( (lv_classesList_10_0= ruleClassm ) )*
            loop26:
            do {
                int alt26=2;
                int LA26_0 = input.LA(1);

                if ( ((LA26_0>=37 && LA26_0<=39)) ) {
                    alt26=1;
                }


                switch (alt26) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1715:1: (lv_classesList_10_0= ruleClassm )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1715:1: (lv_classesList_10_0= ruleClassm )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1716:3: lv_classesList_10_0= ruleClassm
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getDeltaAccess().getClassesListClassmParserRuleCall_6_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleClassm_in_ruleDelta2780);
            	    lv_classesList_10_0=ruleClassm();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getDeltaRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"classesList",
            	    	        		lv_classesList_10_0, 
            	    	        		"Classm", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }
            	    break;

            	default :
            	    break loop26;
                }
            } while (true);

            match(input,19,FOLLOW_19_in_ruleDelta2791); 

                    createLeafNode(grammarAccess.getDeltaAccess().getRightCurlyBracketKeyword_7(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleDelta


    // $ANTLR start entryRuleConfiguration
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1750:1: entryRuleConfiguration returns [EObject current=null] : iv_ruleConfiguration= ruleConfiguration EOF ;
    public final EObject entryRuleConfiguration() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleConfiguration = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1751:2: (iv_ruleConfiguration= ruleConfiguration EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1752:2: iv_ruleConfiguration= ruleConfiguration EOF
            {
             currentNode = createCompositeNode(grammarAccess.getConfigurationRule(), currentNode); 
            pushFollow(FOLLOW_ruleConfiguration_in_entryRuleConfiguration2827);
            iv_ruleConfiguration=ruleConfiguration();
            _fsp--;

             current =iv_ruleConfiguration; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleConfiguration2837); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleConfiguration


    // $ANTLR start ruleConfiguration
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1759:1: ruleConfiguration returns [EObject current=null] : ( ( (lv_featureList_0_0= ruleConfig ) ) ';' )+ ;
    public final EObject ruleConfiguration() throws RecognitionException {
        EObject current = null;

        EObject lv_featureList_0_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1764:6: ( ( ( (lv_featureList_0_0= ruleConfig ) ) ';' )+ )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1765:1: ( ( (lv_featureList_0_0= ruleConfig ) ) ';' )+
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1765:1: ( ( (lv_featureList_0_0= ruleConfig ) ) ';' )+
            int cnt27=0;
            loop27:
            do {
                int alt27=2;
                int LA27_0 = input.LA(1);

                if ( (LA27_0==RULE_ID) ) {
                    alt27=1;
                }


                switch (alt27) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1765:2: ( (lv_featureList_0_0= ruleConfig ) ) ';'
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1765:2: ( (lv_featureList_0_0= ruleConfig ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1766:1: (lv_featureList_0_0= ruleConfig )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1766:1: (lv_featureList_0_0= ruleConfig )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1767:3: lv_featureList_0_0= ruleConfig
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getConfigurationAccess().getFeatureListConfigParserRuleCall_0_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleConfig_in_ruleConfiguration2883);
            	    lv_featureList_0_0=ruleConfig();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getConfigurationRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"featureList",
            	    	        		lv_featureList_0_0, 
            	    	        		"Config", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }

            	    match(input,25,FOLLOW_25_in_ruleConfiguration2893); 

            	            createLeafNode(grammarAccess.getConfigurationAccess().getSemicolonKeyword_1(), null); 
            	        

            	    }
            	    break;

            	default :
            	    if ( cnt27 >= 1 ) break loop27;
                        EarlyExitException eee =
                            new EarlyExitException(27, input);
                        throw eee;
                }
                cnt27++;
            } while (true);


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleConfiguration


    // $ANTLR start entryRuleConfig
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1801:1: entryRuleConfig returns [EObject current=null] : iv_ruleConfig= ruleConfig EOF ;
    public final EObject entryRuleConfig() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleConfig = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1802:2: (iv_ruleConfig= ruleConfig EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1803:2: iv_ruleConfig= ruleConfig EOF
            {
             currentNode = createCompositeNode(grammarAccess.getConfigRule(), currentNode); 
            pushFollow(FOLLOW_ruleConfig_in_entryRuleConfig2930);
            iv_ruleConfig=ruleConfig();
            _fsp--;

             current =iv_ruleConfig; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleConfig2940); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleConfig


    // $ANTLR start ruleConfig
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1810:1: ruleConfig returns [EObject current=null] : ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* ) ;
    public final EObject ruleConfig() throws RecognitionException {
        EObject current = null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1815:6: ( ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1816:1: ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1816:1: ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1816:2: ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )*
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1816:2: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1817:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1817:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1818:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getConfigRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleConfig2983); 

            		createLeafNode(grammarAccess.getConfigAccess().getFeatureFeatureCrossReference_0_0(), "feature"); 
            	

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1830:2: ( ',' ( ( RULE_ID ) ) )*
            loop28:
            do {
                int alt28=2;
                int LA28_0 = input.LA(1);

                if ( (LA28_0==14) ) {
                    alt28=1;
                }


                switch (alt28) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1830:4: ',' ( ( RULE_ID ) )
            	    {
            	    match(input,14,FOLLOW_14_in_ruleConfig2994); 

            	            createLeafNode(grammarAccess.getConfigAccess().getCommaKeyword_1_0(), null); 
            	        
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1834:1: ( ( RULE_ID ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1835:1: ( RULE_ID )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1835:1: ( RULE_ID )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1836:3: RULE_ID
            	    {

            	    			if (current==null) {
            	    	            current = factory.create(grammarAccess.getConfigRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode, current);
            	    	        }
            	            
            	    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleConfig3012); 

            	    		createLeafNode(grammarAccess.getConfigAccess().getFeatureFeatureCrossReference_1_1_0(), "feature"); 
            	    	

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop28;
                }
            } while (true);


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleConfig


    // $ANTLR start entryRuleOperation
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1856:1: entryRuleOperation returns [String current=null] : iv_ruleOperation= ruleOperation EOF ;
    public final String entryRuleOperation() throws RecognitionException {
        String current = null;

        AntlrDatatypeRuleToken iv_ruleOperation = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1857:2: (iv_ruleOperation= ruleOperation EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1858:2: iv_ruleOperation= ruleOperation EOF
            {
             currentNode = createCompositeNode(grammarAccess.getOperationRule(), currentNode); 
            pushFollow(FOLLOW_ruleOperation_in_entryRuleOperation3051);
            iv_ruleOperation=ruleOperation();
            _fsp--;

             current =iv_ruleOperation.getText(); 
            match(input,EOF,FOLLOW_EOF_in_entryRuleOperation3062); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleOperation


    // $ANTLR start ruleOperation
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1865:1: ruleOperation returns [AntlrDatatypeRuleToken current=new AntlrDatatypeRuleToken()] : (kw= '&&' | kw= '||' | kw= '->' | kw= '<->' ) ;
    public final AntlrDatatypeRuleToken ruleOperation() throws RecognitionException {
        AntlrDatatypeRuleToken current = new AntlrDatatypeRuleToken();

        Token kw=null;

         setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1870:6: ( (kw= '&&' | kw= '||' | kw= '->' | kw= '<->' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1871:1: (kw= '&&' | kw= '||' | kw= '->' | kw= '<->' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1871:1: (kw= '&&' | kw= '||' | kw= '->' | kw= '<->' )
            int alt29=4;
            switch ( input.LA(1) ) {
            case 32:
                {
                alt29=1;
                }
                break;
            case 33:
                {
                alt29=2;
                }
                break;
            case 34:
                {
                alt29=3;
                }
                break;
            case 35:
                {
                alt29=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1871:1: (kw= '&&' | kw= '||' | kw= '->' | kw= '<->' )", 29, 0, input);

                throw nvae;
            }

            switch (alt29) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1872:2: kw= '&&'
                    {
                    kw=(Token)input.LT(1);
                    match(input,32,FOLLOW_32_in_ruleOperation3100); 

                            current.merge(kw);
                            createLeafNode(grammarAccess.getOperationAccess().getAmpersandAmpersandKeyword_0(), null); 
                        

                    }
                    break;
                case 2 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1879:2: kw= '||'
                    {
                    kw=(Token)input.LT(1);
                    match(input,33,FOLLOW_33_in_ruleOperation3119); 

                            current.merge(kw);
                            createLeafNode(grammarAccess.getOperationAccess().getVerticalLineVerticalLineKeyword_1(), null); 
                        

                    }
                    break;
                case 3 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1886:2: kw= '->'
                    {
                    kw=(Token)input.LT(1);
                    match(input,34,FOLLOW_34_in_ruleOperation3138); 

                            current.merge(kw);
                            createLeafNode(grammarAccess.getOperationAccess().getHyphenMinusGreaterThanSignKeyword_2(), null); 
                        

                    }
                    break;
                case 4 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1893:2: kw= '<->'
                    {
                    kw=(Token)input.LT(1);
                    match(input,35,FOLLOW_35_in_ruleOperation3157); 

                            current.merge(kw);
                            createLeafNode(grammarAccess.getOperationAccess().getLessThanSignHyphenMinusGreaterThanSignKeyword_3(), null); 
                        

                    }
                    break;

            }


            }

             resetLookahead(); 
            	    lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleOperation


    // $ANTLR start entryRuleCondition
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1906:1: entryRuleCondition returns [EObject current=null] : iv_ruleCondition= ruleCondition EOF ;
    public final EObject entryRuleCondition() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleCondition = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1907:2: (iv_ruleCondition= ruleCondition EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1908:2: iv_ruleCondition= ruleCondition EOF
            {
             currentNode = createCompositeNode(grammarAccess.getConditionRule(), currentNode); 
            pushFollow(FOLLOW_ruleCondition_in_entryRuleCondition3197);
            iv_ruleCondition=ruleCondition();
            _fsp--;

             current =iv_ruleCondition; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleCondition3207); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleCondition


    // $ANTLR start ruleCondition
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1915:1: ruleCondition returns [EObject current=null] : ( ( (lv_complement_0_0= '!' ) )? ( ( '(' ( (lv_condition1_2_0= ruleCondition ) ) ( (lv_operation_3_0= ruleOperation ) ) ( (lv_condition2_4_0= ruleCondition ) ) ')' ) | ( ( RULE_ID ) ) ) ) ;
    public final EObject ruleCondition() throws RecognitionException {
        EObject current = null;

        Token lv_complement_0_0=null;
        EObject lv_condition1_2_0 = null;

        AntlrDatatypeRuleToken lv_operation_3_0 = null;

        EObject lv_condition2_4_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1920:6: ( ( ( (lv_complement_0_0= '!' ) )? ( ( '(' ( (lv_condition1_2_0= ruleCondition ) ) ( (lv_operation_3_0= ruleOperation ) ) ( (lv_condition2_4_0= ruleCondition ) ) ')' ) | ( ( RULE_ID ) ) ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1921:1: ( ( (lv_complement_0_0= '!' ) )? ( ( '(' ( (lv_condition1_2_0= ruleCondition ) ) ( (lv_operation_3_0= ruleOperation ) ) ( (lv_condition2_4_0= ruleCondition ) ) ')' ) | ( ( RULE_ID ) ) ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1921:1: ( ( (lv_complement_0_0= '!' ) )? ( ( '(' ( (lv_condition1_2_0= ruleCondition ) ) ( (lv_operation_3_0= ruleOperation ) ) ( (lv_condition2_4_0= ruleCondition ) ) ')' ) | ( ( RULE_ID ) ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1921:2: ( (lv_complement_0_0= '!' ) )? ( ( '(' ( (lv_condition1_2_0= ruleCondition ) ) ( (lv_operation_3_0= ruleOperation ) ) ( (lv_condition2_4_0= ruleCondition ) ) ')' ) | ( ( RULE_ID ) ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1921:2: ( (lv_complement_0_0= '!' ) )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==36) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1922:1: (lv_complement_0_0= '!' )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1922:1: (lv_complement_0_0= '!' )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1923:3: lv_complement_0_0= '!'
                    {
                    lv_complement_0_0=(Token)input.LT(1);
                    match(input,36,FOLLOW_36_in_ruleCondition3250); 

                            createLeafNode(grammarAccess.getConditionAccess().getComplementExclamationMarkKeyword_0_0(), "complement"); 
                        

                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getConditionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                    	        
                    	        try {
                    	       		set(current, "complement", lv_complement_0_0, "!", lastConsumedNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	    

                    }


                    }
                    break;

            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1942:3: ( ( '(' ( (lv_condition1_2_0= ruleCondition ) ) ( (lv_operation_3_0= ruleOperation ) ) ( (lv_condition2_4_0= ruleCondition ) ) ')' ) | ( ( RULE_ID ) ) )
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( (LA31_0==22) ) {
                alt31=1;
            }
            else if ( (LA31_0==RULE_ID) ) {
                alt31=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1942:3: ( ( '(' ( (lv_condition1_2_0= ruleCondition ) ) ( (lv_operation_3_0= ruleOperation ) ) ( (lv_condition2_4_0= ruleCondition ) ) ')' ) | ( ( RULE_ID ) ) )", 31, 0, input);

                throw nvae;
            }
            switch (alt31) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1942:4: ( '(' ( (lv_condition1_2_0= ruleCondition ) ) ( (lv_operation_3_0= ruleOperation ) ) ( (lv_condition2_4_0= ruleCondition ) ) ')' )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1942:4: ( '(' ( (lv_condition1_2_0= ruleCondition ) ) ( (lv_operation_3_0= ruleOperation ) ) ( (lv_condition2_4_0= ruleCondition ) ) ')' )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1942:6: '(' ( (lv_condition1_2_0= ruleCondition ) ) ( (lv_operation_3_0= ruleOperation ) ) ( (lv_condition2_4_0= ruleCondition ) ) ')'
                    {
                    match(input,22,FOLLOW_22_in_ruleCondition3276); 

                            createLeafNode(grammarAccess.getConditionAccess().getLeftParenthesisKeyword_1_0_0(), null); 
                        
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1946:1: ( (lv_condition1_2_0= ruleCondition ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1947:1: (lv_condition1_2_0= ruleCondition )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1947:1: (lv_condition1_2_0= ruleCondition )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1948:3: lv_condition1_2_0= ruleCondition
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getConditionAccess().getCondition1ConditionParserRuleCall_1_0_1_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleCondition_in_ruleCondition3297);
                    lv_condition1_2_0=ruleCondition();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getConditionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"condition1",
                    	        		lv_condition1_2_0, 
                    	        		"Condition", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1970:2: ( (lv_operation_3_0= ruleOperation ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1971:1: (lv_operation_3_0= ruleOperation )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1971:1: (lv_operation_3_0= ruleOperation )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1972:3: lv_operation_3_0= ruleOperation
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getConditionAccess().getOperationOperationParserRuleCall_1_0_2_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleOperation_in_ruleCondition3318);
                    lv_operation_3_0=ruleOperation();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getConditionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"operation",
                    	        		lv_operation_3_0, 
                    	        		"Operation", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1994:2: ( (lv_condition2_4_0= ruleCondition ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1995:1: (lv_condition2_4_0= ruleCondition )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1995:1: (lv_condition2_4_0= ruleCondition )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:1996:3: lv_condition2_4_0= ruleCondition
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getConditionAccess().getCondition2ConditionParserRuleCall_1_0_3_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleCondition_in_ruleCondition3339);
                    lv_condition2_4_0=ruleCondition();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getConditionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"condition2",
                    	        		lv_condition2_4_0, 
                    	        		"Condition", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }

                    match(input,23,FOLLOW_23_in_ruleCondition3349); 

                            createLeafNode(grammarAccess.getConditionAccess().getRightParenthesisKeyword_1_0_4(), null); 
                        

                    }


                    }
                    break;
                case 2 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2023:6: ( ( RULE_ID ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2023:6: ( ( RULE_ID ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2024:1: ( RULE_ID )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2024:1: ( RULE_ID )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2025:3: RULE_ID
                    {

                    			if (current==null) {
                    	            current = factory.create(grammarAccess.getConditionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                            
                    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleCondition3374); 

                    		createLeafNode(grammarAccess.getConditionAccess().getFeatureFeatureCrossReference_1_1_0(), "feature"); 
                    	

                    }


                    }


                    }
                    break;

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleCondition


    // $ANTLR start entryRuleClassm
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2045:1: entryRuleClassm returns [EObject current=null] : iv_ruleClassm= ruleClassm EOF ;
    public final EObject entryRuleClassm() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleClassm = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2046:2: (iv_ruleClassm= ruleClassm EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2047:2: iv_ruleClassm= ruleClassm EOF
            {
             currentNode = createCompositeNode(grammarAccess.getClassmRule(), currentNode); 
            pushFollow(FOLLOW_ruleClassm_in_entryRuleClassm3411);
            iv_ruleClassm=ruleClassm();
            _fsp--;

             current =iv_ruleClassm; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleClassm3421); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleClassm


    // $ANTLR start ruleClassm
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2054:1: ruleClassm returns [EObject current=null] : ( ( ( (lv_action_0_0= 'modifies' ) ) ( (lv_modifies_1_0= ruleModifiesClass ) ) ) | ( ( (lv_action_2_0= 'adds' ) ) ( (lv_adds_3_0= ruleAddsClass ) ) ) | ( ( (lv_action_4_0= 'remove' ) ) ( (lv_remove_5_0= ruleRemoveClass ) ) ) ) ;
    public final EObject ruleClassm() throws RecognitionException {
        EObject current = null;

        Token lv_action_0_0=null;
        Token lv_action_2_0=null;
        Token lv_action_4_0=null;
        EObject lv_modifies_1_0 = null;

        EObject lv_adds_3_0 = null;

        EObject lv_remove_5_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2059:6: ( ( ( ( (lv_action_0_0= 'modifies' ) ) ( (lv_modifies_1_0= ruleModifiesClass ) ) ) | ( ( (lv_action_2_0= 'adds' ) ) ( (lv_adds_3_0= ruleAddsClass ) ) ) | ( ( (lv_action_4_0= 'remove' ) ) ( (lv_remove_5_0= ruleRemoveClass ) ) ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2060:1: ( ( ( (lv_action_0_0= 'modifies' ) ) ( (lv_modifies_1_0= ruleModifiesClass ) ) ) | ( ( (lv_action_2_0= 'adds' ) ) ( (lv_adds_3_0= ruleAddsClass ) ) ) | ( ( (lv_action_4_0= 'remove' ) ) ( (lv_remove_5_0= ruleRemoveClass ) ) ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2060:1: ( ( ( (lv_action_0_0= 'modifies' ) ) ( (lv_modifies_1_0= ruleModifiesClass ) ) ) | ( ( (lv_action_2_0= 'adds' ) ) ( (lv_adds_3_0= ruleAddsClass ) ) ) | ( ( (lv_action_4_0= 'remove' ) ) ( (lv_remove_5_0= ruleRemoveClass ) ) ) )
            int alt32=3;
            switch ( input.LA(1) ) {
            case 37:
                {
                alt32=1;
                }
                break;
            case 38:
                {
                alt32=2;
                }
                break;
            case 39:
                {
                alt32=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("2060:1: ( ( ( (lv_action_0_0= 'modifies' ) ) ( (lv_modifies_1_0= ruleModifiesClass ) ) ) | ( ( (lv_action_2_0= 'adds' ) ) ( (lv_adds_3_0= ruleAddsClass ) ) ) | ( ( (lv_action_4_0= 'remove' ) ) ( (lv_remove_5_0= ruleRemoveClass ) ) ) )", 32, 0, input);

                throw nvae;
            }

            switch (alt32) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2060:2: ( ( (lv_action_0_0= 'modifies' ) ) ( (lv_modifies_1_0= ruleModifiesClass ) ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2060:2: ( ( (lv_action_0_0= 'modifies' ) ) ( (lv_modifies_1_0= ruleModifiesClass ) ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2060:3: ( (lv_action_0_0= 'modifies' ) ) ( (lv_modifies_1_0= ruleModifiesClass ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2060:3: ( (lv_action_0_0= 'modifies' ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2061:1: (lv_action_0_0= 'modifies' )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2061:1: (lv_action_0_0= 'modifies' )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2062:3: lv_action_0_0= 'modifies'
                    {
                    lv_action_0_0=(Token)input.LT(1);
                    match(input,37,FOLLOW_37_in_ruleClassm3465); 

                            createLeafNode(grammarAccess.getClassmAccess().getActionModifiesKeyword_0_0_0(), "action"); 
                        

                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getClassmRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                    	        
                    	        try {
                    	       		set(current, "action", lv_action_0_0, "modifies", lastConsumedNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2081:2: ( (lv_modifies_1_0= ruleModifiesClass ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2082:1: (lv_modifies_1_0= ruleModifiesClass )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2082:1: (lv_modifies_1_0= ruleModifiesClass )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2083:3: lv_modifies_1_0= ruleModifiesClass
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getClassmAccess().getModifiesModifiesClassParserRuleCall_0_1_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleModifiesClass_in_ruleClassm3499);
                    lv_modifies_1_0=ruleModifiesClass();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getClassmRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"modifies",
                    	        		lv_modifies_1_0, 
                    	        		"ModifiesClass", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }


                    }
                    break;
                case 2 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2106:6: ( ( (lv_action_2_0= 'adds' ) ) ( (lv_adds_3_0= ruleAddsClass ) ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2106:6: ( ( (lv_action_2_0= 'adds' ) ) ( (lv_adds_3_0= ruleAddsClass ) ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2106:7: ( (lv_action_2_0= 'adds' ) ) ( (lv_adds_3_0= ruleAddsClass ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2106:7: ( (lv_action_2_0= 'adds' ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2107:1: (lv_action_2_0= 'adds' )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2107:1: (lv_action_2_0= 'adds' )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2108:3: lv_action_2_0= 'adds'
                    {
                    lv_action_2_0=(Token)input.LT(1);
                    match(input,38,FOLLOW_38_in_ruleClassm3525); 

                            createLeafNode(grammarAccess.getClassmAccess().getActionAddsKeyword_1_0_0(), "action"); 
                        

                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getClassmRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                    	        
                    	        try {
                    	       		set(current, "action", lv_action_2_0, "adds", lastConsumedNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2127:2: ( (lv_adds_3_0= ruleAddsClass ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2128:1: (lv_adds_3_0= ruleAddsClass )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2128:1: (lv_adds_3_0= ruleAddsClass )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2129:3: lv_adds_3_0= ruleAddsClass
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getClassmAccess().getAddsAddsClassParserRuleCall_1_1_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleAddsClass_in_ruleClassm3559);
                    lv_adds_3_0=ruleAddsClass();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getClassmRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"adds",
                    	        		lv_adds_3_0, 
                    	        		"AddsClass", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }


                    }
                    break;
                case 3 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2152:6: ( ( (lv_action_4_0= 'remove' ) ) ( (lv_remove_5_0= ruleRemoveClass ) ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2152:6: ( ( (lv_action_4_0= 'remove' ) ) ( (lv_remove_5_0= ruleRemoveClass ) ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2152:7: ( (lv_action_4_0= 'remove' ) ) ( (lv_remove_5_0= ruleRemoveClass ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2152:7: ( (lv_action_4_0= 'remove' ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2153:1: (lv_action_4_0= 'remove' )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2153:1: (lv_action_4_0= 'remove' )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2154:3: lv_action_4_0= 'remove'
                    {
                    lv_action_4_0=(Token)input.LT(1);
                    match(input,39,FOLLOW_39_in_ruleClassm3585); 

                            createLeafNode(grammarAccess.getClassmAccess().getActionRemoveKeyword_2_0_0(), "action"); 
                        

                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getClassmRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                    	        
                    	        try {
                    	       		set(current, "action", lv_action_4_0, "remove", lastConsumedNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2173:2: ( (lv_remove_5_0= ruleRemoveClass ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2174:1: (lv_remove_5_0= ruleRemoveClass )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2174:1: (lv_remove_5_0= ruleRemoveClass )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2175:3: lv_remove_5_0= ruleRemoveClass
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getClassmAccess().getRemoveRemoveClassParserRuleCall_2_1_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleRemoveClass_in_ruleClassm3619);
                    lv_remove_5_0=ruleRemoveClass();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getClassmRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"remove",
                    	        		lv_remove_5_0, 
                    	        		"RemoveClass", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }


                    }
                    break;

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleClassm


    // $ANTLR start entryRuleModifiesClass
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2205:1: entryRuleModifiesClass returns [EObject current=null] : iv_ruleModifiesClass= ruleModifiesClass EOF ;
    public final EObject entryRuleModifiesClass() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleModifiesClass = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2206:2: (iv_ruleModifiesClass= ruleModifiesClass EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2207:2: iv_ruleModifiesClass= ruleModifiesClass EOF
            {
             currentNode = createCompositeNode(grammarAccess.getModifiesClassRule(), currentNode); 
            pushFollow(FOLLOW_ruleModifiesClass_in_entryRuleModifiesClass3656);
            iv_ruleModifiesClass=ruleModifiesClass();
            _fsp--;

             current =iv_ruleModifiesClass; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleModifiesClass3666); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleModifiesClass


    // $ANTLR start ruleModifiesClass
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2214:1: ruleModifiesClass returns [EObject current=null] : ( 'class' ( ( RULE_ID ) ) ( 'extending' ( ( RULE_ID ) ) )? '{' ( (lv_field_5_0= ruleFieldm ) ) ( (lv_constructor_6_0= ruleConstructor ) )? ( (lv_method_7_0= ruleMethodm ) ) '}' ) ;
    public final EObject ruleModifiesClass() throws RecognitionException {
        EObject current = null;

        EObject lv_field_5_0 = null;

        EObject lv_constructor_6_0 = null;

        EObject lv_method_7_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2219:6: ( ( 'class' ( ( RULE_ID ) ) ( 'extending' ( ( RULE_ID ) ) )? '{' ( (lv_field_5_0= ruleFieldm ) ) ( (lv_constructor_6_0= ruleConstructor ) )? ( (lv_method_7_0= ruleMethodm ) ) '}' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2220:1: ( 'class' ( ( RULE_ID ) ) ( 'extending' ( ( RULE_ID ) ) )? '{' ( (lv_field_5_0= ruleFieldm ) ) ( (lv_constructor_6_0= ruleConstructor ) )? ( (lv_method_7_0= ruleMethodm ) ) '}' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2220:1: ( 'class' ( ( RULE_ID ) ) ( 'extending' ( ( RULE_ID ) ) )? '{' ( (lv_field_5_0= ruleFieldm ) ) ( (lv_constructor_6_0= ruleConstructor ) )? ( (lv_method_7_0= ruleMethodm ) ) '}' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2220:3: 'class' ( ( RULE_ID ) ) ( 'extending' ( ( RULE_ID ) ) )? '{' ( (lv_field_5_0= ruleFieldm ) ) ( (lv_constructor_6_0= ruleConstructor ) )? ( (lv_method_7_0= ruleMethodm ) ) '}'
            {
            match(input,20,FOLLOW_20_in_ruleModifiesClass3701); 

                    createLeafNode(grammarAccess.getModifiesClassAccess().getClassKeyword_0(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2224:1: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2225:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2225:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2226:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getModifiesClassRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleModifiesClass3719); 

            		createLeafNode(grammarAccess.getModifiesClassAccess().getClassClassCrossReference_1_0(), "class"); 
            	

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2238:2: ( 'extending' ( ( RULE_ID ) ) )?
            int alt33=2;
            int LA33_0 = input.LA(1);

            if ( (LA33_0==40) ) {
                alt33=1;
            }
            switch (alt33) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2238:4: 'extending' ( ( RULE_ID ) )
                    {
                    match(input,40,FOLLOW_40_in_ruleModifiesClass3730); 

                            createLeafNode(grammarAccess.getModifiesClassAccess().getExtendingKeyword_2_0(), null); 
                        
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2242:1: ( ( RULE_ID ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2243:1: ( RULE_ID )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2243:1: ( RULE_ID )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2244:3: RULE_ID
                    {

                    			if (current==null) {
                    	            current = factory.create(grammarAccess.getModifiesClassRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                            
                    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleModifiesClass3748); 

                    		createLeafNode(grammarAccess.getModifiesClassAccess().getExtendsClassCrossReference_2_1_0(), "extends"); 
                    	

                    }


                    }


                    }
                    break;

            }

            match(input,18,FOLLOW_18_in_ruleModifiesClass3760); 

                    createLeafNode(grammarAccess.getModifiesClassAccess().getLeftCurlyBracketKeyword_3(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2260:1: ( (lv_field_5_0= ruleFieldm ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2261:1: (lv_field_5_0= ruleFieldm )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2261:1: (lv_field_5_0= ruleFieldm )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2262:3: lv_field_5_0= ruleFieldm
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getModifiesClassAccess().getFieldFieldmParserRuleCall_4_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleFieldm_in_ruleModifiesClass3781);
            lv_field_5_0=ruleFieldm();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getModifiesClassRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"field",
            	        		lv_field_5_0, 
            	        		"Fieldm", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2284:2: ( (lv_constructor_6_0= ruleConstructor ) )?
            int alt34=2;
            int LA34_0 = input.LA(1);

            if ( (LA34_0==RULE_ID) ) {
                alt34=1;
            }
            switch (alt34) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2285:1: (lv_constructor_6_0= ruleConstructor )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2285:1: (lv_constructor_6_0= ruleConstructor )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2286:3: lv_constructor_6_0= ruleConstructor
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getModifiesClassAccess().getConstructorConstructorParserRuleCall_5_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleConstructor_in_ruleModifiesClass3802);
                    lv_constructor_6_0=ruleConstructor();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getModifiesClassRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"constructor",
                    	        		lv_constructor_6_0, 
                    	        		"Constructor", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }
                    break;

            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2308:3: ( (lv_method_7_0= ruleMethodm ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2309:1: (lv_method_7_0= ruleMethodm )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2309:1: (lv_method_7_0= ruleMethodm )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2310:3: lv_method_7_0= ruleMethodm
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getModifiesClassAccess().getMethodMethodmParserRuleCall_6_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleMethodm_in_ruleModifiesClass3824);
            lv_method_7_0=ruleMethodm();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getModifiesClassRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"method",
            	        		lv_method_7_0, 
            	        		"Methodm", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            match(input,19,FOLLOW_19_in_ruleModifiesClass3834); 

                    createLeafNode(grammarAccess.getModifiesClassAccess().getRightCurlyBracketKeyword_7(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleModifiesClass


    // $ANTLR start entryRuleAddsClass
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2344:1: entryRuleAddsClass returns [EObject current=null] : iv_ruleAddsClass= ruleAddsClass EOF ;
    public final EObject entryRuleAddsClass() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAddsClass = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2345:2: (iv_ruleAddsClass= ruleAddsClass EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2346:2: iv_ruleAddsClass= ruleAddsClass EOF
            {
             currentNode = createCompositeNode(grammarAccess.getAddsClassRule(), currentNode); 
            pushFollow(FOLLOW_ruleAddsClass_in_entryRuleAddsClass3870);
            iv_ruleAddsClass=ruleAddsClass();
            _fsp--;

             current =iv_ruleAddsClass; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleAddsClass3880); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleAddsClass


    // $ANTLR start ruleAddsClass
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2353:1: ruleAddsClass returns [EObject current=null] : ( (lv_class_0_0= ruleClass ) ) ;
    public final EObject ruleAddsClass() throws RecognitionException {
        EObject current = null;

        EObject lv_class_0_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2358:6: ( ( (lv_class_0_0= ruleClass ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2359:1: ( (lv_class_0_0= ruleClass ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2359:1: ( (lv_class_0_0= ruleClass ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2360:1: (lv_class_0_0= ruleClass )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2360:1: (lv_class_0_0= ruleClass )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2361:3: lv_class_0_0= ruleClass
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getAddsClassAccess().getClassClassParserRuleCall_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleClass_in_ruleAddsClass3925);
            lv_class_0_0=ruleClass();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getAddsClassRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"class",
            	        		lv_class_0_0, 
            	        		"Class", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleAddsClass


    // $ANTLR start entryRuleRemoveClass
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2391:1: entryRuleRemoveClass returns [EObject current=null] : iv_ruleRemoveClass= ruleRemoveClass EOF ;
    public final EObject entryRuleRemoveClass() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleRemoveClass = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2392:2: (iv_ruleRemoveClass= ruleRemoveClass EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2393:2: iv_ruleRemoveClass= ruleRemoveClass EOF
            {
             currentNode = createCompositeNode(grammarAccess.getRemoveClassRule(), currentNode); 
            pushFollow(FOLLOW_ruleRemoveClass_in_entryRuleRemoveClass3960);
            iv_ruleRemoveClass=ruleRemoveClass();
            _fsp--;

             current =iv_ruleRemoveClass; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleRemoveClass3970); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleRemoveClass


    // $ANTLR start ruleRemoveClass
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2400:1: ruleRemoveClass returns [EObject current=null] : ( ( RULE_ID ) ) ;
    public final EObject ruleRemoveClass() throws RecognitionException {
        EObject current = null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2405:6: ( ( ( RULE_ID ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2406:1: ( ( RULE_ID ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2406:1: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2407:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2407:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2408:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getRemoveClassRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleRemoveClass4012); 

            		createLeafNode(grammarAccess.getRemoveClassAccess().getClassClassCrossReference_0(), "class"); 
            	

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleRemoveClass


    // $ANTLR start entryRuleMethodm
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2428:1: entryRuleMethodm returns [EObject current=null] : iv_ruleMethodm= ruleMethodm EOF ;
    public final EObject entryRuleMethodm() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMethodm = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2429:2: (iv_ruleMethodm= ruleMethodm EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2430:2: iv_ruleMethodm= ruleMethodm EOF
            {
             currentNode = createCompositeNode(grammarAccess.getMethodmRule(), currentNode); 
            pushFollow(FOLLOW_ruleMethodm_in_entryRuleMethodm4047);
            iv_ruleMethodm=ruleMethodm();
            _fsp--;

             current =iv_ruleMethodm; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleMethodm4057); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleMethodm


    // $ANTLR start ruleMethodm
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2437:1: ruleMethodm returns [EObject current=null] : ( () ( 'remove' ( (lv_removeList_2_0= ruleRemovesMethod ) ) )* ( 'modifies' ( (lv_modifiesList_4_0= ruleModifiesMethod ) ) )* ( 'adds' ( (lv_addsList_6_0= ruleAddsMethod ) ) )* ) ;
    public final EObject ruleMethodm() throws RecognitionException {
        EObject current = null;

        EObject lv_removeList_2_0 = null;

        EObject lv_modifiesList_4_0 = null;

        EObject lv_addsList_6_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2442:6: ( ( () ( 'remove' ( (lv_removeList_2_0= ruleRemovesMethod ) ) )* ( 'modifies' ( (lv_modifiesList_4_0= ruleModifiesMethod ) ) )* ( 'adds' ( (lv_addsList_6_0= ruleAddsMethod ) ) )* ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2443:1: ( () ( 'remove' ( (lv_removeList_2_0= ruleRemovesMethod ) ) )* ( 'modifies' ( (lv_modifiesList_4_0= ruleModifiesMethod ) ) )* ( 'adds' ( (lv_addsList_6_0= ruleAddsMethod ) ) )* )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2443:1: ( () ( 'remove' ( (lv_removeList_2_0= ruleRemovesMethod ) ) )* ( 'modifies' ( (lv_modifiesList_4_0= ruleModifiesMethod ) ) )* ( 'adds' ( (lv_addsList_6_0= ruleAddsMethod ) ) )* )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2443:2: () ( 'remove' ( (lv_removeList_2_0= ruleRemovesMethod ) ) )* ( 'modifies' ( (lv_modifiesList_4_0= ruleModifiesMethod ) ) )* ( 'adds' ( (lv_addsList_6_0= ruleAddsMethod ) ) )*
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2443:2: ()
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2444:5: 
            {
             
                    temp=factory.create(grammarAccess.getMethodmAccess().getMethodmAction_0().getType().getClassifier());
                    current = temp; 
                    temp = null;
                    CompositeNode newNode = createCompositeNode(grammarAccess.getMethodmAccess().getMethodmAction_0(), currentNode.getParent());
                newNode.getChildren().add(currentNode);
                moveLookaheadInfo(currentNode, newNode);
                currentNode = newNode; 
                    associateNodeWithAstElement(currentNode, current); 
                

            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2454:2: ( 'remove' ( (lv_removeList_2_0= ruleRemovesMethod ) ) )*
            loop35:
            do {
                int alt35=2;
                int LA35_0 = input.LA(1);

                if ( (LA35_0==39) ) {
                    alt35=1;
                }


                switch (alt35) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2454:4: 'remove' ( (lv_removeList_2_0= ruleRemovesMethod ) )
            	    {
            	    match(input,39,FOLLOW_39_in_ruleMethodm4102); 

            	            createLeafNode(grammarAccess.getMethodmAccess().getRemoveKeyword_1_0(), null); 
            	        
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2458:1: ( (lv_removeList_2_0= ruleRemovesMethod ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2459:1: (lv_removeList_2_0= ruleRemovesMethod )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2459:1: (lv_removeList_2_0= ruleRemovesMethod )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2460:3: lv_removeList_2_0= ruleRemovesMethod
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getMethodmAccess().getRemoveListRemovesMethodParserRuleCall_1_1_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleRemovesMethod_in_ruleMethodm4123);
            	    lv_removeList_2_0=ruleRemovesMethod();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getMethodmRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"removeList",
            	    	        		lv_removeList_2_0, 
            	    	        		"RemovesMethod", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop35;
                }
            } while (true);

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2482:4: ( 'modifies' ( (lv_modifiesList_4_0= ruleModifiesMethod ) ) )*
            loop36:
            do {
                int alt36=2;
                int LA36_0 = input.LA(1);

                if ( (LA36_0==37) ) {
                    alt36=1;
                }


                switch (alt36) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2482:6: 'modifies' ( (lv_modifiesList_4_0= ruleModifiesMethod ) )
            	    {
            	    match(input,37,FOLLOW_37_in_ruleMethodm4136); 

            	            createLeafNode(grammarAccess.getMethodmAccess().getModifiesKeyword_2_0(), null); 
            	        
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2486:1: ( (lv_modifiesList_4_0= ruleModifiesMethod ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2487:1: (lv_modifiesList_4_0= ruleModifiesMethod )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2487:1: (lv_modifiesList_4_0= ruleModifiesMethod )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2488:3: lv_modifiesList_4_0= ruleModifiesMethod
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getMethodmAccess().getModifiesListModifiesMethodParserRuleCall_2_1_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleModifiesMethod_in_ruleMethodm4157);
            	    lv_modifiesList_4_0=ruleModifiesMethod();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getMethodmRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"modifiesList",
            	    	        		lv_modifiesList_4_0, 
            	    	        		"ModifiesMethod", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop36;
                }
            } while (true);

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2510:4: ( 'adds' ( (lv_addsList_6_0= ruleAddsMethod ) ) )*
            loop37:
            do {
                int alt37=2;
                int LA37_0 = input.LA(1);

                if ( (LA37_0==38) ) {
                    alt37=1;
                }


                switch (alt37) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2510:6: 'adds' ( (lv_addsList_6_0= ruleAddsMethod ) )
            	    {
            	    match(input,38,FOLLOW_38_in_ruleMethodm4170); 

            	            createLeafNode(grammarAccess.getMethodmAccess().getAddsKeyword_3_0(), null); 
            	        
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2514:1: ( (lv_addsList_6_0= ruleAddsMethod ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2515:1: (lv_addsList_6_0= ruleAddsMethod )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2515:1: (lv_addsList_6_0= ruleAddsMethod )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2516:3: lv_addsList_6_0= ruleAddsMethod
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getMethodmAccess().getAddsListAddsMethodParserRuleCall_3_1_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleAddsMethod_in_ruleMethodm4191);
            	    lv_addsList_6_0=ruleAddsMethod();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getMethodmRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"addsList",
            	    	        		lv_addsList_6_0, 
            	    	        		"AddsMethod", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop37;
                }
            } while (true);


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleMethodm


    // $ANTLR start entryRuleAddsMethod
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2546:1: entryRuleAddsMethod returns [EObject current=null] : iv_ruleAddsMethod= ruleAddsMethod EOF ;
    public final EObject entryRuleAddsMethod() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAddsMethod = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2547:2: (iv_ruleAddsMethod= ruleAddsMethod EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2548:2: iv_ruleAddsMethod= ruleAddsMethod EOF
            {
             currentNode = createCompositeNode(grammarAccess.getAddsMethodRule(), currentNode); 
            pushFollow(FOLLOW_ruleAddsMethod_in_entryRuleAddsMethod4229);
            iv_ruleAddsMethod=ruleAddsMethod();
            _fsp--;

             current =iv_ruleAddsMethod; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleAddsMethod4239); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleAddsMethod


    // $ANTLR start ruleAddsMethod
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2555:1: ruleAddsMethod returns [EObject current=null] : ( (lv_method_0_0= ruleMethod ) ) ;
    public final EObject ruleAddsMethod() throws RecognitionException {
        EObject current = null;

        EObject lv_method_0_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2560:6: ( ( (lv_method_0_0= ruleMethod ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2561:1: ( (lv_method_0_0= ruleMethod ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2561:1: ( (lv_method_0_0= ruleMethod ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2562:1: (lv_method_0_0= ruleMethod )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2562:1: (lv_method_0_0= ruleMethod )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2563:3: lv_method_0_0= ruleMethod
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getAddsMethodAccess().getMethodMethodParserRuleCall_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleMethod_in_ruleAddsMethod4284);
            lv_method_0_0=ruleMethod();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getAddsMethodRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"method",
            	        		lv_method_0_0, 
            	        		"Method", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleAddsMethod


    // $ANTLR start entryRuleModifiesMethod
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2593:1: entryRuleModifiesMethod returns [EObject current=null] : iv_ruleModifiesMethod= ruleModifiesMethod EOF ;
    public final EObject entryRuleModifiesMethod() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleModifiesMethod = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2594:2: (iv_ruleModifiesMethod= ruleModifiesMethod EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2595:2: iv_ruleModifiesMethod= ruleModifiesMethod EOF
            {
             currentNode = createCompositeNode(grammarAccess.getModifiesMethodRule(), currentNode); 
            pushFollow(FOLLOW_ruleModifiesMethod_in_entryRuleModifiesMethod4319);
            iv_ruleModifiesMethod=ruleModifiesMethod();
            _fsp--;

             current =iv_ruleModifiesMethod; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleModifiesMethod4329); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleModifiesMethod


    // $ANTLR start ruleModifiesMethod
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2602:1: ruleModifiesMethod returns [EObject current=null] : ( () ( (lv_returntype_1_0= ruleType ) ) ( ( RULE_ID ) ) '(' ( ( (lv_params_4_0= ruleParameter ) ) ( ',' ( (lv_params_6_0= ruleParameter ) ) )* )? ')' '{' ( (lv_body_9_0= ruleMethodBody ) ) '}' ) ;
    public final EObject ruleModifiesMethod() throws RecognitionException {
        EObject current = null;

        EObject lv_returntype_1_0 = null;

        EObject lv_params_4_0 = null;

        EObject lv_params_6_0 = null;

        EObject lv_body_9_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2607:6: ( ( () ( (lv_returntype_1_0= ruleType ) ) ( ( RULE_ID ) ) '(' ( ( (lv_params_4_0= ruleParameter ) ) ( ',' ( (lv_params_6_0= ruleParameter ) ) )* )? ')' '{' ( (lv_body_9_0= ruleMethodBody ) ) '}' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2608:1: ( () ( (lv_returntype_1_0= ruleType ) ) ( ( RULE_ID ) ) '(' ( ( (lv_params_4_0= ruleParameter ) ) ( ',' ( (lv_params_6_0= ruleParameter ) ) )* )? ')' '{' ( (lv_body_9_0= ruleMethodBody ) ) '}' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2608:1: ( () ( (lv_returntype_1_0= ruleType ) ) ( ( RULE_ID ) ) '(' ( ( (lv_params_4_0= ruleParameter ) ) ( ',' ( (lv_params_6_0= ruleParameter ) ) )* )? ')' '{' ( (lv_body_9_0= ruleMethodBody ) ) '}' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2608:2: () ( (lv_returntype_1_0= ruleType ) ) ( ( RULE_ID ) ) '(' ( ( (lv_params_4_0= ruleParameter ) ) ( ',' ( (lv_params_6_0= ruleParameter ) ) )* )? ')' '{' ( (lv_body_9_0= ruleMethodBody ) ) '}'
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2608:2: ()
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2609:5: 
            {
             
                    temp=factory.create(grammarAccess.getModifiesMethodAccess().getModifiesMethodAction_0().getType().getClassifier());
                    current = temp; 
                    temp = null;
                    CompositeNode newNode = createCompositeNode(grammarAccess.getModifiesMethodAccess().getModifiesMethodAction_0(), currentNode.getParent());
                newNode.getChildren().add(currentNode);
                moveLookaheadInfo(currentNode, newNode);
                currentNode = newNode; 
                    associateNodeWithAstElement(currentNode, current); 
                

            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2619:2: ( (lv_returntype_1_0= ruleType ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2620:1: (lv_returntype_1_0= ruleType )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2620:1: (lv_returntype_1_0= ruleType )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2621:3: lv_returntype_1_0= ruleType
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getModifiesMethodAccess().getReturntypeTypeParserRuleCall_1_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleType_in_ruleModifiesMethod4384);
            lv_returntype_1_0=ruleType();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getModifiesMethodRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"returntype",
            	        		lv_returntype_1_0, 
            	        		"Type", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2643:2: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2644:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2644:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2645:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getModifiesMethodRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleModifiesMethod4402); 

            		createLeafNode(grammarAccess.getModifiesMethodAccess().getMethodRefMethodRefCrossReference_2_0(), "methodRef"); 
            	

            }


            }

            match(input,22,FOLLOW_22_in_ruleModifiesMethod4412); 

                    createLeafNode(grammarAccess.getModifiesMethodAccess().getLeftParenthesisKeyword_3(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2661:1: ( ( (lv_params_4_0= ruleParameter ) ) ( ',' ( (lv_params_6_0= ruleParameter ) ) )* )?
            int alt39=2;
            int LA39_0 = input.LA(1);

            if ( (LA39_0==RULE_ID||(LA39_0>=41 && LA39_0<=43)) ) {
                alt39=1;
            }
            switch (alt39) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2661:2: ( (lv_params_4_0= ruleParameter ) ) ( ',' ( (lv_params_6_0= ruleParameter ) ) )*
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2661:2: ( (lv_params_4_0= ruleParameter ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2662:1: (lv_params_4_0= ruleParameter )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2662:1: (lv_params_4_0= ruleParameter )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2663:3: lv_params_4_0= ruleParameter
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getModifiesMethodAccess().getParamsParameterParserRuleCall_4_0_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleParameter_in_ruleModifiesMethod4434);
                    lv_params_4_0=ruleParameter();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getModifiesMethodRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		add(
                    	       			current, 
                    	       			"params",
                    	        		lv_params_4_0, 
                    	        		"Parameter", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2685:2: ( ',' ( (lv_params_6_0= ruleParameter ) ) )*
                    loop38:
                    do {
                        int alt38=2;
                        int LA38_0 = input.LA(1);

                        if ( (LA38_0==14) ) {
                            alt38=1;
                        }


                        switch (alt38) {
                    	case 1 :
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2685:4: ',' ( (lv_params_6_0= ruleParameter ) )
                    	    {
                    	    match(input,14,FOLLOW_14_in_ruleModifiesMethod4445); 

                    	            createLeafNode(grammarAccess.getModifiesMethodAccess().getCommaKeyword_4_1_0(), null); 
                    	        
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2689:1: ( (lv_params_6_0= ruleParameter ) )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2690:1: (lv_params_6_0= ruleParameter )
                    	    {
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2690:1: (lv_params_6_0= ruleParameter )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2691:3: lv_params_6_0= ruleParameter
                    	    {
                    	     
                    	    	        currentNode=createCompositeNode(grammarAccess.getModifiesMethodAccess().getParamsParameterParserRuleCall_4_1_1_0(), currentNode); 
                    	    	    
                    	    pushFollow(FOLLOW_ruleParameter_in_ruleModifiesMethod4466);
                    	    lv_params_6_0=ruleParameter();
                    	    _fsp--;


                    	    	        if (current==null) {
                    	    	            current = factory.create(grammarAccess.getModifiesMethodRule().getType().getClassifier());
                    	    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	    	        }
                    	    	        try {
                    	    	       		add(
                    	    	       			current, 
                    	    	       			"params",
                    	    	        		lv_params_6_0, 
                    	    	        		"Parameter", 
                    	    	        		currentNode);
                    	    	        } catch (ValueConverterException vce) {
                    	    				handleValueConverterException(vce);
                    	    	        }
                    	    	        currentNode = currentNode.getParent();
                    	    	    

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop38;
                        }
                    } while (true);


                    }
                    break;

            }

            match(input,23,FOLLOW_23_in_ruleModifiesMethod4480); 

                    createLeafNode(grammarAccess.getModifiesMethodAccess().getRightParenthesisKeyword_5(), null); 
                
            match(input,18,FOLLOW_18_in_ruleModifiesMethod4490); 

                    createLeafNode(grammarAccess.getModifiesMethodAccess().getLeftCurlyBracketKeyword_6(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2721:1: ( (lv_body_9_0= ruleMethodBody ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2722:1: (lv_body_9_0= ruleMethodBody )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2722:1: (lv_body_9_0= ruleMethodBody )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2723:3: lv_body_9_0= ruleMethodBody
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getModifiesMethodAccess().getBodyMethodBodyParserRuleCall_7_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleMethodBody_in_ruleModifiesMethod4511);
            lv_body_9_0=ruleMethodBody();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getModifiesMethodRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"body",
            	        		lv_body_9_0, 
            	        		"MethodBody", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            match(input,19,FOLLOW_19_in_ruleModifiesMethod4521); 

                    createLeafNode(grammarAccess.getModifiesMethodAccess().getRightCurlyBracketKeyword_8(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleModifiesMethod


    // $ANTLR start entryRuleRemovesMethod
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2757:1: entryRuleRemovesMethod returns [EObject current=null] : iv_ruleRemovesMethod= ruleRemovesMethod EOF ;
    public final EObject entryRuleRemovesMethod() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleRemovesMethod = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2758:2: (iv_ruleRemovesMethod= ruleRemovesMethod EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2759:2: iv_ruleRemovesMethod= ruleRemovesMethod EOF
            {
             currentNode = createCompositeNode(grammarAccess.getRemovesMethodRule(), currentNode); 
            pushFollow(FOLLOW_ruleRemovesMethod_in_entryRuleRemovesMethod4557);
            iv_ruleRemovesMethod=ruleRemovesMethod();
            _fsp--;

             current =iv_ruleRemovesMethod; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleRemovesMethod4567); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleRemovesMethod


    // $ANTLR start ruleRemovesMethod
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2766:1: ruleRemovesMethod returns [EObject current=null] : ( ( ( RULE_ID ) ) '(' ')' ';' ) ;
    public final EObject ruleRemovesMethod() throws RecognitionException {
        EObject current = null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2771:6: ( ( ( ( RULE_ID ) ) '(' ')' ';' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2772:1: ( ( ( RULE_ID ) ) '(' ')' ';' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2772:1: ( ( ( RULE_ID ) ) '(' ')' ';' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2772:2: ( ( RULE_ID ) ) '(' ')' ';'
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2772:2: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2773:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2773:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2774:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getRemovesMethodRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleRemovesMethod4610); 

            		createLeafNode(grammarAccess.getRemovesMethodAccess().getMethodRefMethodRefCrossReference_0_0(), "methodRef"); 
            	

            }


            }

            match(input,22,FOLLOW_22_in_ruleRemovesMethod4620); 

                    createLeafNode(grammarAccess.getRemovesMethodAccess().getLeftParenthesisKeyword_1(), null); 
                
            match(input,23,FOLLOW_23_in_ruleRemovesMethod4630); 

                    createLeafNode(grammarAccess.getRemovesMethodAccess().getRightParenthesisKeyword_2(), null); 
                
            match(input,25,FOLLOW_25_in_ruleRemovesMethod4640); 

                    createLeafNode(grammarAccess.getRemovesMethodAccess().getSemicolonKeyword_3(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleRemovesMethod


    // $ANTLR start entryRuleFieldm
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2806:1: entryRuleFieldm returns [EObject current=null] : iv_ruleFieldm= ruleFieldm EOF ;
    public final EObject entryRuleFieldm() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleFieldm = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2807:2: (iv_ruleFieldm= ruleFieldm EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2808:2: iv_ruleFieldm= ruleFieldm EOF
            {
             currentNode = createCompositeNode(grammarAccess.getFieldmRule(), currentNode); 
            pushFollow(FOLLOW_ruleFieldm_in_entryRuleFieldm4676);
            iv_ruleFieldm=ruleFieldm();
            _fsp--;

             current =iv_ruleFieldm; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleFieldm4686); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleFieldm


    // $ANTLR start ruleFieldm
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2815:1: ruleFieldm returns [EObject current=null] : ( () ( 'remove' ( (lv_removeList_2_0= ruleRemovesField ) ) )* ( 'adds' ( (lv_addsList_4_0= ruleAddsField ) ) )* ) ;
    public final EObject ruleFieldm() throws RecognitionException {
        EObject current = null;

        EObject lv_removeList_2_0 = null;

        EObject lv_addsList_4_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2820:6: ( ( () ( 'remove' ( (lv_removeList_2_0= ruleRemovesField ) ) )* ( 'adds' ( (lv_addsList_4_0= ruleAddsField ) ) )* ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2821:1: ( () ( 'remove' ( (lv_removeList_2_0= ruleRemovesField ) ) )* ( 'adds' ( (lv_addsList_4_0= ruleAddsField ) ) )* )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2821:1: ( () ( 'remove' ( (lv_removeList_2_0= ruleRemovesField ) ) )* ( 'adds' ( (lv_addsList_4_0= ruleAddsField ) ) )* )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2821:2: () ( 'remove' ( (lv_removeList_2_0= ruleRemovesField ) ) )* ( 'adds' ( (lv_addsList_4_0= ruleAddsField ) ) )*
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2821:2: ()
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2822:5: 
            {
             
                    temp=factory.create(grammarAccess.getFieldmAccess().getFieldmAction_0().getType().getClassifier());
                    current = temp; 
                    temp = null;
                    CompositeNode newNode = createCompositeNode(grammarAccess.getFieldmAccess().getFieldmAction_0(), currentNode.getParent());
                newNode.getChildren().add(currentNode);
                moveLookaheadInfo(currentNode, newNode);
                currentNode = newNode; 
                    associateNodeWithAstElement(currentNode, current); 
                

            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2832:2: ( 'remove' ( (lv_removeList_2_0= ruleRemovesField ) ) )*
            loop40:
            do {
                int alt40=2;
                int LA40_0 = input.LA(1);

                if ( (LA40_0==39) ) {
                    int LA40_2 = input.LA(2);

                    if ( (LA40_2==RULE_ID) ) {
                        int LA40_3 = input.LA(3);

                        if ( (LA40_3==25) ) {
                            alt40=1;
                        }


                    }


                }


                switch (alt40) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2832:4: 'remove' ( (lv_removeList_2_0= ruleRemovesField ) )
            	    {
            	    match(input,39,FOLLOW_39_in_ruleFieldm4731); 

            	            createLeafNode(grammarAccess.getFieldmAccess().getRemoveKeyword_1_0(), null); 
            	        
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2836:1: ( (lv_removeList_2_0= ruleRemovesField ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2837:1: (lv_removeList_2_0= ruleRemovesField )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2837:1: (lv_removeList_2_0= ruleRemovesField )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2838:3: lv_removeList_2_0= ruleRemovesField
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getFieldmAccess().getRemoveListRemovesFieldParserRuleCall_1_1_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleRemovesField_in_ruleFieldm4752);
            	    lv_removeList_2_0=ruleRemovesField();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getFieldmRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"removeList",
            	    	        		lv_removeList_2_0, 
            	    	        		"RemovesField", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop40;
                }
            } while (true);

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2860:4: ( 'adds' ( (lv_addsList_4_0= ruleAddsField ) ) )*
            loop41:
            do {
                int alt41=2;
                int LA41_0 = input.LA(1);

                if ( (LA41_0==38) ) {
                    switch ( input.LA(2) ) {
                    case 41:
                        {
                        int LA41_3 = input.LA(3);

                        if ( (LA41_3==RULE_ID) ) {
                            int LA41_7 = input.LA(4);

                            if ( (LA41_7==25) ) {
                                alt41=1;
                            }


                        }


                        }
                        break;
                    case 42:
                        {
                        int LA41_4 = input.LA(3);

                        if ( (LA41_4==RULE_ID) ) {
                            int LA41_7 = input.LA(4);

                            if ( (LA41_7==25) ) {
                                alt41=1;
                            }


                        }


                        }
                        break;
                    case 43:
                        {
                        int LA41_5 = input.LA(3);

                        if ( (LA41_5==RULE_ID) ) {
                            int LA41_7 = input.LA(4);

                            if ( (LA41_7==25) ) {
                                alt41=1;
                            }


                        }


                        }
                        break;
                    case RULE_ID:
                        {
                        int LA41_6 = input.LA(3);

                        if ( (LA41_6==RULE_ID) ) {
                            int LA41_7 = input.LA(4);

                            if ( (LA41_7==25) ) {
                                alt41=1;
                            }


                        }


                        }
                        break;

                    }

                }


                switch (alt41) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2860:6: 'adds' ( (lv_addsList_4_0= ruleAddsField ) )
            	    {
            	    match(input,38,FOLLOW_38_in_ruleFieldm4765); 

            	            createLeafNode(grammarAccess.getFieldmAccess().getAddsKeyword_2_0(), null); 
            	        
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2864:1: ( (lv_addsList_4_0= ruleAddsField ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2865:1: (lv_addsList_4_0= ruleAddsField )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2865:1: (lv_addsList_4_0= ruleAddsField )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2866:3: lv_addsList_4_0= ruleAddsField
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getFieldmAccess().getAddsListAddsFieldParserRuleCall_2_1_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleAddsField_in_ruleFieldm4786);
            	    lv_addsList_4_0=ruleAddsField();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getFieldmRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		add(
            	    	       			current, 
            	    	       			"addsList",
            	    	        		lv_addsList_4_0, 
            	    	        		"AddsField", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop41;
                }
            } while (true);


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleFieldm


    // $ANTLR start entryRuleAddsField
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2896:1: entryRuleAddsField returns [EObject current=null] : iv_ruleAddsField= ruleAddsField EOF ;
    public final EObject entryRuleAddsField() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAddsField = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2897:2: (iv_ruleAddsField= ruleAddsField EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2898:2: iv_ruleAddsField= ruleAddsField EOF
            {
             currentNode = createCompositeNode(grammarAccess.getAddsFieldRule(), currentNode); 
            pushFollow(FOLLOW_ruleAddsField_in_entryRuleAddsField4824);
            iv_ruleAddsField=ruleAddsField();
            _fsp--;

             current =iv_ruleAddsField; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleAddsField4834); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleAddsField


    // $ANTLR start ruleAddsField
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2905:1: ruleAddsField returns [EObject current=null] : ( (lv_field_0_0= ruleField ) ) ;
    public final EObject ruleAddsField() throws RecognitionException {
        EObject current = null;

        EObject lv_field_0_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2910:6: ( ( (lv_field_0_0= ruleField ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2911:1: ( (lv_field_0_0= ruleField ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2911:1: ( (lv_field_0_0= ruleField ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2912:1: (lv_field_0_0= ruleField )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2912:1: (lv_field_0_0= ruleField )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2913:3: lv_field_0_0= ruleField
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getAddsFieldAccess().getFieldFieldParserRuleCall_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleField_in_ruleAddsField4879);
            lv_field_0_0=ruleField();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getAddsFieldRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"field",
            	        		lv_field_0_0, 
            	        		"Field", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleAddsField


    // $ANTLR start entryRuleRemovesField
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2945:1: entryRuleRemovesField returns [EObject current=null] : iv_ruleRemovesField= ruleRemovesField EOF ;
    public final EObject entryRuleRemovesField() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleRemovesField = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2946:2: (iv_ruleRemovesField= ruleRemovesField EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2947:2: iv_ruleRemovesField= ruleRemovesField EOF
            {
             currentNode = createCompositeNode(grammarAccess.getRemovesFieldRule(), currentNode); 
            pushFollow(FOLLOW_ruleRemovesField_in_entryRuleRemovesField4916);
            iv_ruleRemovesField=ruleRemovesField();
            _fsp--;

             current =iv_ruleRemovesField; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleRemovesField4926); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleRemovesField


    // $ANTLR start ruleRemovesField
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2954:1: ruleRemovesField returns [EObject current=null] : ( ( ( RULE_ID ) ) ';' ) ;
    public final EObject ruleRemovesField() throws RecognitionException {
        EObject current = null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2959:6: ( ( ( ( RULE_ID ) ) ';' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2960:1: ( ( ( RULE_ID ) ) ';' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2960:1: ( ( ( RULE_ID ) ) ';' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2960:2: ( ( RULE_ID ) ) ';'
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2960:2: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2961:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2961:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2962:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getRemovesFieldRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleRemovesField4969); 

            		createLeafNode(grammarAccess.getRemovesFieldAccess().getFieldRefFieldRefCrossReference_0_0(), "fieldRef"); 
            	

            }


            }

            match(input,25,FOLLOW_25_in_ruleRemovesField4979); 

                    createLeafNode(grammarAccess.getRemovesFieldAccess().getSemicolonKeyword_1(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleRemovesField


    // $ANTLR start entryRuleType
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2986:1: entryRuleType returns [EObject current=null] : iv_ruleType= ruleType EOF ;
    public final EObject entryRuleType() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleType = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2987:2: (iv_ruleType= ruleType EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2988:2: iv_ruleType= ruleType EOF
            {
             currentNode = createCompositeNode(grammarAccess.getTypeRule(), currentNode); 
            pushFollow(FOLLOW_ruleType_in_entryRuleType5015);
            iv_ruleType=ruleType();
            _fsp--;

             current =iv_ruleType; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleType5025); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleType


    // $ANTLR start ruleType
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:2995:1: ruleType returns [EObject current=null] : ( ( ( (lv_basic_0_1= 'void' | lv_basic_0_2= 'int' | lv_basic_0_3= 'boolean' ) ) ) | ( ( RULE_ID ) ) ) ;
    public final EObject ruleType() throws RecognitionException {
        EObject current = null;

        Token lv_basic_0_1=null;
        Token lv_basic_0_2=null;
        Token lv_basic_0_3=null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3000:6: ( ( ( ( (lv_basic_0_1= 'void' | lv_basic_0_2= 'int' | lv_basic_0_3= 'boolean' ) ) ) | ( ( RULE_ID ) ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3001:1: ( ( ( (lv_basic_0_1= 'void' | lv_basic_0_2= 'int' | lv_basic_0_3= 'boolean' ) ) ) | ( ( RULE_ID ) ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3001:1: ( ( ( (lv_basic_0_1= 'void' | lv_basic_0_2= 'int' | lv_basic_0_3= 'boolean' ) ) ) | ( ( RULE_ID ) ) )
            int alt43=2;
            int LA43_0 = input.LA(1);

            if ( ((LA43_0>=41 && LA43_0<=43)) ) {
                alt43=1;
            }
            else if ( (LA43_0==RULE_ID) ) {
                alt43=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("3001:1: ( ( ( (lv_basic_0_1= 'void' | lv_basic_0_2= 'int' | lv_basic_0_3= 'boolean' ) ) ) | ( ( RULE_ID ) ) )", 43, 0, input);

                throw nvae;
            }
            switch (alt43) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3001:2: ( ( (lv_basic_0_1= 'void' | lv_basic_0_2= 'int' | lv_basic_0_3= 'boolean' ) ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3001:2: ( ( (lv_basic_0_1= 'void' | lv_basic_0_2= 'int' | lv_basic_0_3= 'boolean' ) ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3002:1: ( (lv_basic_0_1= 'void' | lv_basic_0_2= 'int' | lv_basic_0_3= 'boolean' ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3002:1: ( (lv_basic_0_1= 'void' | lv_basic_0_2= 'int' | lv_basic_0_3= 'boolean' ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3003:1: (lv_basic_0_1= 'void' | lv_basic_0_2= 'int' | lv_basic_0_3= 'boolean' )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3003:1: (lv_basic_0_1= 'void' | lv_basic_0_2= 'int' | lv_basic_0_3= 'boolean' )
                    int alt42=3;
                    switch ( input.LA(1) ) {
                    case 41:
                        {
                        alt42=1;
                        }
                        break;
                    case 42:
                        {
                        alt42=2;
                        }
                        break;
                    case 43:
                        {
                        alt42=3;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("3003:1: (lv_basic_0_1= 'void' | lv_basic_0_2= 'int' | lv_basic_0_3= 'boolean' )", 42, 0, input);

                        throw nvae;
                    }

                    switch (alt42) {
                        case 1 :
                            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3004:3: lv_basic_0_1= 'void'
                            {
                            lv_basic_0_1=(Token)input.LT(1);
                            match(input,41,FOLLOW_41_in_ruleType5070); 

                                    createLeafNode(grammarAccess.getTypeAccess().getBasicVoidKeyword_0_0_0(), "basic"); 
                                

                            	        if (current==null) {
                            	            current = factory.create(grammarAccess.getTypeRule().getType().getClassifier());
                            	            associateNodeWithAstElement(currentNode, current);
                            	        }
                            	        
                            	        try {
                            	       		set(current, "basic", lv_basic_0_1, null, lastConsumedNode);
                            	        } catch (ValueConverterException vce) {
                            				handleValueConverterException(vce);
                            	        }
                            	    

                            }
                            break;
                        case 2 :
                            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3022:8: lv_basic_0_2= 'int'
                            {
                            lv_basic_0_2=(Token)input.LT(1);
                            match(input,42,FOLLOW_42_in_ruleType5099); 

                                    createLeafNode(grammarAccess.getTypeAccess().getBasicIntKeyword_0_0_1(), "basic"); 
                                

                            	        if (current==null) {
                            	            current = factory.create(grammarAccess.getTypeRule().getType().getClassifier());
                            	            associateNodeWithAstElement(currentNode, current);
                            	        }
                            	        
                            	        try {
                            	       		set(current, "basic", lv_basic_0_2, null, lastConsumedNode);
                            	        } catch (ValueConverterException vce) {
                            				handleValueConverterException(vce);
                            	        }
                            	    

                            }
                            break;
                        case 3 :
                            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3040:8: lv_basic_0_3= 'boolean'
                            {
                            lv_basic_0_3=(Token)input.LT(1);
                            match(input,43,FOLLOW_43_in_ruleType5128); 

                                    createLeafNode(grammarAccess.getTypeAccess().getBasicBooleanKeyword_0_0_2(), "basic"); 
                                

                            	        if (current==null) {
                            	            current = factory.create(grammarAccess.getTypeRule().getType().getClassifier());
                            	            associateNodeWithAstElement(currentNode, current);
                            	        }
                            	        
                            	        try {
                            	       		set(current, "basic", lv_basic_0_3, null, lastConsumedNode);
                            	        } catch (ValueConverterException vce) {
                            				handleValueConverterException(vce);
                            	        }
                            	    

                            }
                            break;

                    }


                    }


                    }


                    }
                    break;
                case 2 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3062:6: ( ( RULE_ID ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3062:6: ( ( RULE_ID ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3063:1: ( RULE_ID )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3063:1: ( RULE_ID )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3064:3: RULE_ID
                    {

                    			if (current==null) {
                    	            current = factory.create(grammarAccess.getTypeRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                            
                    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleType5168); 

                    		createLeafNode(grammarAccess.getTypeAccess().getClassrefClassCrossReference_1_0(), "classref"); 
                    	

                    }


                    }


                    }
                    break;

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleType


    // $ANTLR start entryRuleExpression
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3084:1: entryRuleExpression returns [EObject current=null] : iv_ruleExpression= ruleExpression EOF ;
    public final EObject entryRuleExpression() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleExpression = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3085:2: (iv_ruleExpression= ruleExpression EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3086:2: iv_ruleExpression= ruleExpression EOF
            {
             currentNode = createCompositeNode(grammarAccess.getExpressionRule(), currentNode); 
            pushFollow(FOLLOW_ruleExpression_in_entryRuleExpression5204);
            iv_ruleExpression=ruleExpression();
            _fsp--;

             current =iv_ruleExpression; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleExpression5214); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleExpression


    // $ANTLR start ruleExpression
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3093:1: ruleExpression returns [EObject current=null] : ( ( (lv_terminalExpression_0_0= ruleTerminalExpression ) ) ( () '.' ( (lv_message_3_0= ruleMessage ) ) )* ( '=' ( (lv_value_5_0= ruleExpression ) ) )? ) ;
    public final EObject ruleExpression() throws RecognitionException {
        EObject current = null;

        EObject lv_terminalExpression_0_0 = null;

        EObject lv_message_3_0 = null;

        EObject lv_value_5_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3098:6: ( ( ( (lv_terminalExpression_0_0= ruleTerminalExpression ) ) ( () '.' ( (lv_message_3_0= ruleMessage ) ) )* ( '=' ( (lv_value_5_0= ruleExpression ) ) )? ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3099:1: ( ( (lv_terminalExpression_0_0= ruleTerminalExpression ) ) ( () '.' ( (lv_message_3_0= ruleMessage ) ) )* ( '=' ( (lv_value_5_0= ruleExpression ) ) )? )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3099:1: ( ( (lv_terminalExpression_0_0= ruleTerminalExpression ) ) ( () '.' ( (lv_message_3_0= ruleMessage ) ) )* ( '=' ( (lv_value_5_0= ruleExpression ) ) )? )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3099:2: ( (lv_terminalExpression_0_0= ruleTerminalExpression ) ) ( () '.' ( (lv_message_3_0= ruleMessage ) ) )* ( '=' ( (lv_value_5_0= ruleExpression ) ) )?
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3099:2: ( (lv_terminalExpression_0_0= ruleTerminalExpression ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3100:1: (lv_terminalExpression_0_0= ruleTerminalExpression )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3100:1: (lv_terminalExpression_0_0= ruleTerminalExpression )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3101:3: lv_terminalExpression_0_0= ruleTerminalExpression
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getExpressionAccess().getTerminalExpressionTerminalExpressionParserRuleCall_0_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleTerminalExpression_in_ruleExpression5260);
            lv_terminalExpression_0_0=ruleTerminalExpression();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getExpressionRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"terminalExpression",
            	        		lv_terminalExpression_0_0, 
            	        		"TerminalExpression", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3123:2: ( () '.' ( (lv_message_3_0= ruleMessage ) ) )*
            loop44:
            do {
                int alt44=2;
                int LA44_0 = input.LA(1);

                if ( (LA44_0==27) ) {
                    alt44=1;
                }


                switch (alt44) {
            	case 1 :
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3123:3: () '.' ( (lv_message_3_0= ruleMessage ) )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3123:3: ()
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3124:5: 
            	    {
            	     
            	            temp=factory.create(grammarAccess.getExpressionAccess().getExpressionReceiverAction_1_0().getType().getClassifier());
            	            try {
            	            	factory.set(temp, "receiver", current, null /*ParserRule*/, currentNode);
            	            } catch(ValueConverterException vce) {
            	            	handleValueConverterException(vce);
            	            }
            	            current = temp; 
            	            temp = null;
            	            CompositeNode newNode = createCompositeNode(grammarAccess.getExpressionAccess().getExpressionReceiverAction_1_0(), currentNode.getParent());
            	        newNode.getChildren().add(currentNode);
            	        moveLookaheadInfo(currentNode, newNode);
            	        currentNode = newNode; 
            	            associateNodeWithAstElement(currentNode, current); 
            	        

            	    }

            	    match(input,27,FOLLOW_27_in_ruleExpression5280); 

            	            createLeafNode(grammarAccess.getExpressionAccess().getFullStopKeyword_1_1(), null); 
            	        
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3143:1: ( (lv_message_3_0= ruleMessage ) )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3144:1: (lv_message_3_0= ruleMessage )
            	    {
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3144:1: (lv_message_3_0= ruleMessage )
            	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3145:3: lv_message_3_0= ruleMessage
            	    {
            	     
            	    	        currentNode=createCompositeNode(grammarAccess.getExpressionAccess().getMessageMessageParserRuleCall_1_2_0(), currentNode); 
            	    	    
            	    pushFollow(FOLLOW_ruleMessage_in_ruleExpression5301);
            	    lv_message_3_0=ruleMessage();
            	    _fsp--;


            	    	        if (current==null) {
            	    	            current = factory.create(grammarAccess.getExpressionRule().getType().getClassifier());
            	    	            associateNodeWithAstElement(currentNode.getParent(), current);
            	    	        }
            	    	        try {
            	    	       		set(
            	    	       			current, 
            	    	       			"message",
            	    	        		lv_message_3_0, 
            	    	        		"Message", 
            	    	        		currentNode);
            	    	        } catch (ValueConverterException vce) {
            	    				handleValueConverterException(vce);
            	    	        }
            	    	        currentNode = currentNode.getParent();
            	    	    

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop44;
                }
            } while (true);

            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3167:4: ( '=' ( (lv_value_5_0= ruleExpression ) ) )?
            int alt45=2;
            int LA45_0 = input.LA(1);

            if ( (LA45_0==28) ) {
                alt45=1;
            }
            switch (alt45) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3167:6: '=' ( (lv_value_5_0= ruleExpression ) )
                    {
                    match(input,28,FOLLOW_28_in_ruleExpression5314); 

                            createLeafNode(grammarAccess.getExpressionAccess().getEqualsSignKeyword_2_0(), null); 
                        
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3171:1: ( (lv_value_5_0= ruleExpression ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3172:1: (lv_value_5_0= ruleExpression )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3172:1: (lv_value_5_0= ruleExpression )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3173:3: lv_value_5_0= ruleExpression
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getExpressionAccess().getValueExpressionParserRuleCall_2_1_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleExpression_in_ruleExpression5335);
                    lv_value_5_0=ruleExpression();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getExpressionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"value",
                    	        		lv_value_5_0, 
                    	        		"Expression", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }
                    break;

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleExpression


    // $ANTLR start entryRuleMessage
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3203:1: entryRuleMessage returns [EObject current=null] : iv_ruleMessage= ruleMessage EOF ;
    public final EObject entryRuleMessage() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMessage = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3204:2: (iv_ruleMessage= ruleMessage EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3205:2: iv_ruleMessage= ruleMessage EOF
            {
             currentNode = createCompositeNode(grammarAccess.getMessageRule(), currentNode); 
            pushFollow(FOLLOW_ruleMessage_in_entryRuleMessage5373);
            iv_ruleMessage=ruleMessage();
            _fsp--;

             current =iv_ruleMessage; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleMessage5383); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleMessage


    // $ANTLR start ruleMessage
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3212:1: ruleMessage returns [EObject current=null] : ( ( (lv_methodCall_0_0= ruleMethodCall ) ) | ( (lv_fieldAccess_1_0= ruleFieldAccess ) ) ) ;
    public final EObject ruleMessage() throws RecognitionException {
        EObject current = null;

        EObject lv_methodCall_0_0 = null;

        EObject lv_fieldAccess_1_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3217:6: ( ( ( (lv_methodCall_0_0= ruleMethodCall ) ) | ( (lv_fieldAccess_1_0= ruleFieldAccess ) ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3218:1: ( ( (lv_methodCall_0_0= ruleMethodCall ) ) | ( (lv_fieldAccess_1_0= ruleFieldAccess ) ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3218:1: ( ( (lv_methodCall_0_0= ruleMethodCall ) ) | ( (lv_fieldAccess_1_0= ruleFieldAccess ) ) )
            int alt46=2;
            int LA46_0 = input.LA(1);

            if ( (LA46_0==RULE_ID) ) {
                int LA46_1 = input.LA(2);

                if ( (LA46_1==22) ) {
                    alt46=1;
                }
                else if ( (LA46_1==EOF||LA46_1==14||LA46_1==23||LA46_1==25||(LA46_1>=27 && LA46_1<=28)) ) {
                    alt46=2;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("3218:1: ( ( (lv_methodCall_0_0= ruleMethodCall ) ) | ( (lv_fieldAccess_1_0= ruleFieldAccess ) ) )", 46, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("3218:1: ( ( (lv_methodCall_0_0= ruleMethodCall ) ) | ( (lv_fieldAccess_1_0= ruleFieldAccess ) ) )", 46, 0, input);

                throw nvae;
            }
            switch (alt46) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3218:2: ( (lv_methodCall_0_0= ruleMethodCall ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3218:2: ( (lv_methodCall_0_0= ruleMethodCall ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3219:1: (lv_methodCall_0_0= ruleMethodCall )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3219:1: (lv_methodCall_0_0= ruleMethodCall )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3220:3: lv_methodCall_0_0= ruleMethodCall
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getMessageAccess().getMethodCallMethodCallParserRuleCall_0_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleMethodCall_in_ruleMessage5429);
                    lv_methodCall_0_0=ruleMethodCall();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getMessageRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"methodCall",
                    	        		lv_methodCall_0_0, 
                    	        		"MethodCall", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }
                    break;
                case 2 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3243:6: ( (lv_fieldAccess_1_0= ruleFieldAccess ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3243:6: ( (lv_fieldAccess_1_0= ruleFieldAccess ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3244:1: (lv_fieldAccess_1_0= ruleFieldAccess )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3244:1: (lv_fieldAccess_1_0= ruleFieldAccess )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3245:3: lv_fieldAccess_1_0= ruleFieldAccess
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getMessageAccess().getFieldAccessFieldAccessParserRuleCall_1_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleFieldAccess_in_ruleMessage5456);
                    lv_fieldAccess_1_0=ruleFieldAccess();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getMessageRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"fieldAccess",
                    	        		lv_fieldAccess_1_0, 
                    	        		"FieldAccess", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }
                    break;

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleMessage


    // $ANTLR start entryRuleMethodCall
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3275:1: entryRuleMethodCall returns [EObject current=null] : iv_ruleMethodCall= ruleMethodCall EOF ;
    public final EObject entryRuleMethodCall() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMethodCall = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3276:2: (iv_ruleMethodCall= ruleMethodCall EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3277:2: iv_ruleMethodCall= ruleMethodCall EOF
            {
             currentNode = createCompositeNode(grammarAccess.getMethodCallRule(), currentNode); 
            pushFollow(FOLLOW_ruleMethodCall_in_entryRuleMethodCall5492);
            iv_ruleMethodCall=ruleMethodCall();
            _fsp--;

             current =iv_ruleMethodCall; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleMethodCall5502); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleMethodCall


    // $ANTLR start ruleMethodCall
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3284:1: ruleMethodCall returns [EObject current=null] : ( ( ( RULE_ID ) ) '(' ( ( (lv_args_2_0= ruleArgument ) ) ( ',' ( (lv_args_4_0= ruleArgument ) ) )* )? ')' ) ;
    public final EObject ruleMethodCall() throws RecognitionException {
        EObject current = null;

        EObject lv_args_2_0 = null;

        EObject lv_args_4_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3289:6: ( ( ( ( RULE_ID ) ) '(' ( ( (lv_args_2_0= ruleArgument ) ) ( ',' ( (lv_args_4_0= ruleArgument ) ) )* )? ')' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3290:1: ( ( ( RULE_ID ) ) '(' ( ( (lv_args_2_0= ruleArgument ) ) ( ',' ( (lv_args_4_0= ruleArgument ) ) )* )? ')' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3290:1: ( ( ( RULE_ID ) ) '(' ( ( (lv_args_2_0= ruleArgument ) ) ( ',' ( (lv_args_4_0= ruleArgument ) ) )* )? ')' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3290:2: ( ( RULE_ID ) ) '(' ( ( (lv_args_2_0= ruleArgument ) ) ( ',' ( (lv_args_4_0= ruleArgument ) ) )* )? ')'
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3290:2: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3291:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3291:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3292:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getMethodCallRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleMethodCall5545); 

            		createLeafNode(grammarAccess.getMethodCallAccess().getNameMethodRefCrossReference_0_0(), "name"); 
            	

            }


            }

            match(input,22,FOLLOW_22_in_ruleMethodCall5555); 

                    createLeafNode(grammarAccess.getMethodCallAccess().getLeftParenthesisKeyword_1(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3308:1: ( ( (lv_args_2_0= ruleArgument ) ) ( ',' ( (lv_args_4_0= ruleArgument ) ) )* )?
            int alt48=2;
            int LA48_0 = input.LA(1);

            if ( ((LA48_0>=RULE_STRING && LA48_0<=RULE_ID)||LA48_0==RULE_INT||LA48_0==22||LA48_0==26||(LA48_0>=46 && LA48_0<=48)) ) {
                alt48=1;
            }
            switch (alt48) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3308:2: ( (lv_args_2_0= ruleArgument ) ) ( ',' ( (lv_args_4_0= ruleArgument ) ) )*
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3308:2: ( (lv_args_2_0= ruleArgument ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3309:1: (lv_args_2_0= ruleArgument )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3309:1: (lv_args_2_0= ruleArgument )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3310:3: lv_args_2_0= ruleArgument
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getMethodCallAccess().getArgsArgumentParserRuleCall_2_0_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleArgument_in_ruleMethodCall5577);
                    lv_args_2_0=ruleArgument();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getMethodCallRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		add(
                    	       			current, 
                    	       			"args",
                    	        		lv_args_2_0, 
                    	        		"Argument", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3332:2: ( ',' ( (lv_args_4_0= ruleArgument ) ) )*
                    loop47:
                    do {
                        int alt47=2;
                        int LA47_0 = input.LA(1);

                        if ( (LA47_0==14) ) {
                            alt47=1;
                        }


                        switch (alt47) {
                    	case 1 :
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3332:4: ',' ( (lv_args_4_0= ruleArgument ) )
                    	    {
                    	    match(input,14,FOLLOW_14_in_ruleMethodCall5588); 

                    	            createLeafNode(grammarAccess.getMethodCallAccess().getCommaKeyword_2_1_0(), null); 
                    	        
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3336:1: ( (lv_args_4_0= ruleArgument ) )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3337:1: (lv_args_4_0= ruleArgument )
                    	    {
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3337:1: (lv_args_4_0= ruleArgument )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3338:3: lv_args_4_0= ruleArgument
                    	    {
                    	     
                    	    	        currentNode=createCompositeNode(grammarAccess.getMethodCallAccess().getArgsArgumentParserRuleCall_2_1_1_0(), currentNode); 
                    	    	    
                    	    pushFollow(FOLLOW_ruleArgument_in_ruleMethodCall5609);
                    	    lv_args_4_0=ruleArgument();
                    	    _fsp--;


                    	    	        if (current==null) {
                    	    	            current = factory.create(grammarAccess.getMethodCallRule().getType().getClassifier());
                    	    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	    	        }
                    	    	        try {
                    	    	       		add(
                    	    	       			current, 
                    	    	       			"args",
                    	    	        		lv_args_4_0, 
                    	    	        		"Argument", 
                    	    	        		currentNode);
                    	    	        } catch (ValueConverterException vce) {
                    	    				handleValueConverterException(vce);
                    	    	        }
                    	    	        currentNode = currentNode.getParent();
                    	    	    

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop47;
                        }
                    } while (true);


                    }
                    break;

            }

            match(input,23,FOLLOW_23_in_ruleMethodCall5623); 

                    createLeafNode(grammarAccess.getMethodCallAccess().getRightParenthesisKeyword_3(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleMethodCall


    // $ANTLR start entryRuleFieldAccess
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3372:1: entryRuleFieldAccess returns [EObject current=null] : iv_ruleFieldAccess= ruleFieldAccess EOF ;
    public final EObject entryRuleFieldAccess() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleFieldAccess = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3373:2: (iv_ruleFieldAccess= ruleFieldAccess EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3374:2: iv_ruleFieldAccess= ruleFieldAccess EOF
            {
             currentNode = createCompositeNode(grammarAccess.getFieldAccessRule(), currentNode); 
            pushFollow(FOLLOW_ruleFieldAccess_in_entryRuleFieldAccess5659);
            iv_ruleFieldAccess=ruleFieldAccess();
            _fsp--;

             current =iv_ruleFieldAccess; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleFieldAccess5669); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleFieldAccess


    // $ANTLR start ruleFieldAccess
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3381:1: ruleFieldAccess returns [EObject current=null] : ( ( RULE_ID ) ) ;
    public final EObject ruleFieldAccess() throws RecognitionException {
        EObject current = null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3386:6: ( ( ( RULE_ID ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3387:1: ( ( RULE_ID ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3387:1: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3388:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3388:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3389:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getFieldAccessRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleFieldAccess5711); 

            		createLeafNode(grammarAccess.getFieldAccessAccess().getNameFieldRefCrossReference_0(), "name"); 
            	

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleFieldAccess


    // $ANTLR start entryRuleTerminalExpression
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3409:1: entryRuleTerminalExpression returns [EObject current=null] : iv_ruleTerminalExpression= ruleTerminalExpression EOF ;
    public final EObject entryRuleTerminalExpression() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleTerminalExpression = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3410:2: (iv_ruleTerminalExpression= ruleTerminalExpression EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3411:2: iv_ruleTerminalExpression= ruleTerminalExpression EOF
            {
             currentNode = createCompositeNode(grammarAccess.getTerminalExpressionRule(), currentNode); 
            pushFollow(FOLLOW_ruleTerminalExpression_in_entryRuleTerminalExpression5746);
            iv_ruleTerminalExpression=ruleTerminalExpression();
            _fsp--;

             current =iv_ruleTerminalExpression; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleTerminalExpression5756); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleTerminalExpression


    // $ANTLR start ruleTerminalExpression
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3418:1: ruleTerminalExpression returns [EObject current=null] : ( ( (lv_this_0_0= ruleThis ) ) | ( (lv_variable_1_0= ruleVariable ) ) | ( (lv_new_2_0= ruleNew ) ) | ( (lv_cast_3_0= ruleCast ) ) | ( (lv_original_4_0= ruleOriginal ) ) | ( (lv_int_5_0= ruleIntero ) ) | ( (lv_string_6_0= ruleStringa ) ) | ( (lv_null_7_0= ruleNullo ) ) ) ;
    public final EObject ruleTerminalExpression() throws RecognitionException {
        EObject current = null;

        EObject lv_this_0_0 = null;

        EObject lv_variable_1_0 = null;

        EObject lv_new_2_0 = null;

        EObject lv_cast_3_0 = null;

        EObject lv_original_4_0 = null;

        EObject lv_int_5_0 = null;

        EObject lv_string_6_0 = null;

        EObject lv_null_7_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3423:6: ( ( ( (lv_this_0_0= ruleThis ) ) | ( (lv_variable_1_0= ruleVariable ) ) | ( (lv_new_2_0= ruleNew ) ) | ( (lv_cast_3_0= ruleCast ) ) | ( (lv_original_4_0= ruleOriginal ) ) | ( (lv_int_5_0= ruleIntero ) ) | ( (lv_string_6_0= ruleStringa ) ) | ( (lv_null_7_0= ruleNullo ) ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3424:1: ( ( (lv_this_0_0= ruleThis ) ) | ( (lv_variable_1_0= ruleVariable ) ) | ( (lv_new_2_0= ruleNew ) ) | ( (lv_cast_3_0= ruleCast ) ) | ( (lv_original_4_0= ruleOriginal ) ) | ( (lv_int_5_0= ruleIntero ) ) | ( (lv_string_6_0= ruleStringa ) ) | ( (lv_null_7_0= ruleNullo ) ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3424:1: ( ( (lv_this_0_0= ruleThis ) ) | ( (lv_variable_1_0= ruleVariable ) ) | ( (lv_new_2_0= ruleNew ) ) | ( (lv_cast_3_0= ruleCast ) ) | ( (lv_original_4_0= ruleOriginal ) ) | ( (lv_int_5_0= ruleIntero ) ) | ( (lv_string_6_0= ruleStringa ) ) | ( (lv_null_7_0= ruleNullo ) ) )
            int alt49=8;
            switch ( input.LA(1) ) {
            case 26:
                {
                alt49=1;
                }
                break;
            case RULE_ID:
                {
                alt49=2;
                }
                break;
            case 46:
                {
                alt49=3;
                }
                break;
            case 22:
                {
                alt49=4;
                }
                break;
            case 47:
                {
                alt49=5;
                }
                break;
            case RULE_INT:
                {
                alt49=6;
                }
                break;
            case RULE_STRING:
                {
                alt49=7;
                }
                break;
            case 48:
                {
                alt49=8;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("3424:1: ( ( (lv_this_0_0= ruleThis ) ) | ( (lv_variable_1_0= ruleVariable ) ) | ( (lv_new_2_0= ruleNew ) ) | ( (lv_cast_3_0= ruleCast ) ) | ( (lv_original_4_0= ruleOriginal ) ) | ( (lv_int_5_0= ruleIntero ) ) | ( (lv_string_6_0= ruleStringa ) ) | ( (lv_null_7_0= ruleNullo ) ) )", 49, 0, input);

                throw nvae;
            }

            switch (alt49) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3424:2: ( (lv_this_0_0= ruleThis ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3424:2: ( (lv_this_0_0= ruleThis ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3425:1: (lv_this_0_0= ruleThis )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3425:1: (lv_this_0_0= ruleThis )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3426:3: lv_this_0_0= ruleThis
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getTerminalExpressionAccess().getThisThisParserRuleCall_0_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleThis_in_ruleTerminalExpression5802);
                    lv_this_0_0=ruleThis();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getTerminalExpressionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"this",
                    	        		lv_this_0_0, 
                    	        		"This", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }
                    break;
                case 2 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3449:6: ( (lv_variable_1_0= ruleVariable ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3449:6: ( (lv_variable_1_0= ruleVariable ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3450:1: (lv_variable_1_0= ruleVariable )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3450:1: (lv_variable_1_0= ruleVariable )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3451:3: lv_variable_1_0= ruleVariable
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getTerminalExpressionAccess().getVariableVariableParserRuleCall_1_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleVariable_in_ruleTerminalExpression5829);
                    lv_variable_1_0=ruleVariable();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getTerminalExpressionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"variable",
                    	        		lv_variable_1_0, 
                    	        		"Variable", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }
                    break;
                case 3 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3474:6: ( (lv_new_2_0= ruleNew ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3474:6: ( (lv_new_2_0= ruleNew ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3475:1: (lv_new_2_0= ruleNew )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3475:1: (lv_new_2_0= ruleNew )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3476:3: lv_new_2_0= ruleNew
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getTerminalExpressionAccess().getNewNewParserRuleCall_2_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleNew_in_ruleTerminalExpression5856);
                    lv_new_2_0=ruleNew();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getTerminalExpressionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"new",
                    	        		lv_new_2_0, 
                    	        		"New", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }
                    break;
                case 4 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3499:6: ( (lv_cast_3_0= ruleCast ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3499:6: ( (lv_cast_3_0= ruleCast ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3500:1: (lv_cast_3_0= ruleCast )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3500:1: (lv_cast_3_0= ruleCast )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3501:3: lv_cast_3_0= ruleCast
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getTerminalExpressionAccess().getCastCastParserRuleCall_3_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleCast_in_ruleTerminalExpression5883);
                    lv_cast_3_0=ruleCast();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getTerminalExpressionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"cast",
                    	        		lv_cast_3_0, 
                    	        		"Cast", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }
                    break;
                case 5 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3524:6: ( (lv_original_4_0= ruleOriginal ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3524:6: ( (lv_original_4_0= ruleOriginal ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3525:1: (lv_original_4_0= ruleOriginal )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3525:1: (lv_original_4_0= ruleOriginal )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3526:3: lv_original_4_0= ruleOriginal
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getTerminalExpressionAccess().getOriginalOriginalParserRuleCall_4_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleOriginal_in_ruleTerminalExpression5910);
                    lv_original_4_0=ruleOriginal();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getTerminalExpressionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"original",
                    	        		lv_original_4_0, 
                    	        		"Original", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }
                    break;
                case 6 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3549:6: ( (lv_int_5_0= ruleIntero ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3549:6: ( (lv_int_5_0= ruleIntero ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3550:1: (lv_int_5_0= ruleIntero )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3550:1: (lv_int_5_0= ruleIntero )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3551:3: lv_int_5_0= ruleIntero
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getTerminalExpressionAccess().getIntInteroParserRuleCall_5_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleIntero_in_ruleTerminalExpression5937);
                    lv_int_5_0=ruleIntero();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getTerminalExpressionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"int",
                    	        		lv_int_5_0, 
                    	        		"Intero", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }
                    break;
                case 7 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3574:6: ( (lv_string_6_0= ruleStringa ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3574:6: ( (lv_string_6_0= ruleStringa ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3575:1: (lv_string_6_0= ruleStringa )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3575:1: (lv_string_6_0= ruleStringa )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3576:3: lv_string_6_0= ruleStringa
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getTerminalExpressionAccess().getStringStringaParserRuleCall_6_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleStringa_in_ruleTerminalExpression5964);
                    lv_string_6_0=ruleStringa();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getTerminalExpressionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"string",
                    	        		lv_string_6_0, 
                    	        		"Stringa", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }
                    break;
                case 8 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3599:6: ( (lv_null_7_0= ruleNullo ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3599:6: ( (lv_null_7_0= ruleNullo ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3600:1: (lv_null_7_0= ruleNullo )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3600:1: (lv_null_7_0= ruleNullo )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3601:3: lv_null_7_0= ruleNullo
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getTerminalExpressionAccess().getNullNulloParserRuleCall_7_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleNullo_in_ruleTerminalExpression5991);
                    lv_null_7_0=ruleNullo();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getTerminalExpressionRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		set(
                    	       			current, 
                    	       			"null",
                    	        		lv_null_7_0, 
                    	        		"Nullo", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }


                    }
                    break;

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleTerminalExpression


    // $ANTLR start entryRuleInsertJava
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3631:1: entryRuleInsertJava returns [EObject current=null] : iv_ruleInsertJava= ruleInsertJava EOF ;
    public final EObject entryRuleInsertJava() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleInsertJava = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3632:2: (iv_ruleInsertJava= ruleInsertJava EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3633:2: iv_ruleInsertJava= ruleInsertJava EOF
            {
             currentNode = createCompositeNode(grammarAccess.getInsertJavaRule(), currentNode); 
            pushFollow(FOLLOW_ruleInsertJava_in_entryRuleInsertJava6027);
            iv_ruleInsertJava=ruleInsertJava();
            _fsp--;

             current =iv_ruleInsertJava; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleInsertJava6037); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleInsertJava


    // $ANTLR start ruleInsertJava
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3640:1: ruleInsertJava returns [EObject current=null] : ( () '<' ( (lv_String_2_0= RULE_ALL ) ) '>' ) ;
    public final EObject ruleInsertJava() throws RecognitionException {
        EObject current = null;

        Token lv_String_2_0=null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3645:6: ( ( () '<' ( (lv_String_2_0= RULE_ALL ) ) '>' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3646:1: ( () '<' ( (lv_String_2_0= RULE_ALL ) ) '>' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3646:1: ( () '<' ( (lv_String_2_0= RULE_ALL ) ) '>' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3646:2: () '<' ( (lv_String_2_0= RULE_ALL ) ) '>'
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3646:2: ()
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3647:5: 
            {
             
                    temp=factory.create(grammarAccess.getInsertJavaAccess().getInsertJavaAction_0().getType().getClassifier());
                    current = temp; 
                    temp = null;
                    CompositeNode newNode = createCompositeNode(grammarAccess.getInsertJavaAccess().getInsertJavaAction_0(), currentNode.getParent());
                newNode.getChildren().add(currentNode);
                moveLookaheadInfo(currentNode, newNode);
                currentNode = newNode; 
                    associateNodeWithAstElement(currentNode, current); 
                

            }

            match(input,44,FOLLOW_44_in_ruleInsertJava6081); 

                    createLeafNode(grammarAccess.getInsertJavaAccess().getLessThanSignKeyword_1(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3661:1: ( (lv_String_2_0= RULE_ALL ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3662:1: (lv_String_2_0= RULE_ALL )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3662:1: (lv_String_2_0= RULE_ALL )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3663:3: lv_String_2_0= RULE_ALL
            {
            lv_String_2_0=(Token)input.LT(1);
            match(input,RULE_ALL,FOLLOW_RULE_ALL_in_ruleInsertJava6098); 

            			createLeafNode(grammarAccess.getInsertJavaAccess().getStringALLTerminalRuleCall_2_0(), "String"); 
            		

            	        if (current==null) {
            	            current = factory.create(grammarAccess.getInsertJavaRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"String",
            	        		lv_String_2_0, 
            	        		"ALL", 
            	        		lastConsumedNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	    

            }


            }

            match(input,45,FOLLOW_45_in_ruleInsertJava6113); 

                    createLeafNode(grammarAccess.getInsertJavaAccess().getGreaterThanSignKeyword_3(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleInsertJava


    // $ANTLR start entryRuleThis
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3697:1: entryRuleThis returns [EObject current=null] : iv_ruleThis= ruleThis EOF ;
    public final EObject entryRuleThis() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleThis = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3698:2: (iv_ruleThis= ruleThis EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3699:2: iv_ruleThis= ruleThis EOF
            {
             currentNode = createCompositeNode(grammarAccess.getThisRule(), currentNode); 
            pushFollow(FOLLOW_ruleThis_in_entryRuleThis6149);
            iv_ruleThis=ruleThis();
            _fsp--;

             current =iv_ruleThis; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleThis6159); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleThis


    // $ANTLR start ruleThis
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3706:1: ruleThis returns [EObject current=null] : ( (lv_variable_0_0= 'this' ) ) ;
    public final EObject ruleThis() throws RecognitionException {
        EObject current = null;

        Token lv_variable_0_0=null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3711:6: ( ( (lv_variable_0_0= 'this' ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3712:1: ( (lv_variable_0_0= 'this' ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3712:1: ( (lv_variable_0_0= 'this' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3713:1: (lv_variable_0_0= 'this' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3713:1: (lv_variable_0_0= 'this' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3714:3: lv_variable_0_0= 'this'
            {
            lv_variable_0_0=(Token)input.LT(1);
            match(input,26,FOLLOW_26_in_ruleThis6201); 

                    createLeafNode(grammarAccess.getThisAccess().getVariableThisKeyword_0(), "variable"); 
                

            	        if (current==null) {
            	            current = factory.create(grammarAccess.getThisRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
            	        
            	        try {
            	       		set(current, "variable", lv_variable_0_0, "this", lastConsumedNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	    

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleThis


    // $ANTLR start entryRuleVariable
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3741:1: entryRuleVariable returns [EObject current=null] : iv_ruleVariable= ruleVariable EOF ;
    public final EObject entryRuleVariable() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleVariable = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3742:2: (iv_ruleVariable= ruleVariable EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3743:2: iv_ruleVariable= ruleVariable EOF
            {
             currentNode = createCompositeNode(grammarAccess.getVariableRule(), currentNode); 
            pushFollow(FOLLOW_ruleVariable_in_entryRuleVariable6249);
            iv_ruleVariable=ruleVariable();
            _fsp--;

             current =iv_ruleVariable; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleVariable6259); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleVariable


    // $ANTLR start ruleVariable
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3750:1: ruleVariable returns [EObject current=null] : ( ( ( RULE_ID ) ) | ( ( RULE_ID ) ) ) ;
    public final EObject ruleVariable() throws RecognitionException {
        EObject current = null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3755:6: ( ( ( ( RULE_ID ) ) | ( ( RULE_ID ) ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3756:1: ( ( ( RULE_ID ) ) | ( ( RULE_ID ) ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3756:1: ( ( ( RULE_ID ) ) | ( ( RULE_ID ) ) )
            int alt50=2;
            int LA50_0 = input.LA(1);

            if ( (LA50_0==RULE_ID) ) {
                alt50=1;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("3756:1: ( ( ( RULE_ID ) ) | ( ( RULE_ID ) ) )", 50, 0, input);

                throw nvae;
            }
            switch (alt50) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3756:2: ( ( RULE_ID ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3756:2: ( ( RULE_ID ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3757:1: ( RULE_ID )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3757:1: ( RULE_ID )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3758:3: RULE_ID
                    {

                    			if (current==null) {
                    	            current = factory.create(grammarAccess.getVariableRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                            
                    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleVariable6302); 

                    		createLeafNode(grammarAccess.getVariableAccess().getParameterParameterCrossReference_0_0(), "parameter"); 
                    	

                    }


                    }


                    }
                    break;
                case 2 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3771:6: ( ( RULE_ID ) )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3771:6: ( ( RULE_ID ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3772:1: ( RULE_ID )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3772:1: ( RULE_ID )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3773:3: RULE_ID
                    {

                    			if (current==null) {
                    	            current = factory.create(grammarAccess.getVariableRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                            
                    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleVariable6326); 

                    		createLeafNode(grammarAccess.getVariableAccess().getFieldRefFieldRefCrossReference_1_0(), "fieldRef"); 
                    	

                    }


                    }


                    }
                    break;

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleVariable


    // $ANTLR start entryRuleNew
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3793:1: entryRuleNew returns [EObject current=null] : iv_ruleNew= ruleNew EOF ;
    public final EObject entryRuleNew() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleNew = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3794:2: (iv_ruleNew= ruleNew EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3795:2: iv_ruleNew= ruleNew EOF
            {
             currentNode = createCompositeNode(grammarAccess.getNewRule(), currentNode); 
            pushFollow(FOLLOW_ruleNew_in_entryRuleNew6362);
            iv_ruleNew=ruleNew();
            _fsp--;

             current =iv_ruleNew; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleNew6372); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleNew


    // $ANTLR start ruleNew
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3802:1: ruleNew returns [EObject current=null] : ( 'new' ( ( RULE_ID ) ) '(' ( ( (lv_args_3_0= ruleArgument ) ) ( ',' ( (lv_args_5_0= ruleArgument ) ) )* )? ')' ) ;
    public final EObject ruleNew() throws RecognitionException {
        EObject current = null;

        EObject lv_args_3_0 = null;

        EObject lv_args_5_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3807:6: ( ( 'new' ( ( RULE_ID ) ) '(' ( ( (lv_args_3_0= ruleArgument ) ) ( ',' ( (lv_args_5_0= ruleArgument ) ) )* )? ')' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3808:1: ( 'new' ( ( RULE_ID ) ) '(' ( ( (lv_args_3_0= ruleArgument ) ) ( ',' ( (lv_args_5_0= ruleArgument ) ) )* )? ')' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3808:1: ( 'new' ( ( RULE_ID ) ) '(' ( ( (lv_args_3_0= ruleArgument ) ) ( ',' ( (lv_args_5_0= ruleArgument ) ) )* )? ')' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3808:3: 'new' ( ( RULE_ID ) ) '(' ( ( (lv_args_3_0= ruleArgument ) ) ( ',' ( (lv_args_5_0= ruleArgument ) ) )* )? ')'
            {
            match(input,46,FOLLOW_46_in_ruleNew6407); 

                    createLeafNode(grammarAccess.getNewAccess().getNewKeyword_0(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3812:1: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3813:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3813:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3814:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getNewRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleNew6425); 

            		createLeafNode(grammarAccess.getNewAccess().getTypeClassCrossReference_1_0(), "type"); 
            	

            }


            }

            match(input,22,FOLLOW_22_in_ruleNew6435); 

                    createLeafNode(grammarAccess.getNewAccess().getLeftParenthesisKeyword_2(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3830:1: ( ( (lv_args_3_0= ruleArgument ) ) ( ',' ( (lv_args_5_0= ruleArgument ) ) )* )?
            int alt52=2;
            int LA52_0 = input.LA(1);

            if ( ((LA52_0>=RULE_STRING && LA52_0<=RULE_ID)||LA52_0==RULE_INT||LA52_0==22||LA52_0==26||(LA52_0>=46 && LA52_0<=48)) ) {
                alt52=1;
            }
            switch (alt52) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3830:2: ( (lv_args_3_0= ruleArgument ) ) ( ',' ( (lv_args_5_0= ruleArgument ) ) )*
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3830:2: ( (lv_args_3_0= ruleArgument ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3831:1: (lv_args_3_0= ruleArgument )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3831:1: (lv_args_3_0= ruleArgument )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3832:3: lv_args_3_0= ruleArgument
                    {
                     
                    	        currentNode=createCompositeNode(grammarAccess.getNewAccess().getArgsArgumentParserRuleCall_3_0_0(), currentNode); 
                    	    
                    pushFollow(FOLLOW_ruleArgument_in_ruleNew6457);
                    lv_args_3_0=ruleArgument();
                    _fsp--;


                    	        if (current==null) {
                    	            current = factory.create(grammarAccess.getNewRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	        }
                    	        try {
                    	       		add(
                    	       			current, 
                    	       			"args",
                    	        		lv_args_3_0, 
                    	        		"Argument", 
                    	        		currentNode);
                    	        } catch (ValueConverterException vce) {
                    				handleValueConverterException(vce);
                    	        }
                    	        currentNode = currentNode.getParent();
                    	    

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3854:2: ( ',' ( (lv_args_5_0= ruleArgument ) ) )*
                    loop51:
                    do {
                        int alt51=2;
                        int LA51_0 = input.LA(1);

                        if ( (LA51_0==14) ) {
                            alt51=1;
                        }


                        switch (alt51) {
                    	case 1 :
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3854:4: ',' ( (lv_args_5_0= ruleArgument ) )
                    	    {
                    	    match(input,14,FOLLOW_14_in_ruleNew6468); 

                    	            createLeafNode(grammarAccess.getNewAccess().getCommaKeyword_3_1_0(), null); 
                    	        
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3858:1: ( (lv_args_5_0= ruleArgument ) )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3859:1: (lv_args_5_0= ruleArgument )
                    	    {
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3859:1: (lv_args_5_0= ruleArgument )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3860:3: lv_args_5_0= ruleArgument
                    	    {
                    	     
                    	    	        currentNode=createCompositeNode(grammarAccess.getNewAccess().getArgsArgumentParserRuleCall_3_1_1_0(), currentNode); 
                    	    	    
                    	    pushFollow(FOLLOW_ruleArgument_in_ruleNew6489);
                    	    lv_args_5_0=ruleArgument();
                    	    _fsp--;


                    	    	        if (current==null) {
                    	    	            current = factory.create(grammarAccess.getNewRule().getType().getClassifier());
                    	    	            associateNodeWithAstElement(currentNode.getParent(), current);
                    	    	        }
                    	    	        try {
                    	    	       		add(
                    	    	       			current, 
                    	    	       			"args",
                    	    	        		lv_args_5_0, 
                    	    	        		"Argument", 
                    	    	        		currentNode);
                    	    	        } catch (ValueConverterException vce) {
                    	    				handleValueConverterException(vce);
                    	    	        }
                    	    	        currentNode = currentNode.getParent();
                    	    	    

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop51;
                        }
                    } while (true);


                    }
                    break;

            }

            match(input,23,FOLLOW_23_in_ruleNew6503); 

                    createLeafNode(grammarAccess.getNewAccess().getRightParenthesisKeyword_4(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleNew


    // $ANTLR start entryRuleCast
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3894:1: entryRuleCast returns [EObject current=null] : iv_ruleCast= ruleCast EOF ;
    public final EObject entryRuleCast() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleCast = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3895:2: (iv_ruleCast= ruleCast EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3896:2: iv_ruleCast= ruleCast EOF
            {
             currentNode = createCompositeNode(grammarAccess.getCastRule(), currentNode); 
            pushFollow(FOLLOW_ruleCast_in_entryRuleCast6539);
            iv_ruleCast=ruleCast();
            _fsp--;

             current =iv_ruleCast; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleCast6549); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleCast


    // $ANTLR start ruleCast
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3903:1: ruleCast returns [EObject current=null] : ( ( '(' '(' ( ( RULE_ID ) ) ')' ( (lv_expression_4_0= ruleExpression ) ) ) ')' ) ;
    public final EObject ruleCast() throws RecognitionException {
        EObject current = null;

        EObject lv_expression_4_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3908:6: ( ( ( '(' '(' ( ( RULE_ID ) ) ')' ( (lv_expression_4_0= ruleExpression ) ) ) ')' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3909:1: ( ( '(' '(' ( ( RULE_ID ) ) ')' ( (lv_expression_4_0= ruleExpression ) ) ) ')' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3909:1: ( ( '(' '(' ( ( RULE_ID ) ) ')' ( (lv_expression_4_0= ruleExpression ) ) ) ')' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3909:2: ( '(' '(' ( ( RULE_ID ) ) ')' ( (lv_expression_4_0= ruleExpression ) ) ) ')'
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3909:2: ( '(' '(' ( ( RULE_ID ) ) ')' ( (lv_expression_4_0= ruleExpression ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3909:4: '(' '(' ( ( RULE_ID ) ) ')' ( (lv_expression_4_0= ruleExpression ) )
            {
            match(input,22,FOLLOW_22_in_ruleCast6585); 

                    createLeafNode(grammarAccess.getCastAccess().getLeftParenthesisKeyword_0_0(), null); 
                
            match(input,22,FOLLOW_22_in_ruleCast6595); 

                    createLeafNode(grammarAccess.getCastAccess().getLeftParenthesisKeyword_0_1(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3917:1: ( ( RULE_ID ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3918:1: ( RULE_ID )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3918:1: ( RULE_ID )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3919:3: RULE_ID
            {

            			if (current==null) {
            	            current = factory.create(grammarAccess.getCastRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
                    
            match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleCast6613); 

            		createLeafNode(grammarAccess.getCastAccess().getTypeClassCrossReference_0_2_0(), "type"); 
            	

            }


            }

            match(input,23,FOLLOW_23_in_ruleCast6623); 

                    createLeafNode(grammarAccess.getCastAccess().getRightParenthesisKeyword_0_3(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3935:1: ( (lv_expression_4_0= ruleExpression ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3936:1: (lv_expression_4_0= ruleExpression )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3936:1: (lv_expression_4_0= ruleExpression )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3937:3: lv_expression_4_0= ruleExpression
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getCastAccess().getExpressionExpressionParserRuleCall_0_4_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleExpression_in_ruleCast6644);
            lv_expression_4_0=ruleExpression();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getCastRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"expression",
            	        		lv_expression_4_0, 
            	        		"Expression", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }


            }

            match(input,23,FOLLOW_23_in_ruleCast6655); 

                    createLeafNode(grammarAccess.getCastAccess().getRightParenthesisKeyword_1(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleCast


    // $ANTLR start entryRuleOriginal
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3971:1: entryRuleOriginal returns [EObject current=null] : iv_ruleOriginal= ruleOriginal EOF ;
    public final EObject entryRuleOriginal() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleOriginal = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3972:2: (iv_ruleOriginal= ruleOriginal EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3973:2: iv_ruleOriginal= ruleOriginal EOF
            {
             currentNode = createCompositeNode(grammarAccess.getOriginalRule(), currentNode); 
            pushFollow(FOLLOW_ruleOriginal_in_entryRuleOriginal6691);
            iv_ruleOriginal=ruleOriginal();
            _fsp--;

             current =iv_ruleOriginal; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleOriginal6701); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleOriginal


    // $ANTLR start ruleOriginal
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3980:1: ruleOriginal returns [EObject current=null] : ( () 'original' '(' ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? ')' ) ;
    public final EObject ruleOriginal() throws RecognitionException {
        EObject current = null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3985:6: ( ( () 'original' '(' ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? ')' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3986:1: ( () 'original' '(' ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? ')' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3986:1: ( () 'original' '(' ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? ')' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3986:2: () 'original' '(' ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )? ')'
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3986:2: ()
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:3987:5: 
            {
             
                    temp=factory.create(grammarAccess.getOriginalAccess().getOriginalAction_0().getType().getClassifier());
                    current = temp; 
                    temp = null;
                    CompositeNode newNode = createCompositeNode(grammarAccess.getOriginalAccess().getOriginalAction_0(), currentNode.getParent());
                newNode.getChildren().add(currentNode);
                moveLookaheadInfo(currentNode, newNode);
                currentNode = newNode; 
                    associateNodeWithAstElement(currentNode, current); 
                

            }

            match(input,47,FOLLOW_47_in_ruleOriginal6745); 

                    createLeafNode(grammarAccess.getOriginalAccess().getOriginalKeyword_1(), null); 
                
            match(input,22,FOLLOW_22_in_ruleOriginal6755); 

                    createLeafNode(grammarAccess.getOriginalAccess().getLeftParenthesisKeyword_2(), null); 
                
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4005:1: ( ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )* )?
            int alt54=2;
            int LA54_0 = input.LA(1);

            if ( (LA54_0==RULE_ID) ) {
                alt54=1;
            }
            switch (alt54) {
                case 1 :
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4005:2: ( ( RULE_ID ) ) ( ',' ( ( RULE_ID ) ) )*
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4005:2: ( ( RULE_ID ) )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4006:1: ( RULE_ID )
                    {
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4006:1: ( RULE_ID )
                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4007:3: RULE_ID
                    {

                    			if (current==null) {
                    	            current = factory.create(grammarAccess.getOriginalRule().getType().getClassifier());
                    	            associateNodeWithAstElement(currentNode, current);
                    	        }
                            
                    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleOriginal6774); 

                    		createLeafNode(grammarAccess.getOriginalAccess().getParParameterCrossReference_3_0_0(), "par"); 
                    	

                    }


                    }

                    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4019:2: ( ',' ( ( RULE_ID ) ) )*
                    loop53:
                    do {
                        int alt53=2;
                        int LA53_0 = input.LA(1);

                        if ( (LA53_0==14) ) {
                            alt53=1;
                        }


                        switch (alt53) {
                    	case 1 :
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4019:4: ',' ( ( RULE_ID ) )
                    	    {
                    	    match(input,14,FOLLOW_14_in_ruleOriginal6785); 

                    	            createLeafNode(grammarAccess.getOriginalAccess().getCommaKeyword_3_1_0(), null); 
                    	        
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4023:1: ( ( RULE_ID ) )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4024:1: ( RULE_ID )
                    	    {
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4024:1: ( RULE_ID )
                    	    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4025:3: RULE_ID
                    	    {

                    	    			if (current==null) {
                    	    	            current = factory.create(grammarAccess.getOriginalRule().getType().getClassifier());
                    	    	            associateNodeWithAstElement(currentNode, current);
                    	    	        }
                    	            
                    	    match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleOriginal6803); 

                    	    		createLeafNode(grammarAccess.getOriginalAccess().getParParameterCrossReference_3_1_1_0(), "par"); 
                    	    	

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop53;
                        }
                    } while (true);


                    }
                    break;

            }

            match(input,23,FOLLOW_23_in_ruleOriginal6817); 

                    createLeafNode(grammarAccess.getOriginalAccess().getRightParenthesisKeyword_4(), null); 
                

            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleOriginal


    // $ANTLR start entryRuleIntero
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4049:1: entryRuleIntero returns [EObject current=null] : iv_ruleIntero= ruleIntero EOF ;
    public final EObject entryRuleIntero() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleIntero = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4050:2: (iv_ruleIntero= ruleIntero EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4051:2: iv_ruleIntero= ruleIntero EOF
            {
             currentNode = createCompositeNode(grammarAccess.getInteroRule(), currentNode); 
            pushFollow(FOLLOW_ruleIntero_in_entryRuleIntero6853);
            iv_ruleIntero=ruleIntero();
            _fsp--;

             current =iv_ruleIntero; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleIntero6863); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleIntero


    // $ANTLR start ruleIntero
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4058:1: ruleIntero returns [EObject current=null] : ( (lv_value_0_0= RULE_INT ) ) ;
    public final EObject ruleIntero() throws RecognitionException {
        EObject current = null;

        Token lv_value_0_0=null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4063:6: ( ( (lv_value_0_0= RULE_INT ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4064:1: ( (lv_value_0_0= RULE_INT ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4064:1: ( (lv_value_0_0= RULE_INT ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4065:1: (lv_value_0_0= RULE_INT )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4065:1: (lv_value_0_0= RULE_INT )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4066:3: lv_value_0_0= RULE_INT
            {
            lv_value_0_0=(Token)input.LT(1);
            match(input,RULE_INT,FOLLOW_RULE_INT_in_ruleIntero6904); 

            			createLeafNode(grammarAccess.getInteroAccess().getValueINTTerminalRuleCall_0(), "value"); 
            		

            	        if (current==null) {
            	            current = factory.create(grammarAccess.getInteroRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"value",
            	        		lv_value_0_0, 
            	        		"INT", 
            	        		lastConsumedNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	    

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleIntero


    // $ANTLR start entryRuleStringa
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4096:1: entryRuleStringa returns [EObject current=null] : iv_ruleStringa= ruleStringa EOF ;
    public final EObject entryRuleStringa() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleStringa = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4097:2: (iv_ruleStringa= ruleStringa EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4098:2: iv_ruleStringa= ruleStringa EOF
            {
             currentNode = createCompositeNode(grammarAccess.getStringaRule(), currentNode); 
            pushFollow(FOLLOW_ruleStringa_in_entryRuleStringa6944);
            iv_ruleStringa=ruleStringa();
            _fsp--;

             current =iv_ruleStringa; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleStringa6954); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleStringa


    // $ANTLR start ruleStringa
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4105:1: ruleStringa returns [EObject current=null] : ( (lv_value_0_0= RULE_STRING ) ) ;
    public final EObject ruleStringa() throws RecognitionException {
        EObject current = null;

        Token lv_value_0_0=null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4110:6: ( ( (lv_value_0_0= RULE_STRING ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4111:1: ( (lv_value_0_0= RULE_STRING ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4111:1: ( (lv_value_0_0= RULE_STRING ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4112:1: (lv_value_0_0= RULE_STRING )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4112:1: (lv_value_0_0= RULE_STRING )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4113:3: lv_value_0_0= RULE_STRING
            {
            lv_value_0_0=(Token)input.LT(1);
            match(input,RULE_STRING,FOLLOW_RULE_STRING_in_ruleStringa6995); 

            			createLeafNode(grammarAccess.getStringaAccess().getValueSTRINGTerminalRuleCall_0(), "value"); 
            		

            	        if (current==null) {
            	            current = factory.create(grammarAccess.getStringaRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"value",
            	        		lv_value_0_0, 
            	        		"STRING", 
            	        		lastConsumedNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	    

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleStringa


    // $ANTLR start entryRuleNullo
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4143:1: entryRuleNullo returns [EObject current=null] : iv_ruleNullo= ruleNullo EOF ;
    public final EObject entryRuleNullo() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleNullo = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4144:2: (iv_ruleNullo= ruleNullo EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4145:2: iv_ruleNullo= ruleNullo EOF
            {
             currentNode = createCompositeNode(grammarAccess.getNulloRule(), currentNode); 
            pushFollow(FOLLOW_ruleNullo_in_entryRuleNullo7035);
            iv_ruleNullo=ruleNullo();
            _fsp--;

             current =iv_ruleNullo; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleNullo7045); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleNullo


    // $ANTLR start ruleNullo
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4152:1: ruleNullo returns [EObject current=null] : ( (lv_value_0_0= 'null' ) ) ;
    public final EObject ruleNullo() throws RecognitionException {
        EObject current = null;

        Token lv_value_0_0=null;

         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4157:6: ( ( (lv_value_0_0= 'null' ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4158:1: ( (lv_value_0_0= 'null' ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4158:1: ( (lv_value_0_0= 'null' ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4159:1: (lv_value_0_0= 'null' )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4159:1: (lv_value_0_0= 'null' )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4160:3: lv_value_0_0= 'null'
            {
            lv_value_0_0=(Token)input.LT(1);
            match(input,48,FOLLOW_48_in_ruleNullo7087); 

                    createLeafNode(grammarAccess.getNulloAccess().getValueNullKeyword_0(), "value"); 
                

            	        if (current==null) {
            	            current = factory.create(grammarAccess.getNulloRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode, current);
            	        }
            	        
            	        try {
            	       		set(current, "value", lv_value_0_0, "null", lastConsumedNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	    

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleNullo


    // $ANTLR start entryRuleArgument
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4187:1: entryRuleArgument returns [EObject current=null] : iv_ruleArgument= ruleArgument EOF ;
    public final EObject entryRuleArgument() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleArgument = null;


        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4188:2: (iv_ruleArgument= ruleArgument EOF )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4189:2: iv_ruleArgument= ruleArgument EOF
            {
             currentNode = createCompositeNode(grammarAccess.getArgumentRule(), currentNode); 
            pushFollow(FOLLOW_ruleArgument_in_entryRuleArgument7135);
            iv_ruleArgument=ruleArgument();
            _fsp--;

             current =iv_ruleArgument; 
            match(input,EOF,FOLLOW_EOF_in_entryRuleArgument7145); 

            }

        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end entryRuleArgument


    // $ANTLR start ruleArgument
    // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4196:1: ruleArgument returns [EObject current=null] : ( (lv_expression_0_0= ruleExpression ) ) ;
    public final EObject ruleArgument() throws RecognitionException {
        EObject current = null;

        EObject lv_expression_0_0 = null;


         EObject temp=null; setCurrentLookahead(); resetLookahead(); 
            
        try {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4201:6: ( ( (lv_expression_0_0= ruleExpression ) ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4202:1: ( (lv_expression_0_0= ruleExpression ) )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4202:1: ( (lv_expression_0_0= ruleExpression ) )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4203:1: (lv_expression_0_0= ruleExpression )
            {
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4203:1: (lv_expression_0_0= ruleExpression )
            // ../org.xtext.example.dj/src-gen/org/xtext/example/parser/antlr/internal/InternalDJ.g:4204:3: lv_expression_0_0= ruleExpression
            {
             
            	        currentNode=createCompositeNode(grammarAccess.getArgumentAccess().getExpressionExpressionParserRuleCall_0(), currentNode); 
            	    
            pushFollow(FOLLOW_ruleExpression_in_ruleArgument7190);
            lv_expression_0_0=ruleExpression();
            _fsp--;


            	        if (current==null) {
            	            current = factory.create(grammarAccess.getArgumentRule().getType().getClassifier());
            	            associateNodeWithAstElement(currentNode.getParent(), current);
            	        }
            	        try {
            	       		set(
            	       			current, 
            	       			"expression",
            	        		lv_expression_0_0, 
            	        		"Expression", 
            	        		currentNode);
            	        } catch (ValueConverterException vce) {
            				handleValueConverterException(vce);
            	        }
            	        currentNode = currentNode.getParent();
            	    

            }


            }


            }

             resetLookahead(); 
                	lastConsumedNode = currentNode;
                
        }
         
            catch (RecognitionException re) { 
                recover(input,re); 
                appendSkippedTokens();
            } 
        finally {
        }
        return current;
    }
    // $ANTLR end ruleArgument


 

    public static final BitSet FOLLOW_ruleProgram_in_entryRuleProgram75 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleProgram85 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleImport_in_ruleProgram131 = new BitSet(new long[]{0x0000000000033002L});
    public static final BitSet FOLLOW_ruleFeatures_in_ruleProgram153 = new BitSet(new long[]{0x0000000000030002L});
    public static final BitSet FOLLOW_ruleModule_in_ruleProgram175 = new BitSet(new long[]{0x0000000000030002L});
    public static final BitSet FOLLOW_ruleImport_in_entryRuleImport212 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleImport222 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_12_in_ruleImport257 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_RULE_STRING_in_ruleImport274 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFeatures_in_entryRuleFeatures315 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleFeatures325 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_13_in_ruleFeatures360 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleFeature_in_ruleFeatures382 = new BitSet(new long[]{0x000000000000C000L});
    public static final BitSet FOLLOW_14_in_ruleFeatures393 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleFeature_in_ruleFeatures414 = new BitSet(new long[]{0x000000000000C000L});
    public static final BitSet FOLLOW_15_in_ruleFeatures427 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleConfiguration_in_ruleFeatures448 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFeature_in_entryRuleFeature484 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleFeature494 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleFeature535 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleModule_in_entryRuleModule575 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleModule585 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_16_in_ruleModule639 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleCore_in_ruleModule673 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_17_in_ruleModule700 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleDelta_in_ruleModule734 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleCore_in_entryRuleCore771 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleCore781 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleCore824 = new BitSet(new long[]{0x0000000000044000L});
    public static final BitSet FOLLOW_14_in_ruleCore835 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleCore853 = new BitSet(new long[]{0x0000000000044000L});
    public static final BitSet FOLLOW_18_in_ruleCore865 = new BitSet(new long[]{0x0000000000180000L});
    public static final BitSet FOLLOW_ruleClass_in_ruleCore886 = new BitSet(new long[]{0x0000000000180000L});
    public static final BitSet FOLLOW_19_in_ruleCore897 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClass_in_entryRuleClass933 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleClass943 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_20_in_ruleClass978 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleClass995 = new BitSet(new long[]{0x0000000000240000L});
    public static final BitSet FOLLOW_21_in_ruleClass1011 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleClass1029 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_18_in_ruleClass1041 = new BitSet(new long[]{0x00000E0000080020L});
    public static final BitSet FOLLOW_ruleField_in_ruleClass1062 = new BitSet(new long[]{0x00000E0000080020L});
    public static final BitSet FOLLOW_ruleConstructor_in_ruleClass1084 = new BitSet(new long[]{0x00000E0000080020L});
    public static final BitSet FOLLOW_ruleMethod_in_ruleClass1106 = new BitSet(new long[]{0x00000E0000080020L});
    public static final BitSet FOLLOW_19_in_ruleClass1117 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleConstructor_in_entryRuleConstructor1153 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleConstructor1163 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleConstructor1206 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleConstructor1216 = new BitSet(new long[]{0x00000E0000800020L});
    public static final BitSet FOLLOW_ruleParameter_in_ruleConstructor1238 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_14_in_ruleConstructor1249 = new BitSet(new long[]{0x00000E0000000020L});
    public static final BitSet FOLLOW_ruleParameter_in_ruleConstructor1270 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_23_in_ruleConstructor1284 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_18_in_ruleConstructor1294 = new BitSet(new long[]{0x0000000005080000L});
    public static final BitSet FOLLOW_ruleConstructorSuperExpression_in_ruleConstructor1315 = new BitSet(new long[]{0x0000000004080000L});
    public static final BitSet FOLLOW_ruleConstructorFieldExpression_in_ruleConstructor1337 = new BitSet(new long[]{0x0000000004080000L});
    public static final BitSet FOLLOW_19_in_ruleConstructor1348 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleConstructorSuperExpression_in_entryRuleConstructorSuperExpression1384 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleConstructorSuperExpression1394 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_24_in_ruleConstructorSuperExpression1439 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleConstructorSuperExpression1449 = new BitSet(new long[]{0x0000000000800020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleConstructorSuperExpression1468 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_14_in_ruleConstructorSuperExpression1479 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleConstructorSuperExpression1497 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_23_in_ruleConstructorSuperExpression1511 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_ruleConstructorSuperExpression1521 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleConstructorFieldExpression_in_entryRuleConstructorFieldExpression1558 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleConstructorFieldExpression1568 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_26_in_ruleConstructorFieldExpression1603 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_27_in_ruleConstructorFieldExpression1613 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleConstructorFieldExpression1631 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_28_in_ruleConstructorFieldExpression1641 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleConstructorFieldExpression1659 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_ruleConstructorFieldExpression1669 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleField_in_entryRuleField1705 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleField1715 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleType_in_ruleField1761 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleFieldRef_in_ruleField1782 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_ruleField1792 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFieldRef_in_entryRuleFieldRef1828 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleFieldRef1838 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleFieldRef1879 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleParameter_in_entryRuleParameter1919 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleParameter1929 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleType_in_ruleParameter1975 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleParameter1992 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethod_in_entryRuleMethod2033 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMethod2043 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleType_in_ruleMethod2089 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleMethodRef_in_ruleMethod2110 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleMethod2120 = new BitSet(new long[]{0x00000E0000800020L});
    public static final BitSet FOLLOW_ruleParameter_in_ruleMethod2142 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_14_in_ruleMethod2153 = new BitSet(new long[]{0x00000E0000000020L});
    public static final BitSet FOLLOW_ruleParameter_in_ruleMethod2174 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_23_in_ruleMethod2188 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_18_in_ruleMethod2198 = new BitSet(new long[]{0x0001D000244800B0L});
    public static final BitSet FOLLOW_ruleMethodBody_in_ruleMethod2219 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_19_in_ruleMethod2229 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodRef_in_entryRuleMethodRef2265 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMethodRef2275 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleMethodRef2316 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodBody_in_entryRuleMethodBody2356 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMethodBody2366 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleInsertJava_in_ruleMethodBody2422 = new BitSet(new long[]{0x0001D000244000B2L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleMethodBody2450 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_ruleMethodBody2460 = new BitSet(new long[]{0x0001D000244000B2L});
    public static final BitSet FOLLOW_29_in_ruleMethodBody2482 = new BitSet(new long[]{0x0001C000064000B0L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleMethodBody2516 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_ruleMethodBody2527 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleDelta_in_entryRuleDelta2565 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleDelta2575 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleDelta2617 = new BitSet(new long[]{0x00000000C0000000L});
    public static final BitSet FOLLOW_30_in_ruleDelta2633 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleDelta2651 = new BitSet(new long[]{0x0000000080004000L});
    public static final BitSet FOLLOW_14_in_ruleDelta2662 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleDelta2680 = new BitSet(new long[]{0x0000000080004000L});
    public static final BitSet FOLLOW_31_in_ruleDelta2694 = new BitSet(new long[]{0x0000001000400020L});
    public static final BitSet FOLLOW_ruleCondition_in_ruleDelta2715 = new BitSet(new long[]{0x0000000100040000L});
    public static final BitSet FOLLOW_32_in_ruleDelta2726 = new BitSet(new long[]{0x0000001000400020L});
    public static final BitSet FOLLOW_ruleCondition_in_ruleDelta2747 = new BitSet(new long[]{0x0000000100040000L});
    public static final BitSet FOLLOW_18_in_ruleDelta2759 = new BitSet(new long[]{0x000000E000080000L});
    public static final BitSet FOLLOW_ruleClassm_in_ruleDelta2780 = new BitSet(new long[]{0x000000E000080000L});
    public static final BitSet FOLLOW_19_in_ruleDelta2791 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleConfiguration_in_entryRuleConfiguration2827 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleConfiguration2837 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleConfig_in_ruleConfiguration2883 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_ruleConfiguration2893 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_ruleConfig_in_entryRuleConfig2930 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleConfig2940 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleConfig2983 = new BitSet(new long[]{0x0000000000004002L});
    public static final BitSet FOLLOW_14_in_ruleConfig2994 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleConfig3012 = new BitSet(new long[]{0x0000000000004002L});
    public static final BitSet FOLLOW_ruleOperation_in_entryRuleOperation3051 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleOperation3062 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_32_in_ruleOperation3100 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_33_in_ruleOperation3119 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_34_in_ruleOperation3138 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_35_in_ruleOperation3157 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleCondition_in_entryRuleCondition3197 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleCondition3207 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_36_in_ruleCondition3250 = new BitSet(new long[]{0x0000000000400020L});
    public static final BitSet FOLLOW_22_in_ruleCondition3276 = new BitSet(new long[]{0x0000001000400020L});
    public static final BitSet FOLLOW_ruleCondition_in_ruleCondition3297 = new BitSet(new long[]{0x0000000F00000000L});
    public static final BitSet FOLLOW_ruleOperation_in_ruleCondition3318 = new BitSet(new long[]{0x0000001000400020L});
    public static final BitSet FOLLOW_ruleCondition_in_ruleCondition3339 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_23_in_ruleCondition3349 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleCondition3374 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClassm_in_entryRuleClassm3411 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleClassm3421 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_37_in_ruleClassm3465 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_ruleModifiesClass_in_ruleClassm3499 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_38_in_ruleClassm3525 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_ruleAddsClass_in_ruleClassm3559 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_39_in_ruleClassm3585 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleRemoveClass_in_ruleClassm3619 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleModifiesClass_in_entryRuleModifiesClass3656 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleModifiesClass3666 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_20_in_ruleModifiesClass3701 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleModifiesClass3719 = new BitSet(new long[]{0x0000010000040000L});
    public static final BitSet FOLLOW_40_in_ruleModifiesClass3730 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleModifiesClass3748 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_18_in_ruleModifiesClass3760 = new BitSet(new long[]{0x000000E000080020L});
    public static final BitSet FOLLOW_ruleFieldm_in_ruleModifiesClass3781 = new BitSet(new long[]{0x000000E000080020L});
    public static final BitSet FOLLOW_ruleConstructor_in_ruleModifiesClass3802 = new BitSet(new long[]{0x000000E000080000L});
    public static final BitSet FOLLOW_ruleMethodm_in_ruleModifiesClass3824 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_19_in_ruleModifiesClass3834 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleAddsClass_in_entryRuleAddsClass3870 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleAddsClass3880 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClass_in_ruleAddsClass3925 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleRemoveClass_in_entryRuleRemoveClass3960 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleRemoveClass3970 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleRemoveClass4012 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodm_in_entryRuleMethodm4047 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMethodm4057 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_39_in_ruleMethodm4102 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleRemovesMethod_in_ruleMethodm4123 = new BitSet(new long[]{0x000000E000000002L});
    public static final BitSet FOLLOW_37_in_ruleMethodm4136 = new BitSet(new long[]{0x00000E0000000020L});
    public static final BitSet FOLLOW_ruleModifiesMethod_in_ruleMethodm4157 = new BitSet(new long[]{0x0000006000000002L});
    public static final BitSet FOLLOW_38_in_ruleMethodm4170 = new BitSet(new long[]{0x00000E0000000020L});
    public static final BitSet FOLLOW_ruleAddsMethod_in_ruleMethodm4191 = new BitSet(new long[]{0x0000004000000002L});
    public static final BitSet FOLLOW_ruleAddsMethod_in_entryRuleAddsMethod4229 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleAddsMethod4239 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethod_in_ruleAddsMethod4284 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleModifiesMethod_in_entryRuleModifiesMethod4319 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleModifiesMethod4329 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleType_in_ruleModifiesMethod4384 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleModifiesMethod4402 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleModifiesMethod4412 = new BitSet(new long[]{0x00000E0000800020L});
    public static final BitSet FOLLOW_ruleParameter_in_ruleModifiesMethod4434 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_14_in_ruleModifiesMethod4445 = new BitSet(new long[]{0x00000E0000000020L});
    public static final BitSet FOLLOW_ruleParameter_in_ruleModifiesMethod4466 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_23_in_ruleModifiesMethod4480 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_18_in_ruleModifiesMethod4490 = new BitSet(new long[]{0x0001D000244800B0L});
    public static final BitSet FOLLOW_ruleMethodBody_in_ruleModifiesMethod4511 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_19_in_ruleModifiesMethod4521 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleRemovesMethod_in_entryRuleRemovesMethod4557 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleRemovesMethod4567 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleRemovesMethod4610 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleRemovesMethod4620 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_23_in_ruleRemovesMethod4630 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_ruleRemovesMethod4640 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFieldm_in_entryRuleFieldm4676 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleFieldm4686 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_39_in_ruleFieldm4731 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleRemovesField_in_ruleFieldm4752 = new BitSet(new long[]{0x000000C000000002L});
    public static final BitSet FOLLOW_38_in_ruleFieldm4765 = new BitSet(new long[]{0x00000E0000000020L});
    public static final BitSet FOLLOW_ruleAddsField_in_ruleFieldm4786 = new BitSet(new long[]{0x0000004000000002L});
    public static final BitSet FOLLOW_ruleAddsField_in_entryRuleAddsField4824 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleAddsField4834 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleField_in_ruleAddsField4879 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleRemovesField_in_entryRuleRemovesField4916 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleRemovesField4926 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleRemovesField4969 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_ruleRemovesField4979 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleType_in_entryRuleType5015 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleType5025 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_41_in_ruleType5070 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_ruleType5099 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_43_in_ruleType5128 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleType5168 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleExpression_in_entryRuleExpression5204 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleExpression5214 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleTerminalExpression_in_ruleExpression5260 = new BitSet(new long[]{0x0000000018000002L});
    public static final BitSet FOLLOW_27_in_ruleExpression5280 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleMessage_in_ruleExpression5301 = new BitSet(new long[]{0x0000000018000002L});
    public static final BitSet FOLLOW_28_in_ruleExpression5314 = new BitSet(new long[]{0x0001C000044000B0L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleExpression5335 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMessage_in_entryRuleMessage5373 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMessage5383 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodCall_in_ruleMessage5429 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFieldAccess_in_ruleMessage5456 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodCall_in_entryRuleMethodCall5492 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMethodCall5502 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleMethodCall5545 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleMethodCall5555 = new BitSet(new long[]{0x0001C00004C000B0L});
    public static final BitSet FOLLOW_ruleArgument_in_ruleMethodCall5577 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_14_in_ruleMethodCall5588 = new BitSet(new long[]{0x0001C000044000B0L});
    public static final BitSet FOLLOW_ruleArgument_in_ruleMethodCall5609 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_23_in_ruleMethodCall5623 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFieldAccess_in_entryRuleFieldAccess5659 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleFieldAccess5669 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleFieldAccess5711 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleTerminalExpression_in_entryRuleTerminalExpression5746 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleTerminalExpression5756 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleThis_in_ruleTerminalExpression5802 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleVariable_in_ruleTerminalExpression5829 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleNew_in_ruleTerminalExpression5856 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleCast_in_ruleTerminalExpression5883 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleOriginal_in_ruleTerminalExpression5910 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleIntero_in_ruleTerminalExpression5937 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleStringa_in_ruleTerminalExpression5964 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleNullo_in_ruleTerminalExpression5991 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleInsertJava_in_entryRuleInsertJava6027 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleInsertJava6037 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_44_in_ruleInsertJava6081 = new BitSet(new long[]{0x0000000000000040L});
    public static final BitSet FOLLOW_RULE_ALL_in_ruleInsertJava6098 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_45_in_ruleInsertJava6113 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleThis_in_entryRuleThis6149 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleThis6159 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_26_in_ruleThis6201 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleVariable_in_entryRuleVariable6249 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleVariable6259 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleVariable6302 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleVariable6326 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleNew_in_entryRuleNew6362 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleNew6372 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_46_in_ruleNew6407 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleNew6425 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleNew6435 = new BitSet(new long[]{0x0001C00004C000B0L});
    public static final BitSet FOLLOW_ruleArgument_in_ruleNew6457 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_14_in_ruleNew6468 = new BitSet(new long[]{0x0001C000044000B0L});
    public static final BitSet FOLLOW_ruleArgument_in_ruleNew6489 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_23_in_ruleNew6503 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleCast_in_entryRuleCast6539 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleCast6549 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_22_in_ruleCast6585 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleCast6595 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleCast6613 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_23_in_ruleCast6623 = new BitSet(new long[]{0x0001C000044000B0L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleCast6644 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_23_in_ruleCast6655 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleOriginal_in_entryRuleOriginal6691 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleOriginal6701 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_47_in_ruleOriginal6745 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleOriginal6755 = new BitSet(new long[]{0x0000000000800020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleOriginal6774 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_14_in_ruleOriginal6785 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleOriginal6803 = new BitSet(new long[]{0x0000000000804000L});
    public static final BitSet FOLLOW_23_in_ruleOriginal6817 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleIntero_in_entryRuleIntero6853 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleIntero6863 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_INT_in_ruleIntero6904 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleStringa_in_entryRuleStringa6944 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleStringa6954 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_STRING_in_ruleStringa6995 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleNullo_in_entryRuleNullo7035 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleNullo7045 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_48_in_ruleNullo7087 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleArgument_in_entryRuleArgument7135 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleArgument7145 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleArgument7190 = new BitSet(new long[]{0x0000000000000002L});

}