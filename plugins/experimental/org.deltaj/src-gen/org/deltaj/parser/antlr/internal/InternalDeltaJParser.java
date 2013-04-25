package org.deltaj.parser.antlr.internal; 

import org.eclipse.xtext.*;
import org.eclipse.xtext.parser.*;
import org.eclipse.xtext.parser.impl.*;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.parser.antlr.AbstractInternalAntlrParser;
import org.eclipse.xtext.parser.antlr.XtextTokenStream;
import org.eclipse.xtext.parser.antlr.XtextTokenStream.HiddenTokens;
import org.eclipse.xtext.parser.antlr.AntlrDatatypeRuleToken;
import org.deltaj.services.DeltaJGrammarAccess;



import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
@SuppressWarnings("all")
public class InternalDeltaJParser extends AbstractInternalAntlrParser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "RULE_INT", "RULE_ID", "RULE_JAVAVERBATIM", "RULE_STRING", "RULE_ML_COMMENT", "RULE_SL_COMMENT", "RULE_WS", "RULE_ANY_OTHER", "'<'", "'>'", "'void'", "'int'", "'boolean'", "'String'", "'class'", "'extends'", "'{'", "'}'", "';'", "'('", "','", "')'", "'return'", "'='", "'if'", "'else'", "'+'", "'-'", "'*'", "'/'", "'>='", "'<='", "'=='", "'!='", "'||'", "'&&'", "'!'", "'.'", "'null'", "'this'", "'original'", "'new'", "'true'", "'false'", "'delta'", "'adds'", "'removes'", "'modifies'", "'extending'", "'removesField'", "'removesMethod'", "'spl'", "'features'", "'configurations'", "'deltas'", "'['", "']'", "'when'", "'product'", "'from'", "':'"
    };
    public static final int RULE_ID=5;
    public static final int T__64=64;
    public static final int T__29=29;
    public static final int T__28=28;
    public static final int T__62=62;
    public static final int T__27=27;
    public static final int T__63=63;
    public static final int T__26=26;
    public static final int T__25=25;
    public static final int T__24=24;
    public static final int T__23=23;
    public static final int T__22=22;
    public static final int RULE_ANY_OTHER=11;
    public static final int T__21=21;
    public static final int T__20=20;
    public static final int T__61=61;
    public static final int T__60=60;
    public static final int EOF=-1;
    public static final int T__55=55;
    public static final int T__56=56;
    public static final int T__19=19;
    public static final int T__57=57;
    public static final int T__58=58;
    public static final int T__16=16;
    public static final int T__51=51;
    public static final int T__52=52;
    public static final int T__15=15;
    public static final int T__53=53;
    public static final int T__18=18;
    public static final int T__54=54;
    public static final int T__17=17;
    public static final int T__12=12;
    public static final int T__14=14;
    public static final int T__13=13;
    public static final int T__59=59;
    public static final int RULE_INT=4;
    public static final int T__50=50;
    public static final int T__42=42;
    public static final int T__43=43;
    public static final int T__40=40;
    public static final int T__41=41;
    public static final int T__46=46;
    public static final int T__47=47;
    public static final int T__44=44;
    public static final int T__45=45;
    public static final int T__48=48;
    public static final int T__49=49;
    public static final int RULE_SL_COMMENT=9;
    public static final int RULE_ML_COMMENT=8;
    public static final int T__30=30;
    public static final int T__31=31;
    public static final int RULE_STRING=7;
    public static final int T__32=32;
    public static final int T__33=33;
    public static final int T__34=34;
    public static final int T__35=35;
    public static final int T__36=36;
    public static final int T__37=37;
    public static final int T__38=38;
    public static final int T__39=39;
    public static final int RULE_WS=10;
    public static final int RULE_JAVAVERBATIM=6;

    // delegates
    // delegators


        public InternalDeltaJParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public InternalDeltaJParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return InternalDeltaJParser.tokenNames; }
    public String getGrammarFileName() { return "../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g"; }



    /*
      This grammar contains a lot of empty actions to work around a bug in ANTLR.
      Otherwise the ANTLR tool will create synpreds that cannot be compiled in some rare cases.
    */
     
     	private DeltaJGrammarAccess grammarAccess;
     	
        public InternalDeltaJParser(TokenStream input, DeltaJGrammarAccess grammarAccess) {
            this(input);
            this.grammarAccess = grammarAccess;
            registerRules(grammarAccess.getGrammar());
        }
        
        @Override
        protected String getFirstRuleName() {
        	return "Program";	
       	}
       	
       	@Override
       	protected DeltaJGrammarAccess getGrammarAccess() {
       		return grammarAccess;
       	}



    // $ANTLR start "entryRuleProgram"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:73:1: entryRuleProgram returns [EObject current=null] : iv_ruleProgram= ruleProgram EOF ;
    public final EObject entryRuleProgram() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleProgram = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:74:2: (iv_ruleProgram= ruleProgram EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:75:2: iv_ruleProgram= ruleProgram EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getProgramRule()); 
            }
            pushFollow(FOLLOW_ruleProgram_in_entryRuleProgram81);
            iv_ruleProgram=ruleProgram();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleProgram; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleProgram91); if (state.failed) return current;

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
    // $ANTLR end "entryRuleProgram"


    // $ANTLR start "ruleProgram"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:82:1: ruleProgram returns [EObject current=null] : ( ( (lv_deltaModules_0_0= ruleDeltaModule ) )* ( (lv_productLines_1_0= ruleProductLine ) )* ( (lv_products_2_0= ruleProduct ) )* ) ;
    public final EObject ruleProgram() throws RecognitionException {
        EObject current = null;

        EObject lv_deltaModules_0_0 = null;

        EObject lv_productLines_1_0 = null;

        EObject lv_products_2_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:85:28: ( ( ( (lv_deltaModules_0_0= ruleDeltaModule ) )* ( (lv_productLines_1_0= ruleProductLine ) )* ( (lv_products_2_0= ruleProduct ) )* ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:86:1: ( ( (lv_deltaModules_0_0= ruleDeltaModule ) )* ( (lv_productLines_1_0= ruleProductLine ) )* ( (lv_products_2_0= ruleProduct ) )* )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:86:1: ( ( (lv_deltaModules_0_0= ruleDeltaModule ) )* ( (lv_productLines_1_0= ruleProductLine ) )* ( (lv_products_2_0= ruleProduct ) )* )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:86:2: ( (lv_deltaModules_0_0= ruleDeltaModule ) )* ( (lv_productLines_1_0= ruleProductLine ) )* ( (lv_products_2_0= ruleProduct ) )*
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:86:2: ( (lv_deltaModules_0_0= ruleDeltaModule ) )*
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( (LA1_0==48) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:87:1: (lv_deltaModules_0_0= ruleDeltaModule )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:87:1: (lv_deltaModules_0_0= ruleDeltaModule )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:88:3: lv_deltaModules_0_0= ruleDeltaModule
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getProgramAccess().getDeltaModulesDeltaModuleParserRuleCall_0_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleDeltaModule_in_ruleProgram137);
            	    lv_deltaModules_0_0=ruleDeltaModule();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getProgramRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"deltaModules",
            	              		lv_deltaModules_0_0, 
            	              		"DeltaModule");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop1;
                }
            } while (true);

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:104:3: ( (lv_productLines_1_0= ruleProductLine ) )*
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( (LA2_0==55) ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:105:1: (lv_productLines_1_0= ruleProductLine )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:105:1: (lv_productLines_1_0= ruleProductLine )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:106:3: lv_productLines_1_0= ruleProductLine
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getProgramAccess().getProductLinesProductLineParserRuleCall_1_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleProductLine_in_ruleProgram159);
            	    lv_productLines_1_0=ruleProductLine();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getProgramRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"productLines",
            	              		lv_productLines_1_0, 
            	              		"ProductLine");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop2;
                }
            } while (true);

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:122:3: ( (lv_products_2_0= ruleProduct ) )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( (LA3_0==62) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:123:1: (lv_products_2_0= ruleProduct )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:123:1: (lv_products_2_0= ruleProduct )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:124:3: lv_products_2_0= ruleProduct
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getProgramAccess().getProductsProductParserRuleCall_2_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleProduct_in_ruleProgram181);
            	    lv_products_2_0=ruleProduct();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getProgramRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"products",
            	              		lv_products_2_0, 
            	              		"Product");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop3;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleProgram"


    // $ANTLR start "entryRuleTypeVariable"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:150:1: entryRuleTypeVariable returns [EObject current=null] : iv_ruleTypeVariable= ruleTypeVariable EOF ;
    public final EObject entryRuleTypeVariable() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleTypeVariable = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:151:2: (iv_ruleTypeVariable= ruleTypeVariable EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:152:2: iv_ruleTypeVariable= ruleTypeVariable EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getTypeVariableRule()); 
            }
            pushFollow(FOLLOW_ruleTypeVariable_in_entryRuleTypeVariable220);
            iv_ruleTypeVariable=ruleTypeVariable();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleTypeVariable; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleTypeVariable230); if (state.failed) return current;

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
    // $ANTLR end "entryRuleTypeVariable"


    // $ANTLR start "ruleTypeVariable"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:159:1: ruleTypeVariable returns [EObject current=null] : ( (lv_varName_0_0= ruleTypeVariableId ) ) ;
    public final EObject ruleTypeVariable() throws RecognitionException {
        EObject current = null;

        AntlrDatatypeRuleToken lv_varName_0_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:162:28: ( ( (lv_varName_0_0= ruleTypeVariableId ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:163:1: ( (lv_varName_0_0= ruleTypeVariableId ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:163:1: ( (lv_varName_0_0= ruleTypeVariableId ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:164:1: (lv_varName_0_0= ruleTypeVariableId )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:164:1: (lv_varName_0_0= ruleTypeVariableId )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:165:3: lv_varName_0_0= ruleTypeVariableId
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getTypeVariableAccess().getVarNameTypeVariableIdParserRuleCall_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleTypeVariableId_in_ruleTypeVariable275);
            lv_varName_0_0=ruleTypeVariableId();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getTypeVariableRule());
              	        }
                     		set(
                     			current, 
                     			"varName",
                      		lv_varName_0_0, 
                      		"TypeVariableId");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleTypeVariable"


    // $ANTLR start "entryRuleTypeVariableId"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:189:1: entryRuleTypeVariableId returns [String current=null] : iv_ruleTypeVariableId= ruleTypeVariableId EOF ;
    public final String entryRuleTypeVariableId() throws RecognitionException {
        String current = null;

        AntlrDatatypeRuleToken iv_ruleTypeVariableId = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:190:2: (iv_ruleTypeVariableId= ruleTypeVariableId EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:191:2: iv_ruleTypeVariableId= ruleTypeVariableId EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getTypeVariableIdRule()); 
            }
            pushFollow(FOLLOW_ruleTypeVariableId_in_entryRuleTypeVariableId311);
            iv_ruleTypeVariableId=ruleTypeVariableId();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleTypeVariableId.getText(); 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleTypeVariableId322); if (state.failed) return current;

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
    // $ANTLR end "entryRuleTypeVariableId"


    // $ANTLR start "ruleTypeVariableId"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:198:1: ruleTypeVariableId returns [AntlrDatatypeRuleToken current=new AntlrDatatypeRuleToken()] : (kw= '<' this_INT_1= RULE_INT kw= '>' ) ;
    public final AntlrDatatypeRuleToken ruleTypeVariableId() throws RecognitionException {
        AntlrDatatypeRuleToken current = new AntlrDatatypeRuleToken();

        Token kw=null;
        Token this_INT_1=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:201:28: ( (kw= '<' this_INT_1= RULE_INT kw= '>' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:202:1: (kw= '<' this_INT_1= RULE_INT kw= '>' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:202:1: (kw= '<' this_INT_1= RULE_INT kw= '>' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:203:2: kw= '<' this_INT_1= RULE_INT kw= '>'
            {
            kw=(Token)match(input,12,FOLLOW_12_in_ruleTypeVariableId360); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                      current.merge(kw);
                      newLeafNode(kw, grammarAccess.getTypeVariableIdAccess().getLessThanSignKeyword_0()); 
                  
            }
            this_INT_1=(Token)match(input,RULE_INT,FOLLOW_RULE_INT_in_ruleTypeVariableId375); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              		current.merge(this_INT_1);
                  
            }
            if ( state.backtracking==0 ) {
               
                  newLeafNode(this_INT_1, grammarAccess.getTypeVariableIdAccess().getINTTerminalRuleCall_1()); 
                  
            }
            kw=(Token)match(input,13,FOLLOW_13_in_ruleTypeVariableId393); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                      current.merge(kw);
                      newLeafNode(kw, grammarAccess.getTypeVariableIdAccess().getGreaterThanSignKeyword_2()); 
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleTypeVariableId"


    // $ANTLR start "entryRuleTypeForMethod"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:229:1: entryRuleTypeForMethod returns [EObject current=null] : iv_ruleTypeForMethod= ruleTypeForMethod EOF ;
    public final EObject entryRuleTypeForMethod() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleTypeForMethod = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:230:2: (iv_ruleTypeForMethod= ruleTypeForMethod EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:231:2: iv_ruleTypeForMethod= ruleTypeForMethod EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getTypeForMethodRule()); 
            }
            pushFollow(FOLLOW_ruleTypeForMethod_in_entryRuleTypeForMethod433);
            iv_ruleTypeForMethod=ruleTypeForMethod();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleTypeForMethod; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleTypeForMethod443); if (state.failed) return current;

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
    // $ANTLR end "entryRuleTypeForMethod"


    // $ANTLR start "ruleTypeForMethod"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:238:1: ruleTypeForMethod returns [EObject current=null] : (this_VoidType_0= ruleVoidType | this_TypeForDeclaration_1= ruleTypeForDeclaration ) ;
    public final EObject ruleTypeForMethod() throws RecognitionException {
        EObject current = null;

        EObject this_VoidType_0 = null;

        EObject this_TypeForDeclaration_1 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:241:28: ( (this_VoidType_0= ruleVoidType | this_TypeForDeclaration_1= ruleTypeForDeclaration ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:242:1: (this_VoidType_0= ruleVoidType | this_TypeForDeclaration_1= ruleTypeForDeclaration )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:242:1: (this_VoidType_0= ruleVoidType | this_TypeForDeclaration_1= ruleTypeForDeclaration )
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0==14) ) {
                alt4=1;
            }
            else if ( (LA4_0==RULE_ID||(LA4_0>=15 && LA4_0<=17)) ) {
                alt4=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 4, 0, input);

                throw nvae;
            }
            switch (alt4) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:243:2: this_VoidType_0= ruleVoidType
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getTypeForMethodAccess().getVoidTypeParserRuleCall_0()); 
                          
                    }
                    pushFollow(FOLLOW_ruleVoidType_in_ruleTypeForMethod493);
                    this_VoidType_0=ruleVoidType();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_VoidType_0; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:256:2: this_TypeForDeclaration_1= ruleTypeForDeclaration
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getTypeForMethodAccess().getTypeForDeclarationParserRuleCall_1()); 
                          
                    }
                    pushFollow(FOLLOW_ruleTypeForDeclaration_in_ruleTypeForMethod523);
                    this_TypeForDeclaration_1=ruleTypeForDeclaration();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_TypeForDeclaration_1; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleTypeForMethod"


    // $ANTLR start "entryRuleVoidType"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:275:1: entryRuleVoidType returns [EObject current=null] : iv_ruleVoidType= ruleVoidType EOF ;
    public final EObject entryRuleVoidType() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleVoidType = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:276:2: (iv_ruleVoidType= ruleVoidType EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:277:2: iv_ruleVoidType= ruleVoidType EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getVoidTypeRule()); 
            }
            pushFollow(FOLLOW_ruleVoidType_in_entryRuleVoidType558);
            iv_ruleVoidType=ruleVoidType();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleVoidType; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleVoidType568); if (state.failed) return current;

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
    // $ANTLR end "entryRuleVoidType"


    // $ANTLR start "ruleVoidType"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:284:1: ruleVoidType returns [EObject current=null] : ( (lv_void_0_0= 'void' ) ) ;
    public final EObject ruleVoidType() throws RecognitionException {
        EObject current = null;

        Token lv_void_0_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:287:28: ( ( (lv_void_0_0= 'void' ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:288:1: ( (lv_void_0_0= 'void' ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:288:1: ( (lv_void_0_0= 'void' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:289:1: (lv_void_0_0= 'void' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:289:1: (lv_void_0_0= 'void' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:290:3: lv_void_0_0= 'void'
            {
            lv_void_0_0=(Token)match(input,14,FOLLOW_14_in_ruleVoidType610); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                      newLeafNode(lv_void_0_0, grammarAccess.getVoidTypeAccess().getVoidVoidKeyword_0());
                  
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getVoidTypeRule());
              	        }
                     		setWithLastConsumed(current, "void", lv_void_0_0, "void");
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleVoidType"


    // $ANTLR start "entryRuleTypeForDeclaration"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:311:1: entryRuleTypeForDeclaration returns [EObject current=null] : iv_ruleTypeForDeclaration= ruleTypeForDeclaration EOF ;
    public final EObject entryRuleTypeForDeclaration() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleTypeForDeclaration = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:312:2: (iv_ruleTypeForDeclaration= ruleTypeForDeclaration EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:313:2: iv_ruleTypeForDeclaration= ruleTypeForDeclaration EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getTypeForDeclarationRule()); 
            }
            pushFollow(FOLLOW_ruleTypeForDeclaration_in_entryRuleTypeForDeclaration658);
            iv_ruleTypeForDeclaration=ruleTypeForDeclaration();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleTypeForDeclaration; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleTypeForDeclaration668); if (state.failed) return current;

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
    // $ANTLR end "entryRuleTypeForDeclaration"


    // $ANTLR start "ruleTypeForDeclaration"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:320:1: ruleTypeForDeclaration returns [EObject current=null] : (this_BasicType_0= ruleBasicType | this_ClassType_1= ruleClassType ) ;
    public final EObject ruleTypeForDeclaration() throws RecognitionException {
        EObject current = null;

        EObject this_BasicType_0 = null;

        EObject this_ClassType_1 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:323:28: ( (this_BasicType_0= ruleBasicType | this_ClassType_1= ruleClassType ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:324:1: (this_BasicType_0= ruleBasicType | this_ClassType_1= ruleClassType )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:324:1: (this_BasicType_0= ruleBasicType | this_ClassType_1= ruleClassType )
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( ((LA5_0>=15 && LA5_0<=17)) ) {
                alt5=1;
            }
            else if ( (LA5_0==RULE_ID) ) {
                alt5=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 5, 0, input);

                throw nvae;
            }
            switch (alt5) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:325:2: this_BasicType_0= ruleBasicType
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getTypeForDeclarationAccess().getBasicTypeParserRuleCall_0()); 
                          
                    }
                    pushFollow(FOLLOW_ruleBasicType_in_ruleTypeForDeclaration718);
                    this_BasicType_0=ruleBasicType();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_BasicType_0; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:338:2: this_ClassType_1= ruleClassType
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getTypeForDeclarationAccess().getClassTypeParserRuleCall_1()); 
                          
                    }
                    pushFollow(FOLLOW_ruleClassType_in_ruleTypeForDeclaration748);
                    this_ClassType_1=ruleClassType();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_ClassType_1; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleTypeForDeclaration"


    // $ANTLR start "entryRuleBasicType"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:357:1: entryRuleBasicType returns [EObject current=null] : iv_ruleBasicType= ruleBasicType EOF ;
    public final EObject entryRuleBasicType() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleBasicType = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:358:2: (iv_ruleBasicType= ruleBasicType EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:359:2: iv_ruleBasicType= ruleBasicType EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getBasicTypeRule()); 
            }
            pushFollow(FOLLOW_ruleBasicType_in_entryRuleBasicType783);
            iv_ruleBasicType=ruleBasicType();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleBasicType; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleBasicType793); if (state.failed) return current;

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
    // $ANTLR end "entryRuleBasicType"


    // $ANTLR start "ruleBasicType"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:366:1: ruleBasicType returns [EObject current=null] : (this_IntType_0= ruleIntType | this_BooleanType_1= ruleBooleanType | this_StringType_2= ruleStringType ) ;
    public final EObject ruleBasicType() throws RecognitionException {
        EObject current = null;

        EObject this_IntType_0 = null;

        EObject this_BooleanType_1 = null;

        EObject this_StringType_2 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:369:28: ( (this_IntType_0= ruleIntType | this_BooleanType_1= ruleBooleanType | this_StringType_2= ruleStringType ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:370:1: (this_IntType_0= ruleIntType | this_BooleanType_1= ruleBooleanType | this_StringType_2= ruleStringType )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:370:1: (this_IntType_0= ruleIntType | this_BooleanType_1= ruleBooleanType | this_StringType_2= ruleStringType )
            int alt6=3;
            switch ( input.LA(1) ) {
            case 15:
                {
                alt6=1;
                }
                break;
            case 16:
                {
                alt6=2;
                }
                break;
            case 17:
                {
                alt6=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 6, 0, input);

                throw nvae;
            }

            switch (alt6) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:371:2: this_IntType_0= ruleIntType
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getBasicTypeAccess().getIntTypeParserRuleCall_0()); 
                          
                    }
                    pushFollow(FOLLOW_ruleIntType_in_ruleBasicType843);
                    this_IntType_0=ruleIntType();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_IntType_0; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:384:2: this_BooleanType_1= ruleBooleanType
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getBasicTypeAccess().getBooleanTypeParserRuleCall_1()); 
                          
                    }
                    pushFollow(FOLLOW_ruleBooleanType_in_ruleBasicType873);
                    this_BooleanType_1=ruleBooleanType();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_BooleanType_1; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 3 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:397:2: this_StringType_2= ruleStringType
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getBasicTypeAccess().getStringTypeParserRuleCall_2()); 
                          
                    }
                    pushFollow(FOLLOW_ruleStringType_in_ruleBasicType903);
                    this_StringType_2=ruleStringType();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_StringType_2; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleBasicType"


    // $ANTLR start "entryRuleIntType"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:416:1: entryRuleIntType returns [EObject current=null] : iv_ruleIntType= ruleIntType EOF ;
    public final EObject entryRuleIntType() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleIntType = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:417:2: (iv_ruleIntType= ruleIntType EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:418:2: iv_ruleIntType= ruleIntType EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getIntTypeRule()); 
            }
            pushFollow(FOLLOW_ruleIntType_in_entryRuleIntType938);
            iv_ruleIntType=ruleIntType();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleIntType; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleIntType948); if (state.failed) return current;

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
    // $ANTLR end "entryRuleIntType"


    // $ANTLR start "ruleIntType"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:425:1: ruleIntType returns [EObject current=null] : ( (lv_basic_0_0= 'int' ) ) ;
    public final EObject ruleIntType() throws RecognitionException {
        EObject current = null;

        Token lv_basic_0_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:428:28: ( ( (lv_basic_0_0= 'int' ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:429:1: ( (lv_basic_0_0= 'int' ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:429:1: ( (lv_basic_0_0= 'int' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:430:1: (lv_basic_0_0= 'int' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:430:1: (lv_basic_0_0= 'int' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:431:3: lv_basic_0_0= 'int'
            {
            lv_basic_0_0=(Token)match(input,15,FOLLOW_15_in_ruleIntType990); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                      newLeafNode(lv_basic_0_0, grammarAccess.getIntTypeAccess().getBasicIntKeyword_0());
                  
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getIntTypeRule());
              	        }
                     		setWithLastConsumed(current, "basic", lv_basic_0_0, "int");
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleIntType"


    // $ANTLR start "entryRuleBooleanType"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:452:1: entryRuleBooleanType returns [EObject current=null] : iv_ruleBooleanType= ruleBooleanType EOF ;
    public final EObject entryRuleBooleanType() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleBooleanType = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:453:2: (iv_ruleBooleanType= ruleBooleanType EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:454:2: iv_ruleBooleanType= ruleBooleanType EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getBooleanTypeRule()); 
            }
            pushFollow(FOLLOW_ruleBooleanType_in_entryRuleBooleanType1038);
            iv_ruleBooleanType=ruleBooleanType();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleBooleanType; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleBooleanType1048); if (state.failed) return current;

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
    // $ANTLR end "entryRuleBooleanType"


    // $ANTLR start "ruleBooleanType"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:461:1: ruleBooleanType returns [EObject current=null] : ( (lv_basic_0_0= 'boolean' ) ) ;
    public final EObject ruleBooleanType() throws RecognitionException {
        EObject current = null;

        Token lv_basic_0_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:464:28: ( ( (lv_basic_0_0= 'boolean' ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:465:1: ( (lv_basic_0_0= 'boolean' ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:465:1: ( (lv_basic_0_0= 'boolean' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:466:1: (lv_basic_0_0= 'boolean' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:466:1: (lv_basic_0_0= 'boolean' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:467:3: lv_basic_0_0= 'boolean'
            {
            lv_basic_0_0=(Token)match(input,16,FOLLOW_16_in_ruleBooleanType1090); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                      newLeafNode(lv_basic_0_0, grammarAccess.getBooleanTypeAccess().getBasicBooleanKeyword_0());
                  
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getBooleanTypeRule());
              	        }
                     		setWithLastConsumed(current, "basic", lv_basic_0_0, "boolean");
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleBooleanType"


    // $ANTLR start "entryRuleStringType"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:488:1: entryRuleStringType returns [EObject current=null] : iv_ruleStringType= ruleStringType EOF ;
    public final EObject entryRuleStringType() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleStringType = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:489:2: (iv_ruleStringType= ruleStringType EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:490:2: iv_ruleStringType= ruleStringType EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getStringTypeRule()); 
            }
            pushFollow(FOLLOW_ruleStringType_in_entryRuleStringType1138);
            iv_ruleStringType=ruleStringType();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleStringType; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleStringType1148); if (state.failed) return current;

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
    // $ANTLR end "entryRuleStringType"


    // $ANTLR start "ruleStringType"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:497:1: ruleStringType returns [EObject current=null] : ( (lv_basic_0_0= 'String' ) ) ;
    public final EObject ruleStringType() throws RecognitionException {
        EObject current = null;

        Token lv_basic_0_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:500:28: ( ( (lv_basic_0_0= 'String' ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:501:1: ( (lv_basic_0_0= 'String' ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:501:1: ( (lv_basic_0_0= 'String' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:502:1: (lv_basic_0_0= 'String' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:502:1: (lv_basic_0_0= 'String' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:503:3: lv_basic_0_0= 'String'
            {
            lv_basic_0_0=(Token)match(input,17,FOLLOW_17_in_ruleStringType1190); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                      newLeafNode(lv_basic_0_0, grammarAccess.getStringTypeAccess().getBasicStringKeyword_0());
                  
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getStringTypeRule());
              	        }
                     		setWithLastConsumed(current, "basic", lv_basic_0_0, "String");
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleStringType"


    // $ANTLR start "entryRuleClassType"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:524:1: entryRuleClassType returns [EObject current=null] : iv_ruleClassType= ruleClassType EOF ;
    public final EObject entryRuleClassType() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleClassType = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:525:2: (iv_ruleClassType= ruleClassType EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:526:2: iv_ruleClassType= ruleClassType EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getClassTypeRule()); 
            }
            pushFollow(FOLLOW_ruleClassType_in_entryRuleClassType1238);
            iv_ruleClassType=ruleClassType();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleClassType; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleClassType1248); if (state.failed) return current;

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
    // $ANTLR end "entryRuleClassType"


    // $ANTLR start "ruleClassType"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:533:1: ruleClassType returns [EObject current=null] : ( (lv_classref_0_0= ruleClassName ) ) ;
    public final EObject ruleClassType() throws RecognitionException {
        EObject current = null;

        AntlrDatatypeRuleToken lv_classref_0_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:536:28: ( ( (lv_classref_0_0= ruleClassName ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:537:1: ( (lv_classref_0_0= ruleClassName ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:537:1: ( (lv_classref_0_0= ruleClassName ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:538:1: (lv_classref_0_0= ruleClassName )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:538:1: (lv_classref_0_0= ruleClassName )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:539:3: lv_classref_0_0= ruleClassName
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getClassTypeAccess().getClassrefClassNameParserRuleCall_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleClassName_in_ruleClassType1293);
            lv_classref_0_0=ruleClassName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getClassTypeRule());
              	        }
                     		set(
                     			current, 
                     			"classref",
                      		lv_classref_0_0, 
                      		"ClassName");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleClassType"


    // $ANTLR start "entryRuleClass"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:563:1: entryRuleClass returns [EObject current=null] : iv_ruleClass= ruleClass EOF ;
    public final EObject entryRuleClass() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleClass = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:564:2: (iv_ruleClass= ruleClass EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:565:2: iv_ruleClass= ruleClass EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getClassRule()); 
            }
            pushFollow(FOLLOW_ruleClass_in_entryRuleClass1328);
            iv_ruleClass=ruleClass();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleClass; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleClass1338); if (state.failed) return current;

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
    // $ANTLR end "entryRuleClass"


    // $ANTLR start "ruleClass"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:572:1: ruleClass returns [EObject current=null] : (otherlv_0= 'class' ( (lv_name_1_0= RULE_ID ) ) (otherlv_2= 'extends' ( (lv_extends_3_0= ruleClassName ) ) )? otherlv_4= '{' ( (lv_fields_5_0= ruleField ) )* ( (lv_methods_6_0= ruleMethod ) )* otherlv_7= '}' ) ;
    public final EObject ruleClass() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token lv_name_1_0=null;
        Token otherlv_2=null;
        Token otherlv_4=null;
        Token otherlv_7=null;
        AntlrDatatypeRuleToken lv_extends_3_0 = null;

        EObject lv_fields_5_0 = null;

        EObject lv_methods_6_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:575:28: ( (otherlv_0= 'class' ( (lv_name_1_0= RULE_ID ) ) (otherlv_2= 'extends' ( (lv_extends_3_0= ruleClassName ) ) )? otherlv_4= '{' ( (lv_fields_5_0= ruleField ) )* ( (lv_methods_6_0= ruleMethod ) )* otherlv_7= '}' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:576:1: (otherlv_0= 'class' ( (lv_name_1_0= RULE_ID ) ) (otherlv_2= 'extends' ( (lv_extends_3_0= ruleClassName ) ) )? otherlv_4= '{' ( (lv_fields_5_0= ruleField ) )* ( (lv_methods_6_0= ruleMethod ) )* otherlv_7= '}' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:576:1: (otherlv_0= 'class' ( (lv_name_1_0= RULE_ID ) ) (otherlv_2= 'extends' ( (lv_extends_3_0= ruleClassName ) ) )? otherlv_4= '{' ( (lv_fields_5_0= ruleField ) )* ( (lv_methods_6_0= ruleMethod ) )* otherlv_7= '}' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:576:3: otherlv_0= 'class' ( (lv_name_1_0= RULE_ID ) ) (otherlv_2= 'extends' ( (lv_extends_3_0= ruleClassName ) ) )? otherlv_4= '{' ( (lv_fields_5_0= ruleField ) )* ( (lv_methods_6_0= ruleMethod ) )* otherlv_7= '}'
            {
            otherlv_0=(Token)match(input,18,FOLLOW_18_in_ruleClass1375); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getClassAccess().getClassKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:580:1: ( (lv_name_1_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:581:1: (lv_name_1_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:581:1: (lv_name_1_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:582:3: lv_name_1_0= RULE_ID
            {
            lv_name_1_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleClass1392); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_name_1_0, grammarAccess.getClassAccess().getNameIDTerminalRuleCall_1_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getClassRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"name",
                      		lv_name_1_0, 
                      		"ID");
              	    
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:598:2: (otherlv_2= 'extends' ( (lv_extends_3_0= ruleClassName ) ) )?
            int alt7=2;
            int LA7_0 = input.LA(1);

            if ( (LA7_0==19) ) {
                alt7=1;
            }
            switch (alt7) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:598:4: otherlv_2= 'extends' ( (lv_extends_3_0= ruleClassName ) )
                    {
                    otherlv_2=(Token)match(input,19,FOLLOW_19_in_ruleClass1410); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                          	newLeafNode(otherlv_2, grammarAccess.getClassAccess().getExtendsKeyword_2_0());
                          
                    }
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:602:1: ( (lv_extends_3_0= ruleClassName ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:603:1: (lv_extends_3_0= ruleClassName )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:603:1: (lv_extends_3_0= ruleClassName )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:604:3: lv_extends_3_0= ruleClassName
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getClassAccess().getExtendsClassNameParserRuleCall_2_1_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_ruleClassName_in_ruleClass1431);
                    lv_extends_3_0=ruleClassName();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getClassRule());
                      	        }
                             		set(
                             			current, 
                             			"extends",
                              		lv_extends_3_0, 
                              		"ClassName");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }


                    }
                    break;

            }

            otherlv_4=(Token)match(input,20,FOLLOW_20_in_ruleClass1445); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_4, grammarAccess.getClassAccess().getLeftCurlyBracketKeyword_3());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:624:1: ( (lv_fields_5_0= ruleField ) )*
            loop8:
            do {
                int alt8=2;
                switch ( input.LA(1) ) {
                case 15:
                    {
                    int LA8_2 = input.LA(2);

                    if ( (LA8_2==RULE_ID) ) {
                        int LA8_6 = input.LA(3);

                        if ( (LA8_6==22) ) {
                            alt8=1;
                        }


                    }


                    }
                    break;
                case 16:
                    {
                    int LA8_3 = input.LA(2);

                    if ( (LA8_3==RULE_ID) ) {
                        int LA8_6 = input.LA(3);

                        if ( (LA8_6==22) ) {
                            alt8=1;
                        }


                    }


                    }
                    break;
                case 17:
                    {
                    int LA8_4 = input.LA(2);

                    if ( (LA8_4==RULE_ID) ) {
                        int LA8_6 = input.LA(3);

                        if ( (LA8_6==22) ) {
                            alt8=1;
                        }


                    }


                    }
                    break;
                case RULE_ID:
                    {
                    int LA8_5 = input.LA(2);

                    if ( (LA8_5==RULE_ID) ) {
                        int LA8_6 = input.LA(3);

                        if ( (LA8_6==22) ) {
                            alt8=1;
                        }


                    }


                    }
                    break;

                }

                switch (alt8) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:625:1: (lv_fields_5_0= ruleField )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:625:1: (lv_fields_5_0= ruleField )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:626:3: lv_fields_5_0= ruleField
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getClassAccess().getFieldsFieldParserRuleCall_4_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleField_in_ruleClass1466);
            	    lv_fields_5_0=ruleField();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getClassRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"fields",
            	              		lv_fields_5_0, 
            	              		"Field");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop8;
                }
            } while (true);

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:642:3: ( (lv_methods_6_0= ruleMethod ) )*
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( (LA9_0==RULE_ID||(LA9_0>=14 && LA9_0<=17)) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:643:1: (lv_methods_6_0= ruleMethod )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:643:1: (lv_methods_6_0= ruleMethod )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:644:3: lv_methods_6_0= ruleMethod
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getClassAccess().getMethodsMethodParserRuleCall_5_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleMethod_in_ruleClass1488);
            	    lv_methods_6_0=ruleMethod();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getClassRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"methods",
            	              		lv_methods_6_0, 
            	              		"Method");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop9;
                }
            } while (true);

            otherlv_7=(Token)match(input,21,FOLLOW_21_in_ruleClass1501); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_7, grammarAccess.getClassAccess().getRightCurlyBracketKeyword_6());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleClass"


    // $ANTLR start "entryRuleClassName"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:672:1: entryRuleClassName returns [String current=null] : iv_ruleClassName= ruleClassName EOF ;
    public final String entryRuleClassName() throws RecognitionException {
        String current = null;

        AntlrDatatypeRuleToken iv_ruleClassName = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:673:2: (iv_ruleClassName= ruleClassName EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:674:2: iv_ruleClassName= ruleClassName EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getClassNameRule()); 
            }
            pushFollow(FOLLOW_ruleClassName_in_entryRuleClassName1538);
            iv_ruleClassName=ruleClassName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleClassName.getText(); 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleClassName1549); if (state.failed) return current;

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
    // $ANTLR end "entryRuleClassName"


    // $ANTLR start "ruleClassName"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:681:1: ruleClassName returns [AntlrDatatypeRuleToken current=new AntlrDatatypeRuleToken()] : this_ID_0= RULE_ID ;
    public final AntlrDatatypeRuleToken ruleClassName() throws RecognitionException {
        AntlrDatatypeRuleToken current = new AntlrDatatypeRuleToken();

        Token this_ID_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:684:28: (this_ID_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:685:5: this_ID_0= RULE_ID
            {
            this_ID_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleClassName1588); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              		current.merge(this_ID_0);
                  
            }
            if ( state.backtracking==0 ) {
               
                  newLeafNode(this_ID_0, grammarAccess.getClassNameAccess().getIDTerminalRuleCall()); 
                  
            }

            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleClassName"


    // $ANTLR start "entryRuleFieldName"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:700:1: entryRuleFieldName returns [String current=null] : iv_ruleFieldName= ruleFieldName EOF ;
    public final String entryRuleFieldName() throws RecognitionException {
        String current = null;

        AntlrDatatypeRuleToken iv_ruleFieldName = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:701:2: (iv_ruleFieldName= ruleFieldName EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:702:2: iv_ruleFieldName= ruleFieldName EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getFieldNameRule()); 
            }
            pushFollow(FOLLOW_ruleFieldName_in_entryRuleFieldName1633);
            iv_ruleFieldName=ruleFieldName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleFieldName.getText(); 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleFieldName1644); if (state.failed) return current;

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
    // $ANTLR end "entryRuleFieldName"


    // $ANTLR start "ruleFieldName"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:709:1: ruleFieldName returns [AntlrDatatypeRuleToken current=new AntlrDatatypeRuleToken()] : this_ID_0= RULE_ID ;
    public final AntlrDatatypeRuleToken ruleFieldName() throws RecognitionException {
        AntlrDatatypeRuleToken current = new AntlrDatatypeRuleToken();

        Token this_ID_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:712:28: (this_ID_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:713:5: this_ID_0= RULE_ID
            {
            this_ID_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleFieldName1683); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              		current.merge(this_ID_0);
                  
            }
            if ( state.backtracking==0 ) {
               
                  newLeafNode(this_ID_0, grammarAccess.getFieldNameAccess().getIDTerminalRuleCall()); 
                  
            }

            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleFieldName"


    // $ANTLR start "entryRuleMethodName"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:728:1: entryRuleMethodName returns [String current=null] : iv_ruleMethodName= ruleMethodName EOF ;
    public final String entryRuleMethodName() throws RecognitionException {
        String current = null;

        AntlrDatatypeRuleToken iv_ruleMethodName = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:729:2: (iv_ruleMethodName= ruleMethodName EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:730:2: iv_ruleMethodName= ruleMethodName EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getMethodNameRule()); 
            }
            pushFollow(FOLLOW_ruleMethodName_in_entryRuleMethodName1728);
            iv_ruleMethodName=ruleMethodName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleMethodName.getText(); 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleMethodName1739); if (state.failed) return current;

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
    // $ANTLR end "entryRuleMethodName"


    // $ANTLR start "ruleMethodName"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:737:1: ruleMethodName returns [AntlrDatatypeRuleToken current=new AntlrDatatypeRuleToken()] : this_ID_0= RULE_ID ;
    public final AntlrDatatypeRuleToken ruleMethodName() throws RecognitionException {
        AntlrDatatypeRuleToken current = new AntlrDatatypeRuleToken();

        Token this_ID_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:740:28: (this_ID_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:741:5: this_ID_0= RULE_ID
            {
            this_ID_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleMethodName1778); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              		current.merge(this_ID_0);
                  
            }
            if ( state.backtracking==0 ) {
               
                  newLeafNode(this_ID_0, grammarAccess.getMethodNameAccess().getIDTerminalRuleCall()); 
                  
            }

            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleMethodName"


    // $ANTLR start "entryRuleField"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:758:1: entryRuleField returns [EObject current=null] : iv_ruleField= ruleField EOF ;
    public final EObject entryRuleField() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleField = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:759:2: (iv_ruleField= ruleField EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:760:2: iv_ruleField= ruleField EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getFieldRule()); 
            }
            pushFollow(FOLLOW_ruleField_in_entryRuleField1824);
            iv_ruleField=ruleField();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleField; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleField1834); if (state.failed) return current;

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
    // $ANTLR end "entryRuleField"


    // $ANTLR start "ruleField"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:767:1: ruleField returns [EObject current=null] : ( ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= ';' ) ;
    public final EObject ruleField() throws RecognitionException {
        EObject current = null;

        Token lv_name_1_0=null;
        Token otherlv_2=null;
        EObject lv_type_0_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:770:28: ( ( ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= ';' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:771:1: ( ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= ';' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:771:1: ( ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= ';' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:771:2: ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= ';'
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:771:2: ( (lv_type_0_0= ruleTypeForDeclaration ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:772:1: (lv_type_0_0= ruleTypeForDeclaration )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:772:1: (lv_type_0_0= ruleTypeForDeclaration )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:773:3: lv_type_0_0= ruleTypeForDeclaration
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getFieldAccess().getTypeTypeForDeclarationParserRuleCall_0_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleTypeForDeclaration_in_ruleField1880);
            lv_type_0_0=ruleTypeForDeclaration();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getFieldRule());
              	        }
                     		set(
                     			current, 
                     			"type",
                      		lv_type_0_0, 
                      		"TypeForDeclaration");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:789:2: ( (lv_name_1_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:790:1: (lv_name_1_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:790:1: (lv_name_1_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:791:3: lv_name_1_0= RULE_ID
            {
            lv_name_1_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleField1897); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_name_1_0, grammarAccess.getFieldAccess().getNameIDTerminalRuleCall_1_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getFieldRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"name",
                      		lv_name_1_0, 
                      		"ID");
              	    
            }

            }


            }

            otherlv_2=(Token)match(input,22,FOLLOW_22_in_ruleField1914); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getFieldAccess().getSemicolonKeyword_2());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleField"


    // $ANTLR start "entryRuleLocalVariableDeclaration"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:819:1: entryRuleLocalVariableDeclaration returns [EObject current=null] : iv_ruleLocalVariableDeclaration= ruleLocalVariableDeclaration EOF ;
    public final EObject entryRuleLocalVariableDeclaration() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleLocalVariableDeclaration = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:820:2: (iv_ruleLocalVariableDeclaration= ruleLocalVariableDeclaration EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:821:2: iv_ruleLocalVariableDeclaration= ruleLocalVariableDeclaration EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getLocalVariableDeclarationRule()); 
            }
            pushFollow(FOLLOW_ruleLocalVariableDeclaration_in_entryRuleLocalVariableDeclaration1950);
            iv_ruleLocalVariableDeclaration=ruleLocalVariableDeclaration();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleLocalVariableDeclaration; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleLocalVariableDeclaration1960); if (state.failed) return current;

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
    // $ANTLR end "entryRuleLocalVariableDeclaration"


    // $ANTLR start "ruleLocalVariableDeclaration"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:828:1: ruleLocalVariableDeclaration returns [EObject current=null] : ( ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= ';' ) ;
    public final EObject ruleLocalVariableDeclaration() throws RecognitionException {
        EObject current = null;

        Token lv_name_1_0=null;
        Token otherlv_2=null;
        EObject lv_type_0_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:831:28: ( ( ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= ';' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:832:1: ( ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= ';' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:832:1: ( ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= ';' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:832:2: ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= ';'
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:832:2: ( (lv_type_0_0= ruleTypeForDeclaration ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:833:1: (lv_type_0_0= ruleTypeForDeclaration )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:833:1: (lv_type_0_0= ruleTypeForDeclaration )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:834:3: lv_type_0_0= ruleTypeForDeclaration
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getLocalVariableDeclarationAccess().getTypeTypeForDeclarationParserRuleCall_0_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleTypeForDeclaration_in_ruleLocalVariableDeclaration2006);
            lv_type_0_0=ruleTypeForDeclaration();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getLocalVariableDeclarationRule());
              	        }
                     		set(
                     			current, 
                     			"type",
                      		lv_type_0_0, 
                      		"TypeForDeclaration");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:850:2: ( (lv_name_1_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:851:1: (lv_name_1_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:851:1: (lv_name_1_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:852:3: lv_name_1_0= RULE_ID
            {
            lv_name_1_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleLocalVariableDeclaration2023); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_name_1_0, grammarAccess.getLocalVariableDeclarationAccess().getNameIDTerminalRuleCall_1_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getLocalVariableDeclarationRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"name",
                      		lv_name_1_0, 
                      		"ID");
              	    
            }

            }


            }

            otherlv_2=(Token)match(input,22,FOLLOW_22_in_ruleLocalVariableDeclaration2040); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getLocalVariableDeclarationAccess().getSemicolonKeyword_2());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleLocalVariableDeclaration"


    // $ANTLR start "entryRuleParameter"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:880:1: entryRuleParameter returns [EObject current=null] : iv_ruleParameter= ruleParameter EOF ;
    public final EObject entryRuleParameter() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleParameter = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:881:2: (iv_ruleParameter= ruleParameter EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:882:2: iv_ruleParameter= ruleParameter EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getParameterRule()); 
            }
            pushFollow(FOLLOW_ruleParameter_in_entryRuleParameter2076);
            iv_ruleParameter=ruleParameter();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleParameter; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleParameter2086); if (state.failed) return current;

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
    // $ANTLR end "entryRuleParameter"


    // $ANTLR start "ruleParameter"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:889:1: ruleParameter returns [EObject current=null] : ( ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) ) ;
    public final EObject ruleParameter() throws RecognitionException {
        EObject current = null;

        Token lv_name_1_0=null;
        EObject lv_type_0_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:892:28: ( ( ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:893:1: ( ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:893:1: ( ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:893:2: ( (lv_type_0_0= ruleTypeForDeclaration ) ) ( (lv_name_1_0= RULE_ID ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:893:2: ( (lv_type_0_0= ruleTypeForDeclaration ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:894:1: (lv_type_0_0= ruleTypeForDeclaration )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:894:1: (lv_type_0_0= ruleTypeForDeclaration )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:895:3: lv_type_0_0= ruleTypeForDeclaration
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getParameterAccess().getTypeTypeForDeclarationParserRuleCall_0_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleTypeForDeclaration_in_ruleParameter2132);
            lv_type_0_0=ruleTypeForDeclaration();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getParameterRule());
              	        }
                     		set(
                     			current, 
                     			"type",
                      		lv_type_0_0, 
                      		"TypeForDeclaration");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:911:2: ( (lv_name_1_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:912:1: (lv_name_1_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:912:1: (lv_name_1_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:913:3: lv_name_1_0= RULE_ID
            {
            lv_name_1_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleParameter2149); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_name_1_0, grammarAccess.getParameterAccess().getNameIDTerminalRuleCall_1_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getParameterRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"name",
                      		lv_name_1_0, 
                      		"ID");
              	    
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleParameter"


    // $ANTLR start "entryRuleMethod"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:937:1: entryRuleMethod returns [EObject current=null] : iv_ruleMethod= ruleMethod EOF ;
    public final EObject entryRuleMethod() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMethod = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:938:2: (iv_ruleMethod= ruleMethod EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:939:2: iv_ruleMethod= ruleMethod EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getMethodRule()); 
            }
            pushFollow(FOLLOW_ruleMethod_in_entryRuleMethod2190);
            iv_ruleMethod=ruleMethod();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleMethod; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleMethod2200); if (state.failed) return current;

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
    // $ANTLR end "entryRuleMethod"


    // $ANTLR start "ruleMethod"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:946:1: ruleMethod returns [EObject current=null] : ( ( (lv_returntype_0_0= ruleTypeForMethod ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '(' ( ( (lv_params_3_0= ruleParameter ) ) (otherlv_4= ',' ( (lv_params_5_0= ruleParameter ) ) )* )? otherlv_6= ')' ( (lv_body_7_0= ruleStatementBlock ) )? ) ;
    public final EObject ruleMethod() throws RecognitionException {
        EObject current = null;

        Token lv_name_1_0=null;
        Token otherlv_2=null;
        Token otherlv_4=null;
        Token otherlv_6=null;
        EObject lv_returntype_0_0 = null;

        EObject lv_params_3_0 = null;

        EObject lv_params_5_0 = null;

        EObject lv_body_7_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:949:28: ( ( ( (lv_returntype_0_0= ruleTypeForMethod ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '(' ( ( (lv_params_3_0= ruleParameter ) ) (otherlv_4= ',' ( (lv_params_5_0= ruleParameter ) ) )* )? otherlv_6= ')' ( (lv_body_7_0= ruleStatementBlock ) )? ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:950:1: ( ( (lv_returntype_0_0= ruleTypeForMethod ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '(' ( ( (lv_params_3_0= ruleParameter ) ) (otherlv_4= ',' ( (lv_params_5_0= ruleParameter ) ) )* )? otherlv_6= ')' ( (lv_body_7_0= ruleStatementBlock ) )? )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:950:1: ( ( (lv_returntype_0_0= ruleTypeForMethod ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '(' ( ( (lv_params_3_0= ruleParameter ) ) (otherlv_4= ',' ( (lv_params_5_0= ruleParameter ) ) )* )? otherlv_6= ')' ( (lv_body_7_0= ruleStatementBlock ) )? )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:950:2: ( (lv_returntype_0_0= ruleTypeForMethod ) ) ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '(' ( ( (lv_params_3_0= ruleParameter ) ) (otherlv_4= ',' ( (lv_params_5_0= ruleParameter ) ) )* )? otherlv_6= ')' ( (lv_body_7_0= ruleStatementBlock ) )?
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:950:2: ( (lv_returntype_0_0= ruleTypeForMethod ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:951:1: (lv_returntype_0_0= ruleTypeForMethod )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:951:1: (lv_returntype_0_0= ruleTypeForMethod )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:952:3: lv_returntype_0_0= ruleTypeForMethod
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getMethodAccess().getReturntypeTypeForMethodParserRuleCall_0_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleTypeForMethod_in_ruleMethod2246);
            lv_returntype_0_0=ruleTypeForMethod();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getMethodRule());
              	        }
                     		set(
                     			current, 
                     			"returntype",
                      		lv_returntype_0_0, 
                      		"TypeForMethod");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:968:2: ( (lv_name_1_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:969:1: (lv_name_1_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:969:1: (lv_name_1_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:970:3: lv_name_1_0= RULE_ID
            {
            lv_name_1_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleMethod2263); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_name_1_0, grammarAccess.getMethodAccess().getNameIDTerminalRuleCall_1_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getMethodRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"name",
                      		lv_name_1_0, 
                      		"ID");
              	    
            }

            }


            }

            otherlv_2=(Token)match(input,23,FOLLOW_23_in_ruleMethod2280); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getMethodAccess().getLeftParenthesisKeyword_2());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:990:1: ( ( (lv_params_3_0= ruleParameter ) ) (otherlv_4= ',' ( (lv_params_5_0= ruleParameter ) ) )* )?
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==RULE_ID||(LA11_0>=15 && LA11_0<=17)) ) {
                alt11=1;
            }
            switch (alt11) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:990:2: ( (lv_params_3_0= ruleParameter ) ) (otherlv_4= ',' ( (lv_params_5_0= ruleParameter ) ) )*
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:990:2: ( (lv_params_3_0= ruleParameter ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:991:1: (lv_params_3_0= ruleParameter )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:991:1: (lv_params_3_0= ruleParameter )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:992:3: lv_params_3_0= ruleParameter
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getMethodAccess().getParamsParameterParserRuleCall_3_0_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_ruleParameter_in_ruleMethod2302);
                    lv_params_3_0=ruleParameter();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getMethodRule());
                      	        }
                             		add(
                             			current, 
                             			"params",
                              		lv_params_3_0, 
                              		"Parameter");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }

                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1008:2: (otherlv_4= ',' ( (lv_params_5_0= ruleParameter ) ) )*
                    loop10:
                    do {
                        int alt10=2;
                        int LA10_0 = input.LA(1);

                        if ( (LA10_0==24) ) {
                            alt10=1;
                        }


                        switch (alt10) {
                    	case 1 :
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1008:4: otherlv_4= ',' ( (lv_params_5_0= ruleParameter ) )
                    	    {
                    	    otherlv_4=(Token)match(input,24,FOLLOW_24_in_ruleMethod2315); if (state.failed) return current;
                    	    if ( state.backtracking==0 ) {

                    	          	newLeafNode(otherlv_4, grammarAccess.getMethodAccess().getCommaKeyword_3_1_0());
                    	          
                    	    }
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1012:1: ( (lv_params_5_0= ruleParameter ) )
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1013:1: (lv_params_5_0= ruleParameter )
                    	    {
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1013:1: (lv_params_5_0= ruleParameter )
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1014:3: lv_params_5_0= ruleParameter
                    	    {
                    	    if ( state.backtracking==0 ) {
                    	       
                    	      	        newCompositeNode(grammarAccess.getMethodAccess().getParamsParameterParserRuleCall_3_1_1_0()); 
                    	      	    
                    	    }
                    	    pushFollow(FOLLOW_ruleParameter_in_ruleMethod2336);
                    	    lv_params_5_0=ruleParameter();

                    	    state._fsp--;
                    	    if (state.failed) return current;
                    	    if ( state.backtracking==0 ) {

                    	      	        if (current==null) {
                    	      	            current = createModelElementForParent(grammarAccess.getMethodRule());
                    	      	        }
                    	             		add(
                    	             			current, 
                    	             			"params",
                    	              		lv_params_5_0, 
                    	              		"Parameter");
                    	      	        afterParserOrEnumRuleCall();
                    	      	    
                    	    }

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop10;
                        }
                    } while (true);


                    }
                    break;

            }

            otherlv_6=(Token)match(input,25,FOLLOW_25_in_ruleMethod2352); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_6, grammarAccess.getMethodAccess().getRightParenthesisKeyword_4());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1034:1: ( (lv_body_7_0= ruleStatementBlock ) )?
            int alt12=2;
            int LA12_0 = input.LA(1);

            if ( (LA12_0==20) ) {
                alt12=1;
            }
            switch (alt12) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1035:1: (lv_body_7_0= ruleStatementBlock )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1035:1: (lv_body_7_0= ruleStatementBlock )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1036:3: lv_body_7_0= ruleStatementBlock
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getMethodAccess().getBodyStatementBlockParserRuleCall_5_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_ruleStatementBlock_in_ruleMethod2373);
                    lv_body_7_0=ruleStatementBlock();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getMethodRule());
                      	        }
                             		set(
                             			current, 
                             			"body",
                              		lv_body_7_0, 
                              		"StatementBlock");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }
                    break;

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleMethod"


    // $ANTLR start "entryRuleStatementBlock"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1060:1: entryRuleStatementBlock returns [EObject current=null] : iv_ruleStatementBlock= ruleStatementBlock EOF ;
    public final EObject entryRuleStatementBlock() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleStatementBlock = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1061:2: (iv_ruleStatementBlock= ruleStatementBlock EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1062:2: iv_ruleStatementBlock= ruleStatementBlock EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getStatementBlockRule()); 
            }
            pushFollow(FOLLOW_ruleStatementBlock_in_entryRuleStatementBlock2410);
            iv_ruleStatementBlock=ruleStatementBlock();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleStatementBlock; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleStatementBlock2420); if (state.failed) return current;

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
    // $ANTLR end "entryRuleStatementBlock"


    // $ANTLR start "ruleStatementBlock"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1069:1: ruleStatementBlock returns [EObject current=null] : ( () otherlv_1= '{' ( (lv_localvariables_2_0= ruleLocalVariableDeclaration ) )* ( (lv_statements_3_0= ruleStatement ) )* ( (lv_statements_4_0= ruleReturnStatement ) )? otherlv_5= '}' ) ;
    public final EObject ruleStatementBlock() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        Token otherlv_5=null;
        EObject lv_localvariables_2_0 = null;

        EObject lv_statements_3_0 = null;

        EObject lv_statements_4_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1072:28: ( ( () otherlv_1= '{' ( (lv_localvariables_2_0= ruleLocalVariableDeclaration ) )* ( (lv_statements_3_0= ruleStatement ) )* ( (lv_statements_4_0= ruleReturnStatement ) )? otherlv_5= '}' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1073:1: ( () otherlv_1= '{' ( (lv_localvariables_2_0= ruleLocalVariableDeclaration ) )* ( (lv_statements_3_0= ruleStatement ) )* ( (lv_statements_4_0= ruleReturnStatement ) )? otherlv_5= '}' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1073:1: ( () otherlv_1= '{' ( (lv_localvariables_2_0= ruleLocalVariableDeclaration ) )* ( (lv_statements_3_0= ruleStatement ) )* ( (lv_statements_4_0= ruleReturnStatement ) )? otherlv_5= '}' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1073:2: () otherlv_1= '{' ( (lv_localvariables_2_0= ruleLocalVariableDeclaration ) )* ( (lv_statements_3_0= ruleStatement ) )* ( (lv_statements_4_0= ruleReturnStatement ) )? otherlv_5= '}'
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1073:2: ()
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1074:2: 
            {
            if ( state.backtracking==0 ) {
               
              	  /* */ 
              	
            }
            if ( state.backtracking==0 ) {

                      current = forceCreateModelElement(
                          grammarAccess.getStatementBlockAccess().getStatementBlockAction_0(),
                          current);
                  
            }

            }

            otherlv_1=(Token)match(input,20,FOLLOW_20_in_ruleStatementBlock2469); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_1, grammarAccess.getStatementBlockAccess().getLeftCurlyBracketKeyword_1());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1086:1: ( (lv_localvariables_2_0= ruleLocalVariableDeclaration ) )*
            loop13:
            do {
                int alt13=2;
                int LA13_0 = input.LA(1);

                if ( (LA13_0==RULE_ID) ) {
                    int LA13_2 = input.LA(2);

                    if ( (LA13_2==RULE_ID) ) {
                        alt13=1;
                    }


                }
                else if ( ((LA13_0>=15 && LA13_0<=17)) ) {
                    alt13=1;
                }


                switch (alt13) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1087:1: (lv_localvariables_2_0= ruleLocalVariableDeclaration )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1087:1: (lv_localvariables_2_0= ruleLocalVariableDeclaration )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1088:3: lv_localvariables_2_0= ruleLocalVariableDeclaration
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getStatementBlockAccess().getLocalvariablesLocalVariableDeclarationParserRuleCall_2_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleLocalVariableDeclaration_in_ruleStatementBlock2490);
            	    lv_localvariables_2_0=ruleLocalVariableDeclaration();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getStatementBlockRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"localvariables",
            	              		lv_localvariables_2_0, 
            	              		"LocalVariableDeclaration");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop13;
                }
            } while (true);

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1104:3: ( (lv_statements_3_0= ruleStatement ) )*
            loop14:
            do {
                int alt14=2;
                int LA14_0 = input.LA(1);

                if ( ((LA14_0>=RULE_INT && LA14_0<=RULE_STRING)||LA14_0==23||LA14_0==28||LA14_0==31||LA14_0==40||(LA14_0>=42 && LA14_0<=47)) ) {
                    alt14=1;
                }


                switch (alt14) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1105:1: (lv_statements_3_0= ruleStatement )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1105:1: (lv_statements_3_0= ruleStatement )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1106:3: lv_statements_3_0= ruleStatement
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getStatementBlockAccess().getStatementsStatementParserRuleCall_3_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleStatement_in_ruleStatementBlock2512);
            	    lv_statements_3_0=ruleStatement();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getStatementBlockRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"statements",
            	              		lv_statements_3_0, 
            	              		"Statement");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop14;
                }
            } while (true);

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1122:3: ( (lv_statements_4_0= ruleReturnStatement ) )?
            int alt15=2;
            int LA15_0 = input.LA(1);

            if ( (LA15_0==26) ) {
                alt15=1;
            }
            switch (alt15) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1123:1: (lv_statements_4_0= ruleReturnStatement )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1123:1: (lv_statements_4_0= ruleReturnStatement )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1124:3: lv_statements_4_0= ruleReturnStatement
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getStatementBlockAccess().getStatementsReturnStatementParserRuleCall_4_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_ruleReturnStatement_in_ruleStatementBlock2534);
                    lv_statements_4_0=ruleReturnStatement();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getStatementBlockRule());
                      	        }
                             		add(
                             			current, 
                             			"statements",
                              		lv_statements_4_0, 
                              		"ReturnStatement");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }
                    break;

            }

            otherlv_5=(Token)match(input,21,FOLLOW_21_in_ruleStatementBlock2547); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_5, grammarAccess.getStatementBlockAccess().getRightCurlyBracketKeyword_5());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleStatementBlock"


    // $ANTLR start "entryRuleReturnStatement"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1152:1: entryRuleReturnStatement returns [EObject current=null] : iv_ruleReturnStatement= ruleReturnStatement EOF ;
    public final EObject entryRuleReturnStatement() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleReturnStatement = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1153:2: (iv_ruleReturnStatement= ruleReturnStatement EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1154:2: iv_ruleReturnStatement= ruleReturnStatement EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getReturnStatementRule()); 
            }
            pushFollow(FOLLOW_ruleReturnStatement_in_entryRuleReturnStatement2583);
            iv_ruleReturnStatement=ruleReturnStatement();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleReturnStatement; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleReturnStatement2593); if (state.failed) return current;

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
    // $ANTLR end "entryRuleReturnStatement"


    // $ANTLR start "ruleReturnStatement"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1161:1: ruleReturnStatement returns [EObject current=null] : ( () otherlv_1= 'return' ( (lv_expression_2_0= ruleExpression ) )? otherlv_3= ';' ) ;
    public final EObject ruleReturnStatement() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        Token otherlv_3=null;
        EObject lv_expression_2_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1164:28: ( ( () otherlv_1= 'return' ( (lv_expression_2_0= ruleExpression ) )? otherlv_3= ';' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1165:1: ( () otherlv_1= 'return' ( (lv_expression_2_0= ruleExpression ) )? otherlv_3= ';' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1165:1: ( () otherlv_1= 'return' ( (lv_expression_2_0= ruleExpression ) )? otherlv_3= ';' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1165:2: () otherlv_1= 'return' ( (lv_expression_2_0= ruleExpression ) )? otherlv_3= ';'
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1165:2: ()
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1166:2: 
            {
            if ( state.backtracking==0 ) {
               
              	  /* */ 
              	
            }
            if ( state.backtracking==0 ) {

                      current = forceCreateModelElement(
                          grammarAccess.getReturnStatementAccess().getReturnStatementAction_0(),
                          current);
                  
            }

            }

            otherlv_1=(Token)match(input,26,FOLLOW_26_in_ruleReturnStatement2642); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_1, grammarAccess.getReturnStatementAccess().getReturnKeyword_1());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1178:1: ( (lv_expression_2_0= ruleExpression ) )?
            int alt16=2;
            int LA16_0 = input.LA(1);

            if ( ((LA16_0>=RULE_INT && LA16_0<=RULE_ID)||LA16_0==RULE_STRING||LA16_0==23||LA16_0==31||LA16_0==40||(LA16_0>=42 && LA16_0<=47)) ) {
                alt16=1;
            }
            switch (alt16) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1179:1: (lv_expression_2_0= ruleExpression )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1179:1: (lv_expression_2_0= ruleExpression )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1180:3: lv_expression_2_0= ruleExpression
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getReturnStatementAccess().getExpressionExpressionParserRuleCall_2_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_ruleExpression_in_ruleReturnStatement2663);
                    lv_expression_2_0=ruleExpression();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getReturnStatementRule());
                      	        }
                             		set(
                             			current, 
                             			"expression",
                              		lv_expression_2_0, 
                              		"Expression");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }
                    break;

            }

            otherlv_3=(Token)match(input,22,FOLLOW_22_in_ruleReturnStatement2676); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_3, grammarAccess.getReturnStatementAccess().getSemicolonKeyword_3());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleReturnStatement"


    // $ANTLR start "entryRuleStatement"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1208:1: entryRuleStatement returns [EObject current=null] : iv_ruleStatement= ruleStatement EOF ;
    public final EObject entryRuleStatement() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleStatement = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1209:2: (iv_ruleStatement= ruleStatement EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1210:2: iv_ruleStatement= ruleStatement EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getStatementRule()); 
            }
            pushFollow(FOLLOW_ruleStatement_in_entryRuleStatement2712);
            iv_ruleStatement=ruleStatement();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleStatement; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleStatement2722); if (state.failed) return current;

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
    // $ANTLR end "entryRuleStatement"


    // $ANTLR start "ruleStatement"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1217:1: ruleStatement returns [EObject current=null] : (this_ExpressionStatement_0= ruleExpressionStatement | this_Assignment_1= ruleAssignment | this_IfStatement_2= ruleIfStatement | ( () ( (lv_verbatim_4_0= RULE_JAVAVERBATIM ) ) ) ) ;
    public final EObject ruleStatement() throws RecognitionException {
        EObject current = null;

        Token lv_verbatim_4_0=null;
        EObject this_ExpressionStatement_0 = null;

        EObject this_Assignment_1 = null;

        EObject this_IfStatement_2 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1220:28: ( (this_ExpressionStatement_0= ruleExpressionStatement | this_Assignment_1= ruleAssignment | this_IfStatement_2= ruleIfStatement | ( () ( (lv_verbatim_4_0= RULE_JAVAVERBATIM ) ) ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1221:1: (this_ExpressionStatement_0= ruleExpressionStatement | this_Assignment_1= ruleAssignment | this_IfStatement_2= ruleIfStatement | ( () ( (lv_verbatim_4_0= RULE_JAVAVERBATIM ) ) ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1221:1: (this_ExpressionStatement_0= ruleExpressionStatement | this_Assignment_1= ruleAssignment | this_IfStatement_2= ruleIfStatement | ( () ( (lv_verbatim_4_0= RULE_JAVAVERBATIM ) ) ) )
            int alt17=4;
            alt17 = dfa17.predict(input);
            switch (alt17) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1222:2: this_ExpressionStatement_0= ruleExpressionStatement
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getStatementAccess().getExpressionStatementParserRuleCall_0()); 
                          
                    }
                    pushFollow(FOLLOW_ruleExpressionStatement_in_ruleStatement2772);
                    this_ExpressionStatement_0=ruleExpressionStatement();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_ExpressionStatement_0; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1235:2: this_Assignment_1= ruleAssignment
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getStatementAccess().getAssignmentParserRuleCall_1()); 
                          
                    }
                    pushFollow(FOLLOW_ruleAssignment_in_ruleStatement2802);
                    this_Assignment_1=ruleAssignment();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_Assignment_1; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 3 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1248:2: this_IfStatement_2= ruleIfStatement
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getStatementAccess().getIfStatementParserRuleCall_2()); 
                          
                    }
                    pushFollow(FOLLOW_ruleIfStatement_in_ruleStatement2832);
                    this_IfStatement_2=ruleIfStatement();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_IfStatement_2; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 4 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1260:6: ( () ( (lv_verbatim_4_0= RULE_JAVAVERBATIM ) ) )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1260:6: ( () ( (lv_verbatim_4_0= RULE_JAVAVERBATIM ) ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1260:7: () ( (lv_verbatim_4_0= RULE_JAVAVERBATIM ) )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1260:7: ()
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1261:2: 
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {

                              current = forceCreateModelElement(
                                  grammarAccess.getStatementAccess().getJavaVerbatimAction_3_0(),
                                  current);
                          
                    }

                    }

                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1269:2: ( (lv_verbatim_4_0= RULE_JAVAVERBATIM ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1270:1: (lv_verbatim_4_0= RULE_JAVAVERBATIM )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1270:1: (lv_verbatim_4_0= RULE_JAVAVERBATIM )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1271:3: lv_verbatim_4_0= RULE_JAVAVERBATIM
                    {
                    lv_verbatim_4_0=(Token)match(input,RULE_JAVAVERBATIM,FOLLOW_RULE_JAVAVERBATIM_in_ruleStatement2867); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      			newLeafNode(lv_verbatim_4_0, grammarAccess.getStatementAccess().getVerbatimJAVAVERBATIMTerminalRuleCall_3_1_0()); 
                      		
                    }
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElement(grammarAccess.getStatementRule());
                      	        }
                             		setWithLastConsumed(
                             			current, 
                             			"verbatim",
                              		lv_verbatim_4_0, 
                              		"JAVAVERBATIM");
                      	    
                    }

                    }


                    }


                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleStatement"


    // $ANTLR start "entryRuleExpressionStatement"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1295:1: entryRuleExpressionStatement returns [EObject current=null] : iv_ruleExpressionStatement= ruleExpressionStatement EOF ;
    public final EObject entryRuleExpressionStatement() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleExpressionStatement = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1296:2: (iv_ruleExpressionStatement= ruleExpressionStatement EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1297:2: iv_ruleExpressionStatement= ruleExpressionStatement EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getExpressionStatementRule()); 
            }
            pushFollow(FOLLOW_ruleExpressionStatement_in_entryRuleExpressionStatement2909);
            iv_ruleExpressionStatement=ruleExpressionStatement();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleExpressionStatement; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleExpressionStatement2919); if (state.failed) return current;

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
    // $ANTLR end "entryRuleExpressionStatement"


    // $ANTLR start "ruleExpressionStatement"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1304:1: ruleExpressionStatement returns [EObject current=null] : ( ( (lv_expression_0_0= ruleExpression ) ) otherlv_1= ';' ) ;
    public final EObject ruleExpressionStatement() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        EObject lv_expression_0_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1307:28: ( ( ( (lv_expression_0_0= ruleExpression ) ) otherlv_1= ';' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1308:1: ( ( (lv_expression_0_0= ruleExpression ) ) otherlv_1= ';' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1308:1: ( ( (lv_expression_0_0= ruleExpression ) ) otherlv_1= ';' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1308:2: ( (lv_expression_0_0= ruleExpression ) ) otherlv_1= ';'
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1308:2: ( (lv_expression_0_0= ruleExpression ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1309:1: (lv_expression_0_0= ruleExpression )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1309:1: (lv_expression_0_0= ruleExpression )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1310:3: lv_expression_0_0= ruleExpression
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getExpressionStatementAccess().getExpressionExpressionParserRuleCall_0_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleExpression_in_ruleExpressionStatement2965);
            lv_expression_0_0=ruleExpression();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getExpressionStatementRule());
              	        }
                     		set(
                     			current, 
                     			"expression",
                      		lv_expression_0_0, 
                      		"Expression");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            otherlv_1=(Token)match(input,22,FOLLOW_22_in_ruleExpressionStatement2977); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_1, grammarAccess.getExpressionStatementAccess().getSemicolonKeyword_1());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleExpressionStatement"


    // $ANTLR start "entryRuleAssignment"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1338:1: entryRuleAssignment returns [EObject current=null] : iv_ruleAssignment= ruleAssignment EOF ;
    public final EObject entryRuleAssignment() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAssignment = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1339:2: (iv_ruleAssignment= ruleAssignment EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1340:2: iv_ruleAssignment= ruleAssignment EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAssignmentRule()); 
            }
            pushFollow(FOLLOW_ruleAssignment_in_entryRuleAssignment3013);
            iv_ruleAssignment=ruleAssignment();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAssignment; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleAssignment3023); if (state.failed) return current;

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
    // $ANTLR end "entryRuleAssignment"


    // $ANTLR start "ruleAssignment"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1347:1: ruleAssignment returns [EObject current=null] : ( ( (lv_left_0_0= ruleExpression ) ) otherlv_1= '=' ( (lv_right_2_0= ruleExpression ) ) otherlv_3= ';' ) ;
    public final EObject ruleAssignment() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        Token otherlv_3=null;
        EObject lv_left_0_0 = null;

        EObject lv_right_2_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1350:28: ( ( ( (lv_left_0_0= ruleExpression ) ) otherlv_1= '=' ( (lv_right_2_0= ruleExpression ) ) otherlv_3= ';' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1351:1: ( ( (lv_left_0_0= ruleExpression ) ) otherlv_1= '=' ( (lv_right_2_0= ruleExpression ) ) otherlv_3= ';' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1351:1: ( ( (lv_left_0_0= ruleExpression ) ) otherlv_1= '=' ( (lv_right_2_0= ruleExpression ) ) otherlv_3= ';' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1351:2: ( (lv_left_0_0= ruleExpression ) ) otherlv_1= '=' ( (lv_right_2_0= ruleExpression ) ) otherlv_3= ';'
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1351:2: ( (lv_left_0_0= ruleExpression ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1352:1: (lv_left_0_0= ruleExpression )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1352:1: (lv_left_0_0= ruleExpression )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1353:3: lv_left_0_0= ruleExpression
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getAssignmentAccess().getLeftExpressionParserRuleCall_0_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleExpression_in_ruleAssignment3069);
            lv_left_0_0=ruleExpression();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getAssignmentRule());
              	        }
                     		set(
                     			current, 
                     			"left",
                      		lv_left_0_0, 
                      		"Expression");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            otherlv_1=(Token)match(input,27,FOLLOW_27_in_ruleAssignment3081); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_1, grammarAccess.getAssignmentAccess().getEqualsSignKeyword_1());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1373:1: ( (lv_right_2_0= ruleExpression ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1374:1: (lv_right_2_0= ruleExpression )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1374:1: (lv_right_2_0= ruleExpression )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1375:3: lv_right_2_0= ruleExpression
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getAssignmentAccess().getRightExpressionParserRuleCall_2_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleExpression_in_ruleAssignment3102);
            lv_right_2_0=ruleExpression();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getAssignmentRule());
              	        }
                     		set(
                     			current, 
                     			"right",
                      		lv_right_2_0, 
                      		"Expression");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            otherlv_3=(Token)match(input,22,FOLLOW_22_in_ruleAssignment3114); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_3, grammarAccess.getAssignmentAccess().getSemicolonKeyword_3());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleAssignment"


    // $ANTLR start "entryRuleIfStatement"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1403:1: entryRuleIfStatement returns [EObject current=null] : iv_ruleIfStatement= ruleIfStatement EOF ;
    public final EObject entryRuleIfStatement() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleIfStatement = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1404:2: (iv_ruleIfStatement= ruleIfStatement EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1405:2: iv_ruleIfStatement= ruleIfStatement EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getIfStatementRule()); 
            }
            pushFollow(FOLLOW_ruleIfStatement_in_entryRuleIfStatement3150);
            iv_ruleIfStatement=ruleIfStatement();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleIfStatement; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleIfStatement3160); if (state.failed) return current;

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
    // $ANTLR end "entryRuleIfStatement"


    // $ANTLR start "ruleIfStatement"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1412:1: ruleIfStatement returns [EObject current=null] : ( () otherlv_1= 'if' otherlv_2= '(' ( (lv_expression_3_0= ruleExpression ) ) otherlv_4= ')' ( (lv_thenBlock_5_0= ruleStatementBlock ) ) (otherlv_6= 'else' ( (lv_elseBlock_7_0= ruleStatementBlock ) ) )? ) ;
    public final EObject ruleIfStatement() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        Token otherlv_2=null;
        Token otherlv_4=null;
        Token otherlv_6=null;
        EObject lv_expression_3_0 = null;

        EObject lv_thenBlock_5_0 = null;

        EObject lv_elseBlock_7_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1415:28: ( ( () otherlv_1= 'if' otherlv_2= '(' ( (lv_expression_3_0= ruleExpression ) ) otherlv_4= ')' ( (lv_thenBlock_5_0= ruleStatementBlock ) ) (otherlv_6= 'else' ( (lv_elseBlock_7_0= ruleStatementBlock ) ) )? ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1416:1: ( () otherlv_1= 'if' otherlv_2= '(' ( (lv_expression_3_0= ruleExpression ) ) otherlv_4= ')' ( (lv_thenBlock_5_0= ruleStatementBlock ) ) (otherlv_6= 'else' ( (lv_elseBlock_7_0= ruleStatementBlock ) ) )? )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1416:1: ( () otherlv_1= 'if' otherlv_2= '(' ( (lv_expression_3_0= ruleExpression ) ) otherlv_4= ')' ( (lv_thenBlock_5_0= ruleStatementBlock ) ) (otherlv_6= 'else' ( (lv_elseBlock_7_0= ruleStatementBlock ) ) )? )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1416:2: () otherlv_1= 'if' otherlv_2= '(' ( (lv_expression_3_0= ruleExpression ) ) otherlv_4= ')' ( (lv_thenBlock_5_0= ruleStatementBlock ) ) (otherlv_6= 'else' ( (lv_elseBlock_7_0= ruleStatementBlock ) ) )?
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1416:2: ()
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1417:2: 
            {
            if ( state.backtracking==0 ) {
               
              	  /* */ 
              	
            }
            if ( state.backtracking==0 ) {

                      current = forceCreateModelElement(
                          grammarAccess.getIfStatementAccess().getIfStatementAction_0(),
                          current);
                  
            }

            }

            otherlv_1=(Token)match(input,28,FOLLOW_28_in_ruleIfStatement3209); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_1, grammarAccess.getIfStatementAccess().getIfKeyword_1());
                  
            }
            otherlv_2=(Token)match(input,23,FOLLOW_23_in_ruleIfStatement3221); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getIfStatementAccess().getLeftParenthesisKeyword_2());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1433:1: ( (lv_expression_3_0= ruleExpression ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1434:1: (lv_expression_3_0= ruleExpression )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1434:1: (lv_expression_3_0= ruleExpression )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1435:3: lv_expression_3_0= ruleExpression
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getIfStatementAccess().getExpressionExpressionParserRuleCall_3_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleExpression_in_ruleIfStatement3242);
            lv_expression_3_0=ruleExpression();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getIfStatementRule());
              	        }
                     		set(
                     			current, 
                     			"expression",
                      		lv_expression_3_0, 
                      		"Expression");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            otherlv_4=(Token)match(input,25,FOLLOW_25_in_ruleIfStatement3254); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_4, grammarAccess.getIfStatementAccess().getRightParenthesisKeyword_4());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1455:1: ( (lv_thenBlock_5_0= ruleStatementBlock ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1456:1: (lv_thenBlock_5_0= ruleStatementBlock )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1456:1: (lv_thenBlock_5_0= ruleStatementBlock )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1457:3: lv_thenBlock_5_0= ruleStatementBlock
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getIfStatementAccess().getThenBlockStatementBlockParserRuleCall_5_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleStatementBlock_in_ruleIfStatement3275);
            lv_thenBlock_5_0=ruleStatementBlock();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getIfStatementRule());
              	        }
                     		set(
                     			current, 
                     			"thenBlock",
                      		lv_thenBlock_5_0, 
                      		"StatementBlock");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1473:2: (otherlv_6= 'else' ( (lv_elseBlock_7_0= ruleStatementBlock ) ) )?
            int alt18=2;
            int LA18_0 = input.LA(1);

            if ( (LA18_0==29) ) {
                alt18=1;
            }
            switch (alt18) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1473:4: otherlv_6= 'else' ( (lv_elseBlock_7_0= ruleStatementBlock ) )
                    {
                    otherlv_6=(Token)match(input,29,FOLLOW_29_in_ruleIfStatement3288); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                          	newLeafNode(otherlv_6, grammarAccess.getIfStatementAccess().getElseKeyword_6_0());
                          
                    }
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1477:1: ( (lv_elseBlock_7_0= ruleStatementBlock ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1478:1: (lv_elseBlock_7_0= ruleStatementBlock )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1478:1: (lv_elseBlock_7_0= ruleStatementBlock )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1479:3: lv_elseBlock_7_0= ruleStatementBlock
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getIfStatementAccess().getElseBlockStatementBlockParserRuleCall_6_1_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_ruleStatementBlock_in_ruleIfStatement3309);
                    lv_elseBlock_7_0=ruleStatementBlock();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getIfStatementRule());
                      	        }
                             		set(
                             			current, 
                             			"elseBlock",
                              		lv_elseBlock_7_0, 
                              		"StatementBlock");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }


                    }
                    break;

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleIfStatement"


    // $ANTLR start "entryRuleExpression"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1503:1: entryRuleExpression returns [EObject current=null] : iv_ruleExpression= ruleExpression EOF ;
    public final EObject entryRuleExpression() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleExpression = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1504:2: (iv_ruleExpression= ruleExpression EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1505:2: iv_ruleExpression= ruleExpression EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getExpressionRule()); 
            }
            pushFollow(FOLLOW_ruleExpression_in_entryRuleExpression3347);
            iv_ruleExpression=ruleExpression();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleExpression; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleExpression3357); if (state.failed) return current;

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
    // $ANTLR end "entryRuleExpression"


    // $ANTLR start "ruleExpression"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1512:1: ruleExpression returns [EObject current=null] : this_Addition_0= ruleAddition ;
    public final EObject ruleExpression() throws RecognitionException {
        EObject current = null;

        EObject this_Addition_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1515:28: (this_Addition_0= ruleAddition )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1517:2: this_Addition_0= ruleAddition
            {
            if ( state.backtracking==0 ) {
               
              	  /* */ 
              	
            }
            if ( state.backtracking==0 ) {
               
                      newCompositeNode(grammarAccess.getExpressionAccess().getAdditionParserRuleCall()); 
                  
            }
            pushFollow(FOLLOW_ruleAddition_in_ruleExpression3406);
            this_Addition_0=ruleAddition();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               
                      current = this_Addition_0; 
                      afterParserOrEnumRuleCall();
                  
            }

            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleExpression"


    // $ANTLR start "entryRuleAddition"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1536:1: entryRuleAddition returns [EObject current=null] : iv_ruleAddition= ruleAddition EOF ;
    public final EObject entryRuleAddition() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAddition = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1537:2: (iv_ruleAddition= ruleAddition EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1538:2: iv_ruleAddition= ruleAddition EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAdditionRule()); 
            }
            pushFollow(FOLLOW_ruleAddition_in_entryRuleAddition3440);
            iv_ruleAddition=ruleAddition();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAddition; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleAddition3450); if (state.failed) return current;

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
    // $ANTLR end "entryRuleAddition"


    // $ANTLR start "ruleAddition"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1545:1: ruleAddition returns [EObject current=null] : (this_Multiplication_0= ruleMultiplication ( ( ( () otherlv_2= '+' ) | ( () otherlv_4= '-' ) ) ( (lv_right_5_0= ruleMultiplication ) ) )* ) ;
    public final EObject ruleAddition() throws RecognitionException {
        EObject current = null;

        Token otherlv_2=null;
        Token otherlv_4=null;
        EObject this_Multiplication_0 = null;

        EObject lv_right_5_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1548:28: ( (this_Multiplication_0= ruleMultiplication ( ( ( () otherlv_2= '+' ) | ( () otherlv_4= '-' ) ) ( (lv_right_5_0= ruleMultiplication ) ) )* ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1549:1: (this_Multiplication_0= ruleMultiplication ( ( ( () otherlv_2= '+' ) | ( () otherlv_4= '-' ) ) ( (lv_right_5_0= ruleMultiplication ) ) )* )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1549:1: (this_Multiplication_0= ruleMultiplication ( ( ( () otherlv_2= '+' ) | ( () otherlv_4= '-' ) ) ( (lv_right_5_0= ruleMultiplication ) ) )* )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1550:2: this_Multiplication_0= ruleMultiplication ( ( ( () otherlv_2= '+' ) | ( () otherlv_4= '-' ) ) ( (lv_right_5_0= ruleMultiplication ) ) )*
            {
            if ( state.backtracking==0 ) {
               
              	  /* */ 
              	
            }
            if ( state.backtracking==0 ) {
               
                      newCompositeNode(grammarAccess.getAdditionAccess().getMultiplicationParserRuleCall_0()); 
                  
            }
            pushFollow(FOLLOW_ruleMultiplication_in_ruleAddition3500);
            this_Multiplication_0=ruleMultiplication();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               
                      current = this_Multiplication_0; 
                      afterParserOrEnumRuleCall();
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1561:1: ( ( ( () otherlv_2= '+' ) | ( () otherlv_4= '-' ) ) ( (lv_right_5_0= ruleMultiplication ) ) )*
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( ((LA20_0>=30 && LA20_0<=31)) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1561:2: ( ( () otherlv_2= '+' ) | ( () otherlv_4= '-' ) ) ( (lv_right_5_0= ruleMultiplication ) )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1561:2: ( ( () otherlv_2= '+' ) | ( () otherlv_4= '-' ) )
            	    int alt19=2;
            	    int LA19_0 = input.LA(1);

            	    if ( (LA19_0==30) ) {
            	        alt19=1;
            	    }
            	    else if ( (LA19_0==31) ) {
            	        alt19=2;
            	    }
            	    else {
            	        if (state.backtracking>0) {state.failed=true; return current;}
            	        NoViableAltException nvae =
            	            new NoViableAltException("", 19, 0, input);

            	        throw nvae;
            	    }
            	    switch (alt19) {
            	        case 1 :
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1561:3: ( () otherlv_2= '+' )
            	            {
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1561:3: ( () otherlv_2= '+' )
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1561:4: () otherlv_2= '+'
            	            {
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1561:4: ()
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1562:2: 
            	            {
            	            if ( state.backtracking==0 ) {
            	               
            	              	  /* */ 
            	              	
            	            }
            	            if ( state.backtracking==0 ) {

            	                      current = forceCreateModelElementAndSet(
            	                          grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0(),
            	                          current);
            	                  
            	            }

            	            }

            	            otherlv_2=(Token)match(input,30,FOLLOW_30_in_ruleAddition3526); if (state.failed) return current;
            	            if ( state.backtracking==0 ) {

            	                  	newLeafNode(otherlv_2, grammarAccess.getAdditionAccess().getPlusSignKeyword_1_0_0_1());
            	                  
            	            }

            	            }


            	            }
            	            break;
            	        case 2 :
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1575:6: ( () otherlv_4= '-' )
            	            {
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1575:6: ( () otherlv_4= '-' )
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1575:7: () otherlv_4= '-'
            	            {
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1575:7: ()
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1576:2: 
            	            {
            	            if ( state.backtracking==0 ) {
            	               
            	              	  /* */ 
            	              	
            	            }
            	            if ( state.backtracking==0 ) {

            	                      current = forceCreateModelElementAndSet(
            	                          grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0(),
            	                          current);
            	                  
            	            }

            	            }

            	            otherlv_4=(Token)match(input,31,FOLLOW_31_in_ruleAddition3558); if (state.failed) return current;
            	            if ( state.backtracking==0 ) {

            	                  	newLeafNode(otherlv_4, grammarAccess.getAdditionAccess().getHyphenMinusKeyword_1_0_1_1());
            	                  
            	            }

            	            }


            	            }
            	            break;

            	    }

            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1588:3: ( (lv_right_5_0= ruleMultiplication ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1589:1: (lv_right_5_0= ruleMultiplication )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1589:1: (lv_right_5_0= ruleMultiplication )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1590:3: lv_right_5_0= ruleMultiplication
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getAdditionAccess().getRightMultiplicationParserRuleCall_1_1_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleMultiplication_in_ruleAddition3581);
            	    lv_right_5_0=ruleMultiplication();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getAdditionRule());
            	      	        }
            	             		set(
            	             			current, 
            	             			"right",
            	              		lv_right_5_0, 
            	              		"Multiplication");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop20;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleAddition"


    // $ANTLR start "entryRuleMultiplication"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1614:1: entryRuleMultiplication returns [EObject current=null] : iv_ruleMultiplication= ruleMultiplication EOF ;
    public final EObject entryRuleMultiplication() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMultiplication = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1615:2: (iv_ruleMultiplication= ruleMultiplication EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1616:2: iv_ruleMultiplication= ruleMultiplication EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getMultiplicationRule()); 
            }
            pushFollow(FOLLOW_ruleMultiplication_in_entryRuleMultiplication3619);
            iv_ruleMultiplication=ruleMultiplication();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleMultiplication; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleMultiplication3629); if (state.failed) return current;

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
    // $ANTLR end "entryRuleMultiplication"


    // $ANTLR start "ruleMultiplication"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1623:1: ruleMultiplication returns [EObject current=null] : (this_Comparison_0= ruleComparison ( () ( ( (lv_op_2_1= '*' | lv_op_2_2= '/' ) ) ) ( (lv_right_3_0= ruleComparison ) ) )* ) ;
    public final EObject ruleMultiplication() throws RecognitionException {
        EObject current = null;

        Token lv_op_2_1=null;
        Token lv_op_2_2=null;
        EObject this_Comparison_0 = null;

        EObject lv_right_3_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1626:28: ( (this_Comparison_0= ruleComparison ( () ( ( (lv_op_2_1= '*' | lv_op_2_2= '/' ) ) ) ( (lv_right_3_0= ruleComparison ) ) )* ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1627:1: (this_Comparison_0= ruleComparison ( () ( ( (lv_op_2_1= '*' | lv_op_2_2= '/' ) ) ) ( (lv_right_3_0= ruleComparison ) ) )* )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1627:1: (this_Comparison_0= ruleComparison ( () ( ( (lv_op_2_1= '*' | lv_op_2_2= '/' ) ) ) ( (lv_right_3_0= ruleComparison ) ) )* )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1628:2: this_Comparison_0= ruleComparison ( () ( ( (lv_op_2_1= '*' | lv_op_2_2= '/' ) ) ) ( (lv_right_3_0= ruleComparison ) ) )*
            {
            if ( state.backtracking==0 ) {
               
              	  /* */ 
              	
            }
            if ( state.backtracking==0 ) {
               
                      newCompositeNode(grammarAccess.getMultiplicationAccess().getComparisonParserRuleCall_0()); 
                  
            }
            pushFollow(FOLLOW_ruleComparison_in_ruleMultiplication3679);
            this_Comparison_0=ruleComparison();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               
                      current = this_Comparison_0; 
                      afterParserOrEnumRuleCall();
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1639:1: ( () ( ( (lv_op_2_1= '*' | lv_op_2_2= '/' ) ) ) ( (lv_right_3_0= ruleComparison ) ) )*
            loop22:
            do {
                int alt22=2;
                int LA22_0 = input.LA(1);

                if ( ((LA22_0>=32 && LA22_0<=33)) ) {
                    alt22=1;
                }


                switch (alt22) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1639:2: () ( ( (lv_op_2_1= '*' | lv_op_2_2= '/' ) ) ) ( (lv_right_3_0= ruleComparison ) )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1639:2: ()
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1640:2: 
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	  /* */ 
            	      	
            	    }
            	    if ( state.backtracking==0 ) {

            	              current = forceCreateModelElementAndSet(
            	                  grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0(),
            	                  current);
            	          
            	    }

            	    }

            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1648:2: ( ( (lv_op_2_1= '*' | lv_op_2_2= '/' ) ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1649:1: ( (lv_op_2_1= '*' | lv_op_2_2= '/' ) )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1649:1: ( (lv_op_2_1= '*' | lv_op_2_2= '/' ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1650:1: (lv_op_2_1= '*' | lv_op_2_2= '/' )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1650:1: (lv_op_2_1= '*' | lv_op_2_2= '/' )
            	    int alt21=2;
            	    int LA21_0 = input.LA(1);

            	    if ( (LA21_0==32) ) {
            	        alt21=1;
            	    }
            	    else if ( (LA21_0==33) ) {
            	        alt21=2;
            	    }
            	    else {
            	        if (state.backtracking>0) {state.failed=true; return current;}
            	        NoViableAltException nvae =
            	            new NoViableAltException("", 21, 0, input);

            	        throw nvae;
            	    }
            	    switch (alt21) {
            	        case 1 :
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1651:3: lv_op_2_1= '*'
            	            {
            	            lv_op_2_1=(Token)match(input,32,FOLLOW_32_in_ruleMultiplication3711); if (state.failed) return current;
            	            if ( state.backtracking==0 ) {

            	                      newLeafNode(lv_op_2_1, grammarAccess.getMultiplicationAccess().getOpAsteriskKeyword_1_1_0_0());
            	                  
            	            }
            	            if ( state.backtracking==0 ) {

            	              	        if (current==null) {
            	              	            current = createModelElement(grammarAccess.getMultiplicationRule());
            	              	        }
            	                     		setWithLastConsumed(current, "op", lv_op_2_1, null);
            	              	    
            	            }

            	            }
            	            break;
            	        case 2 :
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1663:8: lv_op_2_2= '/'
            	            {
            	            lv_op_2_2=(Token)match(input,33,FOLLOW_33_in_ruleMultiplication3740); if (state.failed) return current;
            	            if ( state.backtracking==0 ) {

            	                      newLeafNode(lv_op_2_2, grammarAccess.getMultiplicationAccess().getOpSolidusKeyword_1_1_0_1());
            	                  
            	            }
            	            if ( state.backtracking==0 ) {

            	              	        if (current==null) {
            	              	            current = createModelElement(grammarAccess.getMultiplicationRule());
            	              	        }
            	                     		setWithLastConsumed(current, "op", lv_op_2_2, null);
            	              	    
            	            }

            	            }
            	            break;

            	    }


            	    }


            	    }

            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1678:2: ( (lv_right_3_0= ruleComparison ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1679:1: (lv_right_3_0= ruleComparison )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1679:1: (lv_right_3_0= ruleComparison )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1680:3: lv_right_3_0= ruleComparison
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getMultiplicationAccess().getRightComparisonParserRuleCall_1_2_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleComparison_in_ruleMultiplication3777);
            	    lv_right_3_0=ruleComparison();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getMultiplicationRule());
            	      	        }
            	             		set(
            	             			current, 
            	             			"right",
            	              		lv_right_3_0, 
            	              		"Comparison");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop22;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleMultiplication"


    // $ANTLR start "entryRuleComparison"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1704:1: entryRuleComparison returns [EObject current=null] : iv_ruleComparison= ruleComparison EOF ;
    public final EObject entryRuleComparison() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleComparison = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1705:2: (iv_ruleComparison= ruleComparison EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1706:2: iv_ruleComparison= ruleComparison EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getComparisonRule()); 
            }
            pushFollow(FOLLOW_ruleComparison_in_entryRuleComparison3815);
            iv_ruleComparison=ruleComparison();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleComparison; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleComparison3825); if (state.failed) return current;

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
    // $ANTLR end "entryRuleComparison"


    // $ANTLR start "ruleComparison"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1713:1: ruleComparison returns [EObject current=null] : (this_BooleanExpression_0= ruleBooleanExpression ( () ( ( (lv_op_2_1= '>=' | lv_op_2_2= '<=' | lv_op_2_3= '<' | lv_op_2_4= '>' | lv_op_2_5= '==' | lv_op_2_6= '!=' ) ) ) ( (lv_right_3_0= ruleBooleanExpression ) ) )* ) ;
    public final EObject ruleComparison() throws RecognitionException {
        EObject current = null;

        Token lv_op_2_1=null;
        Token lv_op_2_2=null;
        Token lv_op_2_3=null;
        Token lv_op_2_4=null;
        Token lv_op_2_5=null;
        Token lv_op_2_6=null;
        EObject this_BooleanExpression_0 = null;

        EObject lv_right_3_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1716:28: ( (this_BooleanExpression_0= ruleBooleanExpression ( () ( ( (lv_op_2_1= '>=' | lv_op_2_2= '<=' | lv_op_2_3= '<' | lv_op_2_4= '>' | lv_op_2_5= '==' | lv_op_2_6= '!=' ) ) ) ( (lv_right_3_0= ruleBooleanExpression ) ) )* ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1717:1: (this_BooleanExpression_0= ruleBooleanExpression ( () ( ( (lv_op_2_1= '>=' | lv_op_2_2= '<=' | lv_op_2_3= '<' | lv_op_2_4= '>' | lv_op_2_5= '==' | lv_op_2_6= '!=' ) ) ) ( (lv_right_3_0= ruleBooleanExpression ) ) )* )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1717:1: (this_BooleanExpression_0= ruleBooleanExpression ( () ( ( (lv_op_2_1= '>=' | lv_op_2_2= '<=' | lv_op_2_3= '<' | lv_op_2_4= '>' | lv_op_2_5= '==' | lv_op_2_6= '!=' ) ) ) ( (lv_right_3_0= ruleBooleanExpression ) ) )* )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1718:2: this_BooleanExpression_0= ruleBooleanExpression ( () ( ( (lv_op_2_1= '>=' | lv_op_2_2= '<=' | lv_op_2_3= '<' | lv_op_2_4= '>' | lv_op_2_5= '==' | lv_op_2_6= '!=' ) ) ) ( (lv_right_3_0= ruleBooleanExpression ) ) )*
            {
            if ( state.backtracking==0 ) {
               
              	  /* */ 
              	
            }
            if ( state.backtracking==0 ) {
               
                      newCompositeNode(grammarAccess.getComparisonAccess().getBooleanExpressionParserRuleCall_0()); 
                  
            }
            pushFollow(FOLLOW_ruleBooleanExpression_in_ruleComparison3875);
            this_BooleanExpression_0=ruleBooleanExpression();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               
                      current = this_BooleanExpression_0; 
                      afterParserOrEnumRuleCall();
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1729:1: ( () ( ( (lv_op_2_1= '>=' | lv_op_2_2= '<=' | lv_op_2_3= '<' | lv_op_2_4= '>' | lv_op_2_5= '==' | lv_op_2_6= '!=' ) ) ) ( (lv_right_3_0= ruleBooleanExpression ) ) )*
            loop24:
            do {
                int alt24=2;
                int LA24_0 = input.LA(1);

                if ( ((LA24_0>=12 && LA24_0<=13)||(LA24_0>=34 && LA24_0<=37)) ) {
                    alt24=1;
                }


                switch (alt24) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1729:2: () ( ( (lv_op_2_1= '>=' | lv_op_2_2= '<=' | lv_op_2_3= '<' | lv_op_2_4= '>' | lv_op_2_5= '==' | lv_op_2_6= '!=' ) ) ) ( (lv_right_3_0= ruleBooleanExpression ) )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1729:2: ()
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1730:2: 
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	  /* */ 
            	      	
            	    }
            	    if ( state.backtracking==0 ) {

            	              current = forceCreateModelElementAndSet(
            	                  grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0(),
            	                  current);
            	          
            	    }

            	    }

            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1738:2: ( ( (lv_op_2_1= '>=' | lv_op_2_2= '<=' | lv_op_2_3= '<' | lv_op_2_4= '>' | lv_op_2_5= '==' | lv_op_2_6= '!=' ) ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1739:1: ( (lv_op_2_1= '>=' | lv_op_2_2= '<=' | lv_op_2_3= '<' | lv_op_2_4= '>' | lv_op_2_5= '==' | lv_op_2_6= '!=' ) )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1739:1: ( (lv_op_2_1= '>=' | lv_op_2_2= '<=' | lv_op_2_3= '<' | lv_op_2_4= '>' | lv_op_2_5= '==' | lv_op_2_6= '!=' ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1740:1: (lv_op_2_1= '>=' | lv_op_2_2= '<=' | lv_op_2_3= '<' | lv_op_2_4= '>' | lv_op_2_5= '==' | lv_op_2_6= '!=' )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1740:1: (lv_op_2_1= '>=' | lv_op_2_2= '<=' | lv_op_2_3= '<' | lv_op_2_4= '>' | lv_op_2_5= '==' | lv_op_2_6= '!=' )
            	    int alt23=6;
            	    switch ( input.LA(1) ) {
            	    case 34:
            	        {
            	        alt23=1;
            	        }
            	        break;
            	    case 35:
            	        {
            	        alt23=2;
            	        }
            	        break;
            	    case 12:
            	        {
            	        alt23=3;
            	        }
            	        break;
            	    case 13:
            	        {
            	        alt23=4;
            	        }
            	        break;
            	    case 36:
            	        {
            	        alt23=5;
            	        }
            	        break;
            	    case 37:
            	        {
            	        alt23=6;
            	        }
            	        break;
            	    default:
            	        if (state.backtracking>0) {state.failed=true; return current;}
            	        NoViableAltException nvae =
            	            new NoViableAltException("", 23, 0, input);

            	        throw nvae;
            	    }

            	    switch (alt23) {
            	        case 1 :
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1741:3: lv_op_2_1= '>='
            	            {
            	            lv_op_2_1=(Token)match(input,34,FOLLOW_34_in_ruleComparison3907); if (state.failed) return current;
            	            if ( state.backtracking==0 ) {

            	                      newLeafNode(lv_op_2_1, grammarAccess.getComparisonAccess().getOpGreaterThanSignEqualsSignKeyword_1_1_0_0());
            	                  
            	            }
            	            if ( state.backtracking==0 ) {

            	              	        if (current==null) {
            	              	            current = createModelElement(grammarAccess.getComparisonRule());
            	              	        }
            	                     		setWithLastConsumed(current, "op", lv_op_2_1, null);
            	              	    
            	            }

            	            }
            	            break;
            	        case 2 :
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1753:8: lv_op_2_2= '<='
            	            {
            	            lv_op_2_2=(Token)match(input,35,FOLLOW_35_in_ruleComparison3936); if (state.failed) return current;
            	            if ( state.backtracking==0 ) {

            	                      newLeafNode(lv_op_2_2, grammarAccess.getComparisonAccess().getOpLessThanSignEqualsSignKeyword_1_1_0_1());
            	                  
            	            }
            	            if ( state.backtracking==0 ) {

            	              	        if (current==null) {
            	              	            current = createModelElement(grammarAccess.getComparisonRule());
            	              	        }
            	                     		setWithLastConsumed(current, "op", lv_op_2_2, null);
            	              	    
            	            }

            	            }
            	            break;
            	        case 3 :
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1765:8: lv_op_2_3= '<'
            	            {
            	            lv_op_2_3=(Token)match(input,12,FOLLOW_12_in_ruleComparison3965); if (state.failed) return current;
            	            if ( state.backtracking==0 ) {

            	                      newLeafNode(lv_op_2_3, grammarAccess.getComparisonAccess().getOpLessThanSignKeyword_1_1_0_2());
            	                  
            	            }
            	            if ( state.backtracking==0 ) {

            	              	        if (current==null) {
            	              	            current = createModelElement(grammarAccess.getComparisonRule());
            	              	        }
            	                     		setWithLastConsumed(current, "op", lv_op_2_3, null);
            	              	    
            	            }

            	            }
            	            break;
            	        case 4 :
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1777:8: lv_op_2_4= '>'
            	            {
            	            lv_op_2_4=(Token)match(input,13,FOLLOW_13_in_ruleComparison3994); if (state.failed) return current;
            	            if ( state.backtracking==0 ) {

            	                      newLeafNode(lv_op_2_4, grammarAccess.getComparisonAccess().getOpGreaterThanSignKeyword_1_1_0_3());
            	                  
            	            }
            	            if ( state.backtracking==0 ) {

            	              	        if (current==null) {
            	              	            current = createModelElement(grammarAccess.getComparisonRule());
            	              	        }
            	                     		setWithLastConsumed(current, "op", lv_op_2_4, null);
            	              	    
            	            }

            	            }
            	            break;
            	        case 5 :
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1789:8: lv_op_2_5= '=='
            	            {
            	            lv_op_2_5=(Token)match(input,36,FOLLOW_36_in_ruleComparison4023); if (state.failed) return current;
            	            if ( state.backtracking==0 ) {

            	                      newLeafNode(lv_op_2_5, grammarAccess.getComparisonAccess().getOpEqualsSignEqualsSignKeyword_1_1_0_4());
            	                  
            	            }
            	            if ( state.backtracking==0 ) {

            	              	        if (current==null) {
            	              	            current = createModelElement(grammarAccess.getComparisonRule());
            	              	        }
            	                     		setWithLastConsumed(current, "op", lv_op_2_5, null);
            	              	    
            	            }

            	            }
            	            break;
            	        case 6 :
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1801:8: lv_op_2_6= '!='
            	            {
            	            lv_op_2_6=(Token)match(input,37,FOLLOW_37_in_ruleComparison4052); if (state.failed) return current;
            	            if ( state.backtracking==0 ) {

            	                      newLeafNode(lv_op_2_6, grammarAccess.getComparisonAccess().getOpExclamationMarkEqualsSignKeyword_1_1_0_5());
            	                  
            	            }
            	            if ( state.backtracking==0 ) {

            	              	        if (current==null) {
            	              	            current = createModelElement(grammarAccess.getComparisonRule());
            	              	        }
            	                     		setWithLastConsumed(current, "op", lv_op_2_6, null);
            	              	    
            	            }

            	            }
            	            break;

            	    }


            	    }


            	    }

            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1816:2: ( (lv_right_3_0= ruleBooleanExpression ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1817:1: (lv_right_3_0= ruleBooleanExpression )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1817:1: (lv_right_3_0= ruleBooleanExpression )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1818:3: lv_right_3_0= ruleBooleanExpression
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getComparisonAccess().getRightBooleanExpressionParserRuleCall_1_2_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleBooleanExpression_in_ruleComparison4089);
            	    lv_right_3_0=ruleBooleanExpression();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getComparisonRule());
            	      	        }
            	             		set(
            	             			current, 
            	             			"right",
            	              		lv_right_3_0, 
            	              		"BooleanExpression");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop24;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleComparison"


    // $ANTLR start "entryRuleBooleanExpression"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1842:1: entryRuleBooleanExpression returns [EObject current=null] : iv_ruleBooleanExpression= ruleBooleanExpression EOF ;
    public final EObject entryRuleBooleanExpression() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleBooleanExpression = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1843:2: (iv_ruleBooleanExpression= ruleBooleanExpression EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1844:2: iv_ruleBooleanExpression= ruleBooleanExpression EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getBooleanExpressionRule()); 
            }
            pushFollow(FOLLOW_ruleBooleanExpression_in_entryRuleBooleanExpression4127);
            iv_ruleBooleanExpression=ruleBooleanExpression();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleBooleanExpression; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleBooleanExpression4137); if (state.failed) return current;

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
    // $ANTLR end "entryRuleBooleanExpression"


    // $ANTLR start "ruleBooleanExpression"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1851:1: ruleBooleanExpression returns [EObject current=null] : (this_Atomic_0= ruleAtomic ( () ( ( (lv_op_2_1= '||' | lv_op_2_2= '&&' ) ) ) ( (lv_right_3_0= ruleAtomic ) ) )* ) ;
    public final EObject ruleBooleanExpression() throws RecognitionException {
        EObject current = null;

        Token lv_op_2_1=null;
        Token lv_op_2_2=null;
        EObject this_Atomic_0 = null;

        EObject lv_right_3_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1854:28: ( (this_Atomic_0= ruleAtomic ( () ( ( (lv_op_2_1= '||' | lv_op_2_2= '&&' ) ) ) ( (lv_right_3_0= ruleAtomic ) ) )* ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1855:1: (this_Atomic_0= ruleAtomic ( () ( ( (lv_op_2_1= '||' | lv_op_2_2= '&&' ) ) ) ( (lv_right_3_0= ruleAtomic ) ) )* )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1855:1: (this_Atomic_0= ruleAtomic ( () ( ( (lv_op_2_1= '||' | lv_op_2_2= '&&' ) ) ) ( (lv_right_3_0= ruleAtomic ) ) )* )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1856:2: this_Atomic_0= ruleAtomic ( () ( ( (lv_op_2_1= '||' | lv_op_2_2= '&&' ) ) ) ( (lv_right_3_0= ruleAtomic ) ) )*
            {
            if ( state.backtracking==0 ) {
               
              	  /* */ 
              	
            }
            if ( state.backtracking==0 ) {
               
                      newCompositeNode(grammarAccess.getBooleanExpressionAccess().getAtomicParserRuleCall_0()); 
                  
            }
            pushFollow(FOLLOW_ruleAtomic_in_ruleBooleanExpression4187);
            this_Atomic_0=ruleAtomic();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               
                      current = this_Atomic_0; 
                      afterParserOrEnumRuleCall();
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1867:1: ( () ( ( (lv_op_2_1= '||' | lv_op_2_2= '&&' ) ) ) ( (lv_right_3_0= ruleAtomic ) ) )*
            loop26:
            do {
                int alt26=2;
                int LA26_0 = input.LA(1);

                if ( ((LA26_0>=38 && LA26_0<=39)) ) {
                    alt26=1;
                }


                switch (alt26) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1867:2: () ( ( (lv_op_2_1= '||' | lv_op_2_2= '&&' ) ) ) ( (lv_right_3_0= ruleAtomic ) )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1867:2: ()
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1868:2: 
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	  /* */ 
            	      	
            	    }
            	    if ( state.backtracking==0 ) {

            	              current = forceCreateModelElementAndSet(
            	                  grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0(),
            	                  current);
            	          
            	    }

            	    }

            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1876:2: ( ( (lv_op_2_1= '||' | lv_op_2_2= '&&' ) ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1877:1: ( (lv_op_2_1= '||' | lv_op_2_2= '&&' ) )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1877:1: ( (lv_op_2_1= '||' | lv_op_2_2= '&&' ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1878:1: (lv_op_2_1= '||' | lv_op_2_2= '&&' )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1878:1: (lv_op_2_1= '||' | lv_op_2_2= '&&' )
            	    int alt25=2;
            	    int LA25_0 = input.LA(1);

            	    if ( (LA25_0==38) ) {
            	        alt25=1;
            	    }
            	    else if ( (LA25_0==39) ) {
            	        alt25=2;
            	    }
            	    else {
            	        if (state.backtracking>0) {state.failed=true; return current;}
            	        NoViableAltException nvae =
            	            new NoViableAltException("", 25, 0, input);

            	        throw nvae;
            	    }
            	    switch (alt25) {
            	        case 1 :
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1879:3: lv_op_2_1= '||'
            	            {
            	            lv_op_2_1=(Token)match(input,38,FOLLOW_38_in_ruleBooleanExpression4219); if (state.failed) return current;
            	            if ( state.backtracking==0 ) {

            	                      newLeafNode(lv_op_2_1, grammarAccess.getBooleanExpressionAccess().getOpVerticalLineVerticalLineKeyword_1_1_0_0());
            	                  
            	            }
            	            if ( state.backtracking==0 ) {

            	              	        if (current==null) {
            	              	            current = createModelElement(grammarAccess.getBooleanExpressionRule());
            	              	        }
            	                     		setWithLastConsumed(current, "op", lv_op_2_1, null);
            	              	    
            	            }

            	            }
            	            break;
            	        case 2 :
            	            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1891:8: lv_op_2_2= '&&'
            	            {
            	            lv_op_2_2=(Token)match(input,39,FOLLOW_39_in_ruleBooleanExpression4248); if (state.failed) return current;
            	            if ( state.backtracking==0 ) {

            	                      newLeafNode(lv_op_2_2, grammarAccess.getBooleanExpressionAccess().getOpAmpersandAmpersandKeyword_1_1_0_1());
            	                  
            	            }
            	            if ( state.backtracking==0 ) {

            	              	        if (current==null) {
            	              	            current = createModelElement(grammarAccess.getBooleanExpressionRule());
            	              	        }
            	                     		setWithLastConsumed(current, "op", lv_op_2_2, null);
            	              	    
            	            }

            	            }
            	            break;

            	    }


            	    }


            	    }

            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1906:2: ( (lv_right_3_0= ruleAtomic ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1907:1: (lv_right_3_0= ruleAtomic )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1907:1: (lv_right_3_0= ruleAtomic )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1908:3: lv_right_3_0= ruleAtomic
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getBooleanExpressionAccess().getRightAtomicParserRuleCall_1_2_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleAtomic_in_ruleBooleanExpression4285);
            	    lv_right_3_0=ruleAtomic();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getBooleanExpressionRule());
            	      	        }
            	             		set(
            	             			current, 
            	             			"right",
            	              		lv_right_3_0, 
            	              		"Atomic");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop26;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleBooleanExpression"


    // $ANTLR start "entryRuleAtomic"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1932:1: entryRuleAtomic returns [EObject current=null] : iv_ruleAtomic= ruleAtomic EOF ;
    public final EObject entryRuleAtomic() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAtomic = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1933:2: (iv_ruleAtomic= ruleAtomic EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1934:2: iv_ruleAtomic= ruleAtomic EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAtomicRule()); 
            }
            pushFollow(FOLLOW_ruleAtomic_in_entryRuleAtomic4323);
            iv_ruleAtomic=ruleAtomic();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAtomic; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleAtomic4333); if (state.failed) return current;

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
    // $ANTLR end "entryRuleAtomic"


    // $ANTLR start "ruleAtomic"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1941:1: ruleAtomic returns [EObject current=null] : ( ( () otherlv_1= '!' ( (lv_expression_2_0= ruleAtomic ) ) ) | ( () otherlv_4= '-' ( (lv_expression_5_0= ruleAtomic ) ) ) | (this_TerminalExpression_6= ruleTerminalExpression ( () otherlv_8= '.' ( (lv_message_9_0= ruleMessage ) ) )* ) ) ;
    public final EObject ruleAtomic() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        Token otherlv_4=null;
        Token otherlv_8=null;
        EObject lv_expression_2_0 = null;

        EObject lv_expression_5_0 = null;

        EObject this_TerminalExpression_6 = null;

        EObject lv_message_9_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1944:28: ( ( ( () otherlv_1= '!' ( (lv_expression_2_0= ruleAtomic ) ) ) | ( () otherlv_4= '-' ( (lv_expression_5_0= ruleAtomic ) ) ) | (this_TerminalExpression_6= ruleTerminalExpression ( () otherlv_8= '.' ( (lv_message_9_0= ruleMessage ) ) )* ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1945:1: ( ( () otherlv_1= '!' ( (lv_expression_2_0= ruleAtomic ) ) ) | ( () otherlv_4= '-' ( (lv_expression_5_0= ruleAtomic ) ) ) | (this_TerminalExpression_6= ruleTerminalExpression ( () otherlv_8= '.' ( (lv_message_9_0= ruleMessage ) ) )* ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1945:1: ( ( () otherlv_1= '!' ( (lv_expression_2_0= ruleAtomic ) ) ) | ( () otherlv_4= '-' ( (lv_expression_5_0= ruleAtomic ) ) ) | (this_TerminalExpression_6= ruleTerminalExpression ( () otherlv_8= '.' ( (lv_message_9_0= ruleMessage ) ) )* ) )
            int alt28=3;
            switch ( input.LA(1) ) {
            case 40:
                {
                alt28=1;
                }
                break;
            case 31:
                {
                alt28=2;
                }
                break;
            case RULE_INT:
            case RULE_ID:
            case RULE_STRING:
            case 23:
            case 42:
            case 43:
            case 44:
            case 45:
            case 46:
            case 47:
                {
                alt28=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 28, 0, input);

                throw nvae;
            }

            switch (alt28) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1945:2: ( () otherlv_1= '!' ( (lv_expression_2_0= ruleAtomic ) ) )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1945:2: ( () otherlv_1= '!' ( (lv_expression_2_0= ruleAtomic ) ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1945:3: () otherlv_1= '!' ( (lv_expression_2_0= ruleAtomic ) )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1945:3: ()
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1946:2: 
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {

                              current = forceCreateModelElement(
                                  grammarAccess.getAtomicAccess().getBooleanNegationAction_0_0(),
                                  current);
                          
                    }

                    }

                    otherlv_1=(Token)match(input,40,FOLLOW_40_in_ruleAtomic4383); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                          	newLeafNode(otherlv_1, grammarAccess.getAtomicAccess().getExclamationMarkKeyword_0_1());
                          
                    }
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1958:1: ( (lv_expression_2_0= ruleAtomic ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1959:1: (lv_expression_2_0= ruleAtomic )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1959:1: (lv_expression_2_0= ruleAtomic )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1960:3: lv_expression_2_0= ruleAtomic
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getAtomicAccess().getExpressionAtomicParserRuleCall_0_2_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_ruleAtomic_in_ruleAtomic4404);
                    lv_expression_2_0=ruleAtomic();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getAtomicRule());
                      	        }
                             		set(
                             			current, 
                             			"expression",
                              		lv_expression_2_0, 
                              		"Atomic");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }


                    }


                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1977:6: ( () otherlv_4= '-' ( (lv_expression_5_0= ruleAtomic ) ) )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1977:6: ( () otherlv_4= '-' ( (lv_expression_5_0= ruleAtomic ) ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1977:7: () otherlv_4= '-' ( (lv_expression_5_0= ruleAtomic ) )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1977:7: ()
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1978:2: 
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {

                              current = forceCreateModelElement(
                                  grammarAccess.getAtomicAccess().getArithmeticSignedAction_1_0(),
                                  current);
                          
                    }

                    }

                    otherlv_4=(Token)match(input,31,FOLLOW_31_in_ruleAtomic4436); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                          	newLeafNode(otherlv_4, grammarAccess.getAtomicAccess().getHyphenMinusKeyword_1_1());
                          
                    }
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1990:1: ( (lv_expression_5_0= ruleAtomic ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1991:1: (lv_expression_5_0= ruleAtomic )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1991:1: (lv_expression_5_0= ruleAtomic )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1992:3: lv_expression_5_0= ruleAtomic
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getAtomicAccess().getExpressionAtomicParserRuleCall_1_2_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_ruleAtomic_in_ruleAtomic4457);
                    lv_expression_5_0=ruleAtomic();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getAtomicRule());
                      	        }
                             		set(
                             			current, 
                             			"expression",
                              		lv_expression_5_0, 
                              		"Atomic");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }


                    }


                    }
                    break;
                case 3 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2009:6: (this_TerminalExpression_6= ruleTerminalExpression ( () otherlv_8= '.' ( (lv_message_9_0= ruleMessage ) ) )* )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2009:6: (this_TerminalExpression_6= ruleTerminalExpression ( () otherlv_8= '.' ( (lv_message_9_0= ruleMessage ) ) )* )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2010:2: this_TerminalExpression_6= ruleTerminalExpression ( () otherlv_8= '.' ( (lv_message_9_0= ruleMessage ) ) )*
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getAtomicAccess().getTerminalExpressionParserRuleCall_2_0()); 
                          
                    }
                    pushFollow(FOLLOW_ruleTerminalExpression_in_ruleAtomic4490);
                    this_TerminalExpression_6=ruleTerminalExpression();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_TerminalExpression_6; 
                              afterParserOrEnumRuleCall();
                          
                    }
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2021:1: ( () otherlv_8= '.' ( (lv_message_9_0= ruleMessage ) ) )*
                    loop27:
                    do {
                        int alt27=2;
                        int LA27_0 = input.LA(1);

                        if ( (LA27_0==41) ) {
                            alt27=1;
                        }


                        switch (alt27) {
                    	case 1 :
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2021:2: () otherlv_8= '.' ( (lv_message_9_0= ruleMessage ) )
                    	    {
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2021:2: ()
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2022:2: 
                    	    {
                    	    if ( state.backtracking==0 ) {
                    	       
                    	      	  /* */ 
                    	      	
                    	    }
                    	    if ( state.backtracking==0 ) {

                    	              current = forceCreateModelElementAndSet(
                    	                  grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0(),
                    	                  current);
                    	          
                    	    }

                    	    }

                    	    otherlv_8=(Token)match(input,41,FOLLOW_41_in_ruleAtomic4514); if (state.failed) return current;
                    	    if ( state.backtracking==0 ) {

                    	          	newLeafNode(otherlv_8, grammarAccess.getAtomicAccess().getFullStopKeyword_2_1_1());
                    	          
                    	    }
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2034:1: ( (lv_message_9_0= ruleMessage ) )
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2035:1: (lv_message_9_0= ruleMessage )
                    	    {
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2035:1: (lv_message_9_0= ruleMessage )
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2036:3: lv_message_9_0= ruleMessage
                    	    {
                    	    if ( state.backtracking==0 ) {
                    	       
                    	      	        newCompositeNode(grammarAccess.getAtomicAccess().getMessageMessageParserRuleCall_2_1_2_0()); 
                    	      	    
                    	    }
                    	    pushFollow(FOLLOW_ruleMessage_in_ruleAtomic4535);
                    	    lv_message_9_0=ruleMessage();

                    	    state._fsp--;
                    	    if (state.failed) return current;
                    	    if ( state.backtracking==0 ) {

                    	      	        if (current==null) {
                    	      	            current = createModelElementForParent(grammarAccess.getAtomicRule());
                    	      	        }
                    	             		set(
                    	             			current, 
                    	             			"message",
                    	              		lv_message_9_0, 
                    	              		"Message");
                    	      	        afterParserOrEnumRuleCall();
                    	      	    
                    	    }

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop27;
                        }
                    } while (true);


                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleAtomic"


    // $ANTLR start "entryRuleTerminalExpression"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2060:1: entryRuleTerminalExpression returns [EObject current=null] : iv_ruleTerminalExpression= ruleTerminalExpression EOF ;
    public final EObject entryRuleTerminalExpression() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleTerminalExpression = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2061:2: (iv_ruleTerminalExpression= ruleTerminalExpression EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2062:2: iv_ruleTerminalExpression= ruleTerminalExpression EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getTerminalExpressionRule()); 
            }
            pushFollow(FOLLOW_ruleTerminalExpression_in_entryRuleTerminalExpression4574);
            iv_ruleTerminalExpression=ruleTerminalExpression();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleTerminalExpression; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleTerminalExpression4584); if (state.failed) return current;

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
    // $ANTLR end "entryRuleTerminalExpression"


    // $ANTLR start "ruleTerminalExpression"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2069:1: ruleTerminalExpression returns [EObject current=null] : (this_This_0= ruleThis | this_Null_1= ruleNull | this_Original_2= ruleOriginal | this_New_3= ruleNew | this_Cast_4= ruleCast | this_Constant_5= ruleConstant | this_VariableAccess_6= ruleVariableAccess | this_Paren_7= ruleParen ) ;
    public final EObject ruleTerminalExpression() throws RecognitionException {
        EObject current = null;

        EObject this_This_0 = null;

        EObject this_Null_1 = null;

        EObject this_Original_2 = null;

        EObject this_New_3 = null;

        EObject this_Cast_4 = null;

        EObject this_Constant_5 = null;

        EObject this_VariableAccess_6 = null;

        EObject this_Paren_7 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2072:28: ( (this_This_0= ruleThis | this_Null_1= ruleNull | this_Original_2= ruleOriginal | this_New_3= ruleNew | this_Cast_4= ruleCast | this_Constant_5= ruleConstant | this_VariableAccess_6= ruleVariableAccess | this_Paren_7= ruleParen ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2073:1: (this_This_0= ruleThis | this_Null_1= ruleNull | this_Original_2= ruleOriginal | this_New_3= ruleNew | this_Cast_4= ruleCast | this_Constant_5= ruleConstant | this_VariableAccess_6= ruleVariableAccess | this_Paren_7= ruleParen )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2073:1: (this_This_0= ruleThis | this_Null_1= ruleNull | this_Original_2= ruleOriginal | this_New_3= ruleNew | this_Cast_4= ruleCast | this_Constant_5= ruleConstant | this_VariableAccess_6= ruleVariableAccess | this_Paren_7= ruleParen )
            int alt29=8;
            alt29 = dfa29.predict(input);
            switch (alt29) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2074:2: this_This_0= ruleThis
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getTerminalExpressionAccess().getThisParserRuleCall_0()); 
                          
                    }
                    pushFollow(FOLLOW_ruleThis_in_ruleTerminalExpression4634);
                    this_This_0=ruleThis();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_This_0; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2087:2: this_Null_1= ruleNull
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getTerminalExpressionAccess().getNullParserRuleCall_1()); 
                          
                    }
                    pushFollow(FOLLOW_ruleNull_in_ruleTerminalExpression4664);
                    this_Null_1=ruleNull();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_Null_1; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 3 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2100:2: this_Original_2= ruleOriginal
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getTerminalExpressionAccess().getOriginalParserRuleCall_2()); 
                          
                    }
                    pushFollow(FOLLOW_ruleOriginal_in_ruleTerminalExpression4694);
                    this_Original_2=ruleOriginal();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_Original_2; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 4 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2113:2: this_New_3= ruleNew
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getTerminalExpressionAccess().getNewParserRuleCall_3()); 
                          
                    }
                    pushFollow(FOLLOW_ruleNew_in_ruleTerminalExpression4724);
                    this_New_3=ruleNew();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_New_3; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 5 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2126:2: this_Cast_4= ruleCast
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getTerminalExpressionAccess().getCastParserRuleCall_4()); 
                          
                    }
                    pushFollow(FOLLOW_ruleCast_in_ruleTerminalExpression4754);
                    this_Cast_4=ruleCast();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_Cast_4; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 6 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2139:2: this_Constant_5= ruleConstant
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getTerminalExpressionAccess().getConstantParserRuleCall_5()); 
                          
                    }
                    pushFollow(FOLLOW_ruleConstant_in_ruleTerminalExpression4784);
                    this_Constant_5=ruleConstant();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_Constant_5; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 7 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2152:2: this_VariableAccess_6= ruleVariableAccess
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getTerminalExpressionAccess().getVariableAccessParserRuleCall_6()); 
                          
                    }
                    pushFollow(FOLLOW_ruleVariableAccess_in_ruleTerminalExpression4814);
                    this_VariableAccess_6=ruleVariableAccess();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_VariableAccess_6; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 8 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2165:2: this_Paren_7= ruleParen
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getTerminalExpressionAccess().getParenParserRuleCall_7()); 
                          
                    }
                    pushFollow(FOLLOW_ruleParen_in_ruleTerminalExpression4844);
                    this_Paren_7=ruleParen();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_Paren_7; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleTerminalExpression"


    // $ANTLR start "entryRuleNull"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2184:1: entryRuleNull returns [EObject current=null] : iv_ruleNull= ruleNull EOF ;
    public final EObject entryRuleNull() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleNull = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2185:2: (iv_ruleNull= ruleNull EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2186:2: iv_ruleNull= ruleNull EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getNullRule()); 
            }
            pushFollow(FOLLOW_ruleNull_in_entryRuleNull4879);
            iv_ruleNull=ruleNull();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleNull; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleNull4889); if (state.failed) return current;

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
    // $ANTLR end "entryRuleNull"


    // $ANTLR start "ruleNull"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2193:1: ruleNull returns [EObject current=null] : ( (lv_null_0_0= 'null' ) ) ;
    public final EObject ruleNull() throws RecognitionException {
        EObject current = null;

        Token lv_null_0_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2196:28: ( ( (lv_null_0_0= 'null' ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2197:1: ( (lv_null_0_0= 'null' ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2197:1: ( (lv_null_0_0= 'null' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2198:1: (lv_null_0_0= 'null' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2198:1: (lv_null_0_0= 'null' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2199:3: lv_null_0_0= 'null'
            {
            lv_null_0_0=(Token)match(input,42,FOLLOW_42_in_ruleNull4931); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                      newLeafNode(lv_null_0_0, grammarAccess.getNullAccess().getNullNullKeyword_0());
                  
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getNullRule());
              	        }
                     		setWithLastConsumed(current, "null", lv_null_0_0, "null");
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleNull"


    // $ANTLR start "entryRuleThis"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2220:1: entryRuleThis returns [EObject current=null] : iv_ruleThis= ruleThis EOF ;
    public final EObject entryRuleThis() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleThis = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2221:2: (iv_ruleThis= ruleThis EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2222:2: iv_ruleThis= ruleThis EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getThisRule()); 
            }
            pushFollow(FOLLOW_ruleThis_in_entryRuleThis4979);
            iv_ruleThis=ruleThis();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleThis; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleThis4989); if (state.failed) return current;

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
    // $ANTLR end "entryRuleThis"


    // $ANTLR start "ruleThis"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2229:1: ruleThis returns [EObject current=null] : ( (lv_variable_0_0= 'this' ) ) ;
    public final EObject ruleThis() throws RecognitionException {
        EObject current = null;

        Token lv_variable_0_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2232:28: ( ( (lv_variable_0_0= 'this' ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2233:1: ( (lv_variable_0_0= 'this' ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2233:1: ( (lv_variable_0_0= 'this' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2234:1: (lv_variable_0_0= 'this' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2234:1: (lv_variable_0_0= 'this' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2235:3: lv_variable_0_0= 'this'
            {
            lv_variable_0_0=(Token)match(input,43,FOLLOW_43_in_ruleThis5031); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                      newLeafNode(lv_variable_0_0, grammarAccess.getThisAccess().getVariableThisKeyword_0());
                  
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getThisRule());
              	        }
                     		setWithLastConsumed(current, "variable", lv_variable_0_0, "this");
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleThis"


    // $ANTLR start "entryRuleOriginal"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2256:1: entryRuleOriginal returns [EObject current=null] : iv_ruleOriginal= ruleOriginal EOF ;
    public final EObject entryRuleOriginal() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleOriginal = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2257:2: (iv_ruleOriginal= ruleOriginal EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2258:2: iv_ruleOriginal= ruleOriginal EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getOriginalRule()); 
            }
            pushFollow(FOLLOW_ruleOriginal_in_entryRuleOriginal5079);
            iv_ruleOriginal=ruleOriginal();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleOriginal; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleOriginal5089); if (state.failed) return current;

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
    // $ANTLR end "entryRuleOriginal"


    // $ANTLR start "ruleOriginal"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2265:1: ruleOriginal returns [EObject current=null] : ( ( (lv_method_0_0= 'original' ) ) otherlv_1= '(' ( ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )* )? otherlv_5= ')' ) ;
    public final EObject ruleOriginal() throws RecognitionException {
        EObject current = null;

        Token lv_method_0_0=null;
        Token otherlv_1=null;
        Token otherlv_3=null;
        Token otherlv_5=null;
        EObject lv_args_2_0 = null;

        EObject lv_args_4_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2268:28: ( ( ( (lv_method_0_0= 'original' ) ) otherlv_1= '(' ( ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )* )? otherlv_5= ')' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2269:1: ( ( (lv_method_0_0= 'original' ) ) otherlv_1= '(' ( ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )* )? otherlv_5= ')' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2269:1: ( ( (lv_method_0_0= 'original' ) ) otherlv_1= '(' ( ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )* )? otherlv_5= ')' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2269:2: ( (lv_method_0_0= 'original' ) ) otherlv_1= '(' ( ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )* )? otherlv_5= ')'
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2269:2: ( (lv_method_0_0= 'original' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2270:1: (lv_method_0_0= 'original' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2270:1: (lv_method_0_0= 'original' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2271:3: lv_method_0_0= 'original'
            {
            lv_method_0_0=(Token)match(input,44,FOLLOW_44_in_ruleOriginal5132); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                      newLeafNode(lv_method_0_0, grammarAccess.getOriginalAccess().getMethodOriginalKeyword_0_0());
                  
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getOriginalRule());
              	        }
                     		setWithLastConsumed(current, "method", lv_method_0_0, "original");
              	    
            }

            }


            }

            otherlv_1=(Token)match(input,23,FOLLOW_23_in_ruleOriginal5157); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_1, grammarAccess.getOriginalAccess().getLeftParenthesisKeyword_1());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2288:1: ( ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )* )?
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( ((LA31_0>=RULE_INT && LA31_0<=RULE_ID)||LA31_0==RULE_STRING||LA31_0==23||LA31_0==31||LA31_0==40||(LA31_0>=42 && LA31_0<=47)) ) {
                alt31=1;
            }
            switch (alt31) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2288:2: ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )*
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2288:2: ( (lv_args_2_0= ruleExpression ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2289:1: (lv_args_2_0= ruleExpression )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2289:1: (lv_args_2_0= ruleExpression )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2290:3: lv_args_2_0= ruleExpression
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getOriginalAccess().getArgsExpressionParserRuleCall_2_0_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_ruleExpression_in_ruleOriginal5179);
                    lv_args_2_0=ruleExpression();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getOriginalRule());
                      	        }
                             		add(
                             			current, 
                             			"args",
                              		lv_args_2_0, 
                              		"Expression");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }

                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2306:2: (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )*
                    loop30:
                    do {
                        int alt30=2;
                        int LA30_0 = input.LA(1);

                        if ( (LA30_0==24) ) {
                            alt30=1;
                        }


                        switch (alt30) {
                    	case 1 :
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2306:4: otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) )
                    	    {
                    	    otherlv_3=(Token)match(input,24,FOLLOW_24_in_ruleOriginal5192); if (state.failed) return current;
                    	    if ( state.backtracking==0 ) {

                    	          	newLeafNode(otherlv_3, grammarAccess.getOriginalAccess().getCommaKeyword_2_1_0());
                    	          
                    	    }
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2310:1: ( (lv_args_4_0= ruleExpression ) )
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2311:1: (lv_args_4_0= ruleExpression )
                    	    {
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2311:1: (lv_args_4_0= ruleExpression )
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2312:3: lv_args_4_0= ruleExpression
                    	    {
                    	    if ( state.backtracking==0 ) {
                    	       
                    	      	        newCompositeNode(grammarAccess.getOriginalAccess().getArgsExpressionParserRuleCall_2_1_1_0()); 
                    	      	    
                    	    }
                    	    pushFollow(FOLLOW_ruleExpression_in_ruleOriginal5213);
                    	    lv_args_4_0=ruleExpression();

                    	    state._fsp--;
                    	    if (state.failed) return current;
                    	    if ( state.backtracking==0 ) {

                    	      	        if (current==null) {
                    	      	            current = createModelElementForParent(grammarAccess.getOriginalRule());
                    	      	        }
                    	             		add(
                    	             			current, 
                    	             			"args",
                    	              		lv_args_4_0, 
                    	              		"Expression");
                    	      	        afterParserOrEnumRuleCall();
                    	      	    
                    	    }

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop30;
                        }
                    } while (true);


                    }
                    break;

            }

            otherlv_5=(Token)match(input,25,FOLLOW_25_in_ruleOriginal5229); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_5, grammarAccess.getOriginalAccess().getRightParenthesisKeyword_3());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleOriginal"


    // $ANTLR start "entryRuleVariableAccess"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2340:1: entryRuleVariableAccess returns [EObject current=null] : iv_ruleVariableAccess= ruleVariableAccess EOF ;
    public final EObject entryRuleVariableAccess() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleVariableAccess = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2341:2: (iv_ruleVariableAccess= ruleVariableAccess EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2342:2: iv_ruleVariableAccess= ruleVariableAccess EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getVariableAccessRule()); 
            }
            pushFollow(FOLLOW_ruleVariableAccess_in_entryRuleVariableAccess5265);
            iv_ruleVariableAccess=ruleVariableAccess();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleVariableAccess; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleVariableAccess5275); if (state.failed) return current;

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
    // $ANTLR end "entryRuleVariableAccess"


    // $ANTLR start "ruleVariableAccess"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2349:1: ruleVariableAccess returns [EObject current=null] : ( (otherlv_0= RULE_ID ) ) ;
    public final EObject ruleVariableAccess() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2352:28: ( ( (otherlv_0= RULE_ID ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2353:1: ( (otherlv_0= RULE_ID ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2353:1: ( (otherlv_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2354:1: (otherlv_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2354:1: (otherlv_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2355:3: otherlv_0= RULE_ID
            {
            if ( state.backtracking==0 ) {
               
              		  /* */ 
              		
            }
            if ( state.backtracking==0 ) {

              			if (current==null) {
              	            current = createModelElement(grammarAccess.getVariableAccessRule());
              	        }
                      
            }
            otherlv_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleVariableAccess5323); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              		newLeafNode(otherlv_0, grammarAccess.getVariableAccessAccess().getVariableTypedDeclarationCrossReference_0()); 
              	
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleVariableAccess"


    // $ANTLR start "entryRuleNew"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2377:1: entryRuleNew returns [EObject current=null] : iv_ruleNew= ruleNew EOF ;
    public final EObject entryRuleNew() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleNew = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2378:2: (iv_ruleNew= ruleNew EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2379:2: iv_ruleNew= ruleNew EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getNewRule()); 
            }
            pushFollow(FOLLOW_ruleNew_in_entryRuleNew5358);
            iv_ruleNew=ruleNew();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleNew; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleNew5368); if (state.failed) return current;

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
    // $ANTLR end "entryRuleNew"


    // $ANTLR start "ruleNew"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2386:1: ruleNew returns [EObject current=null] : (otherlv_0= 'new' ( (lv_class_1_0= ruleClassName ) ) otherlv_2= '(' otherlv_3= ')' ) ;
    public final EObject ruleNew() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        Token otherlv_3=null;
        AntlrDatatypeRuleToken lv_class_1_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2389:28: ( (otherlv_0= 'new' ( (lv_class_1_0= ruleClassName ) ) otherlv_2= '(' otherlv_3= ')' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2390:1: (otherlv_0= 'new' ( (lv_class_1_0= ruleClassName ) ) otherlv_2= '(' otherlv_3= ')' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2390:1: (otherlv_0= 'new' ( (lv_class_1_0= ruleClassName ) ) otherlv_2= '(' otherlv_3= ')' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2390:3: otherlv_0= 'new' ( (lv_class_1_0= ruleClassName ) ) otherlv_2= '(' otherlv_3= ')'
            {
            otherlv_0=(Token)match(input,45,FOLLOW_45_in_ruleNew5405); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getNewAccess().getNewKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2394:1: ( (lv_class_1_0= ruleClassName ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2395:1: (lv_class_1_0= ruleClassName )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2395:1: (lv_class_1_0= ruleClassName )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2396:3: lv_class_1_0= ruleClassName
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getNewAccess().getClassClassNameParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleClassName_in_ruleNew5426);
            lv_class_1_0=ruleClassName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getNewRule());
              	        }
                     		set(
                     			current, 
                     			"class",
                      		lv_class_1_0, 
                      		"ClassName");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            otherlv_2=(Token)match(input,23,FOLLOW_23_in_ruleNew5438); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getNewAccess().getLeftParenthesisKeyword_2());
                  
            }
            otherlv_3=(Token)match(input,25,FOLLOW_25_in_ruleNew5450); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_3, grammarAccess.getNewAccess().getRightParenthesisKeyword_3());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleNew"


    // $ANTLR start "entryRuleCast"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2428:1: entryRuleCast returns [EObject current=null] : iv_ruleCast= ruleCast EOF ;
    public final EObject entryRuleCast() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleCast = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2429:2: (iv_ruleCast= ruleCast EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2430:2: iv_ruleCast= ruleCast EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getCastRule()); 
            }
            pushFollow(FOLLOW_ruleCast_in_entryRuleCast5486);
            iv_ruleCast=ruleCast();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleCast; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleCast5496); if (state.failed) return current;

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
    // $ANTLR end "entryRuleCast"


    // $ANTLR start "ruleCast"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2437:1: ruleCast returns [EObject current=null] : (otherlv_0= '(' ( (lv_type_1_0= ruleClassName ) ) otherlv_2= ')' ( (lv_object_3_0= ruleTerminalExpression ) ) ) ;
    public final EObject ruleCast() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        AntlrDatatypeRuleToken lv_type_1_0 = null;

        EObject lv_object_3_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2440:28: ( (otherlv_0= '(' ( (lv_type_1_0= ruleClassName ) ) otherlv_2= ')' ( (lv_object_3_0= ruleTerminalExpression ) ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2441:1: (otherlv_0= '(' ( (lv_type_1_0= ruleClassName ) ) otherlv_2= ')' ( (lv_object_3_0= ruleTerminalExpression ) ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2441:1: (otherlv_0= '(' ( (lv_type_1_0= ruleClassName ) ) otherlv_2= ')' ( (lv_object_3_0= ruleTerminalExpression ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2441:3: otherlv_0= '(' ( (lv_type_1_0= ruleClassName ) ) otherlv_2= ')' ( (lv_object_3_0= ruleTerminalExpression ) )
            {
            otherlv_0=(Token)match(input,23,FOLLOW_23_in_ruleCast5533); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getCastAccess().getLeftParenthesisKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2445:1: ( (lv_type_1_0= ruleClassName ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2446:1: (lv_type_1_0= ruleClassName )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2446:1: (lv_type_1_0= ruleClassName )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2447:3: lv_type_1_0= ruleClassName
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getCastAccess().getTypeClassNameParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleClassName_in_ruleCast5554);
            lv_type_1_0=ruleClassName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getCastRule());
              	        }
                     		set(
                     			current, 
                     			"type",
                      		lv_type_1_0, 
                      		"ClassName");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            otherlv_2=(Token)match(input,25,FOLLOW_25_in_ruleCast5566); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getCastAccess().getRightParenthesisKeyword_2());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2467:1: ( (lv_object_3_0= ruleTerminalExpression ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2468:1: (lv_object_3_0= ruleTerminalExpression )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2468:1: (lv_object_3_0= ruleTerminalExpression )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2469:3: lv_object_3_0= ruleTerminalExpression
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getCastAccess().getObjectTerminalExpressionParserRuleCall_3_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleTerminalExpression_in_ruleCast5587);
            lv_object_3_0=ruleTerminalExpression();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getCastRule());
              	        }
                     		set(
                     			current, 
                     			"object",
                      		lv_object_3_0, 
                      		"TerminalExpression");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleCast"


    // $ANTLR start "entryRuleParen"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2493:1: entryRuleParen returns [EObject current=null] : iv_ruleParen= ruleParen EOF ;
    public final EObject entryRuleParen() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleParen = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2494:2: (iv_ruleParen= ruleParen EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2495:2: iv_ruleParen= ruleParen EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getParenRule()); 
            }
            pushFollow(FOLLOW_ruleParen_in_entryRuleParen5623);
            iv_ruleParen=ruleParen();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleParen; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleParen5633); if (state.failed) return current;

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
    // $ANTLR end "entryRuleParen"


    // $ANTLR start "ruleParen"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2502:1: ruleParen returns [EObject current=null] : (otherlv_0= '(' ( (lv_expression_1_0= ruleExpression ) ) otherlv_2= ')' ) ;
    public final EObject ruleParen() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        EObject lv_expression_1_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2505:28: ( (otherlv_0= '(' ( (lv_expression_1_0= ruleExpression ) ) otherlv_2= ')' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2506:1: (otherlv_0= '(' ( (lv_expression_1_0= ruleExpression ) ) otherlv_2= ')' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2506:1: (otherlv_0= '(' ( (lv_expression_1_0= ruleExpression ) ) otherlv_2= ')' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2506:3: otherlv_0= '(' ( (lv_expression_1_0= ruleExpression ) ) otherlv_2= ')'
            {
            otherlv_0=(Token)match(input,23,FOLLOW_23_in_ruleParen5670); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getParenAccess().getLeftParenthesisKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2510:1: ( (lv_expression_1_0= ruleExpression ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2511:1: (lv_expression_1_0= ruleExpression )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2511:1: (lv_expression_1_0= ruleExpression )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2512:3: lv_expression_1_0= ruleExpression
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getParenAccess().getExpressionExpressionParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleExpression_in_ruleParen5691);
            lv_expression_1_0=ruleExpression();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getParenRule());
              	        }
                     		set(
                     			current, 
                     			"expression",
                      		lv_expression_1_0, 
                      		"Expression");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            otherlv_2=(Token)match(input,25,FOLLOW_25_in_ruleParen5703); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getParenAccess().getRightParenthesisKeyword_2());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleParen"


    // $ANTLR start "entryRuleConstant"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2540:1: entryRuleConstant returns [EObject current=null] : iv_ruleConstant= ruleConstant EOF ;
    public final EObject entryRuleConstant() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleConstant = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2541:2: (iv_ruleConstant= ruleConstant EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2542:2: iv_ruleConstant= ruleConstant EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getConstantRule()); 
            }
            pushFollow(FOLLOW_ruleConstant_in_entryRuleConstant5739);
            iv_ruleConstant=ruleConstant();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleConstant; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleConstant5749); if (state.failed) return current;

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
    // $ANTLR end "entryRuleConstant"


    // $ANTLR start "ruleConstant"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2549:1: ruleConstant returns [EObject current=null] : (this_IntConstant_0= ruleIntConstant | this_BoolConstant_1= ruleBoolConstant | this_StringConstant_2= ruleStringConstant ) ;
    public final EObject ruleConstant() throws RecognitionException {
        EObject current = null;

        EObject this_IntConstant_0 = null;

        EObject this_BoolConstant_1 = null;

        EObject this_StringConstant_2 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2552:28: ( (this_IntConstant_0= ruleIntConstant | this_BoolConstant_1= ruleBoolConstant | this_StringConstant_2= ruleStringConstant ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2553:1: (this_IntConstant_0= ruleIntConstant | this_BoolConstant_1= ruleBoolConstant | this_StringConstant_2= ruleStringConstant )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2553:1: (this_IntConstant_0= ruleIntConstant | this_BoolConstant_1= ruleBoolConstant | this_StringConstant_2= ruleStringConstant )
            int alt32=3;
            switch ( input.LA(1) ) {
            case RULE_INT:
                {
                alt32=1;
                }
                break;
            case 46:
            case 47:
                {
                alt32=2;
                }
                break;
            case RULE_STRING:
                {
                alt32=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 32, 0, input);

                throw nvae;
            }

            switch (alt32) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2554:2: this_IntConstant_0= ruleIntConstant
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getConstantAccess().getIntConstantParserRuleCall_0()); 
                          
                    }
                    pushFollow(FOLLOW_ruleIntConstant_in_ruleConstant5799);
                    this_IntConstant_0=ruleIntConstant();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_IntConstant_0; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2567:2: this_BoolConstant_1= ruleBoolConstant
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getConstantAccess().getBoolConstantParserRuleCall_1()); 
                          
                    }
                    pushFollow(FOLLOW_ruleBoolConstant_in_ruleConstant5829);
                    this_BoolConstant_1=ruleBoolConstant();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_BoolConstant_1; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 3 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2580:2: this_StringConstant_2= ruleStringConstant
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getConstantAccess().getStringConstantParserRuleCall_2()); 
                          
                    }
                    pushFollow(FOLLOW_ruleStringConstant_in_ruleConstant5859);
                    this_StringConstant_2=ruleStringConstant();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_StringConstant_2; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleConstant"


    // $ANTLR start "entryRuleStringConstant"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2599:1: entryRuleStringConstant returns [EObject current=null] : iv_ruleStringConstant= ruleStringConstant EOF ;
    public final EObject entryRuleStringConstant() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleStringConstant = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2600:2: (iv_ruleStringConstant= ruleStringConstant EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2601:2: iv_ruleStringConstant= ruleStringConstant EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getStringConstantRule()); 
            }
            pushFollow(FOLLOW_ruleStringConstant_in_entryRuleStringConstant5894);
            iv_ruleStringConstant=ruleStringConstant();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleStringConstant; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleStringConstant5904); if (state.failed) return current;

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
    // $ANTLR end "entryRuleStringConstant"


    // $ANTLR start "ruleStringConstant"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2608:1: ruleStringConstant returns [EObject current=null] : ( (lv_constant_0_0= RULE_STRING ) ) ;
    public final EObject ruleStringConstant() throws RecognitionException {
        EObject current = null;

        Token lv_constant_0_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2611:28: ( ( (lv_constant_0_0= RULE_STRING ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2612:1: ( (lv_constant_0_0= RULE_STRING ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2612:1: ( (lv_constant_0_0= RULE_STRING ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2613:1: (lv_constant_0_0= RULE_STRING )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2613:1: (lv_constant_0_0= RULE_STRING )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2614:3: lv_constant_0_0= RULE_STRING
            {
            lv_constant_0_0=(Token)match(input,RULE_STRING,FOLLOW_RULE_STRING_in_ruleStringConstant5945); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_constant_0_0, grammarAccess.getStringConstantAccess().getConstantSTRINGTerminalRuleCall_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getStringConstantRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"constant",
                      		lv_constant_0_0, 
                      		"STRING");
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleStringConstant"


    // $ANTLR start "entryRuleIntConstant"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2638:1: entryRuleIntConstant returns [EObject current=null] : iv_ruleIntConstant= ruleIntConstant EOF ;
    public final EObject entryRuleIntConstant() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleIntConstant = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2639:2: (iv_ruleIntConstant= ruleIntConstant EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2640:2: iv_ruleIntConstant= ruleIntConstant EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getIntConstantRule()); 
            }
            pushFollow(FOLLOW_ruleIntConstant_in_entryRuleIntConstant5985);
            iv_ruleIntConstant=ruleIntConstant();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleIntConstant; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleIntConstant5995); if (state.failed) return current;

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
    // $ANTLR end "entryRuleIntConstant"


    // $ANTLR start "ruleIntConstant"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2647:1: ruleIntConstant returns [EObject current=null] : ( (lv_constant_0_0= RULE_INT ) ) ;
    public final EObject ruleIntConstant() throws RecognitionException {
        EObject current = null;

        Token lv_constant_0_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2650:28: ( ( (lv_constant_0_0= RULE_INT ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2651:1: ( (lv_constant_0_0= RULE_INT ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2651:1: ( (lv_constant_0_0= RULE_INT ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2652:1: (lv_constant_0_0= RULE_INT )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2652:1: (lv_constant_0_0= RULE_INT )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2653:3: lv_constant_0_0= RULE_INT
            {
            lv_constant_0_0=(Token)match(input,RULE_INT,FOLLOW_RULE_INT_in_ruleIntConstant6036); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_constant_0_0, grammarAccess.getIntConstantAccess().getConstantINTTerminalRuleCall_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getIntConstantRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"constant",
                      		lv_constant_0_0, 
                      		"INT");
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleIntConstant"


    // $ANTLR start "entryRuleBoolConstant"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2677:1: entryRuleBoolConstant returns [EObject current=null] : iv_ruleBoolConstant= ruleBoolConstant EOF ;
    public final EObject entryRuleBoolConstant() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleBoolConstant = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2678:2: (iv_ruleBoolConstant= ruleBoolConstant EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2679:2: iv_ruleBoolConstant= ruleBoolConstant EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getBoolConstantRule()); 
            }
            pushFollow(FOLLOW_ruleBoolConstant_in_entryRuleBoolConstant6076);
            iv_ruleBoolConstant=ruleBoolConstant();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleBoolConstant; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleBoolConstant6086); if (state.failed) return current;

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
    // $ANTLR end "entryRuleBoolConstant"


    // $ANTLR start "ruleBoolConstant"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2686:1: ruleBoolConstant returns [EObject current=null] : ( ( (lv_constant_0_1= 'true' | lv_constant_0_2= 'false' ) ) ) ;
    public final EObject ruleBoolConstant() throws RecognitionException {
        EObject current = null;

        Token lv_constant_0_1=null;
        Token lv_constant_0_2=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2689:28: ( ( ( (lv_constant_0_1= 'true' | lv_constant_0_2= 'false' ) ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2690:1: ( ( (lv_constant_0_1= 'true' | lv_constant_0_2= 'false' ) ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2690:1: ( ( (lv_constant_0_1= 'true' | lv_constant_0_2= 'false' ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2691:1: ( (lv_constant_0_1= 'true' | lv_constant_0_2= 'false' ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2691:1: ( (lv_constant_0_1= 'true' | lv_constant_0_2= 'false' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2692:1: (lv_constant_0_1= 'true' | lv_constant_0_2= 'false' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2692:1: (lv_constant_0_1= 'true' | lv_constant_0_2= 'false' )
            int alt33=2;
            int LA33_0 = input.LA(1);

            if ( (LA33_0==46) ) {
                alt33=1;
            }
            else if ( (LA33_0==47) ) {
                alt33=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 33, 0, input);

                throw nvae;
            }
            switch (alt33) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2693:3: lv_constant_0_1= 'true'
                    {
                    lv_constant_0_1=(Token)match(input,46,FOLLOW_46_in_ruleBoolConstant6130); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                              newLeafNode(lv_constant_0_1, grammarAccess.getBoolConstantAccess().getConstantTrueKeyword_0_0());
                          
                    }
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElement(grammarAccess.getBoolConstantRule());
                      	        }
                             		setWithLastConsumed(current, "constant", lv_constant_0_1, null);
                      	    
                    }

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2705:8: lv_constant_0_2= 'false'
                    {
                    lv_constant_0_2=(Token)match(input,47,FOLLOW_47_in_ruleBoolConstant6159); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                              newLeafNode(lv_constant_0_2, grammarAccess.getBoolConstantAccess().getConstantFalseKeyword_0_1());
                          
                    }
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElement(grammarAccess.getBoolConstantRule());
                      	        }
                             		setWithLastConsumed(current, "constant", lv_constant_0_2, null);
                      	    
                    }

                    }
                    break;

            }


            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleBoolConstant"


    // $ANTLR start "entryRuleMessage"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2728:1: entryRuleMessage returns [EObject current=null] : iv_ruleMessage= ruleMessage EOF ;
    public final EObject entryRuleMessage() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMessage = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2729:2: (iv_ruleMessage= ruleMessage EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2730:2: iv_ruleMessage= ruleMessage EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getMessageRule()); 
            }
            pushFollow(FOLLOW_ruleMessage_in_entryRuleMessage6210);
            iv_ruleMessage=ruleMessage();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleMessage; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleMessage6220); if (state.failed) return current;

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
    // $ANTLR end "entryRuleMessage"


    // $ANTLR start "ruleMessage"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2737:1: ruleMessage returns [EObject current=null] : (this_FieldSelection_0= ruleFieldSelection | this_MethodCall_1= ruleMethodCall ) ;
    public final EObject ruleMessage() throws RecognitionException {
        EObject current = null;

        EObject this_FieldSelection_0 = null;

        EObject this_MethodCall_1 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2740:28: ( (this_FieldSelection_0= ruleFieldSelection | this_MethodCall_1= ruleMethodCall ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2741:1: (this_FieldSelection_0= ruleFieldSelection | this_MethodCall_1= ruleMethodCall )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2741:1: (this_FieldSelection_0= ruleFieldSelection | this_MethodCall_1= ruleMethodCall )
            int alt34=2;
            int LA34_0 = input.LA(1);

            if ( (LA34_0==RULE_ID) ) {
                int LA34_1 = input.LA(2);

                if ( (LA34_1==EOF||(LA34_1>=12 && LA34_1<=13)||LA34_1==22||(LA34_1>=24 && LA34_1<=25)||LA34_1==27||(LA34_1>=30 && LA34_1<=39)||LA34_1==41) ) {
                    alt34=1;
                }
                else if ( (LA34_1==23) ) {
                    alt34=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return current;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 34, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 34, 0, input);

                throw nvae;
            }
            switch (alt34) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2742:2: this_FieldSelection_0= ruleFieldSelection
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getMessageAccess().getFieldSelectionParserRuleCall_0()); 
                          
                    }
                    pushFollow(FOLLOW_ruleFieldSelection_in_ruleMessage6270);
                    this_FieldSelection_0=ruleFieldSelection();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_FieldSelection_0; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2755:2: this_MethodCall_1= ruleMethodCall
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getMessageAccess().getMethodCallParserRuleCall_1()); 
                          
                    }
                    pushFollow(FOLLOW_ruleMethodCall_in_ruleMessage6300);
                    this_MethodCall_1=ruleMethodCall();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_MethodCall_1; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleMessage"


    // $ANTLR start "entryRuleMethodCall"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2774:1: entryRuleMethodCall returns [EObject current=null] : iv_ruleMethodCall= ruleMethodCall EOF ;
    public final EObject entryRuleMethodCall() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMethodCall = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2775:2: (iv_ruleMethodCall= ruleMethodCall EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2776:2: iv_ruleMethodCall= ruleMethodCall EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getMethodCallRule()); 
            }
            pushFollow(FOLLOW_ruleMethodCall_in_entryRuleMethodCall6335);
            iv_ruleMethodCall=ruleMethodCall();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleMethodCall; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleMethodCall6345); if (state.failed) return current;

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
    // $ANTLR end "entryRuleMethodCall"


    // $ANTLR start "ruleMethodCall"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2783:1: ruleMethodCall returns [EObject current=null] : ( ( (lv_method_0_0= RULE_ID ) ) otherlv_1= '(' ( ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )* )? otherlv_5= ')' ) ;
    public final EObject ruleMethodCall() throws RecognitionException {
        EObject current = null;

        Token lv_method_0_0=null;
        Token otherlv_1=null;
        Token otherlv_3=null;
        Token otherlv_5=null;
        EObject lv_args_2_0 = null;

        EObject lv_args_4_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2786:28: ( ( ( (lv_method_0_0= RULE_ID ) ) otherlv_1= '(' ( ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )* )? otherlv_5= ')' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2787:1: ( ( (lv_method_0_0= RULE_ID ) ) otherlv_1= '(' ( ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )* )? otherlv_5= ')' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2787:1: ( ( (lv_method_0_0= RULE_ID ) ) otherlv_1= '(' ( ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )* )? otherlv_5= ')' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2787:2: ( (lv_method_0_0= RULE_ID ) ) otherlv_1= '(' ( ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )* )? otherlv_5= ')'
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2787:2: ( (lv_method_0_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2788:1: (lv_method_0_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2788:1: (lv_method_0_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2789:3: lv_method_0_0= RULE_ID
            {
            lv_method_0_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleMethodCall6387); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_method_0_0, grammarAccess.getMethodCallAccess().getMethodIDTerminalRuleCall_0_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getMethodCallRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"method",
                      		lv_method_0_0, 
                      		"ID");
              	    
            }

            }


            }

            otherlv_1=(Token)match(input,23,FOLLOW_23_in_ruleMethodCall6404); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_1, grammarAccess.getMethodCallAccess().getLeftParenthesisKeyword_1());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2809:1: ( ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )* )?
            int alt36=2;
            int LA36_0 = input.LA(1);

            if ( ((LA36_0>=RULE_INT && LA36_0<=RULE_ID)||LA36_0==RULE_STRING||LA36_0==23||LA36_0==31||LA36_0==40||(LA36_0>=42 && LA36_0<=47)) ) {
                alt36=1;
            }
            switch (alt36) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2809:2: ( (lv_args_2_0= ruleExpression ) ) (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )*
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2809:2: ( (lv_args_2_0= ruleExpression ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2810:1: (lv_args_2_0= ruleExpression )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2810:1: (lv_args_2_0= ruleExpression )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2811:3: lv_args_2_0= ruleExpression
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getMethodCallAccess().getArgsExpressionParserRuleCall_2_0_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_ruleExpression_in_ruleMethodCall6426);
                    lv_args_2_0=ruleExpression();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getMethodCallRule());
                      	        }
                             		add(
                             			current, 
                             			"args",
                              		lv_args_2_0, 
                              		"Expression");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }

                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2827:2: (otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) ) )*
                    loop35:
                    do {
                        int alt35=2;
                        int LA35_0 = input.LA(1);

                        if ( (LA35_0==24) ) {
                            alt35=1;
                        }


                        switch (alt35) {
                    	case 1 :
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2827:4: otherlv_3= ',' ( (lv_args_4_0= ruleExpression ) )
                    	    {
                    	    otherlv_3=(Token)match(input,24,FOLLOW_24_in_ruleMethodCall6439); if (state.failed) return current;
                    	    if ( state.backtracking==0 ) {

                    	          	newLeafNode(otherlv_3, grammarAccess.getMethodCallAccess().getCommaKeyword_2_1_0());
                    	          
                    	    }
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2831:1: ( (lv_args_4_0= ruleExpression ) )
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2832:1: (lv_args_4_0= ruleExpression )
                    	    {
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2832:1: (lv_args_4_0= ruleExpression )
                    	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2833:3: lv_args_4_0= ruleExpression
                    	    {
                    	    if ( state.backtracking==0 ) {
                    	       
                    	      	        newCompositeNode(grammarAccess.getMethodCallAccess().getArgsExpressionParserRuleCall_2_1_1_0()); 
                    	      	    
                    	    }
                    	    pushFollow(FOLLOW_ruleExpression_in_ruleMethodCall6460);
                    	    lv_args_4_0=ruleExpression();

                    	    state._fsp--;
                    	    if (state.failed) return current;
                    	    if ( state.backtracking==0 ) {

                    	      	        if (current==null) {
                    	      	            current = createModelElementForParent(grammarAccess.getMethodCallRule());
                    	      	        }
                    	             		add(
                    	             			current, 
                    	             			"args",
                    	              		lv_args_4_0, 
                    	              		"Expression");
                    	      	        afterParserOrEnumRuleCall();
                    	      	    
                    	    }

                    	    }


                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop35;
                        }
                    } while (true);


                    }
                    break;

            }

            otherlv_5=(Token)match(input,25,FOLLOW_25_in_ruleMethodCall6476); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_5, grammarAccess.getMethodCallAccess().getRightParenthesisKeyword_3());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleMethodCall"


    // $ANTLR start "entryRuleFieldSelection"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2861:1: entryRuleFieldSelection returns [EObject current=null] : iv_ruleFieldSelection= ruleFieldSelection EOF ;
    public final EObject entryRuleFieldSelection() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleFieldSelection = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2862:2: (iv_ruleFieldSelection= ruleFieldSelection EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2863:2: iv_ruleFieldSelection= ruleFieldSelection EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getFieldSelectionRule()); 
            }
            pushFollow(FOLLOW_ruleFieldSelection_in_entryRuleFieldSelection6512);
            iv_ruleFieldSelection=ruleFieldSelection();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleFieldSelection; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleFieldSelection6522); if (state.failed) return current;

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
    // $ANTLR end "entryRuleFieldSelection"


    // $ANTLR start "ruleFieldSelection"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2870:1: ruleFieldSelection returns [EObject current=null] : ( (lv_field_0_0= RULE_ID ) ) ;
    public final EObject ruleFieldSelection() throws RecognitionException {
        EObject current = null;

        Token lv_field_0_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2873:28: ( ( (lv_field_0_0= RULE_ID ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2874:1: ( (lv_field_0_0= RULE_ID ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2874:1: ( (lv_field_0_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2875:1: (lv_field_0_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2875:1: (lv_field_0_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2876:3: lv_field_0_0= RULE_ID
            {
            lv_field_0_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleFieldSelection6563); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_field_0_0, grammarAccess.getFieldSelectionAccess().getFieldIDTerminalRuleCall_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getFieldSelectionRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"field",
                      		lv_field_0_0, 
                      		"ID");
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleFieldSelection"


    // $ANTLR start "entryRuleDeltaModule"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2900:1: entryRuleDeltaModule returns [EObject current=null] : iv_ruleDeltaModule= ruleDeltaModule EOF ;
    public final EObject entryRuleDeltaModule() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleDeltaModule = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2901:2: (iv_ruleDeltaModule= ruleDeltaModule EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2902:2: iv_ruleDeltaModule= ruleDeltaModule EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getDeltaModuleRule()); 
            }
            pushFollow(FOLLOW_ruleDeltaModule_in_entryRuleDeltaModule6603);
            iv_ruleDeltaModule=ruleDeltaModule();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleDeltaModule; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleDeltaModule6613); if (state.failed) return current;

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
    // $ANTLR end "entryRuleDeltaModule"


    // $ANTLR start "ruleDeltaModule"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2909:1: ruleDeltaModule returns [EObject current=null] : (otherlv_0= 'delta' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '{' ( (lv_deltaActions_3_0= ruleDeltaAction ) )* otherlv_4= '}' ) ;
    public final EObject ruleDeltaModule() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token lv_name_1_0=null;
        Token otherlv_2=null;
        Token otherlv_4=null;
        EObject lv_deltaActions_3_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2912:28: ( (otherlv_0= 'delta' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '{' ( (lv_deltaActions_3_0= ruleDeltaAction ) )* otherlv_4= '}' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2913:1: (otherlv_0= 'delta' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '{' ( (lv_deltaActions_3_0= ruleDeltaAction ) )* otherlv_4= '}' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2913:1: (otherlv_0= 'delta' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '{' ( (lv_deltaActions_3_0= ruleDeltaAction ) )* otherlv_4= '}' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2913:3: otherlv_0= 'delta' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '{' ( (lv_deltaActions_3_0= ruleDeltaAction ) )* otherlv_4= '}'
            {
            otherlv_0=(Token)match(input,48,FOLLOW_48_in_ruleDeltaModule6650); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getDeltaModuleAccess().getDeltaKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2917:1: ( (lv_name_1_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2918:1: (lv_name_1_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2918:1: (lv_name_1_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2919:3: lv_name_1_0= RULE_ID
            {
            lv_name_1_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleDeltaModule6667); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_name_1_0, grammarAccess.getDeltaModuleAccess().getNameIDTerminalRuleCall_1_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getDeltaModuleRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"name",
                      		lv_name_1_0, 
                      		"ID");
              	    
            }

            }


            }

            otherlv_2=(Token)match(input,20,FOLLOW_20_in_ruleDeltaModule6684); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getDeltaModuleAccess().getLeftCurlyBracketKeyword_2());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2939:1: ( (lv_deltaActions_3_0= ruleDeltaAction ) )*
            loop37:
            do {
                int alt37=2;
                int LA37_0 = input.LA(1);

                if ( ((LA37_0>=49 && LA37_0<=51)) ) {
                    alt37=1;
                }


                switch (alt37) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2940:1: (lv_deltaActions_3_0= ruleDeltaAction )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2940:1: (lv_deltaActions_3_0= ruleDeltaAction )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2941:3: lv_deltaActions_3_0= ruleDeltaAction
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getDeltaModuleAccess().getDeltaActionsDeltaActionParserRuleCall_3_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleDeltaAction_in_ruleDeltaModule6705);
            	    lv_deltaActions_3_0=ruleDeltaAction();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getDeltaModuleRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"deltaActions",
            	              		lv_deltaActions_3_0, 
            	              		"DeltaAction");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop37;
                }
            } while (true);

            otherlv_4=(Token)match(input,21,FOLLOW_21_in_ruleDeltaModule6718); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_4, grammarAccess.getDeltaModuleAccess().getRightCurlyBracketKeyword_4());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleDeltaModule"


    // $ANTLR start "entryRuleDeltaAction"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2969:1: entryRuleDeltaAction returns [EObject current=null] : iv_ruleDeltaAction= ruleDeltaAction EOF ;
    public final EObject entryRuleDeltaAction() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleDeltaAction = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2970:2: (iv_ruleDeltaAction= ruleDeltaAction EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2971:2: iv_ruleDeltaAction= ruleDeltaAction EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getDeltaActionRule()); 
            }
            pushFollow(FOLLOW_ruleDeltaAction_in_entryRuleDeltaAction6754);
            iv_ruleDeltaAction=ruleDeltaAction();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleDeltaAction; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleDeltaAction6764); if (state.failed) return current;

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
    // $ANTLR end "entryRuleDeltaAction"


    // $ANTLR start "ruleDeltaAction"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2978:1: ruleDeltaAction returns [EObject current=null] : (this_ClassAddition_0= ruleClassAddition | this_RemovesOrModifiesClass_1= ruleRemovesOrModifiesClass ) ;
    public final EObject ruleDeltaAction() throws RecognitionException {
        EObject current = null;

        EObject this_ClassAddition_0 = null;

        EObject this_RemovesOrModifiesClass_1 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2981:28: ( (this_ClassAddition_0= ruleClassAddition | this_RemovesOrModifiesClass_1= ruleRemovesOrModifiesClass ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2982:1: (this_ClassAddition_0= ruleClassAddition | this_RemovesOrModifiesClass_1= ruleRemovesOrModifiesClass )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2982:1: (this_ClassAddition_0= ruleClassAddition | this_RemovesOrModifiesClass_1= ruleRemovesOrModifiesClass )
            int alt38=2;
            int LA38_0 = input.LA(1);

            if ( (LA38_0==49) ) {
                alt38=1;
            }
            else if ( ((LA38_0>=50 && LA38_0<=51)) ) {
                alt38=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 38, 0, input);

                throw nvae;
            }
            switch (alt38) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2983:2: this_ClassAddition_0= ruleClassAddition
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getDeltaActionAccess().getClassAdditionParserRuleCall_0()); 
                          
                    }
                    pushFollow(FOLLOW_ruleClassAddition_in_ruleDeltaAction6814);
                    this_ClassAddition_0=ruleClassAddition();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_ClassAddition_0; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2996:2: this_RemovesOrModifiesClass_1= ruleRemovesOrModifiesClass
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getDeltaActionAccess().getRemovesOrModifiesClassParserRuleCall_1()); 
                          
                    }
                    pushFollow(FOLLOW_ruleRemovesOrModifiesClass_in_ruleDeltaAction6844);
                    this_RemovesOrModifiesClass_1=ruleRemovesOrModifiesClass();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_RemovesOrModifiesClass_1; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleDeltaAction"


    // $ANTLR start "entryRuleClassAddition"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3015:1: entryRuleClassAddition returns [EObject current=null] : iv_ruleClassAddition= ruleClassAddition EOF ;
    public final EObject entryRuleClassAddition() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleClassAddition = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3016:2: (iv_ruleClassAddition= ruleClassAddition EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3017:2: iv_ruleClassAddition= ruleClassAddition EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getClassAdditionRule()); 
            }
            pushFollow(FOLLOW_ruleClassAddition_in_entryRuleClassAddition6879);
            iv_ruleClassAddition=ruleClassAddition();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleClassAddition; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleClassAddition6889); if (state.failed) return current;

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
    // $ANTLR end "entryRuleClassAddition"


    // $ANTLR start "ruleClassAddition"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3024:1: ruleClassAddition returns [EObject current=null] : (otherlv_0= 'adds' ( (lv_class_1_0= ruleClass ) ) ) ;
    public final EObject ruleClassAddition() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        EObject lv_class_1_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3027:28: ( (otherlv_0= 'adds' ( (lv_class_1_0= ruleClass ) ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3028:1: (otherlv_0= 'adds' ( (lv_class_1_0= ruleClass ) ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3028:1: (otherlv_0= 'adds' ( (lv_class_1_0= ruleClass ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3028:3: otherlv_0= 'adds' ( (lv_class_1_0= ruleClass ) )
            {
            otherlv_0=(Token)match(input,49,FOLLOW_49_in_ruleClassAddition6926); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getClassAdditionAccess().getAddsKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3032:1: ( (lv_class_1_0= ruleClass ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3033:1: (lv_class_1_0= ruleClass )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3033:1: (lv_class_1_0= ruleClass )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3034:3: lv_class_1_0= ruleClass
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getClassAdditionAccess().getClassClassParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleClass_in_ruleClassAddition6947);
            lv_class_1_0=ruleClass();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getClassAdditionRule());
              	        }
                     		set(
                     			current, 
                     			"class",
                      		lv_class_1_0, 
                      		"Class");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleClassAddition"


    // $ANTLR start "entryRuleRemovesOrModifiesClass"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3058:1: entryRuleRemovesOrModifiesClass returns [EObject current=null] : iv_ruleRemovesOrModifiesClass= ruleRemovesOrModifiesClass EOF ;
    public final EObject entryRuleRemovesOrModifiesClass() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleRemovesOrModifiesClass = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3059:2: (iv_ruleRemovesOrModifiesClass= ruleRemovesOrModifiesClass EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3060:2: iv_ruleRemovesOrModifiesClass= ruleRemovesOrModifiesClass EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getRemovesOrModifiesClassRule()); 
            }
            pushFollow(FOLLOW_ruleRemovesOrModifiesClass_in_entryRuleRemovesOrModifiesClass6983);
            iv_ruleRemovesOrModifiesClass=ruleRemovesOrModifiesClass();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleRemovesOrModifiesClass; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleRemovesOrModifiesClass6993); if (state.failed) return current;

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
    // $ANTLR end "entryRuleRemovesOrModifiesClass"


    // $ANTLR start "ruleRemovesOrModifiesClass"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3067:1: ruleRemovesOrModifiesClass returns [EObject current=null] : (this_ClassRemoval_0= ruleClassRemoval | this_ClassModification_1= ruleClassModification ) ;
    public final EObject ruleRemovesOrModifiesClass() throws RecognitionException {
        EObject current = null;

        EObject this_ClassRemoval_0 = null;

        EObject this_ClassModification_1 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3070:28: ( (this_ClassRemoval_0= ruleClassRemoval | this_ClassModification_1= ruleClassModification ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3071:1: (this_ClassRemoval_0= ruleClassRemoval | this_ClassModification_1= ruleClassModification )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3071:1: (this_ClassRemoval_0= ruleClassRemoval | this_ClassModification_1= ruleClassModification )
            int alt39=2;
            int LA39_0 = input.LA(1);

            if ( (LA39_0==50) ) {
                alt39=1;
            }
            else if ( (LA39_0==51) ) {
                alt39=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 39, 0, input);

                throw nvae;
            }
            switch (alt39) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3072:2: this_ClassRemoval_0= ruleClassRemoval
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getRemovesOrModifiesClassAccess().getClassRemovalParserRuleCall_0()); 
                          
                    }
                    pushFollow(FOLLOW_ruleClassRemoval_in_ruleRemovesOrModifiesClass7043);
                    this_ClassRemoval_0=ruleClassRemoval();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_ClassRemoval_0; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3085:2: this_ClassModification_1= ruleClassModification
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getRemovesOrModifiesClassAccess().getClassModificationParserRuleCall_1()); 
                          
                    }
                    pushFollow(FOLLOW_ruleClassModification_in_ruleRemovesOrModifiesClass7073);
                    this_ClassModification_1=ruleClassModification();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_ClassModification_1; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleRemovesOrModifiesClass"


    // $ANTLR start "entryRuleClassRemoval"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3104:1: entryRuleClassRemoval returns [EObject current=null] : iv_ruleClassRemoval= ruleClassRemoval EOF ;
    public final EObject entryRuleClassRemoval() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleClassRemoval = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3105:2: (iv_ruleClassRemoval= ruleClassRemoval EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3106:2: iv_ruleClassRemoval= ruleClassRemoval EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getClassRemovalRule()); 
            }
            pushFollow(FOLLOW_ruleClassRemoval_in_entryRuleClassRemoval7108);
            iv_ruleClassRemoval=ruleClassRemoval();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleClassRemoval; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleClassRemoval7118); if (state.failed) return current;

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
    // $ANTLR end "entryRuleClassRemoval"


    // $ANTLR start "ruleClassRemoval"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3113:1: ruleClassRemoval returns [EObject current=null] : (otherlv_0= 'removes' ( (lv_name_1_0= ruleClassName ) ) otherlv_2= ';' ) ;
    public final EObject ruleClassRemoval() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        AntlrDatatypeRuleToken lv_name_1_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3116:28: ( (otherlv_0= 'removes' ( (lv_name_1_0= ruleClassName ) ) otherlv_2= ';' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3117:1: (otherlv_0= 'removes' ( (lv_name_1_0= ruleClassName ) ) otherlv_2= ';' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3117:1: (otherlv_0= 'removes' ( (lv_name_1_0= ruleClassName ) ) otherlv_2= ';' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3117:3: otherlv_0= 'removes' ( (lv_name_1_0= ruleClassName ) ) otherlv_2= ';'
            {
            otherlv_0=(Token)match(input,50,FOLLOW_50_in_ruleClassRemoval7155); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getClassRemovalAccess().getRemovesKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3121:1: ( (lv_name_1_0= ruleClassName ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3122:1: (lv_name_1_0= ruleClassName )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3122:1: (lv_name_1_0= ruleClassName )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3123:3: lv_name_1_0= ruleClassName
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getClassRemovalAccess().getNameClassNameParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleClassName_in_ruleClassRemoval7176);
            lv_name_1_0=ruleClassName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getClassRemovalRule());
              	        }
                     		set(
                     			current, 
                     			"name",
                      		lv_name_1_0, 
                      		"ClassName");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            otherlv_2=(Token)match(input,22,FOLLOW_22_in_ruleClassRemoval7188); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getClassRemovalAccess().getSemicolonKeyword_2());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleClassRemoval"


    // $ANTLR start "entryRuleClassModification"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3151:1: entryRuleClassModification returns [EObject current=null] : iv_ruleClassModification= ruleClassModification EOF ;
    public final EObject entryRuleClassModification() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleClassModification = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3152:2: (iv_ruleClassModification= ruleClassModification EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3153:2: iv_ruleClassModification= ruleClassModification EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getClassModificationRule()); 
            }
            pushFollow(FOLLOW_ruleClassModification_in_entryRuleClassModification7224);
            iv_ruleClassModification=ruleClassModification();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleClassModification; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleClassModification7234); if (state.failed) return current;

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
    // $ANTLR end "entryRuleClassModification"


    // $ANTLR start "ruleClassModification"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3160:1: ruleClassModification returns [EObject current=null] : (otherlv_0= 'modifies' ( (lv_name_1_0= ruleClassName ) ) (otherlv_2= 'extending' ( (lv_extends_3_0= ruleClassName ) ) )? otherlv_4= '{' ( (lv_subActions_5_0= ruleDeltaSubAction ) )* otherlv_6= '}' ) ;
    public final EObject ruleClassModification() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        Token otherlv_4=null;
        Token otherlv_6=null;
        AntlrDatatypeRuleToken lv_name_1_0 = null;

        AntlrDatatypeRuleToken lv_extends_3_0 = null;

        EObject lv_subActions_5_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3163:28: ( (otherlv_0= 'modifies' ( (lv_name_1_0= ruleClassName ) ) (otherlv_2= 'extending' ( (lv_extends_3_0= ruleClassName ) ) )? otherlv_4= '{' ( (lv_subActions_5_0= ruleDeltaSubAction ) )* otherlv_6= '}' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3164:1: (otherlv_0= 'modifies' ( (lv_name_1_0= ruleClassName ) ) (otherlv_2= 'extending' ( (lv_extends_3_0= ruleClassName ) ) )? otherlv_4= '{' ( (lv_subActions_5_0= ruleDeltaSubAction ) )* otherlv_6= '}' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3164:1: (otherlv_0= 'modifies' ( (lv_name_1_0= ruleClassName ) ) (otherlv_2= 'extending' ( (lv_extends_3_0= ruleClassName ) ) )? otherlv_4= '{' ( (lv_subActions_5_0= ruleDeltaSubAction ) )* otherlv_6= '}' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3164:3: otherlv_0= 'modifies' ( (lv_name_1_0= ruleClassName ) ) (otherlv_2= 'extending' ( (lv_extends_3_0= ruleClassName ) ) )? otherlv_4= '{' ( (lv_subActions_5_0= ruleDeltaSubAction ) )* otherlv_6= '}'
            {
            otherlv_0=(Token)match(input,51,FOLLOW_51_in_ruleClassModification7271); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getClassModificationAccess().getModifiesKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3168:1: ( (lv_name_1_0= ruleClassName ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3169:1: (lv_name_1_0= ruleClassName )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3169:1: (lv_name_1_0= ruleClassName )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3170:3: lv_name_1_0= ruleClassName
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getClassModificationAccess().getNameClassNameParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleClassName_in_ruleClassModification7292);
            lv_name_1_0=ruleClassName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getClassModificationRule());
              	        }
                     		set(
                     			current, 
                     			"name",
                      		lv_name_1_0, 
                      		"ClassName");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3186:2: (otherlv_2= 'extending' ( (lv_extends_3_0= ruleClassName ) ) )?
            int alt40=2;
            int LA40_0 = input.LA(1);

            if ( (LA40_0==52) ) {
                alt40=1;
            }
            switch (alt40) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3186:4: otherlv_2= 'extending' ( (lv_extends_3_0= ruleClassName ) )
                    {
                    otherlv_2=(Token)match(input,52,FOLLOW_52_in_ruleClassModification7305); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                          	newLeafNode(otherlv_2, grammarAccess.getClassModificationAccess().getExtendingKeyword_2_0());
                          
                    }
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3190:1: ( (lv_extends_3_0= ruleClassName ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3191:1: (lv_extends_3_0= ruleClassName )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3191:1: (lv_extends_3_0= ruleClassName )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3192:3: lv_extends_3_0= ruleClassName
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getClassModificationAccess().getExtendsClassNameParserRuleCall_2_1_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_ruleClassName_in_ruleClassModification7326);
                    lv_extends_3_0=ruleClassName();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getClassModificationRule());
                      	        }
                             		set(
                             			current, 
                             			"extends",
                              		lv_extends_3_0, 
                              		"ClassName");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }


                    }
                    break;

            }

            otherlv_4=(Token)match(input,20,FOLLOW_20_in_ruleClassModification7340); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_4, grammarAccess.getClassModificationAccess().getLeftCurlyBracketKeyword_3());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3212:1: ( (lv_subActions_5_0= ruleDeltaSubAction ) )*
            loop41:
            do {
                int alt41=2;
                int LA41_0 = input.LA(1);

                if ( (LA41_0==49||LA41_0==51||(LA41_0>=53 && LA41_0<=54)) ) {
                    alt41=1;
                }


                switch (alt41) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3213:1: (lv_subActions_5_0= ruleDeltaSubAction )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3213:1: (lv_subActions_5_0= ruleDeltaSubAction )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3214:3: lv_subActions_5_0= ruleDeltaSubAction
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getClassModificationAccess().getSubActionsDeltaSubActionParserRuleCall_4_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleDeltaSubAction_in_ruleClassModification7361);
            	    lv_subActions_5_0=ruleDeltaSubAction();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getClassModificationRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"subActions",
            	              		lv_subActions_5_0, 
            	              		"DeltaSubAction");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop41;
                }
            } while (true);

            otherlv_6=(Token)match(input,21,FOLLOW_21_in_ruleClassModification7374); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_6, grammarAccess.getClassModificationAccess().getRightCurlyBracketKeyword_5());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleClassModification"


    // $ANTLR start "entryRuleDeltaSubAction"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3242:1: entryRuleDeltaSubAction returns [EObject current=null] : iv_ruleDeltaSubAction= ruleDeltaSubAction EOF ;
    public final EObject entryRuleDeltaSubAction() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleDeltaSubAction = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3243:2: (iv_ruleDeltaSubAction= ruleDeltaSubAction EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3244:2: iv_ruleDeltaSubAction= ruleDeltaSubAction EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getDeltaSubActionRule()); 
            }
            pushFollow(FOLLOW_ruleDeltaSubAction_in_entryRuleDeltaSubAction7410);
            iv_ruleDeltaSubAction=ruleDeltaSubAction();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleDeltaSubAction; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleDeltaSubAction7420); if (state.failed) return current;

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
    // $ANTLR end "entryRuleDeltaSubAction"


    // $ANTLR start "ruleDeltaSubAction"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3251:1: ruleDeltaSubAction returns [EObject current=null] : (this_MethodOrFieldAddition_0= ruleMethodOrFieldAddition | this_FieldRemoval_1= ruleFieldRemoval | this_MethodRemoval_2= ruleMethodRemoval | this_MethodModification_3= ruleMethodModification ) ;
    public final EObject ruleDeltaSubAction() throws RecognitionException {
        EObject current = null;

        EObject this_MethodOrFieldAddition_0 = null;

        EObject this_FieldRemoval_1 = null;

        EObject this_MethodRemoval_2 = null;

        EObject this_MethodModification_3 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3254:28: ( (this_MethodOrFieldAddition_0= ruleMethodOrFieldAddition | this_FieldRemoval_1= ruleFieldRemoval | this_MethodRemoval_2= ruleMethodRemoval | this_MethodModification_3= ruleMethodModification ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3255:1: (this_MethodOrFieldAddition_0= ruleMethodOrFieldAddition | this_FieldRemoval_1= ruleFieldRemoval | this_MethodRemoval_2= ruleMethodRemoval | this_MethodModification_3= ruleMethodModification )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3255:1: (this_MethodOrFieldAddition_0= ruleMethodOrFieldAddition | this_FieldRemoval_1= ruleFieldRemoval | this_MethodRemoval_2= ruleMethodRemoval | this_MethodModification_3= ruleMethodModification )
            int alt42=4;
            switch ( input.LA(1) ) {
            case 49:
                {
                alt42=1;
                }
                break;
            case 53:
                {
                alt42=2;
                }
                break;
            case 54:
                {
                alt42=3;
                }
                break;
            case 51:
                {
                alt42=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 42, 0, input);

                throw nvae;
            }

            switch (alt42) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3256:2: this_MethodOrFieldAddition_0= ruleMethodOrFieldAddition
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getDeltaSubActionAccess().getMethodOrFieldAdditionParserRuleCall_0()); 
                          
                    }
                    pushFollow(FOLLOW_ruleMethodOrFieldAddition_in_ruleDeltaSubAction7470);
                    this_MethodOrFieldAddition_0=ruleMethodOrFieldAddition();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_MethodOrFieldAddition_0; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3269:2: this_FieldRemoval_1= ruleFieldRemoval
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getDeltaSubActionAccess().getFieldRemovalParserRuleCall_1()); 
                          
                    }
                    pushFollow(FOLLOW_ruleFieldRemoval_in_ruleDeltaSubAction7500);
                    this_FieldRemoval_1=ruleFieldRemoval();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_FieldRemoval_1; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 3 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3282:2: this_MethodRemoval_2= ruleMethodRemoval
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getDeltaSubActionAccess().getMethodRemovalParserRuleCall_2()); 
                          
                    }
                    pushFollow(FOLLOW_ruleMethodRemoval_in_ruleDeltaSubAction7530);
                    this_MethodRemoval_2=ruleMethodRemoval();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_MethodRemoval_2; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 4 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3295:2: this_MethodModification_3= ruleMethodModification
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getDeltaSubActionAccess().getMethodModificationParserRuleCall_3()); 
                          
                    }
                    pushFollow(FOLLOW_ruleMethodModification_in_ruleDeltaSubAction7560);
                    this_MethodModification_3=ruleMethodModification();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_MethodModification_3; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleDeltaSubAction"


    // $ANTLR start "entryRuleMethodOrFieldAddition"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3314:1: entryRuleMethodOrFieldAddition returns [EObject current=null] : iv_ruleMethodOrFieldAddition= ruleMethodOrFieldAddition EOF ;
    public final EObject entryRuleMethodOrFieldAddition() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMethodOrFieldAddition = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3315:2: (iv_ruleMethodOrFieldAddition= ruleMethodOrFieldAddition EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3316:2: iv_ruleMethodOrFieldAddition= ruleMethodOrFieldAddition EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getMethodOrFieldAdditionRule()); 
            }
            pushFollow(FOLLOW_ruleMethodOrFieldAddition_in_entryRuleMethodOrFieldAddition7595);
            iv_ruleMethodOrFieldAddition=ruleMethodOrFieldAddition();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleMethodOrFieldAddition; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleMethodOrFieldAddition7605); if (state.failed) return current;

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
    // $ANTLR end "entryRuleMethodOrFieldAddition"


    // $ANTLR start "ruleMethodOrFieldAddition"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3323:1: ruleMethodOrFieldAddition returns [EObject current=null] : (this_FieldAddition_0= ruleFieldAddition | this_MethodAddition_1= ruleMethodAddition ) ;
    public final EObject ruleMethodOrFieldAddition() throws RecognitionException {
        EObject current = null;

        EObject this_FieldAddition_0 = null;

        EObject this_MethodAddition_1 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3326:28: ( (this_FieldAddition_0= ruleFieldAddition | this_MethodAddition_1= ruleMethodAddition ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3327:1: (this_FieldAddition_0= ruleFieldAddition | this_MethodAddition_1= ruleMethodAddition )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3327:1: (this_FieldAddition_0= ruleFieldAddition | this_MethodAddition_1= ruleMethodAddition )
            int alt43=2;
            int LA43_0 = input.LA(1);

            if ( (LA43_0==49) ) {
                switch ( input.LA(2) ) {
                case 15:
                    {
                    int LA43_2 = input.LA(3);

                    if ( (LA43_2==RULE_ID) ) {
                        int LA43_7 = input.LA(4);

                        if ( (LA43_7==23) ) {
                            alt43=2;
                        }
                        else if ( (LA43_7==22) ) {
                            alt43=1;
                        }
                        else {
                            if (state.backtracking>0) {state.failed=true; return current;}
                            NoViableAltException nvae =
                                new NoViableAltException("", 43, 7, input);

                            throw nvae;
                        }
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return current;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 43, 2, input);

                        throw nvae;
                    }
                    }
                    break;
                case 16:
                    {
                    int LA43_3 = input.LA(3);

                    if ( (LA43_3==RULE_ID) ) {
                        int LA43_7 = input.LA(4);

                        if ( (LA43_7==23) ) {
                            alt43=2;
                        }
                        else if ( (LA43_7==22) ) {
                            alt43=1;
                        }
                        else {
                            if (state.backtracking>0) {state.failed=true; return current;}
                            NoViableAltException nvae =
                                new NoViableAltException("", 43, 7, input);

                            throw nvae;
                        }
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return current;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 43, 3, input);

                        throw nvae;
                    }
                    }
                    break;
                case 17:
                    {
                    int LA43_4 = input.LA(3);

                    if ( (LA43_4==RULE_ID) ) {
                        int LA43_7 = input.LA(4);

                        if ( (LA43_7==23) ) {
                            alt43=2;
                        }
                        else if ( (LA43_7==22) ) {
                            alt43=1;
                        }
                        else {
                            if (state.backtracking>0) {state.failed=true; return current;}
                            NoViableAltException nvae =
                                new NoViableAltException("", 43, 7, input);

                            throw nvae;
                        }
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return current;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 43, 4, input);

                        throw nvae;
                    }
                    }
                    break;
                case RULE_ID:
                    {
                    int LA43_5 = input.LA(3);

                    if ( (LA43_5==RULE_ID) ) {
                        int LA43_7 = input.LA(4);

                        if ( (LA43_7==23) ) {
                            alt43=2;
                        }
                        else if ( (LA43_7==22) ) {
                            alt43=1;
                        }
                        else {
                            if (state.backtracking>0) {state.failed=true; return current;}
                            NoViableAltException nvae =
                                new NoViableAltException("", 43, 7, input);

                            throw nvae;
                        }
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return current;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 43, 5, input);

                        throw nvae;
                    }
                    }
                    break;
                case 14:
                    {
                    alt43=2;
                    }
                    break;
                default:
                    if (state.backtracking>0) {state.failed=true; return current;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 43, 1, input);

                    throw nvae;
                }

            }
            else {
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 43, 0, input);

                throw nvae;
            }
            switch (alt43) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3328:2: this_FieldAddition_0= ruleFieldAddition
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getMethodOrFieldAdditionAccess().getFieldAdditionParserRuleCall_0()); 
                          
                    }
                    pushFollow(FOLLOW_ruleFieldAddition_in_ruleMethodOrFieldAddition7655);
                    this_FieldAddition_0=ruleFieldAddition();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_FieldAddition_0; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3341:2: this_MethodAddition_1= ruleMethodAddition
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {
                       
                              newCompositeNode(grammarAccess.getMethodOrFieldAdditionAccess().getMethodAdditionParserRuleCall_1()); 
                          
                    }
                    pushFollow(FOLLOW_ruleMethodAddition_in_ruleMethodOrFieldAddition7685);
                    this_MethodAddition_1=ruleMethodAddition();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {
                       
                              current = this_MethodAddition_1; 
                              afterParserOrEnumRuleCall();
                          
                    }

                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleMethodOrFieldAddition"


    // $ANTLR start "entryRuleFieldAddition"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3360:1: entryRuleFieldAddition returns [EObject current=null] : iv_ruleFieldAddition= ruleFieldAddition EOF ;
    public final EObject entryRuleFieldAddition() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleFieldAddition = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3361:2: (iv_ruleFieldAddition= ruleFieldAddition EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3362:2: iv_ruleFieldAddition= ruleFieldAddition EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getFieldAdditionRule()); 
            }
            pushFollow(FOLLOW_ruleFieldAddition_in_entryRuleFieldAddition7720);
            iv_ruleFieldAddition=ruleFieldAddition();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleFieldAddition; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleFieldAddition7730); if (state.failed) return current;

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
    // $ANTLR end "entryRuleFieldAddition"


    // $ANTLR start "ruleFieldAddition"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3369:1: ruleFieldAddition returns [EObject current=null] : (otherlv_0= 'adds' ( (lv_field_1_0= ruleField ) ) ) ;
    public final EObject ruleFieldAddition() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        EObject lv_field_1_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3372:28: ( (otherlv_0= 'adds' ( (lv_field_1_0= ruleField ) ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3373:1: (otherlv_0= 'adds' ( (lv_field_1_0= ruleField ) ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3373:1: (otherlv_0= 'adds' ( (lv_field_1_0= ruleField ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3373:3: otherlv_0= 'adds' ( (lv_field_1_0= ruleField ) )
            {
            otherlv_0=(Token)match(input,49,FOLLOW_49_in_ruleFieldAddition7767); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getFieldAdditionAccess().getAddsKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3377:1: ( (lv_field_1_0= ruleField ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3378:1: (lv_field_1_0= ruleField )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3378:1: (lv_field_1_0= ruleField )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3379:3: lv_field_1_0= ruleField
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getFieldAdditionAccess().getFieldFieldParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleField_in_ruleFieldAddition7788);
            lv_field_1_0=ruleField();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getFieldAdditionRule());
              	        }
                     		set(
                     			current, 
                     			"field",
                      		lv_field_1_0, 
                      		"Field");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleFieldAddition"


    // $ANTLR start "entryRuleMethodAddition"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3403:1: entryRuleMethodAddition returns [EObject current=null] : iv_ruleMethodAddition= ruleMethodAddition EOF ;
    public final EObject entryRuleMethodAddition() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMethodAddition = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3404:2: (iv_ruleMethodAddition= ruleMethodAddition EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3405:2: iv_ruleMethodAddition= ruleMethodAddition EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getMethodAdditionRule()); 
            }
            pushFollow(FOLLOW_ruleMethodAddition_in_entryRuleMethodAddition7824);
            iv_ruleMethodAddition=ruleMethodAddition();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleMethodAddition; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleMethodAddition7834); if (state.failed) return current;

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
    // $ANTLR end "entryRuleMethodAddition"


    // $ANTLR start "ruleMethodAddition"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3412:1: ruleMethodAddition returns [EObject current=null] : (otherlv_0= 'adds' ( (lv_method_1_0= ruleMethod ) ) ) ;
    public final EObject ruleMethodAddition() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        EObject lv_method_1_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3415:28: ( (otherlv_0= 'adds' ( (lv_method_1_0= ruleMethod ) ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3416:1: (otherlv_0= 'adds' ( (lv_method_1_0= ruleMethod ) ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3416:1: (otherlv_0= 'adds' ( (lv_method_1_0= ruleMethod ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3416:3: otherlv_0= 'adds' ( (lv_method_1_0= ruleMethod ) )
            {
            otherlv_0=(Token)match(input,49,FOLLOW_49_in_ruleMethodAddition7871); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getMethodAdditionAccess().getAddsKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3420:1: ( (lv_method_1_0= ruleMethod ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3421:1: (lv_method_1_0= ruleMethod )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3421:1: (lv_method_1_0= ruleMethod )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3422:3: lv_method_1_0= ruleMethod
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getMethodAdditionAccess().getMethodMethodParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleMethod_in_ruleMethodAddition7892);
            lv_method_1_0=ruleMethod();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getMethodAdditionRule());
              	        }
                     		set(
                     			current, 
                     			"method",
                      		lv_method_1_0, 
                      		"Method");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleMethodAddition"


    // $ANTLR start "entryRuleFieldRemoval"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3446:1: entryRuleFieldRemoval returns [EObject current=null] : iv_ruleFieldRemoval= ruleFieldRemoval EOF ;
    public final EObject entryRuleFieldRemoval() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleFieldRemoval = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3447:2: (iv_ruleFieldRemoval= ruleFieldRemoval EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3448:2: iv_ruleFieldRemoval= ruleFieldRemoval EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getFieldRemovalRule()); 
            }
            pushFollow(FOLLOW_ruleFieldRemoval_in_entryRuleFieldRemoval7928);
            iv_ruleFieldRemoval=ruleFieldRemoval();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleFieldRemoval; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleFieldRemoval7938); if (state.failed) return current;

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
    // $ANTLR end "entryRuleFieldRemoval"


    // $ANTLR start "ruleFieldRemoval"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3455:1: ruleFieldRemoval returns [EObject current=null] : (otherlv_0= 'removesField' ( (lv_name_1_0= ruleFieldName ) ) otherlv_2= ';' ) ;
    public final EObject ruleFieldRemoval() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        AntlrDatatypeRuleToken lv_name_1_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3458:28: ( (otherlv_0= 'removesField' ( (lv_name_1_0= ruleFieldName ) ) otherlv_2= ';' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3459:1: (otherlv_0= 'removesField' ( (lv_name_1_0= ruleFieldName ) ) otherlv_2= ';' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3459:1: (otherlv_0= 'removesField' ( (lv_name_1_0= ruleFieldName ) ) otherlv_2= ';' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3459:3: otherlv_0= 'removesField' ( (lv_name_1_0= ruleFieldName ) ) otherlv_2= ';'
            {
            otherlv_0=(Token)match(input,53,FOLLOW_53_in_ruleFieldRemoval7975); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getFieldRemovalAccess().getRemovesFieldKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3463:1: ( (lv_name_1_0= ruleFieldName ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3464:1: (lv_name_1_0= ruleFieldName )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3464:1: (lv_name_1_0= ruleFieldName )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3465:3: lv_name_1_0= ruleFieldName
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getFieldRemovalAccess().getNameFieldNameParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleFieldName_in_ruleFieldRemoval7996);
            lv_name_1_0=ruleFieldName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getFieldRemovalRule());
              	        }
                     		set(
                     			current, 
                     			"name",
                      		lv_name_1_0, 
                      		"FieldName");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            otherlv_2=(Token)match(input,22,FOLLOW_22_in_ruleFieldRemoval8008); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getFieldRemovalAccess().getSemicolonKeyword_2());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleFieldRemoval"


    // $ANTLR start "entryRuleMethodRemoval"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3493:1: entryRuleMethodRemoval returns [EObject current=null] : iv_ruleMethodRemoval= ruleMethodRemoval EOF ;
    public final EObject entryRuleMethodRemoval() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMethodRemoval = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3494:2: (iv_ruleMethodRemoval= ruleMethodRemoval EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3495:2: iv_ruleMethodRemoval= ruleMethodRemoval EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getMethodRemovalRule()); 
            }
            pushFollow(FOLLOW_ruleMethodRemoval_in_entryRuleMethodRemoval8044);
            iv_ruleMethodRemoval=ruleMethodRemoval();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleMethodRemoval; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleMethodRemoval8054); if (state.failed) return current;

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
    // $ANTLR end "entryRuleMethodRemoval"


    // $ANTLR start "ruleMethodRemoval"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3502:1: ruleMethodRemoval returns [EObject current=null] : (otherlv_0= 'removesMethod' ( (lv_name_1_0= ruleMethodName ) ) otherlv_2= ';' ) ;
    public final EObject ruleMethodRemoval() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        AntlrDatatypeRuleToken lv_name_1_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3505:28: ( (otherlv_0= 'removesMethod' ( (lv_name_1_0= ruleMethodName ) ) otherlv_2= ';' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3506:1: (otherlv_0= 'removesMethod' ( (lv_name_1_0= ruleMethodName ) ) otherlv_2= ';' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3506:1: (otherlv_0= 'removesMethod' ( (lv_name_1_0= ruleMethodName ) ) otherlv_2= ';' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3506:3: otherlv_0= 'removesMethod' ( (lv_name_1_0= ruleMethodName ) ) otherlv_2= ';'
            {
            otherlv_0=(Token)match(input,54,FOLLOW_54_in_ruleMethodRemoval8091); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getMethodRemovalAccess().getRemovesMethodKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3510:1: ( (lv_name_1_0= ruleMethodName ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3511:1: (lv_name_1_0= ruleMethodName )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3511:1: (lv_name_1_0= ruleMethodName )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3512:3: lv_name_1_0= ruleMethodName
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getMethodRemovalAccess().getNameMethodNameParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleMethodName_in_ruleMethodRemoval8112);
            lv_name_1_0=ruleMethodName();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getMethodRemovalRule());
              	        }
                     		set(
                     			current, 
                     			"name",
                      		lv_name_1_0, 
                      		"MethodName");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            otherlv_2=(Token)match(input,22,FOLLOW_22_in_ruleMethodRemoval8124); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getMethodRemovalAccess().getSemicolonKeyword_2());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleMethodRemoval"


    // $ANTLR start "entryRuleMethodModification"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3540:1: entryRuleMethodModification returns [EObject current=null] : iv_ruleMethodModification= ruleMethodModification EOF ;
    public final EObject entryRuleMethodModification() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleMethodModification = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3541:2: (iv_ruleMethodModification= ruleMethodModification EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3542:2: iv_ruleMethodModification= ruleMethodModification EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getMethodModificationRule()); 
            }
            pushFollow(FOLLOW_ruleMethodModification_in_entryRuleMethodModification8160);
            iv_ruleMethodModification=ruleMethodModification();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleMethodModification; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleMethodModification8170); if (state.failed) return current;

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
    // $ANTLR end "entryRuleMethodModification"


    // $ANTLR start "ruleMethodModification"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3549:1: ruleMethodModification returns [EObject current=null] : (otherlv_0= 'modifies' ( (lv_method_1_0= ruleMethod ) ) ) ;
    public final EObject ruleMethodModification() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        EObject lv_method_1_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3552:28: ( (otherlv_0= 'modifies' ( (lv_method_1_0= ruleMethod ) ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3553:1: (otherlv_0= 'modifies' ( (lv_method_1_0= ruleMethod ) ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3553:1: (otherlv_0= 'modifies' ( (lv_method_1_0= ruleMethod ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3553:3: otherlv_0= 'modifies' ( (lv_method_1_0= ruleMethod ) )
            {
            otherlv_0=(Token)match(input,51,FOLLOW_51_in_ruleMethodModification8207); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getMethodModificationAccess().getModifiesKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3557:1: ( (lv_method_1_0= ruleMethod ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3558:1: (lv_method_1_0= ruleMethod )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3558:1: (lv_method_1_0= ruleMethod )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3559:3: lv_method_1_0= ruleMethod
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getMethodModificationAccess().getMethodMethodParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleMethod_in_ruleMethodModification8228);
            lv_method_1_0=ruleMethod();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getMethodModificationRule());
              	        }
                     		set(
                     			current, 
                     			"method",
                      		lv_method_1_0, 
                      		"Method");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleMethodModification"


    // $ANTLR start "entryRuleProductLine"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3583:1: entryRuleProductLine returns [EObject current=null] : iv_ruleProductLine= ruleProductLine EOF ;
    public final EObject entryRuleProductLine() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleProductLine = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3584:2: (iv_ruleProductLine= ruleProductLine EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3585:2: iv_ruleProductLine= ruleProductLine EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getProductLineRule()); 
            }
            pushFollow(FOLLOW_ruleProductLine_in_entryRuleProductLine8264);
            iv_ruleProductLine=ruleProductLine();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleProductLine; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleProductLine8274); if (state.failed) return current;

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
    // $ANTLR end "entryRuleProductLine"


    // $ANTLR start "ruleProductLine"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3592:1: ruleProductLine returns [EObject current=null] : (otherlv_0= 'spl' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '{' ( (lv_features_3_0= ruleFeatures ) ) ( (lv_configurations_4_0= ruleConfigurations ) ) ( (lv_partition_5_0= ruleDeltaPartition ) ) otherlv_6= '}' ) ;
    public final EObject ruleProductLine() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token lv_name_1_0=null;
        Token otherlv_2=null;
        Token otherlv_6=null;
        EObject lv_features_3_0 = null;

        EObject lv_configurations_4_0 = null;

        EObject lv_partition_5_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3595:28: ( (otherlv_0= 'spl' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '{' ( (lv_features_3_0= ruleFeatures ) ) ( (lv_configurations_4_0= ruleConfigurations ) ) ( (lv_partition_5_0= ruleDeltaPartition ) ) otherlv_6= '}' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3596:1: (otherlv_0= 'spl' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '{' ( (lv_features_3_0= ruleFeatures ) ) ( (lv_configurations_4_0= ruleConfigurations ) ) ( (lv_partition_5_0= ruleDeltaPartition ) ) otherlv_6= '}' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3596:1: (otherlv_0= 'spl' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '{' ( (lv_features_3_0= ruleFeatures ) ) ( (lv_configurations_4_0= ruleConfigurations ) ) ( (lv_partition_5_0= ruleDeltaPartition ) ) otherlv_6= '}' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3596:3: otherlv_0= 'spl' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= '{' ( (lv_features_3_0= ruleFeatures ) ) ( (lv_configurations_4_0= ruleConfigurations ) ) ( (lv_partition_5_0= ruleDeltaPartition ) ) otherlv_6= '}'
            {
            otherlv_0=(Token)match(input,55,FOLLOW_55_in_ruleProductLine8311); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getProductLineAccess().getSplKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3600:1: ( (lv_name_1_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3601:1: (lv_name_1_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3601:1: (lv_name_1_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3602:3: lv_name_1_0= RULE_ID
            {
            lv_name_1_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleProductLine8328); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_name_1_0, grammarAccess.getProductLineAccess().getNameIDTerminalRuleCall_1_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getProductLineRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"name",
                      		lv_name_1_0, 
                      		"ID");
              	    
            }

            }


            }

            otherlv_2=(Token)match(input,20,FOLLOW_20_in_ruleProductLine8345); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getProductLineAccess().getLeftCurlyBracketKeyword_2());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3622:1: ( (lv_features_3_0= ruleFeatures ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3623:1: (lv_features_3_0= ruleFeatures )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3623:1: (lv_features_3_0= ruleFeatures )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3624:3: lv_features_3_0= ruleFeatures
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getProductLineAccess().getFeaturesFeaturesParserRuleCall_3_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleFeatures_in_ruleProductLine8366);
            lv_features_3_0=ruleFeatures();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getProductLineRule());
              	        }
                     		set(
                     			current, 
                     			"features",
                      		lv_features_3_0, 
                      		"Features");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3640:2: ( (lv_configurations_4_0= ruleConfigurations ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3641:1: (lv_configurations_4_0= ruleConfigurations )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3641:1: (lv_configurations_4_0= ruleConfigurations )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3642:3: lv_configurations_4_0= ruleConfigurations
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getProductLineAccess().getConfigurationsConfigurationsParserRuleCall_4_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleConfigurations_in_ruleProductLine8387);
            lv_configurations_4_0=ruleConfigurations();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getProductLineRule());
              	        }
                     		set(
                     			current, 
                     			"configurations",
                      		lv_configurations_4_0, 
                      		"Configurations");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3658:2: ( (lv_partition_5_0= ruleDeltaPartition ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3659:1: (lv_partition_5_0= ruleDeltaPartition )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3659:1: (lv_partition_5_0= ruleDeltaPartition )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3660:3: lv_partition_5_0= ruleDeltaPartition
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getProductLineAccess().getPartitionDeltaPartitionParserRuleCall_5_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleDeltaPartition_in_ruleProductLine8408);
            lv_partition_5_0=ruleDeltaPartition();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getProductLineRule());
              	        }
                     		set(
                     			current, 
                     			"partition",
                      		lv_partition_5_0, 
                      		"DeltaPartition");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            otherlv_6=(Token)match(input,21,FOLLOW_21_in_ruleProductLine8420); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_6, grammarAccess.getProductLineAccess().getRightCurlyBracketKeyword_6());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleProductLine"


    // $ANTLR start "entryRuleFeatures"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3688:1: entryRuleFeatures returns [EObject current=null] : iv_ruleFeatures= ruleFeatures EOF ;
    public final EObject entryRuleFeatures() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleFeatures = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3689:2: (iv_ruleFeatures= ruleFeatures EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3690:2: iv_ruleFeatures= ruleFeatures EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getFeaturesRule()); 
            }
            pushFollow(FOLLOW_ruleFeatures_in_entryRuleFeatures8456);
            iv_ruleFeatures=ruleFeatures();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleFeatures; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleFeatures8466); if (state.failed) return current;

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
    // $ANTLR end "entryRuleFeatures"


    // $ANTLR start "ruleFeatures"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3697:1: ruleFeatures returns [EObject current=null] : (otherlv_0= 'features' ( ( (lv_featuresList_1_0= ruleFeature ) ) (otherlv_2= ',' ( (lv_featuresList_3_0= ruleFeature ) ) )* ) ) ;
    public final EObject ruleFeatures() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        EObject lv_featuresList_1_0 = null;

        EObject lv_featuresList_3_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3700:28: ( (otherlv_0= 'features' ( ( (lv_featuresList_1_0= ruleFeature ) ) (otherlv_2= ',' ( (lv_featuresList_3_0= ruleFeature ) ) )* ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3701:1: (otherlv_0= 'features' ( ( (lv_featuresList_1_0= ruleFeature ) ) (otherlv_2= ',' ( (lv_featuresList_3_0= ruleFeature ) ) )* ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3701:1: (otherlv_0= 'features' ( ( (lv_featuresList_1_0= ruleFeature ) ) (otherlv_2= ',' ( (lv_featuresList_3_0= ruleFeature ) ) )* ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3701:3: otherlv_0= 'features' ( ( (lv_featuresList_1_0= ruleFeature ) ) (otherlv_2= ',' ( (lv_featuresList_3_0= ruleFeature ) ) )* )
            {
            otherlv_0=(Token)match(input,56,FOLLOW_56_in_ruleFeatures8503); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getFeaturesAccess().getFeaturesKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3705:1: ( ( (lv_featuresList_1_0= ruleFeature ) ) (otherlv_2= ',' ( (lv_featuresList_3_0= ruleFeature ) ) )* )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3705:2: ( (lv_featuresList_1_0= ruleFeature ) ) (otherlv_2= ',' ( (lv_featuresList_3_0= ruleFeature ) ) )*
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3705:2: ( (lv_featuresList_1_0= ruleFeature ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3706:1: (lv_featuresList_1_0= ruleFeature )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3706:1: (lv_featuresList_1_0= ruleFeature )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3707:3: lv_featuresList_1_0= ruleFeature
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getFeaturesAccess().getFeaturesListFeatureParserRuleCall_1_0_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleFeature_in_ruleFeatures8525);
            lv_featuresList_1_0=ruleFeature();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getFeaturesRule());
              	        }
                     		add(
                     			current, 
                     			"featuresList",
                      		lv_featuresList_1_0, 
                      		"Feature");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3723:2: (otherlv_2= ',' ( (lv_featuresList_3_0= ruleFeature ) ) )*
            loop44:
            do {
                int alt44=2;
                int LA44_0 = input.LA(1);

                if ( (LA44_0==24) ) {
                    alt44=1;
                }


                switch (alt44) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3723:4: otherlv_2= ',' ( (lv_featuresList_3_0= ruleFeature ) )
            	    {
            	    otherlv_2=(Token)match(input,24,FOLLOW_24_in_ruleFeatures8538); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	          	newLeafNode(otherlv_2, grammarAccess.getFeaturesAccess().getCommaKeyword_1_1_0());
            	          
            	    }
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3727:1: ( (lv_featuresList_3_0= ruleFeature ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3728:1: (lv_featuresList_3_0= ruleFeature )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3728:1: (lv_featuresList_3_0= ruleFeature )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3729:3: lv_featuresList_3_0= ruleFeature
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getFeaturesAccess().getFeaturesListFeatureParserRuleCall_1_1_1_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleFeature_in_ruleFeatures8559);
            	    lv_featuresList_3_0=ruleFeature();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getFeaturesRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"featuresList",
            	              		lv_featuresList_3_0, 
            	              		"Feature");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop44;
                }
            } while (true);


            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleFeatures"


    // $ANTLR start "entryRuleFeature"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3753:1: entryRuleFeature returns [EObject current=null] : iv_ruleFeature= ruleFeature EOF ;
    public final EObject entryRuleFeature() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleFeature = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3754:2: (iv_ruleFeature= ruleFeature EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3755:2: iv_ruleFeature= ruleFeature EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getFeatureRule()); 
            }
            pushFollow(FOLLOW_ruleFeature_in_entryRuleFeature8598);
            iv_ruleFeature=ruleFeature();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleFeature; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleFeature8608); if (state.failed) return current;

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
    // $ANTLR end "entryRuleFeature"


    // $ANTLR start "ruleFeature"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3762:1: ruleFeature returns [EObject current=null] : ( (lv_name_0_0= RULE_ID ) ) ;
    public final EObject ruleFeature() throws RecognitionException {
        EObject current = null;

        Token lv_name_0_0=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3765:28: ( ( (lv_name_0_0= RULE_ID ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3766:1: ( (lv_name_0_0= RULE_ID ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3766:1: ( (lv_name_0_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3767:1: (lv_name_0_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3767:1: (lv_name_0_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3768:3: lv_name_0_0= RULE_ID
            {
            lv_name_0_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleFeature8649); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_name_0_0, grammarAccess.getFeatureAccess().getNameIDTerminalRuleCall_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getFeatureRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"name",
                      		lv_name_0_0, 
                      		"ID");
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleFeature"


    // $ANTLR start "entryRuleConfigurations"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3792:1: entryRuleConfigurations returns [EObject current=null] : iv_ruleConfigurations= ruleConfigurations EOF ;
    public final EObject entryRuleConfigurations() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleConfigurations = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3793:2: (iv_ruleConfigurations= ruleConfigurations EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3794:2: iv_ruleConfigurations= ruleConfigurations EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getConfigurationsRule()); 
            }
            pushFollow(FOLLOW_ruleConfigurations_in_entryRuleConfigurations8689);
            iv_ruleConfigurations=ruleConfigurations();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleConfigurations; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleConfigurations8699); if (state.failed) return current;

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
    // $ANTLR end "entryRuleConfigurations"


    // $ANTLR start "ruleConfigurations"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3801:1: ruleConfigurations returns [EObject current=null] : (otherlv_0= 'configurations' ( (lv_configurations_1_0= ruleConfiguration ) ) (otherlv_2= ';' ( (lv_configurations_3_0= ruleConfiguration ) ) )* ) ;
    public final EObject ruleConfigurations() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        EObject lv_configurations_1_0 = null;

        EObject lv_configurations_3_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3804:28: ( (otherlv_0= 'configurations' ( (lv_configurations_1_0= ruleConfiguration ) ) (otherlv_2= ';' ( (lv_configurations_3_0= ruleConfiguration ) ) )* ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3805:1: (otherlv_0= 'configurations' ( (lv_configurations_1_0= ruleConfiguration ) ) (otherlv_2= ';' ( (lv_configurations_3_0= ruleConfiguration ) ) )* )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3805:1: (otherlv_0= 'configurations' ( (lv_configurations_1_0= ruleConfiguration ) ) (otherlv_2= ';' ( (lv_configurations_3_0= ruleConfiguration ) ) )* )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3805:3: otherlv_0= 'configurations' ( (lv_configurations_1_0= ruleConfiguration ) ) (otherlv_2= ';' ( (lv_configurations_3_0= ruleConfiguration ) ) )*
            {
            otherlv_0=(Token)match(input,57,FOLLOW_57_in_ruleConfigurations8736); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getConfigurationsAccess().getConfigurationsKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3809:1: ( (lv_configurations_1_0= ruleConfiguration ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3810:1: (lv_configurations_1_0= ruleConfiguration )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3810:1: (lv_configurations_1_0= ruleConfiguration )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3811:3: lv_configurations_1_0= ruleConfiguration
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getConfigurationsAccess().getConfigurationsConfigurationParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleConfiguration_in_ruleConfigurations8757);
            lv_configurations_1_0=ruleConfiguration();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getConfigurationsRule());
              	        }
                     		add(
                     			current, 
                     			"configurations",
                      		lv_configurations_1_0, 
                      		"Configuration");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3827:2: (otherlv_2= ';' ( (lv_configurations_3_0= ruleConfiguration ) ) )*
            loop45:
            do {
                int alt45=2;
                int LA45_0 = input.LA(1);

                if ( (LA45_0==22) ) {
                    alt45=1;
                }


                switch (alt45) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3827:4: otherlv_2= ';' ( (lv_configurations_3_0= ruleConfiguration ) )
            	    {
            	    otherlv_2=(Token)match(input,22,FOLLOW_22_in_ruleConfigurations8770); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	          	newLeafNode(otherlv_2, grammarAccess.getConfigurationsAccess().getSemicolonKeyword_2_0());
            	          
            	    }
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3831:1: ( (lv_configurations_3_0= ruleConfiguration ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3832:1: (lv_configurations_3_0= ruleConfiguration )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3832:1: (lv_configurations_3_0= ruleConfiguration )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3833:3: lv_configurations_3_0= ruleConfiguration
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getConfigurationsAccess().getConfigurationsConfigurationParserRuleCall_2_1_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleConfiguration_in_ruleConfigurations8791);
            	    lv_configurations_3_0=ruleConfiguration();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getConfigurationsRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"configurations",
            	              		lv_configurations_3_0, 
            	              		"Configuration");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop45;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleConfigurations"


    // $ANTLR start "entryRuleConfiguration"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3857:1: entryRuleConfiguration returns [EObject current=null] : iv_ruleConfiguration= ruleConfiguration EOF ;
    public final EObject entryRuleConfiguration() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleConfiguration = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3858:2: (iv_ruleConfiguration= ruleConfiguration EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3859:2: iv_ruleConfiguration= ruleConfiguration EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getConfigurationRule()); 
            }
            pushFollow(FOLLOW_ruleConfiguration_in_entryRuleConfiguration8829);
            iv_ruleConfiguration=ruleConfiguration();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleConfiguration; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleConfiguration8839); if (state.failed) return current;

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
    // $ANTLR end "entryRuleConfiguration"


    // $ANTLR start "ruleConfiguration"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3866:1: ruleConfiguration returns [EObject current=null] : ( (lv_formula_0_0= rulePropositionalFormula ) ) ;
    public final EObject ruleConfiguration() throws RecognitionException {
        EObject current = null;

        EObject lv_formula_0_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3869:28: ( ( (lv_formula_0_0= rulePropositionalFormula ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3870:1: ( (lv_formula_0_0= rulePropositionalFormula ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3870:1: ( (lv_formula_0_0= rulePropositionalFormula ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3871:1: (lv_formula_0_0= rulePropositionalFormula )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3871:1: (lv_formula_0_0= rulePropositionalFormula )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3872:3: lv_formula_0_0= rulePropositionalFormula
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getConfigurationAccess().getFormulaPropositionalFormulaParserRuleCall_0()); 
              	    
            }
            pushFollow(FOLLOW_rulePropositionalFormula_in_ruleConfiguration8884);
            lv_formula_0_0=rulePropositionalFormula();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getConfigurationRule());
              	        }
                     		set(
                     			current, 
                     			"formula",
                      		lv_formula_0_0, 
                      		"PropositionalFormula");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleConfiguration"


    // $ANTLR start "entryRuleDeltaPartition"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3896:1: entryRuleDeltaPartition returns [EObject current=null] : iv_ruleDeltaPartition= ruleDeltaPartition EOF ;
    public final EObject entryRuleDeltaPartition() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleDeltaPartition = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3897:2: (iv_ruleDeltaPartition= ruleDeltaPartition EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3898:2: iv_ruleDeltaPartition= ruleDeltaPartition EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getDeltaPartitionRule()); 
            }
            pushFollow(FOLLOW_ruleDeltaPartition_in_entryRuleDeltaPartition8919);
            iv_ruleDeltaPartition=ruleDeltaPartition();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleDeltaPartition; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleDeltaPartition8929); if (state.failed) return current;

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
    // $ANTLR end "entryRuleDeltaPartition"


    // $ANTLR start "ruleDeltaPartition"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3905:1: ruleDeltaPartition returns [EObject current=null] : (otherlv_0= 'deltas' ( (lv_parts_1_0= rulePartitionPart ) )+ ) ;
    public final EObject ruleDeltaPartition() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        EObject lv_parts_1_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3908:28: ( (otherlv_0= 'deltas' ( (lv_parts_1_0= rulePartitionPart ) )+ ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3909:1: (otherlv_0= 'deltas' ( (lv_parts_1_0= rulePartitionPart ) )+ )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3909:1: (otherlv_0= 'deltas' ( (lv_parts_1_0= rulePartitionPart ) )+ )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3909:3: otherlv_0= 'deltas' ( (lv_parts_1_0= rulePartitionPart ) )+
            {
            otherlv_0=(Token)match(input,58,FOLLOW_58_in_ruleDeltaPartition8966); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getDeltaPartitionAccess().getDeltasKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3913:1: ( (lv_parts_1_0= rulePartitionPart ) )+
            int cnt46=0;
            loop46:
            do {
                int alt46=2;
                int LA46_0 = input.LA(1);

                if ( (LA46_0==59) ) {
                    alt46=1;
                }


                switch (alt46) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3914:1: (lv_parts_1_0= rulePartitionPart )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3914:1: (lv_parts_1_0= rulePartitionPart )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3915:3: lv_parts_1_0= rulePartitionPart
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getDeltaPartitionAccess().getPartsPartitionPartParserRuleCall_1_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_rulePartitionPart_in_ruleDeltaPartition8987);
            	    lv_parts_1_0=rulePartitionPart();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getDeltaPartitionRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"parts",
            	              		lv_parts_1_0, 
            	              		"PartitionPart");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    if ( cnt46 >= 1 ) break loop46;
            	    if (state.backtracking>0) {state.failed=true; return current;}
                        EarlyExitException eee =
                            new EarlyExitException(46, input);
                        throw eee;
                }
                cnt46++;
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleDeltaPartition"


    // $ANTLR start "entryRulePartitionPart"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3939:1: entryRulePartitionPart returns [EObject current=null] : iv_rulePartitionPart= rulePartitionPart EOF ;
    public final EObject entryRulePartitionPart() throws RecognitionException {
        EObject current = null;

        EObject iv_rulePartitionPart = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3940:2: (iv_rulePartitionPart= rulePartitionPart EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3941:2: iv_rulePartitionPart= rulePartitionPart EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getPartitionPartRule()); 
            }
            pushFollow(FOLLOW_rulePartitionPart_in_entryRulePartitionPart9024);
            iv_rulePartitionPart=rulePartitionPart();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_rulePartitionPart; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRulePartitionPart9034); if (state.failed) return current;

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
    // $ANTLR end "entryRulePartitionPart"


    // $ANTLR start "rulePartitionPart"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3948:1: rulePartitionPart returns [EObject current=null] : (otherlv_0= '[' ( (lv_moduleReferences_1_0= ruleModuleReference ) ) (otherlv_2= ',' ( (lv_moduleReferences_3_0= ruleModuleReference ) ) )* otherlv_4= ']' ) ;
    public final EObject rulePartitionPart() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_2=null;
        Token otherlv_4=null;
        EObject lv_moduleReferences_1_0 = null;

        EObject lv_moduleReferences_3_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3951:28: ( (otherlv_0= '[' ( (lv_moduleReferences_1_0= ruleModuleReference ) ) (otherlv_2= ',' ( (lv_moduleReferences_3_0= ruleModuleReference ) ) )* otherlv_4= ']' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3952:1: (otherlv_0= '[' ( (lv_moduleReferences_1_0= ruleModuleReference ) ) (otherlv_2= ',' ( (lv_moduleReferences_3_0= ruleModuleReference ) ) )* otherlv_4= ']' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3952:1: (otherlv_0= '[' ( (lv_moduleReferences_1_0= ruleModuleReference ) ) (otherlv_2= ',' ( (lv_moduleReferences_3_0= ruleModuleReference ) ) )* otherlv_4= ']' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3952:3: otherlv_0= '[' ( (lv_moduleReferences_1_0= ruleModuleReference ) ) (otherlv_2= ',' ( (lv_moduleReferences_3_0= ruleModuleReference ) ) )* otherlv_4= ']'
            {
            otherlv_0=(Token)match(input,59,FOLLOW_59_in_rulePartitionPart9071); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getPartitionPartAccess().getLeftSquareBracketKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3956:1: ( (lv_moduleReferences_1_0= ruleModuleReference ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3957:1: (lv_moduleReferences_1_0= ruleModuleReference )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3957:1: (lv_moduleReferences_1_0= ruleModuleReference )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3958:3: lv_moduleReferences_1_0= ruleModuleReference
            {
            if ( state.backtracking==0 ) {
               
              	        newCompositeNode(grammarAccess.getPartitionPartAccess().getModuleReferencesModuleReferenceParserRuleCall_1_0()); 
              	    
            }
            pushFollow(FOLLOW_ruleModuleReference_in_rulePartitionPart9092);
            lv_moduleReferences_1_0=ruleModuleReference();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElementForParent(grammarAccess.getPartitionPartRule());
              	        }
                     		add(
                     			current, 
                     			"moduleReferences",
                      		lv_moduleReferences_1_0, 
                      		"ModuleReference");
              	        afterParserOrEnumRuleCall();
              	    
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3974:2: (otherlv_2= ',' ( (lv_moduleReferences_3_0= ruleModuleReference ) ) )*
            loop47:
            do {
                int alt47=2;
                int LA47_0 = input.LA(1);

                if ( (LA47_0==24) ) {
                    alt47=1;
                }


                switch (alt47) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3974:4: otherlv_2= ',' ( (lv_moduleReferences_3_0= ruleModuleReference ) )
            	    {
            	    otherlv_2=(Token)match(input,24,FOLLOW_24_in_rulePartitionPart9105); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	          	newLeafNode(otherlv_2, grammarAccess.getPartitionPartAccess().getCommaKeyword_2_0());
            	          
            	    }
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3978:1: ( (lv_moduleReferences_3_0= ruleModuleReference ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3979:1: (lv_moduleReferences_3_0= ruleModuleReference )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3979:1: (lv_moduleReferences_3_0= ruleModuleReference )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:3980:3: lv_moduleReferences_3_0= ruleModuleReference
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getPartitionPartAccess().getModuleReferencesModuleReferenceParserRuleCall_2_1_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleModuleReference_in_rulePartitionPart9126);
            	    lv_moduleReferences_3_0=ruleModuleReference();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getPartitionPartRule());
            	      	        }
            	             		add(
            	             			current, 
            	             			"moduleReferences",
            	              		lv_moduleReferences_3_0, 
            	              		"ModuleReference");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop47;
                }
            } while (true);

            otherlv_4=(Token)match(input,60,FOLLOW_60_in_rulePartitionPart9140); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_4, grammarAccess.getPartitionPartAccess().getRightSquareBracketKeyword_3());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "rulePartitionPart"


    // $ANTLR start "entryRuleModuleReference"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4008:1: entryRuleModuleReference returns [EObject current=null] : iv_ruleModuleReference= ruleModuleReference EOF ;
    public final EObject entryRuleModuleReference() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleModuleReference = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4009:2: (iv_ruleModuleReference= ruleModuleReference EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4010:2: iv_ruleModuleReference= ruleModuleReference EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getModuleReferenceRule()); 
            }
            pushFollow(FOLLOW_ruleModuleReference_in_entryRuleModuleReference9176);
            iv_ruleModuleReference=ruleModuleReference();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleModuleReference; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleModuleReference9186); if (state.failed) return current;

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
    // $ANTLR end "entryRuleModuleReference"


    // $ANTLR start "ruleModuleReference"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4017:1: ruleModuleReference returns [EObject current=null] : ( ( (otherlv_0= RULE_ID ) ) (otherlv_1= 'when' ( (lv_when_2_0= rulePropositionalFormula ) ) )? ) ;
    public final EObject ruleModuleReference() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token otherlv_1=null;
        EObject lv_when_2_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4020:28: ( ( ( (otherlv_0= RULE_ID ) ) (otherlv_1= 'when' ( (lv_when_2_0= rulePropositionalFormula ) ) )? ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4021:1: ( ( (otherlv_0= RULE_ID ) ) (otherlv_1= 'when' ( (lv_when_2_0= rulePropositionalFormula ) ) )? )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4021:1: ( ( (otherlv_0= RULE_ID ) ) (otherlv_1= 'when' ( (lv_when_2_0= rulePropositionalFormula ) ) )? )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4021:2: ( (otherlv_0= RULE_ID ) ) (otherlv_1= 'when' ( (lv_when_2_0= rulePropositionalFormula ) ) )?
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4021:2: ( (otherlv_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4022:1: (otherlv_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4022:1: (otherlv_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4023:3: otherlv_0= RULE_ID
            {
            if ( state.backtracking==0 ) {
               
              		  /* */ 
              		
            }
            if ( state.backtracking==0 ) {

              			if (current==null) {
              	            current = createModelElement(grammarAccess.getModuleReferenceRule());
              	        }
                      
            }
            otherlv_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleModuleReference9235); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              		newLeafNode(otherlv_0, grammarAccess.getModuleReferenceAccess().getDeltaModuleDeltaModuleCrossReference_0_0()); 
              	
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4037:2: (otherlv_1= 'when' ( (lv_when_2_0= rulePropositionalFormula ) ) )?
            int alt48=2;
            int LA48_0 = input.LA(1);

            if ( (LA48_0==61) ) {
                alt48=1;
            }
            switch (alt48) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4037:4: otherlv_1= 'when' ( (lv_when_2_0= rulePropositionalFormula ) )
                    {
                    otherlv_1=(Token)match(input,61,FOLLOW_61_in_ruleModuleReference9248); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                          	newLeafNode(otherlv_1, grammarAccess.getModuleReferenceAccess().getWhenKeyword_1_0());
                          
                    }
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4041:1: ( (lv_when_2_0= rulePropositionalFormula ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4042:1: (lv_when_2_0= rulePropositionalFormula )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4042:1: (lv_when_2_0= rulePropositionalFormula )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4043:3: lv_when_2_0= rulePropositionalFormula
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getModuleReferenceAccess().getWhenPropositionalFormulaParserRuleCall_1_1_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_rulePropositionalFormula_in_ruleModuleReference9269);
                    lv_when_2_0=rulePropositionalFormula();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getModuleReferenceRule());
                      	        }
                             		set(
                             			current, 
                             			"when",
                              		lv_when_2_0, 
                              		"PropositionalFormula");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }


                    }
                    break;

            }


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleModuleReference"


    // $ANTLR start "entryRulePropositionalFormula"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4067:1: entryRulePropositionalFormula returns [EObject current=null] : iv_rulePropositionalFormula= rulePropositionalFormula EOF ;
    public final EObject entryRulePropositionalFormula() throws RecognitionException {
        EObject current = null;

        EObject iv_rulePropositionalFormula = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4068:2: (iv_rulePropositionalFormula= rulePropositionalFormula EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4069:2: iv_rulePropositionalFormula= rulePropositionalFormula EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getPropositionalFormulaRule()); 
            }
            pushFollow(FOLLOW_rulePropositionalFormula_in_entryRulePropositionalFormula9307);
            iv_rulePropositionalFormula=rulePropositionalFormula();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_rulePropositionalFormula; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRulePropositionalFormula9317); if (state.failed) return current;

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
    // $ANTLR end "entryRulePropositionalFormula"


    // $ANTLR start "rulePropositionalFormula"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4076:1: rulePropositionalFormula returns [EObject current=null] : (this_And_0= ruleAnd ( () otherlv_2= '||' ( (lv_right_3_0= ruleAnd ) ) )* ) ;
    public final EObject rulePropositionalFormula() throws RecognitionException {
        EObject current = null;

        Token otherlv_2=null;
        EObject this_And_0 = null;

        EObject lv_right_3_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4079:28: ( (this_And_0= ruleAnd ( () otherlv_2= '||' ( (lv_right_3_0= ruleAnd ) ) )* ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4080:1: (this_And_0= ruleAnd ( () otherlv_2= '||' ( (lv_right_3_0= ruleAnd ) ) )* )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4080:1: (this_And_0= ruleAnd ( () otherlv_2= '||' ( (lv_right_3_0= ruleAnd ) ) )* )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4081:2: this_And_0= ruleAnd ( () otherlv_2= '||' ( (lv_right_3_0= ruleAnd ) ) )*
            {
            if ( state.backtracking==0 ) {
               
              	  /* */ 
              	
            }
            if ( state.backtracking==0 ) {
               
                      newCompositeNode(grammarAccess.getPropositionalFormulaAccess().getAndParserRuleCall_0()); 
                  
            }
            pushFollow(FOLLOW_ruleAnd_in_rulePropositionalFormula9367);
            this_And_0=ruleAnd();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               
                      current = this_And_0; 
                      afterParserOrEnumRuleCall();
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4092:1: ( () otherlv_2= '||' ( (lv_right_3_0= ruleAnd ) ) )*
            loop49:
            do {
                int alt49=2;
                int LA49_0 = input.LA(1);

                if ( (LA49_0==38) ) {
                    alt49=1;
                }


                switch (alt49) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4092:2: () otherlv_2= '||' ( (lv_right_3_0= ruleAnd ) )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4092:2: ()
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4093:2: 
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	  /* */ 
            	      	
            	    }
            	    if ( state.backtracking==0 ) {

            	              current = forceCreateModelElementAndSet(
            	                  grammarAccess.getPropositionalFormulaAccess().getOrLeftAction_1_0(),
            	                  current);
            	          
            	    }

            	    }

            	    otherlv_2=(Token)match(input,38,FOLLOW_38_in_rulePropositionalFormula9391); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	          	newLeafNode(otherlv_2, grammarAccess.getPropositionalFormulaAccess().getVerticalLineVerticalLineKeyword_1_1());
            	          
            	    }
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4105:1: ( (lv_right_3_0= ruleAnd ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4106:1: (lv_right_3_0= ruleAnd )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4106:1: (lv_right_3_0= ruleAnd )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4107:3: lv_right_3_0= ruleAnd
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getPropositionalFormulaAccess().getRightAndParserRuleCall_1_2_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_ruleAnd_in_rulePropositionalFormula9412);
            	    lv_right_3_0=ruleAnd();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getPropositionalFormulaRule());
            	      	        }
            	             		set(
            	             			current, 
            	             			"right",
            	              		lv_right_3_0, 
            	              		"And");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop49;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "rulePropositionalFormula"


    // $ANTLR start "entryRuleAnd"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4131:1: entryRuleAnd returns [EObject current=null] : iv_ruleAnd= ruleAnd EOF ;
    public final EObject entryRuleAnd() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleAnd = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4132:2: (iv_ruleAnd= ruleAnd EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4133:2: iv_ruleAnd= ruleAnd EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getAndRule()); 
            }
            pushFollow(FOLLOW_ruleAnd_in_entryRuleAnd9450);
            iv_ruleAnd=ruleAnd();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleAnd; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleAnd9460); if (state.failed) return current;

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
    // $ANTLR end "entryRuleAnd"


    // $ANTLR start "ruleAnd"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4140:1: ruleAnd returns [EObject current=null] : (this_Primary_0= rulePrimary ( () otherlv_2= '&&' ( (lv_right_3_0= rulePrimary ) ) )* ) ;
    public final EObject ruleAnd() throws RecognitionException {
        EObject current = null;

        Token otherlv_2=null;
        EObject this_Primary_0 = null;

        EObject lv_right_3_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4143:28: ( (this_Primary_0= rulePrimary ( () otherlv_2= '&&' ( (lv_right_3_0= rulePrimary ) ) )* ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4144:1: (this_Primary_0= rulePrimary ( () otherlv_2= '&&' ( (lv_right_3_0= rulePrimary ) ) )* )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4144:1: (this_Primary_0= rulePrimary ( () otherlv_2= '&&' ( (lv_right_3_0= rulePrimary ) ) )* )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4145:2: this_Primary_0= rulePrimary ( () otherlv_2= '&&' ( (lv_right_3_0= rulePrimary ) ) )*
            {
            if ( state.backtracking==0 ) {
               
              	  /* */ 
              	
            }
            if ( state.backtracking==0 ) {
               
                      newCompositeNode(grammarAccess.getAndAccess().getPrimaryParserRuleCall_0()); 
                  
            }
            pushFollow(FOLLOW_rulePrimary_in_ruleAnd9510);
            this_Primary_0=rulePrimary();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               
                      current = this_Primary_0; 
                      afterParserOrEnumRuleCall();
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4156:1: ( () otherlv_2= '&&' ( (lv_right_3_0= rulePrimary ) ) )*
            loop50:
            do {
                int alt50=2;
                int LA50_0 = input.LA(1);

                if ( (LA50_0==39) ) {
                    alt50=1;
                }


                switch (alt50) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4156:2: () otherlv_2= '&&' ( (lv_right_3_0= rulePrimary ) )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4156:2: ()
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4157:2: 
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	  /* */ 
            	      	
            	    }
            	    if ( state.backtracking==0 ) {

            	              current = forceCreateModelElementAndSet(
            	                  grammarAccess.getAndAccess().getAndLeftAction_1_0(),
            	                  current);
            	          
            	    }

            	    }

            	    otherlv_2=(Token)match(input,39,FOLLOW_39_in_ruleAnd9534); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	          	newLeafNode(otherlv_2, grammarAccess.getAndAccess().getAmpersandAmpersandKeyword_1_1());
            	          
            	    }
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4169:1: ( (lv_right_3_0= rulePrimary ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4170:1: (lv_right_3_0= rulePrimary )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4170:1: (lv_right_3_0= rulePrimary )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4171:3: lv_right_3_0= rulePrimary
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      	        newCompositeNode(grammarAccess.getAndAccess().getRightPrimaryParserRuleCall_1_2_0()); 
            	      	    
            	    }
            	    pushFollow(FOLLOW_rulePrimary_in_ruleAnd9555);
            	    lv_right_3_0=rulePrimary();

            	    state._fsp--;
            	    if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      	        if (current==null) {
            	      	            current = createModelElementForParent(grammarAccess.getAndRule());
            	      	        }
            	             		set(
            	             			current, 
            	             			"right",
            	              		lv_right_3_0, 
            	              		"Primary");
            	      	        afterParserOrEnumRuleCall();
            	      	    
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop50;
                }
            } while (true);


            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleAnd"


    // $ANTLR start "entryRulePrimary"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4195:1: entryRulePrimary returns [EObject current=null] : iv_rulePrimary= rulePrimary EOF ;
    public final EObject entryRulePrimary() throws RecognitionException {
        EObject current = null;

        EObject iv_rulePrimary = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4196:2: (iv_rulePrimary= rulePrimary EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4197:2: iv_rulePrimary= rulePrimary EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getPrimaryRule()); 
            }
            pushFollow(FOLLOW_rulePrimary_in_entryRulePrimary9593);
            iv_rulePrimary=rulePrimary();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_rulePrimary; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRulePrimary9603); if (state.failed) return current;

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
    // $ANTLR end "entryRulePrimary"


    // $ANTLR start "rulePrimary"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4204:1: rulePrimary returns [EObject current=null] : ( ( () ( (otherlv_1= RULE_ID ) ) ) | ( () otherlv_3= '(' ( (lv_formula_4_0= rulePropositionalFormula ) ) otherlv_5= ')' ) | ( () otherlv_7= '!' ( (lv_formula_8_0= rulePrimary ) ) ) | ( () otherlv_10= 'true' ) | ( () otherlv_12= 'false' ) ) ;
    public final EObject rulePrimary() throws RecognitionException {
        EObject current = null;

        Token otherlv_1=null;
        Token otherlv_3=null;
        Token otherlv_5=null;
        Token otherlv_7=null;
        Token otherlv_10=null;
        Token otherlv_12=null;
        EObject lv_formula_4_0 = null;

        EObject lv_formula_8_0 = null;


         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4207:28: ( ( ( () ( (otherlv_1= RULE_ID ) ) ) | ( () otherlv_3= '(' ( (lv_formula_4_0= rulePropositionalFormula ) ) otherlv_5= ')' ) | ( () otherlv_7= '!' ( (lv_formula_8_0= rulePrimary ) ) ) | ( () otherlv_10= 'true' ) | ( () otherlv_12= 'false' ) ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4208:1: ( ( () ( (otherlv_1= RULE_ID ) ) ) | ( () otherlv_3= '(' ( (lv_formula_4_0= rulePropositionalFormula ) ) otherlv_5= ')' ) | ( () otherlv_7= '!' ( (lv_formula_8_0= rulePrimary ) ) ) | ( () otherlv_10= 'true' ) | ( () otherlv_12= 'false' ) )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4208:1: ( ( () ( (otherlv_1= RULE_ID ) ) ) | ( () otherlv_3= '(' ( (lv_formula_4_0= rulePropositionalFormula ) ) otherlv_5= ')' ) | ( () otherlv_7= '!' ( (lv_formula_8_0= rulePrimary ) ) ) | ( () otherlv_10= 'true' ) | ( () otherlv_12= 'false' ) )
            int alt51=5;
            switch ( input.LA(1) ) {
            case RULE_ID:
                {
                alt51=1;
                }
                break;
            case 23:
                {
                alt51=2;
                }
                break;
            case 40:
                {
                alt51=3;
                }
                break;
            case 46:
                {
                alt51=4;
                }
                break;
            case 47:
                {
                alt51=5;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return current;}
                NoViableAltException nvae =
                    new NoViableAltException("", 51, 0, input);

                throw nvae;
            }

            switch (alt51) {
                case 1 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4208:2: ( () ( (otherlv_1= RULE_ID ) ) )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4208:2: ( () ( (otherlv_1= RULE_ID ) ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4208:3: () ( (otherlv_1= RULE_ID ) )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4208:3: ()
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4209:2: 
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {

                              current = forceCreateModelElement(
                                  grammarAccess.getPrimaryAccess().getFeatureRefAction_0_0(),
                                  current);
                          
                    }

                    }

                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4217:2: ( (otherlv_1= RULE_ID ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4218:1: (otherlv_1= RULE_ID )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4218:1: (otherlv_1= RULE_ID )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4219:3: otherlv_1= RULE_ID
                    {
                    if ( state.backtracking==0 ) {
                       
                      		  /* */ 
                      		
                    }
                    if ( state.backtracking==0 ) {

                      			if (current==null) {
                      	            current = createModelElement(grammarAccess.getPrimaryRule());
                      	        }
                              
                    }
                    otherlv_1=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_rulePrimary9665); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      		newLeafNode(otherlv_1, grammarAccess.getPrimaryAccess().getFeatureFeatureCrossReference_0_1_0()); 
                      	
                    }

                    }


                    }


                    }


                    }
                    break;
                case 2 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4234:6: ( () otherlv_3= '(' ( (lv_formula_4_0= rulePropositionalFormula ) ) otherlv_5= ')' )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4234:6: ( () otherlv_3= '(' ( (lv_formula_4_0= rulePropositionalFormula ) ) otherlv_5= ')' )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4234:7: () otherlv_3= '(' ( (lv_formula_4_0= rulePropositionalFormula ) ) otherlv_5= ')'
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4234:7: ()
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4235:2: 
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {

                              current = forceCreateModelElement(
                                  grammarAccess.getPrimaryAccess().getPropParenAction_1_0(),
                                  current);
                          
                    }

                    }

                    otherlv_3=(Token)match(input,23,FOLLOW_23_in_rulePrimary9697); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                          	newLeafNode(otherlv_3, grammarAccess.getPrimaryAccess().getLeftParenthesisKeyword_1_1());
                          
                    }
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4247:1: ( (lv_formula_4_0= rulePropositionalFormula ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4248:1: (lv_formula_4_0= rulePropositionalFormula )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4248:1: (lv_formula_4_0= rulePropositionalFormula )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4249:3: lv_formula_4_0= rulePropositionalFormula
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getPrimaryAccess().getFormulaPropositionalFormulaParserRuleCall_1_2_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_rulePropositionalFormula_in_rulePrimary9718);
                    lv_formula_4_0=rulePropositionalFormula();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getPrimaryRule());
                      	        }
                             		set(
                             			current, 
                             			"formula",
                              		lv_formula_4_0, 
                              		"PropositionalFormula");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }

                    otherlv_5=(Token)match(input,25,FOLLOW_25_in_rulePrimary9730); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                          	newLeafNode(otherlv_5, grammarAccess.getPrimaryAccess().getRightParenthesisKeyword_1_3());
                          
                    }

                    }


                    }
                    break;
                case 3 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4270:6: ( () otherlv_7= '!' ( (lv_formula_8_0= rulePrimary ) ) )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4270:6: ( () otherlv_7= '!' ( (lv_formula_8_0= rulePrimary ) ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4270:7: () otherlv_7= '!' ( (lv_formula_8_0= rulePrimary ) )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4270:7: ()
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4271:2: 
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {

                              current = forceCreateModelElement(
                                  grammarAccess.getPrimaryAccess().getNegationAction_2_0(),
                                  current);
                          
                    }

                    }

                    otherlv_7=(Token)match(input,40,FOLLOW_40_in_rulePrimary9762); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                          	newLeafNode(otherlv_7, grammarAccess.getPrimaryAccess().getExclamationMarkKeyword_2_1());
                          
                    }
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4283:1: ( (lv_formula_8_0= rulePrimary ) )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4284:1: (lv_formula_8_0= rulePrimary )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4284:1: (lv_formula_8_0= rulePrimary )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4285:3: lv_formula_8_0= rulePrimary
                    {
                    if ( state.backtracking==0 ) {
                       
                      	        newCompositeNode(grammarAccess.getPrimaryAccess().getFormulaPrimaryParserRuleCall_2_2_0()); 
                      	    
                    }
                    pushFollow(FOLLOW_rulePrimary_in_rulePrimary9783);
                    lv_formula_8_0=rulePrimary();

                    state._fsp--;
                    if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                      	        if (current==null) {
                      	            current = createModelElementForParent(grammarAccess.getPrimaryRule());
                      	        }
                             		set(
                             			current, 
                             			"formula",
                              		lv_formula_8_0, 
                              		"Primary");
                      	        afterParserOrEnumRuleCall();
                      	    
                    }

                    }


                    }


                    }


                    }
                    break;
                case 4 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4302:6: ( () otherlv_10= 'true' )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4302:6: ( () otherlv_10= 'true' )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4302:7: () otherlv_10= 'true'
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4302:7: ()
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4303:2: 
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {

                              current = forceCreateModelElement(
                                  grammarAccess.getPrimaryAccess().getPropTrueAction_3_0(),
                                  current);
                          
                    }

                    }

                    otherlv_10=(Token)match(input,46,FOLLOW_46_in_rulePrimary9815); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                          	newLeafNode(otherlv_10, grammarAccess.getPrimaryAccess().getTrueKeyword_3_1());
                          
                    }

                    }


                    }
                    break;
                case 5 :
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4316:6: ( () otherlv_12= 'false' )
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4316:6: ( () otherlv_12= 'false' )
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4316:7: () otherlv_12= 'false'
                    {
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4316:7: ()
                    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4317:2: 
                    {
                    if ( state.backtracking==0 ) {
                       
                      	  /* */ 
                      	
                    }
                    if ( state.backtracking==0 ) {

                              current = forceCreateModelElement(
                                  grammarAccess.getPrimaryAccess().getPropFalseAction_4_0(),
                                  current);
                          
                    }

                    }

                    otherlv_12=(Token)match(input,47,FOLLOW_47_in_rulePrimary9847); if (state.failed) return current;
                    if ( state.backtracking==0 ) {

                          	newLeafNode(otherlv_12, grammarAccess.getPrimaryAccess().getFalseKeyword_4_1());
                          
                    }

                    }


                    }
                    break;

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "rulePrimary"


    // $ANTLR start "entryRuleProduct"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4337:1: entryRuleProduct returns [EObject current=null] : iv_ruleProduct= ruleProduct EOF ;
    public final EObject entryRuleProduct() throws RecognitionException {
        EObject current = null;

        EObject iv_ruleProduct = null;


        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4338:2: (iv_ruleProduct= ruleProduct EOF )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4339:2: iv_ruleProduct= ruleProduct EOF
            {
            if ( state.backtracking==0 ) {
               newCompositeNode(grammarAccess.getProductRule()); 
            }
            pushFollow(FOLLOW_ruleProduct_in_entryRuleProduct9884);
            iv_ruleProduct=ruleProduct();

            state._fsp--;
            if (state.failed) return current;
            if ( state.backtracking==0 ) {
               current =iv_ruleProduct; 
            }
            match(input,EOF,FOLLOW_EOF_in_entryRuleProduct9894); if (state.failed) return current;

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
    // $ANTLR end "entryRuleProduct"


    // $ANTLR start "ruleProduct"
    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4346:1: ruleProduct returns [EObject current=null] : (otherlv_0= 'product' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= 'from' ( (otherlv_3= RULE_ID ) ) otherlv_4= ':' otherlv_5= '{' ( (otherlv_6= RULE_ID ) ) (otherlv_7= ',' ( (otherlv_8= RULE_ID ) ) )* otherlv_9= '}' ) ;
    public final EObject ruleProduct() throws RecognitionException {
        EObject current = null;

        Token otherlv_0=null;
        Token lv_name_1_0=null;
        Token otherlv_2=null;
        Token otherlv_3=null;
        Token otherlv_4=null;
        Token otherlv_5=null;
        Token otherlv_6=null;
        Token otherlv_7=null;
        Token otherlv_8=null;
        Token otherlv_9=null;

         enterRule(); 
            
        try {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4349:28: ( (otherlv_0= 'product' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= 'from' ( (otherlv_3= RULE_ID ) ) otherlv_4= ':' otherlv_5= '{' ( (otherlv_6= RULE_ID ) ) (otherlv_7= ',' ( (otherlv_8= RULE_ID ) ) )* otherlv_9= '}' ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4350:1: (otherlv_0= 'product' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= 'from' ( (otherlv_3= RULE_ID ) ) otherlv_4= ':' otherlv_5= '{' ( (otherlv_6= RULE_ID ) ) (otherlv_7= ',' ( (otherlv_8= RULE_ID ) ) )* otherlv_9= '}' )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4350:1: (otherlv_0= 'product' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= 'from' ( (otherlv_3= RULE_ID ) ) otherlv_4= ':' otherlv_5= '{' ( (otherlv_6= RULE_ID ) ) (otherlv_7= ',' ( (otherlv_8= RULE_ID ) ) )* otherlv_9= '}' )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4350:3: otherlv_0= 'product' ( (lv_name_1_0= RULE_ID ) ) otherlv_2= 'from' ( (otherlv_3= RULE_ID ) ) otherlv_4= ':' otherlv_5= '{' ( (otherlv_6= RULE_ID ) ) (otherlv_7= ',' ( (otherlv_8= RULE_ID ) ) )* otherlv_9= '}'
            {
            otherlv_0=(Token)match(input,62,FOLLOW_62_in_ruleProduct9931); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_0, grammarAccess.getProductAccess().getProductKeyword_0());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4354:1: ( (lv_name_1_0= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4355:1: (lv_name_1_0= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4355:1: (lv_name_1_0= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4356:3: lv_name_1_0= RULE_ID
            {
            lv_name_1_0=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleProduct9948); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              			newLeafNode(lv_name_1_0, grammarAccess.getProductAccess().getNameIDTerminalRuleCall_1_0()); 
              		
            }
            if ( state.backtracking==0 ) {

              	        if (current==null) {
              	            current = createModelElement(grammarAccess.getProductRule());
              	        }
                     		setWithLastConsumed(
                     			current, 
                     			"name",
                      		lv_name_1_0, 
                      		"ID");
              	    
            }

            }


            }

            otherlv_2=(Token)match(input,63,FOLLOW_63_in_ruleProduct9965); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_2, grammarAccess.getProductAccess().getFromKeyword_2());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4376:1: ( (otherlv_3= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4377:1: (otherlv_3= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4377:1: (otherlv_3= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4378:3: otherlv_3= RULE_ID
            {
            if ( state.backtracking==0 ) {
               
              		  /* */ 
              		
            }
            if ( state.backtracking==0 ) {

              			if (current==null) {
              	            current = createModelElement(grammarAccess.getProductRule());
              	        }
                      
            }
            otherlv_3=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleProduct9989); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              		newLeafNode(otherlv_3, grammarAccess.getProductAccess().getProductLineProductLineCrossReference_3_0()); 
              	
            }

            }


            }

            otherlv_4=(Token)match(input,64,FOLLOW_64_in_ruleProduct10001); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_4, grammarAccess.getProductAccess().getColonKeyword_4());
                  
            }
            otherlv_5=(Token)match(input,20,FOLLOW_20_in_ruleProduct10013); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_5, grammarAccess.getProductAccess().getLeftCurlyBracketKeyword_5());
                  
            }
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4400:1: ( (otherlv_6= RULE_ID ) )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4401:1: (otherlv_6= RULE_ID )
            {
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4401:1: (otherlv_6= RULE_ID )
            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4402:3: otherlv_6= RULE_ID
            {
            if ( state.backtracking==0 ) {
               
              		  /* */ 
              		
            }
            if ( state.backtracking==0 ) {

              			if (current==null) {
              	            current = createModelElement(grammarAccess.getProductRule());
              	        }
                      
            }
            otherlv_6=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleProduct10037); if (state.failed) return current;
            if ( state.backtracking==0 ) {

              		newLeafNode(otherlv_6, grammarAccess.getProductAccess().getFeaturesFeatureCrossReference_6_0()); 
              	
            }

            }


            }

            // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4416:2: (otherlv_7= ',' ( (otherlv_8= RULE_ID ) ) )*
            loop52:
            do {
                int alt52=2;
                int LA52_0 = input.LA(1);

                if ( (LA52_0==24) ) {
                    alt52=1;
                }


                switch (alt52) {
            	case 1 :
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4416:4: otherlv_7= ',' ( (otherlv_8= RULE_ID ) )
            	    {
            	    otherlv_7=(Token)match(input,24,FOLLOW_24_in_ruleProduct10050); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	          	newLeafNode(otherlv_7, grammarAccess.getProductAccess().getCommaKeyword_7_0());
            	          
            	    }
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4420:1: ( (otherlv_8= RULE_ID ) )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4421:1: (otherlv_8= RULE_ID )
            	    {
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4421:1: (otherlv_8= RULE_ID )
            	    // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:4422:3: otherlv_8= RULE_ID
            	    {
            	    if ( state.backtracking==0 ) {
            	       
            	      		  /* */ 
            	      		
            	    }
            	    if ( state.backtracking==0 ) {

            	      			if (current==null) {
            	      	            current = createModelElement(grammarAccess.getProductRule());
            	      	        }
            	              
            	    }
            	    otherlv_8=(Token)match(input,RULE_ID,FOLLOW_RULE_ID_in_ruleProduct10074); if (state.failed) return current;
            	    if ( state.backtracking==0 ) {

            	      		newLeafNode(otherlv_8, grammarAccess.getProductAccess().getFeaturesFeatureCrossReference_7_1_0()); 
            	      	
            	    }

            	    }


            	    }


            	    }
            	    break;

            	default :
            	    break loop52;
                }
            } while (true);

            otherlv_9=(Token)match(input,21,FOLLOW_21_in_ruleProduct10088); if (state.failed) return current;
            if ( state.backtracking==0 ) {

                  	newLeafNode(otherlv_9, grammarAccess.getProductAccess().getRightCurlyBracketKeyword_8());
                  
            }

            }


            }

            if ( state.backtracking==0 ) {
               leaveRule(); 
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
    // $ANTLR end "ruleProduct"

    // $ANTLR start synpred18_InternalDeltaJ
    public final void synpred18_InternalDeltaJ_fragment() throws RecognitionException {   
        EObject this_ExpressionStatement_0 = null;


        // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1222:2: (this_ExpressionStatement_0= ruleExpressionStatement )
        // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1222:2: this_ExpressionStatement_0= ruleExpressionStatement
        {
        if ( state.backtracking==0 ) {
           
          	  /* */ 
          	
        }
        pushFollow(FOLLOW_ruleExpressionStatement_in_synpred18_InternalDeltaJ2772);
        this_ExpressionStatement_0=ruleExpressionStatement();

        state._fsp--;
        if (state.failed) return ;

        }
    }
    // $ANTLR end synpred18_InternalDeltaJ

    // $ANTLR start synpred19_InternalDeltaJ
    public final void synpred19_InternalDeltaJ_fragment() throws RecognitionException {   
        EObject this_Assignment_1 = null;


        // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1235:2: (this_Assignment_1= ruleAssignment )
        // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:1235:2: this_Assignment_1= ruleAssignment
        {
        if ( state.backtracking==0 ) {
           
          	  /* */ 
          	
        }
        pushFollow(FOLLOW_ruleAssignment_in_synpred19_InternalDeltaJ2802);
        this_Assignment_1=ruleAssignment();

        state._fsp--;
        if (state.failed) return ;

        }
    }
    // $ANTLR end synpred19_InternalDeltaJ

    // $ANTLR start synpred41_InternalDeltaJ
    public final void synpred41_InternalDeltaJ_fragment() throws RecognitionException {   
        EObject this_Cast_4 = null;


        // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2126:2: (this_Cast_4= ruleCast )
        // ../org.deltaj/src-gen/org/deltaj/parser/antlr/internal/InternalDeltaJ.g:2126:2: this_Cast_4= ruleCast
        {
        if ( state.backtracking==0 ) {
           
          	  /* */ 
          	
        }
        pushFollow(FOLLOW_ruleCast_in_synpred41_InternalDeltaJ4754);
        this_Cast_4=ruleCast();

        state._fsp--;
        if (state.failed) return ;

        }
    }
    // $ANTLR end synpred41_InternalDeltaJ

    // Delegated rules

    public final boolean synpred18_InternalDeltaJ() {
        state.backtracking++;
        int start = input.mark();
        try {
            synpred18_InternalDeltaJ_fragment(); // can never throw exception
        } catch (RecognitionException re) {
            System.err.println("impossible: "+re);
        }
        boolean success = !state.failed;
        input.rewind(start);
        state.backtracking--;
        state.failed=false;
        return success;
    }
    public final boolean synpred19_InternalDeltaJ() {
        state.backtracking++;
        int start = input.mark();
        try {
            synpred19_InternalDeltaJ_fragment(); // can never throw exception
        } catch (RecognitionException re) {
            System.err.println("impossible: "+re);
        }
        boolean success = !state.failed;
        input.rewind(start);
        state.backtracking--;
        state.failed=false;
        return success;
    }
    public final boolean synpred41_InternalDeltaJ() {
        state.backtracking++;
        int start = input.mark();
        try {
            synpred41_InternalDeltaJ_fragment(); // can never throw exception
        } catch (RecognitionException re) {
            System.err.println("impossible: "+re);
        }
        boolean success = !state.failed;
        input.rewind(start);
        state.backtracking--;
        state.failed=false;
        return success;
    }


    protected DFA17 dfa17 = new DFA17(this);
    protected DFA29 dfa29 = new DFA29(this);
    static final String DFA17_eotS =
        "\21\uffff";
    static final String DFA17_eofS =
        "\21\uffff";
    static final String DFA17_minS =
        "\1\4\14\0\4\uffff";
    static final String DFA17_maxS =
        "\1\57\14\0\4\uffff";
    static final String DFA17_acceptS =
        "\15\uffff\1\3\1\4\1\1\1\2";
    static final String DFA17_specialS =
        "\1\uffff\1\0\1\1\1\2\1\3\1\4\1\5\1\6\1\7\1\10\1\11\1\12\1\13\4\uffff}>";
    static final String[] DFA17_transitionS = {
            "\1\10\1\14\1\16\1\13\17\uffff\1\7\4\uffff\1\15\2\uffff\1\2\10"+
            "\uffff\1\1\1\uffff\1\4\1\3\1\5\1\6\1\11\1\12",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "",
            "",
            "",
            ""
    };

    static final short[] DFA17_eot = DFA.unpackEncodedString(DFA17_eotS);
    static final short[] DFA17_eof = DFA.unpackEncodedString(DFA17_eofS);
    static final char[] DFA17_min = DFA.unpackEncodedStringToUnsignedChars(DFA17_minS);
    static final char[] DFA17_max = DFA.unpackEncodedStringToUnsignedChars(DFA17_maxS);
    static final short[] DFA17_accept = DFA.unpackEncodedString(DFA17_acceptS);
    static final short[] DFA17_special = DFA.unpackEncodedString(DFA17_specialS);
    static final short[][] DFA17_transition;

    static {
        int numStates = DFA17_transitionS.length;
        DFA17_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA17_transition[i] = DFA.unpackEncodedString(DFA17_transitionS[i]);
        }
    }

    class DFA17 extends DFA {

        public DFA17(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 17;
            this.eot = DFA17_eot;
            this.eof = DFA17_eof;
            this.min = DFA17_min;
            this.max = DFA17_max;
            this.accept = DFA17_accept;
            this.special = DFA17_special;
            this.transition = DFA17_transition;
        }
        public String getDescription() {
            return "1221:1: (this_ExpressionStatement_0= ruleExpressionStatement | this_Assignment_1= ruleAssignment | this_IfStatement_2= ruleIfStatement | ( () ( (lv_verbatim_4_0= RULE_JAVAVERBATIM ) ) ) )";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            TokenStream input = (TokenStream)_input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA17_1 = input.LA(1);

                         
                        int index17_1 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred18_InternalDeltaJ()) ) {s = 15;}

                        else if ( (synpred19_InternalDeltaJ()) ) {s = 16;}

                         
                        input.seek(index17_1);
                        if ( s>=0 ) return s;
                        break;
                    case 1 : 
                        int LA17_2 = input.LA(1);

                         
                        int index17_2 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred18_InternalDeltaJ()) ) {s = 15;}

                        else if ( (synpred19_InternalDeltaJ()) ) {s = 16;}

                         
                        input.seek(index17_2);
                        if ( s>=0 ) return s;
                        break;
                    case 2 : 
                        int LA17_3 = input.LA(1);

                         
                        int index17_3 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred18_InternalDeltaJ()) ) {s = 15;}

                        else if ( (synpred19_InternalDeltaJ()) ) {s = 16;}

                         
                        input.seek(index17_3);
                        if ( s>=0 ) return s;
                        break;
                    case 3 : 
                        int LA17_4 = input.LA(1);

                         
                        int index17_4 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred18_InternalDeltaJ()) ) {s = 15;}

                        else if ( (synpred19_InternalDeltaJ()) ) {s = 16;}

                         
                        input.seek(index17_4);
                        if ( s>=0 ) return s;
                        break;
                    case 4 : 
                        int LA17_5 = input.LA(1);

                         
                        int index17_5 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred18_InternalDeltaJ()) ) {s = 15;}

                        else if ( (synpred19_InternalDeltaJ()) ) {s = 16;}

                         
                        input.seek(index17_5);
                        if ( s>=0 ) return s;
                        break;
                    case 5 : 
                        int LA17_6 = input.LA(1);

                         
                        int index17_6 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred18_InternalDeltaJ()) ) {s = 15;}

                        else if ( (synpred19_InternalDeltaJ()) ) {s = 16;}

                         
                        input.seek(index17_6);
                        if ( s>=0 ) return s;
                        break;
                    case 6 : 
                        int LA17_7 = input.LA(1);

                         
                        int index17_7 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred18_InternalDeltaJ()) ) {s = 15;}

                        else if ( (synpred19_InternalDeltaJ()) ) {s = 16;}

                         
                        input.seek(index17_7);
                        if ( s>=0 ) return s;
                        break;
                    case 7 : 
                        int LA17_8 = input.LA(1);

                         
                        int index17_8 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred18_InternalDeltaJ()) ) {s = 15;}

                        else if ( (synpred19_InternalDeltaJ()) ) {s = 16;}

                         
                        input.seek(index17_8);
                        if ( s>=0 ) return s;
                        break;
                    case 8 : 
                        int LA17_9 = input.LA(1);

                         
                        int index17_9 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred18_InternalDeltaJ()) ) {s = 15;}

                        else if ( (synpred19_InternalDeltaJ()) ) {s = 16;}

                         
                        input.seek(index17_9);
                        if ( s>=0 ) return s;
                        break;
                    case 9 : 
                        int LA17_10 = input.LA(1);

                         
                        int index17_10 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred18_InternalDeltaJ()) ) {s = 15;}

                        else if ( (synpred19_InternalDeltaJ()) ) {s = 16;}

                         
                        input.seek(index17_10);
                        if ( s>=0 ) return s;
                        break;
                    case 10 : 
                        int LA17_11 = input.LA(1);

                         
                        int index17_11 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred18_InternalDeltaJ()) ) {s = 15;}

                        else if ( (synpred19_InternalDeltaJ()) ) {s = 16;}

                         
                        input.seek(index17_11);
                        if ( s>=0 ) return s;
                        break;
                    case 11 : 
                        int LA17_12 = input.LA(1);

                         
                        int index17_12 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred18_InternalDeltaJ()) ) {s = 15;}

                        else if ( (synpred19_InternalDeltaJ()) ) {s = 16;}

                         
                        input.seek(index17_12);
                        if ( s>=0 ) return s;
                        break;
            }
            if (state.backtracking>0) {state.failed=true; return -1;}
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 17, _s, input);
            error(nvae);
            throw nvae;
        }
    }
    static final String DFA29_eotS =
        "\15\uffff";
    static final String DFA29_eofS =
        "\15\uffff";
    static final String DFA29_minS =
        "\1\4\4\uffff\1\0\7\uffff";
    static final String DFA29_maxS =
        "\1\57\4\uffff\1\0\7\uffff";
    static final String DFA29_acceptS =
        "\1\uffff\1\1\1\2\1\3\1\4\1\uffff\1\6\3\uffff\1\7\1\5\1\10";
    static final String DFA29_specialS =
        "\5\uffff\1\0\7\uffff}>";
    static final String[] DFA29_transitionS = {
            "\1\6\1\12\1\uffff\1\6\17\uffff\1\5\22\uffff\1\2\1\1\1\3\1\4"+
            "\2\6",
            "",
            "",
            "",
            "",
            "\1\uffff",
            "",
            "",
            "",
            "",
            "",
            "",
            ""
    };

    static final short[] DFA29_eot = DFA.unpackEncodedString(DFA29_eotS);
    static final short[] DFA29_eof = DFA.unpackEncodedString(DFA29_eofS);
    static final char[] DFA29_min = DFA.unpackEncodedStringToUnsignedChars(DFA29_minS);
    static final char[] DFA29_max = DFA.unpackEncodedStringToUnsignedChars(DFA29_maxS);
    static final short[] DFA29_accept = DFA.unpackEncodedString(DFA29_acceptS);
    static final short[] DFA29_special = DFA.unpackEncodedString(DFA29_specialS);
    static final short[][] DFA29_transition;

    static {
        int numStates = DFA29_transitionS.length;
        DFA29_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA29_transition[i] = DFA.unpackEncodedString(DFA29_transitionS[i]);
        }
    }

    class DFA29 extends DFA {

        public DFA29(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 29;
            this.eot = DFA29_eot;
            this.eof = DFA29_eof;
            this.min = DFA29_min;
            this.max = DFA29_max;
            this.accept = DFA29_accept;
            this.special = DFA29_special;
            this.transition = DFA29_transition;
        }
        public String getDescription() {
            return "2073:1: (this_This_0= ruleThis | this_Null_1= ruleNull | this_Original_2= ruleOriginal | this_New_3= ruleNew | this_Cast_4= ruleCast | this_Constant_5= ruleConstant | this_VariableAccess_6= ruleVariableAccess | this_Paren_7= ruleParen )";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            TokenStream input = (TokenStream)_input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA29_5 = input.LA(1);

                         
                        int index29_5 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred41_InternalDeltaJ()) ) {s = 11;}

                        else if ( (true) ) {s = 12;}

                         
                        input.seek(index29_5);
                        if ( s>=0 ) return s;
                        break;
            }
            if (state.backtracking>0) {state.failed=true; return -1;}
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 29, _s, input);
            error(nvae);
            throw nvae;
        }
    }
 

    public static final BitSet FOLLOW_ruleProgram_in_entryRuleProgram81 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleProgram91 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleDeltaModule_in_ruleProgram137 = new BitSet(new long[]{0x4081000000000002L});
    public static final BitSet FOLLOW_ruleProductLine_in_ruleProgram159 = new BitSet(new long[]{0x4080000000000002L});
    public static final BitSet FOLLOW_ruleProduct_in_ruleProgram181 = new BitSet(new long[]{0x4000000000000002L});
    public static final BitSet FOLLOW_ruleTypeVariable_in_entryRuleTypeVariable220 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleTypeVariable230 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleTypeVariableId_in_ruleTypeVariable275 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleTypeVariableId_in_entryRuleTypeVariableId311 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleTypeVariableId322 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_12_in_ruleTypeVariableId360 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_RULE_INT_in_ruleTypeVariableId375 = new BitSet(new long[]{0x0000000000002000L});
    public static final BitSet FOLLOW_13_in_ruleTypeVariableId393 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleTypeForMethod_in_entryRuleTypeForMethod433 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleTypeForMethod443 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleVoidType_in_ruleTypeForMethod493 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleTypeForDeclaration_in_ruleTypeForMethod523 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleVoidType_in_entryRuleVoidType558 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleVoidType568 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_14_in_ruleVoidType610 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleTypeForDeclaration_in_entryRuleTypeForDeclaration658 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleTypeForDeclaration668 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleBasicType_in_ruleTypeForDeclaration718 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClassType_in_ruleTypeForDeclaration748 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleBasicType_in_entryRuleBasicType783 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleBasicType793 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleIntType_in_ruleBasicType843 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleBooleanType_in_ruleBasicType873 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleStringType_in_ruleBasicType903 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleIntType_in_entryRuleIntType938 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleIntType948 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_15_in_ruleIntType990 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleBooleanType_in_entryRuleBooleanType1038 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleBooleanType1048 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_16_in_ruleBooleanType1090 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleStringType_in_entryRuleStringType1138 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleStringType1148 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_17_in_ruleStringType1190 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClassType_in_entryRuleClassType1238 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleClassType1248 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClassName_in_ruleClassType1293 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClass_in_entryRuleClass1328 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleClass1338 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_18_in_ruleClass1375 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleClass1392 = new BitSet(new long[]{0x0000000000180000L});
    public static final BitSet FOLLOW_19_in_ruleClass1410 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleClassName_in_ruleClass1431 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_20_in_ruleClass1445 = new BitSet(new long[]{0x000000000023C020L});
    public static final BitSet FOLLOW_ruleField_in_ruleClass1466 = new BitSet(new long[]{0x000000000023C020L});
    public static final BitSet FOLLOW_ruleMethod_in_ruleClass1488 = new BitSet(new long[]{0x000000000023C020L});
    public static final BitSet FOLLOW_21_in_ruleClass1501 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClassName_in_entryRuleClassName1538 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleClassName1549 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleClassName1588 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFieldName_in_entryRuleFieldName1633 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleFieldName1644 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleFieldName1683 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodName_in_entryRuleMethodName1728 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMethodName1739 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleMethodName1778 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleField_in_entryRuleField1824 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleField1834 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleTypeForDeclaration_in_ruleField1880 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleField1897 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleField1914 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleLocalVariableDeclaration_in_entryRuleLocalVariableDeclaration1950 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleLocalVariableDeclaration1960 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleTypeForDeclaration_in_ruleLocalVariableDeclaration2006 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleLocalVariableDeclaration2023 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleLocalVariableDeclaration2040 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleParameter_in_entryRuleParameter2076 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleParameter2086 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleTypeForDeclaration_in_ruleParameter2132 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleParameter2149 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethod_in_entryRuleMethod2190 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMethod2200 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleTypeForMethod_in_ruleMethod2246 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleMethod2263 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_23_in_ruleMethod2280 = new BitSet(new long[]{0x0000000002038020L});
    public static final BitSet FOLLOW_ruleParameter_in_ruleMethod2302 = new BitSet(new long[]{0x0000000003000000L});
    public static final BitSet FOLLOW_24_in_ruleMethod2315 = new BitSet(new long[]{0x0000000000038020L});
    public static final BitSet FOLLOW_ruleParameter_in_ruleMethod2336 = new BitSet(new long[]{0x0000000003000000L});
    public static final BitSet FOLLOW_25_in_ruleMethod2352 = new BitSet(new long[]{0x0000000000100002L});
    public static final BitSet FOLLOW_ruleStatementBlock_in_ruleMethod2373 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleStatementBlock_in_entryRuleStatementBlock2410 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleStatementBlock2420 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_20_in_ruleStatementBlock2469 = new BitSet(new long[]{0x0000FD0094A380F0L});
    public static final BitSet FOLLOW_ruleLocalVariableDeclaration_in_ruleStatementBlock2490 = new BitSet(new long[]{0x0000FD0094A380F0L});
    public static final BitSet FOLLOW_ruleStatement_in_ruleStatementBlock2512 = new BitSet(new long[]{0x0000FD0094A000F0L});
    public static final BitSet FOLLOW_ruleReturnStatement_in_ruleStatementBlock2534 = new BitSet(new long[]{0x0000000000200000L});
    public static final BitSet FOLLOW_21_in_ruleStatementBlock2547 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleReturnStatement_in_entryRuleReturnStatement2583 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleReturnStatement2593 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_26_in_ruleReturnStatement2642 = new BitSet(new long[]{0x0000FD0080C000B0L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleReturnStatement2663 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleReturnStatement2676 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleStatement_in_entryRuleStatement2712 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleStatement2722 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleExpressionStatement_in_ruleStatement2772 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleAssignment_in_ruleStatement2802 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleIfStatement_in_ruleStatement2832 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_JAVAVERBATIM_in_ruleStatement2867 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleExpressionStatement_in_entryRuleExpressionStatement2909 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleExpressionStatement2919 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleExpressionStatement2965 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleExpressionStatement2977 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleAssignment_in_entryRuleAssignment3013 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleAssignment3023 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleAssignment3069 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_27_in_ruleAssignment3081 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleAssignment3102 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleAssignment3114 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleIfStatement_in_entryRuleIfStatement3150 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleIfStatement3160 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_28_in_ruleIfStatement3209 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_23_in_ruleIfStatement3221 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleIfStatement3242 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_ruleIfStatement3254 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_ruleStatementBlock_in_ruleIfStatement3275 = new BitSet(new long[]{0x0000000020000002L});
    public static final BitSet FOLLOW_29_in_ruleIfStatement3288 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_ruleStatementBlock_in_ruleIfStatement3309 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleExpression_in_entryRuleExpression3347 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleExpression3357 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleAddition_in_ruleExpression3406 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleAddition_in_entryRuleAddition3440 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleAddition3450 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMultiplication_in_ruleAddition3500 = new BitSet(new long[]{0x00000000C0000002L});
    public static final BitSet FOLLOW_30_in_ruleAddition3526 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_31_in_ruleAddition3558 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_ruleMultiplication_in_ruleAddition3581 = new BitSet(new long[]{0x00000000C0000002L});
    public static final BitSet FOLLOW_ruleMultiplication_in_entryRuleMultiplication3619 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMultiplication3629 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleComparison_in_ruleMultiplication3679 = new BitSet(new long[]{0x0000000300000002L});
    public static final BitSet FOLLOW_32_in_ruleMultiplication3711 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_33_in_ruleMultiplication3740 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_ruleComparison_in_ruleMultiplication3777 = new BitSet(new long[]{0x0000000300000002L});
    public static final BitSet FOLLOW_ruleComparison_in_entryRuleComparison3815 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleComparison3825 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleBooleanExpression_in_ruleComparison3875 = new BitSet(new long[]{0x0000003C00003002L});
    public static final BitSet FOLLOW_34_in_ruleComparison3907 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_35_in_ruleComparison3936 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_12_in_ruleComparison3965 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_13_in_ruleComparison3994 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_36_in_ruleComparison4023 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_37_in_ruleComparison4052 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_ruleBooleanExpression_in_ruleComparison4089 = new BitSet(new long[]{0x0000003C00003002L});
    public static final BitSet FOLLOW_ruleBooleanExpression_in_entryRuleBooleanExpression4127 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleBooleanExpression4137 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleAtomic_in_ruleBooleanExpression4187 = new BitSet(new long[]{0x000000C000000002L});
    public static final BitSet FOLLOW_38_in_ruleBooleanExpression4219 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_39_in_ruleBooleanExpression4248 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_ruleAtomic_in_ruleBooleanExpression4285 = new BitSet(new long[]{0x000000C000000002L});
    public static final BitSet FOLLOW_ruleAtomic_in_entryRuleAtomic4323 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleAtomic4333 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_40_in_ruleAtomic4383 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_ruleAtomic_in_ruleAtomic4404 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_31_in_ruleAtomic4436 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_ruleAtomic_in_ruleAtomic4457 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleTerminalExpression_in_ruleAtomic4490 = new BitSet(new long[]{0x0000020000000002L});
    public static final BitSet FOLLOW_41_in_ruleAtomic4514 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleMessage_in_ruleAtomic4535 = new BitSet(new long[]{0x0000020000000002L});
    public static final BitSet FOLLOW_ruleTerminalExpression_in_entryRuleTerminalExpression4574 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleTerminalExpression4584 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleThis_in_ruleTerminalExpression4634 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleNull_in_ruleTerminalExpression4664 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleOriginal_in_ruleTerminalExpression4694 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleNew_in_ruleTerminalExpression4724 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleCast_in_ruleTerminalExpression4754 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleConstant_in_ruleTerminalExpression4784 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleVariableAccess_in_ruleTerminalExpression4814 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleParen_in_ruleTerminalExpression4844 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleNull_in_entryRuleNull4879 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleNull4889 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_ruleNull4931 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleThis_in_entryRuleThis4979 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleThis4989 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_43_in_ruleThis5031 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleOriginal_in_entryRuleOriginal5079 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleOriginal5089 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_44_in_ruleOriginal5132 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_23_in_ruleOriginal5157 = new BitSet(new long[]{0x0000FD00828000B0L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleOriginal5179 = new BitSet(new long[]{0x0000000003000000L});
    public static final BitSet FOLLOW_24_in_ruleOriginal5192 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleOriginal5213 = new BitSet(new long[]{0x0000000003000000L});
    public static final BitSet FOLLOW_25_in_ruleOriginal5229 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleVariableAccess_in_entryRuleVariableAccess5265 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleVariableAccess5275 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleVariableAccess5323 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleNew_in_entryRuleNew5358 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleNew5368 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_45_in_ruleNew5405 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleClassName_in_ruleNew5426 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_23_in_ruleNew5438 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_ruleNew5450 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleCast_in_entryRuleCast5486 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleCast5496 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_23_in_ruleCast5533 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleClassName_in_ruleCast5554 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_ruleCast5566 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_ruleTerminalExpression_in_ruleCast5587 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleParen_in_entryRuleParen5623 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleParen5633 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_23_in_ruleParen5670 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleParen5691 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_ruleParen5703 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleConstant_in_entryRuleConstant5739 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleConstant5749 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleIntConstant_in_ruleConstant5799 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleBoolConstant_in_ruleConstant5829 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleStringConstant_in_ruleConstant5859 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleStringConstant_in_entryRuleStringConstant5894 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleStringConstant5904 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_STRING_in_ruleStringConstant5945 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleIntConstant_in_entryRuleIntConstant5985 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleIntConstant5995 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_INT_in_ruleIntConstant6036 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleBoolConstant_in_entryRuleBoolConstant6076 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleBoolConstant6086 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_46_in_ruleBoolConstant6130 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_47_in_ruleBoolConstant6159 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMessage_in_entryRuleMessage6210 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMessage6220 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFieldSelection_in_ruleMessage6270 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodCall_in_ruleMessage6300 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodCall_in_entryRuleMethodCall6335 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMethodCall6345 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleMethodCall6387 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_23_in_ruleMethodCall6404 = new BitSet(new long[]{0x0000FD00828000B0L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleMethodCall6426 = new BitSet(new long[]{0x0000000003000000L});
    public static final BitSet FOLLOW_24_in_ruleMethodCall6439 = new BitSet(new long[]{0x0000FD00808000B0L});
    public static final BitSet FOLLOW_ruleExpression_in_ruleMethodCall6460 = new BitSet(new long[]{0x0000000003000000L});
    public static final BitSet FOLLOW_25_in_ruleMethodCall6476 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFieldSelection_in_entryRuleFieldSelection6512 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleFieldSelection6522 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleFieldSelection6563 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleDeltaModule_in_entryRuleDeltaModule6603 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleDeltaModule6613 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_48_in_ruleDeltaModule6650 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleDeltaModule6667 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_20_in_ruleDeltaModule6684 = new BitSet(new long[]{0x000E000000200000L});
    public static final BitSet FOLLOW_ruleDeltaAction_in_ruleDeltaModule6705 = new BitSet(new long[]{0x000E000000200000L});
    public static final BitSet FOLLOW_21_in_ruleDeltaModule6718 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleDeltaAction_in_entryRuleDeltaAction6754 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleDeltaAction6764 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClassAddition_in_ruleDeltaAction6814 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleRemovesOrModifiesClass_in_ruleDeltaAction6844 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClassAddition_in_entryRuleClassAddition6879 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleClassAddition6889 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_49_in_ruleClassAddition6926 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_ruleClass_in_ruleClassAddition6947 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleRemovesOrModifiesClass_in_entryRuleRemovesOrModifiesClass6983 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleRemovesOrModifiesClass6993 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClassRemoval_in_ruleRemovesOrModifiesClass7043 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClassModification_in_ruleRemovesOrModifiesClass7073 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClassRemoval_in_entryRuleClassRemoval7108 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleClassRemoval7118 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_50_in_ruleClassRemoval7155 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleClassName_in_ruleClassRemoval7176 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleClassRemoval7188 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleClassModification_in_entryRuleClassModification7224 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleClassModification7234 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_51_in_ruleClassModification7271 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleClassName_in_ruleClassModification7292 = new BitSet(new long[]{0x0010000000100000L});
    public static final BitSet FOLLOW_52_in_ruleClassModification7305 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleClassName_in_ruleClassModification7326 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_20_in_ruleClassModification7340 = new BitSet(new long[]{0x006A000000200000L});
    public static final BitSet FOLLOW_ruleDeltaSubAction_in_ruleClassModification7361 = new BitSet(new long[]{0x006A000000200000L});
    public static final BitSet FOLLOW_21_in_ruleClassModification7374 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleDeltaSubAction_in_entryRuleDeltaSubAction7410 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleDeltaSubAction7420 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodOrFieldAddition_in_ruleDeltaSubAction7470 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFieldRemoval_in_ruleDeltaSubAction7500 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodRemoval_in_ruleDeltaSubAction7530 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodModification_in_ruleDeltaSubAction7560 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodOrFieldAddition_in_entryRuleMethodOrFieldAddition7595 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMethodOrFieldAddition7605 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFieldAddition_in_ruleMethodOrFieldAddition7655 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodAddition_in_ruleMethodOrFieldAddition7685 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFieldAddition_in_entryRuleFieldAddition7720 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleFieldAddition7730 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_49_in_ruleFieldAddition7767 = new BitSet(new long[]{0x0000000000038020L});
    public static final BitSet FOLLOW_ruleField_in_ruleFieldAddition7788 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodAddition_in_entryRuleMethodAddition7824 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMethodAddition7834 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_49_in_ruleMethodAddition7871 = new BitSet(new long[]{0x000000000003C020L});
    public static final BitSet FOLLOW_ruleMethod_in_ruleMethodAddition7892 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFieldRemoval_in_entryRuleFieldRemoval7928 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleFieldRemoval7938 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_53_in_ruleFieldRemoval7975 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleFieldName_in_ruleFieldRemoval7996 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleFieldRemoval8008 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodRemoval_in_entryRuleMethodRemoval8044 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMethodRemoval8054 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_54_in_ruleMethodRemoval8091 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleMethodName_in_ruleMethodRemoval8112 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_22_in_ruleMethodRemoval8124 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleMethodModification_in_entryRuleMethodModification8160 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleMethodModification8170 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_51_in_ruleMethodModification8207 = new BitSet(new long[]{0x000000000003C020L});
    public static final BitSet FOLLOW_ruleMethod_in_ruleMethodModification8228 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleProductLine_in_entryRuleProductLine8264 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleProductLine8274 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_55_in_ruleProductLine8311 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleProductLine8328 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_20_in_ruleProductLine8345 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_ruleFeatures_in_ruleProductLine8366 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_ruleConfigurations_in_ruleProductLine8387 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_ruleDeltaPartition_in_ruleProductLine8408 = new BitSet(new long[]{0x0000000000200000L});
    public static final BitSet FOLLOW_21_in_ruleProductLine8420 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleFeatures_in_entryRuleFeatures8456 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleFeatures8466 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_56_in_ruleFeatures8503 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleFeature_in_ruleFeatures8525 = new BitSet(new long[]{0x0000000001000002L});
    public static final BitSet FOLLOW_24_in_ruleFeatures8538 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleFeature_in_ruleFeatures8559 = new BitSet(new long[]{0x0000000001000002L});
    public static final BitSet FOLLOW_ruleFeature_in_entryRuleFeature8598 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleFeature8608 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleFeature8649 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleConfigurations_in_entryRuleConfigurations8689 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleConfigurations8699 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_57_in_ruleConfigurations8736 = new BitSet(new long[]{0x0000C10000800020L});
    public static final BitSet FOLLOW_ruleConfiguration_in_ruleConfigurations8757 = new BitSet(new long[]{0x0000000000400002L});
    public static final BitSet FOLLOW_22_in_ruleConfigurations8770 = new BitSet(new long[]{0x0000C10000800020L});
    public static final BitSet FOLLOW_ruleConfiguration_in_ruleConfigurations8791 = new BitSet(new long[]{0x0000000000400002L});
    public static final BitSet FOLLOW_ruleConfiguration_in_entryRuleConfiguration8829 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleConfiguration8839 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_rulePropositionalFormula_in_ruleConfiguration8884 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleDeltaPartition_in_entryRuleDeltaPartition8919 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleDeltaPartition8929 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_58_in_ruleDeltaPartition8966 = new BitSet(new long[]{0x0800000000000000L});
    public static final BitSet FOLLOW_rulePartitionPart_in_ruleDeltaPartition8987 = new BitSet(new long[]{0x0800000000000002L});
    public static final BitSet FOLLOW_rulePartitionPart_in_entryRulePartitionPart9024 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRulePartitionPart9034 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_59_in_rulePartitionPart9071 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleModuleReference_in_rulePartitionPart9092 = new BitSet(new long[]{0x1000000001000000L});
    public static final BitSet FOLLOW_24_in_rulePartitionPart9105 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ruleModuleReference_in_rulePartitionPart9126 = new BitSet(new long[]{0x1000000001000000L});
    public static final BitSet FOLLOW_60_in_rulePartitionPart9140 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleModuleReference_in_entryRuleModuleReference9176 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleModuleReference9186 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleModuleReference9235 = new BitSet(new long[]{0x2000000000000002L});
    public static final BitSet FOLLOW_61_in_ruleModuleReference9248 = new BitSet(new long[]{0x0000C10000800020L});
    public static final BitSet FOLLOW_rulePropositionalFormula_in_ruleModuleReference9269 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_rulePropositionalFormula_in_entryRulePropositionalFormula9307 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRulePropositionalFormula9317 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleAnd_in_rulePropositionalFormula9367 = new BitSet(new long[]{0x0000004000000002L});
    public static final BitSet FOLLOW_38_in_rulePropositionalFormula9391 = new BitSet(new long[]{0x0000C10000800020L});
    public static final BitSet FOLLOW_ruleAnd_in_rulePropositionalFormula9412 = new BitSet(new long[]{0x0000004000000002L});
    public static final BitSet FOLLOW_ruleAnd_in_entryRuleAnd9450 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleAnd9460 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_rulePrimary_in_ruleAnd9510 = new BitSet(new long[]{0x0000008000000002L});
    public static final BitSet FOLLOW_39_in_ruleAnd9534 = new BitSet(new long[]{0x0000C10000800020L});
    public static final BitSet FOLLOW_rulePrimary_in_ruleAnd9555 = new BitSet(new long[]{0x0000008000000002L});
    public static final BitSet FOLLOW_rulePrimary_in_entryRulePrimary9593 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRulePrimary9603 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RULE_ID_in_rulePrimary9665 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_23_in_rulePrimary9697 = new BitSet(new long[]{0x0000C10000800020L});
    public static final BitSet FOLLOW_rulePropositionalFormula_in_rulePrimary9718 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_rulePrimary9730 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_40_in_rulePrimary9762 = new BitSet(new long[]{0x0000C10000800020L});
    public static final BitSet FOLLOW_rulePrimary_in_rulePrimary9783 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_46_in_rulePrimary9815 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_47_in_rulePrimary9847 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleProduct_in_entryRuleProduct9884 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_entryRuleProduct9894 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_62_in_ruleProduct9931 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleProduct9948 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_ruleProduct9965 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleProduct9989 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000001L});
    public static final BitSet FOLLOW_64_in_ruleProduct10001 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_20_in_ruleProduct10013 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleProduct10037 = new BitSet(new long[]{0x0000000001200000L});
    public static final BitSet FOLLOW_24_in_ruleProduct10050 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_RULE_ID_in_ruleProduct10074 = new BitSet(new long[]{0x0000000001200000L});
    public static final BitSet FOLLOW_21_in_ruleProduct10088 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleExpressionStatement_in_synpred18_InternalDeltaJ2772 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleAssignment_in_synpred19_InternalDeltaJ2802 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ruleCast_in_synpred41_InternalDeltaJ4754 = new BitSet(new long[]{0x0000000000000002L});

}