/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
// $ANTLR 3.3 Nov 30, 2010 12:45:30 /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g 2011-04-19 18:20:42

package de.ovgu.featureide.fm.extended.ui.io.constraint;


import java.util.ArrayList;
import java.util.List;

import org.antlr.runtime.BitSet;
import org.antlr.runtime.NoViableAltException;
import org.antlr.runtime.Parser;
import org.antlr.runtime.ParserRuleReturnScope;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.RecognizerSharedState;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenStream;

public class ConstraintParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "SEMICOLON", "NEGATIVE", "ATTRIBUTE", "ATTRIBUTE_SUM", "RELATION", "IDENTIFIER", "NUMBER", "WS", "'-'", "'+'"
    };
    public static final int EOF=-1;
    public static final int T__12=12;
    public static final int T__13=13;
    public static final int SEMICOLON=4;
    public static final int NEGATIVE=5;
    public static final int ATTRIBUTE=6;
    public static final int ATTRIBUTE_SUM=7;
    public static final int RELATION=8;
    public static final int IDENTIFIER=9;
    public static final int NUMBER=10;
    public static final int WS=11;

    // delegates
    // delegators


        public ConstraintParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public ConstraintParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return ConstraintParser.tokenNames; }
    public String getGrammarFileName() { return "/home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g"; }


    	private boolean error = false;

    	@Override
    	public void reportError(RecognitionException e) {
    		this.error = true;
    		//super.reportError(e);
    	}

    	public boolean hadError() {
    		return error;
    	}



    // $ANTLR start "constraint"
    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:46:1: constraint returns [Equation value] : sum[wTerms] RELATION degree SEMICOLON EOF ;
    public final Equation constraint() throws RecognitionException {
        Equation value = null;

        Token RELATION1=null;
        int degree2 = 0;



        List<WeightedTerm> wTerms = new ArrayList<WeightedTerm>();

        try {
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:50:2: ( sum[wTerms] RELATION degree SEMICOLON EOF )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:50:4: sum[wTerms] RELATION degree SEMICOLON EOF
            {
            pushFollow(FOLLOW_sum_in_constraint97);
            sum(wTerms);

            state._fsp--;

            RELATION1=(Token)match(input,RELATION,FOLLOW_RELATION_in_constraint100); 
            pushFollow(FOLLOW_degree_in_constraint102);
            degree2=degree();

            state._fsp--;

            match(input,SEMICOLON,FOLLOW_SEMICOLON_in_constraint104); 
            match(input,EOF,FOLLOW_EOF_in_constraint106); 
            value = new Equation(wTerms, (RELATION1!=null?RELATION1.getText():null), degree2);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return value;
    }
    // $ANTLR end "constraint"


    // $ANTLR start "sum"
    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:52:1: sum[List<WeightedTerm> wTerms] : ( weightedTermFirst ( sumTail[wTerms] )? | weightedTerm ( sumTail[wTerms] )? );
    public final void sum(List<WeightedTerm> wTerms) throws RecognitionException {
        WeightedTerm weightedTermFirst3 = null;

        WeightedTerm weightedTerm4 = null;


        try {
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:53:2: ( weightedTermFirst ( sumTail[wTerms] )? | weightedTerm ( sumTail[wTerms] )? )
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0==NEGATIVE||(LA3_0>=IDENTIFIER && LA3_0<=NUMBER)) ) {
                alt3=1;
            }
            else if ( ((LA3_0>=12 && LA3_0<=13)) ) {
                alt3=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;
            }
            switch (alt3) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:53:4: weightedTermFirst ( sumTail[wTerms] )?
                    {
                    pushFollow(FOLLOW_weightedTermFirst_in_sum119);
                    weightedTermFirst3=weightedTermFirst();

                    state._fsp--;

                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:53:22: ( sumTail[wTerms] )?
                    int alt1=2;
                    int LA1_0 = input.LA(1);

                    if ( ((LA1_0>=12 && LA1_0<=13)) ) {
                        alt1=1;
                    }
                    switch (alt1) {
                        case 1 :
                            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:53:22: sumTail[wTerms]
                            {
                            pushFollow(FOLLOW_sumTail_in_sum121);
                            sumTail(wTerms);

                            state._fsp--;


                            }
                            break;

                    }

                    wTerms.add(weightedTermFirst3);

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:54:4: weightedTerm ( sumTail[wTerms] )?
                    {
                    pushFollow(FOLLOW_weightedTerm_in_sum130);
                    weightedTerm4=weightedTerm();

                    state._fsp--;

                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:54:17: ( sumTail[wTerms] )?
                    int alt2=2;
                    int LA2_0 = input.LA(1);

                    if ( ((LA2_0>=12 && LA2_0<=13)) ) {
                        alt2=1;
                    }
                    switch (alt2) {
                        case 1 :
                            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:54:17: sumTail[wTerms]
                            {
                            pushFollow(FOLLOW_sumTail_in_sum132);
                            sumTail(wTerms);

                            state._fsp--;


                            }
                            break;

                    }

                    wTerms.add(weightedTerm4);

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "sum"


    // $ANTLR start "sumTail"
    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:56:1: sumTail[List<WeightedTerm> wTerms] : weightedTerm ( sumTail[wTerms] )? ;
    public final void sumTail(List<WeightedTerm> wTerms) throws RecognitionException {
        WeightedTerm weightedTerm5 = null;


        try {
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:57:2: ( weightedTerm ( sumTail[wTerms] )? )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:57:4: weightedTerm ( sumTail[wTerms] )?
            {
            pushFollow(FOLLOW_weightedTerm_in_sumTail147);
            weightedTerm5=weightedTerm();

            state._fsp--;

            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:57:17: ( sumTail[wTerms] )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( ((LA4_0>=12 && LA4_0<=13)) ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:57:17: sumTail[wTerms]
                    {
                    pushFollow(FOLLOW_sumTail_in_sumTail149);
                    sumTail(wTerms);

                    state._fsp--;


                    }
                    break;

            }

            wTerms.add(weightedTerm5);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "sumTail"


    // $ANTLR start "weightedTermFirst"
    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:59:1: weightedTermFirst returns [WeightedTerm value] : ( unsigned reference | reference | unsigned NEGATIVE reference | NEGATIVE reference );
    public final WeightedTerm weightedTermFirst() throws RecognitionException {
        WeightedTerm value = null;

        ConstraintParser.unsigned_return unsigned6 = null;

        Reference reference7 = null;

        Reference reference8 = null;

        ConstraintParser.unsigned_return unsigned9 = null;

        Reference reference10 = null;

        Reference reference11 = null;


        try {
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:60:2: ( unsigned reference | reference | unsigned NEGATIVE reference | NEGATIVE reference )
            int alt5=4;
            switch ( input.LA(1) ) {
            case NUMBER:
                {
                int LA5_1 = input.LA(2);

                if ( (LA5_1==IDENTIFIER) ) {
                    alt5=1;
                }
                else if ( (LA5_1==NEGATIVE) ) {
                    alt5=3;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 5, 1, input);

                    throw nvae;
                }
                }
                break;
            case IDENTIFIER:
                {
                alt5=2;
                }
                break;
            case NEGATIVE:
                {
                alt5=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 5, 0, input);

                throw nvae;
            }

            switch (alt5) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:60:4: unsigned reference
                    {
                    pushFollow(FOLLOW_unsigned_in_weightedTermFirst167);
                    unsigned6=unsigned();

                    state._fsp--;

                    pushFollow(FOLLOW_reference_in_weightedTermFirst169);
                    reference7=reference();

                    state._fsp--;

                    value = new WeightedTerm(Integer.parseInt((unsigned6!=null?input.toString(unsigned6.start,unsigned6.stop):null)), true, reference7);

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:61:4: reference
                    {
                    pushFollow(FOLLOW_reference_in_weightedTermFirst176);
                    reference8=reference();

                    state._fsp--;

                    value = new WeightedTerm(1, true, reference8);

                    }
                    break;
                case 3 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:62:4: unsigned NEGATIVE reference
                    {
                    pushFollow(FOLLOW_unsigned_in_weightedTermFirst183);
                    unsigned9=unsigned();

                    state._fsp--;

                    match(input,NEGATIVE,FOLLOW_NEGATIVE_in_weightedTermFirst185); 
                    pushFollow(FOLLOW_reference_in_weightedTermFirst187);
                    reference10=reference();

                    state._fsp--;

                    value = new WeightedTerm(Integer.parseInt((unsigned9!=null?input.toString(unsigned9.start,unsigned9.stop):null)), false, reference10);

                    }
                    break;
                case 4 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:63:4: NEGATIVE reference
                    {
                    match(input,NEGATIVE,FOLLOW_NEGATIVE_in_weightedTermFirst194); 
                    pushFollow(FOLLOW_reference_in_weightedTermFirst196);
                    reference11=reference();

                    state._fsp--;

                    value = new WeightedTerm(1, false, reference11);

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return value;
    }
    // $ANTLR end "weightedTermFirst"


    // $ANTLR start "weightedTerm"
    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:65:1: weightedTerm returns [WeightedTerm value] : ( sign unsigned reference | sign reference | sign unsigned NEGATIVE reference | sign NEGATIVE reference );
    public final WeightedTerm weightedTerm() throws RecognitionException {
        WeightedTerm value = null;

        int sign12 = 0;

        ConstraintParser.unsigned_return unsigned13 = null;

        Reference reference14 = null;

        int sign15 = 0;

        Reference reference16 = null;

        int sign17 = 0;

        ConstraintParser.unsigned_return unsigned18 = null;

        Reference reference19 = null;

        int sign20 = 0;

        Reference reference21 = null;


        try {
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:66:2: ( sign unsigned reference | sign reference | sign unsigned NEGATIVE reference | sign NEGATIVE reference )
            int alt6=4;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==12) ) {
                switch ( input.LA(2) ) {
                case NUMBER:
                    {
                    int LA6_3 = input.LA(3);

                    if ( (LA6_3==IDENTIFIER) ) {
                        alt6=1;
                    }
                    else if ( (LA6_3==NEGATIVE) ) {
                        alt6=3;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("", 6, 3, input);

                        throw nvae;
                    }
                    }
                    break;
                case IDENTIFIER:
                    {
                    alt6=2;
                    }
                    break;
                case NEGATIVE:
                    {
                    alt6=4;
                    }
                    break;
                default:
                    NoViableAltException nvae =
                        new NoViableAltException("", 6, 1, input);

                    throw nvae;
                }

            }
            else if ( (LA6_0==13) ) {
                switch ( input.LA(2) ) {
                case NUMBER:
                    {
                    int LA6_3 = input.LA(3);

                    if ( (LA6_3==IDENTIFIER) ) {
                        alt6=1;
                    }
                    else if ( (LA6_3==NEGATIVE) ) {
                        alt6=3;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("", 6, 3, input);

                        throw nvae;
                    }
                    }
                    break;
                case IDENTIFIER:
                    {
                    alt6=2;
                    }
                    break;
                case NEGATIVE:
                    {
                    alt6=4;
                    }
                    break;
                default:
                    NoViableAltException nvae =
                        new NoViableAltException("", 6, 2, input);

                    throw nvae;
                }

            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 6, 0, input);

                throw nvae;
            }
            switch (alt6) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:66:4: sign unsigned reference
                    {
                    pushFollow(FOLLOW_sign_in_weightedTerm212);
                    sign12=sign();

                    state._fsp--;

                    pushFollow(FOLLOW_unsigned_in_weightedTerm214);
                    unsigned13=unsigned();

                    state._fsp--;

                    pushFollow(FOLLOW_reference_in_weightedTerm216);
                    reference14=reference();

                    state._fsp--;

                    value = new WeightedTerm(sign12*Integer.parseInt((unsigned13!=null?input.toString(unsigned13.start,unsigned13.stop):null)), true, reference14);

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:67:4: sign reference
                    {
                    pushFollow(FOLLOW_sign_in_weightedTerm223);
                    sign15=sign();

                    state._fsp--;

                    pushFollow(FOLLOW_reference_in_weightedTerm225);
                    reference16=reference();

                    state._fsp--;

                    value = new WeightedTerm(sign15, true, reference16);

                    }
                    break;
                case 3 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:68:4: sign unsigned NEGATIVE reference
                    {
                    pushFollow(FOLLOW_sign_in_weightedTerm232);
                    sign17=sign();

                    state._fsp--;

                    pushFollow(FOLLOW_unsigned_in_weightedTerm234);
                    unsigned18=unsigned();

                    state._fsp--;

                    match(input,NEGATIVE,FOLLOW_NEGATIVE_in_weightedTerm236); 
                    pushFollow(FOLLOW_reference_in_weightedTerm238);
                    reference19=reference();

                    state._fsp--;

                    value = new WeightedTerm(sign17*Integer.parseInt((unsigned18!=null?input.toString(unsigned18.start,unsigned18.stop):null)), false, reference19);

                    }
                    break;
                case 4 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:69:4: sign NEGATIVE reference
                    {
                    pushFollow(FOLLOW_sign_in_weightedTerm245);
                    sign20=sign();

                    state._fsp--;

                    match(input,NEGATIVE,FOLLOW_NEGATIVE_in_weightedTerm247); 
                    pushFollow(FOLLOW_reference_in_weightedTerm249);
                    reference21=reference();

                    state._fsp--;

                    value = new WeightedTerm(sign20, false, reference21);

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return value;
    }
    // $ANTLR end "weightedTerm"


    // $ANTLR start "reference"
    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:71:1: reference returns [Reference value] : ( feature | feature ATTRIBUTE attribute | feature ATTRIBUTE_SUM attribute );
    public final Reference reference() throws RecognitionException {
        Reference value = null;

        String feature22 = null;

        String feature23 = null;

        String attribute24 = null;

        String feature25 = null;

        String attribute26 = null;


        try {
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:72:2: ( feature | feature ATTRIBUTE attribute | feature ATTRIBUTE_SUM attribute )
            int alt7=3;
            int LA7_0 = input.LA(1);

            if ( (LA7_0==IDENTIFIER) ) {
                switch ( input.LA(2) ) {
                case RELATION:
                case 12:
                case 13:
                    {
                    alt7=1;
                    }
                    break;
                case ATTRIBUTE:
                    {
                    alt7=2;
                    }
                    break;
                case ATTRIBUTE_SUM:
                    {
                    alt7=3;
                    }
                    break;
                default:
                    NoViableAltException nvae =
                        new NoViableAltException("", 7, 1, input);

                    throw nvae;
                }

            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 7, 0, input);

                throw nvae;
            }
            switch (alt7) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:72:4: feature
                    {
                    pushFollow(FOLLOW_feature_in_reference264);
                    feature22=feature();

                    state._fsp--;

                    value = new Reference(feature22);

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:73:4: feature ATTRIBUTE attribute
                    {
                    pushFollow(FOLLOW_feature_in_reference271);
                    feature23=feature();

                    state._fsp--;

                    match(input,ATTRIBUTE,FOLLOW_ATTRIBUTE_in_reference273); 
                    pushFollow(FOLLOW_attribute_in_reference275);
                    attribute24=attribute();

                    state._fsp--;

                    value = new Reference(feature23, ReferenceType.ATTRIBUTE, attribute24);

                    }
                    break;
                case 3 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:74:4: feature ATTRIBUTE_SUM attribute
                    {
                    pushFollow(FOLLOW_feature_in_reference282);
                    feature25=feature();

                    state._fsp--;

                    match(input,ATTRIBUTE_SUM,FOLLOW_ATTRIBUTE_SUM_in_reference284); 
                    pushFollow(FOLLOW_attribute_in_reference286);
                    attribute26=attribute();

                    state._fsp--;

                    value = new Reference(feature25, ReferenceType.ATTRIBUTE_SUM, attribute26);

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return value;
    }
    // $ANTLR end "reference"


    // $ANTLR start "feature"
    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:76:1: feature returns [String value] : IDENTIFIER ;
    public final String feature() throws RecognitionException {
        String value = null;

        Token IDENTIFIER27=null;

        try {
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:77:2: ( IDENTIFIER )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:77:4: IDENTIFIER
            {
            IDENTIFIER27=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_feature301); 
            value = (IDENTIFIER27!=null?IDENTIFIER27.getText():null);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return value;
    }
    // $ANTLR end "feature"


    // $ANTLR start "attribute"
    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:78:1: attribute returns [String value] : IDENTIFIER ;
    public final String attribute() throws RecognitionException {
        String value = null;

        Token IDENTIFIER28=null;

        try {
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:79:2: ( IDENTIFIER )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:79:4: IDENTIFIER
            {
            IDENTIFIER28=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_attribute315); 
            value = (IDENTIFIER28!=null?IDENTIFIER28.getText():null);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return value;
    }
    // $ANTLR end "attribute"


    // $ANTLR start "degree"
    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:83:1: degree returns [int value] : ( sign unsigned | unsigned );
    public final int degree() throws RecognitionException {
        int value = 0;

        ConstraintParser.unsigned_return unsigned29 = null;

        int sign30 = 0;

        ConstraintParser.unsigned_return unsigned31 = null;


        try {
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:84:2: ( sign unsigned | unsigned )
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( ((LA8_0>=12 && LA8_0<=13)) ) {
                alt8=1;
            }
            else if ( (LA8_0==NUMBER) ) {
                alt8=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 8, 0, input);

                throw nvae;
            }
            switch (alt8) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:84:4: sign unsigned
                    {
                    pushFollow(FOLLOW_sign_in_degree346);
                    sign30=sign();

                    state._fsp--;

                    pushFollow(FOLLOW_unsigned_in_degree348);
                    unsigned29=unsigned();

                    state._fsp--;

                    value = Integer.parseInt((unsigned29!=null?input.toString(unsigned29.start,unsigned29.stop):null))*sign30;

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:85:4: unsigned
                    {
                    pushFollow(FOLLOW_unsigned_in_degree355);
                    unsigned31=unsigned();

                    state._fsp--;

                    value = Integer.parseInt((unsigned31!=null?input.toString(unsigned31.start,unsigned31.stop):null));

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return value;
    }
    // $ANTLR end "degree"


    // $ANTLR start "sign"
    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:87:1: sign returns [int value] : ( '-' | '+' );
    public final int sign() throws RecognitionException {
        int value = 0;

        try {
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:88:2: ( '-' | '+' )
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==12) ) {
                alt9=1;
            }
            else if ( (LA9_0==13) ) {
                alt9=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 9, 0, input);

                throw nvae;
            }
            switch (alt9) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:88:4: '-'
                    {
                    match(input,12,FOLLOW_12_in_sign370); 
                    value = -1;

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:89:3: '+'
                    {
                    match(input,13,FOLLOW_13_in_sign376); 
                    value = 1;

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return value;
    }
    // $ANTLR end "sign"

    public static class unsigned_return extends ParserRuleReturnScope {
        public int value;
    };

    // $ANTLR start "unsigned"
    // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:91:1: unsigned returns [int value] : NUMBER ;
    public final ConstraintParser.unsigned_return unsigned() throws RecognitionException {
        ConstraintParser.unsigned_return retval = new ConstraintParser.unsigned_return();
        retval.start = input.LT(1);

        Token NUMBER32=null;

        try {
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:92:2: ( NUMBER )
            // /home/sibi/workspace_old/Utilities/src/io/constraint/Constraint.g:92:4: NUMBER
            {
            NUMBER32=(Token)match(input,NUMBER,FOLLOW_NUMBER_in_unsigned392); 
            retval.value = Integer.parseInt((NUMBER32!=null?NUMBER32.getText():null));

            }

            retval.stop = input.LT(-1);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end "unsigned"

    // Delegated rules


 

    public static final BitSet FOLLOW_sum_in_constraint97 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_RELATION_in_constraint100 = new BitSet(new long[]{0x0000000000003400L});
    public static final BitSet FOLLOW_degree_in_constraint102 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_SEMICOLON_in_constraint104 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_constraint106 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_weightedTermFirst_in_sum119 = new BitSet(new long[]{0x0000000000003002L});
    public static final BitSet FOLLOW_sumTail_in_sum121 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_weightedTerm_in_sum130 = new BitSet(new long[]{0x0000000000003002L});
    public static final BitSet FOLLOW_sumTail_in_sum132 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_weightedTerm_in_sumTail147 = new BitSet(new long[]{0x0000000000003002L});
    public static final BitSet FOLLOW_sumTail_in_sumTail149 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unsigned_in_weightedTermFirst167 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_reference_in_weightedTermFirst169 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_reference_in_weightedTermFirst176 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unsigned_in_weightedTermFirst183 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NEGATIVE_in_weightedTermFirst185 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_reference_in_weightedTermFirst187 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_NEGATIVE_in_weightedTermFirst194 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_reference_in_weightedTermFirst196 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_weightedTerm212 = new BitSet(new long[]{0x0000000000003400L});
    public static final BitSet FOLLOW_unsigned_in_weightedTerm214 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_reference_in_weightedTerm216 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_weightedTerm223 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_reference_in_weightedTerm225 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_weightedTerm232 = new BitSet(new long[]{0x0000000000003400L});
    public static final BitSet FOLLOW_unsigned_in_weightedTerm234 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NEGATIVE_in_weightedTerm236 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_reference_in_weightedTerm238 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_weightedTerm245 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NEGATIVE_in_weightedTerm247 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_reference_in_weightedTerm249 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_in_reference264 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_in_reference271 = new BitSet(new long[]{0x0000000000000040L});
    public static final BitSet FOLLOW_ATTRIBUTE_in_reference273 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_attribute_in_reference275 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_in_reference282 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_ATTRIBUTE_SUM_in_reference284 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_attribute_in_reference286 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_feature301 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_attribute315 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_degree346 = new BitSet(new long[]{0x0000000000003400L});
    public static final BitSet FOLLOW_unsigned_in_degree348 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unsigned_in_degree355 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_12_in_sign370 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_13_in_sign376 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_NUMBER_in_unsigned392 = new BitSet(new long[]{0x0000000000000002L});

}
