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
// $ANTLR 3.3 Nov 30, 2010 12:45:30 /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g 2011-04-19 19:07:18

package de.ovgu.featureide.fm.extended.ui.io.objective;

import de.ovgu.featureide.fm.extended.ui.io.constraint.Reference;
import de.ovgu.featureide.fm.extended.ui.io.constraint.ReferenceType;
import de.ovgu.featureide.fm.extended.ui.io.constraint.WeightedTerm;

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

public class ObjectiveParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "SEMICOLON", "NEGATIVE", "ATTRIBUTE", "ATTRIBUTE_SUM", "IDENTIFIER", "NUMBER", "WS", "'-'", "'+'"
    };
    public static final int EOF=-1;
    public static final int T__11=11;
    public static final int T__12=12;
    public static final int SEMICOLON=4;
    public static final int NEGATIVE=5;
    public static final int ATTRIBUTE=6;
    public static final int ATTRIBUTE_SUM=7;
    public static final int IDENTIFIER=8;
    public static final int NUMBER=9;
    public static final int WS=10;

    // delegates
    // delegators


        public ObjectiveParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public ObjectiveParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return ObjectiveParser.tokenNames; }
    public String getGrammarFileName() { return "/home/sibi/workspace_old/Utilities/src/io/objective/Objective.g"; }


    	private boolean error = false;

    	@Override
    	public void reportError(RecognitionException e) {
    		this.error = true;
    		//super.reportError(e);
    	}

    	public boolean hadError() {
    		return error;
    	}



    // $ANTLR start "objective"
    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:50:1: objective returns [List<WeightedTerm> value] : sum[wTerms] SEMICOLON EOF ;
    public final List<WeightedTerm> objective() throws RecognitionException {
        List<WeightedTerm> value = null;


        List<WeightedTerm> wTerms = new ArrayList<WeightedTerm>();

        try {
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:54:2: ( sum[wTerms] SEMICOLON EOF )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:54:4: sum[wTerms] SEMICOLON EOF
            {
            pushFollow(FOLLOW_sum_in_objective97);
            sum(wTerms);

            state._fsp--;

            match(input,SEMICOLON,FOLLOW_SEMICOLON_in_objective100); 
            match(input,EOF,FOLLOW_EOF_in_objective102); 
            value = wTerms;

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
    // $ANTLR end "objective"


    // $ANTLR start "sum"
    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:56:1: sum[List<WeightedTerm> wTerms] : ( weightedTermFirst ( sumTail[wTerms] )? | weightedTerm ( sumTail[wTerms] )? );
    public final void sum(List<WeightedTerm> wTerms) throws RecognitionException {
        WeightedTerm weightedTermFirst1 = null;

        WeightedTerm weightedTerm2 = null;


        try {
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:57:2: ( weightedTermFirst ( sumTail[wTerms] )? | weightedTerm ( sumTail[wTerms] )? )
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0==NEGATIVE||(LA3_0>=IDENTIFIER && LA3_0<=NUMBER)) ) {
                alt3=1;
            }
            else if ( ((LA3_0>=11 && LA3_0<=12)) ) {
                alt3=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;
            }
            switch (alt3) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:57:4: weightedTermFirst ( sumTail[wTerms] )?
                    {
                    pushFollow(FOLLOW_weightedTermFirst_in_sum116);
                    weightedTermFirst1=weightedTermFirst();

                    state._fsp--;

                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:57:22: ( sumTail[wTerms] )?
                    int alt1=2;
                    int LA1_0 = input.LA(1);

                    if ( ((LA1_0>=11 && LA1_0<=12)) ) {
                        alt1=1;
                    }
                    switch (alt1) {
                        case 1 :
                            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:57:22: sumTail[wTerms]
                            {
                            pushFollow(FOLLOW_sumTail_in_sum118);
                            sumTail(wTerms);

                            state._fsp--;


                            }
                            break;

                    }

                    wTerms.add(weightedTermFirst1);

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:58:4: weightedTerm ( sumTail[wTerms] )?
                    {
                    pushFollow(FOLLOW_weightedTerm_in_sum127);
                    weightedTerm2=weightedTerm();

                    state._fsp--;

                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:58:17: ( sumTail[wTerms] )?
                    int alt2=2;
                    int LA2_0 = input.LA(1);

                    if ( ((LA2_0>=11 && LA2_0<=12)) ) {
                        alt2=1;
                    }
                    switch (alt2) {
                        case 1 :
                            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:58:17: sumTail[wTerms]
                            {
                            pushFollow(FOLLOW_sumTail_in_sum129);
                            sumTail(wTerms);

                            state._fsp--;


                            }
                            break;

                    }

                    wTerms.add(weightedTerm2);

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
    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:60:1: sumTail[List<WeightedTerm> wTerms] : weightedTerm ( sumTail[wTerms] )? ;
    public final void sumTail(List<WeightedTerm> wTerms) throws RecognitionException {
        WeightedTerm weightedTerm3 = null;


        try {
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:61:2: ( weightedTerm ( sumTail[wTerms] )? )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:61:4: weightedTerm ( sumTail[wTerms] )?
            {
            pushFollow(FOLLOW_weightedTerm_in_sumTail144);
            weightedTerm3=weightedTerm();

            state._fsp--;

            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:61:17: ( sumTail[wTerms] )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( ((LA4_0>=11 && LA4_0<=12)) ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:61:17: sumTail[wTerms]
                    {
                    pushFollow(FOLLOW_sumTail_in_sumTail146);
                    sumTail(wTerms);

                    state._fsp--;


                    }
                    break;

            }

            wTerms.add(weightedTerm3);

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
    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:63:1: weightedTermFirst returns [WeightedTerm value] : ( unsigned reference | reference | unsigned NEGATIVE reference | NEGATIVE reference );
    public final WeightedTerm weightedTermFirst() throws RecognitionException {
        WeightedTerm value = null;

        ObjectiveParser.unsigned_return unsigned4 = null;

        Reference reference5 = null;

        Reference reference6 = null;

        ObjectiveParser.unsigned_return unsigned7 = null;

        Reference reference8 = null;

        Reference reference9 = null;


        try {
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:64:2: ( unsigned reference | reference | unsigned NEGATIVE reference | NEGATIVE reference )
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
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:64:4: unsigned reference
                    {
                    pushFollow(FOLLOW_unsigned_in_weightedTermFirst164);
                    unsigned4=unsigned();

                    state._fsp--;

                    pushFollow(FOLLOW_reference_in_weightedTermFirst166);
                    reference5=reference();

                    state._fsp--;

                    value = new WeightedTerm(Integer.parseInt((unsigned4!=null?input.toString(unsigned4.start,unsigned4.stop):null)), true, reference5);

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:65:4: reference
                    {
                    pushFollow(FOLLOW_reference_in_weightedTermFirst173);
                    reference6=reference();

                    state._fsp--;

                    value = new WeightedTerm(1, true, reference6);

                    }
                    break;
                case 3 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:66:4: unsigned NEGATIVE reference
                    {
                    pushFollow(FOLLOW_unsigned_in_weightedTermFirst180);
                    unsigned7=unsigned();

                    state._fsp--;

                    match(input,NEGATIVE,FOLLOW_NEGATIVE_in_weightedTermFirst182); 
                    pushFollow(FOLLOW_reference_in_weightedTermFirst184);
                    reference8=reference();

                    state._fsp--;

                    value = new WeightedTerm(Integer.parseInt((unsigned7!=null?input.toString(unsigned7.start,unsigned7.stop):null)), false, reference8);

                    }
                    break;
                case 4 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:67:4: NEGATIVE reference
                    {
                    match(input,NEGATIVE,FOLLOW_NEGATIVE_in_weightedTermFirst191); 
                    pushFollow(FOLLOW_reference_in_weightedTermFirst193);
                    reference9=reference();

                    state._fsp--;

                    value = new WeightedTerm(1, false, reference9);

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
    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:69:1: weightedTerm returns [WeightedTerm value] : ( sign unsigned reference | sign reference | sign unsigned NEGATIVE reference | sign NEGATIVE reference );
    public final WeightedTerm weightedTerm() throws RecognitionException {
        WeightedTerm value = null;

        int sign10 = 0;

        ObjectiveParser.unsigned_return unsigned11 = null;

        Reference reference12 = null;

        int sign13 = 0;

        Reference reference14 = null;

        int sign15 = 0;

        ObjectiveParser.unsigned_return unsigned16 = null;

        Reference reference17 = null;

        int sign18 = 0;

        Reference reference19 = null;


        try {
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:70:2: ( sign unsigned reference | sign reference | sign unsigned NEGATIVE reference | sign NEGATIVE reference )
            int alt6=4;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==11) ) {
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
            else if ( (LA6_0==12) ) {
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
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:70:4: sign unsigned reference
                    {
                    pushFollow(FOLLOW_sign_in_weightedTerm209);
                    sign10=sign();

                    state._fsp--;

                    pushFollow(FOLLOW_unsigned_in_weightedTerm211);
                    unsigned11=unsigned();

                    state._fsp--;

                    pushFollow(FOLLOW_reference_in_weightedTerm213);
                    reference12=reference();

                    state._fsp--;

                    value = new WeightedTerm(sign10*Integer.parseInt((unsigned11!=null?input.toString(unsigned11.start,unsigned11.stop):null)), true, reference12);

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:71:4: sign reference
                    {
                    pushFollow(FOLLOW_sign_in_weightedTerm220);
                    sign13=sign();

                    state._fsp--;

                    pushFollow(FOLLOW_reference_in_weightedTerm222);
                    reference14=reference();

                    state._fsp--;

                    value = new WeightedTerm(sign13, true, reference14);

                    }
                    break;
                case 3 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:72:4: sign unsigned NEGATIVE reference
                    {
                    pushFollow(FOLLOW_sign_in_weightedTerm229);
                    sign15=sign();

                    state._fsp--;

                    pushFollow(FOLLOW_unsigned_in_weightedTerm231);
                    unsigned16=unsigned();

                    state._fsp--;

                    match(input,NEGATIVE,FOLLOW_NEGATIVE_in_weightedTerm233); 
                    pushFollow(FOLLOW_reference_in_weightedTerm235);
                    reference17=reference();

                    state._fsp--;

                    value = new WeightedTerm(sign15*Integer.parseInt((unsigned16!=null?input.toString(unsigned16.start,unsigned16.stop):null)), false, reference17);

                    }
                    break;
                case 4 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:73:4: sign NEGATIVE reference
                    {
                    pushFollow(FOLLOW_sign_in_weightedTerm242);
                    sign18=sign();

                    state._fsp--;

                    match(input,NEGATIVE,FOLLOW_NEGATIVE_in_weightedTerm244); 
                    pushFollow(FOLLOW_reference_in_weightedTerm246);
                    reference19=reference();

                    state._fsp--;

                    value = new WeightedTerm(sign18, false, reference19);

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
    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:75:1: reference returns [Reference value] : ( feature | feature ATTRIBUTE attribute | feature ATTRIBUTE_SUM attribute );
    public final Reference reference() throws RecognitionException {
        Reference value = null;

        String feature20 = null;

        String feature21 = null;

        String attribute22 = null;

        String feature23 = null;

        String attribute24 = null;


        try {
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:76:2: ( feature | feature ATTRIBUTE attribute | feature ATTRIBUTE_SUM attribute )
            int alt7=3;
            int LA7_0 = input.LA(1);

            if ( (LA7_0==IDENTIFIER) ) {
                switch ( input.LA(2) ) {
                case SEMICOLON:
                case 11:
                case 12:
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
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:76:4: feature
                    {
                    pushFollow(FOLLOW_feature_in_reference261);
                    feature20=feature();

                    state._fsp--;

                    value = new Reference(feature20);

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:77:4: feature ATTRIBUTE attribute
                    {
                    pushFollow(FOLLOW_feature_in_reference268);
                    feature21=feature();

                    state._fsp--;

                    match(input,ATTRIBUTE,FOLLOW_ATTRIBUTE_in_reference270); 
                    pushFollow(FOLLOW_attribute_in_reference272);
                    attribute22=attribute();

                    state._fsp--;

                    value = new Reference(feature21, ReferenceType.ATTRIBUTE, attribute22);

                    }
                    break;
                case 3 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:78:4: feature ATTRIBUTE_SUM attribute
                    {
                    pushFollow(FOLLOW_feature_in_reference279);
                    feature23=feature();

                    state._fsp--;

                    match(input,ATTRIBUTE_SUM,FOLLOW_ATTRIBUTE_SUM_in_reference281); 
                    pushFollow(FOLLOW_attribute_in_reference283);
                    attribute24=attribute();

                    state._fsp--;

                    value = new Reference(feature23, ReferenceType.ATTRIBUTE_SUM, attribute24);

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
    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:80:1: feature returns [String value] : IDENTIFIER ;
    public final String feature() throws RecognitionException {
        String value = null;

        Token IDENTIFIER25=null;

        try {
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:81:2: ( IDENTIFIER )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:81:4: IDENTIFIER
            {
            IDENTIFIER25=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_feature298); 
            value = (IDENTIFIER25!=null?IDENTIFIER25.getText():null);

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
    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:82:1: attribute returns [String value] : IDENTIFIER ;
    public final String attribute() throws RecognitionException {
        String value = null;

        Token IDENTIFIER26=null;

        try {
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:83:2: ( IDENTIFIER )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:83:4: IDENTIFIER
            {
            IDENTIFIER26=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_attribute312); 
            value = (IDENTIFIER26!=null?IDENTIFIER26.getText():null);

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


    // $ANTLR start "sign"
    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:85:1: sign returns [int value] : ( '-' | '+' );
    public final int sign() throws RecognitionException {
        int value = 0;

        try {
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:86:2: ( '-' | '+' )
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==11) ) {
                alt8=1;
            }
            else if ( (LA8_0==12) ) {
                alt8=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 8, 0, input);

                throw nvae;
            }
            switch (alt8) {
                case 1 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:86:4: '-'
                    {
                    match(input,11,FOLLOW_11_in_sign327); 
                    value = -1;

                    }
                    break;
                case 2 :
                    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:87:3: '+'
                    {
                    match(input,12,FOLLOW_12_in_sign333); 
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
    // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:89:1: unsigned returns [int value] : NUMBER ;
    public final ObjectiveParser.unsigned_return unsigned() throws RecognitionException {
        ObjectiveParser.unsigned_return retval = new ObjectiveParser.unsigned_return();
        retval.start = input.LT(1);

        Token NUMBER27=null;

        try {
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:90:2: ( NUMBER )
            // /home/sibi/workspace_old/Utilities/src/io/objective/Objective.g:90:4: NUMBER
            {
            NUMBER27=(Token)match(input,NUMBER,FOLLOW_NUMBER_in_unsigned349); 
            retval.value = Integer.parseInt((NUMBER27!=null?NUMBER27.getText():null));

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


 

    public static final BitSet FOLLOW_sum_in_objective97 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_SEMICOLON_in_objective100 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_objective102 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_weightedTermFirst_in_sum116 = new BitSet(new long[]{0x0000000000001802L});
    public static final BitSet FOLLOW_sumTail_in_sum118 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_weightedTerm_in_sum127 = new BitSet(new long[]{0x0000000000001802L});
    public static final BitSet FOLLOW_sumTail_in_sum129 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_weightedTerm_in_sumTail144 = new BitSet(new long[]{0x0000000000001802L});
    public static final BitSet FOLLOW_sumTail_in_sumTail146 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unsigned_in_weightedTermFirst164 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_reference_in_weightedTermFirst166 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_reference_in_weightedTermFirst173 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unsigned_in_weightedTermFirst180 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NEGATIVE_in_weightedTermFirst182 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_reference_in_weightedTermFirst184 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_NEGATIVE_in_weightedTermFirst191 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_reference_in_weightedTermFirst193 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_weightedTerm209 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_unsigned_in_weightedTerm211 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_reference_in_weightedTerm213 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_weightedTerm220 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_reference_in_weightedTerm222 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_weightedTerm229 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_unsigned_in_weightedTerm231 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NEGATIVE_in_weightedTerm233 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_reference_in_weightedTerm235 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_weightedTerm242 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NEGATIVE_in_weightedTerm244 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_reference_in_weightedTerm246 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_in_reference261 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_in_reference268 = new BitSet(new long[]{0x0000000000000040L});
    public static final BitSet FOLLOW_ATTRIBUTE_in_reference270 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_attribute_in_reference272 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_in_reference279 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_ATTRIBUTE_SUM_in_reference281 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_attribute_in_reference283 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_feature298 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_attribute312 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_11_in_sign327 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_12_in_sign333 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_NUMBER_in_unsigned349 = new BitSet(new long[]{0x0000000000000002L});

}
