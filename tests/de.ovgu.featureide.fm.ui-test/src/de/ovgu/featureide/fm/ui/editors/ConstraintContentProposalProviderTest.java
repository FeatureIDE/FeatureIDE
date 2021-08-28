/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.jface.fieldassist.IContentProposal;
import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.fm.ui.editors.ConstraintContentProposalProvider.ProposalContext;

/**
 * test class for ConstraintContentProposalProvider
 *
 * @author Fabian Benduhn
 * @author Rahel Arens
 * @author Johannes Herschel
 */
public class ConstraintContentProposalProviderTest {

	private static final String[] PROPS_OPERATORS = { "and", "iff", "implies", "or" };
	private static final String[] PROPS_NONE = new String[0];
	private static final String[] PROPS_FEATURES = { "not", "FeatureA", "FeatureB", "FeatureC" };

	Set<String> features = new HashSet<String>();

	@Test
	public void getProposalContextCursorAtFirstPos() {
		final String content = "|abcdef";
		final ProposalContext expectedContext = new ProposalContext(false, "", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextCursorAtFirstPosWithWhiteSpaces() {
		final String content = "|   abcdef";
		final ProposalContext expectedContext = new ProposalContext(false, "", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextCursorAtThirdPosWithWhiteSpaces() {
		final String content = "   |abcdef";
		final ProposalContext expectedContext = new ProposalContext(false, "", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextCursorAtEndOfFirstWord() {
		final String content = "abcdef|";
		final ProposalContext expectedContext = new ProposalContext(false, "abcdef", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextCursorAfterFirstWord() {
		final String content = "abcdef |";
		final ProposalContext expectedContext = new ProposalContext(true, "", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextCursorAfterFirstWord2() {
		final String content = "abcdef   | ";
		final ProposalContext expectedContext = new ProposalContext(true, "", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextCursorAtSecWord() {
		final String content = "abcdef g|hijk";
		final ProposalContext expectedContext = new ProposalContext(true, "g", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextCursorAtSecWord2() {
		final String content = "abcdef gh|ijk";
		final ProposalContext expectedContext = new ProposalContext(true, "gh", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextWithParantheses() {
		final String content = "(ab|cdef)";
		final ProposalContext expectedContext = new ProposalContext(false, "ab", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextWithParantheses2() {
		final String content = "(  ab|cdef)";
		final ProposalContext expectedContext = new ProposalContext(false, "ab", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextWithParantheses3() {
		final String content = "(  abcdef) (a|sddasd";
		final ProposalContext expectedContext = new ProposalContext(true, "a", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextWithParantheses4() {
		final String content = "(  abcdef) (|asddasd";
		final ProposalContext expectedContext = new ProposalContext(true, "", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextWithParantheses5() {
		final String content = "(abcdef) (word |";
		final ProposalContext expectedContext = new ProposalContext(true, "", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextOperator1() {
		final String content = "abc and |";
		final ProposalContext expectedContext = new ProposalContext(false, "", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextOperator2() {
		final String content = "abc or    def|";
		final ProposalContext expectedContext = new ProposalContext(false, "def", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextQuotationMarkCurrent1() {
		final String content = "\"|";
		final ProposalContext expectedContext = new ProposalContext(false, "", true);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextQuotationMarkCurrent2() {
		final String content = "\"ab|\"";
		final ProposalContext expectedContext = new ProposalContext(false, "ab", true);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextQuotationMarkCurrent3() {
		final String content = "abc \"|";
		final ProposalContext expectedContext = new ProposalContext(true, "", true);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextQuotationMarkCurrent4() {
		final String content = "iff \"|";
		final ProposalContext expectedContext = new ProposalContext(false, "", true);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextQuotationMarkCurrent5() {
		final String content = "\"abc |";
		final ProposalContext expectedContext = new ProposalContext(false, "abc ", true);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextQuotationMarkCurrent6() {
		final String content = "\"abc d|";
		final ProposalContext expectedContext = new ProposalContext(false, "abc d", true);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextQuotationMarkLast1() {
		final String content = "\"abc\" |";
		final ProposalContext expectedContext = new ProposalContext(true, "", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextQuotationMarkLast2() {
		final String content = "\"ab cd\" |";
		final ProposalContext expectedContext = new ProposalContext(true, "", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextQuotationMarkLast3() {
		final String content = "\"and\" |";
		final ProposalContext expectedContext = new ProposalContext(true, "", false);
		testGetWords(content, expectedContext);
	}

	@Test
	public void getProposalContextQuotationMarkCurrentLast() {
		final String content = "\" abcd \" \"|";
		final ProposalContext expectedContext = new ProposalContext(true, "", true);
		testGetWords(content, expectedContext);
	}

	private void testGetWords(String content, ProposalContext expectedContext) {
		final ProposalContext context = ConstraintContentProposalProvider.getProposalContext(removeCursorFromString(content), getCursorPos(content));
		assertEquals(expectedContext.currentWord, context.currentWord);
		assertEquals(expectedContext.featureBefore, context.featureBefore);
		assertEquals(expectedContext.quotationMark, context.quotationMark);
	}

	@Before
	public void init() {
		features.add("FeatureA");
		features.add("FeatureB");
		features.add("FeatureC");
	}

	@Test
	public void getProposalsEmptyString() {
		final String content = "|";
		final String[] expectedProps = PROPS_FEATURES;
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsEmptyStringWithWhitespaces() {
		final String content = "   |";
		final String[] expectedProps = PROPS_FEATURES;
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsCursorAfterFeature() {
		final String content = "FeatureA |";
		final String[] expectedProps = PROPS_OPERATORS;
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsCursorAfterFeature2() {
		final String content = "FeatureA  | ";
		final String[] expectedProps = PROPS_OPERATORS;
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsCursorAfterFeature3() {
		final String content = "FeatureA and FeatureB|";
		final String[] expectedProps = { "FeatureB" };
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsCursorAfterFeature4() {
		final String content = "FeatureA and FeatureB |";
		final String[] expectedProps = PROPS_OPERATORS;
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsCursorAfterFeatureWithParantheses() {
		final String content = "(FeatureA and FeatureB) |  ";
		final String[] expectedProps = PROPS_OPERATORS;
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsCursorAfterFeatureWithParantheses2() {
		final String content = "(FeatureA and FeatureB)|  ";
		final String[] expectedProps = PROPS_OPERATORS;
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsCursorAfterFeatureWithParantheses3() {
		final String content = "(FeatureA and FeatureB )|  ";
		final String[] expectedProps = PROPS_OPERATORS;
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsCursorAfterAnd() {
		final String content = "FeatureA and| ";
		final String[] expectedProps = { "and" };
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsCursorAfterAnd2() {
		final String content = "FeatureA and |";
		final String[] expectedProps = PROPS_FEATURES;
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsPrefixOfFeature() {
		final String content = "Fea|  ";
		final String[] expectedProps = { "FeatureA", "FeatureB", "FeatureC" };
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsCursorAfterNot() {
		final String content = "not|";
		final String[] expectedProps = { "not" };
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsPrefixOfFeatureAfterNot() {
		final String content = "not Fea|";
		final String[] expectedProps = { "FeatureA", "FeatureB", "FeatureC" };
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsPrefixOfAnd() {
		final String content = "FeatureA a|";
		final String[] expectedProps = { "and" };
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsPrefixOfOr() {
		final String content = "FeatureA o|";
		final String[] expectedProps = { "or" };
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsPrefixOfIff() {
		final String content = "FeatureA i|";
		final String[] expectedProps = { "iff", "implies" };
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsLastWordStartsWithParantheses() {
		final String content = "(FeatureA iff FeatureB) and (FeatureA |";
		final String[] expectedProps = PROPS_OPERATORS;
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsOperatorNameAnd() {
		features.add("and");
		final String content = "\"|";
		final String[] expectedProps = { "and (Feature)" };
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsOperatorNameOr() {
		features.add("or");
		final String content = "\"|";
		final String[] expectedProps = { "or (Feature)" };
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsOperatorNameNot() {
		features.add("not");
		final String content = "\"|";
		final String[] expectedProps = { "not (Feature)" };
		testGetProposals(content, expectedProps);
	}

	@Test
	public void getProposalsWhiteSpace() {
		features.clear();
		features.add("Feature A");
		features.add("Feature B");
		final String content = "\"|";
		final String[] expectedProps = { "Feature A", "Feature B" };
		testGetProposals(content, expectedProps);
	}

	private void testGetProposals(String content, String[] expectedProps) {
		final Set<String> expectedPropsSet = new HashSet<String>();
		expectedPropsSet.addAll(Arrays.asList(expectedProps));
		final ConstraintContentProposalProvider propProv = new ConstraintContentProposalProvider(features);
		final IContentProposal[] proposals = propProv.getProposals(removeCursorFromString(content), getCursorPos(content));
		assertEquals(expectedProps.length, proposals.length);
		for (int i = 0; i < expectedProps.length; i++) {
			assertEquals(expectedProps[i], proposals[i].getContent());
		}

	}

	private int getCursorPos(String s) {
		assertTrue(s.contains("|"));
		return s.indexOf("|");

	}

	private String removeCursorFromString(String s) {
		assertTrue("String must contain cursor symbol", s.contains("|"));
		return s.replace("|", "");
	}

	@Test
	public void internalTestGetCursorPos() {
		final String s = "|";
		assertEquals(0, getCursorPos(s));
	}

	@Test
	public void internalTestGetCursorPos2() {
		final String s = "ab|";
		assertEquals(2, getCursorPos(s));
	}

	@Test
	public void internalTestRemoveCursorFromString() {
		final String s = "|";
		assertEquals("", removeCursorFromString(s));
	}

	@Test
	public void internalTestRemoveCursorFromString2() {
		final String s = "abcd|efg";
		assertEquals("abcdefg", removeCursorFromString(s));
	}
}
