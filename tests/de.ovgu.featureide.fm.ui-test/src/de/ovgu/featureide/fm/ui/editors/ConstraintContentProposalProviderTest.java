/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

/**
 * test class for ConstraintContentProposalProvider
 *
 * @author Fabian Benduhn
 */
public class ConstraintContentProposalProviderTest {

	// private static final String[] PROPS_OPERATORS = {"and","iff","implies","or"};
	private static final String[] PROPS_NONE = new String[0];
	// private static final String[] PROPS_FEATURES = {"not","FeatureA","FeatureB","FeatureC"};
	static final int CURRENT = ConstraintContentProposalProvider.CURRENT;
	static final int LAST = ConstraintContentProposalProvider.LAST;

	Set<String> features = new HashSet<String>();

	@Test
	public void getWordsCursorAtFirstPos() {
		final String content = "|abcdef";
		final String expectedCurrentWord = "";
		final String expectedLastWord = "";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	@Test
	public void getWordsCursorAtFirstPosWithWhiteSpaces() {
		final String content = "|   abcdef";
		final String expectedCurrentWord = "";
		final String expectedLastWord = "";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	@Test
	public void getWordsCursorAtThirdPosWithWhiteSpaces() {
		final String content = "   |abcdef";
		final String expectedCurrentWord = "";
		final String expectedLastWord = "";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	@Test
	public void getWordsCursorAtEndOfFirstWord() {
		final String content = "abcdef|";
		final String expectedCurrentWord = "abcdef";
		final String expectedLastWord = "";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	@Test
	public void getWordsCursorAfterFirstWord() {
		final String content = "abcdef |";
		final String expectedCurrentWord = "";
		final String expectedLastWord = "abcdef";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	@Test
	public void getWordsCursorAfterFirstWord2() {
		final String content = "abcdef   | ";
		final String expectedCurrentWord = "";
		final String expectedLastWord = "abcdef";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	@Test
	public void getWordsCursorAtSecWord() {
		final String content = "abcdef g|hijk";
		final String expectedCurrentWord = "g";
		final String expectedLastWord = "abcdef";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	@Test
	public void getWordsCursorAtSecWord2() {
		final String content = "abcdef gh|ijk";
		final String expectedCurrentWord = "gh";
		final String expectedLastWord = "abcdef";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	@Test
	public void getWordsWithParantheses() {
		final String content = "(ab|cdef)";
		final String expectedCurrentWord = "ab";
		final String expectedLastWord = "(";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	@Test
	public void getWordsWithParantheses2() {
		final String content = "(  ab|cdef)";
		final String expectedCurrentWord = "ab";
		final String expectedLastWord = "(";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	@Test
	public void getWordsWithParantheses3() {
		final String content = "(  abcdef) (a|sddasd";
		final String expectedCurrentWord = "a";
		final String expectedLastWord = "(";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	@Test
	public void getWordsWithParantheses4() {
		final String content = "(  abcdef) (|asddasd";
		final String expectedCurrentWord = "";
		final String expectedLastWord = "(";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	@Test
	public void getWordsWithParantheses5() {
		final String content = "(abcdef) (word |";
		final String expectedCurrentWord = "";
		final String expectedLastWord = "word";
		testGetWords(content, expectedCurrentWord, expectedLastWord);
	}

	private void testGetWords(String content, String current, String last) {
		final String[] words = ConstraintContentProposalProvider.getWords(removeCursorFromString(content), getCursorPos(content));
		assertEquals(current, words[CURRENT].trim());
		assertEquals(last, words[LAST].trim());
	}

	@Before
	public void init() {
		features.add("FeatureA");
		features.add("FeatureB");
		features.add("FeatureC");
	}
//	@Test
//	public void getProposalsEmptyString(){
//		String content = "|";
//		String[] expectedProps = PROPS_FEATURES;
//		testGetProposals(content,expectedProps );
//
//	}
//	@Test
//	public void getProposalsEmptyStringWithWhitespaces(){
//		String content = "   |";
//		String[] expectedProps = PROPS_FEATURES;
//		testGetProposals(content,expectedProps );
//
//	}
//	@Test
//	public void getProposalsCursorAfterFeature(){
//		String content = "FeatureA |";
//		String[] expectedProps = PROPS_OPERATORS;
//		testGetProposals(content,expectedProps );
//
//	}

//	@Test
//	public void getProposalsCursorAfterFeature2(){
//		String content = "FeatureA  | ";
//		String[] expectedProps = PROPS_OPERATORS;
//		testGetProposals(content,expectedProps );
//
//	}
	@Test
	public void getProposalsCursorAfterFeature3() {
		final String content = "FeatureA and FeatureB|";
		final String[] expectedProps = PROPS_NONE;
		testGetProposals(content, expectedProps);

	}
//	@Test
//	public void getProposalsCursorAfterFeature4(){
//		String content = "FeatureA and FeatureB |";
//		String[] expectedProps = PROPS_OPERATORS;
//		testGetProposals(content,expectedProps );
//
//	}
//
//	@Test
//	public void getProposalsCursorAfterFeatureWithParantheses(){
//		String content = "(FeatureA and FeatureB) |  ";
//		String[] expectedProps = PROPS_OPERATORS;
//		testGetProposals(content,expectedProps );
//
//	}

//	@Test
//	public void getProposalsCursorAfterFeatureWithParantheses2(){
//		String content = "(FeatureA and FeatureB)|  ";
//		String[] expectedProps = PROPS_NONE;
//		testGetProposals(content,expectedProps );
//
//	}
//	@Test
//	public void getProposalsCursorAfterFeatureWithParantheses3(){
//		String content = "(FeatureA and FeatureB )|  ";
//		String[] expectedProps = PROPS_NONE;
//		testGetProposals(content,expectedProps );
//
//	}
	@Test
	public void getProposalsCursorAfterAnd() {
		final String content = "FeatureA and| ";
		final String[] expectedProps = PROPS_NONE;
		testGetProposals(content, expectedProps);

	}

//	@Test
//	public void getProposalsCursorAfterAnd2(){
//		String content = "FeatureA and |";
//		String[] expectedProps = PROPS_FEATURES;
//		testGetProposals(content,expectedProps );
//
//	}

	@Test
	public void getProposalsPrefixOfFeature() {
		final String content = "Fea|  ";
		final String[] expectedProps = { "FeatureA", "FeatureB", "FeatureC" };
		testGetProposals(content, expectedProps);

	}

	@Test
	public void getProposalsCursorAfterNot() {
		final String content = "not|";
		final String[] expectedProps = PROPS_NONE;
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

//	@Test
//	public void getProposalsLastWordStartsWithParantheses(){
//		String content = "(FeatureA iff FeatureB) and (FeatureA |";
//		String[] expectedProps = PROPS_OPERATORS;
//		testGetProposals(content,expectedProps );
//
//	}

//	@Test
//	public void getProposalsOperatorNameAnd(){
//		features.add("And");
//		String content = "\"|";
//		String[] expectedProps = {"\"And\""};
//		testGetProposals(content,expectedProps);
//	}

//	@Test
//	public void getProposalsOperatorNameOr(){
//		features.add("Or");
//		String content = "\"|";
//		String[] expectedProps = {"\"Or\""};
//		testGetProposals(content,expectedProps);
//	}

//	@Test
//	public void getProposalsOperatorNameNot(){
//		features.add("Not");
//		String content = "\"|";
//		String[] expectedProps = {"\"Not\""};
//		testGetProposals(content,expectedProps);
//	}

//	@Test
//	public void getProposalsWhiteSpace(){
//		features.clear();
//		features.add("Feature A");
//		features.add("Feature B");
//		String content = "\"|";
//		String[] expectedProps = {"\"Feature A\"","\"Feature B\""};
//		testGetProposals(content,expectedProps);
//	}

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
