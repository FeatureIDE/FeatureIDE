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
	
	//private static final String[] PROPS_OPERATORS = {"and","iff","implies","or"};
	private static final String[] PROPS_NONE = new String[0];
	//private static final String[] PROPS_FEATURES = {"not","FeatureA","FeatureB","FeatureC"};
	static final int CURRENT=ConstraintContentProposalProvider.CURRENT;
	static final int LAST=ConstraintContentProposalProvider.LAST;
	
	Set<String> features = new HashSet<String>();
	

		
	
	
	@Test
	public void getWordsCursorAtFirstPos(){
		String content = "|abcdef";
		String expectedCurrentWord = "";
		String expectedLastWord = "";
		testGetWords(content,expectedCurrentWord,expectedLastWord);
	}
	
	@Test
	public void getWordsCursorAtFirstPosWithWhiteSpaces(){
		String content = "|   abcdef";
		String expectedCurrentWord = "";
		String expectedLastWord = "";
		testGetWords(content,expectedCurrentWord,expectedLastWord);
	}
	@Test
	public void getWordsCursorAtThirdPosWithWhiteSpaces(){
		String content = "   |abcdef";
		String expectedCurrentWord = "";
		String expectedLastWord = "";
		testGetWords(content,expectedCurrentWord,expectedLastWord);
	}
	
	@Test
	public void getWordsCursorAtEndOfFirstWord(){
		String content = "abcdef|";
		String expectedCurrentWord = "abcdef";
		String expectedLastWord = "";
		testGetWords(content,expectedCurrentWord,expectedLastWord);
	}
	
	@Test
	public void getWordsCursorAfterFirstWord(){
		String content = "abcdef |";
		String expectedCurrentWord = "";
		String expectedLastWord = "abcdef";
		testGetWords(content,expectedCurrentWord,expectedLastWord);
	}
	
	@Test
	public void getWordsCursorAfterFirstWord2(){
		String content = "abcdef   | ";
		String expectedCurrentWord = "";
		String expectedLastWord = "abcdef";
		testGetWords(content,expectedCurrentWord,expectedLastWord);
	}
	
	@Test
	public void getWordsCursorAtSecWord(){
		String content = "abcdef g|hijk";
		String expectedCurrentWord = "g";
		String expectedLastWord = "abcdef";
		testGetWords(content,expectedCurrentWord,expectedLastWord);
	}
	@Test
	public void getWordsCursorAtSecWord2(){
		String content = "abcdef gh|ijk";
		String expectedCurrentWord = "gh";
		String expectedLastWord = "abcdef";
		testGetWords(content,expectedCurrentWord,expectedLastWord);
	}
	
	@Test
	public void getWordsWithParantheses(){
		String content = "(ab|cdef)";
		String expectedCurrentWord = "ab";
		String expectedLastWord = "(";
		testGetWords(content,expectedCurrentWord,expectedLastWord);
	}
	@Test
	public void getWordsWithParantheses2(){
		String content = "(  ab|cdef)";
		String expectedCurrentWord = "ab";
		String expectedLastWord = "(";
		testGetWords(content,expectedCurrentWord,expectedLastWord);
	}
	@Test
	public void getWordsWithParantheses3(){
		String content = "(  abcdef) (a|sddasd";
		String expectedCurrentWord = "a";
		String expectedLastWord = "(";
		testGetWords(content,expectedCurrentWord,expectedLastWord);
	}
	
	@Test
	public void getWordsWithParantheses4(){
		String content = "(  abcdef) (|asddasd";
		String expectedCurrentWord = "";
		String expectedLastWord = "(";
		testGetWords(content,expectedCurrentWord, expectedLastWord);
	}
	
	@Test
	public void getWordsWithParantheses5(){
		String content = "(abcdef) (word |";
		String expectedCurrentWord = "";
		String expectedLastWord = "word";
		testGetWords(content,expectedCurrentWord, expectedLastWord);
	}
	
	private void testGetWords(String content, String current, String last) {
		String[] words = ConstraintContentProposalProvider.getWords(removeCursorFromString(content),getCursorPos(content));
		assertEquals(current,words[CURRENT].trim());
		assertEquals(last,words[LAST].trim());
	}
	@Before
	public void init(){
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
	public void getProposalsCursorAfterFeature3(){
		String content = "FeatureA and FeatureB|";
		String[] expectedProps = PROPS_NONE;
		testGetProposals(content,expectedProps );
				
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
	public void getProposalsCursorAfterAnd(){
		String content = "FeatureA and| ";
		String[] expectedProps = PROPS_NONE;
		testGetProposals(content,expectedProps );
				
	}
	
//	@Test 
//	public void getProposalsCursorAfterAnd2(){
//		String content = "FeatureA and |";
//		String[] expectedProps = PROPS_FEATURES;
//		testGetProposals(content,expectedProps );
//				
//	}
	
	
	

	
	
	
	@Test 
	public void getProposalsPrefixOfFeature(){
		String content = "Fea|  ";
		String[] expectedProps = {"FeatureA","FeatureB","FeatureC"};
		testGetProposals(content,expectedProps );
				
	}
	
	@Test 
	public void getProposalsCursorAfterNot(){
		String content = "not|";
		String[] expectedProps = PROPS_NONE;
		testGetProposals(content,expectedProps );
				
	}
	@Test 
	public void getProposalsPrefixOfFeatureAfterNot(){
		String content = "not Fea|";
		String[] expectedProps = {"FeatureA","FeatureB","FeatureC"};
		testGetProposals(content,expectedProps );
				
	}
	@Test 
	public void getProposalsPrefixOfAnd(){
		String content = "FeatureA a|";
		String[] expectedProps = {"and"};
		testGetProposals(content,expectedProps );
				
	}

	@Test 
	public void getProposalsPrefixOfOr(){
		String content = "FeatureA o|";
		String[] expectedProps = {"or"};
		testGetProposals(content,expectedProps );
				
	}
	
	@Test 
	public void getProposalsPrefixOfIff(){
		String content = "FeatureA i|";
		String[] expectedProps = {"iff","implies"};
		testGetProposals(content,expectedProps );
				
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
	
	private void testGetProposals(String content,String[] expectedProps) {
		Set<String> expectedPropsSet = new HashSet<String>();
		expectedPropsSet.addAll(Arrays.asList(expectedProps));
		ConstraintContentProposalProvider propProv = new ConstraintContentProposalProvider(features);
		IContentProposal[] proposals = propProv.getProposals(removeCursorFromString(content), getCursorPos(content));
		assertEquals(expectedProps.length,proposals.length);
		for(int i=0;i<expectedProps.length;i++){
		assertEquals(expectedProps[i],proposals[i].getContent());
		}

	}
	private int getCursorPos(String s){
		assertTrue(s.contains("|"));
		return s.indexOf("|");
		
	}
	
	private String removeCursorFromString(String s){
		assertTrue("String must contain cursor symbol",s.contains("|"));
		return s.replace("|","");
	}
	
	@Test
	public void internalTestGetCursorPos(){
		String s = "|";
		assertEquals(0, getCursorPos(s));
	}
	@Test
	public void internalTestGetCursorPos2(){
		String s = "ab|";
		assertEquals(2, getCursorPos(s));
	}
	@Test
	public void internalTestRemoveCursorFromString(){
		String s = "|";
		assertEquals("", removeCursorFromString(s));
	}
	@Test
	public void internalTestRemoveCursorFromString2(){
		String s = "abcd|efg";
		assertEquals("abcdefg", removeCursorFromString(s));
	}
}
