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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import org.eclipse.swt.graphics.Point;
import org.junit.Test;

import de.ovgu.featureide.fm.ui.editors.SimpleSyntaxHighlighterConstraintContentAdapter.InsertionResult;

/**
 * Tests related action of the content proposal in ConstraintDialog, e.g. insertion of a word
 *
 * @author Marcus Pinnecke
 */
public final class ContentProposalActionTest {

	private String applyProposal(String text, Point selection, String proposal) {
		return insertPipe(SimpleSyntaxHighlighterConstraintContentAdapter.performInsertion(removePipe(text), selection, proposal, false));
	} // TODO

	private Point getSelection(String inputText) {
		final String text = inputText;
		final int selStart = text.indexOf("|");
		if (selStart < 0) {
			fail("Input text doest not contain a selection marker \"|\": " + text);
		}
		final String selectionEnd = text.substring(selStart + 1, text.length());
		final int selEnd = selectionEnd.indexOf("|");
		return new Point(selStart, selEnd < 0 ? selStart : selStart + selEnd);
	}

	private String insertPipe(InsertionResult result) {
		final String before = result.text.substring(0, result.selection.x);
		final String after = result.text.substring(result.selection.x, result.text.length());
		return before + "|" + after;
	}

	private String removePipe(String text) {
		return text.replace("|", "");
	}

	@Test
	public void testCase1() {
		testProposalInsertion("|", "FeatureA", "FeatureA|");
	}

	@Test
	public void testCase10() {
		testProposalInsertion("A and | B", "not", "A and not| B");
	}

	@Test
	public void testCase12() {
		testProposalInsertion("A and |B|", "C", "A and C|");
	}

	@Test
	public void testCase13() {
		testProposalInsertion("feature|", "FeatureA", "FeatureA|");
	}

	@Test
	public void testCase14() {
		testProposalInsertion("Feature|A|", "FeatureB", "FeatureB|");
	}

	@Test
	public void testCase15() {
		testProposalInsertion("fea|ture|", "FeatureB", "FeatureB|");
	}

	@Test
	public void testCase16() {
		testProposalInsertion("fea|tureA|", "FeatureB", "FeatureB|");
	}

	@Test
	public void testCase17() {
		testProposalInsertion("A|", "A0", "A0|");
	}

	@Test
	public void testCase18() {
		testProposalInsertion("A and |B", "not", "A and not| B");
	}

	@Test
	public void testCase19() {
		testProposalInsertion("not Elevator and | TwoThirdsFull", "not", "not Elevator and not| TwoThirdsFull");
	}

	@Test
	public void testCase2() {
		testProposalInsertion("|  ", "FeatureA", "FeatureA|  ");
	}

	@Test
	public void testCase20() {
		testProposalInsertion("not Elevator and n| TwoThirdsFull", "not", "not Elevator and not| TwoThirdsFull");
	}

	@Test
	public void testCase21() {
		testProposalInsertion("not A and n| B", "not", "not A and not| B");
	}

	@Test
	public void testCase22() {
		testProposalInsertion("not Elevator and no| TwoThirdsFull", "not", "not Elevator and not| TwoThirdsFull");
	}

	@Test
	public void testCase23() {
		testProposalInsertion("out|", "Output Signal", "\"Output Signal\"|");
	}

	@Test
	public void testCase3() {
		testProposalInsertion("  |  ", "FeatureA", "  FeatureA|  ");
	}

	@Test
	public void testCase4() {
		testProposalInsertion("A |", "and", "A and|");
	}

	@Test
	public void testCase5() {
		testProposalInsertion("A |  ", "and", "A and|  ");
	}

	@Test
	public void testCase6() {
		testProposalInsertion("  A |  ", "and", "  A and|  ");
	}

	@Test
	public void testCase7() {
		testProposalInsertion("Feature |", "and", "Feature and|");
	}

	@Test
	public void testCase8() {
		testProposalInsertion("Feature |  ", "and", "Feature and|  ");
	}

	@Test
	public void testCase9() {
		testProposalInsertion("  Feature |  ", "and", "  Feature and|  ");
	}

	private void testProposalInsertion(String before, String proposal, String expectedAfter) {
		assertEquals(expectedAfter, applyProposal(before, getSelection(before), proposal));
	}

}
