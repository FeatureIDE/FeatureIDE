/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.eclipse.jface.fieldassist.ContentProposal;
import org.eclipse.jface.fieldassist.IContentProposal;
import org.eclipse.jface.fieldassist.IContentProposalProvider;

/**
 * TODO description
 * 
 * @author David Broneske
 * @author Fabian Benduhn
 */
public class ConstraintContentProposalProvider implements
		IContentProposalProvider {
	
	private Set<String> features;


	public ConstraintContentProposalProvider(Set<String> featureNames) {
		super();
		features = featureNames;
	}

	/**
	 * Return an array of Objects s representing the valid content proposals for
	 * a field.
	 * 
	 * @param contents
	 *            the current contents of the field  
	 * @param position
	 *            the current cursor position within the field 
	 * @return the array of Objects that represent valid proposals for the field
	 *         given its current content.
	 */
	public IContentProposal[] getProposals(String contents, int position) {
		String currentWord = new String();
		String wordBefore = new String();
		int posMarker = position - 1;
		if (position != 0) {
			while (posMarker > 0 && contents.charAt(posMarker) != ' ') {
				posMarker--;
			}
			currentWord = contents.substring(posMarker, position);

			while (posMarker > 0 && contents.charAt(posMarker) == ' ') {
				posMarker--;
			}
			int startBefore = posMarker;
			while (startBefore > 0 && contents.charAt(startBefore) != ' ') {
				startBefore--;
			}
			wordBefore = contents.substring(startBefore, posMarker + 1);

		}

		wordBefore = wordBefore.trim();
		currentWord = currentWord.trim();
		if (wordBefore.startsWith("(")) {
			wordBefore = wordBefore.substring(1);

		}
		if (currentWord.startsWith("(")) {
			currentWord = currentWord.substring(1);
			wordBefore = "(";
		}
		if (wordBefore.endsWith(")")) {
			wordBefore = ")";

		}
		if (currentWord.endsWith(")")) {
			wordBefore = ")";
			currentWord = "";

		}

		List<ContentProposal> proposalList = new ArrayList<ContentProposal>();
		if (currentWord.equals("(") || currentWord.equals(")")
				|| currentWord.equals(" ") || currentWord.equals("")) {
			proposalList = getProposalList(wordBefore);
		} else {
			for (ContentProposal proposal : getProposalList(wordBefore)) {

				if (proposal.getContent().length() >= currentWord.length()
						&& proposal.getContent()
								.substring(0, currentWord.length())
								.equalsIgnoreCase(currentWord)) {

					proposalList.add(proposal);
				}
			}
		}

		return (IContentProposal[]) proposalList
				.toArray(new IContentProposal[proposalList.size()]);

	}

	private List<ContentProposal> getProposalList(String wordBefore) {

		ArrayList<ContentProposal> proposals = new ArrayList<ContentProposal>();
		ArrayList<String> featureList = new ArrayList<String>(features);
		Collections.sort(featureList, String.CASE_INSENSITIVE_ORDER);
		if (wordBefore.equals(")") || features.contains(wordBefore.trim())) {
			proposals.add(new ContentProposal("and"));
			proposals.add(new ContentProposal("iff"));
			proposals.add(new ContentProposal("implies"));
			proposals.add(new ContentProposal("or"));

		} else {
			proposals.add(new ContentProposal("not"));

			for (String s : featureList) {
				proposals.add(new ContentProposal(s));
			}

		}

		return proposals;
	}



}