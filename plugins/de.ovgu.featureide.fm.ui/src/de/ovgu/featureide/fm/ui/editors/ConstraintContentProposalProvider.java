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

import static de.ovgu.featureide.fm.core.localization.StringTable.AND;
import static de.ovgu.featureide.fm.core.localization.StringTable.IFF;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPLIES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NOT;
import static de.ovgu.featureide.fm.core.localization.StringTable.OR;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.eclipse.jface.fieldassist.IContentProposal;
import org.eclipse.jface.fieldassist.IContentProposalProvider;

import de.ovgu.featureide.fm.core.Features;
import de.ovgu.featureide.fm.core.Operator;

/**
 * provides proposals for content assist while typing constraints
 *
 * @author David Broneske
 * @author Fabian Benduhn
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Rahel Arens
 * @author Johannes Herschel
 */
public class ConstraintContentProposalProvider implements IContentProposalProvider {

	private final Collection<String> features;

	public ConstraintContentProposalProvider(Collection<String> featureNames) {
		features = featureNames;
	}

	/**
	 * Return an array of Objects s representing the valid content proposals for a field.
	 *
	 * @param contents the current contents of the field
	 * @param position the current cursor position within the field
	 * @return the array of Objects that represent valid proposals for the field given its current content.
	 */
	@Override
	public IContentProposal[] getProposals(String contents, int position) {

		final ProposalContext context = getProposalContext(contents, position);

		final List<ContentProposal> proposalList = getProposalList(context);

		return proposalList.toArray(new IContentProposal[proposalList.size()]);

	}

	/**
	 * @param context context of proposal
	 * @return List of proposals, only contains proposals consistent with previous and current word.
	 */
	private List<ContentProposal> getProposalList(ProposalContext context) {
		List<ContentProposal> proposalList = new ArrayList<ContentProposal>();

		if ("".equals(context.currentWord)) {
			proposalList = getProposalList(context, features);
		} else {
			for (final ContentProposal proposal : getProposalList(context, features)) {
				if ((proposal.getContent().length() >= context.currentWord.length())
					&& proposal.getContent().substring(0, context.currentWord.length()).equalsIgnoreCase(context.currentWord)) {
					proposalList.add(proposal);
				}
			}
		}
		return proposalList;
	}

	/**
	 * @param contents the content, i.e. the string which contains the text
	 * @param position current position of the cursor, first position is 0
	 * @return context of proposal
	 */
	static ProposalContext getProposalContext(String contents, int position) {

		// cut the rest of the string away
		contents = contents.substring(0, position);

		// cut away ( and ) because they do not change the last appearing word of the constraint but this way we can shorten the following code
		contents = contents.replaceAll("\\(|\\)", " ");

		if (position == 0) {
			return new ProposalContext(false, "", false);
		} else {
			int quotMarkCounter = 0;

			// count number of quotation marks
			for (int i = 0; i < contents.length(); i++) {
				if (contents.charAt(i) == '\"') {
					quotMarkCounter++;
				}
			}

			// detect whether it is a feature with multiple words
			final boolean quotationMark = (quotMarkCounter % 2) != 0;
			final char separator = quotationMark ? '\"' : ' ';

			// detect the position where the current feature starts
			int posMarker = contents.lastIndexOf(separator) + 1;

			// the current typed word
			final String currentWord = contents.substring(posMarker);

			if (quotationMark) {
				posMarker--;
			}
			contents = contents.substring(0, posMarker);
			contents = contents.trim();

			// text before current word
			if (contents.endsWith("\"")) {
				return new ProposalContext(true, currentWord, quotationMark);
			} else {
				final String lastWord = contents.substring(contents.lastIndexOf(' ') + 1);
				return new ProposalContext(!Operator.isOperatorName(lastWord) && !lastWord.isEmpty(), currentWord, quotationMark);
			}
		}
	}

	/**
	 * @param context context of proposal
	 * @param features set of all features
	 * @return List of proposals, either operators or feature names. Contains only proposals consistent with the previous text, but may contain proposals
	 *         inconsistent with current word.
	 */
	private static List<ContentProposal> getProposalList(ProposalContext context, Collection<String> features) {

		final ArrayList<ContentProposal> proposals = new ArrayList<ContentProposal>();
		final ArrayList<String> featureList = new ArrayList<String>(features);
		Collections.sort(featureList, String.CASE_INSENSITIVE_ORDER);

		final Collection<String> operatorNamesInFeatures = Features.extractOperatorNamesFromFeatuers(features);

		if (context.featureBefore) {
			if (!context.quotationMark) {
				// Add binary operators only iff their appearance makes sense in content proposal
				// Example:
				// Show "and" for "A |"
				// Hide "and" for "A and |"
				proposals.add(new ContentProposal(AND.toLowerCase()));
				proposals.add(new ContentProposal(IFF.toLowerCase()));
				proposals.add(new ContentProposal(IMPLIES.toLowerCase()));
				proposals.add(new ContentProposal(OR.toLowerCase()));
			}
		} else {
			if (context.quotationMark) {
				// Add features with spaces
				for (final String s : featureList) {
					if (s.contains(" ") || operatorNamesInFeatures.contains(s)) {
						proposals.add(new ContentProposal(s + (operatorNamesInFeatures.contains(s) ? " " + Features.FEATURE_SUFFIX : "")));
					}
				}
			} else {
				// Add NOT only iff its appearance makes sense in content proposal
				// Example:
				// Show NOT for "A implies |"
				// Hide NOT for "A |"
				proposals.add(new ContentProposal(NOT.toLowerCase()));

				// Add features only iff a feature name is valid in context
				// Example:
				// Show feature for "A implies |"
				// Hide features for "A |"
				for (final String s : featureList) {
					proposals.add(new ContentProposal(s + (operatorNamesInFeatures.contains(s.trim()) ? " " + Features.FEATURE_SUFFIX : "")));
				}
			}
		}

		return proposals;
	}

	/**
	 *
	 * Summarizes necessary information about the current context of proposals, i.e. the currently typed word and the word before.
	 *
	 * @author Rahel Arens
	 * @author Johannes Herschel
	 */
	static class ProposalContext {

		/**
		 * True iff the word before the current word is a feature name. False if the previous word is empty.
		 */
		final boolean featureBefore;
		/**
		 * Currently typed word, empty if a new word is started.
		 */
		final String currentWord;
		/**
		 * True iff the currently typed word is started with a quotation mark.
		 */
		final boolean quotationMark;

		ProposalContext(boolean featureBefore, String currentWord, boolean quotationMark) {
			this.featureBefore = featureBefore;
			this.currentWord = currentWord;
			this.quotationMark = quotationMark;
		}
	}
}
