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
package de.ovgu.featureide.fm.core.explanations;

import java.util.Collection;

import org.prop4j.NodeWriter;

/**
 * Transforms {@link Explanation explanations} into user-friendly strings in natural language.
 *
 * @param <E> explanation
 * @author Timo G&uuml;nther
 * @author Sofia Ananieva
 */
public abstract class ExplanationWriter<E extends Explanation<?>> {

	/** The explanation to be transformed. */
	private final E explanation;
	/**
	 * Whether to include the reason count versus explanation count when writing a reason. This acts as an explanation for the reason's confidence.
	 */
	private boolean writingReasonCounts = true;
	/** Whether to write a line break before every reason. */
	private boolean writingLineBreaks = true;
	/** Symbols to use with {@link NodeWriter}. */
	private String[] symbols = NodeWriter.logicalSymbols;

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param explanation explanation to be transformed
	 */
	protected ExplanationWriter(E explanation) {
		this.explanation = explanation;
	}

	/**
	 * Returns the explanation to be transformed.
	 *
	 * @return the explanation to be transformed
	 */
	protected E getExplanation() {
		return explanation;
	}

	/**
	 * Sets the writing reason counts flag.
	 *
	 * @param writingReasonCounts new writing reason counts flag
	 */
	public void setWritingReasonCounts(boolean writingReasonCounts) {
		this.writingReasonCounts = writingReasonCounts;
	}

	/**
	 * Returns the writing reason counts flag. It denotes whether to include the reason count versus explanation count when writing a reason. This acts as an
	 * explanation for the reason's confidence.
	 *
	 * @return the writing reason counts flag
	 */
	public boolean isWritingReasonCounts() {
		return writingReasonCounts;
	}

	/**
	 * <p> Returns the symbols to use with {@link NodeWriter}. </p>
	 *
	 * <p> Defaults to {@link NodeWriter#logicalSymbols logical symbols}. </p>
	 *
	 * @return the symbols to use with {@link NodeWriter}
	 */
	public String[] getSymbols() {
		return symbols;
	}

	/**
	 * Sets the symbols to use with {@link NodeWriter}.
	 *
	 * @param symbols symbols to use with {@link NodeWriter}
	 */
	public void setSymbols(String[] symbols) {
		this.symbols = symbols;
	}

	/**
	 * Returns true iff this is writing line breaks. In that case, a line break is written before every reason.
	 *
	 * @return true iff this is writing line breaks
	 */
	public boolean isWritingLineBreaks() {
		return writingLineBreaks;
	}

	/**
	 * Sets whether to write line breaks.
	 *
	 * @param writingLineBreaks whether to write line breaks
	 */
	public void setWritingLineBreaks(boolean writingLineBreaks) {
		this.writingLineBreaks = writingLineBreaks;
	}

	/**
	 * Returns a string describing the explanation.
	 *
	 * @return a string describing the explanation
	 */
	public String getString() {
		String s = getHeaderString();
		if ((explanation == null) || (explanation.getReasons() == null) || explanation.getReasons().isEmpty()) {
			return s;
		}
		s += getReasonsString();
		return s;
	}

	/**
	 * Returns a string introducing the explanation or one describing its absence.
	 *
	 * @return a string introducing the explanation or one describing its absence
	 */
	public String getHeaderString() {
		if ((explanation == null) || (explanation.getReasons() == null) || explanation.getReasons().isEmpty()) {
			return getMissingExplanationString();
		}
		return getIntroductionString();
	}

	/**
	 * Returns a string saying that no explanation could be found.
	 *
	 * @return a string saying that no explanation could be found
	 */
	protected String getMissingExplanationString() {
		return "No explanation could be found.";
	}

	/**
	 * Returns a user-friendly introduction to the explanation.
	 *
	 * @return a user-friendly introduction to the explanation
	 */
	protected String getIntroductionString() {
		return String.format("%s because:", getCircumstanceString());
	}

	/**
	 * Returns a user-friendly string of the circumstance to explain.
	 *
	 * @return a user-friendly string of the circumstance to explain
	 */
	public String getCircumstanceString() {
		return String.format("The %s is %s", getSubjectString(), getAttributeString());
	}

	/**
	 * Returns the subject of the explanation. That is the element to be explained.
	 *
	 * @return the subject of the explanation
	 */
	protected abstract String getSubjectString();

	/**
	 * Returns the attribute of the explanation. That is what makes the subject worth explaining.
	 *
	 * @return the attribute of the explanation
	 */
	protected abstract String getAttributeString();

	/**
	 * Returns all reasons joined together.
	 *
	 * @return joined reasons
	 */
	public String getReasonsString() {
		return getReasonsString(getExplanation().getReasons());
	}

	/**
	 * Returns the given reasons joined together.
	 *
	 * @param reasons reasons to join
	 * @return joined reasons
	 */
	public String getReasonsString(Collection<? extends Reason<?>> reasons) {
		String s = "";
		for (final Reason<?> reason : reasons) {
			if (isWritingLineBreaks()) {
				s += System.lineSeparator();
				if (getSymbols() == NodeWriter.logicalSymbols) {
					s += "\u2022"; // Unicode bullet point
				} else {
					s += "-"; // simple bullet point
				}
			}
			s += " " + getReasonString(reason);
		}
		return s;
	}

	/**
	 * Returns a user-friendly representation of the given reason.
	 *
	 * @param reason reason to transform
	 * @return a user-friendly representation of the given reason
	 * @throws IllegalStateException if the reason's source attribute is unknown
	 */
	public String getReasonString(Reason<?> reason) throws IllegalArgumentException {
		String s = getConcreteReasonString(reason);
		final int reasonCount = getExplanation().getReasonCounts().get(reason);
		final int explanationCount = getExplanation().getExplanationCount();
		if (isWritingReasonCounts() && (reasonCount > 1) && (explanationCount > 1)) {
			s = String.format("%s (%d/%d)", s, reasonCount, explanationCount);
		}
		return s;
	}

	/**
	 * Returns a user-friendly representation of the given concrete reason.
	 *
	 * @param reason concrete reason to transform
	 * @return a user-friendly representation of the given concrete reason
	 */
	protected abstract String getConcreteReasonString(Reason<?> reason);
}
