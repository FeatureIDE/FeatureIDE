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

import java.util.Iterator;
import java.util.Set;

import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel.FeatureModelElementTrace;
import de.ovgu.featureide.fm.core.explanations.Explanation.Reason;

/**
 * Transforms instances of {@link Explanation} into user-friendly strings in natural language.
 * 
 * @author Timo G&uuml;nther
 * @author Sofia Ananieva
 */
public class ExplanationWriter {
	/** The explanation to be transformed. */
	protected final Explanation explanation;
	/**
	 * Whether to include the reason count versus explanation count when writing a reason.
	 * This acts as an explanation for the reason's confidence.
	 */
	private boolean writingReasonCounts = true;
	/** Symbols to use with {@link NodeWriter}. */
	private String[] symbols = NodeWriter.logicalSymbols;
	
	/**
	 * Constructs a new instance of this class.
	 * @param explanation explanation to be transformed
	 */
	public ExplanationWriter(Explanation explanation) {
		this.explanation = explanation;
	}
	
	/**
	 * Sets the writing reason counts flag.
	 * @param writingReasonCounts new writing reason counts flag
	 */
	public void setWritingReasonCounts(boolean writingReasonCounts) {
		this.writingReasonCounts = writingReasonCounts;
	}
	
	/**
	 * Returns the writing reason counts flag.
	 * It denotes whether to include the reason count versus explanation count when writing a reason.
	 * This acts as an explanation for the reason's confidence.
	 * @return the writing reason counts flag
	 */
	public boolean isWritingReasonCounts() {
		return writingReasonCounts;
	}
	
	/**
	 * <p>
	 * Returns the symbols to use with {@link NodeWriter}.
	 * </p>
	 * 
	 * <p>
	 * Defaults to {@link NodeWriter#logicalSymbols logical symbols}.
	 * </p>
	 * @return the symbols to use with {@link NodeWriter}
	 */
	public String[] getSymbols() {
		return symbols;
	}
	
	/**
	 * Sets the symbols to use with {@link NodeWriter}.
	 * @param symbols symbols to use with {@link NodeWriter}
	 */
	public void setSymbols(String[] symbols) {
		this.symbols = symbols;
	}
	
	/**
	 * Returns a string describing the explanation.
	 * @return a string describing the explanation
	 */
	public String getString() {
		String s = getHeaderString();
		if (explanation == null || explanation.getReasons() == null || explanation.getReasons().isEmpty()) {
			return s;
		}
		for (final Reason reason : explanation.getReasons()) {
			s += String.format("%n\u2022 %s", getReasonString(reason));
		}
		return s;
	}
	
	/**
	 * Returns a string introducing the explanation or one describing its absence.
	 * @return a string introducing the explanation or one describing its absence
	 */
	public String getHeaderString() {
		if (explanation == null || explanation.getReasons() == null || explanation.getReasons().isEmpty()) {
			return getMissingExplanationString();
		}
		return getIntroductionString();
	}
	
	/**
	 * Returns a string saying that no explanation could be found.
	 * @return a string saying that no explanation could be found
	 */
	public String getMissingExplanationString() {
		return "No explanation could be found.";
	}
	
	/**
	 * Returns a user-friendly introduction to the explanation.
	 * @return a user-friendly introduction to the explanation
	 */
	public String getIntroductionString() {
		if (explanation.getMode() == Explanation.Mode.DEAD_FEATURE && FeatureUtils.isRoot((IFeature) explanation.getDefectElement())) {
			return "The feature model is void because:";
		}
		return String.format("The %s is %s because:",
				getDefectElementString(),
				getDefectTypeString());
	}
	
	/**
	 * Returns a string describing the defect element.
	 * @return a string describing the defect element
	 * @throws IllegalStateException if the type of the defect feature model element is unknown
	 */
	protected String getDefectElementString() throws IllegalStateException {
		String s = "";
		final IFeatureModelElement element = explanation.getDefectElement() != null
				? explanation.getDefectElement()
				: explanation.getAutomaticSelection().getFeature();
		if (element instanceof IFeature) {
			final IFeature feature = (IFeature) element;
			if (feature.getStructure().isAbstract()) {
				s += "abstract ";
			} else if (feature.getStructure().isConcrete()) {
				s += "concrete ";
			}
			s += "feature ";
			s += feature.getName();
		} else if (explanation.getDefectElement() instanceof IConstraint) {
			final IConstraint constraint = (IConstraint) explanation.getDefectElement();
			s += "constraint ";
			s += constraint.getNode().toString(NodeWriter.logicalSymbols);
		} else {
			throw new IllegalStateException("Unknown feature model element type");
		}
		return s;
	}
	
	/**
	 * Returns a string describing the defect type.
	 * @return a string describing the defect type
	 * @throws IllegalStateException if the defect type is unknown
	 */
	protected String getDefectTypeString() throws IllegalStateException {
		switch (explanation.getMode()) {
			case DEAD_FEATURE:
				return "dead";
			case FALSE_OPTIONAL_FEATURE:
				return "false-optional";
			case REDUNDANT_CONSTRAINT:
				return explanation.isImplicit() ? "transitive" : "redundant";
			case AUTOMATIC_SELECTION:
				switch (explanation.getAutomaticSelection().getAutomatic()) {
					case SELECTED:
						return "automatically selected";
					case UNSELECTED:
						return "automatically unselected";
					case UNDEFINED:
						throw new IllegalStateException("Feature is not automatically selected or unselected");
					default:
						throw new IllegalStateException("Unknown feature selection state");
				}
			default:
				throw new IllegalStateException("Unkown defect type");
		}
	}
	
	/**
	 * Returns a user-friendly representation of the given reason.
	 * @param reason reason to transform
	 * @return a user-friendly representation of the given reason
	 * @throws IllegalStateException if the reason's source attribute is unknown
	 */
	public String getReasonString(Reason reason) throws IllegalArgumentException {
		String s = null;
		
		if (reason.getTrace() != null) {
			final FeatureModelElementTrace trace = reason.getTrace();
			final Set<IFeatureModelElement> sourceElements = trace.getElements();
			final String joinedSourceElements = join(sourceElements);
			final IFeature parent;
			switch (trace.getOrigin()) {
				case CHILD_UP:
					parent = (IFeature) trace.getElement();
					s = String.format("%s is a child of %s (i.e., %s).", joinedSourceElements, parent.getName(), trace.toString(getSymbols()));
					break;
				case CHILD_DOWN:
					parent = (IFeature) trace.getElement();
					if (parent.getStructure().isAlternative()) {
						s = String.format("%s are alternative children of %s (i.e., %s).", joinedSourceElements, parent.getName(), trace.toString(getSymbols()));
					} else if (parent.getStructure().isOr()) {
						s = String.format("%s are or-children of %s (i.e., %s).", joinedSourceElements, parent.getName(), trace.toString(getSymbols()));
					} else {
						s = String.format("%s is a mandatory child of %s (i.e., %s).", joinedSourceElements, parent.getName(), trace.toString(getSymbols()));
					}
					break;
				case CHILD_HORIZONTAL:
					s = String.format("%s are alternatives (i.e., %s).", joinedSourceElements, trace.toString(getSymbols()));
					break;
				case CONSTRAINT:
					s = String.format("%s is a constraint.", joinedSourceElements);
					break;
				case ROOT:
					s = String.format("%s is the root.", joinedSourceElements);
					break;
				default:
					throw new IllegalStateException("Reason has unexpected source attribute");
			}
		} else if (reason.getFeatureSelection() != null) {
			final String selectionString;
			switch (reason.getFeatureSelection().getSelection()) {
				case SELECTED:
					selectionString = "selected";
					break;
				case UNSELECTED:
					selectionString = "unselected";
					break;
				case UNDEFINED:
					selectionString = "neither selected nor unselected";
				default:
					throw new IllegalStateException("Unknown feature selection state");
			}
			s = String.format("%s is %s.", reason.getFeatureSelection().getFeature().getName(), selectionString);
		} else {
			throw new IllegalStateException("Unknown reason type");
		}
		
		final Explanation explanation = reason.getExplanation();
		final int reasonCount = explanation.getReasonCounts().get(reason);
		final int explanationCount = explanation.getExplanationCount();
		if (isWritingReasonCounts() && reasonCount > 1 && explanationCount > 1) {
			s = String.format("%s (%d/%d)", s, reasonCount, explanationCount);
		}
		
		return s;
	}
	
	/**
	 * Joins the given elements.
	 * @param elements elements to join
	 * @return joined elements
	 */
	private String join(Set<IFeatureModelElement> elements) {
		String s = "";
		int i = 0;
		for (final Iterator<IFeatureModelElement> it = elements.iterator(); it.hasNext();) {
			final IFeatureModelElement element = it.next();
			if (i++ > 0) {
				s += it.hasNext() ? ", " : i > 2 ? ", and " : " and ";
			}
			if (element instanceof IConstraint) {
				final NodeWriter w = new NodeWriter(((IConstraint) element).getNode());
				w.setSymbols(getSymbols());
				s += w.nodeToString();
			} else {
				s += element.getName();
			}
		}
		return s;
	}
}
