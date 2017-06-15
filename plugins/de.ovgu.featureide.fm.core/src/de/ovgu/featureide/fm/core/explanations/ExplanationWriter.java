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
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
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
		if (explanation.getDefectElement() instanceof IFeature) {
			final IFeature feature = (IFeature) explanation.getDefectElement();
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
			default:
				throw new IllegalStateException("Unkown defect type");
		}
	}
	
	/**
	 * Returns a user-friendly representation of the given reason.
	 * @param reason reason to transform
	 * @return a user-friendly representation of the given reason
	 * @throws IllegalArgumentException if the given reason is not part of the explanation
	 * @throws IllegalStateException if there is no parent despite up relationship; if the reason's source attribute is unknown or denotes parent relationship
	 */
	public String getReasonString(Reason reason) throws IllegalArgumentException {
		if (explanation == null || explanation.getReasons() == null || !explanation.getReasons().contains(reason)) {
			throw new IllegalArgumentException("Reason is not part of the explanation");
		}
		String s = null;
		final IFeature feature;
		final IFeature parent;
		switch (reason.getLiteral().getOrigin()) {
			case CHILD_UP:
				feature = (IFeature) reason.getSourceElement();
				parent = FeatureUtils.getParent(feature);
				if (parent == null) {
					throw new IllegalStateException("Missing parent despite up child source attribute");
				}
				s = String.format("%s is child of %s.", feature.getName(), parent.getName());
				break;
			case CHILD_DOWN:
				feature = (IFeature) reason.getSourceElement();
				parent = FeatureUtils.getParent(feature);
				if (parent == null) {
					throw new IllegalStateException("Missing parent despite down child source attribute");
				}
				s = String.format("%s is %s of %s.", feature.getName(), getChildString(feature, parent), parent.getName());
				break;
			case CHILD_HORIZONTAL:
				String alternatives = "";
				final List<Literal> literals = reason.getClause().getLiterals();
				literals.remove(reason.getLiteral());
				boolean first = true;
				for (final Iterator<Literal> it = literals.iterator(); it.hasNext();) {
					final Literal l = it.next();
					if (first) {
						first = false;
					} else {
						alternatives += it.hasNext() ? ", " : " and ";
					}
					alternatives += l.var;
				}
				s = String.format("%s is alternative to %s.", reason.getLiteral().var, alternatives);
				break;
			case CONSTRAINT:
				final IConstraint constraint = (IConstraint) reason.getSourceElement();
				s = String.format("%s is a constraint.", constraint.getNode().toString(NodeWriter.logicalSymbols));
				break;
			case ROOT:
				s = String.format("%s is the root.", reason.getLiteral().var.toString());
				break;
			case PARENT:
				throw new IllegalStateException("Reason denotes parent relationship");
			default:
				throw new IllegalStateException("Reason has unexpected source attribute");
		}
		final int reasonCount = explanation.getReasonCount();
		final int explanationCount = explanation.getExplanationCount();
		if (isWritingReasonCounts() && reasonCount > 1 && explanationCount > 1) {
			s = String.format("%s (%d/%d)", s, reasonCount, explanationCount);
		}
		return s;
	}
	
	/**
	 * Returns a string describing what kind of child the given child is.
	 * @param child child of the parent
	 * @param parent parent of the child
	 * @return a string describing what kind of child the given child is
	 */
	protected String getChildString(IFeature child, IFeature parent) {
		String s = "";
		if (parent.getStructure().isAlternative()) {
			s += "alternative ";
		} else if (parent.getStructure().isOr()) {
			s += "or-";
		} else if (FeatureUtils.isMandatory(child)) {
			s += "mandatory ";
		}
		s += "child";
		return s;
	}
}
