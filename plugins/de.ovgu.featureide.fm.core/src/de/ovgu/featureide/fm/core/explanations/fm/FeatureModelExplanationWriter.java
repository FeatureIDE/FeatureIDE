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
package de.ovgu.featureide.fm.core.explanations.fm;

import java.util.Iterator;
import java.util.Set;

import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel.FeatureModelElementTrace;
import de.ovgu.featureide.fm.core.explanations.ExplanationWriter;
import de.ovgu.featureide.fm.core.explanations.Reason;

/**
 * {@link ExplanationWriter} for instances of {@link FeatureModelExplanation}.
 *
 * @param <E> explanation
 * @author Timo G&uuml;nther
 */
public abstract class FeatureModelExplanationWriter<E extends FeatureModelExplanation<?>> extends ExplanationWriter<E> {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param explanation explanation to be transformed; not null
	 */
	public FeatureModelExplanationWriter(E explanation) {
		super(explanation);
	}

	/**
	 * Returns the given feature as a string.
	 *
	 * @param feature feature to transform; not null
	 * @return the given feature as a string
	 */
	protected String getSubjectString(IFeature feature) {
		if (feature.getStructure().isAbstract()) {
			return String.format("abstract feature %s", feature.getName());
		} else {
			return String.format("concrete feature %s", feature.getName());
		}
	}

	/**
	 * Returns the given constraint as a string.
	 *
	 * @param constraint constraint to transform; not null
	 * @return the given constraint as a string
	 */
	protected String getSubjectString(IConstraint constraint) {
		return String.format("constraint %s", constraint.getNode().toString(getSymbols()));
	}

	@Override
	protected String getConcreteReasonString(Reason<?> reason) throws IllegalArgumentException {
		if (!(reason instanceof FeatureModelReason)) {
			return null;
		}
		final FeatureModelElementTrace trace = ((FeatureModelReason) reason).getSubject();
		final Set<IFeatureModelElement> sourceElements = trace.getElements();
		final String joinedSourceElements = joinElements(sourceElements);
		final IFeature parent;
		switch (trace.getOrigin()) {
		case CHILD_UP:
			parent = (IFeature) trace.getElement();
			return String.format("%s is a child of %s (i.e., %s).", joinedSourceElements, parent.getName(), trace.toString(getSymbols()));
		case CHILD_DOWN:
			parent = (IFeature) trace.getElement();
			if (parent.getStructure().isAlternative()) {
				return String.format("%s are alternative children of %s (i.e., %s).", joinedSourceElements, parent.getName(), trace.toString(getSymbols()));
			} else if (parent.getStructure().isOr()) {
				return String.format("%s are or-children of %s (i.e., %s).", joinedSourceElements, parent.getName(), trace.toString(getSymbols()));
			} else {
				return String.format("%s is a mandatory child of %s (i.e., %s).", joinedSourceElements, parent.getName(), trace.toString(getSymbols()));
			}
		case CHILD_HORIZONTAL:
			return String.format("%s are alternatives (i.e., %s).", joinedSourceElements, trace.toString(getSymbols()));
		case CONSTRAINT:
			return String.format("%s is a constraint.", joinedSourceElements);
		case ROOT:
			return String.format("%s is the root.", joinedSourceElements);
		default:
			throw new IllegalStateException("Reason has unexpected source attribute");
		}
	}

	/**
	 * Joins the given elements.
	 *
	 * @param elements elements to join
	 * @return joined elements
	 */
	private String joinElements(Set<IFeatureModelElement> elements) {
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
