/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Collections;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;

/**
 * {@link MultipleAnomaliesExplanation} composes multiple {@link FeatureModelExplanation}s of {@link IFeatureModelElement}s into a single explanation for a
 * given {@link IFeatureModel} they belong to.
 *
 * @author Benedikt Jutz
 */
public class MultipleAnomaliesExplanation extends FeatureModelExplanation<IFeatureModel> {

	/**
	 * <code>singleExplanations</code> stores the single explanations.
	 */
	private final List<FeatureModelExplanation<? extends IFeatureModelElement>> singleExplanations;

	/**
	 * Returns the single explanations in an unmodifiable {@link List}.
	 *
	 * @return <code>singleExplanations</code> - {@link List}
	 */
	public List<FeatureModelExplanation<? extends IFeatureModelElement>> getSingleExplanations() {
		return Collections.unmodifiableList(singleExplanations);
	}

	/**
	 * Constructs a new {@link MultipleAnomaliesExplanation} and collects the single reasons.
	 *
	 * @param subject - {@link IFeatureModel}
	 */
	public MultipleAnomaliesExplanation(IFeatureModel subject, List<FeatureModelExplanation<? extends IFeatureModelElement>> singleExplanations) {
		super(subject);
		this.singleExplanations = singleExplanations;
		this.singleExplanations.forEach(exp -> exp.getReasonCounts().keySet().forEach(reason -> addReason(reason)));
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.explanations.Explanation#getWriter()
	 */
	@Override
	public MultipleAnomaliesExplanationWriter getWriter() {
		return new MultipleAnomaliesExplanationWriter(this);
	}

	/**
	 * The implications of this composed explanation simply is the conjunction of all its single explanations.
	 *
	 * @return new {@link And} with all implications of <code>singleExplanations</code>
	 * @see de.ovgu.featureide.fm.core.explanations.Explanation#getImplication()
	 */
	@Override
	public Node getImplication() {
		return new And(singleExplanations.stream().map(explanation -> explanation.getImplication()).toArray());
	}

}
