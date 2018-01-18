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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.FOCUS_ON_EXPLANATION;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanation;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation for collapsing all features but those affected by the active explanation.
 *
 * @author Timo G&uuml;nther
 */
public class FocusOnExplanationOperation extends AbstractCollapseOperation {

	/** The currently active explanation. */
	private final FeatureModelExplanation<?> explanation;

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param fm the feature model context
	 * @param explanation the currently active explanation
	 */
	public FocusOnExplanationOperation(IGraphicalFeatureModel fm, FeatureModelExplanation<?> explanation) {
		super(fm, FOCUS_ON_EXPLANATION);
		this.explanation = explanation;
	}

	@Override
	protected Map<IGraphicalFeature, Boolean> createTargets() {
		final Collection<? extends IGraphicalFeature> expandedFeatures =
			FeatureUIHelper.getGraphicalFeatures(FeatureUtils.getParents(explanation.getAffectedFeatures()), graphicalFeatureModel);
		final Map<IGraphicalFeature, Boolean> targets = new HashMap<>(featureModel.getNumberOfFeatures());
		for (final IGraphicalFeature feature : graphicalFeatureModel.getAllFeatures()) {
			final boolean collapse = !expandedFeatures.contains(feature);
			if (feature.isCollapsed() == collapse) { // already in the target state, therefore no change necessary
				continue;
			}
			targets.put(feature, collapse);
		}
		return targets;
	}

	@Override
	protected FeatureIDEEvent operation() {
		super.operation();
		return new FeatureIDEEvent(explanation.getSubject(), EventType.COLLAPSED_ALL_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		super.inverseOperation();
		return new FeatureIDEEvent(explanation.getSubject(), EventType.COLLAPSED_ALL_CHANGED);
	}
}
