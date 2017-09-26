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

import static de.ovgu.featureide.fm.core.localization.StringTable.COLLAPSE_ALL_BUT_EXPLANATION;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanation;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation for collapsing all features but those affected by the active explanation.
 *
 * @author Timo G&uuml;nther
 */
public class CollapseAllButExplanationOperation extends AbstractFeatureModelOperation {

	/** The graphical feature model context. */
	private final IGraphicalFeatureModel fm;
	/** The currently active explanation. */
	private final FeatureModelExplanation explanation;

	/** The features that will be collapsed during the operation. */
	private Set<IGraphicalFeature> collapsedFeatures;

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param fm the feature model context
	 * @param explanation the currently active explanation
	 */
	public CollapseAllButExplanationOperation(IGraphicalFeatureModel fm, FeatureModelExplanation explanation) {
		super(fm.getFeatureModel(), COLLAPSE_ALL_BUT_EXPLANATION);
		this.fm = fm;
		this.explanation = explanation;
	}

	/**
	 * Returns the graphical feature model context.
	 *
	 * @return the graphical feature model context
	 */
	public IGraphicalFeatureModel getGraphicalFeatureModel() {
		return fm;
	}

	/**
	 * Returns the currently active explanation.
	 *
	 * @return the currently active explanation
	 */
	public FeatureModelExplanation getExplanation() {
		return explanation;
	}

	/**
	 * Returns the features that will be collapsed during the operation.
	 *
	 * @return the features that will be collapsed during the operation
	 */
	public Set<IGraphicalFeature> getCollapsedFeatures() {
		return collapsedFeatures;
	}

	/**
	 * Sets the features that will be collapsed during the operation.
	 *
	 * @param collapsedFeatures the features that will be collapsed during the operation
	 */
	protected void setCollapsedFeatures(Set<IGraphicalFeature> collapsedFeatures) {
		this.collapsedFeatures = collapsedFeatures;
	}

	/**
	 * Creates the set of features that will be collapsed during the operation.
	 *
	 * @return the set of features that will be collapsed during the operation
	 */
	protected Set<IGraphicalFeature> createCollapsedFeatures() {
		final Set<IFeature> explanationFeatures = getExplanation().getAffectedFeatures();
		final Set<IFeature> nonExplanationFeatures = new HashSet<>(getGraphicalFeatureModel().getFeatureModel().getFeatureTable().values());
		nonExplanationFeatures.removeAll(getAllParentFeatures(explanationFeatures));
		final Set<IGraphicalFeature> collapsedFeatures = new HashSet<>();
		for (final IFeature f : nonExplanationFeatures) {
			final IGraphicalFeature feature = getGraphicalFeatureModel().getGraphicalFeature(f);
			if (feature.isCollapsed()) {
				continue;
			}
			collapsedFeatures.add(feature);
		}
		return collapsedFeatures;
	}

	/**
	 * Returns all parent features of the given features (not only the direct parents).
	 *
	 * @param features features with parents
	 * @return all parent features of the given features
	 */
	private static Set<IFeature> getAllParentFeatures(Collection<IFeature> features) {
		final Set<IFeature> parents = new HashSet<>();
		for (IFeature feature : features) {
			while (true) {
				if (feature.getStructure().getParent() == null) {
					break;
				}
				feature = feature.getStructure().getParent().getFeature();
				if (!parents.add(feature)) {
					break;
				}
			}
		}
		return parents;
	}

	@Override
	protected FeatureIDEEvent operation() {
		setCollapsedFeatures(createCollapsedFeatures());
		for (final IGraphicalFeature collapsedFeature : getCollapsedFeatures()) {
			collapsedFeature.setCollapsed(true);
		}
		return new FeatureIDEEvent(getExplanation().getSubject(), EventType.COLLAPSED_ALL_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		for (final IGraphicalFeature collapsedFeature : getCollapsedFeatures()) {
			collapsedFeature.setCollapsed(false);
		}
		return new FeatureIDEEvent(getExplanation().getSubject(), EventType.COLLAPSED_ALL_CHANGED);
	}
}
