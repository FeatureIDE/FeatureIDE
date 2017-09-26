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

import static de.ovgu.featureide.fm.core.localization.StringTable.COLLAPSE_ALL;

import java.util.Iterator;
import java.util.LinkedList;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation with functionality to set all features to collapsed. Enables undo/redo functionality.
 *
 * @author Joshua Sprey
 * @author Enis Belli
 * @author Maximilian Kühl
 * @author Christopher Sontag
 */
public class CollapseAllOperation extends AbstractFeatureModelOperation {

	Iterable<IGraphicalFeature> features;
	boolean collapse;

	private final LinkedList<IGraphicalFeature> affectedFeatureList = new LinkedList<IGraphicalFeature>();

	public CollapseAllOperation(IGraphicalFeatureModel graphicalFeatureModel, boolean collapse) {
		super(graphicalFeatureModel.getFeatureModel(), COLLAPSE_ALL);
		features = graphicalFeatureModel.getFeatures();
		this.collapse = collapse;
	}

	@Override
	protected FeatureIDEEvent operation() {
		final Iterator<IGraphicalFeature> feautureModelIterator = features.iterator();
		while (feautureModelIterator.hasNext()) {
			final IGraphicalFeature gFeature = feautureModelIterator.next();
			final IFeature feature = gFeature.getObject();
			if (!feature.getStructure().isRoot() || !collapse) {
				if (feature.getStructure().hasChildren()) {
					if (gFeature.isCollapsed() != collapse) {
						affectedFeatureList.add(gFeature);
					}
					gFeature.setCollapsed(collapse);
				}
			}
		}
		return new FeatureIDEEvent(feautureModelIterator, EventType.COLLAPSED_ALL_CHANGED, null, null);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		final Iterator<IGraphicalFeature> feautureModelIterator = features.iterator();
		for (final IGraphicalFeature f : affectedFeatureList) {
			f.setCollapsed(!collapse);
		}
		return new FeatureIDEEvent(feautureModelIterator, EventType.COLLAPSED_ALL_CHANGED, null, null);

	}

}
