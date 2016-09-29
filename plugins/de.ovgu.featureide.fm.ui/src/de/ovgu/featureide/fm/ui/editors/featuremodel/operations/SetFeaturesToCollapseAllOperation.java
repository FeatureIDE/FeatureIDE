/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Collections;
import java.util.Iterator;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.Feature;

/**
 * TODO description
 * 
 * @author Joshua Sprey
 * @author Enis Belli
 */
public class SetFeaturesToCollapseAllOperation extends AbstractFeatureModelOperation {
	
	Iterable<IFeature> featureModel;
	boolean collapse;
	public SetFeaturesToCollapseAllOperation(IFeatureModel featureModel, IFeature selectedFeature, boolean collapse) {
		super(featureModel, COLLAPSE_ALL);
		this.featureModel = featureModel.getFeatures();
		this.collapse = collapse;
	}

	@Override
	protected FeatureIDEEvent operation() {
		Iterator<IFeature> feautureModelIterator = featureModel.iterator();
		while(feautureModelIterator.hasNext())
		{
			IFeature feature = feautureModelIterator.next();
			feature.getStructure().setCollapsed(collapse);
		}
		return new FeatureIDEEvent(feautureModelIterator, EventType.COLLAPSED_ALL_CHANGED, !collapse, collapse);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		Iterator<IFeature> feautureModelIterator = featureModel.iterator();
		while(feautureModelIterator.hasNext())
		{
			IFeature feature = feautureModelIterator.next();
			feature.getStructure().setCollapsed(collapse);
		}
		return new FeatureIDEEvent(feautureModelIterator, EventType.COLLAPSED_ALL_CHANGED, !collapse, collapse);
		
	}

}
