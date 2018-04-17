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
package de.ovgu.featureide.fm.attributes.view.actions;

import java.util.HashMap;

import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * TODO description
 *
 * @author Joshua
 */
public class RemoveFeatureAttributeAction extends Action {

	private final ExtendedFeatureModel featureModel;
	private final HashMap<IFeatureAttribute, ExtendedFeature> map;

	public RemoveFeatureAttributeAction(ExtendedFeatureModel featureModel, HashMap<IFeatureAttribute, ExtendedFeature> map) {
		super(StringTable.REMOVE_SELECTED_ATTRIBUTE);
		this.featureModel = featureModel;
		this.map = map;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.Action#run()
	 */
	@Override
	public void run() {
		for (final IFeatureAttribute featureAttribute : map.keySet()) {
			map.get(featureAttribute).removeAttribute(featureAttribute);
		}
		featureModel.fireEvent(new FeatureIDEEvent(featureModel.getStructure().getRoot().getFeature(), EventType.FEATURE_ATTRIBUTE_CHANGED));
	}

	@Override
	public boolean isEnabled() {
		return map.size() > 0;
	}

}
