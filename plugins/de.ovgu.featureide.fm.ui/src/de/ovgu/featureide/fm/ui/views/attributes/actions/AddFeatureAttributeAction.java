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
package de.ovgu.featureide.fm.ui.views.attributes.actions;

import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.core.attributes.IFeatureAttribute;
import de.ovgu.featureide.fm.core.attributes.impl.BooleanFeatureAttribute;
import de.ovgu.featureide.fm.core.attributes.impl.DoubleFeatureAttribute;
import de.ovgu.featureide.fm.core.attributes.impl.FeatureAttribute;
import de.ovgu.featureide.fm.core.attributes.impl.LongFeatureAttribute;
import de.ovgu.featureide.fm.core.attributes.impl.StringFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;

/**
 * TODO description
 *
 * @author Joshua
 */
public class AddFeatureAttributeAction extends Action {

	private final IFeatureModel featureModel;
	private final IFeature feature;
	private final String attributeType;

	public AddFeatureAttributeAction(IFeatureModel featureModel, IFeature feature, String attributeType, String actionName) {
		super(actionName);
		this.featureModel = featureModel;
		this.feature = feature;
		this.attributeType = attributeType;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.Action#run()
	 */
	@Override
	public void run() {
		switch (attributeType) {
		case FeatureAttribute.BOOLEAN:
			final IFeatureAttribute attributeBoolean = new BooleanFeatureAttribute("<Name>", "", null, false, false);
			feature.getProperty().addAttribute(attributeBoolean);
			break;
		case FeatureAttribute.DOUBLE:
			final IFeatureAttribute attributeDouble = new DoubleFeatureAttribute("<Name>", "", null, false, false);
			feature.getProperty().addAttribute(attributeDouble);
			break;
		case FeatureAttribute.LONG:
			final IFeatureAttribute attributeLong = new LongFeatureAttribute("<Name>", "", null, false, false);
			feature.getProperty().addAttribute(attributeLong);
			break;
		case FeatureAttribute.STRING:
			final IFeatureAttribute attributeString = new StringFeatureAttribute("<Name>", "", null, false, false);
			feature.getProperty().addAttribute(attributeString);
			break;
		default:
			break;
		}
		featureModel.fireEvent(new FeatureIDEEvent(feature, EventType.FEATURE_ATTRIBUTE_CHANGED));
	}
}
