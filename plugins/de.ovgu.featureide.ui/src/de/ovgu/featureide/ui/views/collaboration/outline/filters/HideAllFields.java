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
package de.ovgu.featureide.ui.views.collaboration.outline.filters;

import java.util.LinkedList;

import org.eclipse.jface.resource.ImageDescriptor;

import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter;
import de.ovgu.featureide.ui.UIPlugin;

/**
 *
 * Filter to hide fields in the collaboration outline.
 *
 * @author Dominic Labsch
 * @author Daniel P�sche
 */
public class HideAllFields implements IOutlineFilter {

	@Override
	public Object[] filter(Object[] obj) {
		final LinkedList<Object> resultList = new LinkedList<Object>();

		if ((obj.length > 0) && (obj[0] instanceof RoleElement)) {
			for (int i = 0; i < obj.length; i++) {
				if (!(obj[i] instanceof FSTField)) {
					resultList.add(obj[i]);
				}
			}
		} else {
			return obj;
		}
		return resultList.toArray();

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter#getName()
	 */
	@Override
	public String getName() {
		return "Hide All Fields";
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter#getImage()
	 */
	@Override
	public ImageDescriptor getImage() {
		return UIPlugin.getDefault().getImageDescriptor("icons/fields_co.gif");
	}

}
