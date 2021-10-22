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
package de.ovgu.featureide.fm.ui.views.constraintview.content;

import java.util.Set;

import org.eclipse.jface.viewers.ColumnLabelProvider;

import de.ovgu.featureide.fm.core.base.IConstraint;

/**
 *
 *
 * @author rahel
 */
public class ConstraintViewTagsColumnLabelProvider extends ColumnLabelProvider {

	@Override
	public String getText(Object element) {
		if (element instanceof String) {
			// if no FeatureModel is opened
			return "";
		} else {
			final IConstraint constraint = (IConstraint) element;
			final Set<String> tags = constraint.getTags();
			String tagsText = "";
			for (final String tag : tags) {
				if (tagsText.equals("")) {
					tagsText += tag;
					continue;
				}
				tagsText += ", " + tag;
			}
			return tagsText;
		}
	}

}
