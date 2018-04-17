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
package de.ovgu.featureide.fm.ui.views.outline.custom.providers;

import static de.ovgu.featureide.fm.core.localization.StringTable.AN_OUTLINE_IS_NOT_AVAILABLE_;

import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider;

/**
 * Content provider for displaying a not available message in the outline
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Reimar Schroeter
 * @author Dominic Labsch
 * @author Daniel Psche
 * @author Christopher Sontag
 */

public class NotAvailableContentProvider extends OutlineTreeContentProvider {

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

	@Override
	public void dispose() {}

	@Override
	public boolean hasChildren(Object element) {
		return false;
	}

	@Override
	public Object getParent(Object element) {
		return null;
	}

	@Override
	public Object[] getElements(Object inputElement) {
		return new String[] { AN_OUTLINE_IS_NOT_AVAILABLE_ };
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		return null;
	}
}
