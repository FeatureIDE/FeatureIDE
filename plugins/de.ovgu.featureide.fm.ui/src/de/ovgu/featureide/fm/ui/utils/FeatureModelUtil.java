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
package de.ovgu.featureide.fm.ui.utils;

import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;

/**
 * TODO This is a util class thats provides some helper methods to get feature model context.
 *
 * @author "Rosiak Kamil"
 */
public class FeatureModelUtil {
	/**
	 * This method returns the active feature model editor if available else it returns null.
	 */
	public static FeatureModelEditor getActiveFMEditor() {
		final IEditorPart viewReferences = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
		if (viewReferences instanceof FeatureModelEditor) {
			return (FeatureModelEditor) viewReferences;
		}
		return null;
	}

	/**
	 * This method returns the feature model of the active editor.
	 */
	public static IFeatureModel getFeatureModel() {
		final FeatureModelEditor fmEditor = getActiveFMEditor();
		return fmEditor.getFeatureModel();
	}

	/**
	 * This method returns the original feature model of the active editor.
	 */
	public static IFeatureModel getOriginalFeatureModel() {
		final FeatureModelEditor fmEditor = getActiveFMEditor();
		return fmEditor.getOriginalFeatureModel();
	}
}
