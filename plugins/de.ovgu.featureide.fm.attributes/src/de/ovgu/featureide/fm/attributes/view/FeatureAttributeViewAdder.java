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
package de.ovgu.featureide.fm.attributes.view;

import org.eclipse.ui.PartInitException;

import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorListener;

/**
 * Listener to open the feature attribute view when a feature model editor is opened.
 * 
 * @author Benedikt Jutz
 * @author Johannes Herschel
 */
public class FeatureAttributeViewAdder implements IFeatureModelEditorListener {

	/**
	 * Opens the FeatureAttributeView whenever an editor with an {@link ExtendedFeatureModel} is opened.
	 * 
	 * @param editor - {@link FeatureModelEditor}
	 */
	@Override
	public void editorOpened(FeatureModelEditor editor) {
		if (!(editor.getOriginalFeatureModel() instanceof ExtendedFeatureModel)) {
			return;
		}

		try {
			editor.getSite().getPage().showView(FeatureAttributeView.ID);
		} catch (PartInitException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
}
