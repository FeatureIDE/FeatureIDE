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
package de.ovgu.featureide.deltamontiarc.actions;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.deltamontiarc.AnnotationHelper;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.SingleSelectionAction;

public class OpenAnnotatedDeltasAction extends SingleSelectionAction{

	public OpenAnnotatedDeltasAction(String text, Object viewer2) {
		super(text, viewer2);
	}
	
	@Override
	public void run() {
		AnnotationHelper helper = new AnnotationHelper();
		List<IFile> deltaFiles = helper.getAnnotatedDeltasForFeature(getSelectedFeature());
		FeatureModelEditor editor = helper.getFeatureModelEditor();
		for (IFile deltaFile : deltaFiles) {
			IFileEditorInput editorInput = new FileEditorInput(deltaFile);
			try {
				if (editor != null) {
					editor.getSite().getPage().openEditor(editorInput, "MADelta");
				}
			} catch (PartInitException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}
    


	@Override
	protected void updateProperties() {
		setEnabled(true);
		setChecked(false);		
	}
}
