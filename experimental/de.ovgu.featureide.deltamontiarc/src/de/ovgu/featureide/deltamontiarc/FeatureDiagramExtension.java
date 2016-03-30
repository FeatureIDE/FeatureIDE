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
package de.ovgu.featureide.deltamontiarc;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.Label;
import org.eclipse.jface.action.IMenuManager;

import de.ovgu.featureide.deltamontiarc.actions.AnnotateDeltaAction;
import de.ovgu.featureide.deltamontiarc.actions.OpenAnnotatedDeltasAction;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.FeatureFigure;

public class FeatureDiagramExtension extends 
	de.ovgu.featureide.fm.ui.editors.FeatureDiagramExtension {

	@Override
	public void extendContextMenu(IMenuManager menu,
			FeatureDiagramEditor featureDiagramEditor) {
		AnnotateDeltaAction annotateAction = new AnnotateDeltaAction("Annotate Delta...", featureDiagramEditor);
		annotateAction.setEnabled(true);
		annotateAction.setChecked(false);
		menu.add(annotateAction);
		
		OpenAnnotatedDeltasAction openAction = new OpenAnnotatedDeltasAction("Open Annotated Deltas", featureDiagramEditor);
		openAction.setEnabled(true);
		openAction.setChecked(false);
		menu.add(openAction);
	}
	
	@Override
	public Figure extendFeatureFigureToolTip(Figure toolTipContent, FeatureFigure figure) {
		AnnotationHelper helper = new AnnotationHelper();
		List<IFile> annotatedDeltas = helper.getAnnotatedDeltasForFeature(figure.getFeature());
		String eol = System.getProperty("line.separator");
		if (!annotatedDeltas.isEmpty()) {
		    String toolTipExtension = "Annotated Deltas:";
		    for (IFile delta : annotatedDeltas) {
		    	toolTipExtension += eol;
		    	toolTipExtension += "  ";
		    	toolTipExtension += delta.getName();
		    }
		    toolTipContent.add(new Label(toolTipExtension));
		}
		return toolTipContent;
	}
}
