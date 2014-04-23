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
