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
