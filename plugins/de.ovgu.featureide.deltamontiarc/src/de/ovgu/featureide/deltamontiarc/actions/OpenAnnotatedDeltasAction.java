package de.ovgu.featureide.deltamontiarc.actions;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

public class OpenAnnotatedDeltasAction implements IObjectActionDelegate{

	private Feature selectedFeature;
	private FeatureModelEditor featureModelEditor;
	
	@Override
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		if (targetPart instanceof FeatureModelEditor) {
			this.featureModelEditor = (FeatureModelEditor) targetPart;
		}
	}

	@Override
	public void run(IAction action) {
		IProject project = ((IResource) featureModelEditor.getGrammarFile().getResource().getAdapter(IFile.class)).getProject();
		String sourceName = featureModelEditor.getFeatureModel().getProjectConfigurationPath(project);
		IFolder sourceFolder = null;
		if (sourceName != null && !sourceName.equals("")) {
			sourceFolder = project.getFolder(sourceName);
		}
		IFolder featureFolder = sourceFolder.getFolder(selectedFeature.getName());
		List<IFile> deltaFiles = getFilesByFileEnding(featureFolder, ".delta");
		for (IFile deltaFile : deltaFiles) {
			IFileEditorInput editorInput = new FileEditorInput(deltaFile);
			try {
				featureModelEditor.getSite().getPage().openEditor(editorInput, "MADelta");
			} catch (PartInitException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		if (selection instanceof StructuredSelection) {
			StructuredSelection structuredSelection = (StructuredSelection) selection;
			Object element = structuredSelection.getFirstElement();
			if (element instanceof FeatureEditPart) {
				FeatureEditPart selectedFeatureEditPart = (FeatureEditPart) element;
				selectedFeature = selectedFeatureEditPart.getFeatureModel();
			}
		}
	}
    
    private List<IFile> getFilesByFileEnding(IFolder dir, String ending) {
        List<IFile> files = new ArrayList<IFile>();
        if (dir.exists()) {
        	File[] content = new File(dir.getRawLocation().toOSString()).listFiles();
            for (File x : content) {
                if (x.isDirectory()) {
                    files.addAll(getFilesByFileEnding(dir.getFolder(x.getName()), ending));
                }
                else if (x.getName().toLowerCase().endsWith(ending)) {
                    files.add(dir.getFile(x.getName()));
                }
            }
            
        }
        return files;
    }
}
