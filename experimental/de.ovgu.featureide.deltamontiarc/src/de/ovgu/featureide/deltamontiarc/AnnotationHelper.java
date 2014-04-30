package de.ovgu.featureide.deltamontiarc;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;

public class AnnotationHelper {

	public FeatureModelEditor getFeatureModelEditor() {
		IWorkbenchPart activePart = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getPartService().getActivePart();
		if (activePart instanceof FeatureModelEditor) {
			return (FeatureModelEditor) activePart;
		}
		return null;
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
    
    public List<IFile> getAnnotatedDeltasForFeature(Feature feature) {
		FeatureModelEditor featureModelEditor = getFeatureModelEditor();
		if (featureModelEditor == null) {
			return new ArrayList<IFile>();
		}
		IProject project = ((IResource) featureModelEditor.getGrammarFile().getResource().getAdapter(IFile.class)).getProject();
		String sourceName = featureModelEditor.getFeatureModel().getProjectConfigurationPath(project);
		IFolder sourceFolder = null;
		if (sourceName != null && !sourceName.equals("")) {
			sourceFolder = project.getFolder(sourceName);
		}
		IFolder featureFolder = sourceFolder.getFolder(feature.getName());
		return getFilesByFileEnding(featureFolder, ".delta");
    }
}
