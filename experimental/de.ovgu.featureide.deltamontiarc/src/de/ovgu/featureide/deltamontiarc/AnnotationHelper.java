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
