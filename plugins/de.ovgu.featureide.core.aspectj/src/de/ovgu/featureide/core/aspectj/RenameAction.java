/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.aspectj;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.IRenameAction;

/**
 * Moves aspectfiles after renamings at featuremodel and updates all entrys 
 * of those aspect of all sourcefiles.
 * 
 * @author Jens Meinicke
 */
public class RenameAction implements IRenameAction {

	private IFile aspectFile;

	public RenameAction() {

	}

	@Override
	public void performRenaming(String oldName, String newName, IProject project) {
		IFolder buildFolder = CorePlugin.getFeatureProject(project).getBuildFolder();
		try {
			aspectFile = AspectJComposer.getAspectFile(oldName, null, buildFolder);
			if (aspectFile.exists()) {
				renameAspect(buildFolder, oldName, newName);
				aspectFile.move(AspectJComposer.getAspectFile(newName, null, buildFolder).getFullPath(), true, null);
				buildFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
			}
		} catch (CoreException e) {
			AspectJCorePlugin.getDefault().logError(e);
		}
	}

	public void renameAspect(IFolder folder, String oldName, String newName) throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				renameAspect((IFolder)res , oldName, newName);
			} else if (res instanceof IFile) {
				setFileText((IFile)res, oldName, newName);
			}
		}
	}
	
	private String getPackege(String aspectName) {
		if (aspectName.contains("_")) {
			return aspectName.replaceAll("_", ".").substring(0, aspectName.lastIndexOf("_"));
		}
		return null;
	}
	
	private String getAspect(String aspectName) {
		if (aspectName.contains("_")) {
			return aspectName.substring(aspectName.lastIndexOf("_") + 1, aspectName.length());
		}
		return aspectName;
	}

	private void setFileText(IFile res, String oldName, String newName) {
		Scanner scanner = null;
		FileWriter fw = null;
		try {
			String packageName = getPackege(newName);
			File file = res.getRawLocation().toFile();
			StringBuffer fileText = new StringBuffer();
			scanner = new Scanner(file);
			while (scanner.hasNext()) {
				String text = scanner.nextLine();
				if (res.equals(aspectFile) && text.contains("package ")) {
					if (packageName != null) {
						fileText.append("package " + packageName + ";");
						fileText.append("\r\n");
					}
				} else {
					fileText.append(text);
					fileText.append("\r\n");
				}
			}
			
			if (!fileText.toString().contains(getAspect(oldName))) {
				return;
			}
			// TODO revise replacement \w or \W for word char
			String fileTextString = fileText.toString().replaceAll(getAspect(oldName), getAspect(newName));
			
			if (packageName != null && !fileTextString.contains("package " + packageName + ";")) {
				fileTextString = "package " + packageName + ";\r\n" + fileTextString;
			}
			fw = new FileWriter(file);
			fw.write(fileTextString);
			
		} catch (FileNotFoundException e) {
			AspectJCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			AspectJCorePlugin.getDefault().logError(e);
		}
		finally{
			if(scanner!=null)
			scanner.close();
			if(fw!=null)
				try {
					fw.close();
				} catch (IOException e) {
					AspectJCorePlugin.getDefault().logError(e);
				}	
		}
	}

}
