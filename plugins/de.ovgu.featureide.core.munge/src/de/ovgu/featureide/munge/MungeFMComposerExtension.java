/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.munge;

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
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FMComposerExtension;
import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Munge specific feature model extensions.
 *  
 * @author Jens Meinicke
*/
public class MungeFMComposerExtension extends FMComposerExtension {

	private static String ORDER_PAGE_MESSAGE = 
			"FeatureIDE projects based on preprocessors such as Munge do not\n" +
			"need an order, as the order is given directly at the source code.";
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.IFMComposerExtension#getComposer()
	 */
	@Override
	public String getOrderPageMessage() {
		return ORDER_PAGE_MESSAGE;
	}
	
	@Override
	public boolean performRenaming(String oldName, String newName, IProject project) {
		IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		IFolder sourceFolder = featureProject.getSourceFolder();
		if (!sourceFolder.exists())
			return true;
		
		try {
			performRenamings(oldName, newName, sourceFolder);
			sourceFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return true;
	}

	private void performRenamings(String oldName, String newName, IFolder folder) throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				performRenamings(oldName, newName, (IFolder)res);
			} else if (res instanceof IFile) {
				IFile file = (IFile)res;
				performRenamings(oldName, newName, file);
			}
			
		}
	}
	
	private void performRenamings(String oldName, String newName, IFile iFile) {
		setFilecontent(performRenamings(oldName, newName, getFileContent(iFile)), iFile);
	}

	/**
	 * @param oldName
	 * @param newName
	 * @param fileContent
	 * @return
	 */
	public String performRenamings(String oldName, String newName,
			String fileContent) {
		if (!fileContent.contains(oldName)) {
			return null;
		}
		return fileContent.replaceAll("\\["+oldName+"\\]\\*\\/","[" + newName + "]*/");
	}

	/**
	 * @param filecontent
	 * @param iFile
	 */
	private void setFilecontent(String filecontent, IFile iFile) {
		if (filecontent == null) {
			return;
		}
		File file = iFile.getRawLocation().toFile();
		FileWriter fw = null;
		try {
			fw = new FileWriter(file);
			fw.write(filecontent);
		} catch (FileNotFoundException e) {
			MungeCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			MungeCorePlugin.getDefault().logError(e);
		} finally{
			if(fw!=null) {
				try {
					fw.close();
				} catch (IOException e) {
					MungeCorePlugin.getDefault().logError(e);
				}	
			}
		}
	}

	/**
	 * @param iFile
	 * @return
	 */
	private String getFileContent(IFile iFile) {
		Scanner scanner = null;
		StringBuilder fileText = new StringBuilder();
		try {
			scanner = new Scanner(iFile.getRawLocation().toFile(), "UTF-8");
			while (scanner.hasNext()) {
				fileText.append(scanner.nextLine());
				fileText.append("\r\n");
			}
		} catch (FileNotFoundException e) {
			MungeCorePlugin.getDefault().logError(e);
		} finally{
			if(scanner!=null) {
				scanner.close();
			}
		}
		return fileText.toString();
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.IFMComposerExtension#hasFeaureOrder()
	 */
	@Override
	public boolean hasFeaureOrder() {
		return false;
	}
}
