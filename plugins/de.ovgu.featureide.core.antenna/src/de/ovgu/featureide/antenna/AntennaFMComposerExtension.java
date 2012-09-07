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
package de.ovgu.featureide.antenna;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.antenna.model.AntennaModelBuilder;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FMComposerExtension;
import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Antenna specific feature model extensions.
 *  
 * @author Christoph Giesel
 * @author Marcus Kamieth
*/
public class AntennaFMComposerExtension extends FMComposerExtension {

	private static String ORDER_PAGE_MESSAGE = 
			"FeatureIDE projects based on preprocessors such as Antenna do not\n" +
			"need an order, as the order is given directly at the source code.";
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.IFMComposerExtension#getComposer()
	 */
	@Override
	public String getOrderPageMessage() {
		return ORDER_PAGE_MESSAGE;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.IFMComposerExtension#hasFeaureOrder()
	 */
	@Override
	public boolean hasFeaureOrder() {
		return false;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.FMComposerExtension#performRenaming(java.lang.String, java.lang.String, org.eclipse.core.resources.IProject)
	 */
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
		Scanner scanner = null;
		FileWriter fw = null;
		try {
			File file = iFile.getRawLocation().toFile();
			
			StringBuilder fileText = new StringBuilder();
			scanner = new Scanner(file, "UTF-8");
			while (scanner.hasNext()) {
				fileText.append(scanner.nextLine());
				fileText.append(System.getProperty("line.separator"));
			}
			
			String newText = replaceFeatureInText(fileText.toString(), oldName, newName);
			
			if (fileText.toString().equals(newText)) {
				return;
			}
			
			fw = new FileWriter(file);
			fw.write(newText);
			
		} catch (FileNotFoundException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} finally{
			if(scanner!=null)
			scanner.close();
			if(fw!=null)
				try {
					fw.close();
				} catch (IOException e) {
					AntennaCorePlugin.getDefault().logError(e);
				}	
		}
	}
	
	private String replaceFeatureInText(String text, String oldName, String newName){
		Pattern pattern = Pattern.compile(String.format(AntennaModelBuilder.REGEX, oldName));
		Matcher matcher = pattern.matcher(text);

		while(matcher.find()){
			String newText = matcher.group(1) + newName + matcher.group(3);
			text = text.replace(matcher.group(0), newText);
			matcher.reset(text);
		}

		return text;
	}
}
