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
package de.ovgu.featureide.ahead.actions;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.LinkedList;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.ahead.AheadComposer;
import de.ovgu.featureide.ahead.AheadCorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTMethod;

/**
 * Changes the composer of an feature project project to <code>AHEAD</code>.
 * 
 * @author Jens Meinicke
 */
public class FeatureHouseToAHEADConversion extends ComposerConversion {

	private static final String SOURCE_ENTRY = "\t<classpathentry kind=\"src\" path=\"";
	private static final String EXCLUDE_ENTRY = "\t<classpathentry excluding=\"";
	private static final String EXCLUDE_SOURCE_ENTRY = "\" kind=\"src\" path=\"";
	private static final String CLASSPATH_START = "<classpath>";
	
	/**
	 * Changes the composer of the given feature project to <code>AHEAD</code>.
	 * @param featureProject
	 */
	public FeatureHouseToAHEADConversion(final IFeatureProject featureProject) {
		if (featureProject == null) {
			return;
		}
		AheadCorePlugin.getDefault().logInfo("Change the composer of project " 
				+ featureProject.getProjectName() + 
				" from FeatureHouse to AHEAD.");
		Job job = new Job("Change composer.") {
			protected IStatus run(IProgressMonitor monitor) {
				setJavaBuildPath(featureProject);
				start(featureProject);
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.SHORT);
		job.schedule();
		
	}

	/**
	 * Sets the java build path to the build folder of the given feature project.
	 * @param featureProject
	 */
	private void setJavaBuildPath(IFeatureProject featureProject) {
		Scanner scanner = null;
		FileWriter fw = null;
		IFile iClasspathFile = featureProject.getProject()
				.getFile(".classpath");
		if (!iClasspathFile.exists()) {
			return;
		}
		try {
			File file = iClasspathFile.getRawLocation().toFile();
			StringBuffer fileText = new StringBuffer();
			scanner = new Scanner(file);
			boolean hasSourceEntry = false;
			while (scanner.hasNext()) {
				String line = scanner.nextLine();
				if (line.contains(SOURCE_ENTRY)) {
					fileText.append(SOURCE_ENTRY
					+ featureProject.getBuildFolder().getName() + "\"/>");
					fileText.append("\r\n");
					hasSourceEntry = true;
				} else if (line.contains(EXCLUDE_ENTRY)) {
					fileText.append(line.substring(0,
							line.indexOf(EXCLUDE_SOURCE_ENTRY)
							+ EXCLUDE_SOURCE_ENTRY.length())
							+ featureProject.getBuildFolder().getName() + "\"/>");
					fileText.append("\r\n");
					hasSourceEntry = true;
				} else {
					fileText.append(line);
					fileText.append("\r\n");
				}
			}
			String fileTextString;
			if (!hasSourceEntry) {
				fileTextString = fileText.toString().replaceFirst(CLASSPATH_START, 
						CLASSPATH_START + "\r\n" + SOURCE_ENTRY
						+ featureProject.getBuildFolder().getName() + "\"/>");
			} else {
				fileTextString = fileText.toString();
			}
			fw = new FileWriter(file);
			fw.write(fileTextString);
		} catch (FileNotFoundException e) {
			AheadCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			AheadCorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
			if (fw != null) {
				try {
					fw.close();
				} catch (IOException e) {
					AheadCorePlugin.getDefault().logError(e);
				}

			}
		}
	}

	/**
	 * Replaces the composer of the given feature project by <code>AHEAD</code>.
	 * @param project 
	 */
	@Override
	void changeComposer(IFeatureProject project) {
		project.setComposerID(AheadComposer.COMPOSER_ID);
	}

	/**
	 * Replaces <code>original()</code> by <code>Super().methodName()</code>.<br>
	 * Inserts <code>refines</code> to classes that refine.
	 */
	@Override
	public String changeFile(String fileText, IFile file) {
		return changeFile(fileText, file, null);
	}
	
	private String changeFile(String fileText, IFile file, LinkedList<String> methodNames) {
		fileText = fileText.replaceFirst("package\\s*\\w*;", ""); 
		
		if (fileText.contains("original(")) {
			fileText = fileText.replaceFirst(" class ",	" refines class ");
		}
		int i = 0;
		while (fileText.contains("original(")) {
			fileText = fileText.replaceFirst("original\\(", "Super()." + 
					(file != null ? getMethodName(getLine(fileText), file) : methodNames.get(i++)) + "(");
		}
		return fileText;
	}
	
	public String TChangeFile(String fileText, LinkedList<String> methodNames) {
		return changeFile(fileText, null, methodNames);
	}

	/**
	 * @param fileText 
	 * @return The lines of the given text
	 */
	private int getLine(String fileText) {
		return (fileText.substring(0, fileText.indexOf("original("))).split("\r\n").length;
	}

	/**
	 * TODO a full FST for FH is needed
	 * 
	 * @param line
	 * @param file
	 * @return The Method at the given line
	 */
	private String getMethodName(int line, IFile file) {
		if (featureProject.getFSTModel() != null &&
				featureProject.getFSTModel().getClass(file) !=  null) {
			for (FSTMethod method : featureProject.getFSTModel().getClass(file).getMethods()) {
				if (method.getBeginLine() <= line && method.getEndLine() >= line) {
					return method.methodName;
				}
			}
		}
		return "";
	}

	/**
	 * Replaces the file extension <code>.java</code> by <code>.jak</code> of the given file
	 * @param file
	 */
	@Override
	void replaceFileExtension(IFile file) {
		try {
			file.move(((IFolder)file.getParent()).getFile(file.getName().replace(".java", ".jak")).getFullPath(), true, null);
		} catch (CoreException e) {
			AheadCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * @param fileExtension The file extension of a file
	 * @return <code>true</code> if java
	 */
	@Override
	boolean canConvert(String fileExtension) {
		return fileExtension.equals("java");
	}

}
