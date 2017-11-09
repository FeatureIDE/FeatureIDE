/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.aspectj;

import static de.ovgu.featureide.fm.core.localization.StringTable.AJ;
import static de.ovgu.featureide.fm.core.localization.StringTable.BEFORE_AND_AFTER_;
import static de.ovgu.featureide.fm.core.localization.StringTable.EMPTY___;

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

/**
 * AspectJ specific feature model extensions.
 *
 * @author Jens Meinicke
 */
public class AspectJFMCompserExtension extends FMComposerExtension {

	private IFile aspectFile;

	private static String ORDER_PAGE_MESSAGE = "FeatureIDE projects based on AspectJ do not need a total order as\n"
		+ "a partial order can be defined in every aspect using the keywords\n" + BEFORE_AND_AFTER_;

	/**
	 * Check for valid java identifier
	 */
	@Override
	protected boolean isValidFeatureNameComposerSpecific(String s) {
		// An empty or null string cannot be a valid identifier
		if ((s == null) || (s.length() == 0)) {
			return false;
		}

		final char[] c = s.toCharArray();
		if (!Character.isJavaIdentifierStart(c[0])) {
			return false;
		}

		for (int i = 1; i < c.length; i++) {
			if (!Character.isJavaIdentifierPart(c[i])) {
				return false;
			}
		}

		return true;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.IFMComposerExtension#getComposer()
	 */
	@Override
	public String getOrderPageMessage() {
		return ORDER_PAGE_MESSAGE;
	}

	@Override
	public boolean performRenaming(String oldName, String newName, IProject project) {
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		if (featureProject == null) {
			return false;
		}
		final IFolder buildFolder = featureProject.getBuildFolder();
		try {
			aspectFile = AspectJComposer.getAspectFile(oldName, null, buildFolder);
			if (aspectFile.exists()) {
				renameAspect(buildFolder, oldName, newName);
				aspectFile.move(AspectJComposer.getAspectFile(newName, null, buildFolder).getFullPath(), true, null);
				buildFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
			}
		} catch (final CoreException e) {
			AspectJCorePlugin.getDefault().logError(e);
		}
		return true;
	}

	public void renameAspect(IFolder folder, String oldName, String newName) throws CoreException {
		for (final IResource res : folder.members()) {
			if (res instanceof IFolder) {
				renameAspect((IFolder) res, oldName, newName);
			} else if ((res instanceof IFile) && AJ.equals(res.getFileExtension())) {
				renameAspect((IFile) res, oldName, newName);
			}
		}
	}

	private String getPackege(String aspectName) {
		if (aspectName.contains(EMPTY___)) {
			return aspectName.replaceAll(EMPTY___, ".").substring(0, aspectName.lastIndexOf('_'));
		}
		return null;
	}

	private String getAspect(String aspectName) {
		if (aspectName.contains(EMPTY___)) {
			return aspectName.substring(aspectName.lastIndexOf('_') + 1, aspectName.length());
		}
		return aspectName;
	}

	private void renameAspect(IFile res, String oldName, String newName) {
		String content = getFileContent(res);
		content = changeFileContent(content, oldName, newName, res.equals(aspectFile));
		setFileContent(res, content);
	}

	/**
	 * Sets the content of the given file.
	 *
	 * @param res The file.
	 * @param content The new file content to set.
	 */
	private void setFileContent(IFile res, String content) {
		FileWriter fw = null;
		try {
			fw = new FileWriter(res.getRawLocation().toFile());
			fw.write(content);
		} catch (final IOException e) {
			AspectJCorePlugin.getDefault().logError(e);
		} finally {
			if (fw != null) {
				try {
					fw.close();
				} catch (final IOException e) {
					AspectJCorePlugin.getDefault().logError(e);
				}
			}
		}
	}

	/**
	 * Changes the files content if an aspect is renamed.
	 *
	 * @param content The current content.
	 * @param oldName The old aspect name.
	 * @param newName The new aspect name.
	 * @param isAspectFile <code>true</code> if the file is the file defining the aspect.
	 * @return The new file content.
	 */
	public String changeFileContent(String content, String oldName, String newName, boolean isAspectFile) {
		final String packageName = getPackege(newName);

		if (isAspectFile && content.matches("[\\w*,\\W*]*package\\s+\\w*;[\\w,\\W]*")) {
			if (packageName != null) {
				content = content.replaceFirst("package\\s+\\w*;", "package " + packageName + ";");
			}
		}

		// renaming for: aspect AspectName {
		content = content.replaceAll("aspect\\s+" + getAspect(oldName) + " ", "aspect " + getAspect(newName) + " ");
		content = content.replaceAll("aspect\\s+" + getAspect(oldName) + "\\{", "aspect " + getAspect(newName) + "\\{");

		// renaming for: aspect A1 extends AspectName {
		content = content.replaceAll("extends\\s+" + getAspect(oldName) + " ", "extends " + getAspect(newName) + " ");
		content = content.replaceAll("extends\\s+" + getAspect(oldName) + "\\{", "extends " + getAspect(newName) + "\\{");

		// renaming for: declare precedence: *, Weight, AspectName, DoubleWeight;
		content = content.replaceAll(":\\s*" + getAspect(oldName) + "s*,", ": " + getAspect(newName) + ",");
		content = content.replaceAll(":\\s*" + getAspect(oldName) + "s*;", ": " + getAspect(newName) + ";");
		content = content.replaceAll(",\\s*" + getAspect(oldName) + "s*,", ", " + getAspect(newName) + ",");
		content = content.replaceAll(",\\s*" + getAspect(oldName) + "s*;", ", " + getAspect(newName) + ";");

		return content;
	}

	/**
	 * Gets the files content.
	 *
	 * @param res The file.
	 * @return The content of the file.
	 */
	private String getFileContent(IFile res) {
		Scanner scanner = null;
		try {
			scanner = new Scanner(res.getRawLocation().toFile(), "UTF-8");
			final StringBuffer buffer = new StringBuffer();
			while (scanner.hasNext()) {
				buffer.append(scanner.nextLine());
				buffer.append("\r\n");
			}
			return buffer.toString();
		} catch (final FileNotFoundException e) {
			AspectJCorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}

		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.IFMComposerExtension#hasFeaureOrder()
	 */
	@Override
	public boolean hasFeatureOrder() {
		return false;
	}

}
