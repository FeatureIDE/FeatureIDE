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
package de.ovgu.featureide.antenna;

import static de.ovgu.featureide.fm.core.localization.StringTable.NEED_AN_ORDER_COMMA__AS_THE_ORDER_IS_GIVEN_DIRECTLY_AT_THE_SOURCE_CODE_;

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
 * @author Marcus Pinnecke
 */
public class AntennaFMComposerExtension extends FMComposerExtension {

	private static String ORDER_PAGE_MESSAGE =
		"FeatureIDE projects based on preprocessors such as Antenna do not\n" + NEED_AN_ORDER_COMMA__AS_THE_ORDER_IS_GIVEN_DIRECTLY_AT_THE_SOURCE_CODE_;

	public static final String FEATURE_NAME_PATTERN = "^[a-zA-Z][\\w\\.\\-]*$";

	@Override
	protected boolean isValidFeatureNameComposerSpecific(String s) {
		return s.matches(FEATURE_NAME_PATTERN);
	}

	@Override
	public String getOrderPageMessage() {
		return ORDER_PAGE_MESSAGE;
	}

	@Override
	public boolean hasFeatureOrder() {
		return false;
	}

	@Override
	public boolean performRenaming(String oldName, String newName, IProject project) {
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		if (featureProject == null) {
			return false;
		}

		final IFolder sourceFolder = featureProject.getSourceFolder();
		if (!sourceFolder.exists()) {
			return true;
		}

		try {
			performRenamings(oldName, newName, sourceFolder);
			sourceFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return true;
	}

	private void performRenamings(String oldName, String newName, IFolder folder) throws CoreException {
		for (final IResource res : folder.members()) {
			if (res instanceof IFolder) {
				performRenamings(oldName, newName, (IFolder) res);
			} else if (res instanceof IFile) {
				final IFile file = (IFile) res;
				performRenamings(oldName, newName, file);
			}

		}
	}

	private void performRenamings(String oldName, String newName, IFile iFile) {
		Scanner scanner = null;
		FileWriter fw = null;
		try {
			final File file = iFile.getRawLocation().toFile();

			final StringBuilder fileText = new StringBuilder();
			scanner = new Scanner(file, "UTF-8");
			while (scanner.hasNext()) {
				fileText.append(scanner.nextLine());
				fileText.append(System.getProperty("line.separator"));
			}

			final String string = fileText.toString();
			final String newText = replaceFeatureInText(string, oldName, newName);

			if (string.equals(newText)) {
				return;
			}

			fw = new FileWriter(file);
			fw.write(newText);

		} catch (final FileNotFoundException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} catch (final IOException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
			if (fw != null) {
				try {
					fw.close();
				} catch (final IOException e) {
					AntennaCorePlugin.getDefault().logError(e);
				}
			}
		}
	}

	private String replaceFeatureInText(String text, String oldName, String newName) {
		final Pattern pattern = Pattern.compile(String.format(AntennaModelBuilder.REGEX, oldName));
		final Matcher matcher = pattern.matcher(text);

		while (matcher.find()) {
			final String newText = matcher.group(1) + newName + matcher.group(3);
			text = text.replace(matcher.group(0), newText);
			matcher.reset(text);
		}

		return text;
	}
}
