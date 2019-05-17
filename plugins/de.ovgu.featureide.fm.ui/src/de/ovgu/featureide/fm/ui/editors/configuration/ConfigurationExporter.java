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
package de.ovgu.featureide.fm.ui.editors.configuration;

import static de.ovgu.featureide.fm.core.localization.StringTable.NOTHING_HAS_BEEN_SAVED_FOR_CONFIGURATION_EXPORT___;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * This class is responsible for exporting the configuration of Feature Models.
 *
 * @author Simon Wenk
 * @author Yang Liu
 */
public class ConfigurationExporter {

	public static boolean exportAs(Configuration configuration) {
		final FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
		final String[] extensions = { "*.tex" };
		fileDialog.setFilterExtensions(extensions);
		final String[] filterNames = { "LaTeX-Document *.tex" };
		fileDialog.setFilterNames(filterNames);
		fileDialog.setOverwrite(true);
		final String filePath = fileDialog.open();
		if (filePath == null) {
			return false;
		}

		final File file = new File(filePath);

		if (file.getAbsolutePath().endsWith(".tex")) {
			// create new folder
			final StringBuilder myFileName = new StringBuilder();
			myFileName.append(file.getName().toString());
			myFileName.delete(myFileName.length() - 4, myFileName.length());
			Path outputDir;
			try {
				outputDir = Paths.get(file.getParent()).resolve(myFileName.toString());
				FileSystem.mkDir(outputDir);
			} catch (final IOException e) {
				FMUIPlugin.getDefault().logError(e);
				return false;
			}

			// print Head
			final IPersistentFormat<Configuration> formatHead = new LatexFormat.LaTeXHead();
			FileHandler.save(outputDir.resolve("head.tex"), null, formatHead);

			// print Main
			final IPersistentFormat<Configuration> formatMain = new LatexFormat.LaTeXMain();
			FileHandler.save(outputDir.resolve(file.getName()), configuration, formatMain);

			// print Body
			final IPersistentFormat<Configuration> formatBody = new LatexFormat.LaTeXBody(file.getName());
			FileHandler.save(outputDir.resolve("body.tex"), null, formatBody);

			ConfigurationExporter.printExportMessage(file, true);
			return true;
		}

		return false;
	}

	public static void printExportMessage(File file, boolean successful) {
		final boolean done = successful && (file != null);
		final String infoMessage =
			done ? "Configuration export has been saved to\n" + file.getAbsolutePath() : NOTHING_HAS_BEEN_SAVED_FOR_CONFIGURATION_EXPORT___;
		FMUIPlugin.getDefault().logInfo(infoMessage);
	}
}
