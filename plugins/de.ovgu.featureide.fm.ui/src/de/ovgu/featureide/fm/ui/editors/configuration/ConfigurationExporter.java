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

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * TODO description
 *
 * @author liuya
 */
public class ConfigurationExporter {

	public static boolean exportAs() {
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
		// TODO: EXPORT
		final IPersistentFormat<Configuration> format = new LatexFormat();
		FileHandler.save(file.toPath(), null, format);
		final boolean succ = true;
		// final boolean succ = ConfigurationExporter.exportAs(diagramEditor, file);
		ConfigurationExporter.printExportMessage(file, succ);
		return succ;
	}

	public static void printExportMessage(File file, boolean successful) {
		final boolean done = successful && (file != null);
		final String infoMessage =
			done ? "Configuration export has been saved to\n" + file.getAbsolutePath() : NOTHING_HAS_BEEN_SAVED_FOR_CONFIGURATION_EXPORT___;
		FMUIPlugin.getDefault().logInfo(infoMessage);
	}

	public static void run() {
		System.out.println("Dies ist ein Test.");
	}
}
