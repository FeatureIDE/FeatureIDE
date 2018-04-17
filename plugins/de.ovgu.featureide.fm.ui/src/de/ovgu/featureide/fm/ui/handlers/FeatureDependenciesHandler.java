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
package de.ovgu.featureide.fm.ui.handlers;

import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATING_FEATURE_DEPENDENCIES;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Paths;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.FeatureDependencies;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.handlers.base.AFileHandler;

/**
 * calculates and shows dependencies between features in a MessageBox
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
//TODO implement own feature model format
public class FeatureDependenciesHandler extends AFileHandler {

	@Override
	protected void singleAction(final IFile inputFile) {
		final IFeatureModel mod = readModel(inputFile);
		final Job job = new Job(CALCULATING_FEATURE_DEPENDENCIES) {

			@Override
			protected IStatus run(IProgressMonitor monitor) {
				final String text = new FeatureDependencies(mod).toStringWithLegend();
				// UI access
				final StringBuilder path = new StringBuilder();
				Display.getDefault().syncExec(new Runnable() {

					@Override
					public void run() {
						path.append(openFileDialog());
					}

				});
				saveFile(text, path.toString());
				return Status.OK_STATUS;
			}

		};
		job.setPriority(Job.INTERACTIVE);
		job.schedule();
	}

	/**
	 * saves the given content to a text File at a given path(including filename)
	 *
	 * @param content
	 * @param path
	 */
	private void saveFile(String content, String path) {
		if (path == null) {
			return;
		}
		final File outputFile = new File(path);
		BufferedWriter out = null;
		try {
			out = new BufferedWriter(new FileWriter(outputFile));
			out.write(content);
		} catch (final IOException e) {} finally {
			if (out != null) {
				try {
					out.close();
				} catch (final IOException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}
		}

		return;
	}

	/**
	 * opens a File Dialog and returns the selected path
	 *
	 * @param text
	 *
	 */
	private String openFileDialog() {
		final FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
		fileDialog.setFileName("*.txt");
		fileDialog.setOverwrite(true);
		return fileDialog.open();
	}

	/**
	 * reads the featureModel from file
	 *
	 * @param inputFile
	 * @return featureModel
	 * @throws UnsupportedModelException
	 * @throws FileNotFoundException
	 */
	private IFeatureModel readModel(IFile inputFile) {
		return FeatureModelManager.load(Paths.get(inputFile.getLocationURI())).getObject();
	}

}
