/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.FeatureModelFormatChecker;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ExportFeatureModelDialog;
import de.ovgu.featureide.fm.ui.handlers.base.AFileHandler;

public abstract class AExportHandler<T> extends AFileHandler {

	@Override
	protected void singleAction(IFile modelFile) {
		singleAction(EclipseFileSystem.getPath(modelFile));
	}

	public void singleAction(Path modelFilePath) {
		final List<? extends IPersistentFormat<T>> formatExtensions = getFormats();
		final String[][] filter = getFilter(formatExtensions);

		final FileHandler<T> fileHandler = read(modelFilePath);

		final T obj = fileHandler.getObject();

		if (obj instanceof IFeatureModel) {
			final IFeatureModel featureModel = (IFeatureModel) obj;
			final ExportFeatureModelDialog dialog = new ExportFeatureModelDialog(new Shell(), modelFilePath.getParent().toString(), filter[0],
						// format callback
						(formatIndex) -> {
							@SuppressWarnings("unchecked")
							final IPersistentFormat<IFeatureModel> format = (IPersistentFormat<IFeatureModel>) formatExtensions.get(formatIndex);
							final ProblemList pl = FeatureModelFormatChecker.checkFormat(format, featureModel);
							return pl;
						},
						// export callback
						(formatIndex, path, name) -> {
							final IPersistentFormat<T> format = (IPersistentFormat<T>) formatExtensions.get(formatIndex);
							save(format, fileHandler, path.resolve(name + "." + format.getSuffix()));
						});
			dialog.open();
		} else {
			final FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
			fileDialog.setFilterNames(filter[0]);
			fileDialog.setFilterExtensions(filter[1]);
			if (filter[0].length > 0) {
				fileDialog.setFilterIndex(getDefaultFormat(formatExtensions));
			}
			fileDialog.setFileName(getDefaultFileName(modelFilePath));
			fileDialog.setFilterPath(getDefaultPath(modelFilePath));
			fileDialog.setOverwrite(true); // Ask for file name
			final String filepath = fileDialog.open();
			if (filepath != null) {
				save(formatExtensions.get(fileDialog.getFilterIndex()), fileHandler, Paths.get(filepath));
			}
		}
	}

	protected abstract List<? extends IPersistentFormat<T>> getFormats();

	protected abstract FileHandler<T> read(final Path modelFilePath);

	protected int getDefaultFormat(List<? extends IPersistentFormat<T>> formatExtensions) {
		return 0;
	}

	protected String getDefaultPath(final Path modelFilePath) {
		return modelFilePath.getParent().toString();
	}

	protected String getDefaultFileName(final Path modelFilePath) {
		return SimpleFileHandler.getFileName(modelFilePath);
	}

	protected void save(final IPersistentFormat<T> format, FileHandler<T> fileHandler, final Path path) {
		if (!fileHandler.getLastProblems().containsError()) {
			SimpleFileHandler.save(path, fileHandler.getObject(), format);
		}
	}

	protected String[][] getFilter(List<? extends IPersistentFormat<T>> formatExtensions) {
		int countWritableFormats = 0;
		for (final IPersistentFormat<?> format : formatExtensions) {
			if (format.supportsWrite()) {
				countWritableFormats++;
			}
		}
		final String[][] filterArray = new String[2][countWritableFormats];
		final String[] names = filterArray[0];
		final String[] extensions = filterArray[1];
		int index = 0;
		for (final IPersistentFormat<?> format : formatExtensions) {
			if (format.supportsWrite()) {
				names[index] = format.getName() + " " + ("*." + format.getSuffix());
				extensions[index++] = "*." + format.getSuffix();
			}
		}

		return filterArray;
	}

	protected static final int getDefaultFormat(List<? extends IPersistentFormat<?>> formatExtensions, String id) {
		int index = 0;
		for (final IPersistentFormat<?> format : formatExtensions) {
			if (format.supportsWrite()) {
				if (id.equals(format.getId())) {
					return index;
				}
				index++;
			}
		}
		return -1;
	}

}
