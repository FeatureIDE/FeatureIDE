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
package de.ovgu.featureide.fm.ui;

import static de.ovgu.featureide.fm.core.localization.StringTable.NOTHING_HAS_BEEN_SAVED_FOR_DIAGRAM_EXPORT___;
import static de.ovgu.featureide.fm.core.localization.StringTable.SAVE_IMAGE;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationTikzExporter;

/**
 * Export graphical representation of some object.
 *
 * @author Sebastian Krieter
 */
public class GraphicsExporter {

	public static final List<ExportType<GraphicalViewerImpl>> exporter = Arrays.asList(//
			new FMBitmapExporter("png", "Portable Network Graphics"), //
			new FMBitmapExporter("bmp", "Windows Bitmap"), //
			new FMBitmapExporter("gif", "GIF"), //
			new FMBitmapExporter("ico", "ICO"), //
			new FMBitmapExporter("jpg", "JPEG"), //
			new FMBitmapExporter("tif", "TIF"), //
			new FMSvgExporter(), //
			new FMTikzExporter());

	private static final List<ExportType<Configuration>> configurationExporter = Arrays.asList(new ConfigurationTikzExporter());

	public static boolean exportAs(GraphicalViewerImpl diagramEditor) {
		return GraphicsExporter.exportAs(diagramEditor, exporter);
	}

	public static boolean exportAs(GraphicalViewerImpl diagramEditor, String filePath, int index) {
		return GraphicsExporter.exportAs(diagramEditor, exporter, filePath, index);
	}

	public static boolean exportAs(Configuration configuration) {
		return GraphicsExporter.exportAs(configuration, configurationExporter);
	}

	private static <T> boolean exportAs(T object, List<ExportType<T>> exporter) {
		final FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);

		fileDialog.setFilterExtensions(exporter.stream().map(exp -> "*." + exp.getFileExtension()).toArray(String[]::new));
		fileDialog.setFilterNames(exporter.stream().map(exp -> exp.getDescription() + " *." + exp.getFileExtension()).toArray(String[]::new));
		fileDialog.setOverwrite(true);
		final String filePath = fileDialog.open();
		if (filePath == null) {
			return false;
		}
		final int index = fileDialog.getFilterIndex();
		return exportAs(object, exporter, filePath, index);
	}

	private static <T> boolean exportAs(T object, List<ExportType<T>> exporter, String filePath, int index) {
		if (index < 0) {
			final String fileExtension = SimpleFileHandler.getFileExtension(filePath);
			final Optional<ExportType<T>> any = exporter.stream().filter(exp -> Objects.equals(fileExtension, exp.getFileExtension())).findAny();
			if (any.isPresent()) {
				writeToFile(any.get(), object, Paths.get(filePath));
			} else {
				return false;
			}
		} else {
			writeToFile(exporter.get(index), object, Paths.get(filePath));
		}
		return true;
	}

	private static <T> void writeToFile(ExportType<T> exporter, final T graphicalViewer, final Path file) {
		final UIJob job = new UIJob(SAVE_IMAGE) {

			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				try {
					exporter.export(file, graphicalViewer);
					FMUIPlugin.getDefault().logInfo("Graphic export has been saved to\n" + file.toAbsolutePath());
					return Status.OK_STATUS;
				} catch (final IOException e) {
					FMUIPlugin.getDefault().logInfo(NOTHING_HAS_BEEN_SAVED_FOR_DIAGRAM_EXPORT___);
					return new Status(IStatus.ERROR, e.getClass().getName(), e.getMessage());
				}
			}
		};
		job.schedule();
	}

}
