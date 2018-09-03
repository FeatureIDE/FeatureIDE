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
package de.ovgu.featureide.fm.ui;

import static de.ovgu.featureide.fm.core.localization.StringTable.DISABLECLIPPINGBUTTON;
import static de.ovgu.featureide.fm.core.localization.StringTable.ECLIPSE_PLUGIN_FOR_EXPORTING_DIAGRAM_IN_SVG_FORMAT_IS_NOT_EXISTING_;
import static de.ovgu.featureide.fm.core.localization.StringTable.NL_UTWENTE_CE_IMAGEEXPORT;
import static de.ovgu.featureide.fm.core.localization.StringTable.NL_UTWENTE_CE_IMAGEEXPORT_CORE_IMAGEEXPORTPLUGIN;
import static de.ovgu.featureide.fm.core.localization.StringTable.NOTHING_HAS_BEEN_SAVED_FOR_DIAGRAM_EXPORT___;
import static de.ovgu.featureide.fm.core.localization.StringTable.PROVIDESETTINGS;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.SVG_EXPORT_FAILED;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.eclipse.core.internal.runtime.InternalPlatform;
import org.eclipse.draw2d.IFigure;
import org.eclipse.gef.editparts.LayerManager;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.osgi.framework.Bundle;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.elements.TikzFormat;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GEFImageWriter;

/**
 * This class is responsible for exporting graphics (FeatureModel and CollaborationDiagram)
 *
 * @author Guenter Ulreich
 * @author Marcus Pinnecke (Feature Interface)
 */
@SuppressWarnings(RESTRICTION)
public class GraphicsExporter {

	public static boolean exportAs(IFeatureModel featureModel, ScrollingGraphicalViewer diagramEditor) {
		final FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
		final String[] extensions = { "*.png", "*.jpg", "*.bmp", "*.m", "*.xml", ".velvet", "*.svg", "*.tex" };
		fileDialog.setFilterExtensions(extensions);
		final String[] filterNames = { "Portable Network Graphics *.png", "JPEG *.jpg", "Windows Bitmap *.bmp", "GUIDSL Grammar *.m", "XML Export *.xml",
			"Velvet Export *.velvet", "Scalable Vector Graphics *.svg", "LaTeX-Document with TikZ *.tex" };
		fileDialog.setFilterNames(filterNames);
		fileDialog.setOverwrite(true);
		final String filePath = fileDialog.open();
		if (filePath == null) {
			return false;
		}

		if (filePath.endsWith(".m") || filePath.endsWith(".xml") || filePath.endsWith(".velvet")) {
			return FeatureModelManager.save(featureModel, Paths.get(filePath));
		} else {
			final File file = new File(filePath);
			final boolean succ = GraphicsExporter.exportAs(diagramEditor, file);
			GraphicsExporter.printExportMessage(file, succ);
			return succ;
		}

	}

	public static boolean exportAs(GraphicalViewerImpl viewer) {
		final FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
		final String[] extensions = { "*.png", "*.jpg", "*.bmp", "*.svg" };
		fileDialog.setFilterExtensions(extensions);
		final String[] filterNames = { "Portable Network Graphics *.png", "JPEG *.jpg", "Windows Bitmap *.bmp", "Scalable Vector Graphics *.svg" };
		fileDialog.setFilterNames(filterNames);
		fileDialog.setOverwrite(true);
		final String filePath = fileDialog.open();
		if (filePath == null) {
			return false;
		}
		final File file = new File(filePath);

		return GraphicsExporter.exportAs(viewer, file);
	}

	public static boolean exportAs(GraphicalViewerImpl viewer, File file) {
		boolean succ = false;

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

			// ---old: one Latex Document---------------------------------------------
			// final IPersistentFormat<IGraphicalFeatureModel> format = new TikzFormat();
			// FileHandler.save(file.toPath(), (IGraphicalFeatureModel) viewer.getContents().getModel(), format);
			// -----------------------------------------------------------------------

			// output Head
			final IPersistentFormat<IGraphicalFeatureModel> formatHead = new TikzFormat.TikZHead();
			FileHandler.save(outputDir.resolve("head.tex"), null, formatHead);

			// output body
			final IPersistentFormat<IGraphicalFeatureModel> formatBody = new TikzFormat.TikZBody(file.getName());
			FileHandler.save(outputDir.resolve("body.tex"), null, formatBody);

			// output main
			final IPersistentFormat<IGraphicalFeatureModel> formatMain = new TikzFormat.TikZMain();
			FileHandler.save(outputDir.resolve(file.getName()), (IGraphicalFeatureModel) viewer.getContents().getModel(), formatMain);

			succ = true;

		} else if (file.getAbsolutePath().endsWith(".svg")) {
			final ScalableFreeformRootEditPart part = (ScalableFreeformRootEditPart) viewer.getEditPartRegistry().get(LayerManager.ID);
			final IFigure rootFigure = part.getFigure();

			Bundle bundleExport = null;
			Bundle bundleExportSVG = null;
			for (final Bundle b : InternalPlatform.getDefault().getBundleContext().getBundles()) {
				if (b.getSymbolicName().equals(NL_UTWENTE_CE_IMAGEEXPORT)) {
					bundleExport = b;
				}
				if (b.getSymbolicName().equals("nl.utwente.ce.imageexport.svg")) {
					bundleExportSVG = b;
				}
				if ((bundleExport != null) && (bundleExportSVG != null)) {
					break;
				}
			}

			// check if gef-imageexport is existing and activated!
			if ((bundleExport != null) && (bundleExportSVG != null)) {
				try {
					final org.osgi.framework.BundleActivator act =
						((org.osgi.framework.BundleActivator) bundleExport.loadClass(NL_UTWENTE_CE_IMAGEEXPORT_CORE_IMAGEEXPORTPLUGIN).newInstance());
					act.start(InternalPlatform.getDefault().getBundleContext());

					final Class<?> cl = bundleExportSVG.loadClass("nl.utwente.ce.imagexport.export.svg.ExportSVG");
					final Object exportSVGObject = cl.newInstance();

					final Method provideSettings = cl.getMethod(PROVIDESETTINGS, String.class, org.eclipse.swt.widgets.Composite.class, IPreferenceStore.class);
					provideSettings.invoke(exportSVGObject, "SVG", viewer.getControl(), FMUIPlugin.getDefault().getPreferenceStore());

					final Method exportImage = cl.getMethod("exportImage", String.class, String.class, IFigure.class);
					exportImage.invoke(exportSVGObject, "SVG", file.getAbsolutePath(), rootFigure);

					final Field disableClippingButton = cl.getDeclaredField(DISABLECLIPPINGBUTTON);
					disableClippingButton.setAccessible(true);

					final Object disableClippingButtonObj = disableClippingButton.get(exportSVGObject);
					if (disableClippingButtonObj instanceof Button) {
						((Button) disableClippingButtonObj).dispose();
					}

					succ = true;
				} catch (final Exception e) {
					FMUIPlugin.getDefault().logError(e);
				}
			} else {
				final String infoMessage = ECLIPSE_PLUGIN_FOR_EXPORTING_DIAGRAM_IN_SVG_FORMAT_IS_NOT_EXISTING_
					+ "\nIf you want to use this, you have to install GEF Imageexport with SVG in Eclipse from "
					+ "\nhttp://veger.github.com/eclipse-gef-imageexport";

				final MessageDialog dialog = new MessageDialog(new Shell(), SVG_EXPORT_FAILED, FMUIPlugin.getImage("FeatureIconSmall.ico"), infoMessage,
						MessageDialog.INFORMATION, new String[] { IDialogConstants.OK_LABEL }, 0);

				dialog.open();
				FMUIPlugin.getDefault().logInfo(infoMessage);
				return false;
			}
		} else {
			GEFImageWriter.writeToFile(viewer, file);
			succ = true;
		}

		GraphicsExporter.printExportMessage(file, succ);

		return succ;
	}

	public static void printExportMessage(File file, boolean successful) {
		final boolean done = successful && (file != null);
		final String infoMessage = done ? "Graphic export has been saved to\n" + file.getAbsolutePath() : NOTHING_HAS_BEEN_SAVED_FOR_DIAGRAM_EXPORT___;
		FMUIPlugin.getDefault().logInfo(infoMessage);
	}
}
