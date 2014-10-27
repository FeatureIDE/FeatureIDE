/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui;

import java.io.File;
import java.lang.reflect.Method;

import org.eclipse.core.internal.runtime.InternalPlatform;
import org.eclipse.draw2d.IFigure;
import org.eclipse.gef.editparts.LayerManager;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.osgi.framework.Bundle;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.IFeatureModelWriter;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslWriter;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GEFImageWriter;

/**
 * This class is responsible for exporting graphics (FeatureModel and
 * CollaborationDiagram)
 * 
 * @author Guenter Ulreich
 */
@SuppressWarnings("restriction")
public class GraphicsExporter {

	public static boolean exportAs(FeatureModel featureModel, FeatureDiagramEditor diagramEditor, IFeatureModelWriter featureModelWriter) {
		boolean succ = false;
		File file = null;
		FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
		String[] extensions = { "*.png", "*.jpg", "*.bmp", "*.m", "*.xml", "*.svg" };
		fileDialog.setFilterExtensions(extensions);
		String[] filterNames = { "Portable Network Graphics *.png", "JPEG *.jpg", "Windows Bitmap *.bmp", "GUIDSL Grammar *.m", "XML Export *.xml", "Scalable Vector Graphics *.svg" };
		fileDialog.setFilterNames(filterNames);
		fileDialog.setOverwrite(true);
		String filePath = fileDialog.open();
		if (filePath == null)
			return false;

		file = new File(filePath);
		if (filePath.endsWith(".m")) {
			new GuidslWriter(featureModel).writeToFile(file);
			succ = true;
		} else if (filePath.endsWith(".xml")) {
			featureModelWriter.writeToFile(file);
			succ = true;
		} else {
			return GraphicsExporter.exportAs(diagramEditor, file);
		}

		GraphicsExporter.printExportMessage(file, succ);

		return succ;
	}

	public static boolean exportAs(GraphicalViewerImpl viewer) {
		FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
		String[] extensions = { "*.png", "*.jpg", "*.bmp", "*.svg" };
		fileDialog.setFilterExtensions(extensions);
		String[] filterNames = { "Portable Network Graphics *.png", "JPEG *.jpg", "Windows Bitmap *.bmp", "Scalable Vector Graphics *.svg" };
		fileDialog.setFilterNames(filterNames);
		fileDialog.setOverwrite(true);
		String filePath = fileDialog.open();
		if (filePath == null)
			return false;
		File file = new File(filePath);

		return GraphicsExporter.exportAs(viewer, file);
	}

	public static boolean exportAs(GraphicalViewerImpl viewer, File file) {
		boolean succ = false;

		if (file.getAbsolutePath().endsWith(".svg")) {
			ScalableFreeformRootEditPart part = (ScalableFreeformRootEditPart) viewer.getEditPartRegistry().get(LayerManager.ID);
			IFigure rootFigure = part.getFigure();
			Bundle bundleExportSVG = null;
			for (Bundle b : InternalPlatform.getDefault().getBundleContext().getBundles()) {
				if (b.getSymbolicName().equals("nl.utwente.ce.imageexport.svg")) {
					bundleExportSVG = b;
					break;
				}
			}

			// check if gef-imageexport is existing and activated!
			if (bundleExportSVG != null) {
				try {
					org.osgi.framework.BundleActivator act = ((org.osgi.framework.BundleActivator) bundleExportSVG.loadClass("nl.utwente.ce.imagexport.export.svg.Activator").newInstance());
					act.start(InternalPlatform.getDefault().getBundleContext());

					Class<?> cl = bundleExportSVG.loadClass("nl.utwente.ce.imagexport.export.svg.ExportSVG");
					Method m = cl.getMethod("exportImage", String.class, String.class, IFigure.class);
					m.invoke(cl.newInstance(), "SVG", file.getAbsolutePath(), rootFigure);
					succ = true;
				} catch (Exception e) {
					FMUIPlugin.getDefault().logError(e);
				}
			} else {
				final String infoMessage = "Eclipse plugin for exporting diagram in SVG format is not existing." + "\nIf you want to use this, you have to install GEF Imageexport with SVG in Eclipse from "
						+ "\nhttp://veger.github.com/eclipse-gef-imageexport";

				MessageDialog dialog = new MessageDialog(new Shell(), "SVG export failed", FMUIPlugin.getImage("FeatureIconSmall.ico"), infoMessage, MessageDialog.INFORMATION, new String[] { IDialogConstants.OK_LABEL }, 0);

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
		boolean done = successful && file != null;
		String infoMessage = done ? "Graphic export has been saved to\n" + file.getAbsolutePath() : "Nothing has been saved for diagram export...";
		FMUIPlugin.getDefault().logInfo(infoMessage);
	}
}
