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

import static de.ovgu.featureide.fm.core.localization.StringTable.DISABLECLIPPINGBUTTON;
import static de.ovgu.featureide.fm.core.localization.StringTable.ECLIPSE_PLUGIN_FOR_EXPORTING_DIAGRAM_IN_SVG_FORMAT_IS_NOT_EXISTING_;
import static de.ovgu.featureide.fm.core.localization.StringTable.NL_UTWENTE_CE_IMAGEEXPORT;
import static de.ovgu.featureide.fm.core.localization.StringTable.NL_UTWENTE_CE_IMAGEEXPORT_CORE_IMAGEEXPORTPLUGIN;
import static de.ovgu.featureide.fm.core.localization.StringTable.PROVIDESETTINGS;
import static de.ovgu.featureide.fm.core.localization.StringTable.SVG_EXPORT_FAILED;

import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.file.Path;

import org.eclipse.core.internal.runtime.InternalPlatform;
import org.eclipse.draw2d.IFigure;
import org.eclipse.gef.editparts.LayerManager;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Shell;
import org.osgi.framework.Bundle;

public class FMSvgExporter implements ExportType<GraphicalViewerImpl> {

	@Override
	public String getFileExtension() {
		return "svg";
	}

	@Override
	public String getDescription() {
		return "Scalable Vector Graphics";
	}

	@Override
	public void export(Path path, GraphicalViewerImpl viewer) throws IOException {
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
				exportImage.invoke(exportSVGObject, "SVG", path, rootFigure);

				final Field disableClippingButton = cl.getDeclaredField(DISABLECLIPPINGBUTTON);
				disableClippingButton.setAccessible(true);

				final Object disableClippingButtonObj = disableClippingButton.get(exportSVGObject);
				if (disableClippingButtonObj instanceof Button) {
					((Button) disableClippingButtonObj).dispose();
				}
			} catch (final Exception e) {
				throw new IOException(e);
			}
		} else {
			final String infoMessage = ECLIPSE_PLUGIN_FOR_EXPORTING_DIAGRAM_IN_SVG_FORMAT_IS_NOT_EXISTING_
				+ "\nIf you want to use this, you have to install GEF Imageexport with SVG in Eclipse from "
				+ "\nhttp://veger.github.com/eclipse-gef-imageexport";

			final MessageDialog dialog = new MessageDialog(new Shell(), SVG_EXPORT_FAILED, FMUIPlugin.getImage("FeatureIconSmall.ico"), infoMessage,
					MessageDialog.INFORMATION, new String[] { IDialogConstants.OK_LABEL }, 0);

			dialog.open();
			FMUIPlugin.getDefault().logInfo(infoMessage);
		}
	}

}
