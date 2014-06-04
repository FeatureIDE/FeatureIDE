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
package de.ovgu.featureide.fm.ui.editors.featuremodel;

import java.io.File;
import java.util.Locale;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.SWTGraphics;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.GraphicalViewer;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.editparts.LayerManager;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.ImageLoader;
import org.eclipse.ui.progress.UIJob;

/**
 * Saves the figures of an GEF editor into a bitmap file.
 * 
 * @author Thomas Thuem
 */
public class GEFImageWriter {

	public static void writeToFile(final GraphicalViewerImpl graphicalViewer,
			final File file) {
		UIJob job = new UIJob("Save image") {
			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				saveEditorContentsAsImage(graphicalViewer, file.toString());
				return Status.OK_STATUS;
			}
		};
		job.schedule();
	}
	
	private static void saveEditorContentsAsImage(GraphicalViewer viewer,
			String saveFilePath) {
		Image image = drawFigureOnImage(viewer);
		Image croppedImage = cropImage(image);
		image.dispose();
		saveImage(croppedImage, saveFilePath);
		croppedImage.dispose();
	}

	private static Image drawFigureOnImage(GraphicalViewer viewer) {
		IFigure figure = getRootFigure(viewer); 
		Rectangle bounds = figure.getBounds();
		
		Image image = new Image(null, bounds.width, bounds.height);
		GC imageGC = new GC(image);
		Graphics imgGraphics = new SWTGraphics(imageGC);
		
		imgGraphics.translate(-bounds.x, -bounds.y);
		figure.paint(imgGraphics);
		imgGraphics.translate(bounds.x, bounds.y);
		
		imageGC.dispose();
		return image;
	}

	private static Image cropImage(Image image) {
		int border = 5;
		Rectangle r = calculateUsedRectangle(image);
		
		Image img2 = new Image(null, r.width + 2 * border, r.height + 2 * border);
		GC imageGC2 = new GC(img2);
		Graphics imgGraphics2 = new SWTGraphics(imageGC2);
		
		imgGraphics2.drawImage(image, r, new Rectangle(border, border, r.width, r.height));
		return img2;
	}

	private static void saveImage(Image image, String saveFilePath) {
		int format = readFormatFromFileName(saveFilePath);

		ImageData[] data = new ImageData[1];
		data[0] = image.getImageData();

		ImageLoader loader = new ImageLoader();
		loader.data = data;
		loader.save(saveFilePath, format);
	}

	private static IFigure getRootFigure(GraphicalViewer viewer) {
		ScalableFreeformRootEditPart rootEditPart = (ScalableFreeformRootEditPart) viewer
				.getEditPartRegistry().get(LayerManager.ID);
		return ((LayerManager) rootEditPart)
				.getLayer(LayerConstants.PRINTABLE_LAYERS);
	}

	private static Rectangle calculateUsedRectangle(Image image) {
		ImageData data = image.getImageData();
		Rectangle r = new Rectangle();
		int bg = data.getPixel(0, 0);
		for (int x = 0; x < data.width; x++)
			for (int y = 0; y < data.height; y++)
				if (data.getPixel(x, y) != bg) {
					r.x = x;
					x = data.width;
					break;
				}
		for (int x = data.width - 1; x >= 0; x--)
			for (int y = 0; y < data.height; y++)
				if (data.getPixel(x, y) != bg) {
					r.width = x - r.x + 1;
					x = 0;
					break;
				}
		for (int y = 0; y < data.height; y++)
			for (int x = 0; x < data.width; x++)
				if (data.getPixel(x, y) != bg) {
					r.y = y;
					y = data.height;
					break;
				}
		for (int y = data.height - 1; y >= 0; y--)
			for (int x = 0; x < data.width; x++)
				if (data.getPixel(x, y) != bg) {
					r.height = y - r.y + 1;
					y = 0;
					break;
				}
		return r;
	}

	private static int readFormatFromFileName(String saveFilePath) {
		String file = saveFilePath.toLowerCase(Locale.ENGLISH);
		if (file.endsWith(".bmp"))
			return SWT.IMAGE_BMP;
		if (file.endsWith(".gif"))
			return SWT.IMAGE_GIF;
		if (file.endsWith(".ico"))
			return SWT.IMAGE_ICO;
		if (file.endsWith(".jpg"))
			return SWT.IMAGE_JPEG;
		if (file.endsWith(".jpeg"))
			return SWT.IMAGE_JPEG;
		if (file.endsWith(".png"))
			return SWT.IMAGE_PNG;
		if (file.endsWith(".tif"))
			return SWT.IMAGE_TIFF;
		throw new RuntimeException("Unknown image file format " + saveFilePath);
	}

}
