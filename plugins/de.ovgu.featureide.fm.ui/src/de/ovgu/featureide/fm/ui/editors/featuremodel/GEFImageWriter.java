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
package de.ovgu.featureide.fm.ui.editors.featuremodel;

import static de.ovgu.featureide.fm.core.localization.StringTable.UNKNOWN_IMAGE_FILE_FORMAT;

import java.io.IOException;
import java.nio.file.Path;

import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.SWTGraphics;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.GraphicalViewer;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.editparts.LayerManager;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.ImageLoader;

import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 * Saves the figures of an GEF editor into a bitmap file.
 *
 * @author Thomas Thuem
 */
public class GEFImageWriter {

	public static void saveEditorContentsAsImage(Path path, GraphicalViewer viewer) throws IOException {
		try {
			final Image image = drawFigureOnImage(viewer);
			final Image croppedImage = cropImage(image);
			image.dispose();
			saveImage(croppedImage, path);
			croppedImage.dispose();
		} catch (final Exception e) {
			throw new IOException(e);
		}
	}

	private static Image drawFigureOnImage(GraphicalViewer viewer) {
		final IFigure figure = getRootFigure(viewer);
		final Rectangle bounds = figure.getBounds();

		final Image image = new Image(null, bounds.width, bounds.height);
		final GC imageGC = new GC(image);
		final Graphics imgGraphics = new SWTGraphics(imageGC);

		imgGraphics.translate(-bounds.x, -bounds.y);
		figure.paint(imgGraphics);
		imgGraphics.translate(bounds.x, bounds.y);

		imageGC.dispose();
		return image;
	}

	private static Image cropImage(Image image) {
		final int border = 5;
		final Rectangle r = calculateUsedRectangle(image);

		final Image img2 = new Image(null, r.width + (2 * border), r.height + (2 * border));
		final GC imageGC2 = new GC(img2);
		final Graphics imgGraphics2 = new SWTGraphics(imageGC2);

		imgGraphics2.drawImage(image, r, new Rectangle(border, border, r.width, r.height));
		return img2;
	}

	private static void saveImage(Image image, Path saveFilePath) {
		final int format = readFormatFromFileName(saveFilePath);

		final ImageData[] data = new ImageData[1];
		data[0] = image.getImageData();

		final ImageLoader loader = new ImageLoader();
		loader.data = data;
		loader.save(saveFilePath.toString(), format);
	}

	private static IFigure getRootFigure(GraphicalViewer viewer) {
		final ScalableFreeformRootEditPart rootEditPart = (ScalableFreeformRootEditPart) viewer.getEditPartRegistry().get(LayerManager.ID);
		return ((LayerManager) rootEditPart).getLayer(LayerConstants.PRINTABLE_LAYERS);
	}

	private static Rectangle calculateUsedRectangle(Image image) {
		final ImageData data = image.getImageData();
		final Rectangle r = new Rectangle();
		final int bg = data.getPixel(0, 0);
		for (int x = 0; x < data.width; x++) {
			for (int y = 0; y < data.height; y++) {
				if (data.getPixel(x, y) != bg) {
					r.x = x;
					x = data.width;
					break;
				}
			}
		}
		for (int x = data.width - 1; x >= 0; x--) {
			for (int y = 0; y < data.height; y++) {
				if (data.getPixel(x, y) != bg) {
					r.width = (x - r.x) + 1;
					x = 0;
					break;
				}
			}
		}
		for (int y = 0; y < data.height; y++) {
			for (int x = 0; x < data.width; x++) {
				if (data.getPixel(x, y) != bg) {
					r.y = y;
					y = data.height;
					break;
				}
			}
		}
		for (int y = data.height - 1; y >= 0; y--) {
			for (int x = 0; x < data.width; x++) {
				if (data.getPixel(x, y) != bg) {
					r.height = (y - r.y) + 1;
					y = 0;
					break;
				}
			}
		}
		return r;
	}

	private static int readFormatFromFileName(Path saveFilePath) {
		switch (SimpleFileHandler.getFileExtension(saveFilePath).toLowerCase()) {
		case "bmp":
			return SWT.IMAGE_BMP;
		case "gif":
			return SWT.IMAGE_GIF;
		case "ico":
			return SWT.IMAGE_ICO;
		case "jpg":
			return SWT.IMAGE_JPEG;
		case "jpeg":
			return SWT.IMAGE_JPEG;
		case "png":
			return SWT.IMAGE_PNG;
		case "tif":
			return SWT.IMAGE_TIFF;
		default:
			throw new RuntimeException(UNKNOWN_IMAGE_FILE_FORMAT + saveFilePath);
		}
	}

}
