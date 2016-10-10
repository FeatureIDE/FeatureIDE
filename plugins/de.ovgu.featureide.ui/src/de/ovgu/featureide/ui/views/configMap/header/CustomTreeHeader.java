/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.views.configMap.header;

import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.PaintEvent;
import org.eclipse.swt.events.PaintListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Transform;
import org.eclipse.swt.widgets.Canvas;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;

/**
 * TODO description
 * 
 * @author gruppe40
 */
public class CustomTreeHeader extends Canvas implements PaintListener {
	private List<CustomTreeColumnStyle> columnStyles;
	private Transform transform;
	private boolean drawLines;

	private float globalRotation;

	public CustomTreeHeader(Composite parent, int style) {
		this(parent, style, null);
	}

	public CustomTreeHeader(Composite parent, int style, List<CustomTreeColumnStyle> columnStyles) {
		super(parent, style);
		setColumnStyles(columnStyles);
		addPaintListener(this);
	}

	public void setColumnStyles(List<CustomTreeColumnStyle> columnStyles) {
		this.columnStyles = columnStyles;
	}

	public float getGlobalRotation() {
		return this.globalRotation;
	}

	public void setGlobalRotation(float rotation) {
		this.globalRotation = rotation;
	}

	/**
	 * @return the drawLines
	 */
	public boolean areLinesVisible() {
		return drawLines;
	}

	/**
	 * @param drawLines the drawLines to set
	 */
	public void setLinesVisible(boolean drawLines) {
		this.drawLines = drawLines;
	}

	public int calculateFittingHeight() {
		int textWidth = 0;
		int textHeight = 0;
		GC gc = new GC(this);

		for (CustomTreeColumnStyle style : this.columnStyles) {
			String text = style.getTitle();

			Point estimatedSize = gc.stringExtent(text);
			if (estimatedSize.x > textWidth)
				textWidth = estimatedSize.x;
			if (estimatedSize.y > textHeight)
				textHeight = estimatedSize.y;
		}

		return (int) Math.abs(textWidth * Math.sin(globalRotation) + textHeight * Math.tan(Math.PI / 2.0 - globalRotation));
	}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.PaintListener#paintControl(org.eclipse.swt.events.PaintEvent)
	 */
	@Override
	public void paintControl(PaintEvent e) {
		if (columnStyles != null && !columnStyles.isEmpty()) {
			Display display = getDisplay();
			GC gc = e.gc;

			if (transform == null)
				this.transform = new Transform(display);

			gc.setAdvanced(true);
			if (!gc.getAdvanced()) {
				gc.drawText("Advanced graphics not supported", 0, 0, true);
				return;
			}

			//gc.setTransform(transform);
			gc.setFont(display.getSystemFont());

			int columnOffset = 0;
			int colIndex = 0;
			for (CustomTreeColumnStyle col : columnStyles) {
				int dx = 0;
				int dy = 0;
				int vAlignment = col.getVerticalAlignment();
				int hAlignment = col.getHorizontalAlignment();
				
				int height = getBounds().height;
				int fontHeight = gc.getFontMetrics().getHeight();
				int width = col.getWidth();
				
				float cos = (float) Math.cos(globalRotation);
				float sin = (float) Math.sin(globalRotation);
				int lineDx = (int) ((double) height / Math.tan(-globalRotation));

				Color fgrnd = col.getForeground();
				Color bgrnd = col.getBackground();
				if (fgrnd != null)
					gc.setForeground(fgrnd);
				if (bgrnd != null) {
					gc.setBackground(bgrnd);
					
					// draw background
					this.transform.identity();
					gc.setTransform(transform);
					int[] backgroundCorners = {
							columnOffset, height,
							columnOffset + (colIndex == 0 ? 0 : lineDx), 0,
							columnOffset + width + lineDx, 0,
							columnOffset + width, height
					};
					gc.fillPolygon(backgroundCorners);
				}

				if (vAlignment == SWT.BOTTOM) {
					dy = height - fontHeight + (int) getFloatingHeight(fontHeight, globalRotation);
				}

				if (hAlignment == SWT.CENTER) {
					float projectedHeight = (float) (fontHeight * Math.cos(0.5 * Math.PI - globalRotation));
					dx = (int) ((col.getWidth() + projectedHeight) / 2f);
				}

				this.transform.setElements(cos, sin, -sin, cos, columnOffset + col.getX() + dx, col.getY() + dy);
				gc.setTransform(transform);
				gc.drawText(col.getTitle(), 0, 0);

				columnOffset += width;
				
				//draw line
				if (drawLines) {
					this.transform.identity();
					gc.setTransform(transform);
					gc.drawLine(columnOffset, height, columnOffset + lineDx, 0);
				}
				
				colIndex++;
			}
		}
	}

	private double getFloatingHeight(int fontHeight, double rotation) {
		double sin = Math.sin(0.5 * Math.PI - rotation);
		return Math.min(fontHeight, fontHeight - fontHeight * sin);
	}

	public static double toRadians(double degrees) {
		return (Math.PI * degrees) / 180.0;
	}
}
