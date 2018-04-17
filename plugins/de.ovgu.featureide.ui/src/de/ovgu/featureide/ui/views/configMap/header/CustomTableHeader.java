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
package de.ovgu.featureide.ui.views.configMap.header;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
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
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 */
public class CustomTableHeader extends Canvas implements PaintListener, MouseListener, ISelectionProvider {

	private List<CustomColumnStyle> columnStyles;
	private Transform transform;
	private final Parallelogram hitbox;
	private Color highlightColor;

	private float globalRotation;
	private int height;

	private int selectedColumn;
	private final List<ICustomTableHeaderSelectionListener> listeners;

	private boolean drawLines;

	public CustomTableHeader(Composite parent, int style) {
		this(parent, style, null);
	}

	public CustomTableHeader(Composite parent, int style, List<CustomColumnStyle> columnStyles) {
		super(parent, style);
		hitbox = new Parallelogram(0, 0, 0);
		listeners = new ArrayList<>(1);
		setSelectedColumn(-1);
		setColumnStyles(columnStyles);
		addPaintListener(this);
		addMouseListener(this);
	}

	public void addColumnSelectionListener(ICustomTableHeaderSelectionListener listener) {
		listeners.add(listener);
	}

	public void removeColumnSelectionListener(ICustomTableHeaderSelectionListener listener) {
		listeners.remove(listener);
	}

	/**
	 * @return the highlightColor
	 */
	public Color getHighlightColor() {
		return highlightColor;
	}

	/**
	 * @param highlightColor the highlightColor to set
	 */
	public void setHighlightColor(Color highlightColor) {
		this.highlightColor = highlightColor;
	}

	public boolean areLinesVisible() {
		return drawLines;
	}

	/**
	 * @param drawLines the drawLines to set
	 */
	public void setLinesVisible(boolean drawLines) {
		this.drawLines = drawLines;
	}

	public void setSelectedColumn(int index) {
		if ((0 <= index) && (index < columnStyles.size())) {
			if (!columnStyles.get(index).isSelectable()) {
				index = -1;
			}
		}
		selectedColumn = index;
		redraw();
		for (final ICustomTableHeaderSelectionListener listener : listeners) {
			listener.onColumnSelectionChanged(index);
		}
	}

	public void setColumnStyles(List<CustomColumnStyle> columnStyles) {
		this.columnStyles = columnStyles;
		setSelectedColumn(-1);
		updateHeight();
		redraw();
	}

	public float getGlobalRotation() {
		return globalRotation;
	}

	public void setGlobalRotation(float rotation) {
		globalRotation = rotation;
		updateHeight();
	}

	private void setHeight(int height) {
		this.height = height;
		hitbox.setHeight(this.height);
		hitbox.setSkew(calculateSkew(globalRotation, this.height));
	}

	public int getHeight() {
		return height;
	}

	private void updateHeight() {
		int textWidth = 0;
		int textHeight = 0;

		if (columnStyles != null) {
			final GC gc = new GC(this);

			for (final CustomColumnStyle style : columnStyles) {
				final String text = style.getTitle();

				final Point estimatedSize = gc.stringExtent(text);
				if (estimatedSize.x > textWidth) {
					textWidth = estimatedSize.x;
				}
				if (estimatedSize.y > textHeight) {
					textHeight = estimatedSize.y;
				}
			}
		}

		setHeight((int) Math.abs((textWidth * Math.sin(globalRotation)) + (textHeight * Math.tan((Math.PI / 2.0) - globalRotation))));
	}

	private float calculateSkew(float rotation, float height) {
		return (float) (height / Math.tan(-globalRotation));
	}

	private double getFloatingHeight(int fontHeight, double rotation) {
		final double sin = Math.sin((0.5 * Math.PI) - rotation);
		return Math.min(fontHeight, fontHeight - (fontHeight * sin));
	}

	private void updateSelection(float ex, float ey) {
		int offset = 0, index = 0, selectedIndex = -1;
		for (final CustomColumnStyle col : columnStyles) {
			if (col.isSelectable()) {
				hitbox.setWidth(col.getWidth());
				hitbox.setLocation(offset, 0);
				if (hitbox.containsPoint(ex, height - ey)) {
					selectedIndex = index;
					break;
				}
			}

			offset += col.getWidth();
			index++;
		}

		setSelectedColumn(selectedIndex);

		redraw();
	}

	@Override
	public void mouseDoubleClick(MouseEvent e) {
		updateSelection(e.x, e.y);
		if (selectedColumn >= 0) {
			for (final ICustomTableHeaderSelectionListener listener : listeners) {
				listener.onColumnDoubleClicked();
			}
		}
	}

	@Override
	public void mouseDown(MouseEvent e) {
		updateSelection(e.x, e.y);
	}

	@Override
	public void mouseUp(MouseEvent e) {

	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.swt.events.PaintListener#paintControl(org.eclipse.swt.events.PaintEvent)
	 */
	@Override
	public void paintControl(PaintEvent e) {
		if ((columnStyles != null) && !columnStyles.isEmpty()) {
			final Display display = getDisplay();
			final GC gc = e.gc;

			if (transform == null) {
				transform = new Transform(display);
			}

			gc.setAdvanced(true);
			if (!gc.getAdvanced()) {
				gc.drawText("Advanced graphics not supported", 0, 0, true);
				return;
			}

			gc.setFont(display.getSystemFont());

			int columnOffset = 0;
			final int[] backgroundCorners = new int[8];

			// y values
			backgroundCorners[1] = height;
			backgroundCorners[3] = 0;
			backgroundCorners[5] = 0;
			backgroundCorners[7] = height;

			int index = 0;
			for (final CustomColumnStyle col : columnStyles) {
				int dx = 0;
				int dy = 0;
				final int hAlignment = col.getHorizontalAlignment();
				final int vAlignment = col.getVerticalAlignment();

				final int fontHeight = gc.getFontMetrics().getHeight();
				final int width = col.getWidth();
				final int skew = (int) hitbox.getSkew();

				// BACKGROUND
				final Color fgrnd = col.getForeground();
				final Color bgrnd = index == selectedColumn ? highlightColor : col.getBackground();

				if (fgrnd != null) {
					gc.setForeground(fgrnd);
				}
				if (bgrnd != null) {
					gc.setBackground(bgrnd);

					// draw background
					transform.identity();
					gc.setTransform(transform);
					backgroundCorners[0] = columnOffset;
					backgroundCorners[2] = columnOffset + skew;
					backgroundCorners[4] = columnOffset + width + skew;
					backgroundCorners[6] = columnOffset + width;
					gc.fillPolygon(backgroundCorners);
				}

				// ALIGNMENTS
				if (hAlignment == SWT.CENTER) {
					final float projectedHeight = (float) (fontHeight * Math.cos((0.5 * Math.PI) - globalRotation));
					dx = (int) ((col.getWidth() + projectedHeight) / 2f);
				}

				if ((vAlignment & (SWT.CENTER | SWT.BOTTOM)) != 0) {
					dy = height - fontHeight;
					if (col.isRotated()) {
						dy += (int) getFloatingHeight(fontHeight, globalRotation);
					}

					if (vAlignment == SWT.CENTER) {
						dy /= 2;
					}
				}

				// ROTATION
				float cos = 1;
				float sin = 0;

				if (col.isRotated()) {
					cos = (float) Math.cos(globalRotation);
					sin = (float) Math.sin(globalRotation);
				}

				transform.setElements(cos, sin, -sin, cos, columnOffset + dx, dy);
				gc.setTransform(transform);

				// RENDERING
				gc.drawText(col.getTitle(), 0, 0);

				columnOffset += width;

				// draw line
				if (drawLines && col.isDrawingLine()) {
					transform.identity();
					gc.setTransform(transform);
					gc.drawLine(columnOffset, height, columnOffset + skew, 0);
				}

				index++;
			}
		}
	}

	public static double toRadians(double degrees) {
		return (Math.PI * degrees) / 180.0;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ISelectionProvider#addSelectionChangedListener(org.eclipse.jface.viewers.ISelectionChangedListener)
	 */
	@Override
	public void addSelectionChangedListener(ISelectionChangedListener listener) {}

	@Override
	public ISelection getSelection() {
		return new StructuredSelection(selectedColumn);
	}

	@Override
	public void removeSelectionChangedListener(ISelectionChangedListener listener) {}

	@Override
	public void setSelection(ISelection selection) {}
}
