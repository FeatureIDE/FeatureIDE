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

import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;

/**
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 */
public class CustomColumnStyle {
	private String title;
	private int width;
	private Color backgroundColor, foregroundColor;
	private int verticalAlignment, horizontalAlignment;
	private boolean isRotated, isSelectable;
	private boolean drawLine;

	public CustomColumnStyle(String title, int width) {
		this.title = title;
		this.width = width;
		this.backgroundColor = this.foregroundColor = null;
		this.verticalAlignment = SWT.TOP;
		this.horizontalAlignment = SWT.CENTER;
		this.isRotated = true;
		this.isSelectable = true;
		this.drawLine = true;
	}

	public int getWidth() {
		return this.width;
	}

	public void setWidth(int width) {
		this.width = width;
	}

	public void setVerticalAlignment(int alignment) {
		this.verticalAlignment = alignment;
	}

	public int getVerticalAlignment() {
		return this.verticalAlignment;
	}

	public void setHorizontalAlignment(int alignment) {
		this.horizontalAlignment = alignment;
	}

	public int getHorizontalAlignment() {
		return this.horizontalAlignment;
	}

	public void setRotated(boolean isRotated) {
		this.isRotated = isRotated;
	}

	public boolean isRotated() {
		return isRotated;
	}

	public void setSelectable(boolean isSelectable) {
		this.isSelectable = isSelectable;
	}

	public boolean isSelectable() {
		return isSelectable;
	}
	
	public void setDrawingLine(boolean drawLine) {
		this.drawLine = drawLine;
	}
	
	public boolean isDrawingLine() {
		return drawLine;
	}

	public String getTitle() {
		return this.title;
	}

	public void setTitle(String title) {
		this.title = title;
	}

	public Color getForeground() {
		return this.foregroundColor;
	}

	public void setForeground(Color foregroundColor) {
		this.foregroundColor = foregroundColor;
	}

	public Color getBackground() {
		return this.backgroundColor;
	}

	public void setBackground(Color backgroundColor) {
		this.backgroundColor = backgroundColor;
	}
}
