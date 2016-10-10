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

import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;

/**
 * TODO description
 * 
 * @author gruppe40
 */
public class CustomTreeColumnStyle {
	private String title;
	private int width;
	private int x, y;
	private Color backgroundColor, foregroundColor;
	private int verticalAlignment, horizontalAlignment;
	
	public CustomTreeColumnStyle(String title, int width) {
		x = y = 0;
		this.title = title;
		this.width = width;
		backgroundColor = foregroundColor = null;
		verticalAlignment = SWT.TOP;
		horizontalAlignment = SWT.CENTER;
	}
	
	public int getX() {
		return this.x;
	}
	
	public int getY() {
		return this.y;
	}
	
	public void setLocation(int x, int y) {
		this.x = x;
		this.y = y;
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
