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
package de.ovgu.featureide.ui.views.collaboration.figures;

import org.eclipse.draw2d.Label;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.core.fstmodel.RoleElement;

/**
 * Label for RoleFigures
 *
 * @author Steffen Schulze
 * @author Christian Lausberger
 */
public class RoleFigureLabel extends Label {

	private final String elementName;
	private RoleElement<?> roleElement;

	public RoleFigureLabel(String text, Image image, String elementName, RoleElement<?> element) {
		this(text, image, elementName);
		roleElement = element;
	}

	public RoleFigureLabel(String text, Image image, String elementName) {
		super(text, image);
		this.elementName = elementName;
	}

	public RoleFigureLabel(String text, String elementName) {
		super(text);
		this.elementName = elementName;
	}

	public String getElementName() {
		return elementName;
	}

	@Override
	public String toString() {
		return elementName;
	}

	public RoleElement<?> getRoleElement() {
		return roleElement;
	}
}
