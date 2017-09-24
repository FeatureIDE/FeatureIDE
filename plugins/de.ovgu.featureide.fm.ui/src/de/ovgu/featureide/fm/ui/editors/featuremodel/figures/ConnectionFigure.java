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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.PolylineConnection;
import org.eclipse.swt.SWT;

import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * A figure for connections.
 *
 * @author Timo G&uuml;nther
 */
public class ConnectionFigure extends PolylineConnection {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param external whether the connection connects two external features
	 */
	public ConnectionFigure(boolean external) {
		setForegroundColor(FMPropertyManager.getConnectionForegroundColor());
		if (external) {
			setLineStyle(SWT.LINE_DASH);
		}
	}

	@Override
	public CircleDecoration getSourceDecoration() {
		return (CircleDecoration) super.getSourceDecoration();
	}

	@Override
	public RelationDecoration getTargetDecoration() {
		return (RelationDecoration) super.getTargetDecoration();
	}
}
