/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming;

import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.tools.CellEditorLocator;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.swt.widgets.Control;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.FeatureFigure;


/**
 * Locates the cell editor to rename features.
 * 
 * @author Thomas Thuem
 */
public class FeatureCellEditorLocator implements CellEditorLocator, GUIDefaults {

	private FeatureFigure figure;

	public FeatureCellEditorLocator(FeatureFigure figure) {
		this.figure = figure;
	}

	public void relocate(CellEditor celleditor) {
		Control control = celleditor.getControl();

		Rectangle labelBounds = figure.getLabelBounds();
		Rectangle bounds = labelBounds.getCopy();
		figure.translateToAbsolute(bounds);
		
		bounds.width = Math.max(bounds.width, CELL_EDITOR_MINSIZE.width);
		bounds.width += CELL_EDITOR_INSETS.getWidth();
		bounds.x += (labelBounds.width - bounds.width) / 2;

		bounds.height = Math.max(bounds.height, CELL_EDITOR_MINSIZE.height);
		bounds.height += CELL_EDITOR_INSETS.getHeight();
		bounds.y += (labelBounds.height - bounds.height) / 2;
		
		control.setBounds(bounds.x, bounds.y, bounds.width, bounds.height);
	}

}
