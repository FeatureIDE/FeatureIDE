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
package de.ovgu.featureide.fm.ui.editors;

import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;

/**
 * Class to add the profilemenu to the contextmenu of the project (projectonly)
 *
 * @author Jonas Weigt
 * @author Christian Harnisch
 * @author Marcus Pinnecke
 */

public class ToolBarMenuManager extends MenuManager {

	private Image image;

	public ToolBarMenuManager(String text) {
		super(text);
	}

	public ToolBarMenuManager(String text, ImageDescriptor image, String id) {
		super(text, image, id);
		this.image = image.createImage();
	}

	@Override
	public void fill(final ToolBar toolbar, int index) {
		final ToolItem toolItem = (index >= 0) ? new ToolItem(toolbar, SWT.DROP_DOWN, index) : new ToolItem(toolbar, SWT.DROP_DOWN);
		toolItem.setText(getMenuText());
		toolItem.setImage(image);
		toolItem.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				final Menu menu = ToolBarMenuManager.this.createContextMenu(toolbar);
				final Rectangle bounds = toolItem.getBounds();
				final Point point = toolbar.toDisplay(bounds.x, bounds.y + bounds.height);
				menu.setLocation(point);
				menu.setVisible(true);
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
	}

}
