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
package de.ovgu.featureide.fm.ui.views.attributes;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * TODO ATTRIBUTE description
 *
 * @author Joshua Sprey
 */
public class FeatureAttributeView extends ViewPart {
	private Label label;

	public FeatureAttributeView() {
		super();
	}

	@Override
	public void init(IViewSite site) throws PartInitException {
		FMUIPlugin.getDefault().logInfo("init" + site.getPage().getLabel());
		super.init(site);
	}

	@Override
	public void createPartControl(Composite parent) {
		FMUIPlugin.getDefault().logInfo("createPartControl");
		label = new Label(parent, 0);
		label.setText("Hello World");
	}

	@Override
	public void setFocus() {
		label.setFocus();
	}
}
