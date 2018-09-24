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
package de.ovgu.featureide.fm.ui.views.constraintview;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.utils.FeatureModelUtil;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintView;

/**
 * TODO description
 *
 * @author "Rosiak Kamil"
 * @author "Domenik Eichhorn"
 */
public class ConstraintViewController extends ViewPart implements IEventListener {
	public ConstraintViewController() {}

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.ConstraintView";

	private ConstraintView viewer;

	@Override
	public void createPartControl(Composite parent) {
		parent.setLayout(new FillLayout(SWT.HORIZONTAL));
		viewer = new ConstraintView(parent);
		final IFeatureModel currentModel = FeatureModelUtil.getFeatureModel();

		if (currentModel != null) {
			for (final IConstraint constraint : currentModel.getConstraints()) {
				viewer.addItem(constraint);

			}
		}
	}

	@Override
	public void setFocus() {}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		System.out.println(event.getEventType());
		switch (event.getEventType()) {
		case MODEL_DATA_LOADED:
		case MODEL_DATA_SAVED:
			System.out.println("model data loaded event triggered");
			break;

		default:
			break;
		}

	}

}
