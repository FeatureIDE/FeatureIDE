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
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPart;
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
 * @author "Rahel Arens"
 * @author "Thomas Graave"
 */
public class ConstraintViewController extends ViewPart implements IEventListener {
	public ConstraintViewController() {}

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.constraintView";

	private ConstraintView viewer;

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
		parent.setLayout(new FillLayout(SWT.HORIZONTAL));
		viewer = new ConstraintView(parent);
		getSite().getPage().addPartListener(constraintListener);

		final IFeatureModel currentModel = FeatureModelUtil.getFeatureModel();

		refreshView(currentModel);
	}

	/**
	 * this method first clears the table and then adds all current existing constraints.
	 *
	 * @param FeatureModel that contains the constraints
	 */
	public void refreshView(IFeatureModel currentModel) {
		viewer.getViewer().refresh();
		if (currentModel != null) {
			for (final IConstraint constraint : currentModel.getConstraints()) {
				viewer.addItem(constraint);
			}
		}
	}

	private final IPartListener constraintListener = new IPartListener() {

		@Override
		public void partOpened(IWorkbenchPart part) {
			// React to ModelView

			// Show/Hide Constraint List
		}

		@Override
		public void partDeactivated(IWorkbenchPart part) {
			// React to ModelView
			if (part == viewer) {
				System.out.println("View ist nicht offen, yeeeah");
			}
			// Show/Hide Constraint List
		}

		@Override
		public void partClosed(IWorkbenchPart part) {
			// React to ModelView

			// Show/Hide Constraint List
		}

		@Override
		public void partBroughtToTop(IWorkbenchPart part) {
			// React to ModelView
			if (part instanceof IEditorPart) {
				System.out.println("Brought to top");
			}
			// Show/Hide Constraint List
		}

		@Override
		public void partActivated(IWorkbenchPart part) {
			// React to ModelView
			if (part instanceof IEditorPart) {
				System.out.println("View ist offen, yeeeah");
			}
			// Show/Hide Constraint List
		}

	};

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	@Override
	public void setFocus() {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.base.event.IEventListener#propertyChange(de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent)
	 */

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		System.out.println(event.getEventType());
		switch (event.getEventType()) {
		case MODEL_DATA_LOADED:
		case MODEL_DATA_SAVED:
			System.out.println("model data loaded event triggered");
			// refreshConstraints();
			break;

		default:
			break;
		}

	}

}
