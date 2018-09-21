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
import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.utils.FeatureModelUtil;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintView;

/**
 * TODO This class represents the controller (MVC) of the constraint view it creates all GUI elements and holds the logic that operates on the view.
 *
 * @author "Rosiak Kamil"
 * @author "Domenik Eichhorn"
 * @author "Rahel Arens"
 * @author "Thomas Graave"
 */
public class ConstraintViewController extends ViewPart implements IEventListener {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.constraintView";

	private ConstraintView viewer;
	private FeatureModelManager fmManager;
	private IFeatureModel currentModel;

	private final ConstraintViewController viewController = this;

	private IFeatureModel featuremodel;
	private IGraphicalFeatureModel graph_model;

	boolean constraintsHidden = true;

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
		parent.setLayout(new FillLayout(SWT.HORIZONTAL));
		viewer = new ConstraintView(parent);
		getSite().getPage().addPartListener(constraintListener);

		currentModel = FeatureModelUtil.getFeatureModel();

		refreshView(currentModel);
	}

	/**
	 * this method first clears the table and then adds all current existing constraints.
	 *
	 * @param FeatureModel that contains the constraints
	 */
	public void refreshView(IFeatureModel currentModel) {
		fmManager = FeatureModelManager.getInstance(currentModel.getSourceFile());
		this.currentModel = currentModel;
		addEventListener(this);
		viewer.getViewer().refresh();
		if (currentModel != null) {
			for (final IConstraint constraint : currentModel.getConstraints()) {
				viewer.addItem(constraint);
			}
		}
		viewer.colorTable();
	}

	private final IPartListener2 constraintListener = new IPartListener2() {

		@Override
		public void partActivated(IWorkbenchPartReference part) {
			// React to ModelView
			if (part.getId().equals(FeatureModelEditor.ID)) {

				refreshView(((FeatureModelEditor) part.getPart(false)).getFeatureModel());
			}
			// Show/Hide Constraint List
			if (part.getPart(false) instanceof IEditorPart) {
				setConstraintsHidden(constraintsHidden);
			}
		}

		@Override
		public void partBroughtToTop(IWorkbenchPartReference part) {
			// React to ModelView
			if (part.getId().equals(FeatureModelEditor.ID)) {
				refreshView(((FeatureModelEditor) part.getPart(false)).getFeatureModel());
			}
		}

		@Override
		public void partClosed(IWorkbenchPartReference part) {
			// React to ModelView
			if (part instanceof FeatureModelEditor) {
				FeatureModelUtil.getActiveFMEditor();
				if ((FeatureModelEditor.ID.equals(part.getId())) || (FeatureModelUtil.getActiveFMEditor() == null)) {
					viewer.getViewer().refresh();
				}
			}
		}

		@Override
		public void partDeactivated(IWorkbenchPartReference partRef) {
			// TODO Auto-generated method stub

		}

		@Override
		public void partOpened(IWorkbenchPartReference part) {
			if (part.getId().equals(ID)) {
				setConstraintsHidden(true);
			}
		}

		@Override
		public void partHidden(IWorkbenchPartReference part) {
			if (part.getId().equals(ID)) {
				setConstraintsHidden(false);
			}
		}

		@Override
		public void partVisible(IWorkbenchPartReference part) {
			if (part.getId().equals(ID)) {
				setConstraintsHidden(true);
			}
		}

		@Override
		public void partInputChanged(IWorkbenchPartReference partRef) {
			// TODO Auto-generated method stub

		}

	};

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus() viewController.getViewSite().getWorkbenchWindow().getActivePage() == viewController
	 */
	@Override
	public void setFocus() {
		// TODO Auto-generated method stub

	}

	public void setConstraintsHidden(boolean hideConstraints) {
		FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().setConstraintsHidden(hideConstraints);
		FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().redrawDiagram();
		constraintsHidden = hideConstraints;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.base.event.IEventListener#propertyChange(de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent)
	 */
	public void addEventListener(IEventListener listener) {
		if (fmManager == null) {
			return;
		}
		fmManager.addListener(listener);
	}

	public void removeEventListener(IEventListener listener) {
		if (fmManager == null) {
			return;
		}
		fmManager.removeListener(listener);
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		// TODO: make refreshView in switch case
		refreshView(currentModel);
	}

}
