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
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
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
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
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
public class ConstraintViewController extends ViewPart implements IEventListener, GUIDefaults {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.constraintView";
	private ConstraintView viewer;
	private IFeatureModel currentModel;

	boolean constraintsHidden = false;
	private String searchText = "";

	/**
	 * Standard SWT initialize called after construction.
	 */
	@Override
	public void createPartControl(Composite parent) {
		parent.setLayout(new FillLayout(SWT.HORIZONTAL));
		viewer = new ConstraintView(parent);
		viewer.getSearchBox().addModifyListener(searchListener);
		getSite().getPage().addPartListener(constraintListener);
		if (FeatureModelUtil.getActiveFMEditor() != null) {
			currentModel = FeatureModelUtil.getFeatureModel();
			refreshView(currentModel, searchText);
		}

	}

	/**
	 * reacts when searchBox noticed input and modifies the Constraint table according to the input
	 */
	private final ModifyListener searchListener = new ModifyListener() {

		@Override
		public void modifyText(ModifyEvent e) {
			searchText = viewer.getSearchBox().getText();
			refreshView(currentModel, searchText);
		}

	};

	/**
	 * this method first clears the table and then adds all constrains that contain searchInput in their DisplayName or Description also it checks for RegEx
	 * matching in searchInput
	 */
	public void refreshView(IFeatureModel currentModel, String searchInput) {
		if (currentModel != null) {
			this.currentModel = currentModel;
			this.currentModel.addListener(this);
			viewer.removeAll();
			for (final IConstraint constraint : currentModel.getConstraints()) {
				final String lazyConstraint = constraint.getDisplayName().toLowerCase();
				final String lazyDescription = constraint.getDescription().toLowerCase().replaceAll("\n", " ");
				searchInput = searchInput.toLowerCase();
				if (lazyConstraint.matches(searchInput) || lazyConstraint.contains(searchInput) || lazyDescription.matches(searchInput)
					|| lazyDescription.contains(searchInput)) {
					viewer.addItem(constraint);
				}
			}
		}
	}

	/**
	 * Listenes to Changes to adapt the View and the Constraint List under the feature diagram
	 */
	private final IPartListener2 constraintListener = new IPartListener2() {

		@Override
		public void partOpened(IWorkbenchPartReference part) {
			if (part.getId().equals(ID)) {
				setConstraintsHidden(true);
			}
		}

		@Override
		public void partDeactivated(IWorkbenchPartReference part) {}

		@Override
		public void partClosed(IWorkbenchPartReference part) {
			if (part instanceof FeatureModelEditor) {
				if ((FeatureModelUtil.getActiveFMEditor() == part) || (FeatureModelUtil.getActiveFMEditor() == null)) {
					viewer.getViewer().refresh();
				}
			}
		}

		@Override
		public void partBroughtToTop(IWorkbenchPartReference part) {
			if (part.getPart(false) instanceof FeatureModelEditor) {
				refreshView(((FeatureModelEditor) part.getPart(false)).getFeatureModel(), searchText);
			} else {
				viewer.addNoFeatureModelItem();
			}
		}

		@Override
		public void partActivated(IWorkbenchPartReference part) {
			if (part.getPart(false) instanceof FeatureModelEditor) {
				refreshView(((FeatureModelEditor) part.getPart(false)).getFeatureModel(), searchText);
			} else if ((part.getPart(false) instanceof ConstraintViewController) && (FeatureModelUtil.getActiveFMEditor() != null)) {
				refreshView(FeatureModelUtil.getFeatureModel(), searchText);
			}
			if (part.getPart(false) instanceof IEditorPart) {
				setConstraintsHidden(constraintsHidden);
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
		public void partInputChanged(IWorkbenchPartReference partRef) {}

	};

	@Override
	public void setFocus() {}

	/**
	 * Changes if the Constraints are shown under the feature model
	 */
	public void setConstraintsHidden(boolean hideConstraints) {
		if ((FeatureModelUtil.getActiveFMEditor() != null) && (constraintsHidden != hideConstraints)) {
			FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().setConstraintsHidden(hideConstraints);
			FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().redrawDiagram();
			constraintsHidden = hideConstraints;
		}
	}

	/**
	 * Reacts on observer of the current feature model
	 */
	@Override
	public void propertyChange(FeatureIDEEvent event) {
		refreshView(currentModel, searchText);
	}
}
