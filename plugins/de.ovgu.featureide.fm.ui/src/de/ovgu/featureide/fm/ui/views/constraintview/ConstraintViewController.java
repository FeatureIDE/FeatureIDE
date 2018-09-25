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

import java.util.List;

import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
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
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateConstraintAction;
import de.ovgu.featureide.fm.ui.utils.FeatureModelUtil;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.DeleteConstraintAction;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.EditConstraintAction;
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
		addListener();
		getSite().getPage().addPartListener(constraintListener);
		if (FeatureModelUtil.getActiveFMEditor() != null) {
			currentModel = FeatureModelUtil.getFeatureModel();
			refreshView(currentModel);
		}
		createContextMenu(viewer.getViewer());

	}

	/**
	 * reacts when searchBox noticed input and modifies the Constraint table according to the input
	 */
	private final ModifyListener searchListener = new ModifyListener() {

		@Override
		public void modifyText(ModifyEvent e) {
			searchText = viewer.getSearchBox().getText();
			refreshView(currentModel);
		}

	};

	/**
	 * this method first clears the table and then adds all constrains that contain searchInput in their DisplayName or Description also it checks for RegEx
	 * matching in searchInput
	 */
	public void refreshView(IFeatureModel currentModel) {
		if (currentModel != null) {
			this.currentModel = currentModel;
			this.currentModel.addListener(this);
			viewer.removeAll();
			// if empty search show only constrains from non collapsed features
			if (searchText.equals("")) {
				hideCollapsedConstraints(currentModel);
			} else {
				findConstraints(currentModel);
			}
		}
	}

	/**
	 * only shows constraints from features that are not collapsed
	 */
	private void hideCollapsedConstraints(IFeatureModel currentModel) {
		final List<IGraphicalConstraint> constraints =
			FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().getNonCollapsedConstraints();
		for (final IGraphicalConstraint constraint : constraints) {
			if (constraint.isFeatureSelected() || FeatureModelUtil.getActiveFMEditor().diagramEditor.getViewer().getSelectedEditParts().isEmpty()) {
				viewer.addItem(constraint.getObject());
			}
		}

	}

	/**
	 * searches constraints that match the searchInput (Description and Displayname) and adds them to the TreeViewer
	 */
	private void findConstraints(IFeatureModel currentModel) {
		for (final IConstraint constraint : currentModel.getConstraints()) {
			final String lazyConstraint = constraint.getDisplayName().toLowerCase();
			final String lazyDescription = constraint.getDescription().toLowerCase().replaceAll("\n", " ");
			searchText = searchText.toLowerCase();
			if (lazyConstraint.matches(".*" + searchText + ".*") || lazyDescription.matches(".*" + searchText + ".*")) {
				viewer.addItem(constraint);

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
				refreshView(((FeatureModelEditor) part.getPart(false)).getFeatureModel());
			} else {
				viewer.addNoFeatureModelItem();
			}
		}

		@Override
		public void partActivated(IWorkbenchPartReference part) {
			if (part.getPart(false) instanceof FeatureModelEditor) {
				refreshView(((FeatureModelEditor) part.getPart(false)).getFeatureModel());
			} else if ((part.getPart(false) instanceof ConstraintViewController) && (FeatureModelUtil.getActiveFMEditor() != null)) {
				refreshView(FeatureModelUtil.getFeatureModel());
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

	/**
	 * adding Listener to the tree viewer
	 */
	private void addListener() {
		// doubleclicklistener
		viewer.getViewer().addDoubleClickListener(new IDoubleClickListener() {
			@Override
			public void doubleClick(DoubleClickEvent event) {

				if (event.getSource() instanceof TreeViewer) {
					final TreeSelection treeSelection = (TreeSelection) event.getSelection();
					if (treeSelection.getFirstElement() instanceof IConstraint) {
						new EditConstraintAction(viewer.getViewer(), currentModel).run();
					}
				}
			}
		});
	}

	/**
	 * Creates the context menu
	 *
	 * @param viewer
	 */
	protected void createContextMenu(Viewer viewer) {
		final MenuManager contextMenu = new MenuManager("#ViewerMenu"); //$NON-NLS-1$
		contextMenu.setRemoveAllWhenShown(true);
		contextMenu.addMenuListener(new IMenuListener() {
			@Override
			public void menuAboutToShow(IMenuManager mgr) {
				fillContextMenu(mgr);
			}
		});

		final Menu menu = contextMenu.createContextMenu(viewer.getControl());
		viewer.getControl().setMenu(menu);
	}

	/**
	 * Fill dynamic context menu
	 *
	 * @param contextMenu
	 */
	protected void fillContextMenu(IMenuManager contextMenu) {
		contextMenu.add(new CreateConstraintAction(viewer.getViewer(), currentModel));
		contextMenu.add(new EditConstraintAction(viewer.getViewer(), currentModel));
		contextMenu.add(new DeleteConstraintAction(viewer.getViewer(), currentModel));
	}

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
		refreshView(currentModel);
	}
}
