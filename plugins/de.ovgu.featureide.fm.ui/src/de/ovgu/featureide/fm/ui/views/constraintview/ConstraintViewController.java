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

import org.eclipse.jface.dialogs.IPageChangedListener;
import org.eclipse.jface.dialogs.PageChangedEvent;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.utils.FeatureModelUtil;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.EditConstraintInViewAction;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewPartListener;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintView;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintViewContextMenu;

/**
 * This class represents the controller (MVC) of the constraint view it creates all GUI elements and holds the logic that operates on the view.
 *
 * @author "Rosiak Kamil"
 * @author "Domenik Eichhorn"
 * @author "Rahel Arens"
 * @author "Thomas Graave"
 */
public class ConstraintViewController extends ViewPart implements IEventListener, GUIDefaults {
	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.ConstraintView";
	private static final Integer FEATURE_EDIT_PART_OFFSET = 17;
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
		getSite().getPage().addPartListener(new ConstraintViewPartListener(this));
		if (FeatureModelUtil.getActiveFMEditor() != null) {
			currentModel = FeatureModelUtil.getFeatureModel();
			addPageChangeListener(FeatureModelUtil.getActiveFMEditor());
			refreshView(currentModel);
		}
		new ConstraintViewContextMenu(this);

	}

	/**
	 * reacts when searchBox noticed input and modifies the Constraint table according to the input
	 */
	private final ModifyListener searchListener = new ModifyListener() {

		@Override
		public void modifyText(ModifyEvent e) {
			searchText = viewer.getSearchBox().getText();
			checkForRefresh();
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
			// no search text is entered:
			if (searchText.equals("")) {
				addConstraints(currentModel);
			} else {
				// when searchText is entered, search through all constraints
				findConstraints(currentModel);
			}
		}
	}

	/**
	 * only shows constraints from features that are not collapsed. If there are selected features we only show constraint containing at least one of the
	 * selected features
	 */
	private void addConstraints(IFeatureModel currentModel) {
		final List<IGraphicalConstraint> constraints =
			FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().getNonCollapsedConstraints();
		// goes through all constraints that are not collapsed
		for (final IGraphicalConstraint constraint : constraints) {
			if (!FeatureModelUtil.getActiveFMEditor().diagramEditor.getViewer().getSelectedEditParts().isEmpty()) {
				// when at least one feature is selected:
				// goes through all features that are selected
				for (final Object part : FeatureModelUtil.getActiveFMEditor().diagramEditor.getViewer().getSelectedEditParts()) {
					if (part instanceof FeatureEditPart) {
						if (matchesConstraint(part, constraint)) {
							viewer.addItem(constraint.getObject());
							break;
						}
					}
				}
			} else {
				// when no feature is selected, adds all constraints to the viewer
				viewer.addItem(constraint.getObject());
			}
		}
	}

	/**
	 * Compares whether a FeatureEditPart occurs in a constraint and returns true if yes
	 */
	private boolean matchesConstraint(Object part, IGraphicalConstraint constraint) {
		if (part instanceof FeatureEditPart) {
			// Cutting the String because FeatureEditPart.toString == "FeatureEditPart( >Name< )";
			final String partName = part.toString().substring(FEATURE_EDIT_PART_OFFSET, part.toString().length() - 2);
			// Adding blanks to allow every case to be covered by just one RegEx
			final String constraintName = " " + constraint.getObject().getDisplayName() + " ";
			if (constraintName.matches(".* " + partName + " .*")) {
				return true;
			}
		}
		return false;
	}

	/**
	 * searches constraints that match the searchInput (Description and Displayname) and adds them to the TreeViewer
	 */
	private void findConstraints(IFeatureModel currentModel) {
		for (final IConstraint constraint : currentModel.getConstraints()) {
			final String lazyConstraint = constraint.getDisplayName().toLowerCase();
			final String lazyDescription = constraint.getDescription().toLowerCase().replaceAll("\n", " ");
			searchText = searchText.toLowerCase();
			// RegEx search with part string: .* at the start and at the end enables part search automatically
			if (lazyConstraint.matches(".*" + searchText + ".*") || lazyDescription.matches(".*" + searchText + ".*")) {
				viewer.addItem(constraint);
			}
		}
	}

	/**
	 * check if the page is the FeatureDiagramEditor.
	 *
	 */
	public void checkForRefresh() {
		if (FeatureModelUtil.getActiveFMEditor() != null) {
			final FeatureModelEditor fme = FeatureModelUtil.getActiveFMEditor();
			if (fme.getActivePage() == 0) {
				addPageChangeListener(fme);
				refreshView(fme.getFeatureModel());
			} else {
				viewer.addNoFeatureModelItem();
			}
		}

	}

	/**
	 * add a listener to the Feature model editor to get the page change events
	 *
	 */
	public void addPageChangeListener(FeatureModelEditor fme) {
		fme.addPageChangedListener(new IPageChangedListener() {
			@Override
			public void pageChanged(PageChangedEvent event) {
				if (event.getSelectedPage() instanceof FeatureDiagramEditor) {
					refreshView(FeatureModelUtil.getFeatureModel());
				} else {
					viewer.addNoFeatureModelItem();
				}

			}
		});
	}

	/**
	 * adding Listener to the tree viewer
	 */
	private void addListener() {
		viewer.getViewer().addDoubleClickListener(new IDoubleClickListener() {
			@Override
			public void doubleClick(DoubleClickEvent event) {

				if (event.getSource() instanceof TreeViewer) {
					final TreeSelection treeSelection = (TreeSelection) event.getSelection();
					if (treeSelection.getFirstElement() instanceof IConstraint) {
						new EditConstraintInViewAction(viewer.getViewer(), currentModel).run();
					}
				}
			}
		});
	}

	@Override
	public void setFocus() {}

	/**
	 * Changes if the Constraints are shown under the feature model
	 */
	public void setConstraintsHidden(boolean hideConstraints) {
		if ((FeatureModelUtil.getActiveFMEditor() != null)) {
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
		if (FeatureModelUtil.getActiveFMEditor() != null) {
			checkForRefresh();
		}
	}

	public boolean isConstraintsHidden() {
		return constraintsHidden;
	}

	/**
	 * returns the current model
	 */
	public IFeatureModel getCurrentModel() {
		return currentModel;
	}

	public TreeViewer getTreeViewer() {
		return viewer.getViewer();
	}

	public ConstraintView getView() {
		return viewer;
	}
}
