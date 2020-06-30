/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.dialogs.IPageChangedListener;
import org.eclipse.jface.dialogs.PageChangedEvent;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewDoubleClickListener;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewKeyListener;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewPartListener;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewSelectionListener;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintView;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintViewContextMenu;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintViewSettingsMenu;

/**
 * This class represents the controller (MVC) of the constraint view it creates all GUI elements and holds the logic that operates on the view.
 *
 * @author Rosiak Kamil
 * @author Domenik Eichhorn
 * @author Rahel Arens
 * @author Thomas Graave
 */
public class ConstraintViewController extends ViewPart implements GUIDefaults {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.ConstraintView";

	private ConstraintView view;
	private ConstraintViewPartListener partListener;
	private ConstraintViewSettingsMenu settingsMenu;
	private boolean featureDiagramPageVisible = false;

	private FeatureModelEditor featureModelEditor;

	private final ISelectionChangedListener selectionListener = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {

			final List<FeatureEditPart> selectionList = new ArrayList<>();

			for (final Object o : event.getStructuredSelection().toList()) {
				// only consider FeatureEditParts
				if (o instanceof FeatureEditPart) {
					selectionList.add((FeatureEditPart) o);
				}
			}
			if (!selectionList.equals(view.filter.getFeatureModelSelection())) {
				view.filter.setFeatureModelSelection(selectionList);
				view.refresh();
			}
		}
	};

	private final IEventListener eventListener = new IEventListener() {

		/**
		 * Reacts on observer of the current feature model
		 */
		@Override
		public void propertyChange(FeatureIDEEvent event) {
			switch (event.getEventType()) {
			case ACTIVE_EXPLANATION_CHANGED:
				view.filter.setActiveExplanation(featureModelEditor.diagramEditor.getActiveExplanation());
			case MODEL_DATA_OVERWRITTEN:
			case MODEL_DATA_CHANGED:
			case MODEL_DATA_SAVED:
			case MANDATORY_CHANGED:
			case GROUP_TYPE_CHANGED:
			case FEATURE_NAME_CHANGED:
			case FEATURE_ADD_SIBLING:
			case FEATURE_ADD:
			case FEATURE_ADD_ABOVE:
			case FEATURE_DELETE:
			case CONSTRAINT_MODIFY:
			case CONSTRAINT_DELETE:
			case CONSTRAINT_ADD:
			case FEATURE_COLLAPSED_CHANGED:
			case FEATURE_COLLAPSED_ALL_CHANGED:
			case ATTRIBUTE_CHANGED:
				view.refresh();
				break;
			default:
				break;
			}
		}
	};

	private final IPageChangedListener pageChangeListener = new IPageChangedListener() {

		@Override
		public void pageChanged(PageChangedEvent event) {
			final boolean previous = featureDiagramPageVisible;
			featureDiagramPageVisible = event.getSelectedPage() instanceof FeatureDiagramEditor;
			if (previous != featureDiagramPageVisible) {
				// only refresh if the visible page changed to or from the FeatureDiagram
				refresh();
			}
		}
	};

	/**
	 * reacts when searchBox noticed input and modifies the Constraint table according to the input
	 */
	private final ModifyListener searchListener = new ModifyListener() {

		@Override
		public void modifyText(ModifyEvent e) {
			final String searchText = view.getSearchBox().getText();
			view.filter.setSearchText(searchText);
			view.refresh();
		}

	};

	/**
	 * Standard SWT initialize called after construction.
	 */
	@Override
	public void createPartControl(Composite parent) {
		parent.setLayout(new FillLayout(SWT.HORIZONTAL));
		view = new ConstraintView(parent, this);

		addListeners();

		settingsMenu = new ConstraintViewSettingsMenu(this);
		new ConstraintViewContextMenu(this);

		final IEditorPart activeEditor = getSite().getPage().getActiveEditor();
		if (activeEditor instanceof FeatureModelEditor) {
			setFeatureModelEditor((FeatureModelEditor) activeEditor);
		} else {
			refresh();
		}
	}

	/**
	 * adding Listener to the tree viewer
	 */
	private void addListeners() {
		view.getSearchBox().addModifyListener(searchListener);

		view.getViewer().addSelectionChangedListener(new ConstraintViewSelectionListener(this));
		view.getViewer().addDoubleClickListener(new ConstraintViewDoubleClickListener(this));
		view.getViewer().getTree().addKeyListener(new ConstraintViewKeyListener(this));

		partListener = new ConstraintViewPartListener(this);
		getSite().getPage().addPartListener(partListener);
	}

	public void refresh() {
		final boolean constraintsViewVisible = isConstraintsViewVisible();
		final boolean constraintsListVisible = isConstraintsListVisible();

		settingsMenu.setStateOfActions(constraintsListVisible && constraintsViewVisible);
		setConstraintsHidden(featureModelEditor, constraintsViewVisible);

		if (constraintsViewVisible && constraintsListVisible) {
			final IFeatureModel featureModel = featureModelEditor.getFeatureModelManager().getVarObject();

			if (view.getViewer().getInput() != featureModel) {
				// set the input (the current FeatureModel) for the content provider
				view.getViewer().setInput(featureModel);
				view.getViewer().getTree().setHeaderVisible(true);
			}
		} else {
			final String openText = StringTable.OPEN_A_FEATURE_DIAGRAM;
			if (view.getViewer().getInput() != openText) {
				view.getViewer().setInput(openText);
				view.getViewer().getTree().setHeaderVisible(false);
			}
		}
	}

	/**
	 * Sets the FeatureModelEditor for the ConstraintView. Adds and removes all listeners accordingly. Sets the input for the ConstraintView and refreshes the
	 * whole view. No other refresh is needed after this call. If the new FeatureModelEditor is the same as the current one, the function returns immediately.
	 *
	 * @param newFeatureModelEditor The new FeatureModelEditor
	 */
	public void setFeatureModelEditor(FeatureModelEditor newFeatureModelEditor) {
		if (featureModelEditor == newFeatureModelEditor) {
			return;
		}

		// remove listeners from previous FeatureModelEditor
		if (featureModelEditor != null) {
			setConstraintsHidden(featureModelEditor, false);
			if (featureModelEditor.diagramEditor != null) {
				featureModelEditor.diagramEditor.removeSelectionChangedListener(selectionListener);
			}
			featureModelEditor.removePageChangedListener(pageChangeListener);
			featureModelEditor.removeEventListener(eventListener);
		}

		if (newFeatureModelEditor != null) {
			newFeatureModelEditor.diagramEditor.addSelectionChangedListener(selectionListener);
			newFeatureModelEditor.addPageChangedListener(pageChangeListener);
			newFeatureModelEditor.addEventListener(eventListener);
			featureDiagramPageVisible = newFeatureModelEditor.getSelectedPage() instanceof FeatureDiagramEditor;
			view.resetSort();
		}

		featureModelEditor = newFeatureModelEditor;
		refresh();
	}

	/**
	 * Checks if the ConstraintView is currently visible for the user
	 *
	 * @return True if the ConstraintView is visible, false if not
	 */
	public boolean isConstraintsViewVisible() {
		return PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().isPartVisible(this);
	}

	/**
	 * Checks if the constraints list is visible, i.e. there is a FeatureModelEditor which shows the FeatureDiagram page.
	 *
	 * @return True if the constraints list is visible, false if not
	 */
	public boolean isConstraintsListVisible() {
		return (featureModelEditor != null) && featureDiagramPageVisible;
	}

	@Override
	public void dispose() {

		if (featureModelEditor != null) {
			featureModelEditor.removeEventListener(eventListener);
			featureModelEditor.removePageChangedListener(pageChangeListener);
			if (featureModelEditor.diagramEditor != null) {
				featureModelEditor.diagramEditor.removeSelectionChangedListener(selectionListener);
			}
		}

		getSite().getPage().removePartListener(partListener);
	}

	@Override
	public void setFocus() {
		view.getViewer().getTree().setFocus();
	}

	/**
	 * Changes if the Constraints are shown under the feature model
	 */
	public void setConstraintsHidden(FeatureModelEditor featureModelEditor, boolean hideConstraints) {
		if (featureModelEditor != null) {
			final IGraphicalFeatureModel graphicalFeatureModel = featureModelEditor.diagramEditor.getGraphicalFeatureModel();

			// we only need to update the model if the state of hideConstraint is different from the current state
			if (graphicalFeatureModel.getConstraintsHidden() != hideConstraints) {
				graphicalFeatureModel.setConstraintsHidden(hideConstraints);
				graphicalFeatureModel.redrawDiagram();
			}
		}
	}

	public FeatureModelManager getFeatureModelManager() {
		return featureModelEditor.getFeatureModelManager();
	}

	public TreeViewer getTreeViewer() {
		return view.getViewer();
	}

	public ConstraintView getView() {
		return view;
	}

	public ConstraintViewSettingsMenu getSettingsMenu() {
		return settingsMenu;
	}

	public FeatureModelEditor getFeatureModelEditor() {
		return featureModelEditor;
	}

}
