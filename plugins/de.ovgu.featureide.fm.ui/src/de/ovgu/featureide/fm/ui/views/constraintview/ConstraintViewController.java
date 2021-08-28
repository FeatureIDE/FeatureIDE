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

import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.jface.dialogs.IPageChangedListener;
import org.eclipse.jface.dialogs.PageChangedEvent;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.operations.RedoActionHandler;
import org.eclipse.ui.operations.UndoActionHandler;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.core.AnalysesCollection;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelProperty;
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
 * This class represents the controller (MVC) of the constraint view. It holds the logic that operates on the view.
 *
 * @author Rosiak Kamil
 * @author Domenik Eichhorn
 * @author Rahel Arens
 * @author Thomas Graave
 * @author Philipp Vulpius
 * @author Soeren Viegener
 */
public class ConstraintViewController extends ViewPart implements GUIDefaults {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.ConstraintView";

	private ConstraintView constraintView;
	private ConstraintViewPartListener partListener;
	private ConstraintViewSettingsMenu settingsMenu;

	private FeatureModelEditor featureModelEditor;
	private boolean featureDiagramPageVisible = false;

	private FeatureModelAnalyzer analyzer;

	/**
	 * The constraint used to detect when the analysis is finished
	 */
	private IConstraint updateConstraint;

	/**
	 * The listener used on the updateConstraint. This listener is called in the FeatureDiagramEditor when the analysis is finished. This happens in
	 * {@link FeatureDiagramEditor#refreshGraphics(AnalysesCollection)}. The whole constraintView is updated as we do not know of a way to figure out the exact
	 * constraints affected by the analysis.
	 */
	private final IEventListener updateConstraintListener = new IEventListener() {

		@Override
		public void propertyChange(FeatureIDEEvent featureIDEEvent) {
			constraintView.refresh();
		}
	};

	/**
	 * SelectionListener for the FeatureDiagramEditor
	 */
	private final ISelectionChangedListener selectionListener = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			final List<FeatureEditPart> selectionList = getSelectionList(event.getStructuredSelection());

			// only update and refresh when the selection changed
			if (!selectionList.equals(constraintView.filter.getFeatureModelSelection())) {
				constraintView.filter.setFeatureModelSelection(selectionList);
				constraintView.refresh();
			}
		}
	};

	/**
	 * EventListener for the FeatureModelEditor
	 */
	private final IEventListener eventListener = new IEventListener() {

		@Override
		public void propertyChange(FeatureIDEEvent event) {
			switch (event.getEventType()) {
			case ACTIVE_EXPLANATION_CHANGED:
				if (featureModelEditor != null) {
					constraintView.filter.setActiveExplanation(featureModelEditor.diagramEditor.getActiveExplanation());
				}
				constraintView.refresh();
				break;
			case CONSTRAINT_DELETE:
				if ((event.getOldValue() == updateConstraint) && (updateConstraint != null)) {
					// remove the updateConstraintListener if the constraint is deleted
					updateConstraint.removeListener(updateConstraintListener);
					updateConstraint = getUpdateConstraint(featureModelEditor);
					if (updateConstraint != null) {
						// add a new updateConstraintListener to a new constraint
						updateConstraint.addListener(updateConstraintListener);
					}
				}
				constraintView.refresh();
				break;
			case MODEL_DATA_CHANGED:
				if (updateConstraint != null) {
					updateConstraint.removeListener(updateConstraintListener);
				}
				updateConstraint = getUpdateConstraint(featureModelEditor);
				if (updateConstraint != null) {
					// add a new updateConstraintListener to a new constraint
					updateConstraint.addListener(updateConstraintListener);
				}
				constraintView.refresh();
				break;
			case MODEL_DATA_OVERWRITTEN:
			case MODEL_DATA_SAVED:
			case MANDATORY_CHANGED:
			case GROUP_TYPE_CHANGED:
			case FEATURE_NAME_CHANGED:
			case FEATURE_ADD_SIBLING:
			case FEATURE_ADD:
			case FEATURE_ADD_ABOVE:
			case FEATURE_DELETE:
			case CONSTRAINT_MODIFY:
			case CONSTRAINT_ADD:
			case FEATURE_COLLAPSED_CHANGED:
			case FEATURE_COLLAPSED_ALL_CHANGED:
			case ATTRIBUTE_CHANGED:
			case STRUCTURE_CHANGED:
				constraintView.refresh();
				break;
			default:
				break;
			}
		}
	};

	/**
	 * PageChangeListener for the FeatureModelEditor
	 */
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
	 * ModifyListener for the search box in the ConstraintView
	 */
	private final ModifyListener searchListener = new ModifyListener() {

		@Override
		public void modifyText(ModifyEvent e) {
			final String searchText = constraintView.getSearchBox().getText();
			constraintView.filter.setSearchText(searchText);
			constraintView.refresh();
		}

	};

	/**
	 * Standard SWT initialize called after construction.
	 */
	@Override
	public void createPartControl(Composite parent) {
		parent.setLayout(new FillLayout(SWT.HORIZONTAL));
		constraintView = new ConstraintView(parent, this);

		addListeners();

		settingsMenu = new ConstraintViewSettingsMenu(this);
		new ConstraintViewContextMenu(this);

		// get the active editor
		final IEditorPart activeEditor = getSite().getPage().getActiveEditor();
		if (activeEditor instanceof FeatureModelEditor) {
			setFeatureModelEditor((FeatureModelEditor) activeEditor);
		} else {
			refresh();
		}
	}

	/**
	 * Adds the needed listeners to the ConstraintView and the page.
	 */
	private void addListeners() {
		constraintView.getSearchBox().addModifyListener(searchListener);

		constraintView.getViewer().addSelectionChangedListener(new ConstraintViewSelectionListener(this));
		constraintView.getViewer().addDoubleClickListener(new ConstraintViewDoubleClickListener(this));
		constraintView.getViewer().getTree().addKeyListener(new ConstraintViewKeyListener(this));

		partListener = new ConstraintViewPartListener(this);
		getSite().getPage().addPartListener(partListener);
	}

	/**
	 * Refreshes the ConstraintView.
	 *
	 * This includes: The state of the settings menu The currently tracked FeatureModelEditor. Either the content is updated to a new FeatureModel or the "Open
	 * a FeatureDiagram" text is shown.
	 */
	public void refresh() {
		final boolean constraintsViewVisible = isConstraintsViewVisible();
		final boolean constraintsListVisible = isConstraintsListVisible();

		settingsMenu.setStateOfActions(constraintsListVisible && constraintsViewVisible);
		setConstraintsHidden(featureModelEditor, constraintsViewVisible);
		updateUndoRedoActions();

		if (constraintsViewVisible && constraintsListVisible) {
			settingsMenu.setShowCollapsedConstraintsInViewActionImage(
					featureModelEditor.diagramEditor.getGraphicalFeatureModel().getLayout().showCollapsedConstraints());
			// set the input (the current FeatureModel) for the content provider
			final IFeatureModel featureModel = featureModelEditor.getFeatureModelManager().getVarObject();
			if (constraintView.getViewer().getInput() != featureModel) {
				constraintView.getViewer().setInput(featureModel);
				constraintView.getViewer().getTree().setHeaderVisible(true);
			}
		} else {
			// set the input for the content provider to be the "Open a FeatureDiagram" text
			final String openText = StringTable.OPEN_A_FEATURE_DIAGRAM;
			if (constraintView.getViewer().getInput() != openText) {
				constraintView.getViewer().setInput(openText);
				constraintView.getViewer().getTree().setHeaderVisible(false);
			}
		}
	}

	/**
	 * Adds or removes action handlers for undo/redo actions depending on the current feature model editor.
	 */
	private void updateUndoRedoActions() {
		final IActionBars actionBars = getViewSite().getActionBars();
		UndoActionHandler undoActionHandler = null;
		RedoActionHandler redoActionHandler = null;
		if (featureModelEditor != null) {
			final Object undoContext = featureModelEditor.getFeatureModelManager().getUndoContext();
			if (undoContext instanceof IUndoContext) {
				undoActionHandler = new UndoActionHandler(getSite(), (IUndoContext) undoContext);
				redoActionHandler = new RedoActionHandler(getSite(), (IUndoContext) undoContext);
			}
		}
		actionBars.setGlobalActionHandler(ActionFactory.UNDO.getId(), undoActionHandler);
		actionBars.setGlobalActionHandler(ActionFactory.REDO.getId(), redoActionHandler);
		actionBars.updateActionBars();
	}

	/**
	 * Sets the FeatureModelEditor for the ConstraintView.
	 *
	 * Adds and removes all listeners accordingly. Refreshes the whole view. No other refresh is needed after this call. If the new FeatureModelEditor is the
	 * same as the current one, the function returns immediately.
	 *
	 * @param newFeatureModelEditor The new FeatureModelEditor
	 */
	public void setFeatureModelEditor(FeatureModelEditor newFeatureModelEditor) {
		if (featureModelEditor == newFeatureModelEditor) {
			return;
		}

		constraintView.getSearchBox().setText("");
		constraintView.filter.clear();

		// remove listeners from previous FeatureModelEditor
		if (featureModelEditor != null) {
			setConstraintsHidden(featureModelEditor, false);
			if (featureModelEditor.diagramEditor != null) {
				featureModelEditor.diagramEditor.removeSelectionChangedListener(selectionListener);
			}
			featureModelEditor.removePageChangedListener(pageChangeListener);
			featureModelEditor.removeEventListener(eventListener);

			if (updateConstraint != null) {
				updateConstraint.removeListener(updateConstraintListener);
			}
		}

		// add listeners, etc. to new FeatureModelEditor
		if (newFeatureModelEditor != null) {
			final Boolean isAutomaticCalculation =
				FeatureModelProperty.getBooleanProperty(newFeatureModelEditor.getFeatureModelManager().getSnapshot().getProperty(),
						FeatureModelProperty.TYPE_CALCULATIONS, FeatureModelProperty.PROPERTY_CALCULATIONS_RUN_AUTOMATICALLY);
			if (isAutomaticCalculation == Boolean.TRUE) {
				analyzer = newFeatureModelEditor.getFeatureModelManager().getVariableFormula().getAnalyzer();
			}

			newFeatureModelEditor.diagramEditor.addSelectionChangedListener(selectionListener);
			newFeatureModelEditor.addPageChangedListener(pageChangeListener);
			newFeatureModelEditor.addEventListener(eventListener);
			featureDiagramPageVisible = newFeatureModelEditor.getSelectedPage() instanceof FeatureDiagramEditor;
			constraintView.resetSort();

			updateConstraint = getUpdateConstraint(newFeatureModelEditor);
			if (updateConstraint != null) {
				updateConstraint.addListener(updateConstraintListener);
			}

			constraintView.filter.setFeatureModelSelection(getSelectionList(newFeatureModelEditor.diagramEditor.getViewer().getSelection()));
			constraintView.filter.setActiveExplanation(newFeatureModelEditor.diagramEditor.getActiveExplanation());

			// update filter and settings menu to correctly handle "showCollapsedConstraints"
			final IGraphicalFeatureModel graphicalFeatureModel = newFeatureModelEditor.diagramEditor.getGraphicalFeatureModel();
			constraintView.filter.setGraphicalFeatureModel(graphicalFeatureModel);
		}

		featureModelEditor = newFeatureModelEditor;
		refresh();
	}

	/**
	 * Returns the first constraint in the FeatureModel of the VariableFormula. The FeatureModel returned by {@link FeatureModelManager#getVarObject()} is a
	 * different one than {@link FeatureModelFormula#getFeatureModel()}.
	 *
	 * @param featureModelEditor The FeatureModelEditor that holds the FeatureModel
	 * @return The first constraint in the FeatureModel
	 */
	private IConstraint getUpdateConstraint(FeatureModelEditor featureModelEditor) {
		final List<IConstraint> graphicalConstraints = featureModelEditor.getFeatureModelManager().getVariableFormula().getFeatureModel().getConstraints();
		if (!graphicalConstraints.isEmpty()) {
			return graphicalConstraints.get(0);
		}
		return null;
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
		constraintView.dispose();
	}

	@Override
	public void setFocus() {
		constraintView.getViewer().getTree().setFocus();
	}

	/**
	 * Sets the constraints to be hidden or shown below the diagram of a FeatureModelEditor.
	 *
	 * @param featureModelEditor The FeatureModelEditor which contains the FeatureDiagramEditor in which the constraints are either hidden or not.
	 * @param hideConstraints True if the constraints are to be hidden. False if the constraints are to be visible.
	 */
	public void setConstraintsHidden(FeatureModelEditor featureModelEditor, boolean hideConstraints) {
		if (featureModelEditor != null) {
			final IGraphicalFeatureModel graphicalFeatureModel = featureModelEditor.diagramEditor.getGraphicalFeatureModel();

			// only update the model if the new state of hideConstraint is different from the current state
			if (graphicalFeatureModel.getConstraintsHidden() != hideConstraints) {
				graphicalFeatureModel.setConstraintsHidden(hideConstraints);
				graphicalFeatureModel.redrawDiagram();
			}
		}
	}

	/**
	 * Filters the selection by only returning the selected FeatureEditParts
	 *
	 * @param selection StructuredSelection to be filtered
	 * @return List of FeatureEditParts that are contained in the selection
	 */
	public List<FeatureEditPart> getSelectionList(ISelection selection) {
		final List<FeatureEditPart> selectionList = new ArrayList<>();

		for (final Object o : ((IStructuredSelection) selection).toList()) {
			// only consider FeatureEditParts
			if (o instanceof FeatureEditPart) {
				selectionList.add((FeatureEditPart) o);
			}
		}
		return selectionList;
	}

	public FeatureModelManager getFeatureModelManager() {
		return featureModelEditor.getFeatureModelManager();
	}

	public TreeViewer getTreeViewer() {
		return constraintView.getViewer();
	}

	public ConstraintView getView() {
		return constraintView;
	}

	public ConstraintViewSettingsMenu getSettingsMenu() {
		return settingsMenu;
	}

	public FeatureModelEditor getFeatureModelEditor() {
		return featureModelEditor;
	}

	public FeatureModelAnalyzer getAnalyzer() {
		return analyzer;
	}
}
