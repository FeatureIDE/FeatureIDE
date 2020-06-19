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
import java.util.regex.PatternSyntaxException;

import org.eclipse.jface.dialogs.IPageChangedListener;
import org.eclipse.jface.dialogs.PageChangedEvent;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties;
import de.ovgu.featureide.fm.core.analysis.FeatureModelProperties.FeatureModelStatus;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelProperty;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel.FeatureModelElementTrace;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelReason;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.FeatureFigure;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;
import de.ovgu.featureide.fm.ui.utils.FeatureModelUtil;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewDoubleClickListener;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewKeyListener;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewPartListener;
import de.ovgu.featureide.fm.ui.views.constraintview.util.ConstraintColorPair;
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
public class ConstraintViewController extends ViewPart implements GUIDefaults, ISelectionChangedListener {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.ConstraintView";

	private static final Integer FEATURE_EDIT_PART_OFFSET = 17;

	private ConstraintView viewer;
	private FeatureModelManager fmManager;
	private ConstraintViewPartListener partListener;
	private ConstraintViewSettingsMenu settingsMenu;
	private Explanation<?> explanation;

	private String searchText = "";
	private boolean featureDiagramPageVisible = false;

	private FeatureModelEditor featureModelEditor;

	private ISelection lastSelection;

	private final ISelectionChangedListener selectionListener = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			if ((lastSelection == null) || !lastSelection.equals(event.getSelection())) {
				if (FeatureModelUtil.getActiveFMEditor() != null) {
					checkForRefresh();
				}
			}
			lastSelection = event.getSelection();
		}
	};

	private final IEventListener eventListener = new IEventListener() {

		/**
		 * Reacts on observer of the current feature model
		 */
		@Override
		public void propertyChange(FeatureIDEEvent event) {
			switch (event.getEventType()) {
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
			case ACTIVE_EXPLANATION_CHANGED:
				if (FeatureModelUtil.getActiveFMEditor() != null) {
					checkForRefresh();
				}
				break;
			default:
				break;
			}
		}
	};

	private final IPageChangedListener pageChangeListener = new IPageChangedListener() {

		@Override
		public void pageChanged(PageChangedEvent event) {
			featureDiagramPageVisible = event.getSelectedPage() instanceof FeatureDiagramEditor;
			checkForRefresh();
		}
	};

	/**
	 * Standard SWT initialize called after construction.
	 */
	@Override
	public void createPartControl(Composite parent) {
		parent.setLayout(new FillLayout(SWT.HORIZONTAL));
		viewer = new ConstraintView(parent, this);
		viewer.getSearchBox().addModifyListener(searchListener);
		addListener();
		settingsMenu = new ConstraintViewSettingsMenu(this);
		new ConstraintViewContextMenu(this);

		final IEditorPart activeEditor = getSite().getPage().getActiveEditor();
		if (activeEditor instanceof FeatureModelEditor) {
			setFeatureModelEditor((FeatureModelEditor) activeEditor);
		}

		checkForRefresh();
	}

	/**
	 * reacts when searchBox noticed input and modifies the Constraint table according to the input
	 */
	private final ModifyListener searchListener = new ModifyListener() {

		@Override
		public void modifyText(ModifyEvent e) {
			searchText = viewer.getSearchBox().getText();
			if (searchText.isEmpty()) {
				viewer.removeAll();
				addVisibleConstraints();
			} else {
				checkForRefresh();
			}
		}

	};

	/**
	 * this method first clears the table and then adds all constrains that contain searchInput in their DisplayName or Description also it checks for RegEx
	 * matching in searchInput
	 */
	public void refreshView(FeatureModelManager fmManager) {
		if (this.fmManager != fmManager) {
			if (this.fmManager != null) {
				this.fmManager.removeListener(eventListener);
				this.fmManager = null;
			}
			if (fmManager != null) {
				this.fmManager = fmManager;
//				fmManager.getVariableFormula().getAnalyzer().analyzeFeatureModel(null);
				this.fmManager.addListener(eventListener);
			}
		}
		if (settingsMenu != null) {
			settingsMenu.update(this);
		}

		refreshConstraints(fmManager);
	}

	/**
	 * only shows constraints from features that are not collapsed. If there are selected features we only show constraint containing at least one of the
	 * selected features
	 */
	private void refreshConstraints(FeatureModelManager currentModel) {
		// Refresh entire List
		viewer.removeAll();
		// no search text is entered:
		if (searchText.isEmpty()) {
			final List<ConstraintColorPair> explanationList = getExplanationConstraints();
			// If one or more Feature were selected
			if (!featureModelEditor.diagramEditor.getViewer().getSelectedEditParts().isEmpty()) {
				addFeatureConstraints();
			} else {
				addVisibleConstraints();
			}
			//

			// Check if automatic calculations are enabled and selection has explanation or Model is void
			if (FeatureModelProperty.isRunCalculationAutomatically(fmManager.getVarObject())
				&& FeatureModelProperty.isCalculateFeatures(fmManager.getVarObject())) {
				if ((explanationList != null) || currentModel.getVariableFormula().getAnalyzer().getFeatureModelProperties().hasVoidModelConstraints()) {
					changeIntoDecoratedConstraints();
				}
			}
		} else {
			// when searchText is entered, search through all constraints
			findConstraints(currentModel.getSnapshot());
		}
		// Only update explanations
	}

	/**
	 * Add decoration to explanation Constraints without hiding the others (called when the subject is a constraint from the view)
	 */
	private void changeIntoDecoratedConstraints() {
		final TreeItem constraints[] = viewer.getViewer().getTree().getItems();
		final List<ConstraintColorPair> explanationList = getExplanationConstraints();
		if (explanationList != null) {
			// Iterate reasons
			m: for (final ConstraintColorPair pair : explanationList) {
				// Iterate items in View
				for (final TreeItem constraint : constraints) {
					// If a match was found: Decorate that item
					if (pair.getConstraint().equals(constraint.getData())) {
						viewer.changeToDecoratedItem(pair.getConstraint(), pair.getColor());
						continue m;
					}
				}
			}
		}
	}

	/**
	 * Show all visible constraints
	 */
	public void addVisibleConstraints() {
		final List<IGraphicalConstraint> constraints = featureModelEditor.diagramEditor.getGraphicalFeatureModel().getNonCollapsedConstraints();
		for (final IGraphicalConstraint constraint : constraints) {
			viewer.addItem(constraint.getObject());
		}
	}

	/**
	 * Show constraints containing the selected feature and those which are part of the current explanation
	 */
	public void addFeatureConstraints() {
		final FeatureDiagramEditor diagramEditor = featureModelEditor.diagramEditor;
		if (!diagramEditor.getViewer().getSelectedEditParts().isEmpty()) {
			// when at least one feature is selected:
			// goes through all features that are selected
			final List<IGraphicalConstraint> constraints = diagramEditor.getGraphicalFeatureModel().getNonCollapsedConstraints();
			for (final IGraphicalConstraint constraint : constraints) {
				for (final Object part : diagramEditor.getViewer().getSelectedEditParts()) {
					if (part instanceof FeatureEditPart) {
						if (matchesConstraint(part, constraint)) {
							viewer.addItem(constraint.getObject());
							break;
						}
					}
				}
			}
		}
		addExplanationConstraints();
	}

	/**
	 * Add all constraints that are part of the active explanation
	 */
	private void addExplanationConstraints() {
		// if there is no active explanation, don't do anything
		if (FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().getActiveExplanation() == null) {
			return;
		}

		final List<IGraphicalConstraint> constraints =
			FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().getNonCollapsedConstraints();
		final Iterable<Reason<?>> reasons = FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().getActiveExplanation().getReasons();

		for (final Reason<?> r : reasons) {
			if (r.getSubject() instanceof FeatureModelElementTrace) {
				if (((FeatureModelElementTrace) r.getSubject()).getElement() != null) {
					if (((FeatureModelElementTrace) r.getSubject()).getElement() instanceof Constraint) {
						final Constraint c = (Constraint) ((FeatureModelElementTrace) r.getSubject()).getElement();
						for (final IGraphicalConstraint constraint : constraints) {
							if (constraint.getObject().equals(c)) {
								boolean additem = true;
								final TreeItem[] treeitems = viewer.getViewer().getTree().getItems();
								for (int i = 0; i < treeitems.length; i++) {
									// check for duplicate constraints before adding
									if (treeitems[i].getData().equals(c)) {
										additem = false;
										break;
									}
								}
								if (additem) {
									viewer.addItem(c);
								}
								break;
							}
						}
					}
				}
			}
		}
	}

//	/**
//	 * Show the explanation constraints with decoration
//	 */
//	public void addDecoratedConstraints(List<ConstraintColorPair> explanationList) {
//		if (explanationList != null) {
//			final List<IGraphicalConstraint> constraints =
//				featureModelEditor.diagramEditor.getGraphicalFeatureModel().getNonCollapsedConstraints();
//			// Iterate over non collapsed constraints
//			m: for (final IGraphicalConstraint constraint : constraints) {
//				// Iterate over Explanation Constraints. If match found decorate it
//				for (final ConstraintColorPair pair : explanationList) {
//					if (pair.getConstraint().equals(constraint.getObject())) {
//						viewer.addDecoratedItem(pair.getConstraint(), pair.getColor());
//						continue m;
//					}
//				}
//				// No match found: Add it undecorated
//				// viewer.addItem(constraint.getObject());
//			}
//		}
//	}

	/**
	 * Compares whether a FeatureEditPart occurs in a constraint and returns true if yes
	 */
	private boolean matchesConstraint(Object part, IGraphicalConstraint constraint) {
		if (part instanceof FeatureEditPart) {
			// Cutting the String because FeatureEditPart.toString == "FeatureEditPart( >Name< )";
			final String partName = part.toString().substring(FEATURE_EDIT_PART_OFFSET, part.toString().length() - 2);
			// Adding blanks to allow every case to be covered by just one RegEx
			final String constraintName = " " + constraint.getObject().getDisplayName() + " ";
			if (constraintName.matches(".* -*" + partName + " .*")) {
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
			final String lazyDescription = constraint.getDescription().toLowerCase().replaceAll("\n", " ").replaceAll("\r", " ");
			searchText = searchText.toLowerCase();
			// RegEx search with part string: .* at the start and at the end enables part search automatically

			try {
				if (lazyConstraint.matches(".*" + searchText + ".*") || lazyDescription.matches(".*" + searchText + ".*")) {
					viewer.addItem(constraint);
				}
			} catch (final PatternSyntaxException e) {

			}

		}
	}

	/**
	 * check if the page is the FeatureDiagramEditor.
	 *
	 */
	public void checkForRefresh() {
		final boolean constraintsViewVisible = isConstraintsViewVisible();
		final boolean constraintsListVisible = isConstraintsListVisible();

		settingsMenu.setStateOfActions(constraintsListVisible && constraintsViewVisible);
		setConstraintsHidden(featureModelEditor, constraintsViewVisible);

		if (constraintsListVisible) {
			refreshView(featureModelEditor.getFeatureModelManager());
		} else if (constraintsViewVisible) {
			viewer.addNoFeatureModelItem();
		}
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

	/**
	 * returns a set of constraints if an explanation is available else null
	 *
	 */
	public List<ConstraintColorPair> getExplanationConstraints() {
		if (featureModelEditor != null) {
			final FeatureModelEditor fmEditor = featureModelEditor;

			// Check if automatic calculations are nessecary (explanations are only present after analysing)
			if (!FeatureModelProperty.isRunCalculationAutomatically(fmManager.getVarObject())
				|| !FeatureModelProperty.isCalculateFeatures(fmManager.getVarObject())) {
				return null;
			}

			if (fmEditor != null) {
				final FeatureModelAnalyzer analyser = fmEditor.getFeatureModelManager().getVariableFormula().getAnalyzer();
				if (analyser.getAnalysesCollection().getFeatureModelProperties().hasStatus(FeatureModelStatus.VOID)) {
					explanation = (Explanation<?>) analyser.getVoidFeatureModelExplanation();
				} else if (fmEditor.diagramEditor.getActiveExplanation() != null) {
					explanation = (Explanation<?>) fmEditor.diagramEditor.getActiveExplanation();
				} else {
					return null;
				}
				final List<ConstraintColorPair> constraintList = new ArrayList<>();
				for (final Object reasonObj : explanation.getReasons()) {
					if (reasonObj == null) {
						continue;
					}
					final FeatureModelReason fmReason = (FeatureModelReason) reasonObj;
					if ((fmReason.getSubject() != null) && (fmReason.getSubject().getElement() != null)) {
						for (final IGraphicalConstraint constraint : fmEditor.diagramEditor.getGraphicalFeatureModel().getConstraints()) {
							if (constraint.getObject().equals(fmReason.getSubject().getElement())) {
								constraintList.add(new ConstraintColorPair(constraint.getObject(), FMPropertyManager.getReasonColor(fmReason)));
								continue;
							}
						}
					}
				}
				return constraintList;
			}
		}
		return null;
	}

	/**
	 * add a listener to the Feature model editor to get the page change events
	 */
	public void addPageChangeListener(FeatureModelEditor fme) {
		fme.addPageChangedListener(pageChangeListener);
	}

	/**
	 * adding Listener to the tree viewer
	 */
	private void addListener() {
		viewer.getViewer().addSelectionChangedListener(this);
		viewer.getViewer().addDoubleClickListener(new ConstraintViewDoubleClickListener(this));
		viewer.getViewer().getTree().addKeyListener(new ConstraintViewKeyListener(this));
		partListener = new ConstraintViewPartListener(this);
		getSite().getPage().addPartListener(partListener);
	}

	public void addSelectionListener() {
		featureModelEditor.diagramEditor.addSelectionChangedListener(selectionListener);
	}

	public void removeSelectionListener() {
		if (featureModelEditor != null) {
			if (featureModelEditor.diagramEditor != null) {
				featureModelEditor.diagramEditor.removeSelectionChangedListener(selectionListener);
			}
		}
	}

	@Override
	public void dispose() {
		// remove eventListener from current FeatureModel
		if (fmManager != null) {
			fmManager.removeListener(eventListener);
		}

		removeSelectionListener();

		// remove all PageListener from open FeatureModelEditors
		final IEditorReference[] editors = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getEditorReferences();
		for (final IEditorReference ref : editors) {
			if (ref.getEditor(false) instanceof FeatureModelEditor) {
				final FeatureModelEditor editor = (FeatureModelEditor) ref.getEditor(false);
				editor.removePageChangedListener(pageChangeListener);
			}
		}

		getSite().getPage().removePartListener(partListener);
	}

	@Override
	public void setFocus() {
		viewer.getViewer().getTree().setFocus();
	}

	/**
	 * Changes if the Constraints are shown under the feature model
	 */
	public void setConstraintsHidden(FeatureModelEditor featureModelEditor, boolean hideConstraints) {
		if (featureModelEditor != null) {
			IGraphicalFeatureModel graphicalFeatureModel = featureModelEditor.diagramEditor.getGraphicalFeatureModel();

			// we only need to update the model if the state of hideConstraint is different from the current state
			if(graphicalFeatureModel.getConstraintsHidden() != hideConstraints) {
				graphicalFeatureModel.setConstraintsHidden(hideConstraints);
				graphicalFeatureModel.redrawDiagram();
			}
		}
	}

	public FeatureModelManager getFeatureModelManager() {
		return fmManager;
	}

	public TreeViewer getTreeViewer() {
		return viewer.getViewer();
	}

	public ConstraintView getView() {
		return viewer;
	}

	public ConstraintViewSettingsMenu getSettingsMenu() {
		return settingsMenu;
	}

	@Override
	public void selectionChanged(SelectionChangedEvent event) {
		final TreeSelection treeSelection = (TreeSelection) event.getSelection();
		final IConstraint constraint = (IConstraint) treeSelection.getFirstElement();
		final FeatureModelEditor activeFMEditor = featureModelEditor;
		if (activeFMEditor != null) {
			final FeatureDiagramEditor diagramEditor = activeFMEditor.diagramEditor;
			if (diagramEditor != null) {
				final IGraphicalFeatureModel graphicalFeatureModel = diagramEditor.getGraphicalFeatureModel();
				if (constraint != null) {
					// Check if automatic calculations are activated (explanation are only available when anaylses are activated)
					if (FeatureModelProperty.isRunCalculationAutomatically(fmManager.getVarObject())
						&& FeatureModelProperty.isCalculateFeatures(fmManager.getVarObject())
						&& FeatureModelProperty.isCalculateConstraints(fmManager.getVarObject())) {
						final FeatureModelAnalyzer anlyzer = activeFMEditor.getFeatureModelManager().getVariableFormula().getAnalyzer();
						diagramEditor.setActiveExplanation(anlyzer.getExplanation(constraint));
					}
				}
				for (final IGraphicalFeature graphFeature : graphicalFeatureModel.getAllFeatures()) {
					if ((constraint != null) && constraint.getContainedFeatures().contains(graphFeature.getObject())) {
						graphFeature.setConstraintSelected(true);
					} else {
						graphFeature.setConstraintSelected(false);
					}
					new FeatureFigure(graphFeature, graphicalFeatureModel).updateProperties();
				}
			}
		}
	}

	public FeatureModelEditor getFeatureModelEditor() {
		return featureModelEditor;
	}

	/**
	 * Sets the current FeatureModelEditor. Removes listeners from the previous FeatureModelEditor and adds listeners to the new one.
	 *
	 * @param newFeatureModelEditor The new FeatureModelEditor
	 */
	public void setFeatureModelEditor(FeatureModelEditor newFeatureModelEditor) {
		if (featureModelEditor == newFeatureModelEditor) {
			return;
		}

		if (featureModelEditor != null) {
			setConstraintsHidden(featureModelEditor, false);
			if (featureModelEditor.diagramEditor != null) {
				featureModelEditor.diagramEditor.removeSelectionChangedListener(selectionListener);
			}
			featureModelEditor.removePageChangedListener(pageChangeListener);
		}

		if (newFeatureModelEditor != null) {
			newFeatureModelEditor.diagramEditor.addSelectionChangedListener(selectionListener);
			newFeatureModelEditor.addPageChangedListener(pageChangeListener);
			featureDiagramPageVisible = newFeatureModelEditor.getSelectedPage() instanceof FeatureDiagramEditor;
		}

		featureModelEditor = newFeatureModelEditor;
	}

	public ConstraintProperties getConstraintProperty(IConstraint element) {
		// Check if automatic calculations are nessecary (propetries are only available when anaylses are activated)
		if (FeatureModelProperty.isRunCalculationAutomatically(fmManager.getVarObject()) && FeatureModelProperty.isCalculateFeatures(fmManager.getVarObject())
			&& FeatureModelProperty.isCalculateConstraints(fmManager.getVarObject())) {
			return fmManager.getVariableFormula().getAnalyzer().getAnalysesCollection().getConstraintProperty(element);
		} else {
			return new ConstraintProperties(element);
		}
	}

}
