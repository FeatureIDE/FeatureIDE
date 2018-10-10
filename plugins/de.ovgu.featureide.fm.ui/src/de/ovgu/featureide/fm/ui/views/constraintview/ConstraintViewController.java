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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.jface.dialogs.IPageChangedListener;
import org.eclipse.jface.dialogs.PageChangedEvent;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelReason;
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
import de.ovgu.featureide.fm.ui.views.constraintview.actions.DeleteConstraintAction;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.EditConstraintInViewAction;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewPartListener;
import de.ovgu.featureide.fm.ui.views.constraintview.util.ConstraintColorPair;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintView;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintViewContextMenu;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintViewSettingsMenu;

/**
 * This class represents the controller (MVC) of the constraint view it creates all GUI elements and holds the logic that operates on the view.
 *
 * @author "Rosiak Kamil"
 * @author "Domenik Eichhorn"
 * @author "Rahel Arens"
 * @author "Thomas Graave"
 */
public class ConstraintViewController extends ViewPart implements GUIDefaults {
	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.ConstraintView";
	private static final Integer FEATURE_EDIT_PART_OFFSET = 17;
	private ConstraintView viewer;
	private IFeatureModel currentModel;
	private IGraphicalFeature graphFeature;
	private IGraphicalFeatureModel graphModel;
	private ConstraintViewPartListener partListener;
	private ConstraintViewSettingsMenu settingsMenu;
	private Explanation<?> explanation;

	boolean refreshWithDelete = true;
	boolean constraintsHidden = false;

	private String searchText = "";

	// integer values that are returned when pressing a special button (from keyListener)
	private final int F_BUTTON_PRESSED = 102;
	private final int Z_BUTTON_PRESSED = 122;

	/**
	 * Standard SWT initialize called after construction.
	 */
	@Override
	public void createPartControl(Composite parent) {
		parent.setLayout(new FillLayout(SWT.HORIZONTAL));
		viewer = new ConstraintView(parent);
		viewer.getSearchBox().addModifyListener(searchListener);
		addListener();
		createListener();
		if (FeatureModelUtil.getActiveFMEditor() != null) {
			addPageChangeListener(FeatureModelUtil.getActiveFMEditor());
			refreshView(FeatureModelUtil.getFeatureModel());
		} else {
			viewer.addNoFeatureModelItem();
		}
		settingsMenu = new ConstraintViewSettingsMenu(this);
		new ConstraintViewContextMenu(this);
	}

	public void createListener() {
		partListener = new ConstraintViewPartListener(this);
		getSite().getPage().addPartListener(partListener);
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
	public void refreshView(IFeatureModel currentModel) {
		if (this.currentModel != currentModel) {
			if (this.currentModel != null) {
				this.currentModel.removeListener(eventListener);
				this.currentModel = null;
			}
			if (currentModel != null) {
				this.currentModel = currentModel;
				this.currentModel.addListener(eventListener);
			}
		}
		if (settingsMenu != null) {
			settingsMenu.update(this);
		}

		refreshConstraints(currentModel);
	}

	/**
	 * only shows constraints from features that are not collapsed. If there are selected features we only show constraint containing at least one of the
	 * selected features
	 */
	private void refreshConstraints(IFeatureModel currentModel) {
		// Refresh entire List
		if (refreshWithDelete) {
			viewer.removeAll();
			// no search text is entered:
			if (searchText.isEmpty()) {
				final List<ConstraintColorPair> explanationList = getExplanationConstraints();
				// If one or more Feature were selected
				if (!FeatureModelUtil.getActiveFMEditor().diagramEditor.getViewer().getSelectedEditParts().isEmpty()) {
					addFeatureConstraints();
				} else {
					addVisibleConstraints();
				}
				// Selection has explanation or Model is void
				if ((explanationList != null) || !FeatureModelUtil.getFeatureModel().getAnalyser().valid()) {
					changeIntoDecoratedConstraints(currentModel);
				}
			} else {
				// when searchText is entered, search through all constraints
				findConstraints(currentModel);
			}
			// Only update explanations
		} else {

			for (final TreeItem constraint : viewer.getViewer().getTree().getItems()) {
				viewer.undecorateItem((IConstraint) constraint.getData());
			}
			if (searchText.isEmpty()) {
				changeIntoDecoratedConstraints(currentModel);
			}
		}
	}

	/**
	 * Add decoration to explanation Constraints without hiding the others (called when the subject is a constraint from the view)
	 */
	private void changeIntoDecoratedConstraints(IFeatureModel currentModel) {
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
		final List<IGraphicalConstraint> constraints =
			FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().getNonCollapsedConstraints();
		for (final IGraphicalConstraint constraint : constraints) {
			viewer.addItem(constraint.getObject());
		}
	}

	/**
	 * Show constraints containing the selected feature
	 */
	public void addFeatureConstraints() {
		if (!FeatureModelUtil.getActiveFMEditor().diagramEditor.getViewer().getSelectedEditParts().isEmpty()) {
			// when at least one feature is selected:
			// goes through all features that are selected
			final List<IGraphicalConstraint> constraints =
				FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().getNonCollapsedConstraints();
			for (final IGraphicalConstraint constraint : constraints) {
				for (final Object part : FeatureModelUtil.getActiveFMEditor().diagramEditor.getViewer().getSelectedEditParts()) {
					if (part instanceof FeatureEditPart) {
						if (matchesConstraint(part, constraint)) {
							viewer.addItem(constraint.getObject());
							break;
						}
					}
				}
			}
		}
	}

	/**
	 * Show the explanation constraints with decoration
	 */
	public void addDecoratedConstraints(List<ConstraintColorPair> explanationList) {
		if (explanationList != null) {
			final List<IGraphicalConstraint> constraints =
				FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().getNonCollapsedConstraints();
			// Iterate over non collapsed constraints
			m: for (final IGraphicalConstraint constraint : constraints) {
				// Iterate over Explanation Constraints. If match found decorate it
				for (final ConstraintColorPair pair : explanationList) {
					if (pair.getConstraint().equals(constraint.getObject())) {
						viewer.addDecoratedItem(pair.getConstraint(), pair.getColor());
						continue m;
					}
				}
				// No match found: Add it undecorated
				// viewer.addItem(constraint.getObject());
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
	 * returns a set of constraints if an explanation is available else null
	 *
	 */
	public List<ConstraintColorPair> getExplanationConstraints() {
		if (FeatureModelUtil.getActiveFMEditor() != null) {
			final FeatureModelEditor fmEditor = FeatureModelUtil.getActiveFMEditor();
			if (!fmEditor.getFeatureModel().getAnalyser().valid()) {
				explanation = (Explanation<?>) fmEditor.getFeatureModel().getAnalyser().getVoidFeatureModelExplanation();
			} else if (fmEditor.diagramEditor.getActiveExplanation() != null) {
				explanation = (Explanation<?>) fmEditor.diagramEditor.getActiveExplanation();
			} else {
				return null;
			}
			final List<ConstraintColorPair> constraintList = new ArrayList<ConstraintColorPair>();
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
		return null;
	}

	/**
	 * add a listener to the Feature model editor to get the page change events
	 *
	 * TODO: remove listener when view is closed
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
		// event fired when clicking on an constraint (one click)
		viewer.getViewer().addSelectionChangedListener(new ISelectionChangedListener() {

			// marks features by changing their border when a related feature is selected
			@Override
			public void selectionChanged(SelectionChangedEvent event) {
				final TreeSelection treeSelection = (TreeSelection) event.getSelection();
				final IConstraint constraint = (IConstraint) treeSelection.getFirstElement();
				if (FeatureModelUtil.getActiveFMEditor() != null) {
					refreshWithDelete = false;
					if (constraint != null) {
						FeatureModelUtil.getActiveFMEditor().diagramEditor
								.setActiveExplanation(constraint.getFeatureModel().getAnalyser().getExplanation(constraint));
					}
					for (final IFeature feature : FeatureModelUtil.getFeatureModel().getFeatures()) {
						graphFeature = FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().getGraphicalFeature(feature);
						graphModel = FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel();
						if ((constraint != null) && constraint.getContainedFeatures().contains(feature)) {
							graphFeature.setConstraintSelected(true);
						} else {
							graphFeature.setConstraintSelected(false);
						}
						new FeatureFigure(graphFeature, graphModel).setProperties();
					}
				}
			}

		});

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

		viewer.getViewer().getTree().addKeyListener(new KeyListener() {

			@Override
			public void keyPressed(KeyEvent e) {
				if (e.keyCode == SWT.DEL) {
					// pressing the del button while having a constraint selected will delete it
					new DeleteConstraintAction(viewer.getViewer(), currentModel).run();
				} else if (((e.stateMask == (SWT.CTRL)) && (e.keyCode == F_BUTTON_PRESSED))) {
					// pressing CTRL + F will get you in the search box
					viewer.getSearchBox().setFocus();
				} else if (((e.stateMask == (SWT.CTRL)) && (e.keyCode == Z_BUTTON_PRESSED))) {
					// pressing CTRL + Z will undo operations
					try {
						PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().undo((IUndoContext) currentModel.getUndoContext(), null, null);
					} catch (final ExecutionException e1) {}
				} else if (((e.stateMask == (SWT.CTRL + SWT.SHIFT)) && (e.keyCode == Z_BUTTON_PRESSED))) {
					// pressing CTRL + SHIFT + Z will re do undo's
					try {
						PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().redo((IUndoContext) currentModel.getUndoContext(), null, null);
					} catch (final ExecutionException e1) {}
				} else if (e.keyCode == SWT.ESC) {
					// pressing the escape button will remove the focus or current selection
					viewer.getViewer().setSelection(null);
				}
			}

			@Override
			public void keyReleased(KeyEvent e) {}

		});
	}

	@Override
	public void dispose() {
		if (currentModel != null) {
			currentModel.removeListener(eventListener);
		}
		getSite().getPage().removePartListener(partListener);

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

	private final IEventListener eventListener = new IEventListener() {
		/**
		 * Reacts on observer of the current feature model
		 */
		@Override
		public void propertyChange(FeatureIDEEvent event) {
			if (FeatureModelUtil.getActiveFMEditor() != null) {
				if (refreshWithDelete == false) {
					checkForRefresh();
					refreshWithDelete = true;
				} else {
					checkForRefresh();
				}
			}
		}
	};

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

	public ConstraintViewSettingsMenu getSettingsMenu() {
		return settingsMenu;
	}
}
