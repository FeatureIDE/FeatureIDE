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

import org.eclipse.jface.dialogs.IPageChangedListener;
import org.eclipse.jface.dialogs.PageChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel.FeatureModelElementTrace;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelReason;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;
import de.ovgu.featureide.fm.ui.utils.FeatureModelUtil;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewDoubleClickListener;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewKeyListener;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewPartListener;
import de.ovgu.featureide.fm.ui.views.constraintview.listener.ConstraintViewSelectionChangedListener;
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
public class ConstraintViewController extends ViewPart implements GUIDefaults {
	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.ConstraintView";
	private static final Integer FEATURE_EDIT_PART_OFFSET = 17;
	private ConstraintView viewer;
	private IFeatureModel currentModel;
	private ConstraintViewPartListener partListener;
	private ConstraintViewSettingsMenu settingsMenu;
	private Explanation<?> explanation;

	boolean refreshWithDelete = true;
	boolean constraintsHidden = false;

	private String searchText = "";

	private final IEventListener eventListener = new IEventListener() {
		/**
		 * Reacts on observer of the current feature model
		 */
		@Override
		public void propertyChange(FeatureIDEEvent event) {
			switch (event.getEventType()) {
			case ACTIVE_EXPLANATION_CHANGED:
				if (FeatureModelUtil.getActiveFMEditor() != null) {
					if (!isRefreshWithDelete()) {
						checkForRefresh();
						setRefreshWithDelete(true);
					} else {
						checkForRefresh();
					}
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
			if (event.getSelectedPage() instanceof FeatureDiagramEditor) {
				refreshView(FeatureModelUtil.getFeatureModel());
			} else {
				viewer.addNoFeatureModelItem();
			}
		}
	};

	/**
	 * Standard SWT initialize called after construction.
	 */
	@Override
	public void createPartControl(Composite parent) {
		parent.setLayout(new FillLayout(SWT.HORIZONTAL));
		viewer = new ConstraintView(parent);
		viewer.getSearchBox().addModifyListener(searchListener);
		addListener();
		if (FeatureModelUtil.getActiveFMEditor() != null) {
			addPageChangeListener(FeatureModelUtil.getActiveFMEditor());
			refreshView(FeatureModelUtil.getFeatureModel());
		} else {
			viewer.addNoFeatureModelItem();
		}
		settingsMenu = new ConstraintViewSettingsMenu(this);
		new ConstraintViewContextMenu(this);
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
	 * Show constraints containing the selected feature and those which are part of the current explanation
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
							if (constraint.getObject() == c) {
								boolean additem = true;
								final TreeItem[] treeitems = viewer.getViewer().getTree().getItems();
								for (int i = 0; i < treeitems.length; i++) {
									// check for duplicate constraints before adding
									if (treeitems[i].getData() == c) {
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
			final String lazyDescription = constraint.getDescription().toLowerCase().replaceAll("\n", " ").replaceAll("\r", " ");
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
	 */
	public void addPageChangeListener(FeatureModelEditor fme) {
		fme.addPageChangedListener(pageChangeListener);
	}

	/**
	 * adding Listener to the tree viewer
	 */
	private void addListener() {
		viewer.getViewer().addSelectionChangedListener(new ConstraintViewSelectionChangedListener(this));
		viewer.getViewer().addDoubleClickListener(new ConstraintViewDoubleClickListener(this));
		viewer.getViewer().getTree().addKeyListener(new ConstraintViewKeyListener(this));
		partListener = new ConstraintViewPartListener(this);
		getSite().getPage().addPartListener(partListener);
	}

	@Override
	public void dispose() {
		// remove eventListener from current FeatureModel
		if (currentModel != null) {
			currentModel.removeListener(eventListener);
		}
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
	public void setConstraintsHidden(boolean hideConstraints) {
		if ((FeatureModelUtil.getActiveFMEditor() != null)) {
			FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().setConstraintsHidden(hideConstraints);
			FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel().redrawDiagram();
			constraintsHidden = hideConstraints;
		}
	}

	public boolean isConstraintsHidden() {
		return constraintsHidden;
	}

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

	public boolean isRefreshWithDelete() {
		return refreshWithDelete;
	}

	public void setRefreshWithDelete(Boolean refreshWithDelete) {
		this.refreshWithDelete = refreshWithDelete;
	}
}
