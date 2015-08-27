/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors;

import static de.ovgu.featureide.fm.core.localization.StringTable.ALTERNATIVE;
import static de.ovgu.featureide.fm.core.localization.StringTable.ANALYZE_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.AND;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_DIAGRAM;
import static de.ovgu.featureide.fm.core.localization.StringTable.OR;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_CALCULATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_LAYOUT;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_NAME_TYPE;
import static de.ovgu.featureide.fm.core.localization.StringTable.UPDATING_FEATURE_MODEL_ATTRIBUTES;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.eclipse.core.commands.operations.ObjectUndoContext;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.draw2d.ConnectionLayer;
import org.eclipse.gef.DefaultEditDomain;
import org.eclipse.gef.EditDomain;
import org.eclipse.gef.EditPartViewer;
import org.eclipse.gef.GraphicalViewer;
import org.eclipse.gef.KeyHandler;
import org.eclipse.gef.KeyStroke;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.commands.CommandStack;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.editparts.ZoomManager;
import org.eclipse.gef.ui.actions.GEFActionConstants;
import org.eclipse.gef.ui.actions.ZoomInAction;
import org.eclipse.gef.ui.actions.ZoomOutAction;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ControlEvent;
import org.eclipse.swt.events.ControlListener;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.Preferences;
import de.ovgu.featureide.fm.core.ProfileManager;
import de.ovgu.featureide.fm.core.ProfileManager.Project.Profile;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.job.AStoppableJob;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.PlugInProfileSerializer;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AbstractAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AlternativeAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AndAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AutoLayoutConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ChangeFeatureDescriptionAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateCompoundAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateConstraintWithAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateLayerAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.DeleteAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.DeleteAllAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.EditConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ExportFeatureModelAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.HiddenAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.LayoutSelectionAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.LegendAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.LegendLayoutAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.MandatoryAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.MoveAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.NameTypeSelectionAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.OrAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.RenameAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ReverseOrderAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.SelectionAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ShowHiddenFeaturesAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.calculations.AutomatedCalculationsAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.calculations.ConstrainsCalculationsAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.calculations.FeaturesOnlyCalculationAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.calculations.RedundantConstrainsCalculationsAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.calculations.RunManualCalculationsAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.calculations.TautologyContraintsCalculationsAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors.ColorSelectedFeatureAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.GraphicalEditPartFactory;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutManager;
import de.ovgu.featureide.fm.ui.editors.keyhandler.FeatureDiagramEditorKeyHandler;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;
import de.ovgu.featureide.fm.ui.views.outline.FmOutlinePage;

/**
 * An editor based on the Graphical Editing Framework to view and edit feature
 * diagrams and cross-tree constraints.
 * 
 * @author Thomas Thuem
 */
public class FeatureDiagramEditor extends ScrollingGraphicalViewer implements GUIDefaults, PropertyConstants, PropertyChangeListener, IFeatureModelEditorPage {

	private static final String PAGE_TEXT = FEATURE_DIAGRAM;
	private static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureDiagramEditor";

	private FeatureModelEditor featureModelEditor;
	private ZoomManager zoomManager;

	private ScalableFreeformRootEditPart rootEditPart;

	private CreateLayerAction createLayerAction;
	private CreateCompoundAction createCompoundAction;
	private DeleteAction deleteAction;
	private DeleteAllAction deleteAllAction;
	private MandatoryAction mandatoryAction;
	private AbstractAction abstractAction;
	private ColorSelectedFeatureAction colorSelectedFeatureAction;
	private HiddenAction hiddenAction;
	private AndAction andAction;
	private OrAction orAction;
	private AlternativeAction alternativeAction;
	private RenameAction renameAction;
	private ChangeFeatureDescriptionAction changeFeatureDescriptionAction;

	private MoveAction moveStopAction;
	private MoveAction moveUpAction;
	private MoveAction moveRightAction;
	private MoveAction moveDownAction;
	private MoveAction moveLeftAction;

	private ShowHiddenFeaturesAction showHiddenFeaturesAction;

	private ZoomInAction zoomIn;
	private ZoomOutAction zoomOut;

	ExportFeatureModelAction exportFeatureModelAction;
	// legend action replaced with property page
	private LegendAction legendAction;
	private LegendLayoutAction legendLayoutAction;

	private EditConstraintAction editConstraintAction;
	private CreateConstraintAction createConstraintAction;
	private CreateConstraintWithAction createConstraintWithAction;

	private ReverseOrderAction reverseOrderAction;

	private List<LayoutSelectionAction> setLayoutActions;

	private List<NameTypeSelectionAction> setNameType;

	private AutoLayoutConstraintAction autoLayoutConstraintAction;

	private int index;

	private Job analyzeJob;

	private boolean waiting = false;

	private FeatureModelAnalyzer analyzer;

	public FeatureDiagramEditor(FeatureModelEditor featureModelEditor, Composite container) {
		super();
		this.featureModelEditor = featureModelEditor;

		createControl(container);
		initializeGraphicalViewer();
		setEditDomain(new DefaultEditDomain(featureModelEditor));

		zoomManager = rootEditPart.getZoomManager();
		zoomManager.setZoomLevels(new double[] { 0.05, 0.10, 0.25, 0.50, 0.75, 0.90, 1.00, 1.10, 1.25, 1.50, 2.00, 2.50, 3.00, 4.00 });
		FeatureUIHelper.setZoomManager(zoomManager);

		setKeyHandler(new FeatureDiagramEditorKeyHandler(this, getFeatureModel()));
	}

	private void initializeGraphicalViewer() {
		getControl().addControlListener(new ControlListener() {

			@Override
			/**
			 * used to remove the feature model when resizing the window
			 */
			public void controlResized(ControlEvent e) {
				// checks for null are necessary because we cannot prevent this
				// method may be called before the model is loaded correctly
				// (including positions in FeatureUIHelper)
				FeatureModel fm = getFeatureModel();
				if (fm == null)
					return;

				org.eclipse.draw2d.geometry.Point oldLoc = FeatureUIHelper.getLocation(fm.getRoot());
				if (oldLoc == null)
					return;
				internRefresh(true);

				org.eclipse.draw2d.geometry.Point newLoc = FeatureUIHelper.getLocation(fm.getRoot());
				if (newLoc == null)
					return;
				int difX = newLoc.x - oldLoc.x;

				if (!FMPropertyManager.isLegendHidden()) {
					moveLegend(fm, difX);
				}

			}

			/**
			 * moves the legend for the editor associated with feature model fm
			 * horizontally (used to move the legend along with the model when
			 * resizing the window)
			 * 
			 * @param fm
			 * @param delta
			 */
			private void moveLegend(FeatureModel fm, int delta) {
				org.eclipse.draw2d.geometry.Point location = FeatureUIHelper.getLegendFigure(fm).getLocation();
				FeatureUIHelper.getLegendFigure(fm).setLocation(new org.eclipse.draw2d.geometry.Point(location.x + delta, location.y));
			}

			@Override
			public void controlMoved(ControlEvent e) {
				// do nothing

			}
		});
		getControl().setBackground(FMPropertyManager.getDiagramBackgroundColor());
		setEditPartFactory(new GraphicalEditPartFactory());
		rootEditPart = new ScalableFreeformRootEditPart();
		((ConnectionLayer) rootEditPart.getLayer(LayerConstants.CONNECTION_LAYER)).setAntialias(SWT.ON);
		setRootEditPart(rootEditPart);
	}

	public FeatureModel getFeatureModel() {
		return featureModelEditor.getFeatureModel();
	}

	public void createActions() {
		FeatureModel featureModel = getFeatureModel();

		createLayerAction = new CreateLayerAction(this, featureModel, null);
		createCompoundAction = new CreateCompoundAction(this, featureModel, null);
		deleteAction = new DeleteAction(this, featureModel);

		colorSelectedFeatureAction = new ColorSelectedFeatureAction(this, featureModelEditor.getModelFile().getProject());

		deleteAllAction = new DeleteAllAction(this, featureModel);
		mandatoryAction = new MandatoryAction(this, featureModel);
		hiddenAction = new HiddenAction(this, featureModel);
		abstractAction = new AbstractAction(this, featureModel, (ObjectUndoContext) featureModel.getUndoContext());
		changeFeatureDescriptionAction = new ChangeFeatureDescriptionAction(this, featureModel, null);
		andAction = new AndAction(this, featureModel);
		orAction = new OrAction(this, featureModel);
		alternativeAction = new AlternativeAction(this, featureModel);
		renameAction = new RenameAction(this, featureModel, null);

		moveStopAction = new MoveAction(this, featureModel, null, MoveAction.STOP);
		moveUpAction = new MoveAction(this, featureModel, null, MoveAction.UP);
		moveRightAction = new MoveAction(this, featureModel, null, MoveAction.RIGHT);
		moveDownAction = new MoveAction(this, featureModel, null, MoveAction.DOWN);
		moveLeftAction = new MoveAction(this, featureModel, null, MoveAction.LEFT);

		new SelectionAction(this, featureModel);

		createConstraintAction = new CreateConstraintAction(this, featureModel);
		createConstraintWithAction = new CreateConstraintWithAction(this, featureModel);
		editConstraintAction = new EditConstraintAction(this, featureModel);
		reverseOrderAction = new ReverseOrderAction(this, featureModel);

		exportFeatureModelAction = new ExportFeatureModelAction(featureModelEditor);
		legendLayoutAction = new LegendLayoutAction(this, featureModel);
		legendAction = new LegendAction(this, featureModel);
		showHiddenFeaturesAction = new ShowHiddenFeaturesAction(this, featureModel);

		zoomIn = new ZoomInAction(zoomManager);
		zoomOut = new ZoomOutAction(zoomManager);

		setLayoutActions = new ArrayList<LayoutSelectionAction>(5);
		for (int i = 0; i < 5; i++) {
			setLayoutActions.add(new LayoutSelectionAction(this, featureModel, i, 0));
		}
		autoLayoutConstraintAction = new AutoLayoutConstraintAction(this, featureModel);

		setNameType = new ArrayList<NameTypeSelectionAction>(2);
		setNameType.add(new NameTypeSelectionAction(this, featureModel, 0));
		setNameType.add(new NameTypeSelectionAction(this, featureModel, 1));

	}

	public void createContextMenu(MenuManager menu) {
		menu.addMenuListener(new IMenuListener() {
			public void menuAboutToShow(IMenuManager manager) {
				FeatureDiagramEditor.this.fillContextMenu(manager);
			}
		});
		menu.createContextMenu(getControl());
		setContextMenu(menu);
		// the following line adds package explorer entries into our context
		// menu
		// getSite().registerContextMenu(menu, graphicalViewer);
	}

	public void createKeyBindings() {
		KeyHandler handler = getKeyHandler();

		handler.put(KeyStroke.getPressed(SWT.F2, 0), renameAction);
		handler.put(KeyStroke.getPressed(SWT.INSERT, 0), createLayerAction);

		handler.put(KeyStroke.getPressed(SWT.ARROW_UP, SWT.CTRL), moveUpAction);
		handler.put(KeyStroke.getPressed(SWT.ARROW_RIGHT, SWT.CTRL), moveRightAction);
		handler.put(KeyStroke.getPressed(SWT.ARROW_DOWN, SWT.CTRL), moveDownAction);
		handler.put(KeyStroke.getPressed(SWT.ARROW_LEFT, SWT.CTRL), moveLeftAction);

		handler.put(KeyStroke.getReleased(SWT.CTRL, SWT.CTRL), moveStopAction);
		handler.put(KeyStroke.getReleased(0, SWT.CTRL), moveStopAction);
		handler.put(KeyStroke.getReleased(SWT.CTRL, 0), moveStopAction);
	}

	private void fillContextMenu(IMenuManager menu) {
		IMenuManager subMenuCalculations = new MenuManager(SET_CALCULATIONS);
		subMenuCalculations.add(new AutomatedCalculationsAction(this, getFeatureModel()));
		subMenuCalculations.add(new RunManualCalculationsAction(this, getFeatureModel()));
		subMenuCalculations.add(new Separator());
		subMenuCalculations.add(new FeaturesOnlyCalculationAction(this, getFeatureModel()));
		subMenuCalculations.add(new ConstrainsCalculationsAction(this, getFeatureModel()));
		subMenuCalculations.add(new RedundantConstrainsCalculationsAction(this, getFeatureModel()));
		subMenuCalculations.add(new TautologyContraintsCalculationsAction(this, getFeatureModel()));

		showHiddenFeaturesAction.setChecked(getFeatureModel().getLayout().showHiddenFeatures());

		final IMenuManager subMenuLayout = new MenuManager(SET_LAYOUT);
		for (int i = 0; i < setLayoutActions.size(); i++) {
			subMenuLayout.add(setLayoutActions.get(i));
			if (i == 0) {
				subMenuLayout.add(autoLayoutConstraintAction);
				subMenuLayout.add(new Separator());
			}
			boolean isChosen = (i == getFeatureModel().getLayout().getLayoutAlgorithm());
			setLayoutActions.get(i).setChecked(isChosen);
			setLayoutActions.get(i).setEnabled(!isChosen);
		}

		final IMenuManager subMenuNameType = new MenuManager(SET_NAME_TYPE);
		for (NameTypeSelectionAction nameType : setNameType) {
			subMenuNameType.add(nameType);
			nameType.setChecked(false);
			nameType.setEnabled(true);
		}

		final NameTypeSelectionAction curNameType = setNameType.get(Preferences.getDefaultFeatureNameScheme());
		curNameType.setChecked(true);
		curNameType.setEnabled(false);

		autoLayoutConstraintAction.setEnabled(!getFeatureModel().getLayout().hasFeaturesAutoLayout());

		boolean connectionSelected = alternativeAction.isConnectionSelected();
		boolean mplModel = false;
		if (getFeatureModel() instanceof ExtendedFeatureModel) {
			ExtendedFeatureModel ext = (ExtendedFeatureModel) getFeatureModel();
			mplModel = ext.isMultiProductLineModel();
		}
		// only allow coloration if the active profile is not the default profile
		if (getCurrentProfile(getFeatureModel()).getActiveProfile().getName().equals("Default")) {
			colorSelectedFeatureAction.setEnabled(false);
		} 
		if (mplModel) {
			menu.add(subMenuLayout);
			menu.add(subMenuNameType);
		}
		// don't show menu to change group type of a feature in case a
		// connection line is selected
		else if ((createLayerAction.isEnabled() || createCompoundAction.isEnabled()) && !connectionSelected) {
			menu.add(createCompoundAction);
			menu.add(createLayerAction);
			menu.add(createConstraintWithAction);
			menu.add(renameAction);
			menu.add(deleteAction);
			menu.add(deleteAllAction);
			menu.add(new Separator());
			connectionEntrys(menu);
			menu.add(mandatoryAction);
			menu.add(abstractAction);
			menu.add(hiddenAction);
			menu.add(changeFeatureDescriptionAction);
			menu.add(new Separator());
			menu.add(subMenuLayout);
			menu.add(subMenuCalculations);
			menu.add(new Separator());
			menu.add(reverseOrderAction);
			menu.add(legendAction);
			menu.add(new Separator());
			menu.add(colorSelectedFeatureAction);		
			menu.add(new Separator());
		} else if (editConstraintAction.isEnabled() && !connectionSelected) {
			menu.add(createConstraintAction);
			menu.add(editConstraintAction);
			menu.add(deleteAction);
			menu.add(new Separator());
			menu.add(colorSelectedFeatureAction);
		} else if (legendLayoutAction.isEnabled()) {
			menu.add(legendLayoutAction);
			menu.add(legendAction);
		} else if (andAction.isEnabled() || orAction.isEnabled() || alternativeAction.isEnabled()) {
			connectionEntrys(menu);
		} else {
			menu.add(createConstraintAction);
			menu.add(new Separator());
			menu.add(subMenuLayout);
			menu.add(subMenuCalculations);
			menu.add(new Separator());
			menu.add(reverseOrderAction);
			menu.add(legendAction);
			menu.add(new Separator());
			menu.add(colorSelectedFeatureAction);
			
		}
		menu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
		if (featureModelEditor.getFeatureModel().hasHidden()) {
			menu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
			menu.add(showHiddenFeaturesAction);
		}
		menu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));

		// call of the FeatureDiagramExtensions (for features only)
		if ((createLayerAction.isEnabled() || createCompoundAction.isEnabled()) && !connectionSelected) {
			for (FeatureDiagramExtension extension : FeatureDiagramExtension.getExtensions()) {
				extension.extendContextMenu(menu, this);
			}
		}

		menu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
		menu.add(this.exportFeatureModelAction);
	}

	private void connectionEntrys(IMenuManager menu) {
		if (andAction.isEnabled() || orAction.isEnabled() || alternativeAction.isEnabled()) {
			boolean connectionSelected = alternativeAction.isConnectionSelected();
			if (andAction.isChecked()) {
				andAction.setText(AND);
				if (connectionSelected)
					orAction.setText("Or (Double Click)");
				else
					orAction.setText(OR);
				alternativeAction.setText(ALTERNATIVE);
			} else if (orAction.isChecked()) {
				andAction.setText(AND);
				orAction.setText(OR);
				if (connectionSelected)
					alternativeAction.setText("Alternative (Double Click)");
				else
					alternativeAction.setText(ALTERNATIVE);
			} else if (alternativeAction.isChecked()) {
				if (connectionSelected)
					andAction.setText("And (Double Click)");
				else
					andAction.setText(AND);
				orAction.setText(OR);
				alternativeAction.setText(ALTERNATIVE);
			}
			menu.add(andAction);
			menu.add(orAction);
			menu.add(alternativeAction);
			menu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
		}
	}

	private Profile getCurrentProfile(FeatureModel featureModel) {
		return ProfileManager.getProject(featureModel.xxxGetEclipseProjectPath(), PlugInProfileSerializer.FEATURE_PROJECT_SERIALIZER).getActiveProfile();
	}

	public IAction getDiagramAction(String workbenchActionID) {
		if (CreateLayerAction.ID.equals(workbenchActionID))
			return createLayerAction;
		if (CreateCompoundAction.ID.equals(workbenchActionID))
			return createCompoundAction;
		if (DeleteAction.ID.equals(workbenchActionID))
			return deleteAction;
		if (MandatoryAction.ID.equals(workbenchActionID))
			return mandatoryAction;
		if (AbstractAction.ID.equals(workbenchActionID))
			return abstractAction;
		if (HiddenAction.ID.equals(workbenchActionID))
			return hiddenAction;
		if (AndAction.ID.equals(workbenchActionID))
			return andAction;
		if (OrAction.ID.equals(workbenchActionID))
			return orAction;
		if (AlternativeAction.ID.equals(workbenchActionID))
			return alternativeAction;
		if (RenameAction.ID.equals(workbenchActionID))
			return renameAction;
		if (GEFActionConstants.ZOOM_IN.equals(workbenchActionID))
			return zoomIn;
		if (GEFActionConstants.ZOOM_OUT.equals(workbenchActionID))
			return zoomOut;
		return null;
	}

	public void internRefresh(boolean onlyLayout) {
		if (getContents() == null)
			return;

		// TODO is this necessary?
		FmOutlinePage outline = featureModelEditor.getOutlinePage();
		if (!onlyLayout && outline != null) {
			outline.setInput(getFeatureModel());
		}

		// refresh size of all feature figures
		if (!onlyLayout)
			getContents().refresh();

		// layout all features if autoLayout is enabled
		setLayout();

		// refresh position of all feature figures
		if (!onlyLayout)
			getContents().refresh();
	}

	public void reload() {
		setContents(getFeatureModel());
	}

	public void refresh() {
		if (getFeatureModel() == null || getFeatureModel().getRoot() == null || getContents() == null) {
			return;
		}

		internRefresh(false);
		if (waiting) {
			return;
		}
		waiting = true;
		final boolean runAnalysis = featureModelEditor.getFeatureModel().getAnalyser().runCalculationAutomatically
				&& featureModelEditor.getFeatureModel().getAnalyser().calculateFeatures;
		/**
		 * This extra job is necessary, else the UI will stop.
		 */
		Job waiter = new Job("Analyze feature model (waiting)") {

			@Override
			protected IStatus run(IProgressMonitor monitor) {

				try {
					if (analyzeJob != null && analyzer != null) {
						// waiting for analyzing job to finish
						analyzer.cancel(true);
						analyzeJob.join();
					}
				} catch (InterruptedException e) {
					FMUIPlugin.getDefault().logError(e);
				} finally {
					// avoid a dead lock
					if (analyzer != null) {
						analyzer.cancel(false);
					}
					waiting = false;
				}
				analyzeJob = new AStoppableJob(ANALYZE_FEATURE_MODEL) {
					@Override
					protected boolean work() throws Exception {
						if (waiting) {
							return true;
						}

						if (!runAnalysis) {
							UIJob refreshGraphics = new UIJob(UPDATING_FEATURE_MODEL_ATTRIBUTES) {

								@Override
								public IStatus runInUIThread(IProgressMonitor monitor) {
									for (Feature f : featureModelEditor.getFeatureModel().getFeatures()) {
										f.setFeatureStatus(FeatureStatus.NORMAL, true);
									}
									for (Constraint c : featureModelEditor.getFeatureModel().getConstraints()) {
										c.setConstraintAttribute(ConstraintAttribute.NORMAL, true);
									}
									getContents().refresh();
									return Status.OK_STATUS;
								}

							};
							refreshGraphics.setPriority(Job.SHORT);
							refreshGraphics.schedule();
							return true;
						}

						analyzer = getFeatureModel().getAnalyser();
						final HashMap<Object, Object> changedAttributes = analyzer.analyzeFeatureModel(new NullProgressMonitor());

						refreshGraphics(changedAttributes);

						return true;
					}
				};
				analyzeJob.setPriority(Job.LONG);
				analyzeJob.schedule();
				return Status.OK_STATUS;
			}
		};
		waiter.setPriority(Job.DECORATE);
		waiter.schedule();
	}

	/**
	 * Refreshes the colors of the feature model.
	 * 
	 * @param changedAttributes
	 *            Result of analyis to only refresh special features, or null if
	 *            all features should be refreshed.
	 */
	private void refreshGraphics(final HashMap<Object, Object> changedAttributes) {
		UIJob refreshGraphics = new UIJob(UPDATING_FEATURE_MODEL_ATTRIBUTES) {

			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				if (changedAttributes == null) {
					for (Feature f : featureModelEditor.getFeatureModel().getFeatures()) {
						f.fire(new PropertyChangeEvent(this, ATTRIBUTE_CHANGED, false, true));
					}
					for (Constraint c : featureModelEditor.getFeatureModel().getConstraints()) {
						c.fire(new PropertyChangeEvent(this, ATTRIBUTE_CHANGED, false, true));
					}
				} else {
					for (Object f : changedAttributes.keySet()) {
						if (f instanceof Feature) {
							((Feature) f).fire(new PropertyChangeEvent(this, ATTRIBUTE_CHANGED, Boolean.FALSE, true));
						} else if (f instanceof Constraint) {
							((Constraint) f).fire(new PropertyChangeEvent(this, ATTRIBUTE_CHANGED, false, true));
						}
					}
				}

				// call refresh to redraw legend
				getContents().refresh();
				return Status.OK_STATUS;
			}

		};
		refreshGraphics.setPriority(Job.SHORT);
		refreshGraphics.schedule();
	}

	public void setLayout() {

		FeatureDiagramLayoutManager layoutManager;
		FeatureModel featureModel = getFeatureModel();

		layoutManager = FeatureDiagramLayoutHelper.getLayoutManager(featureModel.getLayout().getLayoutAlgorithm(), featureModel);

		int previousLayout = featureModel.getLayout().getLayoutAlgorithm();

		for (int i = 0; i < setLayoutActions.size(); i++) {
			setLayoutActions.set(i, new LayoutSelectionAction(this, featureModel, i, previousLayout));
		}

		Point size = getControl().getSize();

		layoutManager.setControlSize(size.x, size.y);
		layoutManager.layout(featureModel);

	}

	@SuppressWarnings("rawtypes")
	public Object getAdapter(Class adapter) {
		if (GraphicalViewer.class.equals(adapter) || EditPartViewer.class.equals(adapter))
			return this;
		if (ZoomManager.class.equals(adapter)) {
			return zoomManager;
		}
		if (CommandStack.class.equals(adapter))
			return getEditDomain().getCommandStack();
		if (EditDomain.class.equals(adapter))
			return getEditDomain();
		return null;
	}

	public void propertyChange(PropertyChangeEvent event) {
		String prop = event.getPropertyName();
		if (MODEL_DATA_CHANGED.equals(prop)) {
			reload();
			refresh();
			featureModelEditor.setPageModified(true);
		} else if (MODEL_DATA_LOADED.equals(prop)) {
			refresh();
		} else if (MODEL_LAYOUT_CHANGED.equals(prop)) {
			featureModelEditor.setPageModified(true);
		} else if (REDRAW_DIAGRAM.equals(prop)) {
			getControl().setBackground(FMPropertyManager.getDiagramBackgroundColor());
			reload();
			refreshGraphics(null);
		} else if (REFRESH_ACTIONS.equals(prop)) {
			// additional actions can be refreshed here
			// legendAction.refresh();
			legendLayoutAction.refresh();
		} else if (LEGEND_LAYOUT_CHANGED.equals(prop)) {
			legendLayoutAction.refresh();
		}

		for (IFeatureModelEditorPage page : featureModelEditor.extensionPages) {
			page.propertyChange(event);
		}
	}

	public void setIndex(int index) {
		this.index = index;
	}

	public int getIndex() {
		return index;
	}

	public String getPageText() {
		return PAGE_TEXT;
	}

	@Override
	public void initEditor() {
		createContextMenu();
		createActions();
		createKeyBindings();
	}

	private void createContextMenu() {
		MenuManager menu = new MenuManager("#PopupMenu");
		menu.setRemoveAllWhenShown(true);
		createContextMenu(menu);
	}

	@Override
	public void setFeatureModelEditor(FeatureModelEditor featureModelEditor) {
		this.featureModelEditor = featureModelEditor;
	}

	@Override
	public IFeatureModelEditorPage getPage(Composite container) {
		return new FeatureDiagramEditor(featureModelEditor, container);
	}

	@Override
	public void doSave(IProgressMonitor monitor) {

	}

	@Override
	public boolean allowPageChange(int newPage) {
		return true;
	}

	@Override
	public void pageChangeFrom(int newPage) {

	}

	@Override
	public void pageChangeTo(int oldPage) {

	}

	@Override
	public String getID() {
		return ID;
	}

	/**
	 * Stops the analyzing job when the editor is closed.
	 */
	public void dispose() {
		if (analyzeJob != null) {
			analyzeJob.cancel();
		}
	}

}
