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
package de.ovgu.featureide.fm.ui.editors;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADJUST_MODEL_TO_EDITOR;
import static de.ovgu.featureide.fm.core.localization.StringTable.ALTERNATIVE;
import static de.ovgu.featureide.fm.core.localization.StringTable.ANALYZE_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.AND;
import static de.ovgu.featureide.fm.core.localization.StringTable.DOUBLE_CLICK;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_DIAGRAM;
import static de.ovgu.featureide.fm.core.localization.StringTable.OR;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_CALCULATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_LAYOUT;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_NAME_TYPE;
import static de.ovgu.featureide.fm.core.localization.StringTable.UPDATING_FEATURE_MODEL_ATTRIBUTES;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.gef.EditDomain;
import org.eclipse.gef.EditPartViewer;
import org.eclipse.gef.GraphicalViewer;
import org.eclipse.gef.KeyHandler;
import org.eclipse.gef.KeyStroke;
import org.eclipse.gef.commands.CommandStack;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;
import org.eclipse.gef.editparts.ZoomManager;
import org.eclipse.gef.ui.actions.GEFActionConstants;
import org.eclipse.gef.ui.actions.ZoomInAction;
import org.eclipse.gef.ui.actions.ZoomOutAction;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.action.ToolBarManager;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.Features;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelReason;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.AFileManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.manager.IFileManager;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.JobStartingStrategy;
import de.ovgu.featureide.fm.core.job.JobToken;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeatureModelFormat;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AbstractAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AdjustModelToEditorSizeAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AlternativeAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AndAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AutoLayoutConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CalculateDependencyAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ChangeFeatureDescriptionAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CollapseAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CollapseAllAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CollapseSiblingsAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateCompoundAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateConstraintWithAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateLayerAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.DeleteAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.DeleteAllAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.EditConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ExpandAllAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ExpandConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ExportFeatureModelAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.FocusOnExplanationAction;
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
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ShowCollapsedConstraintsAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ShowHiddenFeaturesAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.calculations.AutomatedCalculationsAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.calculations.ConstrainsCalculationsAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.calculations.FeaturesOnlyCalculationAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.calculations.RunManualCalculationsAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors.SetFeatureColorAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureCellEditorLocator;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureLabelEditManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelElementEditPart;
import de.ovgu.featureide.fm.ui.editors.keyhandler.FeatureDiagramEditorKeyHandler;
import de.ovgu.featureide.fm.ui.editors.mousehandler.FeatureDiagramEditorMouseHandler;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;
import de.ovgu.featureide.fm.ui.utils.SearchField;

/**
 * An editor based on the Graphical Editing Framework to view and edit feature diagrams and cross-tree constraints.
 *
 * @author Thomas Thuem
 * @author Sebastian Krieter
 */
public class FeatureDiagramEditor extends FeatureModelEditorPage implements GUIDefaults, IEventListener {

	private static final String PAGE_TEXT = FEATURE_DIAGRAM;
	private static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureDiagramEditor";
	private static final IPersistentFormat<IGraphicalFeatureModel> format = new GraphicalFeatureModelFormat();

	private final Path extraPath;
	private final IGraphicalFeatureModel graphicalFeatureModel;

	private final FeatureDiagramViewer viewer;

	private Label infoLabel;

	private CalculateDependencyAction calculateDependencyAction;
	private CreateLayerAction createLayerAction;
	private CreateCompoundAction createCompoundAction;
	private DeleteAction deleteAction;
	private DeleteAllAction deleteAllAction;
	private MandatoryAction mandatoryAction;
	private AbstractAction abstractAction;
	private CollapseAction collapseAction;
	private CollapseSiblingsAction collapseFeaturesAction;
	private CollapseAllAction collapseAllAction;
	private ExpandAllAction expandAllAction;
	private FocusOnExplanationAction focusOnExplanationAction;
	private SetFeatureColorAction colorSelectedFeatureAction;
	private AdjustModelToEditorSizeAction adjustModelToEditorSizeAction;
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
	private ShowCollapsedConstraintsAction showCollapsedConstraintsAction;

	private ZoomInAction zoomIn;
	private ZoomOutAction zoomOut;

	private ExportFeatureModelAction exportFeatureModelAction;
	private LegendAction legendAction;
	private LegendLayoutAction legendLayoutAction;

	private EditConstraintAction editConstraintAction;
	private CreateConstraintAction createConstraintAction;
	private CreateConstraintWithAction createConstraintWithAction;
	private ExpandConstraintAction expandConstraintAction;

	private ReverseOrderAction reverseOrderAction;
	private AutoLayoutConstraintAction autoLayoutConstraintAction;

	private List<Action> setLayoutActions, calculationActions;
	private List<Action> setNameTypeActions;
	private final List<Action> actions = new ArrayList<>();

	private int index;

	private final JobToken analysisToken = LongRunningWrapper.createToken(JobStartingStrategy.CANCEL_WAIT_ONE);

	private FeatureModelAnalyzer analyzer;

	FeatureDiagramEditorKeyHandler editorKeyHandler;

	/** The currently active explanation. */
	private Explanation<?> activeExplanation;

	/**
	 * Constructor. Handles editable and read-only feature models.
	 *
	 * @param featureModelEditor the FeatureModelEditor
	 * @param container Composite which contains the feature model
	 * @param fm The feature model
	 * @param isEditable True, if feature model is editable. False, if feature model is read-only
	 */
	public FeatureDiagramEditor(IFileManager<IFeatureModel> fmManager, boolean isEditable) {
		super(fmManager);

		graphicalFeatureModel = getGrapicalFeatureModel(getFeatureModel());

		// 1. Check if the fmManager exists and is not a VirtualFileManager instance (path returns null)
		// 2. read-only feature model is currently only a view on the editable feature model and not persistent
		if ((fmManager != null) && (fmManager.getPath() != null)) {
			extraPath = AFileManager.constructExtraPath(fmManager.getPath(), format);
			FileHandler.load(extraPath, graphicalFeatureModel, format);
			fmManager.addListener(this);
		} else {
			extraPath = null;
		}

		viewer = new FeatureDiagramViewer(graphicalFeatureModel, this);
		createActions();

		FeatureColorManager.addListener(this);
	}

	public static GraphicalFeatureModel getGrapicalFeatureModel(IFeatureModel featureModel) {
		final GraphicalFeatureModel graphicalFeatureModel = new GraphicalFeatureModel(featureModel);
		graphicalFeatureModel.init();
		return graphicalFeatureModel;
	}

	private void createActions() {
		final IFeatureModel featureModel = getFeatureModel();
		actions.clear();

		// FM structure modify actions
		createLayerAction = addAction(new CreateLayerAction(viewer, featureModel));
		createCompoundAction = addAction(new CreateCompoundAction(viewer, featureModel));
		deleteAction = addAction(new DeleteAction(viewer, featureModel));
		deleteAllAction = addAction(new DeleteAllAction(viewer, featureModel));
		moveStopAction = addAction(new MoveAction(viewer, graphicalFeatureModel, null, MoveAction.STOP));
		moveUpAction = addAction(new MoveAction(viewer, graphicalFeatureModel, null, MoveAction.UP));
		moveRightAction = addAction(new MoveAction(viewer, graphicalFeatureModel, null, MoveAction.RIGHT));
		moveDownAction = addAction(new MoveAction(viewer, graphicalFeatureModel, null, MoveAction.DOWN));
		moveLeftAction = addAction(new MoveAction(viewer, graphicalFeatureModel, null, MoveAction.LEFT));
		reverseOrderAction = addAction(new ReverseOrderAction(viewer, graphicalFeatureModel));

		// Collapse/Expand actions
		collapseAction = addAction(new CollapseAction(viewer, graphicalFeatureModel));
		collapseFeaturesAction = addAction(new CollapseSiblingsAction(viewer, graphicalFeatureModel));
		collapseAllAction = addAction(new CollapseAllAction(graphicalFeatureModel));
		focusOnExplanationAction = addAction(new FocusOnExplanationAction(getGraphicalFeatureModel()));
		expandAllAction = addAction(new ExpandAllAction(graphicalFeatureModel));
		expandConstraintAction = addAction(new ExpandConstraintAction(viewer, graphicalFeatureModel));
		adjustModelToEditorSizeAction = addAction(new AdjustModelToEditorSizeAction(this, graphicalFeatureModel, ADJUST_MODEL_TO_EDITOR));
		showCollapsedConstraintsAction = addAction(new ShowCollapsedConstraintsAction(viewer, graphicalFeatureModel));

		// Feature property actions
		mandatoryAction = addAction(new MandatoryAction(viewer, featureModel));
		abstractAction = addAction(new AbstractAction(viewer, featureModel));
		hiddenAction = addAction(new HiddenAction(viewer, featureModel));
		andAction = addAction(new AndAction(viewer, featureModel));
		orAction = addAction(new OrAction(viewer, featureModel));
		alternativeAction = addAction(new AlternativeAction(viewer, featureModel));
		renameAction = addAction(new RenameAction(viewer, featureModel, null));
		changeFeatureDescriptionAction = addAction(new ChangeFeatureDescriptionAction(viewer, featureModel, null));

		// Constraint actions
		createConstraintAction = addAction(new CreateConstraintAction(viewer, featureModel));
		createConstraintWithAction = addAction(new CreateConstraintWithAction(viewer, featureModel));
		editConstraintAction = addAction(new EditConstraintAction(viewer, featureModel));

		// View actions
		legendLayoutAction = addAction(new LegendLayoutAction(viewer, graphicalFeatureModel));
		legendAction = addAction(new LegendAction(viewer, graphicalFeatureModel));
		showHiddenFeaturesAction = addAction(new ShowHiddenFeaturesAction(viewer, graphicalFeatureModel));
		setNameTypeActions = new ArrayList<>(2);
		setNameTypeActions.add(addAction(new NameTypeSelectionAction(graphicalFeatureModel, 0, 1)));
		setNameTypeActions.add(addAction(new NameTypeSelectionAction(graphicalFeatureModel, 1, 0)));

		// Calculation actions
		calculateDependencyAction = addAction(new CalculateDependencyAction(viewer, featureModel));
		calculationActions = new ArrayList<>(4);
		calculationActions.add(addAction(new AutomatedCalculationsAction(viewer, getFeatureModel())));
		calculationActions.add(addAction(new RunManualCalculationsAction(viewer, getFeatureModel())));
		calculationActions.add(addAction(new FeaturesOnlyCalculationAction(viewer, getFeatureModel())));
		calculationActions.add(addAction(new ConstrainsCalculationsAction(viewer, getFeatureModel())));

		// Zoom actions
		zoomIn = addAction(new ZoomInAction(viewer.getZoomManager()));
		zoomOut = addAction(new ZoomOutAction(viewer.getZoomManager()));

		// Layout actions
		autoLayoutConstraintAction = addAction(new AutoLayoutConstraintAction(viewer, graphicalFeatureModel));
		setLayoutActions = new ArrayList<>(9);
		for (int i = 0; i < 9; i++) {
			setLayoutActions.add(addAction(new LayoutSelectionAction(graphicalFeatureModel, i)));
		}

		// Other actions
		exportFeatureModelAction = addAction(new ExportFeatureModelAction(this));
		colorSelectedFeatureAction = addAction(new SetFeatureColorAction(viewer, getFeatureModel()));

		viewer.addSelectionChangedListener(new SelectionAction(graphicalFeatureModel));
	}

	private <T extends Action> T addAction(T action) {
		actions.add(action);
		return action;
	}

	@Override
	public void createPartControl(Composite parent) {
		parent.setBackground(FMPropertyManager.getDiagramBackgroundColor());
		// parent composite
		GridLayout gridLayout = new GridLayout(1, false);
		gridLayout.verticalSpacing = 0;
		gridLayout.horizontalSpacing = 4;
		gridLayout.marginHeight = 0;
		gridLayout.marginWidth = 0;
		parent.setLayout(gridLayout);

		// 1. sub composite
		GridData gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = false;
		gridData.verticalAlignment = SWT.TOP;
		gridLayout = new GridLayout(3, false);
		gridLayout.marginHeight = 0;
		gridLayout.marginWidth = 0;
		gridLayout.marginLeft = 4;
		final Composite compositeTop = new Composite(parent, SWT.NONE);
		compositeTop.setLayout(gridLayout);
		compositeTop.setLayoutData(gridData);

		// TODO implement update function for info label
		// info label
		final Composite compositeInfoLabel = new Composite(compositeTop, SWT.NONE);
		gridLayout = new GridLayout(2, false);
		gridLayout.marginHeight = 0;
		gridLayout.marginWidth = 0;
		compositeInfoLabel.setLayout(gridLayout);
		gridData = new GridData();
		gridData.horizontalAlignment = SWT.LEFT;
		gridData.grabExcessHorizontalSpace = false;
		gridData.verticalAlignment = SWT.CENTER;
		final Label label = new Label(compositeInfoLabel, SWT.NONE);
		label.setText("");
		label.setLayoutData(gridData);

		gridData = new GridData();
		gridData.horizontalAlignment = SWT.LEFT;
		gridData.grabExcessHorizontalSpace = true;
		gridData.verticalAlignment = SWT.CENTER;
		gridData.widthHint = 100;
		infoLabel = new Label(compositeInfoLabel, SWT.NONE);
		infoLabel.setText("");
		infoLabel.setLayoutData(gridData);

		new SearchField<>(compositeTop, viewer);

		gridData = new GridData();
		gridData.horizontalAlignment = SWT.RIGHT;
		gridData.verticalAlignment = SWT.CENTER;
		gridData.grabExcessHorizontalSpace = false;
		final ToolBar toolbar = new ToolBar(compositeTop, SWT.FLAT | SWT.WRAP | SWT.RIGHT);
		final ToolBarManager toolBarManager = new ToolBarManager(toolbar);
		toolbar.setLayoutData(gridData);

		// 1. Collapse/Expand/Adjust
		toolBarManager.add(collapseAllAction);
		toolBarManager.add(expandAllAction);
		toolBarManager.add(adjustModelToEditorSizeAction);
		toolBarManager.add(new Separator());

		// 3. Layout
		toolBarManager.add(createLayoutMenuManager(false));
		toolBarManager.add(new Separator());

		// 3. Analysis
		toolBarManager.add(createCalculationsMenuManager(false));
		toolBarManager.add(new Separator());

		// 4. Viewer Options

		toolBarManager.update(true);

		// 2. sub composite
		gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.verticalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		final Composite compositeBottom = new Composite(parent, SWT.BORDER);
		compositeBottom.setLayout(new FillLayout());
		compositeBottom.setLayoutData(gridData);

		viewer.createControl(compositeBottom);
		viewer.setContents(graphicalFeatureModel);
		viewer.getControl().addControlListener(viewer.createControlListener());
		viewer.getControl().setBackground(FMPropertyManager.getDiagramBackgroundColor());

		viewer.addSelectionChangedListener(new ISelectionChangedListener() {
			@Override
			public void selectionChanged(SelectionChangedEvent event) {
				setActiveExplanation();
			}
		});
	}

	/**
	 * Sets the active explanation depending on the current selection.
	 */
	protected void setActiveExplanation() {
		ModelElementEditPart primary = null;
		for (final Object selected : viewer.getSelectedEditParts()) {
			if (!(selected instanceof ModelElementEditPart)) {
				continue;
			}
			if (primary != null) { // multiple selected
				setActiveExplanation(null);
				return;
			}
			primary = (ModelElementEditPart) selected;
		}
		if (primary == null) { // none selected
			setActiveExplanation(null);
			return;
		}
		final FeatureModelAnalyzer analyser = getFeatureModel().getAnalyser();
		setActiveExplanation(analyser.valid() ? analyser.getExplanation(primary.getModel().getObject()) : analyser.getVoidFeatureModelExplanation());
	}

	/**
	 * Sets the currently active explanation. Notifies the listeners of the change.
	 *
	 * @param activeExplanation the new active explanation
	 */
	public void setActiveExplanation(Explanation<?> activeExplanation) {
		final Explanation<?> oldActiveExplanation = this.activeExplanation;
		this.activeExplanation = activeExplanation;
		graphicalFeatureModel.setActiveExplanation(activeExplanation);
		getFeatureModel().fireEvent(new FeatureIDEEvent(this, EventType.ACTIVE_EXPLANATION_CHANGED, oldActiveExplanation, activeExplanation));
	}

	/**
	 * Returns the currently active explanation.
	 *
	 * @return the currently active explanation.
	 */
	public Explanation<?> getActiveExplanation() {
		return activeExplanation;
	}

	public void analyzeFeatureModel() {
		if ((getFeatureModel() == null) || (getFeatureModel().getStructure().getRoot() == null) || (viewer.getContents() == null)) {
			return;
		}
		final boolean runAnalysis = getFeatureModel().getAnalyser().runCalculationAutomatically && getFeatureModel().getAnalyser().calculateFeatures;
		final IRunner<Boolean> analyzeJob = LongRunningWrapper.getRunner(new LongRunningMethod<Boolean>() {
			@Override
			public Boolean execute(IMonitor monitor) throws Exception {
				// TODO could be combined with analysis results
				for (final IFeature f : getFeatureModel().getFeatures()) {
					f.getProperty().setFeatureStatus(FeatureStatus.NORMAL, false);
				}
				for (final IConstraint c : getFeatureModel().getConstraints()) {
					c.setConstraintAttribute(ConstraintAttribute.NORMAL, false);
				}
				refreshGraphics(null);

				if (!runAnalysis) {
					return true;
				}

				analyzer = getFeatureModel().getAnalyser();
				final HashMap<Object, Object> changedAttributes = analyzer.analyzeFeatureModel(monitor);
				refreshGraphics(changedAttributes);
				return true;
			}
		}, ANALYZE_FEATURE_MODEL);
		analyzeJob.setPriority(Job.LONG);
		LongRunningWrapper.startJob(analysisToken, analyzeJob);
	}

	/**
	 * Refreshes the colors of the feature model.
	 *
	 * @param changedAttributes Result of analysis to only refresh special features, or null if all features should be refreshed.
	 */
	private void refreshGraphics(final HashMap<Object, Object> changedAttributes) {
		final UIJob refreshGraphics = new UIJob(UPDATING_FEATURE_MODEL_ATTRIBUTES) {

			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				boolean needsRelayout = false;
				if (changedAttributes == null) {
					for (final IFeature f : getFeatureModel().getVisibleFeatures(graphicalFeatureModel.getLayout().showHiddenFeatures())) {
						f.fireEvent(new FeatureIDEEvent(this, EventType.ATTRIBUTE_CHANGED, false, true));
						graphicalFeatureModel.getGraphicalFeature(f).update(FeatureIDEEvent.getDefault(EventType.ATTRIBUTE_CHANGED));
					}
					for (final IGraphicalConstraint c : graphicalFeatureModel.getVisibleConstraints()) {
						c.getObject().fireEvent(new FeatureIDEEvent(this, EventType.ATTRIBUTE_CHANGED, false, true));
						c.update(FeatureIDEEvent.getDefault(EventType.ATTRIBUTE_CHANGED));
					}
				} else {
					for (final Object f : changedAttributes.keySet()) {
						if (f instanceof IFeature) {
							final IFeature feature = (IFeature) f;
							if (changedAttributes.get(feature) instanceof FeatureStatus) {
								final FeatureStatus status = (FeatureStatus) changedAttributes.get(f);
								feature.getProperty().setFeatureStatus(status);
								feature.fireEvent(new FeatureIDEEvent(this, EventType.ATTRIBUTE_CHANGED, Boolean.FALSE, true));
								graphicalFeatureModel.getGraphicalFeature(feature).update(FeatureIDEEvent.getDefault(EventType.ATTRIBUTE_CHANGED));
								if (feature.getStructure().isRoot()) {
									needsRelayout = true;
								}
								if (feature.getStructure().isRoot() && (feature.getProperty().getFeatureStatus() == FeatureStatus.DEAD)) {
									// When root is dead refresh all subfeatures
									for (final IFeature subFeature : getFeatureModel()
											.getVisibleFeatures(graphicalFeatureModel.getLayout().showHiddenFeatures())) {
										subFeature.fireEvent(new FeatureIDEEvent(this, EventType.ATTRIBUTE_CHANGED, Boolean.FALSE, true));
										graphicalFeatureModel.getGraphicalFeature(subFeature).update(FeatureIDEEvent.getDefault(EventType.ATTRIBUTE_CHANGED));
									}
								}
							}
						} else if (f instanceof IConstraint) {
							((IConstraint) f).fireEvent(new FeatureIDEEvent(this, EventType.ATTRIBUTE_CHANGED, false, true));
							graphicalFeatureModel.getGraphicalConstraint((IConstraint) f).update(FeatureIDEEvent.getDefault(EventType.ATTRIBUTE_CHANGED));
						}
					}
				}
				if (needsRelayout) {
					getFeatureModel().fireEvent(new FeatureIDEEvent(null, EventType.LOCATION_CHANGED));
				}
				setActiveExplanation();
				viewer.getContents().refresh();
				return Status.OK_STATUS;
			}
		};
		refreshGraphics.setPriority(Job.SHORT);
		refreshGraphics.schedule();
	}

	@Override
	public <T> T getAdapter(Class<T> adapter) {
		if (GraphicalViewer.class.equals(adapter) || EditPartViewer.class.equals(adapter)) {
			return (T) adapter.cast(getViewer());
		}
		if (ZoomManager.class.equals(adapter)) {
			return adapter.cast(viewer.getZoomManager());
		}
		if (CommandStack.class.equals(adapter)) {
			return adapter.cast(viewer.getEditDomain().getCommandStack());
		}
		if (EditDomain.class.equals(adapter)) {
			return adapter.cast(viewer.getEditDomain());
		}
		return null;
	}

	@Override
	@SuppressWarnings("unchecked")
	public void propertyChange(FeatureIDEEvent event) {
		final EventType prop = event.getEventType();
		switch (prop) {
		case FEATURE_ADD_ABOVE:
			IFeature newCompound = null;
			if ((event.getNewValue() != null) && (event.getNewValue() instanceof IFeature)) {
				newCompound = (IFeature) event.getNewValue();
				for (final IGraphicalFeature child : graphicalFeatureModel.getGraphicalFeature(newCompound)
						.getGraphicalChildren(graphicalFeatureModel.getLayout().showHiddenFeatures())) {
					child.update(FeatureIDEEvent.getDefault(EventType.PARENT_CHANGED));
				}
				final IFeature oldParent = (IFeature) event.getOldValue();
				if (oldParent != null) {
					final IGraphicalFeature parent = graphicalFeatureModel.getGraphicalFeature(oldParent);
					parent.update(FeatureIDEEvent.getDefault(EventType.CHILDREN_CHANGED));
					// new Feature is not root so update all childs from old Parent, which include the new feature and his children
					viewer.refreshChildAll(oldParent);
				} else {
					// new Feature is root so update all childs from root
					viewer.refreshChildAll(newCompound);
				}
			}
			viewer.internRefresh(false);
			setDirty(true);
			analyzeFeatureModel();
			break;
		case FEATURE_ADD:
			((AbstractGraphicalEditPart) viewer.getEditPartRegistry().get(graphicalFeatureModel)).refresh();
			setDirty(true);
			final IFeature newFeature = (IFeature) event.getNewValue();
			final IFeature parent = (IFeature) event.getOldValue();
			final IFeatureModel fm = (IFeatureModel) event.getSource();
			if ((parent != null) && (parent != newFeature)) {
				// Uncollapse if collapsed
				final IGraphicalFeature graphicalParent = graphicalFeatureModel.getGraphicalFeature(parent);
				if (graphicalParent.isCollapsed()) {
					graphicalParent.setCollapsed(false);
					for (final IFeatureStructure featureStructure : parent.getStructure().getChildren()) {
						if (featureStructure != newFeature.getStructure()) {
							final IGraphicalFeature graphicalFeatureStructure = graphicalFeatureModel.getGraphicalFeature(featureStructure.getFeature());
							graphicalFeatureStructure.setCollapsed(true);
						}
					}
					fm.fireEvent(new FeatureIDEEvent(parent, EventType.COLLAPSED_CHANGED, null, null));
				}
				// Draws the connections
				if (parent.getStructure().hasChildren()) {
					for (final IGraphicalFeature child : FeatureUIHelper.getGraphicalChildren(newFeature, graphicalFeatureModel)) {
						child.update(FeatureIDEEvent.getDefault(EventType.PARENT_CHANGED));
					}
				}
				graphicalFeatureModel.getGraphicalFeature(parent).update(new FeatureIDEEvent(newFeature, EventType.CHILDREN_CHANGED));
			} else if ((parent != null) && (parent == newFeature)) {
				if (parent.getStructure().hasChildren()) {
					for (final IGraphicalFeature child : FeatureUIHelper.getGraphicalChildren(newFeature, graphicalFeatureModel)) {
						child.update(FeatureIDEEvent.getDefault(EventType.PARENT_CHANGED));
					}
				}
			}

			final IGraphicalFeature newGraphicalFeature = graphicalFeatureModel.getGraphicalFeature(newFeature);
			final FeatureEditPart newEditPart = (FeatureEditPart) viewer.getEditPartRegistry().get(newGraphicalFeature);
			if (newEditPart != null) {// TODO move to FeatureEditPart
				newEditPart.activate();
				viewer.select(newEditPart);
				// open the renaming command
				new FeatureLabelEditManager(newEditPart, TextCellEditor.class, new FeatureCellEditorLocator(newEditPart.getFigure()), getFeatureModel()).show();
			}
			viewer.internRefresh(true);
			analyzeFeatureModel();
			break;
		case FEATURE_NAME_CHANGED:
			final String newValue = (String) event.getNewValue();
			final IFeature feature = graphicalFeatureModel.getFeatureModel().getFeature(newValue);
			final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(feature);
			graphicalFeature.update(event);
			final FeatureEditPart part = (FeatureEditPart) viewer.getEditPartRegistry().get(graphicalFeature);
			if (part != null) {// TODO move to FeatureEditPart
				viewer.internRefresh(true);
				viewer.deselectAll();
				viewer.select(part);
			} else {
				FMUIPlugin.getDefault().logWarning("Edit part must not be null!");
			}
			viewer.reload();
			setDirty(true);
			break;
		case ALL_FEATURES_CHANGED_NAME_TYPE:
			for (final IGraphicalFeature f : graphicalFeatureModel.getFeatures()) {
				f.update(FeatureIDEEvent.getDefault(EventType.FEATURE_NAME_CHANGED));
			}
			viewer.internRefresh(true);
			viewer.reload();
			if (extraPath != null) {
				FileHandler.save(extraPath, graphicalFeatureModel, format);
			}
			break;
		case MANDATORY_CHANGED:
			FeatureUIHelper.getGraphicalFeature((IFeature) event.getSource(), graphicalFeatureModel).update(event);

			setDirty(true);
			analyzeFeatureModel();
			break;
		case GROUP_TYPE_CHANGED:
			for (final IGraphicalFeature f : FeatureUIHelper.getGraphicalChildren((IFeature) event.getSource(), graphicalFeatureModel)) {
				f.update(event);
			}
			setDirty(true);
			analyzeFeatureModel();
			break;
		case ATTRIBUTE_CHANGED:
			FeatureUIHelper.getGraphicalFeature((IFeature) event.getSource(), graphicalFeatureModel).update(event);
			setDirty(true);
			legendLayoutAction.refresh();
			viewer.internRefresh(false);
			break;
		case LOCATION_CHANGED:
			viewer.internRefresh(true);
			setDirty(true);
			break;
		case CONSTRAINT_MOVE:
			viewer.internRefresh(true);
			setDirty(true);
			break;
		case CONSTRAINT_MODIFY:
			final IConstraint c = (IConstraint) event.getSource();
			final IGraphicalConstraint graphicalConstraint = graphicalFeatureModel.getGraphicalConstraint(c);
			graphicalConstraint.update(event);
			viewer.internRefresh(true);
			setDirty(true);
			analyzeFeatureModel();
			for (final IGraphicalFeature gFeature : graphicalFeatureModel.getFeatures()) {
				gFeature.getObject().fireEvent(new FeatureIDEEvent(null, EventType.ATTRIBUTE_CHANGED, Boolean.FALSE, true));
				gFeature.update(FeatureIDEEvent.getDefault(EventType.ATTRIBUTE_CHANGED));
			}
			break;
		case CONSTRAINT_ADD:
		case CONSTRAINT_DELETE:
		case STRUCTURE_CHANGED:
			viewer.reload();
			analyzeFeatureModel();
			viewer.refreshChildAll(graphicalFeatureModel.getFeatureModel().getStructure().getRoot().getFeature());
			viewer.internRefresh(true);
			setDirty(true);
			for (final IGraphicalFeature gFeature : graphicalFeatureModel.getFeatures()) {
				gFeature.getObject().fireEvent(new FeatureIDEEvent(null, EventType.ATTRIBUTE_CHANGED, Boolean.FALSE, true));
				gFeature.update(FeatureIDEEvent.getDefault(EventType.ATTRIBUTE_CHANGED));
			}
			break;
		case MODEL_DATA_OVERRIDDEN:
			if (extraPath != null) {
				FileHandler.save(extraPath, graphicalFeatureModel, format);
			}
			Display.getDefault().syncExec(new Runnable() {

				@Override
				public void run() {
					viewer.deregisterEditParts();
					graphicalFeatureModel.init();
					if (extraPath != null) {
						FileHandler.load(extraPath, graphicalFeatureModel, format);
					}

					viewer.setContents(graphicalFeatureModel);
					viewer.refreshChildAll(graphicalFeatureModel.getFeatureModel().getStructure().getRoot().getFeature());
					viewer.reload();
				}
			});
			setDirty(false);
			analyzeFeatureModel();
			break;
		case MODEL_DATA_CHANGED:
			// clear registry
			if (extraPath != null) {
				FileHandler.save(extraPath, graphicalFeatureModel, format);
			}
			viewer.deregisterEditParts();
			graphicalFeatureModel.init();
			if (extraPath != null) {
				FileHandler.load(extraPath, graphicalFeatureModel, format);
			}
			viewer.setContents(graphicalFeatureModel);
			viewer.refreshChildAll(graphicalFeatureModel.getFeatureModel().getStructure().getRoot().getFeature());
			viewer.reload();
			setDirty(true);
			analyzeFeatureModel();
			break;
		case FEATURE_DELETE:
			final IGraphicalFeature deletedFeature = graphicalFeatureModel.getGraphicalFeature((IFeature) event.getSource());
			deletedFeature.update(event);
			final IFeature oldParent = (IFeature) event.getOldValue();
			// Update the parent from
			if (oldParent != null) {
				graphicalFeatureModel.getGraphicalFeature(oldParent).update(FeatureIDEEvent.getDefault(EventType.CHILDREN_CHANGED));
				// and update the children that their parent changed
				for (final IGraphicalFeature child : graphicalFeatureModel.getGraphicalFeature(oldParent)
						.getGraphicalChildren(graphicalFeatureModel.getLayout().showHiddenFeatures())) {
					child.update(FeatureIDEEvent.getDefault(EventType.PARENT_CHANGED));
				}
				viewer.refreshChildAll(oldParent);
			} else {
				// No old parent so the new feature was the root
				// Now update roots parent
				final IGraphicalFeature root =
					graphicalFeatureModel.getGraphicalFeature(graphicalFeatureModel.getFeatureModel().getStructure().getRoot().getFeature());
				root.update(FeatureIDEEvent.getDefault(EventType.PARENT_CHANGED));
				viewer.refreshChildAll(root.getObject());
			}
			viewer.internRefresh(true);
			setDirty(true);
			analyzeFeatureModel();
			break;
		case MODEL_DATA_SAVED:
			if (extraPath != null) {
				FileHandler.save(extraPath, graphicalFeatureModel, format);
			}
			break;
		case MODEL_LAYOUT_CHANGED:
			viewer.reload();
			if (extraPath != null) {
				FileHandler.save(extraPath, graphicalFeatureModel, format);
			}
			break;
		case REDRAW_DIAGRAM:
			viewer.getControl().setBackground(FMPropertyManager.getDiagramBackgroundColor());
			viewer.reload();
			refreshGraphics(null);
			viewer.refreshChildAll(graphicalFeatureModel.getFeatureModel().getStructure().getRoot().getFeature());
			analyzeFeatureModel();
			break;
		case REFRESH_ACTIONS:
			// additional actions can be refreshed here
			// legendAction.refresh();
			legendLayoutAction.refresh();
			break;
		case LEGEND_LAYOUT_CHANGED:
			if ((event.getSource() instanceof Boolean) && ((Boolean) event.getSource())) {
				setDirty(true);
			}
			legendLayoutAction.refresh();
			viewer.internRefresh(false);
			break;
		case HIDDEN_CHANGED:
			FeatureUIHelper.getGraphicalFeature((IFeature) event.getSource(), graphicalFeatureModel).update(event);
			for (final IFeatureStructure child : Features.getAllFeatures(new ArrayList<IFeatureStructure>(), ((IFeature) event.getSource()).getStructure())) {
				FeatureUIHelper.getGraphicalFeature(child.getFeature(), graphicalFeatureModel).update(event);
			}
			viewer.reload(); // reload need to be called afterwards so that the events can apply to the to be hidden features. reload would remove the editparts
							 // that
			// leads to errors.
			viewer.refreshChildAll((IFeature) event.getSource());
			legendLayoutAction.refresh();
			setDirty(true);
			viewer.internRefresh(true);
			analyzeFeatureModel();
			break;
		case COLLAPSED_CHANGED:
			// Reload editpart to notify the diagramm that the IGraphicalModel has changed
			viewer.reload();
			if (event.getNewValue() == null) {
				final IFeature selectedFeature = (IFeature) event.getSource();
				viewer.refreshChildAll(selectedFeature);
			}
			viewer.internRefresh(false);
			analyzeFeatureModel();
			setDirty(true);
			// Center collapsed feature after operation
			if (event.getSource() instanceof IFeature) {
				viewer.centerPointOnScreen((IFeature) event.getSource());
			}

			// redraw the explanation after collapse
			setActiveExplanation(activeExplanation);
			break;
		case COLLAPSED_ALL_CHANGED:
			viewer.reload();
			viewer.refreshChildAll(graphicalFeatureModel.getFeatureModel().getStructure().getRoot().getFeature());
			viewer.internRefresh(false);
			analyzeFeatureModel();
			setDirty(true);

			// Center root feature after operation
			viewer.centerPointOnScreen(graphicalFeatureModel.getFeatureModel().getStructure().getRoot().getFeature());

			// redraw the explanation after collapse
			setActiveExplanation(activeExplanation);
			break;
		case COLOR_CHANGED:
			if (event.getSource() instanceof List) {
				final List<?> srcList = (List<?>) event.getSource();

				if (!srcList.isEmpty()) {
					List<IGraphicalFeature> features;

					final Object firstElement = srcList.get(0);
					// If IGraphicalFeatures are passed, use them
					if (firstElement instanceof IGraphicalFeature) {
						features = (List<IGraphicalFeature>) srcList;
					}
					// If not....
					else {
						features = new ArrayList<>();
						// ... get the IGraphicalFeatures, if Features are passed
						if (firstElement instanceof IFeature) {
							for (final Object featureObj : srcList) {
								features.add(graphicalFeatureModel.getGraphicalFeature((IFeature) featureObj));
							}
						}
					}

					for (final IGraphicalFeature gf : features) {
						gf.update(FeatureIDEEvent.getDefault(EventType.COLOR_CHANGED));
					}
				}
			} else {
				FMUIPlugin.getDefault().logWarning(event + " contains wrong source type: " + event.getSource());
			}

			viewer.reload();
			refreshGraphics(null);
			break;
		case DEPENDENCY_CALCULATED:
			setDirty(false);
			break;
		case ACTIVE_EXPLANATION_CHANGED:
			// Deactivate the old active explanation.
			final FeatureModelExplanation<?> oldActiveExplanation = (FeatureModelExplanation<?>) event.getOldValue();
			if (oldActiveExplanation != null) {
				// Reset each element affected by the old active explanation.
				final Set<IGraphicalElement> updatedElements = new HashSet<>();
				for (final Reason<?> reason : oldActiveExplanation.getReasons()) {
					for (final IFeatureModelElement sourceElement : ((FeatureModelReason) reason).getSubject().getElements()) {
						final IGraphicalElement element = FeatureUIHelper.getGraphicalElement(sourceElement, getGraphicalFeatureModel());
						if (element.getObject() instanceof IFeature) {
							if (graphicalFeatureModel.getVisibleFeatures()
									.contains(graphicalFeatureModel.getGraphicalFeature((IFeature) element.getObject()))) {
								if (updatedElements.add(element)) {
									element.update(event);
								}
							}
						} else if (element.getObject() instanceof IConstraint) {
							if (graphicalFeatureModel.getVisibleConstraints()
									.contains(graphicalFeatureModel.getGraphicalConstraint((IConstraint) element.getObject()))) {
								if (updatedElements.add(element)) {
									element.update(event);
								}
							}
						}
					}
				}
			}

			// Activate the new active explanation.
			final FeatureModelExplanation<?> newActiveExplanation = (FeatureModelExplanation<?>) event.getNewValue();
			if (newActiveExplanation != null) {
				// Notify each element affected by the new active explanation of its new active reasons.
				for (final Reason<?> reason : newActiveExplanation.getReasons()) {
					for (final IFeatureModelElement sourceElement : ((FeatureModelReason) reason).getSubject().getElements()) {
						final IGraphicalElement element = FeatureUIHelper.getGraphicalElement(sourceElement, getGraphicalFeatureModel());
						if (element.getObject() instanceof IFeature) {
							if (graphicalFeatureModel.getVisibleFeatures()
									.contains(graphicalFeatureModel.getGraphicalFeature((IFeature) element.getObject()))) {
								element.update(new FeatureIDEEvent(event.getSource(), EventType.ACTIVE_REASON_CHANGED, null, reason));
							}
						} else if (element.getObject() instanceof IConstraint) {
							if (graphicalFeatureModel.getVisibleConstraints()
									.contains(graphicalFeatureModel.getGraphicalConstraint((IConstraint) element.getObject()))) {
								element.update(new FeatureIDEEvent(event.getSource(), EventType.ACTIVE_REASON_CHANGED, null, reason));
							}
						}

					}
				}
			}

			// Refresh the legend.
			if (!graphicalFeatureModel.isLegendHidden()) {
				viewer.layoutLegendOnIntersect();
			}
			break;
		case FEATURE_ATTRIBUTE_CHANGED:
			setDirty(true);
			break;
		case DEFAULT:
			break;
		default:
			FMUIPlugin.getDefault().logWarning(prop + " not handled!");
			break;
		}
//		TODO
//		for (final IFeatureModelEditorPage page : featureModelEditor.extensionPages) {
//			page.propertyChange(event);
//		}
	}

	@Override
	public void setIndex(int index) {
		this.index = index;
	}

	@Override
	public int getIndex() {
		return index;
	}

	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	@Override
	public void initEditor() {
		createContextMenu();
		createKeyBindings();
		createMouseHandlers();
	}

	private void createContextMenu() {
		final MenuManager menuManager = new MenuManager("#PopupMenu");
		menuManager.setRemoveAllWhenShown(true);
		menuManager.addMenuListener(new IMenuListener() {

			@Override
			public void menuAboutToShow(IMenuManager manager) {
				fillContextMenu(manager);
			}
		});
		viewer.setContextMenu(menuManager);
		// the following line adds package explorer entries into our context menu
		// getSite().registerContextMenu(menu, graphicalViewer);
	}

	public void createKeyBindings() {
		final KeyHandler handler = viewer.getKeyHandler();

		handler.put(KeyStroke.getPressed(SWT.F2, 0), renameAction);
		handler.put(KeyStroke.getPressed(SWT.INSERT, 0), createLayerAction);
		handler.put(KeyStroke.getPressed((char) (('d' - 'a') + 1), 'd', SWT.CTRL), deleteAllAction);
		handler.put(KeyStroke.getPressed((char) (('c' - 'a') + 1), 'c', SWT.CTRL), collapseAction);

		handler.put(KeyStroke.getPressed(SWT.ARROW_UP, SWT.CTRL), moveUpAction);
		handler.put(KeyStroke.getPressed(SWT.ARROW_RIGHT, SWT.CTRL), moveRightAction);
		handler.put(KeyStroke.getPressed(SWT.ARROW_DOWN, SWT.CTRL), moveDownAction);
		handler.put(KeyStroke.getPressed(SWT.ARROW_LEFT, SWT.CTRL), moveLeftAction);

		handler.put(KeyStroke.getReleased(SWT.CTRL, SWT.CTRL), moveStopAction);
		handler.put(KeyStroke.getReleased(0, SWT.CTRL), moveStopAction);
		handler.put(KeyStroke.getReleased(SWT.CTRL, 0), moveStopAction);
	}

	public void createMouseHandlers() {
		viewer.getControl().addMouseWheelListener(new FeatureDiagramEditorMouseHandler(zoomIn, zoomOut, SWT.CTRL));
		viewer.createMouseHandlers();
	}

	private MenuManager createLayoutMenuManager(boolean showText) {
		final MenuManager menuManager =
			new ToolBarMenuManager(showText ? SET_LAYOUT : "", FMUIPlugin.getDefault().getImageDescriptor("icons/tree_mode.gif"), "");
		menuManager.setRemoveAllWhenShown(true);
		menuManager.addMenuListener(new IMenuListener() {

			@Override
			public void menuAboutToShow(IMenuManager manager) {
				for (final Action action : setLayoutActions) {
					action.setEnabled(true);
					action.setChecked(false);
					menuManager.add(action);
				}
				final Action selectedAction = setLayoutActions.get(graphicalFeatureModel.getLayout().getLayoutAlgorithm());
				selectedAction.setEnabled(false);
				selectedAction.setChecked(true);
				menuManager.insert(1, new Separator("ManualLayoutSeparator"));
				menuManager.insertBefore("ManualLayoutSeparator", autoLayoutConstraintAction);
				autoLayoutConstraintAction.setEnabled(!graphicalFeatureModel.getLayout().hasFeaturesAutoLayout());
			}
		});
		return menuManager;
	}

	private MenuManager createCalculationsMenuManager(boolean showText) {
		final MenuManager menuManager =
			new ToolBarMenuManager(showText ? SET_CALCULATIONS : "", FMUIPlugin.getDefault().getImageDescriptor("icons/thread_obj.gif"), "");
		menuManager.setRemoveAllWhenShown(true);
		menuManager.addMenuListener(new IMenuListener() {

			@Override
			public void menuAboutToShow(IMenuManager manager) {
				for (final Action action : calculationActions) {
					menuManager.add(action);
				}
				menuManager.insert(2, new Separator());
			}
		});
		return menuManager;
	}

	private MenuManager createNameTypeMenuManager() {
		final MenuManager menuManager = new MenuManager(SET_NAME_TYPE);
		menuManager.setRemoveAllWhenShown(true);
		menuManager.addMenuListener(new IMenuListener() {

			@Override
			public void menuAboutToShow(IMenuManager manager) {
				for (final Action action : setNameTypeActions) {
					menuManager.add(action);
				}
				final Action selectedAction = setNameTypeActions.get((graphicalFeatureModel.getLayout().showShortNames()) ? 1 : 0);
				selectedAction.setChecked(true);
				selectedAction.setEnabled(false);
			}
		});
		return menuManager;
	}

	private boolean isFeatureMenu(IStructuredSelection selection) {
		boolean featureMenu = !selection.toList().isEmpty();
		for (final Object obj : selection.toList()) {
			if (!(obj instanceof FeatureEditPart)) {
				featureMenu = false;
			}
		}
		return featureMenu;
	}

	private boolean isLegendMenu(IStructuredSelection selection) {
		boolean legendMenu = !selection.toList().isEmpty();
		for (final Object obj : selection.toList()) {
			if (!(obj instanceof LegendEditPart)) {
				legendMenu = false;
			}
		}
		return legendMenu;
	}

	private boolean isConstraintMenu(IStructuredSelection selection) {
		boolean constraintMenu = !selection.toList().isEmpty();
		for (final Object obj : selection.toList()) {
			if (!(obj instanceof ConstraintEditPart)) {
				constraintMenu = false;
			}
		}
		return constraintMenu;
	}

	private boolean isConnectionMenu(IStructuredSelection selection) {
		boolean connectionMenu = false;
		for (final Object obj : selection.toList()) {
			if ((obj instanceof ConnectionEditPart)) {
				connectionMenu = true;
			}
		}
		return connectionMenu;

	}

	private void fillContextMenu(IMenuManager menuManager) {
		final IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();

		if (getFeatureModel() instanceof ExtendedFeatureModel) {
			menuManager.add(createLayoutMenuManager(true));
			menuManager.add(createNameTypeMenuManager());
		}
		if (isFeatureMenu(selection)) {
			menuManager.add(createCompoundAction);
			menuManager.add(createLayerAction);
			menuManager.add(createConstraintWithAction);
			menuManager.add(renameAction);
			menuManager.add(changeFeatureDescriptionAction);
			menuManager.add(deleteAction);
			menuManager.add(deleteAllAction);
			menuManager.add(new Separator());
			connectionEntries(menuManager);
			menuManager.add(mandatoryAction);
			menuManager.add(abstractAction);
			menuManager.add(hiddenAction);
			menuManager.add(new Separator());
			menuManager.add(new Separator());
			menuManager.add(colorSelectedFeatureAction);
			menuManager.add(new Separator());
			menuManager.add(collapseAction);
			menuManager.add(collapseFeaturesAction);
			menuManager.add(focusOnExplanationAction);
			for (final FeatureDiagramExtension extension : FeatureDiagramExtension.getExtensions()) {
				extension.extendContextMenu(menuManager, this);
			}
		} else if (isLegendMenu(selection)) {
			menuManager.add(legendLayoutAction);
			menuManager.add(legendAction);
		} else if (isConstraintMenu(selection)) {
			menuManager.add(createConstraintAction);
			menuManager.add(expandConstraintAction);
			menuManager.add(editConstraintAction);
			menuManager.add(deleteAction);
		} else if (isConnectionMenu(selection)) {
			connectionEntries(menuManager);
		} else {
			// nothing selected, build presentation menu
			menuManager.add(createConstraintAction);
			menuManager.add(new Separator());
			menuManager.add(collapseAllAction);
			menuManager.add(expandAllAction);
			menuManager.add(adjustModelToEditorSizeAction);
			menuManager.add(new Separator());
			menuManager.add(createLayoutMenuManager(true));
			menuManager.add(createCalculationsMenuManager(true));
			menuManager.add(new Separator());
			menuManager.add(reverseOrderAction);
			menuManager.add(showHiddenFeaturesAction);
			menuManager.add(showCollapsedConstraintsAction);
			menuManager.add(new Separator());
			menuManager.add(legendAction);
			menuManager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
			menuManager.add(exportFeatureModelAction);
		}
		showHiddenFeaturesAction.setChecked(graphicalFeatureModel.getLayout().showHiddenFeatures());
		showCollapsedConstraintsAction.setChecked(graphicalFeatureModel.getLayout().showCollapsedConstraints());
	}

	private void connectionEntries(IMenuManager menu) {
		if (andAction.isEnabled() || orAction.isEnabled() || alternativeAction.isEnabled()) {
			final boolean connectionSelected = alternativeAction.isConnectionSelected();
			if (andAction.isChecked()) {
				andAction.setText(AND);
				if (connectionSelected) {
					orAction.setText(OR + DOUBLE_CLICK);
				} else {
					orAction.setText(OR);
				}
				alternativeAction.setText(ALTERNATIVE);
			} else if (orAction.isChecked()) {
				andAction.setText(AND);
				orAction.setText(OR);
				if (connectionSelected) {
					alternativeAction.setText(ALTERNATIVE + DOUBLE_CLICK);
				} else {
					alternativeAction.setText(ALTERNATIVE);
				}
			} else if (alternativeAction.isChecked()) {
				if (connectionSelected) {
					andAction.setText(AND + DOUBLE_CLICK);
				} else {
					andAction.setText(AND);
				}
				orAction.setText(OR);
				alternativeAction.setText(ALTERNATIVE);
			}
			if (andAction.isEnabled() || andAction.isChecked()) {
				menu.add(andAction);
			}
			if (orAction.isEnabled() || orAction.isChecked()) {
				menu.add(orAction);
			}
			if (alternativeAction.isEnabled() || alternativeAction.isChecked()) {
				menu.add(alternativeAction);
			}
			menu.add(new Separator());
		}
	}

	@Override
	public IFeatureModelEditorPage getPage(Composite container) {
		return new FeatureDiagramEditor(fmManager, true);
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		if (isDirty()) {
			if (extraPath != null) {
				FileHandler.save(extraPath, graphicalFeatureModel, format);
			}
			super.doSave(monitor);
		}
	}

	@Override
	public String getID() {
		return ID;
	}

	/**
	 * Stops the analyzing job when the editor is closed.
	 */
	@Override
	public void dispose() {
		LongRunningWrapper.cancelAllJobs(analysisToken);
		FeatureColorManager.removeListener(this);
		fmManager.removeListener(this);
		graphicalFeatureModel.getFeatureModel().removeListener(editorKeyHandler);
		super.dispose();
	}

	public IGraphicalFeatureModel getGraphicalFeatureModel() {
		return graphicalFeatureModel;
	}

	public FeatureDiagramViewer getViewer() {
		return viewer;
	}

	public IAction getDiagramAction(String workbenchActionID) {
		if (CreateLayerAction.ID.equals(workbenchActionID)) {
			return createLayerAction;
		}
		if (CreateCompoundAction.ID.equals(workbenchActionID)) {
			return createCompoundAction;
		}
		if (DeleteAction.ID.equals(workbenchActionID)) {
			return deleteAction;
		}
		if (MandatoryAction.ID.equals(workbenchActionID)) {
			return mandatoryAction;
		}
		if (AbstractAction.ID.equals(workbenchActionID)) {
			return abstractAction;
		}
		if (CollapseAction.ID.equals(workbenchActionID)) {
			return collapseAction;
		}
		if (CollapseSiblingsAction.ID.equals(workbenchActionID)) {
			return collapseFeaturesAction;
		}
		if (FocusOnExplanationAction.ID.equals(workbenchActionID)) {
			return focusOnExplanationAction;
		}
		if (AbstractAction.ID.equals(workbenchActionID)) {
			return abstractAction;
		}
		if (HiddenAction.ID.equals(workbenchActionID)) {
			return hiddenAction;
		}
		if (AndAction.ID.equals(workbenchActionID)) {
			return andAction;
		}
		if (OrAction.ID.equals(workbenchActionID)) {
			return orAction;
		}
		if (AlternativeAction.ID.equals(workbenchActionID)) {
			return alternativeAction;
		}
		if (RenameAction.ID.equals(workbenchActionID)) {
			return renameAction;
		}
		if (CalculateDependencyAction.ID.equals(workbenchActionID)) {
			return calculateDependencyAction;
		}
		if (GEFActionConstants.ZOOM_IN.equals(workbenchActionID)) {
			return zoomIn;
		}
		if (GEFActionConstants.ZOOM_OUT.equals(workbenchActionID)) {
			return zoomOut;
		}
		return null;
	}

	public void addSelectionChangedListener(ISelectionChangedListener listener) {
		viewer.addSelectionChangedListener(listener);
	}

	public void removeSelectionChangedListener(ISelectionChangedListener listener) {
		viewer.removeSelectionChangedListener(listener);
	}

}
