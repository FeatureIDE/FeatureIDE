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
package de.ovgu.featureide.ui.views.collaboration;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADD_NEW_CLASS_ROLE;
import static de.ovgu.featureide.fm.core.localization.StringTable.BUILD_COLLABORATIONMODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHANGE_FILTER_FOR_ACCESS_MODIFIERS;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFAULT;
import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE;
import static de.ovgu.featureide.fm.core.localization.StringTable.DESELECT_ALL;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXPORT_AS;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXPORT_AS_IMAGE;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXPORT_AS_XML;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXPORT_AS___;
import static de.ovgu.featureide.fm.core.localization.StringTable.FIELDS_WITHOUT_REFINEMENTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.FIELDS_WITH_REFINEMENTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.FILTER;
import static de.ovgu.featureide.fm.core.localization.StringTable.HIDE_PARAMETER_TYPES;
import static de.ovgu.featureide.fm.core.localization.StringTable.METHODS_WITHOUT_REFINEMENTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.METHODS_WITH_REFINEMENTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.MODEL_LOADING_ERROR;
import static de.ovgu.featureide.fm.core.localization.StringTable.OPEN_A_FILE_FROM_A_FEATUREIDE_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.PRIVATE;
import static de.ovgu.featureide.fm.core.localization.StringTable.PROTECTED;
import static de.ovgu.featureide.fm.core.localization.StringTable.PUBLIC;
import static de.ovgu.featureide.fm.core.localization.StringTable.REFRESH_COLLABORATION_VIEW;
import static de.ovgu.featureide.fm.core.localization.StringTable.SEARCH_IN_COLLABORATION_DIAGRAM;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECT_ALL;
import static de.ovgu.featureide.fm.core.localization.StringTable.SHOW_CLASS_INVARIANTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.SHOW_FIELDS_AND_METHODS;
import static de.ovgu.featureide.fm.core.localization.StringTable.SHOW_METHOD_CONTRACTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.SHOW_NESTED_CLASSES;
import static de.ovgu.featureide.fm.core.localization.StringTable.SHOW_UNSELECTED_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.UPDATE_COLLABORATION_VIEW;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.draw2d.ConnectionLayer;
import org.eclipse.draw2d.FigureCanvas;
import org.eclipse.draw2d.Viewport;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditDomain;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.GraphicalViewer;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.ui.actions.PrintAction;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.ActionContributionItem;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuCreator;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.ISaveablePart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.FSTConfiguration;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.listeners.ICurrentBuildListener;
import de.ovgu.featureide.fm.core.AWaitingJob;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.LongRunningJob;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.ui.GraphicsExporter;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors.SetFeatureColorAction;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.action.AddRoleAction;
import de.ovgu.featureide.ui.views.collaboration.action.DeleteAction;
import de.ovgu.featureide.ui.views.collaboration.action.ExportAsImageImpl;
import de.ovgu.featureide.ui.views.collaboration.action.ExportAsXmlImpl;
import de.ovgu.featureide.ui.views.collaboration.action.FilterAction;
import de.ovgu.featureide.ui.views.collaboration.action.SetColorAction;
import de.ovgu.featureide.ui.views.collaboration.action.ShowFieldsMethodsAction;
import de.ovgu.featureide.ui.views.collaboration.action.ShowUnselectedAction;
import de.ovgu.featureide.ui.views.collaboration.editparts.CollaborationEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.GraphicalEditPartFactory;
import de.ovgu.featureide.ui.views.collaboration.figures.RoleFigure;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModelBuilder;

/**
 * View of the collaboration diagram.
 *
 * @author Constanze Adler
 * @author Stephan Besecke
 * @author Jens Meinicke
 * @author Sebastian Krieter
 * @author Christian Lausberger
 * @author Steffen Schulze
 * @author Bastian Bartens
 * @author Max Kammler
 * @author Antje Moench
 * @author Paul Maximilian Bittner
 */

public class CollaborationView extends ViewPart implements GUIDefaults, ICurrentBuildListener, ISaveablePart {

	public static final String ID = UIPlugin.PLUGIN_ID + ".views.collaboration.Collaboration";

	private static final String OPEN_MESSAGE = OPEN_A_FILE_FROM_A_FEATUREIDE_PROJECT;

	private static final String ADD_LABEL = ADD_NEW_CLASS_ROLE;
	private static final String FILTER_LABEL = FILTER;
	private static final String DELETE_LABEL = DELETE;
	private static final String UNSELECTED_LABEL = SHOW_UNSELECTED_FEATURES;
	private static final String EXPORT_AS_LABEL = EXPORT_AS;

	private static final String REFRESH_TOOL_TIP_LABEL = BUILD_COLLABORATIONMODEL;

	private static final String[] FIELD_METHOD_LABEL_NAMES =
		{ FIELDS_WITH_REFINEMENTS, FIELDS_WITHOUT_REFINEMENTS, METHODS_WITH_REFINEMENTS, METHODS_WITHOUT_REFINEMENTS, SHOW_METHOD_CONTRACTS,
			SHOW_CLASS_INVARIANTS, SHOW_NESTED_CLASSES, HIDE_PARAMETER_TYPES, PUBLIC, PROTECTED, DEFAULT, PRIVATE, SELECT_ALL, DESELECT_ALL };

	private static final Image[] FIELD_METHOD_IMAGES = { IMAGE_FIELDS_REFINEMENTS, IMAGE_FIELDS_WITHOUT_REFINEMENTS, IMAGE_METHODS_REFINEMENTS,
		IMAGE_METHODS_WITHOUT_REFINEMENTS, IMAGE_AT_CONTRACT, IMAGE_AT_INVARIANT, IMAGE_NESTED_CLASS, null, IMAGE_METHODE_PUBLIC, IMAGE_METHODE_PROTECTED,
		IMAGE_METHODE_DEFAULT, IMAGE_METHODE_PRIVATE, IMAGE_SELECT_ALL, IMAGE_DESELECT_ALL };

	private GraphicalViewerImpl viewer;

	private final CollaborationModelBuilder builder = new CollaborationModelBuilder();
	private IWorkbenchPart currentEditor;
	private AddRoleAction addRoleAction;
	private DeleteAction delAction;
	private Action refreshButton;
	private FilterAction filterAction;
	private PrintAction printAction;
	private ShowUnselectedAction showUnselectedAction;
	private SetFeatureColorAction setFeatureColourAction;
	private Point cursorPosition;
	private CollaborationViewSearch search;

	/*
	 * the following codefragments which are commented out, create the submenu of the colorscheme
	 */
	// private AddColorSchemeAction addColorSchemeAction;
	// private RenameColorSchemeAction renameColorSchemeAction;
	// private DeleteColorSchemeAction deleteColorSchemeAction;
	private ExportAsImageImpl exportAsImage;
	private ExportAsXmlImpl exportAsXML;

	private ShowFieldsMethodsAction fieldsWithRefinementsButton;
	private ShowFieldsMethodsAction fieldsWithoutRefinementsButton;
	private ShowFieldsMethodsAction methodsWithRefinementsButton;
	private ShowFieldsMethodsAction methodsWithoutRefinementsButton;
	private ShowFieldsMethodsAction showContracsButton;
	private ShowFieldsMethodsAction showInvariantsButton;
	private ShowFieldsMethodsAction showNestedClassesButton;

	private final SetColorAction[] setColorActions = new SetColorAction[ColorPalette.COLOR_COUNT];
	private final ShowFieldsMethodsAction[] setFieldsMethodsActions = new ShowFieldsMethodsAction[FIELD_METHOD_LABEL_NAMES.length];

	private ShowFieldsMethodsAction showAccessModifiers;

	private IToolBarManager toolbarManager;

	private final Vector<IFile> configurations = new Vector<IFile>();
	private final Job updateGUIJob = new AWaitingJob(UPDATE_COLLABORATION_VIEW) {

		@Override
		public IStatus execute(IProgressMonitor monitor) {
			disableToolbarFilterItems();
			if (configurations.isEmpty()) {
				refreshButton.setEnabled(true);
				return Status.OK_STATUS;
			}
			final IFile configurationFile = configurations.lastElement();
			configurations.clear();
			if ((configurationFile != null) && (CollaborationModelBuilder.editorFile != null)) {
				builder.configuration = configurationFile;
			}
			final FSTModel model = builder.buildCollaborationModel(CorePlugin.getFeatureProject(configurationFile));
			if (model == null) {
				refreshButton.setEnabled(true);
				return Status.OK_STATUS;
			}

			if (!configurations.isEmpty()) {
				return Status.OK_STATUS;
			}
			final UIJob uiJob = new UIJob(UPDATE_COLLABORATION_VIEW) {

				@Override
				public IStatus runInUIThread(IProgressMonitor monitor) {
					viewer.setContents(model);
					final EditPart part = viewer.getContents();
					if (part != null) {
						part.refresh();
					}
					refreshButton.setEnabled(true);
					search.refreshSearchContent();
					return Status.OK_STATUS;
				}
			};
			uiJob.setPriority(Job.SHORT);
			uiJob.schedule();
			try {
				uiJob.join();
			} catch (final InterruptedException e) {
				UIPlugin.getDefault().logError(e);
			}
			return Status.OK_STATUS;
		}
	};

	private final IEventListener colorChangeListener = new IEventListener() {

		@Override
		public void propertyChange(FeatureIDEEvent event) {
			if (event.getEventType() == FeatureIDEEvent.EventType.COLOR_CHANGED) {
				refresh();
			}
		}

	};

	private IFeatureProject featureProject;
	private IFeatureModel featureModel;

	public IFeatureProject getFeatureProject() {
		return featureProject;
	}

	private void setFeatureProject(IFeatureProject featureProject) {
		if (this.featureProject != featureProject) {
			this.featureProject = featureProject;

			if (this.featureProject != null) {
				featureModel = this.featureProject.getFeatureModel();
				setFeatureColourAction.setFeatureModel(featureModel);
			}
		}
	}

	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	public Point getCursorPosition() {
		return cursorPosition;
	}

	private void saveCursorPosition() {
		final Display display = Display.getDefault();
		final FigureCanvas figureCanvas = (FigureCanvas) viewer.getControl();
		final Point point = figureCanvas.toControl(display.getCursorLocation());
		final Viewport viewport = figureCanvas.getViewport();
		final org.eclipse.draw2d.geometry.Point location = viewport.getViewLocation();
		viewport.setIgnoreScroll(true);

		int x = point.x + location.x;
		int y = point.y + location.y;
		final Rectangle bounds = viewport.getBounds();
		if (point.x < 0) {
			x += bounds.width;
		}
		if (point.y < 0) {
			y += bounds.height;
		}

		cursorPosition = new Point(x, y);
	}

	private final IPartListener editorListener = new IPartListener() {

		@Override
		public void partOpened(IWorkbenchPart part) {

		}

		@Override
		public void partDeactivated(IWorkbenchPart part) {

		}

		@Override
		public void partClosed(IWorkbenchPart part) {
			if (part == currentEditor) {
				setEditorActions(null);
			}
		}

		@Override
		public void partBroughtToTop(IWorkbenchPart part) {
			if (part instanceof IEditorPart) {
				setEditorActions(part);
			}

		}

		@Override
		public void partActivated(IWorkbenchPart part) {
			if ((part instanceof IEditorPart) || (part instanceof ViewPart)) {
				setEditorActions(part);
			}
		}

	};

	@Override
	public void createPartControl(Composite parent) {
		final IWorkbenchWindow editor = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		IEditorPart part = null;

		if (editor != null) {
			final IWorkbenchPage page = editor.getActivePage();
			if (page != null) {
				part = page.getActiveEditor();
			}
		}

		viewer = new ScrollingGraphicalViewer();
		viewer.createControl(parent);
		viewer.getControl().setBackground(DIAGRAM_BACKGROUND);

		getSite().getPage().addPartListener(editorListener); // EditorListener
		CorePlugin.getDefault().addCurrentBuildListener(this); // BuildListener

		// required for borders
		final ScalableFreeformRootEditPart rootEditPart = new ScalableFreeformRootEditPart();
		((ConnectionLayer) rootEditPart.getLayer(LayerConstants.CONNECTION_LAYER)).setAntialias(SWT.ON);

		viewer.setRootEditPart(rootEditPart);
		viewer.setEditDomain(new EditDomain());
		viewer.setEditPartFactory(new GraphicalEditPartFactory());

		int select = ShowFieldsMethodsAction.SELECT_ALL_METHOD_ACCESS;
		if (deselectAll()) {
			select = ShowFieldsMethodsAction.DESELECT_ALL_METHOD_ACCESS;
		}
		showAccessModifiers = new ShowFieldsMethodsAction("", null, this, select, IAction.AS_DROP_DOWN_MENU);
		showAccessModifiers.setToolTipText(CHANGE_FILTER_FOR_ACCESS_MODIFIERS);
		showAccessModifiers.setMenuCreator(new IMenuCreator() {

			Menu fMenu = null;

			@Override
			public Menu getMenu(Menu parent) {
				return fMenu;
			}

			@Override
			public Menu getMenu(Control parent) {
				fMenu = new Menu(parent);
				for (int i = ShowFieldsMethodsAction.PUBLIC_FIELDSMETHODS; i <= ShowFieldsMethodsAction.PRIVATE_FIELDSMETHODS; i++) {
					final ShowFieldsMethodsAction action = setFieldsMethodsActions[i];
					action.setChecked(RoleFigure.getRoleSelections()[i]);
					final ActionContributionItem contributionItem = new ActionContributionItem(action);
					contributionItem.fill(fMenu, -1);
				}

				final ShowFieldsMethodsAction selectAll = new ShowFieldsMethodsAction(SELECT_ALL, IMAGE_SELECT_ALL_MODIFIERS, CollaborationView.this,
						ShowFieldsMethodsAction.SELECT_ALL_METHOD_ACCESS);
				final ActionContributionItem contributionItem = new ActionContributionItem(selectAll);
				contributionItem.fill(fMenu, -1);

				final ShowFieldsMethodsAction deselectAll =
					new ShowFieldsMethodsAction(DESELECT_ALL, IMAGE_MODIFIERS_NONE, CollaborationView.this, ShowFieldsMethodsAction.DESELECT_ALL_METHOD_ACCESS);
				final ActionContributionItem deselectAllConteribution = new ActionContributionItem(deselectAll);
				deselectAllConteribution.fill(fMenu, -1);

				return fMenu;
			}

			@Override
			public void dispose() {}
		});

		createContextMenu();
		createActions(part);
		makeActions();
		contributeToActionBars();

		// Add to color CHange Listener
		FeatureColorManager.addListener(colorChangeListener);

		final CollaborationViewSearch.Builder builder = new CollaborationViewSearch.Builder();
		search = builder.setAttachedViewerParent(viewer).setSearchBoxText(SEARCH_IN_COLLABORATION_DIAGRAM).setFindResultsColor(ROLE_BACKGROUND_SELECTED)
				.setNoSearchResultsColor(ROLE_BACKGROUND_UNSELECTED).create();

	}

	private void refreshActionBars() {
		final IActionBars bars = getViewSite().getActionBars();
		bars.getToolBarManager().update(true);
		disableToolbarFilterItems();
	}

	private void contributeToActionBars() {
		final IActionBars bars = getViewSite().getActionBars();

		bars.setGlobalActionHandler(ActionFactory.PRINT.getId(), printAction);
		toolbarManager = bars.getToolBarManager();
		fillLocalToolBar();
	}

	@Override
	public void setFocus() {
		final FigureCanvas figureCanvas = (FigureCanvas) viewer.getControl();

		final Viewport model = figureCanvas.getViewport();
		model.getVerticalRangeModel().setMinimum(0);
		model.getHorizontalRangeModel().setMinimum(0);
		figureCanvas.setFocus();
	}

	/**
	 * Gets the input of the given part and sets the content of the diagram.
	 *
	 * @param activeWorkbenchPart
	 */
	private void setEditorActions(IWorkbenchPart activeWorkbenchPart) {
		IEditorPart activeEditor = null;
		setFeatureProject(null);

		if (activeWorkbenchPart == null) {
			// do nothing
		} else if (activeWorkbenchPart instanceof IEditorPart) {
			activeEditor = (IEditorPart) activeWorkbenchPart;
			currentEditor = activeWorkbenchPart;
		} else {
			final IWorkbenchPage page = activeWorkbenchPart.getSite().getPage();
			if (page != null) {
				activeEditor = page.getActiveEditor();
			}
		}

		if ((activeEditor != null) && (activeEditor.getEditorInput() instanceof FileEditorInput)) {
			// case: open editor
			final IFile inputFile = ((FileEditorInput) activeEditor.getEditorInput()).getFile();
			setFeatureProject(CorePlugin.getFeatureProject(inputFile));

			if (featureProject != null) {
				// case: it's a FeatureIDE project
				// featureProject.getFeatureModel().addListener(new PropertyChangeListener() {
				// @Override
				// public void propertyChange(PropertyChangeEvent event) {
				// if (PropertyConstants.MODEL_DATA_LOADED.equals(event.getPropertyName())) {
				// readColorsFromFile();
				// }
				// }
				// });

				if (ConfigFormatManager.getInstance().hasFormat(inputFile.getName())) {
					// case: open configuration editor
					CollaborationModelBuilder.editorFile = null;
					if ((builder.configuration != null) && builder.configuration.equals(inputFile)
						&& featureProject.equals(CollaborationModelBuilder.project)) {
						return;
					} else {
						builder.configuration = inputFile;
					}
				} else {
					// case: open editor is no configuration editor
					if ((CollaborationModelBuilder.editorFile != null) && CollaborationModelBuilder.editorFile.getName().equals(inputFile.getName())
						&& featureProject.getProject().equals(CollaborationModelBuilder.editorFile.getProject())) {
						return;
					}
					CollaborationModelBuilder.editorFile = inputFile;
					builder.configuration = featureProject.getCurrentConfiguration();
				}
			}
		}

		if (featureProject == null) {
			final FSTModel model = new FSTModel(null);
			model.setConfiguration(new FSTConfiguration(OPEN_MESSAGE, null, false));
			viewer.setContents(model);
			final EditPart content = viewer.getContents();
			if (content != null) {
				content.refresh();
			}
		} else {
			updateGuiAfterBuild(featureProject, null);
		}
	}

	public void createContextMenu() {
		final MenuManager menuMgr = new MenuManager("#PopupMenu");
		menuMgr.setRemoveAllWhenShown(true);

		menuMgr.addMenuListener(new IMenuListener() {

			@Override
			public void menuAboutToShow(IMenuManager m) {
				fillContextMenu(m);
			}
		});
		final Control control = viewer.getControl();
		final Menu menu = menuMgr.createContextMenu(control);
		control.setMenu(menu);
		getSite().registerContextMenu(menuMgr, viewer);

	}

	private void fillContextMenu(IMenuManager menuMgr) {
		disableToolbarFilterItems();
		if (featureProject == null) {
			return;
		}

		final ISelection selection = viewer.getSelection();
		final boolean isNotEmpty = !selection.isEmpty();
		addRoleAction.setEnabled(isNotEmpty);
		filterAction.setEnabled(isNotEmpty);
		delAction.setEnabled(isNotEmpty);
		showUnselectedAction.setEnabled(isNotEmpty);

		saveCursorPosition();

		menuMgr.add(addRoleAction);
		menuMgr.add(filterAction);
		menuMgr.add(showUnselectedAction);
		menuMgr.add(delAction);

		// Show Feature Color Menu if necessary
		if (isNotEmpty && (selection instanceof StructuredSelection)) {
			final StructuredSelection selectionAsStructuredSelection = (StructuredSelection) selection;

			final Iterator<?> iterator = selectionAsStructuredSelection.iterator();
			Object selectedItem = null;
			boolean onlyCollaborations = true;

			while (iterator.hasNext() && ((selectedItem = iterator.next()) != null)) {
				if (!(selectedItem instanceof CollaborationEditPart)) {
					onlyCollaborations = false;
					break;
				}
			}

			if (onlyCollaborations) {
				menuMgr.add(setFeatureColourAction);
			}
		}

		if (featureProject.getComposer().showContextFieldsAndMethods()) {
			final MenuManager methodsFieldsSubMenu = new MenuManager(SHOW_FIELDS_AND_METHODS);

			for (int i = 0; i < setFieldsMethodsActions.length; i++) {
				methodsFieldsSubMenu.add(setFieldsMethodsActions[i]);
				setFieldsMethodsActions[i].setChecked(false);

				if ((i == ShowFieldsMethodsAction.SHOW_NESTED_CLASSES) || (i == ShowFieldsMethodsAction.HIDE_PARAMETERS_AND_TYPES)
					|| (i == ShowFieldsMethodsAction.PRIVATE_FIELDSMETHODS)) {
					methodsFieldsSubMenu.add(new Separator());
				}
			}
			menuMgr.add(methodsFieldsSubMenu);
		}

		menuMgr.add(new Separator());
		final MenuManager exportMenu = new MenuManager(EXPORT_AS_LABEL);
		exportMenu.add(exportAsImage);
		exportMenu.add(exportAsXML);
		menuMgr.add(exportMenu);
	}

	public void disableToolbarFilterItems() {
		boolean value = false;
		if (featureProject != null) {
			final IComposerExtensionClass composer = featureProject.getComposer();
			if (composer != null) {
				value = composer.showContextFieldsAndMethods();
			}
		}

		fieldsWithRefinementsButton.setEnabled(value);
		fieldsWithoutRefinementsButton.setEnabled(value);
		methodsWithRefinementsButton.setEnabled(value);
		methodsWithoutRefinementsButton.setEnabled(value);
		showContracsButton.setEnabled(value);
		showInvariantsButton.setEnabled(value);
		showNestedClassesButton.setEnabled(value);
		showAccessModifiers.setEnabled(value);
	}

	private void createActions(IEditorPart part) {
		addRoleAction = new AddRoleAction(ADD_LABEL, viewer, this);
		delAction = new DeleteAction(DELETE_LABEL, viewer);
		filterAction = new FilterAction(FILTER_LABEL, viewer, this);
		showUnselectedAction = new ShowUnselectedAction(UNSELECTED_LABEL, this);
		setFeatureColourAction = new SetFeatureColorAction(viewer);
		for (int i = 0; i < FIELD_METHOD_LABEL_NAMES.length; i++) {
			setFieldsMethodsActions[i] = new ShowFieldsMethodsAction(FIELD_METHOD_LABEL_NAMES[i], FIELD_METHOD_IMAGES[i], this, i);
		}

		printAction = new PrintAction(this);

		for (int i = 0; i < setColorActions.length; i++) {
			setColorActions[i] = new SetColorAction(viewer, this, i);
		}
	}

	private boolean deselectAll() {
		final boolean[] selectedModifiers = RoleFigure.getRoleSelections();
		if ((selectedModifiers[ShowFieldsMethodsAction.PUBLIC_FIELDSMETHODS]) && (selectedModifiers[ShowFieldsMethodsAction.PRIVATE_FIELDSMETHODS])
			&& (selectedModifiers[ShowFieldsMethodsAction.PROTECTED_FIELDSMETHODS]) && (selectedModifiers[ShowFieldsMethodsAction.DEFAULT_FIELDSMETHODS])) {
			return true;
		}
		return false;
	}

	private ImageDescriptor getAccessModifiersImage(boolean[] selectedModifiers) {
		final ArrayList<Image> arrayList = new ArrayList<Image>();
		if (selectedModifiers[ShowFieldsMethodsAction.PUBLIC_FIELDSMETHODS]) {
			arrayList.add(IMAGE_METHODE_PUBLIC);
		}

		if (selectedModifiers[ShowFieldsMethodsAction.PRIVATE_FIELDSMETHODS]) {
			arrayList.add(IMAGE_METHODE_PRIVATE);
		}

		if (selectedModifiers[ShowFieldsMethodsAction.PROTECTED_FIELDSMETHODS]) {
			arrayList.add(IMAGE_METHODE_PROTECTED);
		}

		if (selectedModifiers[ShowFieldsMethodsAction.DEFAULT_FIELDSMETHODS]) {
			arrayList.add(IMAGE_METHODE_DEFAULT);
		}

		final Image combinedImages = combineImages(arrayList);

		return ImageDescriptor.createFromImage(combinedImages);
	}

	public class ImageComarator implements Comparator<Image> {

		@Override
		public int compare(Image image1, Image image2) {
			return image1.getImageData().bytesPerLine > image2.getImageData().bytesPerLine ? 1 : 0;
		}
	}

	private Image combineImages(ArrayList<Image> images) {
		if (images.size() == 0) {
			return IMAGE_MODIFIERS_NONE;
		}

		Collections.sort(images, new ImageComarator());

		final Image finalImage = new Image(images.get(0).getDevice(), images.get(0).getBounds());
		final GC gc = new GC(finalImage);
		int x = 0;
		int y = 0;

		for (int j = 0; j < images.size(); j++) {
			if (images.size() == 1) {
				x = finalImage.getBounds().width / 4;
				y = finalImage.getBounds().width / 4;
			} else if (((j + 1) % 2) != 0) {
				x = 0;
				y = (j / 2) * 8;
			} else {
				x = 8;
			}
			gc.drawImage(images.get(j), 4, 4, images.get(j).getBounds().width - (2 * 4), images.get(j).getBounds().height - (2 * 4), x, y,
					finalImage.getBounds().width / 2, finalImage.getBounds().height / 2);

		}
		final ImageData data = finalImage.getImageData();
		data.transparentPixel = data.palette.getPixel(new RGB(255, 255, 255));
		gc.dispose();

		return new Image(images.get(0).getDevice(), data);
	}

	public void reloadImage() {
		// build one image from max 4 images
		final boolean[] selectedAccessModifiers = RoleFigure.getRoleSelections();
		showAccessModifiers.setImageDescriptor(getAccessModifiersImage(selectedAccessModifiers));

		if (deselectAll()) {
			showAccessModifiers.setActionIndex(ShowFieldsMethodsAction.DESELECT_ALL_METHOD_ACCESS);
		} else {
			showAccessModifiers.setActionIndex(ShowFieldsMethodsAction.SELECT_ALL_METHOD_ACCESS);
		}
	}

	public void selectAll() {
		contributeToActionBars();
	}

	private void fillLocalToolBar() {
		toolbarManager.removeAll();
		fieldsWithRefinementsButton = setFieldsMethodsActions[ShowFieldsMethodsAction.FIELDS_WITH_REFINEMENTS];
		fieldsWithoutRefinementsButton = setFieldsMethodsActions[ShowFieldsMethodsAction.FIELDS_WITHOUT_REFINEMENTS];
		methodsWithRefinementsButton = setFieldsMethodsActions[ShowFieldsMethodsAction.METHODS_WITH_REFINEMENTS];
		methodsWithoutRefinementsButton = setFieldsMethodsActions[ShowFieldsMethodsAction.METHODS_WITHOUT_REFINEMENTS];
		showContracsButton = setFieldsMethodsActions[ShowFieldsMethodsAction.ONLY_CONTRACTS];
		showInvariantsButton = setFieldsMethodsActions[ShowFieldsMethodsAction.ONLY_INVARIANTS];
		showNestedClassesButton = setFieldsMethodsActions[ShowFieldsMethodsAction.SHOW_NESTED_CLASSES];

		final boolean[] isChecked = RoleFigure.getRoleSelections();
		for (int i = ShowFieldsMethodsAction.FIELDS_WITH_REFINEMENTS; i <= ShowFieldsMethodsAction.SHOW_NESTED_CLASSES; i++) {
			setFieldsMethodsActions[i].setChecked(isChecked[i]);
		}

		toolbarManager.add(showAccessModifiers);
		toolbarManager.add(fieldsWithRefinementsButton);
		toolbarManager.add(fieldsWithoutRefinementsButton);
		toolbarManager.add(methodsWithRefinementsButton);
		toolbarManager.add(methodsWithoutRefinementsButton);
		toolbarManager.add(showContracsButton);
		toolbarManager.add(showInvariantsButton);
		toolbarManager.add(showNestedClassesButton);

		reloadImage();

		toolbarManager.add(new Separator());

		refreshButton.setToolTipText(REFRESH_TOOL_TIP_LABEL);
		refreshButton.setImageDescriptor(ImageDescriptor.createFromImage(REFESH_TAB_IMAGE));

		exportAsImage = new ExportAsImageImpl(EXPORT_AS_IMAGE, viewer);
		exportAsImage.setImageDescriptor(ImageDescriptor.createFromImage(IMAGE_EXPORT_IMAGE_ICON));
		exportAsXML = new ExportAsXmlImpl(EXPORT_AS_XML, viewer);
		exportAsXML.setImageDescriptor(ImageDescriptor.createFromImage(IMAGE_EXPORT_XML_ICON));

		final Action exportAsToolbarIcon = new Action(EXPORT_AS___, IAction.AS_DROP_DOWN_MENU) {

			@Override
			public void run() {

			}
		};
		exportAsToolbarIcon.setMenuCreator(new IMenuCreator() {

			Menu fMenu = null;

			@Override
			public Menu getMenu(Menu parent) {
				return null;
			}

			@Override
			public Menu getMenu(Control parent) {
				fMenu = new Menu(parent);

				final ActionContributionItem exportImageContributionItem = new ActionContributionItem(exportAsImage);
				exportImageContributionItem.fill(fMenu, -1);
				final ActionContributionItem exportXMLContributionItem = new ActionContributionItem(exportAsXML);
				exportXMLContributionItem.fill(fMenu, -1);

				return fMenu;
			}

			@Override
			public void dispose() {}

		});
		exportAsToolbarIcon.setImageDescriptor(ImageDescriptor.createFromImage(IMAGE_EXPORT_ICON));
		toolbarManager.add(exportAsToolbarIcon);
		toolbarManager.add(refreshButton);
	}

	private void makeActions() {
		refreshButton = new Action() {

			@Override
			public void run() {
				disableToolbarFilterItems();
				final LongRunningMethod<Boolean> job = new LongRunningMethod<Boolean>() {

					@Override
					public Boolean execute(IMonitor workMonitor) throws Exception {
						if (!refreshButton.isEnabled()) {
							return true;
						}
						refreshButton.setEnabled(false);
						if (featureProject != null) {
							final IComposerExtensionClass composer = featureProject.getComposer();
							if (composer != null) {
								composer.buildFSTModel();
								updateGuiAfterBuild(featureProject, null);
							}
						}
						return true;
					}
				};
				final IRunner<Boolean> runner = LongRunningWrapper.getRunner(job, REFRESH_COLLABORATION_VIEW);
				if (runner instanceof LongRunningJob<?>) {
					((LongRunningJob<?>) runner).setPriority(Job.SHORT);
				}
				runner.schedule();
			}
		};
	}

	@Override
	public void updateGuiAfterBuild(final IFeatureProject project, final IFile configurationFile) {
		if ((featureProject != null) && featureProject.equals(project)) {
			if (configurationFile == null) {
				configurations.add(project.getCurrentConfiguration());
			} else {
				configurations.add(configurationFile);
			}
			updateGUIJob.setPriority(Job.LONG);
			updateGUIJob.schedule();
		}
	}

	@Override
	public void doSaveAs() {
		GraphicsExporter.exportAs(viewer);
	}

	@Override
	public void doSave(IProgressMonitor monitor) {}

	@Override
	public boolean isDirty() {
		return false;
	}

	@Override
	public boolean isSaveAsAllowed() {
		return true;
	}

	@Override
	public boolean isSaveOnCloseNeeded() {
		return false;
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	@Override
	public Object getAdapter(Class adapter) {
		if (GraphicalViewer.class.equals(adapter) || ViewPart.class.equals(adapter)) {
			return viewer;
		}
		return super.getAdapter(adapter);
	}

	public void refresh() {
		refreshActionBars();

		final FSTModel model = builder.buildCollaborationModel(featureProject);

		if (model == null) {
			UIPlugin.getDefault().logWarning(MODEL_LOADING_ERROR);
			return;
		}
		Display.getDefault().syncExec(new Runnable() {

			@Override
			public void run() {
				viewer.setContents(model);
				viewer.getContents().refresh();
				search.refreshSearchContent();
			}
		});
	}

	public void refreshAll() {
		refreshButton.run();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#dispose()
	 */
	@Override
	public void dispose() {
		FeatureColorManager.removeListener(colorChangeListener);
		super.dispose();
	}
}
