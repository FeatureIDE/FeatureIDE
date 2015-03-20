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
package de.ovgu.featureide.ui.views.collaboration;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
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
import org.eclipse.jface.action.IMenuCreator;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
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
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.listeners.ICurrentBuildListener;
import de.ovgu.featureide.fm.core.AWaitingJob;
import de.ovgu.featureide.fm.core.ColorList;
import de.ovgu.featureide.fm.core.ColorschemeTable;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.job.AStoppableJob;
import de.ovgu.featureide.fm.ui.GraphicsExporter;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.editors.annotation.ColorPalette;
import de.ovgu.featureide.ui.views.collaboration.action.AddColorSchemeAction;
import de.ovgu.featureide.ui.views.collaboration.action.AddRoleAction;
import de.ovgu.featureide.ui.views.collaboration.action.DeleteAction;
import de.ovgu.featureide.ui.views.collaboration.action.DeleteColorSchemeAction;
import de.ovgu.featureide.ui.views.collaboration.action.ExportAsImageImpl;
import de.ovgu.featureide.ui.views.collaboration.action.ExportAsXmlImpl;
import de.ovgu.featureide.ui.views.collaboration.action.FilterAction;
import de.ovgu.featureide.ui.views.collaboration.action.RenameColorSchemeAction;
import de.ovgu.featureide.ui.views.collaboration.action.SetColorAction;
import de.ovgu.featureide.ui.views.collaboration.action.SetColorSchemeAction;
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
 */

public class CollaborationView extends ViewPart implements GUIDefaults, ICurrentBuildListener, ISaveablePart {

	private static final String UPDATE_COLLABORATION_VIEW = "Update Collaboration View";

	public static final String ID = UIPlugin.PLUGIN_ID + ".views.collaboration.Collaboration";

	private static final String OPEN_MESSAGE = "Open a file from a FeatureIDE project";

	private static final String ADD_LABEL = "Add new Class / Role";
	private static final String FILTER_LABEL = "Filter";
	private static final String DELETE_LABEL = "Delete";
	private static final String UNSELECTED_LABEL = "Show unselected features";
	private static final String EXPORT_AS_LABEL = "Export As";

	private static final String REFRESH_TOOL_TIP_LABEL = "Build collaborationmodel";

	private static final String[] FIELD_METHOD_LABEL_NAMES = { "Fields with Refinements", "Fields without Refinements", "Methods with Refinements",
			"Methods without Refinements", "Show Method Contracts", "Show Class Invariants", "Show Nested Classes", "Hide Parameters/Types", "Public",
			"Protected", "Default", "Private", "Select All", "Deselect All", };

	private static final Image[] FIELD_METHOD_IMAGES = { IMAGE_FIELDS_REFINEMENTS, IMAGE_FIELDS_WITHOUT_REFINEMENTS, IMAGE_METHODS_REFINEMENTS,
			IMAGE_METHODS_WITHOUT_REFINEMENTS, IMAGE_AT_CONTRACT, IMAGE_AT_INVARIANT, IMAGE_NESTED_CLASS, null, IMAGE_METHODE_PUBLIC, IMAGE_METHODE_PROTECTED,
			IMAGE_METHODE_DEFAULT, IMAGE_METHODE_PRIVATE, IMAGE_SELECT_ALL, IMAGE_DESELECT_ALL };

	private GraphicalViewerImpl viewer;
	private CollaborationModelBuilder builder = new CollaborationModelBuilder();
	private IWorkbenchPart currentEditor;
	private AddRoleAction addRoleAction;
	private DeleteAction delAction;
	private Action refreshButton;
	private FilterAction filterAction;
	private PrintAction printAction;
	private ShowUnselectedAction showUnselectedAction;
	private Point cursorPosition;
	private CollaborationViewSearch search;
	private MenuManager colorSubMenu;
	private AddColorSchemeAction addColorSchemeAction;
	private RenameColorSchemeAction renameColorSchemeAction;
	private DeleteColorSchemeAction deleteColorSchemeAction;
	private ExportAsImageImpl exportAsImage;
	private ExportAsXmlImpl exportAsXML;

	private ShowFieldsMethodsAction fieldsWithRefinementsButton;
	private ShowFieldsMethodsAction fieldsWithoutRefinementsButton;
	private ShowFieldsMethodsAction methodsWithRefinementsButton;
	private ShowFieldsMethodsAction methodsWithoutRefinementsButton;
	private ShowFieldsMethodsAction showContracsButton;
	private ShowFieldsMethodsAction showInvariantsButton;
	private ShowFieldsMethodsAction showNestedClassesButton;

	private SetColorAction[] setColorActions = new SetColorAction[ColorPalette.COLOR_COUNT];
	private ShowFieldsMethodsAction[] setFieldsMethodsActions = new ShowFieldsMethodsAction[FIELD_METHOD_LABEL_NAMES.length];

	private ShowFieldsMethodsAction showAccessModifiers;

	private IToolBarManager toolbarManager;

	private final Vector<IFile> configurations = new Vector<IFile>();
	private final Job updateGUIJob = new AWaitingJob(UPDATE_COLLABORATION_VIEW) {

		public IStatus execute(IProgressMonitor monitor) {
			disableToolbarFilterItems();
			if (configurations.isEmpty()) {
				refreshButton.setEnabled(true);
				return Status.OK_STATUS;
			}
			IFile configurationFile = configurations.lastElement();
			configurations.clear();
			if (configurationFile != null && CollaborationModelBuilder.editorFile != null) {
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
			UIJob uiJob = new UIJob(UPDATE_COLLABORATION_VIEW) {
				public IStatus runInUIThread(IProgressMonitor monitor) {
					viewer.setContents(model);
					EditPart part = viewer.getContents();
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
			} catch (InterruptedException e) {
				UIPlugin.getDefault().logError(e);
			}
			return Status.OK_STATUS;
		}
	};

	private IFeatureProject featureProject;

	public IFeatureProject getFeatureProject() {
		return featureProject;
	}

	public Point getCursorPosition() {
		return cursorPosition;
	}

	private void saveCursorPosition() {
		Display display = Display.getDefault();
		FigureCanvas figureCanvas = (FigureCanvas) viewer.getControl();
		Point point = figureCanvas.toControl(display.getCursorLocation());
		Viewport viewport = figureCanvas.getViewport();
		org.eclipse.draw2d.geometry.Point location = viewport.getViewLocation();
		viewport.setIgnoreScroll(true);

		int x = point.x + location.x;
		int y = point.y + location.y;
		Rectangle bounds = viewport.getBounds();
		if (point.x < 0)
			x += bounds.width;
		if (point.y < 0)
			y += bounds.height;

		this.cursorPosition = new Point(x, y);
	}

	private IPartListener editorListener = new IPartListener() {

		public void partOpened(IWorkbenchPart part) {

		}

		public void partDeactivated(IWorkbenchPart part) {

		}

		public void partClosed(IWorkbenchPart part) {
			if (part == currentEditor) {
				setEditorActions(null);
			}
		}

		public void partBroughtToTop(IWorkbenchPart part) {
			if (part instanceof IEditorPart) {
				setEditorActions(part);
			}

		}

		public void partActivated(IWorkbenchPart part) {
			if (part instanceof IEditorPart || part instanceof ViewPart) {
				setEditorActions(part);
			}
		}

	};

	public void createPartControl(Composite parent) {
		IWorkbenchWindow editor = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		IEditorPart part = null;

		if (editor != null) {
			IWorkbenchPage page = editor.getActivePage();
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
		ScalableFreeformRootEditPart rootEditPart = new ScalableFreeformRootEditPart();
		((ConnectionLayer) rootEditPart.getLayer(LayerConstants.CONNECTION_LAYER)).setAntialias(SWT.ON);

		viewer.setRootEditPart(rootEditPart);
		viewer.setEditDomain(new EditDomain());
		viewer.setEditPartFactory(new GraphicalEditPartFactory());

		int select = ShowFieldsMethodsAction.SELECT_ALL_METHOD_ACCESS;
		if (deselectAll()) {
			select = ShowFieldsMethodsAction.DESELECT_ALL_METHOD_ACCESS;
		}
		showAccessModifiers = new ShowFieldsMethodsAction("", null, this, select, Action.AS_DROP_DOWN_MENU);
		showAccessModifiers.setToolTipText("Change filter for access modifiers");
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
					ShowFieldsMethodsAction action = setFieldsMethodsActions[i];
					action.setChecked(RoleFigure.getRoleSelections()[i]);
					ActionContributionItem contributionItem = new ActionContributionItem(action);
					contributionItem.fill(fMenu, -1);
				}

				ShowFieldsMethodsAction selectAll = new ShowFieldsMethodsAction("Select all", IMAGE_SELECT_ALL_MODIFIERS, CollaborationView.this,
						ShowFieldsMethodsAction.SELECT_ALL_METHOD_ACCESS);
				ActionContributionItem contributionItem = new ActionContributionItem(selectAll);
				contributionItem.fill(fMenu, -1);

				ShowFieldsMethodsAction deselectAll = new ShowFieldsMethodsAction("Deselect all", IMAGE_MODIFIERS_NONE, CollaborationView.this,
						ShowFieldsMethodsAction.DESELECT_ALL_METHOD_ACCESS);
				ActionContributionItem deselectAllConteribution = new ActionContributionItem(deselectAll);
				deselectAllConteribution.fill(fMenu, -1);

				return fMenu;
			}

			@Override
			public void dispose() {
			}
		});

		createContextMenu();
		createActions(part);
		makeActions();
		contributeToActionBars();

		CollaborationViewSearch.Builder builder = new CollaborationViewSearch.Builder();
		search = builder.setAttachedViewerParent(viewer).setSearchBoxText("Search in Collaboration Diagram").setFindResultsColor(ROLE_BACKGROUND_SELECTED)
				.setNoSearchResultsColor(ROLE_BACKGROUND_UNSELECTED).create();

	}

	private void refreshActionBars() {
		IActionBars bars = getViewSite().getActionBars();
		bars.getToolBarManager().update(true);
		disableToolbarFilterItems();
	}

	private void contributeToActionBars() {
		IActionBars bars = getViewSite().getActionBars();

		bars.setGlobalActionHandler(ActionFactory.PRINT.getId(), printAction);
		toolbarManager = bars.getToolBarManager();
		fillLocalToolBar();
	}

	public void setFocus() {
		FigureCanvas figureCanvas = (FigureCanvas) viewer.getControl();

		Viewport model = figureCanvas.getViewport();
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
		featureProject = null;

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

		if (activeEditor != null && activeEditor.getEditorInput() instanceof FileEditorInput) {
			// case: open editor
			final IFile inputFile = ((FileEditorInput) activeEditor.getEditorInput()).getFile();
			featureProject = CorePlugin.getFeatureProject(inputFile);

			if (featureProject != null) {
				// case: it's a FeatureIDE project
				featureProject.getFeatureModel().addListener(new PropertyChangeListener() {
					@Override
					public void propertyChange(PropertyChangeEvent event) {
						if (PropertyConstants.MODEL_DATA_LOADED.equals(event.getPropertyName())) {
							readColorsFromFile();
						}
					}
				});

				readColorsFromFile();

				if (CorePlugin.getDefault().getConfigurationExtensions().contains(inputFile.getFileExtension())) {
					// case: open configuration editor
					CollaborationModelBuilder.editorFile = null;
					if (builder.configuration != null && builder.configuration.equals(inputFile) && featureProject.equals(CollaborationModelBuilder.project)) {
						return;
					} else {
						builder.configuration = inputFile;
					}
				} else {
					// case: open editor is no configuration editor
					if (CollaborationModelBuilder.editorFile != null && CollaborationModelBuilder.editorFile.getName().equals(inputFile.getName())
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
		MenuManager menuMgr = new MenuManager("#PopupMenu");
		menuMgr.setRemoveAllWhenShown(true);

		menuMgr.addMenuListener(new IMenuListener() {
			public void menuAboutToShow(IMenuManager m) {
				fillContextMenu(m);
			}
		});
		Control control = viewer.getControl();
		Menu menu = menuMgr.createContextMenu(control);
		control.setMenu(menu);
		getSite().registerContextMenu(menuMgr, viewer);

		colorSubMenu = new MenuManager("Color");
	}

	private void fillContextMenu(IMenuManager menuMgr) {
		disableToolbarFilterItems();
		if (featureProject == null) {
			return;
		}
		boolean isNotEmpty = !viewer.getSelection().isEmpty();
		addRoleAction.setEnabled(isNotEmpty);
		filterAction.setEnabled(isNotEmpty);
		delAction.setEnabled(isNotEmpty);
		showUnselectedAction.setEnabled(isNotEmpty);

		saveCursorPosition();

		menuMgr.add(addRoleAction);
		menuMgr.add(filterAction);
		menuMgr.add(showUnselectedAction);
		menuMgr.add(delAction);

		if (featureProject.getComposer().showContextFieldsAndMethods()) {
			MenuManager methodsFieldsSubMenu = new MenuManager("Show Fields and Methods");

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

		Object selection = ((IStructuredSelection) viewer.getSelection()).getFirstElement();
		if (selection instanceof CollaborationEditPart) {
			FSTFeature coll = ((CollaborationEditPart) selection).getCollaborationModel();
			if (!(coll instanceof FSTConfiguration)) {
				FeatureModel fm = featureProject.getFeatureModel();
				ColorschemeTable colorschemeTable = fm.getColorschemeTable();
				List<String> csNames = colorschemeTable.getColorschemeNames();

				String curColorSchemeName = colorschemeTable.getSelectedColorschemeName();
				MenuManager colorSchemeSubMenu = null;

				if (curColorSchemeName != null) {
					colorSchemeSubMenu = new MenuManager(curColorSchemeName);
				} else {
					colorSchemeSubMenu = new MenuManager("No Colorscheme Selected");
				}

				int count = 0;
				for (String name : csNames) {
					SetColorSchemeAction setCSAction = new SetColorSchemeAction(name, viewer, this, ++count);
					if (count == colorschemeTable.getSelectedColorscheme()) {
						setCSAction.setChecked(true);
					}
					colorSchemeSubMenu.add(setCSAction);
				}

				colorSchemeSubMenu.add(new Separator());
				colorSchemeSubMenu.add(addColorSchemeAction);
				colorSchemeSubMenu.add(renameColorSchemeAction);
				colorSchemeSubMenu.add(deleteColorSchemeAction);
				colorSubMenu.removeAll();
				colorSubMenu.add(colorSchemeSubMenu);
				colorSubMenu.add(new Separator());

				boolean enableColorActions = colorschemeTable.getSelectedColorscheme() > 0;
				for (int i = 0; i < setColorActions.length; i++) {
					setColorActions[i].setEnabled(enableColorActions);
					setColorActions[i].setChecked(false);
					colorSubMenu.add(setColorActions[i]);
				}

				int color = fm.getFeature(coll.getName()).getColorList().getColor();
				if (ColorList.isValidColor(color)) {
					setColorActions[color].setChecked(true);
				}

				menuMgr.add(colorSubMenu);
			}
		}

		menuMgr.add(new Separator());
		MenuManager exportMenu = new MenuManager(EXPORT_AS_LABEL);
		exportMenu.add(exportAsImage);
		exportMenu.add(exportAsXML);
		menuMgr.add(exportMenu);
	}

	public void disableToolbarFilterItems() {
		boolean value = false;

		if (featureProject != null && featureProject.getComposer().showContextFieldsAndMethods()) {
			value = true;
		} else {
			value = false;
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

		for (int i = 0; i < FIELD_METHOD_LABEL_NAMES.length; i++) {
			setFieldsMethodsActions[i] = new ShowFieldsMethodsAction(FIELD_METHOD_LABEL_NAMES[i], FIELD_METHOD_IMAGES[i], this, i);
		}

		printAction = new PrintAction(this);

		for (int i = 0; i < setColorActions.length; i++) {
			setColorActions[i] = new SetColorAction(viewer, this, i);
		}

		addColorSchemeAction = new AddColorSchemeAction("&Add Colorscheme", viewer, this);
		renameColorSchemeAction = new RenameColorSchemeAction("&Rename Selected Colorscheme", viewer, this);
		deleteColorSchemeAction = new DeleteColorSchemeAction("&Delete Selected Colorscheme", viewer, this);
	}

	private boolean deselectAll() {
		boolean[] selectedModifiers = RoleFigure.getRoleSelections();
		if ((selectedModifiers[ShowFieldsMethodsAction.PUBLIC_FIELDSMETHODS]) && (selectedModifiers[ShowFieldsMethodsAction.PRIVATE_FIELDSMETHODS])
				&& (selectedModifiers[ShowFieldsMethodsAction.PROTECTED_FIELDSMETHODS]) && (selectedModifiers[ShowFieldsMethodsAction.DEFAULT_FIELDSMETHODS])) {
			return true;
		}
		return false;
	}

	private ImageDescriptor getAccessModifiersImage(boolean[] selectedModifiers) {
		ArrayList<Image> arrayList = new ArrayList<Image>();
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

		Image combinedImages = combineImages(arrayList);

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

		Image finalImage = new Image(images.get(0).getDevice(), images.get(0).getBounds());
		ImageData data = null;
		org.eclipse.swt.graphics.GC gc = new org.eclipse.swt.graphics.GC(finalImage);
		int x = 0;
		int y = 0;

		for (int j = 0; j < images.size(); j++) {
			if (images.size() == 1) {
				x = finalImage.getBounds().width / 4;
				y = finalImage.getBounds().width / 4;
			} else if ((j + 1) % 2 != 0) {
				x = 0;
				y = (j / 2) * 8;
			} else {
				x = 8;
			}
			gc.drawImage(images.get(j), 4, 4, images.get(j).getBounds().width - 2 * 4, images.get(j).getBounds().height - 2 * 4, x, y,
					finalImage.getBounds().width / 2, finalImage.getBounds().height / 2);

		}
		data = finalImage.getImageData();
		data.transparentPixel = finalImage.getImageData().palette.getPixel(new RGB(255, 255, 255));
		gc.dispose();

		return new Image(images.get(0).getDevice(), data);
	}

	public void reloadImage() {
		// build one image from max 4 images
		boolean[] selectedAccessModifiers = RoleFigure.getRoleSelections();
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

		boolean[] isChecked = RoleFigure.getRoleSelections();
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

		exportAsImage = new ExportAsImageImpl("Export as image", viewer);
		exportAsImage.setImageDescriptor(ImageDescriptor.createFromImage(IMAGE_EXPORT_IMAGE_ICON));
		exportAsXML = new ExportAsXmlImpl("Export as XML", viewer);
		exportAsXML.setImageDescriptor(ImageDescriptor.createFromImage(IMAGE_EXPORT_XML_ICON));

		Action exportAsToolbarIcon = new Action("Export as...", Action.AS_DROP_DOWN_MENU) {
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

				ActionContributionItem exportImageContributionItem = new ActionContributionItem(exportAsImage);
				exportImageContributionItem.fill(fMenu, -1);
				ActionContributionItem exportXMLContributionItem = new ActionContributionItem(exportAsXML);
				exportXMLContributionItem.fill(fMenu, -1);

				return fMenu;
			}

			@Override
			public void dispose() {
			}

		});
		exportAsToolbarIcon.setImageDescriptor(ImageDescriptor.createFromImage(IMAGE_EXPORT_ICON));
		toolbarManager.add(exportAsToolbarIcon);
		toolbarManager.add(refreshButton);
	}

	private void makeActions() {
		refreshButton = new Action() {
			public void run() {
				disableToolbarFilterItems();
				Job refreshJob = new AStoppableJob("Refresh Collaboration View") {
					@Override
					protected boolean work() throws Exception {
						if (!refreshButton.isEnabled())
							return true;
						refreshButton.setEnabled(false);
						if (featureProject != null) {
							IComposerExtensionClass composer = featureProject.getComposer();
							if (composer != null) {
								composer.buildFSTModel();
								updateGuiAfterBuild(featureProject, null);
							}
						}
						return true;
					}
				};
				refreshJob.setPriority(Job.SHORT);
				refreshJob.schedule();
			}
		};
	}

	public void updateGuiAfterBuild(final IFeatureProject project, final IFile configurationFile) {
		if (featureProject != null && featureProject.equals(project)) {
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
	public void doSave(IProgressMonitor monitor) {
	}

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

	@SuppressWarnings("rawtypes")
	@Override
	public Object getAdapter(Class adapter) {
		if (GraphicalViewer.class.equals(adapter) || ViewPart.class.equals(adapter))
			return viewer;

		return super.getAdapter(adapter);
	}

	public void refresh() {
		refreshActionBars();

		final FSTModel model = builder.buildCollaborationModel(featureProject);

		if (model == null) {
			UIPlugin.getDefault().logWarning("model loading error");
			return;
		}
		Display.getDefault().syncExec(new Runnable() {
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

	public void saveColorsToFile() {
		featureProject.getFeatureModel().getColorschemeTable().saveColorsToFile(featureProject.getProject());
	}

	private void readColorsFromFile() {
		featureProject.getFeatureModel().getColorschemeTable().readColorsFromFile(featureProject.getProject());
	}

}
