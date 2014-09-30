/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.views.collaboration;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
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
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
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
import de.ovgu.featureide.fm.core.ColorList;
import de.ovgu.featureide.fm.core.ColorschemeTable;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.StoppableJob;
import de.ovgu.featureide.fm.core.WaitingJob;
import de.ovgu.featureide.fm.ui.GraphicsExporter;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.editors.annotation.ColorPalette;
import de.ovgu.featureide.ui.views.collaboration.action.AddColorSchemeAction;
import de.ovgu.featureide.ui.views.collaboration.action.AddRoleAction;
import de.ovgu.featureide.ui.views.collaboration.action.DeleteAction;
import de.ovgu.featureide.ui.views.collaboration.action.DeleteColorSchemeAction;
import de.ovgu.featureide.ui.views.collaboration.action.ExportAsAction;
import de.ovgu.featureide.ui.views.collaboration.action.FilterAction;
import de.ovgu.featureide.ui.views.collaboration.action.RenameColorSchemeAction;
import de.ovgu.featureide.ui.views.collaboration.action.SetColorAction;
import de.ovgu.featureide.ui.views.collaboration.action.SetColorSchemeAction;
import de.ovgu.featureide.ui.views.collaboration.action.ShowFieldsMethodsAction;
import de.ovgu.featureide.ui.views.collaboration.action.ShowUnselectedAction;
import de.ovgu.featureide.ui.views.collaboration.editparts.CollaborationEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.GraphicalEditPartFactory;
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
 */
public class CollaborationView extends ViewPart implements GUIDefaults, ICurrentBuildListener, ISaveablePart {

	private static final String UPDATE_COLLABORATION_VIEW = "Update Collaboration View";

	public static final String ID = UIPlugin.PLUGIN_ID + ".views.collaboration.Collaboration";
	
	private static final String OPEN_MESSAGE = "Open a file from a FeatureIDE project";

	private static final String ADD_LABEL = "Add new Class / Role";
	private static final String DELETE_LABEL = "Delete";
	private static final String FILTER_LABEL = "Filter";
	private static final String UNSELECTED_LABEL = "Show unselected features";
	private static final String EXPORT_AS_LABEL = "Export As";
	
	private static final String TOOL_TIP_LABEL = "Build collaborationmodel";
	
	private static final String[] FIELD_METHOD_LABEL_NAMES = { "Show Fields", "Show Methods", "Show Method Contracts", "Show Class Invariants", "Hide Parameters/Types", "Public", "Protected", "Default",
			"Private", "Select All", "Deselect All", };
	
	private static final Image[] FIELD_METHOD_IMAGES = { null, null, IMAGE_AT, IMAGE_AT,  null, IMAGE_METHODE_PUBLIC, IMAGE_METHODE_PROTECTED, IMAGE_METHODE_DEFAULT,
			IMAGE_METHODE_PRIVATE, null, null };
	
	private GraphicalViewerImpl viewer;
	private CollaborationModelBuilder builder = new CollaborationModelBuilder();
	private IWorkbenchPart currentEditor;
	
	private AddRoleAction addRoleAction;
	private DeleteAction delAction;
	private Action toolbarAction;
	private FilterAction filterAction;
	private PrintAction printAction;
	private ExportAsAction exportAsAction;
	private ShowUnselectedAction showUnselectedAction;
	private Point cursorPosition;
	
	private MenuManager colorSubMenu;
	private AddColorSchemeAction addColorSchemeAction;
	private RenameColorSchemeAction renameColorSchemeAction;
	private DeleteColorSchemeAction deleteColorSchemeAction;
	
	private SetColorAction[] setColorActions = new SetColorAction[ColorPalette.COLOR_COUNT];
	private ShowFieldsMethodsAction[] setFieldsMethodsActions = new ShowFieldsMethodsAction[FIELD_METHOD_LABEL_NAMES.length];

	private final Vector<IFile> configurations = new Vector<IFile>();
	private final Job updateGUIJob = new WaitingJob(UPDATE_COLLABORATION_VIEW) {
		
		public IStatus execute(IProgressMonitor monitor) {
			if (configurations.isEmpty()) {
				toolbarAction.setEnabled(true);
				return Status.OK_STATUS;
			}
			IFile configurationFile = configurations.lastElement();
			configurations.clear();
			if (configurationFile != null && CollaborationModelBuilder.editorFile != null) {
				builder.configuration = configurationFile;
			}
			final FSTModel model = builder.buildCollaborationModel(CorePlugin.getFeatureProject(configurationFile));
			if (model == null) {
				toolbarAction.setEnabled(true);
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
					toolbarAction.setEnabled(true);
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
		
		createContextMenu();
		createActions(part);
		makeActions();
		contributeToActionBars();
	}
	
	private void contributeToActionBars() {
		IActionBars bars = getViewSite().getActionBars();
		
		bars.setGlobalActionHandler(ActionFactory.PRINT.getId(), printAction);
		
		fillLocalToolBar(bars.getToolBarManager());
	}
	
	/*
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
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
	
	private void createContextMenu() {
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
				
				if ((i == ShowFieldsMethodsAction.ONLY_INVARIANTS) || (i == ShowFieldsMethodsAction.PRIVATE_FIELDSMETHODS)
						|| (i == ShowFieldsMethodsAction.HIDE_PARAMETERS_AND_TYPES)) {
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
		menuMgr.add(exportAsAction);
	}
	
	private void createActions(IEditorPart part) {
		addRoleAction = new AddRoleAction(ADD_LABEL, viewer, this);
		delAction = new DeleteAction(DELETE_LABEL, viewer);
		filterAction = new FilterAction(FILTER_LABEL, viewer, this);
		exportAsAction = new ExportAsAction(EXPORT_AS_LABEL,viewer);
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
	
	private void fillLocalToolBar(IToolBarManager manager) {
		manager.add(toolbarAction);
		toolbarAction.setToolTipText(TOOL_TIP_LABEL);
		toolbarAction.setImageDescriptor(ImageDescriptor.createFromImage(REFESH_TAB_IMAGE));
	}
	
	private void makeActions() {
		toolbarAction = new Action() {
			public void run() {
				Job job = new StoppableJob("Refresh Collaboration View") {
					protected IStatus execute(IProgressMonitor monitor) {
						if (!toolbarAction.isEnabled())
							return Status.OK_STATUS;
						toolbarAction.setEnabled(false);
						if (featureProject != null) {
							IComposerExtensionClass composer = featureProject.getComposer();
							if (composer != null) {
								composer.buildFSTModel();
								updateGuiAfterBuild(featureProject, null);
							}
						}
						return Status.OK_STATUS;
					}
				};
				job.setPriority(Job.SHORT);
				job.schedule();
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
	
	@SuppressWarnings("rawtypes")
	@Override
	public Object getAdapter(Class adapter) {
		if (GraphicalViewer.class.equals(adapter) || ViewPart.class.equals(adapter))
			return viewer;
		
		return super.getAdapter(adapter);
	}
	
	public void refresh() {
		final FSTModel model = builder.buildCollaborationModel(featureProject);
		if (model == null) {
			UIPlugin.getDefault().logWarning("model loading error");
			return;
		}
		Display.getDefault().syncExec(new Runnable() {
			public void run() {
				viewer.setContents(model);
				viewer.getContents().refresh();
			}
		});
	}
	
	public void refreshAll() {
		toolbarAction.run();
	}
	
	public void saveColorsToFile() {
		featureProject.getFeatureModel().getColorschemeTable().saveColorsToFile(featureProject.getProject());
	}
	
	private void readColorsFromFile() {
		featureProject.getFeatureModel().getColorschemeTable().readColorsFromFile(featureProject.getProject());
	}
	
}
