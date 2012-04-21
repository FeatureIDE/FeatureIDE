/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.views.collaboration;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.draw2d.ConnectionLayer;
import org.eclipse.gef.EditDomain;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.listeners.ICurrentBuildListener;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.action.AddRoleAction;
import de.ovgu.featureide.ui.views.collaboration.action.DeleteAction;
import de.ovgu.featureide.ui.views.collaboration.action.FilterAction;
import de.ovgu.featureide.ui.views.collaboration.action.ShowUnselectedAction;
import de.ovgu.featureide.ui.views.collaboration.editparts.GraphicalEditPartFactory;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModel;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModelBuilder;

/**
 * View of the collaboration diagram.
 * 
 * @author Constanze Adler
 * @author Jens Meinicke
 * @author Stephan Besecke
 */
public class CollaborationView extends ViewPart implements GUIDefaults, ICurrentBuildListener{
	
	public static final String ID = UIPlugin.PLUGIN_ID + ".views.collaboration.Collaboration";
	
	private static final String OPEN_MESSAGE = "Open a file from a FeatureIDE project";
	private static final String CONFIGURATION_MESSAGE = "Please create a new configuration file";
	
	private static final String ADD_LABEL = "Add new Class / Role";
	private static final String DELETE_LABEL = "Delete";
	private static final String FILTER_LABEL = "Filter";
	private static final String UNSELECTED_LABEL = "Show unselected features";
	private static final String TOOL_TIP_LABEL = "Build collaborationmodel";
	
	private GraphicalViewerImpl viewer;
	public CollaborationModelBuilder builder = new CollaborationModelBuilder();
	private CollaborationModel model = new CollaborationModel();
	
	private AddRoleAction addRoleAction;
	private DeleteAction delAction;
	private Action toolbarAction;
	private FilterAction filterAction;
	private ShowUnselectedAction showUnselectedAction; 
	
	private IFeatureProject featureProject;
	
	public IFeatureProject getFeatureProject() {
		return featureProject;
	}
	
	private IPartListener editorListener = new IPartListener() {
		
		public void partOpened(IWorkbenchPart part) {
		}

		public void partDeactivated(IWorkbenchPart part) {
		}

		public void partClosed(IWorkbenchPart part) {
		}

		public void partBroughtToTop(IWorkbenchPart part) {
			if (part instanceof IEditorPart)
				setEditorActions(part);
		}

		public void partActivated(IWorkbenchPart part) {
			if (part instanceof IViewPart)
				setEditorActions(part);
		}

	};
	
	/*
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
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
		
		ScalableFreeformRootEditPart rootEditPart = new ScalableFreeformRootEditPart(); // required for borders
		((ConnectionLayer) rootEditPart
				.getLayer(LayerConstants.CONNECTION_LAYER))
				.setAntialias(SWT.ON);

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
		 fillLocalToolBar(bars.getToolBarManager());
	 }
	
	/*
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	public void setFocus() {
		viewer.getControl().setFocus();
	}
	
	private void setEditorActions(IWorkbenchPart activeEditor) {
		IEditorPart part = null;
		if (activeEditor != null) {
			IWorkbenchPage page = activeEditor.getSite().getPage();
			if (page != null) {
				part = page.getActiveEditor();
				if (part != null && part.getEditorInput() instanceof FileEditorInput) {
					//case: open editor
					IFile inputFile = ((FileEditorInput)part.getEditorInput()).getFile();
					featureProject = CorePlugin.getFeatureProject(inputFile);
					if (featureProject != null) {
						//case: it's a featureIDE project
						String fileName = inputFile.getName();
						if (fileName.contains(".") &&
								CorePlugin.getDefault().getConfigurationExtensions()
								.contains(fileName.substring(fileName.lastIndexOf('.')))) {
							//case: open configuration editor
							builder.editorFile = null;
							if (builder.configuration != null &&
									builder.configuration.equals(inputFile) &&
									featureProject.equals(builder.project)) {
								return;
							} else {
								builder.configuration = inputFile;
							}
							
						} else {
							//case: open editor is no configuration editor
							if (builder.editorFile != null &&
									builder.editorFile.getName().equals(inputFile.getName()) &&
									featureProject.getProject().equals(builder.editorFile.getProject())) {
								return;
							}
							builder.editorFile = inputFile;
							builder.configuration = featureProject.getCurrentConfiguration();
						}
					}
				}
			}
		}
		
		if (featureProject == null) {
			model = new CollaborationModel();
			model.collaborations.add(new Collaboration(OPEN_MESSAGE));
			viewer.setContents(model);
		} else {
			if (featureProject.getCurrentConfiguration() == null){
				model = new CollaborationModel();
				model.collaborations.add(new Collaboration(CONFIGURATION_MESSAGE));
				viewer.setContents(model);
			} else
				updateGuiAfterBuild(featureProject, null);
		}
	}
	
	private void createContextMenu() {
		
		MenuManager menuMgr = new MenuManager("#PopupMenu");
		menuMgr.setRemoveAllWhenShown(true);
		
		menuMgr.addMenuListener(new IMenuListener(){
			public void menuAboutToShow(IMenuManager m){
				fillContextMenu(m);
			}
		});
		
		Menu menu = menuMgr.createContextMenu(viewer.getControl());
		viewer.getControl().setMenu(menu);
		getSite().registerContextMenu(menuMgr, viewer);
	}
	
	private void fillContextMenu(IMenuManager menuMgr){
		boolean isEmpty = viewer.getSelection().isEmpty();
		addRoleAction.setEnabled(!isEmpty);
		filterAction.setEnabled(!isEmpty);
		delAction.setEnabled(!isEmpty);
		showUnselectedAction.setEnabled(!isEmpty);
		
		menuMgr.add(addRoleAction);
		menuMgr.add(filterAction);
		menuMgr.add(showUnselectedAction);
		menuMgr.add(delAction);
	}

	private void createActions(IEditorPart part) {
		addRoleAction	= new AddRoleAction(ADD_LABEL, viewer, this);
		delAction		= new DeleteAction(DELETE_LABEL, viewer);
		filterAction	= new FilterAction(FILTER_LABEL,viewer,this,model);
		showUnselectedAction = new ShowUnselectedAction(UNSELECTED_LABEL,viewer,this,model);
	}
	
	private void fillLocalToolBar(IToolBarManager manager) {
		manager.add(toolbarAction);
		toolbarAction.setToolTipText(TOOL_TIP_LABEL);
		toolbarAction.setImageDescriptor(ImageDescriptor.createFromImage(REFESH_TAB_IMAGE));
	}
	
	private void makeActions() {
		toolbarAction = new Action() {
			public void run() {
				Job job = new Job("Refresh Collaboration View") {
					protected IStatus run(IProgressMonitor monitor) {
						if (!toolbarAction.isEnabled())
							return Status.OK_STATUS;
						toolbarAction.setEnabled(false);
						builded = true;
						if (featureProject != null) {
							// TODO @Jens check this method
							IComposerExtension composer = featureProject.getComposer();
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
	
	private boolean builded = true; 
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.listeners.ICurrentBuildListener#updateGuiAfterBuild(de.ovgu.featureide.core.IFeatureProject)
	 */
	public void updateGuiAfterBuild(final IFeatureProject project, final IFile configurationFile) {
		if (featureProject != null && featureProject.equals(project)) {
			Job job = new Job("Build Collaboration Model") {

				public IStatus run(IProgressMonitor monitor) {
					if (builded) {
						builded = false;
						if (configurationFile != null && builder.editorFile != null) {
							builder.configuration = configurationFile;
						}
						model = builder.buildCollaborationModel(project);
						builded = true;
						if (model == null) {
							toolbarAction.setEnabled(true);
							return Status.OK_STATUS;
						}
					
						UIJob uiJob = new UIJob("Update Collaboration View") {
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
						uiJob.setPriority(Job.DECORATE);
						uiJob.schedule();
					}
					return Status.OK_STATUS;
				}
			};
			job.setPriority(Job.DECORATE);
			job.schedule();
		}
	}
}