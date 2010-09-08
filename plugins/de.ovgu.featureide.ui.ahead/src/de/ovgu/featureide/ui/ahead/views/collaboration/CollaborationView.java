/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.ahead.views.collaboration;

import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.draw2d.ConnectionLayer;
import org.eclipse.gef.EditDomain;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
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
import de.ovgu.featureide.core.listeners.ICurrentBuildListener;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.ui.ahead.AheadUIPlugin;
import de.ovgu.featureide.ui.ahead.views.collaboration.action.AddClassAction;
import de.ovgu.featureide.ui.ahead.views.collaboration.action.DeleteAction;
import de.ovgu.featureide.ui.ahead.views.collaboration.action.FilterAction;
import de.ovgu.featureide.ui.ahead.views.collaboration.editparts.GraphicalEditPartFactory;
import de.ovgu.featureide.ui.ahead.views.collaboration.model.Collaboration;
import de.ovgu.featureide.ui.ahead.views.collaboration.model.CollaborationModel;
import de.ovgu.featureide.ui.ahead.views.collaboration.model.CollaborationModelBuilder;

/**
 * View of the collaboration diagram.
 * 
 * @author Constanze Adler
 * @author Jens Meinicke
 * 
 */
public class CollaborationView extends ViewPart implements GUIDefaults, ICurrentBuildListener{
	
	public static final String ID = AheadUIPlugin.PLUGIN_ID + ".views.collaboration.Collaboration";
	private GraphicalViewerImpl viewer;
	private CollaborationModelBuilder builder = new CollaborationModelBuilder();
	private CollaborationModel model = new CollaborationModel();
	
	private AddClassAction addClassAction;
	private DeleteAction delAction;
	private Action toolbarAction;
	private IAction filterAction;
	
	private IFeatureProject featureProject;
	
	public IFeatureProject getFeatureProject() {
		return featureProject;
	}

	private FileEditorInput inputFile;
	
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
				if (part != null) {
					inputFile = (FileEditorInput)part.getEditorInput();
					featureProject = CorePlugin.getFeatureProject(inputFile.getFile());
				}
			}
		}		
		
		if (featureProject == null) {
			model = new CollaborationModel();
			model.collaborations.add(new Collaboration("you have to open a file from a FeatureIDE Project"));
			viewer.setContents(model);
		}
		else
		{
			if (featureProject.getCurrentEquationFile() == null){
				model = new CollaborationModel();
				model.collaborations.add(new Collaboration("Please create a new equation file"));
				viewer.setContents(model);
			}
			else
				
			updateGuiAfterBuild(featureProject);
			
			if (model == null){
				model = new CollaborationModel();
				model.collaborations.add(new Collaboration("Please build the Project with the button on the top right of this view"));
				viewer.setContents(model);
			}
		}
		
	}
	
	private void buildProject(IFeatureProject featureProject){
		if (featureProject == null) {
			toolbarAction.setEnabled(true);
			return;
		}
		
		updateGuiAfterBuild(featureProject);
		
		if (model == null){
			final IFeatureProject iFeatureProject = featureProject;
			Job job = new Job("buildProject") {
				public IStatus run(IProgressMonitor monitor) {
					try {
						iFeatureProject.getProject().build(IncrementalProjectBuilder.FULL_BUILD, monitor);
					} catch (CoreException e) {
						model = new CollaborationModel();
						model.collaborations.add(new Collaboration("the project couldn't build, please change this"));
						viewer.setContents(model);
						AheadUIPlugin.getDefault().logError(e);
					}
					toolbarAction.setEnabled(true);
					return Status.OK_STATUS;
				}
			};
			job.setPriority(Job.BUILD);
			job.schedule();
		} else {
			toolbarAction.setEnabled(true);
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
		addClassAction.setEnabled(!isEmpty);
		filterAction.setEnabled(!isEmpty);
		delAction.setEnabled(!isEmpty);
		
		menuMgr.add(addClassAction);
		menuMgr.add(filterAction);
		menuMgr.add(delAction);
	}
	
	private void createActions(IEditorPart part) {
		addClassAction	= new AddClassAction("Add new Class / Role", viewer);
		delAction		= new DeleteAction("Delete", viewer);
		filterAction	= new FilterAction("Filter",viewer,this,model);
	}
	
	private void fillLocalToolBar(IToolBarManager manager) {
		manager.add(toolbarAction);
		toolbarAction.setToolTipText("Build the Project");
		toolbarAction.setImageDescriptor(ImageDescriptor.createFromImage(AheadUIPlugin.getImage("refresh_tab.gif")));
	}
	
	private void makeActions() {
		toolbarAction = new Action() {
			public void run() {
				Job job = new Job("toolbarAction") {
					protected IStatus run(IProgressMonitor monitor) {
						if (!toolbarAction.isEnabled())
							return Status.OK_STATUS;
						toolbarAction.setEnabled(false);
						buildProject(featureProject);
						return Status.OK_STATUS;
					}
				};
				job.setPriority(Job.SHORT);
				job.schedule();
			}
		};
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.listeners.ICurrentBuildListener#updateGuiAfterBuild(de.ovgu.featureide.core.IFeatureProject)
	 */
	public void updateGuiAfterBuild(IFeatureProject project) {
		model = builder.buildCollaborationModel(project);
		if (model == null) {
			return;
		}
		UIJob job = new UIJob("updateGuiAfterBuild") {
			public IStatus runInUIThread(IProgressMonitor monitor) {
				viewer.setContents(model);		
				viewer.getContents().refresh();
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.DECORATE);
		job.schedule();
		
	}
}