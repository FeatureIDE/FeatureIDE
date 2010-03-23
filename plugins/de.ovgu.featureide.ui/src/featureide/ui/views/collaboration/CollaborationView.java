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
package featureide.ui.views.collaboration;

import org.eclipse.draw2d.ConnectionLayer;
import org.eclipse.gef.EditDomain;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.ViewPart;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;
import featureide.core.listeners.ICurrentBuildListener;
import featureide.ui.UIPlugin;
import featureide.ui.views.collaboration.action.AddClassAction;
import featureide.ui.views.collaboration.action.AddFeatureAction;
import featureide.ui.views.collaboration.action.DeleteClassAction;
import featureide.ui.views.collaboration.action.DeleteFeatureAction;
import featureide.ui.views.collaboration.action.DeleteRoleAction;
import featureide.ui.views.collaboration.editparts.GraphicalEditPartFactory;
import featureide.ui.views.collaboration.model.CollaborationModel;
import featureide.ui.views.collaboration.model.CollaborationModelBuilder;


/**
 * View of the collaboration diagram.
 * 
 * @author Constanze Adler
 */

public class CollaborationView extends ViewPart implements GUIDefaults, ICurrentBuildListener{
	public static final String ID = UIPlugin.PLUGIN_ID + ".views.collaboration.Collaboration";
	private GraphicalViewerImpl graphicalViewer;
	private ScalableFreeformRootEditPart rootEditPart;
	private CollaborationModelBuilder builder;
	private CollaborationModel model;
	//private ShowRoleImplementationAction showRoleAction;
	private AddClassAction addClassAction;
	private AddFeatureAction addFeatureAction;
	private DeleteClassAction delClassAction;
	private DeleteFeatureAction delFeatureAction;
	private DeleteRoleAction delRoleAction;
	
	
	/*
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	public void createPartControl(Composite parent) {
	
		IWorkbenchWindow editor = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		IFeatureProject featureProject = null;
		IEditorPart part=null;
		if (editor!=null) {
			IWorkbenchPage page = editor.getActivePage();
			if (page!=null) {
				part = page.getActiveEditor();
				if (part!=null) {
					FileEditorInput inputFile = (FileEditorInput)part.getEditorInput(); 
					featureProject = CorePlugin.getFeatureProject(inputFile.getFile());
				}
			}
		}
				
		if (featureProject == null) 
			return;
		builder = new CollaborationModelBuilder();
		model = builder.buildCollaborationModel(featureProject);
	
		CorePlugin.getDefault().addCurrentBuildListener(this);
		graphicalViewer = new ScrollingGraphicalViewer();
		graphicalViewer.createControl(parent);
		graphicalViewer.getControl().setBackground(DIAGRAM_BACKGROUND);

		rootEditPart = new ScalableFreeformRootEditPart();
		((ConnectionLayer) rootEditPart
				.getLayer(LayerConstants.CONNECTION_LAYER))
				.setAntialias(SWT.ON);
		graphicalViewer.setRootEditPart(rootEditPart);
		graphicalViewer.setEditDomain(new EditDomain());
		graphicalViewer.setEditPartFactory(new GraphicalEditPartFactory());
		
		createActions(part);
		createContextMenu();
		if (model == null)
			return;
		graphicalViewer.setContents(model);
		
	}
	


	/*
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */

	public void setFocus() {
		if (graphicalViewer != null)
			graphicalViewer.getControl().setFocus();
	
	}

	
	private void createContextMenu(){
		MenuManager menuMgr = new MenuManager("#PopupMenu");
		menuMgr.setRemoveAllWhenShown(true);
		menuMgr.addMenuListener(new IMenuListener(){
			public void menuAboutToShow(IMenuManager m){
				fillContextMenu(m);
			}
		});
		Menu menu = menuMgr.createContextMenu(graphicalViewer.getControl());
		graphicalViewer.getControl().setMenu(menu);
		getSite().registerContextMenu(menuMgr, graphicalViewer);
	}
	
	private void fillContextMenu(IMenuManager menuMgr){
		boolean isEmpty = graphicalViewer.getSelection().isEmpty();		
	//	showRoleAction.setEnabled(!isEmpty);
		addClassAction.setEnabled(!isEmpty);
		addFeatureAction.setEnabled(!isEmpty);
		delRoleAction.setEnabled(!isEmpty);
		delClassAction.setEnabled(!isEmpty);
		delFeatureAction.setEnabled(!isEmpty);
	//	menuMgr.add(showRoleAction);
		menuMgr.add(addClassAction);
	//	menuMgr.add(addFeatureAction);
		menuMgr.add(delRoleAction);
		menuMgr.add(delClassAction);
	//	menuMgr.add(delFeatureAction);		
	}
	
	
	
	private void createActions(IEditorPart part) {
	//	showRoleAction	 = new ShowRoleImplementationAction("Role Implementation", graphicalViewer);
		addClassAction	 = new AddClassAction("Add new Class / Role", graphicalViewer);
		addFeatureAction = new AddFeatureAction("Add new Feture", graphicalViewer);
		delClassAction 	 = new DeleteClassAction("Delete Class", graphicalViewer,part,model);
		delFeatureAction = new DeleteFeatureAction("Delete Feture", graphicalViewer);
		delRoleAction 	 = new DeleteRoleAction("Delete Role", graphicalViewer,part,model);
	}

	/* (non-Javadoc)
	 * @see featureide.core.listeners.ICurrentBuildListener#updateGuiAfterBuild(featureide.core.IFeatureProject)
	 */
	public void updateGuiAfterBuild(IFeatureProject project) {
		model = builder.buildCollaborationModel(project);
		if (model == null) return;
		Display.getDefault().syncExec(new Runnable(){	
			public void run(){
				graphicalViewer.setContents(model);		
				graphicalViewer.getContents().refresh();
			}
		});

		//System.out.println("refreshing");
	}
	

	

	


}
