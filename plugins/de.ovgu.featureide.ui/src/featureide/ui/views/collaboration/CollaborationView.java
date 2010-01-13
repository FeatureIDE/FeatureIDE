/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.ViewPart;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;
import featureide.core.listeners.IEquationChangedListener;
import featureide.ui.UIPlugin;
import featureide.ui.views.collaboration.action.ShowRoleImplementationAction;
import featureide.ui.views.collaboration.editparts.GraphicalEditPartFactory;
import featureide.ui.views.collaboration.model.CollaborationModel;
import featureide.ui.views.collaboration.model.CollaborationModelBuilder;


/**
 * View of the collaboration diagram.
 * 
 * @author Constanze Adler
 */

public class CollaborationView extends ViewPart implements GUIDefaults, IEquationChangedListener{
	public static final String ID = UIPlugin.PLUGIN_ID + ".views.collaboration.Collaboration";
	private GraphicalViewerImpl graphicalViewer;
	private ScalableFreeformRootEditPart rootEditPart;
	private CollaborationModelBuilder builder;
	private CollaborationModel model;
	private ShowRoleImplementationAction showRoleAction;
	
	/*
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
		IWorkbenchWindow editor = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		if (editor==null) return;
		FileEditorInput inputFile = (FileEditorInput)editor.getActivePage().getActiveEditor().getEditorInput(); 
		IFeatureProject featureProject = CorePlugin.getProjectData(inputFile.getFile());
		if (featureProject == null) return;
		builder = new CollaborationModelBuilder();
		model = builder.buildCollaborationModel(featureProject);
		
		graphicalViewer = new ScrollingGraphicalViewer();
		graphicalViewer.createControl(parent);
		graphicalViewer.getControl().setBackground(DIAGRAM_BACKGROUND);
		CorePlugin.getDefault().addEquationChangedListener(this);
		
		rootEditPart = new ScalableFreeformRootEditPart();
		((ConnectionLayer) rootEditPart
				.getLayer(LayerConstants.CONNECTION_LAYER))
				.setAntialias(SWT.ON);
		graphicalViewer.setRootEditPart(rootEditPart);
		graphicalViewer.setEditDomain(new EditDomain());
		graphicalViewer.setEditPartFactory(new GraphicalEditPartFactory());
		graphicalViewer.setContents(model);
		createActions();
		createContextMenu();
	}

	/*
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	@Override
	public void setFocus() {
		graphicalViewer.getControl().setFocus();
	}

	/* (non-Javadoc)
	 * @see featureide.core.listeners.IEquationChangedListener#equationChanged(featureide.core.IFeatureProject)
	 */

	public void equationChanged(IFeatureProject featureProject) {
		model = builder.buildCollaborationModel(featureProject);
		graphicalViewer.setContents(model);
		graphicalViewer.getContents().refresh();
		System.out.println("refreshing");
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
		showRoleAction.setEnabled(!isEmpty);
		
		menuMgr.add(showRoleAction);
		
		
	}
	
	
	
	private void createActions() {
		showRoleAction = new ShowRoleImplementationAction("Role Implementation", graphicalViewer);
	
	}
	

	


}
