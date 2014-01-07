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
package de.ovgu.featureide.ui.views.collaboration.editparts;

import org.eclipse.core.resources.IFile;
import org.eclipse.draw2d.IFigure;
import org.eclipse.gef.Request;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.figures.UnderlayerFigure;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;

/**
 * An EditPart for the collaboration.
 * 
 * @author Constanze Adler
 */
public class CollaborationEditPart extends AbstractGraphicalEditPart implements GUIDefaults {
	
	public CollaborationEditPart(Collaboration coll){
		super();
		setModel(coll);
	}
	
	public Collaboration getCollaborationModel(){
		return (Collaboration) getModel();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.gef.editparts.AbstractGraphicalEditPart#createFigure()
	 */
	@Override
	protected IFigure createFigure() {
		return new UnderlayerFigure(getCollaborationModel());
	}

	/* (non-Javadoc)
	 * @see org.eclipse.gef.editparts.AbstractEditPart#createEditPolicies()
	 */
	//@Override
	protected void createEditPolicies() {
	}
	
	/**
	 * {@link ModelEditPart#refreshVisuals()}
	 */
	@Override
	protected void refreshVisuals() {
		this.getFigure().getBounds().x =GUIDefaults.DEFAULT_INSET_TO_EDGE;
		this.getFigure().getBounds().y= this.getFigure().getBounds().y + GUIDefaults.DEFAULT_INSET_TO_EDGE;
	}
	
	/**
	 * Opens the configuration editor if the element is a configuration.
	 */
	public void performRequest(Request request) {
		if (REQ_OPEN.equals(request.getType())) {
			 if (!this.getCollaborationModel().isConfiguration)
				 return;
			 
			 IFile file = this.getCollaborationModel().configurationFile;
			 if (file == null)
				 return;
			 
			 IWorkbenchWindow dw = UIPlugin.getDefault().getWorkbench().getActiveWorkbenchWindow();	 
			 try {
				 IWorkbenchPage page = dw.getActivePage();
				 if (page != null) {
					 FileEditorInput fileEditorInput = new FileEditorInput(file);
					 page.openEditor(fileEditorInput, "de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor");
				 }
			 } catch (PartInitException e) {
				 UIPlugin.getDefault().logError(e);
			 }
	
		}
		super.performRequest(request);
	}
}
