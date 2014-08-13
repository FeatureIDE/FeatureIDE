///* FeatureIDE - A Framework for Feature-Oriented Software Development
// * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
// *
// * This file is part of FeatureIDE.
// * 
// * FeatureIDE is free software: you can redistribute it and/or modify
// * it under the terms of the GNU Lesser General Public License as published by
// * the Free Software Foundation, either version 3 of the License, or
// * (at your option) any later version.
// * 
// * FeatureIDE is distributed in the hope that it will be useful,
// * but WITHOUT ANY WARRANTY; without even the implied warranty of
// * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// * GNU Lesser General Public License for more details.
// * 
// * You should have received a copy of the GNU Lesser General Public License
// * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
// *
// * See http://www.fosd.de/featureide/ for further information.
// */
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.MoveOperation;

/**
 * This is the MoveAction for the manual movement of objects in the FeatureModelDiagram
 *  
 * @author Günter Ulreich
 * @author Andy Koch
 */
public class MoveAction extends Action {
	public static int STEPS = 2;
	public static final String ID = "de.ovgu.featureide.move";
	public static final int UP = 1;
	public static final int RIGHT = 2;
	public static final int DOWN = 4;
	public static final int LEFT = 8;
	
	private int dir;

	Object viewer;
	private FeatureModel featureModel;
	
	private ISelectionChangedListener listener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			setEnabled(isValidSelection(selection) && isMovingAllowed()); //action only active when manual layout and feature diagram elements are selected
		}
	};
	
	/**
	 * 
	 * @param viewer the object which for the MoveAction has been registered
	 * @param featureModel the according FeatureModel object
	 * @param graphicalViewer the according GraphicalViewerImpl
	 * @param direction
	 */
	public MoveAction(Object viewer, FeatureModel featureModel, Object graphicalViewer, int direction) {
		super("Moving");
		this.setId(ID);
		this.viewer = viewer;
		this.featureModel = featureModel;
		this.dir = direction;
		setEnabled(false);
		
		if (viewer instanceof GraphicalViewerImpl) {
			((GraphicalViewerImpl)viewer).addSelectionChangedListener(listener);
		}
		
	}
	
	@Override
	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.Action#run()
	 */
	public void run() {
		MoveOperation op = new MoveOperation(viewer, featureModel, dir);
		op.addContext((IUndoContext) featureModel.getUndoContext());

		try {
			PlatformUI.getWorkbench().getOperationSupport()
					.getOperationHistory().execute(op, null, null);
		} catch (ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}
	
	/**
	 * check the rules (actually, if there is AutoLayout not active)
	 * 
	 * @return true if rules are not infringed
	 */
	public boolean isMovingAllowed()
	{
		return !featureModel.getLayout().hasFeaturesAutoLayout();
	}
	
	/**
	 * check if the selection has not only one element who is a ModelEditPart
	 * 
	 * @param selection the IStructuredSelection object who contains the selected controls
	 * @return true if condition is matched
	 */
	private boolean isValidSelection(IStructuredSelection selection) {
		// check empty selection (only ModelEditPart is selected)
		return !(selection.size() == 1 && selection.getFirstElement() instanceof ModelEditPart);
	}
}
