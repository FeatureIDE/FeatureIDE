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

import java.util.HashMap;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.Legend;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.MoveOperation;

/**
 * This is the MoveAction for the manual movement of objects in the FeatureModelDiagram
 *  
 *  
 * @author Günter Ulreich
 * @author Andy Koch
 */
public class MoveAction extends Action {
	public static final int stepwidth = 2;
	public static final String ID = "de.ovgu.featureide.move";
	public static final int UP = 1;
	public static final int RIGHT = 2;
	public static final int DOWN = 4;
	public static final int LEFT = 8;
	public static final int STOP = 0; // whole movement has been stopped (needed for undo redo purposes)
	
	private int dir;

	private int deltaX;
    private int deltaY;
    private boolean doStop;
    
	Object viewer;
	private FeatureModel featureModel;
	
	private HashMap<Object,Point> endPositions;
	
	private ISelectionChangedListener listener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			setEnabled(isValidSelection(selection) && isMovingAllowed()); // action only active when manual layout and feature diagram elements are selected
			
			// TODO: insert check for selection changed (would also end transaction for moving)
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
		deltaX=0;
		deltaY=0;
		doStop = dir == MoveAction.STOP;
				
		if(!doStop)
		{
			if((dir & MoveAction.DOWN) != 0)
				deltaY = stepwidth;
			if((dir & MoveAction.UP) != 0)
				deltaY = stepwidth*(-1);
			if((dir & MoveAction.RIGHT) != 0)
				deltaX = stepwidth;
			if((dir & MoveAction.LEFT) != 0)
				deltaX = stepwidth*(-1);
		}
		
		if(doStop)
		{
			doStop = dir == MoveAction.STOP;
		}
		
		if (viewer instanceof GraphicalViewerImpl) {
			((GraphicalViewerImpl)viewer).addSelectionChangedListener(listener);
		}
		
		this.endPositions = new HashMap<Object,Point>();
	}
	
	@Override
	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.Action#run()
	 */
	public void run() {
		if(doStop)
			this.stop();
		else
			this.doMove(false);
	}
	/**
	 * Executes the requested move operation.
	 * and add it for undo and redo
	 */
	private void doMove(boolean doStop) {
		if(!getSelection().isEmpty())
		{
			for (Object element : getSelection().toArray()) {
				// check for infringe of rules
				moveFigure(element,doStop);
			}
			featureModel.handleModelLayoutChanged();
		}
	}

	private IStructuredSelection getSelection() {
		return (IStructuredSelection) ((GraphicalViewerImpl) viewer).getSelection();
	}
	
	/**
	 * Tries to move the given {@link Feature}
	 * 
	 * @param element
	 */
	private void moveFigure(Object element,boolean doStop) {
		
		boolean firstRun = MoveOperation.totalDeltaX == 0 && MoveOperation.totalDeltaY == 0;
		
		if(firstRun)
			//MoveOperation.initialPositions = new HashMap<String,Point>();
		
		if ((element instanceof FeatureEditPart) || (element instanceof Feature))
		{
			Feature feature = element instanceof FeatureEditPart ? ((FeatureEditPart) element).getFeature() : (Feature) element;
			Point oldPos = FeatureUIHelper.getLocation(feature);
			Point newPos = new Point(oldPos.x+deltaX, oldPos.y+deltaY);

			if(firstRun)
				//MoveOperation.initialPositions.put(feature.getName(), oldPos);
			
			if(doStop)
				this.endPositions.put(element, newPos);

			FeatureUIHelper.setLocation(feature, newPos);
		}
		
		if((element instanceof ConstraintEditPart) || (element instanceof Constraint))
		{
			Constraint constraint = element instanceof ConstraintEditPart ? ((ConstraintEditPart) element).getConstraintModel() : (Constraint) element;
			Point oldPos = FeatureUIHelper.getLocation(constraint);
			Point newPos = new Point(oldPos.x+deltaX, oldPos.y+deltaY);
//
//			if(firstRun)
//				MoveOperation.initialPositions.put(constraint.getCreationIdentifier(), oldPos);
//			
//			if(doStop)
//				this.endPositions.put(element, newPos);
//			
			FeatureUIHelper.setLocation(constraint, newPos);
		}
		if((element instanceof LegendEditPart) || (element instanceof LegendFigure) || (element instanceof Legend))
		{
			LegendFigure legendFigure = FeatureUIHelper.getLegendFigure(featureModel);
			Point oldPos = legendFigure.getLocation();
			Point newPos = new Point(oldPos.x+deltaX, oldPos.y+deltaY);
			legendFigure.setLocation(newPos);
		}

	}
	
	private void stop()
	{   
		this.doMove(true);
		// create Operation
		MoveOperation op = new MoveOperation(featureModel, this.endPositions);
//		op.addContext((IUndoContext) featureModel.getUndoContext());
//		
//		try {
//			PlatformUI.getWorkbench().getOperationSupport()
//					.getOperationHistory().execute(op, null, null);
//		} catch (ExecutionException e) {
//			FMUIPlugin.getDefault().logError(e);
//		}
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
