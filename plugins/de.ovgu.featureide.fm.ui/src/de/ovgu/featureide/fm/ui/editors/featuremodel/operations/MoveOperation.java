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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.core.commands.operations.ObjectUndoContext;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.MoveAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;

/**
 * the operation for moving Features in the FeatureModelDiagram
 * 
 * @author Günter Ulreich
 * @author Andy Koch
 */
public class MoveOperation extends AbstractFeatureModelOperation implements	GUIDefaults {
	public static final int stepwidth = 2;
	private static final String LABEL = "Move";
	private Object viewer;
	private Deque<AbstractFeatureModelOperation> operations = new LinkedList<AbstractFeatureModelOperation>();
		
	private int deltaX;
    private int deltaY;
    private boolean doStop;
    
    private Object[] everTouchedFigures; 
	
	public MoveOperation(Object viewer, FeatureModel featureModel, int dir) {
		super(featureModel, LABEL);
		
		deltaX=0;
		deltaY=0;
		doStop= dir == MoveAction.STOP;
		
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
		
		this.viewer = viewer;
	}
	
	@Override
	public IStatus execute(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
		doMove();
		return Status.OK_STATUS;
	}
	
	/**
	 * Executes the requested move operation.
	 * and add it for undo and redo
	 */
	private void doMove() {
		if(!getSelection().isEmpty())
		{
			for (Object element : getSelection().toArray()) {
				// check for infringe of rules
				moveFigure(element);
			}
			featureModel.handleModelLayoutChanged();
		}
	}

	/**
	 * Tries to move the given {@link Feature}
	 * 
	 * @param element
	 */
	private void moveFigure(Object element) {
			if ((element instanceof FeatureEditPart) || (element instanceof Feature))
			{
				Feature feature = element instanceof FeatureEditPart ? ((FeatureEditPart) element).getFeature() : (Feature) element;
				Point oldPos = FeatureUIHelper.getLocation(feature);
				Point newPos = new Point(oldPos.x+deltaX, oldPos.y+deltaY);
				//FeatureUIHelper.setLocation(feature, newPos);

				Feature oldParent = feature.getParent();
				// TODO: calculate new parent!
				Feature newParent = oldParent;
				int oldIndex = oldParent != null ? oldParent.getChildIndex(feature) : 0;
				// TODO: calculate new index!
				int newIndex = oldIndex;
				
				FeatureOperationData data = new FeatureOperationData(feature,
						oldParent, newParent, newIndex, oldIndex);
				FeatureMoveOperation op = new FeatureMoveOperation(data, featureModel, newPos, 
						FeatureUIHelper.getLocation(feature).getCopy(), feature);
				op.addContext((ObjectUndoContext) featureModel.getUndoContext());
				this.operations.add(op);
				FeatureUIHelper.setLocation(feature, newPos);
			}
			
			if((element instanceof ConstraintEditPart) || (element instanceof Constraint))
			{
				Constraint constraint = ((ConstraintEditPart) element).getConstraintModel();
				Point oldPos = FeatureUIHelper.getLocation(constraint);
				Point newPos = new Point(oldPos.x+deltaX, oldPos.y+deltaY);
				
				boolean isLastPos = true;
				for (Constraint c : featureModel.getConstraints()) {
					if ((FeatureUIHelper.getLocation(c).y + 17) > newPos.y) {
						isLastPos = false;
						break;
					}
				}
				
				int oldIndex = featureModel.getConstraints().indexOf(constraint);
				// TODO: calculate new index 
				int index = oldIndex;
				
				ConstraintMoveOperation op = new ConstraintMoveOperation(constraint,
						featureModel, index, oldIndex, isLastPos ,newPos, 
						FeatureUIHelper.getLocation(constraint).getCopy());
				op.addContext((IUndoContext) featureModel.getUndoContext());

				this.operations.add(op);
				FeatureUIHelper.setLocation(constraint, newPos);
			}
			
			if(element instanceof LegendFigure)
			{
				LegendFigure legendFigure = (LegendFigure) element;
				Point oldPos = legendFigure.getLocation();
				Point newPos = new Point(oldPos.x+deltaX, oldPos.y+deltaY);
				legendFigure.newPos = newPos;
				Point p = legendFigure.newPos.getCopy();
				legendFigure.translateToRelative(p);
				if (!(featureModel.getLayout().getLegendPos().x == p.x && featureModel.getLayout().getLegendPos().y == p.y)) {
					LegendMoveOperation op = new LegendMoveOperation(featureModel, p,legendFigure.newPos, legendFigure);
					op.addContext((IUndoContext) featureModel.getUndoContext());
					this.operations.add(op);
				}
			}
	}

	private IStructuredSelection getSelection() {
		return (IStructuredSelection) ((GraphicalViewerImpl) viewer).getSelection();
	}
	
	@Override
	protected void redo() {
		for (Iterator<AbstractFeatureModelOperation> it = operations.iterator(); it.hasNext();) {
			AbstractFeatureModelOperation operation = it.next();
			if (operation.canRedo()) {
				operation.redo();
			}
		}
	}

	@Override
	protected void undo() {
		for (Iterator<AbstractFeatureModelOperation> it = operations.descendingIterator(); it.hasNext();) {
			AbstractFeatureModelOperation operation = it.next();
			if (operation.canUndo()) {
				operation.undo();
			}
		}
	}

}
