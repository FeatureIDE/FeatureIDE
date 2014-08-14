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
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map.Entry;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.core.commands.operations.ObjectUndoContext;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
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
	private static final String LABEL = "Move";
	private Deque<AbstractFeatureModelOperation> operations = new LinkedList<AbstractFeatureModelOperation>();
    
    public static HashMap<String,Point> initialPositions;
    
    private HashMap<Object,Point> endPositions;
    	
	public MoveOperation(FeatureModel featureModel, HashMap<Object,Point> endPositions) {
		super(featureModel, LABEL);
		this.endPositions = endPositions;
	}

	/**
	 * Executes the requested move operation.
	 * and add it for undo and redo
	 */
	@Override
	public IStatus execute(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
		if(!endPositions.isEmpty())
		{
			for (Entry<Object,Point> element : endPositions.entrySet()) {
				// check for infringe of rules
				moveFigure(element);
			}
			
//			for(AbstractFeatureModelOperation op : this.operations)
//			{
//				op.execute(monitor, info);
//			}
		}
		MoveOperation.initialPositions.clear();
		featureModel.handleModelLayoutChanged();
		return Status.OK_STATUS;
	}
	
	/**
	 * Tries to move the given {@link Feature}
	 * 
	 * @param element
	 */
	private void moveFigure(Entry<Object,Point> element) {
			Point newPos = element.getValue();
			
			if ((element.getKey() instanceof FeatureEditPart) || (element.getKey() instanceof Feature))
			{
				Feature feature = element.getKey() instanceof FeatureEditPart ? ((FeatureEditPart) element.getKey()).getFeature() : (Feature) element.getKey();

				Point oldPos = MoveOperation.initialPositions.get(feature.getName());
				
				Feature oldParent = feature.getParent();
				Feature newParent = oldParent;
				int oldIndex = oldParent != null ? oldParent.getChildIndex(feature) : 0;
				int newIndex = oldIndex;
				
				FeatureOperationData data = new FeatureOperationData(feature,
						oldParent, newParent, newIndex, oldIndex);
				FeatureMoveOperation op = new FeatureMoveOperation(data, featureModel, newPos,oldPos, feature);
				op.addContext((ObjectUndoContext) featureModel.getUndoContext());
				this.operations.add(op);
			}
			
//			if((element.getKey() instanceof ConstraintEditPart) || (element.getKey() instanceof Constraint))
//			{
//				Constraint constraint = ((ConstraintEditPart) element.getKey()).getConstraintModel();
//				Point oldPos = MoveOperation.initialPositions.get(constraint.getCreationIdentifier());
//				
//				boolean isLastPos = true;
//				for (Constraint c : featureModel.getConstraints()) {
//					if ((FeatureUIHelper.getLocation(c).y + 17) > newPos.y) {
//						isLastPos = false;
//						break;
//					}
//				}
//				
//				int oldIndex = featureModel.getConstraints().indexOf(constraint);
//				int index = oldIndex;
//				
//				ConstraintMoveOperation op = new ConstraintMoveOperation(constraint,
//						featureModel, index, oldIndex, isLastPos ,newPos,oldPos);
//				op.addContext((IUndoContext) featureModel.getUndoContext());
//				this.operations.add(op);
//			}
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
