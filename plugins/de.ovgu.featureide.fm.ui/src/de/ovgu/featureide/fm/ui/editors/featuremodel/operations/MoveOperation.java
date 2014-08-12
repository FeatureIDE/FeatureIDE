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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * TODO description
 * 
 * @author andkoch
 */
public class MoveOperation extends AbstractFeatureModelOperation implements	GUIDefaults {
	private static final String LABEL = "Move";
	private Object viewer;
	private List<AbstractFeatureModelOperation > operations = new LinkedList<AbstractFeatureModelOperation >();
	
	public MoveOperation(Object viewer, FeatureModel featureModel) {
		super(featureModel, LABEL);
		this.viewer = viewer;
	}
	
	@Override
	public IStatus execute(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
		doMove();
		return Status.OK_STATUS;
	}
	
	/**
	 * Executes the requested move operation.
	 */
	private void doMove() {
		for (Object element : getSelection().toArray()) {
			// check for infringe of rules
			moveFeature(element);
		}
	}

	/**
	 * @param Tries to move the given {@link Feature}
	 */
	private void moveFeature(Object element) {
		
	}

	private IStructuredSelection getSelection() {
		return (IStructuredSelection) ((GraphicalViewerImpl) viewer).getSelection();
	}
	
	/**
	 * @param save operation for undo(), redo() and execute it
	 */
	public void executeOperation(AbstractFeatureModelOperation  operation) {
		operations.add(operation);
		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(operation, null, null);
		} catch (ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}
	
	@Override
	protected void redo() {
		List<AbstractFeatureModelOperation > ops = new LinkedList<AbstractFeatureModelOperation >();
		ops.addAll(operations);
		Collections.reverse(operations);
		
		while (!ops.isEmpty()) {
			for (AbstractFeatureModelOperation  op : operations) {
				try {
					op.redo();
					ops.remove(op);
				} catch (Exception e) {
					
				}

			}
		}

	}

	@Override
	protected void undo() {
		List<AbstractFeatureModelOperation > ops = new ArrayList<AbstractFeatureModelOperation >(operations);
		Collections.reverse(operations);
		
		while (!ops.isEmpty()) {
			for (AbstractFeatureModelOperation  op : operations) {
				if (op.canUndo()) {
					op.undo();
					ops.remove(op);
				}
			}
		}
	}

}
