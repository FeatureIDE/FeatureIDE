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
package de.ovgu.featureide.fm.ui.editors.keyhandler;

import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.gef.KeyHandler;
import org.eclipse.gef.KeyStroke;
import org.eclipse.gef.ui.parts.GraphicalViewerKeyHandler;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.swt.events.KeyEvent;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;

/**
 * the KeyHandler for the FeatureDiagramEditor
 * 
 * At Manual-Layout:
 * =================
 * to ensure that actions registered in @see createKeyBindings() will be handled first!
 * default actions will be handled at last!
 * 
 * Handles searching of features in the Tree
 * 
 * At Automatic-Layout: run @see GraphicalViewerKeyHandler first
 * 
 * @author Guenter Ulreich
 */
public class FeatureDiagramEditorKeyHandler extends KeyHandler {

	private FeatureModel featureModel;
	private GraphicalViewerKeyHandler gvKeyHandler;
	private KeyHandler alternativeKeyHandler;
	private FeatureDiagramEditor viewer;
	private LinkedList<String> sF;
	Iterator<String> sFIter;
	private String toSearchFor;
	private String curr;
	
	/**
	 * alternativeKeyHandler handles the KeyEvents, if the GraphicalViewerKeyHandler is active for auto-layout
	 */
	public FeatureDiagramEditorKeyHandler(FeatureDiagramEditor view, FeatureModel featureModel) {

		super();

		alternativeKeyHandler = new KeyHandler();
		gvKeyHandler =  new GraphicalViewerKeyHandler(view);
		gvKeyHandler.setParent(alternativeKeyHandler);
		setParent(gvKeyHandler);
		this.featureModel = featureModel;
		this.viewer = view;
		toSearchFor = "";
		curr = "";
		sF = new LinkedList<String>();
		sFIter = sF.iterator();
	}
		
	private void resetSearchList()
	{
		sF = new LinkedList<String>();
//		sF.addAll(featureModel.getFeatureNames());
//		
		// traverse preorder
		sF.addAll(featureModel.getFeatureNamesPreorder());
//		for(Feature f : featureModel.getConcreteFeatures())
//		{
//			sF.add(f.getName());
//		}
		
		sFIter = sF.iterator();
	}
	
	/*
	 * use @see GraphicalViewerKeyHandler first if auto-layout is active
	 * handles the searching on the graph (depth-first, same way as in Outline)
	 * @see org.eclipse.gef.KeyHandler#keyPressed(org.eclipse.swt.events.KeyEvent)
	 */
	@Override
	public boolean keyPressed(KeyEvent e)
	{
		
		// search-handling for letters
		if(Character.isLetter(e.character)
				// and if no control-characters are pressed
				)
		{
			if(toSearchFor.length() == 0) // start search
				resetSearchList();

			// if 1 feature is selected
			// set Iterator to this position if the iterator is not yet at the current selected position;
			boolean found = updateIterator();
						
			boolean startFoundSomething = toSearchFor.length() <= 1;
			boolean doUpdateIterator = false;
			
			// if always typing the same character, get next feature after selected one
			if(startFoundSomething && toSearchFor.startsWith(Character.toString(e.character).toLowerCase()))
			{
				toSearchFor = "";
				//doUpdateIterator = true;
			}

			toSearchFor += Character.toString(e.character).toLowerCase();
			
			if(toSearchFor.length() > 1 && curr.length() > 0 && found
//					|| (!found && curr.length() > 0 && toSearchFor.length() == 1))
					)
				found = curr.toLowerCase().startsWith(toSearchFor);
			else
				found = false;

			// search from actual selected position (or from start)
			if(!found)
				found = setFound();
			
			// restart with last character, if current searching for a word with more than 1 character failed...
			if(!found && toSearchFor.length() > 1)
			{
				toSearchFor = Character.toString(e.character).toLowerCase();
				doUpdateIterator = true;
				startFoundSomething = true;
			}
			
			// restart search if there has been already found a feature with one character and after this, there is no other one
			// -> start from beginning (at least it would result in the same feature)
			if(startFoundSomething && !found)
			{
				this.resetSearchList();
				if(doUpdateIterator) // step to selected position
					updateIterator();
				found = setFound();
			}
			
			if(found)
			{
				// then we have the first occurrence of the featurname
				Feature foundFeature = featureModel.getFeature(curr);
				
				// select the new feature
				FeatureEditPart part;
				part = (FeatureEditPart) viewer.getEditPartRegistry().get(foundFeature);
				viewer.setSelection(new StructuredSelection(part));
			}
			else
			{
				toSearchFor = "";
				curr = "";
				resetSearchList();
				viewer.setSelection(new StructuredSelection());
			}
			return found;
		}
		else
		{
			if( featureModel.getLayout().hasFeaturesAutoLayout())
			{
				return gvKeyHandler.keyPressed(e);			
			}
			else
			{
				return super.keyPressed(e);
			}
		}
		
	}

	/*
	 * does the searching
	 */
	private boolean setFound()
	{
		boolean found = false;
		while(sFIter.hasNext() && !found)
		{
			curr = sFIter.next();
			found = curr.toLowerCase().startsWith(toSearchFor);
		}
		return found;
	}
	
	/*
	 * sets iterator and curr
	 */
	private boolean updateIterator()
	{
		IStructuredSelection sel = (IStructuredSelection) viewer.getSelection();
		boolean found = false;
		if(sel.size() == 1 && !(sel.getFirstElement() instanceof ModelEditPart))
		{
			Object element = sel.toArray()[0];
			if ((element instanceof FeatureEditPart) || (element instanceof Feature))
			{
				Feature feature = element instanceof FeatureEditPart ? ((FeatureEditPart) element).getFeature() : (Feature) element;
				
				if(curr.length() > 0 && !feature.getName().toLowerCase().equals(curr.toLowerCase()))
				{
					String selItem = "";
					while(sFIter.hasNext() && !found)
					{
						selItem = sFIter.next();
						found = selItem.toLowerCase().equals(feature.getName().toLowerCase());
					}
					curr = selItem;
				}
				else
				{
					curr.toLowerCase().equals(feature.getName().toLowerCase());
				}
			}
		}
		return found;
	}
	

	/*
	 * to handle 2 KeyHandler (otherwise there would be an action loop)
	 * (non-Javadoc)
	 * @see org.eclipse.gef.KeyHandler#put(org.eclipse.gef.KeyStroke, org.eclipse.jface.action.IAction)
	 */
	@Override
	public void put(KeyStroke keystroke, IAction action)
	{
		this.alternativeKeyHandler.put(keystroke, action);
		super.put(keystroke, action);
	}
	
}
