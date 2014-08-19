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
import java.util.Set;

import org.eclipse.gef.KeyHandler;
import org.eclipse.gef.KeyStroke;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.gef.ui.parts.GraphicalViewerKeyHandler;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * the KeyHandler for the FeatureDiagramEditor
 * 
 * At Manual-Layout:
 * =================
 * to ensure that actions registered in @see createKeyBindings() will be handled first!
 * default actions will be handled at last!
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
	private String toSearchFor;
	private String recFound;
	private LinkedList<String> sF;
	
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
		recFound = "";
		sF = new LinkedList<String>();
	}
	
	/*
	 * use @see GraphicalViewerKeyHandler if
	 * @see org.eclipse.gef.KeyHandler#keyPressed(org.eclipse.swt.events.KeyEvent)
	 */
	@Override
	public boolean keyPressed(KeyEvent e)
	{	
		boolean halt=false;
		
		// search-handling for letters
		if(Character.isLetter(e.character))
		{
			if(sF.isEmpty())
				sF = new LinkedList<String>(featureModel.getFeatureOrderList());
//			for(String c: featureModel.getFeatureNames())
//			{
//				sF.add(c);
//			}
			Iterator<String> iter = featureModel.getFeatureOrderList().iterator();
			String curr = "";
			boolean found = false;
			toSearchFor += Character.toString(e.character).toLowerCase();
			
			while(iter.hasNext() && !found)
			{
				curr = iter.next();
				found = curr.toLowerCase().startsWith(toSearchFor);
				this.recFound = curr;
			}
			
//			if(toSearchFor.length() > 1)
//			{
//				halt = true;
//			}

			iter = sF.iterator();
//			
			if(!found && toSearchFor.length() > 1)
			{
				toSearchFor = Character.toString(e.character).toLowerCase();
				
				while(iter.hasNext() && !found)
				{
					curr = iter.next();
					found = curr.toLowerCase().startsWith(toSearchFor);
					
//					if(found)
//					{
//						int indexRec = sF.indexOf(this.recFound);
//						int indexCurr = sF.indexOf(curr);
//						if(found = indexRec < indexCurr)
//							this.recFound = curr;
//					}
				}
			}
						
			if(found)
			{
				sF.removeFirstOccurrence(curr);
				// then we have the first occurrence of the featurname
				Feature foundFeature = featureModel.getFeature(curr);
				recFound = "";
				
				// select the new feature
				FeatureEditPart part;
				part = (FeatureEditPart) viewer.getEditPartRegistry().get(foundFeature);
				viewer.setSelection(new StructuredSelection(part));
			}
			else
			{
				toSearchFor = "";
				recFound = "";
				sF.clear();
				viewer.setSelection(new StructuredSelection());
			}
			return found;
		}
		else
		{
			if( featureModel.getLayout().hasFeaturesAutoLayout())
			{
				halt = true;
				return gvKeyHandler.keyPressed(e);			
			}
			else
			{
				halt = true;
				return super.keyPressed(e);
			}
		}
		
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
