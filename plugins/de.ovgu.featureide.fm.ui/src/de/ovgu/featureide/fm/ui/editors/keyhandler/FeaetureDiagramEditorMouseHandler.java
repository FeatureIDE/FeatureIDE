/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.keyhandler;

import org.eclipse.jface.action.Action;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseWheelListener;

/**
 * The mouse wheel listener performs two actions depending on mouse wheel input 
 * preferred with state mask (optional)
 * 
 * The default state mask is 0x0
 * 
 * @author Enis Belli
 * @author Joshua Sprey
 */
public class FeaetureDiagramEditorMouseHandler implements MouseWheelListener{

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.MouseWheelListener#mouseScrolled(org.eclipse.swt.events.MouseEvent)
	 */
	
	private Action mouseWheelUpAction;
	private Action mouseWheelDownAction;
	private int stateMask;
	
	
	public FeaetureDiagramEditorMouseHandler(Action mouseWheelUpAction, Action mouseWheelDownAtion) {
		this.mouseWheelDownAction = mouseWheelDownAtion;
		this.mouseWheelUpAction = mouseWheelUpAction;
		stateMask = 0x0;
	}
	
	public FeaetureDiagramEditorMouseHandler(Action mouseWheelUpAction, Action mouseWheelDownAtion, int stateMask) {
		this.mouseWheelDownAction = mouseWheelDownAtion;
		this.mouseWheelUpAction = mouseWheelUpAction;;
		this.stateMask = stateMask;
	}
	

	
	@Override
	public void mouseScrolled(MouseEvent e) {
		if (e.stateMask == stateMask && e.count > 0) {
			mouseWheelUpAction.run();
		} else if(e.stateMask == stateMask && e.count < 0){
			mouseWheelDownAction.run();
		}
		
	}
	


}
