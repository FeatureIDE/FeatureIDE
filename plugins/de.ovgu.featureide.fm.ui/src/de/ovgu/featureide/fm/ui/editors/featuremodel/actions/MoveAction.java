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

import org.eclipse.jface.action.Action;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * TODO description 
 * @author ulreich
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
	private FeatureModel model;
	
	
	public MoveAction(Object viewer, FeatureModel featureModel, Object graphicalViewer, int direction) {
		super("Moving");
		this.setId(ID);
		this.viewer = graphicalViewer;
		this.model = featureModel;
		this.dir = direction;
		setEnabled(true);
	}
	
	@Override
	public void run() {

		switch(this.dir)
		{
		case UP:
			break;
		case RIGHT:
			break;
		case DOWN:
			break;
		case LEFT:
			break;
		}
	}
	
	/**
	 * 
	 * @return
	 */
	public boolean isMovingAllowed()
	{
		return !model.getLayout().hasFeaturesAutoLayout();
	}
	

}
