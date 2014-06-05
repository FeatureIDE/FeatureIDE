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
package de.ovgu.featureide.ui.views.collaboration.action;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.views.collaboration.figures.RoleFigure;

/**
 * Collaboration diagram context menu option
 * Filter methods and fields of roles 
 * 
 * @author Steffen Schulze 
 * @author Christian Lausberger 
 */
public class ShowFieldsMethodsAction extends Action {
	
	public static final int ONLY_FIELDS = 0;
	public static final int ONLY_METHODS = 1;
	public static final int ONLY_CONTRACTS = 2;
	public static final int ONLY_INVARIANTS = 3;
	public static final int HIDE_PARAMETERS_AND_TYPES = 4;
	public static final int PUBLIC_FIELDSMETHODS = 5;
	public static final int PROTECTED_FIELDSMETHODS = 6;
	public static final int DEFAULT_FIELDSMETHODS = 7;
	public static final int PRIVATE_FIELDSMETHODS = 8;
	public static final int SELECT_ALL = 9;
	public static final int DESELECT_ALL = 10;
	
	private CollaborationView collaborationView;
	private int index;
	public ShowFieldsMethodsAction(String text, Image image, CollaborationView collaborationView, int index) {
		super(text, getImageDiscriptor(image));
		this.collaborationView = collaborationView;
		this.index = index;
	}
	
	@Override
	public void setChecked(boolean checked) {
		super.setChecked(isSelected());
	}
	
	private static ImageDescriptor getImageDiscriptor(Image image) {
		if (image != null){
			return ImageDescriptor.createFromImage(image);
		}
		return null;
	}
	
	public void run() {
		boolean[] selected = RoleFigure.getSelectedFieldMethod();
		
		switch (this.index) {
			case SELECT_ALL:
				setSelected(true, selected);
				break;
			case DESELECT_ALL:
				setSelected(false, selected);
				break;
			case ONLY_CONTRACTS:
			case ONLY_INVARIANTS:
			case ONLY_FIELDS:
			case ONLY_METHODS:
				noDeclarationTypSelected(selected);
				break;
			case HIDE_PARAMETERS_AND_TYPES:
				selected[index] = !selected[index];
				break;
			default:
				noOnlyFieldOrMethodSelected(selected);
		}
		RoleFigure.setSelectedFieldMethod(selected);
		collaborationView.refresh();
	}

	private void setSelected(boolean value, boolean[] selected) {
		for (int i = ONLY_FIELDS; i < selected.length; i++) {
			if (i != HIDE_PARAMETERS_AND_TYPES)
			selected[i] = value;
		}
		
	}
	
	private void noOnlyFieldOrMethodSelected(boolean[] selected) {
		if(!selected[ONLY_FIELDS] && !selected[ONLY_METHODS] ) {
			selected[ONLY_FIELDS] = true;
			selected[ONLY_METHODS] = true;
		}
		/*if(!selected[ONLY_FIELDS] && !selected[ONLY_METHODS]) {
			selected[ONLY_FIELDS] = true;
			selected[ONLY_METHODS] = true;
		}*/
		
		selected[index] = !selected[index];
	}
	
	private void noDeclarationTypSelected(boolean[] selected) {
		if(!selected[PUBLIC_FIELDSMETHODS] && !selected[PROTECTED_FIELDSMETHODS] && 
		   !selected[DEFAULT_FIELDSMETHODS] && !selected[PRIVATE_FIELDSMETHODS]) {
			selected[PUBLIC_FIELDSMETHODS] = true;
			selected[PROTECTED_FIELDSMETHODS] = true;
			selected[DEFAULT_FIELDSMETHODS] = true;
			selected[PRIVATE_FIELDSMETHODS] = true;
		}
		selected[index] = !selected[index];
	}
	
	private boolean isSelected() {
		switch (index) {
			case SELECT_ALL:
				return false;
			case DESELECT_ALL:
				return false;
			default:
				return RoleFigure.getSelectedFieldMethod()[index];
		}	
	}
}
