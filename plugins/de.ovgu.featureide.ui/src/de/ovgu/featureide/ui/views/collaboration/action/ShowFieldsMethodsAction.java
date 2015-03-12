/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

	public static final int FIELDS_WITH_REFINEMENTS = 0;
	public static final int FIELDS_WITHOUT_REFINEMENTS = 1;
	public static final int METHODS_WITH_REFINEMENTS = 2;
	public static final int METHODS_WITHOUT_REFINEMENTS = 3;
	public static final int ONLY_CONTRACTS = 4;
	public static final int ONLY_INVARIANTS = 5;
	public static final int SHOW_NESTED_CLASSES = 6;
	public static final int HIDE_PARAMETERS_AND_TYPES = 7;
	public static final int PUBLIC_FIELDSMETHODS = 8;
	public static final int PROTECTED_FIELDSMETHODS = 9;
	public static final int DEFAULT_FIELDSMETHODS = 10;
	public static final int PRIVATE_FIELDSMETHODS = 11;
	public static final int SELECT_ALL = 12;
	public static final int DESELECT_ALL = 13;

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
		if (image != null) {
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
		default:
			selected[this.index] = !selected[this.index];			
			super.setChecked(selected[this.index]);
			break;
		}
		
		RoleFigure.setSelectedFieldMethod(selected);
		collaborationView.refresh();
	}

	private void setSelected(boolean value, boolean[] selected) {
		for (int i = FIELDS_WITH_REFINEMENTS; i < selected.length; i++) {
			if (i != HIDE_PARAMETERS_AND_TYPES)
			{
				selected[i] = value;
			}
		}
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
