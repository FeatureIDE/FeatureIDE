/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.views.collaboration.figures.RoleFigure;

/**
 * Collaboration diagram context menu option Filter methods and fields of roles
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

	public static final int SELECT_ALL_METHOD_ACCESS = 20;
	public static final int DESELECT_ALL_METHOD_ACCESS = 21;

	private final CollaborationView collaborationView;
	private int index;

	// Custom action with checkbox
	public ShowFieldsMethodsAction(String text, Image image, CollaborationView collaborationView, int index) {
		this(text, image, collaborationView, index, IAction.AS_CHECK_BOX);
	}

	// Custom action with style
	public ShowFieldsMethodsAction(String text, Image image, CollaborationView collaborationView, int index, int style) {
		super(text, style);
		setImageDescriptor(getImageDiscriptor(image));
		this.collaborationView = collaborationView;
		this.index = index;
	}

	public void setActionIndex(int index) {
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

	private boolean[] selectAllAccessModifiers(boolean[] selected, boolean value) {
		for (int i = PUBLIC_FIELDSMETHODS; i <= PRIVATE_FIELDSMETHODS; i++) {
			selected[i] = value;
		}
		return selected;
	}

	@Override
	public void run() {
		final boolean[] selected = RoleFigure.getSelectedFieldMethod();
		switch (index) {
		case SELECT_ALL:
			setSelected(true, selected);
			break;
		case DESELECT_ALL:
			setDeselected(false, selected);
			break;
		case SELECT_ALL_METHOD_ACCESS:
			selectAllAccessModifiers(selected, true);
			break;
		case DESELECT_ALL_METHOD_ACCESS:
			selectAllAccessModifiers(selected, false);
			break;
		case PUBLIC_FIELDSMETHODS:
			selected[index] = !selected[index];
			super.setChecked(selected[index]);
			break;
		case PRIVATE_FIELDSMETHODS:
			selected[index] = !selected[index];
			super.setChecked(selected[index]);
			break;
		case DEFAULT_FIELDSMETHODS:
			selected[index] = !selected[index];
			super.setChecked(selected[index]);
			break;
		case PROTECTED_FIELDSMETHODS:
			selected[index] = !selected[index];
			super.setChecked(selected[index]);
			break;
		default:
			selected[index] = !selected[index];
			super.setChecked(selected[index]);
			break;
		}

		RoleFigure.setSelectedFieldMethod(selected);
		collaborationView.reloadImage();
		collaborationView.refresh();

		if ((index == SELECT_ALL) || (index == DESELECT_ALL)) {
			collaborationView.selectAll();
		}
	}

	private void setSelected(boolean value, boolean[] selected) {
		for (int i = FIELDS_WITH_REFINEMENTS; i < selected.length; i++) {
			if ((i != HIDE_PARAMETERS_AND_TYPES) && (i != ONLY_CONTRACTS) && (i != ONLY_INVARIANTS)) {
				selected[i] = value;
			}
		}
	}

	private void setDeselected(boolean value, boolean[] selected) {
		for (int i = FIELDS_WITH_REFINEMENTS; i < selected.length; i++) {
			if (i != HIDE_PARAMETERS_AND_TYPES) {
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
		case SELECT_ALL_METHOD_ACCESS:
			return true;
		case DESELECT_ALL_METHOD_ACCESS:
			return false;
		default:
			return RoleFigure.getSelectedFieldMethod()[index];
		}
	}

}
