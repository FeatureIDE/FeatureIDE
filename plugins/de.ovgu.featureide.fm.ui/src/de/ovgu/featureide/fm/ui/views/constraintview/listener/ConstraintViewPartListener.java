/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.views.constraintview.listener;

import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;

/**
 * This class is the implementation of the IPartListener for the ConstraintView.
 *
 * @author Rosiak Kamil
 * @author Soeren Viegener
 * @author Philipp Vulpius
 */
public class ConstraintViewPartListener implements IPartListener {

	private final ConstraintViewController controller;

	public ConstraintViewPartListener(ConstraintViewController cvc) {
		controller = cvc;
	}

	@Override
	public void partActivated(IWorkbenchPart part) {
		if (part instanceof FeatureModelEditor) {
			controller.setFeatureModelEditor((FeatureModelEditor) part);
			controller.checkForRefresh();
		} else if (part instanceof IEditorPart) {
			controller.setFeatureModelEditor(null);
			controller.checkForRefresh();
		}

		if(!controller.isConstraintsViewVisible()){
			controller.setConstraintsHidden(controller.getFeatureModelEditor(), false);
		}else if(part instanceof ConstraintViewController){
			controller.setConstraintsHidden(controller.getFeatureModelEditor(), true);
		}
	}

	@Override
	public void partBroughtToTop(IWorkbenchPart part) {
		if (part instanceof FeatureModelEditor) {
			controller.setFeatureModelEditor((FeatureModelEditor) part);
			controller.checkForRefresh();
		}
	}

	@Override
	public void partClosed(IWorkbenchPart part) {
		if ((part instanceof FeatureModelEditor) && (part == controller.getFeatureModelEditor())) {
			controller.setFeatureModelEditor(null);
			controller.checkForRefresh();
		}
	}

	@Override
	public void partDeactivated(IWorkbenchPart part) {
		// not needed, covered in the other events
	}

	@Override
	public void partOpened(IWorkbenchPart part) {
		if (part instanceof FeatureModelEditor) {
			controller.setFeatureModelEditor((FeatureModelEditor) part);
			controller.checkForRefresh();
		}
	}
}
