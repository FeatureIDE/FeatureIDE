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
package de.ovgu.featureide.ui.views.collaboration.action;

import java.util.List;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.views.collaboration.editparts.ClassEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.CollaborationEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.RoleEditPart;
import de.ovgu.featureide.ui.views.collaboration.figures.ClassFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.CollaborationFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.UnderlayerFigure;
import de.ovgu.featureide.ui.wizards.NewFeatureIDEFileWizard;

/**
 * Add a role to the CollaborationDiagramm.
 * 
 * @author Constanze Adler
 * @author Stephan Besecke
 * @author Jens Meinicke
 */
public class AddRoleAction extends Action {
	private GraphicalViewerImpl viewer;
	private CollaborationView collaborationView;

	public AddRoleAction(String text, GraphicalViewerImpl view, CollaborationView collcaborationView) {
		super(text);
		viewer = view;
		this.collaborationView = collcaborationView;
		setImageDescriptor(PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_OBJ_ADD));
	}

	public void run() {
		IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
		Object selectedItem = selection.getFirstElement();

		String feature = getFeatureName();
		String clss = "";

		if (selectedItem != null) {
			if (selectedItem instanceof CollaborationEditPart) {
				feature = ((CollaborationEditPart) selectedItem).getCollaborationModel().getName();
			} else if (selectedItem instanceof RoleEditPart) {
				feature = ((RoleEditPart) selectedItem).getRoleModel().getFeature().getName();
			} else if (selectedItem instanceof ClassEditPart) {
				clss = ((ClassEditPart) selectedItem).getClassModel().getName();
				if (clss.contains("."))
					clss = clss.substring(0, clss.lastIndexOf('.'));
			}
		}

		NewFeatureIDEFileWizard wizard = new NewFeatureIDEFileWizard();
		wizard.init(PlatformUI.getWorkbench(), selection, feature, clss);

		WizardDialog dialog = new WizardDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), wizard);
		dialog.create();
		dialog.open();
	}

	/**
	 * returns feature name of current cursor position
	 */
	private String getFeatureName() {
		String feature = "";

		List<?> list = viewer.getContents().getChildren();
		int cursorY = collaborationView.getCursorPosition().y;

		for (Object object : list) {
			if (object instanceof CollaborationEditPart) {
				CollaborationFigure collFigure = ((UnderlayerFigure) ((CollaborationEditPart) object).getFigure()).getCollaborationFigure();

				if (collFigure.isConfiguration)
					continue;

				int index = list.indexOf(object);

				int min = collFigure.getBounds().y - 4;
				int max = collFigure.getBounds().y + collFigure.getBounds().height + 4;

				if (list.size() > index + 1) {
					Object edit = list.get(index + 1);
					if (edit instanceof CollaborationEditPart) {

						CollaborationFigure nextCollFigure = ((UnderlayerFigure) ((CollaborationEditPart) edit).getFigure())
								.getCollaborationFigure();

						max = nextCollFigure.getBounds().y - 4;
					} else if (edit instanceof ClassEditPart) {
						ClassFigure nextCollFigure = ((ClassFigure) ((ClassEditPart) edit).getFigure());
						max = nextCollFigure.getBounds().height - 4;
					}
				}
				if (cursorY >= min && cursorY <= max) {
					feature = ((CollaborationEditPart) object).getCollaborationModel().getName();
					break;
				}
			}
		}
		return feature;
	}
}
