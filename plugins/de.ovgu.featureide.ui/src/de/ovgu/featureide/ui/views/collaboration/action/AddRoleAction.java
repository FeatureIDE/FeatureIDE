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

	private final GraphicalViewerImpl viewer;
	private final CollaborationView collaborationView;

	public AddRoleAction(String text, GraphicalViewerImpl view, CollaborationView collcaborationView) {
		super(text);
		viewer = view;
		collaborationView = collcaborationView;
		setImageDescriptor(PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_OBJ_ADD));
	}

	@Override
	public void run() {
		final IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
		final Object selectedItem = selection.getFirstElement();

		String feature = getFeatureName();
		String clss = "";
		String pack = "";

		if (selectedItem != null) {
			if (selectedItem instanceof CollaborationEditPart) {
				feature = ((CollaborationEditPart) selectedItem).getCollaborationModel().getName();
			} else if (selectedItem instanceof RoleEditPart) {
				feature = ((RoleEditPart) selectedItem).getRoleModel().getFeature().getName();
				clss = ((RoleEditPart) selectedItem).getRoleModel().getClassFragment().getName();
				pack = ((RoleEditPart) selectedItem).getRoleModel().getClassFragment().getPackage();
				if (clss.contains(".")) {
					clss = clss.substring(0, clss.lastIndexOf('.'));
				}
				if (clss.contains("/")) {
					clss = clss.substring(clss.lastIndexOf("/") + 1, clss.length());
				}
			} else if (selectedItem instanceof ClassEditPart) {
				clss = ((ClassEditPart) selectedItem).getClassModel().getName();
				pack = ((ClassEditPart) selectedItem).getClassModel().getName().replace("/", ".");
				if (pack.indexOf(".") != pack.lastIndexOf(".")) {
					pack = pack.substring(0, pack.lastIndexOf("."));
					pack = pack.substring(0, pack.lastIndexOf('.'));
				} else {
					pack = "";
				}
				if (clss.contains(".")) {
					clss = clss.substring(0, clss.lastIndexOf('.'));
				}
				if (clss.contains("/")) {
					clss = clss.substring(clss.lastIndexOf("/") + 1, clss.length());
				}
			}
		}

		final NewFeatureIDEFileWizard wizard = new NewFeatureIDEFileWizard();
		wizard.init(PlatformUI.getWorkbench(), selection, feature, clss, pack);

		final WizardDialog dialog = new WizardDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), wizard);
		dialog.create();
		dialog.open();
	}

	/**
	 * returns feature name of current cursor position
	 */
	private String getFeatureName() {
		String feature = "";

		final List<?> list = viewer.getContents().getChildren();
		final int cursorY = collaborationView.getCursorPosition().y;

		for (final Object object : list) {
			if (object instanceof CollaborationEditPart) {
				final CollaborationFigure collFigure = ((UnderlayerFigure) ((CollaborationEditPart) object).getFigure()).getCollaborationFigure();

				if (collFigure.isConfiguration) {
					continue;
				}

				final int index = list.indexOf(object);

				final int min = collFigure.getBounds().y - 4;
				int max = collFigure.getBounds().y + collFigure.getBounds().height + 4;

				if (list.size() > (index + 1)) {
					final Object edit = list.get(index + 1);
					if (edit instanceof CollaborationEditPart) {

						final CollaborationFigure nextCollFigure = ((UnderlayerFigure) ((CollaborationEditPart) edit).getFigure()).getCollaborationFigure();

						max = nextCollFigure.getBounds().y - 4;
					} else if (edit instanceof ClassEditPart) {
						final ClassFigure nextCollFigure = ((ClassFigure) ((ClassEditPart) edit).getFigure());
						max = nextCollFigure.getBounds().height - 4;
					}
				}
				if ((cursorY >= min) && (cursorY <= max)) {
					feature = ((CollaborationEditPart) object).getCollaborationModel().getName();
					break;
				}
			}
		}
		return feature;
	}
}
