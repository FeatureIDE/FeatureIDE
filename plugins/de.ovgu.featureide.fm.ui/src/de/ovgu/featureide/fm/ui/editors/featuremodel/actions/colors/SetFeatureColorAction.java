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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors;

import static de.ovgu.featureide.fm.core.localization.StringTable.COLORATION;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.wizards.SelectColorSchemeWizard;

/**
 * ColorSelectedFeatureAction is the action that opens the ColorSelectedFeatureDialog
 * with the selected features in the feature diagram.
 * 
 * @author Christian Elzholz
 * @author Marcus Schmelz
 * @author Marcus Pinnecke
 * @author Paul Maximilian Bittner
 * @author Niklas Lehnfeld
 * @author Mohammed Mahhouk
 * @author Antje Moench
 */
public class SetFeatureColorAction extends Action {

	private static ImageDescriptor colorImage = FMUIPlugin.getDefault().getImageDescriptor("icons/FeatureColorIcon.gif");
	private List<IEventListener> colorChangedListeners;
	protected List<IFeature> featureList = new ArrayList<>();
	private IFeatureModel featureModel;

	private boolean undoRedoEnabled = false;

	private ISelectionChangedListener selectionListener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			setEnabled(isSelectionValid(selection));
			if (isEnabled())
				updateFeatureList(selection);
		}
	};
	/**
	 * @param viewer
	 */
	public SetFeatureColorAction(ISelectionProvider viewer) {
		this(viewer, null);
	}

	/**
	 * @param viewer
	 */
	public SetFeatureColorAction(Viewer viewer) {
		this(viewer, null);
	}

	/**
	 * @param viewer
	 * @param featureModel
	 */
	public SetFeatureColorAction(Viewer viewer, IFeatureModel featureModel) {
		super(COLORATION);
		viewer.addSelectionChangedListener(selectionListener);
		init(featureModel);
	}

	/**
	 * @param viewer
	 * @param featureModel
	 */
	public SetFeatureColorAction(ISelectionProvider viewer, IFeatureModel featureModel) {
		super(COLORATION);
		viewer.addSelectionChangedListener(selectionListener);
		init(featureModel);
	}

	public SetFeatureColorAction(IStructuredSelection selection, IFeatureModel featureModel) {
		super(COLORATION);
		updateFeatureList(selection);
		init(featureModel);
	}

	private void init(IFeatureModel featureModel) {
		setImageDescriptor(colorImage);
		this.featureModel = featureModel;
	}

	public void setEnableUndoRedo(boolean set) {
		this.undoRedoEnabled = set;
	}

	protected boolean isSelectionValid(IStructuredSelection selection) {
		for (Object object : selection.toList()) {
			if (object instanceof IFeature) {
				continue;
			} else if (object instanceof AbstractGraphicalEditPart) {
				AbstractGraphicalEditPart agep = (AbstractGraphicalEditPart) object;
				IFeature feature = featureModel.getFeature(agep.getModel().toString());
				if (feature != null)
					continue;
			} else if (object instanceof FeatureEditPart) {
				continue;
			} else {
				return false;
			}
		}
		return true;
	}

	/**
	 * Creates a featureList with the selected features of the feature diagram.
	 * 
	 * @param selection
	 */
	public void updateFeatureList(IStructuredSelection selection) {
		if (!selection.isEmpty()) {
			featureList.clear();

			Object[] editPartArray = selection.toArray();

			for (int i = 0; i < selection.size(); i++) {
				Object editPart = editPartArray[i];

				if (editPart instanceof IFeature) {
					featureList.add((IFeature) editPart);
				} else if (editPart instanceof FeatureEditPart) {
					FeatureEditPart editP = (FeatureEditPart) editPart;
					IGraphicalFeature feature = editP.getModel();
					featureList.add(feature.getObject());
				} else if (editPart instanceof AbstractGraphicalEditPart) {
					AbstractGraphicalEditPart agep = (AbstractGraphicalEditPart) editPart;
					IFeature feature = featureModel.getFeature(agep.getModel().toString());
					featureList.add(feature);
				}
			}
		}
		setEnabled(!featureList.isEmpty());
	}

	public void setFeatureModel(IFeatureModel featureModel) {
		this.featureModel = featureModel;
	}

	public void run() {
		FeatureColor selectedColor = null;
		Shell shell = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell();
		List<IFeature> features = new ArrayList<>(featureList);

		if (!features.isEmpty()) {

			if (featureModel != null) {
				// only allow coloration if the active profile is not the default profile
				if (FeatureColorManager.isDefault(featureModel)) {
					Wizard selectColorSchemeWizard = new SelectColorSchemeWizard(featureModel);

					WizardDialog dialog = new WizardDialog(shell, selectColorSchemeWizard);
					dialog.create();

					if (dialog.open() == Dialog.CANCEL) {
						return;
					}
				}
			}

			// If the color of only one object should be changed, its color is selected in the dialog initially.
			if (features.size() == 1) {
				IFeature selectedFeature = features.get(0);
				selectedColor = FeatureColorManager.getColor(selectedFeature);
			}

			SetFeatureColorDialog dialog = new SetFeatureColorDialog(shell, features, selectedColor, undoRedoEnabled);

			// inform ui to update
			if (dialog.open() == Window.OK) {
				//TODO SPREY 
				/*
				try {
					java.nio.file.Path modelPath = featureModel.getSourceFile().getFileName();
					IPath rootPath = ResourcesPlugin.getWorkspace().getRoot().getLocation();
					IPath relPath = modelPath.makeRelativeTo(rootPath);

					IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(relPath);
					IFeatureProject project = CorePlugin.getFeatureProject(file);
					project.getProject().touch(null);
					project.getProject().refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());
				} catch (IOException e) {
					e.printStackTrace();
				} catch (CoreException e) {
					e.printStackTrace();
				}
				*/
			}
		}
	}

}
