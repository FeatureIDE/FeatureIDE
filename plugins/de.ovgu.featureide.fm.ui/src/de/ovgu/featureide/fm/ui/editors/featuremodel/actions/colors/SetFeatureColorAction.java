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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.wizards.SelectColorSchemeWizard;

/**
 * ColorSelectedFeatureAction is the action that opens the ColorSelectedFeatureDialog
 * with the selected features in the feature diagram.
 * 
 * @author Christian Elzholz, Marcus Schmelz
 * @author Marcus Pinnecke
 */
public class SetFeatureColorAction extends Action {

	private static ImageDescriptor colorImage = FMUIPlugin.getDefault().getImageDescriptor("icons/FeatureColorIcon.gif");

	protected List<IGraphicalFeature> featureList = new ArrayList<>();
	private final IFeatureModel featureModel;

	/**
	 * @param viewer
	 * @param project
	 */
	public SetFeatureColorAction(FeatureDiagramEditor viewer) {
		this(viewer, null);
	}

	/**
	 * @param viewer
	 * @param project
	 * @param featureModel
	 */
	public SetFeatureColorAction(FeatureDiagramEditor viewer, IFeatureModel featureModel) {
		super(COLORATION);
		if (viewer instanceof GraphicalViewerImpl) {
			
			ISelectionChangedListener selectionListener = new ISelectionChangedListener() {
				public void selectionChanged(SelectionChangedEvent event) {
					IStructuredSelection selection = (IStructuredSelection) event.getSelection();
					updateFeatureList(selection);
					setEnabled(!featureList.isEmpty());
				}
			};
			
			((GraphicalViewerImpl) viewer).addSelectionChangedListener(selectionListener);
		}
		
		setImageDescriptor(colorImage);
		this.featureModel = featureModel;
	}
	
	public SetFeatureColorAction(final TreeViewer viewer, final IGraphicalFeatureModel graphicalFeatureModel, IFeatureModel featureModel){
		super(COLORATION);
		ISelectionChangedListener selectionListener = new ISelectionChangedListener() {
			
			public void selectionChanged(SelectionChangedEvent event) {
				
				IStructuredSelection selection = (IStructuredSelection) event.getSelection();
				featureList.clear();
				
				Object[] objects = selection.toArray();
				for(Object obj : objects){
					Feature feature = (Feature) obj;
					featureList.add(graphicalFeatureModel.getGraphicalFeature(feature));					
				}
				setEnabled(!featureList.isEmpty());
				
				viewer.refresh();
			}
		};
			
		viewer.addSelectionChangedListener(selectionListener);
		

		setImageDescriptor(colorImage);
		this.featureModel = featureModel;
	}

	/**
	 * @param selection
	 *            Creates a featureList with the selected features of the feature diagram.
	 */
	public void updateFeatureList(IStructuredSelection selection) {
		if (!selection.isEmpty()) {			
			featureList.clear();
			
			Object[] editPartArray = selection.toArray();

			for (int i = 0; i < selection.size(); i++) {
				Object editPart = editPartArray[i];
				
				if (editPart instanceof FeatureEditPart) {
					FeatureEditPart editP = (FeatureEditPart) editPart;
					IGraphicalFeature feature = editP.getFeature();
					if (!featureList.contains(feature))
						featureList.add(feature);
				}
			}
		}
	}
	

	public void run() {
		FeatureColor selectedColor = null;
		Shell shell = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell();
		List<IGraphicalFeature> features = new ArrayList<>(featureList);

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
				IGraphicalFeature selectedFeature = features.get(0);
				selectedColor = FeatureColorManager.getColor(selectedFeature.getObject());
			}

			SetFeatureColorDialog dialog = new SetFeatureColorDialog(shell, features, selectedColor);

			if (dialog.open() == Window.OK) {
				featureModel.fireEvent(new FeatureIDEEvent(features, FeatureIDEEvent.EventType.COLOR_CHANGED));
			}
		}
	}

}
