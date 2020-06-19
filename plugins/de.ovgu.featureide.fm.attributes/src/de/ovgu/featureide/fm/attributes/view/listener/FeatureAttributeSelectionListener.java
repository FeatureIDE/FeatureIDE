package de.ovgu.featureide.fm.attributes.view.listener;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * Listener used to define the set of features to show in the {@link FeatureAttributeView}. Is only active when {@link FeatureAttributeView} is in operation
 * mode {@link FeatureAttributeView.FeatureAttributeOperationMode} == FEATURE_DIAGRAM
 * 
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class FeatureAttributeSelectionListener implements ISelectionChangedListener {

	FeatureAttributeView view;
	TreeViewer treeViewer;

	public FeatureAttributeSelectionListener(FeatureAttributeView attributeView, TreeViewer treeView) {
		this.view = attributeView;
		this.treeViewer = treeView;
	}

	public List<IFeature> selectedManualFeatures;
	public List<IFeature> selectedAutomaticFeatures;

	@Override
	public void selectionChanged(SelectionChangedEvent event) {
		if (view.getManager() == null) {
			return;
		}

		if (!view.synchToFeatureDiagram) {
			selectedManualFeatures = null;
			selectedAutomaticFeatures = null;
			treeViewer.refresh();
			return;
		}

		// First, filter only features from the selection and add them to the manual set
		selectedManualFeatures = new ArrayList<>();
		ISelection selection = event.getSelection();
		if (selection instanceof IStructuredSelection) {
			for (Object obj : ((IStructuredSelection) selection).toList()) {
				if (obj instanceof FeatureEditPart) {
					FeatureEditPart editPart = (FeatureEditPart) obj;
					selectedManualFeatures.add(editPart.getModel().getObject());
				}
			}
		}

		selectedAutomaticFeatures = new ArrayList<>();
		for (IFeature iFeature : selectedManualFeatures) {
			addParentsToFullList(iFeature);
		}

		treeViewer.refresh();

		for (IFeature iFeature : selectedAutomaticFeatures) {
			treeViewer.setExpandedState(iFeature, true);
		}
		view.repackAllColumns();

	}

	private void addParentsToFullList(IFeature feature) {
		if (!selectedAutomaticFeatures.contains(feature)) {
			selectedAutomaticFeatures.add(feature);
		}
		if (!feature.getStructure().isRoot()) {
			addParentsToFullList(feature.getStructure().getParent().getFeature());
		}
	}

	/**
	 * Returns all {@link IFeature} which should be displayed in the {@link FeatureAttributeView}.
	 * 
	 * @return Set of all filtered {@link IFeature}
	 */
	public List<IFeature> getSelectedFeatures() {
		return selectedAutomaticFeatures;
	}

	/**
	 * Returns all {@link IFeature} whose {@link FeatureAttribute} should be displayed in the {@link FeatureAttributeView}.
	 * 
	 * @return Set of all filtered {@link IFeature}
	 */
	public List<IFeature> getSelectedFeaturesOfInterest() {
		return selectedManualFeatures;
	}

	/**
	 * Removes all {@link IFeature} from the selection.
	 */
	public void clearSelection() {
		selectedManualFeatures = new ArrayList<>();
		selectedAutomaticFeatures = new ArrayList<>();
		if (!treeViewer.getControl().isDisposed()) {
			treeViewer.refresh();
		}
	}
}
