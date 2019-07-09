package de.ovgu.featureide.fm.attributes.view.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeViewSelectionFilter;

/**
 * Action for the {@link FeatureAttributeView}. Is used to toggle the filtering for the view.
 * 
 * @see FeatureAttributeViewSelectionFilter
 * 
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class SynchFeatureAttributesToFeatureDiagramAction extends Action {

	private FeatureAttributeView view;
	private TreeViewer treeView;

	public SynchFeatureAttributesToFeatureDiagramAction(FeatureAttributeView view, TreeViewer treeView, ImageDescriptor icon) {
		super("", icon);
		this.view = view;
		this.treeView = treeView;
		setChecked(view.synchToFeatureDiagram);
	}

	@Override
	public void run() {
		view.synchToFeatureDiagram = !view.synchToFeatureDiagram;
		setChecked(view.synchToFeatureDiagram);
		view.selectedAutomaticFeatures = null;
		view.selectedManualFeatures = null;
		treeView.refresh();
	}

}
