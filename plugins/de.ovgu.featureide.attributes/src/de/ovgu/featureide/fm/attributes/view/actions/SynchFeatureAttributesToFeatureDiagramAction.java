package de.ovgu.featureide.fm.attributes.view.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;

public class SynchFeatureAttributesToFeatureDiagramAction extends Action {

	private FeatureAttributeView view;
	private TreeViewer treeView;

	public SynchFeatureAttributesToFeatureDiagramAction(FeatureAttributeView view, TreeViewer treeView, ImageDescriptor icon) {
		super("", icon);
		this.view = view;
		this.treeView = treeView;
		setChecked(view.synchToFeatureDiagram);
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.Action#run()
	 */
	@Override
	public void run() {
		view.synchToFeatureDiagram ^= true;
		setChecked(view.synchToFeatureDiagram);
		view.selectedAutomaticFeatures = null;
		view.selectedManualFeatures = null;
		treeView.refresh();
	}
}
