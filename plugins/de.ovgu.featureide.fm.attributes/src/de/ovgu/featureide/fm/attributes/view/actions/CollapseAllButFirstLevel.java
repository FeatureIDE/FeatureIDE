package de.ovgu.featureide.fm.attributes.view.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;

/**
 * Action for the {@link FeatureAttributeView}. Is used to collapse all tree entries to the first layer.
 * 
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class CollapseAllButFirstLevel extends Action {

	private TreeViewer view;

	public CollapseAllButFirstLevel(TreeViewer view, ImageDescriptor icon) {
		super("", icon);
		this.view = view;
	}

	@Override
	public void run() {
		view.collapseAll();
		view.expandToLevel(2);
	}

}
