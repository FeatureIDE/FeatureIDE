package de.ovgu.featureide.fm.attributes.view.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;

/**
 * Action for the {@link FeatureAttributeView}. Is used to expand all tree entries.
 * 
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class ExpandTreeViewer extends Action {

	private TreeViewer view;

	public ExpandTreeViewer(TreeViewer view, ImageDescriptor icon) {
		super("", icon);
		this.view = view;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.Action#run()
	 */
	@Override
	public void run() {
		view.expandToLevel(TreeViewer.ALL_LEVELS);
	}
}
