package de.ovgu.featureide.ui.statistics.ui.helper;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.ConfigParentNode;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.AbstractSortModeNode;
import de.ovgu.featureide.ui.statistics.ui.ConfigDialog;

/**
 * Simple listener for the treeview.
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class TreeClickListener implements IDoubleClickListener {
	
	private TreeViewer view;
	
	public TreeClickListener(TreeViewer view) {
		super();
		this.view = view;
	}

	/**
	 * Performs actions depending on the type of the clicked note e.g. opening a
	 * dialog for {@link ConfigParentNode.ConfigNode} or
	 * expanding/collapsing nodes(default operation).
	 * 
	 */
	@Override
	public void doubleClick(DoubleClickEvent event) {
		Object[] selectedObjects = ((TreeSelection) event.getSelection()).toArray();
		for (Object selected : selectedObjects) {
			if (selected instanceof ConfigParentNode.ConfigNode) {
				handleConfigNodes(event, selected);
			} else if (selected instanceof AbstractSortModeNode && view.getExpandedState(selected)) {
				final AbstractSortModeNode sortNode = ((AbstractSortModeNode) selected);
				sortNode.setSortByValue(!sortNode.isSortByValue());
				
				UIJob job = new UIJob("resort node") {
					@Override
					public IStatus runInUIThread(IProgressMonitor monitor) {
						view.refresh(sortNode);
						return Status.OK_STATUS;
					}
				};
				job.setPriority(Job.INTERACTIVE);
				job.schedule();
			} else if (selected instanceof Parent && ((Parent) selected).hasChildren()) {
				view.setExpandedState(selected, !view.getExpandedState(selected));
			}
		}
	}
	
	/**
	 * Opens a dialog to start the calculation corresponding to the clicked
	 * config-node - but only if their isn't already a calculation in progress.
	 * 
	 */
	private void handleConfigNodes(DoubleClickEvent event, Object selected) {
		ConfigParentNode.ConfigNode clickedNode = (ConfigParentNode.ConfigNode) selected;
		if (!clickedNode.isCalculating()) {
			ConfigDialog dial = new ConfigDialog(event.getViewer().getControl().getShell(), clickedNode.getDescription());
			if (dial.open() == ConfigDialog.OK) {
				clickedNode.calculate(dial.getTimeout(), dial.getPriority());
			}
		}
	}
}