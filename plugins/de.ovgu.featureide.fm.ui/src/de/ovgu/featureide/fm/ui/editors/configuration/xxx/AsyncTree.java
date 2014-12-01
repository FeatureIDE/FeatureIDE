/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.configuration.xxx;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationPage.Methode;

/**
 * TODO description
 * 
 * @author Marcus Pinnecke
 */
public class AsyncTree {

	private static final String JOB_NAME_BUILDING_TREE = "Building tree...";
	private static final String JOB_NAME_TRAVERSE_TREE = "Traversing tree...";
	
	private Tree tree;

	public AsyncTree(Tree tree) 
	{
		this.tree = tree;
	}
	
	public Tree getTree()
	{
		return this.tree;
	}

	public UIJob build(final TreeItem node, final TreeElement[] children,
					 final FunctionalInterfaces.IFunction<Void, Void> callbackIfDone) 
	{
		UIJob job = new UIJob(AsyncTree.JOB_NAME_BUILDING_TREE) {

			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				doBuildingAsync(node, children);
				callbackIfDone.invoke(null);
				return Status.OK_STATUS;
			}

		};
		job.schedule();
		return job;
	}

	public UIJob traverse(
			final TreeItem node,
			final FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void> perNodeFunction,
			final FunctionalInterfaces.IFunction<Void, Void> callbackIfDone) 
	{
		UIJob job = new UIJob(AsyncTree.JOB_NAME_TRAVERSE_TREE) {

			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				traverseAsync(node, perNodeFunction);
				callbackIfDone.invoke(null);
				return Status.OK_STATUS;
			}

		};
		job.schedule();
		return job;
	}
	
	private void traverseAsync(TreeItem item, final FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void> perNodeFunction)
	{
		final TreeItem[] children = item.getItems();
		for (int i = 0; i < children.length; i++) {		
			final TreeItem childNode = children[i];
			final Object data = childNode.getData();
			final SelectableFeature feature = (SelectableFeature) data;
			perNodeFunction.invoke(childNode, feature);
			
			Display.getCurrent().asyncExec(new Runnable() {
				@Override
				public void run() {
					if (childNode.getItemCount() > 0) {
						traverseAsync(childNode, perNodeFunction);
					}
				}
			});		
		}
	}

	private void doBuildingAsync(final TreeItem parent, final TreeElement[] children) 
	{
		for (int i = 0; i < children.length; i++) {
			if (children[i] instanceof SelectableFeature) {
				final SelectableFeature currentFeature = (SelectableFeature) children[i];
				if (!currentFeature.getFeature().isHidden()) {
					final TreeItem childNode = new TreeItem(parent, 0);
					final String displayText = currentFeature.getFeature().getDisplayName();
					childNode.setText(displayText);
					childNode.setData(currentFeature);
					if (children[i].hasChildren()) {
						Display.getCurrent().asyncExec(new Runnable() {
							@Override
							public void run() {
								doBuildingAsync(childNode, currentFeature.getChildren());
							}
						});
					}
				}
			}
		}
	}
}
