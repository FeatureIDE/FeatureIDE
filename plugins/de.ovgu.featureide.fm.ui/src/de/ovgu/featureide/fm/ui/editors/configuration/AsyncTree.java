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
package de.ovgu.featureide.fm.ui.editors.configuration;

import java.util.HashMap;

import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.FunctionalInterfaces;
import de.ovgu.featureide.fm.core.FunctionalInterfaces.IFunction;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.TreeElement;

/**
 * TODO description
 * 
 * @author Marcus Pinnecke
 */
public class AsyncTree {
	
	private static class ThreadCounter {
		private final FunctionalInterfaces.IFunction<Void, Void> callbackIfDone;
		private Integer count = 0;
		
		public ThreadCounter(IFunction<Void, Void> callbackIfDone) {
			this.callbackIfDone = callbackIfDone;
		}

		public void inc() {
			synchronized (count) {
				++count;
			}
		}

		public void dec() {
			boolean done;
			synchronized (count) {
				done = --count == 0;
			}
			if (done) {
				callbackIfDone.invoke(null);
			}
		}
	}

	private Tree tree;
	private final HashMap<SelectableFeature, TreeItem> itemMap;

	public AsyncTree(Tree tree, HashMap<SelectableFeature, TreeItem> itemMap) {
		this.tree = tree;
		this.itemMap = itemMap;
	}

	public Tree getTree() {
		return this.tree;
	}

	public UIJob build(final TreeItem node, final TreeElement[] children, final FunctionalInterfaces.IFunction<Void, Void> callbackIfDone) {
		final Display currentDisplay = Display.getCurrent();
		if (currentDisplay != null) {
			doBuildingAsync(node, children, new ThreadCounter(callbackIfDone), currentDisplay);
		}
		return null;
	}

	public UIJob traverse(final TreeItem node, final FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void> perNodeFunction, final FunctionalInterfaces.IFunction<Void, Void> callbackIfDone) {
		final Display currentDisplay = Display.getCurrent();
		if (currentDisplay != null) {
			traverseAsync(node, perNodeFunction, new ThreadCounter(callbackIfDone), currentDisplay);
		}
		return null;
	}

	private void traverseAsyncRec(TreeItem item, final FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void> perNodeFunction,
			ThreadCounter threadCounter, Display currentDisplay) {
		final TreeItem[] children = item.getItems();
		for (int i = 0; i < children.length; i++) {
			final TreeItem childNode = children[i];
			final Object data = childNode.getData();
			final SelectableFeature feature = (SelectableFeature) data;
			perNodeFunction.invoke(childNode, feature);
			
			if (childNode.getItemCount() > 0) {
				traverseAsync(childNode, perNodeFunction, threadCounter, currentDisplay);
			}
		}
		threadCounter.dec();
	}
	
	private void traverseAsync(final TreeItem item, final FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void> perNodeFunction,
			final ThreadCounter threadCounter, final Display currentDisplay) {
		threadCounter.inc();
		currentDisplay.asyncExec(new Runnable() {
			@Override
			public void run() {
				traverseAsyncRec(item, perNodeFunction, threadCounter, currentDisplay);
			}
		});
	}	

	private void doBuildingAsyncRec(final TreeItem parent, final TreeElement[] children, final ThreadCounter threadCounter, final Display currentDisplay) {
		for (int i = 0; i < children.length; i++) {
			final TreeElement child = children[i];
			if (child instanceof SelectableFeature) {
				final SelectableFeature currentFeature = (SelectableFeature) child;
				if (!currentFeature.getFeature().isHidden()) {
					final TreeItem childNode = new TreeItem(parent, 0);
					childNode.setText(currentFeature.getFeature().getDisplayName());
					childNode.setData(currentFeature);
					itemMap.put(currentFeature, childNode);
					if (currentFeature.hasChildren()) {
						doBuildingAsync(childNode, currentFeature.getChildren(), threadCounter, currentDisplay);
					}
				}
			}
		}
		parent.setExpanded(true);
		threadCounter.dec();
	}
	
	private void doBuildingAsync(final TreeItem parent, final TreeElement[] children, final ThreadCounter threadCounter, final Display currentDisplay) {
		threadCounter.inc();
		currentDisplay.asyncExec(new Runnable() {
			@Override
			public void run() {
				doBuildingAsyncRec(parent, children, threadCounter, currentDisplay);
			}
		});
	}
	
}
