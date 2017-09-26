/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;

import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IBinaryFunction;

/**
 * Builds and traverses a {@link Tree} recursively with single asynchronous UI calls for each item.
 *
 * @author Marcus Pinnecke
 * @author Sebastian Krieter
 */
public class AsyncTree extends Thread {

	private class Builder implements Runnable {

		private final TreeItem parent;
		private final TreeElement[] children;

		public Builder(TreeItem parent, TreeElement[] children) {
			inc();
			this.parent = parent;
			this.children = children;
		}

		@Override
		public void run() {
			for (int i = 0; i < children.length; i++) {
				final TreeElement child = children[i];
				if (child instanceof SelectableFeature) {
					final SelectableFeature currentFeature = (SelectableFeature) child;
					if (!currentFeature.getFeature().getStructure().isHidden()) {
						TreeItem childNode = null;
						// This try for the case that the parent item is already disposed.
						try {
							childNode = new TreeItem(parent, 0);
						} catch (final Exception e) {
							interrupt();
							return;
						}
						childNode.setText(currentFeature.getFeature().getProperty().getDisplayName());
						childNode.setData(currentFeature);

						childNode.setFont(ConfigurationTreeEditorPage.treeItemStandardFont);
						childNode.setForeground(null);

						itemMap.put(currentFeature, childNode);
						if (currentFeature.hasChildren()) {
							runnableList.add(new Builder(childNode, currentFeature.getChildren()));
						}
					}
				}
			}
			try {
				parent.setExpanded(true);
			} catch (final Exception e) {
				interrupt();
				return;
			}
			dec();
		}

	}

	private class Traverser implements Runnable {

		private final TreeItem item;
		private final IBinaryFunction<TreeItem, SelectableFeature, Void> perNodeFunction;

		public Traverser(TreeItem item, IBinaryFunction<TreeItem, SelectableFeature, Void> perNodeFunction) {
			inc();
			this.item = item;
			this.perNodeFunction = perNodeFunction;
		}

		@Override
		public void run() {
			perNodeFunction.invoke(item, (SelectableFeature) item.getData());
			final TreeItem[] children = item.getItems();
			for (int i = 0; i < children.length; i++) {
				final TreeItem childNode = children[i];
				runnableList.add(new Traverser(childNode, perNodeFunction));
			}
			dec();
		}

	}

	private final Display currentDisplay;
	private final BlockingQueue<Runnable> runnableList = new LinkedBlockingQueue<>();

	private final HashMap<SelectableFeature, TreeItem> itemMap;

	private final Functional.IFunction<Void, Void> callbackIfDone;
	private final Object countLock = new Object();
	private Integer count = 0;

	public void inc() {
		synchronized (countLock) {
			++count;
		}
	}

	public void dec() {
		boolean done;
		synchronized (countLock) {
			done = --count == 0;
		}
		if (done) {
			interrupt();
			callbackIfDone.invoke(null);
		}
	}

	@Override
	public void run() {
		try {
			while (true) {
				currentDisplay.syncExec(runnableList.take());
			}
		} catch (final InterruptedException e) {}
	}

	private AsyncTree(HashMap<SelectableFeature, TreeItem> itemMap, final Functional.IFunction<Void, Void> callbackIfDone) {
		this.itemMap = itemMap;
		currentDisplay = Display.getCurrent();
		this.callbackIfDone = callbackIfDone;
	}

	public static void build(HashMap<SelectableFeature, TreeItem> itemMap, final TreeItem node, final TreeElement[] children,
			final Functional.IFunction<Void, Void> callbackIfDone) {
		final AsyncTree curInstance = new AsyncTree(itemMap, callbackIfDone);
		if ((curInstance.currentDisplay != null) && !node.isDisposed()) {
			curInstance.runnableList.add(curInstance.new Builder(node, children));
			curInstance.start();
		}
	}

	public static void traverse(HashMap<SelectableFeature, TreeItem> itemMap, final TreeItem node,
			final Functional.IBinaryFunction<TreeItem, SelectableFeature, Void> perNodeFunction, final Functional.IFunction<Void, Void> callbackIfDone) {
		final AsyncTree curInstance = new AsyncTree(itemMap, callbackIfDone);
		if ((curInstance.currentDisplay != null) && !node.isDisposed()) {
			curInstance.runnableList.add(curInstance.new Traverser(node, perNodeFunction));
			curInstance.start();
		}
	}

}
