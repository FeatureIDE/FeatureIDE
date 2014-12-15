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

import java.util.HashSet;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.fm.core.FunctionalInterfaces;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.configuration.xxx.AsyncTree;

/**
 * Displays the tree for common configuration selection at the configuration
 * editor
 * 
 * @author Jens Meinicke
 * @author Hannes Smurawsky
 * @author Marcus Pinnecke
 */
public class ConfigurationPage extends ConfigurationTreeEditorPage {

	private static final String ID = FMUIPlugin.PLUGIN_ID + "ConfigurationPage";

	private static final String PAGE_TEXT = "Configuration";

	private final FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void> treeWalker = new FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void>() {
		@Override
		public Void invoke(TreeItem item, SelectableFeature feature) {
			item.setBackground(null);
			if (feature.getAutomatic() != Selection.UNDEFINED) {
				item.setFont(treeItemStandardFont);
				if (feature.getAutomatic() == Selection.SELECTED) {
					item.setGrayed(true);
					item.setForeground(null);
					item.setChecked(true);
				} else {
					item.setGrayed(true);
					item.setForeground(gray);
					item.setChecked(false);
				}
			} else {
				boolean selected = feature.getManual() == Selection.SELECTED;
				item.setGrayed(false);
				item.setChecked(selected);
			}
			return null;
		}
	};

	private Tree tree;

	public interface Methode {
		public void invoke();
	}

	private void buildTree(final TreeItem node, final TreeElement[] children, final FunctionalInterfaces.IFunction<Void, Void> callbackIfDone) {
		getAsyncTree().build(node, children, callbackIfDone);
	}

	protected void createUITree(Composite parent) {
		tree = new Tree(parent, SWT.CHECK);
		tree.addSelectionListener(new SelectionListener() {
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
			}

			@Override
			public void widgetSelected(SelectionEvent event) {
				if (event.detail == SWT.CHECK) {
					final TreeItem item = (TreeItem) event.item;
					SelectableFeature feature = (SelectableFeature)item.getData();
					switch (feature.getAutomatic()) {
						case SELECTED: item.setChecked(true); break;
						case UNSELECTED: item.setChecked(false); break;
						case UNDEFINED: changeSelection(item, true); break;
					}
				}
			}
		});
	}

	@Override
	protected FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void> getDefaultTreeWalker() {
		return treeWalker;
	}

	@Override
	public String getID() {
		return ID;
	}

	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	@Override
	protected TreeItem getRoot() {
		return tree.getItem(0);
	}

	@Override
	public void pageChangeTo(int index) {
		final Configuration configuration = configurationEditor.getConfiguration();
		final boolean oldPropagate = configuration.isPropagate();
		configuration.setPropagate(false);

		final HashSet<SelectableFeature> selectedFeatures = new HashSet<SelectableFeature>();
		for (SelectableFeature feature : configuration.getFeatures()) {
			if (feature.getAutomatic() == Selection.SELECTED) {
				selectedFeatures.add(feature);
			} else if (feature.getAutomatic() == Selection.UNDEFINED && feature.getManual() == Selection.UNSELECTED) {
				configuration.setManual(feature, Selection.UNDEFINED);
			}
		}

		configuration.setPropagate(oldPropagate);
		configuration.update();
		configuration.setPropagate(false);

		// reselect implied features
		for (SelectableFeature feature : configuration.getFeatures()) {
			if (feature.getAutomatic() == Selection.UNDEFINED && selectedFeatures.contains(feature)) {
				configuration.setManual(feature, Selection.SELECTED);
			}
		}

		configuration.setPropagate(oldPropagate);
		configuration.update();
		super.pageChangeTo(index);
	}

	@Override
	protected void updateTree() {
		itemMap.clear();
		if (errorMessage(tree)) {
			final Configuration configuration = configurationEditor.getConfiguration();
			tree.removeAll();
			final TreeItem root = new TreeItem(tree, 0);
			root.setText(configuration.getRoot().getName());
			root.setData(configuration.getRoot());
			root.setChecked(true);
			root.setGrayed(true);
			itemMap.put(configuration.getRoot(), root);

			buildTree(root, configuration.getRoot().getChildren(), new FunctionalInterfaces.IFunction<Void, Void>() {
				@Override
				public Void invoke(Void t) {
					updateInfoLabel();
					computeTree(false);
					return null;
				}
			});
		}
	}

	@Override
	protected AsyncTree getAsyncTree() {
		return new AsyncTree(tree, itemMap);
	}

	@Override
	protected Tree getTree() {
		return tree;
	}
}
