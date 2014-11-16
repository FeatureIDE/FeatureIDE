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

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Displays the tree for common configuration selection at the configuration
 * editor
 * 
 * @author Jens Meinicke
 * @author Hannes Smurawsky
 */
public class ConfigurationPage extends ConfigurationEditorPage {
	
	private static final String PAGE_TEXT = "Configuration";
	private static final String ID = FMUIPlugin.PLUGIN_ID + "ConfigurationPage";
	
	private final ConfigurationTreeWalker treeWalker = new ConfigurationTreeWalker() {
		@Override
		public boolean visitTreeItem(TreeItem item, SelectableFeature feature) {
			item.setBackground(null);
			if (feature.getAutomatic() != Selection.UNDEFINED) {
				item.setFont(treeItemStandardFont);
				if (feature.getAutomatic() == Selection.SELECTED) {
					item.setGrayed(true);
					item.setForeground(null);
					item.setChecked(true);
				} else {
					item.setGrayed(false);
					item.setForeground(gray);
					item.setChecked(false);
				}
			} else {
				boolean selected = feature.getManual() == Selection.SELECTED;
				item.setGrayed(false);
				item.setChecked(selected);
				if (colorFeatureNames.contains(feature.getName())) {
					item.setForeground(selected ? blue : green);
					item.setFont(treeItemSpecialFont);
				} else {
					item.setForeground(null);
					item.setFont(treeItemStandardFont);
				}
			}
			return true;
		}
	};

	private Tree tree;
	
	private boolean selectionCanChange = true;

	@Override
	public void createPartControl(Composite parent) {
		tree = new Tree(parent, SWT.BORDER | SWT.CHECK);
		tree.addSelectionListener(new SelectionListener() {
			@Override
			public void widgetSelected(SelectionEvent event) {
				if (event.detail == SWT.CHECK) {
					final TreeItem item = (TreeItem) event.item;
					if (item.getGrayed()) {
						// case: grayed and selected
						item.setChecked(true);
					} else if (item.getForeground().equals(gray)) {
						// case: grayed and unselected
						item.setChecked(false);
					} else if (selectionCanChange) {
						changeSelection((SelectableFeature)item.getData());
					}
				}
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});
	}

	@Override
	protected void updateTree() {
		if (errorMessage(tree)) {
			final Configuration configuration = configurationEditor.getConfiguration();
			tree.removeAll();
			TreeItem root = new TreeItem(tree, 0);
			root.setData(configuration.getRoot().getName());
			add(root, configuration.getRoot().getChildren());
			root.setGrayed(true);
			root.setExpanded(true);
			root.setChecked(true);
			
			refreshTree();
		}
	}
	
	private void add(TreeItem parent, TreeElement[] children) {
		for (TreeElement child : children) {
			if (child instanceof SelectableFeature) {
				final SelectableFeature currentFeature = (SelectableFeature) child;
				if (!currentFeature.getFeature().isHidden()) {
					TreeItem item = new TreeItem(parent, 0);
					item.setText(currentFeature.getFeature().getDisplayName());
					item.setData(currentFeature);
					add(item, currentFeature.getChildren());
					item.setExpanded(true);
				}
			}
		}
	}
	
	@Override
	protected void refreshTree() {
		TreeItem root = tree.getItem(0);
		root.setText(AdvancedConfigurationLabelProvider.getRootlabel(configurationEditor.getConfiguration()));
		refreshItems();
	}	
	
	@Override
	protected TreeItem getRoot() {
		return tree.getItem(0);
	}
	
	@Override
	protected ConfigurationTreeWalker getDefaultTreeWalker() {
		return treeWalker;
	}
	
	@Override
	protected boolean changeSelection(SelectableFeature feature, boolean select) {
		selectionCanChange = false;
		final boolean result = super.changeSelection(feature, select);
		selectionCanChange = true;
		return result;
	}

	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	@Override
	public String getID() {
		return ID;
	}
}
