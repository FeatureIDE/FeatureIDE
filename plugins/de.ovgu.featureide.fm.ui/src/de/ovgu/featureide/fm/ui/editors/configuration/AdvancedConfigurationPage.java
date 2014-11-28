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

import org.eclipse.jface.viewers.ColumnViewerToolTipSupport;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Displays the tree for advanced configuration selection at the configuration editor.
 * 
 * @author Jens MeOinicke
 * @author Hannes Smurawsky
 */
public class AdvancedConfigurationPage extends ConfigurationTreeEditorPage {
	
	private static final String PAGE_TEXT = "Advanced Configuration";
	private static final String ID = FMUIPlugin.PLUGIN_ID + "AdvancedConfigurationPage";
	
	private final ConfigurationTreeWalker treeWalker = new ConfigurationTreeWalker() {
		@Override
		public boolean visitTreeItem(TreeItem item, SelectableFeature feature) {
			item.setBackground(null);
			if (feature.getAutomatic() != Selection.UNDEFINED) {
				item.setFont(treeItemStandardFont);
				if (feature.getAutomatic() == Selection.SELECTED) {
					item.setGrayed(true);
					item.setForeground(null);
				} else {
					item.setGrayed(false);
					item.setForeground(gray);
				}
			} else {
				boolean selected = feature.getManual() == Selection.SELECTED;
				item.setGrayed(false);
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
	
	private TreeViewer viewer;
	
	protected void createUITree(Composite parent) {	    
		viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		viewer.getTree().addMouseListener(new MouseListener() {
			@Override
			public void mouseUp(MouseEvent e) {
				if (e.button == 1 || e.button == 3) {
					TreeItem item = viewer.getTree().getItem(new Point(e.x, e.y));
					if (item != null) {
						Object data = item.getData();
						if (data instanceof SelectableFeature) {
							changeSelection(item, e.button == 1);
						}
					}
				}
			}
			@Override
			public void mouseDown(MouseEvent e) {}
			@Override
			public void mouseDoubleClick(MouseEvent e) {}
		});
		viewer.getTree().addKeyListener(new KeyListener() {
			public void keyPressed(KeyEvent e) {
				if (e.character == ' ') {
					if (viewer.getSelection() instanceof ITreeSelection) {
						final ITreeSelection tree = (ITreeSelection) viewer
								.getSelection();
						Object object = tree.getFirstElement();
						if (object instanceof SelectableFeature) {
							final SelectableFeature feature = (SelectableFeature) object;
							cycleSelection(feature, true);
						}
					}
				}
			}
			
			public void keyReleased(KeyEvent e) {
			}
		});
		
		viewer.setContentProvider(new ConfigurationContentProvider());
		viewer.setLabelProvider(new AdvancedConfigurationLabelProvider());
		viewer.setInput(null);
		viewer.expandAll();
		ColumnViewerToolTipSupport.enableFor(viewer);
	}

	@Override
	public void setFocus() {
		viewer.getControl().setFocus();
	}
	
	@Override
	protected void updateTree() {
		viewer.getTree().setRedraw(false);
		viewer.setContentProvider(new ConfigurationContentProvider());
		viewer.setLabelProvider(new AdvancedConfigurationLabelProvider());
		viewer.setInput(configurationEditor.getConfiguration());
		viewer.expandAll();
		if (errorMessage(viewer.getTree())) {
			refreshTree();
		}
		viewer.getTree().setRedraw(true);
	}
	
	@Override
	protected void refreshTree() {
		super.refreshTree();
		viewer.refresh();
	}
	
	@Override
	protected void refreshItem(TreeItem item, SelectableFeature feature) {
		super.refreshItem(item, feature);
		viewer.update(feature, null);
	}
	
	@Override
	protected TreeItem getRoot() {
		return viewer.getTree().getItem(0);
	}
	
	@Override
	protected ConfigurationTreeWalker getDefaultTreeWalker() {
		return treeWalker;
	}
	
	@Override
	protected boolean canDeselectFeatures() {
		return true;
	}
	
	private void cycleSelection(SelectableFeature feature, boolean up) {
		if (feature.getAutomatic() == Selection.UNDEFINED) {
			switch (feature.getManual()) {
			case SELECTED: set(feature, (up) ? Selection.UNSELECTED : Selection.UNDEFINED);  break;
			case UNSELECTED: set(feature, (up) ? Selection.UNDEFINED : Selection.SELECTED);  break;
			case UNDEFINED: set(feature, (up) ? Selection.SELECTED : Selection.UNSELECTED); break;
			default: set(feature, Selection.UNDEFINED);
			}
			if (!dirty) {
				setDirty();
			}
			refreshTree();
		}
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