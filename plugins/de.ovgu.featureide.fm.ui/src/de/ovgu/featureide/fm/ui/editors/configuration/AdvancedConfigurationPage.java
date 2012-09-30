/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.configuration;


import java.beans.PropertyChangeEvent;
import java.util.LinkedList;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Displays the tree for advanced configuration selection at the configuration editor.
 * 
 * @author Jens Meinicke
 * @author Hannes Smurawsky
 */
//TODO #458 remove duplicate code configurationPage/AdvancedConfigurationPage

public class AdvancedConfigurationPage extends ConfigurationEditorPage {
	
	private static final String PAGE_TEXT = "Advanced Configuration";

	private static final String ID = FMUIPlugin.PLUGIN_ID + "AdvancedConfigurationPage";

	private TreeViewer viewer;
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#getPageText()
	 */
	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	public void updateTree() {
		viewer.refresh();
		if (!errorMessage())
			updateForeground(viewer.getTree().getItem(0));
		removeHiddenFeatures();
	}
	
	private IDoubleClickListener listener = new IDoubleClickListener() {
		public void doubleClick(DoubleClickEvent event) {
			Object object = ((ITreeSelection) event.getSelection())
					.getFirstElement();
			if (object instanceof SelectableFeature) {
				final SelectableFeature feature = (SelectableFeature) object;
				changeSelection(feature);
			}
		}
	};

	@Override
	public void createPartControl(Composite parent) {
		viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		viewer.addDoubleClickListener(listener);
		viewer.getTree().addKeyListener(new KeyListener() {

			public void keyPressed(KeyEvent e) {
				if (e.character == ' ') {
					if (viewer.getSelection() instanceof ITreeSelection) {
						final ITreeSelection tree = (ITreeSelection) viewer
								.getSelection();
						Object object = tree.getFirstElement();
						if (object instanceof SelectableFeature) {
							final SelectableFeature feature = (SelectableFeature) object;
							changeSelection(feature);
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
	}

	@Override
	public void setFocus() {
		viewer.getControl().setFocus();
	}
	private boolean initialized = false;

	private LinkedList<String> hiddenFeatures;
	
	@Override
	public void propertyChange(PropertyChangeEvent evt) {
		if (initialized)
			dirty = true;
		else
			initialized = true;
		UIJob job = new UIJob("refresh tree") {
			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				refreshTree();
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.SHORT);
		job.schedule();
	}

	private void refreshTree() {
		viewer.getTree().setRedraw(false);
		viewer.setContentProvider(new ConfigurationContentProvider());
		viewer.setLabelProvider(new AdvancedConfigurationLabelProvider());
		viewer.setInput(configurationEditor.configuration);
		viewer.expandAll();
		viewer.refresh();
		if (!errorMessage())
			updateForeground(viewer.getTree().getItem(0));
		removeHiddenFeatures();
		viewer.getTree().setRedraw(true);
	}

	private void removeHiddenFeatures() {
		hiddenFeatures = new LinkedList<String>();
		for (Feature feature : configurationEditor.configuration.getFeatureModel().getFeatures()) {
			if (feature.isHidden())
				hiddenFeatures.add(feature.getName());
		}
		for (TreeElement feature : configurationEditor.configuration.getRoot().getChildren())
			removeHiddenElement(feature);
	}
	
	private void removeHiddenElement(TreeElement element) {
		if (hiddenFeatures.contains(element.toString())) {
			for (TreeElement feature : element.getChildren())
				remove(feature);
			viewer.remove(element);
		} else {
			for (TreeElement feature : element.getChildren())
				removeHiddenElement(feature);
		}	
	}

	private boolean errorMessage() { 
		if (!configurationEditor.configuration.valid() && configurationEditor.configuration.number() == 0){
			for (TreeElement feature : configurationEditor.configuration.getRoot().getChildren()) {
					remove(feature);
			}
			viewer.getTree().getItem(0).setText("The feature model for " +
					"this project is void, i.e., there is no valid configuration. " +
					"You need to correct the feature model before you can create " +
					"or edit configurations.");
			viewer.getTree().getItem(0).setImage(0,FMUIPlugin.getDefault()
				.getWorkbench().getSharedImages().getImage
				(ISharedImages.IMG_OBJS_ERROR_TSK));
			dirty = false;
			return true;
		}
		return false;
	}
	
	private void remove(TreeElement element) {
		for (TreeElement feature : element.getChildren())
			remove(feature);
		viewer.remove(element);
	}
	
	protected void changeSelection(SelectableFeature feature) {
		viewer.getTree().setRedraw(false);
		if (feature.getAutomatic() == Selection.UNDEFINED) {
			// set to the next value
			if (feature.getManual() == Selection.UNDEFINED)
				set(feature, Selection.SELECTED);
			else if (feature.getManual() == Selection.SELECTED)
				set(feature, Selection.UNSELECTED);
			else
				// case: unselected
				set(feature, Selection.UNDEFINED);
			if (!dirty) {
				dirty = true;
				firePropertyChange(IEditorPart.PROP_DIRTY);
			}
			viewer.refresh();
			removeHiddenFeatures();
		
		}
		viewer.getTree().setRedraw(true);
		}
	
	protected void set(SelectableFeature feature, Selection selection) {
		configurationEditor.configuration.setManual(feature, selection);
		updateForeground(viewer.getTree().getItem(0));
	}
	
	private void updateForeground(
			TreeItem item) {	
		// TODO #458 implement coloring
//		for (TreeItem child : item.getItems()) {
//			SelectableFeature feature = configurationEditor.configuration.getSelectablefeature(child.getText());
//			child.setForeground(null);
//			child.setFont(treeItemStandardFont);
//			if (feature != null) {
//				if (!configurationEditor.configuration.valid())
//					if (feature.getAutomatic() == Selection.UNDEFINED) {
//						if (feature.getManual() == Selection.UNDEFINED) {
//							if (configurationEditor.configuration.leadToValidConfiguration(feature, Selection.SELECTED, Selection.UNDEFINED)){
//								child.setForeground(green);
//								child.setFont(treeItemSpecialFont);	
//							}
//						} else if (feature.getManual() == Selection.SELECTED) {
//							if (configurationEditor.configuration.leadToValidConfiguration(feature, Selection.UNSELECTED, Selection.SELECTED)){
//								child.setForeground(blue);
//								child.setFont(treeItemSpecialFont);
//							}
//							// case: unselected
//						} else if (configurationEditor.configuration.leadToValidConfiguration(feature, Selection.SELECTED, Selection.UNSELECTED)){
//								child.setForeground(green);
//								child.setFont(treeItemSpecialFont);	
//						}
//					}
//				updateForeground(child);
//			}
//		}
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#getID()
	 */
	@Override
	public String getID() {
		return ID;
	}
}