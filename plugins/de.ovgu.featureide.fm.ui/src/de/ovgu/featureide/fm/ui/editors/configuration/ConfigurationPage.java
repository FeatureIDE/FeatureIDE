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
import java.util.HashMap;
import java.util.LinkedList;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Displays the tree for common configuration selection at the configuration editor
 * 
 * @author Jens Meinicke
 * @author Hannes Smurawsky
 */
public class ConfigurationPage extends ConfigurationEditorPage {
	private static final String PAGE_TEXT = "Configuration";
	private static final String ID = FMUIPlugin.PLUGIN_ID + "ConfigurationPage";
	
	private Tree tree;
	
	private Color gray = new Color(null,140,140,140);
	private Color green = new Color(null,0,140,0);
	private Color blue = new Color(null,0,0,200);
	
	private Font treeItemStandardFont = new Font(null, "Arial", 8, SWT.NORMAL);
	private Font treeItemSpecialFont = new Font(null,"Arial", 8, SWT.BOLD);

	/**
	 * Contains the TreeItems for coloring.
	 */
	private HashMap<SelectableFeature, TreeItem> items = new HashMap<SelectableFeature, TreeItem>();	
	/**
	 * Contains the features to be checked at coloring thread.
	 */
	private LinkedList<SelectableFeature> features = new LinkedList<SelectableFeature>();
	/**
	 * Stops the coloring thread if true.
	 */
	private boolean returnFormThread = false;
	private Job job_color;
	public void cancelColorJob() {
		returnFormThread = true;
	}
	
	private boolean selectionChanged = true;
	
	private boolean initialized = false;
	
	private LinkedList<String> hiddenFeatures;
	
	public void updateTree(){
		if (errorMessage())
			refreshTree();
	}

	@Override
	public void createPartControl(Composite parent) {		
		tree = new Tree(parent, SWT.BORDER | SWT.CHECK);
		tree.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent event) {
				if (event.detail == SWT.CHECK) {
					if ((((TreeItem)event.item).getText()).startsWith(configurationEditor.configuration.getRoot().getName())) {
						// case: root
						((TreeItem)event.item).setChecked(true);
						//((TreeItem)event.item).setGrayed(true);
					} else if (((TreeItem)event.item).getGrayed()) {
						// case: grayed and selected
						((TreeItem)event.item).setChecked(true);
					} else if (((TreeItem)event.item).getForeground().equals(gray)) {
						// case: grayed and unselected
						((TreeItem)event.item).setChecked(false);
					} else {
						// case: selectable
						if (!selectionChanged) {
							// do nothing if selection changed to fast
							if (((TreeItem)event.item).getChecked()) {
								((TreeItem)event.item).setChecked(true);
							} else {
								((TreeItem)event.item).setChecked(false);
							}
						} else {
							changeSelection(configurationEditor.configuration.getSelectablefeature(
								((TreeItem)event.item).getText()));		
							refreshTree();
						}
					}
				}
			}
			
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});
	}

	@Override
	public void propertyChange(PropertyChangeEvent evt) {
		if (initialized)
			dirty = true;
		else
			initialized = true;
		UIJob job = new UIJob("refresh tree") {
			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				if (errorMessage()) {
					setInput(configurationEditor.configuration);			
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.SHORT);
		job.schedule();
	}

	private void refreshTree() {
		hiddenFeatures = new LinkedList<String>();
		for (Feature feature : configurationEditor.configuration.getFeatureModel().getFeatures()) {
			if (feature.isHidden())
				hiddenFeatures.add(feature.getName());
		}
		TreeItem root = tree.getItem(0);
		root.setText(AdvancedConfigurationLabelProvider.getRootlabel(configurationEditor.configuration));
		setCheckbox(root);
	}

	private void setCheckbox(TreeItem root) {
		resetColor();
		setCheckbox(root, configurationEditor.configuration.valid());
		selectionChanged = true;
		setColor();
	}
	
	/**
	 * Stops the coloring job.
	 */
	public void resetColor() {
		returnFormThread = true;
		try {
			if (job_color != null) {
				job_color.join();
			}
		} catch (InterruptedException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		items = new HashMap<SelectableFeature, TreeItem>();
		features = new LinkedList<SelectableFeature>();
	}
	
	private void setCheckbox(TreeItem item, boolean configuration_valid){
		for (TreeItem child : item.getItems()) {
			child.setGrayed(false);
			child.setForeground(null);
			child.setBackground(null);
			child.setFont(treeItemStandardFont);
			SelectableFeature feature = configurationEditor.configuration.getSelectablefeature(child.getText());
			if (feature.getAutomatic() != Selection.UNDEFINED) {
				if (feature.getAutomatic() == Selection.SELECTED){
					child.setChecked(true);
					child.setGrayed(true);
				} else {
					child.setChecked(false);
					child.setForeground(gray);
				}
			} else if (feature.getManual() == Selection.UNDEFINED || 
					feature.getManual() == Selection.UNSELECTED){
				child.setChecked(false);
				if(!configuration_valid) {
					features.add(feature);
					items.put(feature, child);
				}
			} else if (feature.getManual() == Selection.SELECTED) {
				child.setChecked(true);
				if(!configuration_valid) {
					features.add(feature);
					items.put(feature, child);
				}
			}
			setCheckbox(child, configuration_valid);
		} 
	}
	
	/**
	 * Colors all features if they lead to a valid configuration 
	 * if current configuration is invalid. 
	 * deselect:blue, select:green 
	 */
	private void setColor() {
		returnFormThread = false;
		job_color = new Job("Feature coloring.(" + configurationEditor.file.getName() + ")") {
			public IStatus run(IProgressMonitor monitor) {
				if (features != null && features.size() != 0 && !features.isEmpty()) {
					monitor.beginTask("", features.size());
					for (SelectableFeature feature : features) {
						monitor.subTask("Check feature " + feature.getName());
						if (returnFormThread || monitor.isCanceled()) {
							monitor.done();
							return Status.OK_STATUS;
						}
						if (feature.getManual() == Selection.SELECTED) {
							if (configurationEditor.configuration.leadToValidConfiguration(feature, Selection.UNDEFINED, Selection.SELECTED )) {
								if (!returnFormThread) {
									setColor(items.get(feature), blue);
								}
							}
						} else {
							if (configurationEditor.configuration.leadToValidConfiguration(feature, Selection.SELECTED, Selection.UNDEFINED)) {
								if (!returnFormThread) {
									setColor(items.get(feature), green);
								}
							}
						}
						monitor.worked(1);
					}
				}
				monitor.done();
				return Status.OK_STATUS;
			}
		};
		job_color.setPriority(Job.DECORATE);
		job_color.schedule();
	}

	protected void setColor(final TreeItem item, final Color color) {
		UIJob job_setColor = new UIJob("") {
			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				item.setForeground(color);
				item.setFont(treeItemSpecialFont);
				return Status.OK_STATUS;
			}
		};
		job_setColor.setPriority(Job.SHORT);
		job_setColor.schedule();
	}

	private void setInput(Configuration configuration){
		hiddenFeatures = new LinkedList<String>();
		for (Feature feature : configuration.getFeatureModel().getFeatures()) {
			if (feature.isHidden())
				hiddenFeatures.add(feature.getName());
		}
		tree.removeAll();
		TreeItem item = new TreeItem(tree, 0);
		item.setText(AdvancedConfigurationLabelProvider.getRootlabel(configuration));
		add(item,configuration.getRoot().getChildren());
		setCheckbox(item);
		item.setGrayed(true);
		item.setExpanded(true);
		item.setChecked(true);
	}
	
	private void add(TreeItem parent,TreeElement[] children){
		for (TreeElement child : children){
			String childName = child.toString();
			if (!hiddenFeatures.contains(childName)) {
				TreeItem item = new TreeItem(parent,0);
				item.setText(childName);
				add(item,child.getChildren());
				item.setExpanded(true);
			}
		}
	}
	
	private boolean errorMessage() {

		if (configurationEditor.configuration==null||(!configurationEditor.configuration.valid() && configurationEditor.configuration.number() == 0)){
			tree.removeAll();
			TreeItem item = new TreeItem(tree, 1);
			if (configurationEditor.modelFile ==  null) {
				item.setText("There is no feature model corresponding to this configuration, reopen the editor and select one.");
			} else if (!configurationEditor.modelFile.exists()) {
				// This case should never happen
				item.setText("The given feature model " + configurationEditor.modelFile.getPath() + " does not exist.");
			} else {
				item.setText("The feature model for this project is void, i.e., " +
						"there is no valid configuration. You need to correct the " +
						"feature model before you can create or edit configurations.");
			}
			item.setImage(FMUIPlugin.getDefault()
					.getWorkbench().getSharedImages().getImage
					(ISharedImages.IMG_OBJS_ERROR_TSK));
			item.setChecked(true);
			item.setGrayed(true);
				dirty = false;
				return false;
		}
		return true;
	}
	
	protected void changeSelection(SelectableFeature feature) {
		selectionChanged = false;
		resetColor();
		if (feature.getAutomatic() == Selection.UNDEFINED) {
			// set to the next value
			if (feature.getManual() == Selection.UNDEFINED ||
					feature.getManual() == Selection.UNSELECTED)
				set(feature, Selection.SELECTED);
			else // case: selected
				set(feature, Selection.UNDEFINED);
			
			if (!dirty) {
				dirty = true;
				firePropertyChange(IEditorPart.PROP_DIRTY);
			}
		}
	}

	protected void set(SelectableFeature feature, Selection selection) {
		configurationEditor.configuration.setManual(feature, selection);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#getPageText()
	 */
	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#getID()
	 */
	@Override
	public String getID() {
		return ID;
	}

}
