/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.ahead.editors;

import java.beans.PropertyChangeEvent;
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
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Displays the tree for common configuration selection at the configurationeditor
 * 
 * @author Jens Meinicke
 * @author Hannes Smurawsky
 */
public class ConfigurationPage extends EditorPart {
	private ConfigurationEditor configurationEditor;
	
	private boolean dirty = false;
	
	private Tree tree;
	
	private LinkedList<String> selectedFeatures;
	
	private Color gray = new Color(null,140,140,140);
	private Color green = new Color(null,1,140,2);
	private Color blue = new Color(null,0,0,200);
	
	private Font treeItemStandardFont = new Font(null, "Arial", 8, SWT.NORMAL);
	private Font treeItemSpecialFont = new Font(null,"Arial", 8, SWT.BOLD);

	public void updateTree(){
		if (errorMassage())
			refreshTree();
	}
	
	public void setConfigurationEditor(ConfigurationEditor configurationEditor){
		this.configurationEditor = configurationEditor;
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		dirty = false;
		firePropertyChange(IEditorPart.PROP_DIRTY);
	}

	@Override
	public void doSaveAs() {
	}

	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		setSite(site);
		setInput(input);
	}
	
	@Override
	public boolean isDirty() {
		return dirty;
	}

	@Override
	public boolean isSaveAsAllowed() {
		return false;
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
						//((TreeItem)event.item).setGrayed(true);
					} else if (((TreeItem)event.item).getForeground().equals(gray)) {
						// case: grayed and unselected
						((TreeItem)event.item).setChecked(false);
					} else {
						// case: selectable
						changeSelection(configurationEditor.configuration.getSelectablefeature(
							((TreeItem)event.item).getText()));		
						refreshTree();
					}
				}
			}
			
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});
	}

	@Override
	public void setFocus() {
	}
	
	private boolean initialized = false;
	
	public void propertyChange(PropertyChangeEvent evt) {
		if (initialized)
			dirty = true;
		else
			initialized = true;
		UIJob job = new UIJob("refresh tree") {
			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				if (errorMassage())
					setInput(configurationEditor.configuration);
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.SHORT);
		job.schedule();
	}

	private void refreshTree() {
		selectedFeatures = new LinkedList<String>();
		for (Feature feature : configurationEditor.configuration.getSelectedFeatures())
			selectedFeatures.add(feature.getName());
		TreeItem root = tree.getItem(0);
		root.setText(getRootlabel());
		setCheckbox(root);
	}
	
	private void setCheckbox(TreeItem item){
		for (TreeItem child : item.getItems()) {
			child.setGrayed(false);
			child.setForeground(null);
			child.setBackground(null);
			child.setFont(treeItemStandardFont);
			SelectableFeature feature = configurationEditor.configuration.getSelectablefeature(child.getText());
			if (feature.getAutomatic() != Selection.UNDEFINED)
				if (feature.getAutomatic() == Selection.SELECTED){
					child.setChecked(true);
					child.setGrayed(true);
				} else {
					child.setChecked(false);
					child.setForeground(gray);
				}
			
			else if (feature.getManual() == Selection.UNDEFINED || 
					feature.getManual() == Selection.UNSELECTED){
				child.setChecked(false);
				if(!configurationEditor.configuration.valid())
					if (configurationEditor.configuration.leadToValidConfiguration(feature, Selection.SELECTED, Selection.UNDEFINED)) {
						child.setForeground(green);
						child.setFont(treeItemSpecialFont);
					}
			} else if (feature.getManual() == Selection.SELECTED) {
				child.setChecked(true);
				if(!configurationEditor.configuration.valid())
					if (configurationEditor.configuration.leadToValidConfiguration(feature, Selection.UNDEFINED, Selection.SELECTED )){
						child.setForeground(blue);
						child.setFont(treeItemSpecialFont);
					}
				}
			setCheckbox(child);
		}
	}
	
	private String getRootlabel(){
		String s = configurationEditor.configuration.valid() ? "valid" : "invalid";
		s += ", ";
		long number = configurationEditor.configuration.number();
		if (number < 0)
			s += "more than " + (-1 - number) + " solutions";
		else
			s += number + " solutions";
		return configurationEditor.configuration.getRoot().getName() + " (" + s + ")";
	}
	
	private void setInput(Configuration configuration){
		selectedFeatures = new LinkedList<String>();
		for (Feature feature : configuration.getSelectedFeatures())
			selectedFeatures.add(feature.getName());
		tree.removeAll();
		TreeItem item = new TreeItem(tree, 0);
		item.setText(getRootlabel());
		add(item,configuration.getRoot().getChildren());
		setCheckbox(item);
		item.setGrayed(true);
		item.setExpanded(true);
		item.setChecked(true);
	}
	
	private void add(TreeItem parent,TreeElement[] children){
		for (TreeElement child : children){
			TreeItem item = new TreeItem(parent,0);
			item.setText(child.toString());
			add(item,child.getChildren());
			item.setExpanded(true);
		}
	}
	
	private boolean errorMassage() {
		if (!configurationEditor.configuration.valid() && configurationEditor.configuration.number() == 0){
			tree.removeAll();
			TreeItem item = new TreeItem(tree, 1);
			item.setText("The feature model for this project is void, i.e., " +
					"there is no valid configuration. You need to correct the " +
					"feature model before you can create or edit configurations.");
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

}
