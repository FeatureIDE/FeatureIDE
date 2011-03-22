/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.editors;


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
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.configuration.AdvancedConfigurationLabelProvider;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationContentProvider;

/**
 * Displays the tree for advanced configuration selection at the configurationeditor
 * 
 * @author Jens Meinicke
 * @author Hannes Smurawsky
 */
public class AdvancedConfigurationPage extends EditorPart {
	
	private ConfigurationEditor configurationEditor;
	
	private Color green = new Color(null,0,140,0);
	private Color blue = new Color(null,0,1,140);
	
	private Font treeItemStandardFont = new Font(null, "Arial", 8, SWT.NORMAL);
	private Font treeItemSpecialFont = new Font(null,"Arial", 8, SWT.BOLD);
	
	private TreeViewer viewer;

	private boolean dirty = false;

	public void updateTree() {
		removeHiddenFeatures();
		viewer.refresh();
	
		if (!errorMassage())
			updateForeground(viewer.getTree().getItem(0));
		
	}
	
	public void setConfigurationEditor(ConfigurationEditor configurationEditor) {
		this.configurationEditor = configurationEditor;
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
		viewer.setContentProvider(new ConfigurationContentProvider());
		viewer.setLabelProvider(new AdvancedConfigurationLabelProvider());
		viewer.setInput(configurationEditor.configuration);
		
		viewer.expandAll();
		removeHiddenFeatures();
		viewer.refresh();
		if (!errorMassage())
			updateForeground(viewer.getTree().getItem(0));
	
	}

	/**
	 * 
	 */
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
	
	
	private boolean errorMassage() { 
		if (!configurationEditor.configuration.valid() && configurationEditor.configuration.number() == 0){
			for (TreeElement feature : configurationEditor.configuration.getRoot().getChildren())
				remove(feature);
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
			removeHiddenFeatures();
			viewer.refresh();
			
		}
	}
	
	protected void set(SelectableFeature feature, Selection selection) {
		configurationEditor.configuration.setManual(feature, selection);
		updateForeground(viewer.getTree().getItem(0));
	}
	
	private void updateForeground(TreeItem item) {		
		for (TreeItem child : item.getItems()) {
			SelectableFeature feature = configurationEditor.configuration.getSelectablefeature(child.getText());
			child.setForeground(null);
			child.setFont(treeItemStandardFont);
			if (feature != null) {
				if (!configurationEditor.configuration.valid())
					if (feature.getAutomatic() == Selection.UNDEFINED) {
						if (feature.getManual() == Selection.UNDEFINED) {
							if (configurationEditor.configuration.leadToValidConfiguration(feature, Selection.SELECTED, Selection.UNDEFINED)){
								child.setForeground(green);
								child.setFont(treeItemSpecialFont);	
							}
						} else if (feature.getManual() == Selection.SELECTED) {
							if (configurationEditor.configuration.leadToValidConfiguration(feature, Selection.UNSELECTED, Selection.SELECTED)){
								child.setForeground(blue);
								child.setFont(treeItemSpecialFont);
							}
							// case: unselected
						} else if (configurationEditor.configuration.leadToValidConfiguration(feature, Selection.SELECTED, Selection.UNSELECTED)){
								child.setForeground(green);
								child.setFont(treeItemSpecialFont);	
						}
					}
				updateForeground(child);
			}
		}
	}
}