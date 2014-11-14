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

import java.beans.PropertyChangeEvent;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
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
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.Configuration.ValidConfigJob;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
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
	
	private ValidConfigJobManager validConfigJobManager = null;
	
	@Override
	protected void setInput(IEditorInput input) {
		super.setInput(input);
		if (configurationEditor instanceof ConfigurationEditor) {
			validConfigJobManager = ((ConfigurationEditor)configurationEditor).getValidConfigJobManager();
		}
	}

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

	@Override
	public void createPartControl(Composite parent) {
		viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		viewer.getTree().addMouseListener(new MouseListener() {
			@Override
			public void mouseUp(MouseEvent e) {
				if (e.button == 1 || e.button == 3) {
					TreeItem item = viewer.getTree().getItem(new Point(e.x, e.y));
					if (item != null) {
						Object data = item.getData();
						if (data instanceof SelectableFeature) {
							final SelectableFeature feature = (SelectableFeature) data;
							changeSelection(feature, e.button == 1);
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
							cycleSelection(feature);
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
	private boolean initialized = false;

	private LinkedList<String> hiddenFeatures;
	
	@Override
	public void propertyChange(PropertyChangeEvent evt) {
		if (initialized) {
			setDirty();
		} else {
			initialized = true;
		}
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
		viewer.setInput(configurationEditor.getConfiguration());
		viewer.expandAll();
		viewer.refresh();
		if (!errorMessage())
			updateForeground(viewer.getTree().getItem(0));
		removeHiddenFeatures();
		viewer.getTree().setRedraw(true);
	}

	private void removeHiddenFeatures() {
		hiddenFeatures = new LinkedList<String>();
		for (Feature feature : configurationEditor.getConfiguration().getFeatureModel().getFeatures()) {
			if (feature.isHidden())
				hiddenFeatures.add(feature.getName());
		}
		for (TreeElement feature : configurationEditor.getConfiguration().getRoot().getChildren())
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
		if (!configurationEditor.getConfiguration().isValid() && configurationEditor.getConfiguration().number() == 0){
			for (TreeElement feature : configurationEditor.getConfiguration().getRoot().getChildren()) {
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
	
	protected void cycleSelection(SelectableFeature feature) {
		cycleSelection(feature, true);
	}
	
	protected void cycleSelection(SelectableFeature feature, boolean up) {
		viewer.getTree().setRedraw(false);
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
			viewer.refresh();
			removeHiddenFeatures();
		}
		viewer.getTree().setRedraw(true);
	}
	
	protected void changeSelection(SelectableFeature feature, boolean select) {
		viewer.getTree().setRedraw(false);
		if (feature.getAutomatic() == Selection.UNDEFINED) {
			switch (feature.getManual()) {
			case SELECTED: set(feature, (select) ? Selection.UNDEFINED : Selection.UNSELECTED);  break;
			case UNSELECTED: set(feature, (select) ? Selection.SELECTED : Selection.UNDEFINED);  break;
			case UNDEFINED: set(feature, (select) ? Selection.SELECTED : Selection.UNSELECTED); break;
			default: set(feature, Selection.UNDEFINED);
			}
			if (!dirty) {
				setDirty();
			}
			viewer.refresh();
			removeHiddenFeatures();
		}
		viewer.getTree().setRedraw(true);
	}
	
	protected void set(SelectableFeature feature, Selection selection) {
		configurationEditor.getConfiguration().setManual(feature, selection);
		updateForeground(viewer.getTree().getItem(0));
	}
	
	private void updateForegroundRec(TreeItem item, HashSet<String> featureSet) {
		for (TreeItem child : item.getItems()) {
			final Object data = child.getData();
			if (data instanceof SelectableFeature) {
				final SelectableFeature feature = (SelectableFeature) data;
				if (featureSet.contains(feature.getName())) {
					child.setForeground((feature.getManual() == Selection.SELECTED) ? ConfigurationPage.blue : ConfigurationPage.green);
				} else {
					child.setForeground(ConfigurationPage.black);
				}
			}
			updateForegroundRec(child, featureSet);
		}
	}
	
	private void updateForegroundRec(TreeItem item) {
		for (TreeItem child : item.getItems()) {
			item.setForeground(ConfigurationPage.black);
			updateForegroundRec(child);
		}
	}
	
	private void updateForeground(final TreeItem item) {
		if (validConfigJobManager != null && !configurationEditor.getConfiguration().isValid()) {
			final List<SelectableFeature> featureList = new LinkedList<SelectableFeature>();
			final List<SelectableFeature> allFeatures = configurationEditor.getConfiguration().getFeatures();
			for (SelectableFeature selectableFeature : allFeatures) {
				if (selectableFeature.getAutomatic() == Selection.UNDEFINED) {
					featureList.add(selectableFeature);
				}
			}
			
			final Display currentDisplay = Display.getCurrent();
			
			final JobFinishListener colorListener = new JobFinishListener() {
				@Override
				public void jobFinished(IJob finishedJob, boolean success) {
					if (success) {
						boolean[] validConf = ((ValidConfigJob)finishedJob).getResults();
						final HashSet<String> featureSet = new HashSet<String>();
						int i = 0;
						for (SelectableFeature selectableFeature : featureList) {
							if (validConf[i++]) {
								featureSet.add(selectableFeature.getName());
							}
						}
						
						// needs to be executed on GUI Thread (otherwise there is an InvalidAccessException)
						currentDisplay.asyncExec(new Runnable() {
							@Override
							public void run() {
								updateForegroundRec(item, featureSet);								
							}
						});
					}
				}
			};
			
			validConfigJobManager.startNewValidConfigJob(featureList, colorListener);
		} else {
			// reset color
			updateForegroundRec(item);
		}
	}
	
	@Override
	public String getID() {
		return ID;
	}
}