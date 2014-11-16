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
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.configuration.Configuration.ValidConfigJob;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Basic class with some default methods for configuration editor pages.
 * 
 * @author Jens Meinicke
 */
public abstract class ConfigurationEditorPage extends EditorPart implements IConfigurationEditorPage {
	static interface ConfigurationTreeWalker {
		boolean visitTreeItem(TreeItem item, SelectableFeature feature);
	}
	
	static final Color gray = new Color(null, 140, 140, 140);
	static final Color green = new Color(null, 0, 140, 0);
	static final Color blue = new Color(null, 0, 0, 200);
	
	static final Font treeItemStandardFont = new Font(null, "Arial", 8, SWT.NORMAL);
	static final Font treeItemSpecialFont = new Font(null, "Arial", 8, SWT.BOLD);
	
	protected final Set<String> colorFeatureNames = new HashSet<String>();
	
	protected IConfigurationEditor configurationEditor = null;
	protected ValidConfigJobManager validConfigJobManager = null;

	private int index;
	protected boolean dirty = false;
	protected boolean initialized = false;
	
	public void setDirty() {
		dirty = true;
		firePropertyChange(PROP_DIRTY);
	}
	
	@Override
	public void setIndex(int index) {
		this.index = index;
	}
	
	@Override
	public int getIndex() {
		return index;
	}
	
	@Override
	public void setConfigurationEditor(IConfigurationEditor configurationEditor) {
		this.configurationEditor = configurationEditor;
	}
	
	@Override
	public void propertyChange(PropertyChangeEvent evt) {
		if (initialized) {
			setDirty();
		} else {
			initialized = true;
		}
		UIJob job = new UIJob("update tree") {
			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				updateTree();
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.SHORT);
		job.schedule();
	}
	
	@Override
	public void pageChangeFrom(int index) {
	
	}
	
	@Override
	public void pageChangeTo(int index) {

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
	public void init(IEditorSite site, IEditorInput input) throws PartInitException {
		setSite(site);
		setInput(input);
	}
	
	@Override
	protected void setInput(IEditorInput input) {
		super.setInput(input);
		if (configurationEditor instanceof ConfigurationEditor) {
			validConfigJobManager = ((ConfigurationEditor)configurationEditor).getValidConfigJobManager();
		}
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
	}
	
	@Override
	public void setFocus() {
	}
	
	@Override
	public IConfigurationEditorPage getPage() {
		return this;
	}
	
	protected boolean errorMessage(Tree tree) {
		if (configurationEditor.getConfiguration() == null 
				|| (!configurationEditor.getConfiguration().isValid() && configurationEditor.getConfiguration().number() == 0)) {
			tree.removeAll();
			TreeItem item = new TreeItem(tree, 1);
			if (configurationEditor.getModelFile() == null) {
				item.setText("There is no feature model corresponding to this configuration, reopen the editor and select one.");
			} else if (!configurationEditor.getModelFile().exists()) {
				// This case should never happen
				item.setText("The given feature model " + configurationEditor.getModelFile().getPath() + " does not exist.");
			} else {
				item.setText("The feature model for this project is void, i.e., " + "there is no valid configuration. You need to correct the " + "feature model before you can create or edit configurations.");
			}
			tree.getItem(0).setImage(0,FMUIPlugin.getDefault()
					.getWorkbench().getSharedImages().getImage
					(ISharedImages.IMG_OBJS_ERROR_TSK));
			dirty = false;
			item.setChecked(true);
			item.setGrayed(true);
			return false;
		}
		return true;
	}
	
	protected void set(SelectableFeature feature, Selection selection) {
		configurationEditor.getConfiguration().setManual(feature, selection);
	}
	
	protected boolean changeSelection(SelectableFeature feature) {
		return changeSelection(feature, true);
	}
	
	protected boolean changeSelection(SelectableFeature feature, boolean select) {
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
			refreshTree();
			return true;
		}
		return false;
	}
	
	protected abstract TreeItem getRoot();

	protected abstract void updateTree();
	protected abstract void refreshTree();
	
	protected ConfigurationTreeWalker getDefaultTreeWalker() {
		return null;
	}
	
	protected void refreshItems() {
		colorFeatureNames.clear();
		walkTree(getDefaultTreeWalker());
		computeColoring();
	}
	
	/**
	 * Colors all features if they lead to a valid configuration if current
	 * configuration is invalid. deselect:blue, select:green
	 */
	private void computeColoring() {
		if (validConfigJobManager != null 
				&& validConfigJobManager.isCompletionEnabled()
				&& !configurationEditor.getConfiguration().isValid()) {
			final List<SelectableFeature> featureList = configurationEditor.getConfiguration().getManualFeatures();
			final Display currentDisplay = Display.getCurrent();
			
			final JobFinishListener colorListener = new JobFinishListener() {
				@Override
				public void jobFinished(IJob finishedJob, boolean success) {
					if (success) {
						boolean[] validConf = ((ValidConfigJob)finishedJob).getResults();
						colorFeatureNames.clear();
						int i = 0;
						for (SelectableFeature selectableFeature : featureList) {
							if (validConf[i++]) {
								colorFeatureNames.add(selectableFeature.getName());
							}
						}
						
						// needs to be executed on GUI Thread (otherwise there is an InvalidAccessException)
						currentDisplay.asyncExec(new Runnable() {
							@Override
							public void run() {
								walkTree(new ConfigurationTreeWalker() {
									@Override
									public boolean visitTreeItem(TreeItem item, SelectableFeature feature) {
										if (colorFeatureNames.contains(feature.getName())) {
											item.setForeground((feature.getManual() == Selection.SELECTED) ? blue : green);
											item.setFont(treeItemSpecialFont);
										}
										return true;
									}
								});
							}
						});
					}
				}
			};
			
			validConfigJobManager.startNewValidConfigJob(featureList, colorListener);
		}
	}
	
	protected final void walkTree(ConfigurationTreeWalker walker) {
		walkTree(getRoot(), walker);
	}

	protected final void walkTree(TreeItem item, ConfigurationTreeWalker walker) {
		if (walker == null) {
			return;
		}
		for (TreeItem child : item.getItems()) {
			final Object data = child.getData();
			if (data instanceof SelectableFeature) {
				final SelectableFeature feature = (SelectableFeature) data;
				if (walker.visitTreeItem(child, feature)) {
					walkTree(child, walker);
				}
			}
		}
	}	
}
