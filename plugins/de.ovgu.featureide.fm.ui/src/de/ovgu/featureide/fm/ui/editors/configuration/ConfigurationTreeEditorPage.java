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
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.FunctionalInterfaces;
import de.ovgu.featureide.fm.core.FunctionalInterfaces.IFunction;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationPropagatorJobWrapper.IConfigJob;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.job.AJob;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.configuration.xxx.AsyncTree;

/**
 * Basic class with some default methods for configuration editor pages.
 * 
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 */
public abstract class ConfigurationTreeEditorPage extends EditorPart implements IConfigurationEditorPage {
	static interface ConfigurationTreeWalker {
		boolean visitTreeItem(TreeItem item, SelectableFeature feature);
	}	
		
	static final Color gray = new Color(null, 140, 140, 140);
	static final Color green = new Color(null, 0, 140, 0);
	static final Color blue = new Color(null, 0, 0, 200);
	static final Color red = new Color(null, 240, 0, 0);
	
	static final Font treeItemStandardFont = new Font(null, "Arial", 8, SWT.NORMAL);
	static final Font treeItemSpecialFont = new Font(null, "Arial", 8, SWT.BOLD);
	
	protected final Set<String> colorFeatureNames = new HashSet<String>();
	private final HashSet<SelectableFeature> invalidFeatures = new HashSet<SelectableFeature>();
	
	protected IConfigurationEditor configurationEditor = null;
	protected ConfigJobManager configJobManager = null;

	protected boolean dirty = false;

	private int index;
	
	private Label infoLabel;
	private Button autoSelectButton;
	
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
		refreshPage();
		setDirty();
	}

	protected final void refreshPage() {
		autoSelectButton.setSelection(configurationEditor.getConfiguration().isPropagate());
		updateTree();
	}
	
	@Override
	public void pageChangeFrom(int index) {
		
	}
	
	@Override
	public void pageChangeTo(int index) {
		refreshPage();
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
			configJobManager = ((ConfigurationEditor)configurationEditor).getConfigJobManager();
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
		// parent composite
		GridLayout gridLayout = new GridLayout(1, false);
		gridLayout.verticalSpacing = 4;
		gridLayout.marginHeight = 2;
		gridLayout.marginWidth = 0;
		parent.setLayout(gridLayout);
		
		// 1. sub composite
		GridData gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = false;
		gridData.verticalAlignment = SWT.TOP;
	    gridLayout = new GridLayout(2, false);
		gridLayout.marginHeight = 0;
		gridLayout.marginWidth = 0;
		gridLayout.marginLeft = 4;
		final Composite compositeTop = new Composite(parent, SWT.NONE);
	    compositeTop.setLayout(gridLayout);
	    compositeTop.setLayoutData(gridData);
	    
	    // info label
	    gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.verticalAlignment = SWT.CENTER;
	    infoLabel = new Label(compositeTop, SWT.NONE);
	    infoLabel.setLayoutData(gridData);
	    updateInfoLabel();
	    		
		// autoselect button 
		gridData = new GridData();
		gridData.horizontalAlignment = SWT.RIGHT;
		gridData.verticalAlignment = SWT.CENTER;
		autoSelectButton = new Button(compositeTop, SWT.TOGGLE);
		autoSelectButton.setText("Autoselect Features");
		autoSelectButton.setLayoutData(gridData);
		autoSelectButton.setSelection(true);
				
		autoSelectButton.addSelectionListener(new SelectionListener() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				final Configuration config = configurationEditor.getConfiguration();
				boolean oldPropagate = config.isPropagate();
				if (oldPropagate) {
					invalidFeatures.clear();
					config.setPropagate(false);
					config.makeManual(!canDeselectFeatures());
					refreshTree();
				} else {
					if (invalidFeatures.isEmpty()) {
						config.setPropagate(true);
						computeFeatures();
					} else {
						autoSelectButton.setSelection(false);
					}
				}
			}
			
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		
		// 2. sub composite
		gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.verticalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		final Composite compositeBottom = new Composite(parent, SWT.BORDER);
	    compositeBottom.setLayout(new FillLayout());
	    compositeBottom.setLayoutData(gridData);
	    
	    createUITree(compositeBottom);
	}
	
	private void computeFeatures() {
		configurationEditor.getConfiguration().update(true, true);
		refreshTree();
	}
	
	protected abstract void createUITree(Composite parent);
	
	private void updateInfoLabel() {
		final Display display = Display.getCurrent();
		if (display == null) {
			return;
		}
		IJob job = new AJob("Update Label") {
			@Override
			protected boolean work() {
				Configuration configuration = configurationEditor.getConfiguration();
				final boolean valid = configuration .isValid();
				final StringBuilder sb = new StringBuilder();
				sb.append(valid ? "valid, " : "invalid, ");
				long number = configuration.number();
				if (number < 0) {
					sb.append("more than ");
					sb.append(-1 - number);
				} else {
					sb.append(number);
				}
				sb.append(" possible configurations");
				if (number == 0 && !configuration.isPropagate()) {
					sb.append(" - Autoselect not possible!");
				}

				display.asyncExec(new Runnable() {
					@Override
					public void run() {
						infoLabel.setText(sb.toString());
						infoLabel.setForeground(valid ? blue : red);
					}
				});
				return true;
			}
		};
		job.schedule();
	}
	
	@Override
	public void setFocus() {
	}
	
	@Override
	public IConfigurationEditorPage getPage() {
		return this;
	}
	
	protected boolean errorMessage(Tree tree) {
		if (configurationEditor.getConfiguration() == null) {
			if (configurationEditor.getModelFile() == null) {
				displayError(tree, "There is no feature model corresponding to this configuration, reopen the editor and select one.");
			} else if (!configurationEditor.getModelFile().exists()) {
				displayError(tree, "The given feature model " + configurationEditor.getModelFile().getPath() + " does not exist.");
			} else {
				displayError(tree, "An unknown error occurred.");
			}
			return false;
		} else {
			final FeatureModelAnalyzer analyzer = configurationEditor.getConfiguration().getFeatureModel().getAnalyser();
			try {
				if (!analyzer.isValid()) {
					displayError(tree, "The feature model for this project is void, i.e., there is no valid configuration. You need to correct the feature model before you can create or edit configurations.");
					return false;
				}
			} catch (TimeoutException e) {
				FMUIPlugin.getDefault().logError(e);
			}

		}
		return true;
	}
	
	private void displayError(Tree tree, String message) {
		tree.removeAll();
		TreeItem item = new TreeItem(tree, 1);
		item.setText(message);
		item.setImage(0, FMUIPlugin.getDefault().getWorkbench().getSharedImages().getImage(ISharedImages.IMG_OBJS_ERROR_TSK));
		item.setChecked(true);
		item.setGrayed(true);
		dirty = false;
	}
	
	protected void set(SelectableFeature feature, Selection selection) {
		final Configuration config = configurationEditor.getConfiguration();
		final boolean propagate = config.isPropagate();
		config.setPropagate(false);
		config.setManual(feature, selection);
		config.setPropagate(propagate);
		
		if (propagate) {
			final IConfigJob<?> job = config.getPropagator().getJobWrapper().update(false, false, feature.getName());
			configJobManager.startJob(job, null, new IFunction<Object, Void>() {
				
				@Override
				public Void invoke(Object t) {
					Feature f = (Feature) t;
					return null;
				}
			});
		} else {
			if (config.canBeValid()) {
				invalidFeatures.clear();
			} else {
				invalidFeatures.add(feature);
			}
		}
	}
	
	protected boolean changeSelection(TreeItem item) {
		return changeSelection(item, true);
	}
	
	protected boolean changeSelection(TreeItem item, boolean select) {
		SelectableFeature feature = (SelectableFeature)item.getData();
		if (feature.getAutomatic() == Selection.UNDEFINED) {
			switch (feature.getManual()) {
			case SELECTED: set(feature, (select) ? Selection.UNDEFINED : Selection.UNSELECTED); break;
			case UNSELECTED: set(feature, (select) ? Selection.SELECTED : Selection.UNDEFINED); break;
			case UNDEFINED: set(feature, (select) ? Selection.SELECTED : Selection.UNSELECTED); break;
			default: set(feature, Selection.UNDEFINED);
			}
			if (!dirty) {
				setDirty();
			}
			if (configurationEditor.getConfiguration().isPropagate()) {
				refreshTree();
			} else {
				refreshItem(item, feature);
			}
			return true;
		}
		return false;
	}

	protected abstract TreeItem getRoot();
	protected abstract void updateTree();
	
	protected FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void> getDefaultTreeWalker() {
		return null;
	}
	
	protected boolean canDeselectFeatures() {
		return false;
	}
	
	protected void refreshTree() {
		colorFeatureNames.clear();
		updateInfoLabel();
		if (configurationEditor.getConfiguration().isPropagate()) {
			computeColoring();
		}
		walkTree(getDefaultTreeWalker(), new FunctionalInterfaces.NullFunction<Void,Void>());
	}
	
	protected void refreshItem(TreeItem item, SelectableFeature feature) {
		FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void> walker = getDefaultTreeWalker();
		if (walker != null) {
			walker.invoke(item, feature);
		}
		updateInfoLabel();
	}
	
	/**
	 * Colors all features if they lead to a valid configuration if current
	 * configuration is invalid. deselect:blue, select:green
	 */
	private void computeColoring() {
		if (
				configJobManager != null &&
//				validConfigJobManager.isCompletionEnabled() && 
				!configurationEditor.getConfiguration().isValid()) {
			final List<SelectableFeature> featureList = configurationEditor.getConfiguration().getManualFeatures();
			final Display currentDisplay = Display.getCurrent();
			
			final JobFinishListener colorListener = new JobFinishListener() {
				@Override
				public void jobFinished(IJob finishedJob, boolean success) {
					if (success) {
						@SuppressWarnings("unchecked")
						boolean[] validConf = ((IConfigJob<boolean[]>)finishedJob).getResults();
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
								walkTree(new FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void>() {
									@Override
									public Void invoke(TreeItem item, SelectableFeature feature) {
										if (colorFeatureNames.contains(feature.getName())) {
											item.setForeground((feature.getManual() == Selection.SELECTED) ? blue : green);
											item.setFont(treeItemSpecialFont);
										}
										return null;
									}
								}, new FunctionalInterfaces.NullFunction<Void,Void>());
							}
						});
					}
				}
			};
			
			final IConfigJob<boolean[]> job = configurationEditor.getConfiguration().getPropagator().getJobWrapper().leadToValidConfiguration(featureList);
			
			configJobManager.startJob(job, colorListener, null);
		}
	}
	
	protected final void walkTree( 
			final FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void> perNodeFunction,
			final FunctionalInterfaces.IFunction<Void, Void> callbackIfDone) {
		getTree().traverse(getRoot(), perNodeFunction, callbackIfDone);
	}

	protected abstract AsyncTree getTree();

}
