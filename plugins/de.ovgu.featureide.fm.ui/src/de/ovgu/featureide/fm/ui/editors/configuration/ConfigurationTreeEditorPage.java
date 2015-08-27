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

import static de.ovgu.featureide.fm.core.localization.StringTable.AN_UNKNOWN_ERROR_OCCURRED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.ARIAL;
import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATING____;
import static de.ovgu.featureide.fm.core.localization.StringTable.DOES_NOT_EXIST_;
import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_COMMA_;
import static de.ovgu.featureide.fm.core.localization.StringTable.MORE_THAN;
import static de.ovgu.featureide.fm.core.localization.StringTable.POSSIBLE_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.THERE_IS_NO_FEATURE_MODEL_CORRESPONDING_TO_THIS_CONFIGURATION_COMMA__REOPEN_THE_EDITOR_AND_SELECT_ONE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_FEATURE_MODEL_FOR_THIS_PROJECT_IS_VOID_COMMA__I_E__COMMA__THERE_IS_NO_VALID_CONFIGURATION__YOU_NEED_TO_CORRECT_THE_FEATURE_MODEL_BEFORE_YOU_CAN_CREATE_OR_EDIT_CONFIGURATIONS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_GIVEN_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.VALID_COMMA_;

import java.beans.PropertyChangeEvent;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
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
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.FunctionalInterfaces;
import de.ovgu.featureide.fm.core.FunctionalInterfaces.IBinaryFunction;
import de.ovgu.featureide.fm.core.FunctionalInterfaces.IFunction;
import de.ovgu.featureide.fm.core.ProfileManager;
import de.ovgu.featureide.fm.core.ProfileManager.Project.Profile;
import de.ovgu.featureide.fm.core.annotation.ColorPalette;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationPropagatorJobWrapper.IConfigJob;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.PlugInProfileSerializer;

/**
 * Basic class with some default methods for configuration editor pages.
 * 
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 */
public abstract class ConfigurationTreeEditorPage extends EditorPart implements IConfigurationEditorPage {
	protected static final Color gray = new Color(null, 140, 140, 140);
	protected static final Color green = new Color(null, 0, 140, 0);
	protected static final Color blue = new Color(null, 0, 0, 200);
	protected static final Color red = new Color(null, 240, 0, 0);

	protected static final Font treeItemStandardFont = new Font(null, ARIAL, 8, SWT.NORMAL);
	protected static final Font treeItemSpecialFont = new Font(null, ARIAL, 8, SWT.BOLD);

	private final HashSet<SelectableFeature> invalidFeatures = new HashSet<SelectableFeature>();
	protected final HashSet<SelectableFeature> updateFeatures = new HashSet<SelectableFeature>();

	protected IConfigurationEditor configurationEditor = null;

	protected boolean dirty = false;

	protected Tree tree;

	private int index;

	private Label infoLabel;

	//	private Button autoSelectButton;

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
	}

	protected final void refreshPage() {
		//		if (configurationEditor.isAutoSelectFeatures()) {
		//			autoSelectButton.setEnabled(true);
		//		}
		//		autoSelectButton.setSelection(configurationEditor.isAutoSelectFeatures());
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
		gridLayout = new GridLayout(1, false);
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
		updateInfoLabel(Display.getCurrent());

		// autoselect button 
		//		gridData = new GridData();
		//		gridData.horizontalAlignment = SWT.RIGHT;
		//		gridData.verticalAlignment = SWT.CENTER;
		//		autoSelectButton = new Button(compositeTop, SWT.TOGGLE);
		//		autoSelectButton.setText(AUTOSELECT_FEATURES);
		//		autoSelectButton.setLayoutData(gridData);
		//		autoSelectButton.setSelection(false);
		//		autoSelectButton.setEnabled(false);
		//				
		//		autoSelectButton.addSelectionListener(new SelectionListener() {
		//			@Override
		//			public void widgetSelected(SelectionEvent e) {
		//				final Configuration config = configurationEditor.getConfiguration();
		//				if (configurationEditor.isAutoSelectFeatures()) {
		//					invalidFeatures.clear();
		//					configurationEditor.setAutoSelectFeatures(false);
		//					configurationEditor.getConfigJobManager().cancelAllJobs();
		//					config.makeManual(!canDeselectFeatures());
		//					walkTree(new IBinaryFunction<TreeItem, SelectableFeature, Void>() {
		//						@Override
		//						public Void invoke(TreeItem item, SelectableFeature feature) {
		//							refreshItem(item, feature);
		//							return null;
		//						}
		//					}, new FunctionalInterfaces.NullFunction<Void, Void>());
		//					updateInfoLabel(Display.getCurrent());
		//				} else {
		//					if (invalidFeatures.isEmpty()) {
		//						configurationEditor.setAutoSelectFeatures(true);
		////						updateInfoLabel();
		//						computeTree(true);
		//					} else {
		//						autoSelectButton.setSelection(false);
		//					}
		//				}
		//			}
		//			
		//			@Override
		//			public void widgetDefaultSelected(SelectionEvent e) {}
		//		});

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

	protected final HashMap<SelectableFeature, TreeItem> itemMap = new HashMap<SelectableFeature, TreeItem>();

	protected abstract void createUITree(Composite parent);

	protected void updateInfoLabel(final Display display) {
		if (display == null) {
			infoLabel.setText(CALCULATING____);
			infoLabel.setForeground(null);
			return;
		}
		final boolean valid = configurationEditor.getConfiguration().isValid();

		final IConfigJob<Long> job = configurationEditor.getConfiguration().getPropagator().getJobWrapper().number(250);
		job.addJobFinishedListener(new JobFinishListener() {
			@Override
			public void jobFinished(IJob finishedJob, boolean success) {
				final StringBuilder sb = new StringBuilder();
				sb.append(valid ? VALID_COMMA_ : INVALID_COMMA_);

				@SuppressWarnings("unchecked")
				final long number = ((IConfigJob<Long>) finishedJob).getResults();
				if (number < 0) {
					sb.append(MORE_THAN);
					sb.append(-1 - number);
				} else {
					sb.append(number);
				}
				sb.append(POSSIBLE_CONFIGURATIONS);
				if (number == 0 && !configurationEditor.isAutoSelectFeatures()) {
					sb.append(" - Autoselect not possible!");
				}

				display.asyncExec(new Runnable() {
					@Override
					public void run() {
						infoLabel.setText(sb.toString());
						infoLabel.setForeground(valid ? blue : red);
					}
				});
			}
		});
		configurationEditor.getConfigJobManager().startJob(job);
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
				displayError(tree, THERE_IS_NO_FEATURE_MODEL_CORRESPONDING_TO_THIS_CONFIGURATION_COMMA__REOPEN_THE_EDITOR_AND_SELECT_ONE_);
			} else if (!configurationEditor.getModelFile().exists()) {
				displayError(tree, THE_GIVEN_FEATURE_MODEL + configurationEditor.getModelFile().getPath() + DOES_NOT_EXIST_);
			} else {
				displayError(tree, AN_UNKNOWN_ERROR_OCCURRED_);
			}
			return false;
		} else {
			final FeatureModelAnalyzer analyzer = configurationEditor.getConfiguration().getFeatureModel().getAnalyser();
			try {
				if (!analyzer.isValid()) {
					displayError(
							tree,
							THE_FEATURE_MODEL_FOR_THIS_PROJECT_IS_VOID_COMMA__I_E__COMMA__THERE_IS_NO_VALID_CONFIGURATION__YOU_NEED_TO_CORRECT_THE_FEATURE_MODEL_BEFORE_YOU_CAN_CREATE_OR_EDIT_CONFIGURATIONS_);
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
		configurationEditor.getConfiguration().setManual(feature, selection);
	}

	protected void changeSelection(final TreeItem item, final boolean select) {
		SelectableFeature feature = (SelectableFeature) item.getData();
		if (feature.getAutomatic() == Selection.UNDEFINED) {
			switch (feature.getManual()) {
			case SELECTED:
				set(feature, (select) ? Selection.UNDEFINED : Selection.UNSELECTED);
				break;
			case UNSELECTED:
				set(feature, (select) ? Selection.SELECTED : Selection.UNDEFINED);
				break;
			case UNDEFINED:
				set(feature, (select) ? Selection.SELECTED : Selection.UNSELECTED);
				break;
			default:
				set(feature, Selection.UNDEFINED);
			}
			if (!dirty) {
				setDirty();
			}
			if (configurationEditor.isAutoSelectFeatures()) {
				computeTree(false);
				//				updateInfoLabel();
			} else {
				refreshItem(item, feature);
				if (configurationEditor.getConfiguration().canBeValid()) {
					invalidFeatures.clear();
				} else {
					invalidFeatures.add(feature);
				}
				//				updateInfoLabel();
			}
		}
	}

	private Profile getCurrentProfile(FeatureModel featureModel) {
		return ProfileManager.getProject(featureModel.xxxGetEclipseProjectPath(), PlugInProfileSerializer.FEATURE_PROJECT_SERIALIZER).getActiveProfile();
	}

	protected void updateTree() {
		itemMap.clear();
		if (errorMessage(tree)) {
			final Configuration configuration = configurationEditor.getConfiguration();
			tree.removeAll();
			tree.addListener(SWT.PaintItem, new Listener() {

				@Override
				public void handleEvent(Event event) {
					if (event.item instanceof TreeItem) {
						TreeItem item = (TreeItem) event.item;
						if (item.getData() instanceof SelectableFeature) {
							SelectableFeature selectableFeature = (SelectableFeature) item.getData();
							Feature feature = selectableFeature.getFeature();
							
							if (ProfileManager.toColorIndex(getCurrentProfile(feature.getFeatureModel()).getColor(feature.getName())) != -1) {
								item.setBackground(new Color(null, ColorPalette.getRGB(
										ProfileManager.toColorIndex(getCurrentProfile(feature.getFeatureModel()).getColor(feature.getName())), 0.5f)));
							}
						}
					}
				}
			});
			final TreeItem root = new TreeItem(tree, 0);

			root.setText(configuration.getRoot().getName());
			root.setData(configuration.getRoot());
			itemMap.put(configuration.getRoot(), root);

			buildTree(root, configuration.getRoot().getChildren(), new FunctionalInterfaces.IFunction<Void, Void>() {
				@Override
				public Void invoke(Void t) {
					//					updateInfoLabel();
					computeTree(false);
					return null;
				}
			});
		}
	}

	protected boolean canDeselectFeatures() {
		return false;
	}

	protected void refreshItem(TreeItem item, SelectableFeature feature) {
		item.setBackground(null);
		item.setFont(treeItemStandardFont);
		switch (feature.getAutomatic()) {
		case SELECTED:
			item.setGrayed(true);
			item.setForeground(null);
			item.setChecked(true);
			break;
		case UNSELECTED:
			item.setGrayed(true);
			item.setForeground(gray);
			item.setChecked(false);
			break;
		case UNDEFINED:
			item.setGrayed(false);
			item.setForeground(null);
			item.setChecked(feature.getManual() == Selection.SELECTED);
			break;
		}
	}

	/**
	 * Colors all features if they lead to a valid configuration if current
	 * configuration is invalid. deselect:blue, select:green
	 */
	protected IConfigJob<?> computeColoring(final Display currentDisplay) {
		if (!configurationEditor.isAutoSelectFeatures() || configurationEditor.getConfiguration().isValid()) {
			return null;
		}
		final List<SelectableFeature> featureList = configurationEditor.getConfiguration().getManualFeatures();
		final IConfigJob<?> job = configurationEditor.getConfiguration().getPropagator().getJobWrapper().leadToValidConfiguration(featureList);
		job.setIntermediateFunction(new IFunction<Object, Void>() {
			@Override
			public Void invoke(Object t) {
				if (t instanceof SelectableFeature) {
					final SelectableFeature feature = (SelectableFeature) t;
					final TreeItem item = itemMap.get(feature);
					if (item == null) {
						return null;
					}
					currentDisplay.asyncExec(new Runnable() {
						@Override
						public void run() {
							if (feature.getAutomatic() == Selection.UNDEFINED) {
								switch (feature.getRecommended()) {
								case SELECTED:
									item.setFont(treeItemSpecialFont);
									item.setForeground(green);
									break;
								case UNSELECTED:
									item.setFont(treeItemSpecialFont);
									item.setForeground(blue);
									break;
								case UNDEFINED:
									item.setFont(treeItemStandardFont);
									item.setForeground(null);
									break;
								}
							}
						}
					});
				}
				return null;
			}
		});
		return job;
	}

	protected IConfigJob<?> computeFeatures(final boolean redundantManual, final Display currentDisplay) {
		if (!configurationEditor.isAutoSelectFeatures()) {
			return null;
		}
		final TreeItem topItem = tree.getTopItem();
		SelectableFeature feature = (SelectableFeature) (topItem.getData());
		final IConfigJob<?> job = configurationEditor.getConfiguration().getPropagator().getJobWrapper()
				.update(redundantManual, feature.getFeature().getName());
		job.setIntermediateFunction(new IFunction<Object, Void>() {
			@Override
			public Void invoke(Object t) {
				if (t instanceof SelectableFeature) {
					final SelectableFeature feature = (SelectableFeature) t;
					final TreeItem item = itemMap.get(feature);
					if (item == null) {
						return null;
					}
					currentDisplay.asyncExec(new Runnable() {
						@Override
						public void run() {
							updateFeatures.remove(feature);
							refreshItem(item, feature);
						}
					});
				}
				return null;
			}
		});
		return job;
	}

	protected void lockItem(TreeItem item) {
		item.setGrayed(true);
		item.setChecked(true);
		item.setForeground(gray);
		item.setFont(treeItemStandardFont);
	}

	protected void computeTree(boolean redundantManual) {
		final Display currentDisplay = Display.getCurrent();
		if (currentDisplay == null) {
			return;
		}
		updateInfoLabel(null);

		final IConfigJob<?> updateJob = computeFeatures(redundantManual, currentDisplay);
		updateJob.addJobFinishedListener(new JobFinishListener() {

			@Override
			public void jobFinished(IJob finishedJob, boolean success) {
				if (success) {
					updateInfoLabel(currentDisplay);
					configurationEditor.getConfigJobManager().startJob(computeColoring(currentDisplay));
				}
			}
		});

		updateFeatures.clear();
		walkTree(new IBinaryFunction<TreeItem, SelectableFeature, Void>() {
			@Override
			public Void invoke(TreeItem item, SelectableFeature feature) {
				//				lockItem(item);
				updateFeatures.add(feature);
				return null;
			}
		}, new IFunction<Void, Void>() {
			@Override
			public Void invoke(Void t) {
				configurationEditor.getConfigJobManager().startJob(updateJob);
				return null;
			}
		});
	}

	protected final void walkTree(final FunctionalInterfaces.IBinaryFunction<TreeItem, SelectableFeature, Void> perNodeFunction,
			final FunctionalInterfaces.IFunction<Void, Void> callbackIfDone) {
		AsyncTree.traverse(itemMap, tree.getItem(0), perNodeFunction, callbackIfDone);
	}

	private void buildTree(final TreeItem node, final TreeElement[] children, final FunctionalInterfaces.IFunction<Void, Void> callbackIfDone) {
		AsyncTree.build(itemMap, node, children, callbackIfDone);
	}

}
