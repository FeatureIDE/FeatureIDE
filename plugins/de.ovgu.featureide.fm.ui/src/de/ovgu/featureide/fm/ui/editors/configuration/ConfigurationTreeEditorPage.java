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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;
import org.prop4j.Node;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureModelEvent;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationMatrix;
import de.ovgu.featureide.fm.core.configuration.ConfigurationPropagatorJobWrapper.IConfigJob;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IBinaryFunction;
import de.ovgu.featureide.fm.core.functional.Functional.IFunction;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.utils.ISearchable;
import de.ovgu.featureide.fm.ui.utils.SearchField;
import de.ovgu.featureide.fm.ui.utils.UITreeIterator;

/**
 * Basic class with some default methods for configuration editor pages.
 * 
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public abstract class ConfigurationTreeEditorPage extends EditorPart implements IConfigurationEditorPage, ISearchable<TreeItem> {

	protected static final Color gray = new Color(null, 140, 140, 140);
	protected static final Color green = new Color(null, 0, 140, 0);
	protected static final Color blue = new Color(null, 0, 0, 200);
	protected static final Color red = new Color(null, 240, 0, 0);

	protected static final Font treeItemStandardFont = new Font(null, ARIAL, 8, SWT.NORMAL);
	protected static final Font treeItemSpecialFont = new Font(null, ARIAL, 8, SWT.BOLD);

	private static final Image IMAGE_EXPAND = FMUIPlugin.getDefault().getImageDescriptor("icons/expand.gif").createImage();
	private static final Image IMAGE_COLLAPSE = FMUIPlugin.getDefault().getImageDescriptor("icons/collapse.gif").createImage();
	private static final Image IMAGE_AUTOEXPAND_LEVEL = FMUIPlugin.getDefault().getImageDescriptor("icons/tree01.png").createImage();
	private static final Image IMAGE_AUTOEXPAND_GROUP = FMUIPlugin.getDefault().getImageDescriptor("icons/tree02.png").createImage();
	private static final Image IMAGE_NEXT = FMUIPlugin.getDefault().getImageDescriptor("icons/arrow_down.png").createImage();
	private static final Image IMAGE_PREVIOUS = FMUIPlugin.getDefault().getImageDescriptor("icons/arrow_up.png").createImage();

	private static final int AUTOEXPAND_LEVEL = 1;
	private static final int AUTOEXPAND_GROUP = 2;

	private final HashSet<SelectableFeature> invalidFeatures = new HashSet<SelectableFeature>();
	protected final HashSet<SelectableFeature> updateFeatures = new HashSet<SelectableFeature>();

	protected IConfigurationEditor configurationEditor = null;

	protected boolean dirty = false;

	/**
	 * 0 = No automatic expand.
	 * 1 = Display only items whose direct parents are selected. (Expands selected features)
	 * 2 = Display only items of the current color group.
	 * 3 = Display items whose direct parents are selected and items of the current color group.
	 */
	protected int autoExpand = AUTOEXPAND_LEVEL;

	protected int curGroup = 0;
	protected int curSearchIndex = 0;
	protected int maxGroup = 0;
	protected boolean useGroups = false;
	protected boolean useRecommendation = false;

	protected Tree tree;

	private int index;

	private Label infoLabel;

	private ToolItem autoExpandLevelToolItem, autoExpandGroupToolItem;

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
	public void propertyChange(FeatureModelEvent evt) {
		// TODO is a refresh necessary?
		// refreshPage();
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
		gridLayout = new GridLayout(3, false);
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
		if (configurationEditor.hasValidFeatureModel()) {
			updateInfoLabel(Display.getCurrent());
		}

		new SearchField<TreeItem>(compositeTop, this);

		gridData = new GridData();
		gridData.horizontalAlignment = SWT.RIGHT;
		gridData.verticalAlignment = SWT.CENTER;
		gridData.grabExcessHorizontalSpace = false;
		ToolBar toolbar = new ToolBar(compositeTop, SWT.FLAT | SWT.WRAP | SWT.RIGHT);
		toolbar.setLayoutData(gridData);

		new ToolItem(toolbar, SWT.SEPARATOR);

		ToolItem item = new ToolItem(toolbar, SWT.PUSH);
		item.setImage(IMAGE_COLLAPSE);
		item.setToolTipText("Collapse All Features");
		item.addSelectionListener(new SelectionListener() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				walkTree(new IBinaryFunction<TreeItem, SelectableFeature, Void>() {
					@Override
					public Void invoke(TreeItem item, SelectableFeature feature) {
						item.setExpanded(false);
						return null;
					}
				}, new IFunction<Void, Void>() {
					@Override
					public Void invoke(Void t) {
						final TreeItem root = tree.getItem(0);
						if (root != null) {
							root.setExpanded(true);
						}
						return null;
					}
				});
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});

		item = new ToolItem(toolbar, SWT.PUSH);
		item.setImage(IMAGE_EXPAND);
		item.setToolTipText("Expand All Features");
		item.addSelectionListener(new SelectionListener() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				walkTree(new IBinaryFunction<TreeItem, SelectableFeature, Void>() {
					@Override
					public Void invoke(TreeItem item, SelectableFeature feature) {
						item.setExpanded(true);
						return null;
					}
				}, new Functional.NullFunction<Void, Void>());
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});

		autoExpandLevelToolItem = new ToolItem(toolbar, SWT.CHECK);
		autoExpandLevelToolItem.setImage(IMAGE_AUTOEXPAND_LEVEL);
		autoExpandLevelToolItem.setSelection(autoExpand == AUTOEXPAND_LEVEL);
		autoExpandLevelToolItem.setToolTipText("Expand Levelwise");

		new ToolItem(toolbar, SWT.SEPARATOR);

		item = new ToolItem(toolbar, SWT.PUSH);
		item.setImage(IMAGE_NEXT);
		item.setToolTipText("Show Next Open Clause");
		item.addSelectionListener(new SelectionListener() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				if (curGroup < maxGroup) {
					curGroup++;
					autoExpandManual();
				}
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});

		item = new ToolItem(toolbar, SWT.PUSH);
		item.setImage(IMAGE_PREVIOUS);
		item.setToolTipText("Show Previous Open Clause");
		item.addSelectionListener(new SelectionListener() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				if (curGroup < 1) {
					curGroup = 1;
					autoExpandManual();
				} else if (curGroup > 1) {
					curGroup--;
					autoExpandManual();
				}
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});

		autoExpandGroupToolItem = new ToolItem(toolbar, SWT.CHECK);
		autoExpandGroupToolItem.setImage(IMAGE_AUTOEXPAND_GROUP);
		autoExpandGroupToolItem.setSelection(autoExpand == AUTOEXPAND_GROUP);
		autoExpandGroupToolItem.setToolTipText("Automatically Show Next Open Clause");

		autoExpandGroupToolItem.addSelectionListener(new SelectionListener() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				autoExpand ^= AUTOEXPAND_GROUP;
				if ((autoExpand & AUTOEXPAND_GROUP) > 0) {
					curGroup = 1;
					autoExpand();
				}
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});

		autoExpandLevelToolItem.addSelectionListener(new SelectionListener() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				autoExpand ^= AUTOEXPAND_LEVEL;
				if ((autoExpand & AUTOEXPAND_LEVEL) > 0) {
					autoExpand();
				}
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
			}
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

		tree.addListener(SWT.PaintItem, new Listener() {
			@Override
			public void handleEvent(Event event) {
				if (event.item instanceof TreeItem) {
					TreeItem item = (TreeItem) event.item;
					if (item.getData() instanceof SelectableFeature) {
						SelectableFeature selectableFeature = (SelectableFeature) item.getData();
						IFeature feature = selectableFeature.getFeature();
						FeatureColor color = FeatureColorManager.getColor(feature);
						if (color != FeatureColor.NO_COLOR) {
							item.setBackground(new Color(null, ColorPalette.getRGB(color.getValue(), 0.5f)));
						}
					}
				}
			}
		});
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

	protected boolean errorMessage() {
		if (!configurationEditor.hasValidFeatureModel()) {
			displayError(THE_GIVEN_FEATURE_MODEL + " is invalid.");
			return false;
		}
		if (configurationEditor.getConfiguration() == null) {
			if (configurationEditor.getModelFile() == null) {
				displayError(THERE_IS_NO_FEATURE_MODEL_CORRESPONDING_TO_THIS_CONFIGURATION_COMMA__REOPEN_THE_EDITOR_AND_SELECT_ONE_);
			} else if (!configurationEditor.getModelFile().exists()) {
				displayError(THE_GIVEN_FEATURE_MODEL + configurationEditor.getModelFile().getPath() + DOES_NOT_EXIST_);
			} else {
				displayError(AN_UNKNOWN_ERROR_OCCURRED_);
			}
			return false;
		} else {
			final FeatureModelAnalyzer analyzer = configurationEditor.getConfiguration().getFeatureModel().getAnalyser();
			try {
				if (!analyzer.isValid()) {
					displayError(
							THE_FEATURE_MODEL_FOR_THIS_PROJECT_IS_VOID_COMMA__I_E__COMMA__THERE_IS_NO_VALID_CONFIGURATION__YOU_NEED_TO_CORRECT_THE_FEATURE_MODEL_BEFORE_YOU_CAN_CREATE_OR_EDIT_CONFIGURATIONS_);
					return false;
				}
			} catch (TimeoutException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
		return true;
	}

	private void displayError(String message) {
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
			} else {
				item.setForeground(null);
				item.setFont(treeItemStandardFont);
				refreshItem(item, feature);
				if (configurationEditor.getConfiguration().canBeValid()) {
					invalidFeatures.clear();
				} else {
					invalidFeatures.add(feature);
				}
			}
			//				updateInfoLabel();
		}
	}

	protected void updateTree() {
		itemMap.clear();
		if (errorMessage()) {
			final Configuration configuration = configurationEditor.getConfiguration();
			tree.removeAll();

			final TreeItem root = new TreeItem(tree, 0);
			if (autoExpand == AUTOEXPAND_LEVEL) {
				root.setExpanded(true);
			}

			root.setFont(treeItemStandardFont);
			root.setForeground(null);

			root.setText(configuration.getRoot().getName());
			root.setData(configuration.getRoot());
			itemMap.put(configuration.getRoot(), root);

			buildTree(root, configuration.getRoot().getChildren(), new Functional.IFunction<Void, Void>() {
				@Override
				public Void invoke(Void t) {
					//					updateInfoLabel();
					computeTree(false);
					return null;
				}
			});
		}
	}

	private void autoExpand(Display display) {
		display.asyncExec(new Runnable() {
			@Override
			public void run() {
				autoExpand();
			}
		});
	}

	private void autoExpandManual() {
		if ((autoExpand & AUTOEXPAND_LEVEL) > 0) {
			levelExpand();
			groupExpand(false);
		} else {
			groupExpand(true);
		}
	}

	private void autoExpand() {
		if (autoExpand == (AUTOEXPAND_LEVEL | AUTOEXPAND_GROUP)) {
			levelExpand();
			groupExpand(false);
		} else if (autoExpand == AUTOEXPAND_LEVEL) {
			levelExpand();
		} else if (autoExpand == AUTOEXPAND_GROUP) {
			groupExpand(true);
		}
	}

	private boolean groupExpand(boolean collapse) {
		final LinkedList<TreeItem> groupItems = new LinkedList<>();
		final TreeItem root = tree.getItem(0);
		if (root != null) {
			searchGroupRec(root, curGroup, groupItems);

			if (collapse) {
				collapseRec(root);
			}
			if (!groupItems.isEmpty()) {
				for (TreeItem treeItem : groupItems) {
					TreeItem parent = treeItem.getParentItem();
					while (parent != null) {
						parent.setExpanded(true);
						parent = parent.getParentItem();
					}
				}
				tree.showItem(groupItems.getLast());
				tree.showItem(groupItems.getFirst());
				return true;
			}
		}
		return false;
	}

	private void searchGroupRec(TreeItem root, int group, LinkedList<TreeItem> groupItems) {
		final Object data = root.getData();
		if (data instanceof SelectableFeature) {
			final SelectableFeature feature = (SelectableFeature) data;
			if ((feature.getOpenClauseRelative() + 1) == group) {
				groupItems.add(root);
			}
		}

		final TreeItem[] items = root.getItems();
		for (TreeItem treeItem : items) {
			searchGroupRec(treeItem, group, groupItems);
		}
	}

	private void collapseRec(TreeItem root) {
		root.setExpanded(false);

		final TreeItem[] items = root.getItems();
		for (TreeItem treeItem : items) {
			collapseRec(treeItem);
		}
	}

	private void levelExpand() {
		final TreeItem root = tree.getItem(0);
		if (root != null) {
			root.setExpanded(true);
			expandRec(root);
		}
	}

	private void expandRec(TreeItem root) {
		TreeItem[] items = root.getItems();
		for (TreeItem treeItem : items) {
			final Object data = treeItem.getData();
			if (data instanceof SelectableFeature) {
				final SelectableFeature feature = (SelectableFeature) data;
				if (feature.getSelection() == Selection.UNDEFINED) {
					treeItem.setExpanded(false);
				} else {
					treeItem.setExpanded(true);
					expandRec(treeItem);
				}
			}
		}
	}

	protected boolean canDeselectFeatures() {
		return false;
	}

	protected void refreshItem(TreeItem item, SelectableFeature feature) {
		item.setBackground(null);
		item.setFont(treeItemStandardFont);
		item.setText(feature.getName());
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
			for (SelectableFeature selectableFeature : configurationEditor.getConfiguration().getFeatures()) {
				selectableFeature.setRecommendationValue(-1);
				selectableFeature.setOpenClauseAbsolute(-1);
				selectableFeature.setOpenClauseRelative(-2);
			}
			if ((autoExpand & AUTOEXPAND_GROUP) > 0) {
				autoExpand(currentDisplay);
			}
			return null;
		}

		final List<SelectableFeature> automaticFeatureList = new LinkedList<>();
		final List<SelectableFeature> manualFeatureList = new LinkedList<>();
		for (SelectableFeature selectableFeature : configurationEditor.getConfiguration().getFeatures()) {
			if (!selectableFeature.getFeature().getStructure().hasHiddenParent()) {
				if (selectableFeature.getAutomatic() == Selection.UNDEFINED && !selectableFeature.getFeature().getStructure().hasHiddenParent()) {
					manualFeatureList.add(selectableFeature);
				} else {
					automaticFeatureList.add(selectableFeature);
				}
			}
		}

		currentDisplay.syncExec(new Runnable() {
			@Override
			public void run() {
				for (SelectableFeature selectableFeature : automaticFeatureList) {
					selectableFeature.setRecommendationValue(-1);
					selectableFeature.setOpenClauseAbsolute(-1);
					selectableFeature.setOpenClauseRelative(-2);
					final TreeItem item = itemMap.get(selectableFeature);
					if (item != null) {
						refreshItem(item, selectableFeature);
					}
				}
			}
		});
		curGroup = 0;

		if (useRecommendation) {
			final ConfigurationMatrix configurationMatrix = ((ConfigurationEditor) configurationEditor).getConfigurationMatrix();
			configurationMatrix.calcRec(configurationEditor.getConfiguration());
			final double[] rec = configurationMatrix.getRec();
			if (rec != null) {
				int i = 0;
				for (SelectableFeature selectableFeature : configurationEditor.getConfiguration().getFeatures()) {
					selectableFeature.setRecommendationValue((int) Math.floor(rec[i++] * 100));
				}
			}
		}

		final IConfigJob<?> job = configurationEditor.getConfiguration().getPropagator().getJobWrapper().findOpenClauses(manualFeatureList);

		job.addJobFinishedListener(new JobFinishListener() {
			@SuppressWarnings("unchecked")
			@Override
			public void jobFinished(IJob finishedJob, boolean success) {
				final IConfigJob<List<Node>> job = ((IConfigJob<List<Node>>) finishedJob);
				maxGroup = job.getResults().size();
				for (final SelectableFeature feature : manualFeatureList) {
					final TreeItem item = itemMap.get(feature);
					if (item != null) {
						currentDisplay.asyncExec(new Runnable() {
							@Override
							public void run() {
								switch (feature.getRecommended()) {
								case SELECTED:
									item.setFont(treeItemSpecialFont);
									item.setForeground(green);
									item.setText(getValueText(feature) + feature.getName() + getGroupText(feature));
									break;
								case UNSELECTED:
									item.setFont(treeItemSpecialFont);
									item.setForeground(blue);
									item.setText(getValueText(feature) + feature.getName() + getGroupText(feature));
									break;
								case UNDEFINED:
									item.setFont(treeItemStandardFont);
									item.setForeground(null);
									item.setText(feature.getName());
									break;
								}
							}

							private String getGroupText(SelectableFeature feature) {
								if (!useGroups) {
									return "";
								}
								final int groupAbs = feature.getOpenClauseAbsolute();
								final int groupRel = feature.getOpenClauseRelative() + 1;
								final StringBuilder sb = new StringBuilder();

								sb.append(" | ");
								sb.append(groupRel);
								sb.append("/");
								sb.append(maxGroup);
								sb.append(" (");
								sb.append(groupAbs);
								sb.append(")");

								return sb.toString();
							}

							private String getValueText(SelectableFeature feature) {
								if (!useRecommendation) {
									return "";
								}
								final int value = feature.getRecommendationValue();
								final StringBuilder sb = new StringBuilder();

								// sb.append(value);
								if (value < 0) {
									sb.append("_____");
								} else if (value < 20) {
									sb.append("+____");
								} else if (value < 40) {
									sb.append("++___ ");
								} else if (value < 60) {
									sb.append("+++__");
								} else if (value < 80) {
									sb.append("++++_");
								} else {
									sb.append("+++++");
								}
								sb.append(" ");

								return sb.toString();
							}
						});
					}
				}
			}
		});
		if ((autoExpand & AUTOEXPAND_GROUP) > 0) {
			job.addJobFinishedListener(new JobFinishListener() {
				@Override
				public void jobFinished(IJob finishedJob, boolean success) {
					currentDisplay.asyncExec(new Runnable() {
						@Override
						public void run() {
							curGroup = 1;
							autoExpand();
						}
					});
				}
			});
		}
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
					autoExpand(currentDisplay);
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

	protected final void walkTree(final Functional.IBinaryFunction<TreeItem, SelectableFeature, Void> perNodeFunction,
			final Functional.IFunction<Void, Void> callbackIfDone) {
		AsyncTree.traverse(itemMap, tree.getItem(0), perNodeFunction, callbackIfDone);
	}

	private void buildTree(final TreeItem node, final TreeElement[] children, final Functional.IFunction<Void, Void> callbackIfDone) {
		AsyncTree.build(itemMap, node, children, callbackIfDone);
	}

	@Override
	public boolean matches(TreeItem element, String searchString) {
		final Object data = element.getData();
		if (data instanceof SelectableFeature) {
			final SelectableFeature feature = (SelectableFeature) data;
			if (searchString.startsWith("*")) {
				return feature.getName().toLowerCase().contains(searchString.substring(1).toLowerCase());
			} else {
				return feature.getName().toLowerCase().startsWith(searchString.toLowerCase());
			}
		}
		return false;
	}

	@Override
	public Iterator<TreeItem> createIterator() {
		return new UITreeIterator(tree);
	}

	@Override
	public void found(TreeItem searchResult) {
		tree.showItem(searchResult);
		tree.setSelection(searchResult);
	}

}
