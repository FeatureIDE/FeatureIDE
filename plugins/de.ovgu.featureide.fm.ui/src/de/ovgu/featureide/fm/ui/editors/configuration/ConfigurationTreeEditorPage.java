/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ArmEvent;
import org.eclipse.swt.events.ArmListener;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.events.MenuEvent;
import org.eclipse.swt.events.MenuListener;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseMoveListener;
import org.eclipse.swt.events.MouseTrackListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;
import org.eclipse.swt.widgets.ToolTip;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;
import org.prop4j.Node;
import org.prop4j.NodeWriter;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationMatrix;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.config.AutomaticSelectionExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.config.ConfigurationExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.explanations.fm.DeadFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FalseOptionalFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IBinaryFunction;
import de.ovgu.featureide.fm.core.functional.Functional.IConsumer;
import de.ovgu.featureide.fm.core.functional.Functional.IFunction;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.IJob.JobStatus;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.JobStartingStrategy;
import de.ovgu.featureide.fm.core.job.JobToken;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.configuration.IConfigurationEditor.EXPAND_ALGORITHM;
import de.ovgu.featureide.fm.ui.utils.ISearchable;
import de.ovgu.featureide.fm.ui.utils.SearchField;
import de.ovgu.featureide.fm.ui.utils.UITreeIterator;

/**
 * Basic class with some default methods for configuration editor pages.
 *
 * @author Jens Meinicke
 */
public abstract class ConfigurationTreeEditorPage extends EditorPart implements IConfigurationEditorPage, ISearchable<TreeItem> {

	private static final String EXPAND_DIRECT_CHILDREN_TOOL_TIP = "Expands The Direct Children Of The Selected Feature";
	private static final String EXPAND_DIRECT_CHILDREN = "Expand Direct Children";

	private static final String SHOWS_NEXT_OPEN_CLAUSE_AND_EXPANDS_ALL_SELECTIONS_TOOL_TIP = "Shows Next Open Clause And Expands All Selections";
	private static final String SHOW_NEXT_OPEN_CLAUSE_AND_EXPAND_ALL_SELECTIONS = "Show Next Open Clause And Expand All Selections";

	private static final String SHOW_PREVIOUS_OPEN_CLAUSE = "Show Previous Open Clause";
	private static final String SHOW_NEXT_OPEN_CLAUSE = "Show Next Open Clause";
	private static final String SHOW_NEXT_OPEN_CLAUSE_TOOL_TIP = "Automatically Shows Next Open Clause";

	private static final String EXPAND_ALL_SELECTIONS_TOOL_TIP = "Expands All Items With Selections";
	private static final String EXPAND_ALL_SELECTIONS = "Expand All Selections";

	private static final String NO_AUTOMATIC_EXPAND_TOOL_TIP = "Does Not Expand Automatically";
	private static final String NO_AUTOMATIC_EXPAND = "No Automatic Expand";

	protected static final Color gray = new Color(null, 140, 140, 140);
	protected static final Color green = new Color(null, 0, 140, 0);
	protected static final Color blue = new Color(null, 0, 0, 200);
	protected static final Color red = new Color(null, 240, 0, 0);

	protected static final Font treeItemStandardFont = new Font(null, ARIAL, 8, SWT.NORMAL);
	protected static final Font treeItemSpecialFont = new Font(null, ARIAL, 8, SWT.BOLD);

	private static final Image IMAGE_EXPAND = FMUIPlugin.getDefault().getImageDescriptor("icons/expand.gif").createImage();
	private static final Image IMAGE_COLLAPSE = FMUIPlugin.getDefault().getImageDescriptor("icons/collapse.gif").createImage();
	private static final Image IMAGE_AUTOEXPAND_GROUP = FMUIPlugin.getDefault().getImageDescriptor("icons/tree02.png").createImage();
	private static final Image IMAGE_NEXT = FMUIPlugin.getDefault().getImageDescriptor("icons/arrow_down.png").createImage();
	private static final Image IMAGE_PREVIOUS = FMUIPlugin.getDefault().getImageDescriptor("icons/arrow_up.png").createImage();
	private static final Image IMAGE_EXPORT_AS = FMUIPlugin.getDefault().getImageDescriptor("icons/export_wiz.gif").createImage();

	private static final int MAX_TOOLTIP_ELEMENT_LENGTH = 500;

	private final HashSet<SelectableFeature> invalidFeatures = new HashSet<>();
	protected final HashSet<SelectableFeature> updateFeatures = new HashSet<>();

	/** Generates explanations for automatic selections. */
	private final AutomaticSelectionExplanationCreator automaticSelectionExplanationCreator =
		ConfigurationExplanationCreatorFactory.getDefault().getAutomaticSelectionExplanationCreator();
	/** Generates explanations for dead features. */
	private final DeadFeatureExplanationCreator deadFeatureExplanationCreator =
		FeatureModelExplanationCreatorFactory.getDefault().getDeadFeatureExplanationCreator();
	/** Generates explanations for false-optional features. */
	private final FalseOptionalFeatureExplanationCreator falseOptionalFeatureExplanationCreator =
		FeatureModelExplanationCreatorFactory.getDefault().getFalseOptionalFeatureExplanationCreator();

	protected IConfigurationEditor configurationEditor = null;

	protected boolean dirty = false;

	protected int curGroup = 0;
	protected int curSearchIndex = 0;
	protected int maxGroup = 0;
	protected boolean useGroups = false;
	protected boolean useRecommendation = false;

	protected Tree tree;

	private int index;

	private Label infoLabel;

	protected final HashMap<SelectableFeature, TreeItem> itemMap = new HashMap<>();

	protected final JobToken infoLabelToken = LongRunningWrapper.createToken(JobStartingStrategy.CANCEL_WAIT_ONE);
	protected final JobToken updateToken = LongRunningWrapper.createToken(JobStartingStrategy.CANCEL_WAIT_ONE);
	protected final JobToken coloringToken = LongRunningWrapper.createToken(JobStartingStrategy.CANCEL_WAIT_ONE);

	/**
	 * The item the toolTip belongs to.
	 */
	protected TreeItem tipItem;
	/**
	 * A tooltip the displays information about the current feature.
	 */
	private ToolTip toolTip = null;

	private Menu menu;
	private ToolItem dropDownMenu;

	public void setDirty() {
		if (!dirty) {
			dirty = true;
			firePropertyChange(PROP_DIRTY);
		}
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
	public void propertyChange(FeatureIDEEvent evt) {
		if (evt != null) {
			if (evt.getSource() instanceof IFeatureModel) {
				switch (evt.getEventType()) {
				case MODEL_DATA_SAVED:
				case MODEL_DATA_OVERRIDDEN:
					refreshPage();
					break;
				default:
					break;
				}
			} else if (evt.getSource() instanceof Configuration) {
				switch (evt.getEventType()) {
				case MODEL_DATA_SAVED:
					dirty = false;
					break;
				case MODEL_DATA_OVERRIDDEN:
					refreshPage();
					setDirty();
					break;
				default:
					break;
				}
			}
		}
	}

	protected final void refreshPage() {
		// if (configurationEditor.isAutoSelectFeatures()) {
		// autoSelectButton.setEnabled(true);
		// }
		// autoSelectButton.setSelection(configurationEditor.isAutoSelectFeatures());
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
		gridData.horizontalAlignment = SWT.LEFT;
		gridData.grabExcessHorizontalSpace = true;
		gridData.verticalAlignment = SWT.CENTER;
		gridData.minimumWidth = 250;
		gridData.widthHint = 300;
		infoLabel = new Label(compositeTop, SWT.NONE);
		infoLabel.setLayoutData(gridData);
		if (configurationEditor.hasValidFeatureModel()) {
			updateInfoLabel(Display.getCurrent());
		}

		new SearchField<>(compositeTop, this);

		gridData = new GridData();
		gridData.horizontalAlignment = SWT.RIGHT;
		gridData.verticalAlignment = SWT.CENTER;
		gridData.grabExcessHorizontalSpace = false;
		final ToolBar toolbar = new ToolBar(compositeTop, SWT.FLAT | SWT.WRAP | SWT.RIGHT);
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
			public void widgetDefaultSelected(SelectionEvent e) {}
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
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		dropDownMenu = new ToolItem(toolbar, SWT.DROP_DOWN);
		dropDownMenu.setImage(IMAGE_AUTOEXPAND_GROUP);
		dropDownMenu.setToolTipText("Choose Expand Algorithm");

		menu = new Menu(toolbar.getShell(), SWT.POP_UP);
		dropDownMenu.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				final Rectangle bounds = dropDownMenu.getBounds();
				final Point point = toolbar.toDisplay(bounds.x, bounds.y + bounds.height);
				menu.setLocation(point);
				menu.setVisible(true);
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		createMenu(NO_AUTOMATIC_EXPAND, NO_AUTOMATIC_EXPAND_TOOL_TIP, EXPAND_ALGORITHM.DEFUALT).setSelection(true);
		createMenu(EXPAND_ALL_SELECTIONS, EXPAND_ALL_SELECTIONS_TOOL_TIP, EXPAND_ALGORITHM.PARENT);
		createMenu(SHOW_NEXT_OPEN_CLAUSE, SHOW_NEXT_OPEN_CLAUSE_TOOL_TIP, EXPAND_ALGORITHM.OPEN_CLAUSE);
		createMenu(SHOW_NEXT_OPEN_CLAUSE_AND_EXPAND_ALL_SELECTIONS, SHOWS_NEXT_OPEN_CLAUSE_AND_EXPANDS_ALL_SELECTIONS_TOOL_TIP, EXPAND_ALGORITHM.PARENT_CLAUSE);
		createMenu(EXPAND_DIRECT_CHILDREN, EXPAND_DIRECT_CHILDREN_TOOL_TIP, EXPAND_ALGORITHM.CHILDREN);

		new ToolItem(toolbar, SWT.SEPARATOR);

		item = new ToolItem(toolbar, SWT.PUSH);
		item.setImage(IMAGE_NEXT);
		item.setToolTipText(SHOW_NEXT_OPEN_CLAUSE);
		item.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				if (curGroup < maxGroup) {
					curGroup++;
					expandToOpenClause();
				} else {
					curGroup = maxGroup;
					expandToOpenClause();
				}
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		item = new ToolItem(toolbar, SWT.PUSH);
		item.setImage(IMAGE_PREVIOUS);
		item.setToolTipText(SHOW_PREVIOUS_OPEN_CLAUSE);
		item.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				if (curGroup <= 0) {
					curGroup = 0;
					expandToOpenClause();
				} else if (curGroup > 0) {
					curGroup--;
					expandToOpenClause();
				}
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		new ToolItem(toolbar, SWT.SEPARATOR);

		item = new ToolItem(toolbar, SWT.PUSH);
		item.setImage(IMAGE_EXPORT_AS);
		item.setToolTipText("Export Configuration");
		item.setText("Export As...");
		item.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				ConfigurationExporter.exportAs(configurationEditor.getConfiguration());
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
					final TreeItem item = (TreeItem) event.item;
					if (item.getData() instanceof SelectableFeature) {
						final SelectableFeature selectableFeature = (SelectableFeature) item.getData();
						final IFeature feature = selectableFeature.getFeature();
						final FeatureColor color = FeatureColorManager.getColor(feature);
						if (color != FeatureColor.NO_COLOR) {
							item.setBackground(new Color(null, ColorPalette.getRGB(color.getValue(), 0.5f)));
						}
					}
				}
			}
		});
		tree.addMouseMoveListener(new MouseMoveListener() {

			@Override
			public void mouseMove(MouseEvent e) {
				final TreeItem item = tree.getItem(new Point(e.x, e.y));
				boolean changed = false;
				if ((item == null) || (item != tipItem)) {
					tipItem = item;
					changed = true;
				}

				if (changed) {
					disposeTooltip();
					if (item != null) {
						createTooltip(item, e);
					}
				}
			}
		});

		tree.addMouseTrackListener(new MouseTrackListener() {
			@Override
			public void mouseEnter(MouseEvent e) {}

			@Override
			public void mouseExit(MouseEvent e) {
				tipItem = null;
				disposeTooltip();
			}

			@Override
			public void mouseHover(MouseEvent e) {}
		});
	}

	private MenuItem createMenu(String text, final String toolTipText, final EXPAND_ALGORITHM algorithm) {
		final MenuItem menuItem = new MenuItem(menu, SWT.RADIO);
		menuItem.setText(text);
		menuItem.addDisposeListener(new DisposeListener() {

			@Override
			public void widgetDisposed(DisposeEvent e) {
				disposeTooltip();
			}
		});
		menu.addMenuListener(new MenuListener() {

			@Override
			public void menuShown(MenuEvent e) {}

			@Override
			public void menuHidden(MenuEvent e) {
				disposeTooltip();
			}
		});
		menuItem.addArmListener(new ArmListener() {

			@Override
			public void widgetArmed(ArmEvent e) {
				final Point cursorLocation = menu.getShell().getDisplay().getCursorLocation();
				newToolTip(menu.getShell(), toolTipText, true, cursorLocation.x + 20, cursorLocation.y + 10);
			}
		});
		menuItem.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				if (configurationEditor.getExpandAlgorithm() != algorithm) {
					configurationEditor.setExpandAlgorithm(algorithm);
					curGroup = 0;
					autoExpand();
				} else {
					configurationEditor.setExpandAlgorithm(EXPAND_ALGORITHM.DEFUALT);
				}
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		return menuItem;
	}

	protected abstract void createUITree(Composite parent);

	protected void updateInfoLabel(final Display display) {
		if (display == null) {
			infoLabel.setText(CALCULATING____);
			infoLabel.setForeground(null);
			return;
		}
		final boolean valid = configurationEditor.getConfiguration().isValid();
		if (configurationEditor.getConfiguration().getPropagator() == null) {
			return;
		}
		final IRunner<Long> job = LongRunningWrapper.getRunner(configurationEditor.getConfiguration().getPropagator().number(250, false));
		job.addJobFinishedListener(new JobFinishListener<Long>() {

			@Override
			public void jobFinished(IJob<Long> finishedJob) {
				final StringBuilder sb = new StringBuilder();
				sb.append(valid ? VALID_COMMA_ : INVALID_COMMA_);

				final Long number = finishedJob.getResults();
				if (number != null) {
					if (number < 0) {
						sb.append(MORE_THAN);
						sb.append(-1 - number);
					} else {
						sb.append(number);
					}
					sb.append(POSSIBLE_CONFIGURATIONS);

					if ((number == 0) && !configurationEditor.isAutoSelectFeatures()) {
						sb.append(" - Autoselect not possible!");
					}
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
		LongRunningWrapper.startJob(infoLabelToken, job);
	}

	@Override
	public void setFocus() {}

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
			} catch (final TimeoutException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
		return true;
	}

	private void displayError(String message) {
		tree.removeAll();
		final TreeItem item = new TreeItem(tree, 1);
		item.setText(message);
		item.setImage(0, FMUIPlugin.getDefault().getWorkbench().getSharedImages().getImage(ISharedImages.IMG_OBJS_ERROR_TSK));
		item.setChecked(true);
		item.setGrayed(true);
		dirty = false;
	}

	protected void setManual(final TreeItem item, Selection manualSelection) {
		final SelectableFeature feature = (SelectableFeature) item.getData();
		if (feature.getAutomatic() == Selection.UNDEFINED) {
			configurationEditor.getConfiguration().setManual(feature, manualSelection);
			if (configurationEditor.getExpandAlgorithm() == EXPAND_ALGORITHM.CHILDREN) {
				switch (manualSelection) {
				case SELECTED:
					expandSingleChildren(item);
					break;
				case UNSELECTED:
					item.setExpanded(false);
					break;
				case UNDEFINED:
					break;
				default:
					throw new AssertionError(manualSelection);
				}
			}
			setDirty();

			if (configurationEditor.isAutoSelectFeatures()) {
				computeTree(true);
			} else {
				item.setForeground(null);
				item.setFont(treeItemStandardFont);
				refreshItem(item);
				if (configurationEditor.getConfiguration().canBeValid()) {
					invalidFeatures.clear();
				} else {
					invalidFeatures.add(feature);
				}
			}
			// updateInfoLabel();
		}
	}

	protected void changeSelection(final TreeItem item, final boolean select) {
		final Selection manualSelection = ((SelectableFeature) item.getData()).getManual();
		switch (manualSelection) {
		case SELECTED:
			setManual(item, (select) ? Selection.UNDEFINED : Selection.UNSELECTED);
			break;
		case UNSELECTED:
			setManual(item, (select) ? Selection.SELECTED : Selection.UNDEFINED);
			break;
		case UNDEFINED:
			setManual(item, (select) ? Selection.SELECTED : Selection.UNSELECTED);
			break;
		default:
			throw new AssertionError(manualSelection);
		}
	}

	private void expandSingleChildren(TreeItem item) {
		final SelectableFeature feature = (SelectableFeature) item.getData();
		if (feature.getSelection() != Selection.UNSELECTED) {
			item.setExpanded(true);
			if (feature.getChildren().length == 1) {
				expandSingleChildren(item.getItem(0));
			}
		}
	}

	protected void updateTree() {
		itemMap.clear();
		if (errorMessage()) {
			final Configuration configuration = configurationEditor.getConfiguration();
			tree.removeAll();

			final TreeItem root = new TreeItem(tree, 0);
			root.setExpanded(true);

			root.setFont(treeItemStandardFont);
			root.setForeground(null);

			root.setText(configuration.getRoot().getName());
			root.setData(configuration.getRoot());
			itemMap.put(configuration.getRoot(), root);

			buildTree(root, configuration.getRoot().getChildren(), new Functional.IFunction<Void, Void>() {

				@Override
				public Void invoke(Void t) {
					// updateInfoLabel();
					computeTree(true);
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

	/**
	 * Manually expands the tree to show the next open clause.
	 */
	private void expandToOpenClause() {
		switch (configurationEditor.getExpandAlgorithm()) {
		case PARENT_CLAUSE:
			levelExpand();
			groupExpand(false);
			break;
		default:
			groupExpand(true);
			break;
		}
	}

	/**
	 * Applies the selected expand algorithm.
	 */
	private void autoExpand() {
		final EXPAND_ALGORITHM expandAlgorithm = configurationEditor.getExpandAlgorithm();
		switch (expandAlgorithm) {
		case DEFUALT:
			break;
		case CHILDREN:
			break;
		case OPEN_CLAUSE:
			groupExpand(true);
			break;
		case PARENT:
			levelExpand();
			break;
		case PARENT_CLAUSE:
			levelExpand();
			groupExpand(false);
			break;
		default:
			throw new AssertionError("case " + expandAlgorithm + " not supported!");
		}
	}

	private boolean groupExpand(boolean collapse) {
		final LinkedList<TreeItem> groupItems = new LinkedList<>();
		final TreeItem root = tree.getItem(0);
		if (root != null) {
			searchGroupRec(root, groupItems);
			if (!groupItems.isEmpty()) {
				if (collapse) {
					collapseRec(root);
				}
				for (final TreeItem treeItem : groupItems) {
					TreeItem parent = treeItem.getParentItem();
					while (parent != null) {
						parent.setExpanded(true);
						parent = parent.getParentItem();
					}
				}
				tree.showItem(groupItems.getLast());
				tree.showItem(groupItems.getFirst());
				return true;
			} else {
				levelExpand();
			}
		}
		return false;
	}

	private void searchGroupRec(TreeItem root, LinkedList<TreeItem> groupItems) {
		final Object data = root.getData();
		if (data instanceof SelectableFeature) {
			final SelectableFeature feature = (SelectableFeature) data;
			if (feature.getOpenClauseIndexes().contains(curGroup)) {
				groupItems.add(root);
			}
		}

		final TreeItem[] items = root.getItems();
		for (final TreeItem treeItem : items) {
			searchGroupRec(treeItem, groupItems);
		}
	}

	private void collapseRec(TreeItem root) {
		root.setExpanded(false);

		final TreeItem[] items = root.getItems();
		for (final TreeItem treeItem : items) {
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
		final TreeItem[] items = root.getItems();
		for (final TreeItem treeItem : items) {
			final Object data = treeItem.getData();
			if (data instanceof SelectableFeature) {
				final SelectableFeature feature = (SelectableFeature) data;
				if ((feature.getSelection() == Selection.UNDEFINED) || (feature.getSelection() == Selection.UNSELECTED)) {
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

	protected void refreshItem(TreeItem item) {
		final Object data = item.getData();
		if (data instanceof SelectableFeature) {
			final SelectableFeature feature = (SelectableFeature) data;
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
	}

	/**
	 * Colors all features if they lead to a valid configuration if current configuration is invalid. deselect:blue, select:green
	 */
	protected IRunner<List<Node>> computeColoring(final Display currentDisplay) {
		if (!configurationEditor.isAutoSelectFeatures() || configurationEditor.getConfiguration().isValid()) {
			for (final SelectableFeature selectableFeature : configurationEditor.getConfiguration().getFeatures()) {
				selectableFeature.setRecommendationValue(-1);
				selectableFeature.clearOpenClauses();
			}
			if ((configurationEditor.getExpandAlgorithm() == EXPAND_ALGORITHM.OPEN_CLAUSE)
				|| (configurationEditor.getExpandAlgorithm() == EXPAND_ALGORITHM.PARENT_CLAUSE)) {
				autoExpand(currentDisplay);
			}
			return null;
		}

		final List<SelectableFeature> automaticFeatureList = new LinkedList<>();
		final List<SelectableFeature> manualFeatureList = new LinkedList<>();
		for (final SelectableFeature selectableFeature : configurationEditor.getConfiguration().getFeatures()) {
			if (!selectableFeature.getFeature().getStructure().hasHiddenParent()) {
				if ((selectableFeature.getAutomatic() == Selection.UNDEFINED) && !selectableFeature.getFeature().getStructure().hasHiddenParent()) {
					manualFeatureList.add(selectableFeature);
				} else {
					automaticFeatureList.add(selectableFeature);
				}
			}
		}

		currentDisplay.syncExec(new Runnable() {

			@Override
			public void run() {
				for (final SelectableFeature selectableFeature : automaticFeatureList) {
					selectableFeature.setRecommendationValue(-1);
					selectableFeature.clearOpenClauses();
					final TreeItem item = itemMap.get(selectableFeature);
					if (item != null) {
						refreshItem(item);
					}
				}
			}
		});
		curGroup = 0;

		if (useRecommendation) {
			final ConfigurationMatrix configurationMatrix = new ConfigurationMatrix(configurationEditor.getConfiguration().getFeatureModel(),
					Paths.get(configurationEditor.getFile().getParent().getLocationURI()));
			configurationMatrix.readConfigurations(configurationEditor.getFile().getName());
			configurationMatrix.calcRec(configurationEditor.getConfiguration());
			final double[] rec = configurationMatrix.getRec();
			if (rec != null) {
				int i = 0;
				for (final SelectableFeature selectableFeature : configurationEditor.getConfiguration().getFeatures()) {
					selectableFeature.setRecommendationValue((int) Math.floor(rec[i++] * 100));
				}
			}
		}

		final LongRunningMethod<List<Node>> jobs = configurationEditor.getConfiguration().getPropagator().findOpenClauses(manualFeatureList);
		final IRunner<List<Node>> job = LongRunningWrapper.getRunner(jobs, "FindClauses");

		job.addJobFinishedListener(new JobFinishListener<List<Node>>() {

			@Override
			public void jobFinished(IJob<List<Node>> finishedJob) {
				maxGroup = finishedJob.getResults().size() - 1;
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
								// TODO @Sebastian: might not work anymore
								final Node groupAbs = feature.getOpenClauses().iterator().next();
								final int groupRel = feature.getOpenClauseIndexes().iterator().next();
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
		if ((configurationEditor.getExpandAlgorithm() == EXPAND_ALGORITHM.OPEN_CLAUSE)
			|| (configurationEditor.getExpandAlgorithm() == EXPAND_ALGORITHM.PARENT_CLAUSE)) {
			job.addJobFinishedListener(new JobFinishListener<List<Node>>() {

				@Override
				public void jobFinished(IJob<List<Node>> finishedJob) {
					currentDisplay.asyncExec(new Runnable() {

						@Override
						public void run() {
							curGroup = 0;
							autoExpand();
						}
					});
				}
			});
		}
		return job;
	}

	protected IRunner<Void> computeFeatures(final boolean redundantManual, final Display currentDisplay) {
		if (!configurationEditor.isAutoSelectFeatures()) {
			return null;
		}
		final TreeItem topItem = tree.getTopItem();
		final SelectableFeature feature = (SelectableFeature) (topItem.getData());
		final LongRunningMethod<Void> update = configurationEditor.getConfiguration().getPropagator().update(redundantManual, Arrays.asList(feature));
		final IRunner<Void> job = LongRunningWrapper.getRunner(update);
		job.setIntermediateFunction(new IConsumer<Object>() {

			@Override
			public void invoke(Object t) {
				if (t instanceof SelectableFeature) {
					final SelectableFeature feature = (SelectableFeature) t;
					final TreeItem item = itemMap.get(feature);
					if (item == null) {
						return;
					}
					currentDisplay.asyncExec(new Runnable() {

						@Override
						public void run() {
							updateFeatures.remove(feature);
							refreshItem(item);
						}
					});
				}
			}
		});
		return job;
	}

	/**
	 * Returns an explanation for the given feature selection. Generates it first if necessary.
	 *
	 * @param featureSelection a feature selection; not null
	 * @return an explanation for the given feature selection; null if none could be found
	 */
	public Explanation<?> getExplanation(SelectableFeature featureSelection) {
		switch (featureSelection.getAutomatic()) {
		case SELECTED:
		case UNSELECTED:
			return getAutomaticSelectionExplanation(featureSelection);
		case UNDEFINED:
			break;
		default:
			throw new IllegalStateException("Unknown feature selection state");
		}
		return null;
	}

	/**
	 * Returns an explanation why the given feature is automatically selected or unselected. Generates it first if necessary.
	 *
	 * @param automaticSelection an automatically selected feature; not null
	 * @return an explanation why the given feature is automatically selected or unselected; null if none could be found
	 */
	public Explanation<?> getAutomaticSelectionExplanation(SelectableFeature automaticSelection) {
		// TODO Remember previously generated explanations.
		return createAutomaticSelectionExplanation(automaticSelection);
	}

	/**
	 * Returns a new explanation for the given automatic selection.
	 *
	 * @param automaticSelection the automatic selection
	 * @return a new explanation for the given automatic selection; null if none could be generated
	 */
	protected Explanation<?> createAutomaticSelectionExplanation(SelectableFeature automaticSelection) {
		final Configuration config = configurationEditor.getConfiguration();
		if (config == null) {
			return null;
		}
		final IFeatureModel fm = config.getFeatureModel();
		if (fm == null) {
			return null;
		}
		switch (automaticSelection.getFeature().getProperty().getFeatureStatus()) {
		case DEAD:
			deadFeatureExplanationCreator.setFeatureModel(fm);
			deadFeatureExplanationCreator.setSubject(automaticSelection.getFeature());
			return deadFeatureExplanationCreator.getExplanation();
		case FALSE_OPTIONAL:
			falseOptionalFeatureExplanationCreator.setFeatureModel(fm);
			falseOptionalFeatureExplanationCreator.setSubject(automaticSelection.getFeature());
			return falseOptionalFeatureExplanationCreator.getExplanation();
		default:
			break;
		}
		automaticSelectionExplanationCreator.setConfiguration(config);
		automaticSelectionExplanationCreator.setSubject(automaticSelection);
		return automaticSelectionExplanationCreator.getExplanation();
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

		final IRunner<Void> updateJob = computeFeatures(redundantManual, currentDisplay);
		if (updateJob != null) {
			updateJob.addJobFinishedListener(new JobFinishListener<Void>() {

				@Override
				public void jobFinished(IJob<Void> finishedJob) {
					if (finishedJob.getStatus() == JobStatus.OK) {
						updateInfoLabel(currentDisplay);
						autoExpand(currentDisplay);

						LongRunningWrapper.startJob(coloringToken, computeColoring(currentDisplay));
						// XXX Prevents configuration files from being deleted (read/write conflict)
//						if (configurationEditor instanceof ConfigurationEditor) {
//							final ConfigurationManager manager = ((ConfigurationEditor) configurationEditor).getConfigurationManager();
//							// Get current configuration
//							final String source = manager.getFormat().getInstance().write(configurationEditor.getConfiguration());
//							// Cast is necessary, don't remove
//							final IFile document = (IFile) getEditorInput().getAdapter(IFile.class);
//
//							byte[] content;
//							try {
//								content = new byte[document.getContents().available()];
//								document.getContents().read(content);
//								if (!source.equals(new String(content))) {
//									setDirty();
//								}
//							} catch (final IOException e) {
//								FMUIPlugin.getDefault().logError(e);
//							} catch (final CoreException e) {
//								FMUIPlugin.getDefault().logError(e);
//							}
//						}
					}
				}
			});

			updateFeatures.clear();
			walkTree(new IBinaryFunction<TreeItem, SelectableFeature, Void>() {

				@Override
				public Void invoke(TreeItem item, SelectableFeature feature) {
					// lockItem(item);
					updateFeatures.add(feature);
					return null;
				}
			}, new IFunction<Void, Void>() {

				@Override
				public Void invoke(Void t) {
					LongRunningWrapper.startJob(updateToken, updateJob);
					return null;
				}
			});
		}
	}

	/**
	 * Applies the given functions to the tree.
	 *
	 * @param perNodeFunction The function that is applied to all nodes of the tree.
	 * @param callbackIfDone A functions that executed once after the tree is completely traversed has finished.
	 */
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

	@Override
	public boolean allowPageChange(int newPageIndex) {
		return true;
	}

	protected void createTooltip(TreeItem item, MouseEvent e) {
		final Object data = item.getData();

		if (data instanceof SelectableFeature) {
			final SelectableFeature feature = (SelectableFeature) item.getData();
			final String relConst = FeatureUtils.getRelevantConstraintsString(feature.getFeature());
			final String describ = feature.getFeature().getProperty().getDescription();
			final StringBuilder sb = new StringBuilder();

			if (!describ.isEmpty()) {
				addElement(sb, "Description:", describ);
			}
			if (!relConst.isEmpty()) {
				addElement(sb, "Constraints:", relConst);
			}
			final Collection<Node> openClauses = feature.getOpenClauses();
			if (!openClauses.isEmpty()) {
				final StringBuilder elementBuilder = new StringBuilder();
				for (final Node clause : openClauses) {
					elementBuilder.append(clause.toString(NodeWriter.logicalSymbols)).append('\n');
				}
				addElement(sb, "Open Clauses:", elementBuilder.toString());
			}

			// Print the explanation.
			final Explanation<?> explanation = getExplanation(feature);
			if ((explanation != null) && (explanation.getReasons() != null) && !explanation.getReasons().isEmpty()) {
				addElement(sb, null, explanation.getWriter().getString());
			}

			if (sb.length() > 0) {
				tipItem = item;
				final Rectangle bounds = item.getBounds();
				final Point displayPoint = tree.toDisplay(new Point(bounds.x + bounds.width + 12, bounds.y));
				newToolTip(tree.getShell(), sb, false, displayPoint.x, displayPoint.y);
			}
		}
	}

	private void addElement(final StringBuilder sb, final String header, final String element) {
		if (sb.length() > 0) {
			sb.append("\n\n");
		}
		if (header != null) {
			sb.append(header);
			sb.append("\n");
		}
		sb.append((element.length() <= MAX_TOOLTIP_ELEMENT_LENGTH) ? element : element.substring(0, MAX_TOOLTIP_ELEMENT_LENGTH) + "\n[...]");
	}

	private void newToolTip(Shell shell, CharSequence toolTipText, boolean autoHide, int x, int y) {
		disposeTooltip();
		toolTip = new ToolTip(shell, SWT.NONE);
		toolTip.setMessage(toolTipText.toString());
		toolTip.setLocation(x, y);
		toolTip.setAutoHide(autoHide);
		toolTip.setVisible(true);
	}

	@Override
	public void dispose() {
		disposeTooltip();
		super.dispose();
	}

	protected void disposeTooltip() {
		if (toolTip != null) {
			if (!toolTip.isDisposed()) {
				toolTip.setVisible(false);
				toolTip.dispose();
			}
			toolTip = null;
		}
	}

}
