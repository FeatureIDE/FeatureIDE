/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
import static de.ovgu.featureide.fm.core.localization.StringTable.CONFLICTING_COMMA_;
import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_COMMA_;
import static de.ovgu.featureide.fm.core.localization.StringTable.MORE_THAN;
import static de.ovgu.featureide.fm.core.localization.StringTable.POSSIBLE_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.THERE_IS_NO_FEATURE_MODEL_CORRESPONDING_TO_THIS_CONFIGURATION_COMMA__REOPEN_THE_EDITOR_AND_SELECT_ONE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_FEATURE_MODEL_FOR_THIS_PROJECT_IS_VOID_COMMA__I_E__COMMA__THERE_IS_NO_VALID_CONFIGURATION__YOU_NEED_TO_CORRECT_THE_FEATURE_MODEL_BEFORE_YOU_CAN_CREATE_OR_EDIT_CONFIGURATIONS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_GIVEN_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.VALID_COMMA_;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.function.Consumer;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.resource.ImageDescriptor;
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
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureStatus;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Nodes;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationMatrix;
import de.ovgu.featureide.fm.core.configuration.ConfigurationPropagator;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.config.AutomaticSelectionExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.config.ConfigurationExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.explanations.fm.DeadFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FalseOptionalFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.JobStartingStrategy;
import de.ovgu.featureide.fm.core.job.JobToken;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.util.RunnerSequence;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.configuration.IConfigurationEditor.ExpandAlgorithm;
import de.ovgu.featureide.fm.ui.utils.ISearchable;
import de.ovgu.featureide.fm.ui.utils.SearchField;
import de.ovgu.featureide.fm.ui.utils.UITreeIterator;

/**
 * Basic class with some default methods for configuration editor pages.
 *
 * @author Jens Meinicke
 */
public abstract class ConfigurationTreeEditorPage extends EditorPart implements IConfigurationEditorPage, ISearchable<TreeItem> {

	private static final String EXPAND_CURRENT_SELECTION_TOOL_TIP = "Expands/Collapses Only The Currently Selected Item";
	private static final String EXPAND_CURRENT_SELECTION = "Expand Current Selection";

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
	private static final Image IMAGE_RESOLVE = FMUIPlugin.getDefault().getImageDescriptor("icons/synch_toc_nav.gif").createImage();
	protected static final ImageDescriptor IMAGE_EXPORT_AS = FMUIPlugin.getDefault().getImageDescriptor("icons/export_wiz.gif");

	private static final int MAX_TOOLTIP_ELEMENT_LENGTH = 500;

	private static enum UpdateStrategy {
		BUILD, UPDATE, RESOLVE
	}

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
	private ToolItem resolveButton;

	protected final LinkedHashMap<SelectableFeature, TreeItem> itemMap = new LinkedHashMap<>();

	protected final JobToken updateToken = LongRunningWrapper.createToken(JobStartingStrategy.CANCEL_WAIT_ONE);

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
				case MODEL_DATA_OVERWRITTEN:
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
				case MODEL_DATA_OVERWRITTEN:
					refreshPage();
					setDirty();
					break;
				default:
					break;
				}
			} else {
				if (evt.getEventType() == EventType.CONFIGURABLE_ATTRIBUTE_CHANGED) {
					refreshPage();
					setDirty();
				}
			}
		}
	}

	protected final void refreshPage() {
		itemMap.clear();

		if (configurationEditor.hasValidFeatureModel()) {

			final ConfigurationManager configurationManager = configurationEditor.getConfigurationManager();
			if (configurationManager != null) {
				final FeatureModelFormula persistentFormula = configurationEditor.getFeatureModelManager().getPersistentFormula();
				final FeatureModelAnalyzer fmAnalyzer = persistentFormula.getAnalyzer();
				if (fmAnalyzer.isValid(null)) {
					computeTree(UpdateStrategy.BUILD);
				} else {
					displayError(
							THE_FEATURE_MODEL_FOR_THIS_PROJECT_IS_VOID_COMMA__I_E__COMMA__THERE_IS_NO_VALID_CONFIGURATION__YOU_NEED_TO_CORRECT_THE_FEATURE_MODEL_BEFORE_YOU_CAN_CREATE_OR_EDIT_CONFIGURATIONS_);

				}
			} else {

				if (configurationEditor.isReadFeatureModelError()) {
					displayError(THERE_IS_NO_FEATURE_MODEL_CORRESPONDING_TO_THIS_CONFIGURATION_COMMA__REOPEN_THE_EDITOR_AND_SELECT_ONE_);
				} else {
					displayError(AN_UNKNOWN_ERROR_OCCURRED_);
				}
			}
		} else {
			displayError(THE_GIVEN_FEATURE_MODEL + " is invalid.");
		}
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

		new SearchField<>(compositeTop, this);

		gridData = new GridData();
		gridData.horizontalAlignment = SWT.RIGHT;
		gridData.verticalAlignment = SWT.CENTER;
		gridData.grabExcessHorizontalSpace = false;
		final ToolBar toolbar = new ToolBar(compositeTop, SWT.FLAT | SWT.WRAP | SWT.RIGHT);
		toolbar.setLayoutData(gridData);

		new ToolItem(toolbar, SWT.SEPARATOR);

		resolveButton = new ToolItem(toolbar, SWT.PUSH);
		resolveButton.setImage(IMAGE_RESOLVE);
		resolveButton.setToolTipText("Automatically Resolve Conflicting Selections");
		resolveButton.setEnabled(false);
		resolveButton.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				computeTree(UpdateStrategy.RESOLVE);
				setResolveButton(false);
				setDirty();
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		new ToolItem(toolbar, SWT.SEPARATOR);

		ToolItem item = new ToolItem(toolbar, SWT.PUSH);
		item.setImage(IMAGE_COLLAPSE);
		item.setToolTipText("Collapse All Features");
		item.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				expandItems(itemMap.values(), false);
				expandRoot();
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
				expandItems(itemMap.values(), true);
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

		createMenu(NO_AUTOMATIC_EXPAND, NO_AUTOMATIC_EXPAND_TOOL_TIP, ExpandAlgorithm.NONE);
		final MenuItem defaultItem = createMenu(EXPAND_ALL_SELECTIONS, EXPAND_ALL_SELECTIONS_TOOL_TIP, ExpandAlgorithm.ALL_SELECTED);
		createMenu(EXPAND_CURRENT_SELECTION, EXPAND_CURRENT_SELECTION_TOOL_TIP, ExpandAlgorithm.CURRENTLY_SELECTED);
		createMenu(SHOW_NEXT_OPEN_CLAUSE, SHOW_NEXT_OPEN_CLAUSE_TOOL_TIP, ExpandAlgorithm.OPEN_CLAUSES);
		createMenu(SHOW_NEXT_OPEN_CLAUSE_AND_EXPAND_ALL_SELECTIONS, SHOWS_NEXT_OPEN_CLAUSE_AND_EXPANDS_ALL_SELECTIONS_TOOL_TIP,
				ExpandAlgorithm.ALL_SELECTED_OPEN_CLAUSE);

		menu.setDefaultItem(defaultItem);
		defaultItem.setSelection(true);

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

	private MenuItem createMenu(String text, final String toolTipText, final ExpandAlgorithm algorithm) {
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
					if (useGroups) {
						curGroup = 0;
					}
					autoExpand();
				}
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
				if (useGroups) {
					curGroup = 0;
				}
				configurationEditor.setExpandAlgorithm(ExpandAlgorithm.ALL_SELECTED);
			}
		});
		return menuItem;
	}

	protected abstract void createUITree(Composite parent);

	protected Void resetSnapshot(ConfigurationManager manager) {
		manager.resetSnapshot();
		return null;
	}

	protected Void updateInfoLabel(final Display display, ConfigurationPropagator propagator) {
		final boolean valid = LongRunningWrapper.runMethod(propagator.isValid());
		final boolean conflicting = !valid && !LongRunningWrapper.runMethod(propagator.canBeValid());

		final StringBuilder sb = new StringBuilder();
		if (conflicting) {
			sb.append(CONFLICTING_COMMA_);
			sb.append("0");
			sb.append(POSSIBLE_CONFIGURATIONS);
			display.asyncExec(() -> setResolveButton(true));
		} else {
			final long number = conflicting ? 0 : LongRunningWrapper.runMethod(propagator.number(250));
			sb.append(valid ? VALID_COMMA_ : INVALID_COMMA_);
			if (number < 0) {
				sb.append(MORE_THAN);
				sb.append(-1 - number);
			} else {
				sb.append(number);
			}
			sb.append(POSSIBLE_CONFIGURATIONS);
			display.asyncExec(() -> setResolveButton(false));
		}
		final String message = sb.toString();
		final Color color = valid ? blue : red;
		display.syncExec(() -> setInfoLabel(message, color));
		return null;
	}

	private void setInfoLabel(String message, Color color) {
		if (!infoLabel.isDisposed()) {
			infoLabel.setText(message);
			infoLabel.setForeground(color);
		}
	}

	private void setResolveButton(boolean enable) {
		if (!resolveButton.isDisposed()) {
			resolveButton.setEnabled(enable);
		}
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
		if (configurationEditor.getConfigurationManager() == null) {
			if (configurationEditor.isReadFeatureModelError()) {
				displayError(THERE_IS_NO_FEATURE_MODEL_CORRESPONDING_TO_THIS_CONFIGURATION_COMMA__REOPEN_THE_EDITOR_AND_SELECT_ONE_);
			} else {
				displayError(AN_UNKNOWN_ERROR_OCCURRED_);
			}
			return false;
		} else {
			final FeatureModelAnalyzer analyzer = configurationEditor.getFeatureModelManager().getPersistentFormula().getAnalyzer();
			if (!analyzer.isValid(null)) {
				displayError(
						THE_FEATURE_MODEL_FOR_THIS_PROJECT_IS_VOID_COMMA__I_E__COMMA__THERE_IS_NO_VALID_CONFIGURATION__YOU_NEED_TO_CORRECT_THE_FEATURE_MODEL_BEFORE_YOU_CAN_CREATE_OR_EDIT_CONFIGURATIONS_);
				return false;
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

			final ConfigurationManager configurationManager = configurationEditor.getConfigurationManager();
			if (configurationManager != null) {
				configurationManager.editObject(config -> config.setManual(feature, manualSelection), ConfigurationManager.CHANGE_MANUAL);
				if (configurationEditor.getExpandAlgorithm() == ExpandAlgorithm.CURRENTLY_SELECTED) {
					switch (manualSelection) {
					case SELECTED:
						expandRec(item);
						break;
					case UNSELECTED:
					case UNDEFINED:
						item.setExpanded(false);
						break;
					default:
						throw new AssertionError(manualSelection);
					}
				}
				setDirty();

				if (configurationEditor.isAutoSelectFeatures()) {
					computeTree(UpdateStrategy.UPDATE);
				} else {
					refreshItem(Arrays.asList(item));
					if (LongRunningWrapper.runMethod(getPropagator().canBeValid())) {
						invalidFeatures.clear();
					} else {
						invalidFeatures.add(feature);
					}
				}
			}
		}
	}

	protected ConfigurationPropagator getPropagator() {
		final ConfigurationManager configurationManager = configurationEditor.getConfigurationManager();
		final FeatureModelManager featureModelManager = configurationEditor.getFeatureModelManager();
		if ((configurationManager != null) && (featureModelManager != null)) {
			return new ConfigurationPropagator(featureModelManager.getPersistentFormula(), configurationManager.getSnapshot());
		}
		return null;
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

	private Void expandAll(Display display) {
		display.syncExec(() -> expandItems(itemMap.values(), true));
		return null;
	}

	private Void expandAuto(Display display) {
		display.syncExec(() -> autoExpand());
		return null;
	}

	private Void expandLevel(Display display) {
		display.syncExec(() -> levelExpand());
		return null;
	}

	/**
	 * Manually expands the tree to show the next open clause.
	 */
	private void expandToOpenClause() {
		switch (configurationEditor.getExpandAlgorithm()) {
		case ALL_SELECTED_OPEN_CLAUSE:
			levelExpand();
			groupExpand(false);
			break;
		default:
			groupExpand(true);
			break;
		}
	}

	private void autoExpand() {
		final ExpandAlgorithm expandAlgorithm = configurationEditor.getExpandAlgorithm();
		switch (expandAlgorithm) {
		case NONE:
			break;
		case CURRENTLY_SELECTED:
			break;
		case OPEN_CLAUSES:
			groupExpand(true);
			break;
		case ALL_SELECTED:
			levelExpand();
			break;
		case ALL_SELECTED_OPEN_CLAUSE:
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

	private void expandRoot() {
		tree.getItem(0).setExpanded(true);
	}

	private void expandItems(Collection<TreeItem> items, boolean expand) {
		for (final TreeItem treeItem : items) {
			treeItem.setExpanded(expand);
		}
	}

	private void levelExpand() {
		if (!tree.isDisposed()) {
			final TreeItem root = tree.getItem(0);
			if (root != null) {
				expandRec(root);
			}
		}
	}

	private void expandRec(TreeItem root) {
		if (root.isDisposed()) {
			return;
		}
		final Object data = root.getData();
		if (data instanceof SelectableFeature) {
			final SelectableFeature feature = (SelectableFeature) data;
			if ((feature.getSelection() == Selection.UNDEFINED) || (feature.getSelection() == Selection.UNSELECTED)) {
				root.setExpanded(false);
			} else {
				root.setExpanded(true);
				for (final TreeItem treeItem : root.getItems()) {
					expandRec(treeItem);
				}
			}
		}
	}

	protected boolean canDeselectFeatures() {
		return false;
	}

	protected void refreshItem(Collection<TreeItem> items) {
		for (final TreeItem item : items) {
			if (!item.isDisposed()) {
				final Object data = item.getData();
				if (data instanceof SelectableFeature) {
					boolean checked = false;
					boolean grayed = false;
					Color fgColor = null;
					Font font = treeItemStandardFont;
					final SelectableFeature feature = (SelectableFeature) data;
					final Selection automatic = feature.getAutomatic();
					final Selection recommended = feature.getRecommended();
					switch (automatic) {
					case SELECTED:
						checked = true;
						grayed = true;
						break;
					case UNSELECTED:
						checked = false;
						grayed = true;
						fgColor = gray;
						break;
					case UNDEFINED:
						checked = feature.getManual() == Selection.SELECTED;
						break;
					}

					final StringBuilder sb = new StringBuilder();
					if (automatic == Selection.UNDEFINED) {
						switch (recommended) {
						case SELECTED:
							font = treeItemSpecialFont;
							fgColor = green;
							break;
						case UNSELECTED:
							font = treeItemSpecialFont;
							fgColor = blue;
							break;
						case UNDEFINED:
							break;
						}
						if (recommended == Selection.UNDEFINED) {
							sb.append(feature.getName());
						} else {
							final int recommendationValue = feature.getRecommendationValue();
							if (useRecommendation && (recommendationValue >= 0)) {
								sb.append(recommendationValue);
								sb.append(" ");
							}
							sb.append(feature.getName());
							final Set<Integer> openClauseIndexes = feature.getOpenClauseIndexes();
							if (useGroups && !openClauseIndexes.isEmpty()) {
								sb.append(" (unsatisfied group ");
								sb.append(openClauseIndexes.iterator().next());
								sb.append(")");
							}
						}
					} else {
						sb.append(feature.getName());
					}
					item.setText(sb.toString());
					item.setChecked(checked);
					item.setGrayed(grayed);
					item.setFont(font);
					item.setBackground(null);
					item.setForeground(fgColor);
				}
			}
		}
	}

	private Void computeRecommendation(Configuration configuration) {
		final Path path = configurationEditor.getConfigurationManager().getPath();
		final ConfigurationMatrix configurationMatrix =
			new ConfigurationMatrix(configurationEditor.getFeatureModelManager().getPersistentFormula(), path.getParent());
		configurationMatrix.readConfigurations(path.getFileName().toString());
		configurationMatrix.calcRec(configuration);
		final double[] rec = configurationMatrix.getRec();
		if (rec != null) {
			int i = 0;
			for (final SelectableFeature selectableFeature : configuration.getFeatures()) {
				selectableFeature.setRecommendationValue((int) Math.floor(rec[i++] * 100));
			}
		}
		return null;
	}

	private void updateFeatures(final Display currentDisplay, Collection<SelectableFeature> t) {
		final ArrayList<TreeItem> itmes = new ArrayList<>();
		for (final SelectableFeature feature : t) {
			final TreeItem item = itemMap.get(feature);
			if (item != null) {
				updateFeatures.remove(feature);
				itmes.add(item);
			}
		}
		currentDisplay.asyncExec(() -> refreshItem(itmes));
	}

	private Void resetUpdateFeatures(IMonitor<Void> monitor) {
		updateFeatures.clear();
		return null;
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
		final ConfigurationManager configManager = configurationEditor.getConfigurationManager();
		if (configManager == null) {
			return null;
		}
		final IFeatureModelManager featureModelManager = configurationEditor.getFeatureModelManager();
		if (featureModelManager == null) {
			return null;
		}
		final FeatureModelFormula fm = featureModelManager.getPersistentFormula();
		final FeatureProperties featureProperties = fm.getAnalyzer().getFeatureProperties(automaticSelection.getFeature());
		if (featureProperties.hasStatus(FeatureStatus.DEAD)) {
			deadFeatureExplanationCreator.setFeatureModel(fm.getFeatureModel());
			deadFeatureExplanationCreator.setSubject(automaticSelection.getFeature());
			return deadFeatureExplanationCreator.getExplanation();
		}
		if (featureProperties.hasStatus(FeatureStatus.FALSE_OPTIONAL)) {
			falseOptionalFeatureExplanationCreator.setFeatureModel(fm.getFeatureModel());
			falseOptionalFeatureExplanationCreator.setSubject(automaticSelection.getFeature());
			return falseOptionalFeatureExplanationCreator.getExplanation();
		}
		automaticSelectionExplanationCreator.setConfiguration(configManager.getSnapshot());
		automaticSelectionExplanationCreator.setSubject(automaticSelection);
		return automaticSelectionExplanationCreator.getExplanation();
	}

	protected void computeTree(UpdateStrategy updateStrategy) {
		final Display currentDisplay = Display.getCurrent();
		final FeatureModelManager featureModelManager = configurationEditor.getFeatureModelManager();
		final ConfigurationManager configurationManager = configurationEditor.getConfigurationManager();
		if ((featureModelManager == null) || (configurationManager == null) || (currentDisplay == null)) {
			displayError(AN_UNKNOWN_ERROR_OCCURRED_);
			return;
		}

		setInfoLabel(CALCULATING____, null);

		configurationManager.editObject(config -> update(updateStrategy, currentDisplay, configurationManager, featureModelManager, config),
				ConfigurationManager.CHANGE_AUTOMATIC);
	}

	private void update(UpdateStrategy updateStrategy, final Display currentDisplay, ConfigurationManager configurationManager,
			final FeatureModelManager featureModelManager, final Configuration configuration) {
		final ConfigurationPropagator propagator = new ConfigurationPropagator(featureModelManager.getPersistentFormula(), configuration);

		final Boolean canBeValid = LongRunningWrapper.runMethod(propagator.canBeValid());
		final boolean conflicting;
		if (canBeValid == null) {
			return;
		} else {
			conflicting = !canBeValid;
		}

		final RunnerSequence sequence = new RunnerSequence();
		sequence.setIgnorePreviousJobFail(false);
		IRunner<Collection<SelectableFeature>> updateJob = null;
		switch (updateStrategy) {
		case RESOLVE:
			sequence.addJob(LongRunningWrapper.getRunner(propagator.resolve()));
			updateJob = LongRunningWrapper.getRunner(propagator.update(true));
			updateFeatures.clear();
			updateFeatures.addAll(configuration.getFeatures());
			break;
		case BUILD:
			sequence.addJob(LongRunningWrapper.getRunner(monitor -> build(configuration.getRoot(), currentDisplay)));
		case UPDATE:
			if (configurationEditor.isAutoSelectFeatures()) {
				if (conflicting) {
					updateJob = LongRunningWrapper.getRunner(propagator.resetAutomatic());
				} else {
					final TreeItem topItem = tree.getTopItem();
					if (topItem != null) {
						final List<SelectableFeature> featureOrder = Arrays.asList((SelectableFeature) (topItem.getData()));
						updateJob = LongRunningWrapper.getRunner(propagator.update(true, featureOrder));
					} else {
						updateJob = LongRunningWrapper.getRunner(propagator.update(true));
					}
				}
				updateFeatures.clear();
				updateFeatures.addAll(configuration.getFeatures());
			}
			break;
		}
		if (updateJob != null) {
			updateJob.setIntermediateFunction(t -> updateFeatures(currentDisplay, t));
			sequence.addJob(updateJob);
			sequence.addJob(LongRunningWrapper.getRunner(this::resetUpdateFeatures));
		}

		final IRunner<Collection<SelectableFeature>> coloringJob = LongRunningWrapper.getRunner(propagator.findOpenClauses());
		coloringJob.setIntermediateFunction(t -> updateFeatures(currentDisplay, t));
		sequence.addJob(coloringJob);

		if (useRecommendation) {
			sequence.addJob(LongRunningWrapper.getRunner(monitor -> computeRecommendation(configuration)));
		}
		if (useGroups) {
			curGroup = 0;
		}
		if (conflicting) {
			sequence.addJob(LongRunningWrapper.getRunner(monitor -> expandAll(currentDisplay)));
		} else {
			switch (updateStrategy) {
			case BUILD:
				sequence.addJob(LongRunningWrapper.getRunner(monitor -> expandLevel(currentDisplay)));
				break;
			case RESOLVE:
			case UPDATE:
				sequence.addJob(LongRunningWrapper.getRunner(monitor -> expandAuto(currentDisplay)));
				break;
			}
		}
		sequence.addJob(LongRunningWrapper.getRunner(monitor -> resetSnapshot(configurationManager)));
		sequence.addJob(LongRunningWrapper.getRunner(monitor -> updateInfoLabel(currentDisplay, propagator)));
		final IRunner<Boolean> runner = LongRunningWrapper.getRunner(sequence);
		runner.addJobFinishedListener((finishedJob) -> {
			currentDisplay.syncExec(() -> configurationManager.fireEvent(new FeatureIDEEvent(null, EventType.FEATURE_SELECTION_CHANGED)));
		});
		LongRunningWrapper.startJob(updateToken, runner);
	}

	@Override
	public boolean matches(TreeItem element, String searchString) {
		final Object data = element.getData();
		if (data instanceof SelectableFeature) {
			final SelectableFeature feature = (SelectableFeature) data;
			return feature.getName().toLowerCase().matches(".*" + searchString.toLowerCase() + ".*");
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
			final Collection<LiteralSet> openClauses = feature.getOpenClauses();
			if (!openClauses.isEmpty()) {
				final StringBuilder elementBuilder = new StringBuilder();
				for (final LiteralSet clause : openClauses) {
					final NodeWriter nodeWriter = new NodeWriter(Nodes.convert(feature.getVariables(), clause));
					nodeWriter.setSymbols(NodeWriter.logicalSymbols);
					elementBuilder.append(nodeWriter.nodeToString()).append('\n');
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

	public Void traverse(Consumer<List<TreeItem>> perNodeFunction, final Display currentDisplay) {
		final LinkedList<List<TreeItem>> updateElements = new LinkedList<>();
		currentDisplay.syncExec(() -> updateElements.add(Arrays.asList(tree.getItem(0))));
		while (!updateElements.isEmpty()) {
			final List<TreeItem> group = updateElements.poll();
			currentDisplay.syncExec(() -> traverse(perNodeFunction, group, updateElements));
		}
		return null;
	}

	public Void traverse(Consumer<List<TreeItem>> perNodeFunction, List<TreeItem> group, LinkedList<List<TreeItem>> updateElements) {
		for (final TreeItem parent : group) {
			updateElements.offer(Arrays.asList(parent.getItems()));
		}
		perNodeFunction.accept(group);
		return null;
	}

	public Void build(SelectableFeature rootFeature, final Display currentDisplay) {
		final LinkedList<TreeItem> parentElements = new LinkedList<>();
		currentDisplay.syncExec(() -> createRootItem(rootFeature, parentElements));
		if (parentElements.isEmpty()) {
			return null;
		}

		final LinkedList<List<TreeElement>> newElements = new LinkedList<>();
		newElements.offer(Arrays.asList(rootFeature.getChildren()));

		while (!newElements.isEmpty()) {
			final List<TreeElement> newGroup = newElements.poll();
			final TreeItem parent = parentElements.poll();

			final List<SelectableFeature> nonHidden = new ArrayList<>(newGroup.size());
			for (final TreeElement element : newGroup) {
				final SelectableFeature feature = (SelectableFeature) element;
				if (!feature.getFeature().getStructure().isHidden()) {
					nonHidden.add(feature);
					newElements.offer(Arrays.asList(feature.getChildren()));
				}
			}
			if (!nonHidden.isEmpty()) {
				final LinkedList<TreeItem> newParentElements = new LinkedList<>();
				currentDisplay.syncExec(() -> createFeatureItems(nonHidden, parent, newParentElements));
				if (newParentElements.isEmpty()) {
					return null;
				} else {
					parentElements.addAll(newParentElements);
				}
			}
		}
		return null;
	}

	private void createRootItem(SelectableFeature rootFeature, LinkedList<TreeItem> parentElements) {
		if (!tree.isDisposed()) {
			tree.removeAll();
			final TreeItem root = new TreeItem(tree, 0);
			root.setData(rootFeature);
			parentElements.add(root);
			itemMap.put(rootFeature, root);
			refreshItem(Arrays.asList(root));
		}
	}

	private void createFeatureItems(List<SelectableFeature> features, TreeItem parent, LinkedList<TreeItem> parentElements) {
		if (!parent.isDisposed()) {
			final List<TreeItem> items = new ArrayList<>();
			for (final SelectableFeature currentFeature : features) {
				// This try for the case that the parent item is already disposed.
				try {
					final TreeItem childNode = new TreeItem(parent, 0);
					childNode.setData(currentFeature);
					items.add(childNode);
					parentElements.add(childNode);
					itemMap.put(currentFeature, childNode);
				} catch (final Exception e) {}
			}
			refreshItem(items);
		}
	}

}
