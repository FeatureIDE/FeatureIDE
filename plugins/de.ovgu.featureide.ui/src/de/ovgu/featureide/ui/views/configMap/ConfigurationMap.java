/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistributetree/or modify
 * it under the terms of the GNU Ltreeeneral Putreecense as published by
 * the Fretreeare Foundation, either version 3 of the License, or
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.ui.views.configMap;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartSite;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.ViewPart;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.io.ConfigurationLoader;
import de.ovgu.featureide.fm.core.configuration.io.IConfigurationLoaderCallback;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors.SetFeatureColorAction;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.configMap.actions.ConfigMapFilterMenuAction;
import de.ovgu.featureide.ui.views.configMap.actions.ConfigMapRefreshAction;
import de.ovgu.featureide.ui.views.configMap.actions.OpenFileAction;
import de.ovgu.featureide.ui.views.configMap.filters.CoreFeatureFilter;
import de.ovgu.featureide.ui.views.configMap.filters.DeadFeatureFilter;
import de.ovgu.featureide.ui.views.configMap.filters.FeatureIsFalseOptionalFilter;
import de.ovgu.featureide.ui.views.configMap.filters.FeatureUnusedFilter;
import de.ovgu.featureide.ui.views.configMap.filters.NotAnyFilterFiltersFeatureFilter;
import de.ovgu.featureide.ui.views.configMap.header.CustomColumnStyle;
import de.ovgu.featureide.ui.views.configMap.header.CustomTableHeader;
import de.ovgu.featureide.ui.views.configMap.header.ICustomTableHeaderSelectionListener;

/**
 * TODO description
 * 
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 */

public class ConfigurationMap extends ViewPart implements ICustomTableHeaderSelectionListener {
	public static final String ID = UIPlugin.PLUGIN_ID + ".view1";

	private int featureColumnWidth, defaultColumnWidth;

	private SetFeatureColorAction setFeatureColor;

	// VIEW
	private Composite parent;
	private Tree tableTree;
	private TreeViewer tree;
	private CustomTableHeader header;
	private Color headerBackground;
	private Color columnHighlightColor;
	private List<TreeColumn> configurationColumns;
	private int configColumnsOffset = 0;
	private int gridColumns;
	private int selectedColumnIndex;
	private boolean configUpdateNecessary;

	private ConfigurationMapTreeContentProvider treeViewerContentProvider;
	private ConfigurationMapLabelProvider labelProvider;
	private IEditorPart currentEditor;
	private IPartListener partListener;

	private ConfigurationLoader loader;
	private List<Configuration> configurations;
	private Map<Configuration, Path> configPaths;

	private List<IConfigurationMapFilter> filters;
	private ConfigMapFilterMenuAction filterMenu;

	private ConfigMapRefreshAction refresh;
	private OpenFileAction openFileAction;

	// MODEL
	private IFeatureProject featureProject;

	public ConfigurationMap() {
		IConfigurationLoaderCallback configLoaderCallback = new IConfigurationLoaderCallback() {

			@Override
			public void onLoadingStarted() {
				// clear all old columns because new configurations are going to be loaded
				for (TreeColumn column : configurationColumns)
					column.dispose();
				configurationColumns.clear();
				configPaths.clear();
			}

			/**
			 * Create a column in the view for each configuration, that has been loaded.
			 */
			@Override
			public void onConfigurationLoaded(Configuration configuration, Path path) {
				if (tableTree == null)
					return;

				String configFileName = path.getFileName().toString();
				String[] configFileNameParts = configFileName.split("\\.");
				String configName = configFileNameParts[0];

				TreeColumn column = new TreeColumn(tableTree, SWT.CENTER);
				column.setAlignment(SWT.CENTER);
				column.setWidth(defaultColumnWidth);
				column.setText(configName);

				configurationColumns.add(column);
				configPaths.put(configuration, path);
			}

			@Override
			public void onLoadingFinished() {
				TreeColumn dummy = new TreeColumn(tableTree, SWT.NULL);
				dummy.setWidth(defaultColumnWidth);
				configurationColumns.add(dummy);
			}

			@Override
			public void onLoadingError(IOException exception) {
			}

		};

		this.featureColumnWidth = 200;
		this.defaultColumnWidth = 40;
		selectedColumnIndex = -1;

		openFileAction = new OpenFileAction("Open");

		this.loader = new ConfigurationLoader(configLoaderCallback);
		this.configurationColumns = new ArrayList<>();
		this.configPaths = new HashMap<>();

		this.filters = new ArrayList<>();
		createFilters();
	}

	/**
	 * If you want to add filters to the view, do it here.
	 * The gui elements will be created automatically.
	 */
	private void createFilters() {
		filters.add(new CoreFeatureFilter(true));
		filters.add(new FeatureIsFalseOptionalFilter(true));
		filters.add(new FeatureUnusedFilter(true));
		filters.add(new DeadFeatureFilter(true));

		List<IConfigurationMapFilter> previousFiltersCopy = new ArrayList<>(filters);

		filters.add(new NotAnyFilterFiltersFeatureFilter("remaining features", true, previousFiltersCopy));
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
		this.gridColumns = 1;
		this.parent = parent;
		columnHighlightColor = new Color(parent.getDisplay(), 181, 181, 197);

		GridLayout layout = new GridLayout(gridColumns, true);
		layout.verticalSpacing = 0;
		layout.horizontalSpacing = 0;
		parent.setLayout(layout);

		// HEADER
		header = new CustomTableHeader(parent, SWT.FILL);
		tableTree = new Tree(parent, SWT.H_SCROLL | SWT.V_SCROLL);
		headerBackground = header.getDisplay().getSystemColor(SWT.COLOR_WHITE);

		GridData headerGridData = new GridData(SWT.FILL, SWT.CENTER, true, false);
		headerGridData.horizontalSpan = gridColumns;
		header.setLayoutData(headerGridData);
		header.setBackground(headerBackground);
		header.setGlobalRotation((float) CustomTableHeader.toRadians(-70));
		header.setLinesVisible(true);
		header.setHighlightColor(columnHighlightColor);
		header.addColumnSelectionListener(this);

		// TREE
		GridData tableTreeGridData = new GridData(SWT.FILL, SWT.FILL, true, true);
		tableTreeGridData.horizontalSpan = gridColumns;
		tableTree.setLayoutData(tableTreeGridData);
		tableTree.setHeaderVisible(false);
		tableTree.setLinesVisible(true);

		tree = new TreeViewer(tableTree);

		labelProvider = new ConfigurationMapLabelProvider(this);
		treeViewerContentProvider = new ConfigurationMapTreeContentProvider(this);

		TreeColumn featuresColumn = new TreeColumn(tableTree, SWT.LEFT);
		featuresColumn.setAlignment(SWT.CENTER);
		featuresColumn.setText("Features");
		featuresColumn.setWidth(featureColumnWidth);

		// There is one column before the configuration columns
		configColumnsOffset = 1;

		tree.setContentProvider(treeViewerContentProvider);
		tree.setLabelProvider(labelProvider);

		// init
		IWorkbenchPage page = getSite().getPage();
		this.partListener = new IPartListener() {
			public void partOpened(IWorkbenchPart part) {
			}

			public void partDeactivated(IWorkbenchPart part) {
			}

			public void partClosed(IWorkbenchPart part) {
				if (part == currentEditor)
					setEditor(null);
			}

			public void partBroughtToTop(IWorkbenchPart part) {
				update(part);
			}

			public void partActivated(IWorkbenchPart part) {
				update(part);
			}
			
			private void update(IWorkbenchPart part) {
				if (part instanceof IEditorPart)
					setEditor((IEditorPart) part);
				
				if (configUpdateNecessary) {
					refresh();
					configUpdateNecessary = false;
				}
			}
		};
		page.addPartListener(this.partListener);

		setEditor(page.getActiveEditor());

		setFeatureColor = new SetFeatureColorAction(tree, featureProject.getFeatureModel());
		setFeatureColor.addColorChangedListener(new IEventListener() {
			@Override
			public void propertyChange(FeatureIDEEvent event) {
				if (event.getEventType() == FeatureIDEEvent.EventType.COLOR_CHANGED)
					updateTree();
			}
		});

		createToolbar();
		createContextMenu();

		tableTree.addMouseListener(new MouseListener() {

			@Override
			public void mouseDoubleClick(MouseEvent e) {

			}

			@Override
			public void mouseDown(MouseEvent e) {
				int columnCount = tableTree.getColumnCount();
				int xOffset = 0;
				int clickedColumn = -1;

				for (int i = 0; i < columnCount; i++) {
					xOffset += tableTree.getColumn(i).getWidth();
					if (e.x < xOffset) {
						clickedColumn = i;
						break;
					}
				}
				
				header.setSelectedColumn(clickedColumn);
			}

			@Override
			public void mouseUp(MouseEvent e) {

			}
		});
	}

	private void createToolbar() {
		IActionBars bars = getViewSite().getActionBars();
		IToolBarManager toolbarManager = bars.getToolBarManager();
		toolbarManager.removeAll();
		;
		if (filterMenu == null) {
			IConfigurationMapFilter[] filtersArray = new IConfigurationMapFilter[this.filters.size()];
			this.filters.toArray(filtersArray);
			filterMenu = new ConfigMapFilterMenuAction(treeViewerContentProvider, filtersArray);
		}
		toolbarManager.add(filterMenu);

		if (refresh == null)
			refresh = new ConfigMapRefreshAction(this);
		toolbarManager.add(refresh);
	}

	public void createContextMenu() {
		MenuManager menuMgr = new MenuManager("#PopupMenu");
		menuMgr.setRemoveAllWhenShown(true);

		menuMgr.addMenuListener(new IMenuListener() {
			public void menuAboutToShow(IMenuManager m) {
				fillContextMenu(m);
			}
		});
		Control control = tree.getControl();
		Menu menu = menuMgr.createContextMenu(control);
		control.setMenu(menu);
		getSite().registerContextMenu(menuMgr, tree);

		MenuManager headerMenu = new MenuManager("#HeaderPopup");
		headerMenu.setRemoveAllWhenShown(true);
		headerMenu.addMenuListener(new IMenuListener() {
			public void menuAboutToShow(IMenuManager m) {
				fillHeaderMenu(m);
			}
		});
		header.setMenu(headerMenu.createContextMenu(header));
		getSite().registerContextMenu(headerMenu, header);
	}

	private void fillHeaderMenu(IMenuManager menuMgr) {
		if (featureProject == null)
			return;
		openFileAction.setFile(getFileOfConfiguration(getSelectedConfigIndex()));
		menuMgr.add(openFileAction);
	}

	private void fillContextMenu(IMenuManager menuMgr) {
		if (featureProject == null)
			return;
		boolean isNotEmpty = !tree.getSelection().isEmpty();
		setFeatureColor.setFeatureModel(featureProject.getFeatureModel());

		setFeatureColor.setEnabled(isNotEmpty);
		menuMgr.add(setFeatureColor);
	}

	public void loadConfigurations() {
		// Callback will handle creating columns
		this.configurations = loader.loadConfigurations(featureProject.getFeatureModel(), featureProject.getConfigPath());

		// update header
		TreeColumn[] columns = tableTree.getColumns();
		List<CustomColumnStyle> styles = new ArrayList<>(columns.length);

		Display display = header.getDisplay();
		Color[] alternatingColors = new Color[] { new Color(display, 237, 237, 255), new Color(display, 221, 221, 237) };

		for (int i = 0; i < columns.length; i++) {
			TreeColumn col = columns[i];

			CustomColumnStyle style = new CustomColumnStyle(col.getText(), defaultColumnWidth);
			style.setVerticalAlignment(SWT.BOTTOM);
			style.setBackground(alternatingColors[i % alternatingColors.length]);

			if (!isConfigColumn(i)) {
				style.setHorizontalAlignment(SWT.LEFT);
				style.setWidth(featureColumnWidth);
				style.setRotated(false);
				style.setSelectable(false);
				style.setBackground(headerBackground);

				if (this.configColumnsOffset <= i)
					style.setDrawingLine(false);
			}

			styles.add(style);
		}

		header.setColumnStyles(styles);

		// refresh gui
		updateGUI();
	}
	
	public void refresh() {
		loadConfigurations();
		updateGUI(true);
	}
	
	public void updateGUI() {
		updateGUI(false);
	}
	
	public void updateGUI(boolean forceUpdate) {
		if (forceUpdate || isActive()) {
			updateHeaderHeight();
			updateTree();
		}
	}

	void updateTree() {
		tree.refresh();
		tree.expandAll();
	}

	private void updateHeaderHeight() {
		GridData headerGridData = new GridData(SWT.FILL, SWT.CENTER, true, false);
		headerGridData.horizontalSpan = gridColumns;
		headerGridData.heightHint = header.getHeight();
		header.setLayoutData(headerGridData);
		parent.layout();
	}

	public boolean isConfigColumn(int index) {
		return configColumnsOffset <= index && index < tableTree.getColumnCount() - 1; // -1 for dummy column
	}

	public int getConfigColumnsOffset() {
		return this.configColumnsOffset;
	}
	
	private boolean isActive() {
		IWorkbenchPartSite site = getSite();
		return site.getPage().isPartVisible(site.getPart());
	}

	@Override
	public void setFocus() {
	}

	protected CustomTableHeader getHeader() {
		return this.header;
	}

	public IFeatureProject getFeatureProject() {
		return this.featureProject;
	}

	private void setFeatureProject(IFeatureProject featureProject) {
		if (this.featureProject != featureProject) {
			this.featureProject = featureProject;
			if (isActive())
				loadConfigurations();
			else
				configUpdateNecessary = true;
			treeViewerContentProvider.setFeatureProject(this.featureProject);
		}
	}

	private void setEditor(IEditorPart newEditor) {
		if (this.currentEditor == newEditor)
			return;

		// update project
		if (newEditor != null) {
			IEditorInput newInput = newEditor.getEditorInput();

			if (newInput != null) {
				if (newInput instanceof FileEditorInput) {
					IFile projectFile = ((FileEditorInput) newInput).getFile();
					IFeatureProject newProject = CorePlugin.getFeatureProject(projectFile);
					if (!newProject.equals(this.featureProject))
						setFeatureProject(newProject);
				}

				tree.setInput(newInput);
				updateTree();
			}
		}

		this.currentEditor = newEditor;
	}

	public List<Configuration> getConfigurations() {
		return Collections.unmodifiableList(this.configurations);
	}

	public Configuration getConfigurationOfColumn(int columnIndex) {
		if (isConfigColumn(columnIndex))
			return this.configurations.get(columnIndex - this.configColumnsOffset);
		return null;
	}

	public int getSelectedColumnIndex() {
		return this.selectedColumnIndex;
	}

	public int getSelectedConfigIndex() {
		if (this.selectedColumnIndex == -1)
			return this.selectedColumnIndex;
		return this.selectedColumnIndex - this.configColumnsOffset;
	}

	Color getColumnHighlightColor() {
		return this.columnHighlightColor;
	}

	private IFile getFileOfConfiguration(int configurationIndex) {
		Configuration config = this.configurations.get(configurationIndex);
		return this.featureProject.getConfigFolder().getFile(configPaths.get(config).getFileName().toString());
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.configMap.header.ICustomTableHeaderSelectionListener#onColumnSelectionChanged(int)
	 */
	@Override
	public void onColumnSelectionChanged(int columnIndex) {
		this.selectedColumnIndex = columnIndex;
		updateTree();
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.configMap.header.ICustomTableHeaderSelectionListener#onColumnDoubleClicked()
	 */
	@Override
	public void onColumnDoubleClicked() {
		openFileAction.setFile(getFileOfConfiguration(getSelectedConfigIndex()));
		openFileAction.run();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#dispose()
	 */
	@Override
	public void dispose() {
		IWorkbenchPage page = getSite().getPage();
		page.removePartListener(this.partListener);
		header.removeColumnSelectionListener(this);
		header.dispose();
		columnHighlightColor.dispose();
		super.dispose();
	}
}
