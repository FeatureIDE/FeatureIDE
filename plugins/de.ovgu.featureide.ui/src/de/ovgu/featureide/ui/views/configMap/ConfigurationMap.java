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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.io.ConfigurationLoader;
import de.ovgu.featureide.fm.core.configuration.io.IConfigurationLoaderCallback;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.configMap.actions.ConfigMapFilterMenuAction;
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
	private int featureColumnWidth, defaultColumnWidth;

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

	private ConfigurationMapTreeContentProvider treeViewerContentProvider;
	private ConfigurationMapLabelProvider labelProvider;
	private IEditorPart currentEditor;
	private IPartListener partListener;

	private ConfigurationLoader loader;
	private List<Configuration> configurations;
	private Map<Configuration, Path> configPaths;
	
	private List<IConfigurationMapFilter> filters;
	private ConfigMapFilterMenuAction filterMenu;
	

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
			public void onLoadingError(IOException exception) {
			}

		};

		this.loader = new ConfigurationLoader(configLoaderCallback);
		this.configurationColumns = new ArrayList<>();
		this.configPaths = new HashMap<>();
		
		this.filters = new ArrayList<>();
		createFilters();

		this.featureColumnWidth = 200;
		this.defaultColumnWidth = 40;
		selectedColumnIndex = -1;
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
		columnHighlightColor = new Color(parent.getDisplay(), 255, 188, 0);

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
				partActivated(part);
			}

			public void partActivated(IWorkbenchPart part) {
				if (part instanceof IEditorPart)
					setEditor((IEditorPart) part);
			}
		};
		page.addPartListener(this.partListener);

		setEditor(page.getActiveEditor());
		
		createToolbar();
	}
	
	private void createToolbar() {
		IActionBars bars = getViewSite().getActionBars();
		IToolBarManager toolbarManager = bars.getToolBarManager();
		toolbarManager.removeAll();
		if (filterMenu == null) {
			IConfigurationMapFilter[] filtersArray = new IConfigurationMapFilter[this.filters.size()];
			this.filters.toArray(filtersArray);
			filterMenu = new ConfigMapFilterMenuAction(treeViewerContentProvider, filtersArray);
		}
		toolbarManager.add(filterMenu);
	}

	private void loadConfigurations() {
		// Callback will handle creating columns
		this.configurations = loader.loadConfigurations(featureProject.getFeatureModel(), featureProject.getConfigPath());
		// update header
		TreeColumn[] columns = tableTree.getColumns();
		List<CustomColumnStyle> styles = new ArrayList<>(columns.length);
		
		Display display = header.getDisplay();
		Color[] alternatingColors = new Color[] {
				new Color(display, 237, 237, 255),
				new Color(display, 221, 221, 237)
		};
		
		int offset = getConfigurationColumnsOffset();
		
		for (int i = 0; i < columns.length; i++) {
			TreeColumn col = columns[i];

			CustomColumnStyle style = new CustomColumnStyle(col.getText(), defaultColumnWidth);
			style.setVerticalAlignment(SWT.BOTTOM);
			style.setBackground(alternatingColors[i % alternatingColors.length]);
			
			if (i < offset) {
				style.setHorizontalAlignment(SWT.LEFT);
				style.setWidth(featureColumnWidth);
				style.setRotated(false);
				style.setSelectable(false);
				style.setBackground(headerBackground);
			}

			styles.add(style);
		}

		header.setColumnStyles(styles);

		// refresh gui
		updateHeaderHeight();
		updateTree();
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
			loadConfigurations();
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
		return this.configurations;
	}

	public int getConfigurationColumnsOffset() {
		return this.configColumnsOffset;
	}

	public int getSelectedColumnIndex() {
		return this.selectedColumnIndex;
	}

	Color getColumnHighlightColor() {
		return this.columnHighlightColor;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.configMap.header.ICustomTableHeaderSelectionListener#onColumnSelectionChanged(int)
	 */
	@Override
	public void onColumnSelectionChanged(int columnIndex) {
		this.selectedColumnIndex = columnIndex - getConfigurationColumnsOffset();
		updateTree();
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.configMap.header.ICustomTableHeaderSelectionListener#onColumnDoubleClicked()
	 */
	@Override
	public void onColumnDoubleClicked() {
		openConfiguration(this.selectedColumnIndex);
	}
	
	private void openConfiguration(int configIndex) {
		Configuration config = this.configurations.get(configIndex);
		IFile file = this.featureProject.getConfigFolder().getFile(configPaths.get(config).getFileName().toString());
		try {
			openEditor(file);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}
	
	private IEditorDescriptor getDescriptor(IFile file) throws CoreException {
		IContentType contentType = null;
		
		IContentDescription description = file.getContentDescription();
		if (description != null)
			contentType = description.getContentType();
			
		return PlatformUI.getWorkbench().getEditorRegistry().getDefaultEditor(file.getName(), contentType);
	}

	private void openEditor(IFile file) throws CoreException {
		IWorkbenchPage page = UIPlugin.getDefault().getWorkbench().getActiveWorkbenchWindow().getActivePage();
		if (page == null) return;

		String editorId = "org.eclipse.ui.DefaultTextEditor";

		IEditorDescriptor desc = getDescriptor(file);
		if (desc != null)
			editorId = desc.getId();
		
		page.openEditor(new FileEditorInput(file), editorId);
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
