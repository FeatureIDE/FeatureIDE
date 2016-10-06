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
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.io.ConfigurationLoader;
import de.ovgu.featureide.fm.core.configuration.io.IConfigurationLoaderCallback;

/**
 * TODO description
 * 
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 */
public class ConfigurationMap extends ViewPart {
	// DEFAULT VALUES
	private static final int COLUMN_WIDTH = 150;

	// VIEW
	private Tree tableTree;
	private TreeViewer tree;
	private List<TreeColumn> configurationColumns;
	private int configColumnsOffset = 0;

	private ConfigurationMapTreeContentProvider treeViewerContentProvider;
	private ConfigurationMapLabelProvider labelProvider;
	private IEditorPart currentEditor;

	private ConfigurationLoader loader;
	private List<Configuration> configurations;

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
			}

			/**
			 * Create a column in the view for each configuration, that has been loaded.
			 */
			@Override
			public void onConfigurationLoaded(Configuration configuration, Path path) {
				if (tableTree == null) return;
				
				String configFileName = path.getFileName().toString();
				System.err.println(configFileName);
				String[] configFileNameParts = configFileName.split("\\.");
				String configName = configFileNameParts[0];

				TreeColumn column = new TreeColumn(tableTree, SWT.LEFT);
				column.setAlignment(SWT.CENTER);
				column.setText(configName);
				column.setWidth(COLUMN_WIDTH); //Magic number
				
				configurationColumns.add(column);
			}

			@Override
			public void onLoadingError(IOException exception) {}

		};
		
		loader = new ConfigurationLoader(configLoaderCallback);
		configurationColumns = new ArrayList<>();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
		tableTree = new Tree(parent, SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL);
		tree = new TreeViewer(tableTree);

		tableTree.setHeaderVisible(true);
		tableTree.setLinesVisible(true);

		TreeColumn featuresColumn = new TreeColumn(tableTree, SWT.CENTER);
		featuresColumn.setAlignment(SWT.CENTER);
		featuresColumn.setText("Features");
		featuresColumn.setWidth(300); //Magic number
		
		// There is one column before the configuration columns
		configColumnsOffset = 1;

		treeViewerContentProvider = new ConfigurationMapTreeContentProvider();
		labelProvider = new ConfigurationMapLabelProvider(this);
		
		tree.setContentProvider(treeViewerContentProvider);
		tree.setLabelProvider(labelProvider);

		// init
		IWorkbenchPage page = getSite().getPage();
		page.addPartListener(new IPartListener() {
			public void partOpened(IWorkbenchPart part) {}
			public void partDeactivated(IWorkbenchPart part) {}

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
		});
		
		setEditor(page.getActiveEditor());
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	@Override
	public void setFocus() {}

	private void loadConfigurations() {
		// Callback will handle creating columns
		this.configurations = loader.loadConfigurations(featureProject.getFeatureModel(), featureProject.getConfigPath());
		tree.refresh();
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
			}
		}

		this.currentEditor = newEditor;
	}
	
	public List<Configuration> getConfigurations() {
		return this.configurations;
	}
	
	public int getConfigurationColumnsOffset() {
		return configColumnsOffset;
	}
}
