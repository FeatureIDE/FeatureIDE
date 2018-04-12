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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.ui.views.outline.custom.providers;

import java.nio.file.Paths;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeExpansionEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter;

/**
 * TODO description
 *
 * @author Chico Sundermann
 */
public class ConfigurationOutlineProvider extends OutlineProvider {

	Configuration config;

	public ConfigurationOutlineProvider() {
		super(new ConfigurationTreeContentProvider(), new ConfigurationLabelProvider());
	}

	public ConfigurationOutlineProvider(OutlineTreeContentProvider treeProvider, OutlineLabelProvider labelProvider) {
		super(treeProvider, labelProvider);
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ISelectionChangedListener#selectionChanged(org.eclipse.jface.viewers.SelectionChangedEvent)
	 */
	@Override
	public void selectionChanged(SelectionChangedEvent event) {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeViewerListener#treeCollapsed(org.eclipse.jface.viewers.TreeExpansionEvent)
	 */
	@Override
	public void treeCollapsed(TreeExpansionEvent event) {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeViewerListener#treeExpanded(org.eclipse.jface.viewers.TreeExpansionEvent)
	 */
	@Override
	public void treeExpanded(TreeExpansionEvent event) {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider#initContextMenuActions(org.eclipse.jface.action.IMenuManager)
	 */
	@Override
	protected void initContextMenuActions(IMenuManager manager) {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider#initToolbarActions(org.eclipse.jface.action.IToolBarManager)
	 */
	@Override
	protected void initToolbarActions(IToolBarManager manager) {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider#getFilters()
	 */
	@Override
	protected List<IOutlineFilter> getFilters() {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider#isSupported(org.eclipse.core.resources.IFile)
	 */
	@Override
	public boolean isSupported(IFile file) {
		try {
			return ConfigurationManager.getInstance(Paths.get(file.getLocationURI())) != null;
		} catch (final ClassCastException e) {
			return false;
		}
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider#handleUpdate(org.eclipse.jface.viewers.TreeViewer, org.eclipse.core.resources.IFile)
	 */
	@Override
	public void handleUpdate(TreeViewer viewer, IFile iFile) {
		final IWorkbench workbench = PlatformUI.getWorkbench();
		final IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
		final IWorkbenchPage page = window.getActivePage();
		final IEditorPart activeEditor = page.getActiveEditor();
		if (activeEditor instanceof ConfigurationEditor) {
			final ConfigurationEditor confEditor = (ConfigurationEditor) activeEditor;
			config = confEditor.getConfiguration();

			getTreeProvider().inputChanged(viewer, null, config);
		}

	}

}
