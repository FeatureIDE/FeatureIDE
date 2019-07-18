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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.ui.views.outline.custom.providers;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeExpansionEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;
import de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry;
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
	TreeViewer viewer;
	IDoubleClickListener dblClickListener;

	public ConfigurationOutlineProvider() {
		super(new ConfigurationTreeContentProvider(), new ConfigurationLabelProvider());
	}

	public ConfigurationOutlineProvider(OutlineTreeContentProvider treeProvider, OutlineLabelProvider labelProvider) {
		super(treeProvider, labelProvider);
	}

	@Override
	public void selectionChanged(SelectionChangedEvent event) {}

	@Override
	public void treeCollapsed(TreeExpansionEvent event) {}

	@Override
	public void treeExpanded(TreeExpansionEvent event) {}

	@Override
	protected void initContextMenuActions(IMenuManager manager) {}

	@Override
	protected void initToolbarActions(IToolBarManager manager) {}

	@Override
	protected List<IOutlineFilter> getFilters() {
		return null;
	}

	@Override
	public boolean isSupported(IFile file) {
		return ConfigFormatManager.getInstance().hasFormat(EclipseFileSystem.getPath(file));
	}

	private void initListeners() {
		dblClickListener = new IDoubleClickListener() {

			@Override
			public void doubleClick(DoubleClickEvent event) {
				if ((((IStructuredSelection) viewer.getSelection()).getFirstElement() instanceof IOutlineEntry)) {
					final IOutlineEntry entry = (IOutlineEntry) ((IStructuredSelection) viewer.getSelection()).getFirstElement();
					entry.handleDoubleClick();
					viewer.refresh(entry);
				}
			}
		};
	}

	@Override
	public void handleUpdate(TreeViewer viewer, IFile iFile) {
		this.viewer = viewer;
		initListeners();
		viewer.removeDoubleClickListener(dblClickListener);
		viewer.addDoubleClickListener(dblClickListener);
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
