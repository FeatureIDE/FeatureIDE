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

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeExpansionEvent;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter;

/**
 * Provider for NotAvailable
 *
 * @author Christopher Sontag
 */
public class NotAvailableOutlineProvider extends OutlineProvider {

	public NotAvailableOutlineProvider() {
		super(new NotAvailableContentProvider(), new NotAvailableLabelProvider());
	}

	@Override
	public boolean isSupported(IFile file) {
		return true;
	}

	@Override
	public void handleUpdate(TreeViewer viewer, IFile iFile) {

	}

	@Override
	public String getProviderName() {
		return "";
	}

	@Override
	public void selectionChanged(SelectionChangedEvent event) {}

	@Override
	protected void initContextMenuActions(IMenuManager manager) {}

	@Override
	protected void initToolbarActions(IToolBarManager manager) {}

	@Override
	protected List<IOutlineFilter> getFilters() {
		return null;
	}

	@Override
	public void treeCollapsed(TreeExpansionEvent event) {}

	@Override
	public void treeExpanded(TreeExpansionEvent event) {}

}
