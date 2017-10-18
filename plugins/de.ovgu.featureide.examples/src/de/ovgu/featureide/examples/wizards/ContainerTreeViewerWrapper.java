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
package de.ovgu.featureide.examples.wizards;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTreeViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.ICheckable;
import org.eclipse.jface.viewers.StructuredViewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.dialogs.ContainerCheckedTreeViewer;

import de.ovgu.featureide.examples.utils.ProjectRecord;
import de.ovgu.featureide.examples.utils.ProjectRecord.TreeItem;

/**
 *
 * @author Reimar Schroeter
 */
public class ContainerTreeViewerWrapper implements ICheckable {

	private final List<ContainerCheckedTreeViewer> listOfTreeViewer = new ArrayList<>();
	private ContainerCheckedTreeViewer selectedViewer;

	class ParentCheckStateChangedEvent extends CheckStateChangedEvent {

		private static final long serialVersionUID = 3615026101952835765L;
		private boolean onlyRefresh = false;

		public boolean isOnlyRefresh() {
			return onlyRefresh;
		}

		private void setOnlyRefresh(boolean onlyRefresh) {
			this.onlyRefresh = onlyRefresh;
		}

		public ParentCheckStateChangedEvent(ICheckable source, Object element, boolean state) {
			super(source, element, state);
		}
	}

	private class WrappedContainerCheckedTreeViewer extends ContainerCheckedTreeViewer {

		public WrappedContainerCheckedTreeViewer(Composite parent, int style) {
			super(parent, style);
		}

		@Override
		protected void doCheckStateChanged(Object element) {
			super.doCheckStateChanged(element);
			final Object[] filteredChildren = super.getFilteredChildren(element);
			for (final Object object : filteredChildren) {
				final ParentCheckStateChangedEvent event = new ParentCheckStateChangedEvent(this, object, getChecked(element));
				if (object instanceof ProjectRecord.TreeItem) {
					final ProjectRecord.TreeItem item = (ProjectRecord.TreeItem) object;
					event.setOnlyRefresh(!item.getRecord().hasErrors() && !item.getRecord().hasWarnings());
					fireCheckStateChanged(event);
				} else if (object instanceof IPath) {
					fireCheckStateChanged(event);
				}
			}
		}
	}

	public ContainerCheckedTreeViewer getNewContainerViewer(Composite parent, int style) {
		final WrappedContainerCheckedTreeViewer intern = new WrappedContainerCheckedTreeViewer(parent, style);
		listOfTreeViewer.add(intern);
		return intern;
	}

	public void refreshAllViewers() {
		for (final ContainerCheckedTreeViewer containerCheckedTreeViewer : listOfTreeViewer) {
			containerCheckedTreeViewer.refresh();
		}
	}

	public ContainerCheckedTreeViewer getSelectedViewer() {
		return selectedViewer;
	}

	public void setSelectedViewer(Control contr) {
		for (final StructuredViewer structuredViewer : listOfTreeViewer) {
			if (structuredViewer.getControl().getParent().equals(contr)) {
				selectedViewer = (ContainerCheckedTreeViewer) structuredViewer;
			}
		}
	}

	@Override
	public boolean setChecked(Object element, boolean state) {
		boolean ret = true;
		if (element instanceof ProjectRecord.TreeItem) {
			final ProjectRecord.TreeItem treeitem = (ProjectRecord.TreeItem) element;
			for (final ProjectRecord.TreeItem curr : treeitem.getRecord().getTreeItems()) {
				for (final ContainerCheckedTreeViewer containerCheckedTreeViewer : listOfTreeViewer) {
					if (!containerCheckedTreeViewer.setChecked(curr, state)) {
						ret = false;
					}
				}
			}
		}
		return ret;
	}

	public boolean setGrayed(Object element, boolean state) {
		boolean ret = true;
		if (element instanceof ProjectRecord.TreeItem) {
			final ProjectRecord.TreeItem treeitem = (ProjectRecord.TreeItem) element;
			for (final ProjectRecord.TreeItem curr : treeitem.getRecord().getTreeItems()) {
				for (final ContainerCheckedTreeViewer containerCheckedTreeViewer : listOfTreeViewer) {
					if (!containerCheckedTreeViewer.setGrayed(curr, state)) {
						ret = false;
					}
				}
			}
		}
		return ret;
	}

	public Object[] getCheckedProjects() {
		final Set<ProjectRecord> ret = new HashSet<>();
		for (final ContainerCheckedTreeViewer containerCheckedTreeViewer : listOfTreeViewer) {
			final ArrayList<Object> list = new ArrayList<>(Arrays.asList(containerCheckedTreeViewer.getCheckedElements()));
			for (final Object object : new ArrayList<>(list)) {
				if ((object instanceof ProjectRecord.TreeItem)) {
					final ProjectRecord.TreeItem treeItem = (ProjectRecord.TreeItem) object;
					ret.add(treeItem.getRecord());
				}
			}
		}
		return ret.toArray();
	}

	// necessary to determine finish
	public boolean isProjectSelected() {
		for (final ContainerCheckedTreeViewer containerCheckedTreeViewer : listOfTreeViewer) {
			final Object[] checkedElements = containerCheckedTreeViewer.getCheckedElements();
			for (final Object object : checkedElements) {
				if ((object instanceof ProjectRecord.TreeItem)) {
					return true;
				}
			}
		}
		return false;
	}

	public Object[] getAllProjectItems(ContainerCheckedTreeViewer containerCheckedTreeViewer) {
		final Set<ProjectRecord.TreeItem> ret = new HashSet<>();
		final Collection<ProjectRecord> projects = ProjectProvider.getProjects();
		for (final ProjectRecord object : projects) {
			for (final ProjectRecord.TreeItem treeItem : object.getTreeItems()) {
				if (treeItem.getProvider().equals(containerCheckedTreeViewer.getContentProvider())) {
					ret.add(treeItem);
				}
			}
		}
		return ret.toArray();
	}

	public Object[] getCheckedProjectItems(ContainerCheckedTreeViewer viewer) {
		final Set<ProjectRecord.TreeItem> ret = new HashSet<>();
		for (final ContainerCheckedTreeViewer containerCheckedTreeViewer : listOfTreeViewer) {
			if ((viewer == null) || ((viewer != null) && (containerCheckedTreeViewer == selectedViewer))) {
				for (final Object object : ((CheckboxTreeViewer) containerCheckedTreeViewer).getCheckedElements()) {
					if ((object instanceof ProjectRecord.TreeItem)) {
						ret.add((TreeItem) object);
					}
				}
			}
		}
		return ret.toArray();
	}

	public void refreshCheckOfSelectedViewer(Object[] checkedProjects) {
		final ContainerCheckedTreeViewer getselectedViewer = getSelectedViewer();
		getselectedViewer.setCheckedElements(checkedProjects);
	}

	public void addFilter(ViewerFilter searchFilter) {
		for (final ContainerCheckedTreeViewer containerCheckedTreeViewer : listOfTreeViewer) {
			containerCheckedTreeViewer.addFilter(searchFilter);
		}
	}

	public void removeFilter(ViewerFilter filter) {
		for (final ContainerCheckedTreeViewer containerCheckedTreeViewer : listOfTreeViewer) {
			containerCheckedTreeViewer.removeFilter(filter);
		}
	}

	@Override
	public void addCheckStateListener(ICheckStateListener listener) {}

	@Override
	public boolean getChecked(Object element) {
		return false;
	}

	@Override
	public void removeCheckStateListener(ICheckStateListener listener) {}

}
