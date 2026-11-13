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
package de.ovgu.featureide.ui.projectExplorer.packages;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jface.viewers.StructuredViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.navigator.ICommonContentExtensionSite;
import org.eclipse.ui.navigator.IPipelinedTreeContentProvider2;
import org.eclipse.ui.navigator.PipelinedShapeModification;
import org.eclipse.ui.navigator.PipelinedViewerUpdate;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Shows the content of feature folders in the Project Explorer as packages, like the content of a Java source folder.
 * <p>
 * The Java content of the Project Explorer shows feature folders as normal folders, because they are not on the build path. This provider replaces the
 * children of feature folders (and of the folders <code>src</code> and <code>src/main</code> in feature folders with the Maven layout) with the nodes
 * computed by {@link FeaturePackageStructure}, and provides the children of these nodes.
 *
 * @author Philipp Hehnle
 */
public class FeaturePackageContentProvider implements IPipelinedTreeContentProvider2, IResourceChangeListener {

	private static final Object[] NO_CHILDREN = new Object[0];

	private StructuredViewer viewer;

	@Override
	public void init(ICommonContentExtensionSite config) {
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this, IResourceChangeEvent.POST_CHANGE);
	}

	@Override
	public void dispose() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
		viewer = null;
	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		this.viewer = (viewer instanceof StructuredViewer) ? (StructuredViewer) viewer : null;
	}

	@Override
	public void restoreState(IMemento memento) {}

	@Override
	public void saveState(IMemento memento) {}

	// ----- children of the nodes of this provider -----

	@Override
	public Object[] getElements(Object inputElement) {
		return NO_CHILDREN;
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		try {
			if (parentElement instanceof FeaturePackageRoot) {
				final FeaturePackageRoot root = (FeaturePackageRoot) parentElement;
				if (root.getFolder().exists()) {
					return FeaturePackageStructure.getPackageRootChildren(root, root.getFolder()).toArray();
				}
			} else if (parentElement instanceof FeaturePackage) {
				final FeaturePackage featurePackage = (FeaturePackage) parentElement;
				if (featurePackage.getFolder().exists()) {
					return FeaturePackageStructure.getPackageChildren(featurePackage).toArray();
				}
			}
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
		return NO_CHILDREN;
	}

	@Override
	public boolean hasChildren(Object element) {
		return getChildren(element).length > 0;
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof FeaturePackageRoot) {
			return ((FeaturePackageRoot) element).getFeatureFolder();
		} else if (element instanceof FeaturePackage) {
			return ((FeaturePackage) element).getParent();
		}
		// files in feature folders are shown in packages
		return getPipelinedParent(element, null);
	}

	// ----- changes to the content of the Java Project Explorer content -----

	@SuppressWarnings({ "rawtypes", "unchecked" })
	@Override
	public void getPipelinedChildren(Object aParent, Set theCurrentChildren) {
		if (!(aParent instanceof IFolder) || containsJavaElements(theCurrentChildren)) {
			// if the folder is on the build path, its content is already shown as packages
			return;
		}
		final IFolder folder = (IFolder) aParent;
		final IFolder featureFolder = FeatureFolders.getFeatureFolder(folder);
		if (featureFolder == null) {
			return;
		}
		try {
			if (featureFolder.equals(folder)) {
				final List<Object> children = FeaturePackageStructure.getFeatureFolderChildren(featureFolder);
				theCurrentChildren.clear();
				theCurrentChildren.addAll(children);
			} else {
				// e.g. the folder src of a feature with src/main/java and src/test/java
				FeaturePackageStructure.removeResourcesInSourceFolders(featureFolder, theCurrentChildren);
			}
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
	}

	@Override
	public boolean hasPipelinedChildren(Object anInput, boolean currentHasChildren) {
		return currentHasChildren;
	}

	@SuppressWarnings("rawtypes")
	@Override
	public void getPipelinedElements(Object anInput, Set theCurrentElements) {}

	@Override
	public Object getPipelinedParent(Object anObject, Object aSuggestedParent) {
		if (anObject instanceof IResource) {
			final IResource resource = (IResource) anObject;
			final IFolder featureFolder = FeatureFolders.getFeatureFolder(resource);
			if ((featureFolder != null) && !featureFolder.equals(resource)) {
				final Object parent = FeaturePackageStructure.getParent(resource, featureFolder);
				if (parent != null) {
					return parent;
				}
			}
		}
		return aSuggestedParent;
	}

	@Override
	public PipelinedShapeModification interceptAdd(PipelinedShapeModification anAddModification) {
		// added resources in feature folders are shown by refreshing the feature folder, see resourceChanged()
		return anAddModification;
	}

	@Override
	public PipelinedShapeModification interceptRemove(PipelinedShapeModification aRemoveModification) {
		return aRemoveModification;
	}

	@Override
	public boolean interceptRefresh(PipelinedViewerUpdate aRefreshSynchronization) {
		return false;
	}

	@Override
	public boolean interceptUpdate(PipelinedViewerUpdate anUpdateSynchronization) {
		return false;
	}

	private static boolean containsJavaElements(Set<?> children) {
		for (final Object child : children) {
			if (child instanceof IJavaElement) {
				return true;
			}
		}
		return false;
	}

	// ----- refreshing -----

	/**
	 * Refreshes the feature folders in which resources were added or removed, because the packages shown in them are computed from their content.
	 */
	@Override
	public void resourceChanged(IResourceChangeEvent event) {
		final IResourceDelta delta = event.getDelta();
		if ((delta == null) || (viewer == null)) {
			return;
		}
		final Set<IFolder> changedFeatureFolders = new LinkedHashSet<>();
		try {
			delta.accept(new FeatureFolderDeltaVisitor(changedFeatureFolders));
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
		if (changedFeatureFolders.isEmpty()) {
			return;
		}
		final StructuredViewer currentViewer = viewer;
		final Control control = (currentViewer != null) ? currentViewer.getControl() : null;
		if ((control == null) || control.isDisposed()) {
			return;
		}
		control.getDisplay().asyncExec(() -> {
			if (!control.isDisposed()) {
				for (final IFolder featureFolder : changedFeatureFolders) {
					currentViewer.refresh(featureFolder);
				}
			}
		});
	}

	/**
	 * Collects the feature folders that contain added or removed resources. Only visits the source folders of feature projects.
	 */
	private static final class FeatureFolderDeltaVisitor implements org.eclipse.core.resources.IResourceDeltaVisitor {

		private final Set<IFolder> changedFeatureFolders;
		private IPath sourceFolderPath;

		FeatureFolderDeltaVisitor(Set<IFolder> changedFeatureFolders) {
			this.changedFeatureFolders = changedFeatureFolders;
		}

		@Override
		public boolean visit(IResourceDelta delta) {
			final IResource resource = delta.getResource();
			switch (resource.getType()) {
			case IResource.ROOT:
				return true;
			case IResource.PROJECT:
				final IFeatureProject featureProject = CorePlugin.getFeatureProject(resource);
				final IFolder sourceFolder = (featureProject != null) ? featureProject.getSourceFolder() : null;
				sourceFolderPath = (sourceFolder != null) ? sourceFolder.getFullPath() : null;
				return (sourceFolderPath != null) && ((IProject) resource).isOpen();
			default:
				final IPath path = resource.getFullPath();
				if ((sourceFolderPath == null) || !(sourceFolderPath.isPrefixOf(path) || path.isPrefixOf(sourceFolderPath))) {
					return false;
				}
				if ((delta.getKind() & (IResourceDelta.ADDED | IResourceDelta.REMOVED)) != 0) {
					final IFolder featureFolder = FeatureFolders.getFeatureFolder(resource);
					if ((featureFolder != null) && !featureFolder.equals(resource)) {
						changedFeatureFolders.add(featureFolder);
					}
				}
				return true;
			}
		}
	}
}
