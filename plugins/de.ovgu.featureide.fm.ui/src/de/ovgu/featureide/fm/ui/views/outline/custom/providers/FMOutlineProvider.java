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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.IContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeExpansionEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.views.outline.FmOutlinePageContextMenu;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.action.SyncCollapsedStateAction;
import de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter;

public class FMOutlineProvider extends OutlineProvider implements IEventListener {

	private SyncCollapsedStateAction syncCollapsedStateAction;
	private IGraphicalFeatureModel graphicalFeatureModel;
	private FmOutlinePageContextMenu contextMenu;

	public FMOutlineProvider() {
		super(new FMTreeContentProvider(), new FMLabelProvider());
	}

	public FMOutlineProvider(OutlineTreeContentProvider treeProvider, OutlineLabelProvider labelProvider) {
		super(treeProvider, labelProvider);
	}

	@Override
	public boolean isSupported(IEditorPart part, IFile file) {
		if (file != null) {
			return "xml".equalsIgnoreCase(file.getFileExtension()) && (FMFormatManager.getInstance().hasFormat(EclipseFileSystem.getPath(file)));
		}
		return false;
	}

	@Override
	public void handleUpdate(TreeViewer viewer, IFile iFile) {
		this.viewer = viewer;
		file = iFile;

		final IWorkbench workbench = PlatformUI.getWorkbench();
		final IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
		final IWorkbenchPage page = window.getActivePage();
		final IEditorPart activeEditor = page.getActiveEditor();
		if (activeEditor instanceof FeatureModelEditor) {
			final FeatureModelEditor fTextEditor = (FeatureModelEditor) activeEditor;
			featureModelManager = fTextEditor.getFeatureModelManager();

			// Remove Listener and add the listener again to minimize the listeners held by the provider to one. With a feature model check does not help here
			// as otherwise SyncCollapsedStateAction does not work
			featureModelManager.removeListener(this);
			featureModelManager.addListener(this);
			graphicalFeatureModel = fTextEditor.diagramEditor.getGraphicalFeatureModel();

			getTreeProvider().inputChanged(viewer, null, featureModelManager.getSnapshot());
			setExpandedElements();

			if ((contextMenu == null) || (contextMenu.getFeatureModelManager() != featureModelManager)) {
				contextMenu = new FmOutlinePageContextMenu(fTextEditor.getSite(), fTextEditor, viewer, featureModelManager, true, false);
			}
		}
	}

	@Override
	protected void initContextMenuActions(IMenuManager manager) {
		if (contextMenu != null) {
			contextMenu.fillContextMenu(manager);
		}
	}

	@Override
	protected void initToolbarActions(IToolBarManager manager) {
		syncCollapsedStateAction = new SyncCollapsedStateAction();
		syncCollapsedStateAction.setEnabled(true);
		manager.add(syncCollapsedStateAction);
	}

	@Override
	protected List<IOutlineFilter> getFilters() {
		return null;
	}

	private void setExpandedElements() {
		final ArrayList<Object> expandedElements = new ArrayList<>();
		for (final IGraphicalFeature f : graphicalFeatureModel.getAllFeatures()) {
			if (!f.isCollapsed()) {
				expandedElements.add(f);
			}
		}
		expandedElements.add("Constraints");
		viewer.setExpandedElements(expandedElements.toArray());
	}

	@Override
	public void treeCollapsed(TreeExpansionEvent event) {
		if ((graphicalFeatureModel != null) && syncCollapsedStateAction.isChecked() && (event.getElement() instanceof IFeature)) {
			final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(((IFeature) event.getElement()));
			if (!graphicalFeature.isCollapsed()) {
				graphicalFeature.setCollapsed(true);
				featureModelManager.fireEvent(new FeatureIDEEvent((event.getElement()), EventType.FEATURE_COLLAPSED_CHANGED));
			}
		}

	}

	@Override
	public void treeExpanded(TreeExpansionEvent event) {
		((OutlineLabelProvider) viewer.getLabelProvider()).colorizeItems(viewer.getTree().getItems(), file);
		if ((graphicalFeatureModel != null) && syncCollapsedStateAction.isChecked() && (event.getElement() instanceof IFeature)) {
			final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(((IFeature) event.getElement()));
			if (graphicalFeature.isCollapsed()) {
				graphicalFeature.setCollapsed(false);
				featureModelManager.fireEvent(new FeatureIDEEvent((event.getElement()), EventType.FEATURE_COLLAPSED_CHANGED));
			}
		}
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		final IContentProvider contentProvider = viewer.getContentProvider();
		if (contentProvider != null) {
			switch (event.getEventType()) {
			case MODEL_DATA_OVERWRITTEN:
			case MODEL_DATA_CHANGED:
			case MODEL_DATA_SAVED:
			case MANDATORY_CHANGED:
			case GROUP_TYPE_CHANGED:
			case FEATURE_NAME_CHANGED:
			case FEATURE_ADD_SIBLING:
			case FEATURE_ADD:
			case FEATURE_ADD_ABOVE:
			case FEATURE_DELETE:
			case CONSTRAINT_MODIFY:
			case CONSTRAINT_DELETE:
			case CONSTRAINT_ADD:
			case FEATURE_COLLAPSED_CHANGED:
			case FEATURE_COLLAPSED_ALL_CHANGED:
				contentProvider.inputChanged(viewer, null, file);
				break;
			default:
				break;
			}
		}
	}

	@Override
	public void handleExpandAll(PropertyChangeEvent event) {
		if (syncCollapsedStateAction.isChecked()) {
			final IFeatureModel featureModel = featureModelManager.getSnapshot();
			for (final IFeature f : featureModel.getFeatures()) {
				graphicalFeatureModel.getGraphicalFeature(f).setCollapsed(false);
			}
			featureModelManager.fireEvent(new FeatureIDEEvent(featureModel.getFeatures().iterator(), EventType.FEATURE_COLLAPSED_ALL_CHANGED));
		}
	}

	@Override
	public void handleCollapseAll(PropertyChangeEvent event) {
		if (syncCollapsedStateAction.isChecked()) {
			final IFeatureModel featureModel = featureModelManager.getSnapshot();
			for (final IFeature f : featureModel.getFeatures()) {
				if (!f.getStructure().isRoot()) {
					graphicalFeatureModel.getGraphicalFeature(f).setCollapsed(true);
				}
			}
			featureModelManager.fireEvent(new FeatureIDEEvent(featureModel.getFeatures().iterator(), EventType.FEATURE_COLLAPSED_ALL_CHANGED));
		}
	}

	@Override
	public void selectionChanged(SelectionChangedEvent event) {}

}
