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

import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURE_COLLAPSED;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURE_EXPANDED;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.core.resources.IFile;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.IContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeExpansionEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.operations.RedoActionHandler;
import org.eclipse.ui.operations.UndoActionHandler;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.CollapseAllOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.CollapseFeatureOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.views.outline.FmOutlinePageContextMenu;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.action.ImportFeatureModelAction;
import de.ovgu.featureide.fm.ui.views.outline.custom.action.SyncCollapsedStateAction;
import de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter;

/**
 * FMOutlineProvider provides specifically the data for the currently shown feature model in a {@link FeatureModelEditor}.
 *
 * @author Christopher Sontag
 * @author Thomas Thuem
 * @author Sebastian Krieter
 * @author Joshua Sprey
 * @author Chico Sundermann
 * @author Benedikt Jutz
 * @author Kevin Jedelhauser
 * @author Johannes Herschel
 */
public class FMOutlineProvider extends OutlineProvider implements IEventListener {

	private SyncCollapsedStateAction syncCollapsedStateAction;
	private IGraphicalFeatureModel graphicalFeatureModel;
	private FmOutlinePageContextMenu contextMenu;

	private FeatureModelEditor featureModelEditor;

	public FMOutlineProvider() {
		super(new FMTreeContentProvider(), new FMLabelProvider());
	}

	public FMOutlineProvider(OutlineTreeContentProvider treeProvider, OutlineLabelProvider labelProvider) {
		super(treeProvider, labelProvider);
	}

	@Override
	public void setActiveEditor(IEditorPart part) {
		if (part == null) {
			featureModelEditor = null;
			featureModelManager = null;
		} else if (part instanceof FeatureModelEditor) {
			featureModelEditor = (FeatureModelEditor) part;
			featureModelManager = featureModelEditor.getFeatureModelManager();
		}
	}

	/**
	 * FMOutlineProvider supports feature models in the FeatureIDE format (File ending .xml), and UVL models (File ending .uvl).
	 *
	 * @see {@link OutlineProvider#isSupported(IEditorPart, IFile)}
	 */
	@Override
	public boolean isSupported(IEditorPart part, IFile file) {
		if (file == null) {
			return false;
		}

		final String extension = file.getFileExtension();
		return ("xml".equalsIgnoreCase(extension) || "uvl".equalsIgnoreCase(extension))
			&& (FMFormatManager.getInstance().hasFormat(EclipseFileSystem.getPath(file)));
	}

	@Override
	public void handleUpdate(TreeViewer viewer, IFile iFile) {
		this.viewer = viewer;
		file = iFile;

		if (featureModelEditor != null) {
			// Remove Listener and add the listener again to minimize the listeners held by the provider to one. With a feature model check does not help here
			// as otherwise SyncCollapsedStateAction does not work
			featureModelManager.removeListener(this);
			featureModelManager.addListener(this);
			graphicalFeatureModel = featureModelEditor.diagramEditor.getGraphicalFeatureModel();

			getTreeProvider().inputChanged(viewer, null, featureModelManager.getSnapshot());
			setExpandedElements();

			if ((contextMenu == null) || (contextMenu.getFeatureModelManager() != featureModelManager)) {
				contextMenu = new FmOutlinePageContextMenu(featureModelEditor.getSite(), featureModelEditor, viewer, featureModelManager, true, false);
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
		final ImportFeatureModelAction importFeatureModelAction = new ImportFeatureModelAction(featureModelManager);
		manager.add(importFeatureModelAction);

		syncCollapsedStateAction = new SyncCollapsedStateAction();
		syncCollapsedStateAction.addPropertyChangeListener(new IPropertyChangeListener() {

			@Override
			public void propertyChange(PropertyChangeEvent event) {
				setExpandedElements();
			}
		});
		syncCollapsedStateAction.setEnabled(true);
		manager.add(syncCollapsedStateAction);
	}

	@Override
	protected void initGlobalActions(IViewSite site) {
		final IActionBars actionBars = site.getActionBars();
		final IUndoContext undoContext = (IUndoContext) featureModelManager.getUndoContext();
		actionBars.setGlobalActionHandler(ActionFactory.UNDO.getId(), new UndoActionHandler(site, undoContext));
		actionBars.setGlobalActionHandler(ActionFactory.REDO.getId(), new RedoActionHandler(site, undoContext));
		actionBars.updateActionBars();
	}

	@Override
	protected List<IOutlineFilter> getFilters() {
		return null;
	}

	private void setExpandedElements() {
		if (syncCollapsedStateAction.isChecked()) {
			final ArrayList<Object> expandedElements = new ArrayList<>();
			for (final IGraphicalFeature f : graphicalFeatureModel.getAllFeatures()) {
				if (!f.isCollapsed()) {
					expandedElements.add(f.getObject());
				}
			}
			expandedElements.add("Constraints");
			viewer.setExpandedElements(expandedElements.toArray());
		}
	}

	@Override
	public void treeCollapsed(TreeExpansionEvent event) {
		if ((graphicalFeatureModel != null) && syncCollapsedStateAction.isChecked() && (event.getElement() instanceof IFeature)) {
			final IFeature feature = (IFeature) event.getElement();
			final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(feature);
			if (!graphicalFeature.isCollapsed()) {
				FeatureModelOperationWrapper.run(new CollapseFeatureOperation(feature.getName(), graphicalFeatureModel, SET_FEATURE_COLLAPSED));
			}
		}
	}

	@Override
	public void treeExpanded(TreeExpansionEvent event) {
		((OutlineLabelProvider) viewer.getLabelProvider()).colorizeItems(viewer.getTree().getItems(), file);
		if ((graphicalFeatureModel != null) && syncCollapsedStateAction.isChecked() && (event.getElement() instanceof IFeature)) {
			final IFeature feature = (IFeature) event.getElement();
			final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(feature);
			if (graphicalFeature.isCollapsed()) {
				FeatureModelOperationWrapper.run(new CollapseFeatureOperation(feature.getName(), graphicalFeatureModel, SET_FEATURE_EXPANDED));
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
			FeatureModelOperationWrapper.run(new CollapseAllOperation(graphicalFeatureModel, false));
		}
	}

	@Override
	public void handleCollapseAll(PropertyChangeEvent event) {
		if (syncCollapsedStateAction.isChecked()) {
			FeatureModelOperationWrapper.run(new CollapseAllOperation(graphicalFeatureModel, true));
		}
	}

	@Override
	public void selectionChanged(SelectionChangedEvent event) {}

}
