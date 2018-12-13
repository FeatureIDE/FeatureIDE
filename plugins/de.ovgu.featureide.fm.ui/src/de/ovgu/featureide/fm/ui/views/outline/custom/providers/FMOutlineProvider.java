package de.ovgu.featureide.fm.ui.views.outline.custom.providers;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.util.PropertyChangeEvent;
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
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
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
	public boolean isSupported(IFile file) {
		if (file != null) {
			return file.getFileExtension().equalsIgnoreCase("xml") && (FeatureModelManager.getInstance(Paths.get(file.getLocationURI())) != null);
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
			final IFeatureModel featureModel = featureModelManager.editObject();
			featureModel.removeListener(this);
			featureModel.addListener(this);
			graphicalFeatureModel = fTextEditor.diagramEditor.getGraphicalFeatureModel();

			getTreeProvider().inputChanged(viewer, null, featureModel);
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
		syncCollapsedStateAction = new SyncCollapsedStateAction(viewer);
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
			expandedElements.add("Constraints");
			viewer.setExpandedElements(expandedElements.toArray());
		}
	}

	@Override
	public void treeCollapsed(TreeExpansionEvent event) {
		if ((graphicalFeatureModel != null) && syncCollapsedStateAction.isChecked() && (event.getElement() instanceof IFeature)) {
			final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(((IFeature) event.getElement()));
			if (!graphicalFeature.isCollapsed()) {
				graphicalFeature.setCollapsed(true);
				featureModelManager.editObject().fireEvent(new FeatureIDEEvent((event.getElement()), EventType.COLLAPSED_CHANGED));
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
				featureModelManager.editObject().fireEvent(new FeatureIDEEvent((event.getElement()), EventType.COLLAPSED_CHANGED));
			}
		}
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		viewer.getContentProvider().inputChanged(viewer, null, file);
	}

	@Override
	public void handleExpandAll(PropertyChangeEvent event) {
		if (syncCollapsedStateAction.isChecked()) {
			final IFeatureModel featureModel = featureModelManager.getSnapshot();
			for (final IFeature f : featureModel.getFeatures()) {
				graphicalFeatureModel.getGraphicalFeature(f).setCollapsed(false);
			}
			featureModelManager.editObject().fireEvent(new FeatureIDEEvent(featureModel.getFeatures().iterator(), EventType.COLLAPSED_ALL_CHANGED));
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
			featureModelManager.editObject().fireEvent(new FeatureIDEEvent(featureModel.getFeatures().iterator(), EventType.COLLAPSED_ALL_CHANGED));
		}
	}

	@Override
	public void selectionChanged(SelectionChangedEvent event) {}

}
