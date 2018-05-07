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

	private TreeViewer viewer;
	private IFile file;
	private IFeatureModel featureModel;
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
			featureModel = fTextEditor.getFeatureModel();

			// Remove Listener and add the listener again to minimize the listeners held by the provider to one. With a feature model check does not help here
			// as otherwise SyncCollapsedStateAction does not work
			featureModel.removeListener(this);
			featureModel.addListener(this);
			graphicalFeatureModel = fTextEditor.diagramEditor.getGraphicalFeatureModel();

			getTreeProvider().inputChanged(viewer, null, featureModel);
			setExpandedElements();

			if ((contextMenu == null) || (contextMenu.getFeatureModel() != featureModel)) {
				contextMenu = new FmOutlinePageContextMenu(fTextEditor.getSite(), fTextEditor, viewer, featureModel, true, false);
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

	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	private void setExpandedElements() {
		final FMTreeContentProvider contentProvider = (FMTreeContentProvider) getTreeProvider();
		final ArrayList<Object> expandedElements = new ArrayList<>();
		if (contentProvider.getFeatureModel() != null) {
			for (final IFeature f : contentProvider.getFeatureModel().getFeatures()) {
				if (f.getStructure().hasChildren() && !graphicalFeatureModel.getGraphicalFeature(f).isCollapsed()) {
					expandedElements.add(f);
				}
			}
			expandedElements.add("Constraints");
			viewer.setExpandedElements(expandedElements.toArray());
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeViewerListener#treeCollapsed(org.eclipse.jface.viewers.TreeExpansionEvent)
	 */
	@Override
	public void treeCollapsed(TreeExpansionEvent event) {
		if ((graphicalFeatureModel != null) && syncCollapsedStateAction.isChecked() && (event.getElement() instanceof IFeature)) {
			final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(((IFeature) event.getElement()));
			if (!graphicalFeature.isCollapsed()) {
				graphicalFeature.setCollapsed(true);
				featureModel.fireEvent(new FeatureIDEEvent((event.getElement()), EventType.COLLAPSED_CHANGED));
			}
		}

	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeViewerListener#treeExpanded(org.eclipse.jface.viewers.TreeExpansionEvent)
	 */
	@Override
	public void treeExpanded(TreeExpansionEvent event) {
		((OutlineLabelProvider) viewer.getLabelProvider()).colorizeItems(viewer.getTree().getItems(), file);
		if ((graphicalFeatureModel != null) && syncCollapsedStateAction.isChecked() && (event.getElement() instanceof IFeature)) {
			final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(((IFeature) event.getElement()));
			if (graphicalFeature.isCollapsed()) {
				graphicalFeature.setCollapsed(false);
				featureModel.fireEvent(new FeatureIDEEvent((event.getElement()), EventType.COLLAPSED_CHANGED));
			}
		}
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.base.event.IEventListener#propertyChange(de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent)
	 */
	@Override
	public void propertyChange(FeatureIDEEvent event) {
		viewer.getContentProvider().inputChanged(viewer, null, file);
	}

	@Override
	public void handleExpandAll(PropertyChangeEvent event) {
		if (syncCollapsedStateAction.isChecked()) {
			for (final IFeature f : featureModel.getFeatures()) {
				graphicalFeatureModel.getGraphicalFeature(f).setCollapsed(false);
			}
			featureModel.fireEvent(new FeatureIDEEvent(featureModel.getFeatures().iterator(), EventType.COLLAPSED_ALL_CHANGED));
		}
	}

	@Override
	public void handleCollapseAll(PropertyChangeEvent event) {
		if (syncCollapsedStateAction.isChecked()) {
			for (final IFeature f : featureModel.getFeatures()) {
				if (!f.getStructure().isRoot()) {
					graphicalFeatureModel.getGraphicalFeature(f).setCollapsed(true);
				}
			}
			featureModel.fireEvent(new FeatureIDEEvent(featureModel.getFeatures().iterator(), EventType.COLLAPSED_ALL_CHANGED));
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ISelectionChangedListener#selectionChanged(org.eclipse.jface.viewers.SelectionChangedEvent)
	 */
	@Override
	public void selectionChanged(SelectionChangedEvent event) {

	}

}
