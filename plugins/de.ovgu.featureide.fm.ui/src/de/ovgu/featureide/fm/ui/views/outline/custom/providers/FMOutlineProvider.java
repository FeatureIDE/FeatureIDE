package de.ovgu.featureide.fm.ui.views.outline.custom.providers;

import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_FEATURE_BELOW;
import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE;

import java.beans.PropertyChangeListener;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.commands.operations.ObjectUndoContext;
import org.eclipse.core.resources.IFile;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPartViewer;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeExpansionEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.internal.win32.GESTURECONFIG;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AbstractAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AlternativeAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AndAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateCompoundAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateLayerAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.DeleteAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.DeleteAllAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.EditConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.HiddenAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.MandatoryAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.OrAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors.SetFeatureColorAction;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.action.SyncCollapsedStateAction;
import de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter;
import de.ovgu.featureide.fm.ui.views.outline.standard.FmOutlineGroupStateStorage;
import de.ovgu.featureide.fm.ui.views.outline.standard.FmTreeContentProvider;

public class FMOutlineProvider extends OutlineProvider implements IEventListener {

	private TreeViewer viewer;
	private IFile file;
	private IFeatureModel featureModel;
	private SyncCollapsedStateAction syncCollapsedStateAction;
	private IGraphicalFeatureModel graphicalFeatureModel;
	private IStructuredSelection selection;
	private SetFeatureColorAction setFeatureColorAction;
	private MandatoryAction mAction;
	private HiddenAction hAction;
	private AbstractAction aAction;
	private DeleteAction dAction;
	private DeleteAllAction dAAction;
	private CreateConstraintAction ccAction;
	private EditConstraintAction ecAction;
	private CreateCompoundAction cAction;
	private CreateLayerAction clAction;
	private OrAction oAction;
	private AndAction andAction;
	private AlternativeAction altAction;

	public FMOutlineProvider() {
		super(new FmTreeContentProvider(), new FMLabelProvider());
	}

	public FMOutlineProvider(OutlineTreeContentProvider treeProvider, OutlineLabelProvider labelProvider) {
		super(treeProvider, labelProvider);
	}

	@Override
	public boolean isSupported(IFile file) {
		return file.getFileExtension().equalsIgnoreCase("xml") && FeatureModelManager.getInstance(Paths.get(file.getLocationURI())) != null;
	}

	@Override
	public void handleUpdate(TreeViewer viewer, IFile iFile) {
		this.viewer = viewer;
		this.file = iFile;

		IWorkbench workbench = PlatformUI.getWorkbench();
		IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
		IWorkbenchPage page = window.getActivePage();
		IEditorPart activeEditor = page.getActiveEditor();
		FeatureModelEditor fTextEditor = (FeatureModelEditor) activeEditor;
		featureModel = fTextEditor.diagramEditor.getFeatureModel();
		featureModel.addListener(this);
		graphicalFeatureModel = fTextEditor.diagramEditor.getGraphicalFeatureModel();

		((FmTreeContentProvider) getTreeProvider()).setGraphicalFeatureModel(graphicalFeatureModel);
		setExpandedElements();

		if (featureModel != null && setFeatureColorAction == null) {
			setFeatureColorAction = new SetFeatureColorAction(viewer, featureModel);
			setFeatureColorAction.setEnabled(true);
			mAction = new MandatoryAction(viewer, featureModel);
			hAction = new HiddenAction(viewer, featureModel);
			aAction = new AbstractAction(viewer, featureModel, (ObjectUndoContext) featureModel.getUndoContext());
			dAction = new DeleteAction(viewer, featureModel);
			dAAction = new DeleteAllAction(viewer, featureModel);
			ccAction = new CreateConstraintAction(viewer, featureModel);
			ecAction = new EditConstraintAction(viewer, featureModel);
			cAction = new CreateCompoundAction(viewer, featureModel);
			clAction = new CreateLayerAction(viewer, featureModel);

			oAction = new OrAction(viewer, featureModel);
			andAction = new AndAction(viewer, featureModel);
			altAction = new AlternativeAction(viewer, featureModel);
		}
	}

	@Override
	public void selectionChanged(SelectionChangedEvent event) {
		if (viewer == null || viewer.getSelection() == null)
			return;

		IWorkbench workbench = PlatformUI.getWorkbench();
		IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
		IWorkbenchPage page = window.getActivePage();
		IEditorPart activeEditor = page.getActiveEditor();
		FeatureModelEditor fTextEditor = (FeatureModelEditor) activeEditor;

		selection = (IStructuredSelection) viewer.getSelection();

		EditPart part;
		if (selection.getFirstElement() instanceof IFeature) {
			IFeature feat = (IFeature) selection.getFirstElement();
			part = (EditPart) fTextEditor.diagramEditor.getEditPartRegistry().get(feat);
		} else if (selection.getFirstElement() instanceof IConstraint) {
			IConstraint constr = (IConstraint) selection.getFirstElement();
			part = (EditPart) fTextEditor.diagramEditor.getEditPartRegistry().get(constr);
		} else {
			return;
		}
		// workaround for bug: close the FM-editor and open it again, 
		//					-> selecting something at the outline causes a null-pointer exception
		if (part == null) {
			return;
		}
		((GraphicalViewerImpl) fTextEditor.diagramEditor).setSelection(new StructuredSelection(part));

		EditPartViewer view = part.getViewer();
		if (view != null) {
			view.reveal(part);
		}
	}

	@Override
	protected void initContextMenuActions(IMenuManager manager) {
		if (featureModel != null) {
			if (selection != null) {
				Object sel = selection.getFirstElement();
				setFeatureColorAction.setFeatureModel(featureModel);

				if (sel instanceof FmOutlineGroupStateStorage) {
					IFeature feature = ((FmOutlineGroupStateStorage) sel).getFeature();
					if (feature instanceof ExtendedFeature && ((ExtendedFeature) feature).isFromExtern()) {
						return;
					}
					manager.add(andAction);
					manager.add(oAction);
					manager.add(altAction);
				}
				if (sel instanceof IFeature) {

					manager.add(cAction);

					clAction.setText(CREATE_FEATURE_BELOW);
					manager.add(clAction);

					dAction.setText(DELETE);
					manager.add(dAction);

					manager.add(dAAction);

					manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));

					if (oAction.isEnabled() || altAction.isEnabled() || andAction.isEnabled()) {
						manager.add(andAction);
						manager.add(oAction);
						manager.add(altAction);
						manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
					}

					manager.add(mAction);
					manager.add(aAction);
					manager.add(hAction);
					manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
					manager.add(setFeatureColorAction);
				}
				if (sel instanceof IConstraint) {
					manager.add(ccAction);
					manager.add(ecAction);

					dAction.setText(DELETE);
					manager.add(dAction);
				}
				if (sel instanceof String)
					if (sel.equals(CONSTRAINTS))
						manager.add(ccAction);
			}
		}
	}

	@Override
	protected void initToolbarActions(IToolBarManager manager) {
		syncCollapsedStateAction = new SyncCollapsedStateAction(viewer, true);
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
		FmTreeContentProvider contentProvider = (FmTreeContentProvider) this.getTreeProvider();
		ArrayList<Object> expandedElements = new ArrayList<>();
		for (IFeature f : contentProvider.getFeatureModel().getFeatures()) {
			if (f.getStructure().hasChildren() && !contentProvider.getGraphicalFeatureModel().getGraphicalFeature(f).isCollapsed())
				expandedElements.add(f);
		}
		expandedElements.add("Constraints");
		viewer.setExpandedElements(expandedElements.toArray());
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeViewerListener#treeCollapsed(org.eclipse.jface.viewers.TreeExpansionEvent)
	 */
	@Override
	public void treeCollapsed(TreeExpansionEvent event) {
		if (graphicalFeatureModel != null && syncCollapsedStateAction.isChecked() && event.getElement() instanceof IFeature) {
			IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(((IFeature) event.getElement()));
			if (!graphicalFeature.isCollapsed()) {
				graphicalFeature.setCollapsed(true);
				featureModel.fireEvent(new FeatureIDEEvent(((IFeature) event.getElement()), EventType.COLLAPSED_CHANGED));
			}
		}

	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeViewerListener#treeExpanded(org.eclipse.jface.viewers.TreeExpansionEvent)
	 */
	@Override
	public void treeExpanded(TreeExpansionEvent event) {
		((OutlineLabelProvider) viewer.getLabelProvider()).colorizeItems(viewer.getTree().getItems(), file);
		if (graphicalFeatureModel != null && syncCollapsedStateAction.isChecked() && event.getElement() instanceof IFeature) {
			IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(((IFeature) event.getElement()));
			if (graphicalFeature.isCollapsed()) {
				graphicalFeature.setCollapsed(false);
				featureModel.fireEvent(new FeatureIDEEvent(((IFeature) event.getElement()), EventType.COLLAPSED_CHANGED));
			}
		}
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.base.event.IEventListener#propertyChange(de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent)
	 */
	@Override
	public void propertyChange(FeatureIDEEvent event) {
		viewer.getContentProvider().inputChanged(viewer, null, file);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider#handleExpandAll(org.eclipse.jface.util.PropertyChangeEvent)
	 */
	@Override
	public void handleExpandAll(PropertyChangeEvent event) {
		if (syncCollapsedStateAction.isChecked()) {
			for (IFeature f : featureModel.getFeatures()) {
				graphicalFeatureModel.getGraphicalFeature(f).setCollapsed(false);
			}
			featureModel.fireEvent(new FeatureIDEEvent(featureModel.getFeatures().iterator(), EventType.COLLAPSED_ALL_CHANGED));
		}
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider#handleCollapseAll(org.eclipse.jface.util.PropertyChangeEvent)
	 */
	@Override
	public void handleCollapseAll(PropertyChangeEvent event) {
		if (syncCollapsedStateAction.isChecked()) {
			for (IFeature f : featureModel.getFeatures()) {
				if (!f.getStructure().isRoot()) {
					graphicalFeatureModel.getGraphicalFeature(f).setCollapsed(true);
				}
			}
			featureModel.fireEvent(new FeatureIDEEvent(featureModel.getFeatures().iterator(), EventType.COLLAPSED_ALL_CHANGED));
		}
	}

}
