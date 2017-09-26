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
package de.ovgu.featureide.fm.ui.editors;

import static de.ovgu.featureide.fm.core.localization.StringTable.MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.MODEL_SHOULD_BE_SAVED_AFTER_RENAMINGS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SAVE_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.SAVE_RESOURCES;
import static de.ovgu.featureide.fm.core.localization.StringTable.SOME_MODIFIED_RESOURCES_MUST_BE_SAVED_BEFORE_SAVING_THE_FEATUREMODEL_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_FEATURE_MODEL_IS_VOID_COMMA__I_E__COMMA__IT_CONTAINS_NO_PRODUCTS;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.operations.IOperationHistory;
import org.eclipse.core.commands.operations.IOperationHistoryListener;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.core.commands.operations.ObjectUndoContext;
import org.eclipse.core.commands.operations.OperationHistoryEvent;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.gef.ui.actions.SelectAllAction;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPartSite;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.dialogs.ListDialog;
import org.eclipse.ui.ide.IGotoMarker;
import org.eclipse.ui.operations.RedoActionHandler;
import org.eclipse.ui.operations.UndoActionHandler;
import org.eclipse.ui.part.MultiPageEditorPart;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.ModelMarkerHandler;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFileManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.GraphicsExporter;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.FeatureModelEditorContributor;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;
import de.ovgu.featureide.fm.ui.views.outline.standard.FmOutlinePage;

/**
 * A multi page editor to edit feature models. If the model file contains errors, markers will be created on save.
 *
 * @author Thomas Thuem
 * @author Christian Becker
 */
public class FeatureModelEditor extends MultiPageEditorPart implements IEventListener, IResourceChangeListener {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureModelEditor";

	public FeatureDiagramEditor diagramEditor;
	public FeatureOrderEditor featureOrderEditor;
	public FeatureModelTextEditorPage textEditor;

	public LinkedList<IFeatureModelEditorPage> extensionPages = new LinkedList<>();

	private ModelMarkerHandler<IFile> markerHandler;
	boolean isPageModified = false;
	IFileManager<IFeatureModel> fmManager;

	private boolean closeEditor;

	private int currentPageIndex;
	private int operationCounter;

	private FmOutlinePage outlinePage;

	private FMPrintAction printAction;
	private SelectAllAction selectAllAction;
	private UndoActionHandler undoAction;
	private RedoActionHandler redoAction;

	public FeatureModelEditor() {
		super();
	}

	public FeatureModelEditor(IFileManager<IFeatureModel> fmManager) {
		super();
		this.fmManager = fmManager;
	}

	public boolean checkModel(String source) {
		IFeatureModelFactory manager;
		try {
			manager = FMFactoryManager.getFactory(markerHandler.getModelFile().getLocation().toString(), fmManager.getFormat());
		} catch (final NoSuchExtensionException e) {
			FMUIPlugin.getDefault().logError(e);
			manager = FMFactoryManager.getDefaultFactory();
		}
		final IFeatureModel model = manager.createFeatureModel();

		if (getEditorInput() instanceof IFileEditorInput) {
			final IFileEditorInput input = (IFileEditorInput) getEditorInput();
			final IFile sourceFile = input.getFile();
			model.setSourceFile(sourceFile.getRawLocation().toFile().toPath());
		}
		final ProblemList warnings = fmManager.getFormat().getInstance().read(model, source);
		createModelFileMarkers(warnings);

		return !warnings.containsError();
	}

	@Override
	public void init(IEditorSite site, IEditorInput input) throws PartInitException {
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
		super.init(site, input);
	}

	@Override
	public void dispose() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
		FMPropertyManager.unregisterEditor(this);
		if (diagramEditor != null) {
			diagramEditor.dispose();
			getFeatureModel().removeListener(diagramEditor);
			fmManager.removeListener(diagramEditor);
			fmManager.override();
		}
		super.dispose();
	}

	@Override
	public void doSave(final IProgressMonitor monitor) {
		if (!saveEditors()) {
			return;
		}

		diagramEditor.doSave(monitor);
		featureOrderEditor.doSave(monitor);
		final IFeatureModel featureModel = getFeatureModel();
		featureModel.getRenamingsManager().performRenamings(featureModel.getSourceFile());
		for (final IFeatureModelEditorPage page : extensionPages) {
			page.doSave(monitor);
		}

		// write the model to the file
		if (getActivePage() == textEditor.getIndex()) {
			textEditor.executeSaveOperation();
			// textEditor.updateDiagram();
			fmManager.externalSave(new Runnable() {

				@Override
				public void run() {
					textEditor.doSave(monitor);
				}
			});
		} else {
			fmManager.save();
		}

		setPageModified(false);
	}

	@Override
	public void doSaveAs() {
		GraphicsExporter.exportAs(getFeatureModel(), diagramEditor);
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	@Override
	public Object getAdapter(Class adapter) {
		if (IContentOutlinePage.class.equals(adapter)) {
			if (getOutlinePage() == null) {
				setOutlinePage(new FmOutlinePage(null, this));
				getOutlinePage().setInput(getFeatureModel());
			}
			return getOutlinePage();
		}
		if (IGotoMarker.class.equals(adapter)) {
			if (getActivePage() != getDiagramEditorIndex()) {
				setActivePage(getDiagramEditorIndex());
			}
		}
		final Object o = diagramEditor.getAdapter(adapter);
		if (o != null) {
			return o;
		}
		return super.getAdapter(adapter);
	}

	public IAction getDiagramAction(String workbenchActionID) {
		if (ActionFactory.PRINT.getId().equals(workbenchActionID)) {
			return printAction;
		}
		if (ActionFactory.SELECT_ALL.getId().equals(workbenchActionID)) {
			return selectAllAction;
		}
		if (ActionFactory.UNDO.getId().equals(workbenchActionID)) {
			return undoAction;
		}
		if (ActionFactory.REDO.getId().equals(workbenchActionID)) {
			return redoAction;
		}
		final IAction action = diagramEditor.getDiagramAction(workbenchActionID);
		if (action != null) {
			return action;
		}
		FMCorePlugin.getDefault().logInfo("The following workbench action is not registered at the feature diagram editor: " + workbenchActionID);
		return null;
	}

	public IFeatureModel getFeatureModel() {
		return fmManager.editObject();
	}

	public IFile getModelFile() {
		return markerHandler.getModelFile();
	}

	public IFeatureModel getOriginalFeatureModel() {
		return fmManager.getObject();
	}

	public FmOutlinePage getOutlinePage() {
		return outlinePage;
	}

	public ITextEditor getSourceEditor() {
		return textEditor;
	}

	@Override
	public boolean isDirty() {
		return isPageModified || super.isDirty();
	}

	@Override
	public boolean isSaveAsAllowed() {
		return true;
	}

	@Override
	public void resourceChanged(IResourceChangeEvent event) {
		if (event.getResource() == null) {
			return;
		}
		if (event.getResource().getType() == IResource.PROJECT) {
			closeEditor = true;
		}
		final IEditorInput input = getEditorInput();
		if (!(input instanceof IFileEditorInput)) {
			return;
		}
		final IFile inputFile = ((IFileEditorInput) input).getFile();

		/*
		 * Closes editor if resource is deleted
		 */
		if ((event.getType() == IResourceChangeEvent.POST_CHANGE) && closeEditor) {
			final List<IResource> deletedlist = new ArrayList<>();
			final IResourceDelta inputFileDelta = event.getDelta().findMember(inputFile.getFullPath());
			if (inputFileDelta != null) {
				final IResourceDeltaVisitor visitor = new IResourceDeltaVisitor() {

					@Override
					public boolean visit(IResourceDelta delta) {
						// only interested in removal changes
						if (((delta.getFlags() & IResourceDelta.REMOVED) == 0) && closeEditor) {
							deletedlist.add(delta.getResource());
						}
						return true;
					}
				};
				try {
					inputFileDelta.accept(visitor);
				} catch (final CoreException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}
			if ((deletedlist.size() > 0) && deletedlist.contains(inputFile)) {
				Display.getDefault().asyncExec(new Runnable() {

					@Override
					public void run() {
						if (getSite() == null) {
							return;
						}
						if (getSite().getWorkbenchWindow() == null) {
							return;
						}
						final IWorkbenchPage[] pages = getSite().getWorkbenchWindow().getPages();
						for (int i = 0; i < pages.length; i++) {
							final IEditorPart editorPart = pages[i].findEditor(input);
							pages[i].closeEditor(editorPart, true);
						}
					}
				});
			}
		}

		/*
		 * Closes all editors with this editor input on project close.
		 */
		final IResource res = event.getResource();
		if ((event.getType() == IResourceChangeEvent.PRE_CLOSE) || closeEditor) {
			Display.getDefault().asyncExec(new Runnable() {

				@Override
				public void run() {
					final IWorkbenchPartSite site = getSite();
					if (site == null) {
						return;
					}
					final IWorkbenchWindow workbenchWindow = site.getWorkbenchWindow();
					if (workbenchWindow == null) {
						return;
					}
					final IWorkbenchPage[] pages = workbenchWindow.getPages();
					for (int i = 0; i < pages.length; i++) {
						if (inputFile.getProject().equals(res)) {
							final IEditorPart editorPart = pages[i].findEditor(input);
							pages[i].closeEditor(editorPart, true);
						}
					}
				}
			});
		}
	}

	/**
	 * Open a dialog to save the model.
	 */
	public void saveModelForConsistentRenamings() {
		final LinkedList<String> editor = new LinkedList<String>();
		editor.add(getModelFile().getName());

		final ListDialog dialog = new ListDialog(getSite().getWorkbenchWindow().getShell());
		dialog.setAddCancelButton(true);
		dialog.setContentProvider(new ArrayContentProvider());
		dialog.setLabelProvider(new LabelProvider());
		dialog.setInput(editor);
		dialog.setInitialElementSelections(editor);
		dialog.setTitle(SAVE_FEATURE_MODEL);
		dialog.setHelpAvailable(false);
		dialog.setMessage(MODEL_SHOULD_BE_SAVED_AFTER_RENAMINGS_);
		dialog.open();

		if (dialog.getResult() != null) {
			doSave(null);
		}
	}

	/**
	 * This is just a call to the private method {@link #setActivePage(int)}.
	 *
	 * @param index
	 */
	public void setActiveEditorPage(int index) {
		setActivePage(index);
	}

	@Override
	public void setFocus() {
		if (getActivePage() == getDiagramEditorIndex()) {
			diagramEditor.getControl().setFocus();
		} else {
			textEditor.setFocus();
		}
	}

	public void setPageModified(boolean modified) {
		if (!modified) {
			operationCounter = 0;
		}
		isPageModified = modified;
		firePropertyChange(PROP_DIRTY);
	}

	@Override
	protected void createPages() {
		createActions();
		createDiagramPage();
		createFeatureOrderPage();
		createExtensionPages();
		createSourcePage();
		currentPageIndex = 0;
		// if there are errors in the model file, go to source page
		if (!checkModel(textEditor.getCurrentContent())) {
			setActivePage(getTextEditorIndex());
		} else {
			diagramEditor.getControl().getDisplay().asyncExec(new Runnable() {

				@Override
				public void run() {
					diagramEditor.setContents(diagramEditor.getGraphicalFeatureModel());
					pageChange(getDiagramEditorIndex());
					diagramEditor.internRefresh(false);
					diagramEditor.analyzeFeatureModel();
				}
			});
		}
	}

	@Override
	protected void handlePropertyChange(int propertyId) {
		if (propertyId == PROP_DIRTY) {
			isPageModified = isDirty();
		}
		super.handlePropertyChange(propertyId);
	}

	@Override
	protected void pageChange(int newPageIndex) {
		if (getPage(currentPageIndex).allowPageChange(newPageIndex)) {
			final IEditorActionBarContributor contributor = getEditorSite().getActionBarContributor();
			if (contributor instanceof FeatureModelEditorContributor) {
				((FeatureModelEditorContributor) contributor).setActivePage(this, newPageIndex);
			}
			getPage(currentPageIndex).pageChangeFrom(newPageIndex);
			getPage(newPageIndex).pageChangeTo(currentPageIndex);
			currentPageIndex = newPageIndex;
			super.pageChange(newPageIndex);
		} else {
			setActiveEditorPage(currentPageIndex);
		}
	}

	@Override
	protected void setInput(IEditorInput input) {
		// Cast is necessary, don't remove
		markerHandler = new ModelMarkerHandler<>((IFile) input.getAdapter(IFile.class));
		setPartName(getModelFile().getProject().getName() + MODEL);
		setTitleToolTip(input.getToolTipText());

		super.setInput(input);

		final Path path = markerHandler.getModelFile().getLocation().toFile().toPath();
		fmManager = FeatureModelManager.getInstance(path);
		createModelFileMarkers(fmManager.getLastProblems());

		// TODO _Interfaces Removed Code
		// FeatureUIHelper.showHiddenFeatures(featureModel.getGraphicRepresenation().getLayout().showHiddenFeatures(), featureModel);
		// FeatureUIHelper.setVerticalLayoutBounds(featureModel.getGraphicRepresenation().getLayout().verticalLayout(), featureModel);

		getExtensions();

		FMPropertyManager.registerEditor(this);
		// featureModel.getColorschemeTable().readColorsFromFile(file.getProject());
	}

	void createDiagramPage() {
		diagramEditor = new FeatureDiagramEditor(this, getContainer());
		fmManager.addListener(diagramEditor);
		getFeatureModel().addListener(diagramEditor);
		diagramEditor.setIndex(addPage(diagramEditor.getControl()));
		setPageText(getDiagramEditorIndex(), diagramEditor.getPageText());
		diagramEditor.initEditor();
	}

	void createSourcePage() {
		closeEditor = false;
		textEditor = new FeatureModelTextEditorPage();
		textEditor.setFeatureModelEditor(this);
		try {
			textEditor.setIndex(addPage(textEditor, getEditorInput()));
			setPageText(textEditor.getIndex(), textEditor.getPageText());
		} catch (final PartInitException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	private void createActions() {
		final IOperationHistory history = PlatformUI.getWorkbench().getOperationSupport().getOperationHistory();
		history.addOperationHistoryListener(new IOperationHistoryListener() {

			@Override
			public void historyNotification(OperationHistoryEvent event) {
				if (!hasFMUndoContext(event)) {
					return;
				}
				if ((event.getEventType() == OperationHistoryEvent.DONE) || (event.getEventType() == OperationHistoryEvent.REDONE)) {
					operationCounter++;
				}
				if (event.getEventType() == OperationHistoryEvent.UNDONE) {
					operationCounter--;
				}
				if (operationCounter == 0) {
					setPageModified(false);
				}
			}

			/**
			 * returns true if the event matches the FMUndoContext
			 *
			 * @param event
			 * @param hasFMContext
			 */
			private boolean hasFMUndoContext(OperationHistoryEvent event) {
				for (final IUndoContext c : event.getOperation().getContexts()) {
					if (c.matches((IUndoContext) getFeatureModel().getUndoContext())) {
						return true;
					}
				}
				return false;
			}

		});
		final ObjectUndoContext undoContext = new ObjectUndoContext(this);
		getFeatureModel().setUndoContext(undoContext);

		printAction = new FMPrintAction(this);
		selectAllAction = new SelectAllAction(this);

		final IWorkbenchPartSite site = getSite();
		undoAction = new UndoActionHandler(site, undoContext);
		redoAction = new RedoActionHandler(site, undoContext);
	}

	private void createExtensionPages() {
		for (IFeatureModelEditorPage page : extensionPages) {
			try {
				page.setFeatureModelEditor(this);
				page = page.getPage(getContainer());
				if (page instanceof IEditorPart) {
					page.setIndex(addPage((IEditorPart) page, getEditorInput()));
				} else {
					page.setIndex(addPage(page.getControl()));
				}
				setPageText(page.getIndex(), page.getPageText());
				page.initEditor();
			} catch (final PartInitException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}

	private void createFeatureOrderPage() {
		featureOrderEditor = new FeatureOrderEditor(this);
		try {
			featureOrderEditor.setIndex(addPage(featureOrderEditor, getEditorInput()));
			setPageText(featureOrderEditor.getIndex(), featureOrderEditor.getPageText());
			featureOrderEditor.initEditor();
		} catch (final PartInitException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	private void createModelFileMarkers(ProblemList warnings) {
		markerHandler.deleteAllModelMarkers();
		for (final Problem warning : warnings) {
			markerHandler.createModelMarker(warning.message, warning.severity.getLevel(), warning.line);
		}
		if (!warnings.containsError()) {
			try {
				if (!getFeatureModel().getAnalyser().isValid()) {
					markerHandler.createModelMarker(THE_FEATURE_MODEL_IS_VOID_COMMA__I_E__COMMA__IT_CONTAINS_NO_PRODUCTS, IMarker.SEVERITY_ERROR, 0);
				}
			} catch (final TimeoutException e) {
				// do nothing, assume the model is correct
			}
		}
	}

	private int getDiagramEditorIndex() {
		return diagramEditor.getIndex();
	}

	private void getExtensions() {
		final IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(FMUIPlugin.PLUGIN_ID + ".FeatureModelEditor");
		try {
			for (final IConfigurationElement e : config) {
				final Object o = e.createExecutableExtension("class");
				if (o instanceof IFeatureModelEditorPage) {
					extensionPages.add(((IFeatureModelEditorPage) o));
				}
			}
		} catch (final Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	private int getOrderEditorIndex() {
		return featureOrderEditor.getIndex();
	}

	/**
	 * Gets the corresponding page for the given index.
	 *
	 * @param index The index of the page
	 * @return The page
	 */
	private IFeatureModelEditorPage getPage(int index) {
		if (index == getDiagramEditorIndex()) {
			return diagramEditor;
		}
		if (index == getOrderEditorIndex()) {
			return featureOrderEditor;
		}
		if (index == getTextEditorIndex()) {
			return textEditor;
		}

		for (final IFeatureModelEditorPage page : extensionPages) {
			if (page.getIndex() == index) {
				return page;
			}
		}

		return null;
	}

	private int getTextEditorIndex() {
		return textEditor.getIndex();
	}

	public void readModel(String newSource) {
		final ProblemList warnings = fmManager.getFormat().getInstance().read(getFeatureModel(), newSource);
		createModelFileMarkers(warnings);
		// final AModelFormatHandler modelHandler2 = PersistentFeatureModelManager.getModelHandler(ioType);
		// modelHandler2.setObject(fmManager.editFeatureModel());
		// final List<Problem> warnings = modelHandler2.read(newSource);
		// featureModel = fmManager.editFeatureModel();
	}

	private boolean saveEditors() {
		if (getFeatureModel().getRenamingsManager().isRenamed()) {
			final IProject project = getModelFile().getProject();
			final ArrayList<String> dirtyEditors = new ArrayList<String>();
			final ArrayList<IEditorPart> dirtyEditors2 = new ArrayList<IEditorPart>();
			for (final IWorkbenchWindow window : getSite().getWorkbenchWindow().getWorkbench().getWorkbenchWindows()) {
				for (final IWorkbenchPage page : window.getPages()) {
					for (final IEditorReference editorRef : page.getEditorReferences()) {
						if (ConfigurationEditor.ID.equals(editorRef.getId())) {
							final IEditorPart editor = editorRef.getEditor(true);
							if (editor.isDirty()) {
								final IEditorInput editorInput = editor.getEditorInput();
								// Cast is necessary, don't remove
								final IFile editorFile = (IFile) editorInput.getAdapter(IFile.class);
								if (editorFile.getProject().equals(project)) {
									dirtyEditors.add(editorFile.getName());
									dirtyEditors2.add(editor);
								}
							}
						}
					}
				}
			}

			if (dirtyEditors.size() != 0) {
				final ListDialog dialog = new ListDialog(getSite().getWorkbenchWindow().getShell());
				dialog.setAddCancelButton(true);
				dialog.setContentProvider(new ArrayContentProvider());
				dialog.setLabelProvider(new LabelProvider());
				dialog.setInput(dirtyEditors);
				dialog.setInitialElementSelections(dirtyEditors);
				dialog.setTitle(SAVE_RESOURCES);
				dialog.setHelpAvailable(false);
				dialog.setMessage(SOME_MODIFIED_RESOURCES_MUST_BE_SAVED_BEFORE_SAVING_THE_FEATUREMODEL_);
				dialog.open();

				if (dialog.getResult() != null) {
					for (final IEditorPart editor : dirtyEditors2) {
						editor.doSave(null);
					}
				} else {
					// case: cancel pressed
					return false;
				}
			}
		}
		return true;
	}

	private void setOutlinePage(FmOutlinePage fmOutlinePage) {
		outlinePage = fmOutlinePage;
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		if (getActivePage() == getDiagramEditorIndex()) {
			diagramEditor.propertyChange(event);
		}
	}

}
