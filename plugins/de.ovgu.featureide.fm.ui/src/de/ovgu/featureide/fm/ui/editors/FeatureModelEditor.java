/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import java.beans.PropertyChangeEvent;
import java.io.File;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.operations.IOperationHistory;
import org.eclipse.core.commands.operations.IOperationHistoryListener;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.core.commands.operations.ObjectUndoContext;
import org.eclipse.core.commands.operations.OperationHistoryEvent;
import org.eclipse.core.resources.IFile;
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
import org.eclipse.gef.ui.actions.PrintAction;
import org.eclipse.gef.ui.actions.SelectAllAction;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkbenchPage;
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

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelFile;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.io.FeatureModelReaderIFileWrapper;
import de.ovgu.featureide.fm.core.io.FeatureModelWriterIFileWrapper;
import de.ovgu.featureide.fm.core.io.IFeatureModelReader;
import de.ovgu.featureide.fm.core.io.IFeatureModelWriter;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslWriter;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.FeatureModelEditorContributor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GEFImageWriter;
import de.ovgu.featureide.fm.ui.views.outline.FmOutlinePage;

/**
 * A multi page editor to edit feature models. If the model file contains
 * errors, markers will be created on save.
 * 
 * @author Thomas Thuem
 * @author Christian Becker
 */
public class FeatureModelEditor extends MultiPageEditorPart implements
		IResourceChangeListener {

	public static final String ID = FMUIPlugin.PLUGIN_ID
			+ ".editors.FeatureModelEditor";

	public FeatureDiagramEditor diagramEditor;
	public FeatureModelTextEditorPage textEditor;
	public FeatureOrderEditor featureOrderEditor;

	boolean isPageModified;

	private boolean closeEditor;

	public FeatureModel featureModel;
	public FeatureModel originalFeatureModel;

	IFeatureModelReader featureModelReader;
	IFeatureModelWriter featureModelWriter;

	FeatureModelFile fmFile;
	private IFile file;
	private int operationCounter;
	private PrintAction printAction;
	private SelectAllAction selectAllAction;
	private UndoActionHandler undoAction;
	private RedoActionHandler redoAction;

	private FmOutlinePage outlinePage;

	public LinkedList<IFeatureModelEditorPage> extensionPages = new LinkedList<IFeatureModelEditorPage>();

	private int getTextEditorIndex() {
		return textEditor.getIndex();
	}

	private int getDiagramEditorIndex() {
		return diagramEditor.getIndex();
	}

	private int getOrderEditorIndex() {
		return featureOrderEditor.getIndex();
	}

	@Override
	protected void setInput(IEditorInput input) {
		file = (IFile) input.getAdapter(IFile.class);
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
		fmFile = new FeatureModelFile(file);
		setPartName(file.getProject().getName() + " Model");
		setTitleToolTip(input.getToolTipText());
		super.setInput(input);

		featureModel = new FeatureModel();

		featureModelReader = new XmlFeatureModelReader(featureModel);
		featureModelWriter = new XmlFeatureModelWriter(featureModel);

		originalFeatureModel = new FeatureModel();
		try {
	    	new FeatureModelReaderIFileWrapper(new XmlFeatureModelReader(originalFeatureModel)).readFromFile(file);
	    	new FeatureModelReaderIFileWrapper(new XmlFeatureModelReader(featureModel)).readFromFile(file);
		} catch (Exception e) {
			FMUIPlugin.getDefault().logError(e);
		}
		FeatureUIHelper.showHiddenFeatures(originalFeatureModel
				.getLayout().showHiddenFeatures(),featureModel);
		FeatureUIHelper.setVerticalLayoutBounds(originalFeatureModel
				.getLayout().verticalLayout(),featureModel);
		
		getExtensions();
	}

	/**
	 * 
	 */
	private void getExtensions() {
		IConfigurationElement[] config = Platform.getExtensionRegistry()
				.getConfigurationElementsFor(
						FMUIPlugin.PLUGIN_ID + ".FeatureModelEditor");
		try {
			for (IConfigurationElement e : config) {
				final Object o = e.createExecutableExtension("class");
				if (o instanceof IFeatureModelEditorPage) {
					extensionPages.add(((IFeatureModelEditorPage) o));
				}
			}
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	public FeatureModel getOriginalFeatureModel() {
		return originalFeatureModel;
	}

	@Override
	protected void createPages() {
		createActions();
		createDiagramPage();
		createFeatureOrderPage();
		createExtensionPages();
		createSourcePage();
	}

	void createDiagramPage() {
		diagramEditor = new FeatureDiagramEditor(this, getContainer());
		featureModel.addListener(diagramEditor);
		diagramEditor.getControl().getDisplay().asyncExec(new Runnable() {
			public void run() {
				diagramEditor.setContents(featureModel);
				pageChange(getDiagramEditorIndex());
			}
		});
		diagramEditor.setIndex(addPage(diagramEditor.getControl()));
		setPageText(getDiagramEditorIndex(), diagramEditor.getPageText());
		diagramEditor.initEditor();
	}

	private void createFeatureOrderPage() {
		featureOrderEditor = new FeatureOrderEditor(this);
		try {
			featureOrderEditor.setIndex(addPage(featureOrderEditor,
					getEditorInput()));
			setPageText(featureOrderEditor.getIndex(),
					featureOrderEditor.getPageText());
			featureOrderEditor.initEditor();
		} catch (PartInitException e) {
			FMUIPlugin.getDefault().logError(e);
		}
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
			} catch (PartInitException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}

	void createSourcePage() {
		closeEditor = false;
		textEditor = new FeatureModelTextEditorPage();
		textEditor.setFeatureModelEditor(this);
		try {
			textEditor.setIndex(addPage(textEditor, getEditorInput()));
			setPageText(textEditor.getIndex(), textEditor.getPageText());
		} catch (PartInitException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	private void createActions() {
		IOperationHistory history = PlatformUI.getWorkbench()
				.getOperationSupport().getOperationHistory();
		history.addOperationHistoryListener(new IOperationHistoryListener() {

			@Override
			public void historyNotification(OperationHistoryEvent event) {
				if (!hasFMUndoContext(event))
					return;
				if (event.getEventType() == OperationHistoryEvent.DONE
						|| event.getEventType() == OperationHistoryEvent.REDONE) {
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
				for (IUndoContext c : event.getOperation().getContexts()) {
					if (c.matches((IUndoContext) featureModel.getUndoContext())) {
						return true;
					}
				}
				return false;
			}

		});
		ObjectUndoContext undoContext = new ObjectUndoContext(this);
		featureModel.setUndoContext(undoContext);

		printAction = new PrintAction(this);
		selectAllAction = new SelectAllAction(this);

		undoAction = new UndoActionHandler(this.getSite(), undoContext);
		redoAction = new RedoActionHandler(this.getSite(), undoContext);
	}

	public IAction getDiagramAction(String workbenchActionID) {
		if (ActionFactory.PRINT.getId().equals(workbenchActionID))
			return printAction;
		if (ActionFactory.SELECT_ALL.getId().equals(workbenchActionID))
			return selectAllAction;
		if (ActionFactory.UNDO.getId().equals(workbenchActionID))
			return undoAction;
		if (ActionFactory.REDO.getId().equals(workbenchActionID))
			return redoAction;
		IAction action = diagramEditor.getDiagramAction(workbenchActionID);
		if (action != null)
			return action;
		FMCorePlugin
				.getDefault()
				.logInfo(
						"The following workbench action is not registered at the feature diagram editor: "
								+ workbenchActionID);
		return null;
	}

	public void diagramModified() {
		if (isPageModified)
			return;
		boolean wasDirty = isDirty();
		isPageModified = true;
		if (!wasDirty)
			firePropertyChange(IEditorPart.PROP_DIRTY);
	}

	@Override
	protected void handlePropertyChange(int propertyId) {
		if (propertyId == IEditorPart.PROP_DIRTY)
			isPageModified = isDirty();
		super.handlePropertyChange(propertyId);
	}

	@Override
	public boolean isDirty() {
		return isPageModified || super.isDirty();
	}

	@Override
	public void setFocus() {
		if (getActivePage() == getDiagramEditorIndex())
			diagramEditor.getControl().setFocus();
		else
			textEditor.setFocus();
	}

	private int oldPageIndex;

	@Override
	protected void pageChange(int newPageIndex) {
		IEditorActionBarContributor contributor = getEditorSite().getActionBarContributor();
		if (contributor instanceof FeatureModelEditorContributor) {
			((FeatureModelEditorContributor) contributor).setActivePage(this, newPageIndex);
		}
		getPage(oldPageIndex).pageChangeFrom(newPageIndex);
		getPage(newPageIndex).pageChangeTo(oldPageIndex);

		oldPageIndex = newPageIndex;
		
		super.pageChange(newPageIndex);
	}

	/**
	 * Gets the corresponding page for the given index.
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
		
		for (IFeatureModelEditorPage page : extensionPages) {
			if (page.getIndex() == index) {
				return page; 
			}
		}

		return null;
	}

	/**
	 * Open a dialog to save the model.
	 */
	public void saveModelForConsistentRenamings() {
		LinkedList<String> editor = new LinkedList<String>();
		editor.add(fmFile.getResource().getName());

		ListDialog dialog = new ListDialog(getSite().getWorkbenchWindow()
				.getShell());
		dialog.setAddCancelButton(true);
		dialog.setContentProvider(new ArrayContentProvider());
		dialog.setLabelProvider(new LabelProvider());
		dialog.setInput(editor);
		dialog.setInitialElementSelections(editor);
		dialog.setTitle("Save feature model");
		dialog.setHelpAvailable(false);
		dialog.setMessage("Model should be saved after renamings.");
		dialog.open();

		if (dialog.getResult() != null) {
			doSave(null);
		}
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		if (!saveEditors())
			return;

		featureOrderEditor.doSave(monitor);
		featureModel.performRenamings(file);
		for (IFeatureModelEditorPage page : extensionPages) {
			page.doSave(monitor);
		}
		
		// write the model to the file
		if (getActivePage() == textEditor.getIndex()) {
			textEditor.doSave(monitor);
		} else {
			try {
				new FeatureModelWriterIFileWrapper(new XmlFeatureModelWriter(featureModel)).writeToFile(getModelFile());
			} catch (CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}

		// set originalFeatureModel
		try {
			new FeatureModelReaderIFileWrapper(new XmlFeatureModelReader(originalFeatureModel))
				.readFromFile(fmFile.getResource());
		} catch (Exception e) {
			FMUIPlugin.getDefault().logError(e);
		}
		
		setPageModified(false);
		updateConfigurationEditors();
	}

	/**
	 * Sets the actual FeatureModel at the corresponding {@link ConfigurationEditor}s.
	 * @see ConfigurationEditor#propertyChange(PropertyChangeEvent)
	 */
	@SuppressWarnings("deprecation")
	private void updateConfigurationEditors() {
		IProject project = file.getProject();
		for (IWorkbenchWindow window : getSite().getWorkbenchWindow()
				.getWorkbench().getWorkbenchWindows()) {
			for (IWorkbenchPage page : window.getPages()) {
				for (IEditorPart editor : page.getEditors()) {
					if (editor instanceof ConfigurationEditor) {
						IEditorInput editorInput = editor.getEditorInput();
						IFile editorFile = (IFile) editorInput
								.getAdapter(IFile.class);
						if (editorFile.getProject().equals(project)) {
							((ConfigurationEditor) editor).propertyChange(
									new PropertyChangeEvent(file,PropertyConstants.MODEL_DATA_CHANGED,null,null));
						}
					}
				}
			}
		}
	}

	@SuppressWarnings("deprecation")
	private boolean saveEditors() {
		if (featureModel.isRenamed()) {
			IProject project = file.getProject();
			ArrayList<String> dirtyEditors = new ArrayList<String>();
			ArrayList<IEditorPart> dirtyEditors2 = new ArrayList<IEditorPart>();
			for (IWorkbenchWindow window : getSite().getWorkbenchWindow()
					.getWorkbench().getWorkbenchWindows()) {
				for (IWorkbenchPage page : window.getPages()) {
					for (IEditorPart editor : page.getEditors()) {
						if (editor instanceof ConfigurationEditor && editor.isDirty()) {
							IEditorInput editorInput = editor.getEditorInput();
							IFile editorFile = (IFile) editorInput.getAdapter(IFile.class);
							if (editorFile.getProject().equals(project)) {
								dirtyEditors.add(editorFile.getName());
								dirtyEditors2.add(editor);
							}
						}
					}
				}
			}
			if (dirtyEditors.size() != 0) {
				ListDialog dialog = new ListDialog(getSite()
						.getWorkbenchWindow().getShell());
				dialog.setAddCancelButton(true);
				dialog.setContentProvider(new ArrayContentProvider());
				dialog.setLabelProvider(new LabelProvider());
				dialog.setInput(dirtyEditors);
				dialog.setInitialElementSelections(dirtyEditors);
				dialog.setTitle("Save Resources");
				dialog.setHelpAvailable(false);
				dialog.setMessage("Some modified resources must be saved before saving the featuremodel.");
				dialog.open();

				if (dialog.getResult() != null) {
					for (IEditorPart editor : dirtyEditors2) {
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

	@Override
	public boolean isSaveAsAllowed() {
		return true;
	}

	@Override
	public void doSaveAs() {
		FileDialog fileDialog = new FileDialog(getEditorSite().getShell(),
				SWT.SAVE);
		String[] extensions = { "*.png", "*.jpg", "*.bmp", "*.m", "*.xml" };
		fileDialog.setFilterExtensions(extensions);
		String[] filterNames = { "Portable Network Graphics *.png",
				"JPEG *.jpg", "Windows Bitmap *.bmp", "GUIDSL Grammar *.m",
				"XML Export *.xml" };
		fileDialog.setFilterNames(filterNames);
		fileDialog.setOverwrite(true);
		String filePath = fileDialog.open();
		if (filePath == null)
			return;
		File file = new File(filePath);
		if (filePath.endsWith(".m")) {
			new GuidslWriter(featureModel).writeToFile(file);
		} else if (filePath.endsWith(".xml")) {
			featureModelWriter.writeToFile(file);
		} else {
			GEFImageWriter.writeToFile(diagramEditor, file);
		}
	}

	@SuppressWarnings("rawtypes")
	@Override
	public Object getAdapter(Class adapter) {
		if (IContentOutlinePage.class.equals(adapter)) {
			if (getOutlinePage() == null) {
				setOutlinePage(new FmOutlinePage(null, this));
				getOutlinePage().setInput(getFeatureModel());
			}
			return getOutlinePage();
		}
		if (IGotoMarker.class.equals(adapter))
			if (getActivePage() != getDiagramEditorIndex())
				setActivePage(getDiagramEditorIndex());
		Object o = diagramEditor.getAdapter(adapter);
		if (o != null)
			return o;
		return super.getAdapter(adapter);
	}

	public ITextEditor getSourceEditor() {
		return textEditor;
	}

	public FeatureModel getFeatureModel() {
		return featureModel;
	}

	public FeatureModelFile getGrammarFile() {
		return fmFile;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.resources.IResourceChangeListener#resourceChanged(org
	 * .eclipse.core.resources.IResourceChangeEvent)
	 */
	public void resourceChanged(IResourceChangeEvent event) {
		if (event.getResource() == null)
			return;
		if (event.getResource().getType() == IResource.PROJECT)
			closeEditor = true;
		final IEditorInput input = getEditorInput();
		if (!(input instanceof IFileEditorInput))
			return;
		final IFile jmolfile = ((IFileEditorInput) input).getFile();

		/*
		 * Closes editor if resource is deleted
		 */
		if ((event.getType() == IResourceChangeEvent.POST_CHANGE)
				&& closeEditor) {
			IResourceDelta rootDelta = event.getDelta();
			// get the delta, if any, for the documentation directory
			final List<IResource> deletedlist = new ArrayList<IResource>();
			IResourceDelta docDelta = rootDelta.findMember(jmolfile
					.getFullPath());
			if (docDelta != null) {
				IResourceDeltaVisitor visitor = new IResourceDeltaVisitor() {
					public boolean visit(IResourceDelta delta) {
						// only interested in removal changes
						if (((delta.getFlags() & IResourceDelta.REMOVED) == 0)
								&& closeEditor) {
							deletedlist.add(delta.getResource());
						}
						return true;
					}
				};
				try {
					docDelta.accept(visitor);
				} catch (CoreException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}
			if (deletedlist.size() > 0 && deletedlist.contains(jmolfile)) {
				Display.getDefault().asyncExec(new Runnable() {
					public void run() {
						if (getSite() == null)
							return;
						if (getSite().getWorkbenchWindow() == null)
							return;
						IWorkbenchPage[] pages = getSite().getWorkbenchWindow()
								.getPages();
						for (int i = 0; i < pages.length; i++) {
							IEditorPart editorPart = pages[i].findEditor(input);
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
				public void run() {
					if (getSite() == null)
						return;
					if (getSite().getWorkbenchWindow() == null)
						return;
					IWorkbenchPage[] pages = getSite().getWorkbenchWindow()
							.getPages();
					for (int i = 0; i < pages.length; i++) {
						if (jmolfile.getProject().equals(res)) {
							IEditorPart editorPart = pages[i].findEditor(input);
							pages[i].closeEditor(editorPart, true);
						}
					}
				}
			});
		}
	}

	public void setPageModified(boolean modified) {
		if (!modified)
			operationCounter = 0;
		isPageModified = modified;
		firePropertyChange(PROP_DIRTY);
	}

	public FmOutlinePage getOutlinePage() {
		return outlinePage;
	}

	private void setOutlinePage(FmOutlinePage fmOutlinePage) {
		outlinePage = fmOutlinePage;
	}
	
	public IFile getModelFile() {
		return file;
	}
	
	/**
	 * This is just a call to the private method <code>setActivePage(int index)</code>.
	 * @param index
	 */
	public void setActiveEditorPage(int index) {
		setActivePage(index);
	}

}
