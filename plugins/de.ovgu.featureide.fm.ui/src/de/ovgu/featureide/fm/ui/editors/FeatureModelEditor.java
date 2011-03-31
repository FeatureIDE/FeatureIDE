/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
import java.beans.PropertyChangeListener;
import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.commands.operations.ObjectUndoContext;
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
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.gef.ui.actions.PrintAction;
import org.eclipse.gef.ui.actions.SelectAllAction;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.text.IDocument;
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
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.dialogs.ListDialog;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.ide.IGotoMarker;
import org.eclipse.ui.operations.RedoActionHandler;
import org.eclipse.ui.operations.UndoActionHandler;
import org.eclipse.ui.part.MultiPageEditorPart;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.GrammarFile;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.io.IFeatureModelReader;
import de.ovgu.featureide.fm.core.io.IFeatureModelWriter;
import de.ovgu.featureide.fm.core.io.ModelWarning;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslWriter;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.FeatureModelEditorContributor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GEFImageWriter;

/**
 * A multi page editor to edit feature models. If the model file contains
 * errors, markers will be created on save.
 * 
 * @author Thomas Thuem
 * @author Christian Becker
 */
public class FeatureModelEditor extends MultiPageEditorPart implements
		PropertyConstants, PropertyChangeListener,
		IResourceChangeListener {

	public static final String ID = FMUIPlugin.PLUGIN_ID
			+ ".editors.FeatureModelEditor";

	// TODO new extension point
	private FeatureDiagramEditor diagramEditor;

	// TODO new extension point
	private TextEditor textEditor;

	// TODO new extension point
	private int graphicalViewerIndex;

	// TODO new extension point
	private int textEditorIndex;

	// TODO new extension point
	private int featureOrderEditorIndex;

	private boolean isPageModified;

	private boolean closeEditor;

	private FeatureModel featureModel;

	private IFeatureModelReader featureModelReader;

	private IFeatureModelWriter featureModelWriter;

	private GrammarFile grammarFile;

	private FeatureModel originalFeatureModel;

	// TODO new extension point
	private FeatureOrderEditor featureOrderEditor;

	private IFile file;

	private PrintAction printAction;

	private SelectAllAction selectAllAction;

	private UndoActionHandler undoAction;

	private RedoActionHandler redoAction;

	@Override
	protected void setInput(IEditorInput input) {
		file = (IFile) input.getAdapter(IFile.class);
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
		grammarFile = new GrammarFile(file);
		setPartName(file.getProject().getName() + " Model");
		setTitleToolTip(input.getToolTipText());
		super.setInput(input);

		featureModel = new FeatureModel();
		featureModel.addListener(this);
		featureModelReader = new XmlFeatureModelReader(featureModel);
		featureModelWriter = new XmlFeatureModelWriter(featureModel);

		originalFeatureModel = new FeatureModel();

		try {

			new XmlFeatureModelReader(originalFeatureModel).readFromFile(file);

		} catch (Exception e) {
		}
	}

	public FeatureModel getOriginalFeatureModel() {
		return originalFeatureModel;
	}

	@Override
	protected void createPages() {
		// TODO new extension point
		createDiagramPage();
		createFeatureOrderPage();
		createSourcePage();
		createActions();
		createContextMenu();
		createKeyBindings();
	}

	// TODO new extension point
	private void createFeatureOrderPage() {
		featureOrderEditor = new FeatureOrderEditor(originalFeatureModel);
		try {
			featureOrderEditorIndex = addPage(featureOrderEditor,
					getEditorInput());
			setPageText(featureOrderEditorIndex, "Feature Order");
			// featureOrderEditor.updateOrderEditor(getOriginalFeatureModel().getFeatures());
			featureOrderEditor.initOrderEditor();
		} catch (PartInitException e) {

			FMUIPlugin.getDefault().logError(e);
		}
		;
	}

	// TODO new extension point
	void createDiagramPage() {
		diagramEditor = new FeatureDiagramEditor(this, getContainer());
		diagramEditor.getPage().getDisplay().asyncExec(new Runnable() {
			public void run() {
				diagramEditor.getGraphicalViewer().setContents(getFeatureModel());
				isPageModified = true;
				pageChange(graphicalViewerIndex);
			}
		});
		graphicalViewerIndex = addPage(diagramEditor.getPage());
		setPageText(graphicalViewerIndex, "Feature Diagram");
	}

	// TODO new extension point
	void createSourcePage() {
		closeEditor = false;
		textEditor = new TextEditor();
		try {
			textEditorIndex = addPage(textEditor, getEditorInput());
			setPageText(textEditorIndex, "Source");
		} catch (PartInitException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	private void createActions() {
		// TODO new extension point
		ObjectUndoContext undoContext = new ObjectUndoContext(this);
		featureModel.setUndoContext(undoContext);
		diagramEditor.createActions();
		
		printAction = new PrintAction(this);
		selectAllAction = new SelectAllAction(this);

		undoAction = new UndoActionHandler(this.getSite(), undoContext);
		redoAction = new RedoActionHandler(this.getSite(), undoContext);
	}

	private void createContextMenu() {
		MenuManager menu = new MenuManager("#PopupMenu");
		menu.setRemoveAllWhenShown(true);
		diagramEditor.createContextMenu(menu);
	}

	private void createKeyBindings() {
		diagramEditor.createKeyBindings();
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

	// TODO new extension point
	public boolean updateDiagramFromTextEditor() {
		IDocumentProvider provider = textEditor.getDocumentProvider();
		IDocument document = provider.getDocument(textEditor.getEditorInput());
		String text = document.get();
		grammarFile.deleteAllModelMarkers();
		try {
			featureModelReader.readFromString(text);
			for (ModelWarning warning : featureModelReader.getWarnings())
				grammarFile.createModelMarker(warning.message,
						IMarker.SEVERITY_WARNING, warning.line);
			try {
				if (!featureModel.isValid())
					grammarFile
							.createModelMarker(
									"The feature model is void, i.e., it contains no products",
									IMarker.SEVERITY_ERROR, 0);
			} catch (TimeoutException e) {
				// do nothing, assume the model is correct
			}
		} catch (UnsupportedModelException e) {
			grammarFile.createModelMarker(e.getMessage(),
					IMarker.SEVERITY_ERROR, e.lineNumber);
			return false;
		}
		return true;
	}

	// TODO new extension point
	void updateTextEditorFromDiagram() {
		String text = featureModelWriter.writeToString();
		IDocumentProvider provider = textEditor.getDocumentProvider();
		IDocument document = provider.getDocument(textEditor.getEditorInput());
		document.set(text);
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
		// TODO new extension point
		if (getActivePage() == graphicalViewerIndex)
			diagramEditor.getPage().setFocus();
		else
			textEditor.setFocus();
	}

	private int oldPage;

	// TODO new extension point
	@Override
	protected void pageChange(int newPageIndex) {
		if (oldPage == graphicalViewerIndex) {
			if (newPageIndex == textEditorIndex) {
				if (isPageModified) {
					updateTextEditorFromDiagram();
					if (featureModel.isRenamed()) {
						saveModelForConsistentRenamings();
					}
				}
			} else if (newPageIndex == featureOrderEditorIndex) {

				if (isPageModified) {
					updateTextEditorFromDiagram();
					featureOrderEditor.updateOrderEditor(featureModel);
				}
			} else if (oldPage == newPageIndex) {
				updateDiagramFromTextEditor();
			}
		} else if (oldPage == textEditorIndex) {
			if (newPageIndex == graphicalViewerIndex) {
				// delete this line, so the import in the source view is correct
				// if (isDirty() || grammarFile.hasModelMarkers())
				if (!updateDiagramFromTextEditor()) {
					// there are errors in the file, stay at this editor page
					isPageModified = false;
					setActivePage(textEditorIndex);
					return;
				}
			} else if (newPageIndex == featureOrderEditorIndex) {
				if (isDirty() || grammarFile.hasModelMarkers()) {

					if (!updateDiagramFromTextEditor()) {
						// there are errors in the file, stay at this editor
						// page
						isPageModified = false;
						setActivePage(textEditorIndex);
						return;
					} else
						featureOrderEditor.updateOrderEditor(featureModel);
				}
			}
		} else {
			if (newPageIndex == textEditorIndex) {
				if (isPageModified && featureModel.isRenamed()) {
					saveModelForConsistentRenamings();
				}
			}
		}
		isPageModified = false;

		IEditorActionBarContributor contributor = getEditorSite()
				.getActionBarContributor();
		if (contributor instanceof FeatureModelEditorContributor)
			((FeatureModelEditorContributor) contributor).setActivePage(this,
					newPageIndex);
		oldPage = newPageIndex;
		super.pageChange(newPageIndex);

	}

	/**
	 * Open a dialog to save the model.
	 */
	private void saveModelForConsistentRenamings() {
		ArrayList<String> editor = new ArrayList<String>();
		editor.add(grammarFile.getResource().getName());

		ArrayList<IEditorPart> editorspart = new ArrayList<IEditorPart>();
		editorspart.add(this.getEditor(graphicalViewerIndex));

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

	// TODO new extension point
	@Override
	public void doSave(IProgressMonitor monitor) {
		if (!saveEditors())
			return;

		featureOrderEditor.updateOrderEditor(featureModel);
		featureOrderEditor.doSave(monitor);
		featureModel.performRenamings(file);

		if (getActivePage() == graphicalViewerIndex && isPageModified) {
			updateTextEditorFromDiagram();
			setActivePage(textEditorIndex);
			setActivePage(graphicalViewerIndex);

		} else if (getActivePage() == textEditorIndex) {
			updateDiagramFromTextEditor();

		} else if (getActivePage() == featureOrderEditorIndex) {
			// isPageModified = false;
			updateTextEditorFromDiagram();
		}

		isPageModified = false;

		textEditor.doSave(monitor);
		try {
			new XmlFeatureModelReader(originalFeatureModel)
					.readFromFile(grammarFile.getResource());
		} catch (Exception e) {
			FMUIPlugin.getDefault().logError(e);
		}
		firePropertyChange(PROP_DIRTY);
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
						if (editor.isDirty()) {
							IEditorInput editorInput = editor.getEditorInput();
							IFile editorFile = (IFile) editorInput
									.getAdapter(IFile.class);
							if (editorFile.getProject().equals(project)
									&& !editorFile.getName().endsWith(".xml")) {
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
			GEFImageWriter.writeToFile(diagramEditor.getGraphicalViewer(), file);
		}
	}

	public void propertyChange(PropertyChangeEvent event) {

		String prop = event.getPropertyName();
		if (prop.equals(MODEL_DATA_CHANGED)) {
			diagramEditor.getGraphicalViewer().setContents(featureModel);
			diagramEditor.refresh();
			isPageModified = true;
			firePropertyChange(PROP_DIRTY);
		} else if (prop.equals(MODEL_DATA_LOADED)) {
			diagramEditor.refresh();
		} else if (prop.equals(REDRAW_DIAGRAM)) {
			// TODO new extension point
			updateTextEditorFromDiagram();
			updateDiagramFromTextEditor();
		} else if (prop.equals(REFRESH_ACTIONS)) {
			// additional actions can be refreshed here
			diagramEditor.refreshLegend();
		}
	}

	@SuppressWarnings("rawtypes")
	@Override
	public Object getAdapter(Class adapter) {
		if (IGotoMarker.class.equals(adapter))
			if (getActivePage() != textEditorIndex)
				setActivePage(textEditorIndex);
		Object o = diagramEditor.getAdapter(adapter);
		if (o != null)
			return o;
		return super.getAdapter(adapter);
	}

	// TODO remove?
	@Override
	public int getActivePage() {
		return super.getActivePage();
	}

	// TODO new extension point
	public ITextEditor getSourceEditor() {
		return textEditor;
	}

	public FeatureModel getFeatureModel() {
		return featureModel;
	}

	public GrammarFile getGrammarFile() {
		return grammarFile;
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

}
