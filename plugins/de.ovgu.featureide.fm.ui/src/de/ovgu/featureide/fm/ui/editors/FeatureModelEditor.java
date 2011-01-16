/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
import org.eclipse.draw2d.ConnectionLayer;
import org.eclipse.gef.DefaultEditDomain;
import org.eclipse.gef.EditDomain;
import org.eclipse.gef.EditPartViewer;
import org.eclipse.gef.GraphicalViewer;
import org.eclipse.gef.KeyHandler;
import org.eclipse.gef.KeyStroke;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.commands.CommandStack;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.editparts.ZoomManager;
import org.eclipse.gef.ui.actions.GEFActionConstants;
import org.eclipse.gef.ui.actions.PrintAction;
import org.eclipse.gef.ui.actions.RedoAction;
import org.eclipse.gef.ui.actions.SelectAllAction;
import org.eclipse.gef.ui.actions.UndoAction;
import org.eclipse.gef.ui.actions.ZoomInAction;
import org.eclipse.gef.ui.actions.ZoomOutAction;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.gef.ui.parts.GraphicalViewerKeyHandler;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.dialogs.ListDialog;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.ide.IGotoMarker;
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
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AbstractAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AlternativeAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AndAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateCompoundAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateLayerAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.DeleteAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.EditConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.HiddenAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.MandantoryAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.OrAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.RenameAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ReverseOrderAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.GraphicalEditPartFactory;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.LevelOrderLayout;

/**
 * A multi page editor to edit feature models. If the model file contains
 * errors, markers will be created on save.
 * 
 * @author Thomas Thuem
 * @author Christian Becker
 */
public class FeatureModelEditor extends MultiPageEditorPart implements
		GUIDefaults, PropertyConstants, PropertyChangeListener,
		IResourceChangeListener {

	public static final String ID = FMUIPlugin.PLUGIN_ID
			+ ".editors.GrammarEditor";

	private GraphicalViewerImpl graphicalViewer;

	private TextEditor textEditor;

	private int graphicalViewerIndex;

	private int textEditorIndex;

	private int featureOrderEditorIndex;

	private boolean isPageModified;

	private boolean closeEditor;

	private FeatureModel featureModel;

	private IFeatureModelReader featureModelReader;

	private IFeatureModelWriter featureModelWriter;

	private CreateLayerAction createLayerAction;

	private CreateCompoundAction createCompoundAction;

	private DeleteAction deleteAction;

	private MandantoryAction mandantoryAction;

	private AbstractAction abstractAction;

	private HiddenAction hiddenAction;

	private AndAction andAction;

	private OrAction orAction;

	private AlternativeAction alternativeAction;

	private PrintAction printAction;

	private SelectAllAction selectAllAction;

	private UndoAction undoAction;

	private RedoAction redoAction;

	private RenameAction renameAction;

	private ZoomInAction zoomIn;

	private ZoomOutAction zoomOut;

	private FeatureDiagramLayoutManager layoutManager = new LevelOrderLayout();

	private GrammarFile grammarFile;

	private FeatureModel originalFeatureModel;

	private ZoomManager zoomManager;

	private ScalableFreeformRootEditPart rootEditPart;

	private FeatureOrderEditor featureOrderEditor;

	private EditConstraintAction editConstraintAction;

	private CreateConstraintAction createConstraintAction;

	private ReverseOrderAction reverseOrderAction;

	private IFile file;

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

		createDiagramPage();
		createSourcePage();
		createFeatureOrderPage();
		createActions();
		createContextMenu();
		createKeyBindings();
	}

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

	void createDiagramPage() {
		graphicalViewer = new ScrollingGraphicalViewer();
		graphicalViewer.setKeyHandler(new GraphicalViewerKeyHandler(
				graphicalViewer));

		graphicalViewer.createControl(getContainer());
		initializeGraphicalViewer();

		graphicalViewer.setEditDomain(new DefaultEditDomain(this));

		initDiagramContent();

		graphicalViewerIndex = addPage(graphicalViewer.getControl());
		setPageText(graphicalViewerIndex, "Feature Diagram");
		zoomManager = rootEditPart.getZoomManager();
		zoomManager.setZoomLevels(new double[] { 0.05, 0.10, 0.25, 0.50, 0.75,
				0.90, 1.00, 1.10, 1.25, 1.50, 2.00, 2.50, 3.00, 4.00 });
	}

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
		createLayerAction = new CreateLayerAction(graphicalViewer, featureModel);
		createCompoundAction = new CreateCompoundAction(graphicalViewer,
				featureModel);
		deleteAction = new DeleteAction(graphicalViewer, featureModel);
		mandantoryAction = new MandantoryAction(graphicalViewer, featureModel);
		hiddenAction = new HiddenAction(graphicalViewer, featureModel);
		abstractAction = new AbstractAction(graphicalViewer, featureModel);
		andAction = new AndAction(graphicalViewer, featureModel);
		orAction = new OrAction(graphicalViewer, featureModel);
		alternativeAction = new AlternativeAction(graphicalViewer, featureModel);
		printAction = new PrintAction(this);
		selectAllAction = new SelectAllAction(this);
		undoAction = new UndoAction(this);
		redoAction = new RedoAction(this);
		renameAction = new RenameAction(graphicalViewer, featureModel);
		zoomIn = new ZoomInAction(zoomManager);
		zoomOut = new ZoomOutAction(zoomManager);
		createConstraintAction = new CreateConstraintAction(graphicalViewer,
				featureModel, "Create Constraint");
		editConstraintAction = new EditConstraintAction(graphicalViewer,
				featureModel, "Edit Constraint");
		reverseOrderAction = new ReverseOrderAction(graphicalViewer, featureModel);
	}

	private void createContextMenu() {
		MenuManager menu = new MenuManager("#PopupMenu");
		menu.setRemoveAllWhenShown(true);
		menu.addMenuListener(new IMenuListener() {
			public void menuAboutToShow(IMenuManager manager) {
				FeatureModelEditor.this.fillContextMenu(manager);
			}
		});
		menu.createContextMenu(graphicalViewer.getControl());
		graphicalViewer.setContextMenu(menu);
		getSite().registerContextMenu(menu, graphicalViewer);
	}

	private void createKeyBindings() {
		KeyHandler handler = graphicalViewer.getKeyHandler();
		handler.put(KeyStroke.getPressed(SWT.F2, 0), renameAction);
		graphicalViewer.setKeyHandler(handler);
	}

	private void fillContextMenu(IMenuManager menu) {
		if (andAction.isEnabled() || orAction.isEnabled()) {
			if (andAction.isChecked()) {
				andAction.setText("AND");
				orAction.setText("OR (Double Click)");
				alternativeAction.setText("ALTERNATIVE");
			} else if (orAction.isChecked()) {
				andAction.setText("AND");
				orAction.setText("OR");
				alternativeAction.setText("ALTERNATIVE (Double Click)");
			} else if (alternativeAction.isChecked()) {
				andAction.setText("AND (Double Click)");
				orAction.setText("OR");
				alternativeAction.setText("ALTERNATIVE");
			}
			menu.add(andAction);
			menu.add(orAction);
			menu.add(alternativeAction);
		} else if (createLayerAction.isEnabled()
				|| createCompoundAction.isEnabled()) {
			menu.add(createCompoundAction);
			menu.add(createLayerAction);
			menu.add(mandantoryAction);
			menu.add(abstractAction);
			menu.add(hiddenAction);
			menu.add(deleteAction);
			menu.add(renameAction);
		} else {

			menu.add(createConstraintAction);
			menu.add(editConstraintAction);
			menu.add(deleteAction);
			menu.add(reverseOrderAction);
		}
		menu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
	}

	public IAction getDiagramAction(String workbenchActionID) {

		if (CreateLayerAction.ID.equals(workbenchActionID))
			return createLayerAction;
		if (CreateCompoundAction.ID.equals(workbenchActionID))
			return createCompoundAction;
		if (DeleteAction.ID.equals(workbenchActionID))
			return deleteAction;
		if (MandantoryAction.ID.equals(workbenchActionID))
			return mandantoryAction;
		if (AbstractAction.ID.equals(workbenchActionID))
			return abstractAction;
		if (HiddenAction.ID.equals(workbenchActionID))
			return hiddenAction;
		if (AndAction.ID.equals(workbenchActionID))
			return andAction;
		if (OrAction.ID.equals(workbenchActionID))
			return orAction;
		if (AlternativeAction.ID.equals(workbenchActionID))
			return alternativeAction;
		if (ActionFactory.PRINT.getId().equals(workbenchActionID))
			return printAction;
		if (ActionFactory.SELECT_ALL.getId().equals(workbenchActionID))
			return selectAllAction;
		if (ActionFactory.UNDO.getId().equals(workbenchActionID))
			return undoAction;
		if (ActionFactory.REDO.getId().equals(workbenchActionID))
			return redoAction;
		if (RenameAction.ID.equals(workbenchActionID))
			return renameAction;
		if (GEFActionConstants.ZOOM_IN.equals(workbenchActionID))
			return zoomIn;
		if (GEFActionConstants.ZOOM_OUT.equals(workbenchActionID))
			return zoomOut;
		FMCorePlugin
				.getDefault()
				.logInfo(
						"The following workbench action is not registered at the feature diagram editor: "
								+ workbenchActionID);
		return null;
	}

	void initDiagramContent() {
		graphicalViewer.getControl().getDisplay().asyncExec(new Runnable() {
			public void run() {
				graphicalViewer.setContents(featureModel);
				isPageModified = true;
				pageChange(graphicalViewerIndex);
			}
		});
	}

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

	void initializeGraphicalViewer() {
		graphicalViewer.getControl().setBackground(DIAGRAM_BACKGROUND);
		graphicalViewer.setEditPartFactory(new GraphicalEditPartFactory());
		rootEditPart = new ScalableFreeformRootEditPart();
		((ConnectionLayer) rootEditPart
				.getLayer(LayerConstants.CONNECTION_LAYER))
				.setAntialias(SWT.ON);
		graphicalViewer.setRootEditPart(rootEditPart);
	}

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
		if (getActivePage() == graphicalViewerIndex)
			graphicalViewer.getControl().setFocus();
		else
			textEditor.setFocus();
	}

	private int oldPage;

	@Override
	protected void pageChange(int newPageIndex) {
		if (oldPage == graphicalViewerIndex) {
			if (newPageIndex == textEditorIndex) {
				if (isPageModified)
					updateTextEditorFromDiagram();
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
	}

	/**
	 *  
	 */
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
			GEFImageWriter.writeToFile(graphicalViewer, file);
		}
	}

	public void propertyChange(PropertyChangeEvent event) {

		String prop = event.getPropertyName();
		if (prop.equals(MODEL_DATA_CHANGED)) {
			refreshGraphicalViewer();
			isPageModified = true;
			firePropertyChange(PROP_DIRTY);
		} else if (prop.equals(MODEL_DATA_LOADED)) {
			refreshGraphicalViewer();
		} else if (prop.equals(REDRAW_DIAGRAM)) {

			updateTextEditorFromDiagram();
			updateDiagramFromTextEditor();
		}
	}

	private void refreshGraphicalViewer() {
		if (graphicalViewer.getContents() == null)
			return;

		// refresh size of all feature figures
		graphicalViewer.getContents().refresh();
		// layout all features
		Point size = graphicalViewer.getControl().getSize();
		layoutManager.setControlSize(size.x, size.y);
		layoutManager.layout(featureModel);

		// refresh position of all feature figures
		graphicalViewer.getContents().refresh();
	}

	@SuppressWarnings("rawtypes")
	@Override
	public Object getAdapter(Class adapter) {
		if (GraphicalViewer.class.equals(adapter)
				|| EditPartViewer.class.equals(adapter))
			return graphicalViewer;
		if (ZoomManager.class.equals(adapter))
			return zoomManager;
		if (CommandStack.class.equals(adapter))
			return graphicalViewer.getEditDomain().getCommandStack();
		if (EditDomain.class.equals(adapter))
			return graphicalViewer.getEditDomain();
		if (IGotoMarker.class.equals(adapter))
			if (getActivePage() != textEditorIndex)
				setActivePage(textEditorIndex);
		return super.getAdapter(adapter);
	}

	@Override
	public int getActivePage() {
		return super.getActivePage();
	}

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
