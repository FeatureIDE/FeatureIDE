/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.fm.ui.editors;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.draw2d.ConnectionLayer;
import org.eclipse.gef.DefaultEditDomain;
import org.eclipse.gef.EditDomain;
import org.eclipse.gef.EditPartViewer;
import org.eclipse.gef.GraphicalViewer;
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
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.ide.IGotoMarker;
import org.eclipse.ui.part.MultiPageEditorPart;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;
import org.sat4j.specs.TimeoutException;

import featureide.fm.core.FeatureModel;
import featureide.fm.core.GrammarFile;
import featureide.fm.core.PropertyConstants;
import featureide.fm.core.io.IFeatureModelReader;
import featureide.fm.core.io.IFeatureModelWriter;
import featureide.fm.core.io.ModelWarning;
import featureide.fm.core.io.UnsupportedModelException;
import featureide.fm.core.io.guidsl.FeatureModelReader;
import featureide.fm.core.io.guidsl.FeatureModelWriter;
import featureide.fm.core.io.xml.XmlFeatureModelWriter;
import featureide.fm.ui.editors.featuremodel.FeatureModelEditorContributor;
import featureide.fm.ui.editors.featuremodel.GEFImageWriter;
import featureide.fm.ui.editors.featuremodel.GUIDefaults;
import featureide.fm.ui.editors.featuremodel.actions.AlternativeAction;
import featureide.fm.ui.editors.featuremodel.actions.AndAction;
import featureide.fm.ui.editors.featuremodel.actions.CreateCompoundAction;
import featureide.fm.ui.editors.featuremodel.actions.CreateLayerAction;
import featureide.fm.ui.editors.featuremodel.actions.DeleteAction;
import featureide.fm.ui.editors.featuremodel.actions.MandantoryAction;
import featureide.fm.ui.editors.featuremodel.actions.OrAction;
import featureide.fm.ui.editors.featuremodel.editparts.GraphicalEditPartFactory;
import featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutManager;
import featureide.fm.ui.editors.featuremodel.layouts.LevelOrderLayout;

/**
 * A multi page editor to edit feature models. If the model file contains
 * errors, markers will be created on save.
 * 
 * @author Thomas Thuem
 */
public class FeatureModelEditor extends MultiPageEditorPart implements GUIDefaults,
		PropertyConstants, PropertyChangeListener {

	public static final String ID = "featureide.fm.ui.editors.GrammarEditor";

	private GraphicalViewerImpl graphicalViewer;

	private TextEditor textEditor;

	private int graphicalViewerIndex;

	private int textEditorIndex;

	private boolean isPageModified;

	private FeatureModel featureModel;

	private IFeatureModelReader featureModelReader;

	private IFeatureModelWriter featureModelWriter;
	
	private IFeatureModelWriter xmlFeatureModelWriter;

	private CreateLayerAction createLayerAction;

	private CreateCompoundAction createCompoundAction;

	private DeleteAction deleteAction;

	private MandantoryAction mandantoryAction;

	private AndAction andAction;

	private OrAction orAction;

	private AlternativeAction alternativeAction;
	
	private PrintAction printAction;

	private SelectAllAction selectAllAction;

	private UndoAction undoAction;

	private RedoAction redoAction;
	
	private ZoomInAction zoomIn;
	
	private ZoomOutAction zoomOut;

	private FeatureDiagramLayoutManager layoutManager = new LevelOrderLayout();

	private GrammarFile grammarFile;

	private FeatureModel originalFeatureModel;

	private ZoomManager zoomManager;

	private ScalableFreeformRootEditPart rootEditPart;

	@Override
	protected void setInput(IEditorInput input) {
		IFile file = (IFile) input.getAdapter(IFile.class);
		grammarFile = new GrammarFile(file);
		setPartName(file.getProject().getName() + " Model");
		setTitleToolTip(input.getToolTipText());
		super.setInput(input);

		featureModel = new FeatureModel();
		featureModel.addListener(this);
		featureModelReader = new FeatureModelReader(featureModel);
		featureModelWriter = new FeatureModelWriter(featureModel);
		xmlFeatureModelWriter = new XmlFeatureModelWriter(featureModel);

		originalFeatureModel = new FeatureModel();
		try {
			new FeatureModelReader(originalFeatureModel).readFromFile(file);
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
		createActions();
		createContextMenu();
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
		zoomManager.setZoomLevels(new double[] {0.05, 0.10, 0.25, 0.50, 0.75, 0.90, 1.00, 1.10, 1.25, 1.50, 2.00, 2.50, 3.00, 4.00});
	}

	void createSourcePage() {
		textEditor = new TextEditor();
		try {
			textEditorIndex = addPage(textEditor, getEditorInput());
			setPageText(textEditorIndex, "Source");
		} catch (PartInitException e) {
			e.printStackTrace();
		}
	}

	private void createActions() {
		createLayerAction = new CreateLayerAction(graphicalViewer, featureModel);
		createCompoundAction = new CreateCompoundAction(graphicalViewer,
				featureModel);
		deleteAction = new DeleteAction(graphicalViewer, featureModel);
		mandantoryAction = new MandantoryAction(graphicalViewer, featureModel);
		andAction = new AndAction(graphicalViewer, featureModel);
		orAction = new OrAction(graphicalViewer, featureModel);
		alternativeAction = new AlternativeAction(graphicalViewer, featureModel);
		printAction = new PrintAction(this);
		selectAllAction = new SelectAllAction(this);
		undoAction = new UndoAction(this);
		redoAction = new RedoAction(this);
		zoomIn = new ZoomInAction(zoomManager);
		zoomOut = new ZoomOutAction(zoomManager);
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

	private void fillContextMenu(IMenuManager menu) {
		if (andAction.isEnabled() || orAction.isEnabled()
				|| alternativeAction.isEnabled()) {
			menu.add(andAction);
			menu.add(orAction);
			menu.add(alternativeAction);
		} else {
			menu.add(createLayerAction);
			menu.add(createCompoundAction);
			menu.add(deleteAction);
			menu.add(mandantoryAction);
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
		if (GEFActionConstants.ZOOM_IN.equals(workbenchActionID))
			return zoomIn;
		if (GEFActionConstants.ZOOM_OUT.equals(workbenchActionID))
			return zoomOut;
		System.out.println("The following workbench action is not registered at the feature diagram editor: " + workbenchActionID);
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
					grammarFile.createModelMarker(
						"The feature model is void, i.e., it contains no products",
						IMarker.SEVERITY_ERROR, 0);
			} catch (TimeoutException e) {
				//do nothing, assume the model is correct
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

	@Override
	protected void pageChange(int newPageIndex) {
		if (newPageIndex == textEditorIndex) {
			if (isPageModified)
				updateTextEditorFromDiagram();
		} else { // newPageIndex == graphicalViewerIndex
			if (isDirty() || grammarFile.hasModelMarkers())
				if (!updateDiagramFromTextEditor()) {
					// there are errors in the file, stay at this editor page
					isPageModified = false;
					setActivePage(textEditorIndex);
					return;
				}
		}
		isPageModified = false;

		IEditorActionBarContributor contributor = getEditorSite()
				.getActionBarContributor();
		if (contributor instanceof FeatureModelEditorContributor)
			((FeatureModelEditorContributor) contributor).setActivePage(this,
					newPageIndex);

		super.pageChange(newPageIndex);
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		if (getActivePage() == graphicalViewerIndex && isPageModified) {
			updateTextEditorFromDiagram();
			setActivePage(textEditorIndex);
			setActivePage(graphicalViewerIndex);
		} else
			updateDiagramFromTextEditor();
		isPageModified = false;
		featureModel.performRenamings();
		textEditor.doSave(monitor);
		try {
			new FeatureModelReader(originalFeatureModel)
					.readFromFile(grammarFile.getResource());
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	@Override
	public boolean isSaveAsAllowed() {
		return true;
	}

	@Override
	public void doSaveAs() {
		FileDialog fileDialog = new FileDialog(getEditorSite().getShell(), SWT.SAVE);
		String[] extensions = {
				"*.bmp",
//				"*.gif", 
//				"*.ico", 
				"*.jpg", 
				"*.m",
				"*.png", 
//				"*.tif", 
				"*.xml" };
		fileDialog.setFilterExtensions(extensions);
		String[] filterNames = {
				"Windows Bitmap *.bmp",
//				"CompuServe GIF *.gif",
//				"Windows Icon *.ico",
				"JPEG *.jpg",
				"GUIDSL Grammar *.m",
				"Portable Network Graphics *.png",
//				"TIFF *.tif",
				"XML Export *.xml"};
		fileDialog.setFilterNames(filterNames);
		fileDialog.setOverwrite(true);
		String filePath = fileDialog.open();
		if (filePath == null)
			return;
		File file = new File(filePath);
		if (filePath.endsWith(".m")) {
			featureModelWriter.writeToFile(file);
		} else if (filePath.endsWith(".xml")) {
			xmlFeatureModelWriter.writeToFile(file);
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

	@SuppressWarnings("unchecked")
	@Override
	public Object getAdapter(Class adapter) {
		if (GraphicalViewer.class.equals(adapter) || EditPartViewer.class.equals(adapter))
			return graphicalViewer;
		if (ZoomManager.class.equals(adapter))
			return zoomManager;
		if (CommandStack.class.equals(adapter))
			return graphicalViewer.getEditDomain().getCommandStack();
		if (EditDomain.class.equals(adapter))
			return graphicalViewer.getEditDomain();
		if (IGotoMarker.class.equals(adapter))
			if (getActivePage() == graphicalViewerIndex)
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

}
