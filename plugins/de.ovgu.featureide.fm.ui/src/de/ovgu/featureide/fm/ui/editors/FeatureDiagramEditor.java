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

import org.eclipse.core.commands.operations.ObjectUndoContext;
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
import org.eclipse.gef.ui.actions.ZoomInAction;
import org.eclipse.gef.ui.actions.ZoomOutAction;
import org.eclipse.gef.ui.parts.GraphicalViewerKeyHandler;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbenchActionConstants;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
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
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.LayoutSelectionAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.LegendAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.LegendLayoutAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.MandatoryAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ManualLayoutSelectionAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.OrAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.RenameAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ReverseOrderAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.GraphicalEditPartFactory;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.BreadthFirstLayout;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.DepthFirstLayout;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.LevelOrderLayout;

/**
 * An editor based on the Graphical Editing Framework to view and edit feature
 * diagrams and cross-tree constraints.
 * 
 * @author Thomas Thuem
 */
public class FeatureDiagramEditor extends ScrollingGraphicalViewer implements
		GUIDefaults, PropertyConstants, PropertyChangeListener, IFeatureModelEditorPage {

	private static final String PAGE_TEXT = "Feature Diagram";
	private static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureDiagramEditor";

	private FeatureModelEditor featureModelEditor;

	private ZoomManager zoomManager;

	private ScalableFreeformRootEditPart rootEditPart;

	private CreateLayerAction createLayerAction;
	private CreateCompoundAction createCompoundAction;
	private DeleteAction deleteAction;
	private MandatoryAction mandatoryAction;
	private AbstractAction abstractAction;
	private HiddenAction hiddenAction;
	private AndAction andAction;
	private OrAction orAction;
	private AlternativeAction alternativeAction;
	private RenameAction renameAction;

	private ZoomInAction zoomIn;
	private ZoomOutAction zoomOut;

	private LegendAction legendAction;
	private LegendLayoutAction legendLayoutAction;

	private EditConstraintAction editConstraintAction;
	private CreateConstraintAction createConstraintAction;

	private ReverseOrderAction reverseOrderAction;
	
	private LayoutSelectionAction setLevelOrderLayoutAction;
	private LayoutSelectionAction setBreadthFirstLayoutAction;
	private LayoutSelectionAction setDepthFirstLayoutAction;
	
	private ManualLayoutSelectionAction manualLayoutSelectionAction;

	private int index;

	public FeatureDiagramEditor(FeatureModelEditor featureModelEditor,
			Composite container) {
		super();
		this.featureModelEditor = featureModelEditor;

		setKeyHandler(new GraphicalViewerKeyHandler(this));

		createControl(container);
		initializeGraphicalViewer();
		setEditDomain(new DefaultEditDomain(featureModelEditor));

		zoomManager = rootEditPart.getZoomManager();
		zoomManager.setZoomLevels(new double[] { 0.05, 0.10, 0.25, 0.50, 0.75,
				0.90, 1.00, 1.10, 1.25, 1.50, 2.00, 2.50, 3.00, 4.00 });
	}

	void initializeGraphicalViewer() {
		getControl().setBackground(DIAGRAM_BACKGROUND);
		setEditPartFactory(new GraphicalEditPartFactory());
		rootEditPart = new ScalableFreeformRootEditPart();
		((ConnectionLayer) rootEditPart
				.getLayer(LayerConstants.CONNECTION_LAYER))
				.setAntialias(SWT.ON);
		setRootEditPart(rootEditPart);
	}

	private FeatureModel getFeatureModel() {
		return featureModelEditor.getFeatureModel();
	}

	public void createActions() {
		FeatureModel featureModel = getFeatureModel();

		createLayerAction = new CreateLayerAction(this, featureModel);
		createCompoundAction = new CreateCompoundAction(this, featureModel);
		deleteAction = new DeleteAction(this, featureModel);
		mandatoryAction = new MandatoryAction(this, featureModel);
		hiddenAction = new HiddenAction(this, featureModel);
		abstractAction = new AbstractAction(this, featureModel,
				(ObjectUndoContext) featureModel.getUndoContext());
		andAction = new AndAction(this, featureModel);
		orAction = new OrAction(this, featureModel);
		alternativeAction = new AlternativeAction(this, featureModel);
		renameAction = new RenameAction(this, featureModel);

		createConstraintAction = new CreateConstraintAction(this, featureModel,
				"Create Constraint");
		editConstraintAction = new EditConstraintAction(this, featureModel,
				"Edit Constraint");
		reverseOrderAction = new ReverseOrderAction(this, featureModel);

		legendAction = new LegendAction(this, featureModel);
		legendLayoutAction = new LegendLayoutAction(this, featureModel);

		zoomIn = new ZoomInAction(zoomManager);
		zoomOut = new ZoomOutAction(zoomManager);
		
		setLevelOrderLayoutAction = new LayoutSelectionAction(this, featureModel,0,0);
		setBreadthFirstLayoutAction = new LayoutSelectionAction(this, featureModel,1,0);
		setDepthFirstLayoutAction = new LayoutSelectionAction(this, featureModel,2,0);
		
		manualLayoutSelectionAction = new ManualLayoutSelectionAction(this, featureModel);
	}

	public void createContextMenu(MenuManager menu) {
		menu.addMenuListener(new IMenuListener() {
			public void menuAboutToShow(IMenuManager manager) {
				FeatureDiagramEditor.this.fillContextMenu(manager);
			}
		});
		menu.createContextMenu(getControl());
		setContextMenu(menu);
		// the following line adds package explorer entries into our context
		// menu
		// getSite().registerContextMenu(menu, graphicalViewer);
	}

	public void createKeyBindings() {
		KeyHandler handler = getKeyHandler();
		handler.put(KeyStroke.getPressed(SWT.F2, 0), renameAction);
		handler.put(KeyStroke.getPressed(SWT.INSERT, 0), createLayerAction);
		setKeyHandler(handler);
	}
	
	public void createContextSubMenu(MenuManager menu) {
		menu.addMenuListener(new IMenuListener() {
			public void menuAboutToShow(IMenuManager manager) {
				FeatureDiagramEditor.this.fillContextMenu(manager);
			}
		});
		menu.createContextMenu(getControl());
		setContextMenu(menu);
	}
	
	private void fillContextMenu(IMenuManager menu) {
			
		/*
		 * Menu Management for Feature Diagram Layout entries
		 */
		if(getFeatureModel().hasModelAutoLayout()){
			setLevelOrderLayoutAction.setEnabled(true);
			setBreadthFirstLayoutAction.setEnabled(true);
			setDepthFirstLayoutAction.setEnabled(true);
			setLevelOrderLayoutAction.setChecked(false);
			setBreadthFirstLayoutAction.setChecked(false);
			setDepthFirstLayoutAction.setChecked(false);
			if(getFeatureModel().getLayoutAlgorithm() == 1){
				setBreadthFirstLayoutAction.setEnabled(false);
				setBreadthFirstLayoutAction.setChecked(true);	
			} else if(getFeatureModel().getLayoutAlgorithm() == 2){
				setDepthFirstLayoutAction.setEnabled(false);
				setDepthFirstLayoutAction.setChecked(true);
			} else {
				setLevelOrderLayoutAction.setEnabled(false);
				setLevelOrderLayoutAction.setChecked(true);
			}
		} else {
			setLevelOrderLayoutAction.setEnabled(false);
			setBreadthFirstLayoutAction.setEnabled(false);
			setDepthFirstLayoutAction.setEnabled(false);
			setLevelOrderLayoutAction.setChecked(false);
			setBreadthFirstLayoutAction.setChecked(false);
			setDepthFirstLayoutAction.setChecked(false);
		}
		
		if (andAction.isEnabled() || orAction.isEnabled()) {
			if (andAction.isChecked()) {
				andAction.setText("And");
				orAction.setText("Or (Double Click)");
				alternativeAction.setText("Alternative");
			} else if (orAction.isChecked()) {
				andAction.setText("And");
				orAction.setText("Or");
				alternativeAction.setText("Alternative (Double Click)");
			} else if (alternativeAction.isChecked()) {
				andAction.setText("And (Double Click)");
				orAction.setText("Or");
				alternativeAction.setText("Alternative");
			}
			menu.add(andAction);
			menu.add(orAction);
			menu.add(alternativeAction);
		} else if (createLayerAction.isEnabled()
				|| createCompoundAction.isEnabled()) {
			menu.add(createCompoundAction);
			menu.add(createLayerAction);
			menu.add(createConstraintAction);
			menu.add(renameAction);
			menu.add(deleteAction);
			menu.add(new Separator());
			menu.add(mandatoryAction);
			menu.add(abstractAction);
			menu.add(hiddenAction);
			menu.add(new Separator());
			//menu.add(manualLayoutSelectionAction);
			menu.add(setLevelOrderLayoutAction);
			menu.add(setBreadthFirstLayoutAction);
			menu.add(setDepthFirstLayoutAction);
			menu.add(new Separator());
			menu.add(reverseOrderAction);
		} else if (editConstraintAction.isEnabled()) {
			menu.add(createConstraintAction);
			menu.add(editConstraintAction);
			menu.add(deleteAction);
		} else if (legendLayoutAction.isEnabled()){
			menu.add(legendLayoutAction);
		} else {
			menu.add(createConstraintAction);
			menu.add(new Separator());
			//menu.add(manualLayoutSelectionAction);
			menu.add(setLevelOrderLayoutAction);
			menu.add(setBreadthFirstLayoutAction);
			menu.add(setDepthFirstLayoutAction);
			menu.add(new Separator());
			menu.add(reverseOrderAction);	
		}
		menu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
		menu.add(legendAction);
		menu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
	}

	public IAction getDiagramAction(String workbenchActionID) {
		if (CreateLayerAction.ID.equals(workbenchActionID))
			return createLayerAction;
		if (CreateCompoundAction.ID.equals(workbenchActionID))
			return createCompoundAction;
		if (DeleteAction.ID.equals(workbenchActionID))
			return deleteAction;
		if (MandatoryAction.ID.equals(workbenchActionID))
			return mandatoryAction;
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
		if (RenameAction.ID.equals(workbenchActionID))
			return renameAction;
		if (GEFActionConstants.ZOOM_IN.equals(workbenchActionID))
			return zoomIn;
		if (GEFActionConstants.ZOOM_OUT.equals(workbenchActionID))
			return zoomOut;
		return null;
	}

	public void refresh() {
		if (getContents() == null)
			return;

		// refresh size of all feature figures
		getContents().refresh();
		// layout all features if autoLayout is enabled
		if(getFeatureModel().hasModelAutoLayout()){
			setLayout();
		}
		// refresh position of all feature figures
		getContents().refresh();
	}

	public void setLayout(){
		
		FeatureDiagramLayoutManager layoutManager;
		FeatureModel featureModel = getFeatureModel();
		
		switch(getFeatureModel().getLayoutAlgorithm()){
			case 1: 
				layoutManager = new BreadthFirstLayout();
				break;
			case 2: 
				layoutManager = new DepthFirstLayout();
				break;
			default:
				layoutManager = new LevelOrderLayout();
				break;
		}	
		
		int previousLayout = featureModel.getLayoutAlgorithm();
		
		setLevelOrderLayoutAction = new LayoutSelectionAction(this, featureModel,0,previousLayout);
		setBreadthFirstLayoutAction = new LayoutSelectionAction(this, featureModel,1,previousLayout);
		setDepthFirstLayoutAction = new LayoutSelectionAction(this, featureModel,2,previousLayout);
		
		Point size = getControl().getSize();
		layoutManager.setControlSize(size.x, size.y);
		layoutManager.layout(featureModel);
		
		
		

				
	}
	
	@SuppressWarnings("rawtypes")
	public Object getAdapter(Class adapter) {
		if (GraphicalViewer.class.equals(adapter)
				|| EditPartViewer.class.equals(adapter))
			return this;
		if (ZoomManager.class.equals(adapter))
			return zoomManager;
		if (CommandStack.class.equals(adapter))
			return getEditDomain().getCommandStack();
		if (EditDomain.class.equals(adapter))
			return getEditDomain();
		return null;
	}

	public void propertyChange(PropertyChangeEvent event) {
		String prop = event.getPropertyName();
		if (prop.equals(MODEL_DATA_CHANGED)) {
			setContents(getFeatureModel());
			refresh();
			featureModelEditor.setPageModified(true);
		} else if (prop.equals(MODEL_DATA_LOADED)) {
			refresh();
		} else if (prop.equals(REDRAW_DIAGRAM)) {
			featureModelEditor.textEditor.updateTextEditor();
			featureModelEditor.textEditor.updateDiagram();
		} else if (prop.equals(REFRESH_ACTIONS)) {
			// additional actions can be refreshed here
			legendAction.refresh();
			legendLayoutAction.refresh();
		}
		
		for (IFeatureModelEditorPage page : featureModelEditor.extensionPages) {
			page.propertyChange(event);
		}
	}

	public void setIndex(int index) {
		this.index = index;
	}

	public int getIndex() {
		return index;
	}

	public String getPageText() {
		return PAGE_TEXT;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#initEditor()
	 */
	@Override
	public void initEditor() {
		createContextMenu();
		createActions();
		createKeyBindings();
	}
	
	private void createContextMenu() {
		MenuManager menu = new MenuManager("#PopupMenu");
		menu.setRemoveAllWhenShown(true);
		createContextMenu(menu);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#setFeatureModelEditor(de.ovgu.featureide.fm.ui.editors.FeatureModelEditor)
	 */
	@Override
	public void setFeatureModelEditor(FeatureModelEditor featureModelEditor) {
		this.featureModelEditor = featureModelEditor;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#getPage()
	 */
	@Override
	public IFeatureModelEditorPage getPage(Composite container) {
		return new FeatureDiagramEditor(featureModelEditor, container);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#doSave(org.eclipse.core.runtime.IProgressMonitor)
	 */
	@Override
	public void doSave(IProgressMonitor monitor) {
		
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#pageChangeFrom(int)
	 */
	@Override
	public void pageChangeFrom(int newPage) {
		
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#pageChangeTo(int)
	 */
	@Override
	public void pageChangeTo(int oldPage) {
		
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#getID()
	 */
	@Override
	public String getID() {
		return ID;
	}

}
