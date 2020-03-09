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
package de.ovgu.featureide.fm.attributes.view;

import java.util.ArrayList;
import java.util.EventObject;
import java.util.HashMap;
import java.util.List;

import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.dialogs.IPageChangedListener;
import org.eclipse.jface.dialogs.PageChangedEvent;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ColumnViewerEditor;
import org.eclipse.jface.viewers.ColumnViewerEditorActivationEvent;
import org.eclipse.jface.viewers.ColumnViewerEditorActivationStrategy;
import org.eclipse.jface.viewers.ColumnViewerToolTipSupport;
import org.eclipse.jface.viewers.FocusCellOwnerDrawHighlighter;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.jface.viewers.TreeViewerEditor;
import org.eclipse.jface.viewers.TreeViewerFocusCellManager;
import org.eclipse.jface.viewers.ViewerCell;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.attributes.FMAttributesPlugin;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.attributes.config.ExtendedConfiguration;
import de.ovgu.featureide.fm.attributes.view.actions.AddFeatureAttributeAction;
import de.ovgu.featureide.fm.attributes.view.actions.CollapseAllButFirstLevel;
import de.ovgu.featureide.fm.attributes.view.actions.ExpandTreeViewer;
import de.ovgu.featureide.fm.attributes.view.actions.RemoveFeatureAttributeAction;
import de.ovgu.featureide.fm.attributes.view.editingsupports.FeatureAttributeConfigureableEditingSupport;
import de.ovgu.featureide.fm.attributes.view.editingsupports.FeatureAttributeNameEditingSupport;
import de.ovgu.featureide.fm.attributes.view.editingsupports.FeatureAttributeRecursiveEditingSupport;
import de.ovgu.featureide.fm.attributes.view.editingsupports.FeatureAttributeUnitEditingSupport;
import de.ovgu.featureide.fm.attributes.view.editingsupports.FeatureAttributeValueEditingSupport;
import de.ovgu.featureide.fm.attributes.view.labelprovider.FeatureAttributeConfigureableColumnLabelProvider;
import de.ovgu.featureide.fm.attributes.view.labelprovider.FeatureAttributeNameColumnLabelProvider;
import de.ovgu.featureide.fm.attributes.view.labelprovider.FeatureAttributeRecursiveColumnLabelProvider;
import de.ovgu.featureide.fm.attributes.view.labelprovider.FeatureAttributeTypeColumnLabelProvider;
import de.ovgu.featureide.fm.attributes.view.labelprovider.FeatureAttributeUnitColumnLabelProvider;
import de.ovgu.featureide.fm.attributes.view.labelprovider.FeatureAttributeValueColumnLabelProvider;
import de.ovgu.featureide.fm.attributes.view.listener.FeatureAttributeSelectionListener;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.AFileManager;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationTreeEditorPage;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeature;

/**
 * A view to help the user of managing attributes of {@link ExtendedFeatureModel}. This includes the creation, edit, filtering and deletion of such attributes.
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class FeatureAttributeView extends ViewPart implements IEventListener {

	public enum FeatureAttributeOperationMode {

		NONE(StringTable.PLEASE_OPEN_A_FEATURE_DIAGRAM_EDITOR), NON_EXTENDED_FEATURE_MODEL(
				StringTable.MODEL_NOT_SUPPORTED_PLEASE_CONVERT_TO_EXTENDED_MODEL), INVALID_FM_PAGE(
						StringTable.PAGE_NOT_SUPPORTED_EXTENDED_FEATURE_MODEL), FEATURE_DIAGRAM(
								StringTable.SELECT_FEATURES_IN_FEATURE_DIAGRAM), NON_EXTENDED_CONFIGURATION(
										StringTable.CONFIG_NOT_SUPPORTED_PLEASE_CREATE_EXTENDED_CONFIG), INVALID_CONFIG_PAGE(
												StringTable.PAGE_NOT_SUPPORTED_EXTENDED_CONFIGURATION), CONFIGURATION_EDITOR(
														StringTable.NO_CONFIGURABLE_ATTRIBUTES);

		private Object message;

		private FeatureAttributeOperationMode(Object message) {
			this.message = message;
		}

		public Object getMessage() {
			return message;
		}
	}

	public final static String imgFeature = "FeatureIconSmall.ico";
	public final static String imgAttribute = "attribute_obj.ico";
	public final static String imgAttributeRecurisve = "recursive_attribute_obj.ico";
	public final static String checkboxEnabled = "icon_reg_enable.png";
	public final static String checkboxDisabled = "icon_reg_disable.png";
	public final static String expandAll = "expand.gif";
	public final static String collapseAll = "collapse.gif";
	public final static String synch_tree = "synch_tree.gif";
	private final HashMap<String, Image> cachedImages;

	private Tree tree;
	private TreeViewer treeViewer;
	private GridLayout layout;
	private MenuManager menuManager;
	private final String COLUMN_ELEMENT = "Element";
	private final String COLUMN_TYPE = "Type";
	private final String COLUMN_VALUE = "Value";
	private final String COLUMN_UNIT = "Unit";
	private final String COLUMN_RECURSIVE = "Recursive";
	private final String COLUMN_CONFIGURABLE = "Configureable";

	// EditingSupports
	private FeatureAttributeNameEditingSupport nameEditingSupport;
	private FeatureAttributeUnitEditingSupport unitEditingSupport;
	private FeatureAttributeValueEditingSupport valueEditingSupport;
	private FeatureAttributeRecursiveEditingSupport recursiveEditingSupport;
	private FeatureAttributeConfigureableEditingSupport configureableEditingSupport;

	// Selection and filtering
	public boolean synchToFeatureDiagram = true;
	private FeatureAttributeSelectionListener selectionListener;
	// Dynamic data objects
	private IWorkbenchPart currentEditor;
	private AFileManager<?> manager;

	// Feature attribute view states
	private FeatureAttributeOperationMode mode;

	public FeatureAttributeView() {
		super();
		cachedImages = new HashMap<String, Image>();
		cachedImages.put(imgFeature, FMAttributesPlugin.getImage(imgFeature));
		cachedImages.put(imgAttribute, FMAttributesPlugin.getImage(imgAttribute));
		cachedImages.put(imgAttributeRecurisve, FMAttributesPlugin.getImage(imgAttributeRecurisve));
		cachedImages.put(checkboxEnabled, FMAttributesPlugin.getImage(checkboxEnabled));
		cachedImages.put(checkboxDisabled, FMAttributesPlugin.getImage(checkboxDisabled));
		cachedImages.put(expandAll, FMAttributesPlugin.getImage(expandAll));
		cachedImages.put(collapseAll, FMAttributesPlugin.getImage(collapseAll));
		cachedImages.put(synch_tree, FMAttributesPlugin.getImage(synch_tree));
		mode = FeatureAttributeOperationMode.NONE;
		FeatureColorManager.addListener(this);
	}

	public FeatureAttributeOperationMode getMode() {
		return mode;
	}

	private final IPageChangedListener pageListener = new IPageChangedListener() {

		@Override
		public void pageChanged(PageChangedEvent event) {
			if (event.getSource() instanceof IEditorPart) {
				setEditorContentByEditor((IEditorPart) event.getSource());
			}
		}

	};
	private final IPartListener editorListener = new IPartListener() {

		@Override
		public void partOpened(IWorkbenchPart part) {

		}

		@Override
		public void partDeactivated(IWorkbenchPart part) {

		}

		@Override
		public void partClosed(IWorkbenchPart part) {
			if (currentEditor == part) {
				setEditorContent(null);
			}
		}

		@Override
		public void partBroughtToTop(IWorkbenchPart part) {
			if (getSite().getPart() != part && currentEditor != part) {
				setEditorContent(part);
			}
		}

		@Override
		public void partActivated(IWorkbenchPart part) {
			if (getSite().getPart() != part && currentEditor != part) {
				setEditorContent(part);
			}
		}

	};

	@Override
	public void init(IViewSite site) throws PartInitException {
		super.init(site);
	}

	@Override
	public void createPartControl(Composite parent) {
		// Add part listener and resource listener
		getSite().getPage().addPartListener(editorListener);

		// Create Layout
		layout = new GridLayout(2, false);
		parent.setLayout(layout);

		// define the TableViewer
		treeViewer = new TreeViewer(parent, SWT.H_SCROLL | SWT.V_SCROLL | SWT.FULL_SELECTION | SWT.BORDER | SWT.VIRTUAL);
		// create edit supports (inline editors)
		createEditSupports();
		// create the columns
		createColumns();

		selectionListener = new FeatureAttributeSelectionListener(this, treeViewer);
		treeViewer.addFilter(new FeatureAttributeViewSelectionFilter(this));
		treeViewer.setContentProvider(new FeatureAttributeContentProvider(this));
		treeViewer.setUseHashlookup(true);

		// make lines and header visible and set layout
		tree = treeViewer.getTree();
		tree.setHeaderVisible(true);
		tree.setLinesVisible(true);
		final GridData gridData = new GridData(GridData.FILL, GridData.FILL, true, true);
		gridData.horizontalSpan = 2;
		tree.setLayoutData(gridData);

		if (!treeViewer.getControl().isDisposed()) {
			setEditorContent(null);
		}

		// create the contex menu
		createContexMenu();

		// create a tree viewer editor to only activate the editing supports when double clicking a cell
		createTreeViewerEditor();

		// pack all columns
		repackAllColumns();
	}

	private void repackAllColumns() {
		for (final TreeColumn col : tree.getColumns()) {
			col.pack();
		}
	}

	/**
	 * Returns all {@link IFeature} which should be displayed in the {@link FeatureAttributeView}.
	 * 
	 * @return Set of all filtered {@link IFeature}, null if empty
	 */
	public List<IFeature> getSelectedFeatures() {
		return selectionListener != null ? selectionListener.getSelectedFeatures() : null;
	}

	/**
	 * Returns all {@link IFeature} whose {@link FeatureAttribute} should be displayed in the {@link FeatureAttributeView}.
	 * 
	 * @return Set of all filtered {@link IFeature}, null if empty
	 */
	public List<IFeature> getSelectedFeaturesOfInterest() {
		return selectionListener != null ? selectionListener.getSelectedFeaturesOfInterest() : null;
	}

	/**
	 * Removes all {@link IFeature} from the selection.
	 */
	public void clearSelection() {
		if (selectionListener != null) {
			selectionListener.clearSelection();
		}
	}

	private void createTreeViewerEditor() {
		final TreeViewerFocusCellManager focusCellManager = new TreeViewerFocusCellManager(treeViewer, new FocusCellOwnerDrawHighlighter(treeViewer));
		final ColumnViewerEditorActivationStrategy activationSupport = new ColumnViewerEditorActivationStrategy(treeViewer) {

			@Override
			protected boolean isEditorActivationEvent(ColumnViewerEditorActivationEvent event) {
				// Enable editor only with mouse double click
				if (event.eventType == ColumnViewerEditorActivationEvent.MOUSE_CLICK_SELECTION) {
					final EventObject source = event.sourceEvent;
					if ((source instanceof MouseEvent) && (((MouseEvent) source).button == 3)) {
						return false;
					}
					if (event.getSource() instanceof ViewerCell) {
						int index = ((ViewerCell) event.getSource()).getColumnIndex();
						if (index == 4 || index == 5) {
							return true;
						}
					}
				} else if (event.eventType == ColumnViewerEditorActivationEvent.MOUSE_DOUBLE_CLICK_SELECTION) {
					final EventObject source = event.sourceEvent;
					if ((source instanceof MouseEvent) && (((MouseEvent) source).button == 3)) {
						return false;
					}
					return true;
				}
				return false;
			}
		};
		TreeViewerEditor.create(treeViewer, focusCellManager, activationSupport, ColumnViewerEditor.TABBING_HORIZONTAL
			| ColumnViewerEditor.TABBING_MOVE_TO_ROW_NEIGHBOR | ColumnViewerEditor.TABBING_VERTICAL | ColumnViewerEditor.KEYBOARD_ACTIVATION);
	}

	private void createEditSupports() {
		nameEditingSupport = new FeatureAttributeNameEditingSupport(this, treeViewer, true);
		unitEditingSupport = new FeatureAttributeUnitEditingSupport(this, treeViewer, true);
		valueEditingSupport = new FeatureAttributeValueEditingSupport(this, treeViewer, true);
		recursiveEditingSupport = new FeatureAttributeRecursiveEditingSupport(this, treeViewer, true);
		configureableEditingSupport = new FeatureAttributeConfigureableEditingSupport(this, treeViewer, true);
	}

	private void createContexMenu() {
		// Toolbar
		IActionBars actionBars = getViewSite().getActionBars();
		IToolBarManager toolBar = actionBars.getToolBarManager();
		toolBar.add(new ExpandTreeViewer(treeViewer, ImageDescriptor.createFromImage(cachedImages.get(expandAll))));
		toolBar.add(new CollapseAllButFirstLevel(treeViewer, ImageDescriptor.createFromImage(cachedImages.get(collapseAll))));

		menuManager = new MenuManager();
		menuManager.setRemoveAllWhenShown(true);
		menuManager.addMenuListener(new IMenuListener() {

			@Override
			public void menuAboutToShow(IMenuManager manager) {
				final IStructuredSelection selection = treeViewer.getStructuredSelection();
				if (!selection.isEmpty() && mode == FeatureAttributeOperationMode.FEATURE_DIAGRAM) {
					FeatureModelManager fmManager = (FeatureModelManager) FeatureAttributeView.this.manager;
					if ((selection.size() == 1) && (selection.getFirstElement() instanceof ExtendedFeature)) {
						final String featureName = selection.getFirstElement().toString();
						// Add actions to create new attributes
						menuManager.add(new AddFeatureAttributeAction(fmManager, featureName, FeatureAttribute.STRING, StringTable.ADD_STRING_ATTRIBUTE));
						menuManager.add(new AddFeatureAttributeAction(fmManager, featureName, FeatureAttribute.BOOLEAN, StringTable.ADD_BOOLEAN_ATTRIBUTE));
						menuManager.add(new AddFeatureAttributeAction(fmManager, featureName, FeatureAttribute.LONG, StringTable.ADD_LONG_ATTRIBUTE));
						menuManager.add(new AddFeatureAttributeAction(fmManager, featureName, FeatureAttribute.DOUBLE, StringTable.ADD_DOUBLE_ATTRIBUTE));
					} else {
						List<IFeatureAttribute> attributes = new ArrayList<>();
						for (final Object object : selection.toList()) {
							if (!(object instanceof IFeatureAttribute)) {
								return;
							} else {
								attributes.add((IFeatureAttribute) object);
							}
						}
						menuManager.add(new RemoveFeatureAttributeAction(fmManager, attributes));
					}
				}
			}
		});
		treeViewer.getControl().setMenu(menuManager.createContextMenu(treeViewer.getControl()));

	}

	private void createColumns() {
		ColumnViewerToolTipSupport.enableFor(treeViewer);
		// Feature
		final TreeViewerColumn colFeature = new TreeViewerColumn(treeViewer, SWT.NONE);
		colFeature.getColumn().setWidth(200);
		colFeature.getColumn().setText(COLUMN_ELEMENT);
		colFeature.setEditingSupport(nameEditingSupport);
		colFeature.setLabelProvider(new FeatureAttributeNameColumnLabelProvider(cachedImages, this));

		// Type
		final TreeViewerColumn colType = new TreeViewerColumn(treeViewer, SWT.NONE);
		colType.getColumn().setWidth(200);
		colType.getColumn().setText(COLUMN_TYPE);
		colType.setLabelProvider(new FeatureAttributeTypeColumnLabelProvider(cachedImages, this));

		// Value
		final TreeViewerColumn colValue = new TreeViewerColumn(treeViewer, SWT.NONE);
		colValue.getColumn().setWidth(200);
		colValue.getColumn().setText(COLUMN_VALUE);
		colValue.setEditingSupport(valueEditingSupport);
		colValue.setLabelProvider(new FeatureAttributeValueColumnLabelProvider(cachedImages, this));

		// Unit
		final TreeViewerColumn colUnit = new TreeViewerColumn(treeViewer, SWT.NONE);
		colUnit.getColumn().setWidth(200);
		colUnit.getColumn().setText(COLUMN_UNIT);
		colUnit.setEditingSupport(unitEditingSupport);
		colUnit.setLabelProvider(new FeatureAttributeUnitColumnLabelProvider(cachedImages, this));

		// Recursive
		final TreeViewerColumn colRecursive = new TreeViewerColumn(treeViewer, SWT.NONE);
		colRecursive.getColumn().setWidth(200);
		colRecursive.getColumn().setText(COLUMN_RECURSIVE);
		colRecursive.setEditingSupport(recursiveEditingSupport);
		colRecursive.setLabelProvider(new FeatureAttributeRecursiveColumnLabelProvider(cachedImages, this));
		// Configureable
		final TreeViewerColumn colConfigureable = new TreeViewerColumn(treeViewer, SWT.NONE);
		colConfigureable.getColumn().setWidth(200);
		colConfigureable.getColumn().setText(COLUMN_CONFIGURABLE);
		colConfigureable.setEditingSupport(configureableEditingSupport);
		colConfigureable.setLabelProvider(new FeatureAttributeConfigureableColumnLabelProvider(cachedImages, this));
	}

	@Override
	public void setFocus() {
		treeViewer.getControl().setFocus();
	}

	private void setEditorContent(IWorkbenchPart activeWorkbenchPart) {
		if (activeWorkbenchPart instanceof IEditorPart) {
			setEditorContentByEditor((IEditorPart) activeWorkbenchPart);
		} else {
			setEditorContentByEditor(null);
		}
	}

	private void setEditorContentByEditor(IEditorPart editor) {
		if (editor != null && (editor instanceof FeatureModelEditor)) {
			final FeatureModelEditor fmEditor = (FeatureModelEditor) editor;
			setEmptyEditorContent();
			setFMEditorContent(fmEditor);
		} else if (editor != null && (editor instanceof ConfigurationEditor)) {
			final ConfigurationEditor confEditor = (ConfigurationEditor) editor;
			setEmptyEditorContent();
			setConfEditorContent(confEditor);
		} else {
			setEmptyEditorContent();
			// Set mode
			mode = FeatureAttributeOperationMode.NONE;
			if (!treeViewer.getControl().isDisposed()) {
				treeViewer.setInput("");
				repackAllColumns();
			}
		}
	}

	private void setEmptyEditorContent() {
		// Clear selection
		clearSelection();

		// Clear editors
		if (currentEditor instanceof FeatureModelEditor) {
			final FeatureModelEditor editor = (FeatureModelEditor) currentEditor;
			editor.removeEventListener(this);
			editor.removePageChangedListener(pageListener);
			editor.diagramEditor.removeSelectionChangedListener(selectionListener);
		} else if (currentEditor instanceof ConfigurationEditor) {
			final ConfigurationEditor editor = (ConfigurationEditor) currentEditor;
			editor.removePageChangedListener(pageListener);
		}
		currentEditor = null;

		// Clear dynamic data objects
		if (manager != null) {
			manager.removeListener(this);
			manager = null;
		}
		return;
	}

	private void setFMEditorContent(FeatureModelEditor editor) {
		currentEditor = editor;
		editor.addEventListener(this);
		editor.addPageChangedListener(pageListener);
		editor.diagramEditor.addSelectionChangedListener(selectionListener);
		if (editor.getSelectedPage() instanceof FeatureDiagramEditor) {
			final FeatureModelManager featureModelManager = editor.getFeatureModelManager();
			IFeatureModel curFeatureModel = featureModelManager.getVarObject();
			if (curFeatureModel instanceof ExtendedFeatureModel) {
				// Valid
				manager = featureModelManager;
				manager.addListener(this);
				mode = FeatureAttributeOperationMode.FEATURE_DIAGRAM;
				if (!treeViewer.getControl().isDisposed()) {
					treeViewer.setInput(curFeatureModel);
				}
			} else {
				// Wrong format
				mode = FeatureAttributeOperationMode.NON_EXTENDED_FEATURE_MODEL;
				if (!treeViewer.getControl().isDisposed()) {
					treeViewer.setInput("");
				}
			}
		} else {
			// Wrong page
			mode = FeatureAttributeOperationMode.INVALID_FM_PAGE;
			if (!treeViewer.getControl().isDisposed()) {
				treeViewer.setInput("");
			}
		}
		repackAllColumns();
	}

	private void setConfEditorContent(ConfigurationEditor editor) {
		currentEditor = editor;
		editor.addPageChangedListener(pageListener);
		if (editor.getSelectedPage() instanceof ConfigurationTreeEditorPage) {
			final ConfigurationManager configurationManager = editor.getConfigurationManager();
			Configuration currentConfiguration = configurationManager.getVarObject();
			if (currentConfiguration instanceof ExtendedConfiguration) {
				// Valid
				manager = configurationManager;
				manager.addListener(this);
				mode = FeatureAttributeOperationMode.CONFIGURATION_EDITOR;
				if (!treeViewer.getControl().isDisposed()) {
					treeViewer.setInput(currentConfiguration);
				}
			} else {
				// Invalid format
				mode = FeatureAttributeOperationMode.NON_EXTENDED_CONFIGURATION;
				if (!treeViewer.getControl().isDisposed()) {
					treeViewer.setInput("");
				}
			}
		} else {
			// Wrong page
			mode = FeatureAttributeOperationMode.INVALID_CONFIG_PAGE;
			if (!treeViewer.getControl().isDisposed()) {
				treeViewer.setInput("");
			}
		}
		treeViewer.expandAll();
		repackAllColumns();
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		if (event.getEventType() == EventType.MODEL_DATA_SAVED) {
			if (!treeViewer.getControl().isDisposed()) {
				treeViewer.refresh(manager.getVarObject());
			}
			if (getMode() == FeatureAttributeOperationMode.CONFIGURATION_EDITOR) {
				treeViewer.expandAll();
				repackAllColumns();
			}
		} else if (event.getEventType() == EventType.FEATURE_ATTRIBUTE_CHANGED) {
			if (event.getOldValue() != null && event.getOldValue() instanceof Boolean && event.getNewValue() != null
				&& event.getNewValue() instanceof IFeature) {
				if ((Boolean) event.getOldValue()) {
					if (!treeViewer.getControl().isDisposed()) {
						treeViewer.refresh((IFeature) event.getNewValue());
					}
				}
			}
		} else if (event.getEventType() == EventType.FEATURE_ADD) {
			if (event.getSource() instanceof ExtendedFeatureModel) {
				ExtendedFeature feature = (ExtendedFeature) event.getNewValue();
				for (IFeatureAttribute att : ((ExtendedFeature) feature.getStructure().getParent().getFeature()).getAttributes()) {
					if (att.isRecursive()) {
						feature.addAttribute(att.cloneRecursive(feature));
					}
				}
				treeViewer.refresh();
			}
		} else if (event.getEventType() == EventType.STRUCTURE_CHANGED) {
			if (event.getSource() instanceof GraphicalFeature) {
				GraphicalFeature graphFeat = (GraphicalFeature) event.getSource();
				ExtendedFeature feat = (ExtendedFeature) graphFeat.getObject();
				for (IFeatureAttribute att : feat.getAttributes()) {
					if (att.isRecursive() && !((ExtendedFeature) feat.getStructure().getParent().getFeature()).isContainingAttribute(att)) {
						feat.removeAttribute(att);
					}
				}
				for (IFeatureAttribute att : ((ExtendedFeature) feat.getStructure().getParent().getFeature()).getAttributes()) {
					if (att.isRecursive()) {
						if (!feat.isContainingAttribute(att)) {
							feat.addAttribute(att.cloneRecursive(feat));
						}
					}
				}
				treeViewer.refresh();
			}
		} else if (event.getEventType() == EventType.FEATURE_COLOR_CHANGED) {
			treeViewer.refresh();
		} else if (event.getEventType() == EventType.FEATURE_SELECTION_CHANGED) {
			if (getMode() == FeatureAttributeOperationMode.CONFIGURATION_EDITOR) {
				treeViewer.refresh();
				treeViewer.expandAll();
				repackAllColumns();
			}
		}
	}

	@Override
	public void dispose() {
		setEditorContent(null);
		getSite().getPage().removePartListener(editorListener);
		FeatureColorManager.removeListener(this);
		// Dispose all cached images to prevent leaks
		for (Image image : cachedImages.values()) {
			image.dispose();
		}
		super.dispose();
	}

	/**
	 * Returns current editor of the view
	 * 
	 * @return current editor
	 */
	public IWorkbenchPart getCurrentEditor() {
		return currentEditor;
	}

	public AFileManager<?> getManager() {
		return manager;
	}
}
