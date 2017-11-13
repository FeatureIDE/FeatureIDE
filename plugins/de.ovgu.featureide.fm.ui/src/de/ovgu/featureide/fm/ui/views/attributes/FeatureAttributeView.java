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
package de.ovgu.featureide.fm.ui.views.attributes;

import java.util.HashMap;

import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.core.attributes.IFeatureAttribute;
import de.ovgu.featureide.fm.core.attributes.impl.FeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;
import de.ovgu.featureide.fm.ui.views.attributes.actions.AddFeatureAttributeAction;
import de.ovgu.featureide.fm.ui.views.attributes.actions.RemoveFeatureAttributeAction;
import de.ovgu.featureide.fm.ui.views.attributes.editingsupport.FeatureAttributeNameEditingSupport;

/**
 * TODO ATTRIBUTE description
 *
 * @author Joshua Sprey
 */
public class FeatureAttributeView extends ViewPart implements IEventListener {

	public FeatureAttributeView() {
		super();

		cachedImages = new HashMap<String, Image>();
		cachedImages.put(imgFeature, FMUIPlugin.getImage(imgFeature));
		cachedImages.put(imgAttribute, FMUIPlugin.getImage(imgAttribute));
	}

	private final static String imgFeature = "FeatureIconSmall.ico";
	private final static String imgAttribute = "message_warning.gif";
	private final HashMap<String, Image> cachedImages;

	private Tree tree;
	private TreeViewer treeViewer;
	private GridLayout layout;
	private Menu menu;
	private final String COLUMN_ELEMENT = "Element";
	private final String COLUMN_TYPE = "Type";
	private final String COLUMN_VALUE = "Value";
	private final String COLUMN_UNIT = "Unit";
	private final String COLUMN_RECURSIVE = "Recursive";
	private final String COLUMN_CONFIGUREABLE = "Configureable";

	private IWorkbenchPart currentEditor;
	private IFeatureModel featureModel;

	// EditingSupports
	private FeatureAttributeNameEditingSupport nameEditingSupport;

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
				// Close if current editor is closed
				setEditorContent(null);
			}
		}

		@Override
		public void partBroughtToTop(IWorkbenchPart part) {
			if (getSite().getPart() != part) {
				setEditorContent(part);
			}
		}

		@Override
		public void partActivated(IWorkbenchPart part) {
			if (getSite().getPart() != part) {
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
		treeViewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL | SWT.FULL_SELECTION | SWT.BORDER);

		// create edit supports (inline editors)
		createEditSupports();
		// create the columns
		createColumns();

		// make lines and header visible and set layout
		tree = treeViewer.getTree();
		tree.setHeaderVisible(true);
		tree.setLinesVisible(true);
		final GridData gridData = new GridData();
		gridData.horizontalAlignment = GridData.FILL;
		gridData.minimumHeight = 500;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		tree.setLayoutData(gridData);

		treeViewer.setContentProvider(new FeatureAttributeContentProvider());

		if (!treeViewer.getControl().isDisposed()) {
			setEditorContent(null);
		}

		parent.pack();
		tree.pack();

		createContexMenu();

		tree.addListener(SWT.MouseDown, new Listener() {

			@Override
			public void handleEvent(Event event) {
				nameEditingSupport.enabled = false;
			}

		});

		tree.addListener(SWT.MouseDoubleClick, new Listener() {

			@Override
			public void handleEvent(Event event) {
				nameEditingSupport.enabled = true;
				final TreeItem[] selection = tree.getSelection();

				if (selection.length != 1) {
					return;
				}

				final TreeItem item = tree.getSelection()[0];

				for (int i = 0; i < tree.getColumnCount(); i++) {
					if (item.getBounds(i).contains(event.x, event.y)) {
						treeViewer.editElement(treeViewer.getStructuredSelection().getFirstElement(), i);
						nameEditingSupport.enabled = false;
						break;
					}
				}
			}

		});
	}

	private void createEditSupports() {

		nameEditingSupport = new FeatureAttributeNameEditingSupport(treeViewer, false);

	}

	private void createContexMenu() {
		final MenuManager mgr = new MenuManager();
		mgr.setRemoveAllWhenShown(true);
		mgr.addMenuListener(new IMenuListener() {

			@Override
			public void menuAboutToShow(IMenuManager manager) {
				final IStructuredSelection selection = treeViewer.getStructuredSelection();
				if (!selection.isEmpty()) {
					if ((selection.size() == 1) && (selection.getFirstElement() instanceof IFeature)) {
						final IFeature feature = (IFeature) selection.getFirstElement();
						// Add actions to create new attributes
						mgr.add(new AddFeatureAttributeAction(featureModel, feature, FeatureAttribute.STRING, StringTable.ADD_STRING_ATTRIBUTE));
						mgr.add(new AddFeatureAttributeAction(featureModel, feature, FeatureAttribute.BOOLEAN, StringTable.ADD_BOOLEAN_ATTRIBUTE));
						mgr.add(new AddFeatureAttributeAction(featureModel, feature, FeatureAttribute.LONG, StringTable.ADD_LONG_ATTRIBUTE));
						mgr.add(new AddFeatureAttributeAction(featureModel, feature, FeatureAttribute.DOUBLE, StringTable.ADD_DOUBLE_ATTRIBUTE));
					} else {
						final HashMap<IFeatureAttribute, IFeature> attributes = new HashMap<>();
						// Check if all selected items are IFeatureAttributes
						for (final Object object : selection.toList()) {
							if (!(object instanceof IFeatureAttribute)) {
								return;
							} else {
								final IFeatureAttribute attribute = (IFeatureAttribute) object;
								for (final IFeature feature : featureModel.getFeatures()) {
									if (feature.getProperty().getAttributes().contains(attribute)) {
										attributes.put((IFeatureAttribute) object, feature);
									}
								}
							}
						}
						mgr.add(new RemoveFeatureAttributeAction(featureModel, attributes));
					}
				}
			}
		});
		treeViewer.getControl().setMenu(mgr.createContextMenu(treeViewer.getControl()));
	}

	private void createColumns() {
		// Feature
		final TreeViewerColumn colFeature = new TreeViewerColumn(treeViewer, SWT.NONE);
		colFeature.getColumn().setWidth(200);
		colFeature.getColumn().setText(COLUMN_ELEMENT);
		colFeature.setEditingSupport(nameEditingSupport);
		colFeature.setLabelProvider(new ColumnLabelProvider() {
			@Override
			public String getText(Object element) {
				if ((element instanceof IFeature) || (element instanceof String)) {
					return element.toString();
				} else if (element instanceof IFeatureAttribute) {
					final IFeatureAttribute attribute = (IFeatureAttribute) element;
					return attribute.getName();
				}
				return "null";
			}

			@Override
			public Image getImage(Object element) {
				if ((element instanceof IFeature) || (element instanceof String)) {
					return cachedImages.get(imgFeature);
				} else if (element instanceof IFeatureAttribute) {
					return cachedImages.get(imgAttribute);
				}
				return null;
			}
		});

		// Type
		final TreeViewerColumn colType = new TreeViewerColumn(treeViewer, SWT.NONE);
		colType.getColumn().setWidth(200);
		colType.getColumn().setText(COLUMN_TYPE);
		colType.setLabelProvider(new ColumnLabelProvider() {
			@Override
			public String getText(Object element) {
				if ((element instanceof IFeature) || (element instanceof String)) {
					return "-";
				} else if (element instanceof IFeatureAttribute) {
					final IFeatureAttribute attribute = (IFeatureAttribute) element;
					return attribute.getType();
				}
				return "null";
			}
		});

		// Value
		final TreeViewerColumn colValue = new TreeViewerColumn(treeViewer, SWT.NONE);
		colValue.getColumn().setWidth(200);
		colValue.getColumn().setText(COLUMN_VALUE);
		colValue.setLabelProvider(new ColumnLabelProvider() {
			@Override
			public String getText(Object element) {
				if ((element instanceof IFeature) || (element instanceof String)) {
					return "-";
				} else if (element instanceof IFeatureAttribute) {
					final IFeatureAttribute attribute = (IFeatureAttribute) element;
					return attribute.getValue().toString();
				}
				return "null";
			}
		});

		// Unit
		final TreeViewerColumn colUnit = new TreeViewerColumn(treeViewer, SWT.NONE);
		colUnit.getColumn().setWidth(200);
		colUnit.getColumn().setText(COLUMN_UNIT);
		colUnit.setLabelProvider(new ColumnLabelProvider() {
			@Override
			public String getText(Object element) {
				if ((element instanceof IFeature) || (element instanceof String)) {
					return "-";
				} else if (element instanceof IFeatureAttribute) {
					final IFeatureAttribute attribute = (IFeatureAttribute) element;
					return attribute.getUnit();
				}
				return "null";
			}
		});

		// Recursive
		final TreeViewerColumn colRecursive = new TreeViewerColumn(treeViewer, SWT.NONE);
		colRecursive.getColumn().setWidth(200);
		colRecursive.getColumn().setText(COLUMN_RECURSIVE);
		colRecursive.setLabelProvider(new ColumnLabelProvider() {
			@Override
			public String getText(Object element) {
				if ((element instanceof IFeature) || (element instanceof String)) {
					return "-";
				} else if (element instanceof IFeatureAttribute) {
					final IFeatureAttribute attribute = (IFeatureAttribute) element;
					return attribute.isRecursive() ? "true" : "false";
				}
				return "null";
			}
		});

		// Configureable
		final TreeViewerColumn colConfigureable = new TreeViewerColumn(treeViewer, SWT.NONE);
		colConfigureable.getColumn().setWidth(200);
		colConfigureable.getColumn().setText(COLUMN_CONFIGUREABLE);
		colConfigureable.setLabelProvider(new ColumnLabelProvider() {
			@Override
			public String getText(Object element) {
				if ((element instanceof IFeature) || (element instanceof String)) {
					return "-";
				} else if (element instanceof IFeatureAttribute) {
					final IFeatureAttribute attribute = (IFeatureAttribute) element;
					return attribute.isConfigurable() ? "true" : "false";
				}
				return "null";
			}
		});
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	@Override
	public void setFocus() {
		treeViewer.getControl().setFocus();
	}

	private void setEditorContent(IWorkbenchPart activeWorkbenchPart) {
		if (activeWorkbenchPart == null) {
			setFeatureModel(null);
			if (!treeViewer.getControl().isDisposed()) {
				treeViewer.setInput(FeatureAttributeContentProvider.EMPTY_ROOT);
			}
			if (currentEditor instanceof FeatureModelEditor) {
				final FeatureModelEditor editor = (FeatureModelEditor) currentEditor;
				editor.removeEventListener(this);
			}
			currentEditor = null;
			return;
		}
		if ((activeWorkbenchPart instanceof FeatureModelEditor) && (currentEditor != activeWorkbenchPart)) {
			currentEditor = activeWorkbenchPart;
			final FeatureModelEditor editor = (FeatureModelEditor) activeWorkbenchPart;
			editor.addEventListener(this);
			setFeatureModel(editor.getFeatureModel());
			if (!treeViewer.getControl().isDisposed()) {
				treeViewer.setInput(featureModel);
			}
			treeViewer.expandAll();
		} else if ((activeWorkbenchPart instanceof ConfigurationEditor) && (currentEditor != activeWorkbenchPart)) {
			currentEditor = activeWorkbenchPart;
			final ConfigurationEditor editor = (ConfigurationEditor) activeWorkbenchPart;
			setFeatureModel(editor.getConfiguration().getFeatureModel());
			if (!treeViewer.getControl().isDisposed()) {
				treeViewer.setInput(featureModel);
			}
			treeViewer.expandAll();
		}
	}

	/**
	 * Returns the current feature model when an valid view was opened before. Otherwise the feature model is null.
	 *
	 * @return
	 */
	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	private void setFeatureModel(IFeatureModel featureModel) {
		if (this.featureModel != null) {
			this.featureModel.removeListener(this);
		}
		if (featureModel == null) {
			this.featureModel = null;
			return;
		}

		this.featureModel = featureModel;
		this.featureModel.addListener(this);
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.base.event.IEventListener#propertyChange(de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent)
	 */
	@Override
	public void propertyChange(FeatureIDEEvent event) {
		if (event.getEventType() == EventType.MODEL_DATA_SAVED) {
			if (!treeViewer.getControl().isDisposed()) {
				treeViewer.refresh(featureModel); // TODO ATTRIBUTE hmm mal schauen, komische widget dispose meldung
			}
		} else if (event.getEventType() == EventType.FEATURE_ATTRIBUTE_CHANGED) {
			if (event.getSource() instanceof IFeature) {
				if (!treeViewer.getControl().isDisposed()) {
					treeViewer.refresh((IFeature) event.getSource()); // TODO ATTRIBUTE hmm mal schauen, komische widget dispose meldung
				}
				treeViewer.expandAll();
			}
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#dispose()
	 */
	@Override
	public void dispose() {
		setFeatureModel(null);
		if (currentEditor instanceof FeatureModelEditor) {
			final FeatureModelEditor editor = (FeatureModelEditor) currentEditor;
			editor.removeEventListener(this);
		}
		currentEditor = null;
		super.dispose();
	}

}
