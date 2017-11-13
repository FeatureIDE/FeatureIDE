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

import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.core.attributes.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;

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

	private Tree table;
	private TreeViewer tableViewer;
	private GridLayout layout;
	private final String COLUMN_FEATURE = "Feature";
	private final String COLUMN_TYPE = "Type";
	private final String COLUMN_VALUE = "Value";
	private final String COLUMN_UNIT = "Unit";
	private final String COLUMN_RECURSIVE = "Recursive";
	private final String COLUMN_CONFIGUREABLE = "Configureable";

	private IWorkbenchPart currentEditor;
	private IFeatureModel featureModel;

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

	IResourceChangeListener resourceChangeListener = new IResourceChangeListener() {

		@Override
		public void resourceChanged(IResourceChangeEvent event) {

		}

	};

	private final static String imgFeature = "FeatureIconSmall.ico";
	private final static String imgAttribute = "message_warning.gif";
	private final HashMap<String, Image> cachedImages;

	@Override
	public void init(IViewSite site) throws PartInitException {
		super.init(site);
	}

	@Override
	public void createPartControl(Composite parent) {
		// Add part listener and resource listener
		getSite().getPage().addPartListener(editorListener);
		ResourcesPlugin.getWorkspace().addResourceChangeListener(resourceChangeListener);

		// Create Layout
		layout = new GridLayout(2, false);
		parent.setLayout(layout);

		// define the TableViewer
		tableViewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL | SWT.FULL_SELECTION | SWT.BORDER);

		// create the columns
		createColumns();

		// make lines and header visible and set layout
		table = tableViewer.getTree();
		table.setHeaderVisible(true);
		table.setLinesVisible(true);
		final GridData gridData = new GridData();
		gridData.horizontalAlignment = GridData.FILL;
		gridData.minimumHeight = 500;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		table.setLayoutData(gridData);

		tableViewer.setContentProvider(new FeatureAttributeContentProvider());
	}

	private void createColumns() {
		// Feature
		final TreeViewerColumn colFeature = new TreeViewerColumn(tableViewer, SWT.NONE);
		colFeature.getColumn().setWidth(200);
		colFeature.getColumn().setText(COLUMN_FEATURE);
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
		final TreeViewerColumn colType = new TreeViewerColumn(tableViewer, SWT.NONE);
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
		final TreeViewerColumn colValue = new TreeViewerColumn(tableViewer, SWT.NONE);
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
		final TreeViewerColumn colUnit = new TreeViewerColumn(tableViewer, SWT.NONE);
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
		final TreeViewerColumn colRecursive = new TreeViewerColumn(tableViewer, SWT.NONE);
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
		final TreeViewerColumn colConfigureable = new TreeViewerColumn(tableViewer, SWT.NONE);
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
		tableViewer.getControl().setFocus();
	}

	private void setEditorContent(IWorkbenchPart activeWorkbenchPart) {
		if (activeWorkbenchPart == null) {
			setFeatureModel(null);
			tableViewer.setInput(FeatureAttributeContentProvider.EMPTY_ROOT);
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
			tableViewer.setInput(featureModel);
			tableViewer.expandAll();
		} else if ((activeWorkbenchPart instanceof ConfigurationEditor) && (currentEditor != activeWorkbenchPart)) {
			currentEditor = activeWorkbenchPart;
			final ConfigurationEditor editor = (ConfigurationEditor) activeWorkbenchPart;
			setFeatureModel(editor.getConfiguration().getFeatureModel());
			tableViewer.setInput(featureModel);
			tableViewer.expandAll();
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
		if (this.featureModel != null) {}
		if (featureModel == null) {
			this.featureModel = null;
			return;
		}
		this.featureModel = featureModel;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.base.event.IEventListener#propertyChange(de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent)
	 */
	@Override
	public void propertyChange(FeatureIDEEvent event) {
		FMUIPlugin.getDefault().logInfo("" + event.getEventType());
		if (event.getEventType() == EventType.MODEL_DATA_SAVED) {

		}
	}

}
