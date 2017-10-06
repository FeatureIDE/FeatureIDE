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

import static de.ovgu.featureide.fm.core.localization.StringTable.MANAGE_ATTRIBUTE;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.window.*;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.*;
import org.eclipse.swt.layout.*;
import org.eclipse.swt.widgets.*;

import static de.ovgu.featureide.fm.core.localization.StringTable.CHOOSE_ACTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.COLORATION_DIALOG;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURES_;

import java.awt.Insets;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.net.URL;

import javax.annotation.PostConstruct;
import javax.swing.text.TableView;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.resource.LocalResourceManager;
import org.eclipse.jface.resource.ResourceManager;
import org.eclipse.jface.viewers.DelegatingStyledCellLabelProvider;
import org.eclipse.jface.viewers.DelegatingStyledCellLabelProvider.IStyledLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.StyledString;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;
import org.w3c.dom.Element;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FeatureAttributeInherited;
import de.ovgu.featureide.fm.core.base.impl.FeatureAttribute;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.ColumnViewerEditor;
import org.eclipse.jface.viewers.ColumnViewerEditorActivationEvent;
import org.eclipse.jface.viewers.ColumnViewerEditorActivationStrategy;
import org.eclipse.jface.viewers.EditingSupport;
import org.eclipse.jface.viewers.FocusCellOwnerDrawHighlighter;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.jface.viewers.TreeViewerEditor;
import org.eclipse.jface.viewers.TreeViewerFocusCellManager;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;

/**
 * A simple editor to change description of a particular feature diagram.
 *
 */
public class AddAttributeDialog extends Dialog  {
	
	private IFeatureModel featureModel;
	private static final Color WHITE = new Color(null, 255, 255, 255);
	private String[] columLabels = { "Feature", "Attributename", "Value", "Type", "Unit", "Configurable", "Recursive"};
	
	public AddAttributeDialog(final Shell parentShell, IFeatureModel featureModel) {
		super(parentShell);
		this.featureModel = featureModel;
	}
	
	/**
	 * Sets the minimal size and the text in the title of the dialog.
	 *
	 * @param newshell
	 */
	@Override
	protected void configureShell(Shell newShell) {
		newShell.setMinimumSize(new Point(500, 500));
		super.configureShell(newShell);
		newShell.setText(MANAGE_ATTRIBUTE);
	}

	@Override
	protected Point getInitialSize() {
		return new Point(1300, 1000);
	}
	
	/**
	 * Creates the general layout of the dialog.
	 *
	 * @param parent
	 */
	@Override
	protected Control createDialogArea(Composite parent) {
		final Composite container = (Composite) super.createDialogArea(parent);
		container.setBackground(new Color(parent.getDisplay(), 255, 255, 255));
		final GridLayout gridLayout = (GridLayout) container.getLayout();
		gridLayout.numColumns = 2;

		GridData gridData = new GridData();
		gridData.verticalAlignment = GridData.FILL_BOTH;
		gridData.horizontalAlignment = GridData.FILL;
		
		final TreeViewer viewer = new TreeViewer(container);
		viewer.getTree().setLayoutData(new GridData(GridData.FILL_BOTH));
		viewer.setContentProvider(new MyContentProvider());
//		viewer.setLabelProvider(new FileTreeLabelProvider());
		viewer.getTree().setHeaderVisible(true);
		viewer.getTree().setLinesVisible(true);
		
		
		for (int i = 0; i < columLabels.length; i++) {
			TreeViewerColumn column = new TreeViewerColumn(viewer, SWT.NONE);
			column.getColumn().setWidth(110);
			column.getColumn().setMoveable(true);
			column.getColumn().setText(columLabels[i]);
			column.setLabelProvider(createColumnLabelProvider());
		}
		

		final Label featureLabel = new Label(container, SWT.NONE);
		featureLabel.setLayoutData(gridData);
		featureLabel.setBackground(WHITE);
		featureLabel.setText(featureModel.getFeature("HelloWorld").getName());
		//System.out.println(featureModel.getFeature("HelloWorld").getName());
		//
		viewer.setInput(featureModel);

    	return parent;
	
	}
	
	private ColumnLabelProvider createColumnLabelProvider() {
		return new ColumnLabelProvider() {

			@Override
			public String getText(Object element) {
				return  element.toString();
			}

		};
	}
	
	private LinkedList<IFeature> getFeatureList(IFeatureModel featureModel){
		LinkedList<IFeature> featureList = new LinkedList<>();
		List<String> featureNameList = featureModel.getFeatureOrderList();
		for(int i = 0; i < featureNameList.size(); i++) {
			featureList.add(featureModel.getFeature(featureNameList.get(i)));
		}
		return featureList;
	}
	
	
	private class MyContentProvider implements ITreeContentProvider {
		
		@Override
		public Object[] getElements(Object inputElement) {
			IFeatureModel fm = (IFeatureModel) inputElement;
			ArrayList<IFeature> feature = new ArrayList();
			IFeature name = fm.getStructure().getRoot().getFeature();
			feature.add(name);
//			feature.add(fm.getFeature(name.get(3).toString()));
//			for(String name : fm.getFeatureOrderList()) {
//				feature.add(fm.getFeature(name));
//			}
		    if (fm.getNumberOfFeatures() == 0) {
		    	return new Object[0];
		    }       
		    return feature.toArray();
		}

		@Override
		public void dispose() {}

		@Override
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

		@Override
		public Object[] getChildren(Object parentElement) {
			if(hasChildren(parentElement)) {
				IFeature f = (IFeature) parentElement;
				ArrayList<IFeature> feature = new ArrayList();
				for(int i = 0; i < f.getStructure().getChildrenCount(); i++) {
					IFeature cf = f.getStructure().getChildren().get(i).getFeature();
					feature.add(cf);
				}
				return feature.toArray();
			}
			return null;
		}

		@Override
		public Object getParent(Object element) {
			if (element instanceof IFeature) {
				return ((IFeature) element).getStructure().getParent().getFeature();
		    }  
			    return null;
	    }

		@Override
		public boolean hasChildren(Object element) {
			if (element instanceof IFeature) {
		         IFeature f = (IFeature) element;
		         return f.getStructure().hasChildren();
		    }
		    return false;
		}
	}
		
}
	

//		class FileTreeLabelProvider implements ILabelProvider {
//		  private List listeners;
//
//		  private Image file;
//
//		  private Image dir;
//
//		  public FileTreeLabelProvider() {
//		    listeners = new ArrayList();
//
//		    try {
//		      file = new Image(null, new FileInputStream("images/file.gif"));
//		      dir = new Image(null, new FileInputStream("images/directory.gif"));
//		    } catch (FileNotFoundException e) {
//		    }
//		  }
//
//		  public Image getImage(Object arg0) {
//		    return ((File) arg0).isDirectory() ? dir : file;
//		  }
//
//		  public String getText(Object arg0) {
//		    String text = ((File) arg0).getName();
//
//		    if (((File) arg0).getName().length() == 0) {
//		      text = ((File) arg0).getPath();
//		    }
//		    return text;
//		  }
//
//		  public void addListener(ILabelProviderListener arg0) {
//		    listeners.add(arg0);
//		  }
//
//		  public void dispose() {
//		    // Dispose the images
//		    if (dir != null)
//		      dir.dispose();
//		    if (file != null)
//		      file.dispose();
//		  }
//
//		  public boolean isLabelProperty(Object arg0, String arg1) {
//		    return false;
//		  }
//
//		  public void removeListener(ILabelProviderListener arg0) {
//		    listeners.remove(arg0);
//		  }

	
	
//				Button b = new Button(shell, SWT.PUSH);
//				b.setText("Remove column");
//				final TreeViewer v = new TreeViewer(shell, SWT.BORDER | SWT.FULL_SELECTION);
//				v.getTree().setLinesVisible(true);
//				v.getTree().setHeaderVisible(true);
//				b.addSelectionListener(new SelectionListener() {
//		
//					@Override
//					public void widgetDefaultSelected(SelectionEvent e) {
//		
//					}
//		
//					@Override
//					public void widgetSelected(SelectionEvent e) {
//						v.getTree().getColumn(1).dispose();
//					}
//		
//				});
//		
//				TreeViewerFocusCellManager focusCellManager = new TreeViewerFocusCellManager(v, new FocusCellOwnerDrawHighlighter(v));
//				ColumnViewerEditorActivationStrategy actSupport = new ColumnViewerEditorActivationStrategy(v) {
//		
//					@Override
//					protected boolean isEditorActivationEvent(ColumnViewerEditorActivationEvent event) {
//						return event.eventType == ColumnViewerEditorActivationEvent.TRAVERSAL
//							|| event.eventType == ColumnViewerEditorActivationEvent.MOUSE_DOUBLE_CLICK_SELECTION
//							|| (event.eventType == ColumnViewerEditorActivationEvent.KEY_PRESSED && event.keyCode == SWT.CR)
//							|| event.eventType == ColumnViewerEditorActivationEvent.PROGRAMMATIC;
//					}
//				};
//		
//				int feature = ColumnViewerEditor.TABBING_HORIZONTAL | ColumnViewerEditor.TABBING_MOVE_TO_ROW_NEIGHBOR | ColumnViewerEditor.TABBING_VERTICAL
//					| ColumnViewerEditor.KEYBOARD_ACTIVATION;
//		
//				TreeViewerEditor.create(v, focusCellManager, actSupport, feature);
//				final TextCellEditor textCellEditor = new TextCellEditor(v.getTree());
//		
//				String[] columLabels = { "Feature", "Attributename", "Value", "Type", "Unit", "Configurable", "Recursive"};
//				String[] labelPrefix = { "", "", "","","","","" };
//
//				for (int i = 0; i < columLabels.length; i++) {
//					TreeViewerColumn column = new TreeViewerColumn(v, SWT.NONE);
//					column.getColumn().setWidth(200);
//					column.getColumn().setMoveable(true);
//					column.getColumn().setText(columLabels[i]);
//					column.setLabelProvider(createColumnLabelProvider(labelPrefix[i]));
//					column.setEditingSupport(createEditingSupportFor(v, textCellEditor));
//				}
//				v.setContentProvider(new MyContentProvider());
//				v.setInput();
//			}
//
//			private ColumnLabelProvider createColumnLabelProvider(final String prefix) {
//				return new ColumnLabelProvider() {
//		
//					@Override
//					public String getText(Object element) {
//						return prefix + element.toString();
//					}
//		
//				};
//			}
//		
//			private EditingSupport createEditingSupportFor(final TreeViewer viewer, final TextCellEditor textCellEditor) {
//				return new EditingSupport(viewer) {
//		
//					@Override
//					protected boolean canEdit(Object element) {
//						return false;
//					}
//		
//					@Override
//					protected CellEditor getCellEditor(Object element) {
//						return textCellEditor;
//					}
//		
//					@Override
//					protected Object getValue(Object element) {
//						return ((MyModel) element).counter + "";
//					}
//		
//					@Override
//					protected void setValue(Object element, Object value) {
//						((MyModel) element).counter = Integer.parseInt(value.toString());
//						viewer.update(element, null);
//					}
//				};
//			}
//		
//			private MyModel createModel() {
//				MyModel root = new MyModel(0, null);
//				root.counter = 0;
//		
//				MyModel tmp;
//				MyModel subItem;
//				for (int i = 1; i < 10; i++) {
//					tmp = new MyModel(i, root);
//					root.child.add(tmp);
//					for (int j = 1; j < i; j++) {
//						subItem = new MyModel(j, tmp);
//						subItem.child.add(new MyModel(j * 100, subItem));
//						tmp.child.add(subItem);
//					}
//				}
//				return root;
//			}
//		
//			
//		
//			private class MyContentProvider implements ITreeContentProvider {
//		
//				@Override
//				public Object[] getElements(Object inputElement) {
//					return ((MyModel) inputElement).child.toArray();
//				}
//		
//				@Override
//		 	public void dispose() {}
//		
//				@Override
//				public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
//		
//				@Override
//				public Object[] getChildren(Object parentElement) {
//					return getElements(parentElement);
//				}
//		
//				@Override
//				public Object getParent(Object element) {
//					if (element == null) {
//						return null;
//				}
//					return ((MyModel) element).parent;
//				}
//		
//				@Override
//				public boolean hasChildren(Object element) {
//					return ((MyModel) element).child.size() > 0;
//				}
//		
//			}
//		
//			
//		
//			public class MyModel {
//		
//				public MyModel parent;
//				public List<MyModel> child = new ArrayList<>();
//				public int counter;
//		
//				public MyModel(int counter, MyModel parent) {
//					this.parent = parent;
//					this.counter = counter;
//				}
//		
//				@Override
//				public String toString() {
//					String rv = "Item ";
//					if (parent != null) {
//						rv = parent.toString() + ".";
//					}
//					rv += counter;
//		
//					return rv;
//				}
//			}



