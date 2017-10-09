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
import org.eclipse.jface.viewers.SelectionChangedEvent;
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
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
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
		
		Tree featureAttributeTree= new Tree(container, SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL);
		final TreeViewer viewer = new TreeViewer(featureAttributeTree);
		viewer.getTree().setLayoutData(new GridData(GridData.FILL_BOTH));
		viewer.setContentProvider(new MyContentProvider());
		viewer.setLabelProvider(new TableLabelProvider());
		viewer.getTree().setHeaderVisible(true);
		viewer.getTree().setLinesVisible(true);
		
		
		for (int i = 0; i < columLabels.length; i++) {
			TreeColumn column = new TreeColumn(featureAttributeTree, SWT.NONE);
			column.setWidth(150);
			column.setMoveable(true);
			column.setText(columLabels[i]);
		}
		Button bAdd = new Button(container, SWT.PUSH);
		bAdd.setText("Add Attribute");
		bAdd.addSelectionListener(new SelectionAdapter() {
	       	
	        // Add a task to the ExampleTaskList and refresh the view
		    public void widgetSelected(SelectionEvent e) {
	            FeatureAttribute.addTask();
	        }
	    });

		Button bRemove = new Button(container, SWT.PUSH);
		bRemove.setText("Remove Attribute");
		
		viewer.setInput(featureModel);
		
		viewer.addSelectionChangedListener(new ISelectionChangedListener() {
			  @Override
			  public void selectionChanged(SelectionChangedEvent event) {
			    IStructuredSelection selection = viewer.getStructuredSelection();
			    Object firstElement = selection.getFirstElement();
			    // do something with it
			  }
			});
    	return parent;
	
	}
	
		
	private class MyContentProvider implements ITreeContentProvider, IStructuredContentProvider {
		
		@Override
		public Object[] getElements(Object inputElement) {
			IFeatureModel fm = (IFeatureModel) inputElement;
			ArrayList<IFeature> feature = new ArrayList();
			IFeature name = fm.getStructure().getRoot().getFeature();
			feature.add(name);
		    if (fm.getNumberOfFeatures() == 0) {
		    	return new Object[0];
		    }       
		    return feature.toArray();
		}

		public void addTask(Object task) {
            viewer.add(task);
        }
		
		@Override
		public void dispose() {}

		@Override
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

		@Override
		public Object[] getChildren(Object parentElement) {
			ArrayList<Object> feature = new ArrayList();
			LinkedList<FeatureAttribute> attList = new LinkedList<>();
			LinkedList<FeatureAttributeInherited> attListInh = new LinkedList<>();
			if(parentElement instanceof IFeature) {
				IFeature f = (IFeature) parentElement;
				attList = f.getStructure().getAttributeList();
				attListInh = f.getStructure().getAttributeListInherited();
				for(FeatureAttribute attribute : attList) {
					feature.add(attribute);
					
				}
				for(FeatureAttributeInherited attributeInh : attListInh) {
					if(!isInList(attList, attributeInh.getParent())) {
						feature.add(attributeInh);
					}
				}
				for(int i = 0; i < f.getStructure().getChildrenCount(); i++) {
					IFeature cf = f.getStructure().getChildren().get(i).getFeature();
					feature.add(cf);
				}
			}
				return feature.toArray();
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
		         if(f.getStructure().hasChildren()) {
		        	 return true;
		         } else if (f.getStructure().getAttributeList() != null || f.getStructure().getAttributeListInherited() != null) {
		        	 return true;
		         }
		    }
		    return false;
		}
		
		private boolean isInList(LinkedList<FeatureAttribute> attList, FeatureAttribute inhAtt) {
			for(FeatureAttribute attribute : attList) {
				if (attribute.equals(inhAtt)) {
					return true;
				}						
		}
			return false;
		}
	}
		

	

		class TableLabelProvider implements ITableLabelProvider {

		@Override
		public Image getColumnImage(Object element, int columnIndex) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String getColumnText(Object element, int columnIndex) { 
			switch(columnIndex) {
		    	  case 0:
		    		  if (element instanceof IFeature) {
		    			  return ((IFeature) element).getName();
		    		  }
		    		  if (element instanceof FeatureAttribute) {
		    			  return "Attribute";
		    		  }
		    		  if (element instanceof FeatureAttributeInherited) {
		    			  return "Inherited attribute";
		    		  }
		    	  case 1:
		    		  if (element instanceof FeatureAttribute) {
		    			  return ((FeatureAttribute) element).getName();
		    		  }
		    		  if (element instanceof FeatureAttributeInherited) {
		    			  return ((FeatureAttributeInherited) element).getName();
		    		  }		    		  
		    	  case 2:
		    		  if (element instanceof FeatureAttribute) {
		    			  return ((FeatureAttribute) element).getValue();
		    		  }
		    		  if (element instanceof FeatureAttributeInherited) {
		    			  return ((FeatureAttributeInherited) element).getValue();
		    		  }
		      		  
		    	  case 3:
		    		  if (element instanceof FeatureAttribute) {
		    			  return ((FeatureAttribute) element).getTypeString();
		    		  }
		    		  if (element instanceof FeatureAttributeInherited) {
		    			  return ((FeatureAttributeInherited) element).getParent().getTypeString();
		    		  }
		    		  
		    	  case 4:
		    		  if (element instanceof FeatureAttribute) {
		    			  return ((FeatureAttribute) element).getUnit();
		    		  }
		    		  if (element instanceof FeatureAttributeInherited) {
		    			  return ((FeatureAttributeInherited) element).getParent().getUnit();
		    		  }
		    		 
		    	  case 5:
		    		  if (element instanceof FeatureAttribute) {
		    			  return String.valueOf(((FeatureAttribute) element).getConfigurable()); 
		    		  }
		    		  if (element instanceof FeatureAttributeInherited) {
		    			  return String.valueOf(((FeatureAttributeInherited) element).getParent().getConfigurable());
		    		  }
		    		  
		    	  case 6:
		    		  if (element instanceof FeatureAttribute) {
		    			  return String.valueOf(((FeatureAttribute) element).getRecursive());
		    		  }
		    		  if (element instanceof FeatureAttributeInherited) {
		    			  return String.valueOf(((FeatureAttributeInherited) element).getParent().getRecursive());
		    		  }
		    	  }
		      return null; 
		}

		@Override
		public void addListener(ILabelProviderListener listener) {
			// TODO Auto-generated method stub
			
		}

		@Override
		public void dispose() {
			// TODO Auto-generated method stub
			
		}

		@Override
		public boolean isLabelProperty(Object element, String property) {
			// TODO Auto-generated method stub
			return false;
		}

		public void removeListener(ILabelProviderListener listener) {
			// TODO Auto-generated method stub
			
		}
		}
}
//		private EditingSupport createEditingSupportFor(final TreeViewer viewer, final TextCellEditor textCellEditor) {
//			return new EditingSupport(viewer) {
//	
//				@Override
//				protected boolean canEdit(Object element) {
//					return false;
//				}
//	
//				@Override
//				protected CellEditor getCellEditor(Object element) {
//					return textCellEditor;
//				}
//	
//				@Override
//				protected Object getValue(Object element) {
//					return ((Object) element).counter + "";
//				}
//	
//				@Override
//				protected void setValue(Object element, Object value) {
//					((MyModel) element).counter = Integer.parseInt(value.toString());
//					viewer.update(element, null);
//				}
//			};
//		}
//		}
	
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



