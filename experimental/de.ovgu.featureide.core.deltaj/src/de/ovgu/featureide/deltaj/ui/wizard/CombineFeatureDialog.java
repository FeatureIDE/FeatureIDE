/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.deltaj.ui.wizard;

import java.util.ArrayList;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * @author Andr� Specht
 * Adapted for FeatureIDE by Sven Schuster
 */
public class CombineFeatureDialog extends Dialog {
	String moduleName;
	public String getModuleName() {
		return moduleName;
	}

	public ArrayList<String> getFeatureList() {
		return featureList;
	}

	ArrayList<String> featureList;
	ListViewer listViewer;
	List list;
	
	
	private static class ViewerLabelProvider extends LabelProvider {
		public Image getImage(Object element) {
			return super.getImage(element);
		}
		public String getText(Object element) {
			Feature feature = (Feature)element;
			return feature.getName();
		}
	}
	private static class ContentProvider implements IStructuredContentProvider {
		public Object[] getElements(Object inputElement) {
			DeltaJFeatureMapper mapper = new DeltaJFeatureMapper((FeatureModel)inputElement);
			ArrayList<Feature> features = mapper.getOptionalEndFeatures();
			
			return features.toArray();		}
		public void dispose() {
		}
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		}
	}
	private Text text;
	private FeatureModel model;
	/**
	 * Create the dialog.
	 * @param parentShell
	 */
	public CombineFeatureDialog(Shell parentShell,FeatureModel model) {
		super(parentShell);
		this.setModel(model);
		this.featureList = new ArrayList<String>();
	}

	/**
	 * Create contents of the dialog.
	 * @param parent
	 */
	@Override
	protected Control createDialogArea(Composite parent) {
		Composite container = (Composite) super.createDialogArea(parent);
		container.setLayout(null);
	
		text = new Text(container, SWT.BORDER);

		text.setBounds(92, 3, 237, 21);
		
		Label lblEnterModuleName = new Label(container, SWT.NONE);
		lblEnterModuleName.setBounds(10, 9, 76, 15);
		lblEnterModuleName.setText("Enter name");
		
		Label lblSelectFeaturesTo = new Label(container, SWT.NONE);
		lblSelectFeaturesTo.setBounds(13, 42, 181, 15);
		lblSelectFeaturesTo.setText("Select features to combine");
		
		listViewer = new ListViewer(container, SWT.BORDER | SWT.V_SCROLL | SWT.MULTI);
		list = listViewer.getList();
		list.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
			}
		});
		list.setBounds(10, 63, 319, 145);
		listViewer.setLabelProvider(new ViewerLabelProvider());
		listViewer.setContentProvider(new ContentProvider());
	    listViewer.setInput(model);

		return container;
	}

	/**
	 * Create contents of the button bar.
	 * @param parent
	 */
	@Override
	protected void createButtonsForButtonBar(Composite parent) {
		createButton(parent, IDialogConstants.OK_ID, IDialogConstants.OK_LABEL,
				true);
		createButton(parent, IDialogConstants.CANCEL_ID,
				IDialogConstants.CANCEL_LABEL, false);
	}

	/**
	 * Return the initial size of the dialog.
	 */
	@Override
	protected Point getInitialSize() {
		return new Point(355, 300);
	}

	public FeatureModel getModel() {
		return model;
	}

	public void setModel(FeatureModel model) {
		this.model = model;
	}
	
	  @Override
	  protected void okPressed() {
		  if(this.text.getText().matches("^([0-9a-zA-Z])+$")){		
	    saveInput();
	    if(!this.moduleName.isEmpty()&&this.getFeatureList().size()>1)
	    	super.okPressed();
		  }
	  }

	private void saveInput() {
		moduleName = this.text.getText();
		this.featureList.clear();
		for (String clist : list.getSelection()) {
			this.featureList.add(clist);
		}
	}

}
