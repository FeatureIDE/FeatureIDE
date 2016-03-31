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

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.List;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * @author Andr� Specht
 * Adapted for FeatureIDE by Sven Schuster
 */
public class FeatureToDeltaPage extends WizardPage {
	private static class ViewerLabelProvider_2 extends LabelProvider {
		public Image getImage(Object element) {
			return null;
		}
		public String getText(Object element) {
			Feature feature = (Feature)element;
			if(feature.isMandatory())
				return feature.getName()+"(mandatory)";
			else
				return feature.getName();
		}
	}
	private static class ContentProvider_2 implements IStructuredContentProvider {
		public Object[] getElements(Object inputElement) {
			DeltaJFeatureMapper mapper = new DeltaJFeatureMapper((FeatureModel)inputElement);
			ArrayList<Feature> features = mapper.getMandatoryEndFeatures();
			
			return features.toArray();	
		}
		public void dispose() {
		}
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		}
	}
	private static class ViewerLabelProvider_3 extends LabelProvider {
		public Image getImage(Object element) {
			return super.getImage(element);
		}
		public String getText(Object element) {
			return ((DOptFeature)element).getDeltaModule();
		}
	}
	private static class ContentProvider_3 implements IStructuredContentProvider {
		public Object[] getElements(Object inputElement) {
			return new ArrayList<DOptFeature>().toArray();
		}
		public void dispose() {
		}
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		}
	}


	private static class ViewerLabelProvider_1 extends LabelProvider {
		public Image getImage(Object element) {
			return null;
		}
		public String getText(Object element) {
			return super.getText(element);
		}
	}
	private static class ContentProvider_1 implements IStructuredContentProvider {
		public Object[] getElements(Object inputElement) {
			DeltaJFeatureMapper mapper = new DeltaJFeatureMapper((FeatureModel)inputElement);
			ArrayList<Feature> features = mapper.getMandatoryEndFeatures();
			
			return features.toArray();		
			}
		public void dispose() {
		}
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		}
	}
	private static class ViewerLabelProvider extends LabelProvider {
		public Image getImage(Object element) {
			return null;
		}
		public String getText(Object element) {
			Feature feature = (Feature)element;
			if(feature.isMandatory())
				return feature.getName()+"(mandatory)";
			else
				return feature.getName();
		}
	}
	private static class ContentProvider implements IStructuredContentProvider {
		public Object[] getElements(Object inputElement) {
			DeltaJFeatureMapper mapper = new DeltaJFeatureMapper((FeatureModel)inputElement);
			ArrayList<Feature> features = mapper.getOptionalEndFeatures();
			
			return features.toArray();
		}
		public void dispose() {
		}
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		}
	}

	private List featurelist;
	private List deltalist;
	private ListViewer featureViewer;
	private ListViewer deltaViewer;
	private ListViewer listViewerComb;
	private ListViewer mandViewer;
	FeatureModel model;
	DeltaJNewProjectWizardExtension extension;
	/**
	 * Create the wizard.
	 */
	public FeatureToDeltaPage(FeatureModel model, DeltaJNewProjectWizardExtension extension) {
		super("featureToDeltaPage");
		this.extension = extension;
		setTitle("Features to Delta Modules");
		setDescription("Select features from the model, for which delta modules shall be created.");
		this.model=model;
	}

	/**
	 * Create contents of the wizard.
	 * @param parent
	 */
	public void createControl(final Composite parent) {
		Composite container = new Composite(parent, SWT.NULL);

		setControl(container);
		container.setLayout(new FillLayout(SWT.VERTICAL));
		
		Composite composite_3 = new Composite(container, SWT.NONE);
		composite_3.setLayout(new FillLayout(SWT.HORIZONTAL));
		
		Group grpFeatures = new Group(composite_3, SWT.NONE);
		grpFeatures.setText("Optional Features");
		grpFeatures.setLayout(new FillLayout(SWT.VERTICAL));
		
		featureViewer = new ListViewer(grpFeatures, SWT.BORDER | SWT.V_SCROLL | SWT.MULTI);
		featurelist = featureViewer.getList();
		featureViewer.setLabelProvider(new ViewerLabelProvider());
		featureViewer.setContentProvider(new ContentProvider());
		
		Composite composite_1 = new Composite(composite_3, SWT.NONE);
		composite_1.setLayout(new FillLayout(SWT.VERTICAL));
		
		Button btnAddAll = new Button(composite_1, SWT.NONE);
		btnAddAll.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				String[] selection = featureViewer.getList().getItems();
				for (String element : selection) {
					featurelist.remove(element);
					deltalist.add(element);
				}
				updateOptional();
			}
		});
		btnAddAll.setText("Add All-->");
		
		Button btnNewButton = new Button(composite_1, SWT.NONE);
		btnNewButton.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				String[] selection = featureViewer.getList().getSelection();
				for (String element : selection) {
					featurelist.remove(element);
					deltalist.add(element);
					
				}
				updateOptional();
			}
		});
		btnNewButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
			}
		});
		btnNewButton.setText("Add-->");
		
		Button button = new Button(composite_1, SWT.NONE);
		button.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				String[] selection = deltaViewer.getList().getSelection();
				for (String element : selection) {
					deltalist.remove(element);
					featurelist.add(element);
				}
				updateOptional();
			}
		});
		button.setText("<--Remove");
		
		Button btnRemoveAll = new Button(composite_1, SWT.NONE);
		btnRemoveAll.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				String[] selection = deltaViewer.getList().getItems();
				for (String element : selection) {
					deltalist.remove(element);
					featurelist.add(element);
				}
				updateOptional();
			}
		});
		btnRemoveAll.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
			}
		});
		btnRemoveAll.setText("<--Remove All");
		
		Group grpdeltas = new Group(composite_3, SWT.NONE);
		grpdeltas.setText("Delta Modules");
		grpdeltas.setLayout(new FillLayout(SWT.VERTICAL));
		
		
		deltaViewer = new ListViewer(grpdeltas, SWT.BORDER | SWT.V_SCROLL | SWT.MULTI);
		deltalist = deltaViewer.getList();
		deltaViewer.setLabelProvider(new ViewerLabelProvider_1());
		deltaViewer.setContentProvider(new ContentProvider_1());
		
		Composite composite = new Composite(container, SWT.NONE);
		composite.setLayout(new FillLayout(SWT.HORIZONTAL));
		
		Group grpMandatoryFeatures = new Group(composite, SWT.NONE);
		grpMandatoryFeatures.setEnabled(false);
		grpMandatoryFeatures.setText("Mandatory Features");
		grpMandatoryFeatures.setLayout(new FillLayout(SWT.HORIZONTAL));
		
		mandViewer = new ListViewer(grpMandatoryFeatures, SWT.BORDER | SWT.V_SCROLL);
		List list = mandViewer.getList();
		list.setBackground(Display.getCurrent().getSystemColor(SWT.COLOR_GRAY));
		list.setEnabled(true);
		
		Composite composite_2 = new Composite(composite, SWT.NONE);
		FillLayout fl_composite_2 = new FillLayout(SWT.VERTICAL);
		fl_composite_2.marginHeight = 40;
		composite_2.setLayout(fl_composite_2);
		
		Button btnCombination = new Button(composite_2, SWT.NONE);
		btnCombination.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				CombineFeatureDialog dialog = new CombineFeatureDialog(parent.getShell(),extension.getModel());
				if(dialog.open()== Window.OK){
					DOptFeature combFeature = new DOptFeature(dialog.getModuleName(), dialog.getFeatureList());
					listViewerComb.add(combFeature);
					updateOptional();
				}
			}
		});
		btnCombination.setText("Combine");
		
		Button btnRemove = new Button(composite_2, SWT.NONE);
		btnRemove.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
			}
		});
		btnRemove.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				for (String element : listViewerComb.getList().getSelection()) {
					listViewerComb.getList().remove(element);
				}
				updateOptional();
			}
		});
		btnRemove.setText("Remove Combined");
		
		Group grpCombinedOptional = new Group(composite, SWT.NONE);
		grpCombinedOptional.setText("Combined Optional");
		grpCombinedOptional.setLayout(new FillLayout(SWT.VERTICAL));
		
		listViewerComb = new ListViewer(grpCombinedOptional, SWT.BORDER | SWT.V_SCROLL);
		listViewerComb.setLabelProvider(new ViewerLabelProvider_3());
		listViewerComb.setContentProvider(new ContentProvider_3());
		mandViewer.setContentProvider(new ContentProvider_2());
		mandViewer.setLabelProvider(new ViewerLabelProvider_2());
	}
	
	public void updateOptional(){
		String[] items = deltalist.getItems();
		this.extension.getSelectedOptionalFeatures().clear();
		this.extension.getCombinedOptionalFeatures().clear();
		for (String string : items) {
			Feature feature = this.extension.getModel().getFeature(string);
			this.extension.getSelectedOptionalFeatures().add(feature);
		}
		
		ArrayList<DOptFeature> flist = new ArrayList<DOptFeature>();
		
		for (int i = 0; i < listViewerComb.getList().getItemCount(); i++) {
			DOptFeature dfeat = ((DOptFeature)listViewerComb.getElementAt(i));
			if(!dfeat.getDeltaModule().isEmpty())	
				flist.add(dfeat);
		}

		this.extension.setCombinedOptionalFeatures(flist);

	
	}
    @Override
    public void setVisible(boolean visible) {
        super.setVisible(visible);
        if (visible) {
        	this.extension.setSelectedOptionalFeatures(new ArrayList<Feature>());
        	this.extension.setCombinedOptionalFeatures(new ArrayList<DOptFeature>());
        	
        	featureViewer.setInput(this.extension.getModel());
        	mandViewer.setInput(this.extension.getModel());
        	deltalist.removeAll();
        	listViewerComb.getList().removeAll();
        }
    }
}
