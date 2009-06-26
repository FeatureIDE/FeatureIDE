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
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Collection;
import java.util.Scanner;

import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.SWT;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Label;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.core.PropertyConstants;
import featureide.fm.core.configuration.ConfigurationWriter;

/**
 * New editor page for the feature model editor. In this editor you can change the 
 * order of features
 * 
 * @author Christian Becker
 */
public class FeatureOrderEditor extends EditorPart implements PropertyConstants, PropertyChangeListener {

	public static final String ID = "featureide.fm.ui.editors.FeatureOrderEditor"; 
	
	private List featurelist = null;
	
	private Button up = null;
	
	private Button down = null;

	private Button save = null;
	
	private Button activate = null;
	
	private IEditorInput input;  
	
	private IEditorSite site;  
	
	private Writer fw;
	
	//private boolean dirty=false;
	
	//private FeatureModel featureModel;
	
	//private Configuration configuration; 
	
	public FeatureOrderEditor(FeatureModel featureModel){
		//this.featureModel = featureModel;
		//configuration = new Configuration(featureModel, true);
	//	featureModel.addListener(this);
	}
	
	
	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.IProgressMonitor)
	 */
	@Override
	public void doSave(IProgressMonitor monitor) {
	

	}
	
	public  IEditorSite getSite(){
		return site;
		
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.EditorPart#doSaveAs()
	 */
	@Override
	public void doSaveAs() {
	

	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.EditorPart#init(org.eclipse.ui.IEditorSite, org.eclipse.ui.IEditorInput)
	 */
	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		this.input =input;
		this.site = site;
		

	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.EditorPart#isDirty()
	 */
	@Override
	public boolean isDirty() {
		return false;
		//return isDirty;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.EditorPart#isSaveAsAllowed()
	 */
	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	public void setListItems(Collection<Feature> features){
	    featurelist.removeAll();
	    
		for(Feature ft: features){
	       	if (ft.isLayer())
			featurelist.add(ft.getName());
		}
		//featureOrderrReader();
	    
	}
	
	
	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
		GridData gridData;
		GridLayout layout = new GridLayout();
		layout.numColumns = 3;
		Composite comp = new Composite(parent,SWT.NONE);
		comp.setLayout(layout);
		
		Label label1 = new Label(comp,SWT.NONE);
		label1.setText("Userdefine feature order");
		
							
		activate=new Button (comp,SWT.CHECK);
		activate.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				ConfigurationWriter.userdefineorder=activate.getSelection();
			
			}});
		
		featurelist = new List(comp, SWT.NONE);
		gridData = new GridData(GridData.FILL_BOTH);
		gridData.horizontalSpan=2;
		gridData.verticalSpan=8;
		featurelist.setLayoutData(gridData);
		
		gridData = new GridData(GridData.GRAB_HORIZONTAL);
		gridData.widthHint=70;
		up = new Button(comp, SWT.NONE);
		up.setText("Up");
		up.setLayoutData(gridData);	
		up.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				int focus = featurelist.getFocusIndex();
				if(focus != 0){ //First Element is selected, no change
					String temp = featurelist.getItem(focus-1);			
					featurelist.setItem(focus-1, featurelist.getItem(focus));
					featurelist.setItem(focus, temp);
					featurelist.setSelection(focus-1);
				}
			}
		});
;
		down = new Button(comp, SWT.NONE);
		down.setText("Down");
		down.setLayoutData(gridData);
		down.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				int focus = featurelist.getFocusIndex();
				if(focus != featurelist.getItemCount()-1){ //Last Element is selected, no change
					String temp = featurelist.getItem(focus+1);
					featurelist.setItem(focus+1, featurelist.getItem(focus));
					featurelist.setItem(focus, temp);
					featurelist.setSelection(focus+1);
				}
			}
		});
		save = new Button(comp, SWT.NONE);
		save.setText("SaveOrder");
		save.setLayoutData(gridData);
		save.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				featureOrderWriter();
//				try {
//					new ConfigurationWriter(configuration).saveToFile(((IFile) input.getAdapter(IFile.class)));
//				} catch (CoreException e1) {
//					// 
//					e1.printStackTrace();
//				}				
			}
		});
		
	}

	public void featureOrderWriter(){
	
		File file = ((IFile) input.getAdapter(IFile.class)).
			getProject().getLocation().toFile();
		try {
			fw=new FileWriter(file.toString()+"\\.order");
			for(int i=0;i<featurelist.getItemCount();i++){
					fw.write(featurelist.getItem(i));
					fw.append( System.getProperty("line.separator") );
			}
			fw.close();
		} catch (IOException e) {
			
			e.printStackTrace();
		}	
	}
	
	public void featureOrderReader(){
		File file = ((IFile) input.getAdapter(IFile.class)).
		getProject().getLocation().toFile();
		featurelist.removeAll();
		file=new File(file.toString()+"\\.order");
		Scanner scanner = null;
		try {
			scanner = new Scanner(file);
		} catch (FileNotFoundException e) {
			
			e.printStackTrace();
		}
		while(scanner.hasNext()){
			featurelist.add(scanner.next());
		}	
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	@Override
	
	
	public void setFocus() {
	

	}


	/* (non-Javadoc)
	 * @see java.beans.PropertyChangeListener#propertyChange(java.beans.PropertyChangeEvent)
	 */
	@Override
	public void propertyChange(PropertyChangeEvent event) {
		String prop = event.getPropertyName();
		if (prop.equals(FEATURE_NAME_CHANGED))
		{
	
		}
			
		
	}

}
