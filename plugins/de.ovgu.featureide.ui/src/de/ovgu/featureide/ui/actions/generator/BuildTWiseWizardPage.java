/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.actions.generator;

import javax.annotation.CheckForNull;

import org.eclipse.core.internal.runtime.InternalPlatform;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Scale;
import org.eclipse.swt.widgets.Text;
import org.osgi.framework.Bundle;

import de.ovgu.featureide.core.IFeatureProject;

/**
 * A wizard page for creating T-Wise configurations with SPLCATool.
 * 
 * @author Jens Meinicke
 */
@SuppressWarnings("restriction")
public class BuildTWiseWizardPage extends WizardPage implements IConfigurationBuilderBasics {

	private static final String INTERACTIONS = "&Interactions: ";

	@CheckForNull
	private IFeatureProject project;

	Text fileName;

	private Combo comboLanguage;
	private Button buttonBuildProject;
	private Scale scale;
	private Label labelT;

	private boolean toggleState;

	private int t;

	private String algorithm;

	public BuildTWiseWizardPage(String project, IFeatureProject featureProject, boolean toggleState, String algorithm, int t) {
		super(project);
		this.project = featureProject;
		this.toggleState = toggleState;
		this.algorithm = algorithm;
		this.t = t;
		setDescription("Build T-Wise Configurations with SPLCATool for project " + featureProject.getProjectName() + ".");
	}

	@Override
	public void createControl(Composite parent) {
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		Composite composite = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		layout.verticalSpacing = 9;
		composite.setLayout(layout);
		Label label = new Label(composite, SWT.NULL);
		label.setText("&Algorithm:");
		comboLanguage = new Combo(composite, SWT.BORDER | SWT.SINGLE
				| SWT.READ_ONLY);
		comboLanguage.setLayoutData(gd);
		comboLanguage.add(CASA);
		comboLanguage.add(CHVATAL);
		comboLanguage.add(ICPL);
		comboLanguage.setText(algorithm);
	
		labelT = new Label(composite, SWT.NULL);
		labelT.setText(INTERACTIONS);
		scale = new Scale(composite,SWT.HORIZONTAL);
		scale.setIncrement(1);
		scale.setPageIncrement(1);
		scale.setSelection(t);
		setScale();


		Label labelRefines = new Label(composite, SWT.NULL);
		labelRefines.setText("&Create new projects:");
		buttonBuildProject = new Button(composite, SWT.CHECK);
		buttonBuildProject.setLayoutData(gd);
		buttonBuildProject.setSelection(toggleState);
		
		setPageComplete(false);
		setControl(composite);
		addListeners();
		dialogChanged();
	}

	private void setScale() {
		/** Help content of SPLCATool:
		-t t_wise -a Chvatal -fm <feature_model> -s <strength, 1-4> (-startFrom <covering array>) (-limit <coverage limit>) (-sizelimit <rows>) (-onlyOnes) (-noAllZeros)
		-t t_wise -a ICPL 	 -fm <feature_model> -s <strength, 1-3> (-startFrom <covering array>) (-onlyOnes) (-noAllZeros) [Inexact: (-sizelimit <rows>) (-limit <coverage limit>)] (for 3-wise, -eights <1-8>)
		-t t_wise -a CASA 	 -fm <feature_model> -s <strength, 1-6>
		**/
		
		String selection = comboLanguage.getText();
		int lastSelection = scale.getSelection();
		scale.setMinimum(1);
		if (selection.equals(CHVATAL)) {
			scale.setMaximum(CHVATAL_MAX);
		} else if (selection.equals(ICPL)) {
			scale.setMaximum(ICPL_MAX);
		} else if (selection.equals(CASA)) {
			scale.setMaximum(CASA_MAX);
		}
		if (lastSelection > scale.getMaximum()) {
    		scale.setSelection(scale.getMaximum());
    		labelT.setText(INTERACTIONS + scale.getMaximum());
    	}
	}


	private void dialogChanged() {
		setPageComplete(false);
		// check
		int perspectiveValue = scale.getSelection();
        labelT.setText(INTERACTIONS + perspectiveValue);
        
		setPageComplete(true);

	}
	private void addListeners() {
		comboLanguage.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				setScale();
			}
		});
		
		
		scale.addListener(SWT.Selection, new Listener() {
	        public void handleEvent(Event event) {
	        	int selection = scale.getSelection();
	        	labelT.setText(INTERACTIONS + selection);
	        }
	      });
	}
	
	boolean getToggleState() {
		return buttonBuildProject.getSelection();
	}

	String getAlgorithm() {
		return comboLanguage.getText();
	}
	
	int getT() {
		return scale.getSelection();
	}
	
	public boolean isPluginInstalled(String ID) {
		for(Bundle b :InternalPlatform.getDefault().getBundleContext().getBundles()){
			System.out.println(b.getSymbolicName());
			if(b.getSymbolicName().startsWith(ID))return true;
		}
		return false;
	}
	
}
